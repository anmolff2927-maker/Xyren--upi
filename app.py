import math
import os
import time
import random
import io
import re
import uuid
import string
import threading
import copy
import hmac
import hashlib
import collections
from datetime import datetime
import requests
from flask import Flask, request, jsonify
from PIL import Image, ImageDraw, ImageFont

app = Flask(__name__)

TELEGRAM_BOT_TOKEN = os.environ.get("TELEGRAM_BOT_TOKEN")
ZAPUPI_API_KEY = os.environ.get("ZAPUPI_API_KEY")
BOT_USERNAME = "@Xyren_upibot"
WINS_CHANNEL_ID = os.environ.get("WINS_CHANNEL_ID", "3555754688")
WITHDRAW_LOG_CHANNEL_ID = os.environ.get("WITHDRAW_LOG_CHANNEL_ID", "3975966539")
WINS_CHANNEL_USERNAME = "xyren_wins"

TELEGRAM_API_URL = f"https://api.telegram.org/bot{TELEGRAM_BOT_TOKEN}"

ADMIN_USER_ID = int(os.environ.get("ADMIN_USER_ID", "1822336097"))
PUBLIC_BASE_URL = os.environ.get("PUBLIC_BASE_URL", "https://xyren-upi.onrender.com").rstrip("/")

# ---- Startup safety checks ----
if not TELEGRAM_BOT_TOKEN:
    raise RuntimeError("TELEGRAM_BOT_TOKEN env variable is not set. Bot cannot start.")
if not ZAPUPI_API_KEY:
    print("⚠️ WARNING: ZAPUPI_API_KEY is not set. Deposits will NOT work.")

# ---- Webhook secrets (set TELEGRAM_WEBHOOK_SECRET / ZAPUPI_WEBHOOK_SECRET in env for custom ones;
#      otherwise a stable secret is derived from your tokens) ----
def _derive_secret(label, base):
    return hashlib.sha256(f"{label}:{base}".encode()).hexdigest()

TELEGRAM_WEBHOOK_SECRET = os.environ.get("TELEGRAM_WEBHOOK_SECRET") or _derive_secret("xyren-main", TELEGRAM_BOT_TOKEN)
ZAPUPI_WEBHOOK_SECRET = os.environ.get("ZAPUPI_WEBHOOK_SECRET") or _derive_secret("xyren-zap", ZAPUPI_API_KEY or TELEGRAM_BOT_TOKEN)
admin_list = {ADMIN_USER_ID}

approved_groups = set()

user_balances = {}
user_currency = {}
user_usernames = {}
user_first_names = {}
username_to_id = {}
user_stats = {}
user_deposits = {}
user_withdrawals = {}
user_bet_logs = {}
deposit_history = []
withdrawal_history = []
banned_users = set()

active_games = {}
active_7up_games = {}
pending_game_setup = {}
open_pvp_challenges = {}
active_rains = {}   # rain_id -> rain dict (group giveaways)
active_dr_self_games = {}   # user_id -> /dr self-mode game waiting for the player's own dice
active_pvp_games = {}
active_bj_games = {}
post_match_actions = {}
button_owners = {}  # (chat_id, message_id) -> user_id who owns that message's buttons
NOT_YOUR_MESSAGE_TEXT = "This is not your message ❌"
pending_manual_txns = {}
turn_locks = {}

def get_turn_lock(lock_key):
    if lock_key not in turn_locks:
        turn_locks[lock_key] = threading.Lock()
    return turn_locks[lock_key]

def get_active_game_summary(user_id):
    if user_id in active_7up_games:
        g7 = active_7up_games[user_id]
        gid = g7.get("game_id")
        return f"7Up (`{gid}`)" if gid else "7Up"
    if user_id in globals().get("active_mines_games", {}):
        gid = active_mines_games[user_id].get("game_id")
        return f"Mines (`{gid}`)"
    if user_id in globals().get("active_tower_games", {}):
        gid = active_tower_games[user_id].get("game_id")
        return f"Tower (`{gid}`)"
    if user_id in active_bj_games:
        gbj = active_bj_games[user_id]
        gid = gbj.get("game_id")
        return f"Blackjack (`{gid}`)" if gid else "Blackjack"
    if user_id in active_dr_self_games:
        gid = active_dr_self_games[user_id].get("game_id")
        return f"Prediction (`{gid}`)" if gid else "Prediction"
    if user_id in active_games:
        ref = active_games[user_id]
        if isinstance(ref, str) and ref in active_pvp_games:
            pvm = active_pvp_games[ref]
            gid = pvm.get("game_id") or ref
            return f"PvP Match (`{gid}`)"
        if isinstance(ref, dict):
            gid = ref.get("game_id")
            emoji = ref.get("emoji", "🎮")
            return f"{emoji} Versus Match (`{gid}`)" if gid else f"{emoji} Versus Match"
        return "an active match"
    return None

def is_player_in_active_game(user_id):
    return get_active_game_summary(user_id) is not None

def schedule_pvb_turn_timeout(chat_id, user_id, game):
    token = uuid.uuid4().hex
    game["turn_token"] = token
    emoji = game["emoji"]
    gid = game.get("game_id")

    def on_warn():
        cur = active_games.get(user_id)
        if not isinstance(cur, dict) or cur is not game or cur.get("turn_token") != token:
            return
        if cur.get("step") not in ["selecting_turn", "waiting_user_first", "waiting_user_second"]:
            return
        player_tag = format_user_mention(user_id)
        rem_rolls = cur["rolls_per_round"] - len(cur["current_user_rolls"])
        if rem_rolls <= 0:
            return
        gid_part = f" (`{gid}`)" if gid else ""
        warn_msg = (
            f"⏳ *Turn Timeout Warning*{gid_part}\n\n"
            f"⚠️ {player_tag}, please send {emoji} (`x{rem_rolls}`) within the next *60 seconds*, "
            f"else the bot will roll for you!"
        )
        send_message(chat_id, warn_msg)

    def on_timeout():
        lock = get_turn_lock(f"pvb_{user_id}")
        with lock:
            cur = active_games.get(user_id)
            if not isinstance(cur, dict) or cur is not game or cur.get("turn_token") != token:
                return
            if cur.get("step") not in ["selecting_turn", "waiting_user_first", "waiting_user_second"]:
                return

            cur["turn_token"] = None
            player_tag = format_user_mention(user_id)
            rolls_needed = cur["rolls_per_round"]
            rem_rolls = rolls_needed - len(cur["current_user_rolls"])
            if rem_rolls <= 0:
                return

            if cur["step"] == "selecting_turn":
                cur["first_turn"] = "user"
                cur["step"] = "waiting_user_first"
                s_chat_id = cur.get("start_chat_id") or chat_id
                s_msg_id = cur.get("start_message_id")
                if s_msg_id:
                    remove_inline_keyboard(s_chat_id, s_msg_id)
                    cur["start_message_id"] = None

            gid_part = f" (`{gid}`)" if gid else ""
            send_message(
                chat_id,
                f"⏰ *Timeout*{gid_part} — {player_tag}, bot is throwing {emoji} (`x{rem_rolls}`) for you..."
            )

            auto_vals = roll_bot_series(chat_id, emoji, rem_rolls)
            cur["current_user_rolls"].extend(auto_vals)

            step = cur["step"]
            if step == "waiting_user_first":
                u_expr = "+".join(map(str, cur["current_user_rolls"]))
                send_message(
                    chat_id,
                    f"👤 {player_tag} Auto-Rolls ({emoji}): `{u_expr}` (*{sum(cur['current_user_rolls'])}*)\n\n🤖 Now bot is throwing..."
                )
                time.sleep(0.8)
                b_vals = roll_bot_series(chat_id, emoji, rolls_needed)
                cur["current_bot_rolls"] = b_vals
                resolve_round_and_match(chat_id, user_id, cur)
            elif step == "waiting_user_second":
                resolve_round_and_match(chat_id, user_id, cur)

    t_warn = threading.Timer(60.0, on_warn)
    t_warn.daemon = True
    t_warn.start()

    t_expire = threading.Timer(120.0, on_timeout)
    t_expire.daemon = True
    t_expire.start()

def schedule_pvp_turn_timeout(chat_id, match_id, pvm):
    token = uuid.uuid4().hex
    pvm["turn_token"] = token
    target_uid = pvm["turn"]
    emoji = pvm["emoji"]
    gid = pvm.get("game_id") or match_id

    def on_warn():
        cur = active_pvp_games.get(match_id)
        if cur is not pvm or cur.get("turn_token") != token or cur.get("turn") != target_uid:
            return
        is_p1 = (target_uid == cur["p1_id"])
        cur_rolls = cur["p1_rolls"] if is_p1 else cur["p2_rolls"]
        rem_rolls = cur["rolls_per_round"] - len(cur_rolls)
        if rem_rolls <= 0:
            return
        player_tag = format_user_mention(target_uid)
        warn_msg = (
            f"⏳ *Turn Timeout Warning* (`{gid}`)\n\n"
            f"⚠️ {player_tag}, throw {emoji} (`x{rem_rolls}`) within the next *60 seconds*, "
            f"else your game will forfeit!"
        )
        send_message(chat_id, warn_msg)

    def on_forfeit():
        global HOUSE_BALANCE
        lock = get_turn_lock(f"pvp_{match_id}")
        with lock:
            cur = active_pvp_games.get(match_id)
            if cur is not pvm or cur.get("turn_token") != token or cur.get("turn") != target_uid:
                return

            cur["turn_token"] = None
            p1 = cur["p1_id"]
            p2 = cur["p2_id"]
            loser_id = target_uid
            winner_id = p2 if loser_id == p1 else p1
            bet = cur["bet"]
            g_name = GAME_NAME_MAP.get(emoji, "Game")
            mode = cur["mode"]
            rw_label = cur["rw_label"]

            mult = float(GAME_MULTIPLIERS.get("pvp", 1.94))
            payout = bet * mult
            house_fee = max(0.0, (bet * 2) - payout)
            HOUSE_BALANCE += house_fee

            win_pnl = payout - bet
            user_balances[winner_id] = user_balances.get(winner_id, 0.0) + payout
            persist_user(winner_id)
            persist_user(loser_id)
            save_config_value("house_balance", HOUSE_BALANCE)
            update_user_stats(winner_id, emoji, bet, win_pnl, True)
            update_user_stats(loser_id, emoji, bet, -bet, False)

            label = f"PvP {g_name} ({rw_label}/{mode})"
            record_user_bet(winner_id, label, bet, win_pnl, "WON (Forfeit)", game_id=gid)
            record_user_bet(loser_id, label, bet, -bet, "FORFEITED", game_id=gid)
            win_actor = format_win_actor(winner_id)
            mark_game_finished(
                gid,
                "forfeited",
                extra_meta={"winner_id": winner_id, "winner_label": win_actor, "forfeited_by": loser_id, "payout": payout}
            )
            log_win_to_channel(winner_id, emoji, f"PvP {g_name}", payout, fmt_mult(mult))

            loser_tag = format_user_mention(loser_id)
            winner_tag = format_user_mention(winner_id)
            forfeit_text = (
                f"⌛ *Match Forfeited!* (`{gid}` | {emoji} | `{rw_label}`)\n\n"
                f"🚫 {loser_tag} failed to throw within 2 minutes and forfeited the match.\n"
                f"🏆 *Winner:* {winner_tag}\n"
                f"🎁 *Payout:* *{format_money(payout, winner_id)}* (`{fmt_mult(mult)}`)"
            )
            send_message(chat_id, forfeit_text)

            active_pvp_games.pop(match_id, None)
            if active_games.get(p1) == match_id:
                active_games.pop(p1, None)
            if active_games.get(p2) == match_id:
                active_games.pop(p2, None)

    t_warn = threading.Timer(60.0, on_warn)
    t_warn.daemon = True
    t_warn.start()

    t_forfeit = threading.Timer(120.0, on_forfeit)
    t_forfeit.daemon = True
    t_forfeit.start()

def normalize_chat_id(raw_id):
    if raw_id is None:
        return None
    s = str(raw_id).strip()
    if s.lstrip("-").isdigit():
        return int(s)
    return raw_id

def is_group_approved(raw_chat_id):
    norm = normalize_chat_id(raw_chat_id)
    if norm in approved_groups:
        return True
    if str(norm) in {str(x) for x in approved_groups}:
        return True
    return False

def create_manual_txn_confirmation(initiator_id, prompt_chat_id, action_type, payload):
    token = uuid.uuid4().hex[:10]
    pending_manual_txns[token] = {
        "initiator_id": initiator_id,
        "prompt_chat_id": prompt_chat_id,
        "action_type": action_type,
        "payload": payload,
        "created_at": time.time(),
    }
    keyboard = {
        "inline_keyboard": [
            [
                {"text": "✅ Confirm", "callback_data": f"mtx_ok_{token}"},
                {"text": "❌ Cancel", "callback_data": f"mtx_no_{token}"},
            ]
        ]
    }
    return token, keyboard

def execute_manual_txn(entry):
    global HOUSE_BALANCE
    action_type = entry["action_type"]
    initiator_id = entry["initiator_id"]
    prompt_chat_id = entry["prompt_chat_id"]
    p = entry["payload"]

    if action_type == "sethb":
        val = float(p["val"])
        HOUSE_BALANCE = val
        save_config_value("house_balance", HOUSE_BALANCE)
        send_message(prompt_chat_id, f"✅ House Balance set to *{format_money(HOUSE_BALANCE, initiator_id)}*.")

    elif action_type == "deducthb":
        amt = float(p["amt"])
        HOUSE_BALANCE = max(0.0, HOUSE_BALANCE - amt)
        save_config_value("house_balance", HOUSE_BALANCE)
        send_message(
            prompt_chat_id,
            f"✅ Deducted *{format_money(amt, initiator_id)}* from House Balance.\n🏦 New House Balance: *{format_money(HOUSE_BALANCE, initiator_id)}*"
        )

    elif action_type == "addbalance":
        target_uid = int(p["target_uid"])
        amt_inr = float(p["amt_inr"])
        if target_uid not in user_balances:
            user_balances[target_uid] = 0.0
            user_currency[target_uid] = 'INR'
        user_balances[target_uid] += amt_inr
        persist_user(target_uid)
        send_message(
            prompt_chat_id,
            f"✅ Added *{format_money(amt_inr, target_uid)}* to `{target_uid}`.\n💰 New Balance: *{format_money(user_balances[target_uid], target_uid)}*"
        )
        send_message(target_uid, f"💰 *Admin credited your account!* +{format_money(amt_inr, target_uid)}")

    elif action_type == "deductbalance":
        target_uid = int(p["target_uid"])
        amt_inr = float(p["amt_inr"])
        cur_b = float(user_balances.get(target_uid, 0.0))
        user_balances[target_uid] = max(0.0, cur_b - amt_inr)
        persist_user(target_uid)
        send_message(
            prompt_chat_id,
            f"✅ Deducted *{format_money(amt_inr, target_uid)}* from `{target_uid}`.\n💰 New Balance: *{format_money(user_balances[target_uid], target_uid)}*"
        )
        send_message(target_uid, f"⚠️ *Admin deducted from your account.* -{format_money(amt_inr, target_uid)}")

    elif action_type in ("grp_addbal", "grp_deductbal"):
        # Group message never shows the user's balance.
        target_uid = int(p["target_uid"])
        amt_inr = float(p["amt_inr"])
        label = group_user_label(target_uid)
        msg_id = entry.get("prompt_message_id")
        if target_uid not in user_balances:
            user_balances[target_uid] = 0.0
            user_currency[target_uid] = 'INR'
        cur_b = float(user_balances.get(target_uid, 0.0))
        if action_type == "grp_addbal":
            user_balances[target_uid] = cur_b + amt_inr
            persist_user(target_uid)
            result_txt = f"✅ {group_money(amt_inr, target_uid)} added to {label} balance"
            send_message(target_uid, f"💰 *Admin credited your account!* +{format_money(amt_inr, target_uid)}")
        else:
            if cur_b + 1e-9 < amt_inr:
                result_txt = f"❌ Can't deduct {group_money(amt_inr, target_uid)} — {label} doesn't have enough balance"
            else:
                user_balances[target_uid] = cur_b - amt_inr
                persist_user(target_uid)
                result_txt = f"✅ {group_money(amt_inr, target_uid)} deducted from {label} balance"
                send_message(target_uid, f"⚠️ *Admin deducted from your account.* -{format_money(amt_inr, target_uid)}")
        if msg_id:
            edit_message(prompt_chat_id, msg_id, result_txt)
        else:
            send_message(prompt_chat_id, result_txt)

    elif action_type == "resetdata":
        msg_id = entry.get("prompt_message_id")
        def _show(txt):
            if msg_id:
                edit_message(prompt_chat_id, msg_id, txt)
            else:
                send_message(prompt_chat_id, txt)
        if initiator_id != ADMIN_USER_ID:
            return
        if time.time() - float(entry.get("created_at") or 0) > RESET_CONFIRM_SECONDS:
            _show("⌛ *Reset request expired.* Send /resetdata again.")
            return
        _show("⏳ *Resetting all bot data...*")
        ok, err = reset_all_bot_data()
        if ok:
            _show(
                "✅ *Bot data reset complete!*\n\n"
                "🗑 All old data deleted.\n"
                "🆕 Fresh database is ready — the bot starts from zero."
            )
        else:
            _show(f"❌ *Reset failed.* Nothing was deleted.\n\nError: `{_md_safe(err)}`")

    elif action_type == "tip":
        receiver_id = int(p["receiver_id"])
        amt_inr = float(p["amt_inr"])
        origin_chat_id = p.get("origin_chat_id", prompt_chat_id)
        current_bal = float(user_balances.get(initiator_id, 0.0))
        if current_bal < amt_inr:
            send_message(
                prompt_chat_id,
                f"❌ *Insufficient Balance!*\n💰 Your Balance: *{format_money(current_bal, initiator_id)}*\n🎯 Required Tip: *{format_money(amt_inr, initiator_id)}*"
            )
            return
        if receiver_id not in user_balances:
            user_balances[receiver_id] = 0.0
            user_currency[receiver_id] = 'INR'
        user_balances[initiator_id] = current_bal - amt_inr
        user_balances[receiver_id] = float(user_balances.get(receiver_id, 0.0)) + amt_inr
        persist_user(initiator_id)
        persist_user(receiver_id)

        sender_label = display_sender_label(initiator_id)
        amt_for_receiver = format_money(amt_inr, receiver_id)
        amt_for_sender = format_money(amt_inr, initiator_id)
        send_message(receiver_id, f"{amt_for_receiver} tip recived from {sender_label}")
        if origin_chat_id != receiver_id:
            send_message(origin_chat_id, f"✅ Sent *{amt_for_sender}* tip to {display_sender_label(receiver_id)}!")
        if prompt_chat_id != origin_chat_id:
            send_message(prompt_chat_id, f"✅ Tip confirmed: *{amt_for_sender}* sent to {display_sender_label(receiver_id)}.")

# ===================== 👥 GROUP ADMIN COMMANDS =====================
# In groups the only admin commands that work are /addbal and /deductbal.
# These admin commands work only in DM; in a group the bot stays silent (even for the owner).
DM_ONLY_ADMIN_COMMANDS = {
    "addbalance", "deductbalance", "sethb", "deducthb", "mindep", "minwd", "minbet", "maxbet",
    "setrate", "setgc", "offgame", "ongame", "helper", "helpers", "mults", "approve", "info",
    "search", "panel", "admin", "resetdata",
    "minbetemoji", "maxbetemoji", "minbetdr", "maxbetdr", "minbet7up", "maxbet7up",
    "minbetspecial", "maxbetspecial", "minbetspeacial", "maxbetspeacial",
    "minbetlimbo", "maxbetlimbo", "maxpaylimbo",
}

def _command_name(text):
    m = re.match(r"^/([A-Za-z0-9_]+)(?:@(\S+))?", text or "")
    if not m:
        return None
    if m.group(2) and m.group(2).lower() != BOT_USERNAME.lstrip('@').lower():
        return None  # command meant for another bot
    return m.group(1).lower()

def is_group_balance_command(text):
    return _command_name(text) in ("addbal", "deductbal")

def is_dm_only_admin_command(text):
    name = _command_name(text)
    if not name:
        return False
    return name in DM_ONLY_ADMIN_COMMANDS or name.startswith("setmulti")

def group_money(amount_inr, uid):
    t = format_money(amount_inr, uid)
    return t[:-3] if t.endswith(".00") else t

def group_user_label(uid):
    uname = user_usernames.get(uid)
    if uname:
        return "@" + _md_escape_name(uname)
    return f"`{uid}`"

def handle_group_balance_command(chat_id, user_id, message):
    """Admin replies to a user's message in the group with /addbal 100 or /deductbal 100.
    Also works as /addbal @username 100. Anything else in a group: no answer."""
    text = (message.get('text') or '').strip()
    bot_name = re.escape(BOT_USERNAME.lstrip('@'))
    m = re.match(rf"^/(addbal|deductbal)(?:@{bot_name})?(?:\s+(.*))?$", text, re.IGNORECASE | re.DOTALL)
    if not m:
        return
    if user_id not in admin_list:
        return  # normal users get no reply to admin commands
    cmd = m.group(1).lower()
    args = (m.group(2) or '').split()
    reply_from = (message.get('reply_to_message') or {}).get('from')

    target_uid = None
    amt_raw = None
    if len(args) >= 2:
        target_uid = resolve_user_identifier(args[0])
        amt_raw = args[1]
        if target_uid is None:
            send_message(chat_id, f"⚠️ User `{args[0]}` not found.")
            return
    elif len(args) == 1 and reply_from:
        if reply_from.get('is_bot'):
            send_message(chat_id, "⚠️ Reply to a user's message, not a bot.")
            return
        target_uid = reply_from.get('id')
        amt_raw = args[0]
    else:
        send_message(chat_id, f"⚠️ Reply to a user's message with `/{cmd} <amount>`")
        return

    amt_inr = parse_user_amount(amt_raw, target_uid)
    if amt_inr is None or amt_inr <= 0:
        send_message(chat_id, "⚠️ Enter a valid positive amount.")
        return

    action = "grp_addbal" if cmd == "addbal" else "grp_deductbal"
    _, kb = create_manual_txn_confirmation(user_id, chat_id, action, {"target_uid": target_uid, "amt_inr": amt_inr})
    if cmd == "addbal":
        conf_txt = f"⚠️ *Confirm*\n\nAdd *{group_money(amt_inr, target_uid)}* to {group_user_label(target_uid)} balance?"
    else:
        conf_txt = f"⚠️ *Confirm*\n\nDeduct *{group_money(amt_inr, target_uid)}* from {group_user_label(target_uid)} balance?"
    send_message(chat_id, conf_txt, reply_markup=kb)

game_id_registry = {}
deposit_states = {}
withdrawal_states = {}
admin_states = {}

HOUSE_BALANCE = 100000.0
MIN_BET = 10.0
MAX_BET = 1000.0

# ---- Per-game bet limits (admin: /minbetemoji, /maxbetdr, /maxbet7up, ...) ----
# emoji   = /dice /dart /foot /basket /bowl (bot + PvP)
# dr      = /dr prediction
# 7up     = /7up
# special = /tower /mines /bj
# limbo   = /limbo  (+ LIMBO_MAX_PAYOUT = max win per bet, 0 = no limit)
BET_CATEGORIES = {
    "emoji": "Emoji games",
    "dr": "Prediction/dr",
    "7up": "7up/down",
    "special": "Special games",
    "limbo": "Limbo",
}
BET_LIMITS = {k: {"min": MIN_BET, "max": MAX_BET} for k in BET_CATEGORIES}
LIMBO_MAX_PAYOUT = 0.0
GAME_KIND_TO_BET_CAT = {
    "versus": "emoji", "emoji": "emoji",
    "dr": "dr", "prediction": "dr",
    "7up": "7up",
    "mines": "special", "tower": "special", "bj": "special",
    "limbo": "limbo",
}
CMD_TO_BET_CAT = {
    "/dice": "emoji", "/dart": "emoji", "/foot": "emoji", "/basket": "emoji", "/bowl": "emoji",
    "/dr": "dr", "/7up": "7up",
    "/mines": "special", "/tower": "special", "/bj": "special",
    "/limbo": "limbo",
}
BET_CAT_ALIASES = {"emoji": "emoji", "dr": "dr", "7up": "7up", "special": "special", "speacial": "special", "limbo": "limbo"}

def bet_cat(kind):
    k = str(kind or "").lower()
    if k in BET_LIMITS:
        return k
    return GAME_KIND_TO_BET_CAT.get(k, "emoji")

def bet_cat_for_command(text):
    cmd = (str(text or "").split() or [""])[0].lower().split("@")[0]
    return CMD_TO_BET_CAT.get(cmd, "emoji")

def bet_min(cat):
    return float(BET_LIMITS.get(bet_cat(cat), {}).get("min", MIN_BET))

def bet_max(cat):
    return float(BET_LIMITS.get(bet_cat(cat), {}).get("max", MAX_BET))

def bet_out_of_limits(bet_inr, cat):
    return bet_inr < bet_min(cat) - 1e-9 or bet_inr > bet_max(cat) + 1e-9

def bet_limit_text(cat, user_id):
    c = bet_cat(cat)
    return f"⚠️ Bet out of limits for {BET_CATEGORIES[c]}! Min: {format_money(bet_min(c), user_id)} | Max: {format_money(bet_max(c), user_id)}"

def limbo_payout_error(bet_inr, target, user_id):
    """Error text when bet x target would win more than LIMBO_MAX_PAYOUT, else None."""
    if LIMBO_MAX_PAYOUT <= 0 or bet_inr <= 0:
        return None
    payout = bet_inr * float(target)
    if payout <= LIMBO_MAX_PAYOUT + 1e-9:
        return None
    max_target = math.floor(LIMBO_MAX_PAYOUT / bet_inr * 100) / 100.0
    max_bet_here = math.floor(LIMBO_MAX_PAYOUT / float(target) * 100) / 100.0
    msg = (
        f"⚠️ *Limbo max win is {format_money(LIMBO_MAX_PAYOUT, user_id)}*\n"
        f"{format_money(bet_inr, user_id)} × {float(target):.2f}x = {format_money(payout, user_id)}, which is more than the max win.\n\n"
    )
    tips = []
    if max_target >= 1.01:
        tips.append(f"• Keep the target at *{max_target:.2f}x* or lower")
    if max_bet_here > 0:
        tips.append(f"• Or bet *{format_money(max_bet_here, user_id)}* or less at {float(target):.2f}x")
    return msg + "\n".join(tips)

def _money_short(val):
    v = float(val)
    return f"₹{v:,.0f}" if abs(v - round(v)) < 1e-9 else f"₹{v:,.2f}"

def money_short(val, user_id):
    if user_currency.get(user_id, 'INR') == 'USDT':
        return format_money(val, user_id)
    return _money_short(val)

def build_maxbets_text(user_id):
    lines = ["🎯 *Max Bets*", ""]
    for c, label in BET_CATEGORIES.items():
        line = f"{label}: *{money_short(bet_max(c), user_id)}*"
        if c == "limbo" and LIMBO_MAX_PAYOUT > 0:
            line += f" (maxwin {money_short(LIMBO_MAX_PAYOUT, user_id)})"
        lines.append(line)
    lines.append("")
    lines.append("_Emoji: dice, dart, foot, basket, bowl · Special: tower, mines, bj_")
    return "\n".join(lines)

def _parse_admin_amount(raw):
    val = float(str(raw).replace('₹', '').replace(',', '').strip())
    if not math.isfinite(val):
        raise ValueError()
    return val

def save_bet_limits():
    save_config_value("bet_limits", BET_LIMITS)
    save_config_value("limbo_max_payout", LIMBO_MAX_PAYOUT)

# ===================== 💳 DEPOSIT / WITHDRAW RULES =====================
MIN_DEPOSIT = 100.0          # admin can change with /mindep <amount>
MIN_WITHDRAW = 200.0         # admin can change with /minwd <amount>
WITHDRAW_MULTIPLE = 10       # withdraw amount must be a multiple of this (₹10, ₹20, ...)
WITHDRAW_FEE_FIXED = 10.0    # fixed fee ₹10
WITHDRAW_FEE_PERCENT = 1.0   # + 1% of the withdraw amount
# "deduct": balance cut = amount, user receives amount - fee   (₹200 -> gets ₹188)
# "add":    balance cut = amount + fee, user receives amount   (₹200 -> ₹212 cut, gets ₹200)
WITHDRAW_FEE_MODE = "deduct"
MAIN_GROUP_LINK = "https://t.me/xyren_pro"

def calc_withdraw_fee(amount_inr):
    return round(WITHDRAW_FEE_FIXED + (float(amount_inr) * WITHDRAW_FEE_PERCENT / 100.0), 2)

def withdraw_breakdown(amount_inr):
    """Returns requested amount, fee, how much is cut from balance and how much the user receives."""
    amount_inr = float(amount_inr)
    fee = calc_withdraw_fee(amount_inr)
    if WITHDRAW_FEE_MODE == "add":
        debit, payout = amount_inr + fee, amount_inr
    else:
        debit, payout = amount_inr, amount_inr - fee
    return {"requested": amount_inr, "fee": fee, "debit": round(debit, 2), "payout": round(payout, 2)}

def is_withdraw_multiple(amount_inr):
    return abs(float(amount_inr) / WITHDRAW_MULTIPLE - round(float(amount_inr) / WITHDRAW_MULTIPLE)) < 1e-9

def withdraw_amount_from_word(text_val, user_id):
    """'all' / 'half' for withdrawals: largest amount (multiple of WITHDRAW_MULTIPLE)
    whose balance cut (incl. fee in 'add' mode) fits in full / half of the balance."""
    cap = resolve_all_half(text_val, user_balances.get(user_id, 0.0))
    if cap is None:
        return None
    if WITHDRAW_FEE_MODE == "add":
        # debit = amt + fixed + amt*pct  ->  amt <= (cap - fixed) / (1 + pct)
        cap = (cap - WITHDRAW_FEE_FIXED) / (1 + WITHDRAW_FEE_PERCENT / 100.0)
    amt = math.floor(cap / WITHDRAW_MULTIPLE + 1e-9) * WITHDRAW_MULTIPLE
    while amt > 0 and withdraw_breakdown(amt)["debit"] > float(user_balances.get(user_id, 0.0)) + 1e-9:
        amt -= WITHDRAW_MULTIPLE
    return float(amt) if amt > 0 else 0.0

def validate_withdraw_amount(amount_inr, user_id):
    """Returns an error message, or None when the amount is OK."""
    if amount_inr < MIN_WITHDRAW:
        return f"⚠️ Minimum withdrawal is *₹{MIN_WITHDRAW:,.0f}*."
    if not is_withdraw_multiple(amount_inr):
        return f"⚠️ Withdrawal amount must be a multiple of *₹{WITHDRAW_MULTIPLE}* (e.g. ₹100, ₹110, ₹200)."
    bd = withdraw_breakdown(amount_inr)
    if user_balances.get(user_id, 0.0) < bd["debit"]:
        need = f" (amount + fee ₹{bd['fee']:,.2f})" if WITHDRAW_FEE_MODE == "add" else ""
        return (f"❌ Insufficient balance! You need *₹{bd['debit']:,.2f}*{need}, "
                f"your balance is {format_money(user_balances.get(user_id, 0.0), user_id)}.")
    return None

UPI_MIN_NAME_CHARS = 5
_UPI_NAME_RE = re.compile(r"^[A-Za-z0-9._-]+$")
_UPI_HANDLE_RE = re.compile(r"^[A-Za-z][A-Za-z0-9]{1,63}$")

def validate_upi_id(raw):
    """Returns (clean_upi, None) when OK, or (None, error_message)."""
    upi = str(raw or "").strip()
    example = "\n\nExample: `yourname@ybl`, `9876543210@paytm`"
    if not upi or " " in upi:
        return None, "⚠️ UPI ID me space nahi hona chahiye." + example
    if upi.count("@") != 1:
        return None, "⚠️ UPI ID me ek `@` hona zaroori hai." + example
    name, handle = upi.split("@")
    if not _UPI_NAME_RE.match(name or ""):
        return None, "⚠️ `@` se pehle sirf letters, numbers, `.` `_` `-` allowed hain." + example
    if sum(ch.isalnum() for ch in name) < UPI_MIN_NAME_CHARS:
        return None, f"⚠️ `@` se pehle kam se kam *{UPI_MIN_NAME_CHARS}* letters/numbers hone chahiye." + example
    if not _UPI_HANDLE_RE.match(handle or ""):
        return None, "⚠️ `@` ke baad bank ka naam likho (jaise `ybl`, `paytm`, `okaxis`)." + example
    return upi, None

def build_withdraw_rules_text():
    return (
        f"💸 *Minimum Withdrawal:* ₹{MIN_WITHDRAW:,.0f}\n\n"
        f"• Amount must be in multiples of ₹{WITHDRAW_MULTIPLE}\n"
        f"• Fee: ₹{WITHDRAW_FEE_FIXED:,.0f} + {WITHDRAW_FEE_PERCENT:g}% of the amount"
    )

def build_withdraw_prompt_text():
    return "💸 *Withdrawal Funds*\n\n" + build_withdraw_rules_text() + "\n\nPlease enter the amount you want to withdraw:"

def _md_escape_name(name):
    for ch in ("\\", "_", "*", "`", "["):
        name = name.replace(ch, "\\" + ch)
    return name

def build_welcome_text(from_user):
    from_user = from_user or {}
    if from_user.get("username"):
        uname = "@" + from_user["username"]
    else:
        uname = (from_user.get("first_name") or "Player").strip()
    uname = _md_escape_name(uname)
    return (
        "🎮 Your Gaming Zone Starts Here!\n\n"
        f"Hey {uname}! 👋\n\n"
        "🎲 Available Games\n"
        "┌ 🎲 /dice — Roll the Dice\n"
        "├ 🎳 /bowl — Bowl Game\n"
        "├ 🎯 /dart — Dart Challenge\n"
        "├ 🎲 /dr — Dice Roll\n"
        "├ ↕️ /7up — 7 Up 7 Down\n"
        "├ 💣 /mines — Mines Game\n"
        "└ 🚀 /limbo — Limbo Challenge\n\n"
        "✨ Pick your favorite game and enjoy the action!\n\n"
        "💙 Play smart. Have fun. Stay legendary.\n\n"
        "PaisaPlayz — The Game Has a Name."
    )

def welcome_keyboard():
    return {"inline_keyboard": [[{"text": "join main group", "url": MAIN_GROUP_LINK}]]}
EXCHANGE_RATE = 98.0
MAINTENANCE_MODE = False
DEPOSIT_ENABLED = True
WITHDRAW_ENABLED = True
DM_GAMES_ENABLED = True
GROUP_LINK = None

DM_GAME_COMMANDS = ['/dice', '/dart', '/foot', '/basket', '/bowl', '/dr', '/bj', '/7up', '/mines', '/tower', '/limbo']

def is_dm_game_command(text):
    bot_name = re.escape(BOT_USERNAME.lstrip('@'))
    for cmd in DM_GAME_COMMANDS:
        if re.match(rf"^{re.escape(cmd)}(?:@{bot_name})?(?:\s|$)", text, re.IGNORECASE):
            return True
    return False

def build_dm_games_off_text():
    if GROUP_LINK:
        safe_link = GROUP_LINK.replace('_', '\\_').replace('*', '\\*').replace('`', '\\`').replace('[', '\\[')
        place = safe_link
    else:
        place = "our group"
    return f"❌ Games in DM are currently turned off.\n\nPlease play in {place}."

PAGE_SIZE = 5

GAME_MULTIPLIERS = {
    "dice": 1.94,
    "dart": 1.94,
    "foot": 1.94,
    "basket": 1.94,
    "bowl": 1.94,
    "pvp": 1.94,
    "bj": 2.0,
    "dr": 1.92,
    "dr_nums": {1: 5.56, 2: 2.88, 3: 1.92, 4: 1.44, 5: 1.15},
    "7up": {
        "up": 2.16,
        "down": 2.16,
        "odd": 1.9,
        "even": 1.9,
        "7": 5.16,
    },
}

EMOJI_TO_MULT_KEY = {
    "🎲": "dice",
    "🎯": "dart",
    "⚽": "foot",
    "🏀": "basket",
    "🎳": "bowl",
}

VALID_RW_MODES = {
    "1r1w": (1, 1),
    "2r1w": (2, 1),
    "3r1w": (3, 1),
    "1r2w": (1, 2),
    "2r2w": (2, 2),
    "3r2w": (3, 2),
    "1r3w": (1, 3),
    "2r3w": (2, 3),
    "3r3w": (3, 3),
}

GAME_NAME_MAP = {
    "🎲": "Dice",
    "🎯": "Dart",
    "⚽": "Football",
    "🏀": "Basketball",
    "🎳": "Bowling",
}

def normalize_7up_choice(raw_choice):
    if raw_choice is None:
        return None
    c = str(raw_choice).strip().lower()
    if c in ("up", "high"):
        return "up"
    if c in ("down", "low"):
        return "down"
    if c == "odd":
        return "odd"
    if c == "even":
        return "even"
    if c == "7":
        return "7"
    return None

def format_7up_choice_label(canonical_choice, is_win=True):
    if canonical_choice == "up":
        return "up / high (8–12)" if is_win else "up/ high (8–12)"
    if canonical_choice == "down":
        return "down / low (2–6)" if is_win else "down/ low (2–6)"
    if canonical_choice == "odd":
        return "odd"
    if canonical_choice == "even":
        return "even"
    if canonical_choice == "7":
        return "7"
    return str(canonical_choice)

def format_7up_outcome_tag(canonical_choice, total_val):
    if canonical_choice in ("up", "down"):
        return "up/high" if total_val >= 8 else ("down/low" if total_val <= 6 else "7")
    if canonical_choice in ("odd", "even"):
        return "even" if total_val % 2 == 0 else "odd"
    if canonical_choice == "7":
        if total_val == 7:
            return "7"
        return "up/high" if total_val >= 8 else "down/low"
    return "up/high" if total_val >= 8 else ("down/low" if total_val <= 6 else "7")

def evaluate_7up_outcome(canonical_choice, total_val):
    if canonical_choice == "up":
        return 8 <= total_val <= 12
    if canonical_choice == "down":
        return 2 <= total_val <= 6
    if canonical_choice == "odd":
        return (total_val % 2) == 1
    if canonical_choice == "even":
        return (total_val % 2) == 0
    if canonical_choice == "7":
        return total_val == 7
    return False

def get_7up_multiplier(canonical_choice):
    mult_map = GAME_MULTIPLIERS.get("7up") or {}
    defaults = {"up": 2.16, "down": 2.16, "odd": 1.9, "even": 1.9, "7": 5.16}
    return float(mult_map.get(canonical_choice, defaults.get(canonical_choice, 1.0)))

def run_7up_game(chat_id, user_id, bet_inr, canonical_choice, raw_choice_text=None, reply_to_message_id=None):
    global HOUSE_BALANCE
    gid = generate_game_id()
    current_bal = float(user_balances.get(user_id, 0.0))
    user_balances[user_id] = current_bal - bet_inr
    persist_user(user_id)

    active_7up_games[user_id] = {
        "game_id": gid,
        "chat_id": chat_id,
        "bet": bet_inr,
        "choice": canonical_choice,
        "raw_choice": raw_choice_text or canonical_choice,
    }

    try:
        register_game_record(
            gid,
            "seven_up",
            user_id,
            bet_inr,
            meta={"choice": canonical_choice, "raw_choice": raw_choice_text or canonical_choice},
            refund_on_cancel=True
        )
        choice_disp_hist = format_7up_choice_label(canonical_choice, is_win=True)
        mult = get_7up_multiplier(canonical_choice)
        res1 = send_animated_game(chat_id, "🎲", reply_to_message_id=reply_to_message_id)
        d1 = res1["result"]["dice"]["value"] if res1 and "result" in res1 else random.randint(1, 6)
        time.sleep(0.6)
        res2 = send_animated_game(chat_id, "🎲", reply_to_message_id=reply_to_message_id)
        d2 = res2["result"]["dice"]["value"] if res2 and "result" in res2 else random.randint(1, 6)
        time.sleep(0.8)

        total_val = d1 + d2
        is_win = evaluate_7up_outcome(canonical_choice, total_val)
        outcome_tag = format_7up_outcome_tag(canonical_choice, total_val)

        if is_win:
            win_amt = bet_inr * mult
            profit_inr = win_amt - bet_inr
            user_balances[user_id] = float(user_balances.get(user_id, 0.0)) + win_amt
            HOUSE_BALANCE -= profit_inr
            persist_user(user_id)
            save_config_value("house_balance", HOUSE_BALANCE)
            update_user_stats(user_id, "7up", bet_inr, profit_inr, True)
            record_user_bet(user_id, f"7Up ({choice_disp_hist})", bet_inr, profit_inr, "WON", game_id=gid)
            mark_game_finished(
                gid,
                "completed",
                extra_meta={"outcome": "WON", "d1": d1, "d2": d2, "total": total_val, "pnl": profit_inr}
            )
            log_win_to_channel(user_id, "🎲", "7Up", win_amt, fmt_mult(mult))
            pick_label = format_7up_choice_label(canonical_choice, is_win=True)
            result_text = (
                f"📊 7UP GAME REPORT\n"
                f"━━━━━━━━━━━━━━━━\n"
                f"🔑 Round ID: {gid}\n"
                f"🎲 Dice Result: {d1} + {d2} = {total_val}\n"
                f"🎯 Selected: {pick_label}\n"
                f"🔥 Outcome: Win\n"
                f"💰 Payout: {format_money(win_amt, user_id)}\n"
                f"⚡ Multiplier: {fmt_mult(mult)}\n"
                f"━━━━━━━━━━━━━━━━"
            )
        else:
            profit_inr = -bet_inr
            HOUSE_BALANCE += bet_inr
            persist_user(user_id)
            save_config_value("house_balance", HOUSE_BALANCE)
            update_user_stats(user_id, "7up", bet_inr, profit_inr, False)
            record_user_bet(user_id, f"7Up ({choice_disp_hist})", bet_inr, profit_inr, "LOST", game_id=gid)
            mark_game_finished(
                gid,
                "completed",
                extra_meta={"outcome": "LOST", "d1": d1, "d2": d2, "total": total_val, "pnl": profit_inr}
            )
            pick_label = format_7up_choice_label(canonical_choice, is_win=True)
            result_text = (
                f"📊 7UP GAME REPORT\n"
                f"━━━━━━━━━━━━━━━━\n"
                f"🔑 Round ID: {gid}\n"
                f"🎲 Dice Result: {d1} + {d2} = {total_val}\n"
                f"🎯 Selected: {pick_label}\n"
                f"🔥 Outcome: loss\n"
                f"💰 Payout: {format_money(0.0, user_id)}\n"
                f"⚡ Multiplier: {fmt_mult(mult)}\n"
                f"━━━━━━━━━━━━━━━━"
            )

        pm_7up_payload = {
            "kind": "7up",
            "owner_id": user_id,
            "bet": bet_inr,
            "choice_7up": canonical_choice,
        }
        send_message(chat_id, result_text, reply_markup=create_post_match_keyboard(user_id, pm_7up_payload))
    finally:
        active_7up_games.pop(user_id, None)

import json
import psycopg2
from psycopg2.extras import RealDictCursor

DATABASE_URL = os.environ.get("DATABASE_URL")

def get_db_connection():
    if not DATABASE_URL:
        return None
    return psycopg2.connect(DATABASE_URL)

def init_db():
    conn = get_db_connection()
    if not conn:
        return
    try:
        with conn:
            with conn.cursor() as cur:
                cur.execute("""
                    CREATE TABLE IF NOT EXISTS users (
                        user_id BIGINT PRIMARY KEY,
                        balance DOUBLE PRECISION DEFAULT 0.0,
                        currency TEXT DEFAULT 'INR',
                        username TEXT,
                        first_name TEXT,
                        is_banned BOOLEAN DEFAULT FALSE,
                        is_admin BOOLEAN DEFAULT FALSE,
                        total_deposits DOUBLE PRECISION DEFAULT 0.0,
                        total_withdrawals DOUBLE PRECISION DEFAULT 0.0,
                        stats_json TEXT DEFAULT '{}'
                    )
                """)
                cur.execute("""
                    CREATE TABLE IF NOT EXISTS bet_logs (
                        id SERIAL PRIMARY KEY,
                        user_id BIGINT,
                        game_id TEXT,
                        game_label TEXT,
                        bet_inr DOUBLE PRECISION,
                        pnl_inr DOUBLE PRECISION,
                        outcome_label TEXT,
                        created_at TEXT
                    )
                """)
                cur.execute("""
                    CREATE TABLE IF NOT EXISTS deposits (
                        id SERIAL PRIMARY KEY,
                        user_id BIGINT,
                        amount DOUBLE PRECISION,
                        utr TEXT,
                        created_at TEXT
                    )
                """)
                cur.execute("""
                    CREATE TABLE IF NOT EXISTS withdrawals (
                        id SERIAL PRIMARY KEY,
                        user_id BIGINT,
                        amount DOUBLE PRECISION,
                        upi TEXT,
                        created_at TEXT
                    )
                """)
                # Transaction IDs + withdrawal status (safe to run on every start)
                cur.execute("ALTER TABLE deposits ADD COLUMN IF NOT EXISTS txn_id TEXT")
                cur.execute("ALTER TABLE deposits ADD COLUMN IF NOT EXISTS order_id TEXT")
                cur.execute("ALTER TABLE withdrawals ADD COLUMN IF NOT EXISTS txn_id TEXT")
                cur.execute("ALTER TABLE withdrawals ADD COLUMN IF NOT EXISTS status TEXT DEFAULT 'pending'")
                cur.execute("ALTER TABLE withdrawals ADD COLUMN IF NOT EXISTS processed_at TEXT")
                cur.execute("ALTER TABLE withdrawals ADD COLUMN IF NOT EXISTS processed_by BIGINT")
                cur.execute("ALTER TABLE withdrawals ADD COLUMN IF NOT EXISTS reject_reason TEXT")
                cur.execute("ALTER TABLE withdrawals ADD COLUMN IF NOT EXISTS fee DOUBLE PRECISION")
                cur.execute("ALTER TABLE withdrawals ADD COLUMN IF NOT EXISTS payout DOUBLE PRECISION")
                # Refer system
                cur.execute("ALTER TABLE users ADD COLUMN IF NOT EXISTS ref_code TEXT")
                cur.execute("ALTER TABLE users ADD COLUMN IF NOT EXISTS referred_by BIGINT")
                cur.execute("ALTER TABLE users ADD COLUMN IF NOT EXISTS referred_at TEXT")
                cur.execute("ALTER TABLE users ADD COLUMN IF NOT EXISTS ref_gen_dep DOUBLE PRECISION DEFAULT 0.0")
                cur.execute("ALTER TABLE users ADD COLUMN IF NOT EXISTS ref_gen_wager DOUBLE PRECISION DEFAULT 0.0")
                cur.execute("ALTER TABLE users ADD COLUMN IF NOT EXISTS ref_earned DOUBLE PRECISION DEFAULT 0.0")
                cur.execute("""
                    CREATE TABLE IF NOT EXISTS deposit_orders (
                        txn_id TEXT PRIMARY KEY,
                        order_id TEXT,
                        user_id BIGINT,
                        amount DOUBLE PRECISION,
                        status TEXT DEFAULT 'pending',
                        created_at TEXT,
                        credited_at TEXT
                    )
                """)
                cur.execute("""
                    CREATE TABLE IF NOT EXISTS approved_groups (
                        chat_id BIGINT PRIMARY KEY
                    )
                """)
                cur.execute("""
                    CREATE TABLE IF NOT EXISTS bot_config (
                        key TEXT PRIMARY KEY,
                        value_json TEXT
                    )
                """)
                cur.execute("""
                    CREATE TABLE IF NOT EXISTS game_records (
                        game_id TEXT PRIMARY KEY,
                        record_json TEXT
                    )
                """)
    except Exception as e:
        print(f"DB init error: {e}")
    finally:
        conn.close()

def save_config_value(key, val):
    conn = get_db_connection()
    if not conn:
        return
    try:
        with conn:
            with conn.cursor() as cur:
                cur.execute(
                    """
                    INSERT INTO bot_config (key, value_json) VALUES (%s, %s)
                    ON CONFLICT (key) DO UPDATE SET value_json = EXCLUDED.value_json
                    """,
                    (key, json.dumps(val))
                )
    except Exception as e:
        print(f"DB save_config error ({key}): {e}")
    finally:
        conn.close()

def persist_config_all():
    save_config_value("house_balance", HOUSE_BALANCE)
    save_config_value("min_bet", MIN_BET)
    save_config_value("max_bet", MAX_BET)
    save_config_value("bet_limits", BET_LIMITS)
    save_config_value("limbo_max_payout", LIMBO_MAX_PAYOUT)
    save_config_value("exchange_rate", EXCHANGE_RATE)
    save_config_value("maintenance_mode", MAINTENANCE_MODE)
    save_config_value("deposit_enabled", DEPOSIT_ENABLED)
    save_config_value("withdraw_enabled", WITHDRAW_ENABLED)
    save_config_value("game_multipliers", GAME_MULTIPLIERS)
    save_config_value("dm_games_enabled", DM_GAMES_ENABLED)
    save_config_value("group_link", GROUP_LINK)
    save_config_value("min_deposit", MIN_DEPOSIT)
    save_config_value("min_withdraw", MIN_WITHDRAW)

def persist_user(uid):
    if uid is None:
        return
    conn = get_db_connection()
    if not conn:
        return
    try:
        bal = float(user_balances.get(uid, 0.0))
        curr = user_currency.get(uid, "INR")
        uname = user_usernames.get(uid)
        fname = user_first_names.get(uid)
        is_banned = uid in banned_users
        is_adm = uid in admin_list
        tot_dep = float(user_deposits.get(uid, 0.0))
        tot_wd = float(user_withdrawals.get(uid, 0.0))
        st_json = json.dumps(user_stats.get(uid, {"games": 0, "wins": 0, "losses": 0, "total_pnl": 0.0, "biggest_win": 0.0, "game_counts": {}}))
        r_code = user_ref_code.get(uid)
        r_by = user_referred_by.get(uid)
        r_at = user_referred_at.get(uid)
        r_gd = float(user_ref_gen_dep.get(uid, 0.0))
        r_gw = float(user_ref_gen_wager.get(uid, 0.0))
        r_earn = float(user_ref_earned.get(uid, 0.0))
        with conn:
            with conn.cursor() as cur:
                cur.execute(
                    """
                    INSERT INTO users (user_id, balance, currency, username, first_name, is_banned, is_admin, total_deposits, total_withdrawals, stats_json,
                                       ref_code, referred_by, referred_at, ref_gen_dep, ref_gen_wager, ref_earned)
                    VALUES (%s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s)
                    ON CONFLICT (user_id) DO UPDATE SET
                        balance = EXCLUDED.balance,
                        currency = EXCLUDED.currency,
                        username = COALESCE(EXCLUDED.username, users.username),
                        first_name = COALESCE(EXCLUDED.first_name, users.first_name),
                        is_banned = EXCLUDED.is_banned,
                        is_admin = EXCLUDED.is_admin,
                        total_deposits = EXCLUDED.total_deposits,
                        total_withdrawals = EXCLUDED.total_withdrawals,
                        stats_json = EXCLUDED.stats_json,
                        ref_code = COALESCE(users.ref_code, EXCLUDED.ref_code),
                        referred_by = COALESCE(users.referred_by, EXCLUDED.referred_by),
                        referred_at = COALESCE(users.referred_at, EXCLUDED.referred_at),
                        ref_gen_dep = EXCLUDED.ref_gen_dep,
                        ref_gen_wager = EXCLUDED.ref_gen_wager,
                        ref_earned = EXCLUDED.ref_earned
                    """,
                    (uid, bal, curr, uname, fname, is_banned, is_adm, tot_dep, tot_wd, st_json,
                     r_code, r_by, r_at, r_gd, r_gw, r_earn)
                )
    except Exception as e:
        print(f"DB persist_user error ({uid}): {e}")
    finally:
        conn.close()

def persist_bet_log(user_id, game_label, bet_inr, pnl_inr, outcome_label, game_id, ts):
    conn = get_db_connection()
    if not conn:
        return
    try:
        with conn:
            with conn.cursor() as cur:
                cur.execute(
                    """
                    INSERT INTO bet_logs (user_id, game_id, game_label, bet_inr, pnl_inr, outcome_label, created_at)
                    VALUES (%s, %s, %s, %s, %s, %s, %s)
                    """,
                    (user_id, game_id, game_label, float(bet_inr), float(pnl_inr), outcome_label, ts)
                )
    except Exception as e:
        print(f"DB persist_bet_log error: {e}")
    finally:
        conn.close()

def persist_deposit(user_id, amount, utr, ts, txn_id=None, order_id=None):
    conn = get_db_connection()
    if not conn:
        return
    try:
        with conn:
            with conn.cursor() as cur:
                cur.execute(
                    "INSERT INTO deposits (user_id, amount, utr, created_at, txn_id, order_id) VALUES (%s, %s, %s, %s, %s, %s)",
                    (user_id, float(amount), utr, ts, txn_id, order_id)
                )
    except Exception as e:
        print(f"DB persist_deposit error: {e}")
    finally:
        conn.close()

def persist_withdrawal(user_id, amount, upi, ts, txn_id=None, status="pending", fee=None, payout=None):
    conn = get_db_connection()
    if not conn:
        return
    try:
        with conn:
            with conn.cursor() as cur:
                cur.execute(
                    "INSERT INTO withdrawals (user_id, amount, upi, created_at, txn_id, status, fee, payout) VALUES (%s, %s, %s, %s, %s, %s, %s, %s)",
                    (user_id, float(amount), upi, ts, txn_id, status, fee, payout)
                )
    except Exception as e:
        print(f"DB persist_withdrawal error: {e}")
    finally:
        conn.close()

def persist_deposit_order(rec):
    conn = get_db_connection()
    if not conn:
        return
    try:
        with conn:
            with conn.cursor() as cur:
                cur.execute(
                    """
                    INSERT INTO deposit_orders (txn_id, order_id, user_id, amount, status, created_at, credited_at)
                    VALUES (%s, %s, %s, %s, %s, %s, %s)
                    ON CONFLICT (txn_id) DO UPDATE SET status = EXCLUDED.status, credited_at = EXCLUDED.credited_at
                    """,
                    (rec["id"], rec["order_id"], rec["user"], float(rec["amount"]), rec["status"], rec["time"], rec.get("credited_at"))
                )
    except Exception as e:
        print(f"DB persist_deposit_order error: {e}")
    finally:
        conn.close()

def persist_withdrawal_status(txn_id, status, processed_at=None, processed_by=None, reject_reason=None):
    conn = get_db_connection()
    if not conn or not txn_id:
        return
    try:
        with conn:
            with conn.cursor() as cur:
                cur.execute(
                    "UPDATE withdrawals SET status = %s, processed_at = %s, processed_by = %s, reject_reason = %s WHERE txn_id = %s",
                    (status, processed_at, processed_by, reject_reason, txn_id)
                )
    except Exception as e:
        print(f"DB persist_withdrawal_status error: {e}")
    finally:
        conn.close()

def persist_approved_group(chat_id):
    norm_id = normalize_chat_id(chat_id)
    if norm_id is None:
        return
    conn = get_db_connection()
    if not conn:
        return
    try:
        with conn:
            with conn.cursor() as cur:
                cur.execute(
                    "INSERT INTO approved_groups (chat_id) VALUES (%s) ON CONFLICT (chat_id) DO NOTHING",
                    (int(norm_id),)
                )
    except Exception as e:
        print(f"DB persist_approved_group error: {e}")
    finally:
        conn.close()

def persist_game_record(game_id, record):
    conn = get_db_connection()
    if not conn:
        return
    try:
        with conn:
            with conn.cursor() as cur:
                cur.execute(
                    """
                    INSERT INTO game_records (game_id, record_json) VALUES (%s, %s)
                    ON CONFLICT (game_id) DO UPDATE SET record_json = EXCLUDED.record_json
                    """,
                    (game_id, json.dumps(record))
                )
    except Exception as e:
        print(f"DB persist_game_record error: {e}")
    finally:
        conn.close()

def load_all_from_db():
    global HOUSE_BALANCE, MIN_BET, MAX_BET, EXCHANGE_RATE, MAINTENANCE_MODE, DEPOSIT_ENABLED, WITHDRAW_ENABLED, DM_GAMES_ENABLED, GROUP_LINK, MIN_DEPOSIT, MIN_WITHDRAW
    global LIMBO_MAX_PAYOUT
    conn = get_db_connection()
    if not conn:
        return
    try:
        with conn.cursor(cursor_factory=RealDictCursor) as cur:
            cur.execute("SELECT key, value_json FROM bot_config")
            _saved_bet_limits = None
            for row in cur.fetchall():
                k = row["key"]
                v = json.loads(row["value_json"])
                if k == "house_balance":
                    HOUSE_BALANCE = float(v)
                elif k == "min_bet":
                    MIN_BET = float(v)
                elif k == "min_deposit":
                    MIN_DEPOSIT = float(v)
                elif k == "min_withdraw":
                    MIN_WITHDRAW = float(v)
                elif k == "max_bet":
                    MAX_BET = float(v)
                elif k == "bet_limits" and isinstance(v, dict):
                    _saved_bet_limits = v
                elif k == "limbo_max_payout":
                    LIMBO_MAX_PAYOUT = float(v or 0.0)
                elif k == "exchange_rate":
                    EXCHANGE_RATE = float(v)
                elif k == "maintenance_mode":
                    MAINTENANCE_MODE = bool(v)
                elif k == "deposit_enabled":
                    DEPOSIT_ENABLED = bool(v)
                elif k == "withdraw_enabled":
                    WITHDRAW_ENABLED = bool(v)
                elif k == "dm_games_enabled":
                    DM_GAMES_ENABLED = bool(v)
                elif k == "helper_bots":
                    HELPER_BOTS[:] = [x for x in (v or []) if isinstance(x, dict) and x.get("token")]
                elif k == "group_link":
                    GROUP_LINK = v if v else None
                elif k == "game_multipliers" and isinstance(v, dict):
                    for mk, mv in v.items():
                        if mk == "dr_nums" and isinstance(mv, dict):
                            GAME_MULTIPLIERS["dr_nums"].update({int(dk): float(dv) for dk, dv in mv.items()})
                        elif mk == "7up" and isinstance(mv, dict):
                            GAME_MULTIPLIERS["7up"].update({str(sk): float(sv) for sk, sv in mv.items()})
                        else:
                            GAME_MULTIPLIERS[mk] = float(mv)

            # Per-game bet limits: start from the general min/max, then apply saved values.
            for _c in BET_LIMITS:
                BET_LIMITS[_c] = {"min": MIN_BET, "max": MAX_BET}
            if _saved_bet_limits:
                for _c, _lim in _saved_bet_limits.items():
                    if _c in BET_LIMITS and isinstance(_lim, dict):
                        try:
                            BET_LIMITS[_c]["min"] = float(_lim.get("min", BET_LIMITS[_c]["min"]))
                            BET_LIMITS[_c]["max"] = float(_lim.get("max", BET_LIMITS[_c]["max"]))
                        except (TypeError, ValueError):
                            pass

            cur.execute("SELECT * FROM users")
            for r in cur.fetchall():
                uid = int(r["user_id"])
                user_balances[uid] = float(r["balance"] or 0.0)
                user_currency[uid] = r["currency"] or "INR"
                if r["username"]:
                    clean_u = r["username"].lstrip("@").lower()
                    user_usernames[uid] = clean_u
                    username_to_id[clean_u] = uid
                if r["first_name"]:
                    user_first_names[uid] = r["first_name"]
                if r["is_banned"]:
                    banned_users.add(uid)
                if r["is_admin"]:
                    admin_list.add(uid)
                user_deposits[uid] = float(r["total_deposits"] or 0.0)
                user_withdrawals[uid] = float(r["total_withdrawals"] or 0.0)
                if r.get("ref_code"):
                    user_ref_code[uid] = r["ref_code"]
                    ref_code_to_id[r["ref_code"]] = uid
                if r.get("referred_by") is not None:
                    user_referred_by[uid] = int(r["referred_by"])
                    user_referred_at[uid] = r.get("referred_at") or ""
                user_ref_gen_dep[uid] = float(r.get("ref_gen_dep") or 0.0)
                user_ref_gen_wager[uid] = float(r.get("ref_gen_wager") or 0.0)
                user_ref_earned[uid] = float(r.get("ref_earned") or 0.0)
                if r["stats_json"]:
                    try:
                        parsed_st = json.loads(r["stats_json"])
                        if isinstance(parsed_st, dict):
                            user_stats[uid] = parsed_st
                    except Exception:
                        pass

            cur.execute("SELECT * FROM bet_logs ORDER BY id ASC")
            for r in cur.fetchall():
                uid = int(r["user_id"])
                user_bet_logs.setdefault(uid, []).append({
                    "game_id": r["game_id"],
                    "game": r["game_label"],
                    "bet": float(r["bet_inr"] or 0.0),
                    "pnl": float(r["pnl_inr"] or 0.0),
                    "outcome": r["outcome_label"],
                    "time": r["created_at"] or ""
                })

            backfill_dep = []
            cur.execute("SELECT * FROM deposits ORDER BY id ASC")
            for r in cur.fetchall():
                tid = r.get("txn_id")
                if not tid:
                    tid = generate_txn_id("DP")
                    backfill_dep.append((tid, r["id"]))
                _txn_ids_in_use.add(tid)
                deposit_history.append({
                    "id": tid,
                    "user": int(r["user_id"]),
                    "amount": float(r["amount"] or 0.0),
                    "utr": r["utr"] or "",
                    "order_id": r.get("order_id") or "",
                    "time": r["created_at"] or ""
                })

            try:
                cur.execute("SELECT * FROM deposit_orders")
                for r in cur.fetchall():
                    _txn_ids_in_use.add(r["txn_id"])
                    deposit_orders[r["order_id"]] = {
                        "id": r["txn_id"],
                        "order_id": r["order_id"],
                        "user": int(r["user_id"]),
                        "amount": float(r["amount"] or 0.0),
                        "status": r.get("status") or "pending",
                        "time": r.get("created_at") or "",
                        "credited_at": r.get("credited_at") or ""
                    }
            except Exception as e:
                print(f"DB load deposit_orders error: {e}")
                conn.rollback()

            backfill_wd = []
            cur.execute("SELECT * FROM withdrawals ORDER BY id ASC")
            for r in cur.fetchall():
                tid = r.get("txn_id")
                if not tid:
                    tid = generate_txn_id("WD")
                    backfill_wd.append((tid, r["id"]))
                _txn_ids_in_use.add(tid)
                withdrawal_history.append({
                    "id": tid,
                    "user": int(r["user_id"]),
                    "amount": float(r["amount"] or 0.0),
                    "upi": r["upi"] or "",
                    "time": r["created_at"] or "",
                    # Old rows (before status tracking) are treated as already handled
                    "status": r.get("status") or "legacy",
                    "processed_at": r.get("processed_at") or "",
                    "processed_by": r.get("processed_by"),
                    "reject_reason": r.get("reject_reason") or "",
                    "fee": float(r["fee"]) if r.get("fee") is not None else None,
                    "payout": float(r["payout"]) if r.get("payout") is not None else None
                })

            for tid, row_id in backfill_dep:
                cur.execute("UPDATE deposits SET txn_id = %s WHERE id = %s", (tid, row_id))
            for tid, row_id in backfill_wd:
                cur.execute("UPDATE withdrawals SET txn_id = %s, status = COALESCE(status, 'legacy') WHERE id = %s", (tid, row_id))
            if backfill_dep or backfill_wd:
                conn.commit()

            cur.execute("SELECT chat_id FROM approved_groups")
            for r in cur.fetchall():
                if r and r.get("chat_id") is not None:
                    approved_groups.add(int(r["chat_id"]))

            cur.execute("SELECT game_id, record_json FROM game_records")
            for r in cur.fetchall():
                try:
                    game_id_registry[r["game_id"]] = json.loads(r["record_json"])
                except Exception:
                    pass
    except Exception as e:
        print(f"DB load_all error: {e}")
    finally:
        conn.close()


def fmt_mult(val):
    s = f"{float(val):.4f}".rstrip("0").rstrip(".")
    return f"{s}x"

def get_versus_multiplier(emoji):
    key = EMOJI_TO_MULT_KEY.get(emoji, "dice")
    return float(GAME_MULTIPLIERS.get(key, 1.94))

def normalize_channel_id(raw_id):
    if raw_id is None:
        return None
    s = str(raw_id).strip()
    if not s:
        return None
    if s.startswith("-100"):
        return int(s)
    if s.startswith("-"):
        num = s[1:]
        return int(f"-100{num}") if not num.startswith("100") else int(s)
    if s.isdigit():
        return int(f"-100{s}")
    return s

def mask_user_id_for_log(user_id):
    value = str(user_id)
    if len(value) <= 4:
        return "*" * len(value)
    return "*" * (len(value) - 4) + value[-4:]

def mask_upi_id_for_log(upi_id):
    value = str(upi_id or "").strip()
    local, separator, provider = value.partition("@")
    if separator:
        if len(local) <= 2:
            masked_local = (local[:1] + "*") if local else "**"
        else:
            masked_local = local[0] + "*" * (len(local) - 2) + local[-1]
        return f"{masked_local}@{provider}"
    return mask_user_id_for_log(value)

def format_user_mention(user_id):
    uname = user_usernames.get(user_id)
    if uname:
        return f"@{uname}"
    fname = user_first_names.get(user_id) or f"User {user_id}"
    safe_name = str(fname).replace("[", "").replace("]", "")
    return f"[{safe_name}](tg://user?id={user_id})"

def tag_player(user_id):
    """Clickable mention that tags the player (safe for Markdown)."""
    uname = user_usernames.get(user_id)
    if uname:
        return "@" + str(uname).replace("_", "\\_")
    fname = user_first_names.get(user_id) or "Player"
    safe_name = re.sub(r"[\[\]_*`()]", "", str(fname)).strip() or "Player"
    return f"[{safe_name}](tg://user?id={user_id})"

def format_win_actor(user_id):
    if user_id in user_usernames and user_usernames[user_id]:
        return f"@{user_usernames[user_id]}"
    if user_id in user_first_names and user_first_names[user_id]:
        return user_first_names[user_id]
    return f"User {user_id}"

def log_win_to_channel(user_id, game_emoji, game_title, won_inr, mult_text=None):
    target_channel = normalize_channel_id(WINS_CHANNEL_ID)
    actor = format_win_actor(user_id)
    amt_str = f"₹{won_inr:,.2f}"
    mult_part = f" `({mult_text})`" if mult_text else ""
    msg = f"{game_emoji} *{game_title}* · *{actor}* won *{amt_str}*{mult_part}"

    res = send_message(target_channel, msg) if target_channel else None
    if (not res or not res.get("ok")) and WINS_CHANNEL_USERNAME:
        send_message(f"@{WINS_CHANNEL_USERNAME}", msg)

def current_timestamp():
    return datetime.now().strftime("%Y-%m-%d %H:%M:%S")

def generate_game_id():
    while True:
        mid = "".join(random.choices(string.ascii_uppercase + string.digits, k=7))
        tail = "".join(random.choices(string.digits, k=4))
        gid = f"XC-{mid}-{tail}"
        if gid not in game_id_registry:
            return gid

_txn_ids_in_use = set()

def generate_txn_id(prefix):
    """Deposit IDs look like DP-XXXXXXX-1234, withdraw IDs like WD-XXXXXXX-1234."""
    while True:
        mid = "".join(random.choices(string.ascii_uppercase + string.digits, k=7))
        tail = "".join(random.choices(string.digits, k=4))
        tid = f"{prefix}-{mid}-{tail}"
        if tid not in _txn_ids_in_use and tid not in game_id_registry:
            _txn_ids_in_use.add(tid)
            return tid

def find_withdrawal(txn_id):
    tid = str(txn_id or "").strip().upper()
    for w in withdrawal_history:
        if w.get("id") == tid:
            return w
    return None

deposit_orders = {}  # order_id -> deposit order (created when the payment link is made)

def find_deposit_order(txn_id):
    tid = str(txn_id or "").strip().upper()
    for o in deposit_orders.values():
        if o.get("id") == tid:
            return o
    return None

def find_deposit(txn_id):
    tid = str(txn_id or "").strip().upper()
    for d in deposit_history:
        if d.get("id") == tid:
            return d
    return None

WD_STATUS_LABELS = {
    "pending": "⏳ PENDING",
    "paid": "✅ PAID",
    "rejected": "❌ REJECTED",
    "legacy": "📁 OLD RECORD (before status tracking)",
}

def _user_label_for_report(uid):
    uname = user_usernames.get(uid)
    return f"@{uname} (`{uid}`)" if uname else f"`{uid}`"

def build_withdraw_search_report(txn_id):
    w = find_withdrawal(txn_id)
    tid = str(txn_id or "").strip().upper()
    if not w:
        return f"⚠️ No withdrawal found with ID `{tid}`."
    uid = w["user"]
    lines = [
        "🔎 *Withdrawal Details*",
        f"• *Withdraw ID:* `{w['id']}`",
        f"• *User:* {_user_label_for_report(uid)}",
        f"• *Amount:* *{format_money(w['amount'], uid)}*",
        f"• *UPI ID:* `{w.get('upi') or 'N/A'}`",
        f"• *Status:* *{WD_STATUS_LABELS.get(w.get('status'), str(w.get('status')).upper())}*",
        f"• *Requested At:* `{w.get('time') or 'N/A'}`",
    ]
    if w.get("processed_at"):
        lines.append(f"• *Processed At:* `{w['processed_at']}`")
    if w.get("processed_by"):
        lines.append(f"• *Processed By:* `{w['processed_by']}`")
    if w.get("reject_reason"):
        lines.append(f"• *Reject Reason:* _{w['reject_reason']}_")
    return "\n".join(lines)

def build_deposit_search_report(txn_id):
    d = find_deposit(txn_id)
    tid = str(txn_id or "").strip().upper()
    if not d:
        o = find_deposit_order(tid)
        if not o:
            return f"⚠️ No deposit found with ID `{tid}`."
        uid = o["user"]
        return "\n".join([
            "🔎 *Deposit Details*",
            f"• *Deposit ID:* `{o['id']}`",
            f"• *User:* {_user_label_for_report(uid)}",
            f"• *Amount:* *{format_money(o['amount'], uid)}*",
            f"• *Order ID:* `{o['order_id']}`",
            "• *Status:* *⏳ PENDING (not paid yet)*",
            f"• *Order Created At:* `{o.get('time') or 'N/A'}`",
        ])
    uid = d["user"]
    lines = [
        "🔎 *Deposit Details*",
        f"• *Deposit ID:* `{d['id']}`",
        f"• *User:* {_user_label_for_report(uid)}",
        f"• *Amount:* *{format_money(d['amount'], uid)}*",
        f"• *UTR:* `{d.get('utr') or 'N/A'}`",
    ]
    if d.get("order_id"):
        lines.append(f"• *Order ID:* `{d['order_id']}`")
    lines.append(f"• *Status:* *✅ CREDITED*")
    lines.append(f"• *Time:* `{d.get('time') or 'N/A'}`")
    return "\n".join(lines)

def build_any_search_report(raw_id):
    """/search works for game IDs (XC-...), deposit IDs (DP-...) and withdraw IDs (WD-...)."""
    tid = str(raw_id or "").strip().upper()
    if tid.startswith("WD-"):
        return build_withdraw_search_report(tid)
    if tid.startswith("DP-"):
        return build_deposit_search_report(tid)
    return build_game_search_report(tid)

def register_game_record(game_id, kind, owner_id, bet_inr, meta=None, refund_on_cancel=True):
    record = {
        "game_id": game_id,
        "kind": kind,
        "owner_id": owner_id,
        "bet_inr": bet_inr,
        "refund_on_cancel": refund_on_cancel,
        "created_at": current_timestamp(),
        "status": "active",
        "meta": meta or {}
    }
    game_id_registry[game_id] = record
    persist_game_record(game_id, record)
    return record

def mark_game_finished(game_id, status="completed", extra_meta=None):
    if game_id and game_id in game_id_registry:
        game_id_registry[game_id]["status"] = status
        game_id_registry[game_id]["ended_at"] = current_timestamp()
        if extra_meta:
            game_id_registry[game_id]["meta"].update(extra_meta)
        persist_game_record(game_id, game_id_registry[game_id])

def record_user_bet(user_id, game_label, bet_inr, pnl_inr, outcome_label, game_id=None):
    if user_id not in user_bet_logs:
        user_bet_logs[user_id] = []
    ts = current_timestamp()
    user_bet_logs[user_id].append({
        "game_id": game_id,
        "game": game_label,
        "bet": bet_inr,
        "pnl": pnl_inr,
        "outcome": outcome_label,
        "time": ts
    })
    persist_bet_log(user_id, game_label, bet_inr, pnl_inr, outcome_label, game_id, ts)
    try:
        if float(pnl_inr or 0.0) < 0:
            rakeback_on_loss(user_id, -float(pnl_inr))
    except Exception as e:
        print(f"Rakeback hook error: {e}")
    persist_user(user_id)

def resolve_user_identifier(raw_ident):
    if not raw_ident:
        return None
    cleaned = raw_ident.strip()
    if cleaned.lstrip("-").isdigit():
        return int(cleaned)
    uname = cleaned.lstrip("@").lower()
    return username_to_id.get(uname)

def register_user_identity(from_user):
    if not from_user:
        return None
    uid = from_user.get("id")
    if uid is None:
        return None
    if uid not in user_balances:
        user_balances[uid] = 0.0
        user_currency[uid] = 'INR'
    first_name = from_user.get("first_name")
    if first_name:
        user_first_names[uid] = first_name.strip()
    uname = from_user.get("username")
    if uname:
        clean_uname = uname.lstrip("@").lower()
        old_uname = user_usernames.get(uid)
        if old_uname and old_uname != clean_uname and username_to_id.get(old_uname) == uid:
            del username_to_id[old_uname]
        user_usernames[uid] = clean_uname
        username_to_id[clean_uname] = uid
    return uid

def display_sender_label(user_id):
    uname = user_usernames.get(user_id)
    if uname:
        return f"@{uname}"
    return f"`{user_id}`"

def game_style_keyboard():
    return {
        "inline_keyboard": [
            [
                {"text": "🔥 Crazy", "callback_data": "gs_style_crazy"},
                {"text": "⚡ Normal", "callback_data": "gs_style_normal"},
            ],
            [
                {"text": "❌ Cancel", "callback_data": "gs_cancel"},
            ],
        ]
    }

def rw_mode_keyboard():
    return {
        "inline_keyboard": [
            [
                {"text": "1r1w", "callback_data": "rw_pick_1r1w"},
                {"text": "2r1w", "callback_data": "rw_pick_2r1w"},
                {"text": "3r1w", "callback_data": "rw_pick_3r1w"},
            ],
            [
                {"text": "1r2w", "callback_data": "rw_pick_1r2w"},
                {"text": "2r2w", "callback_data": "rw_pick_2r2w"},
                {"text": "3r2w", "callback_data": "rw_pick_3r2w"},
            ],
            [
                {"text": "1r3w", "callback_data": "rw_pick_1r3w"},
                {"text": "2r3w", "callback_data": "rw_pick_2r3w"},
                {"text": "3r3w", "callback_data": "rw_pick_3r3w"},
            ],
            [
                {"text": "❌ Cancel", "callback_data": "gs_cancel"},
            ],
        ]
    }

def match_confirm_keyboard(chat_type="group"):
    if chat_type == "private":
        opponent_row = [
            {"text": "🤖 Against Bot", "callback_data": "mc_bot"},
        ]
    else:
        opponent_row = [
            {"text": "🤖 Against Bot", "callback_data": "mc_bot"},
            {"text": "👥 Against Player", "callback_data": "mc_player"},
        ]
    return {
        "inline_keyboard": [
            opponent_row,
            [
                {"text": "❌ Cancel", "callback_data": "gs_cancel"},
            ],
        ]
    }

def build_match_confirmation_text(user_id, emoji, bet_inr, mode, rw_label, game_id=None):
    mode_label = "CRAZY" if mode == "crazy" else "NORMAL"
    g_name = GAME_NAME_MAP.get(emoji, "Game")
    gid_line = f"🆔 *Game ID:* `{game_id}`\n" if game_id else ""
    return (
        "📋 *Match Confirmation*\n\n"
        f"{gid_line}"
        f"🎮 *Game:* {g_name} ({emoji})\n"
        f"⚙️ *Mode:* *{mode_label}*\n"
        f"🏆 *RW Format:* `{rw_label}`\n"
        f"💰 *Bet Amount:* *{format_money(bet_inr, user_id)}*\n\n"
        "Choose how you want to play:"
    )

def send_direct_pvp_challenge(chat_id, host_id, target_id, emoji, bet_inr, mode, rw_label, gid, trigger_msg_id=None):
    """Challenge sent straight to one player. Only that player can tap Accept."""
    challenge_id = uuid.uuid4().hex[:8]
    rolls_per_round, target_wins = VALID_RW_MODES[rw_label]
    mode_label = "CRAZY" if mode == "crazy" else "NORMAL"
    g_name = GAME_NAME_MAP.get(emoji, "Game")
    invite_msg = (
        "⚔️ *Player vs Player Challenge!*\n\n"
        f"🆔 *Game ID:* `{gid}`\n"
        f"👤 *Challenger:* {tag_player(host_id)}\n"
        f"🎯 *Challenged:* {tag_player(target_id)}\n"
        f"🎮 *Game:* {g_name} ({emoji})\n"
        f"⚙️ *Mode:* *{mode_label}*\n"
        f"🏆 *RW Format:* `{rw_label}` (First to *{target_wins}*)\n"
        f"💰 *Bet Each:* *{format_money(bet_inr, host_id)}*\n\n"
        f"Only {tag_player(target_id)} can tap *Accept* to start:"
    )
    kb = {
        "inline_keyboard": [
            [
                {"text": "✅ Accept Challenge", "callback_data": f"pvp_acc_{challenge_id}"},
                {"text": "❌ Cancel", "callback_data": f"pvp_can_{challenge_id}"}
            ]
        ]
    }
    sent = send_message(chat_id, invite_msg, reply_markup=kb, reply_to_message_id=trigger_msg_id)
    msg_id = sent.get("result", {}).get("message_id") if sent and sent.get("ok") else None
    open_pvp_challenges[challenge_id] = {
        "game_id": gid,
        "chat_id": chat_id,
        "message_id": msg_id,
        "host_id": host_id,
        "target_id": target_id,
        "emoji": emoji,
        "bet": bet_inr,
        "mode": mode,
        "rw_label": rw_label,
        "rolls_per_round": rolls_per_round,
        "target_wins": target_wins,
    }
    return challenge_id

def start_versus_match(chat_id, message_id, user_id, emoji, bet_inr, mode, rw_label, game_id=None, trigger_msg_id=None):
    gid = game_id or generate_game_id()
    rolls_per_round, target_wins = VALID_RW_MODES[rw_label]
    user_balances[user_id] = user_balances.get(user_id, 0.0) - bet_inr
    persist_user(user_id)
    register_game_record(
        gid,
        "bot_versus",
        user_id,
        bet_inr,
        meta={"chat_id": chat_id, "emoji": emoji, "mode": mode, "rw_label": rw_label, "trigger_msg_id": trigger_msg_id},
        refund_on_cancel=True
    )
    mode_title = "🔥 CRAZY MODE" if mode == "crazy" else "⚡ NORMAL MODE"
    player_tag = format_user_mention(user_id)
    keyboard = {
        "inline_keyboard": [
            [
                {"text": "🤖 Bot Roll First", "callback_data": "play_bot_first"}
            ]
        ]
    }
    text = (
        f"🎮 *Game Started* (`{gid}`)\n"
        f"  {emoji} | `{rw_label}` | {mode_title}\n"
        f"👤 Player: {player_tag}\n"
        f"🎯 First to *{target_wins}* round win(s) | *{rolls_per_round}* roll(s)/round\n"
        f"💰 Bet: {format_money(bet_inr, user_id)}\n\n{player_tag}, send {emoji} x{rolls_per_round}"
    )
    sent_msg_id = message_id
    if message_id:
        edit_message(chat_id, message_id, text, reply_markup=keyboard)
    else:
        res = send_message(chat_id, text, reply_markup=keyboard)
        if res and res.get("ok"):
            sent_msg_id = res["result"]["message_id"]
    remember_button_owner(chat_id, sent_msg_id, user_id)

    active_games[user_id] = {
        "game_id": gid,
        "bet": bet_inr,
        "emoji": emoji,
        "mode": mode,
        "rw_label": rw_label,
        "rolls_per_round": rolls_per_round,
        "target_wins": target_wins,
        "round_num": 1,
        "user_wins": 0,
        "bot_wins": 0,
        "current_user_rolls": [],
        "current_bot_rolls": [],
        "first_turn": None,
        "step": "selecting_turn",
        "start_chat_id": chat_id,
        "start_message_id": sent_msg_id,
        "trigger_msg_id": trigger_msg_id
    }
    schedule_pvb_turn_timeout(chat_id, user_id, active_games[user_id])

def roll_text(vals):
    """Single roll -> '4'; multiple rolls -> '3+4 = 7'."""
    total = sum(vals)
    if len(vals) <= 1:
        return f"{total}"
    return f"{'+'.join(map(str, vals))} = {total}"

def resolve_pvp_round_and_match(chat_id, match_id, pvm):
    with helper_voice(chat_id):
        return _resolve_pvp_round_and_match(chat_id, match_id, pvm)

def _resolve_pvp_round_and_match(chat_id, match_id, pvm):
    global HOUSE_BALANCE
    gid = pvm.get("game_id") or match_id
    emoji = pvm["emoji"]
    g_name = GAME_NAME_MAP.get(emoji, "Game")
    mode = pvm["mode"]
    rw_label = pvm["rw_label"]
    target_wins = pvm["target_wins"]
    bet = pvm["bet"]
    p1 = pvm["p1_id"]
    p2 = pvm["p2_id"]

    r1_vals = pvm["p1_rolls"]
    r2_vals = pvm["p2_rolls"]
    s1 = sum(r1_vals)
    s2 = sum(r2_vals)

    expr1 = "+".join(map(str, r1_vals))
    expr2 = "+".join(map(str, r2_vals))
    round_num = pvm["round_num"]
    mode_tag = "🔥 CRAZY" if mode == "crazy" else "⚡ NORMAL"

    round_winner = None
    if s1 == s2:
        r_status = "🤝 *Round Tied!* No point awarded."
    elif mode == "crazy":
        if s1 < s2:
            pvm["p1_wins"] += 1
            round_winner = p1
            r_status = f"✨ {tag_player(p1)} takes this round! (Lower sum wins)"
        else:
            pvm["p2_wins"] += 1
            round_winner = p2
            r_status = f"✨ {tag_player(p2)} takes this round! (Lower sum wins)"
    else:
        if s1 > s2:
            pvm["p1_wins"] += 1
            round_winner = p1
            r_status = f"✨ {tag_player(p1)} takes this round! (Higher sum wins)"
        else:
            pvm["p2_wins"] += 1
            round_winner = p2
            r_status = f"✨ {tag_player(p2)} takes this round! (Higher sum wins)"

    if pvm["p1_wins"] >= target_wins or pvm["p2_wins"] >= target_wins:
        winner_id = p1 if pvm["p1_wins"] >= target_wins else p2
        loser_id = p2 if winner_id == p1 else p1

        mult = float(GAME_MULTIPLIERS.get("pvp", 1.94))
        payout = bet * mult
        house_fee = max(0.0, (bet * 2) - payout)
        HOUSE_BALANCE += house_fee

        win_pnl = payout - bet
        user_balances[winner_id] = user_balances.get(winner_id, 0.0) + payout
        persist_user(winner_id)
        persist_user(loser_id)
        save_config_value("house_balance", HOUSE_BALANCE)
        update_user_stats(winner_id, emoji, bet, win_pnl, True)
        update_user_stats(loser_id, emoji, bet, -bet, False)

        label = f"PvP {g_name} ({rw_label}/{mode})"
        record_user_bet(winner_id, label, bet, win_pnl, "WON", game_id=gid)
        record_user_bet(loser_id, label, bet, -bet, "LOST", game_id=gid)
        win_actor = format_win_actor(winner_id)
        mark_game_finished(gid, "completed", extra_meta={"winner_id": winner_id, "winner_label": win_actor, "payout": payout})
        log_win_to_channel(winner_id, emoji, f"PvP {g_name}", payout, fmt_mult(mult))

        final_text = (
            f"⚔️ *Final Round Result*\n"
            f"━━━━━━━━━━━━━━━━\n"
            f"{emoji} {tag_player(p1)} — {roll_text(r1_vals)}{' ✅' if winner_id == p1 else ''}\n"
            f"{emoji} {tag_player(p2)} — {roll_text(r2_vals)}{' ✅' if winner_id == p2 else ''}\n"
            f"━━━━━━━━━━━━━━━━\n"
            f"🔥 Winner: {tag_player(winner_id)}\n"
            f"🏆 Score: {pvm['p1_wins']} : {pvm['p2_wins']} | First to {target_wins}\n"
            f"🆔 `{gid}`\n"
            f"💰 Final payout: {format_money(payout, winner_id)} ({fmt_mult(mult)})"
        )
        send_message(chat_id, final_text)

        active_pvp_games.pop(match_id, None)
        if active_games.get(p1) == match_id:
            active_games.pop(p1, None)
        if active_games.get(p2) == match_id:
            active_games.pop(p2, None)
        return

    if round_winner is None:
        winner_line = "🤝 Round Tied — no point"
    else:
        winner_line = f"🔥 Winner: {tag_player(round_winner)}"
    msg = (
        f"⚔️ *Round {round_num} Result*\n"
        f"━━━━━━━━━━━━━━━━\n"
        f"{emoji} {tag_player(p1)} — {roll_text(r1_vals)}{' ✅' if round_winner == p1 else ''}\n"
        f"{emoji} {tag_player(p2)} — {roll_text(r2_vals)}{' ✅' if round_winner == p2 else ''}\n"
        f"━━━━━━━━━━━━━━━━\n"
        f"{winner_line}\n"
        f"🏆 Score: {pvm['p1_wins']} : {pvm['p2_wins']} | First to {target_wins}\n"
        f"🆔 `{gid}`"
    )
    send_message(chat_id, msg)

    pvm["round_num"] += 1
    pvm["p1_rolls"] = []
    pvm["p2_rolls"] = []
    pvm["turn"] = p1
    send_message(
        chat_id,
        f"➡️ *Round {pvm['round_num']}* — {tag_player(p1)}, send `{emoji}` x{pvm['rolls_per_round']} in chat!"
    )
    schedule_pvp_turn_timeout(chat_id, match_id, pvm)

DECK_RANKS = ["A", "2", "3", "4", "5", "6", "7", "8", "9", "10", "J", "Q", "K"]
DECK_SUITS = ["♠", "♥", "♦", "♣"]

def draw_card():
    rank = random.choice(DECK_RANKS)
    suit = random.choice(DECK_SUITS)
    return f"{rank}{suit}"

def card_value(card):
    rank = card[:-1]
    if rank == "A":
        return 11
    if rank in ["K", "Q", "J", "10"]:
        return 10
    return int(rank)

def calculate_hand_total(cards):
    total = sum(card_value(c) for c in cards)
    aces = sum(1 for c in cards if c[:-1] == "A")
    while total > 21 and aces > 0:
        total -= 10
        aces -= 1
    return total

def format_cards(cards):
    return " ".join(f"`{c}`" for c in cards)

def bj_action_keyboard(can_double=True):
    row1 = [
        {"text": "🃏 Hit", "callback_data": "bj_hit"},
        {"text": "🛑 Stand", "callback_data": "bj_stand"}
    ]
    rows = [row1]
    if can_double:
        rows.append([{"text": "⚡ Double", "callback_data": "bj_double"}])
    return {"inline_keyboard": rows}

def format_money(amount_in_inr, user_id):
    curr = user_currency.get(user_id, 'INR')
    if curr == 'USDT':
        val = amount_in_inr / EXCHANGE_RATE
        return f"${val:.2f} USDT"
    else:
        return f"₹{amount_in_inr:.2f}"

pending_amount_prompts = {}
AMOUNT_PROMPT_SECONDS = 120
AMOUNT_FIRST_GAMES = ['/dr', '/bj', '/mines', '/tower', '/limbo']
TOKEN_AMOUNT_GAMES = ['/dice', '/dart', '/foot', '/basket', '/bowl', '/7up']

def game_command_missing_amount(text, user_id):
    """True when a game command was sent without any bet amount."""
    parts = text.split()
    if not parts:
        return False
    cmd = parts[0].lower().split('@')[0]
    if cmd in AMOUNT_FIRST_GAMES:
        return len(parts) < 2
    if cmd in TOKEN_AMOUNT_GAMES:
        for tok in parts[1:]:
            low = tok.lower()
            if low.startswith('@') or re.fullmatch(r"\d+r\d+w", low):
                continue
            if cmd == '/7up' and normalize_7up_choice(tok) is not None:
                continue
            if parse_user_amount(tok, user_id) is not None:
                return False
        return True
    return False

ALL_AMOUNT_WORDS = ("all", "max", "allin")
HALF_AMOUNT_WORDS = ("half",)

def is_all_half_word(text_val):
    """True when the player typed 'all' or 'half' instead of a number."""
    low = str(text_val or "").strip().lower()
    return low in ALL_AMOUNT_WORDS or low in HALF_AMOUNT_WORDS

def _floor2(val):
    return math.floor(float(val) * 100 + 1e-9) / 100.0

def resolve_all_half(text_val, base_inr):
    """'all' -> full base amount, 'half' -> half of it (INR, rounded down to paise).
    Returns None for anything else, or when the result is 0."""
    low = str(text_val or "").strip().lower()
    base = max(0.0, float(base_inr or 0.0))
    if low in ALL_AMOUNT_WORDS:
        val = _floor2(base)
    elif low in HALF_AMOUNT_WORDS:
        val = _floor2(base / 2.0)
    else:
        return None
    return val if val > 0 else None

def parse_user_amount(text_val, user_id, allow_all_half=True):
    """Amount typed by a player -> INR.
    Accepts a manual number (₹ / commas OK, USDT users get converted) or
    'all' / 'half' = full / half of that user's current balance."""
    if is_all_half_word(text_val):
        if not allow_all_half:
            return None
        return resolve_all_half(text_val, user_balances.get(user_id, 0.0))
    try:
        val = float(str(text_val).replace('₹', '').replace(',', '').strip())
        if not math.isfinite(val) or val <= 0:
            return None
        curr = user_currency.get(user_id, 'INR')
        if curr == 'USDT':
            return val * EXCHANGE_RATE
        return val
    except Exception:
        return None


# =====================================================================
# 🤖 HELPER BOTS — up to 3 helper bots throw every emoji in groups and
# send the round / final round messages, so the main bot has less load.
# Admin manages them with /helper (token is saved in the DB, no file edits).
# Main bot throws only as an emergency backup (no helper could throw)
# and in player DMs (Telegram does not let helpers post in someone's DM).
# =====================================================================
import hashlib as _hb_hashlib
import hmac as _hb_hmac

MAX_HELPERS = 3
HELPER_BOTS = []            # [{"id", "username", "token", "enabled", "hook"}]
HELPER_THROW_WAIT = 4       # seconds to wait for a rate-limited helper before backup
_helper_lock = threading.Lock()
_helper_rr = [0]
_helper_cooldown = {}       # helper_id -> unix time it can be used again (Telegram 429)
_helper_chat_block = {}     # (helper_id, chat_id) -> unix time (helper not in that chat)
_helper_backup_note = {}    # chat_id -> last time admin was told main bot threw
_tg_ctx = threading.local() # per-request: which bot answers / which helper speaks

def _api_base():
    return getattr(_tg_ctx, "api", None) or TELEGRAM_API_URL

def tg_url(method):
    return f"{_api_base()}/{method}"

def helper_api(h):
    return f"https://api.telegram.org/bot{h['token']}"

def helper_ids():
    return {h.get("id") for h in HELPER_BOTS}

def save_helpers():
    save_config_value("helper_bots", HELPER_BOTS)

def helper_hook_secret(token):
    return _hb_hashlib.sha256(f"xyren-helper:{token}".encode()).hexdigest()

def _md_safe(t):
    return str(t).replace('_', '\\_').replace('*', '\\*').replace('`', '\\`').replace('[', '\\[')

def _helpers_for_chat(chat_id):
    """Enabled helpers usable in this chat, in round-robin order (spreads the load)."""
    now = time.time()
    with _helper_lock:
        live = [h for h in HELPER_BOTS if h.get("enabled") and _helper_chat_block.get((h.get("id"), chat_id), 0) <= now]
        if not live:
            return []
        start = _helper_rr[0] % len(live)
        _helper_rr[0] += 1
    return live[start:] + live[:start]

_HELPER_NOT_IN_CHAT = ("chat not found", "not a member", "kicked", "forbidden", "rights", "chat_send", "initiate", "blocked", "restricted")

def _helper_post(h, method, payload, timeout=5):
    try:
        data = requests.post(f"{helper_api(h)}/{method}", json=payload, timeout=timeout).json()
    except Exception as e:
        print(f"Helper @{h.get('username')} {method} error: {e}")
        return None
    if not data.get("ok"):
        code = data.get("error_code")
        desc = str(data.get("description", "")).lower()
        if code == 429:
            wait = (data.get("parameters") or {}).get("retry_after", 3)
            _helper_cooldown[h.get("id")] = time.time() + float(wait)
        elif code == 401:
            h["enabled"] = False
            save_helpers()
            try:
                requests.post(f"{TELEGRAM_API_URL}/sendMessage", json={"chat_id": ADMIN_USER_ID, "text": f"⚠️ Helper @{h.get('username')} token stopped working (revoked?). It is now OFF. Re-add it with /helper add <token>."}, timeout=5)
            except Exception:
                pass
        elif code in (400, 403) and any(k in desc for k in _HELPER_NOT_IN_CHAT):
            _helper_chat_block[(h.get("id"), payload.get("chat_id"))] = time.time() + 600
        print(f"Helper @{h.get('username')} {method} failed: {data.get('description')}")
    return data

def _main_throw(payload):
    """Main bot dice throw. Retries up to 3 times (handles Telegram 429 / network blips)
    so a real Telegram dice is used instead of the random fallback."""
    for _attempt in range(3):
        try:
            data = requests.post(f"{TELEGRAM_API_URL}/sendDice", json=payload, timeout=8).json()
            if data and data.get("ok") and (data.get("result") or {}).get("dice"):
                return data
            retry_after = ((data or {}).get("parameters") or {}).get("retry_after")
            print(f"sendDice not ok (attempt {_attempt + 1}): {data}")
            time.sleep(min(float(retry_after), 3.0) if retry_after else 0.5)
        except Exception as e:
            print(f"Error sending game (attempt {_attempt + 1}): {e}")
            time.sleep(0.5)
    return None

def _note_backup_throw(chat_id, why):
    now = time.time()
    if now - _helper_backup_note.get(chat_id, 0) < 600:
        return
    _helper_backup_note[chat_id] = now
    try:
        requests.post(
            f"{TELEGRAM_API_URL}/sendMessage",
            json={"chat_id": ADMIN_USER_ID, "text": f"⚠️ Main bot threw an emoji as backup in chat {chat_id} ({why}). Check /helper — add the helpers to that group or turn them on."},
            timeout=5,
        )
    except Exception:
        pass

class helper_voice:
    """Inside this block, messages to `chat_id` go out from a helper bot.
    If the helper can't send, the main bot sends it instead (no message is lost)."""
    def __init__(self, chat_id):
        self.chat_id = chat_id
    def __enter__(self):
        self.prev = (getattr(_tg_ctx, "voice", None), getattr(_tg_ctx, "voice_chat", None))
        pick = None
        if isinstance(self.chat_id, int) and self.chat_id < 0:
            now = time.time()
            for h in _helpers_for_chat(self.chat_id):
                if _helper_cooldown.get(h.get("id"), 0) <= now:
                    pick = h
                    break
        _tg_ctx.voice = pick
        _tg_ctx.voice_chat = self.chat_id if pick else None
        return self
    def __exit__(self, *exc):
        _tg_ctx.voice, _tg_ctx.voice_chat = self.prev
        return False

_EDIT_WRONG_BOT = ("can't be edited", "message to edit not found", "message_id_invalid", "message can't be")

def _tg_edit(method, payload, timeout=5):
    """Edit a message. If this bot didn't send it, try the other bots (main + helpers)."""
    bases = [_api_base(), TELEGRAM_API_URL] + [helper_api(h) for h in HELPER_BOTS]
    seen = set()
    data = None
    for base in bases:
        if base in seen:
            continue
        seen.add(base)
        body = dict(payload)
        try:
            data = requests.post(f"{base}/{method}", json=body, timeout=timeout).json()
            if not data.get("ok") and "parse" in str(data.get("description", "")).lower() and "parse_mode" in body:
                body.pop("parse_mode", None)
                data = requests.post(f"{base}/{method}", json=body, timeout=timeout).json()
        except Exception as e:
            print(f"Error {method}: {e}")
            return None
        if data.get("ok"):
            return data
        desc = str(data.get("description", "")).lower()
        if not any(k in desc for k in _EDIT_WRONG_BOT):
            return data
    return data

def _auto_reply_id(chat_id, reply_to_message_id):
    """Every bot answer is sent as a reply to the user's message that triggered it."""
    if reply_to_message_id:
        return reply_to_message_id
    if chat_id is not None and getattr(_tg_ctx, "reply_chat", None) == chat_id:
        return getattr(_tg_ctx, "reply_mid", None)
    return None

def _has_fair_link(text):
    url = os.environ.get("VERIFY_URL")
    return bool(url and text and url.rstrip("/") in text)

def send_message(chat_id, text, reply_markup=None, reply_to_message_id=None):
    payload = {"chat_id": chat_id, "text": text, "parse_mode": "Markdown"}
    if reply_markup:
        payload["reply_markup"] = reply_markup
    reply_to_message_id = _auto_reply_id(chat_id, reply_to_message_id)
    if reply_to_message_id:
        payload["reply_to_message_id"] = reply_to_message_id
        payload["allow_sending_without_reply"] = True
    if _has_fair_link(text):
        payload["link_preview_options"] = {"is_disabled": True}

    # Round / final round messages: sent by a helper bot.
    voice = getattr(_tg_ctx, "voice", None)
    if voice and voice.get("enabled") and getattr(_tg_ctx, "voice_chat", None) == chat_id and (not reply_markup or voice.get("hook")):
        body = dict(payload)
        data = _helper_post(voice, "sendMessage", body)
        if data and not data.get("ok") and "parse" in str(data.get("description", "")).lower():
            body.pop("parse_mode", None)
            data = _helper_post(voice, "sendMessage", body)
        if data and data.get("ok"):
            return data

    bases = [_api_base()]
    if bases[0] != TELEGRAM_API_URL:
        bases.append(TELEGRAM_API_URL)
    data = None
    for base in bases:
        body = dict(payload)
        try:
            data = requests.post(f"{base}/sendMessage", json=body, timeout=5).json()
            if not data.get("ok") and "parse" in str(data.get("description", "")).lower():
                body.pop("parse_mode", None)
                data = requests.post(f"{base}/sendMessage", json=body, timeout=5).json()
            if data.get("ok"):
                return data
        except Exception as e:
            print(f"Error sending message: {e}")
            data = None
    return data

def edit_message(chat_id, message_id, text, reply_markup=None):
    payload = {
        "chat_id": chat_id,
        "message_id": message_id,
        "text": text,
        "parse_mode": "Markdown"
    }
    if reply_markup:
        payload["reply_markup"] = reply_markup
    else:
        payload["reply_markup"] = {"inline_keyboard": []}
    if _has_fair_link(text):
        payload["link_preview_options"] = {"is_disabled": True}
    data = _tg_edit("editMessageText", payload, timeout=5)
    if data is None:
        print("Error editing message")
    return data

def answer_callback(callback_query_id, text=""):
    url = tg_url("answerCallbackQuery")
    payload = {"callback_query_id": callback_query_id, "text": text}
    try:
        requests.post(url, json=payload, timeout=3)
    except Exception as e:
        print(f"Error answering callback: {e}")

# ===================== 🎲 /dr SELF MODE =====================
# /dr <amount> <high|low|odd|even|1,3,5> self
# The player throws the 🎲 himself. If he does not within DR_SELF_TIMEOUT seconds, the bot throws
# for him and the game is resolved. Forwarded dice never reach this code (they are banned earlier).
DR_SELF_TIMEOUT = 60

def dr_choice_valid(arg):
    if arg in ("high", "low", "odd", "even"):
        return True
    try:
        nums = [int(n.strip()) for n in str(arg).split(",")]
        return all(1 <= n <= 6 for n in nums) and len(nums) <= 5 and len(nums) == len(set(nums))
    except Exception:
        return False

def dr_pick_label(arg):
    if arg in ("high", "low", "odd", "even"):
        return arg.upper()
    return " • ".join(str(int(n.strip())) for n in str(arg).split(","))

def resolve_dr_game(chat_id, user_id, gid, bet_inr, arg, dice_val, self_mode=False, reply_to_message_id=None):
    """Settles a /dr prediction with the given dice value and posts the report."""
    global HOUSE_BALANCE
    rec = game_id_registry.get(gid)
    if self_mode and rec and rec.get("status") != "active":
        return   # cancelled meanwhile (admin /cancel) -> never pay out

    is_win = False
    if arg in ("high", "low", "odd", "even"):
        if arg == "high" and dice_val in (4, 5, 6): is_win = True
        elif arg == "low" and dice_val in (1, 2, 3): is_win = True
        elif arg == "odd" and dice_val in (1, 3, 5): is_win = True
        elif arg == "even" and dice_val in (2, 4, 6): is_win = True
        multiplier = float(GAME_MULTIPLIERS.get("dr", 1.92))
        win_desc = f"Prediction: {arg.upper()}"
    else:
        nums = [int(n.strip()) for n in str(arg).split(",")]
        if dice_val in nums: is_win = True
        dr_num_map = GAME_MULTIPLIERS.get("dr_nums", {1: 5.56, 2: 2.88, 3: 1.92, 4: 1.44, 5: 1.15})
        multiplier = float(dr_num_map.get(len(nums), 1.0))
        win_desc = f"Numbers: {nums}"

    if is_win:
        win_amt = bet_inr * multiplier
        profit_inr = win_amt - bet_inr
        user_balances[user_id] = user_balances.get(user_id, 0.0) + win_amt
        HOUSE_BALANCE -= profit_inr
        persist_user(user_id)
        save_config_value("house_balance", HOUSE_BALANCE)
        update_user_stats(user_id, "prediction", bet_inr, profit_inr, True)
        record_user_bet(user_id, f"Prediction ({win_desc})", bet_inr, profit_inr, "WON", game_id=gid)
        mark_game_finished(gid, "completed", extra_meta={"outcome": "WON", "pnl": profit_inr})
        log_win_to_channel(user_id, "🔮", "Predict", win_amt, fmt_mult(multiplier))
        result_text = build_dr_result_message(gid, dice_val, arg, True, win_amt=win_amt, multiplier=multiplier, user_id=user_id)
    else:
        profit_inr = -bet_inr
        HOUSE_BALANCE += bet_inr
        persist_user(user_id)
        save_config_value("house_balance", HOUSE_BALANCE)
        update_user_stats(user_id, "prediction", bet_inr, profit_inr, False)
        record_user_bet(user_id, f"Prediction ({win_desc})", bet_inr, profit_inr, "LOST", game_id=gid)
        mark_game_finished(gid, "completed", extra_meta={"outcome": "LOST", "pnl": profit_inr})
        result_text = build_dr_result_message(gid, dice_val, arg, False, user_id=user_id)

    pm_payload = {"kind": "dr", "owner_id": user_id, "bet": bet_inr, "dr_arg": arg, "dr_self": bool(self_mode)}
    send_message(chat_id, result_text, reply_markup=create_post_match_keyboard(user_id, pm_payload),
                 reply_to_message_id=reply_to_message_id)

def _dr_self_timeout(user_id, token):
    with get_turn_lock(f"dr_{user_id}"):
        g = active_dr_self_games.get(user_id)
        if not g or g.get("token") != token:
            return
        active_dr_self_games.pop(user_id, None)
        g["token"] = None
    chat_id, gid = g["chat_id"], g["game_id"]
    try:
        send_message(chat_id, f"⏰ *Timeout* (`{gid}`) — {format_user_mention(user_id)}, bot is throwing 🎲 for you...")
        res = send_animated_game(chat_id, "🎲")
        dice_val = res["result"]["dice"]["value"] if res and "result" in res else random.randint(1, 6)
        time.sleep(1)
        resolve_dr_game(chat_id, user_id, gid, g["bet_inr"], g["arg"], dice_val, self_mode=True)
    except Exception as e:
        print(f"dr self timeout error ({gid}): {e}")
        # never leave the player's stake stuck
        rec = game_id_registry.get(gid)
        if rec and rec.get("status") == "active":
            try:
                cancel_game_by_id(gid)
                send_message(chat_id, f"⚠️ Game `{gid}` could not be completed and was cancelled. Stake refunded.")
            except Exception as e2:
                print(f"dr self refund error ({gid}): {e2}")

def start_dr_self_game(chat_id, user_id, bet_inr, arg, reply_to_message_id=None):
    """Takes the bet and waits for the player's own 🎲 (or the timeout)."""
    gid = generate_game_id()
    user_balances[user_id] = user_balances.get(user_id, 0.0) - bet_inr
    persist_user(user_id)
    meta = {"mode": "self", "chat_id": chat_id}
    if arg in ("high", "low", "odd", "even"):
        meta["choice"] = arg
    else:
        meta["nums"] = [int(n.strip()) for n in arg.split(",")]
    register_game_record(gid, "prediction", user_id, bet_inr, meta=meta, refund_on_cancel=True)

    token = uuid.uuid4().hex
    active_dr_self_games[user_id] = {
        "game_id": gid, "chat_id": chat_id, "bet_inr": bet_inr, "arg": arg, "token": token,
    }
    send_message(
        chat_id,
        f"🎲 *Prediction — Self Mode* (`{gid}`)\n"
        f"🎯 Pick: *{dr_pick_label(arg)}*\n"
        f"💰 Bet: *{format_money(bet_inr, user_id)}*\n\n"
        f"👉 {format_user_mention(user_id)}, send 🎲 within *{DR_SELF_TIMEOUT} seconds*, else the bot will throw for you!",
        reply_to_message_id=reply_to_message_id,
    )
    t = threading.Timer(float(DR_SELF_TIMEOUT), _dr_self_timeout, args=(user_id, token))
    t.daemon = True
    t.start()
    return gid

def handle_dr_self_dice(message, chat_id, user_id):
    """Player's own 🎲 for a waiting /dr self game. Returns True if it was used."""
    g = active_dr_self_games.get(user_id)
    if not g or g["chat_id"] != chat_id:
        return False
    dice = message.get("dice") or {}
    if dice.get("emoji") != "🎲":
        return False
    with get_turn_lock(f"dr_{user_id}"):
        g = active_dr_self_games.get(user_id)
        if not g or g.get("token") is None:
            return True
        active_dr_self_games.pop(user_id, None)
        g["token"] = None
    time.sleep(3)   # let the dice animation finish before the result is shown
    resolve_dr_game(chat_id, user_id, g["game_id"], g["bet_inr"], g["arg"], int(dice.get("value", 1)),
                    self_mode=True, reply_to_message_id=message.get("message_id"))
    return True

# ===================== 🌧 RAIN (group giveaway, always in USDT) =====================
# /rain <amount> <required_wager> <required_deposit> <time_seconds>   (all money in USDT)
# The rain amount is taken from the host's balance. Players tap "Join Rain" (needs the
# name tag in their display name + the wager/deposit of the last 30 days). When the time
# ends the amount is split equally between everyone who joined; if nobody joined it goes
# back to the host.
from datetime import timedelta as _rain_td

RAIN_REQUIRED_NAME_TAG = "@PaisaPlayz"   # must be inside the joiner's display name
RAIN_MIN_USDT = 0.10
RAIN_MIN_SECONDS = 10
RAIN_MAX_SECONDS = 3600
RAIN_WINDOW_DAYS = 30
RAIN_UNPIN_ON_END = False   # True = unpin the rain message when the rain ends
# Money source: OWNER (ADMIN_USER_ID) -> House Balance. Admins / normal users -> their own balance.

def fmt_usdt(amount_inr):
    val = float(amount_inr) / EXCHANGE_RATE
    if val == 0 or val >= 0.01:
        return f"${val:.2f} USDT"
    return f"${val:.4f} USDT"

def _rain_ts(value):
    try:
        return datetime.strptime(str(value), "%Y-%m-%d %H:%M:%S")
    except Exception:
        return None

def rain_recent_wager_inr(uid, days=RAIN_WINDOW_DAYS):
    cutoff = datetime.now() - _rain_td(days=days)
    total = 0.0
    for b in reversed(user_bet_logs.get(uid, [])):
        t = _rain_ts(b.get("time"))
        if t is None:
            continue
        if t < cutoff:
            break
        total += float(b.get("bet") or 0.0)
    return total

def rain_recent_deposit_inr(uid, days=RAIN_WINDOW_DAYS):
    cutoff = datetime.now() - _rain_td(days=days)
    total = 0.0
    for d in reversed(deposit_history):
        t = _rain_ts(d.get("time"))
        if t is None:
            continue
        if t < cutoff:
            break
        if d.get("user") == uid:
            total += float(d.get("amount") or 0.0)
    return total

def rain_name_ok(from_user):
    full = f"{from_user.get('first_name') or ''} {from_user.get('last_name') or ''}"
    return RAIN_REQUIRED_NAME_TAG.lower() in full.lower()

def answer_callback_alert(callback_query_id, text):
    try:
        requests.post(tg_url("answerCallbackQuery"),
                      json={"callback_query_id": callback_query_id, "text": text, "show_alert": True},
                      timeout=3)
    except Exception as e:
        print(f"Error answering callback alert: {e}")

def _rain_money_arg(raw):
    try:
        val = float(str(raw).replace("$", "").replace(",", "").strip())
        if not math.isfinite(val) or val < 0:
            return None
        return val
    except Exception:
        return None

def _rain_seconds_arg(raw):
    raw = str(raw).strip().lower()
    mult = 1
    if raw.endswith("m"):
        mult, raw = 60, raw[:-1]
    elif raw.endswith("s"):
        raw = raw[:-1]
    try:
        val = float(raw)
        if not math.isfinite(val) or val <= 0:
            return None
        return int(val * mult)
    except Exception:
        return None

def _rain_req_line(label, inr):
    return f"{label}: *{fmt_usdt(inr)}*" if inr > 0 else f"{label}: *None*"

def pin_group_message(chat_id, message_id):
    """Pins a message (the bot needs the 'Pin messages' admin right; failure is harmless)."""
    try:
        r = requests.post(f"{TELEGRAM_API_URL}/pinChatMessage",
                          json={"chat_id": chat_id, "message_id": message_id}, timeout=5).json()
        if not r.get("ok"):
            print(f"pinChatMessage failed in {chat_id}: {r.get('description')}")
        return bool(r.get("ok"))
    except Exception as e:
        print(f"pinChatMessage error: {e}")
        return False

def unpin_group_message(chat_id, message_id):
    try:
        requests.post(f"{TELEGRAM_API_URL}/unpinChatMessage",
                      json={"chat_id": chat_id, "message_id": message_id}, timeout=5)
    except Exception as e:
        print(f"unpinChatMessage error: {e}")

def rain_source_for(user_id):
    return "house" if user_id == ADMIN_USER_ID else "user"

def rain_take_funds(source, user_id, amount_inr):
    """Takes the rain amount. Returns (ok, available_inr)."""
    global HOUSE_BALANCE
    if source == "house":
        if HOUSE_BALANCE + 1e-9 < amount_inr:
            return False, HOUSE_BALANCE
        HOUSE_BALANCE -= amount_inr
        save_config_value("house_balance", HOUSE_BALANCE)
        return True, HOUSE_BALANCE
    bal = user_balances.get(user_id, 0.0)
    if bal + 1e-9 < amount_inr:
        return False, bal
    user_balances[user_id] = bal - amount_inr
    persist_user(user_id)
    return True, user_balances[user_id]

def rain_return_funds(source, user_id, amount_inr):
    global HOUSE_BALANCE
    if source == "house":
        HOUSE_BALANCE += amount_inr
        save_config_value("house_balance", HOUSE_BALANCE)
    else:
        user_balances[user_id] = user_balances.get(user_id, 0.0) + amount_inr
        persist_user(user_id)

def build_rain_text(rain, ended=False, joined=0, share_inr=0.0, cancelled_note=None):
    head = "🌧 *RAIN ENDED!*" if ended else "🌧 *RAIN STARTED!*"
    lines = [
        f"{head} (`{rain['rain_id']}`)",
        "",
        f"💰 Rain Amount: *{fmt_usdt(rain['amount_inr'])}*",
        f"👤 Hosted by: {format_user_mention(rain['host_id'])}",
        _rain_req_line("📊 Required Wager (30 days)", rain["req_wager_inr"]),
        _rain_req_line("💳 Required Deposit (30 days)", rain["req_deposit_inr"]),
        f"🏷 Name must contain: `{RAIN_REQUIRED_NAME_TAG}`",
    ]
    if not ended:
        lines.append(f"⏳ Time: *{rain['seconds']}s*")
        lines.append("")
        lines.append("Tap *Join Rain* below if you meet the requirements!")
    else:
        lines.append("")
        lines.append(f"👥 Players Joined: *{joined}*")
        if joined > 0:
            lines.append(f"🎁 Each Player Got: *{fmt_usdt(share_inr)}*")
        else:
            lines.append("😔 Nobody joined — the rain amount was returned to the host.")
    return "\n".join(lines)

def finish_rain(rain_id):
    rain = active_rains.get(rain_id)
    if not rain:
        return
    with rain["lock"]:
        if rain["done"]:
            return
        rain["done"] = True
        joined = list(rain["joined"])
    active_rains.pop(rain_id, None)

    n = len(joined)
    amount_inr = rain["amount_inr"]
    share_inr = (amount_inr / n) if n else 0.0

    if n:
        for uid in joined:
            user_balances[uid] = user_balances.get(uid, 0.0) + share_inr
            try:
                persist_user(uid)
            except Exception as e:
                print(f"rain credit persist error {uid}: {e}")
    else:
        try:
            rain_return_funds(rain["source"], rain["host_id"], amount_inr)
        except Exception as e:
            print(f"rain refund error: {e}")

    mark_game_finished(rain_id, "completed", extra_meta={"joined": n, "share_inr": share_inr})

    try:
        edit_message(rain["chat_id"], rain["message_id"],
                     build_rain_text(rain, ended=True, joined=n, share_inr=share_inr))
    except Exception as e:
        print(f"rain final edit error: {e}")

    if RAIN_UNPIN_ON_END and rain.get("message_id"):
        unpin_group_message(rain["chat_id"], rain["message_id"])

    for uid in joined:
        try:
            send_message(
                uid,
                "🌧 *Rain Collected!* 🎉\n\n"
                f"🆔 Rain ID: `{rain_id}`\n"
                f"💰 You received: *{fmt_usdt(share_inr)}*\n"
                f"👤 Hosted by: {format_user_mention(rain['host_id'])}\n"
                f"🏦 New Balance: {format_money(user_balances.get(uid, 0.0), uid)}"
            )
        except Exception as e:
            print(f"rain DM error {uid}: {e}")
        time.sleep(0.05)

def handle_rain_command(chat_id, chat_type, user_id, text):
    if chat_type not in ("group", "supergroup"):
        send_message(chat_id, "⚠️ Rain works only in groups.")
        return
    parts = text.split()
    usage = (
        "⚠️ Usage: `/rain <amount> <required_wager> <required_deposit> <time_seconds>`\n"
        "Example: `/rain 5 10 0 60`\n"
        "All amounts are in *USDT*. Wager and deposit are checked for the last 30 days (use `0` for no requirement)."
    )
    if len(parts) != 5:
        send_message(chat_id, usage)
        return
    amount_usdt = _rain_money_arg(parts[1])
    wager_usdt = _rain_money_arg(parts[2])
    deposit_usdt = _rain_money_arg(parts[3])
    seconds = _rain_seconds_arg(parts[4])
    if amount_usdt is None or wager_usdt is None or deposit_usdt is None or seconds is None:
        send_message(chat_id, usage)
        return
    if amount_usdt < RAIN_MIN_USDT:
        send_message(chat_id, f"⚠️ Minimum rain amount is *${RAIN_MIN_USDT:.2f} USDT*.")
        return
    if seconds < RAIN_MIN_SECONDS or seconds > RAIN_MAX_SECONDS:
        send_message(chat_id, f"⚠️ Rain time must be between *{RAIN_MIN_SECONDS}* and *{RAIN_MAX_SECONDS}* seconds.")
        return

    amount_inr = amount_usdt * EXCHANGE_RATE
    source = rain_source_for(user_id)
    rain_id = generate_game_id()
    ok, available = rain_take_funds(source, user_id, amount_inr)
    if not ok:
        label = "House Balance" if source == "house" else "Your Balance"
        send_message(chat_id, f"❌ *Insufficient Balance!*\n💰 {label}: *{fmt_usdt(available)}*\n🌧 Rain Amount: *{fmt_usdt(amount_inr)}*")
        return
    rain = {
        "rain_id": rain_id, "chat_id": chat_id, "message_id": None, "host_id": user_id,
        "amount_inr": amount_inr, "req_wager_inr": wager_usdt * EXCHANGE_RATE,
        "req_deposit_inr": deposit_usdt * EXCHANGE_RATE, "seconds": seconds,
        "source": source, "joined": set(), "done": False, "lock": threading.Lock(),
    }
    register_game_record(
        rain_id, "rain", user_id, amount_inr,
        meta={"chat_id": chat_id, "seconds": seconds, "source": source,
              "req_wager_inr": rain["req_wager_inr"], "req_deposit_inr": rain["req_deposit_inr"]},
        refund_on_cancel=True,
    )
    active_rains[rain_id] = rain

    kb = {"inline_keyboard": [[{"text": "🌧 Join Rain", "callback_data": f"rain_join_{rain_id}"}]]}
    sent = send_message(chat_id, build_rain_text(rain), reply_markup=kb)
    msg_id = sent.get("result", {}).get("message_id") if sent and sent.get("ok") else None
    if not msg_id:
        active_rains.pop(rain_id, None)
        rain_return_funds(source, user_id, amount_inr)
        mark_game_finished(rain_id, "cancelled")
        send_message(chat_id, "⚠️ Could not start the rain. The amount was returned.")
        return
    rain["message_id"] = msg_id
    pin_group_message(chat_id, msg_id)

    t = threading.Timer(float(seconds), finish_rain, args=(rain_id,))
    t.daemon = True
    t.start()

def handle_rain_join(callback_query_id, callback_data, chat_id, message_id, from_user):
    user_id = from_user.get("id")
    rain_id = callback_data.replace("rain_join_", "", 1)
    rain = active_rains.get(rain_id)
    if not rain:
        answer_callback(callback_query_id, "This rain has already ended.")
        remove_inline_keyboard(chat_id, message_id)
        return
    if from_user.get("is_bot"):
        return
    register_user_identity(from_user)

    if user_id in banned_users:
        answer_callback_alert(callback_query_id, "⛔ You are banned from using this bot.")
        return
    if MAINTENANCE_MODE and user_id not in admin_list:
        answer_callback(callback_query_id, "🛠 Bot is under maintenance.")
        return
    if user_id == rain["host_id"]:
        answer_callback(callback_query_id, "You cannot join your own rain!")
        return
    if user_id in rain["joined"]:
        answer_callback(callback_query_id, "You already joined this rain ✅")
        return
    if not rain_name_ok(from_user):
        answer_callback_alert(callback_query_id, f"❌ Add {RAIN_REQUIRED_NAME_TAG} in your Telegram display name to join this rain.")
        return
    if rain["req_wager_inr"] > 0:
        w = rain_recent_wager_inr(user_id)
        if w + 1e-9 < rain["req_wager_inr"]:
            answer_callback_alert(callback_query_id,
                f"❌ Wager requirement not met.\nRequired (30 days): {fmt_usdt(rain['req_wager_inr'])}\nYour wager: {fmt_usdt(w)}")
            return
    if rain["req_deposit_inr"] > 0:
        d = rain_recent_deposit_inr(user_id)
        if d + 1e-9 < rain["req_deposit_inr"]:
            answer_callback_alert(callback_query_id,
                f"❌ Deposit requirement not met.\nRequired (30 days): {fmt_usdt(rain['req_deposit_inr'])}\nYour deposits: {fmt_usdt(d)}")
            return

    with rain["lock"]:
        if rain["done"]:
            answer_callback(callback_query_id, "This rain has already ended.")
            return
        if user_id in rain["joined"]:
            answer_callback(callback_query_id, "You already joined this rain ✅")
            return
        rain["joined"].add(user_id)
    answer_callback(callback_query_id, "✅ You joined the rain!")

# ===================== 🚫 FORWARDED DICE / EMOJI PROTECTION =====================
# A dice emoji that is FORWARDED from another chat is never a real throw made inside
# this chat. It is never counted as a roll, and the sender is banned from the bot AND
# from the group. Owner/admins are only ignored (not banned) so they can test safely.
_FORWARD_KEYS = (
    "forward_origin", "forward_from", "forward_from_chat", "forward_from_message_id",
    "forward_sender_name", "forward_signature", "forward_date",
)

def is_forwarded_message(message):
    if message.get("is_automatic_forward"):
        return False   # channel post mirrored into the linked discussion group
    return any(message.get(k) for k in _FORWARD_KEYS)

def ban_from_group(chat_id, target_user_id):
    try:
        r = requests.post(
            f"{TELEGRAM_API_URL}/banChatMember",
            json={"chat_id": chat_id, "user_id": target_user_id, "revoke_messages": False},
            timeout=5,
        ).json()
        if not r.get("ok"):
            print(f"banChatMember failed for {target_user_id} in {chat_id}: {r.get('description')}")
        return bool(r.get("ok"))
    except Exception as e:
        print(f"banChatMember error: {e}")
        return False

def cancel_user_games_on_ban(user_id):
    """Cancels EVERY live game, open challenge and setup of this user (stake is refunded
    through the normal cancel logic) so no timer can auto-throw for a banned player.
    Returns a list of cancel-status texts."""
    results = []

    # open PvP challenges (no stake taken yet) + half-finished game setup
    for cid, ch in list(open_pvp_challenges.items()):
        if user_id in (ch.get("host_id"), ch.get("target_id")):
            open_pvp_challenges.pop(cid, None)
            if ch.get("game_id"):
                mark_game_finished(ch["game_id"], "cancelled")
            if ch.get("message_id"):
                try:
                    edit_message(ch.get("chat_id"), ch["message_id"], f"❌ PvP Challenge `{cid}` cancelled (player banned).")
                except Exception as e:
                    print(f"challenge edit error: {e}")
    setup = pending_game_setup.pop(user_id, None)
    if setup and setup.get("game_id") in game_id_registry:
        mark_game_finished(setup["game_id"], "cancelled")

    gids = []
    def _add(gid):
        if gid and gid not in gids:
            gids.append(gid)

    pvp_ref = None
    ref = active_games.get(user_id)
    if isinstance(ref, dict):
        _add(ref.get("game_id"))
    elif isinstance(ref, str):
        pvp_ref = ref
        _add((active_pvp_games.get(ref) or {}).get("game_id") or ref)
    for store in (active_7up_games, active_bj_games, active_mines_games, active_tower_games, active_dr_self_games):
        g = store.get(user_id)
        if isinstance(g, dict):
            _add(g.get("game_id"))

    def _do_cancel():
        # Mines/Tower with picks refuse a plain cancel -> drop the live state first
        active_mines_games.pop(user_id, None)
        active_tower_games.pop(user_id, None)
        for gid in gids:
            rec = game_id_registry.get(gid)
            if not rec or rec.get("status") != "active":
                continue
            try:
                ok, msg = cancel_game_by_id(gid)
                if ok:
                    results.append(msg)
            except Exception as e:
                print(f"cancel on ban failed for {gid}: {e}")
        # make sure nothing is left that a timer could still act on
        active_games.pop(user_id, None)
        active_7up_games.pop(user_id, None)
        active_bj_games.pop(user_id, None)
        active_dr_self_games.pop(user_id, None)

    with get_turn_lock(f"pvb_{user_id}"):
        if pvp_ref:
            with get_turn_lock(f"pvp_{pvp_ref}"):
                _do_cancel()
        else:
            _do_cancel()
    return results

def handle_forwarded_dice(message, chat_id, chat_type, user_id):
    """Returns True if the message was a forwarded dice (already handled, stop processing)."""
    if "dice" not in message or not is_forwarded_message(message):
        return False
    if (message.get("from") or {}).get("is_bot"):
        return False

    msg_id = message.get("message_id")
    in_group = chat_type in ("group", "supergroup")

    # Admins: just ignore the forwarded dice, never ban
    if user_id in admin_list:
        send_message(chat_id, "⚠️ Forwarded emoji ignored. (Admins are not banned.)")
        return True

    # 1) remove the forwarded dice from the chat
    try:
        requests.post(f"{TELEGRAM_API_URL}/deleteMessage",
                      json={"chat_id": chat_id, "message_id": msg_id}, timeout=3)
    except Exception as e:
        print(f"deleteMessage error: {e}")

    # 2) ban from the bot
    banned_users.add(user_id)
    persist_user(user_id)

    # 3) cancel every active game of this player (no more auto-throws)
    cancelled = []
    try:
        cancelled = cancel_user_games_on_ban(user_id)
    except Exception as e:
        print(f"cancel_user_games_on_ban error: {e}")

    # 4) ban from the group
    group_banned = ban_from_group(chat_id, user_id) if in_group else False

    # 5) messages: chat notice, the banned player, the owner
    where = "the group and the bot" if group_banned else "the bot"
    if in_group:
        send_message(chat_id, f"🚫 {format_user_mention(user_id)} forwarded an emoji and has been banned from {where}.")
    for status in cancelled:
        send_message(chat_id, status)

    # Direct message to the banned player (in a DM this is the only banned notice)
    try:
        refund_line = "\n\nYour active game was cancelled and your stake was refunded." if cancelled else ""
        send_message(
            user_id,
            "🚫 *You are banned from the bot for forwarding dice.*\n\n"
            "Forwarding a dice emoji is not allowed — only dice thrown by you inside the chat count."
            f"{refund_line}"
        )
    except Exception as e:
        print(f"ban DM error: {e}")

    try:
        _alert_owner(
            "🚫 *Forwarded emoji — user banned*\n"
            f"👤 User: `{user_id}`\n"
            f"💬 Chat: `{chat_id}`\n"
            f"Group ban: {'✅' if group_banned else ('❌ (bot lacks ban rights?)' if in_group else 'n/a (DM)')}\n"
            f"Games cancelled: {len(cancelled)}"
        )
    except Exception as e:
        print(f"owner alert error: {e}")
    return True

def remove_inline_keyboard(chat_id, message_id):
    payload = {
        "chat_id": chat_id,
        "message_id": message_id,
        "reply_markup": {"inline_keyboard": []}
    }
    _tg_edit("editMessageReplyMarkup", payload, timeout=3)

def set_inline_keyboard(chat_id, message_id, reply_markup):
    payload = {"chat_id": chat_id, "message_id": message_id, "reply_markup": reply_markup}
    _tg_edit("editMessageReplyMarkup", payload, timeout=3)

def send_photo(chat_id, photo_bio, caption=""):
    url = f"{TELEGRAM_API_URL}/sendPhoto"
    files = {'photo': ('game.png', photo_bio, 'image/png')}
    data = {'chat_id': chat_id, 'caption': caption, 'parse_mode': 'Markdown'}
    _rid = _auto_reply_id(chat_id, None)
    if _rid:
        data['reply_to_message_id'] = _rid
        data['allow_sending_without_reply'] = 'true'
    try:
        requests.post(url, files=files, data=data, timeout=10)
    except Exception as e:
        print(f"Error sending photo: {e}")

_STATS_CARD_BG_B64 = "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"
_TOP_CARD_BG_B64 = "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"
# ================= RED NEON CARD DESIGN (STATS + TOP 10) =================
import base64 as _card_b64
from PIL import ImageFilter as _CardFilter

_CARD_FONT_URL = "https://github.com/google/fonts/raw/main/ofl/exo2/Exo2-Italic%5Bwght%5D.ttf"
_CARD_FONT_PATHS = [
    os.path.join(os.path.dirname(os.path.abspath(__file__)), "Exo2-Italic.ttf"),
    os.path.join("/tmp", "Exo2-Italic.ttf"),
]
_card_font_cache = {}
_card_font_file = None
_card_font_lock = threading.Lock()
_card_bg_cache = {}

def _card_font_path():
    global _card_font_file
    if _card_font_file is not None:
        return _card_font_file or None
    with _card_font_lock:
        if _card_font_file is not None:
            return _card_font_file or None
        for p in _CARD_FONT_PATHS:
            if os.path.exists(p) and os.path.getsize(p) > 10000:
                _card_font_file = p
                return p
        try:
            r = requests.get(_CARD_FONT_URL, timeout=15)
            if r.status_code == 200 and len(r.content) > 10000:
                for p in _CARD_FONT_PATHS:
                    try:
                        with open(p, "wb") as fh:
                            fh.write(r.content)
                        _card_font_file = p
                        return p
                    except Exception:
                        continue
        except Exception as e:
            print(f"Card font download failed: {e}")
        _card_font_file = ""
        return None

def _card_font(size, weight=700):
    key = (size, weight)
    if key in _card_font_cache:
        return _card_font_cache[key]
    font = None
    path = _card_font_path()
    if path:
        try:
            font = ImageFont.truetype(path, size)
            try:
                font.set_variation_by_axes([weight])
            except Exception:
                pass
        except Exception:
            font = None
    if font is None:
        for fb in ["DejaVuSans-Bold.ttf", "/usr/share/fonts/truetype/dejavu/DejaVuSans-Bold.ttf", "arialbd.ttf"]:
            try:
                font = ImageFont.truetype(fb, size)
                break
            except Exception:
                continue
    if font is None:
        try:
            font = ImageFont.load_default(size=size)
        except Exception:
            font = ImageFont.load_default()
    _card_font_cache[key] = font
    return font

def _card_bg(name):
    if name not in _card_bg_cache:
        raw = _card_b64.b64decode(_STATS_CARD_BG_B64 if name == "stats" else _TOP_CARD_BG_B64)
        _card_bg_cache[name] = Image.open(io.BytesIO(raw)).convert("RGB")
    return _card_bg_cache[name].copy()

def _fit_font(text, max_w, size, weight=700, min_size=18):
    while size > min_size:
        f = _card_font(size, weight)
        l, t, r, b = f.getbbox(text)
        if r - l <= max_w:
            return f
        size -= 2
    return _card_font(min_size, weight)

def _glow_text(img, xy, text, font, fill, glow, anchor="lm", radius=8):
    # soft neon glow behind the text, then crisp text on top
    layer = Image.new("RGBA", img.size, (0, 0, 0, 0))
    ImageDraw.Draw(layer).text(xy, text, font=font, fill=glow + (200,), anchor=anchor)
    layer = layer.filter(_CardFilter.GaussianBlur(radius))
    img.paste(layer, (0, 0), layer)
    d = ImageDraw.Draw(img)
    d.text(xy, text, font=font, fill=fill, anchor=anchor)

def _indian_group(n):
    s = f"{abs(n):.2f}"
    whole, frac = s.split(".")
    if len(whole) > 3:
        head, tail = whole[:-3], whole[-3:]
        parts = []
        while len(head) > 2:
            parts.insert(0, head[-2:])
            head = head[:-2]
        if head:
            parts.insert(0, head)
        whole = ",".join(parts + [tail])
    return f"{whole}.{frac}"

def _card_money(amount_inr, viewer_id, signed=False):
    amount_inr = float(amount_inr or 0.0)
    curr = user_currency.get(viewer_id, "INR") if viewer_id is not None else "INR"
    if curr == "USDT" and EXCHANGE_RATE > 0:
        val = amount_inr / EXCHANGE_RATE
        txt = f"${abs(val):,.2f}"
        neg = val < 0
    else:
        txt = f"\u20b9{_indian_group(amount_inr)}"
        neg = amount_inr < 0
    if neg:
        return "-" + txt
    if signed and amount_inr > 0:
        return "+" + txt
    return txt

def _biggest_win_date(user_id, stats):
    raw = stats.get("biggest_win_date")
    if not raw:
        best = None
        for item in (user_bet_logs.get(user_id) or []):
            try:
                p = float(item.get("pnl", 0.0))
            except Exception:
                continue
            if p > 0 and (best is None or p > best[0]):
                best = (p, item.get("time"))
        raw = best[1] if best else None
    if not raw:
        return "\u2014"
    try:
        return datetime.strptime(str(raw)[:19], "%Y-%m-%d %H:%M:%S").strftime("%d %b %Y")
    except Exception:
        return str(raw)[:11]

def generate_stats_image(user_id):
    stats = user_stats.get(user_id, {"games": 0, "wins": 0, "losses": 0, "total_pnl": 0.0, "biggest_win": 0.0, "game_counts": {}})
    total_games = int(stats.get("games", 0))
    total_pnl = float(stats.get("total_pnl", 0.0))
    biggest_win = float(stats.get("biggest_win", 0.0))
    total_dep = user_deposits.get(user_id, 0.0)
    total_wd = user_withdrawals.get(user_id, 0.0)
    game_counts = stats.get("game_counts", {}) or {}
    most_played = max(game_counts, key=game_counts.get) if game_counts else "\u2014"

    img = _card_bg("stats")
    # value column of the red neon card (1303 x 802): starts right of the 2nd divider
    VALUE_X, MAX_W = 838, 345
    WHITE, RED_GLOW = (255, 244, 244), (235, 30, 30)
    GREEN, GREEN_GLOW = (80, 245, 90), (20, 180, 40)
    LOSS, LOSS_GLOW = (255, 92, 92), (220, 20, 20)
    GOLD, GOLD_GLOW = (255, 212, 60), (235, 140, 10)

    pnl_col, pnl_glow = (GREEN, GREEN_GLOW) if total_pnl >= 0 else (LOSS, LOSS_GLOW)
    rows = [
        (170, f"{total_games:,}", WHITE, RED_GLOW),
        (250, _card_money(total_dep, user_id), WHITE, RED_GLOW),
        (328, _card_money(total_wd, user_id), WHITE, RED_GLOW),
        (405, str(most_played).upper(), WHITE, RED_GLOW),
        (482, _card_money(total_pnl, user_id), pnl_col, pnl_glow),
        (561, _biggest_win_date(user_id, stats), WHITE, RED_GLOW),
        (640, _card_money(biggest_win, user_id), GOLD, GOLD_GLOW),
    ]
    for y, text, col, glow in rows:
        font = _fit_font(text, MAX_W, 50, weight=800)
        _glow_text(img, (VALUE_X, y), text, font, col, glow, anchor="lm", radius=7)

    bio = io.BytesIO()
    img.save(bio, "PNG")
    bio.seek(0)
    return bio


# ================= REFER SYSTEM =================
REF_DEPOSIT_PERCENT = 0.8   # referrer gets 0.8% of every deposit by their referred player
REF_WAGER_PERCENT = 0.5     # referrer gets 0.5% of every bet amount (wager) by their referred player
REF_PAGE_SIZE = 10
_REF_CODE_CHARS = "ABCDEFGHJKLMNPQRSTUVWXYZ23456789"

user_ref_code = {}        # uid -> own referral code
ref_code_to_id = {}       # code -> uid
user_referred_by = {}     # uid -> referrer uid (permanent, can never change)
user_referred_at = {}     # uid -> timestamp of joining
user_ref_gen_dep = {}     # uid -> bonus this player generated for referrer from deposits
user_ref_gen_wager = {}   # uid -> bonus this player generated for referrer from wagers
user_ref_earned = {}      # uid -> lifetime referral bonus earned as referrer
_ref_lock = threading.Lock()

def get_or_create_ref_code(uid):
    code = user_ref_code.get(uid)
    if code:
        return code
    with _ref_lock:
        code = user_ref_code.get(uid)
        if code:
            return code
        while True:
            code = "".join(random.choice(_REF_CODE_CHARS) for _ in range(7))
            if code not in ref_code_to_id:
                break
        user_ref_code[uid] = code
        ref_code_to_id[code] = uid
    persist_user(uid)
    return code

def build_ref_link(uid):
    return f"https://t.me/{BOT_USERNAME.lstrip('@')}?start=ref_{get_or_create_ref_code(uid)}"

def get_referred_players(referrer_id):
    return [u for u, r in user_referred_by.items() if r == referrer_id]

def ref_generated_total(uid):
    return float(user_ref_gen_dep.get(uid, 0.0)) + float(user_ref_gen_wager.get(uid, 0.0))

def ref_lifetime_earned(referrer_id):
    return float(user_ref_earned.get(referrer_id, 0.0))

def join_referral(user_id, raw_code):
    """Links user_id to the owner of raw_code. Returns (ok, message)."""
    code = str(raw_code or "").strip().upper()
    if code.startswith("REF_"):
        code = code[4:]
    with _ref_lock:
        if user_id in user_referred_by:
            return False, f"⚠️ You are already referred by {tag_player(user_referred_by[user_id])}"
        if not code:
            return False, "⚠️ Usage: `/joinref <refcode>`\nExample: `/joinref AB12CD3`"
        referrer_id = ref_code_to_id.get(code)
        if referrer_id is None:
            return False, "❌ Invalid refer code. Please check the code and try again."
        if referrer_id == user_id:
            return False, "❌ You cannot use your own refer code."
        # Stop loops: you cannot join someone who is (directly or indirectly) under you
        cur, seen = referrer_id, set()
        while cur in user_referred_by and cur not in seen:
            seen.add(cur)
            cur = user_referred_by[cur]
            if cur == user_id:
                return False, "❌ You cannot join the refer of a player who is already under you."
        user_referred_by[user_id] = referrer_id
        user_referred_at[user_id] = current_timestamp()
    persist_user(user_id)
    try:
        send_message(referrer_id, f"🎉 *New Referral!*\n\n{tag_player(user_id)} joined using your refer code.\nYou will earn *{REF_DEPOSIT_PERCENT:g}%* of their deposits and *{REF_WAGER_PERCENT:g}%* of their wagers.")
    except Exception as e:
        print(f"Referral notify error: {e}")
    return True, f"✅ *Referral joined!*\n\nYou are now referred by {tag_player(referrer_id)}."

def _pay_referral_bonus(player_id, base_inr, percent, kind):
    global HOUSE_BALANCE
    referrer_id = user_referred_by.get(player_id)
    if referrer_id is None:
        return 0.0
    try:
        base_inr = float(base_inr or 0.0)
    except Exception:
        return 0.0
    if base_inr <= 0:
        return 0.0
    bonus = round(base_inr * percent / 100.0, 4)
    if bonus <= 0:
        return 0.0
    with _ref_lock:
        if referrer_id not in user_balances:
            user_balances[referrer_id] = 0.0
            user_currency[referrer_id] = 'INR'
        user_balances[referrer_id] += bonus
        user_ref_earned[referrer_id] = float(user_ref_earned.get(referrer_id, 0.0)) + bonus
        store = user_ref_gen_dep if kind == "deposit" else user_ref_gen_wager
        store[player_id] = float(store.get(player_id, 0.0)) + bonus
        HOUSE_BALANCE -= bonus
    persist_user(referrer_id)
    return bonus

def referral_on_deposit(player_id, amount_inr):
    try:
        bonus = _pay_referral_bonus(player_id, amount_inr, REF_DEPOSIT_PERCENT, "deposit")
        if bonus > 0:
            referrer_id = user_referred_by.get(player_id)
            persist_user(player_id)
            save_config_value("house_balance", HOUSE_BALANCE)
            send_message(referrer_id, f"💸 *Referral Bonus!*\n\n{tag_player(player_id)} deposited, you earned *{format_money(bonus, referrer_id)}* ({REF_DEPOSIT_PERCENT:g}%).\n💰 New Balance: *{format_money(user_balances.get(referrer_id, 0.0), referrer_id)}*")
    except Exception as e:
        print(f"Referral deposit bonus error: {e}")

def referral_on_wager(player_id, bet_inr):
    # Silent (no message per bet). The player's own row is saved by the caller.
    try:
        _pay_referral_bonus(player_id, bet_inr, REF_WAGER_PERCENT, "wager")
    except Exception as e:
        print(f"Referral wager bonus error: {e}")

def _ref_date(ts):
    try:
        return datetime.strptime(str(ts)[:19], "%Y-%m-%d %H:%M:%S").strftime("%d %b %Y")
    except Exception:
        return str(ts or "-")[:11]

def build_ref_details_text(uid):
    code = get_or_create_ref_code(uid)
    link = build_ref_link(uid)
    refs = get_referred_players(uid)
    top3 = sorted(refs, key=ref_generated_total, reverse=True)[:3]
    medals = ["🥇", "🥈", "🥉"]
    lines = [
        "🤝 *Refer & Earn*",
        "",
        f"🔗 *Your Refer Link:*\n{link.replace('_', chr(92) + '_')}",
        f"🎟 *Your Refer Code:* `{code}`",
        "",
        f"👥 *Total Refers:* *{len(refs)}*",
        f"💰 *Lifetime Earned:* *{format_money(ref_lifetime_earned(uid), uid)}*",
        "",
        "🏆 *Top 3 Refers:*",
    ]
    if top3:
        for i, r in enumerate(top3):
            lines.append(f"{medals[i]} {tag_player(r)} — *{format_money(ref_generated_total(r), uid)}*")
    else:
        lines.append("_No refers yet. Share your link to start earning!_")
    lines += [
        "",
        f"🎁 You earn *{REF_DEPOSIT_PERCENT:g}%* of every deposit and *{REF_WAGER_PERCENT:g}%* of every wager made by your refers.",
        f"📥 Friends can join with your link or by sending `/joinref {code}`",
        "👀 See all your refers: /myref",
    ]
    if uid in user_referred_by:
        lines.append(f"\n🙋 You are referred by {tag_player(user_referred_by[uid])}")
    return "\n".join(lines)

def myref_page_keyboard(uid, page, total_items):
    total_pages = max(1, (total_items + REF_PAGE_SIZE - 1) // REF_PAGE_SIZE)
    nav = []
    if page > 0:
        nav.append({"text": "⬅️", "callback_data": f"myrefpg_{uid}_{page - 1}"})
    if page + 1 < total_pages:
        nav.append({"text": "➡️", "callback_data": f"myrefpg_{uid}_{page + 1}"})
    return {"inline_keyboard": [nav]} if nav else None

def build_myref_page(uid, page=0):
    refs = sorted(get_referred_players(uid), key=lambda r: user_referred_at.get(r, ""), reverse=True)
    total = len(refs)
    if total == 0:
        code = get_or_create_ref_code(uid)
        return f"👥 *My Refers*\n\n_No one has joined with your refer yet._\n\nShare your code `{code}` or use /ref to get your link.", None
    total_pages = max(1, (total + REF_PAGE_SIZE - 1) // REF_PAGE_SIZE)
    page = max(0, min(page, total_pages - 1))
    start = page * REF_PAGE_SIZE
    lines = [f"👥 *My Refers* ({total})", f"💰 Lifetime Earned: *{format_money(ref_lifetime_earned(uid), uid)}*", ""]
    for i, r in enumerate(refs[start:start + REF_PAGE_SIZE], start=start + 1):
        games = int((user_stats.get(r) or {}).get("games", 0))
        lines.append(f"{i}. {tag_player(r)}")
        lines.append(f"    🎲 Wagered *{format_money(get_user_total_wager(r), uid)}* ({games} games)")
        lines.append(f"    💰 You earned *{format_money(ref_generated_total(r), uid)}*")
        lines.append(f"    📅 Joined {_ref_date(user_referred_at.get(r))}")
        lines.append("")
    lines.append(f"Page {page + 1}/{total_pages}")
    return "\n".join(lines).strip(), myref_page_keyboard(uid, page, total)

# ================= LEVELS (WAGER TIERS) =================
# (name, emoji, total wager required in ₹, level-up bonus in ₹)
LEVEL_TIERS = [
    ("Bronze I", "🥉", 0, 0),
    ("Bronze II", "🥉", 9800, 98),
    ("Bronze III", "🥉", 49000, 147),
    ("Silver I", "🥈", 98000, 196),
    ("Silver II", "🥈", 147000, 245),
    ("Silver III", "🥈", 196000, 294),
    ("Gold I", "🥇", 294000, 392),
    ("Gold II", "🥇", 441000, 490),
    ("Gold III", "🥇", 588000, 686),
    ("Platinum I", "💎", 882000, 882),
    ("Platinum II", "💎", 1323000, 1078),
    ("Platinum III", "💎", 1984500, 1274),
    ("Diamond I", "👑", 2646000, 1470),
    ("Diamond II", "👑", 3969000, 1666),
    ("Diamond III", "👑", 5292000, 1862),
]
# False: players who already wagered a lot only get bonuses for levels they reach from now on.
LEVEL_BONUS_FOR_PAST_LEVELS = False
_level_lock = threading.Lock()

def level_index_for_wager(wager_inr):
    idx = 0
    for i, tier in enumerate(LEVEL_TIERS):
        if float(wager_inr or 0.0) >= tier[2]:
            idx = i
    return idx

def level_label(idx):
    name, emoji, _, _ = LEVEL_TIERS[idx]
    return f"{emoji} {name}"

def check_level_up(user_id, bet_inr=0.0):
    """Pays the level-up bonus for every new tier reached. Call after total_wager was updated."""
    global HOUSE_BALANCE
    st = user_stats.get(user_id)
    if st is None:
        return
    paid = []
    with _level_lock:
        wager = float(st.get("total_wager", 0.0))
        if "level_claimed" not in st:
            if LEVEL_BONUS_FOR_PAST_LEVELS:
                st["level_claimed"] = 0
            else:
                st["level_claimed"] = level_index_for_wager(max(0.0, wager - float(bet_inr or 0.0)))
        new_idx = level_index_for_wager(wager)
        old_idx = int(st.get("level_claimed", 0))
        if new_idx <= old_idx:
            return
        for i in range(old_idx + 1, new_idx + 1):
            bonus = float(LEVEL_TIERS[i][3])
            if bonus > 0:
                if user_id not in user_balances:
                    user_balances[user_id] = 0.0
                    user_currency[user_id] = 'INR'
                user_balances[user_id] += bonus
                HOUSE_BALANCE -= bonus
                paid.append((i, bonus))
        st["level_claimed"] = new_idx
    if not paid:
        return
    try:
        save_config_value("house_balance", HOUSE_BALANCE)
    except Exception as e:
        print(f"Level house save error: {e}")
    total_bonus = sum(b for _, b in paid)
    lines = ["🎉 *LEVEL UP!*", "", f"You reached *{level_label(new_idx)}*", ""]
    for i, b in paid:
        lines.append(f"🎁 {level_label(i)} bonus: *{format_money(b, user_id)}*")
    lines += ["", f"💰 Total added: *{format_money(total_bonus, user_id)}*",
              f"🏦 New Balance: *{format_money(user_balances.get(user_id, 0.0), user_id)}*",
              "", "Check your progress: /levels"]
    try:
        send_message(user_id, "\n".join(lines))
    except Exception as e:
        print(f"Level up notify error: {e}")

def _inr_short(v):
    return f"₹{int(v):,}" if float(v).is_integer() else f"₹{v:,.2f}"

def levels_page_keyboard(user_id, idx):
    nav = []
    if idx > 0:
        nav.append({"text": "⬅️ Previous", "callback_data": f"lvlpg_{user_id}_{idx - 1}"})
    nav.append({"text": f"{idx + 1}/{len(LEVEL_TIERS)}", "callback_data": f"lvlpg_{user_id}_{idx}"})
    if idx + 1 < len(LEVEL_TIERS):
        nav.append({"text": "Next ➡️", "callback_data": f"lvlpg_{user_id}_{idx + 1}"})
    return {"inline_keyboard": [nav]}

def build_level_page(user_id, idx=None):
    """One level per message. idx=None opens the player's current level."""
    wager = get_user_total_wager(user_id)
    cur_idx = level_index_for_wager(wager)
    if idx is None:
        idx = cur_idx
    idx = max(0, min(int(idx), len(LEVEL_TIERS) - 1))
    name, emoji, req, bonus = LEVEL_TIERS[idx]

    if idx == cur_idx:
        status = "⭐ *Your Current Level*"
    elif idx < cur_idx:
        status = "✅ *Reached*"
    else:
        status = "🔒 *Locked*"

    lines = [
        f"🏅 *LEVEL {idx + 1}/{len(LEVEL_TIERS)}*",
        "",
        f"{emoji} *{name}*",
        status,
        "",
        f"🎲 Total Wager Required: *{_inr_short(req)}*",
        f"🎁 Level-Up Bonus: *{'Starting Tier' if idx == 0 else _inr_short(bonus)}*",
        f"💸 Rakeback: *{rakeback_percent_for_idx(idx):g}%* of lost deposits",
        "",
        f"👤 Your Level: *{level_label(cur_idx)}*",
        f"💰 Your Total Wager: *{format_money(wager, user_id)}*",
    ]
    if idx > cur_idx:
        pct = max(0.0, min(1.0, wager / float(req))) if req else 1.0
        filled = int(round(pct * 10))
        lines += [
            "",
            f"📈 `{'█' * filled}{'░' * (10 - filled)}` {pct * 100:.0f}%",
            f"🎯 Wager *{format_money(max(0.0, req - wager), user_id)}* more to reach {emoji} {name}",
        ]
    elif idx == cur_idx and idx + 1 < len(LEVEL_TIERS):
        nxt = LEVEL_TIERS[idx + 1]
        span = max(1.0, float(nxt[2] - req))
        pct = max(0.0, min(1.0, (wager - req) / span))
        filled = int(round(pct * 10))
        lines += [
            "",
            f"⏭ Next: *{nxt[1]} {nxt[0]}* (bonus *{_inr_short(nxt[3])}*)",
            f"📈 `{'█' * filled}{'░' * (10 - filled)}` {pct * 100:.0f}%",
            f"🎯 Wager *{format_money(max(0.0, nxt[2] - wager), user_id)}* more to level up",
        ]
    elif idx == cur_idx:
        lines += ["", "👑 *You reached the highest level!*"]
    lines += ["", "_Level-up bonus is added to your balance automatically._"]
    return "\n".join(lines), levels_page_keyboard(user_id, idx)


# ================= RAKEBACK (DEPOSIT-LOSS BACK) =================
# Rakeback % per level. Only LOST DEPOSIT money counts, never lost winnings.
# Example: deposit ₹500 -> grow to ₹1500 -> lose all ₹1500 = rakeback on ₹500 only.
RAKEBACK_PERCENTS = {
    "Bronze I": 0.5, "Bronze II": 1.2, "Bronze III": 2.5,
    "Silver I": 3.0, "Silver II": 3.5, "Silver III": 4.0,
    "Gold I": 4.5, "Gold II": 5.0, "Gold III": 5.5,
    "Platinum I": 6.0, "Platinum II": 6.5, "Platinum III": 7.0,
    "Diamond I": 8.0, "Diamond II": 9.0, "Diamond III": 10.0,
}
RAKEBACK_MIN_CLAIM = 1.0   # minimum pending rakeback (₹) needed to claim
_rb_lock = threading.RLock()

def _default_user_stats():
    return {"games": 0, "wins": 0, "losses": 0, "total_pnl": 0.0, "total_wager": 0.0, "biggest_win": 0.0, "game_counts": {}}

def rakeback_percent_for_idx(idx):
    return float(RAKEBACK_PERCENTS.get(LEVEL_TIERS[idx][0], 0.0))

def get_rakeback_percent(uid):
    return rakeback_percent_for_idx(level_index_for_wager(get_user_total_wager(uid)))

def _rb_stats(uid):
    """Player's rakeback fields (stored inside stats_json, so no DB change needed).
    rb_dep_left  = deposited money still in the wallet (not lost yet)
    rb_loss_total = lifetime deposit money lost (counted for rakeback)
    rb_pending   = rakeback ready to claim
    rb_claimed   = lifetime rakeback claimed"""
    st = user_stats.get(uid)
    if st is None:
        st = _default_user_stats()
        user_stats[uid] = st
    st.setdefault("rb_dep_left", 0.0)
    st.setdefault("rb_loss_total", 0.0)
    st.setdefault("rb_pending", 0.0)
    st.setdefault("rb_claimed", 0.0)
    if not isinstance(st.get("rb_wd_cuts"), dict):
        st["rb_wd_cuts"] = {}
    return st

def rakeback_backfill():
    """Runs once at start. Old players get their deposit money still in wallet:
    min(total deposits - total withdrawals, current balance)."""
    for uid in list(user_balances.keys()):
        st = user_stats.get(uid)
        if st is not None and "rb_dep_left" in st:
            continue
        dep_net = max(0.0, float(user_deposits.get(uid, 0.0)) - float(user_withdrawals.get(uid, 0.0)))
        if dep_net <= 0 and st is None:
            continue
        st = _rb_stats(uid)
        st["rb_dep_left"] = round(max(0.0, min(dep_net, float(user_balances.get(uid, 0.0)))), 4)

def rakeback_on_deposit(uid, amount_inr):
    try:
        amt = float(amount_inr or 0.0)
        if amt <= 0:
            return
        with _rb_lock:
            st = _rb_stats(uid)
            st["rb_dep_left"] = round(float(st["rb_dep_left"]) + amt, 4)
    except Exception as e:
        print(f"Rakeback deposit error: {e}")

def rakeback_on_loss(uid, loss_inr):
    """Call after a lost bet (stake already gone from balance).
    Winnings are lost first; only the part that eats into deposit money counts."""
    try:
        loss = float(loss_inr or 0.0)
        if loss <= 0:
            return 0.0
        with _rb_lock:
            st = _rb_stats(uid)
            dep_left = float(st["rb_dep_left"])
            bal = max(0.0, float(user_balances.get(uid, 0.0)))
            from_dep = round(max(0.0, min(loss, dep_left - bal)), 4)
            if from_dep <= 0:
                return 0.0
            st["rb_dep_left"] = round(dep_left - from_dep, 4)
            st["rb_loss_total"] = round(float(st["rb_loss_total"]) + from_dep, 4)
            earned = round(from_dep * get_rakeback_percent(uid) / 100.0, 4)
            st["rb_pending"] = round(float(st["rb_pending"]) + earned, 4)
            return earned
    except Exception as e:
        print(f"Rakeback loss error: {e}")
        return 0.0

def rakeback_on_withdraw(uid, amount_inr, wd_id=None):
    """Withdrawn money counts as deposit taken back first (stops profit-then-lose abuse)."""
    try:
        with _rb_lock:
            st = _rb_stats(uid)
            dep_left = float(st["rb_dep_left"])
            cut = round(max(0.0, min(dep_left, float(amount_inr or 0.0))), 4)
            st["rb_dep_left"] = round(dep_left - cut, 4)
            if wd_id and cut > 0:
                st["rb_wd_cuts"][str(wd_id)] = cut
    except Exception as e:
        print(f"Rakeback withdraw error: {e}")

def rakeback_on_withdraw_done(uid, wd_id, rejected):
    """Rejected withdrawal -> money is back in wallet, so deposit money is back too."""
    try:
        with _rb_lock:
            st = _rb_stats(uid)
            cut = float(st["rb_wd_cuts"].pop(str(wd_id), 0.0) or 0.0) if wd_id else 0.0
            if rejected and cut > 0:
                st["rb_dep_left"] = round(float(st["rb_dep_left"]) + cut, 4)
    except Exception as e:
        print(f"Rakeback withdraw-done error: {e}")

def claim_rakeback(uid):
    global HOUSE_BALANCE
    with _rb_lock:
        st = _rb_stats(uid)
        pending = float(st["rb_pending"])
        amt = float(int(pending * 100)) / 100.0   # whole paise only, the rest stays pending
        if amt <= 0 or amt < RAKEBACK_MIN_CLAIM:
            return 0.0
        st["rb_pending"] = round(pending - amt, 4)
        st["rb_claimed"] = round(float(st["rb_claimed"]) + amt, 4)
        if uid not in user_balances:
            user_balances[uid] = 0.0
            user_currency[uid] = 'INR'
        user_balances[uid] += amt
        HOUSE_BALANCE -= amt
    persist_user(uid)
    try:
        save_config_value("house_balance", HOUSE_BALANCE)
    except Exception as e:
        print(f"Rakeback house save error: {e}")
    return amt

def build_rakeback_text(uid, claimed_amt=0.0):
    st = _rb_stats(uid)
    idx = level_index_for_wager(get_user_total_wager(uid))
    pct = rakeback_percent_for_idx(idx)
    pending = float(st["rb_pending"])
    lines = ["💸 *RAKEBACK*", ""]
    if claimed_amt > 0:
        lines += [f"✅ *Claimed {format_money(claimed_amt, uid)}!*",
                  f"🏦 New Balance: *{format_money(user_balances.get(uid, 0.0), uid)}*", ""]
    lines += [
        f"🏅 Your Level: *{level_label(idx)}*",
        f"📊 Your Rakeback Rate: *{pct:g}%*",
    ]
    if idx + 1 < len(LEVEL_TIERS):
        nxt = LEVEL_TIERS[idx + 1]
        lines.append(f"⏭ Next: *{nxt[1]} {nxt[0]}* → *{rakeback_percent_for_idx(idx + 1):g}%*")
    lines += [
        "",
        f"⏳ Ready to Claim: *{format_money(pending, uid)}*",
        f"📉 Deposit Lost (counted): *{format_money(float(st['rb_loss_total']), uid)}*",
        f"💰 Lifetime Claimed: *{format_money(float(st['rb_claimed']), uid)}*",
    ]
    if claimed_amt <= 0:
        if pending > 0:
            lines += ["", f"⚠️ Minimum claim is *{format_money(RAKEBACK_MIN_CLAIM, uid)}*. Keep playing!"]
        else:
            lines += ["", "_Nothing to claim right now._"]
    return "\n".join(lines)

def update_user_stats(user_id, game_name, bet_inr, profit_inr, is_win):
    if user_id not in user_stats:
        user_stats[user_id] = {"games": 0, "wins": 0, "losses": 0, "total_pnl": 0.0, "total_wager": 0.0, "biggest_win": 0.0, "game_counts": {}}
    
    st = user_stats[user_id]
    st["games"] += 1
    st["total_wager"] = float(st.get("total_wager", 0.0)) + float(bet_inr)
    st["total_pnl"] += profit_inr
    
    if game_name not in st["game_counts"]:
        st["game_counts"][game_name] = 0
    st["game_counts"][game_name] += 1
    
    if is_win:
        st["wins"] += 1
        if profit_inr > st["biggest_win"]:
            st["biggest_win"] = profit_inr
            st["biggest_win_date"] = current_timestamp()
    else:
        st["losses"] += 1
    referral_on_wager(user_id, bet_inr)
    check_level_up(user_id, bet_inr)
    persist_user(user_id)


def get_user_total_wager(uid):
    st = user_stats.get(uid) or {}
    if "total_wager" in st and st["total_wager"] is not None:
        return float(st["total_wager"])
    logs = user_bet_logs.get(uid) or []
    if logs:
        return sum(float(item.get("bet", 0.0)) for item in logs)
    return 0.0

def generate_top_wagerers_image(viewer_id=None):
    ranked = []
    candidate_ids = set(user_stats.keys()) | set(user_bet_logs.keys()) | set(user_balances.keys())
    for uid in candidate_ids:
        wager_inr = get_user_total_wager(uid)
        if wager_inr > 0:
            uname = user_usernames.get(uid)
            fname = user_first_names.get(uid)
            label = f"@{uname}" if uname else (fname if fname else f"User {uid}")
            ranked.append({"uid": uid, "label": label, "wager_inr": wager_inr})

    ranked.sort(key=lambda x: x["wager_inr"], reverse=True)
    top10 = ranked[:10]

    img = _card_bg("top")
    # red neon Top 10 card (1273 x 786): one row between each pair of red lines
    row_ys = [207, 262, 315, 368, 420, 473, 526, 580, 633, 687]
    NAME_X = 384
    NAME_MAX_W = 410            # rows 1-9
    NAME_MAX_W_LAST = 195       # row 10 stops before the spade at the bottom
    WAGER_CX, WAGER_MAX_W = 975, 330
    WHITE, RED_GLOW = (255, 244, 244), (235, 30, 30)
    DIM = (200, 170, 170)
    MEDAL = {0: ((255, 212, 60), (235, 140, 10)), 1: ((235, 240, 250), (170, 180, 210)), 2: ((255, 165, 100), (215, 95, 30))}

    for i, y in enumerate(row_ys):
        if i < len(top10):
            row = top10[i]
            name = str(row["label"])
            if len(name) > 22:
                name = name[:21] + "\u2026"
            wager = _card_money(row["wager_inr"], viewer_id)
            name_col, name_glow = MEDAL.get(i, (WHITE, RED_GLOW))
        else:
            name, wager = "\u2014", _card_money(0.0, viewer_id)
            name_col, name_glow = (DIM, RED_GLOW)
        max_w = NAME_MAX_W_LAST if i == 9 else NAME_MAX_W
        nf = _fit_font(name, max_w, 36, weight=700, min_size=20)
        while nf.getbbox(name)[2] - nf.getbbox(name)[0] > max_w and len(name) > 4:
            name = name[:-2] + "\u2026"
        _glow_text(img, (NAME_X, y), name, nf, name_col, name_glow, anchor="lm", radius=6)
        wf = _fit_font(wager, WAGER_MAX_W, 44, weight=800)
        _glow_text(img, (WAGER_CX, y), wager, wf, WHITE, RED_GLOW, anchor="mm", radius=7)

    bio = io.BytesIO()
    img.save(bio, "PNG")
    bio.seek(0)
    return bio


def build_dr_result_message(gid, dice_val, arg, is_win, win_amt=0.0, multiplier=0.0, user_id=None):
    if arg in ["high", "low", "odd", "even"]:
        pick_label = arg.upper()
    else:
        nums = [int(n.strip()) for n in str(arg).split(",")]
        pick_label = " • ".join(str(n) for n in nums)

    if is_win:
        return (
            f"📊 PREDICTION REPORT\n"
            f"━━━━━━━━━━━━━━━━\n"
            f"🔑 Round ID: {gid}\n"
            f"🎲 Actual Result: {dice_val}\n"
            f"🎯 Selected Range: {pick_label}\n"
            f"🔥 Final Status: Win\n"
            f"💰 Payout: {format_money(win_amt, user_id)} ({fmt_mult(multiplier)})\n"
            f"━━━━━━━━━━━━━━━━"
        )
    return (
        f"📊 PREDICTION REPORT\n"
        f"━━━━━━━━━━━━━━━━\n"
        f"🔑 Round ID: {gid}\n"
        f"🎲 Actual Roll: {dice_val}\n"
        f"🎯 Selected Range: {pick_label}\n"
        f"📉 Final Status: Lost\n"
        f"💰 Payout: {format_money(0.0, user_id)}\n"
        f"━━━━━━━━━━━━━━━━"
    )

def remember_button_owner(chat_id, sent_or_msg_id, user_id):
    """Remember which player owns the buttons on a message (accepts a send_message result or a message id)."""
    msg_id = sent_or_msg_id
    if isinstance(sent_or_msg_id, dict):
        msg_id = sent_or_msg_id.get("result", {}).get("message_id") if sent_or_msg_id.get("ok") else None
    if chat_id is None or not msg_id or user_id is None:
        return
    button_owners[(chat_id, msg_id)] = user_id
    if len(button_owners) > 5000:
        for k in list(button_owners.keys())[:1000]:
            button_owners.pop(k, None)

def find_button_owner(chat_id, message_id):
    """Who owns the buttons on this message? None if unknown."""
    owner = button_owners.get((chat_id, message_id))
    if owner is not None:
        return owner
    for uid, st in list(pending_game_setup.items()):
        if st and st.get("message_id") == message_id and st.get("chat_id") in (chat_id, None):
            return uid
    for uid, g in list(active_games.items()):
        if isinstance(g, dict) and g.get("start_message_id") == message_id and g.get("start_chat_id") in (chat_id, None):
            return uid
    for uid, bj in list(active_bj_games.items()):
        if bj and bj.get("message_id") == message_id and bj.get("chat_id") in (chat_id, None):
            return uid
    return None

def create_post_match_keyboard(user_id, payload):
    token = uuid.uuid4().hex[:10]
    post_match_actions[token] = payload
    last_bet = float(payload.get("bet", 0.0))
    double_bet = last_bet * 2.0

    again_label = "🔁 Bet Again"
    row1 = [{"text": again_label, "callback_data": f"pm_again_{token}"}]

    _pm_kind = payload.get("kind")
    _show_double = double_bet <= bet_max(bet_cat(_pm_kind)) + 1e-9
    if _show_double and _pm_kind == "limbo" and limbo_payout_error(double_bet, float(payload.get("target", 2.0)), user_id):
        _show_double = False
    if _show_double:
        double_label = "⚡ Bet Double"
        row1.append({"text": double_label, "callback_data": f"pm_double_{token}"})

    return {"inline_keyboard": [row1]}

def execute_post_match_restart(chat_id, message_id, user_id, payload, multiplier_factor, callback_query_id):
    global HOUSE_BALANCE
    kind = payload.get("kind")
    last_bet = float(payload.get("bet", 0.0))
    next_bet = last_bet * multiplier_factor

    if next_bet <= 0:
        answer_callback(callback_query_id, "Invalid bet amount.")
        return

    _cat = bet_cat(kind)
    if bet_out_of_limits(next_bet, _cat):
        answer_callback(
            callback_query_id,
            f"Bet limit check failed! {BET_CATEGORIES[_cat]}: {format_money(bet_min(_cat), user_id)} - {format_money(bet_max(_cat), user_id)}"
        )
        return
    if kind == "limbo" and limbo_payout_error(next_bet, float(payload.get("target", 2.0)), user_id):
        answer_callback(callback_query_id, f"Limbo max win is {format_money(LIMBO_MAX_PAYOUT, user_id)}. Lower the bet or target.")
        return

    active_summary = get_active_game_summary(user_id)
    if active_summary:
        answer_callback(callback_query_id, f"Finish your active {active_summary} game first!")
        return

    fresh_bal = float(user_balances.get(user_id, 0.0))
    if fresh_bal < next_bet:
        answer_callback(
            callback_query_id,
            f"Insufficient balance! Need {format_money(next_bet, user_id)}, have {format_money(fresh_bal, user_id)}"
        )
        return

    if payload.get("result_grid"):
        set_inline_keyboard(chat_id, message_id, {"inline_keyboard": payload["result_grid"]})
    else:
        remove_inline_keyboard(chat_id, message_id)

    if kind == "versus":
        gid = generate_game_id()
        start_versus_match(
            chat_id,
            None,
            user_id,
            payload["emoji"],
            next_bet,
            payload.get("mode") or "normal",
            payload.get("rw_label") or "1r1w",
            game_id=gid
        )
        answer_callback(callback_query_id, f"Started {format_money(next_bet, user_id)} match!")

    elif kind in ("mines", "tower", "limbo"):
        answer_callback(callback_query_id, f"Starting {kind.title()} ({format_money(next_bet, user_id)})!")
        restart_fair_game(chat_id, user_id, payload, next_bet)

    elif kind == "7up":
        choice_7up = normalize_7up_choice(payload.get("choice_7up")) or "up"
        answer_callback(callback_query_id, f"Rolling 7Up ({format_money(next_bet, user_id)})!")
        run_7up_game(chat_id, user_id, next_bet, choice_7up, raw_choice_text=payload.get("choice_7up"))

    elif kind == "bj":
        start_bj_game(chat_id, user_id, next_bet)
        answer_callback(callback_query_id, f"Blackjack started ({format_money(next_bet, user_id)})!")

    elif kind == "dr" and payload.get("dr_self"):
        answer_callback(callback_query_id, f"Self-mode prediction ({format_money(next_bet, user_id)})!")
        start_dr_self_game(chat_id, user_id, next_bet, payload.get("dr_arg"))

    elif kind == "dr":
        arg = payload.get("dr_arg")
        gid = generate_game_id()
        user_balances[user_id] = fresh_bal - next_bet
        persist_user(user_id)
        register_game_record(gid, "prediction", user_id, next_bet, meta={"choice": arg}, refund_on_cancel=True)

        is_win = False
        multiplier = 0.0
        win_desc = ""
        if arg in ["high", "low", "odd", "even"]:
            res = send_animated_game(chat_id, "🎲")
            dice_val = res["result"]["dice"]["value"] if res and "result" in res else random.randint(1, 6)
            time.sleep(1)
            if arg == "high" and dice_val in [4, 5, 6]: is_win = True
            elif arg == "low" and dice_val in [1, 2, 3]: is_win = True
            elif arg == "odd" and dice_val in [1, 3, 5]: is_win = True
            elif arg == "even" and dice_val in [2, 4, 6]: is_win = True
            multiplier = float(GAME_MULTIPLIERS.get("dr", 1.92))
            win_desc = f"Prediction: {arg.upper()}"
        else:
            nums = [int(n.strip()) for n in str(arg).split(",")]
            res = send_animated_game(chat_id, "🎲")
            dice_val = res["result"]["dice"]["value"] if res and "result" in res else random.randint(1, 6)
            time.sleep(1)
            if dice_val in nums: is_win = True
            dr_num_map = GAME_MULTIPLIERS.get("dr_nums", {1: 5.56, 2: 2.88, 3: 1.92, 4: 1.44, 5: 1.15})
            multiplier = float(dr_num_map.get(len(nums), 1.0))
            win_desc = f"Numbers: {nums}"

        if is_win:
            win_amt = next_bet * multiplier
            profit_inr = win_amt - next_bet
            user_balances[user_id] = float(user_balances.get(user_id, 0.0)) + win_amt
            HOUSE_BALANCE -= profit_inr
            persist_user(user_id)
            save_config_value("house_balance", HOUSE_BALANCE)
            update_user_stats(user_id, "prediction", next_bet, profit_inr, True)
            record_user_bet(user_id, f"Prediction ({win_desc})", next_bet, profit_inr, "WON", game_id=gid)
            mark_game_finished(gid, "completed", extra_meta={"outcome": "WON", "pnl": profit_inr})
            log_win_to_channel(user_id, "🔮", "Predict", win_amt, fmt_mult(multiplier))
            result_text = build_dr_result_message(gid, dice_val, arg, True, win_amt=win_amt, multiplier=multiplier, user_id=user_id)
        else:
            profit_inr = -next_bet
            HOUSE_BALANCE += next_bet
            persist_user(user_id)
            save_config_value("house_balance", HOUSE_BALANCE)
            update_user_stats(user_id, "prediction", next_bet, profit_inr, False)
            record_user_bet(user_id, f"Prediction ({win_desc})", next_bet, profit_inr, "LOST", game_id=gid)
            mark_game_finished(gid, "completed", extra_meta={"outcome": "LOST", "pnl": profit_inr})
            result_text = build_dr_result_message(gid, dice_val, arg, False, user_id=user_id)

        pm_payload = {"kind": "dr", "owner_id": user_id, "bet": next_bet, "dr_arg": arg}
        send_message(chat_id, result_text, reply_markup=create_post_match_keyboard(user_id, pm_payload))
        answer_callback(callback_query_id, f"Predicted {arg} ({format_money(next_bet, user_id)})!")

def format_history_money(amount_in_inr, user_id):
    curr = user_currency.get(user_id, 'INR')
    if curr == 'USDT':
        val = amount_in_inr / EXCHANGE_RATE
        return f"${val:.2f}"
    return f"₹{amount_in_inr:.2f}"

def history_page_keyboard(target_uid, page, total_items):
    total_pages = max(1, (total_items + PAGE_SIZE - 1) // PAGE_SIZE)
    page = max(0, min(page, total_pages - 1))
    nav_row = []
    if page > 0:
        nav_row.append({"text": "⬅️", "callback_data": f"myhistpg_{target_uid}_{page - 1}"})
    if page + 1 < total_pages:
        nav_row.append({"text": "➡️", "callback_data": f"myhistpg_{target_uid}_{page + 1}"})
    return {"inline_keyboard": [nav_row]} if nav_row else None

def build_user_history_page(user_id, page=0):
    raw_logs = user_bet_logs.get(user_id, [])
    logs = list(reversed(raw_logs))
    total_items = len(logs)
    total_pages = max(1, (total_items + PAGE_SIZE - 1) // PAGE_SIZE)
    page = max(0, min(page, total_pages - 1))

    start_idx = page * PAGE_SIZE
    end_idx = start_idx + PAGE_SIZE
    page_items = logs[start_idx:end_idx]

    if not page_items:
        return "📜 *Bet History*\n\n_No bets found yet._\n\nPage 1/1", None

    lines = ["📜 *Your Bet History*", ""]
    for item in page_items:
        game_title = item.get("game", "Game")
        gid = item.get("game_id")
        id_part = f" `#{gid}`" if gid else ""
        bet_val = float(item.get("bet", 0.0))
        pnl_val = float(item.get("pnl", 0.0))
        outcome = str(item.get("outcome", "")).upper()
        if outcome == "PUSH":
            payout_val = bet_val
        elif pnl_val > 0:
            payout_val = bet_val + pnl_val
        else:
            payout_val = 0.0

        t_str = item.get("time", "")
        lines.append(f"🎲 *{game_title}*{id_part}")
        lines.append(f"⬆️ Bet *{format_history_money(bet_val, user_id)}*")
        lines.append(f"⬇️ Payout *{format_history_money(payout_val, user_id)}*")
        if t_str:
            lines.append(f"🕒 `{t_str}`")
        lines.append("")

    lines.append(f"Page {page + 1}/{total_pages}")
    return "\n".join(lines).strip(), history_page_keyboard(user_id, page, total_items)

def info_menu_keyboard(target_uid):
    return {
        "inline_keyboard": [
            [
                {"text": "📥 Deposits", "callback_data": f"infopg_{target_uid}_deposits_0"},
                {"text": "📤 Withdrawals", "callback_data": f"infopg_{target_uid}_withdrawals_0"},
                {"text": "🎲 Bets", "callback_data": f"infopg_{target_uid}_bets_0"},
            ]
        ]
    }

def info_page_keyboard(target_uid, section, page, total_items):
    total_pages = max(1, (total_items + PAGE_SIZE - 1) // PAGE_SIZE)
    page = max(0, min(page, total_pages - 1))
    nav_row = []
    if page > 0:
        nav_row.append({"text": "⬅️ Previous", "callback_data": f"infopg_{target_uid}_{section}_{page - 1}"})
    if page + 1 < total_pages:
        nav_row.append({"text": "➡️ Next", "callback_data": f"infopg_{target_uid}_{section}_{page + 1}"})

    switch_row = []
    for sec_key, sec_label in [("deposits", "📥 Deposits"), ("withdrawals", "📤 Withdrawals"), ("bets", "🎲 Bets")]:
        prefix = "• " if sec_key == section else ""
        switch_row.append({"text": f"{prefix}{sec_label}", "callback_data": f"infopg_{target_uid}_{sec_key}_0"})

    rows = []
    if nav_row:
        rows.append(nav_row)
    rows.append(switch_row)
    return {"inline_keyboard": rows}

def build_user_info_summary(target_uid):
    bal_str = format_money(user_balances.get(target_uid, 0.0), target_uid)
    curr = user_currency.get(target_uid, "INR")
    uname = user_usernames.get(target_uid)
    uname_str = f"@{uname}" if uname else "N/A"
    status_str = "🔴 BANNED" if target_uid in banned_users else "🟢 Active"

    u_deps = [d for d in deposit_history if d.get("user") == target_uid]
    u_wds = [w for w in withdrawal_history if w.get("user") == target_uid]
    u_bets = user_bet_logs.get(target_uid, [])

    dep_total = format_money(user_deposits.get(target_uid, 0.0), target_uid)
    wd_total = format_money(user_withdrawals.get(target_uid, 0.0), target_uid)

    lines = [
        "🪪 *User Lifetime Info*",
        f"• *User ID:* `{target_uid}`",
        f"• *Username:* {uname_str}",
        f"• *Status:* {status_str}",
        f"• *Currency:* *{curr}*",
        f"• *Current Balance:* *{bal_str}*",
        f"• *Lifetime Deposits:* *{dep_total}* (`{len(u_deps)}` txns)",
        f"• *Lifetime Withdrawals:* *{wd_total}* (`{len(u_wds)}` txns)",
        f"• *Lifetime Bets:* *{len(u_bets)}*",
        "",
        "Tap a section below to view lifetime history (5 per page):"
    ]
    return "\n".join(lines)

def build_user_info_section_page(target_uid, section, page):
    uname = user_usernames.get(target_uid)
    who_str = f"@{uname} (`{target_uid}`)" if uname else f"`{target_uid}`"

    if section == "deposits":
        records = [d for d in deposit_history if d.get("user") == target_uid]
        title = "📥 *Lifetime Deposits*"
    elif section == "withdrawals":
        records = [w for w in withdrawal_history if w.get("user") == target_uid]
        title = "📤 *Lifetime Withdrawals*"
    else:
        records = user_bet_logs.get(target_uid, [])
        title = "🎲 *Lifetime Bets*"

    total_items = len(records)
    total_pages = max(1, (total_items + PAGE_SIZE - 1) // PAGE_SIZE)
    page = max(0, min(page, total_pages - 1))

    start_idx = page * PAGE_SIZE
    end_idx = start_idx + PAGE_SIZE
    slice_items = records[start_idx:end_idx]

    lines = [
        f"{title} — {who_str}",
        f"📄 *Page {page + 1} / {total_pages}* (Total: *{total_items}*)",
        ""
    ]

    if not slice_items:
        lines.append("_No records found._")
    else:
        for idx, item in enumerate(slice_items, start=start_idx + 1):
            if section == "deposits":
                t_str = item.get("time", "N/A")
                utr_str = item.get("utr") or "N/A"
                lines.append(f"{idx}. `{item.get('id', '-')}` | `{t_str}` | *{format_money(item['amount'], target_uid)}* | UTR: `{utr_str}`")
            elif section == "withdrawals":
                t_str = item.get("time", "N/A")
                upi_str = item.get("upi") or "N/A"
                st_tag = {"pending": "⏳", "paid": "✅", "rejected": "❌"}.get(item.get("status"), "📁")
                lines.append(f"{idx}. {st_tag} `{item.get('id', '-')}` | `{t_str}` | *{format_money(item['amount'], target_uid)}* | UPI: `{upi_str}`")
            else:
                gid_part = f"`{item['game_id']}` | " if item.get("game_id") else ""
                pnl_val = item.get("pnl", 0.0)
                sign = "+" if pnl_val > 0 else ""
                pnl_str = f"{sign}{format_money(pnl_val, target_uid)}"
                lines.append(
                    f"{idx}. {gid_part}*{item['game']}* | Bet: *{format_money(item['bet'], target_uid)}* | "
                    f"*{item['outcome']}* ({pnl_str}) | `{item.get('time', '')}`"
                )

    return "\n".join(lines), info_page_keyboard(target_uid, section, page, total_items)

def build_game_search_report(target_gid):
    gid = target_gid.strip().upper()
    rec = game_id_registry.get(gid)
    if not rec:
        return f"⚠️ No game found with ID `{gid}`."

    meta = rec.get("meta", {})
    kind_labels = {
        "bot_versus": "🤖 Bot Versus",
        "pvp_match": "⚔️ Player vs Player",
        "blackjack": "🃏 Blackjack",
        "prediction": "🔮 Dice Prediction",
        "seven_up": "🎲🎲 7Up",
        "mines": "💣 Mines",
        "tower": "🗼 Tower",
        "limbo": "🚀 Limbo",
    }
    kind_str = kind_labels.get(rec.get("kind"), rec.get("kind", "Game"))
    status_str = str(rec.get("status", "unknown")).upper()
    owner_id = rec.get("owner_id")
    bet_inr = rec.get("bet_inr", 0.0)

    lines = [
        "🔎 *Game ID Details*",
        f"• *Game ID:* `{gid}`",
        f"• *Type:* {kind_str}",
        f"• *Status:* *{status_str}*",
        f"• *Started By:* `{owner_id}`",
    ]

    if rec.get("kind") == "pvp_match":
        p1 = meta.get("p1_id")
        p2 = meta.get("p2_id")
        lines.append(f"• *Players:* P1 `{p1}` vs P2 `{p2}`")
        lines.append(f"• *Bet Each:* *{format_money(bet_inr, owner_id)}*")
        if status_str == "COMPLETED":
            if meta.get("winner_id"):
                w_lbl = f" ({meta['winner_label']})" if meta.get("winner_label") else ""
                lines.append(f"• *Winner:* `{meta['winner_id']}`{w_lbl}")
            else:
                lines.append("• *Winner:* _N/A_")
    elif rec.get("kind") == "bot_versus":
        lines.append(f"• *Bet Amount:* *{format_money(bet_inr, owner_id)}*")
        if status_str == "COMPLETED":
            w_id = meta.get("winner_id")
            w_lbl = meta.get("winner_label")
            if w_id is not None:
                lbl_part = f" ({w_lbl})" if w_lbl else ""
                lines.append(f"• *Winner:* `{w_id}`{lbl_part}")
            else:
                lines.append("• *Winner:* _N/A_")
    else:
        lines.append(f"• *Bet Amount:* *{format_money(bet_inr, owner_id)}*")
        if status_str == "COMPLETED" and meta.get("outcome"):
            lines.append(f"• *Outcome:* *{meta['outcome']}*")

    if meta.get("emoji"):
        g_name = GAME_NAME_MAP.get(meta["emoji"], "Game")
        lines.append(f"• *Game:* {g_name} ({meta['emoji']})")
    if meta.get("rw_label") or meta.get("mode"):
        lines.append(f"• *Format / Mode:* `{meta.get('rw_label', '-')}` / *{meta.get('mode', '-')}*")
    if meta.get("choice"):
        lines.append(f"• *Prediction:* *{str(meta['choice']).upper()}*")
    if meta.get("nums"):
        lines.append(f"• *Numbers:* `{meta['nums']}`")

    lines.append(f"• *Created At:* `{rec.get('created_at', 'N/A')}`")
    if rec.get("ended_at"):
        lines.append(f"• *Ended At:* `{rec.get('ended_at')}`")

    return "\n".join(lines)

def cancel_game_by_id(target_gid):
    gid = target_gid.strip().upper()
    rec = game_id_registry.get(gid)
    if not rec:
        return False, f"⚠️ Game ID `{gid}` not found."

    if rec.get("status") != "active":
        return False, f"⚠️ Game `{gid}` is already *{rec.get('status')}*."

    kind = rec.get("kind")
    owner_id = rec.get("owner_id")
    bet_inr = rec.get("bet_inr", 0.0)
    refund = rec.get("refund_on_cancel", True)

    if kind == "bot_versus":
        active_games.pop(owner_id, None)
        if refund and bet_inr > 0:
            user_balances[owner_id] = user_balances.get(owner_id, 0.0) + bet_inr
    elif kind == "pvp_match":
        match_id = rec.get("meta", {}).get("match_id")
        p1 = rec.get("meta", {}).get("p1_id")
        p2 = rec.get("meta", {}).get("p2_id")
        if match_id:
            active_pvp_games.pop(match_id, None)
        if p1 and active_games.get(p1) == match_id:
            active_games.pop(p1, None)
        if p2 and active_games.get(p2) == match_id:
            active_games.pop(p2, None)
        if refund and bet_inr > 0:
            if p1 is not None:
                user_balances[p1] = user_balances.get(p1, 0.0) + bet_inr
            if p2 is not None:
                user_balances[p2] = user_balances.get(p2, 0.0) + bet_inr
    elif kind == "blackjack":
        bj = active_bj_games.pop(owner_id, None)
        effective_bet = (bj or {}).get("bet", bet_inr)
        if refund and effective_bet > 0:
            user_balances[owner_id] = user_balances.get(owner_id, 0.0) + effective_bet
    elif kind == "seven_up":
        g7 = active_7up_games.pop(owner_id, None)
        effective_bet = (g7 or {}).get("bet", bet_inr)
        if refund and effective_bet > 0:
            user_balances[owner_id] = user_balances.get(owner_id, 0.0) + effective_bet
    elif kind == "prediction":
        _dg = active_dr_self_games.get(owner_id)
        if _dg and _dg.get("game_id") == gid:
            _dg["token"] = None
            active_dr_self_games.pop(owner_id, None)
        if refund and bet_inr > 0:
            user_balances[owner_id] = user_balances.get(owner_id, 0.0) + bet_inr
    elif kind == "rain":
        rn = active_rains.pop(gid, None)
        if rn:
            with rn["lock"]:
                rn["done"] = True
            if rn.get("message_id"):
                try:
                    edit_message(rn["chat_id"], rn["message_id"], f"🌧 *Rain* `{gid}` *was cancelled by admin.* The rain amount was refunded.")
                except Exception as e:
                    print(f"rain cancel edit error: {e}")
        if refund and bet_inr > 0:
            rain_return_funds(rec.get("meta", {}).get("source", "user"), owner_id, bet_inr)
    elif kind in ("mines", "tower"):
        store = active_mines_games if kind == "mines" else active_tower_games
        live = store.get(owner_id)
        if live and live.get("game_id") == gid and (live.get("revealed") or live.get("picks")):
            return False, f"⚠️ Game `{gid}` already has picks. Use the 💰 Cashout button instead."
        if live and live.get("game_id") == gid:
            store.pop(owner_id, None)
        if refund and bet_inr > 0:
            user_balances[owner_id] = user_balances.get(owner_id, 0.0) + bet_inr
            persist_user(owner_id)

    mark_game_finished(gid, "cancelled")
    if refund and bet_inr > 0:
        for _u in {owner_id, rec.get("meta", {}).get("p1_id"), rec.get("meta", {}).get("p2_id")}:
            if _u is not None:
                try:
                    persist_user(_u)
                except Exception as _e:
                    print(f"persist after cancel failed for {_u}: {_e}")
    refund_note = " Stake refunded." if refund and bet_inr > 0 else ""
    return True, f"🛑 Game `{gid}` has been *CANCELLED*.{refund_note}"

def finish_bj_game(chat_id, message_id, user_id, bj, outcome):
    global HOUSE_BALANCE
    gid = bj.get("game_id")
    p_cards = bj["player_cards"]
    d_cards = bj["dealer_cards"]
    p_tot = calculate_hand_total(p_cards)
    d_tot = calculate_hand_total(d_cards)
    bet = bj["bet"]
    mult = float(GAME_MULTIPLIERS.get("bj", 2.0))

    header = (
        f"🃏 *Blackjack Result* (`{gid}`)\n\n"
        f"👤 Your Hand: {format_cards(p_cards)} (*{p_tot}*)\n"
        f"🤖 Dealer Hand: {format_cards(d_cards)} (*{d_tot}*)\n"
        f"💰 Total Bet: {format_money(bet, user_id)}\n\n"
    )

    if outcome == "push":
        user_balances[user_id] = user_balances.get(user_id, 0.0) + bet
        persist_user(user_id)
        update_user_stats(user_id, "blackjack", bet, 0.0, False)
        record_user_bet(user_id, "Blackjack", bet, 0.0, "PUSH", game_id=gid)
        body = f"🤝 *Push (Tie)!* Bet refunded.\n💰 Balance: {format_money(user_balances[user_id], user_id)}"
    elif outcome == "win":
        win_amt = bet * mult
        profit_inr = win_amt - bet
        user_balances[user_id] = user_balances.get(user_id, 0.0) + win_amt
        HOUSE_BALANCE -= profit_inr
        persist_user(user_id)
        save_config_value("house_balance", HOUSE_BALANCE)
        update_user_stats(user_id, "blackjack", bet, profit_inr, True)
        record_user_bet(user_id, "Blackjack", bet, profit_inr, "WON", game_id=gid)
        log_win_to_channel(user_id, "🃏", "Blackjack", win_amt, fmt_mult(mult))
        body = f"🎉 *You WON {format_money(win_amt, user_id)}* (`{fmt_mult(mult)}`)! 🥳\n💰 Balance: {format_money(user_balances[user_id], user_id)}"
    else:
        profit_inr = -bet
        HOUSE_BALANCE += bet
        update_user_stats(user_id, "blackjack", bet, profit_inr, False)
        record_user_bet(user_id, "Blackjack", bet, profit_inr, "LOST", game_id=gid)
        reason_txt = "Bust! Over 21." if outcome == "bust" else "Dealer wins."
        body = f"😢 *You Lost!* {reason_txt}\n💰 Balance: {format_money(user_balances[user_id], user_id)}"

    mark_game_finished(gid, "completed", extra_meta={"outcome": outcome})
    if bj.get("seeds"):
        fair_reveal(bj["seeds"], user_id)
        body += bj_fair_footer(bj, reveal=True)
    pm_bj_payload = {"kind": "bj", "owner_id": user_id, "bet": bet}
    edit_message(chat_id, message_id, header + body, reply_markup=create_post_match_keyboard(user_id, pm_bj_payload))
    if user_id in active_bj_games:
        del active_bj_games[user_id]

def play_dealer_and_settle(chat_id, message_id, user_id, bj):
    p_tot = calculate_hand_total(bj["player_cards"])
    while calculate_hand_total(bj["dealer_cards"]) < 17:
        bj["dealer_cards"].append(bj_draw(bj))
    d_tot = calculate_hand_total(bj["dealer_cards"])

    if d_tot > 21 or p_tot > d_tot:
        finish_bj_game(chat_id, message_id, user_id, bj, "win")
    elif p_tot < d_tot:
        finish_bj_game(chat_id, message_id, user_id, bj, "lose")
    else:
        finish_bj_game(chat_id, message_id, user_id, bj, "push")

def send_animated_game(chat_id, emoji, reply_to_message_id=None):
    """Every emoji throw in a group is done by a helper bot (round-robin).
    Main bot throws only in a player's DM, or as emergency backup when no helper could."""
    payload = {"chat_id": chat_id, "emoji": emoji}
    reply_to_message_id = _auto_reply_id(chat_id, reply_to_message_id)
    if reply_to_message_id:
        payload["reply_to_message_id"] = reply_to_message_id
        payload["allow_sending_without_reply"] = True

    # Player DM: helpers can't post there, the main bot throws.
    if isinstance(chat_id, int) and chat_id > 0:
        return _main_throw(payload)

    deadline = time.time() + HELPER_THROW_WAIT
    while True:
        order = _helpers_for_chat(chat_id)
        if not order:
            break
        now = time.time()
        for h in order:
            if _helper_cooldown.get(h.get("id"), 0) > now:
                continue
            data = _helper_post(h, "sendDice", payload)
            if data and data.get("ok") and (data.get("result") or {}).get("dice"):
                return data
        left = deadline - time.time()
        if left <= 0:
            break
        soonest = min(max(0.3, _helper_cooldown.get(h.get("id"), 0) - time.time()) for h in order)
        if soonest > left:
            break
        time.sleep(soonest)

    # Emergency backup: no helper could throw here.
    why = "no helper is ON" if not any(h.get("enabled") for h in HELPER_BOTS) else "helpers failed or are not in this group"
    _note_backup_throw(chat_id, why)
    return _main_throw(payload)

def roll_bot_series(chat_id, emoji, rolls_count, reply_to_message_id=None):
    vals = []
    for idx in range(rolls_count):
        res = send_animated_game(chat_id, emoji, reply_to_message_id=reply_to_message_id)
        v = res['result']['dice']['value'] if res and 'result' in res else random.randint(1, 6)
        vals.append(v)
        if rolls_count > 1:
            time.sleep(0.6)
    return vals

def create_zapupi_order(amount, chat_id):
    try:
        if float(amount) < MIN_DEPOSIT:
            return f"⚠️ Minimum deposit is *₹{MIN_DEPOSIT:,.0f}*. Please enter a higher amount.", None
    except (TypeError, ValueError):
        return "⚠️ Invalid amount.", None
    url = "https://pay.zapupi.com/api/create-order"
    order_id = "ORD" + str(int(time.time() * 1000)) + str(random.randint(100, 999))
    
    payload = {
        "zap_key": ZAPUPI_API_KEY,
        "order_id": order_id,
        "amount": str(amount),
        "remark": f"Deposit|{chat_id}",
        "webhook_url": f"{PUBLIC_BASE_URL}/zapupi-webhook?key={ZAPUPI_WEBHOOK_SECRET}"
    }
    
    headers = {"Content-Type": "application/json"}
    try:
        response = requests.post(url, json=payload, headers=headers, timeout=10)
        data = response.json()
        if data.get("status") == "success" and data.get("payment_url"):
            dep_id = generate_txn_id("DP")
            order_rec = {
                "id": dep_id,
                "order_id": order_id,
                "user": chat_id,
                "amount": float(amount),
                "status": "pending",
                "time": current_timestamp(),
                "credited_at": ""
            }
            deposit_orders[order_id] = order_rec
            persist_deposit_order(order_rec)
            msg = (
                f"🔗 *Deposit Order Created!*\n\n"
                f"🆔 Deposit ID: `{dep_id}`\n"
                f"💰 Amount: *₹{amount}*\n"
                f"🧾 Order ID: `{order_id}`"
            )
            kb = {
                "inline_keyboard": [
                    [{"text": "💳 Deposit Now", "url": data.get("payment_url")}]
                ]
            }
            return msg, kb
        else:
            return f"❌ Failed: {data.get('message', 'Unknown error')}", None
    except Exception as e:
        print(f"❌ ZapUPI create_order error: {e}")
        return "⚠️ Failed to connect to payment gateway.", None

def build_pvb_round_text(user_id, emoji, u_vals, b_vals, round_winner, game, gid, round_num):
    """PvB round result. round_winner: 'user', 'bot' or None (tie)."""
    if round_winner == "user":
        winner_line = f"🔥 Winner: {tag_player(user_id)}"
    elif round_winner == "bot":
        winner_line = "🔥 Winner: Bot"
    else:
        winner_line = "🤝 Round Tied — no point"
    return (
        f"⚔️ *Round {round_num} Result*\n"
        f"━━━━━━━━━━━━━━━━\n"
        f"{emoji} {tag_player(user_id)} — {roll_text(u_vals)}{' ✅' if round_winner == 'user' else ''}\n"
        f"{emoji} Bot — {roll_text(b_vals)}{' ✅' if round_winner == 'bot' else ''}\n"
        f"━━━━━━━━━━━━━━━━\n"
        f"{winner_line}\n"
        f"🏆 Score: {game['user_wins']} : {game['bot_wins']} | First to {game['target_wins']}\n"
        f"🆔 `{gid}`"
    )

def build_pvb_final_text(user_id, emoji, u_vals, b_vals, user_won, game, gid, win_amt, mult):
    """PvB final result. Multiplier is read live, so /setmulti changes show here."""
    return (
        f"⚔️ *Final Round Result*\n"
        f"━━━━━━━━━━━━━━━━\n"
        f"{emoji} {tag_player(user_id)} — {roll_text(u_vals)}{' ✅' if user_won else ''}\n"
        f"{emoji} Bot — {roll_text(b_vals)}{'' if user_won else ' ✅'}\n"
        f"━━━━━━━━━━━━━━━━\n"
        f"🔥 Winner: {tag_player(user_id) if user_won else 'Bot'}\n"
        f"🏆 Score: {game['user_wins']} : {game['bot_wins']} | First to {game['target_wins']}\n"
        f"🆔 `{gid}`\n"
        f"🏁 Winnings: {format_money(win_amt, user_id)} ({fmt_mult(mult)})"
    )

def resolve_round_and_match(chat_id, user_id, game):
    with helper_voice(chat_id):
        return _resolve_round_and_match(chat_id, user_id, game)

def _resolve_round_and_match(chat_id, user_id, game):
    global HOUSE_BALANCE
    gid = game.get("game_id")
    emoji = game["emoji"]
    g_name = GAME_NAME_MAP.get(emoji, "Game")
    mode = game["mode"]
    rw_label = game["rw_label"]
    target_wins = game["target_wins"]
    bet = game["bet"]
    
    u_vals = game["current_user_rolls"]
    b_vals = game["current_bot_rolls"]
    u_sum = sum(u_vals)
    b_sum = sum(b_vals)
    
    u_expr = "+".join(map(str, u_vals))
    b_expr = "+".join(map(str, b_vals))
    
    round_num = game["round_num"]
    mode_tag = "🔥 CRAZY" if mode == "crazy" else "⚡ NORMAL"
    
    round_winner = None
    if u_sum == b_sum:
        r_status = "🤝 *Round Tied!* No point awarded."
    elif mode == "crazy":
        if u_sum < b_sum:
            round_winner = "user"
            game["user_wins"] += 1
            r_status = "✨ *You took this round!* (Lower sum wins)"
        else:
            round_winner = "bot"
            game["bot_wins"] += 1
            r_status = "🤖 *Bot took this round!* (Lower sum wins)"
    else:
        if u_sum > b_sum:
            round_winner = "user"
            game["user_wins"] += 1
            r_status = "✨ *You took this round!* (Higher sum wins)"
        else:
            round_winner = "bot"
            game["bot_wins"] += 1
            r_status = "🤖 *Bot took this round!* (Higher sum wins)"

    if game["user_wins"] >= target_wins or game["bot_wins"] >= target_wins:
        user_won_match = game["user_wins"] >= target_wins
        label = f"Bot {g_name} ({rw_label}/{mode})"
        if user_won_match:
            mult = get_versus_multiplier(emoji)
            win_amt = bet * mult
            profit_inr = win_amt - bet
            user_balances[user_id] = user_balances.get(user_id, 0.0) + win_amt
            HOUSE_BALANCE -= profit_inr
            persist_user(user_id)
            save_config_value("house_balance", HOUSE_BALANCE)
            update_user_stats(user_id, emoji, bet, profit_inr, True)
            record_user_bet(user_id, label, bet, profit_inr, "WON", game_id=gid)
            mark_game_finished(
                gid,
                "completed",
                extra_meta={
                    "outcome": "WON",
                    "winner_id": user_id,
                    "winner_label": format_win_actor(user_id),
                    "pnl": profit_inr
                }
            )
            log_win_to_channel(user_id, emoji, g_name, win_amt, fmt_mult(mult))
            final_text = build_pvb_final_text(user_id, emoji, u_vals, b_vals, True, game, gid, win_amt, mult)
        else:
            profit_inr = -bet
            HOUSE_BALANCE += bet
            update_user_stats(user_id, emoji, bet, profit_inr, False)
            record_user_bet(user_id, label, bet, profit_inr, "LOST", game_id=gid)
            mark_game_finished(
                gid,
                "completed",
                extra_meta={
                    "outcome": "LOST",
                    "winner_id": "Bot",
                    "winner_label": "Bot",
                    "pnl": profit_inr
                }
            )
            final_text = build_pvb_final_text(user_id, emoji, u_vals, b_vals, False, game, gid, 0.0, get_versus_multiplier(emoji))

        pm_vs_payload = {
            "kind": "versus",
            "owner_id": user_id,
            "bet": bet,
            "emoji": emoji,
            "mode": mode,
            "rw_label": rw_label
        }
        send_message(chat_id, final_text, reply_markup=create_post_match_keyboard(user_id, pm_vs_payload))
        if user_id in active_games:
            del active_games[user_id]
        return

    msg = build_pvb_round_text(user_id, emoji, u_vals, b_vals, round_winner, game, gid, round_num)
    send_message(chat_id, msg)

    game["round_num"] += 1
    game["current_user_rolls"] = []
    game["current_bot_rolls"] = []
    rolls_per_round = game["rolls_per_round"]
    
    if game["first_turn"] == "bot":
        game["step"] = "waiting_user_second"
        send_message(chat_id, f"🤖 *Round {game['round_num']}* — Bot is throwing `{emoji}` x{rolls_per_round}...")
        b_next = roll_bot_series(chat_id, emoji, rolls_per_round)
        game["current_bot_rolls"] = b_next
        b_next_expr = "+".join(map(str, b_next))
        send_message(chat_id, f"🤖 Bot Roll: `{b_next_expr}` (*{sum(b_next)}*)\n\n👉 *Now* {tag_player(user_id)}*'s turn! Send `{emoji}` x{rolls_per_round} in chat.*")
        schedule_pvb_turn_timeout(chat_id, user_id, game)
    else:
        game["step"] = "waiting_user_first"
        send_message(chat_id, f"👤 *Round {game['round_num']}* — Your turn! Send `{emoji}` x{rolls_per_round} in chat.")
        schedule_pvb_turn_timeout(chat_id, user_id, game)

# =====================================================================
# 🔐 PROVABLY FAIR GAMES: MINES · TOWER · LIMBO
# ---------------------------------------------------------------------
# result bytes = HMAC_SHA256(key=server_seed, msg=f"{client_seed}:{nonce}:{round}")
# every 4 bytes -> one float in [0, 1). Player sees sha256(server_seed)
# before betting. Every bet gets its own fresh server seed, revealed
# automatically when that game ends (so it can never predict another bet).
# =====================================================================
import hmac as _pf_hmac
import hashlib as _pf_hashlib
import secrets as _pf_secrets
import math as _pf_math
from urllib.parse import urlencode as _pf_urlencode

FAIR_HOUSE_EDGE = 0.08          # 8% house edge
FAIR_RTP = 1.0 - FAIR_HOUSE_EDGE
VERIFY_URL = os.environ.get("VERIFY_URL")  # optional: link to the online verify page

MINES_TILES = 25
MINES_DEFAULT = 3
LIMBO_MAX = 1000000.0
LIMBO_MIN_TARGET = 1.01
LIMBO_MAX_TARGET = 1000.0
TOWER_LEVELS = 9
TOWER_DIFFICULTIES = {
    "easy":   {"cols": 4, "bombs": 1},
    "medium": {"cols": 3, "bombs": 1},
    "hard":   {"cols": 2, "bombs": 1},
    "expert": {"cols": 3, "bombs": 2},
    "master": {"cols": 4, "bombs": 3},
}

fair_seeds = {}             # uid -> {"server_seed", "client_seed", "nonce"}
revealed_server_seeds = {}  # sha256(server_seed) -> server_seed
active_mines_games = {}     # uid -> game dict
active_tower_games = {}     # uid -> game dict


# ---------------- core math (same as the verify page) ----------------
def pf_sha256(text_val):
    return _pf_hashlib.sha256(text_val.encode()).hexdigest()

def pf_floats(server_seed, client_seed, nonce, count):
    out = []
    rnd = 0
    while len(out) < count:
        msg = f"{client_seed}:{nonce}:{rnd}".encode()
        digest = _pf_hmac.new(server_seed.encode(), msg, _pf_hashlib.sha256).digest()
        for i in range(0, 32, 4):
            if len(out) >= count:
                break
            f = 0.0
            for j in range(4):
                f += digest[i + j] / (256 ** (j + 1))
            out.append(f)
        rnd += 1
    return out

def pf_pick(floats, size, picks):
    pool = list(range(size))
    res = []
    for i in range(picks):
        idx = int(_pf_math.floor(floats[i] * len(pool)))
        res.append(pool.pop(idx))
    return res

def pf_floor2(x):
    return _pf_math.floor(x * 100) / 100

def pf_limbo_result(seeds):
    f = pf_floats(seeds["server_seed"], seeds["client_seed"], seeds["nonce"], 1)[0]
    if f == 0:
        return LIMBO_MAX
    return min(LIMBO_MAX, max(1.0, pf_floor2((1.0 / f) * FAIR_RTP)))

def pf_mines_layout(seeds, mines):
    floats = pf_floats(seeds["server_seed"], seeds["client_seed"], seeds["nonce"], mines)
    return pf_pick(floats, MINES_TILES, mines)

def pf_mines_multiplier(mines, safe_revealed):
    if safe_revealed <= 0:
        return 1.0
    fair = 1.0
    for i in range(safe_revealed):
        fair *= (MINES_TILES - i) / (MINES_TILES - mines - i)
    return pf_floor2(fair * FAIR_RTP)

def pf_tower_layout(seeds, difficulty):
    cfg = TOWER_DIFFICULTIES[difficulty]
    cols, bombs = cfg["cols"], cfg["bombs"]
    floats = pf_floats(seeds["server_seed"], seeds["client_seed"], seeds["nonce"], TOWER_LEVELS * bombs)
    levels = []
    for lvl in range(TOWER_LEVELS):
        levels.append(sorted(pf_pick(floats[lvl * bombs:(lvl + 1) * bombs], cols, bombs)))
    return levels

def pf_tower_multiplier(difficulty, levels_cleared):
    if levels_cleared <= 0:
        return 1.0
    cfg = TOWER_DIFFICULTIES[difficulty]
    return pf_floor2((cfg["cols"] / (cfg["cols"] - cfg["bombs"])) ** levels_cleared * FAIR_RTP)


# ---------------- seeds storage ----------------
def init_fair_db():
    conn = get_db_connection()
    if not conn:
        return
    try:
        with conn:
            with conn.cursor() as cur:
                cur.execute("""
                    CREATE TABLE IF NOT EXISTS fair_seeds (
                        user_id BIGINT PRIMARY KEY,
                        server_seed TEXT,
                        client_seed TEXT,
                        nonce BIGINT DEFAULT 0
                    )
                """)
                cur.execute("""
                    CREATE TABLE IF NOT EXISTS fair_revealed_seeds (
                        seed_hash TEXT PRIMARY KEY,
                        server_seed TEXT,
                        user_id BIGINT
                    )
                """)
    except Exception as e:
        print(f"DB init_fair error: {e}")
    finally:
        conn.close()

def load_fair_from_db():
    conn = get_db_connection()
    if not conn:
        return
    try:
        with conn.cursor(cursor_factory=RealDictCursor) as cur:
            cur.execute("SELECT user_id, server_seed, client_seed, nonce FROM fair_seeds")
            for r in cur.fetchall():
                fair_seeds[int(r["user_id"])] = {
                    "server_seed": r["server_seed"],
                    "client_seed": r["client_seed"],
                    "nonce": int(r["nonce"] or 0),
                }
            cur.execute("SELECT seed_hash, server_seed FROM fair_revealed_seeds")
            for r in cur.fetchall():
                revealed_server_seeds[r["seed_hash"]] = r["server_seed"]
    except Exception as e:
        print(f"DB load_fair error: {e}")
    finally:
        conn.close()

def persist_fair_seed(uid):
    st = fair_seeds.get(uid)
    conn = get_db_connection()
    if not conn or not st:
        return
    try:
        with conn:
            with conn.cursor() as cur:
                cur.execute(
                    """
                    INSERT INTO fair_seeds (user_id, server_seed, client_seed, nonce) VALUES (%s, %s, %s, %s)
                    ON CONFLICT (user_id) DO UPDATE SET server_seed = EXCLUDED.server_seed,
                        client_seed = EXCLUDED.client_seed, nonce = EXCLUDED.nonce
                    """,
                    (uid, st["server_seed"], st["client_seed"], st["nonce"])
                )
    except Exception as e:
        print(f"DB persist_fair_seed error ({uid}): {e}")
    finally:
        conn.close()

def persist_revealed_seed(seed_hash, server_seed, uid):
    conn = get_db_connection()
    if not conn:
        return
    try:
        with conn:
            with conn.cursor() as cur:
                cur.execute(
                    "INSERT INTO fair_revealed_seeds (seed_hash, server_seed, user_id) VALUES (%s, %s, %s) ON CONFLICT (seed_hash) DO NOTHING",
                    (seed_hash, server_seed, uid)
                )
    except Exception as e:
        print(f"DB persist_revealed_seed error: {e}")
    finally:
        conn.close()

def fair_get_state(uid):
    st = fair_seeds.get(uid)
    if not st:
        st = {"server_seed": _pf_secrets.token_hex(32), "client_seed": _pf_secrets.token_hex(10), "nonce": 0}
        fair_seeds[uid] = st
        persist_fair_seed(uid)
    return st

def fair_take_seeds(uid):
    """Seeds for the next bet. The server seed is used for this ONE bet only:
    a fresh one is prepared right away for the next bet, so revealing this
    seed after the game can never help predict another game."""
    st = fair_get_state(uid)
    seeds = {"server_seed": st["server_seed"], "client_seed": st["client_seed"], "nonce": st["nonce"]}
    st["nonce"] += 1
    st["server_seed"] = _pf_secrets.token_hex(32)
    persist_fair_seed(uid)
    return seeds

def fair_reveal(seeds, uid):
    """Game is over -> publish its server seed so anyone can verify it."""
    seed_hash = pf_sha256(seeds["server_seed"])
    if revealed_server_seeds.get(seed_hash) != seeds["server_seed"]:
        revealed_server_seeds[seed_hash] = seeds["server_seed"]
        persist_revealed_seed(seed_hash, seeds["server_seed"], uid)

def fair_meta(seeds):
    return {"server_seed_hash": pf_sha256(seeds["server_seed"]), "client_seed": seeds["client_seed"], "nonce": seeds["nonce"]}

def fair_rotate(uid, new_client_seed=None):
    st = fair_get_state(uid)
    old_seed = st["server_seed"]
    old_hash = pf_sha256(old_seed)
    revealed_server_seeds[old_hash] = old_seed
    persist_revealed_seed(old_hash, old_seed, uid)
    st["server_seed"] = _pf_secrets.token_hex(32)
    st["client_seed"] = new_client_seed or _pf_secrets.token_hex(10)
    st["nonce"] = 0
    persist_fair_seed(uid)
    return old_seed, old_hash

def fair_link(seeds, kind=None, gid=None, reveal=False, **extra):
    """Browser link that shows the fairness details of this bet (needs VERIFY_URL).
    reveal=True only after the game is over: adds the real server seed."""
    if not VERIFY_URL:
        return None
    params = {}
    if kind:
        params["game"] = kind
    if gid:
        params["id"] = gid
    params["hash"] = pf_sha256(seeds["server_seed"])
    params["client"] = seeds["client_seed"]
    params["nonce"] = seeds["nonce"]
    if reveal:
        params["server"] = seeds["server_seed"]
    for k, v in extra.items():
        if v is not None:
            params[k] = v
    return f"{VERIFY_URL.rstrip('/')}/?{_pf_urlencode(params)}"

def fair_footer(seeds, kind=None, gid=None, reveal=False, **extra):
    link = fair_link(seeds, kind, gid, reveal, **extra)
    if not link:
        return f"\n\n🔐 _Provably Fair_ · Nonce `{seeds['nonce']}` · /fair"
    return f"\n\n🔐 [Provably Fair]({link})"

def build_fair_text(uid):
    st = fair_get_state(uid)
    return (
        "🔐 *Provably Fair*\n\n"
        f"🔒 Next Server Seed (hashed):\n`{pf_sha256(st['server_seed'])}`\n\n"
        f"👤 Client Seed: `{st['client_seed']}`\n"
        f"🔢 Nonce (next bet): `{st['nonce']}`\n\n"
        "ℹ️ Every Mines, Tower, Limbo and Blackjack bet gets its own server seed. "
        "It is revealed automatically when the game ends — just tap *Provably Fair* on the result message.\n"
        "✏️ Set your own client seed: `/setseed yourtext`"
    )

def fair_keyboard():
    return {"inline_keyboard": [[{"text": "🔄 Change Seed (reveal)", "callback_data": "pf_rotate"}]]}

def clean_client_seed(raw):
    cleaned = re.sub(r"[^A-Za-z0-9\-]", "", raw or "")[:32]
    return cleaned or None

def has_open_fair_game(uid):
    return uid in active_mines_games or uid in active_tower_games or uid in active_bj_games


# ---------------- shared bet helpers ----------------
def fair_validate_bet(chat_id, user_id, bet_inr, example, cat="special"):
    if is_player_in_active_game(user_id):
        send_message(chat_id, f"⚠️ You already have an active game (*{get_active_game_summary(user_id)}*)! Finish it before starting a new game.")
        return False
    if bet_inr is None or bet_inr <= 0:
        send_message(chat_id, f"⚠️ Enter a valid bet amount. Example: `{example}`")
        return False
    if bet_out_of_limits(bet_inr, cat):
        send_message(chat_id, bet_limit_text(cat, user_id))
        return False
    bal = float(user_balances.get(user_id, 0.0))
    if bal < bet_inr:
        send_message(chat_id, f"❌ *Insufficient Balance!*\n💰 Your Balance: *{format_money(bal, user_id)}*\n🎯 Required Bet: *{format_money(bet_inr, user_id)}*")
        return False
    return True

def fair_settle(user_id, game_key, game_label, emoji, title, bet, mult, won, gid, outcome_meta):
    """won=True pays bet*mult. Returns (win_amt, profit)."""
    global HOUSE_BALANCE
    if won:
        win_amt = bet * mult
        profit = win_amt - bet
        user_balances[user_id] = float(user_balances.get(user_id, 0.0)) + win_amt
        HOUSE_BALANCE -= profit
        persist_user(user_id)
        save_config_value("house_balance", HOUSE_BALANCE)
        update_user_stats(user_id, game_key, bet, profit, profit > 0)
        record_user_bet(user_id, game_label, bet, profit, "WON", game_id=gid)
        if profit > 0:
            log_win_to_channel(user_id, emoji, title, win_amt, fmt_mult(mult))
    else:
        win_amt = 0.0
        profit = -bet
        HOUSE_BALANCE += bet
        save_config_value("house_balance", HOUSE_BALANCE)
        update_user_stats(user_id, game_key, bet, profit, False)
        record_user_bet(user_id, game_label, bet, profit, "LOST", game_id=gid)
    mark_game_finished(gid, "completed", extra_meta=dict(outcome_meta, outcome="WON" if won else "LOST", pnl=profit))
    return win_amt, profit


def signed_money(amount_in_inr, user_id):
    if amount_in_inr < 0:
        return "-" + format_money(-amount_in_inr, user_id)
    return format_money(amount_in_inr, user_id)

def fair_result_text(title, bet, mult, win_amt, user_id):
    return (
        f"{title}\n\n"
        f"Profit: *{signed_money(win_amt - bet, user_id)}*\n"
        f"Multiplier: *{fmt_mult(mult)}*\n"
        f"Bet: {format_money(bet, user_id)}\n"
        f"Payout: *{format_money(win_amt, user_id)}*"
    )


# ---------------- LIMBO ----------------
def run_limbo_game(chat_id, user_id, bet_inr, target, reply_to_message_id=None):
    if not fair_validate_bet(chat_id, user_id, bet_inr, "/limbo 50 2", cat="limbo"):
        return
    _pay_err = limbo_payout_error(bet_inr, target, user_id)
    if _pay_err:
        send_message(chat_id, _pay_err, reply_to_message_id=reply_to_message_id)
        return
    gid = generate_game_id()
    user_balances[user_id] = float(user_balances.get(user_id, 0.0)) - bet_inr
    persist_user(user_id)
    seeds = fair_take_seeds(user_id)
    meta = dict(fair_meta(seeds), chat_id=chat_id, target=target)
    register_game_record(gid, "limbo", user_id, bet_inr, meta=meta, refund_on_cancel=False)

    result = pf_limbo_result(seeds)
    won = result >= target
    win_amt, _ = fair_settle(user_id, "limbo", f"Limbo ({target:.2f}x)", "🚀", "Limbo", bet_inr, target, won, gid, {"result": result})

    fair_reveal(seeds, user_id)
    text_out = (
        f"🚀 *Limbo* (`{gid}`)\n\n"
        f"🎯 Target: *{target:.2f}x*\n"
        f"📈 Result: *{result:.2f}x* {'✅' if won else '❌'}\n"
        f"💰 Bet: {format_money(bet_inr, user_id)}"
    ) + fair_footer(seeds, "limbo", gid, reveal=True, target=f"{target:.2f}", result=f"{result:.2f}")
    payload = {"kind": "limbo", "owner_id": user_id, "bet": bet_inr, "target": target}
    sent = send_message(chat_id, text_out, reply_markup=create_post_match_keyboard(user_id, payload), reply_to_message_id=reply_to_message_id)
    remember_button_owner(chat_id, sent.get("result", {}).get("message_id") if sent and sent.get("ok") else None, user_id)


# ---------------- MINES ----------------
def mines_keyboard(game):
    rows = []
    for r in range(5):
        row = []
        for c in range(5):
            idx = r * 5 + c
            if idx in game["revealed"]:
                row.append({"text": "💎", "callback_data": "mn_x"})
            else:
                row.append({"text": "🟦", "callback_data": f"mn_t_{idx}"})
        rows.append(row)
    picks = len(game["revealed"])
    ctrl = [{"text": "🎲 Random", "callback_data": "mn_rand"}]
    if picks > 0:
        mult = pf_mines_multiplier(game["mines"], picks)
        ctrl.append({"text": f"💰 Cashout {fmt_mult(mult)}", "callback_data": "mn_cash"})
    rows.append(ctrl)
    return {"inline_keyboard": rows}

def mines_status_text(game, user_id):
    picks = len(game["revealed"])
    cur = pf_mines_multiplier(game["mines"], picks)
    nxt = pf_mines_multiplier(game["mines"], picks + 1) if picks < MINES_TILES - game["mines"] else cur
    return (
        f"💣 *Mines* (`{game['game_id']}`)\n\n"
        f"💣 Mines: *{game['mines']}* | 💎 Found: *{picks}*\n"
        f"💰 Bet: {format_money(game['bet'], user_id)}\n"
        f"📈 Current: *{fmt_mult(cur)}* → Next: *{fmt_mult(nxt)}*\n\n"
        "Pick a tile:" + fair_footer(game["seeds"], "mines", game["game_id"], mines=game["mines"])
    )

def mines_final_grid(game, hit_idx=None):
    lines = []
    for r in range(5):
        cells = []
        for c in range(5):
            idx = r * 5 + c
            if idx == hit_idx:
                cells.append("💥")
            elif idx in game["layout"]:
                cells.append("💣")
            elif idx in game["revealed"]:
                cells.append("💎")
            else:
                cells.append("▫️")
        lines.append("".join(cells))
    return "\n".join(lines)

def start_mines_game(chat_id, user_id, bet_inr, mines, reply_to_message_id=None):
    if not fair_validate_bet(chat_id, user_id, bet_inr, "/mines 50 3"):
        return
    gid = generate_game_id()
    user_balances[user_id] = float(user_balances.get(user_id, 0.0)) - bet_inr
    persist_user(user_id)
    seeds = fair_take_seeds(user_id)
    register_game_record(gid, "mines", user_id, bet_inr, meta=dict(fair_meta(seeds), chat_id=chat_id, mines=mines), refund_on_cancel=True)
    game = {
        "game_id": gid, "chat_id": chat_id, "message_id": None, "bet": bet_inr,
        "mines": mines, "seeds": seeds, "layout": set(pf_mines_layout(seeds, mines)), "revealed": [],
    }
    active_mines_games[user_id] = game
    sent = send_message(chat_id, mines_status_text(game, user_id), reply_markup=mines_keyboard(game), reply_to_message_id=reply_to_message_id)
    msg_id = sent.get("result", {}).get("message_id") if sent and sent.get("ok") else None
    game["message_id"] = msg_id
    remember_button_owner(chat_id, msg_id, user_id)

def mines_result_rows(game, hit_idx=None):
    """Final board as buttons: 💣 = mine, 💎 = safe, red = the mine you hit, green = your picks."""
    rows = []
    for r in range(5):
        row = []
        for c in range(5):
            idx = r * 5 + c
            btn = {"text": "💣" if idx in game["layout"] else "💎", "callback_data": "mn_done"}
            if idx == hit_idx:
                btn["style"] = "danger"
            elif idx in game["revealed"]:
                btn["style"] = "success"
            row.append(btn)
        rows.append(row)
    return rows

def finish_mines_game(user_id, game, won, hit_idx=None):
    active_mines_games.pop(user_id, None)
    picks = len(game["revealed"])
    mult = pf_mines_multiplier(game["mines"], picks) if won else 0.0
    win_amt, _ = fair_settle(user_id, "mines", f"Mines ({game['mines']}💣)", "💣", "Mines", game["bet"], mult, won,
                             game["game_id"], {"picks": picks, "revealed": list(game["revealed"])})
    fair_reveal(game["seeds"], user_id)
    text_out = fair_result_text("*Mines* 💣", game["bet"], mult, win_amt, user_id) + fair_footer(
        game["seeds"], "mines", game["game_id"], reveal=True, mines=game["mines"],
        picks=",".join(str(i) for i in game["revealed"]) or None,
        hit=hit_idx)
    grid = mines_result_rows(game, hit_idx)
    payload = {"kind": "mines", "owner_id": user_id, "bet": game["bet"], "mines": game["mines"], "result_grid": grid}
    post_kb = create_post_match_keyboard(user_id, payload)
    edit_message(game["chat_id"], game["message_id"], text_out,
                 reply_markup={"inline_keyboard": grid + post_kb["inline_keyboard"]})

def handle_mines_callback(user_id, chat_id, message_id, data):
    game = active_mines_games.get(user_id)
    if not game:
        if data != "mn_x":
            edit_message(chat_id, message_id, "⚠️ Mines session expired. Start a new game with `/mines <amount> <mines>`.")
        return
    if game.get("message_id") is None:
        game["message_id"] = message_id
    if data == "mn_x":
        return
    if data == "mn_cash":
        if game["revealed"]:
            finish_mines_game(user_id, game, True)
        return
    if data == "mn_rand":
        hidden = [i for i in range(MINES_TILES) if i not in game["revealed"]]
        idx = _pf_secrets.choice(hidden)
    else:
        try:
            idx = int(data.replace("mn_t_", "", 1))
        except ValueError:
            return
        if idx < 0 or idx >= MINES_TILES or idx in game["revealed"]:
            return
    if idx in game["layout"]:
        finish_mines_game(user_id, game, False, hit_idx=idx)
        return
    game["revealed"].append(idx)
    if len(game["revealed"]) >= MINES_TILES - game["mines"]:
        finish_mines_game(user_id, game, True)
        return
    edit_message(game["chat_id"], game["message_id"], mines_status_text(game, user_id), reply_markup=mines_keyboard(game))


# ---------------- TOWER ----------------
def tower_keyboard(game):
    cfg = TOWER_DIFFICULTIES[game["difficulty"]]
    level = len(game["picks"])
    rows = []
    for lvl in range(TOWER_LEVELS - 1, -1, -1):
        row = []
        for c in range(cfg["cols"]):
            if lvl < level:
                txt = "✅" if game["picks"][lvl] == c else "⬛"
                row.append({"text": txt, "callback_data": "tw_x"})
            elif lvl == level:
                row.append({"text": f"❓ {fmt_mult(pf_tower_multiplier(game['difficulty'], lvl + 1))}", "callback_data": f"tw_p_{c}"})
            else:
                row.append({"text": "⬛", "callback_data": "tw_x"})
        rows.append(row)
    ctrl = [{"text": "🎲 Random", "callback_data": "tw_rand"}]
    if level > 0:
        ctrl.append({"text": f"💰 Cashout {fmt_mult(pf_tower_multiplier(game['difficulty'], level))}", "callback_data": "tw_cash"})
    rows.append(ctrl)
    return {"inline_keyboard": rows}

def tower_status_text(game, user_id):
    level = len(game["picks"])
    cfg = TOWER_DIFFICULTIES[game["difficulty"]]
    return (
        f"🗼 *Tower* (`{game['game_id']}`)\n\n"
        f"⚙️ Mode: *{game['difficulty'].title()}* ({cfg['cols']} tiles, {cfg['bombs']} 💀 per row)\n"
        f"🪜 Level: *{level}/{TOWER_LEVELS}*\n"
        f"💰 Bet: {format_money(game['bet'], user_id)}\n"
        f"📈 Current: *{fmt_mult(pf_tower_multiplier(game['difficulty'], level))}*\n\n"
        "Climb! Pick a tile on the ❓ row:" + fair_footer(game["seeds"], "tower", game["game_id"], difficulty=game["difficulty"])
    )

def tower_final_grid(game, hit=None):
    cfg = TOWER_DIFFICULTIES[game["difficulty"]]
    lines = []
    for lvl in range(TOWER_LEVELS - 1, -1, -1):
        cells = []
        for c in range(cfg["cols"]):
            if hit == (lvl, c):
                cells.append("💥")
            elif c in game["layout"][lvl]:
                cells.append("💀")
            elif lvl < len(game["picks"]) and game["picks"][lvl] == c:
                cells.append("✅")
            else:
                cells.append("🟩")
        lines.append("".join(cells))
    return "\n".join(lines)

def start_tower_game(chat_id, user_id, bet_inr, difficulty, reply_to_message_id=None):
    if not fair_validate_bet(chat_id, user_id, bet_inr, "/tower 50 easy"):
        return
    gid = generate_game_id()
    user_balances[user_id] = float(user_balances.get(user_id, 0.0)) - bet_inr
    persist_user(user_id)
    seeds = fair_take_seeds(user_id)
    register_game_record(gid, "tower", user_id, bet_inr, meta=dict(fair_meta(seeds), chat_id=chat_id, difficulty=difficulty), refund_on_cancel=True)
    game = {
        "game_id": gid, "chat_id": chat_id, "message_id": None, "bet": bet_inr,
        "difficulty": difficulty, "seeds": seeds, "layout": pf_tower_layout(seeds, difficulty), "picks": [],
    }
    active_tower_games[user_id] = game
    sent = send_message(chat_id, tower_status_text(game, user_id), reply_markup=tower_keyboard(game), reply_to_message_id=reply_to_message_id)
    msg_id = sent.get("result", {}).get("message_id") if sent and sent.get("ok") else None
    game["message_id"] = msg_id
    remember_button_owner(chat_id, msg_id, user_id)

def tower_result_rows(game, hit=None):
    """Final tower as buttons: 🐍 = skull tile, 🥚 = safe tile, red = the tile that was hit, green = your picks."""
    cfg = TOWER_DIFFICULTIES[game["difficulty"]]
    picks = game["picks"]
    rows = []
    for lvl in range(TOWER_LEVELS - 1, -1, -1):
        row = []
        for c in range(cfg["cols"]):
            btn = {"text": "🐍" if c in game["layout"][lvl] else "🥚", "callback_data": "tw_done"}
            if hit == (lvl, c):
                btn["style"] = "danger"
            elif lvl < len(picks) and picks[lvl] == c:
                btn["style"] = "success"
            row.append(btn)
        rows.append(row)
    return rows

def finish_tower_game(user_id, game, won, hit=None):
    active_tower_games.pop(user_id, None)
    level = len(game["picks"])
    mult = pf_tower_multiplier(game["difficulty"], level) if won else 0.0
    win_amt, _ = fair_settle(user_id, "tower", f"Tower ({game['difficulty'].title()})", "🗼", "Tower", game["bet"], mult, won,
                             game["game_id"], {"levels": level, "picks": list(game["picks"])})
    fair_reveal(game["seeds"], user_id)
    text_out = fair_result_text("*Tower* 🗼", game["bet"], mult, win_amt, user_id)
    text_out += fair_footer(game["seeds"], "tower", game["game_id"], reveal=True, difficulty=game["difficulty"],
                            picks=",".join(str(c) for c in game["picks"]) or None,
                            hit=hit[1] if hit else None)
    grid = tower_result_rows(game, hit)
    payload = {"kind": "tower", "owner_id": user_id, "bet": game["bet"], "difficulty": game["difficulty"], "result_grid": grid}
    post_kb = create_post_match_keyboard(user_id, payload)
    edit_message(game["chat_id"], game["message_id"], text_out,
                 reply_markup={"inline_keyboard": grid + post_kb["inline_keyboard"]})

def handle_tower_callback(user_id, chat_id, message_id, data):
    game = active_tower_games.get(user_id)
    if not game:
        if data != "tw_x":
            edit_message(chat_id, message_id, "⚠️ Tower session expired. Start a new game with `/tower <amount> <mode>`.")
        return
    if game.get("message_id") is None:
        game["message_id"] = message_id
    if data == "tw_x":
        return
    level = len(game["picks"])
    if data == "tw_cash":
        if level > 0:
            finish_tower_game(user_id, game, True)
        return
    cols = TOWER_DIFFICULTIES[game["difficulty"]]["cols"]
    if data == "tw_rand":
        col = _pf_secrets.randbelow(cols)
    else:
        try:
            col = int(data.replace("tw_p_", "", 1))
        except ValueError:
            return
        if col < 0 or col >= cols:
            return
    if col in game["layout"][level]:
        finish_tower_game(user_id, game, False, hit=(level, col))
        return
    game["picks"].append(col)
    if len(game["picks"]) >= TOWER_LEVELS:
        finish_tower_game(user_id, game, True)
        return
    edit_message(game["chat_id"], game["message_id"], tower_status_text(game, user_id), reply_markup=tower_keyboard(game))


# ---------------- VERIFY ----------------
def build_verify_text(gid):
    gid = gid.strip().upper()
    rec = game_id_registry.get(gid)
    if not rec or rec.get("kind") not in ("mines", "tower", "limbo"):
        return f"⚠️ No Mines / Tower / Limbo game found with ID `{gid}`."
    meta = rec.get("meta", {})
    seed_hash = meta.get("server_seed_hash")
    server_seed = revealed_server_seeds.get(seed_hash)
    head = (
        f"🔍 *Verify* `{gid}` ({rec['kind'].title()})\n\n"
        f"🔒 Server Seed Hash: `{seed_hash}`\n"
        f"👤 Client Seed: `{meta.get('client_seed')}`\n"
        f"🔢 Nonce: `{meta.get('nonce')}`\n"
    )
    if not server_seed:
        return head + "\n⏳ This game is still running. The server seed is revealed automatically when it ends."
    seeds = {"server_seed": server_seed, "client_seed": meta.get("client_seed"), "nonce": int(meta.get("nonce", 0))}
    head += f"🔓 Server Seed: `{server_seed}`\n✅ Hash matches: *{'YES' if pf_sha256(server_seed) == seed_hash else 'NO'}*\n\n"
    link_params = f"server={server_seed}&client={seeds['client_seed']}&nonce={seeds['nonce']}"
    if rec["kind"] == "limbo":
        res = pf_limbo_result(seeds)
        head += f"🚀 Limbo result: *{res:.2f}x* (target {float(meta.get('target', 0)):.2f}x)"
        link_params = f"game=limbo&{link_params}"
    elif rec["kind"] == "mines":
        m = int(meta.get("mines", MINES_DEFAULT))
        layout = sorted(t + 1 for t in pf_mines_layout(seeds, m))
        head += f"💣 Mine tiles (1-25, left→right, top→bottom): `{', '.join(map(str, layout))}`"
        link_params = f"game=mines&mines={m}&{link_params}"
    else:
        d = meta.get("difficulty", "easy")
        layout = pf_tower_layout(seeds, d)
        rows = " | ".join(f"L{i + 1}:{'/'.join(str(c + 1) for c in row)}" for i, row in enumerate(layout))
        head += f"💀 Skull tiles per level (bottom→top): `{rows}`"
        link_params = f"game=tower&difficulty={d}&{link_params}"
    if VERIFY_URL:
        head += f"\n\n🌐 Check online: {VERIFY_URL.rstrip('/')}/?{link_params}"
    return head


# ---------------- COMMAND + CALLBACK ROUTERS ----------------
FAIR_CMD_RE = rf"^/(mines|tower|limbo|fair|setseed|verify)(?:@{re.escape(BOT_USERNAME.lstrip('@'))})?(?:\s|$)"

def handle_fair_command(chat_id, chat_type, user_id, text, message):
    m = re.match(FAIR_CMD_RE, text, re.IGNORECASE)
    cmd = m.group(1).lower()
    parts = text.split()
    reply_to = message.get("message_id") if chat_type in ["group", "supergroup"] else None

    if cmd == "fair":
        sent = send_message(chat_id, build_fair_text(user_id), reply_markup=fair_keyboard())
        remember_button_owner(chat_id, sent.get("result", {}).get("message_id") if sent and sent.get("ok") else None, user_id)
        return

    if cmd == "setseed":
        new_seed = clean_client_seed(parts[1]) if len(parts) > 1 else None
        if not new_seed:
            send_message(chat_id, "⚠️ Usage: `/setseed yourtext` (letters, numbers, - only, max 32)")
            return
        if has_open_fair_game(user_id):
            send_message(chat_id, "⚠️ Finish your Mines / Tower / Blackjack game before changing seeds.")
            return
        old_seed, old_hash = fair_rotate(user_id, new_seed)
        send_message(chat_id, f"✅ Client seed set to `{new_seed}`.\n\n🔓 Previous server seed revealed:\n`{old_seed}`\n\n" + build_fair_text(user_id))
        return

    if cmd == "verify":
        if len(parts) < 2:
            send_message(chat_id, "⚠️ Usage: `/verify XC-XXXXXXX-XXXX`")
            return
        send_message(chat_id, build_verify_text(parts[1]))
        return

    bet_inr = parse_user_amount(parts[1], user_id) if len(parts) > 1 else parse_user_amount("10", user_id)

    if cmd == "limbo":
        try:
            target = float(parts[2].lower().rstrip("x")) if len(parts) > 2 else 2.0
        except ValueError:
            target = None
        if target is None or target < LIMBO_MIN_TARGET or target > LIMBO_MAX_TARGET:
            send_message(chat_id, f"⚠️ Target must be {LIMBO_MIN_TARGET:.2f}x – {LIMBO_MAX_TARGET:.0f}x. Example: `/limbo 50 2`")
            return
        run_limbo_game(chat_id, user_id, bet_inr, round(target, 2), reply_to_message_id=reply_to)
    elif cmd == "mines":
        try:
            mines = int(parts[2]) if len(parts) > 2 else MINES_DEFAULT
        except ValueError:
            mines = None
        if mines is None or mines < 1 or mines > 24:
            send_message(chat_id, "⚠️ Mines must be 1–24. Example: `/mines 50 3`")
            return
        start_mines_game(chat_id, user_id, bet_inr, mines, reply_to_message_id=reply_to)
    elif cmd == "tower":
        diff = parts[2].lower() if len(parts) > 2 else "easy"
        if diff not in TOWER_DIFFICULTIES:
            send_message(chat_id, "⚠️ Mode must be `easy`, `medium`, `hard`, `expert` or `master`. Example: `/tower 50 easy`")
            return
        start_tower_game(chat_id, user_id, bet_inr, diff, reply_to_message_id=reply_to)

def handle_fair_callback(chat_id, message_id, user_id, data):
    with get_turn_lock(f"fair_{user_id}"):
        if data in ("tw_done", "mn_done"):
            return
        if data.startswith("mn_"):
            handle_mines_callback(user_id, chat_id, message_id, data)
        elif data.startswith("tw_"):
            handle_tower_callback(user_id, chat_id, message_id, data)
        elif data == "pf_rotate":
            if has_open_fair_game(user_id):
                send_message(chat_id, "⚠️ Finish your Mines / Tower / Blackjack game before changing seeds.")
                return
            old_seed, _ = fair_rotate(user_id)
            edit_message(chat_id, message_id, f"🔓 *Previous server seed revealed:*\n`{old_seed}`\n\n" + build_fair_text(user_id), reply_markup=fair_keyboard())

def restart_fair_game(chat_id, user_id, payload, next_bet):
    kind = payload.get("kind")
    if kind == "limbo":
        run_limbo_game(chat_id, user_id, next_bet, float(payload.get("target", 2.0)))
    elif kind == "mines":
        start_mines_game(chat_id, user_id, next_bet, int(payload.get("mines", MINES_DEFAULT)))
    elif kind == "tower":
        start_tower_game(chat_id, user_id, next_bet, payload.get("difficulty", "easy"))
# ---------------- BLACKJACK (provably fair deck) ----------------
def pf_bj_cards(seeds, count):
    """Card i of the hand = float i of the bet: 0..51 -> rank (i % 13) + suit (i // 13).
    Deal order: you, you, dealer, dealer, then your hits, then the dealer's draws."""
    floats = pf_floats(seeds["server_seed"], seeds["client_seed"], seeds["nonce"], count)
    cards = []
    for f in floats:
        idx = int(_pf_math.floor(f * 52))
        cards.append(f"{DECK_RANKS[idx % 13]}{DECK_SUITS[idx // 13]}")
    return cards

def bj_draw(bj):
    seeds = bj.get("seeds")
    if not seeds:
        return draw_card()
    pos = bj.get("drawn", 0)
    bj["drawn"] = pos + 1
    return pf_bj_cards(seeds, pos + 1)[pos]

def bj_fair_footer(bj, reveal=False):
    seeds = bj.get("seeds")
    if not seeds:
        return ""
    extra = {}
    if reveal:
        extra = {"pc": len(bj["player_cards"]), "dc": len(bj["dealer_cards"])}
    return fair_footer(seeds, "bj", bj.get("game_id"), reveal=reveal, **extra)

def start_bj_game(chat_id, user_id, bet_inr):
    gid = generate_game_id()
    user_balances[user_id] = float(user_balances.get(user_id, 0.0)) - bet_inr
    persist_user(user_id)
    seeds = fair_take_seeds(user_id)
    register_game_record(gid, "blackjack", user_id, bet_inr, meta=dict(fair_meta(seeds), chat_id=chat_id), refund_on_cancel=True)
    bj = {
        "game_id": gid,
        "chat_id": chat_id,
        "message_id": None,
        "bet": bet_inr,
        "seeds": seeds,
        "drawn": 0,
        "player_cards": [],
        "dealer_cards": [],
        "doubled": False,
    }
    bj["player_cards"] = [bj_draw(bj), bj_draw(bj)]
    bj["dealer_cards"] = [bj_draw(bj), bj_draw(bj)]
    p_tot = calculate_hand_total(bj["player_cards"])
    can_double = float(user_balances.get(user_id, 0.0)) >= bet_inr
    table_msg = (
        f"🃏 *Blackjack Started!* (`{gid}`)\n\n"
        f"👤 Your Hand: {format_cards(bj['player_cards'])} (*{p_tot}*)\n"
        f"🤖 Dealer Shows: `{bj['dealer_cards'][0]}` `[?]`\n"
        f"💰 Bet: {format_money(bet_inr, user_id)}\n\n"
        f"Choose your move:" + bj_fair_footer(bj)
    )
    active_bj_games[user_id] = bj
    sent = send_message(chat_id, table_msg, reply_markup=bj_action_keyboard(can_double=can_double))
    msg_id = sent.get("result", {}).get("message_id") if sent and sent.get("ok") else None
    bj["message_id"] = msg_id
    remember_button_owner(chat_id, msg_id, user_id)

# ===================== END PROVABLY FAIR GAMES =====================


@app.route('/')
def index():
    return f"{BOT_USERNAME} Casino Bot is Live!", 200

_seen_updates = collections.OrderedDict()
_seen_updates_lock = threading.Lock()
_user_locks = {}
_user_locks_guard = threading.Lock()
USER_LOCK_TIMEOUT = 60

def get_user_lock(uid):
    """One re-entrant lock per user: bets/balance changes of the same user never run in parallel."""
    with _user_locks_guard:
        lk = _user_locks.get(uid)
        if lk is None:
            lk = threading.RLock()
            _user_locks[uid] = lk
        return lk

def _update_user_id(data):
    for k in ("message", "callback_query", "edited_message"):
        obj = data.get(k)
        if isinstance(obj, dict):
            frm = obj.get("from") or {}
            if frm.get("id") is not None:
                return frm["id"]
    return None

@app.route('/webhook', methods=['POST'])
def telegram_webhook():
    helper_call = getattr(_tg_ctx, "api", None) is not None  # helper_webhook already verified its own secret
    if not helper_call:
        got = request.headers.get("X-Telegram-Bot-Api-Secret-Token", "")
        if not hmac.compare_digest(got, TELEGRAM_WEBHOOK_SECRET):
            return "Unauthorized", 401

    data = request.get_json(silent=True)
    if not isinstance(data, dict):
        return jsonify({'status': 'error'}), 400

    # Telegram re-sends an update if we are slow -> ignore duplicates (no double bets)
    upd_id = data.get("update_id")
    if upd_id is not None:
        key = ("helper" if helper_call else "main", upd_id)
        with _seen_updates_lock:
            if key in _seen_updates:
                return jsonify({'status': 'ok'}), 200
            _seen_updates[key] = time.time()
            while len(_seen_updates) > 5000:
                _seen_updates.popitem(last=False)

    uid = _update_user_id(data)
    if uid is None:
        return _telegram_webhook_inner()
    lock = get_user_lock(uid)
    if not lock.acquire(timeout=USER_LOCK_TIMEOUT):
        return jsonify({'status': 'ok'}), 200
    try:
        return _telegram_webhook_inner()
    finally:
        lock.release()

def _telegram_webhook_inner():
    global HOUSE_BALANCE, MIN_BET, MAX_BET, EXCHANGE_RATE, MAINTENANCE_MODE, DEPOSIT_ENABLED, WITHDRAW_ENABLED, DM_GAMES_ENABLED, GROUP_LINK, MIN_DEPOSIT, MIN_WITHDRAW, LIMBO_MAX_PAYOUT
    try:
        data = request.get_json()
        if not data:
            return jsonify({'status': 'error'}), 400
        _tg_ctx.reply_chat = None
        _tg_ctx.reply_mid = None
            
        if 'message' in data:
            message = data['message']
            chat_id = message['chat'].get('id')
            chat_type = message['chat'].get('type')
            user_id = message['from'].get('id')

            if message['from'].get('is_bot') and user_id in helper_ids():
                return jsonify({'status': 'ok'}), 200

            # Every answer goes out as a reply to this message.
            _tg_ctx.reply_chat = chat_id
            _tg_ctx.reply_mid = message.get('message_id')

            if 'reply_to_message' in message and message['reply_to_message'].get('from'):
                register_user_identity(message['reply_to_message']['from'])

            # Groups: /addbal and /deductbal are the only admin commands that work here.
            # Other admin commands work only in DM (no answer in groups, even from the owner).
            # Player commands and games work in both groups and DM.
            if chat_type in ['group', 'supergroup']:
                _gtext = (message.get('text') or '').strip()
                if is_group_balance_command(_gtext):
                    if not message['from'].get('is_bot'):
                        register_user_identity(message.get('from'))
                    handle_group_balance_command(chat_id, user_id, message)
                    return jsonify({'status': 'ok'}), 200
                if is_dm_only_admin_command(_gtext):
                    return jsonify({'status': 'ok'}), 200
            
            if chat_type in ['group', 'supergroup'] and not is_group_approved(chat_id) and user_id not in admin_list:
                if 'text' in message and message['text'].startswith('/myid'):
                    send_message(chat_id, f"📌 This Group Chat ID is: `{chat_id}`")
                return jsonify({'status': 'ok'}), 200

            if user_id in banned_users:
                send_message(chat_id, "⛔ Your account has been banned from using this bot.")
                return jsonify({'status': 'ok'}), 200
                
            if MAINTENANCE_MODE and user_id not in admin_list:
                send_message(chat_id, "🛠 *Bot is under Maintenance.* Please try again later.")
                return jsonify({'status': 'ok'}), 200
                
            register_user_identity(message.get('from'))

            # Forwarded dice/emoji: never counted -> ban from bot + group
            if handle_forwarded_dice(message, chat_id, chat_type, user_id):
                return jsonify({'status': 'ok'}), 200
                
            if user_id in admin_list and user_id in admin_states and 'text' in message:
                state = admin_states[user_id]
                text = message['text'].strip()
                action = state['action']
                
                if action == 'add_bal':
                    try:
                        parts = text.split(' ')
                        t_user = resolve_user_identifier(parts[0])
                        if t_user is None:
                            raise ValueError()
                        amt = parse_user_amount(parts[1], t_user)
                        if amt is None or amt <= 0:
                            raise ValueError()
                        if t_user not in user_balances: user_balances[t_user] = 0.0
                        user_balances[t_user] += amt
                        persist_user(t_user)
                        send_message(chat_id, f"✅ Added {format_money(amt, t_user)} to user `{t_user}`.")
                        send_message(t_user, f"💰 *Admin credited your account!* +{format_money(amt, t_user)}")
                    except Exception:
                        send_message(chat_id, "⚠️ Invalid format. Use: `<user_id/@username> <amount>`")
                    del admin_states[user_id]
                    return jsonify({'status': 'ok'}), 200
                    
                elif action == 'deduct_bal':
                    try:
                        parts = text.split(' ')
                        t_user = resolve_user_identifier(parts[0])
                        if t_user is None:
                            raise ValueError()
                        amt = parse_user_amount(parts[1], t_user)
                        if amt is None or amt <= 0:
                            raise ValueError()
                        if t_user in user_balances:
                            user_balances[t_user] = max(0.0, user_balances[t_user] - amt)
                            persist_user(t_user)
                            send_message(chat_id, f"✅ Deducted {format_money(amt, t_user)} from user `{t_user}`.")
                            send_message(t_user, f"⚠️ *Admin deducted from your account.* -{format_money(amt, t_user)}")
                    except Exception:
                        send_message(chat_id, "⚠️ Invalid format. Use: `<user_id/@username> <amount>`")
                    del admin_states[user_id]
                    return jsonify({'status': 'ok'}), 200
                    
                elif action == 'user_stats':
                    try:
                        target_u = resolve_user_identifier(text)
                        if target_u is None:
                            raise ValueError()
                        bio = generate_stats_image(target_u)
                        send_photo(chat_id, bio, caption=f"📊 Stats for User `{target_u}`")
                    except Exception:
                        send_message(chat_id, "⚠️ Invalid User ID or Username.")
                    del admin_states[user_id]
                    return jsonify({'status': 'ok'}), 200
                    
                elif action == 'ban_user':
                    try:
                        target_u = resolve_user_identifier(text)
                        if target_u is None:
                            raise ValueError()
                        banned_users.add(target_u)
                        persist_user(target_u)
                        send_message(chat_id, f"🚫 User `{target_u}` has been BANNED.")
                    except Exception:
                        send_message(chat_id, "⚠️ Invalid User ID or Username.")
                    del admin_states[user_id]
                    return jsonify({'status': 'ok'}), 200
                    
                elif action == 'unban_user':
                    try:
                        target_u = resolve_user_identifier(text)
                        if target_u is None:
                            raise ValueError()
                        if target_u in banned_users: banned_users.remove(target_u)
                        persist_user(target_u)
                        send_message(chat_id, f"✅ User `{target_u}` has been UNBANNED.")
                    except Exception:
                        send_message(chat_id, "⚠️ Invalid User ID or Username.")
                    del admin_states[user_id]
                    return jsonify({'status': 'ok'}), 200
                    
                elif action == 'grant_admin':
                    try:
                        target_u = resolve_user_identifier(text)
                        if target_u is None:
                            raise ValueError()
                        admin_list.add(target_u)
                        persist_user(target_u)
                        send_message(chat_id, f"👑 User `{target_u}` granted Admin rights.")
                    except Exception:
                        send_message(chat_id, "⚠️ Invalid User ID or Username.")
                    del admin_states[user_id]
                    return jsonify({'status': 'ok'}), 200
                    
                elif action == 'revoke_admin':
                    try:
                        target_u = resolve_user_identifier(text)
                        if target_u is None:
                            raise ValueError()
                        if target_u != ADMIN_USER_ID and target_u in admin_list:
                            admin_list.remove(target_u)
                            send_message(chat_id, f"⛔ Admin rights revoked for `{target_u}`.")
                    except Exception:
                        send_message(chat_id, "⚠️ Invalid User ID or Username.")
                    del admin_states[user_id]
                    return jsonify({'status': 'ok'}), 200
                    
                elif action == 'broadcast_all':
                    count = 0
                    for u in list(user_balances.keys()):
                        send_message(u, f"📢 *Announcement*\n\n{text}")
                        count += 1
                    send_message(chat_id, f"✅ Broadcast sent to {count} users.")
                    del admin_states[user_id]
                    return jsonify({'status': 'ok'}), 200
                    
                elif action == 'broadcast_private':
                    try:
                        parts = text.split(' ', 1)
                        target_u = resolve_user_identifier(parts[0])
                        if target_u is None:
                            raise ValueError()
                        msg = parts[1]
                        send_message(target_u, f"📢 *Admin Message*\n\n{msg}")
                        send_message(chat_id, f"✅ Private message sent to `{target_u}`.")
                    except Exception:
                        send_message(chat_id, "⚠️ Format error. Use: `<user_id/@username> <message>`")
                    del admin_states[user_id]
                    return jsonify({'status': 'ok'}), 200

            if user_id in deposit_states and 'text' in message:
                text = message['text'].strip()
                if chat_type != 'private':
                    del deposit_states[user_id]
                    send_message(chat_id, "❌ Deposit can only be done in Bot's DM (Private Chat)!", reply_markup={"inline_keyboard": [[{"text": "🤖 Open Bot DM", "url": f"https://t.me/{BOT_USERNAME.replace('@','')}"}]]})
                    return jsonify({'status': 'ok'}), 200

                if text.startswith('/'):  
                    del deposit_states[user_id]
                else:
                    del deposit_states[user_id]
                    if not DEPOSIT_ENABLED:
                        send_message(chat_id, "❌ Deposits are currently disabled by Admin.")
                        return jsonify({'status': 'ok'}), 200
                    amt_inr = parse_user_amount(text, user_id, allow_all_half=False)
                    if amt_inr and amt_inr > 0:
                        res_text, pay_kb = create_zapupi_order(amt_inr, user_id)
                        send_message(chat_id, res_text, reply_markup=pay_kb)
                    else:
                        send_message(chat_id, "⚠️ Invalid amount. Use `/deposit <amount>` or `/deposit` again.")
                    return jsonify({'status': 'ok'}), 200

            if user_id in withdrawal_states and 'text' in message:
                state = withdrawal_states[user_id]
                text = message['text'].strip()
                if chat_type != 'private':
                    del withdrawal_states[user_id]
                    send_message(chat_id, "❌ Withdrawal can only be done in Bot's DM (Private Chat)!", reply_markup={"inline_keyboard": [[{"text": "🤖 Open Bot DM", "url": f"https://t.me/{BOT_USERNAME.replace('@','')}"}]]})
                    return jsonify({'status': 'ok'}), 200

                if text.startswith('/'):
                    del withdrawal_states[user_id]
                else:
                    if state['step'] == 'waiting_amount':
                        if not WITHDRAW_ENABLED:
                            send_message(chat_id, "❌ Withdrawals are currently disabled by Admin.")
                            del withdrawal_states[user_id]
                            return jsonify({'status': 'ok'}), 200
                        if is_all_half_word(text):
                            amt_inr = withdraw_amount_from_word(text, user_id)
                            if amt_inr is not None and amt_inr <= 0:
                                send_message(chat_id, f"⚠️ Your balance is too low to withdraw. Min withdrawal is *₹{MIN_WITHDRAW:,.0f}* (plus fee).\n\nPlease enter another amount:")
                                return jsonify({'status': 'ok'}), 200
                        else:
                            amt_inr = parse_user_amount(text, user_id)
                        if not amt_inr or amt_inr <= 0:
                            send_message(chat_id, "⚠️ Invalid amount. Please enter a valid number, `all` or `half`:")
                            return jsonify({'status': 'ok'}), 200
                        wd_err = validate_withdraw_amount(amt_inr, user_id)
                        if wd_err:
                            if wd_err.startswith("❌"):
                                del withdrawal_states[user_id]
                                send_message(chat_id, wd_err)
                            else:
                                send_message(chat_id, wd_err + "\n\nPlease enter another amount:")
                            return jsonify({'status': 'ok'}), 200
                            
                        state['amount'] = amt_inr
                        state['step'] = 'waiting_upi'
                        send_message(chat_id, "🏦 *Please enter your UPI ID for payout:*\n\nExample: `yourname@ybl`")
                        return jsonify({'status': 'ok'}), 200
                        
                    elif state['step'] == 'waiting_upi':
                        clean_upi, upi_err = validate_upi_id(text)
                        if upi_err:
                            send_message(chat_id, "🚨 Invalid upi id\n\nDrop another valid upi id below:")
                            return jsonify({'status': 'ok'}), 200
                        state['upi_id'] = clean_upi
                        withdrawal_states[user_id]['step'] = 'confirming'
                        
                        bd = withdraw_breakdown(state['amount'])
                        summary = (
                            "📋 *Withdrawal Summary*\n\n"
                            f"💰 Amount: *₹{bd['requested']:,.2f}*\n"
                            f"🧾 Fee (₹{WITHDRAW_FEE_FIXED:,.0f} + {WITHDRAW_FEE_PERCENT:g}%): *₹{bd['fee']:,.2f}*\n"
                            f"➖ Cut from Balance: *₹{bd['debit']:,.2f}*\n"
                            f"✅ You Receive: *₹{bd['payout']:,.2f}*\n"
                            f"🏦 UPI ID: `{state['upi_id']}`\n\n"
                            "Please verify your details below:"
                        )
                        keyboard = {
                            "inline_keyboard": [
                                [
                                    {"text": "✅ Confirm Withdrawal", "callback_data": "wd_confirm"},
                                    {"text": "❌ Cancel", "callback_data": "wd_cancel"}
                                ]
                            ]
                        }
                        send_message(chat_id, summary, reply_markup=keyboard)
                        return jsonify({'status': 'ok'}), 200

            if user_id in admin_list and user_id in withdrawal_states and withdrawal_states[user_id].get('step') == 'waiting_reject_reason' and 'text' in message:
                reason = message['text'].strip()
                rej_state = withdrawal_states[user_id]
                target_user = rej_state['target_user']
                amt_str = rej_state['amount_str']
                wd_id = rej_state.get('wd_id')
                wd = find_withdrawal(wd_id) if wd_id else None

                if wd and wd.get("status") in ("paid", "rejected"):
                    send_message(chat_id, f"⚠️ Withdrawal `{wd_id}` is already *{wd['status']}*. Nothing changed.")
                    del withdrawal_states[user_id]
                    return jsonify({'status': 'ok'}), 200
                
                user_balances[target_user] = user_balances.get(target_user, 0.0) + rej_state['raw_amount']
                rakeback_on_withdraw_done(target_user, wd_id, rejected=True)
                persist_user(target_user)
                if wd:
                    ts_rej = current_timestamp()
                    wd["status"] = "rejected"
                    wd["processed_at"] = ts_rej
                    wd["processed_by"] = user_id
                    wd["reject_reason"] = reason
                    persist_withdrawal_status(wd_id, "rejected", ts_rej, user_id, reason)
                if rej_state.get('admin_msg_id'):
                    remove_inline_keyboard(rej_state.get('admin_chat_id', chat_id), rej_state['admin_msg_id'])
                
                id_line = f"🆔 Withdraw ID: `{wd_id}`\n" if wd_id else ""
                send_message(target_user, f"❌ *Withdrawal Request Rejected*\n\n{id_line}Amount: {amt_str}\nReason: *{reason}*\n\nYour funds have been refunded to your wallet.")
                send_message(chat_id, f"✅ Rejection sent to user `{target_user}` with reason: _{reason}_")
                del withdrawal_states[user_id]
                return jsonify({'status': 'ok'}), 200

            if 'dice' in message and user_id in active_dr_self_games:
                if handle_dr_self_dice(message, chat_id, user_id):
                    return jsonify({'status': 'ok'}), 200

            if 'dice' in message and user_id in active_games:
                active_ref = active_games[user_id]
                user_dice = message['dice']

                if isinstance(active_ref, str) and active_ref in active_pvp_games:
                    with get_turn_lock(f"pvp_{active_ref}"):
                        pvm = active_pvp_games.get(active_ref)
                        if not pvm or pvm["chat_id"] != chat_id or pvm["turn"] != user_id:
                            return jsonify({'status': 'ok'}), 200
                        if user_dice.get('emoji') != pvm["emoji"]:
                            return jsonify({'status': 'ok'}), 200

                        pvm["turn_token"] = None
                        val = user_dice.get('value', 1)
                        needed = pvm["rolls_per_round"]
                        is_p1 = (user_id == pvm["p1_id"])
                        roll_list = pvm["p1_rolls"] if is_p1 else pvm["p2_rolls"]
                        roll_list.append(val)

                        rem = needed - len(roll_list)
                        if rem > 0:
                            send_message(chat_id, f"🎲 {tag_player(user_id)} Roll `{len(roll_list)}/{needed}`: *{val}* — Send `{rem}` more `{pvm['emoji']}`!")
                            schedule_pvp_turn_timeout(chat_id, active_ref, pvm)
                            return jsonify({'status': 'ok'}), 200

                        if is_p1:
                            expr = "+".join(map(str, roll_list))
                            send_message(chat_id, f"👤 {tag_player(pvm['p1_id'])} Rolls: `{expr}` (*{sum(roll_list)}*)\n\n👉 {tag_player(pvm['p2_id'])}, *your turn! Send* `{pvm['emoji']}` *x{needed}.*")
                            pvm["turn"] = pvm["p2_id"]
                            schedule_pvp_turn_timeout(chat_id, active_ref, pvm)
                        else:
                            resolve_pvp_round_and_match(chat_id, active_ref, pvm)
                        return jsonify({'status': 'ok'}), 200

                with get_turn_lock(f"pvb_{user_id}"):
                    game = active_games.get(user_id)
                    if not isinstance(game, dict):
                        return jsonify({'status': 'ok'}), 200
                    expected_emoji = game['emoji']
                    
                    if user_dice.get('emoji') == expected_emoji and game['step'] in ['selecting_turn', 'waiting_user_first', 'waiting_user_second']:
                        game["turn_token"] = None
                        if game['step'] == 'selecting_turn':
                            game['first_turn'] = 'user'
                            game['step'] = 'waiting_user_first'
                            s_chat_id = game.get('start_chat_id') or chat_id
                            s_msg_id = game.get('start_message_id')
                            if s_msg_id:
                                remove_inline_keyboard(s_chat_id, s_msg_id)
                                game['start_message_id'] = None
                        user_val = user_dice.get('value', 1)
                        rolls_needed = game['rolls_per_round']
                        game['current_user_rolls'].append(user_val)
                        
                        remaining = rolls_needed - len(game['current_user_rolls'])
                        if remaining > 0:
                            send_message(chat_id, f"🎲 Roll `{len(game['current_user_rolls'])}/{rolls_needed}`: *{user_val}* — Send `{remaining}` more `{expected_emoji}`!")
                            schedule_pvb_turn_timeout(chat_id, user_id, game)
                            return jsonify({'status': 'ok'}), 200
                            
                        step = game['step']
                        if step == 'waiting_user_first':
                            u_expr = "+".join(map(str, game['current_user_rolls']))
                            player_tag = format_user_mention(user_id)
                            user_roll_msg_id = message.get('message_id')
                            send_message(chat_id, f"👤 {player_tag} Rolls ({expected_emoji}): `{u_expr}` (*{sum(game['current_user_rolls'])}*)\n\n🤖 Now bot is throwing...")
                            time.sleep(0.8)
                            
                            b_vals = roll_bot_series(chat_id, expected_emoji, rolls_needed, reply_to_message_id=user_roll_msg_id)
                            game['current_bot_rolls'] = b_vals
                            
                            resolve_round_and_match(chat_id, user_id, game)
                            return jsonify({'status': 'ok'}), 200
                            
                        elif step == 'waiting_user_second':
                            resolve_round_and_match(chat_id, user_id, game)
                            return jsonify({'status': 'ok'}), 200

            if 'text' in message:
                text = message['text'].strip()

                # ---- Ask for bet amount when a game command is sent without one ----
                _amt_key = (chat_id, user_id)
                _pending_amt = pending_amount_prompts.get(_amt_key)
                if _pending_amt and time.time() - _pending_amt["at"] > AMOUNT_PROMPT_SECONDS:
                    pending_amount_prompts.pop(_amt_key, None)
                    _pending_amt = None
                if text.startswith('/'):
                    pending_amount_prompts.pop(_amt_key, None)
                    if game_command_missing_amount(text, user_id) and not (chat_type == 'private' and not DM_GAMES_ENABLED):
                        pending_amount_prompts[_amt_key] = {
                            "text": text,
                            "reply_to_message": message.get("reply_to_message"),
                            "at": time.time(),
                        }
                        _pcat = bet_cat_for_command(text)
                        send_message(
                            chat_id,
                            f"💰 {format_user_mention(user_id)}, enter your *bet amount*:\n"
                            f"Min: *{format_money(bet_min(_pcat), user_id)}* | Max: *{format_money(bet_max(_pcat), user_id)}*",
                            reply_to_message_id=message.get('message_id') if chat_type in ['group', 'supergroup'] else None
                        )
                        return jsonify({'status': 'ok'}), 200
                elif _pending_amt and user_id not in deposit_states and user_id not in withdrawal_states:
                    _amt_tok = text.split()[0] if text.split() else ""
                    if parse_user_amount(_amt_tok, user_id) is None:
                        send_message(chat_id, "⚠️ Please enter a valid amount (example: `50`).")
                        return jsonify({'status': 'ok'}), 200
                    pending_amount_prompts.pop(_amt_key, None)
                    _orig_parts = _pending_amt["text"].split()
                    text = " ".join([_orig_parts[0], _amt_tok] + _orig_parts[1:])
                    if _pending_amt.get("reply_to_message") and not message.get("reply_to_message"):
                        message["reply_to_message"] = _pending_amt["reply_to_message"]

                if re.match(rf"^/helpers?(?:@{re.escape(BOT_USERNAME.lstrip('@'))})?(?:\s|$)", text, re.IGNORECASE):
                    if user_id not in admin_list:
                        return jsonify({'status': 'ok'}), 200
                    handle_helper_command(chat_id, chat_type, text, message)
                    return jsonify({'status': 'ok'}), 200

                if re.match(rf"^/offgame(?:@{re.escape(BOT_USERNAME.lstrip('@'))})?$", text, re.IGNORECASE):
                    if user_id not in admin_list:
                        pass  # normal users get no reply to admin commands
                        return jsonify({'status': 'ok'}), 200
                    DM_GAMES_ENABLED = False
                    save_config_value("dm_games_enabled", DM_GAMES_ENABLED)
                    send_message(chat_id, "🔴 *Games in Bot DM are now OFF.*\nPlayers will be asked to play in the group.")
                    return jsonify({'status': 'ok'}), 200

                if re.match(rf"^/ongame(?:@{re.escape(BOT_USERNAME.lstrip('@'))})?$", text, re.IGNORECASE):
                    if user_id not in admin_list:
                        pass  # normal users get no reply to admin commands
                        return jsonify({'status': 'ok'}), 200
                    DM_GAMES_ENABLED = True
                    save_config_value("dm_games_enabled", DM_GAMES_ENABLED)
                    send_message(chat_id, "🟢 *Games in Bot DM are now ON.*")
                    return jsonify({'status': 'ok'}), 200

                if re.match(rf"^/setgc(?:@{re.escape(BOT_USERNAME.lstrip('@'))})?(?:\s|$)", text, re.IGNORECASE):
                    if user_id not in admin_list:
                        pass  # normal users get no reply to admin commands
                        return jsonify({'status': 'ok'}), 200
                    parts = text.split(maxsplit=1)
                    if len(parts) < 2 or not parts[1].strip():
                        current = GROUP_LINK if GROUP_LINK else "Not set"
                        current = current.replace('_', '\\_')
                        send_message(chat_id, f"🔗 Current Group Link: {current}\nUsage: `/setgc @grouplink`")
                        return jsonify({'status': 'ok'}), 200
                    GROUP_LINK = parts[1].strip()
                    save_config_value("group_link", GROUP_LINK)
                    safe = GROUP_LINK.replace('_', '\\_')
                    send_message(chat_id, f"✅ Group link set to: {safe}")
                    return jsonify({'status': 'ok'}), 200

                if chat_type == 'private' and not DM_GAMES_ENABLED and is_dm_game_command(text):
                    send_message(chat_id, build_dm_games_off_text())
                    return jsonify({'status': 'ok'}), 200

                if re.match(rf"^/setrate(?:@{re.escape(BOT_USERNAME.lstrip('@'))})?(?:\s|$)", text, re.IGNORECASE):
                    if user_id not in admin_list:
                        pass  # normal users get no reply to admin commands
                        return jsonify({'status': 'ok'}), 200
                    parts = text.split()
                    if len(parts) < 2:
                        send_message(chat_id, f"💱 Current Rate: *₹{EXCHANGE_RATE:.2f} / USDT*\nUsage: `/setrate <rate>`")
                        return jsonify({'status': 'ok'}), 200
                    try:
                        val = float(parts[1])
                        if val <= 0:
                            raise ValueError()
                        EXCHANGE_RATE = val
                        save_config_value("exchange_rate", EXCHANGE_RATE)
                        send_message(chat_id, f"✅ Exchange rate updated to *₹{EXCHANGE_RATE:.2f} / USDT*.")
                    except ValueError:
                        send_message(chat_id, "⚠️ Enter a valid positive rate (e.g. `/setrate 98`).")
                    return jsonify({'status': 'ok'}), 200

                if re.match(rf"^/resetdata(?:@{re.escape(BOT_USERNAME.lstrip('@'))})?(?:\s|$)", text, re.IGNORECASE):
                    if user_id != ADMIN_USER_ID or chat_type != 'private':
                        return jsonify({'status': 'ok'}), 200  # owner only, DM only
                    _, kb = create_manual_txn_confirmation(user_id, chat_id, "resetdata", {})
                    settings_line = (
                        "• Settings stay as they are\n" if RESET_KEEP_SETTINGS
                        else "• All settings (min deposit/withdraw, bets, multipliers, house balance, approved groups) go back to default\n"
                    )
                    conf_txt = (
                        "⚠️ *Reset ALL Bot Data?*\n\n"
                        "This will permanently delete:\n"
                        "• All users and their balances\n"
                        "• All bets, games and stats\n"
                        "• All deposits and withdrawals\n"
                        "• Bans and extra admins\n"
                        f"{settings_line}\n"
                        "A fresh new database will be created.\n\n"
                        f"❗ *This cannot be undone.* Confirm within {RESET_CONFIRM_SECONDS // 60} minutes."
                    )
                    send_message(chat_id, conf_txt, reply_markup=kb)
                    return jsonify({'status': 'ok'}), 200

                if re.match(rf"^/sethb(?:@{re.escape(BOT_USERNAME.lstrip('@'))})?(?:\s|$)", text, re.IGNORECASE):
                    if user_id not in admin_list:
                        pass  # normal users get no reply to admin commands
                        return jsonify({'status': 'ok'}), 200
                    parts = text.split()
                    if len(parts) < 2:
                        send_message(chat_id, f"🏦 Current House Balance: *{format_money(HOUSE_BALANCE, user_id)}*\nUsage: `/sethb <amount>`")
                        return jsonify({'status': 'ok'}), 200
                    try:
                        val = float(parts[1])
                        if val < 0:
                            raise ValueError()
                        _, kb = create_manual_txn_confirmation(user_id, chat_id, "sethb", {"val": val})
                        conf_txt = (
                            "⚠️ *Confirm Manual Transaction*\n\n"
                            "• *Action:* Set House Balance (`/sethb`)\n"
                            f"• *Current HB:* *{format_money(HOUSE_BALANCE, user_id)}*\n"
                            f"• *New HB:* *{format_money(val, user_id)}*"
                        )
                        send_message(chat_id, conf_txt, reply_markup=kb)
                    except ValueError:
                        send_message(chat_id, "⚠️ Enter a valid non-negative amount (e.g. `/sethb 150000`).")
                    return jsonify({'status': 'ok'}), 200

                if re.match(rf"^/deducthb(?:@{re.escape(BOT_USERNAME.lstrip('@'))})?(?:\s|$)", text, re.IGNORECASE):
                    if user_id not in admin_list:
                        pass  # normal users get no reply to admin commands
                        return jsonify({'status': 'ok'}), 200
                    parts = text.split()
                    if len(parts) < 2:
                        send_message(chat_id, f"🏦 Current House Balance: *{format_money(HOUSE_BALANCE, user_id)}*\nUsage: `/deducthb <amount>`")
                        return jsonify({'status': 'ok'}), 200
                    try:
                        if is_all_half_word(parts[1]):
                            amt = resolve_all_half(parts[1], HOUSE_BALANCE)
                            if amt is None:
                                raise ValueError()
                        else:
                            amt = float(parts[1].replace('₹', '').replace(',', ''))
                        if amt <= 0:
                            raise ValueError()
                        new_hb = max(0.0, HOUSE_BALANCE - amt)
                        _, kb = create_manual_txn_confirmation(user_id, chat_id, "deducthb", {"amt": amt})
                        conf_txt = (
                            "⚠️ *Confirm Manual Transaction*\n\n"
                            "• *Action:* Deduct House Balance (`/deducthb`)\n"
                            f"• *Deduct Amount:* *{format_money(amt, user_id)}*\n"
                            f"• *Current HB:* *{format_money(HOUSE_BALANCE, user_id)}*\n"
                            f"• *HB After:* *{format_money(new_hb, user_id)}*"
                        )
                        send_message(chat_id, conf_txt, reply_markup=kb)
                    except ValueError:
                        send_message(chat_id, "⚠️ Enter a valid positive amount, `all` or `half` (e.g. `/deducthb 5000`).")
                    return jsonify({'status': 'ok'}), 200

                if re.match(rf"^/mindep(?:@{re.escape(BOT_USERNAME.lstrip('@'))})?(?:\s|$)", text, re.IGNORECASE):
                    if user_id not in admin_list:
                        return jsonify({'status': 'ok'}), 200  # admin-only
                    parts = text.split()
                    if len(parts) < 2:
                        send_message(chat_id, f"💳 Current Min Deposit: *₹{MIN_DEPOSIT:,.0f}*\nUsage: `/mindep <amount>` (e.g. `/mindep 200`)")
                        return jsonify({'status': 'ok'}), 200
                    try:
                        val = float(parts[1].replace('₹', '').replace(',', ''))
                        if val <= 0 or val != int(val):
                            raise ValueError()
                        MIN_DEPOSIT = val
                        save_config_value("min_deposit", MIN_DEPOSIT)
                        send_message(chat_id, f"✅ Minimum Deposit updated to *₹{MIN_DEPOSIT:,.0f}*.")
                    except ValueError:
                        send_message(chat_id, "⚠️ Enter a valid whole amount greater than 0 (e.g. `/mindep 200`).")
                    return jsonify({'status': 'ok'}), 200

                if re.match(rf"^/minwd(?:@{re.escape(BOT_USERNAME.lstrip('@'))})?(?:\s|$)", text, re.IGNORECASE):
                    if user_id not in admin_list:
                        return jsonify({'status': 'ok'}), 200  # admin-only
                    parts = text.split()
                    if len(parts) < 2:
                        send_message(chat_id, f"💸 Current Min Withdrawal: *₹{MIN_WITHDRAW:,.0f}*\nUsage: `/minwd <amount>` (e.g. `/minwd 100`)")
                        return jsonify({'status': 'ok'}), 200
                    try:
                        val = float(parts[1].replace('₹', '').replace(',', ''))
                        if val < WITHDRAW_MULTIPLE * 2 or not is_withdraw_multiple(val):
                            raise ValueError()
                        MIN_WITHDRAW = val
                        save_config_value("min_withdraw", MIN_WITHDRAW)
                        send_message(chat_id, f"✅ Minimum Withdrawal updated to *₹{MIN_WITHDRAW:,.0f}*.")
                    except ValueError:
                        send_message(chat_id, f"⚠️ Enter an amount in multiples of ₹{WITHDRAW_MULTIPLE}, at least ₹{WITHDRAW_MULTIPLE * 2} (e.g. `/minwd 100`).")
                    return jsonify({'status': 'ok'}), 200

                if re.match(rf"^/maxbets(?:@{re.escape(BOT_USERNAME.lstrip('@'))})?$", text, re.IGNORECASE):
                    send_message(chat_id, build_maxbets_text(user_id))
                    return jsonify({'status': 'ok'}), 200

                _blm = re.match(rf"^/(min|max)bet(emoji|dr|7up|special|speacial|limbo)(?:@{re.escape(BOT_USERNAME.lstrip('@'))})?(?:\s+(\S+))?\s*$", text, re.IGNORECASE)
                if _blm:
                    if user_id not in admin_list:
                        return jsonify({'status': 'ok'}), 200  # admin-only
                    _which = _blm.group(1).lower()
                    _cat = BET_CAT_ALIASES[_blm.group(2).lower()]
                    _label = BET_CATEGORIES[_cat]
                    _cmd = f"/{_which}bet{_blm.group(2).lower()}"
                    if not _blm.group(3):
                        send_message(chat_id, f"🎯 *{_label}*\nMin Bet: *{format_money(bet_min(_cat), user_id)}* | Max Bet: *{format_money(bet_max(_cat), user_id)}*\nUsage: `{_cmd} <amount>`")
                        return jsonify({'status': 'ok'}), 200
                    try:
                        val = _parse_admin_amount(_blm.group(3))
                        if val <= 0:
                            raise ValueError()
                    except ValueError:
                        send_message(chat_id, f"⚠️ Enter a valid amount greater than 0 (e.g. `{_cmd} 500`).")
                        return jsonify({'status': 'ok'}), 200
                    if _which == "min" and val > bet_max(_cat):
                        send_message(chat_id, f"⚠️ Min bet can't be more than the {_label} max bet (*{format_money(bet_max(_cat), user_id)}*).")
                        return jsonify({'status': 'ok'}), 200
                    if _which == "max" and val < bet_min(_cat):
                        send_message(chat_id, f"⚠️ Max bet can't be less than the {_label} min bet (*{format_money(bet_min(_cat), user_id)}*).")
                        return jsonify({'status': 'ok'}), 200
                    BET_LIMITS[_cat][_which] = val
                    save_bet_limits()
                    _nm = "Min" if _which == "min" else "Max"
                    send_message(chat_id, f"✅ {_label} {_nm} Bet set to *{format_money(val, user_id)}*.\nNow: Min *{format_money(bet_min(_cat), user_id)}* | Max *{format_money(bet_max(_cat), user_id)}*")
                    return jsonify({'status': 'ok'}), 200

                _mpl = re.match(rf"^/maxpaylimbo(?:@{re.escape(BOT_USERNAME.lstrip('@'))})?(?:\s+(\S+))?\s*$", text, re.IGNORECASE)
                if _mpl:
                    if user_id not in admin_list:
                        return jsonify({'status': 'ok'}), 200  # admin-only
                    if not _mpl.group(1):
                        _cur = format_money(LIMBO_MAX_PAYOUT, user_id) if LIMBO_MAX_PAYOUT > 0 else "No limit"
                        send_message(chat_id, f"🚀 Limbo Max Win: *{_cur}*\nUsage: `/maxpaylimbo <amount>` (`/maxpaylimbo 0` = no limit)")
                        return jsonify({'status': 'ok'}), 200
                    _raw = _mpl.group(1).lower()
                    try:
                        val = 0.0 if _raw in ("off", "none", "no") else _parse_admin_amount(_raw)
                        if val < 0:
                            raise ValueError()
                    except ValueError:
                        send_message(chat_id, "⚠️ Enter a valid amount (e.g. `/maxpaylimbo 1000`, or `0` for no limit).")
                        return jsonify({'status': 'ok'}), 200
                    LIMBO_MAX_PAYOUT = val
                    save_bet_limits()
                    if val > 0:
                        send_message(chat_id, f"✅ Limbo Max Win set to *{format_money(val, user_id)}*.\nA bet whose bet × target is more than this will be refused.")
                    else:
                        send_message(chat_id, "✅ Limbo Max Win limit removed (no limit).")
                    return jsonify({'status': 'ok'}), 200

                if re.match(rf"^/minbet(?:@{re.escape(BOT_USERNAME.lstrip('@'))})?(?:\s|$)", text, re.IGNORECASE):
                    if user_id not in admin_list:
                        pass  # normal users get no reply to admin commands
                        return jsonify({'status': 'ok'}), 200
                    parts = text.split()
                    if len(parts) < 2:
                        send_message(chat_id, "🎯 *Min Bets*\n" + "\n".join(f"{BET_CATEGORIES[c]}: *{format_money(bet_min(c), user_id)}*" for c in BET_CATEGORIES) + "\n\nUsage: `/minbet <amount>` sets every game at once.\nPer game: `/minbetemoji`, `/minbetdr`, `/minbet7up`, `/minbetspecial`, `/minbetlimbo`")
                        return jsonify({'status': 'ok'}), 200
                    try:
                        val = _parse_admin_amount(parts[1])
                        _lowest_max = min(bet_max(c) for c in BET_CATEGORIES)
                        if val <= 0 or val > _lowest_max:
                            raise ValueError()
                        MIN_BET = val
                        for c in BET_LIMITS:
                            BET_LIMITS[c]["min"] = val
                        save_config_value("min_bet", MIN_BET)
                        save_bet_limits()
                        send_message(chat_id, f"✅ Min Bet for *all games* set to *{format_money(MIN_BET, user_id)}*.")
                    except ValueError:
                        send_message(chat_id, f"⚠️ Enter a valid amount `> 0` and not more than the lowest max bet (*{format_money(min(bet_max(c) for c in BET_CATEGORIES), user_id)}*).")
                    return jsonify({'status': 'ok'}), 200

                if re.match(rf"^/maxbet(?:@{re.escape(BOT_USERNAME.lstrip('@'))})?(?:\s|$)", text, re.IGNORECASE):
                    if user_id not in admin_list:
                        pass  # normal users get no reply to admin commands
                        return jsonify({'status': 'ok'}), 200
                    parts = text.split()
                    if len(parts) < 2:
                        send_message(chat_id, build_maxbets_text(user_id) + "\n\nUsage: `/maxbet <amount>` sets every game at once.\nPer game: `/maxbetemoji`, `/maxbetdr`, `/maxbet7up`, `/maxbetspecial`, `/maxbetlimbo`, `/maxpaylimbo`")
                        return jsonify({'status': 'ok'}), 200
                    try:
                        val = _parse_admin_amount(parts[1])
                        _highest_min = max(bet_min(c) for c in BET_CATEGORIES)
                        if val <= 0 or val < _highest_min:
                            raise ValueError()
                        MAX_BET = val
                        for c in BET_LIMITS:
                            BET_LIMITS[c]["max"] = val
                        save_config_value("max_bet", MAX_BET)
                        save_bet_limits()
                        send_message(chat_id, f"✅ Max Bet for *all games* set to *{format_money(MAX_BET, user_id)}*.")
                    except ValueError:
                        send_message(chat_id, f"⚠️ Enter a valid amount not less than the highest min bet (*{format_money(max(bet_min(c) for c in BET_CATEGORIES), user_id)}*).")
                    return jsonify({'status': 'ok'}), 200

                if re.match(rf"^/addbalance(?:@{re.escape(BOT_USERNAME.lstrip('@'))})?(?:\s|$)", text, re.IGNORECASE):
                    if user_id not in admin_list:
                        pass  # normal users get no reply to admin commands
                        return jsonify({'status': 'ok'}), 200
                    parts = text.split()
                    if len(parts) < 3:
                        send_message(chat_id, "⚠️ Usage: `/addbalance <user_id/@username> <amount>`")
                        return jsonify({'status': 'ok'}), 200
                    target_uid = resolve_user_identifier(parts[1])
                    if target_uid is None:
                        send_message(chat_id, f"⚠️ User `{parts[1]}` not found.")
                        return jsonify({'status': 'ok'}), 200
                    amt_inr = parse_user_amount(parts[2], target_uid)
                    if amt_inr is None or amt_inr <= 0:
                        send_message(chat_id, "⚠️ Enter a valid positive amount.")
                        return jsonify({'status': 'ok'}), 200
                    cur_b = float(user_balances.get(target_uid, 0.0))
                    _, kb = create_manual_txn_confirmation(
                        user_id, chat_id, "addbalance", {"target_uid": target_uid, "amt_inr": amt_inr}
                    )
                    conf_txt = (
                        "⚠️ *Confirm Manual Transaction*\n\n"
                        "• *Action:* Add Balance (`/addbalance`)\n"
                        f"• *Target User:* `{target_uid}` ({display_sender_label(target_uid)})\n"
                        f"• *Amount:* *+{format_money(amt_inr, target_uid)}*\n"
                        f"• *Current Balance:* *{format_money(cur_b, target_uid)}*\n"
                        f"• *Balance After:* *{format_money(cur_b + amt_inr, target_uid)}*"
                    )
                    send_message(chat_id, conf_txt, reply_markup=kb)
                    return jsonify({'status': 'ok'}), 200

                if re.match(rf"^/deductbalance(?:@{re.escape(BOT_USERNAME.lstrip('@'))})?(?:\s|$)", text, re.IGNORECASE):
                    if user_id not in admin_list:
                        pass  # normal users get no reply to admin commands
                        return jsonify({'status': 'ok'}), 200
                    parts = text.split()
                    if len(parts) < 3:
                        send_message(chat_id, "⚠️ Usage: `/deductbalance <user_id/@username> <amount>`")
                        return jsonify({'status': 'ok'}), 200
                    target_uid = resolve_user_identifier(parts[1])
                    if target_uid is None:
                        send_message(chat_id, f"⚠️ User `{parts[1]}` not found.")
                        return jsonify({'status': 'ok'}), 200
                    amt_inr = parse_user_amount(parts[2], target_uid)
                    if amt_inr is None or amt_inr <= 0:
                        send_message(chat_id, "⚠️ Enter a valid positive amount.")
                        return jsonify({'status': 'ok'}), 200
                    cur_b = float(user_balances.get(target_uid, 0.0))
                    after_b = max(0.0, cur_b - amt_inr)
                    _, kb = create_manual_txn_confirmation(
                        user_id, chat_id, "deductbalance", {"target_uid": target_uid, "amt_inr": amt_inr}
                    )
                    conf_txt = (
                        "⚠️ *Confirm Manual Transaction*\n\n"
                        "• *Action:* Deduct Balance (`/deductbalance`)\n"
                        f"• *Target User:* `{target_uid}` ({display_sender_label(target_uid)})\n"
                        f"• *Deduct Amount:* *-{format_money(amt_inr, target_uid)}*\n"
                        f"• *Current Balance:* *{format_money(cur_b, target_uid)}*\n"
                        f"• *Balance After:* *{format_money(after_b, target_uid)}*"
                    )
                    send_message(chat_id, conf_txt, reply_markup=kb)
                    return jsonify({'status': 'ok'}), 200

                mult_cmd_map = {
                    "/setmultidice": "dice",
                    "/setmultidart": "dart",
                    "/setmultifoot": "foot",
                    "/setmultibasket": "basket",
                    "/setmultibowl": "bowl",
                    "/setmultiboel": "bowl",
                    "/setmultipvp": "pvp",
                    "/setmultibj": "bj",
                    "/setmultidr": "dr",
                }

                matched_mult_key = None
                for cmd_prefix, m_key in mult_cmd_map.items():
                    if re.match(rf"^{re.escape(cmd_prefix)}(?:@{re.escape(BOT_USERNAME.lstrip('@'))})?(?:\s|$)", text, re.IGNORECASE):
                        matched_mult_key = m_key
                        break

                if matched_mult_key:
                    if user_id not in admin_list:
                        pass  # normal users get no reply to admin commands
                        return jsonify({'status': 'ok'}), 200
                    parts = text.split()
                    if len(parts) < 2:
                        cur_m = GAME_MULTIPLIERS.get(matched_mult_key)
                        send_message(chat_id, f"⚙️ Current `{matched_mult_key}` multiplier: *{fmt_mult(cur_m)}*\nUsage: `{parts[0]} <multiplier>`")
                        return jsonify({'status': 'ok'}), 200
                    try:
                        new_val = float(parts[1])
                        if new_val <= 0 or new_val > 100:
                            raise ValueError()
                        GAME_MULTIPLIERS[matched_mult_key] = new_val
                        send_message(chat_id, f"✅ Updated `{matched_mult_key}` multiplier to *{fmt_mult(new_val)}*.")
                    except ValueError:
                        send_message(chat_id, "⚠️ Enter a valid positive multiplier (e.g. `1.94`, `1.9`, `2`).")
                    return jsonify({'status': 'ok'}), 200

                seven_up_mult_cmd_map = {
                    "/setmulti7upup": "up",
                    "/setmultihigh": "up",
                    "/setmulti7updown": "down",
                    "/setmultilow": "down",
                    "/setmulti7upodd": "odd",
                    "/setmulti7upeven": "even",
                    "/setmulti7up7": "7",
                }
                matched_7up_key = None
                for cmd_prefix, s_key in seven_up_mult_cmd_map.items():
                    if re.match(rf"^{re.escape(cmd_prefix)}(?:@{re.escape(BOT_USERNAME.lstrip('@'))})?(?:\s|$)", text, re.IGNORECASE):
                        matched_7up_key = s_key
                        break

                if matched_7up_key:
                    if user_id not in admin_list:
                        pass  # normal users get no reply to admin commands
                        return jsonify({'status': 'ok'}), 200
                    parts = text.split()
                    if len(parts) < 2:
                        cur_m = get_7up_multiplier(matched_7up_key)
                        send_message(chat_id, f"⚙️ Current `7up` (`{matched_7up_key}`) multiplier: *{fmt_mult(cur_m)}*\nUsage: `{parts[0]} <multiplier>`")
                        return jsonify({'status': 'ok'}), 200
                    try:
                        new_val = float(parts[1])
                        if new_val <= 0 or new_val > 100:
                            raise ValueError()
                        GAME_MULTIPLIERS.setdefault("7up", {})[matched_7up_key] = new_val
                        send_message(chat_id, f"✅ Updated `7up` (`{matched_7up_key}`) multiplier to *{fmt_mult(new_val)}*.")
                    except ValueError:
                        send_message(chat_id, "⚠️ Enter a valid positive multiplier (e.g. `2.16`, `1.9`, `5.16`).")
                    return jsonify({'status': 'ok'}), 200

                if re.match(rf"^/setmultidrnum(?:@{re.escape(BOT_USERNAME.lstrip('@'))})?(?:\s|$)", text, re.IGNORECASE):
                    if user_id not in admin_list:
                        pass  # normal users get no reply to admin commands
                        return jsonify({'status': 'ok'}), 200
                    parts = text.split()
                    if len(parts) < 3:
                        send_message(chat_id, "⚠️ Usage: `/setmultidrnum <1-5> <multiplier>` (e.g. `/setmultidrnum 3 1.92`)")
                        return jsonify({'status': 'ok'}), 200
                    try:
                        cnt = int(parts[1])
                        new_val = float(parts[2])
                        if cnt not in [1, 2, 3, 4, 5] or new_val <= 0 or new_val > 100:
                            raise ValueError()
                        GAME_MULTIPLIERS["dr_nums"][cnt] = new_val
                        send_message(chat_id, f"✅ Updated `/dr` ({cnt} number(s)) multiplier to *{fmt_mult(new_val)}*.")
                    except ValueError:
                        send_message(chat_id, "⚠️ Invalid input. Count must be `1`–`5` and multiplier `> 0`.")
                    return jsonify({'status': 'ok'}), 200

                if re.match(rf"^/mults(?:@{re.escape(BOT_USERNAME.lstrip('@'))})?$", text, re.IGNORECASE):
                    if user_id not in admin_list:
                        pass  # normal users get no reply to admin commands
                        return jsonify({'status': 'ok'}), 200
                    dr_nums_str = ", ".join(f"{k}n: {fmt_mult(v)}" for k, v in GAME_MULTIPLIERS["dr_nums"].items())
                    m7 = GAME_MULTIPLIERS.get("7up", {})
                    txt = (
                        "⚙️ *Active Game Multipliers*\n\n"
                        f"• Dice: *{fmt_mult(GAME_MULTIPLIERS['dice'])}*\n"
                        f"• Dart: *{fmt_mult(GAME_MULTIPLIERS['dart'])}*\n"
                        f"• Football: *{fmt_mult(GAME_MULTIPLIERS['foot'])}*\n"
                        f"• Basketball: *{fmt_mult(GAME_MULTIPLIERS['basket'])}*\n"
                        f"• Bowling: *{fmt_mult(GAME_MULTIPLIERS['bowl'])}*\n"
                        f"• PvP: *{fmt_mult(GAME_MULTIPLIERS['pvp'])}*\n"
                        f"• Blackjack: *{fmt_mult(GAME_MULTIPLIERS['bj'])}*\n"
                        f"• Predict (H/L/O/E): *{fmt_mult(GAME_MULTIPLIERS['dr'])}*\n"
                        f"• Predict Numbers: `{dr_nums_str}`\n"
                        f"• 7Up: `up/high: {fmt_mult(m7.get('up', 2.16))}, down/low: {fmt_mult(m7.get('down', 2.16))}, odd: {fmt_mult(m7.get('odd', 1.9))}, even: {fmt_mult(m7.get('even', 1.9))}, 7: {fmt_mult(m7.get('7', 5.16))}`"
                    )
                    send_message(chat_id, txt)
                    return jsonify({'status': 'ok'}), 200
                
                if re.match(r'^/approve(?:@\S+)?(?:\s+|$)', text, re.IGNORECASE):
                    if user_id in admin_list:
                        parts = text.split(' ')
                        if len(parts) > 1 and parts[1].strip('-').isdigit():
                            target_chat_id = int(parts[1])
                            approved_groups.add(target_chat_id)
                            persist_approved_group(target_chat_id)
                            send_message(chat_id, f"✅ Group `{target_chat_id}` has been successfully *APPROVED*!")
                        else:
                            send_message(chat_id, "⚠️ Invalid format. Use: `/approve <chat_id>`")
                    else:
                        pass  # normal users get no reply to admin commands
                    return jsonify({'status': 'ok'}), 200

                if re.match(rf"^/info(?:@{re.escape(BOT_USERNAME.lstrip('@'))})?(?:\s|$)", text, re.IGNORECASE):
                    if user_id not in admin_list:
                        pass  # normal users get no reply to admin commands
                        return jsonify({'status': 'ok'}), 200
                    parts = text.split()
                    if len(parts) < 2:
                        send_message(chat_id, "⚠️ Usage: `/info <username/userid>`")
                        return jsonify({'status': 'ok'}), 200
                    target_uid = resolve_user_identifier(parts[1])
                    if target_uid is None:
                        send_message(chat_id, f"⚠️ User `{parts[1]}` not found.")
                        return jsonify({'status': 'ok'}), 200
                    send_message(chat_id, build_user_info_summary(target_uid), reply_markup=info_menu_keyboard(target_uid))
                    return jsonify({'status': 'ok'}), 200

                if re.match(rf"^/search(?:@{re.escape(BOT_USERNAME.lstrip('@'))})?(?:\s|$)", text, re.IGNORECASE):
                    if user_id not in admin_list:
                        pass  # normal users get no reply to admin commands
                        return jsonify({'status': 'ok'}), 200
                    parts = text.split()
                    search_usage = (
                        "⚠️ *Usage:*\n"
                        "• Game: `/search XC-XXXXXXX-XXXX`\n"
                        "• Deposit: `/search DP-XXXXXXX-XXXX`\n"
                        "• Withdraw: `/search WD-XXXXXXX-XXXX`"
                    )
                    # Also accept "/search deposit <id>" and "/search withdraw <id>"
                    if len(parts) >= 2 and parts[1].lower() in ("deposit", "dep", "withdraw", "withdrawal", "wd", "game"):
                        kind_word = parts[1].lower()
                        if len(parts) < 3:
                            send_message(chat_id, search_usage)
                            return jsonify({'status': 'ok'}), 200
                        if kind_word in ("deposit", "dep"):
                            send_message(chat_id, build_deposit_search_report(parts[2]))
                        elif kind_word == "game":
                            send_message(chat_id, build_game_search_report(parts[2]))
                        else:
                            send_message(chat_id, build_withdraw_search_report(parts[2]))
                        return jsonify({'status': 'ok'}), 200
                    if len(parts) < 2:
                        send_message(chat_id, search_usage)
                        return jsonify({'status': 'ok'}), 200
                    send_message(chat_id, build_any_search_report(parts[1]))
                    return jsonify({'status': 'ok'}), 200

                if re.match(rf"^/cancel(?:@{re.escape(BOT_USERNAME.lstrip('@'))})?(?:\s|$)", text, re.IGNORECASE):
                    # Admin-only: normal players can never cancel a game (no reply, like other admin commands)
                    if user_id not in admin_list:
                        return jsonify({'status': 'ok'}), 200
                    parts = text.split()
                    if len(parts) < 2:
                        send_message(chat_id, "⚠️ Usage: `/cancel XC-XXXXXXX-XXXX`")
                        return jsonify({'status': 'ok'}), 200
                    gid = parts[1].strip().upper()
                    rec = game_id_registry.get(gid)
                    if not rec:
                        send_message(chat_id, f"⚠️ Game ID `{gid}` not found.")
                        return jsonify({'status': 'ok'}), 200
                    _, status_msg = cancel_game_by_id(gid)
                    send_message(chat_id, status_msg)
                    return jsonify({'status': 'ok'}), 200

                if re.match(rf"^/rain(?:@{re.escape(BOT_USERNAME.lstrip('@'))})?(?:\s|$)", text, re.IGNORECASE):
                    handle_rain_command(chat_id, chat_type, user_id, text)
                    return jsonify({'status': 'ok'}), 200

                if re.match(rf"^/tip(?:@{re.escape(BOT_USERNAME.lstrip('@'))})?(?:\s|$)", text, re.IGNORECASE):
                    parts = text.split()
                    current_bal = user_balances.get(user_id, 0.0)
                    receiver_id = None
                    amt_inr = None

                    if 'reply_to_message' in message and message['reply_to_message'].get('from'):
                        reply_from = message['reply_to_message']['from']
                        if not reply_from.get('is_bot'):
                            receiver_id = register_user_identity(reply_from)
                        if len(parts) >= 2:
                            amt_inr = parse_user_amount(parts[1], user_id)
                    else:
                        if len(parts) >= 3:
                            amt_inr = parse_user_amount(parts[1], user_id)
                            target_uname = parts[2].lstrip("@").lower()
                            receiver_id = username_to_id.get(target_uname)
                        elif len(parts) == 2:
                            send_message(chat_id, "⚠️ Reply to a user's message with `/tip <amount>` or use `/tip <amount> <username>`.")
                            return jsonify({'status': 'ok'}), 200
                        else:
                            send_message(chat_id, "⚠️ Usage: `/tip <amount> <username>` or reply to a message with `/tip <amount>`.")
                            return jsonify({'status': 'ok'}), 200

                    if amt_inr is None or amt_inr <= 0:
                        send_message(chat_id, "⚠️ Enter a valid tip amount. Example: `/tip 50 @username`")
                        return jsonify({'status': 'ok'}), 200

                    if receiver_id is None:
                        send_message(chat_id, "⚠️ Recipient not found! Make sure they have interacted with the bot or reply directly to their message.")
                        return jsonify({'status': 'ok'}), 200

                    if receiver_id == user_id:
                        send_message(chat_id, "⚠️ You cannot tip yourself!")
                        return jsonify({'status': 'ok'}), 200

                    if current_bal < amt_inr:
                        send_message(
                            chat_id,
                            f"❌ *Insufficient Balance!*\n💰 Your Balance: *{format_money(current_bal, user_id)}*\n🎯 Required Tip: *{format_money(amt_inr, user_id)}*"
                        )
                        return jsonify({'status': 'ok'}), 200

                    _, kb = create_manual_txn_confirmation(
                        user_id,
                        chat_id,
                        "tip",
                        {"receiver_id": receiver_id, "amt_inr": amt_inr, "origin_chat_id": chat_id},
                    )
                    conf_txt = (
                        "⚠️ *Confirm Tip Transaction*\n\n"
                        "• *Action:* Send Tip (`/tip`)\n"
                        f"• *To:* {display_sender_label(receiver_id)} (`{receiver_id}`)\n"
                        f"• *Amount:* *{format_money(amt_inr, user_id)}*\n"
                        f"• *Your Balance:* *{format_money(current_bal, user_id)}*"
                    )
                    send_message(chat_id, conf_txt, reply_markup=kb)
                    return jsonify({'status': 'ok'}), 200

                if re.match(rf"^/(?:ref|refer)(?:@{re.escape(BOT_USERNAME.lstrip('@'))})?$", text, re.IGNORECASE):
                    _share = "https://t.me/share/url?url=" + requests.utils.quote(build_ref_link(user_id), safe="")
                    send_message(chat_id, build_ref_details_text(user_id), reply_markup={"inline_keyboard": [[{"text": "📤 Share Refer Link", "url": _share}]]})
                    return jsonify({'status': 'ok'}), 200

                if re.match(rf"^/levels?(?:@{re.escape(BOT_USERNAME.lstrip('@'))})?$", text, re.IGNORECASE):
                    lv_text, lv_kb = build_level_page(user_id)
                    lv_sent = send_message(chat_id, lv_text, reply_markup=lv_kb)
                    remember_button_owner(chat_id, lv_sent, user_id)
                    return jsonify({'status': 'ok'}), 200

                if re.match(rf"^/(?:rakeback|rb)(?:@{re.escape(BOT_USERNAME.lstrip('@'))})?$", text, re.IGNORECASE):
                    rb_amt = claim_rakeback(user_id)
                    send_message(chat_id, build_rakeback_text(user_id, rb_amt))
                    return jsonify({'status': 'ok'}), 200

                if re.match(rf"^/myref(?:@{re.escape(BOT_USERNAME.lstrip('@'))})?$", text, re.IGNORECASE):
                    mr_text, mr_kb = build_myref_page(user_id, page=0)
                    mr_sent = send_message(chat_id, mr_text, reply_markup=mr_kb)
                    if mr_kb:
                        remember_button_owner(chat_id, mr_sent, user_id)
                    return jsonify({'status': 'ok'}), 200

                if re.match(rf"^/joinref(?:@{re.escape(BOT_USERNAME.lstrip('@'))})?(?:\s|$)", text, re.IGNORECASE):
                    jr_parts = text.split()
                    _, jr_msg = join_referral(user_id, jr_parts[1] if len(jr_parts) > 1 else "")
                    send_message(chat_id, jr_msg)
                    return jsonify({'status': 'ok'}), 200

                if re.match(rf"^/start(?:@{re.escape(BOT_USERNAME.lstrip('@'))})?(?:\s|$)", text, re.IGNORECASE):
                    st_parts = text.split()
                    # Deep links from the group balance buttons: open the deposit / withdraw flow directly in DM
                    if chat_type == 'private' and len(st_parts) > 1 and st_parts[1].lower() in ("deposit", "withdraw"):
                        if user_id in deposit_states: del deposit_states[user_id]
                        if user_id in withdrawal_states: del withdrawal_states[user_id]
                        if st_parts[1].lower() == "deposit":
                            if not DEPOSIT_ENABLED:
                                send_message(chat_id, "❌ Deposits are currently disabled by Admin.")
                            else:
                                deposit_states[user_id] = True
                                send_message(chat_id, "💳 *Please enter the amount you want to deposit (e.g. 200):*")
                        else:
                            if not WITHDRAW_ENABLED:
                                send_message(chat_id, "❌ Withdrawals are currently disabled by Admin.")
                            else:
                                withdrawal_states[user_id] = {'step': 'waiting_amount'}
                                send_message(chat_id, build_withdraw_prompt_text())
                        return jsonify({'status': 'ok'}), 200
                    if len(st_parts) > 1 and st_parts[1].lower().startswith("ref_"):
                        if user_id in user_referred_by:
                            send_message(chat_id, f"⚠️ You are already referred by {tag_player(user_referred_by[user_id])}")
                        else:
                            _, jr_msg = join_referral(user_id, st_parts[1])
                            send_message(chat_id, jr_msg)
                    send_message(chat_id, build_welcome_text(message.get('from')), reply_markup=welcome_keyboard())

                elif re.match(rf"^/help(?:@{re.escape(BOT_USERNAME.lstrip('@'))})?$", text, re.IGNORECASE):
                    help_text = (
                        f"🎰 *Welcome to {BOT_USERNAME} Casino!* 🎲\n\n"
                        "Commands:\n"
                        "- `/balance` or `/bal` - Check wallet balance\n"
                        "- `/hb` - Check House Balance\n"
                        "- `/currency` - Change currency (INR / USDT)\n"
                        "- `/stats` - View your visual stats card\n"
                        "- `/history` - View your bet history (5 per page)\n"
                        "- `/deposit` - Add money via ZapUPI (DM Only)\n"
                        "- `/withdraw` - Withdraw your winnings (DM Only)\n"
                        "- `/tip <amount> <username>` or reply `/tip <amount>` - Send tip\n"
                        "- `/maxbets` - Max bet of every game\n"
                        "- `/search <id>` - Search Game (XC-), Deposit (DP-) or Withdraw (WD-) by ID\n"
                        "- `/ref` or `/refer` - Your refer link, code & earnings\n"
                        "- `/myref` - See all players you referred\n"
                        "- `/joinref <code>` - Join someone's refer\n"
                        "- `/levels` - Your level, progress & level-up bonuses\n"
                        "- `/rakeback` - Claim rakeback on your lost deposit money\n\n"
                        "🃏 *Blackjack:* `/bj 50` (Hit / Stand / Double buttons)\n\n"
                        "🔐 *Provably Fair Games:*\n"
                        "• 💣 `/mines 50 3` → 5x5 board, 3 mines (1-24)\n"
                        "• 🗼 `/tower 50 easy` → easy / medium / hard / expert / master\n"
                        "• 🚀 `/limbo 50 2` → win if result ≥ your target\n"
                        "• `/fair` seeds · `/setseed <text>` · `/verify <game_id>`\n\n"
                        "🎮 *Versus Games (`/dice`, `/dart`, `/foot`, `/basket`, `/bowl`)*\n"
                        "• `/dice 50` → Opens menu\n"
                        "• `/dice 50 1r1w` → Auto `normal` mode + direct confirmation\n"
                        "• `/dice 50 1r1w crazy` → `crazy` mode + direct confirmation\n"
                        "• `/dice 50 1r1w @username` → Direct PvP challenge to that player\n"
                        "• Reply to a player + `/dice 50 1r1w crazy` → Direct PvP challenge to them\n\n"
                        "🔮 *Prediction Game (`/dr`):*\n"
                        "- `/dr 50 high` or `/dr 50 2,4,6`\n"
                        "- `/dr 50 high self` — you throw the 🎲 yourself (bot throws if you don't in 60s)\n\n"
                        "🎲🎲 *7Up Game (`/7up`):*\n"
                        "- `/7up 50 up` (`high`), `/7up 50 down` (`low`), `/7up 50 odd`, `/7up 50 even`, `/7up 50 7`\n\n"
                        "💡 *Tip:* Amount ki jagah `all` (poora balance) ya `half` (aadha balance) likh sakte ho.\n"
                        "Example: `/tip all @user`, `/dice half`, `/bj all`"
                    )
                    if user_id in admin_list:
                        help_text += "\n\n🛠 *Admin:* `/cancel <game_id>` - Cancel an active game (stake is refunded)"
                    send_message(chat_id, help_text)

                elif re.match(rf"^/top(?:@{re.escape(BOT_USERNAME.lstrip('@'))})?$", text, re.IGNORECASE):
                    bio = generate_top_wagerers_image(viewer_id=user_id)
                    send_photo(chat_id, bio, caption="🏆 *Top 10 Wagerers Leaderboard*")
                    return jsonify({'status': 'ok'}), 200

                elif re.match(rf"^/hb(?:@{re.escape(BOT_USERNAME.lstrip('@'))})?$", text, re.IGNORECASE):
                    send_message(chat_id, f"🏦 *House Balance:* *{format_money(HOUSE_BALANCE, user_id)}*")

                elif re.match(rf"^/(?:history|mybets)(?:@{re.escape(BOT_USERNAME.lstrip('@'))})?$", text, re.IGNORECASE):
                    hist_text, hist_kb = build_user_history_page(user_id, page=0)
                    send_message(chat_id, hist_text, reply_markup=hist_kb)
                    return jsonify({'status': 'ok'}), 200

                elif re.match(rf"^/7up(?:@{re.escape(BOT_USERNAME.lstrip('@'))})?(?:\s|$)", text, re.IGNORECASE):
                    active_summary = get_active_game_summary(user_id)
                    if active_summary:
                        send_message(chat_id, f"⚠️ You are already playing *{active_summary}*! Finish it before starting another game.")
                        return jsonify({'status': 'ok'}), 200

                    tokens = text.split()[1:]
                    bet_inr = None
                    canonical_choice = None
                    raw_choice = None

                    for tok in tokens:
                        norm_c = normalize_7up_choice(tok)
                        if norm_c is not None and canonical_choice is None:
                            canonical_choice = norm_c
                            raw_choice = tok
                        elif bet_inr is None:
                            parsed = parse_user_amount(tok, user_id)
                            if parsed is not None:
                                bet_inr = parsed

                    if canonical_choice is None or bet_inr is None:
                        send_message(
                            chat_id,
                            "⚠️ Usage: `/7up <amount> <up/high | down/low | odd | even | 7>`\n"
                            "Example: `/7up 50 up` or `/7up 50 7`"
                        )
                        return jsonify({'status': 'ok'}), 200

                    current_bal = float(user_balances.get(user_id, 0.0))
                    if bet_inr <= 0:
                        send_message(chat_id, "⚠️ Enter a valid bet amount.")
                    elif bet_out_of_limits(bet_inr, "7up"):
                        send_message(chat_id, bet_limit_text("7up", user_id))
                    elif current_bal < bet_inr:
                        send_message(
                            chat_id,
                            f"❌ *Insufficient Balance!*\n💰 Your Balance: *{format_money(current_bal, user_id)}*\n🎯 Required Bet: *{format_money(bet_inr, user_id)}*"
                        )
                    else:
                        run_7up_game(
                            chat_id, user_id, bet_inr, canonical_choice, raw_choice_text=raw_choice,
                            reply_to_message_id=message.get('message_id') if chat_type in ['group', 'supergroup'] else None
                        )
                    return jsonify({'status': 'ok'}), 200

                elif re.match(FAIR_CMD_RE, text, re.IGNORECASE):
                    handle_fair_command(chat_id, chat_type, user_id, text, message)
                    return jsonify({'status': 'ok'}), 200

                elif re.match(rf"^/bj(?:@{re.escape(BOT_USERNAME.lstrip('@'))})?(?:\s|$)", text, re.IGNORECASE):
                    active_summary = get_active_game_summary(user_id)
                    if active_summary:
                        send_message(chat_id, f"⚠️ You already have an active game (*{active_summary}*)! Finish it before starting a new game.")
                        return jsonify({'status': 'ok'}), 200

                    parts = text.split()
                    bet_inr = parse_user_amount(parts[1], user_id) if len(parts) > 1 else parse_user_amount("10", user_id)
                    current_bal = user_balances.get(user_id, 0.0)

                    if bet_inr is None or bet_inr <= 0:
                        send_message(chat_id, "⚠️ Enter a valid bet amount. Example: `/bj 50`")
                    elif bet_out_of_limits(bet_inr, "special"):
                        send_message(chat_id, bet_limit_text("special", user_id))
                    elif current_bal < bet_inr:
                        send_message(
                            chat_id,
                            f"❌ *Insufficient Balance!*\n💰 Your Balance: *{format_money(current_bal, user_id)}*\n🎯 Required Bet: *{format_money(bet_inr, user_id)}*"
                        )
                    else:
                        start_bj_game(chat_id, user_id, bet_inr)
                    return jsonify({'status': 'ok'}), 200
                    
                elif text in ['/balance', '/bal']:
                    if user_id in deposit_states: del deposit_states[user_id]
                    if user_id in withdrawal_states: del withdrawal_states[user_id]
                    
                    bal_str = format_money(user_balances.get(user_id, 0.0), user_id)
                    
                    if chat_type == 'private':
                        bal_keyboard = {
                            "inline_keyboard": [
                                [
                                    {"text": "💳 Deposit", "callback_data": "btn_deposit"},
                                    {"text": "💸 Withdraw", "callback_data": "btn_withdraw"}
                                ]
                            ]
                        }
                        send_message(chat_id, f"💰 *Wallet Balance:* {bal_str}", reply_markup=bal_keyboard)
                    else:
                        _bot_link = f"https://t.me/{BOT_USERNAME.replace('@','')}"
                        bal_keyboard = {
                            "inline_keyboard": [
                                [
                                    {"text": "💳 Deposit", "url": f"{_bot_link}?start=deposit"},
                                    {"text": "💸 Withdraw", "url": f"{_bot_link}?start=withdraw"}
                                ]
                            ]
                        }
                        send_message(chat_id, f"💰 *Wallet Balance:* {bal_str}", reply_markup=bal_keyboard)
                    
                elif text == '/currency':
                    keyboard = {
                        "inline_keyboard": [
                            [
                                {"text": "🇮🇳 INR (₹)", "callback_data": "curr_inr"},
                                {"text": "🇺🇸 USDT ($)", "callback_data": "curr_usdt"}
                            ]
                        ]
                    }
                    cur_sent = send_message(chat_id, f"🌐 *Select Your Preferred Currency:*\nCurrent: *{user_currency.get(user_id, 'INR')}*", reply_markup=keyboard)
                    remember_button_owner(chat_id, cur_sent, user_id)
                    
                elif text == '/stats':
                    send_message(chat_id, "📊 Generating your stats card...")
                    bio = generate_stats_image(user_id)
                    send_photo(chat_id, bio, caption=f"✨ *Stats for user `{user_id}`*")
                    
                elif text == '/deposit':
                    if chat_type != 'private':
                        send_message(chat_id, f"❌ Deposit command can only be used in Bot's DM (Private Chat)!", reply_markup={"inline_keyboard": [[{"text": "🤖 Open Bot DM", "url": f"https://t.me/{BOT_USERNAME.replace('@','')}"}]]})
                        return jsonify({'status': 'ok'}), 200

                    if not DEPOSIT_ENABLED:
                        send_message(chat_id, "❌ Deposits are currently disabled by Admin.")
                        return jsonify({'status': 'ok'}), 200
                    deposit_states[user_id] = True
                    send_message(chat_id, "💳 *Please enter the amount you want to deposit (e.g. 200):*")
                    
                elif text.startswith('/deposit '):
                    if chat_type != 'private':
                        send_message(chat_id, f"❌ Deposit command can only be used in Bot's DM (Private Chat)!", reply_markup={"inline_keyboard": [[{"text": "🤖 Open Bot DM", "url": f"https://t.me/{BOT_USERNAME.replace('@','')}"}]]})
                        return jsonify({'status': 'ok'}), 200

                    if not DEPOSIT_ENABLED:
                        send_message(chat_id, "❌ Deposits are currently disabled by Admin.")
                        return jsonify({'status': 'ok'}), 200
                    parts = text.split(' ')
                    if len(parts) > 1 and parts[1].replace('.', '', 1).isdigit():
                        amt_inr = parse_user_amount(parts[1], user_id)
                        res_text, pay_kb = create_zapupi_order(amt_inr, user_id)
                        send_message(chat_id, res_text, reply_markup=pay_kb)
                    else:
                        send_message(chat_id, "⚠️ Use format: `/deposit 100`")

                elif text == '/withdraw':
                    if chat_type != 'private':
                        send_message(chat_id, f"❌ Withdrawal command can only be used in Bot's DM (Private Chat)!", reply_markup={"inline_keyboard": [[{"text": "🤖 Open Bot DM", "url": f"https://t.me/{BOT_USERNAME.replace('@','')}"}]]})
                        return jsonify({'status': 'ok'}), 200

                    if not WITHDRAW_ENABLED:
                        send_message(chat_id, "❌ Withdrawals are currently disabled by Admin.")
                        return jsonify({'status': 'ok'}), 200
                    withdrawal_states[user_id] = {'step': 'waiting_amount'}
                    send_message(chat_id, build_withdraw_prompt_text())
                    
                elif text in ['/panel', '/admin']:
                    if user_id in admin_list:
                        panel_text = (
                            "👑 *Owner & Admin Control Dashboard*\n\n"
                            f"🛠 *Maintenance:* {'🟢 OFF' if not MAINTENANCE_MODE else '🔴 ON'}\n"
                            f"💳 *Deposits:* {'🟢 Enabled' if DEPOSIT_ENABLED else '🔴 Disabled'}\n"
                            f"💸 *Withdrawals:* {'🟢 Enabled' if WITHDRAW_ENABLED else '🔴 Disabled'}\n"
                            f"🎮 *DM Games:* {'🟢 ON' if DM_GAMES_ENABLED else '🔴 OFF'}\n"
                            f"🤖 *Helper Bots:* {sum(1 for h in HELPER_BOTS if h.get('enabled'))}/{len(HELPER_BOTS)} ON (`/helper`)\n"
                            f"🏦 *House Balance:* ₹{HOUSE_BALANCE:,.2f}"
                        )
                        admin_keyboard = {
                            "inline_keyboard": [
                                [{"text": "➕ Add Balance", "callback_data": "adm_add_bal"}, {"text": "➖ Deduct Balance", "callback_data": "adm_deduct_bal"}],
                                [{"text": "📊 User Stats", "callback_data": "adm_user_stats"}, {"text": "👥 User List", "callback_data": "adm_users"}],
                                [{"text": "🚫 Ban User", "callback_data": "adm_ban"}, {"text": "✅ Unban User", "callback_data": "adm_unban"}],
                                [{"text": "📥 Last 50 Deposits", "callback_data": "adm_last_dep"}, {"text": "📤 Last 50 Withdraws", "callback_data": "adm_last_wd"}],
                                [{"text": "👑 Grant Admin", "callback_data": "adm_grant"}, {"text": "⛔ Revoke Admin", "callback_data": "adm_revoke"}],
                                [{"text": "📢 Broadcast All", "callback_data": "adm_bc_all"}, {"text": "💬 Broadcast Private", "callback_data": "adm_bc_priv"}],
                                [{"text": "🛠 Toggle Maintenance", "callback_data": "adm_toggle_maint"}],
                                [{"text": "💳 Toggle Deposit", "callback_data": "adm_toggle_dep"}, {"text": "💸 Toggle Withdraw", "callback_data": "adm_toggle_wd"}]
                            ]
                        }
                        send_message(chat_id, panel_text, reply_markup=admin_keyboard)
                    else:
                        pass  # normal users get no reply to admin commands
                        
                elif text.startswith('/dr '):
                    active_summary = get_active_game_summary(user_id)
                    if active_summary:
                        send_message(chat_id, f"⚠️ You are already playing *{active_summary}*! Finish it before starting another game.")
                        return jsonify({'status': 'ok'}), 200

                    _dr_tok = text.split()
                    if len(_dr_tok) == 4 and _dr_tok[3].lower() == 'self':
                        _self_bal = user_balances.get(user_id, 0.0)
                        if not (_dr_tok[1].replace('.', '', 1).isdigit() or is_all_half_word(_dr_tok[1])):
                            send_message(chat_id, "⚠️ Format error! Use: `/dr <amount> <choice> self`\nExample: `/dr 50 high self`")
                            return jsonify({'status': 'ok'}), 200
                        _self_bet = parse_user_amount(_dr_tok[1], user_id)
                        _self_arg = _dr_tok[2].lower()
                        if _self_bet is None or _self_bet <= 0:
                            send_message(chat_id, "⚠️ Enter a valid bet amount.")
                        elif bet_out_of_limits(_self_bet, "dr"):
                            send_message(chat_id, bet_limit_text("dr", user_id))
                        elif _self_bal < _self_bet:
                            send_message(
                                chat_id,
                                f"❌ *Insufficient Balance!*\n💰 Your Balance: *{format_money(_self_bal, user_id)}*\n🎯 Required Bet: *{format_money(_self_bet, user_id)}*"
                            )
                        elif not dr_choice_valid(_self_arg):
                            send_message(chat_id, "⚠️ Invalid format! Use `high`, `low`, `odd`, `even` or numbers like `2,4,6`.\nExample: `/dr 50 high self`")
                        else:
                            start_dr_self_game(
                                chat_id, user_id, _self_bet, _self_arg,
                                reply_to_message_id=message.get('message_id') if chat_type in ['group', 'supergroup'] else None
                            )
                        return jsonify({'status': 'ok'}), 200

                    parts = text.split(' ')
                    current_bal = user_balances.get(user_id, 0.0)
                    if len(parts) == 3 and (parts[1].replace('.', '', 1).isdigit() or is_all_half_word(parts[1])):
                        bet_inr = parse_user_amount(parts[1], user_id)
                        arg = parts[2].lower()
                        
                        if bet_inr is None or bet_inr <= 0:
                            send_message(chat_id, "⚠️ Enter a valid bet amount.")
                            return jsonify({'status': 'ok'}), 200
                        elif bet_out_of_limits(bet_inr, "dr"):
                            send_message(chat_id, bet_limit_text("dr", user_id))
                            return jsonify({'status': 'ok'}), 200
                        elif current_bal < bet_inr:
                            send_message(
                                chat_id,
                                f"❌ *Insufficient Balance!*\n💰 Your Balance: *{format_money(current_bal, user_id)}*\n🎯 Required Bet: *{format_money(bet_inr, user_id)}*"
                            )
                            return jsonify({'status': 'ok'}), 200
                            
                        is_win = False
                        multiplier = 0.0
                        win_desc = ""
                        
                        if arg in ['high', 'low', 'odd', 'even']:
                            gid = generate_game_id()
                            user_balances[user_id] = current_bal - bet_inr
                            register_game_record(gid, "prediction", user_id, bet_inr, meta={"choice": arg}, refund_on_cancel=True)
                            res = send_animated_game(chat_id, '🎲', reply_to_message_id=message.get('message_id') if chat_type in ['group', 'supergroup'] else None)
                            dice_val = res['result']['dice']['value'] if res and 'result' in res else random.randint(1, 6)
                            time.sleep(1)
                            
                            if arg == 'high' and dice_val in [4, 5, 6]: is_win = True
                            elif arg == 'low' and dice_val in [1, 2, 3]: is_win = True
                            elif arg == 'odd' and dice_val in [1, 3, 5]: is_win = True
                            elif arg == 'even' and dice_val in [2, 4, 6]: is_win = True
                            
                            multiplier = float(GAME_MULTIPLIERS.get("dr", 1.92))
                            win_desc = f"Prediction: {arg.upper()}"
                        else:
                            try:
                                nums = [int(n.strip()) for n in arg.split(',')]
                                if not all(1 <= n <= 6 for n in nums) or len(nums) > 5 or len(nums) != len(set(nums)):
                                    raise ValueError()
                                    
                                gid = generate_game_id()
                                user_balances[user_id] = current_bal - bet_inr
                                register_game_record(gid, "prediction", user_id, bet_inr, meta={"nums": nums}, refund_on_cancel=True)
                                res = send_animated_game(chat_id, '🎲', reply_to_message_id=message.get('message_id') if chat_type in ['group', 'supergroup'] else None)
                                dice_val = res['result']['dice']['value'] if res and 'result' in res else random.randint(1, 6)
                                time.sleep(1)
                                
                                if dice_val in nums: is_win = True
                                
                                count = len(nums)
                                dr_num_map = GAME_MULTIPLIERS.get("dr_nums", {1: 5.56, 2: 2.88, 3: 1.92, 4: 1.44, 5: 1.15})
                                multiplier = float(dr_num_map.get(count, 1.0))
                                win_desc = f"Numbers: {nums}"
                            except Exception:
                                send_message(chat_id, "⚠️ Invalid format! Use `high`, `low`, `odd`, `even` or numbers like `2,4,6`.\nExample: `/dr 50 2,4,6`")
                                return jsonify({'status': 'ok'}), 200
                                
                        if is_win:
                            win_amt = bet_inr * multiplier
                            profit_inr = win_amt - bet_inr
                            user_balances[user_id] = user_balances.get(user_id, 0.0) + win_amt
                            HOUSE_BALANCE -= profit_inr
                            update_user_stats(user_id, "prediction", bet_inr, profit_inr, True)
                            record_user_bet(user_id, f"Prediction ({win_desc})", bet_inr, profit_inr, "WON", game_id=gid)
                            mark_game_finished(gid, "completed", extra_meta={"outcome": "WON", "pnl": profit_inr})
                            log_win_to_channel(user_id, "🔮", "Predict", win_amt, fmt_mult(multiplier))
                            result_text = build_dr_result_message(gid, dice_val, arg, True, win_amt=win_amt, multiplier=multiplier, user_id=user_id)
                        else:
                            profit_inr = -bet_inr
                            HOUSE_BALANCE += bet_inr
                            update_user_stats(user_id, "prediction", bet_inr, profit_inr, False)
                            record_user_bet(user_id, f"Prediction ({win_desc})", bet_inr, profit_inr, "LOST", game_id=gid)
                            mark_game_finished(gid, "completed", extra_meta={"outcome": "LOST", "pnl": profit_inr})
                            result_text = build_dr_result_message(gid, dice_val, arg, False, user_id=user_id)
                            
                        pm_dr_payload = {"kind": "dr", "owner_id": user_id, "bet": bet_inr, "dr_arg": arg}
                        send_message(chat_id, result_text, reply_markup=create_post_match_keyboard(user_id, pm_dr_payload))
                    else:
                        send_message(chat_id, "⚠️ Format error! Use: `/dr <amount> <choice>`\nExample: `/dr 50 high` or `/dr 50 1,3,5`")
                        
                else:
                    game_cmd_map = {
                        '/dice': '🎲',
                        '/dart': '🎯',
                        '/foot': '⚽',
                        '/basket': '🏀',
                        '/bowl': '🎳'
                    }
                    
                    triggered_game = None
                    for cmd, emoji in game_cmd_map.items():
                        if re.match(rf"^{re.escape(cmd)}(?:@{re.escape(BOT_USERNAME.lstrip('@'))})?(?:\s|$)", text, re.IGNORECASE):
                            triggered_game = emoji
                            break
                    
                    if triggered_game:
                        active_summary = get_active_game_summary(user_id)
                        if active_summary:
                            send_message(chat_id, f"⚠️ You are already playing *{active_summary}*! Finish it before starting another game.")
                            return jsonify({'status': 'ok'}), 200

                        tokens = text.split()[1:]
                        bet_inr = parse_user_amount("10", user_id)
                        mode = None
                        rw_label = None
                        invalid_rw = False
                        current_bal = user_balances.get(user_id, 0.0)
                        # Direct PvP challenge target: "/dice 50 1r1w @user" or reply to someone's message
                        challenge_target = None
                        target_error = None
                        
                        for tok in tokens:
                            low_tok = tok.lower()
                            if low_tok in ["crazy", "normal"]:
                                mode = low_tok
                            elif re.fullmatch(r"\d+r\d+w", low_tok):
                                if low_tok in VALID_RW_MODES:
                                    rw_label = low_tok
                                else:
                                    invalid_rw = True
                            elif tok.startswith("@") and len(tok) > 1:
                                found_uid = username_to_id.get(tok.lstrip("@").lower())
                                if found_uid is None:
                                    target_error = f"⚠️ Player `{tok}` not found! Ask them to send any message in the group first, or reply to their message with the command."
                                else:
                                    challenge_target = found_uid
                            else:
                                parsed = parse_user_amount(tok, user_id)
                                if parsed is not None:
                                    bet_inr = parsed
                                elif username_to_id.get(low_tok) is not None:
                                    challenge_target = username_to_id[low_tok]

                        reply_msg = message.get('reply_to_message') or {}
                        reply_from = reply_msg.get('from') or {}
                        if challenge_target is None and target_error is None and reply_from:
                            if reply_from.get('is_bot'):
                                target_error = None  # replying to the bot's own message: normal game flow
                            else:
                                challenge_target = register_user_identity(reply_from)

                        if challenge_target is not None and rw_label is None:
                            rw_label = "1r1w"
                        if rw_label is not None and mode is None:
                            mode = "normal"
                                    
                        if target_error:
                            send_message(chat_id, target_error)
                        elif challenge_target is not None and chat_type not in ['group', 'supergroup']:
                            send_message(chat_id, "❌ Player vs Player challenges are only available in groups!")
                        elif challenge_target is not None and challenge_target == user_id:
                            send_message(chat_id, "⚠️ You cannot challenge yourself!")
                        elif invalid_rw:
                            send_message(chat_id, "⚠️ Invalid RW mode! Allowed modes: `1r1w`, `2r1w`, `3r1w`, `1r2w`, `2r2w`, `3r2w`, `1r3w`, `2r3w`, `3r3w`.")
                        elif bet_inr is None or bet_inr <= 0:
                            send_message(chat_id, "⚠️ Enter a valid bet amount.")
                        elif bet_out_of_limits(bet_inr, "emoji"):
                            send_message(chat_id, bet_limit_text("emoji", user_id))
                        elif current_bal < bet_inr:
                            send_message(
                                chat_id,
                                f"❌ *Insufficient Balance!*\n💰 Your Balance: *{format_money(current_bal, user_id)}*\n🎯 Required Bet: *{format_money(bet_inr, user_id)}*"
                            )
                        else:
                            gid = generate_game_id()
                            g_name = GAME_NAME_MAP.get(triggered_game, "Game")
                            if challenge_target is not None:
                                send_direct_pvp_challenge(
                                    chat_id, user_id, challenge_target, triggered_game, bet_inr, mode, rw_label, gid,
                                    trigger_msg_id=message.get('message_id')
                                )
                            elif rw_label is not None and mode is not None:
                                conf_msg = build_match_confirmation_text(user_id, triggered_game, bet_inr, mode, rw_label, game_id=gid)
                                sent = send_message(
                                    chat_id, conf_msg, reply_markup=match_confirm_keyboard(chat_type),
                                    reply_to_message_id=message.get('message_id') if chat_type in ['group', 'supergroup'] else None
                                )
                                msg_id = sent.get("result", {}).get("message_id") if sent and sent.get("ok") else None
                                remember_button_owner(chat_id, msg_id, user_id)
                                pending_game_setup[user_id] = {
                                    "game_id": gid,
                                    "chat_id": chat_id,
                                    "chat_type": chat_type,
                                    "message_id": msg_id,
                                    "trigger_msg_id": message.get('message_id'),
                                    "emoji": triggered_game,
                                    "bet": bet_inr,
                                    "mode": mode,
                                    "rw_label": rw_label
                                }
                            elif mode is None:
                                setup_msg = (
                                    f"🎮 *{g_name} ({triggered_game}) Setup* (`{gid}`)\n"
                                    f"💰 Bet: *{format_money(bet_inr, user_id)}*\n\n"
                                    "Select Mode:"
                                )
                                sent = send_message(chat_id, setup_msg, reply_markup=game_style_keyboard())
                                msg_id = sent.get("result", {}).get("message_id") if sent and sent.get("ok") else None
                                remember_button_owner(chat_id, msg_id, user_id)
                                pending_game_setup[user_id] = {
                                    "game_id": gid,
                                    "chat_id": chat_id,
                                    "chat_type": chat_type,
                                    "message_id": msg_id,
                                    "emoji": triggered_game,
                                    "bet": bet_inr,
                                    "mode": None,
                                    "rw_label": None
                                }
                            else:
                                mode_title = "🔥 CRAZY MODE" if mode == "crazy" else "⚡ NORMAL MODE"
                                rw_msg = (
                                    f"🎯 *Select RW Mode* (`{gid}` | {g_name} {triggered_game} | {mode_title})\n"
                                    f"💰 Bet: *{format_money(bet_inr, user_id)}*\n\nTap a mode below:"
                                )
                                sent = send_message(chat_id, rw_msg, reply_markup=rw_mode_keyboard())
                                msg_id = sent.get("result", {}).get("message_id") if sent and sent.get("ok") else None
                                remember_button_owner(chat_id, msg_id, user_id)
                                pending_game_setup[user_id] = {
                                    "game_id": gid,
                                    "chat_id": chat_id,
                                    "chat_type": chat_type,
                                    "message_id": msg_id,
                                    "emoji": triggered_game,
                                    "bet": bet_inr,
                                    "mode": mode,
                                    "rw_label": None
                                }

        elif 'callback_query' in data:
            query = data['callback_query']
            callback_query_id = query['id']
            callback_data = query['data']
            chat_id = query['message']['chat']['id']
            chat_type = query['message']['chat']['type']
            message_id = query['message']['message_id']
            user_id = query['from']['id']

            # Messages sent after a button tap reply to the user's original command.
            _tg_ctx.reply_chat = chat_id
            _tg_ctx.reply_mid = (query['message'].get('reply_to_message') or {}).get('message_id') or message_id

            
            if callback_data.startswith("rain_join_"):
                handle_rain_join(callback_query_id, callback_data, chat_id, message_id, query['from'])
                return jsonify({'status': 'ok'}), 200

            if callback_data.startswith("mtx_ok_") or callback_data.startswith("mtx_no_"):
                is_confirm = callback_data.startswith("mtx_ok_")
                token = callback_data.replace("mtx_ok_", "", 1) if is_confirm else callback_data.replace("mtx_no_", "", 1)
                entry = pending_manual_txns.get(token)
                if not entry:
                    answer_callback(callback_query_id, "Transaction already processed or expired.")
                    remove_inline_keyboard(chat_id, message_id)
                    return jsonify({'status': 'ok'}), 200
                if user_id != entry.get("initiator_id"):
                    answer_callback(callback_query_id, NOT_YOUR_MESSAGE_TEXT)
                    return jsonify({'status': 'ok'}), 200
                pending_manual_txns.pop(token, None)
                entry["prompt_message_id"] = message_id
                if entry.get("action_type") in ("grp_addbal", "grp_deductbal"):
                    if is_confirm:
                        execute_manual_txn(entry)
                        answer_callback(callback_query_id, "Done!")
                    else:
                        edit_message(chat_id, message_id, "❌ *Cancelled.*")
                        answer_callback(callback_query_id, "Cancelled.")
                    return jsonify({'status': 'ok'}), 200
                remove_inline_keyboard(chat_id, message_id)
                if is_confirm:
                    execute_manual_txn(entry)
                    answer_callback(callback_query_id, "Transaction confirmed!")
                else:
                    edit_message(chat_id, message_id, "❌ *Transaction Cancelled.*")
                    answer_callback(callback_query_id, "Transaction cancelled.")
                return jsonify({'status': 'ok'}), 200

            # Direct challenge: only the challenged player may accept
            if callback_data.startswith("pvp_acc_"):
                _ch = open_pvp_challenges.get(callback_data.replace("pvp_acc_", ""))
                if _ch and _ch.get("target_id") is not None and user_id != _ch["target_id"]:
                    if user_id == _ch.get("host_id"):
                        answer_callback(callback_query_id, "You cannot accept your own challenge!")
                    else:
                        answer_callback(callback_query_id, "This challenge is not for you ❌")
                    return jsonify({'status': 'ok'}), 200

            # Another player tapped someone else's buttons: warn them, change nothing.
            shared_buttons = ("rain_join_", "pvp_acc_", "pvp_can_", "adm_", "admin_wd_", "admin_wdid_", "infopg_", "pm_again_", "pm_double_", "myhistpg_", "myrefpg_")
            if not callback_data.startswith(shared_buttons):
                btn_owner = find_button_owner(chat_id, message_id)
                if btn_owner is not None and btn_owner != user_id:
                    answer_callback(callback_query_id, NOT_YOUR_MESSAGE_TEXT)
                    return jsonify({'status': 'ok'}), 200

            if chat_type == 'private' and not DM_GAMES_ENABLED and (callback_data.startswith("pm_again_") or callback_data.startswith("pm_double_")):
                answer_callback(callback_query_id, "❌ Games in DM are currently turned off.")
                remove_inline_keyboard(chat_id, message_id)
                send_message(chat_id, build_dm_games_off_text())
                return jsonify({'status': 'ok'}), 200

            if callback_data.startswith("pm_again_") or callback_data.startswith("pm_double_"):
                is_double = callback_data.startswith("pm_double_")
                token = callback_data.replace("pm_double_", "", 1) if is_double else callback_data.replace("pm_again_", "", 1)
                payload = post_match_actions.get(token)
                if not payload:
                    answer_callback(callback_query_id, "This action has already been used or expired.")
                    remove_inline_keyboard(chat_id, message_id)
                    return jsonify({'status': 'ok'}), 200
                if user_id != payload.get("owner_id"):
                    answer_callback(callback_query_id, NOT_YOUR_MESSAGE_TEXT)
                    return jsonify({'status': 'ok'}), 200
                active_summary = get_active_game_summary(user_id)
                if active_summary:
                    answer_callback(callback_query_id, f"Finish your active {active_summary} game first!")
                    return jsonify({'status': 'ok'}), 200
                post_match_actions.pop(token, None)
                factor = 2.0 if is_double else 1.0
                execute_post_match_restart(chat_id, message_id, user_id, payload, factor, callback_query_id)
                return jsonify({'status': 'ok'}), 200

            if callback_data.startswith("hlp_"):
                if user_id not in admin_list:
                    answer_callback(callback_query_id, NOT_YOUR_MESSAGE_TEXT)
                    return jsonify({'status': 'ok'}), 200
                note = handle_helper_button(callback_data)
                h_text, h_kb = build_helper_panel()
                edit_message(chat_id, message_id, h_text, reply_markup=h_kb)
                answer_callback(callback_query_id, note)
                return jsonify({'status': 'ok'}), 200

            answer_callback(callback_query_id)
            
            if not callback_data.startswith(("mn_", "tw_", "pf_")) and not callback_data.startswith("adm_") and not callback_data.startswith("bj_") and not callback_data.startswith("gs_") and not callback_data.startswith("rw_") and not callback_data.startswith("mc_") and not callback_data.startswith("pvp_") and not callback_data.startswith("infopg_") and not callback_data.startswith("myhistpg_") and not callback_data.startswith("myrefpg_") and not callback_data.startswith("lvlpg_"):
                remove_inline_keyboard(chat_id, message_id)
            
            register_user_identity(query.get('from'))

            if callback_data.startswith("infopg_"):
                if user_id not in admin_list:
                    pass  # normal users get no reply to admin commands
                    return jsonify({'status': 'ok'}), 200
                try:
                    _, raw_uid, section, raw_page = callback_data.split("_", 3)
                    target_uid = int(raw_uid)
                    page = int(raw_page)
                    sec_text, sec_kb = build_user_info_section_page(target_uid, section, page)
                    edit_message(chat_id, message_id, sec_text, reply_markup=sec_kb)
                except Exception as e:
                    print(f"Info pagination error: {e}")
                return jsonify({'status': 'ok'}), 200

            if callback_data.startswith("lvlpg_"):
                try:
                    _, raw_uid, raw_idx = callback_data.split("_", 2)
                    target_uid = int(raw_uid)
                    if user_id != target_uid:
                        answer_callback(callback_query_id, NOT_YOUR_MESSAGE_TEXT)
                        return jsonify({'status': 'ok'}), 200
                    lv_text, lv_kb = build_level_page(target_uid, int(raw_idx))
                    edit_message(chat_id, message_id, lv_text, reply_markup=lv_kb)
                except Exception as e:
                    print(f"Levels page error: {e}")
                return jsonify({'status': 'ok'}), 200

            if callback_data.startswith("myrefpg_"):
                try:
                    _, raw_uid, raw_page = callback_data.split("_", 2)
                    target_uid = int(raw_uid)
                    if user_id != target_uid and user_id not in admin_list:
                        return jsonify({'status': 'ok'}), 200
                    mr_text, mr_kb = build_myref_page(target_uid, page=int(raw_page))
                    edit_message(chat_id, message_id, mr_text, reply_markup=mr_kb)
                except Exception as e:
                    print(f"Myref pagination error: {e}")
                return jsonify({'status': 'ok'}), 200

            if callback_data.startswith("myhistpg_"):
                try:
                    _, raw_uid, raw_page = callback_data.split("_", 2)
                    target_uid = int(raw_uid)
                    page = int(raw_page)
                    if user_id != target_uid and user_id not in admin_list:
                        answer_callback(callback_query_id, NOT_YOUR_MESSAGE_TEXT)
                        return jsonify({'status': 'ok'}), 200
                    hist_text, hist_kb = build_user_history_page(target_uid, page=page)
                    edit_message(chat_id, message_id, hist_text, reply_markup=hist_kb)
                except Exception as e:
                    print(f"History pagination error: {e}")
                return jsonify({'status': 'ok'}), 200

            if callback_data == "gs_cancel":
                setup = pending_game_setup.pop(user_id, None)
                if setup and setup.get("game_id") in game_id_registry:
                    mark_game_finished(setup["game_id"], "cancelled")
                target_chat = (setup or {}).get("chat_id") or chat_id
                target_msg = (setup or {}).get("message_id") or message_id
                for cid, ch in list(open_pvp_challenges.items()):
                    if ch["host_id"] == user_id:
                        if ch.get("game_id"):
                            mark_game_finished(ch["game_id"], "cancelled")
                        open_pvp_challenges.pop(cid, None)
                edit_message(target_chat, target_msg, "❌ Game cancelled.")
                return jsonify({'status': 'ok'}), 200

            if callback_data in ["gs_style_crazy", "gs_style_normal"]:
                if user_id not in pending_game_setup:
                    edit_message(chat_id, message_id, "⚠️ Session expired. Start a new game command.")
                    return jsonify({'status': 'ok'}), 200
                setup = pending_game_setup[user_id]
                chosen_mode = "crazy" if callback_data == "gs_style_crazy" else "normal"
                setup["mode"] = chosen_mode
                target_chat = setup.get("chat_id") or chat_id
                target_msg = setup.get("message_id") or message_id
                target_chat_type = setup.get("chat_type") or chat_type
                setup["message_id"] = target_msg
                bet_inr = setup["bet"]
                emoji = setup["emoji"]
                gid = setup.get("game_id")
                current_bal = user_balances.get(user_id, 0.0)

                if setup.get("rw_label") in VALID_RW_MODES:
                    if bet_out_of_limits(bet_inr, "emoji"):
                        pending_game_setup.pop(user_id, None)
                        edit_message(target_chat, target_msg, bet_limit_text("emoji", user_id))
                    elif current_bal < bet_inr:
                        pending_game_setup.pop(user_id, None)
                        edit_message(
                            target_chat,
                            target_msg,
                            f"❌ *Insufficient Balance!*\n💰 Your Balance: *{format_money(current_bal, user_id)}*\n🎯 Required Bet: *{format_money(bet_inr, user_id)}*"
                        )
                    else:
                        conf_msg = build_match_confirmation_text(user_id, emoji, bet_inr, chosen_mode, setup["rw_label"], game_id=gid)
                        edit_message(target_chat, target_msg, conf_msg, reply_markup=match_confirm_keyboard(target_chat_type))
                    return jsonify({'status': 'ok'}), 200

                g_name = GAME_NAME_MAP.get(emoji, "Game")
                mode_title = "🔥 CRAZY MODE" if chosen_mode == "crazy" else "⚡ NORMAL MODE"
                rw_msg = (
                    f"🎯 *Select RW Mode* (`{gid}` | {g_name} {emoji} | {mode_title})\n"
                    f"💰 Bet: *{format_money(bet_inr, user_id)}*\n\nTap a mode below:"
                )
                edit_message(target_chat, target_msg, rw_msg, reply_markup=rw_mode_keyboard())
                return jsonify({'status': 'ok'}), 200

            if callback_data.startswith("rw_pick_"):
                chosen_rw = callback_data.replace("rw_pick_", "")
                if user_id not in pending_game_setup or chosen_rw not in VALID_RW_MODES:
                    edit_message(chat_id, message_id, "⚠️ RW selection expired. Start the game command again.")
                    return jsonify({'status': 'ok'}), 200

                setup = pending_game_setup[user_id]
                target_chat = setup.get("chat_id") or chat_id
                target_msg = setup.get("message_id") or message_id
                target_chat_type = setup.get("chat_type") or chat_type
                setup["message_id"] = target_msg
                bet_inr = setup["bet"]
                mode = setup["mode"] or "normal"
                setup["mode"] = mode
                setup["rw_label"] = chosen_rw
                emoji = setup["emoji"]
                gid = setup.get("game_id")
                current_bal = user_balances.get(user_id, 0.0)

                if bet_out_of_limits(bet_inr, "emoji"):
                    pending_game_setup.pop(user_id, None)
                    edit_message(target_chat, target_msg, bet_limit_text("emoji", user_id))
                elif current_bal < bet_inr:
                    pending_game_setup.pop(user_id, None)
                    edit_message(
                        target_chat,
                        target_msg,
                        f"❌ *Insufficient Balance!*\n💰 Your Balance: *{format_money(current_bal, user_id)}*\n🎯 Required Bet: *{format_money(bet_inr, user_id)}*"
                    )
                else:
                    conf_msg = build_match_confirmation_text(user_id, emoji, bet_inr, mode, chosen_rw, game_id=gid)
                    edit_message(target_chat, target_msg, conf_msg, reply_markup=match_confirm_keyboard(target_chat_type))
                return jsonify({'status': 'ok'}), 200

            if callback_data == "mc_bot":
                if user_id not in pending_game_setup:
                    edit_message(chat_id, message_id, "⚠️ Confirmation expired. Start a new game command.")
                    return jsonify({'status': 'ok'}), 200
                conf = pending_game_setup.pop(user_id)
                target_chat = conf.get("chat_id") or chat_id
                target_msg = conf.get("message_id") or message_id
                active_summary = get_active_game_summary(user_id)
                if active_summary:
                    edit_message(target_chat, target_msg, f"⚠️ You are already playing *{active_summary}*! Finish it before starting another game.")
                    return jsonify({'status': 'ok'}), 200
                bet_inr = conf["bet"]
                gid = conf.get("game_id") or generate_game_id()
                current_bal = user_balances.get(user_id, 0.0)
                if bet_out_of_limits(bet_inr, "emoji"):
                    edit_message(target_chat, target_msg, bet_limit_text("emoji", user_id))
                elif current_bal < bet_inr:
                    edit_message(
                        target_chat,
                        target_msg,
                        f"❌ *Insufficient Balance!*\n💰 Your Balance: *{format_money(current_bal, user_id)}*\n🎯 Required Bet: *{format_money(bet_inr, user_id)}*"
                    )
                else:
                    start_versus_match(target_chat, target_msg, user_id, conf["emoji"], bet_inr, conf["mode"] or "normal", conf["rw_label"], game_id=gid, trigger_msg_id=conf.get("trigger_msg_id"))
                return jsonify({'status': 'ok'}), 200

            if callback_data == "mc_player":
                if user_id not in pending_game_setup:
                    edit_message(chat_id, message_id, "⚠️ Confirmation expired. Start a new game command.")
                    return jsonify({'status': 'ok'}), 200
                conf = pending_game_setup.pop(user_id)
                target_chat = conf.get("chat_id") or chat_id
                target_msg = conf.get("message_id") or message_id
                target_chat_type = conf.get("chat_type") or chat_type

                if target_chat_type == "private":
                    edit_message(target_chat, target_msg, "❌ Against Player is only available in groups!")
                    return jsonify({'status': 'ok'}), 200

                active_summary = get_active_game_summary(user_id)
                if active_summary:
                    edit_message(target_chat, target_msg, f"⚠️ You are already playing *{active_summary}*! Finish it before starting a PvP challenge.")
                    return jsonify({'status': 'ok'}), 200

                bet_inr = conf["bet"]
                current_bal = user_balances.get(user_id, 0.0)
                if bet_out_of_limits(bet_inr, "emoji"):
                    edit_message(target_chat, target_msg, bet_limit_text("emoji", user_id))
                    return jsonify({'status': 'ok'}), 200
                if current_bal < bet_inr:
                    edit_message(
                        target_chat,
                        target_msg,
                        f"❌ *Insufficient Balance!*\n💰 Your Balance: *{format_money(current_bal, user_id)}*\n🎯 Required Bet: *{format_money(bet_inr, user_id)}*"
                    )
                    return jsonify({'status': 'ok'}), 200

                challenge_id = uuid.uuid4().hex[:8]
                gid = conf.get("game_id") or generate_game_id()
                mode = conf["mode"] or "normal"
                rw_label = conf["rw_label"] or "1r1w"
                rolls_per_round, target_wins = VALID_RW_MODES[rw_label]
                mode_label = "CRAZY" if mode == "crazy" else "NORMAL"
                g_name = GAME_NAME_MAP.get(conf["emoji"], "Game")

                open_pvp_challenges[challenge_id] = {
                    "game_id": gid,
                    "chat_id": target_chat,
                    "message_id": target_msg,
                    "host_id": user_id,
                    "emoji": conf["emoji"],
                    "bet": bet_inr,
                    "mode": mode,
                    "rw_label": rw_label,
                    "rolls_per_round": rolls_per_round,
                    "target_wins": target_wins,
                }
                invite_msg = (
                    "⚔️ *Player vs Player Challenge!*\n\n"
                    f"🆔 *Game ID:* `{gid}`\n"
                    f"👤 *Challenger:* {tag_player(user_id)}\n"
                    f"🎮 *Game:* {g_name} ({conf['emoji']})\n"
                    f"⚙️ *Mode:* *{mode_label}*\n"
                    f"🏆 *RW Format:* `{rw_label}` (First to *{target_wins}*)\n"
                    f"💰 *Bet Each:* *{format_money(bet_inr, user_id)}*\n\n"
                    "Tap *Accept* to start:"
                )
                kb = {
                    "inline_keyboard": [
                        [
                            {"text": "✅ Accept Challenge", "callback_data": f"pvp_acc_{challenge_id}"},
                            {"text": "❌ Cancel", "callback_data": f"pvp_can_{challenge_id}"}
                        ]
                    ]
                }
                edit_message(target_chat, target_msg, invite_msg, reply_markup=kb)
                return jsonify({'status': 'ok'}), 200

            if callback_data.startswith("pvp_can_"):
                cid = callback_data.replace("pvp_can_", "")
                ch = open_pvp_challenges.get(cid)
                if not ch:
                    edit_message(chat_id, message_id, "⚠️ Challenge already closed or expired.")
                    return jsonify({'status': 'ok'}), 200
                if user_id != ch["host_id"] and user_id != ch.get("target_id") and user_id not in admin_list:
                    answer_callback(callback_query_id, NOT_YOUR_MESSAGE_TEXT)
                    return jsonify({'status': 'ok'}), 200
                if ch.get("game_id"):
                    mark_game_finished(ch["game_id"], "cancelled")
                open_pvp_challenges.pop(cid, None)
                if ch.get("target_id") is not None and user_id == ch.get("target_id"):
                    edit_message(ch.get("chat_id") or chat_id, ch.get("message_id") or message_id, f"❌ {tag_player(user_id)} declined the PvP challenge.")
                else:
                    edit_message(ch.get("chat_id") or chat_id, ch.get("message_id") or message_id, f"❌ PvP Challenge `{cid}` cancelled.")
                return jsonify({'status': 'ok'}), 200

            if callback_data.startswith("pvp_acc_"):
                cid = callback_data.replace("pvp_acc_", "")
                ch = open_pvp_challenges.get(cid)
                if not ch:
                    edit_message(chat_id, message_id, "⚠️ Challenge already accepted or expired.")
                    return jsonify({'status': 'ok'}), 200

                host_id = ch["host_id"]
                if user_id == host_id:
                    answer_callback(callback_query_id, "You cannot accept your own challenge!")
                    return jsonify({'status': 'ok'}), 200

                active_summary = get_active_game_summary(user_id)
                if active_summary:
                    answer_callback(callback_query_id, f"Finish your active {active_summary} game first!")
                    return jsonify({'status': 'ok'}), 200

                host_active = get_active_game_summary(host_id)
                if host_active:
                    if ch.get("game_id"):
                        mark_game_finished(ch["game_id"], "cancelled")
                    open_pvp_challenges.pop(cid, None)
                    target_chat = ch.get("chat_id") or chat_id
                    target_msg = ch.get("message_id") or message_id
                    edit_message(target_chat, target_msg, f"⚠️ Challenger is already in *{host_active}*. Challenge cancelled.")
                    return jsonify({'status': 'ok'}), 200

                bet_inr = ch["bet"]
                target_chat = ch.get("chat_id") or chat_id
                target_msg = ch.get("message_id") or message_id

                if user_balances.get(host_id, 0.0) < bet_inr:
                    if ch.get("game_id"):
                        mark_game_finished(ch["game_id"], "cancelled")
                    open_pvp_challenges.pop(cid, None)
                    edit_message(target_chat, target_msg, "❌ Challenger has insufficient balance. Challenge cancelled.")
                    return jsonify({'status': 'ok'}), 200

                if user_balances.get(user_id, 0.0) < bet_inr:
                    answer_callback(callback_query_id, "Insufficient balance to accept!")
                    return jsonify({'status': 'ok'}), 200

                open_pvp_challenges.pop(cid, None)
                user_balances[host_id] = user_balances.get(host_id, 0.0) - bet_inr
                user_balances[user_id] = user_balances.get(user_id, 0.0) - bet_inr

                gid = ch.get("game_id") or generate_game_id()
                match_id = f"pvp_{cid}"
                register_game_record(
                    gid,
                    "pvp_match",
                    host_id,
                    bet_inr,
                    meta={"match_id": match_id, "p1_id": host_id, "p2_id": user_id},
                    refund_on_cancel=True
                )
                active_pvp_games[match_id] = {
                    "game_id": gid,
                    "chat_id": target_chat,
                    "p1_id": host_id,
                    "p2_id": user_id,
                    "emoji": ch["emoji"],
                    "bet": bet_inr,
                    "mode": ch["mode"],
                    "rw_label": ch["rw_label"],
                    "rolls_per_round": ch["rolls_per_round"],
                    "target_wins": ch["target_wins"],
                    "round_num": 1,
                    "p1_wins": 0,
                    "p2_wins": 0,
                    "p1_rolls": [],
                    "p2_rolls": [],
                    "turn": host_id,
                }
                active_games[host_id] = match_id
                active_games[user_id] = match_id

                start_text = (
                    f"🎮 *PvP Match Started!* (`{gid}` | {ch['emoji']} | `{ch['rw_label']}`)\n"
                    f"👤 {tag_player(host_id)} vs {tag_player(user_id)} | Bet: *{format_money(bet_inr, user_id)}*\n"
                    f"🎯 First to *{ch['target_wins']}* round win(s) | *{ch['rolls_per_round']}* roll(s)/round\n\n"
                    f"👉 *Round 1 —* {tag_player(host_id)}, *send* `{ch['emoji']}` *x{ch['rolls_per_round']} in chat!*"
                )
                edit_message(target_chat, target_msg, start_text)
                schedule_pvp_turn_timeout(target_chat, match_id, active_pvp_games[match_id])
                return jsonify({'status': 'ok'}), 200

            if callback_data.startswith(("mn_", "tw_", "pf_")):
                handle_fair_callback(chat_id, message_id, user_id, callback_data)
                return jsonify({'status': 'ok'}), 200

            if callback_data.startswith("bj_"):
                if user_id not in active_bj_games:
                    edit_message(chat_id, message_id, "⚠️ Blackjack session expired. Start a new game with `/bj <amount>`.")
                    return jsonify({'status': 'ok'}), 200

                bj = active_bj_games[user_id]
                target_chat = bj.get("chat_id") or chat_id
                target_msg = bj.get("message_id") or message_id

                if callback_data == "bj_hit":
                    bj["player_cards"].append(bj_draw(bj))
                    p_tot = calculate_hand_total(bj["player_cards"])
                    if p_tot > 21:
                        finish_bj_game(target_chat, target_msg, user_id, bj, "bust")
                    elif p_tot == 21:
                        play_dealer_and_settle(target_chat, target_msg, user_id, bj)
                    else:
                        msg = (
                            f"🃏 *Blackjack (Hit)* (`{bj.get('game_id')}`)\n\n"
                            f"👤 Your Hand: {format_cards(bj['player_cards'])} (*{p_tot}*)\n"
                            f"🤖 Dealer Shows: `{bj['dealer_cards'][0]}` `[?]`\n"
                            f"💰 Bet: {format_money(bj['bet'], user_id)}\n\n"
                            f"Choose your next move:" + bj_fair_footer(bj)
                        )
                        edit_message(target_chat, target_msg, msg, reply_markup=bj_action_keyboard(can_double=False))

                elif callback_data == "bj_stand":
                    play_dealer_and_settle(target_chat, target_msg, user_id, bj)

                elif callback_data == "bj_double":
                    extra_bet = bj["bet"]
                    if user_balances.get(user_id, 0.0) < extra_bet:
                        p_tot = calculate_hand_total(bj["player_cards"])
                        msg = (
                            f"🃏 *Blackjack* (`{bj.get('game_id')}`)\n\n"
                            f"👤 Your Hand: {format_cards(bj['player_cards'])} (*{p_tot}*)\n"
                            f"🤖 Dealer Shows: `{bj['dealer_cards'][0]}` `[?]`\n"
                            f"💰 Bet: {format_money(bj['bet'], user_id)}\n\n"
                            f"❌ Insufficient balance to Double! Choose Hit or Stand:" + bj_fair_footer(bj)
                        )
                        edit_message(target_chat, target_msg, msg, reply_markup=bj_action_keyboard(can_double=False))
                        return jsonify({'status': 'ok'}), 200

                    user_balances[user_id] = user_balances.get(user_id, 0.0) - extra_bet
                    bj["bet"] += extra_bet
                    bj["doubled"] = True
                    bj["player_cards"].append(bj_draw(bj))
                    p_tot = calculate_hand_total(bj["player_cards"])

                    if p_tot > 21:
                        finish_bj_game(target_chat, target_msg, user_id, bj, "bust")
                    else:
                        play_dealer_and_settle(target_chat, target_msg, user_id, bj)

                return jsonify({'status': 'ok'}), 200
                
            if callback_data == "curr_inr":
                user_currency[user_id] = 'INR'
                persist_user(user_id)
                send_message(chat_id, "✅ Currency successfully set to *INR (₹)*!")
            elif callback_data == "curr_usdt":
                user_currency[user_id] = 'USDT'
                persist_user(user_id)
                send_message(chat_id, "✅ Currency successfully set to *USD ($)*!")
                
            elif callback_data == "btn_deposit":
                if chat_type != 'private':
                    send_message(chat_id, f"❌ Deposit can only be done in Bot's DM!", reply_markup={"inline_keyboard": [[{"text": "🤖 Open Bot DM", "url": f"https://t.me/{BOT_USERNAME.replace('@','')}"}]]})
                    return jsonify({'status': 'ok'}), 200

                if not DEPOSIT_ENABLED:
                    send_message(chat_id, "❌ Deposits are currently disabled by Admin.")
                    return jsonify({'status': 'ok'}), 200
                deposit_states[user_id] = True
                send_message(chat_id, "💳 *Please enter the amount you want to deposit (e.g. 200):*")
                
            elif callback_data == "btn_withdraw":
                if chat_type != 'private':
                    send_message(chat_id, f"❌ Withdrawal can only be done in Bot's DM!", reply_markup={"inline_keyboard": [[{"text": "🤖 Open Bot DM", "url": f"https://t.me/{BOT_USERNAME.replace('@','')}"}]]})
                    return jsonify({'status': 'ok'}), 200

                if not WITHDRAW_ENABLED:
                    send_message(chat_id, "❌ Withdrawals are currently disabled by Admin.")
                    return jsonify({'status': 'ok'}), 200
                withdrawal_states[user_id] = {'step': 'waiting_amount'}
                send_message(chat_id, build_withdraw_prompt_text())
                
            elif callback_data.startswith("adm_"):
                if user_id not in admin_list:
                    pass  # normal users get no reply to admin commands
                    return jsonify({'status': 'ok'}), 200
                    
                if callback_data == "adm_add_bal":
                    admin_states[user_id] = {'action': 'add_bal'}
                    send_message(chat_id, "➕ *Enter User ID and Amount to add*\nFormat: `<user_id> <amount>`")
                elif callback_data == "adm_deduct_bal":
                    admin_states[user_id] = {'action': 'deduct_bal'}
                    send_message(chat_id, "➖ *Enter User ID and Amount to deduct*\nFormat: `<user_id> <amount>`")
                elif callback_data == "adm_user_stats":
                    admin_states[user_id] = {'action': 'user_stats'}
                    send_message(chat_id, "📊 *Enter User ID to view stats:*")
                elif callback_data == "adm_users":
                    txt = "👥 *Registered Users & Balances:*\n"
                    for uid, bal in user_balances.items():
                        status = "🔴 BANNED" if uid in banned_users else "🟢 Active"
                        txt += f"- `{uid}`: {format_money(bal, uid)} [{status}]\n"
                    send_message(chat_id, txt)
                elif callback_data == "adm_ban":
                    admin_states[user_id] = {'action': 'ban_user'}
                    send_message(chat_id, "🚫 *Enter User ID to Ban:*")
                elif callback_data == "adm_unban":
                    admin_states[user_id] = {'action': 'unban_user'}
                    send_message(chat_id, "✅ *Enter User ID to Unban:*")
                elif callback_data == "adm_last_dep":
                    txt = "📥 *Last 50 Deposits:*\n"
                    for d in deposit_history[-50:]:
                        t_str = f" [{d['time']}]" if d.get("time") else ""
                        txt += f"- `{d.get('id', '-')}` | User `{d['user']}`: {format_money(d['amount'], d['user'])} (UTR: `{d['utr']}`){t_str}\n"
                    if not deposit_history: txt += "No deposits recorded yet."
                    send_message(chat_id, txt)
                elif callback_data == "adm_last_wd":
                    txt = "📤 *Last 50 Withdrawals:*\n"
                    for w in withdrawal_history[-50:]:
                        t_str = f" [{w['time']}]" if w.get("time") else ""
                        st_tag = {"pending": "⏳", "paid": "✅", "rejected": "❌"}.get(w.get("status"), "📁")
                        txt += f"- {st_tag} `{w.get('id', '-')}` | User `{w['user']}`: {format_money(w['amount'], w['user'])} to `{w['upi']}`{t_str}\n"
                    if not withdrawal_history: txt += "No withdrawals recorded yet."
                    send_message(chat_id, txt)
                elif callback_data == "adm_grant":
                    admin_states[user_id] = {'action': 'grant_admin'}
                    send_message(chat_id, "👑 *Enter User ID to grant Admin rights:*")
                elif callback_data == "adm_revoke":
                    admin_states[user_id] = {'action': 'revoke_admin'}
                    send_message(chat_id, "⛔ *Enter User ID to revoke Admin rights:*")
                elif callback_data == "adm_bc_all":
                    admin_states[user_id] = {'action': 'broadcast_all'}
                    send_message(chat_id, "📢 *Enter message to broadcast to all users:*")
                elif callback_data == "adm_bc_priv":
                    admin_states[user_id] = {'action': 'broadcast_private'}
                    send_message(chat_id, "💬 *Enter User ID and Message*\nFormat: `<user_id> <message>`")
                elif callback_data == "adm_toggle_maint":
                    MAINTENANCE_MODE = not MAINTENANCE_MODE
                    send_message(chat_id, f"🛠 Maintenance Mode is now: {'🔴 ON' if MAINTENANCE_MODE else '🟢 OFF'}")
                elif callback_data == "adm_toggle_dep":
                    DEPOSIT_ENABLED = not DEPOSIT_ENABLED
                    send_message(chat_id, f"💳 Deposits are now: {'🟢 Enabled' if DEPOSIT_ENABLED else '🔴 Disabled'}")
                elif callback_data == "adm_toggle_wd":
                    WITHDRAW_ENABLED = not WITHDRAW_ENABLED
                    send_message(chat_id, f"💸 Withdrawals are now: {'🟢 Enabled' if WITHDRAW_ENABLED else '🔴 Disabled'}")
                
            elif callback_data == "wd_cancel":
                # Balance is only cut on confirm, so nothing needs to be refunded here.
                if user_id in withdrawal_states and withdrawal_states[user_id].get('step') != 'waiting_reject_reason':
                    del withdrawal_states[user_id]
                send_message(chat_id, "❌ Withdrawal request cancelled. No money was deducted.")
                
            elif callback_data == "wd_confirm":
                if user_id in withdrawal_states:
                    st = withdrawal_states[user_id]
                    if st.get('step') != 'confirming' or 'amount' not in st or 'upi_id' not in st:
                        return jsonify({'status': 'ok'}), 200
                    if validate_upi_id(st['upi_id'])[1]:
                        send_message(chat_id, "⚠️ Invalid UPI ID. Please start /withdraw again.")
                        del withdrawal_states[user_id]
                        return jsonify({'status': 'ok'}), 200
                    wd_err = validate_withdraw_amount(st['amount'], user_id)
                    if wd_err:
                        send_message(chat_id, wd_err)
                        del withdrawal_states[user_id]
                        return jsonify({'status': 'ok'}), 200
                    bd = withdraw_breakdown(st['amount'])
                    raw_amt = bd['debit']
                        
                    user_balances[user_id] = user_balances.get(user_id, 0.0) - raw_amt
                    if user_id not in user_withdrawals: user_withdrawals[user_id] = 0.0
                    user_withdrawals[user_id] += raw_amt
                    
                    ts_wd = current_timestamp()
                    wd_id = generate_txn_id("WD")
                    withdrawal_history.append({
                        'id': wd_id,
                        'user': user_id,
                        'amount': raw_amt,
                        'upi': st['upi_id'],
                        'time': ts_wd,
                        'status': 'pending',
                        'processed_at': '',
                        'processed_by': None,
                        'reject_reason': '',
                        'fee': bd['fee'],
                        'payout': bd['payout']
                    })
                    persist_withdrawal(user_id, raw_amt, st['upi_id'], ts_wd, txn_id=wd_id, status='pending', fee=bd['fee'], payout=bd['payout'])
                    rakeback_on_withdraw(user_id, raw_amt, wd_id)
                    persist_user(user_id)
                    
                    amt_str = format_money(raw_amt, user_id)
                    upi_id = st['upi_id']
                    
                    send_message(chat_id, f"📤 *Withdrawal Request Submitted!*\n\n🆔 Withdraw ID: `{wd_id}`\n💰 Amount: *₹{bd['requested']:,.2f}*\n🧾 Fee: *₹{bd['fee']:,.2f}*\n✅ You Receive: *₹{bd['payout']:,.2f}*\n\nYour request has been sent to the admin for verification. You will be notified once processed.")
                    
                    admin_msg = (
                        "🚨 *NEW WITHDRAWAL REQUEST*\n\n"
                        f"🆔 Withdraw ID: `{wd_id}`\n"
                        f"👤 User ID: `{user_id}`\n"
                        f"💰 Requested: *₹{bd['requested']:,.2f}*\n"
                        f"🧾 Fee: *₹{bd['fee']:,.2f}*\n"
                        f"➖ Cut from Balance: *₹{bd['debit']:,.2f}*\n"
                        f"💸 *PAY TO USER: ₹{bd['payout']:,.2f}*\n"
                        f"🏦 UPI ID: `{upi_id}`"
                    )
                    admin_keyboard = {
                        "inline_keyboard": [
                            [
                                {"text": "✅ Paid", "callback_data": f"admin_wdid_paid_{wd_id}"},
                                {"text": "❌ Reject", "callback_data": f"admin_wdid_reject_{wd_id}"}
                            ]
                        ]
                    }
                    send_message(ADMIN_USER_ID, admin_msg, reply_markup=admin_keyboard)
                    # Withdraw log channel is posted only when an admin marks it as Paid.
                    del withdrawal_states[user_id]
                
            elif (callback_data.startswith("admin_wdid_paid_") or callback_data.startswith("admin_wdid_reject_")
                  or callback_data.startswith("admin_wd_paid_") or callback_data.startswith("admin_wd_reject_")):
                if user_id in admin_list:
                    parts = callback_data.split('_')
                    action = parts[2]
                    wd = None
                    if parts[1] == "wdid":
                        wd = find_withdrawal("_".join(parts[3:]))
                    else:
                        # Buttons sent before Withdraw IDs existed: admin_wd_<action>_<user>_<amount>
                        try:
                            old_user = int(parts[3])
                            old_amt = float(parts[4])
                        except (IndexError, ValueError):
                            old_user, old_amt = None, None
                        for w in reversed(withdrawal_history):
                            if w.get("user") == old_user and abs(float(w.get("amount", 0)) - (old_amt or 0)) < 1e-9 and w.get("status") in ("pending", "legacy"):
                                wd = w
                                break
                        if wd is None and old_user is not None:
                            # Fallback: keep old behaviour working even if record is missing
                            wd = {"id": None, "user": old_user, "amount": old_amt, "upi": "", "status": "pending"}

                    if not wd:
                        send_message(chat_id, "⚠️ Withdrawal not found.")
                        return jsonify({'status': 'ok'}), 200
                    if wd.get("status") in ("paid", "rejected"):
                        send_message(chat_id, f"⚠️ Withdrawal {('`' + wd['id'] + '` ') if wd.get('id') else ''}is already *{wd['status']}*.")
                        return jsonify({'status': 'ok'}), 200

                    target_user = wd["user"]
                    raw_amt = float(wd["amount"])
                    amt_str = format_money(raw_amt, target_user)
                    paid_str = f"₹{float(wd['payout']):,.2f}" if wd.get("payout") is not None else amt_str
                    wd_id = wd.get("id")
                    id_line = f"🆔 Withdraw ID: `{wd_id}`\n" if wd_id else ""
                    
                    if action == "paid":
                        ts_paid = current_timestamp()
                        wd["status"] = "paid"
                        wd["processed_at"] = ts_paid
                        wd["processed_by"] = user_id
                        persist_withdrawal_status(wd_id, "paid", ts_paid, user_id)
                        rakeback_on_withdraw_done(target_user, wd_id, rejected=False)
                        persist_user(target_user)

                        success_msg = (
                            "🎉 *Withdrawal Approved & Paid!* ✨\n\n"
                            f"{id_line}"
                            f"Dear User, your withdrawal of *{paid_str}* has been successfully processed and transferred to your account/UPI ID. 🚀\n\n"
                            f"Thank you for playing with *{BOT_USERNAME}*! 🎰"
                        )
                        send_message(target_user, success_msg)
                        send_message(chat_id, f"✅ Successfully marked withdrawal {('`' + wd_id + '` ') if wd_id else ''}for user `{target_user}` as Paid.")

                        # Post to the withdraw log channel only after payment, details masked
                        withdraw_log_channel = normalize_channel_id(WITHDRAW_LOG_CHANNEL_ID)
                        if withdraw_log_channel:
                            upi_part = f"🏦 UPI ID: `{mask_upi_id_for_log(wd.get('upi'))}`\n" if wd.get("upi") else ""
                            channel_log_msg = (
                                "✅ *WITHDRAWAL PAID*\n\n"
                                f"👤 User ID: `{mask_user_id_for_log(target_user)}`\n"
                                f"💰 Amount: *{paid_str}*\n"
                                f"{upi_part}"
                                f"🕒 Paid At: `{ts_paid}`"
                            )
                            send_message(withdraw_log_channel, channel_log_msg)
                    elif action == "reject":
                        withdrawal_states[user_id] = {
                            'step': 'waiting_reject_reason',
                            'target_user': target_user,
                            'raw_amount': raw_amt,
                            'amount_str': amt_str,
                            'wd_id': wd_id,
                            'admin_msg_id': message_id,
                            'admin_chat_id': chat_id
                        }
                        send_message(chat_id, f"✍️ *Please enter the rejection reason for {('`' + wd_id + '` / ') if wd_id else ''}user `{target_user}` in chat:*")
                else:
                    pass  # normal users get no reply to admin commands
                
            elif callback_data == "play_bot_first":
                remove_inline_keyboard(chat_id, message_id)
                with get_turn_lock(f"pvb_{user_id}"):
                    if user_id not in active_games or isinstance(active_games[user_id], str):
                        send_message(chat_id, "⚠️ Session expired. Start a new game.")
                        return jsonify({'status': 'ok'}), 200
                        
                    game = active_games[user_id]
                    if game.get("step") != "selecting_turn":
                        return jsonify({'status': 'ok'}), 200
                    game["turn_token"] = None
                    game["start_message_id"] = None
                    emoji = game["emoji"]
                    rolls_needed = game["rolls_per_round"]
                    game["current_user_rolls"] = []
                    game["current_bot_rolls"] = []
                    
                    game["first_turn"] = "bot"
                    game["step"] = "waiting_user_second"
                    player_tag = format_user_mention(user_id)
                    trig_id = game.get("trigger_msg_id")
                    send_message(chat_id, f"🤖 Bot is throwing `{emoji}` x{rolls_needed} first for {player_tag}...", reply_to_message_id=trig_id)
                    
                    b_vals = roll_bot_series(chat_id, emoji, rolls_needed, reply_to_message_id=trig_id)
                    game["current_bot_rolls"] = b_vals
                    b_expr = "+".join(map(str, b_vals))
                    
                    send_message(chat_id, f"🤖 Bot Roll: `{b_expr}` (*{sum(b_vals)}*)\n\n👉 *Now* {tag_player(user_id)}*'s turn! Send `{emoji}` x{rolls_needed} in chat.*")
                    schedule_pvb_turn_timeout(chat_id, user_id, game)
                
        return jsonify({'status': 'ok'}), 200
    except Exception as e:
        print(f"❌ Webhook Error: {e}")
        return jsonify({'status': 'error', 'message': str(e)}), 200


# ===================== 🤖 /helper COMMAND + HELPER WEBHOOK =====================
def _public_base_url():
    env = os.environ.get("PUBLIC_URL")
    if env:
        return env.rstrip("/")
    host = request.headers.get("X-Forwarded-Host") or request.host
    return f"https://{host}"

def helper_set_hook(h, base_url):
    """Button taps on helper messages (Bet Again / Bet Double) come back to this server."""
    data = _helper_post(h, "setWebhook", {
        "url": f"{base_url}/helper-webhook/{h['id']}",
        "secret_token": helper_hook_secret(h["token"]),
        "allowed_updates": ["callback_query"],
        "drop_pending_updates": True,
    }, timeout=10)
    h["hook"] = bool(data and data.get("ok"))
    return h["hook"]

def build_helper_panel():
    on_count = sum(1 for h in HELPER_BOTS if h.get("enabled"))
    lines = [f"🤖 *Helper Bots* ({len(HELPER_BOTS)}/{MAX_HELPERS}) · {on_count} ON", ""]
    if not HELPER_BOTS:
        lines.append("No helper added yet. Main bot is throwing emojis itself.")
    for i, h in enumerate(HELPER_BOTS, 1):
        state = "🟢 ON" if h.get("enabled") else "🔴 OFF"
        btn = "" if h.get("hook") else " · ⚠️ buttons not linked"
        lines.append(f"{i}. @{_md_safe(h.get('username'))} — {state}{btn}")
    lines += [
        "",
        "Helpers throw every emoji in groups and send the round / final round messages.",
        "Main bot throws only in DMs, or as backup if no helper can.",
        "",
        "`/helper add <token>` — add (send in bot DM)",
        "`/helper remove 1` · `/helper on 1` · `/helper off 1`",
        "`/helper on all` · `/helper off all`",
        "`/helper test` — send in the group to check helpers",
    ]
    rows = []
    for i, h in enumerate(HELPER_BOTS, 1):
        rows.append([
            {"text": f"{i}. @{h.get('username')} {'🟢 ON' if h.get('enabled') else '🔴 OFF'}", "callback_data": f"hlp_tg_{h['id']}"},
            {"text": "🗑 Remove", "callback_data": f"hlp_rm_{h['id']}"},
        ])
    return "\n".join(lines), ({"inline_keyboard": rows} if rows else None)

def _find_helper(ref):
    ref = str(ref or "").strip().lstrip("@").lower()
    if ref.isdigit() and 1 <= int(ref) <= len(HELPER_BOTS):
        return HELPER_BOTS[int(ref) - 1]
    for h in HELPER_BOTS:
        if str(h.get("username", "")).lower() == ref or str(h.get("id")) == ref:
            return h
    return None

def _remove_helper(h):
    _helper_post(h, "deleteWebhook", {"drop_pending_updates": True})
    if h in HELPER_BOTS:
        HELPER_BOTS.remove(h)
    save_helpers()

def handle_helper_button(data):
    try:
        hid = int(data.rsplit("_", 1)[1])
    except Exception:
        return "Expired."
    h = next((x for x in HELPER_BOTS if x.get("id") == hid), None)
    if not h:
        return "Helper already removed."
    if data.startswith("hlp_tg_"):
        h["enabled"] = not h.get("enabled")
        save_helpers()
        return f"@{h.get('username')} is now {'ON' if h['enabled'] else 'OFF'}"
    if data.startswith("hlp_rm_"):
        _remove_helper(h)
        return f"@{h.get('username')} removed"
    return ""

def handle_helper_command(chat_id, chat_type, text, message):
    parts = text.split()
    sub = parts[1].lower() if len(parts) > 1 else ""
    arg = parts[2] if len(parts) > 2 else ""

    if sub == "add":
        if chat_type != "private":
            try:
                requests.post(f"{TELEGRAM_API_URL}/deleteMessage", json={"chat_id": chat_id, "message_id": message.get("message_id")}, timeout=3)
            except Exception:
                pass
            send_message(chat_id, "🔒 Never send a bot token in a group. Send `/helper add <token>` in my DM.\nIf others saw it, open @BotFather → /revoke for that bot and use the new token.")
            return
        token = arg.strip()
        if not re.match(r"^\d{5,}:[A-Za-z0-9_-]{30,}$", token):
            send_message(chat_id, "⚠️ Usage: `/helper add <bot token>`\nCreate a new bot in @BotFather (/newbot) and paste its token here.")
            return
        if TELEGRAM_BOT_TOKEN and token.split(":")[0] == str(TELEGRAM_BOT_TOKEN).split(":")[0]:
            send_message(chat_id, "⚠️ That is the main bot's own token. Use a new bot from @BotFather.")
            return
        if any(h.get("token") == token or str(h.get("id")) == token.split(":")[0] for h in HELPER_BOTS):
            send_message(chat_id, "⚠️ This helper is already added.")
            return
        if len(HELPER_BOTS) >= MAX_HELPERS:
            send_message(chat_id, f"⚠️ Max {MAX_HELPERS} helpers. Remove one first with `/helper remove <number>`.")
            return
        try:
            me = requests.get(f"https://api.telegram.org/bot{token}/getMe", timeout=8).json()
        except Exception:
            me = None
        if not me or not me.get("ok") or not (me.get("result") or {}).get("is_bot"):
            send_message(chat_id, "❌ Token not working. Copy it again from @BotFather.")
            return
        r = me["result"]
        h = {"id": r["id"], "username": r.get("username") or str(r["id"]), "token": token, "enabled": True, "hook": False}
        hook_ok = helper_set_hook(h, _public_base_url())
        HELPER_BOTS.append(h)
        save_helpers()
        n = len(HELPER_BOTS)
        uname = _md_safe(h["username"])
        msg = (
            f"✅ *Helper {n} added:* @{uname} (🟢 ON)\n\n"
            f"Next step: add @{uname} to your game group(s).\n"
            "If members can't send stickers/GIFs in that group, make the helper an admin.\n"
            "Then send `/helper test` in the group."
        )
        if not hook_ok:
            msg += "\n\n⚠️ Could not link its buttons — final round messages with buttons will be sent by the main bot. Try `/helper add` again later."
        send_message(chat_id, msg)
        return

    if sub in ("remove", "del", "delete", "rm"):
        h = _find_helper(arg)
        if not h:
            send_message(chat_id, "⚠️ Usage: `/helper remove <number>` (see `/helper`)")
            return
        _remove_helper(h)
        send_message(chat_id, f"🗑 Helper @{_md_safe(h.get('username'))} removed.")
        return

    if sub in ("on", "off"):
        want = sub == "on"
        targets = HELPER_BOTS if arg.lower() == "all" else [x for x in [_find_helper(arg)] if x]
        if not targets:
            send_message(chat_id, f"⚠️ Usage: `/helper {sub} <number>` or `/helper {sub} all`")
            return
        for h in targets:
            h["enabled"] = want
            if want:
                _helper_cooldown.pop(h.get("id"), None)
                for k in [k for k in _helper_chat_block if k[0] == h.get("id")]:
                    _helper_chat_block.pop(k, None)
        save_helpers()
        names = ", ".join("@" + _md_safe(h.get("username")) for h in targets)
        send_message(chat_id, f"{'🟢' if want else '🔴'} {names} {'ON' if want else 'OFF'}.")
        return

    if sub == "test":
        if chat_type == "private":
            send_message(chat_id, "ℹ️ Send `/helper test` inside the game group.")
            return
        report = []
        for i, h in enumerate(HELPER_BOTS, 1):
            uname = _md_safe(h.get("username"))
            if not h.get("enabled"):
                report.append(f"{i}. @{uname} — 🔴 OFF")
                continue
            _helper_chat_block.pop((h.get("id"), chat_id), None)
            data = _helper_post(h, "sendMessage", {"chat_id": chat_id, "text": f"🤖 Helper {i} ready ✅"})
            if data and data.get("ok"):
                report.append(f"{i}. @{uname} — ✅ ready")
            else:
                why = (data or {}).get("description", "no reply")
                report.append(f"{i}. @{uname} — ❌ {_md_safe(why)}")
        if not report:
            report.append("No helpers added. Use `/helper add <token>` in my DM.")
        send_message(chat_id, "🧪 *Helper test*\n" + "\n".join(report))
        return

    p_text, p_kb = build_helper_panel()
    send_message(chat_id, p_text, reply_markup=p_kb)

@app.route('/helper-webhook/<int:helper_id>', methods=['POST'])
def helper_webhook(helper_id):
    """Button taps on messages a helper sent arrive here and are handled exactly
    like main-bot taps, but the replies go out through that helper."""
    h = next((x for x in HELPER_BOTS if x.get("id") == helper_id), None)
    if not h:
        return jsonify({'status': 'ok'}), 200
    got = request.headers.get("X-Telegram-Bot-Api-Secret-Token", "")
    if not _hb_hmac.compare_digest(got, helper_hook_secret(h["token"])):
        return "Unauthorized", 401
    data = request.get_json(silent=True) or {}
    if 'callback_query' not in data:
        return jsonify({'status': 'ok'}), 200
    prev = getattr(_tg_ctx, "api", None)
    _tg_ctx.api = helper_api(h)
    try:
        return telegram_webhook()
    finally:
        _tg_ctx.api = prev

_deposit_lock = threading.Lock()
ZAPUPI_STATUS_URL = "https://pay.zapupi.com/api/order-status"
ALLOW_ZAPUPI_TEST = os.environ.get("ALLOW_ZAPUPI_TEST", "0") == "1"   # 'test' environment payments are NOT real money
ZAPUPI_VERIFY_RETRY_DELAYS = [20, 60, 180, 600]                       # seconds, used if ZapUPI status API is slow/down

def _alert_owner(text):
    try:
        send_message(ADMIN_USER_ID, text)
    except Exception as e:
        print(f"owner alert failed: {e}")

def verify_zapupi_order(order_id):
    """Asks ZapUPI directly (order-status API) whether this order is really paid.
    Returns (state, data): state is 'paid' | 'pending' | 'failed' | 'error'."""
    try:
        r = requests.post(ZAPUPI_STATUS_URL, json={"zap_key": ZAPUPI_API_KEY, "order_id": order_id}, timeout=10)
        resp = r.json()
    except Exception as e:
        print(f"order-status request failed for {order_id}: {e}")
        return "error", {}
    if not isinstance(resp, dict):
        return "error", {}
    d = resp.get("data") if isinstance(resp.get("data"), dict) else resp   # works for nested or flat response
    st = str(d.get("status") or "").strip().lower()
    if st in ("success", "paid", "completed"):
        return "paid", d
    if st in ("pending", "processing", "created", "initiated"):
        return "pending", d
    print(f"order-status for {order_id} not paid: {resp}")
    return "failed", d

def _amount_matches(value, expected):
    try:
        return math.isfinite(float(value)) and abs(float(value) - float(expected)) <= 0.01
    except (TypeError, ValueError):
        return False

def process_zapupi_success(order_id, webhook_utr="", webhook_env=""):
    """Returns 'credited' | 'dup' | 'rejected' | 'retry'. Safe to call many times for the same order."""
    with _deposit_lock:
        rec = deposit_orders.get(order_id) if order_id else None
        if not rec:
            print(f"⚠️ ZapUPI success for unknown order {order_id!r}, NOT credited")
            _alert_owner(f"⚠️ *Unknown deposit order* `{order_id}`\nUTR: `{webhook_utr}`\nNot credited — check manually.")
            return "rejected"
        if rec.get("status") == "credited":
            return "dup"
        expected = float(rec["amount"])
        chat_id = int(rec["user"])

    # Confirm with ZapUPI itself (network call, kept outside the lock)
    state, d = verify_zapupi_order(order_id)
    if state in ("error", "pending"):
        return "retry"
    if state != "paid":
        _alert_owner(f"⚠️ *Webhook said success but ZapUPI says NOT paid*\nOrder: `{order_id}`\nUser: `{chat_id}`\nNot credited.")
        return "rejected"

    env = str(d.get("environment") or webhook_env or "").strip().lower()
    if env == "test" and not ALLOW_ZAPUPI_TEST:
        print(f"⚠️ ZapUPI TEST payment {order_id}, NOT credited")
        _alert_owner(f"🧪 *Test-environment payment ignored*\nOrder: `{order_id}`\nUser: `{chat_id}`\nNot credited (real money only).")
        return "rejected"

    api_oid = d.get("order_id")
    if api_oid and str(api_oid) != str(order_id):
        _alert_owner(f"⚠️ *Order id mismatch from ZapUPI*\nOurs: `{order_id}`\nTheirs: `{api_oid}`\nNot credited.")
        return "rejected"

    if not (_amount_matches(d.get("amount"), expected) or _amount_matches(d.get("pay_amount"), expected)):
        print(f"⚠️ Amount mismatch order {order_id}: expected {expected}, ZapUPI says {d.get('amount')}/{d.get('pay_amount')}")
        _alert_owner(f"⚠️ *Deposit amount mismatch*\nOrder: `{order_id}`\nUser: `{chat_id}`\nExpected: ₹{expected}\nZapUPI amount: {d.get('amount')} / pay_amount: {d.get('pay_amount')}\nUTR: `{d.get('utr') or webhook_utr}`\nNot credited — check manually.")
        return "rejected"

    utr = str(d.get("utr") or webhook_utr or "")
    with _deposit_lock:
        rec = deposit_orders.get(order_id)
        if not rec or rec.get("status") == "credited":
            return "dup"
        amount = expected
        with get_user_lock(chat_id):
            if chat_id not in user_balances:
                user_balances[chat_id] = 0.0
                user_currency[chat_id] = 'INR'
            user_balances[chat_id] += amount
            user_deposits[chat_id] = user_deposits.get(chat_id, 0.0) + amount

            ts_dep = current_timestamp()
            dep_id = rec["id"]
            rec["status"] = "credited"
            rec["credited_at"] = ts_dep
            persist_deposit_order(rec)
            deposit_history.append({
                'id': dep_id, 'user': chat_id, 'amount': amount,
                'utr': utr, 'order_id': order_id, 'time': ts_dep
            })
            persist_deposit(chat_id, amount, utr, ts_dep, txn_id=dep_id, order_id=order_id)
            rakeback_on_deposit(chat_id, amount)
            persist_user(chat_id)
            referral_on_deposit(chat_id, amount)
            new_balance = user_balances[chat_id]

    # Messages go out after the locks are released
    send_message(chat_id, f"✅ *Deposit Successful!* 🎉\n\n🆔 Deposit ID: `{dep_id}`\nAdded: {format_money(amount, chat_id)}\nNew Balance: {format_money(new_balance, chat_id)}\nOrder ID: `{order_id}`\nUTR: `{utr}`")
    # Private alert to the owner only (not to other admins or any channel)
    send_message(ADMIN_USER_ID, (
        "💰 *NEW DEPOSIT RECEIVED*\n\n"
        f"🆔 Deposit ID: `{dep_id}`\n"
        f"👤 User: {_user_label_for_report(chat_id)}\n"
        f"💵 Amount: *{format_money(amount, chat_id)}*\n"
        f"🏦 New Balance: *{format_money(new_balance, chat_id)}*\n"
        f"🧾 Order ID: `{order_id}`\n"
        f"🔢 UTR: `{utr}`\n"
        f"🕒 Time: `{ts_dep}`"
    ))
    return "credited"

def _retry_zapupi_verification(order_id, utr, env):
    for delay in ZAPUPI_VERIFY_RETRY_DELAYS:
        time.sleep(delay)
        try:
            if process_zapupi_success(order_id, utr, env) != "retry":
                return
        except Exception as e:
            print(f"verify retry error for {order_id}: {e}")
    _alert_owner(f"⚠️ *Could not verify payment with ZapUPI*\nOrder: `{order_id}`\nUTR: `{utr}`\nNot credited — check the ZapUPI dashboard and add balance manually if it is paid.")

@app.route('/zapupi-webhook', methods=['POST'])
def zapupi_webhook():
    try:
        # Only ZapUPI (which knows the secret key in the URL) may call this.
        got = request.args.get("key", "") or request.headers.get("X-Webhook-Key", "")
        if not hmac.compare_digest(got, ZAPUPI_WEBHOOK_SECRET):
            print("⚠️ ZapUPI webhook rejected: bad key")
            return "Unauthorized", 401

        data = request.get_json(silent=True)
        if not data:
            return jsonify({'status': 'error', 'message': 'No data'}), 400

        order_id = str(data.get('order_id') or '').strip()
        status = str(data.get('status') or '').strip().lower()   # ZapUPI sends "Success" | "Failed"
        utr = str(data.get('utr') or '')
        env = str(data.get('environment') or '')

        if status == 'success':
            outcome = process_zapupi_success(order_id, utr, env)
            if outcome == "retry":
                threading.Thread(target=_retry_zapupi_verification, args=(order_id, utr, env), daemon=True).start()

        # ZapUPI wants HTTP 200 + {"status":"ok"} always
        return jsonify({'status': 'ok'}), 200
    except Exception as e:
        print(f"❌ ZapUPI Webhook Error: {e}")
        return jsonify({'status': 'ok'}), 200


# ===================== 🧨 RESET ALL DATA (owner only, /resetdata) =====================
RESET_KEEP_SETTINGS = False   # True = wipe only player data, keep settings + approved groups
RESET_CONFIRM_SECONDS = 120   # the Confirm button stops working after this
SETTINGS_TABLES = ["bot_config", "approved_groups"]
PLAYER_DATA_TABLES = [
    "users", "bet_logs", "deposits", "withdrawals", "deposit_orders",
    "game_records", "fair_seeds", "fair_revealed_seeds",
]
_reset_lock = threading.Lock()

def _snapshot_default_config():
    return {
        "HOUSE_BALANCE": HOUSE_BALANCE, "MIN_BET": MIN_BET, "MAX_BET": MAX_BET,
        "EXCHANGE_RATE": EXCHANGE_RATE, "MAINTENANCE_MODE": MAINTENANCE_MODE,
        "DEPOSIT_ENABLED": DEPOSIT_ENABLED, "WITHDRAW_ENABLED": WITHDRAW_ENABLED,
        "DM_GAMES_ENABLED": DM_GAMES_ENABLED, "GROUP_LINK": GROUP_LINK,
        "MIN_DEPOSIT": MIN_DEPOSIT, "MIN_WITHDRAW": MIN_WITHDRAW,
        "GAME_MULTIPLIERS": copy.deepcopy(GAME_MULTIPLIERS),
        "BET_LIMITS": copy.deepcopy(BET_LIMITS), "LIMBO_MAX_PAYOUT": LIMBO_MAX_PAYOUT,
    }

# Taken before anything is loaded from the database = the code's default settings.
_DEFAULT_CONFIG = _snapshot_default_config()

def _clear_player_memory():
    for store in (
        user_balances, user_currency, user_usernames, user_first_names, username_to_id,
        user_stats, user_deposits, user_withdrawals, user_bet_logs,
        deposit_history, withdrawal_history, banned_users,
        active_games, active_7up_games, pending_game_setup, open_pvp_challenges, active_rains, active_dr_self_games,
        active_pvp_games, active_bj_games, post_match_actions, button_owners,
        pending_manual_txns, game_id_registry, deposit_states, withdrawal_states,
        admin_states, _txn_ids_in_use, deposit_orders,
        fair_seeds, revealed_server_seeds, active_mines_games, active_tower_games,
    ):
        store.clear()
    admin_list.clear()
    admin_list.add(ADMIN_USER_ID)

def _restore_default_settings():
    global HOUSE_BALANCE, MIN_BET, MAX_BET, EXCHANGE_RATE, MAINTENANCE_MODE, DEPOSIT_ENABLED
    global WITHDRAW_ENABLED, DM_GAMES_ENABLED, GROUP_LINK, MIN_DEPOSIT, MIN_WITHDRAW, LIMBO_MAX_PAYOUT
    d = _DEFAULT_CONFIG
    BET_LIMITS.clear()
    BET_LIMITS.update(copy.deepcopy(d["BET_LIMITS"]))
    LIMBO_MAX_PAYOUT = d["LIMBO_MAX_PAYOUT"]
    HOUSE_BALANCE = d["HOUSE_BALANCE"]
    MIN_BET = d["MIN_BET"]
    MAX_BET = d["MAX_BET"]
    EXCHANGE_RATE = d["EXCHANGE_RATE"]
    MAINTENANCE_MODE = d["MAINTENANCE_MODE"]
    DEPOSIT_ENABLED = d["DEPOSIT_ENABLED"]
    WITHDRAW_ENABLED = d["WITHDRAW_ENABLED"]
    DM_GAMES_ENABLED = d["DM_GAMES_ENABLED"]
    GROUP_LINK = d["GROUP_LINK"]
    MIN_DEPOSIT = d["MIN_DEPOSIT"]
    MIN_WITHDRAW = d["MIN_WITHDRAW"]
    GAME_MULTIPLIERS.clear()
    GAME_MULTIPLIERS.update(copy.deepcopy(d["GAME_MULTIPLIERS"]))
    approved_groups.clear()

def reset_all_bot_data():
    """Deletes every bot table, creates fresh empty ones and clears memory.
    Helper bots are kept so dice keep working in groups. Returns (ok, error_text)."""
    with _reset_lock:
        tables = list(PLAYER_DATA_TABLES) + ([] if RESET_KEEP_SETTINGS else list(SETTINGS_TABLES))
        conn = get_db_connection()
        if conn:
            try:
                with conn:
                    with conn.cursor() as cur:
                        cur.execute("DROP TABLE IF EXISTS " + ", ".join(tables) + " CASCADE")
            except Exception as e:
                print(f"DB reset error: {e}")
                return False, str(e)
            finally:
                conn.close()
            init_db()
            init_fair_db()
        _clear_player_memory()
        if not RESET_KEEP_SETTINGS:
            _restore_default_settings()
            persist_config_all()
            save_helpers()
        return True, None


init_db()
load_all_from_db()
try:
    rakeback_backfill()
except Exception as _rb_e:
    print(f"Rakeback backfill error: {_rb_e}")
init_fair_db()
load_fair_from_db()

def report_orphan_games():
    """Games that were 'active' when the server restarted lost their in-memory state.
    Tell the owner so they can /cancel them (stake is refunded for refundable games)."""
    try:
        orphans = [g for g in game_id_registry.values() if g.get("status") == "active"]
        if not orphans:
            return
        lines = [f"`{g.get('game_id')}` — {g.get('kind')} — user `{g.get('owner_id')}` — ₹{g.get('bet_inr')}" for g in orphans[:40]]
        more = f"\n…and {len(orphans) - 40} more" if len(orphans) > 40 else ""
        _alert_owner("♻️ *Bot restarted — unfinished games found:*\n\n" + "\n".join(lines) + more +
                     "\n\nCancel each with `/cancel <GAME_ID>` to refund the stake (check the player balance first).")
    except Exception as e:
        print(f"orphan report error: {e}")

def register_main_webhook():
    """Registers /webhook with Telegram WITH the secret token, so only Telegram can call it."""
    try:
        r = requests.post(f"{TELEGRAM_API_URL}/setWebhook", json={
            "url": f"{PUBLIC_BASE_URL}/webhook",
            "secret_token": TELEGRAM_WEBHOOK_SECRET,
        }, timeout=15).json()
        print(f"setWebhook: {r}")
    except Exception as e:
        print(f"setWebhook failed: {e}")

if os.environ.get("AUTO_SET_WEBHOOK", "1") == "1":
    threading.Thread(target=register_main_webhook, daemon=True).start()
threading.Thread(target=report_orphan_games, daemon=True).start()

if __name__ == '__main__':
    # Local testing only. In production run:  gunicorn app:app --workers 1 --threads 16 --timeout 120
    app.run(host='0.0.0.0', port=int(os.environ.get("PORT", 5000)))
