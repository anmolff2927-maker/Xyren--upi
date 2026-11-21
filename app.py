import os
import time
import random
import io
import re
import uuid
import string
import threading
import copy
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

ADMIN_USER_ID = 1822336097
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
        with conn:
            with conn.cursor() as cur:
                cur.execute(
                    """
                    INSERT INTO users (user_id, balance, currency, username, first_name, is_banned, is_admin, total_deposits, total_withdrawals, stats_json)
                    VALUES (%s, %s, %s, %s, %s, %s, %s, %s, %s, %s)
                    ON CONFLICT (user_id) DO UPDATE SET
                        balance = EXCLUDED.balance,
                        currency = EXCLUDED.currency,
                        username = COALESCE(EXCLUDED.username, users.username),
                        first_name = COALESCE(EXCLUDED.first_name, users.first_name),
                        is_banned = EXCLUDED.is_banned,
                        is_admin = EXCLUDED.is_admin,
                        total_deposits = EXCLUDED.total_deposits,
                        total_withdrawals = EXCLUDED.total_withdrawals,
                        stats_json = EXCLUDED.stats_json
                    """,
                    (uid, bal, curr, uname, fname, is_banned, is_adm, tot_dep, tot_wd, st_json)
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
    conn = get_db_connection()
    if not conn:
        return
    try:
        with conn.cursor(cursor_factory=RealDictCursor) as cur:
            cur.execute("SELECT key, value_json FROM bot_config")
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
    mode_label = "CRAZY (Lowest Sum Wins)" if mode == "crazy" else "NORMAL (Highest Sum Wins)"
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
    mode_label = "CRAZY (Lowest Sum Wins)" if mode == "crazy" else "NORMAL (Highest Sum Wins)"
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
    mode_title = "🔥 CRAZY MODE (Lowest Sum Wins)" if mode == "crazy" else "⚡ NORMAL MODE (Highest Sum Wins)"
    player_tag = format_user_mention(user_id)
    keyboard = {
        "inline_keyboard": [
            [
                {"text": "🤖 Bot Roll First", "callback_data": "play_bot_first"}
            ]
        ]
    }
    text = (
        f"🎮 *Game Started* (`{gid}` | {emoji} | `{rw_label}` | {mode_title})\n"
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

def parse_user_amount(text_val, user_id):
    try:
        val = float(text_val)
        curr = user_currency.get(user_id, 'INR')
        if curr == 'USDT':
            return val * EXCHANGE_RATE
        return val
    except:
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
    try:
        return requests.post(f"{TELEGRAM_API_URL}/sendDice", json=payload, timeout=5).json()
    except Exception as e:
        print(f"Error sending game: {e}")
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
_TOP_CARD_BG_B64 = "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EA5NtaxE2ZcTvKf4w4cpuuh0DwQVZMJpi6QZNsW3nBkll+lWvFPgjcYSFKixqLjGnVWcaPMlYsuYe31bV8lS3GICbZwKWiv4VoE6dcPvivMzjjvcVNanoZxBR9LUDR7UIUOBX31CHT3shu4RrHvcG3uN4G9bns8D/il0JhOPKe1xaCQZM5XHrVtRiGYsXutfYoshDtgXPxs2bW2il8bcPvit/neCAxa05Y9pv5ofisYawvg96xq9aOJrFtXxpT52FCisgQpSFLlr4z3XyBvyWVMWKMkcGNeCT703QZIuR4LU104++RKYZp+eZW6WgvwaGJNM2i+k4wbiqUo0Oo7TocrHlS9waDa978qm0XwP+K7+Zj6mH1yZ/wBSjJisbHFhkFwptpyRcNXPkTLuc2TjNlu4ntW9OLPBLaQaHh+dnaXiSmVuagQzEZJQ4Dob4tvvQdrIrRjEVCqOF61N0uqycaQqEpEMKPLx2lrmOBsQQsiLEBK28brqLoLHWE3x1wv53vSeOuJ+ce1W0vzSl9ip6Y/elmgrkZwk/O96BOu+ke1WzhOtG3blS0x+9GZCuYnXDc73pTPO+ke1WvbRtnenpj96My1XLx530j2pDOudy+9W4P60m3lvS0t+9GZarl467dtHtSGedf53vVt20odl1JaW/enmmq4+Out849qPHnEfOKt211o2yDkbpaW/ejNNVzbPOvm429ad48bfOKtW1kEu2c1LTH70sy1XUTzj98e1BnXH773q1CJl1pRFNk9MfvSzIVy8ecNzvek8edkdpW3a5ijb5kaY/enmWq5+POv873pHTzz98e1Wzb60baWlv3ozLVcfHSfvj2pPHHW+crft5JA66jpb96lmgrl484W85Hjzifne9W3aS360CsfvRmWq5ePOP33rzR4663zj2q3B3agm6lpj96WZarl464/fe9IZ11/ne9W7a60F2+yNMfvSzTVcvHnD773o8dcTfaParYH2KNqyNNfvTzLVc/HnfSPakM+4/f8AvVuD7epIH2ujTX70sy1XIzrvpe9IJ130iPardt2NyjbujTHntTzTVcxOu+ke1OE64DerYH25Uu2SpCsfvUcyFdBPOH357U/xtzh85WlryDdZk1ZNXuq6yekA4Ypc9Dphhy7pmLORYe2xgG4Edas05waS42AUMyOxYx8acD84p7Zpx++K34Pgh8Yv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VLrD/abyRog43c1LOGwz9B3v+KURsM/Qd71EhdKCU+sP9pvJLRBxu5qW8Nhn6DvejhsM/Qd71E8+tGafWH+03kjRRxu5qWiPhn6DvejhsNfQd71ErFKLp9Yf7beSWijjdzUt4bDP0He9HDYZ+g/3qJ3KXNPT/wDbbyS0UcbualfD4Z9G73peHw16N/vUTz60WKfWH+23kloo43c1LeHw16N3v+KOHw16N3vUTuUtyn1h/tt5JaKON3NSvh8Neid70vjGGvRO96ieaM+tPrD/AG28kaKON3NSzxjDfon+9L4xhr0bveonmluVLT/9tvJLRRxu5qV8Phv0bvejhsN+jd71Fbounp/+23kjRBxu5qViPhsfwTvel8Yw36J3v+KieaUEp6f/ALbeSWijjdzUr8Yw36J3v+KPGMN+id71FblF09P/ANtvJLRRxu5qV8Phv0TvejxjDnone9RS6LlMV/8Att5JaION3NSzxjDfone9HjGHPRO96ilynXKen/7beSWijjdzUq8Yw36J3vR4xhv0TveordF09P8A9tvJGijjdzUrEzhz0Tvel8Zw56J3vUTuRypdo86en/7beSNFHG7mpX4zhz0TvejxnDfoXe9RTaKUEqQr/wDbbyS0UcbualfjWGx/Au96XxrDnoXe9RS6LnnT0/8A228ktEHGealfjWHPQu96PGsOehd71FNo86No86NP/wBtvJLRRxu5qWCaw36F3vR41hz0LveontHnS7RUtO/228kaKON3NSzxrDnoXe9HjWHPQu96igcesJdo86en/wC23kloo4zzUq8aw56F3vR41hz0LveortHnRtFPT/8AbbyS0UcZ5qV+NYd9C73pfGsO+hd71FNooBJT07/bbyS0UcbualfjWHfQu96PGsO+hd71FblG0edPTvuN5I0UcbualfjWHfQO96XxrDvoXe9RTaPOjaPOnpx4G8ktEHGealfjeHfQO96PHMO+gd71FNopQ49alpx4G8kaIOI81K/G8Pegd70eNYd9A73qK7R50bR509OPA3kloo4jzUrE3h30DvejxvDvoHe9RTaKXaKenHgbyS0UcR5qV+N4e9A73o8bw90d3vUVDr86LlPTjwN5JaKOI81K/G8PdHd70eN4e6O73qK7R50bRT077jeSWijiPNSvxzD3R3e9HjmHuju96im0UoddPTjwN5I0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"
# ================= NEON CARD DESIGN (STATS + TOP 10) =================
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
    VALUE_X, MAX_W = 790, 370
    BLUE, BLUE_GLOW = (205, 238, 255), (40, 150, 255)
    GREEN, GREEN_GLOW = (60, 235, 140), (20, 170, 90)
    RED, RED_GLOW = (255, 95, 95), (200, 40, 40)
    GOLD, GOLD_GLOW = (255, 214, 70), (230, 150, 20)

    pnl_col, pnl_glow = (GREEN, GREEN_GLOW) if total_pnl >= 0 else (RED, RED_GLOW)
    rows = [
        (155, f"{total_games:,}", BLUE, BLUE_GLOW),
        (243, _card_money(total_dep, user_id), BLUE, BLUE_GLOW),
        (330, _card_money(total_wd, user_id), BLUE, BLUE_GLOW),
        (418, str(most_played).upper(), BLUE, BLUE_GLOW),
        (505, _card_money(total_pnl, user_id), pnl_col, pnl_glow),
        (590, _biggest_win_date(user_id, stats), BLUE, BLUE_GLOW),
        (677, _card_money(biggest_win, user_id), GOLD, GOLD_GLOW),
    ]
    for y, text, col, glow in rows:
        font = _fit_font(text, MAX_W, 54, weight=800)
        _glow_text(img, (VALUE_X, y), text, font, col, glow, anchor="lm", radius=7)

    bio = io.BytesIO()
    img.save(bio, "PNG")
    bio.seek(0)
    return bio


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
    row_ys = [232, 297, 360, 422, 485, 546, 607, 667, 724, 783]
    NAME_X, NAME_MAX_W = 378, 430
    WAGER_CX, WAGER_MAX_W = 995, 330
    WHITE, BLUE_GLOW = (240, 248, 255), (40, 150, 255)
    MEDAL = {0: ((255, 214, 70), (230, 150, 20)), 1: ((225, 235, 250), (150, 180, 230)), 2: ((255, 170, 110), (210, 110, 40))}

    for i, y in enumerate(row_ys):
        if i < len(top10):
            row = top10[i]
            name = str(row["label"])
            if len(name) > 22:
                name = name[:21] + "\u2026"
            wager = _card_money(row["wager_inr"], viewer_id)
            name_col, name_glow = MEDAL.get(i, (WHITE, BLUE_GLOW))
        else:
            name, wager = "\u2014", _card_money(0.0, viewer_id)
            name_col, name_glow = (WHITE, BLUE_GLOW)
        nf = _fit_font(name, NAME_MAX_W, 38, weight=650)
        _glow_text(img, (NAME_X, y), name, nf, name_col, name_glow, anchor="lm", radius=6)
        wf = _fit_font(wager, WAGER_MAX_W, 48, weight=800)
        _glow_text(img, (WAGER_CX, y), wager, wf, WHITE, BLUE_GLOW, anchor="mm", radius=7)

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

    if double_bet <= MAX_BET:
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

    if next_bet < MIN_BET or next_bet > MAX_BET:
        answer_callback(
            callback_query_id,
            f"Bet limit check failed! Allowed: {format_money(MIN_BET, user_id)} - {format_money(MAX_BET, user_id)}"
        )
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
        if refund and bet_inr > 0:
            user_balances[owner_id] = user_balances.get(owner_id, 0.0) + bet_inr
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
    order_id = "ORD" + str(int(time.time() * 1000))
    
    payload = {
        "zap_key": ZAPUPI_API_KEY,
        "order_id": order_id,
        "amount": str(amount),
        "remark": f"Deposit|{chat_id}",
        "webhook_url": "https://xyren-upi.onrender.com/zapupi-webhook"
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
    except Exception:
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
def fair_validate_bet(chat_id, user_id, bet_inr, example):
    if is_player_in_active_game(user_id):
        send_message(chat_id, f"⚠️ You already have an active game (*{get_active_game_summary(user_id)}*)! Finish it before starting a new game.")
        return False
    if bet_inr is None or bet_inr <= 0:
        send_message(chat_id, f"⚠️ Enter a valid bet amount. Example: `{example}`")
        return False
    if bet_inr < MIN_BET or bet_inr > MAX_BET:
        send_message(chat_id, f"⚠️ Bet out of limits! Min: {format_money(MIN_BET, user_id)} | Max: {format_money(MAX_BET, user_id)}")
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
    if not fair_validate_bet(chat_id, user_id, bet_inr, "/limbo 50 2"):
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

    chance = min(100.0, FAIR_RTP / target * 100)
    fair_reveal(seeds, user_id)
    text_out = (
        f"🚀 *Limbo* (`{gid}`)\n\n"
        f"🎯 Target: *{target:.2f}x* (win chance {chance:.2f}%)\n"
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

@app.route('/webhook', methods=['POST'])
def telegram_webhook():
    global HOUSE_BALANCE, MIN_BET, MAX_BET, EXCHANGE_RATE, MAINTENANCE_MODE, DEPOSIT_ENABLED, WITHDRAW_ENABLED, DM_GAMES_ENABLED, GROUP_LINK, MIN_DEPOSIT, MIN_WITHDRAW
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
                    except:
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
                    except:
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
                    except:
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
                    except:
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
                    except:
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
                    except:
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
                    except:
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
                    except:
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
                    amt_inr = parse_user_amount(text, user_id)
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
                        amt_inr = parse_user_amount(text, user_id)
                        if not amt_inr or amt_inr <= 0:
                            send_message(chat_id, "⚠️ Invalid amount. Please enter a valid number:")
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
                            send_message(chat_id, upi_err + "\n\nPlease enter a valid UPI ID:")
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
                        amt = float(parts[1])
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
                        send_message(chat_id, "⚠️ Enter a valid positive amount (e.g. `/deducthb 5000`).")
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

                if re.match(rf"^/minbet(?:@{re.escape(BOT_USERNAME.lstrip('@'))})?(?:\s|$)", text, re.IGNORECASE):
                    if user_id not in admin_list:
                        pass  # normal users get no reply to admin commands
                        return jsonify({'status': 'ok'}), 200
                    parts = text.split()
                    if len(parts) < 2:
                        send_message(chat_id, f"🎯 Current Min Bet: *{format_money(MIN_BET, user_id)}*\nUsage: `/minbet <amount>`")
                        return jsonify({'status': 'ok'}), 200
                    try:
                        val = float(parts[1])
                        if val <= 0 or val > MAX_BET:
                            raise ValueError()
                        MIN_BET = val
                        send_message(chat_id, f"✅ Min Bet updated to *{format_money(MIN_BET, user_id)}*.")
                    except ValueError:
                        send_message(chat_id, f"⚠️ Enter a valid amount `> 0` and `<= MAX_BET` (`{MAX_BET}`).")
                    return jsonify({'status': 'ok'}), 200

                if re.match(rf"^/maxbet(?:@{re.escape(BOT_USERNAME.lstrip('@'))})?(?:\s|$)", text, re.IGNORECASE):
                    if user_id not in admin_list:
                        pass  # normal users get no reply to admin commands
                        return jsonify({'status': 'ok'}), 200
                    parts = text.split()
                    if len(parts) < 2:
                        send_message(chat_id, f"🎯 Current Max Bet: *{format_money(MAX_BET, user_id)}*\nUsage: `/maxbet <amount>`")
                        return jsonify({'status': 'ok'}), 200
                    try:
                        val = float(parts[1])
                        if val <= 0 or val < MIN_BET:
                            raise ValueError()
                        MAX_BET = val
                        send_message(chat_id, f"✅ Max Bet updated to *{format_money(MAX_BET, user_id)}*.")
                    except ValueError:
                        send_message(chat_id, f"⚠️ Enter a valid amount `>= MIN_BET` (`{MIN_BET}`).")
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
                    parts = text.split()
                    if len(parts) < 2:
                        send_message(chat_id, "⚠️ Usage: `/cancel XC-XXXXXXX-XXXX`")
                        return jsonify({'status': 'ok'}), 200
                    gid = parts[1].strip().upper()
                    rec = game_id_registry.get(gid)
                    if not rec:
                        send_message(chat_id, f"⚠️ Game ID `{gid}` not found.")
                        return jsonify({'status': 'ok'}), 200
                    involved = {rec.get("owner_id"), rec.get("meta", {}).get("p1_id"), rec.get("meta", {}).get("p2_id")}
                    if user_id not in admin_list and user_id not in involved:
                        send_message(chat_id, "⛔ You can only cancel your own active games.")
                        return jsonify({'status': 'ok'}), 200
                    _, status_msg = cancel_game_by_id(gid)
                    send_message(chat_id, status_msg)
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

                if re.match(rf"^/start(?:@{re.escape(BOT_USERNAME.lstrip('@'))})?(?:\s|$)", text, re.IGNORECASE):
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
                        "- `/cancel <game_id>` - Cancel an active game\n"
                        "- `/search <id>` - Search Game (XC-), Deposit (DP-) or Withdraw (WD-) by ID\n\n"
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
                        "- `/dr 50 high` or `/dr 50 2,4,6`\n\n"
                        "🎲🎲 *7Up Game (`/7up`):*\n"
                        "- `/7up 50 up` (`high`), `/7up 50 down` (`low`), `/7up 50 odd`, `/7up 50 even`, `/7up 50 7`"
                    )
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
                    elif bet_inr < MIN_BET or bet_inr > MAX_BET:
                        send_message(chat_id, f"⚠️ Bet out of limits! Min: {format_money(MIN_BET, user_id)} | Max: {format_money(MAX_BET, user_id)}")
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
                    elif bet_inr < MIN_BET or bet_inr > MAX_BET:
                        send_message(chat_id, f"⚠️ Bet out of limits! Min: {format_money(MIN_BET, user_id)} | Max: {format_money(MAX_BET, user_id)}")
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
                        send_message(chat_id, f"💰 *Your Wallet Balance:* {bal_str}", reply_markup=bal_keyboard)
                    else:
                        bal_keyboard = {
                            "inline_keyboard": [
                                [
                                    {"text": "📥 Manage Balance in DM", "url": f"https://t.me/{BOT_USERNAME.replace('@','')}"}
                                ]
                            ]
                        }
                        send_message(chat_id, f"💰 *Your Wallet Balance:* {bal_str}\n\n_ℹ️ Deposit & Withdraw can only be done in Bot's DM!_", reply_markup=bal_keyboard)
                    
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

                    parts = text.split(' ')
                    current_bal = user_balances.get(user_id, 0.0)
                    if len(parts) == 3 and parts[1].replace('.', '', 1).isdigit():
                        bet_inr = parse_user_amount(parts[1], user_id)
                        arg = parts[2].lower()
                        
                        if bet_inr is None or bet_inr <= 0:
                            send_message(chat_id, "⚠️ Enter a valid bet amount.")
                            return jsonify({'status': 'ok'}), 200
                        elif bet_inr < MIN_BET or bet_inr > MAX_BET:
                            send_message(chat_id, f"⚠️ Bet out of limits! Min: {format_money(MIN_BET, user_id)} | Max: {format_money(MAX_BET, user_id)}")
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
                            except:
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
                        elif bet_inr < MIN_BET or bet_inr > MAX_BET:
                            send_message(chat_id, f"⚠️ Bet out of limits! Min: {format_money(MIN_BET, user_id)} | Max: {format_money(MAX_BET, user_id)}")
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
                                mode_title = "🔥 CRAZY MODE (Lowest Sum Wins)" if mode == "crazy" else "⚡ NORMAL MODE (Highest Sum Wins)"
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
            shared_buttons = ("pvp_acc_", "pvp_can_", "adm_", "admin_wd_", "admin_wdid_", "infopg_", "pm_again_", "pm_double_", "myhistpg_")
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
            
            if not callback_data.startswith(("mn_", "tw_", "pf_")) and not callback_data.startswith("adm_") and not callback_data.startswith("bj_") and not callback_data.startswith("gs_") and not callback_data.startswith("rw_") and not callback_data.startswith("mc_") and not callback_data.startswith("pvp_") and not callback_data.startswith("infopg_") and not callback_data.startswith("myhistpg_"):
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
                    if bet_inr < MIN_BET or bet_inr > MAX_BET:
                        pending_game_setup.pop(user_id, None)
                        edit_message(target_chat, target_msg, f"⚠️ Bet out of limits! Min: {format_money(MIN_BET, user_id)} | Max: {format_money(MAX_BET, user_id)}")
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
                mode_title = "🔥 CRAZY MODE (Lowest Sum Wins)" if chosen_mode == "crazy" else "⚡ NORMAL MODE (Highest Sum Wins)"
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

                if bet_inr < MIN_BET or bet_inr > MAX_BET:
                    pending_game_setup.pop(user_id, None)
                    edit_message(target_chat, target_msg, f"⚠️ Bet out of limits! Min: {format_money(MIN_BET, user_id)} | Max: {format_money(MAX_BET, user_id)}")
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
                if bet_inr < MIN_BET or bet_inr > MAX_BET:
                    edit_message(target_chat, target_msg, f"⚠️ Bet out of limits! Min: {format_money(MIN_BET, user_id)} | Max: {format_money(MAX_BET, user_id)}")
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
                if bet_inr < MIN_BET or bet_inr > MAX_BET:
                    edit_message(target_chat, target_msg, f"⚠️ Bet out of limits! Min: {format_money(MIN_BET, user_id)} | Max: {format_money(MAX_BET, user_id)}")
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
                mode_label = "CRAZY (Lowest Sum Wins)" if mode == "crazy" else "NORMAL (Highest Sum Wins)"
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

@app.route('/zapupi-webhook', methods=['POST'])
def zapupi_webhook():
    try:
        data = request.get_json()
        if not data: 
            return jsonify({'status': 'error', 'message': 'No data'}), 400
        
        order_id = data.get('order_id')
        status = data.get('status')
        amount = float(data.get('amount', 0))
        utr = data.get('utr', '')
        
        if status and status.lower() == 'success':
            remark = data.get('remark', '')
            chat_id = None
            
            if '|' in remark:
                parts = remark.split('|')
                for p in parts:
                    if p.isdigit():
                        chat_id = int(p)
                        break
            elif remark.isdigit():
                chat_id = int(remark)
                
            order_rec = deposit_orders.get(order_id) if order_id else None
            if order_rec and order_rec.get("status") == "credited":
                # Same payment reported again: don't add balance twice
                return jsonify({'status': 'ok'}), 200

            if chat_id:
                if chat_id not in user_balances: 
                    user_balances[chat_id] = 0.0
                    user_currency[chat_id] = 'INR'
                user_balances[chat_id] += amount
                
                if chat_id not in user_deposits: user_deposits[chat_id] = 0.0
                user_deposits[chat_id] += amount
                
                ts_dep = current_timestamp()
                dep_id = order_rec["id"] if order_rec else generate_txn_id("DP")
                if order_rec:
                    order_rec["status"] = "credited"
                    order_rec["credited_at"] = ts_dep
                    persist_deposit_order(order_rec)
                deposit_history.append({
                    'id': dep_id,
                    'user': chat_id,
                    'amount': amount,
                    'utr': utr,
                    'order_id': order_id or '',
                    'time': ts_dep
                })
                persist_deposit(chat_id, amount, utr, ts_dep, txn_id=dep_id, order_id=order_id)
                persist_user(chat_id)
                
                success_msg = f"✅ *Deposit Successful!* 🎉\n\n🆔 Deposit ID: `{dep_id}`\nAdded: {format_money(amount, chat_id)}\nNew Balance: {format_money(user_balances[chat_id], chat_id)}\nOrder ID: `{order_id}`\nUTR: `{utr}`"
                send_message(chat_id, success_msg)

                # Private alert to the owner only (not to other admins or any channel)
                owner_msg = (
                    "💰 *NEW DEPOSIT RECEIVED*\n\n"
                    f"🆔 Deposit ID: `{dep_id}`\n"
                    f"👤 User: {_user_label_for_report(chat_id)}\n"
                    f"💵 Amount: *{format_money(amount, chat_id)}*\n"
                    f"🏦 New Balance: *{format_money(user_balances[chat_id], chat_id)}*\n"
                    f"🧾 Order ID: `{order_id}`\n"
                    f"🔢 UTR: `{utr}`\n"
                    f"🕒 Time: `{ts_dep}`"
                )
                send_message(ADMIN_USER_ID, owner_msg)
                    
        return jsonify({'status': 'ok'}), 200
    except Exception as e:
        print(f"❌ ZapUPI Webhook Error: {e}")
        return jsonify({'status': 'error', 'message': str(e)}), 200


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
    }

# Taken before anything is loaded from the database = the code's default settings.
_DEFAULT_CONFIG = _snapshot_default_config()

def _clear_player_memory():
    for store in (
        user_balances, user_currency, user_usernames, user_first_names, username_to_id,
        user_stats, user_deposits, user_withdrawals, user_bet_logs,
        deposit_history, withdrawal_history, banned_users,
        active_games, active_7up_games, pending_game_setup, open_pvp_challenges,
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
    global WITHDRAW_ENABLED, DM_GAMES_ENABLED, GROUP_LINK, MIN_DEPOSIT, MIN_WITHDRAW
    d = _DEFAULT_CONFIG
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
init_fair_db()
load_fair_from_db()

if __name__ == '__main__':
    app.run(host='0.0.0.0', port=5000)
