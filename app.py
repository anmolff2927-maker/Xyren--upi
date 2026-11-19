import os
import time
import random
import io
import re
import uuid
import requests
from flask import Flask, request, jsonify
from PIL import Image, ImageDraw, ImageFont

app = Flask(__name__)

TELEGRAM_BOT_TOKEN = os.environ.get("TELEGRAM_BOT_TOKEN")
ZAPUPI_API_KEY = os.environ.get("ZAPUPI_API_KEY")
BOT_USERNAME = "@Xyren_upibot"

TELEGRAM_API_URL = f"https://api.telegram.org/bot{TELEGRAM_BOT_TOKEN}"

ADMIN_USER_ID = 1822336097
admin_list = {ADMIN_USER_ID}

approved_groups = set()

user_balances = {}
user_currency = {}
user_stats = {}
user_deposits = {}
user_withdrawals = {}
deposit_history = []
withdrawal_history = []
banned_users = set()

active_games = {}
pending_game_setup = {}
open_pvp_challenges = {}
active_pvp_games = {}
active_bj_games = {}
deposit_states = {}
withdrawal_states = {}
admin_states = {}

HOUSE_BALANCE = 100000.0
MIN_BET = 10.0
MAX_BET = 1000.0
EXCHANGE_RATE = 98.0
MAINTENANCE_MODE = False
DEPOSIT_ENABLED = True
WITHDRAW_ENABLED = True

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

def match_confirm_keyboard():
    return {
        "inline_keyboard": [
            [
                {"text": "🤖 Against Bot", "callback_data": "mc_bot"},
                {"text": "👥 Against Player", "callback_data": "mc_player"},
            ],
            [
                {"text": "❌ Cancel", "callback_data": "gs_cancel"},
            ],
        ]
    }

def build_match_confirmation_text(user_id, emoji, bet_inr, mode, rw_label):
    mode_label = "CRAZY (Lowest Sum Wins)" if mode == "crazy" else "NORMAL (Highest Sum Wins)"
    g_name = GAME_NAME_MAP.get(emoji, "Game")
    return (
        "📋 *Match Confirmation*\n\n"
        f"🎮 *Game:* {g_name} ({emoji})\n"
        f"⚙️ *Mode:* *{mode_label}*\n"
        f"🏆 *RW Format:* `{rw_label}`\n"
        f"💰 *Bet Amount:* *{format_money(bet_inr, user_id)}*\n\n"
        "Choose how you want to play:"
    )

def start_versus_match(chat_id, message_id, user_id, emoji, bet_inr, mode, rw_label):
    rolls_per_round, target_wins = VALID_RW_MODES[rw_label]
    user_balances[user_id] -= bet_inr
    active_games[user_id] = {
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
        "step": "selecting_turn"
    }
    mode_title = "🔥 CRAZY MODE (Lowest Sum Wins)" if mode == "crazy" else "⚡ NORMAL MODE (Highest Sum Wins)"
    keyboard = {
        "inline_keyboard": [
            [
                {"text": "🤖 Bot Roll First", "callback_data": "play_bot_first"},
                {"text": "👤 You Roll First", "callback_data": "play_user_first"}
            ]
        ]
    }
    text = (
        f"🎮 *Game Started* ({emoji} | `{rw_label}` | {mode_title})\n"
        f"🎯 First to *{target_wins}* round win(s) | *{rolls_per_round}* roll(s)/round\n"
        f"💰 Bet: {format_money(bet_inr, user_id)}\n\nChoose who rolls first:"
    )
    if message_id:
        edit_message(chat_id, message_id, text, reply_markup=keyboard)
    else:
        send_message(chat_id, text, reply_markup=keyboard)

def resolve_pvp_round_and_match(chat_id, match_id, pvm):
    global HOUSE_BALANCE
    emoji = pvm["emoji"]
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

    if s1 == s2:
        r_status = "🤝 *Round Tied!* No point awarded."
    elif mode == "crazy":
        if s1 < s2:
            pvm["p1_wins"] += 1
            r_status = f"✨ *Player 1 (`{p1}`)* takes this round! (Lower sum wins)"
        else:
            pvm["p2_wins"] += 1
            r_status = f"✨ *Player 2 (`{p2}`)* takes this round! (Lower sum wins)"
    else:
        if s1 > s2:
            pvm["p1_wins"] += 1
            r_status = f"✨ *Player 1 (`{p1}`)* takes this round! (Higher sum wins)"
        else:
            pvm["p2_wins"] += 1
            r_status = f"✨ *Player 2 (`{p2}`)* takes this round! (Higher sum wins)"

    if pvm["p1_wins"] >= target_wins or pvm["p2_wins"] >= target_wins:
        winner_id = p1 if pvm["p1_wins"] >= target_wins else p2
        loser_id = p2 if winner_id == p1 else p1

        total_pot = bet * 2
        payout = total_pot * 0.97
        house_fee = total_pot - payout
        HOUSE_BALANCE += house_fee

        user_balances[winner_id] += payout
        update_user_stats(winner_id, emoji, bet, payout - bet, True)
        update_user_stats(loser_id, emoji, bet, -bet, False)

        final_text = (
            f"🏁 *Final Round {round_num}* ({emoji} | `{rw_label}` | {mode_tag})\n"
            f"👤 P1 (`{p1}`): `{expr1}` = *{s1}*\n"
            f"👤 P2 (`{p2}`): `{expr2}` = *{s2}*\n\n"
            f"🌟 *Match Won by `{winner_id}`!* 🌟\n"
            f"🎁 *Payout:* *{format_money(payout, winner_id)}*"
        )
        send_message(chat_id, final_text)

        active_pvp_games.pop(match_id, None)
        if active_games.get(p1) == match_id:
            active_games.pop(p1, None)
        if active_games.get(p2) == match_id:
            active_games.pop(p2, None)
        return

    msg = (
        f"⚔️ *Round {round_num}* ({emoji} | `{rw_label}` | {mode_tag})\n"
        f"👤 P1 (`{p1}`): `{expr1}` = *{s1}*\n"
        f"👤 P2 (`{p2}`): `{expr2}` = *{s2}*\n"
        f"{r_status}\n"
        f"🏆 Score — P1: *{pvm['p1_wins']}* | P2: *{pvm['p2_wins']}* (First to *{target_wins}*)"
    )
    send_message(chat_id, msg)

    pvm["round_num"] += 1
    pvm["p1_rolls"] = []
    pvm["p2_rolls"] = []
    pvm["turn"] = p1
    send_message(
        chat_id,
        f"➡️ *Round {pvm['round_num']}* — Player 1 (`{p1}`), send `{emoji}` x{pvm['rolls_per_round']} in chat!"
    )

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

def send_message(chat_id, text, reply_markup=None):
    url = f"{TELEGRAM_API_URL}/sendMessage"
    payload = {"chat_id": chat_id, "text": text, "parse_mode": "Markdown"}
    if reply_markup:
        payload["reply_markup"] = reply_markup
    try:
        res = requests.post(url, json=payload, timeout=5)
        return res.json()
    except Exception as e:
        print(f"Error sending message: {e}")
        return None

def edit_message(chat_id, message_id, text, reply_markup=None):
    url = f"{TELEGRAM_API_URL}/editMessageText"
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
    try:
        res = requests.post(url, json=payload, timeout=5)
        return res.json()
    except Exception as e:
        print(f"Error editing message: {e}")
        return None

def answer_callback(callback_query_id, text=""):
    url = f"{TELEGRAM_API_URL}/answerCallbackQuery"
    payload = {"callback_query_id": callback_query_id, "text": text}
    try:
        requests.post(url, json=payload, timeout=3)
    except Exception as e:
        print(f"Error answering callback: {e}")

def remove_inline_keyboard(chat_id, message_id):
    url = f"{TELEGRAM_API_URL}/editMessageReplyMarkup"
    payload = {
        "chat_id": chat_id,
        "message_id": message_id,
        "reply_markup": {"inline_keyboard": []}
    }
    try:
        requests.post(url, json=payload, timeout=3)
    except Exception as e:
        print(f"Error removing keyboard: {e}")

def send_photo(chat_id, photo_bio, caption=""):
    url = f"{TELEGRAM_API_URL}/sendPhoto"
    files = {'photo': ('game.png', photo_bio, 'image/png')}
    data = {'chat_id': chat_id, 'caption': caption, 'parse_mode': 'Markdown'}
    try:
        requests.post(url, files=files, data=data, timeout=10)
    except Exception as e:
        print(f"Error sending photo: {e}")

def generate_stats_image(user_id):
    stats = user_stats.get(user_id, {"games": 0, "wins": 0, "losses": 0, "total_pnl": 0.0, "biggest_win": 0.0, "game_counts": {}})
    total_games = stats["games"]
    wins = stats["wins"]
    losses = stats["losses"]
    win_rate = (wins / total_games * 100) if total_games > 0 else 0.0
    total_pnl = stats["total_pnl"]
    biggest_win = stats["biggest_win"]
    total_dep = user_deposits.get(user_id, 0.0)
    total_wd = user_withdrawals.get(user_id, 0.0)
    
    game_counts = stats.get("game_counts", {})
    most_played = max(game_counts, key=game_counts.get) if game_counts else "None"

    img = Image.new('RGB', (600, 480), color=(15, 15, 25))
    d = ImageDraw.Draw(img)
    
    d.rectangle([0, 0, 600, 75], fill=(30, 30, 50))
    d.text((25, 25), f"📊 {BOT_USERNAME} - PLAYER STATS", fill=(255, 215, 0))
    
    y = 100
    items = [
        ("Total Games Played:", f"{total_games}"),
        ("Total Deposits:", format_money(total_dep, user_id)),
        ("Total Withdrawals:", format_money(total_wd, user_id)),
        ("Most Played Game:", f"{str(most_played).upper()}"),
        ("Total PnL:", format_money(total_pnl, user_id)),
        ("Win Rate:", f"{win_rate:.1f}% ({wins}W / {losses}L)"),
        ("Biggest Lifetime Win:", format_money(biggest_win, user_id))
    ]
    
    for label, val in items:
        d.text((30, y), label, fill=(180, 180, 200))
        d.text((340, y), val, fill=(0, 255, 127) if "PnL" not in label or total_pnl >= 0 else (255, 69, 0))
        y += 42
        
    bio = io.BytesIO()
    img.save(bio, 'PNG')
    bio.seek(0)
    return bio

def update_user_stats(user_id, game_name, bet_inr, profit_inr, is_win):
    if user_id not in user_stats:
        user_stats[user_id] = {"games": 0, "wins": 0, "losses": 0, "total_pnl": 0.0, "biggest_win": 0.0, "game_counts": {}}
    
    st = user_stats[user_id]
    st["games"] += 1
    st["total_pnl"] += profit_inr
    
    if game_name not in st["game_counts"]:
        st["game_counts"][game_name] = 0
    st["game_counts"][game_name] += 1
    
    if is_win:
        st["wins"] += 1
        if profit_inr > st["biggest_win"]:
            st["biggest_win"] = profit_inr
    else:
        st["losses"] += 1

def finish_bj_game(chat_id, message_id, user_id, bj, outcome):
    global HOUSE_BALANCE
    p_cards = bj["player_cards"]
    d_cards = bj["dealer_cards"]
    p_tot = calculate_hand_total(p_cards)
    d_tot = calculate_hand_total(d_cards)
    bet = bj["bet"]

    header = (
        f"🃏 *Blackjack Result*\n\n"
        f"👤 Your Hand: {format_cards(p_cards)} (*{p_tot}*)\n"
        f"🤖 Dealer Hand: {format_cards(d_cards)} (*{d_tot}*)\n"
        f"💰 Total Bet: {format_money(bet, user_id)}\n\n"
    )

    if outcome == "push":
        user_balances[user_id] += bet
        update_user_stats(user_id, "blackjack", bet, 0.0, False)
        body = f"🤝 *Push (Tie)!* Bet refunded.\n💰 Balance: {format_money(user_balances[user_id], user_id)}"
    elif outcome == "win":
        win_amt = bet * 1.94
        profit_inr = win_amt - bet
        user_balances[user_id] += win_amt
        HOUSE_BALANCE -= profit_inr
        update_user_stats(user_id, "blackjack", bet, profit_inr, True)
        body = f"🎉 *You WON {format_money(win_amt, user_id)}* (`1.94x`)! 🥳\n💰 Balance: {format_money(user_balances[user_id], user_id)}"
    else:
        profit_inr = -bet
        HOUSE_BALANCE += bet
        update_user_stats(user_id, "blackjack", bet, profit_inr, False)
        reason_txt = "Bust! Over 21." if outcome == "bust" else "Dealer wins."
        body = f"😢 *You Lost!* {reason_txt}\n💰 Balance: {format_money(user_balances[user_id], user_id)}"

    edit_message(chat_id, message_id, header + body, reply_markup=None)
    if user_id in active_bj_games:
        del active_bj_games[user_id]

def play_dealer_and_settle(chat_id, message_id, user_id, bj):
    p_tot = calculate_hand_total(bj["player_cards"])
    while calculate_hand_total(bj["dealer_cards"]) < 17:
        bj["dealer_cards"].append(draw_card())
    d_tot = calculate_hand_total(bj["dealer_cards"])

    if d_tot > 21 or p_tot > d_tot:
        finish_bj_game(chat_id, message_id, user_id, bj, "win")
    elif p_tot < d_tot:
        finish_bj_game(chat_id, message_id, user_id, bj, "lose")
    else:
        finish_bj_game(chat_id, message_id, user_id, bj, "push")

def send_animated_game(chat_id, emoji):
    url = f"{TELEGRAM_API_URL}/sendDice"
    payload = {"chat_id": chat_id, "emoji": emoji}
    try:
        res = requests.post(url, json=payload, timeout=5)
        return res.json()
    except Exception as e:
        print(f"Error sending game: {e}")
        return None

def roll_bot_series(chat_id, emoji, rolls_count):
    vals = []
    for _ in range(rolls_count):
        res = send_animated_game(chat_id, emoji)
        v = res['result']['dice']['value'] if res and 'result' in res else random.randint(1, 6)
        vals.append(v)
        if rolls_count > 1:
            time.sleep(0.6)
    return vals

def create_zapupi_order(amount, chat_id):
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
            msg = (
                f"🔗 *Deposit Order Created!*\n\n"
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

def resolve_round_and_match(chat_id, user_id, game):
    global HOUSE_BALANCE
    emoji = game["emoji"]
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
    
    if u_sum == b_sum:
        r_status = "🤝 *Round Tied!* No point awarded."
    elif mode == "crazy":
        if u_sum < b_sum:
            game["user_wins"] += 1
            r_status = "✨ *You took this round!* (Lower sum wins)"
        else:
            game["bot_wins"] += 1
            r_status = "🤖 *Bot took this round!* (Lower sum wins)"
    else:
        if u_sum > b_sum:
            game["user_wins"] += 1
            r_status = "✨ *You took this round!* (Higher sum wins)"
        else:
            game["bot_wins"] += 1
            r_status = "🤖 *Bot took this round!* (Higher sum wins)"

    if game["user_wins"] >= target_wins or game["bot_wins"] >= target_wins:
        user_won_match = game["user_wins"] >= target_wins
        if user_won_match:
            win_amt = bet * 1.94
            profit_inr = win_amt - bet
            user_balances[user_id] += win_amt
            HOUSE_BALANCE -= profit_inr
            update_user_stats(user_id, emoji, bet, profit_inr, True)
            final_text = (
                f"🏁 *Final Round {round_num}* (`{rw_label}` | {mode_tag})\n"
                f"👤 You: `{u_expr}` = *{u_sum}*\n"
                f"🤖 Bot: `{b_expr}` = *{b_sum}*\n\n"
                f"🎉 *Congratulations! You won the match!* ✨\n"
                f"🎁 *Winnings:* *{format_money(win_amt, user_id)}* (`1.94x`)"
            )
        else:
            profit_inr = -bet
            HOUSE_BALANCE += bet
            update_user_stats(user_id, emoji, bet, profit_inr, False)
            final_text = (
                f"🏁 *Final Round {round_num}* (`{rw_label}` | {mode_tag})\n"
                f"👤 You: `{u_expr}` = *{u_sum}*\n"
                f"🤖 Bot: `{b_expr}` = *{b_sum}*\n\n"
                f"💫 *Well played, but the bot got the better of you this time!* Better luck next round."
            )

        send_message(chat_id, final_text)
        if user_id in active_games:
            del active_games[user_id]
        return

    msg = (
        f"⚔️ *Round {round_num}* (`{rw_label}` | {mode_tag})\n"
        f"👤 You: `{u_expr}` = *{u_sum}*\n"
        f"🤖 Bot: `{b_expr}` = *{b_sum}*\n"
        f"{r_status}\n"
        f"🏆 Score — You: *{game['user_wins']}* | Bot: *{game['bot_wins']}* (First to *{target_wins}*)"
    )
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
        send_message(chat_id, f"🤖 Bot Roll: `{b_next_expr}` (*{sum(b_next)}*)\n\n👉 *Now your turn! Send `{emoji}` x{rolls_per_round} in chat.*")
    else:
        game["step"] = "waiting_user_first"
        send_message(chat_id, f"👤 *Round {game['round_num']}* — Your turn! Send `{emoji}` x{rolls_per_round} in chat.")

@app.route('/')
def index():
    return f"{BOT_USERNAME} Casino Bot is Live!", 200

@app.route('/webhook', methods=['POST'])
def telegram_webhook():
    global HOUSE_BALANCE, MIN_BET, MAX_BET, EXCHANGE_RATE, MAINTENANCE_MODE, DEPOSIT_ENABLED, WITHDRAW_ENABLED
    try:
        data = request.get_json()
        if not data:
            return jsonify({'status': 'error'}), 400
            
        if 'message' in data:
            message = data['message']
            chat_id = message['chat'].get('id')
            chat_type = message['chat'].get('type')
            user_id = message['from'].get('id')
            
            if chat_type in ['group', 'supergroup'] and chat_id not in approved_groups and user_id not in admin_list:
                if 'text' in message and message['text'].startswith('/myid'):
                    send_message(chat_id, f"📌 This Group Chat ID is: `{chat_id}`")
                return jsonify({'status': 'ok'}), 200

            if user_id in banned_users:
                send_message(chat_id, "⛔ Your account has been banned from using this bot.")
                return jsonify({'status': 'ok'}), 200
                
            if MAINTENANCE_MODE and user_id not in admin_list:
                send_message(chat_id, "🛠 *Bot is under Maintenance.* Please try again later.")
                return jsonify({'status': 'ok'}), 200
                
            if user_id not in user_balances:
                user_balances[user_id] = 0.0
                user_currency[user_id] = 'INR'
                
            if user_id in admin_list and user_id in admin_states and 'text' in message:
                state = admin_states[user_id]
                text = message['text'].strip()
                action = state['action']
                
                if action == 'add_bal':
                    try:
                        parts = text.split(' ')
                        t_user = int(parts[0])
                        amt = parse_user_amount(parts[1], t_user)
                        if t_user not in user_balances: user_balances[t_user] = 0.0
                        user_balances[t_user] += amt
                        send_message(chat_id, f"✅ Added {format_money(amt, t_user)} to user `{t_user}`.")
                        send_message(t_user, f"💰 *Admin credited your account!* +{format_money(amt, t_user)}")
                    except:
                        send_message(chat_id, "⚠️ Invalid format. Use: `<user_id> <amount>`")
                    del admin_states[user_id]
                    return jsonify({'status': 'ok'}), 200
                    
                elif action == 'deduct_bal':
                    try:
                        parts = text.split(' ')
                        t_user = int(parts[0])
                        amt = parse_user_amount(parts[1], t_user)
                        if t_user in user_balances:
                            user_balances[t_user] = max(0.0, user_balances[t_user] - amt)
                            send_message(chat_id, f"✅ Deducted {format_money(amt, t_user)} from user `{t_user}`.")
                            send_message(t_user, f"⚠️ *Admin deducted from your account.* -{format_money(amt, t_user)}")
                    except:
                        send_message(chat_id, "⚠️ Invalid format. Use: `<user_id> <amount>`")
                    del admin_states[user_id]
                    return jsonify({'status': 'ok'}), 200
                    
                elif action == 'user_stats':
                    try:
                        target_u = int(text)
                        bio = generate_stats_image(target_u)
                        send_photo(chat_id, bio, caption=f"📊 Stats for User `{target_u}`")
                    except:
                        send_message(chat_id, "⚠️ Invalid User ID.")
                    del admin_states[user_id]
                    return jsonify({'status': 'ok'}), 200
                    
                elif action == 'ban_user':
                    try:
                        target_u = int(text)
                        banned_users.add(target_u)
                        send_message(chat_id, f"🚫 User `{target_u}` has been BANNED.")
                    except:
                        send_message(chat_id, "⚠️ Invalid User ID.")
                    del admin_states[user_id]
                    return jsonify({'status': 'ok'}), 200
                    
                elif action == 'unban_user':
                    try:
                        target_u = int(text)
                        if target_u in banned_users: banned_users.remove(target_u)
                        send_message(chat_id, f"✅ User `{target_u}` has been UNBANNED.")
                    except:
                        send_message(chat_id, "⚠️ Invalid User ID.")
                    del admin_states[user_id]
                    return jsonify({'status': 'ok'}), 200
                    
                elif action == 'grant_admin':
                    try:
                        target_u = int(text)
                        admin_list.add(target_u)
                        send_message(chat_id, f"👑 User `{target_u}` granted Admin rights.")
                    except:
                        send_message(chat_id, "⚠️ Invalid User ID.")
                    del admin_states[user_id]
                    return jsonify({'status': 'ok'}), 200
                    
                elif action == 'revoke_admin':
                    try:
                        target_u = int(text)
                        if target_u != ADMIN_USER_ID and target_u in admin_list:
                            admin_list.remove(target_u)
                            send_message(chat_id, f"⛔ Admin rights revoked for `{target_u}`.")
                    except:
                        send_message(chat_id, "⚠️ Invalid User ID.")
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
                        target_u = int(parts[0])
                        msg = parts[1]
                        send_message(target_u, f"📢 *Admin Message*\n\n{msg}")
                        send_message(chat_id, f"✅ Private message sent to `{target_u}`.")
                    except:
                        send_message(chat_id, "⚠️ Format error. Use: `<user_id> <message>`")
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
                        send_message(chat_id, "⏳ Generating deposit link...")
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
                        if user_balances[user_id] < amt_inr:
                            send_message(chat_id, f"❌ Insufficient balance! Your balance is {format_money(user_balances[user_id], user_id)}.")
                            del withdrawal_states[user_id]
                            return jsonify({'status': 'ok'}), 200
                            
                        state['amount'] = amt_inr
                        state['step'] = 'waiting_upi'
                        send_message(chat_id, "🏦 *Please enter your UPI ID / Destination Address for payout:*")
                        return jsonify({'status': 'ok'}), 200
                        
                    elif state['step'] == 'waiting_upi':
                        state['upi_id'] = text
                        withdrawal_states[user_id]['step'] = 'confirming'
                        
                        amt_str = format_money(state['amount'], user_id)
                        summary = (
                            "📋 *Withdrawal Summary*\n\n"
                            f"💰 Amount: *{amt_str}*\n"
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
                target_user = withdrawal_states[user_id]['target_user']
                amt_str = withdrawal_states[user_id]['amount_str']
                
                user_balances[target_user] += withdrawal_states[user_id]['raw_amount']
                
                send_message(target_user, f"❌ *Withdrawal Request Rejected*\n\nAmount: {amt_str}\nReason: *{reason}*\n\nYour funds have been refunded to your wallet.")
                send_message(chat_id, f"✅ Rejection sent to user `{target_user}` with reason: _{reason}_")
                del withdrawal_states[user_id]
                return jsonify({'status': 'ok'}), 200

            if 'dice' in message and user_id in active_games:
                active_ref = active_games[user_id]
                user_dice = message['dice']

                if isinstance(active_ref, str) and active_ref in active_pvp_games:
                    pvm = active_pvp_games[active_ref]
                    if pvm["chat_id"] != chat_id or pvm["turn"] != user_id:
                        return jsonify({'status': 'ok'}), 200
                    if user_dice.get('emoji') != pvm["emoji"]:
                        return jsonify({'status': 'ok'}), 200

                    val = user_dice.get('value', 1)
                    needed = pvm["rolls_per_round"]
                    is_p1 = (user_id == pvm["p1_id"])
                    roll_list = pvm["p1_rolls"] if is_p1 else pvm["p2_rolls"]
                    roll_list.append(val)

                    rem = needed - len(roll_list)
                    if rem > 0:
                        send_message(chat_id, f"🎲 Player `{user_id}` Roll `{len(roll_list)}/{needed}`: *{val}* — Send `{rem}` more `{pvm['emoji']}`!")
                        return jsonify({'status': 'ok'}), 200

                    if is_p1:
                        expr = "+".join(map(str, roll_list))
                        send_message(chat_id, f"👤 P1 (`{pvm['p1_id']}`) Rolls: `{expr}` (*{sum(roll_list)}*)\n\n👉 *Player 2 (`{pvm['p2_id']}`), your turn! Send `{pvm['emoji']}` x{needed}.*")
                        pvm["turn"] = pvm["p2_id"]
                    else:
                        resolve_pvp_round_and_match(chat_id, active_ref, pvm)
                    return jsonify({'status': 'ok'}), 200

                game = active_ref
                expected_emoji = game['emoji']
                
                if user_dice.get('emoji') == expected_emoji and game['step'] in ['waiting_user_first', 'waiting_user_second']:
                    user_val = user_dice.get('value', 1)
                    rolls_needed = game['rolls_per_round']
                    game['current_user_rolls'].append(user_val)
                    
                    remaining = rolls_needed - len(game['current_user_rolls'])
                    if remaining > 0:
                        send_message(chat_id, f"🎲 Roll `{len(game['current_user_rolls'])}/{rolls_needed}`: *{user_val}* — Send `{remaining}` more `{expected_emoji}`!")
                        return jsonify({'status': 'ok'}), 200
                        
                    step = game['step']
                    if step == 'waiting_user_first':
                        u_expr = "+".join(map(str, game['current_user_rolls']))
                        send_message(chat_id, f"👤 Your Rolls ({expected_emoji}): `{u_expr}` (*{sum(game['current_user_rolls'])}*)\n\n🤖 Now bot is throwing...")
                        time.sleep(0.8)
                        
                        b_vals = roll_bot_series(chat_id, expected_emoji, rolls_needed)
                        game['current_bot_rolls'] = b_vals
                        
                        resolve_round_and_match(chat_id, user_id, game)
                        return jsonify({'status': 'ok'}), 200
                        
                    elif step == 'waiting_user_second':
                        resolve_round_and_match(chat_id, user_id, game)
                        return jsonify({'status': 'ok'}), 200

            if 'text' in message:
                text = message['text'].strip()
                
                if text.startswith('/approve '):
                    if user_id in admin_list:
                        parts = text.split(' ')
                        if len(parts) > 1 and parts[1].strip('-').isdigit():
                            target_chat_id = int(parts[1])
                            approved_groups.add(target_chat_id)
                            send_message(chat_id, f"✅ Group `{target_chat_id}` has been successfully *APPROVED*!")
                        else:
                            send_message(chat_id, "⚠️ Invalid format. Use: `/approve <chat_id>`")
                    else:
                        send_message(chat_id, "⛔ Unauthorized.")
                    return jsonify({'status': 'ok'}), 200

                if text == '/start':
                    help_text = (
                        f"🎰 *Welcome to {BOT_USERNAME} Casino!* 🎲\n\n"
                        "Commands:\n"
                        "- `/balance` or `/bal` - Check wallet balance\n"
                        "- `/hb` - Check House Balance\n"
                        "- `/currency` - Change currency (INR / USDT)\n"
                        "- `/stats` - View your visual stats card\n"
                        "- `/deposit` - Add money via ZapUPI (DM Only)\n"
                        "- `/withdraw` - Withdraw your winnings (DM Only)\n\n"
                        "🃏 *Blackjack:* `/bj 50` (Hit / Stand / Double buttons)\n\n"
                        "🎮 *Versus Games (`/dice`, `/dart`, `/foot`, `/basket`, `/bowl`)*\n"
                        "• Pick *Crazy* or *Normal* → `1r1w`–`3r3w` → *Against Bot* or *Against Player*\n"
                        "• Example: `/dice 50`\n\n"
                        "🔮 *Prediction Game (`/dr`):*\n"
                        "- `/dr 50 high` or `/dr 50 2,4,6`"
                    )
                    send_message(chat_id, help_text)

                elif re.match(rf"^/hb(?:@{re.escape(BOT_USERNAME.lstrip('@'))})?$", text, re.IGNORECASE):
                    send_message(chat_id, f"🏦 *House Balance:* *{format_money(HOUSE_BALANCE, user_id)}*")

                elif re.match(rf"^/bj(?:@{re.escape(BOT_USERNAME.lstrip('@'))})?(?:\s|$)", text, re.IGNORECASE):
                    if user_id in active_bj_games:
                        send_message(chat_id, "⚠️ You already have an active Blackjack hand! Use the buttons on your current game message.")
                        return jsonify({'status': 'ok'}), 200

                    parts = text.split()
                    bet_inr = parse_user_amount(parts[1], user_id) if len(parts) > 1 else parse_user_amount("10", user_id)

                    if bet_inr is None or bet_inr <= 0:
                        send_message(chat_id, "⚠️ Enter a valid bet amount. Example: `/bj 50`")
                    elif bet_inr < MIN_BET or bet_inr > MAX_BET:
                        send_message(chat_id, f"⚠️ Bet out of limits! Min: {format_money(MIN_BET, user_id)} | Max: {format_money(MAX_BET, user_id)}")
                    elif user_balances[user_id] < bet_inr:
                        send_message(chat_id, f"❌ Insufficient balance! Please open Bot DM to deposit: https://t.me/{BOT_USERNAME.replace('@','')}")
                    else:
                        user_balances[user_id] -= bet_inr
                        p_cards = [draw_card(), draw_card()]
                        d_cards = [draw_card(), draw_card()]
                        p_tot = calculate_hand_total(p_cards)

                        can_double = user_balances[user_id] >= bet_inr
                        table_msg = (
                            f"🃏 *Blackjack Started!*\n\n"
                            f"👤 Your Hand: {format_cards(p_cards)} (*{p_tot}*)\n"
                            f"🤖 Dealer Shows: `{d_cards[0]}` `[?]`\n"
                            f"💰 Bet: {format_money(bet_inr, user_id)}\n\n"
                            f"Choose your move:"
                        )
                        sent = send_message(chat_id, table_msg, reply_markup=bj_action_keyboard(can_double=can_double))
                        msg_id = sent.get("result", {}).get("message_id") if sent and sent.get("ok") else None

                        active_bj_games[user_id] = {
                            "chat_id": chat_id,
                            "message_id": msg_id,
                            "bet": bet_inr,
                            "player_cards": p_cards,
                            "dealer_cards": d_cards,
                            "doubled": False
                        }
                    return jsonify({'status': 'ok'}), 200
                    
                elif text in ['/balance', '/bal']:
                    if user_id in deposit_states: del deposit_states[user_id]
                    if user_id in withdrawal_states: del withdrawal_states[user_id]
                    
                    bal_str = format_money(user_balances[user_id], user_id)
                    
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
                    send_message(chat_id, f"🌐 *Select Your Preferred Currency:*\nCurrent: *{user_currency.get(user_id, 'INR')}*", reply_markup=keyboard)
                    
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
                        send_message(chat_id, "⏳ Generating deposit link...")
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
                    send_message(chat_id, "💸 *Withdrawal Flow*\n\nPlease enter the amount you want to withdraw:")
                    
                elif text in ['/panel', '/admin']:
                    if user_id in admin_list:
                        panel_text = (
                            "👑 *Owner & Admin Control Dashboard*\n\n"
                            f"🛠 *Maintenance:* {'🟢 OFF' if not MAINTENANCE_MODE else '🔴 ON'}\n"
                            f"💳 *Deposits:* {'🟢 Enabled' if DEPOSIT_ENABLED else '🔴 Disabled'}\n"
                            f"💸 *Withdrawals:* {'🟢 Enabled' if WITHDRAW_ENABLED else '🔴 Disabled'}\n"
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
                        send_message(chat_id, "⛔ Unauthorized.")
                        
                elif text.startswith('/dr '):
                    parts = text.split(' ')
                    if len(parts) == 3 and parts[1].replace('.', '', 1).isdigit():
                        bet_inr = parse_user_amount(parts[1], user_id)
                        arg = parts[2].lower()
                        
                        if bet_inr < MIN_BET or bet_inr > MAX_BET:
                            send_message(chat_id, f"⚠️ Bet out of limits! Min: {format_money(MIN_BET, user_id)} | Max: {format_money(MAX_BET, user_id)}")
                            return jsonify({'status': 'ok'}), 200
                        elif user_balances[user_id] < bet_inr:
                            send_message(chat_id, f"❌ Insufficient balance! Please open Bot DM to deposit: https://t.me/{BOT_USERNAME.replace('@','')}")
                            return jsonify({'status': 'ok'}), 200
                            
                        is_win = False
                        multiplier = 0.0
                        win_desc = ""
                        
                        if arg in ['high', 'low', 'odd', 'even']:
                            user_balances[user_id] -= bet_inr
                            send_message(chat_id, f"🎲 Rolling dice for Prediction (*{arg.upper()}* | Bet: {format_money(bet_inr, user_id)})...")
                            
                            res = send_animated_game(chat_id, '🎲')
                            dice_val = res['result']['dice']['value'] if res and 'result' in res else random.randint(1, 6)
                            time.sleep(1)
                            
                            if arg == 'high' and dice_val in [4, 5, 6]: is_win = True
                            elif arg == 'low' and dice_val in [1, 2, 3]: is_win = True
                            elif arg == 'odd' and dice_val in [1, 3, 5]: is_win = True
                            elif arg == 'even' and dice_val in [2, 4, 6]: is_win = True
                            
                            multiplier = 1.92
                            win_desc = f"Prediction: {arg.upper()}"
                        else:
                            try:
                                nums = [int(n.strip()) for n in arg.split(',')]
                                if not all(1 <= n <= 6 for n in nums) or len(nums) > 5 or len(nums) != len(set(nums)):
                                    raise ValueError()
                                    
                                user_balances[user_id] -= bet_inr
                                send_message(chat_id, f"🎲 Rolling dice for Numbers (*{nums}* | Bet: {format_money(bet_inr, user_id)})...")
                                
                                res = send_animated_game(chat_id, '🎲')
                                dice_val = res['result']['dice']['value'] if res and 'result' in res else random.randint(1, 6)
                                time.sleep(1)
                                
                                if dice_val in nums: is_win = True
                                
                                count = len(nums)
                                mult_map = {1: 5.56, 2: 2.88, 3: 1.92, 4: 1.44, 5: 1.15}
                                multiplier = mult_map.get(count, 1.0)
                                win_desc = f"Numbers: {nums}"
                            except:
                                send_message(chat_id, "⚠️ Invalid format! Use `high`, `low`, `odd`, `even` or numbers like `2,4,6`.\nExample: `/dr 50 2,4,6`")
                                return jsonify({'status': 'ok'}), 200
                                
                        result_text = f"📊 *Dice Prediction Result*\n\n🎲 Rolled Number: *{dice_val}*\n🎯 {win_desc}\n\n"
                        if is_win:
                            win_amt = bet_inr * multiplier
                            profit_inr = win_amt - bet_inr
                            user_balances[user_id] += win_amt
                            HOUSE_BALANCE -= profit_inr
                            update_user_stats(user_id, "prediction", bet_inr, profit_inr, True)
                            result_text += f"🎉 *Congratulations! You WON {format_money(win_amt, user_id)}* (`{multiplier}x`)! 🥳\n💰 Balance: {format_money(user_balances[user_id], user_id)}"
                        else:
                            profit_inr = -bet_inr
                            HOUSE_BALANCE += bet_inr
                            update_user_stats(user_id, "prediction", bet_inr, profit_inr, False)
                            result_text += f"😢 *You Lost!* Better luck next time.\n💰 Balance: {format_money(user_balances[user_id], user_id)}"
                            
                        send_message(chat_id, result_text)
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
                        tokens = text.split()[1:]
                        bet_inr = parse_user_amount("10", user_id)
                        mode = None
                        rw_label = None
                        invalid_rw = False
                        
                        for tok in tokens:
                            low_tok = tok.lower()
                            if low_tok == "crazy":
                                mode = "crazy"
                            elif low_tok == "normal":
                                mode = "normal"
                            elif re.fullmatch(r"\d+r\d+w", low_tok):
                                if low_tok in VALID_RW_MODES:
                                    rw_label = low_tok
                                else:
                                    invalid_rw = True
                            else:
                                parsed = parse_user_amount(tok, user_id)
                                if parsed is not None:
                                    bet_inr = parsed
                                    
                        if invalid_rw:
                            send_message(chat_id, "⚠️ Invalid RW mode! Allowed modes: `1r1w`, `2r1w`, `3r1w`, `1r2w`, `2r2w`, `3r2w`, `1r3w`, `2r3w`, `3r3w`.")
                        elif bet_inr is None or bet_inr <= 0:
                            send_message(chat_id, "⚠️ Enter a valid bet amount.")
                        elif bet_inr < MIN_BET or bet_inr > MAX_BET:
                            send_message(chat_id, f"⚠️ Bet out of limits! Min: {format_money(MIN_BET, user_id)} | Max: {format_money(MAX_BET, user_id)}")
                        elif user_balances[user_id] < bet_inr:
                            send_message(chat_id, f"❌ Insufficient balance! Please open Bot DM to deposit: https://t.me/{BOT_USERNAME.replace('@','')}")
                        else:
                            g_name = GAME_NAME_MAP.get(triggered_game, "Game")
                            if mode is None:
                                setup_msg = (
                                    f"🎮 *{g_name} ({triggered_game}) Setup*\n"
                                    f"💰 Bet: *{format_money(bet_inr, user_id)}*\n\n"
                                    "Select Mode:"
                                )
                                sent = send_message(chat_id, setup_msg, reply_markup=game_style_keyboard())
                                msg_id = sent.get("result", {}).get("message_id") if sent and sent.get("ok") else None
                                pending_game_setup[user_id] = {
                                    "chat_id": chat_id,
                                    "message_id": msg_id,
                                    "emoji": triggered_game,
                                    "bet": bet_inr,
                                    "mode": None,
                                    "rw_label": rw_label
                                }
                            elif rw_label is None:
                                mode_title = "🔥 CRAZY MODE (Lowest Sum Wins)" if mode == "crazy" else "⚡ NORMAL MODE (Highest Sum Wins)"
                                rw_msg = (
                                    f"🎯 *Select RW Mode* ({g_name} {triggered_game} | {mode_title})\n"
                                    f"💰 Bet: *{format_money(bet_inr, user_id)}*\n\nTap a mode below:"
                                )
                                sent = send_message(chat_id, rw_msg, reply_markup=rw_mode_keyboard())
                                msg_id = sent.get("result", {}).get("message_id") if sent and sent.get("ok") else None
                                pending_game_setup[user_id] = {
                                    "chat_id": chat_id,
                                    "message_id": msg_id,
                                    "emoji": triggered_game,
                                    "bet": bet_inr,
                                    "mode": mode,
                                    "rw_label": None
                                }
                            else:
                                conf_msg = build_match_confirmation_text(user_id, triggered_game, bet_inr, mode, rw_label)
                                sent = send_message(chat_id, conf_msg, reply_markup=match_confirm_keyboard())
                                msg_id = sent.get("result", {}).get("message_id") if sent and sent.get("ok") else None
                                pending_game_setup[user_id] = {
                                    "chat_id": chat_id,
                                    "message_id": msg_id,
                                    "emoji": triggered_game,
                                    "bet": bet_inr,
                                    "mode": mode,
                                    "rw_label": rw_label
                                }

        elif 'callback_query' in data:
            query = data['callback_query']
            callback_query_id = query['id']
            callback_data = query['data']
            chat_id = query['message']['chat']['id']
            chat_type = query['message']['chat']['type']
            message_id = query['message']['message_id']
            user_id = query['from']['id']
            
            answer_callback(callback_query_id)
            
            if not callback_data.startswith("adm_") and not callback_data.startswith("bj_") and not callback_data.startswith("gs_") and not callback_data.startswith("rw_") and not callback_data.startswith("mc_") and not callback_data.startswith("pvp_"):
                remove_inline_keyboard(chat_id, message_id)
            
            if user_id not in user_balances:
                user_balances[user_id] = 0.0
                user_currency[user_id] = 'INR'

            if callback_data == "gs_cancel":
                setup = pending_game_setup.pop(user_id, None)
                target_chat = (setup or {}).get("chat_id") or chat_id
                target_msg = (setup or {}).get("message_id") or message_id
                for cid, ch in list(open_pvp_challenges.items()):
                    if ch["host_id"] == user_id:
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
                setup["message_id"] = target_msg

                g_name = GAME_NAME_MAP.get(setup["emoji"], "Game")
                mode_title = "🔥 CRAZY MODE (Lowest Sum Wins)" if chosen_mode == "crazy" else "⚡ NORMAL MODE (Highest Sum Wins)"
                rw_msg = (
                    f"🎯 *Select RW Mode* ({g_name} {setup['emoji']} | {mode_title})\n"
                    f"💰 Bet: *{format_money(setup['bet'], user_id)}*\n\nTap a mode below:"
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
                setup["message_id"] = target_msg
                bet_inr = setup["bet"]
                mode = setup["mode"] or "normal"
                setup["mode"] = mode
                setup["rw_label"] = chosen_rw
                emoji = setup["emoji"]

                if bet_inr < MIN_BET or bet_inr > MAX_BET:
                    pending_game_setup.pop(user_id, None)
                    edit_message(target_chat, target_msg, f"⚠️ Bet out of limits! Min: {format_money(MIN_BET, user_id)} | Max: {format_money(MAX_BET, user_id)}")
                elif user_balances[user_id] < bet_inr:
                    pending_game_setup.pop(user_id, None)
                    edit_message(target_chat, target_msg, f"❌ Insufficient balance! Please open Bot DM to deposit: https://t.me/{BOT_USERNAME.replace('@','')}")
                else:
                    conf_msg = build_match_confirmation_text(user_id, emoji, bet_inr, mode, chosen_rw)
                    edit_message(target_chat, target_msg, conf_msg, reply_markup=match_confirm_keyboard())
                return jsonify({'status': 'ok'}), 200

            if callback_data == "mc_bot":
                if user_id not in pending_game_setup:
                    edit_message(chat_id, message_id, "⚠️ Confirmation expired. Start a new game command.")
                    return jsonify({'status': 'ok'}), 200
                conf = pending_game_setup.pop(user_id)
                target_chat = conf.get("chat_id") or chat_id
                target_msg = conf.get("message_id") or message_id
                bet_inr = conf["bet"]
                if bet_inr < MIN_BET or bet_inr > MAX_BET:
                    edit_message(target_chat, target_msg, f"⚠️ Bet out of limits! Min: {format_money(MIN_BET, user_id)} | Max: {format_money(MAX_BET, user_id)}")
                elif user_balances[user_id] < bet_inr:
                    edit_message(target_chat, target_msg, f"❌ Insufficient balance! Please open Bot DM to deposit: https://t.me/{BOT_USERNAME.replace('@','')}")
                else:
                    start_versus_match(target_chat, target_msg, user_id, conf["emoji"], bet_inr, conf["mode"] or "normal", conf["rw_label"])
                return jsonify({'status': 'ok'}), 200

            if callback_data == "mc_player":
                if user_id not in pending_game_setup:
                    edit_message(chat_id, message_id, "⚠️ Confirmation expired. Start a new game command.")
                    return jsonify({'status': 'ok'}), 200
                conf = pending_game_setup.pop(user_id)
                target_chat = conf.get("chat_id") or chat_id
                target_msg = conf.get("message_id") or message_id
                bet_inr = conf["bet"]
                if bet_inr < MIN_BET or bet_inr > MAX_BET:
                    edit_message(target_chat, target_msg, f"⚠️ Bet out of limits! Min: {format_money(MIN_BET, user_id)} | Max: {format_money(MAX_BET, user_id)}")
                    return jsonify({'status': 'ok'}), 200
                if user_balances[user_id] < bet_inr:
                    edit_message(target_chat, target_msg, f"❌ Insufficient balance! Please open Bot DM to deposit: https://t.me/{BOT_USERNAME.replace('@','')}")
                    return jsonify({'status': 'ok'}), 200

                challenge_id = uuid.uuid4().hex[:8]
                mode = conf["mode"] or "normal"
                rw_label = conf["rw_label"] or "1r1w"
                rolls_per_round, target_wins = VALID_RW_MODES[rw_label]
                mode_label = "CRAZY (Lowest Sum Wins)" if mode == "crazy" else "NORMAL (Highest Sum Wins)"
                g_name = GAME_NAME_MAP.get(conf["emoji"], "Game")

                open_pvp_challenges[challenge_id] = {
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
                    f"👤 *Challenger:* `{user_id}`\n"
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
                if user_id != ch["host_id"] and user_id not in admin_list:
                    answer_callback(callback_query_id, "Only challenger can cancel!")
                    return jsonify({'status': 'ok'}), 200
                open_pvp_challenges.pop(cid, None)
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

                bet_inr = ch["bet"]
                target_chat = ch.get("chat_id") or chat_id
                target_msg = ch.get("message_id") or message_id

                if user_balances.get(host_id, 0.0) < bet_inr:
                    open_pvp_challenges.pop(cid, None)
                    edit_message(target_chat, target_msg, "❌ Challenger has insufficient balance. Challenge cancelled.")
                    return jsonify({'status': 'ok'}), 200

                if user_balances.get(user_id, 0.0) < bet_inr:
                    answer_callback(callback_query_id, "Insufficient balance to accept!")
                    return jsonify({'status': 'ok'}), 200

                open_pvp_challenges.pop(cid, None)
                user_balances[host_id] -= bet_inr
                user_balances[user_id] -= bet_inr

                match_id = f"pvp_{cid}"
                active_pvp_games[match_id] = {
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
                    f"🎮 *PvP Match Started!* ({ch['emoji']} | `{ch['rw_label']}`)\n"
                    f"👤 P1: `{host_id}` vs P2: `{user_id}` | Bet: *{format_money(bet_inr, user_id)}*\n"
                    f"🎯 First to *{ch['target_wins']}* round win(s) | *{ch['rolls_per_round']}* roll(s)/round\n\n"
                    f"👉 *Round 1 — Player 1 (`{host_id}`), send `{ch['emoji']}` x{ch['rolls_per_round']} in chat!*"
                )
                edit_message(target_chat, target_msg, start_text)
                return jsonify({'status': 'ok'}), 200

            if callback_data.startswith("bj_"):
                if user_id not in active_bj_games:
                    edit_message(chat_id, message_id, "⚠️ Blackjack session expired. Start a new game with `/bj <amount>`.")
                    return jsonify({'status': 'ok'}), 200

                bj = active_bj_games[user_id]
                target_chat = bj.get("chat_id") or chat_id
                target_msg = bj.get("message_id") or message_id

                if callback_data == "bj_hit":
                    bj["player_cards"].append(draw_card())
                    p_tot = calculate_hand_total(bj["player_cards"])
                    if p_tot > 21:
                        finish_bj_game(target_chat, target_msg, user_id, bj, "bust")
                    elif p_tot == 21:
                        play_dealer_and_settle(target_chat, target_msg, user_id, bj)
                    else:
                        msg = (
                            f"🃏 *Blackjack (Hit)*\n\n"
                            f"👤 Your Hand: {format_cards(bj['player_cards'])} (*{p_tot}*)\n"
                            f"🤖 Dealer Shows: `{bj['dealer_cards'][0]}` `[?]`\n"
                            f"💰 Bet: {format_money(bj['bet'], user_id)}\n\n"
                            f"Choose your next move:"
                        )
                        edit_message(target_chat, target_msg, msg, reply_markup=bj_action_keyboard(can_double=False))

                elif callback_data == "bj_stand":
                    play_dealer_and_settle(target_chat, target_msg, user_id, bj)

                elif callback_data == "bj_double":
                    extra_bet = bj["bet"]
                    if user_balances[user_id] < extra_bet:
                        p_tot = calculate_hand_total(bj["player_cards"])
                        msg = (
                            f"🃏 *Blackjack*\n\n"
                            f"👤 Your Hand: {format_cards(bj['player_cards'])} (*{p_tot}*)\n"
                            f"🤖 Dealer Shows: `{bj['dealer_cards'][0]}` `[?]`\n"
                            f"💰 Bet: {format_money(bj['bet'], user_id)}\n\n"
                            f"❌ Insufficient balance to Double! Choose Hit or Stand:"
                        )
                        edit_message(target_chat, target_msg, msg, reply_markup=bj_action_keyboard(can_double=False))
                        return jsonify({'status': 'ok'}), 200

                    user_balances[user_id] -= extra_bet
                    bj["bet"] += extra_bet
                    bj["doubled"] = True
                    bj["player_cards"].append(draw_card())
                    p_tot = calculate_hand_total(bj["player_cards"])

                    if p_tot > 21:
                        finish_bj_game(target_chat, target_msg, user_id, bj, "bust")
                    else:
                        play_dealer_and_settle(target_chat, target_msg, user_id, bj)

                return jsonify({'status': 'ok'}), 200
                
            if callback_data == "curr_inr":
                user_currency[user_id] = 'INR'
                send_message(chat_id, "✅ Currency successfully set to *INR (₹)*!")
            elif callback_data == "curr_usdt":
                user_currency[user_id] = 'USDT'
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
                send_message(chat_id, "💸 *Withdrawal Flow*\n\nPlease enter the amount you want to withdraw:")
                
            elif callback_data.startswith("adm_"):
                if user_id not in admin_list:
                    send_message(chat_id, "⛔ Unauthorized.")
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
                        txt += f"- User `{d['user']}`: {format_money(d['amount'], d['user'])} (UTR: `{d['utr']}`)\n"
                    if not deposit_history: txt += "No deposits recorded yet."
                    send_message(chat_id, txt)
                elif callback_data == "adm_last_wd":
                    txt = "📤 *Last 50 Withdrawals:*\n"
                    for w in withdrawal_history[-50:]:
                        txt += f"- User `{w['user']}`: {format_money(w['amount'], w['user'])} to `{w['upi']}`\n"
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
                if user_id in withdrawal_states:
                    user_balances[user_id] += withdrawal_states[user_id].get('amount', 0)
                    del withdrawal_states[user_id]
                send_message(chat_id, "❌ Withdrawal request cancelled. Funds refunded.")
                
            elif callback_data == "wd_confirm":
                if user_id in withdrawal_states:
                    st = withdrawal_states[user_id]
                    raw_amt = st['amount']
                    if user_balances[user_id] < raw_amt:
                        send_message(chat_id, "❌ Insufficient balance.")
                        del withdrawal_states[user_id]
                        return jsonify({'status': 'ok'}), 200
                        
                    user_balances[user_id] -= raw_amt
                    if user_id not in user_withdrawals: user_withdrawals[user_id] = 0.0
                    user_withdrawals[user_id] += raw_amt
                    
                    withdrawal_history.append({'user': user_id, 'amount': raw_amt, 'upi': st['upi_id']})
                    
                    amt_str = format_money(raw_amt, user_id)
                    upi_id = st['upi_id']
                    
                    send_message(chat_id, "📤 *Withdrawal Request Submitted!*\n\nYour request has been sent to the admin for verification. You will be notified once processed.")
                    
                    admin_msg = (
                        "🚨 *NEW WITHDRAWAL REQUEST*\n\n"
                        f"👤 User ID: `{user_id}`\n"
                        f"💰 Amount: *{amt_str}*\n"
                        f"🏦 UPI ID: `{upi_id}`"
                    )
                    admin_keyboard = {
                        "inline_keyboard": [
                            [
                                {"text": "✅ Paid", "callback_data": f"admin_wd_paid_{user_id}_{raw_amt}"},
                                {"text": "❌ Reject", "callback_data": f"admin_wd_reject_{user_id}_{raw_amt}"}
                            ]
                        ]
                    }
                    send_message(ADMIN_USER_ID, admin_msg, reply_markup=admin_keyboard)
                    del withdrawal_states[user_id]
                
            elif callback_data.startswith("admin_wd_paid_") or callback_data.startswith("admin_wd_reject_"):
                if user_id in admin_list:
                    parts = callback_data.split('_')
                    action = parts[2]
                    target_user = int(parts[3])
                    raw_amt = float(parts[4])
                    amt_str = format_money(raw_amt, target_user)
                    
                    if action == "paid":
                        success_msg = (
                            "🎉 *Withdrawal Approved & Paid!* ✨\n\n"
                            f"Dear User, your withdrawal of *{amt_str}* has been successfully processed and transferred to your account/UPI ID. 🚀\n\n"
                            f"Thank you for playing with *{BOT_USERNAME}*! 🎰"
                        )
                        send_message(target_user, success_msg)
                        send_message(chat_id, f"✅ Successfully marked withdrawal for user `{target_user}` as Paid.")
                    elif action == "reject":
                        withdrawal_states[user_id] = {
                            'step': 'waiting_reject_reason',
                            'target_user': target_user,
                            'raw_amount': raw_amt,
                            'amount_str': amt_str
                        }
                        send_message(chat_id, f"✍️ *Please enter the rejection reason for user `{target_user}` in chat:*")
                else:
                    send_message(chat_id, "⛔ Unauthorized.")
                
            elif callback_data in ["play_user_first", "play_bot_first"]:
                remove_inline_keyboard(chat_id, message_id)
                if user_id not in active_games or isinstance(active_games[user_id], str):
                    send_message(chat_id, "⚠️ Session expired. Start a new game.")
                    return jsonify({'status': 'ok'}), 200
                    
                game = active_games[user_id]
                emoji = game["emoji"]
                rolls_needed = game["rolls_per_round"]
                game["current_user_rolls"] = []
                game["current_bot_rolls"] = []
                
                if callback_data == "play_user_first":
                    game["first_turn"] = "user"
                    game["step"] = "waiting_user_first"
                    send_message(chat_id, f"👤 You chose to roll first!\n\n👉 *Please send `{emoji}` x{rolls_needed} in chat now for Round {game['round_num']}!*")
                else:
                    game["first_turn"] = "bot"
                    game["step"] = "waiting_user_second"
                    send_message(chat_id, f"🤖 Bot is throwing `{emoji}` x{rolls_needed} first...")
                    
                    b_vals = roll_bot_series(chat_id, emoji, rolls_needed)
                    game["current_bot_rolls"] = b_vals
                    b_expr = "+".join(map(str, b_vals))
                    
                    send_message(chat_id, f"🤖 Bot Rolls: `{b_expr}` (*{sum(b_vals)}*)\n\n👉 *Now your turn! Please send `{emoji}` x{rolls_needed} in chat.*")
                
        return jsonify({'status': 'ok'}), 200
    except Exception as e:
        print(f"❌ Webhook Error: {e}")
        return jsonify({'status': 'error', 'message': str(e)}), 200

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
                
            if chat_id:
                if chat_id not in user_balances: 
                    user_balances[chat_id] = 0.0
                    user_currency[chat_id] = 'INR'
                user_balances[chat_id] += amount
                
                if chat_id not in user_deposits: user_deposits[chat_id] = 0.0
                user_deposits[chat_id] += amount
                
                deposit_history.append({'user': chat_id, 'amount': amount, 'utr': utr})
                
                success_msg = f"✅ *Deposit Successful!* 🎉\n\nAdded: {format_money(amount, chat_id)}\nNew Balance: {format_money(user_balances[chat_id], chat_id)}\nOrder ID: `{order_id}`\nUTR: `{utr}`"
                send_message(chat_id, success_msg)
                    
        return jsonify({'status': 'ok'}), 200
    except Exception as e:
        print(f"❌ ZapUPI Webhook Error: {e}")
        return jsonify({'status': 'error', 'message': str(e)}), 200

if __name__ == '__main__':
    app.run(host='0.0.0.0', port=5000)
