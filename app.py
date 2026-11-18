import os
import time
import random
import io
import requests
from flask import Flask, request, jsonify
from PIL import Image, ImageDraw, ImageFont

app = Flask(__name__)

TELEGRAM_BOT_TOKEN = os.environ.get("TELEGRAM_BOT_TOKEN")
ZAPUPI_API_KEY = os.environ.get("ZAPUPI_API_KEY")

TELEGRAM_API_URL = f"https://api.telegram.org/bot{TELEGRAM_BOT_TOKEN}"

# Tera Admin User ID
ADMIN_USER_ID = 1822336097

# Storage & Casino Settings
user_balances = {}
user_currency = {}
user_stats = {}
user_deposits = {}
user_withdrawals = {}
active_games = {}
deposit_states = {}

HOUSE_BALANCE = 100000.0
MIN_BET = 10.0
MAX_BET = 1000.0
EXCHANGE_RATE = 98.0

# Admin Win-Rate Rigging Controls (Bot Win Percentage)
RIG_CONTROL = {
    "bj": 50.0,
    "tower": 50.0,
    "mines": 50.0,
    "limbo": 50.0
}

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
    payload = {
        "chat_id": chat_id,
        "text": text,
        "parse_mode": "Markdown"
    }
    if reply_markup:
        payload["reply_markup"] = reply_markup
    try:
        res = requests.post(url, json=payload, timeout=10)
        return res.json()
    except Exception as e:
        print(f"Error sending message: {e}")
        return None

def send_photo(chat_id, photo_bio, caption=""):
    url = f"{TELEGRAM_API_URL}/sendPhoto"
    files = {'photo': ('game.png', photo_bio, 'image/png')}
    data = {'chat_id': chat_id, 'caption': caption, 'parse_mode': 'Markdown'}
    try:
        requests.post(url, files=files, data=data, timeout=15)
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
    d.text((25, 25), "📊 XYREN CASINO - PLAYER STATS", fill=(255, 215, 0))
    
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

def generate_game_card_image(title, details_list, bg_color=(20, 20, 35)):
    img = Image.new('RGB', (500, 320), color=bg_color)
    d = ImageDraw.Draw(img)
    
    d.rectangle([0, 0, 500, 60], fill=(40, 40, 70))
    d.text((20, 20), title, fill=(255, 215, 0))
    
    y = 85
    for label, val in details_list:
        d.text((25, y), label, fill=(180, 180, 200))
        d.text((280, y), val, fill=(255, 255, 255))
        y += 35
        
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

def send_animated_game(chat_id, emoji):
    url = f"{TELEGRAM_API_URL}/sendDice"
    payload = {"chat_id": chat_id, "emoji": emoji}
    try:
        res = requests.post(url, json=payload, timeout=10)
        return res.json()
    except Exception as e:
        print(f"Error sending game: {e}")
        return None

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
        response = requests.post(url, json=payload, headers=headers, timeout=15)
        data = response.json()
        if data.get("status") == "success":
            return f"🔗 *Deposit Link Generated!*\n\nAmount: ₹{amount}\nOrder ID: `{order_id}`\n\n[Click here to Pay & Add Money]({data.get('payment_url')})"
        else:
            return f"❌ Failed: {data.get('message', 'Unknown error')}"
    except Exception as e:
        return "⚠️ Failed to connect to payment gateway."

@app.route('/')
def index():
    return "Xyren Pro Casino Bot is Live!", 200

@app.route('/webhook', methods=['POST'])
def telegram_webhook():
    global HOUSE_BALANCE, MIN_BET, MAX_BET, EXCHANGE_RATE
    try:
        data = request.get_json()
        if not data:
            return jsonify({'status': 'error'}), 400
            
        if 'message' in data:
            message = data['message']
            chat_id = message['chat'].get('id')
            user_id = message['from'].get('id')
            
            if user_id not in user_balances:
                user_balances[user_id] = 0.0
                user_currency[user_id] = 'INR'
                
            # Handle interactive deposit amount input
            if user_id in deposit_states and 'text' in message:
                text = message['text'].strip()
                del deposit_states[user_id]
                amt_inr = parse_user_amount(text, user_id)
                if amt_inr and amt_inr > 0:
                    send_message(chat_id, "⏳ Generating deposit link...")
                    res_text = create_zapupi_order(amt_inr, user_id)
                    send_message(chat_id, res_text)
                else:
                    send_message(chat_id, "⚠️ Invalid amount. Use `/deposit <amount>` or `/deposit` again.")
                return jsonify({'status': 'ok'}), 200

            if 'dice' in message and user_id in active_games:
                game = active_games[user_id]
                expected_emoji = game['emoji']
                user_dice = message['dice']
                
                if user_dice.get('emoji') == expected_emoji:
                    user_val = user_dice.get('value', 1)
                    bet = game['bet']
                    step = game['step']
                    mode = game['mode']
                    
                    if step == 'waiting_user_first':
                        game['user_val'] = user_val
                        send_message(chat_id, f"👤 Your Roll ({expected_emoji}): *{user_val}*\n\n🤖 Now bot is throwing...")
                        time.sleep(1)
                        
                        res_b = send_animated_game(chat_id, expected_emoji)
                        bot_val = res_b['result']['dice']['value'] if res_b and 'result' in res_b else random.randint(1, 6)
                        
                        finish_game(chat_id, user_id, user_val, bot_val, bet, expected_emoji, mode)
                        return jsonify({'status': 'ok'}), 200
                        
                    elif step == 'waiting_user_second':
                        bot_val = game['bot_val']
                        finish_game(chat_id, user_id, user_val, bot_val, bet, expected_emoji, mode)
                        return jsonify({'status': 'ok'}), 200

            if 'text' in message:
                text = message['text'].strip()
                
                if text == '/start':
                    help_text = (
                        "🎰 *Welcome to Xyren Pro Casino!* 🎲\n\n"
                        "Commands:\n"
                        "- `/balance` - Check wallet balance\n"
                        "- `/currency` - Change currency (INR / USDT)\n"
                        "- `/stats` - View your visual stats card\n"
                        "- `/deposit <amount>` - Add money via ZapUPI\n\n"
                        "🎮 *Versus Games (`/dice`, `/dart`, `/foot`, `/basket`, `/bowl`)*\n"
                        "_🔥 Add `crazy` for Lowest Win mode! (e.g. `/dice 50 crazy`)_\n\n"
                        "🃏 *New Mini Games (Image Format):*\n"
                        "- `/bj <amount>` - Blackjack 21\n"
                        "- `/limbo <amount> <multiplier>` - Limbo Game\n"
                        "- `/tower <amount>` - Tower Climb\n"
                        "- `/mines <amount>` - Minesweeper\n\n"
                        "🔮 *Prediction Game (`/dr`):*\n"
                        "- `/dr 50 high` or `/dr 50 2,4,6`"
                    )
                    send_message(chat_id, help_text)
                    
                elif text == '/balance':
                    bal_str = format_money(user_balances[user_id], user_id)
                    send_message(chat_id, f"💰 *Your Wallet Balance:* {bal_str}\n\nUse `/deposit <amount>` to add funds.")
                    
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
                    deposit_states[user_id] = True
                    send_message(chat_id, "💳 *Please enter the amount you want to deposit (e.g. 200):*")
                    
                elif text.startswith('/deposit '):
                    parts = text.split(' ')
                    if len(parts) > 1 and parts[1].replace('.', '', 1).isdigit():
                        amt_inr = parse_user_amount(parts[1], user_id)
                        send_message(chat_id, "⏳ Generating deposit link...")
                        res_text = create_zapupi_order(amt_inr, user_id)
                        send_message(chat_id, res_text)
                    else:
                        send_message(chat_id, "⚠️ Use format: `/deposit 100`")
                        
                # --- RIGGING / WIN-RATE ADMIN COMMANDS ---
                elif text.startswith('/setbj '):
                    if user_id == ADMIN_USER_ID:
                        val = float(text.split(' ')[1])
                        RIG_CONTROL["bj"] = val
                        send_message(chat_id, f"✅ Blackjack Bot Win Chance set to {val}%")
                    else:
                        send_message(chat_id, "⛔ Unauthorized.")
                elif text.startswith('/settower '):
                    if user_id == ADMIN_USER_ID:
                        val = float(text.split(' ')[1])
                        RIG_CONTROL["tower"] = val
                        send_message(chat_id, f"✅ Tower Bot Win Chance set to {val}%")
                    else:
                        send_message(chat_id, "⛔ Unauthorized.")
                elif text.startswith('/setmines '):
                    if user_id == ADMIN_USER_ID:
                        val = float(text.split(' ')[1])
                        RIG_CONTROL["mines"] = val
                        send_message(chat_id, f"✅ Mines Bot Win Chance set to {val}%")
                    else:
                        send_message(chat_id, "⛔ Unauthorized.")
                elif text.startswith('/setlimbo '):
                    if user_id == ADMIN_USER_ID:
                        val = float(text.split(' ')[1])
                        RIG_CONTROL["limbo"] = val
                        send_message(chat_id, f"✅ Limbo Bot Win Chance set to {val}%")
                    else:
                        send_message(chat_id, "⛔ Unauthorized.")

                # --- NEW GAMES: BLACKJACK, LIMBO, TOWER, MINES ---
                elif text.startswith('/bj '):
                    parts = text.split(' ')
                    bet_inr = parse_user_amount(parts[1], user_id) if len(parts) > 1 else parse_user_amount("10", user_id)
                    if not bet_inr or bet_inr < MIN_BET or bet_inr > MAX_BET:
                        send_message(chat_id, f"⚠️ Invalid bet! Min: {format_money(MIN_BET, user_id)} | Max: {format_money(MAX_BET, user_id)}")
                    elif user_balances[user_id] < bet_inr:
                        send_message(chat_id, "❌ Insufficient balance! Use `/deposit` to add money.")
                    else:
                        user_balances[user_id] -= bet_inr
                        # Blackjack rigged outcome using RIG_CONTROL["bj"]
                        bot_win_chance = RIG_CONTROL["bj"]
                        is_win = random.random() * 100 >= bot_win_chance
                        
                        p_score = random.randint(18, 21) if is_win else random.randint(12, 17)
                        d_score = random.randint(12, 17) if is_win else random.randint(18, 21)
                        if p_score == d_score: p_score += 1
                        
                        res_text = f"🃏 *Blackjack 21 Table*\n\n👤 Your Hand: *{p_score}*\n🤖 Dealer Hand: *{d_score}*\n\n"
                        if p_score > 21 or (d_score <= 21 and d_score >= p_score):
                            is_win = False
                        else:
                            is_win = True
                            
                        profit_inr = 0.0
                        if is_win:
                            win_amt = bet_inr * 2.0
                            profit_inr = win_amt - bet_inr
                            user_balances[user_id] += win_amt
                            HOUSE_BALANCE -= profit_inr
                            update_user_stats(user_id, "blackjack", bet_inr, profit_inr, True)
                            res_text += f"🎉 *You WON {format_money(win_amt, user_id)}*! 🥳"
                        else:
                            profit_inr = -bet_inr
                            HOUSE_BALANCE += bet_inr
                            update_user_stats(user_id, "blackjack", bet_inr, profit_inr, False)
                            res_text += f"😢 *Dealer wins!* You lost."
                            
                        bio = generate_game_card_image("BLACKJACK 21 TABLE", [("Your Cards:", f"Score {p_score}"), ("Dealer Cards:", f"Score {d_score}"), ("Result:", "WIN" if is_win else "LOSS")])
                        send_photo(chat_id, bio, caption=res_text)

                elif text.startswith('/limbo '):
                    parts = text.split(' ')
                    if len(parts) >= 3:
                        bet_inr = parse_user_amount(parts[1], user_id)
                        try:
                            target_mult = float(parts[2])
                        except:
                            target_mult = 2.0
                            
                        if not bet_inr or bet_inr < MIN_BET or bet_inr > MAX_BET:
                            send_message(chat_id, "⚠️ Invalid bet amount or limits.")
                        elif user_balances[user_id] < bet_inr:
                            send_message(chat_id, "❌ Insufficient balance!")
                        else:
                            user_balances[user_id] -= bet_inr
                            bot_win_chance = RIG_CONTROL["limbo"]
                            is_win = random.random() * 100 >= bot_win_chance
                            
                            landed = target_mult + round(random.uniform(0.1, 2.0), 2) if is_win else max(1.0, target_mult - round(random.uniform(0.1, 1.5), 2))
                            
                            res_text = f"🚀 *Limbo Game Results*\n\n🎯 Target: *{target_mult}x*\n📈 Landed: *{landed}x*\n\n"
                            if landed >= target_mult:
                                win_amt = bet_inr * target_mult
                                profit_inr = win_amt - bet_inr
                                user_balances[user_id] += win_amt
                                HOUSE_BALANCE -= profit_inr
                                update_user_stats(user_id, "limbo", bet_inr, profit_inr, True)
                                res_text += f"🎉 *Hit Target! You WON {format_money(win_amt, user_id)}*!"
                            else:
                                profit_inr = -bet_inr
                                HOUSE_BALANCE += bet_inr
                                update_user_stats(user_id, "limbo", bet_inr, profit_inr, False)
                                res_text += f"💥 *Crashed!* You lost."
                                
                            bio = generate_game_card_image("LIMBO MULTIPLIER", [("Target Multiplier:", f"{target_mult}x"), ("Landed Multiplier:", f"{landed}x"), ("Outcome:", "SUCCESS" if landed >= target_mult else "CRASHED")])
                            send_photo(chat_id, bio, caption=res_text)
                    else:
                        send_message(chat_id, "⚠️ Format: `/limbo <amount> <multiplier>`\nExample: `/limbo 50 2.0`")

                elif text.startswith('/tower '):
                    parts = text.split(' ')
                    bet_inr = parse_user_amount(parts[1], user_id) if len(parts) > 1 else parse_user_amount("10", user_id)
                    if not bet_inr or bet_inr < MIN_BET or bet_inr > MAX_BET:
                        send_message(chat_id, "⚠️ Invalid bet limits.")
                    elif user_balances[user_id] < bet_inr:
                        send_message(chat_id, "❌ Insufficient balance!")
                    else:
                        user_balances[user_id] -= bet_inr
                        bot_win_chance = RIG_CONTROL["tower"]
                        is_win = random.random() * 100 >= bot_win_chance
                        
                        climbed_levels = random.randint(3, 5) if is_win else random.randint(0, 2)
                        multiplier = 1.5 * climbed_levels if climbed_levels > 0 else 0.0
                        
                        res_text = f"🏰 *Tower Climb Results
