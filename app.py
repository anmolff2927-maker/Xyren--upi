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

HOUSE_BALANCE = 100000.0
MIN_BET = 10.0
MAX_BET = 1000.0
EXCHANGE_RATE = 98.0

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
    files = {'photo': ('stats.png', photo_bio, 'image/png')}
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
            
            # New user gets ₹100 starting balance
            if user_id not in user_balances:
                user_balances[user_id] = 100.0
                user_currency[user_id] = 'INR'
                
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
                        "🎮 *Versus Games (1.94x Multiplier):*\n"
                        "- `/dice <amount>` 🎲 | `/dart <amount>` 🎯\n"
                        "- `/foot <amount>` ⚽ | `/basket <amount>` 🏀\n"
                        "- `/bowl <amount>` 🎳\n"
                        "_🔥 Add `crazy` for Lowest Win mode! (e.g. `/dice 50 crazy`)_\n\n"
                        "🔮 *Prediction Game (`/dr`):*\n"
                        "- `/dr 50 high` or `/dr 50 2,4,6`"
                    )
                    send_message(chat_id, help_text)
                    
                elif text == '/balance':
                    bal_str = format_money(user_balances[user_id], user_id)
                    send_message(chat_id, f"💰 *Your Wallet Balance:* {bal_str}")
                    
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
                    
                elif text.startswith('/deposit '):
                    parts = text.split(' ')
                    if len(parts) > 1 and parts[1].replace('.', '', 1).isdigit():
                        amt_inr = parse_user_amount(parts[1], user_id)
                        send_message(chat_id, "⏳ Generating deposit link...")
                        res_text = create_zapupi_order(amt_inr, user_id)
                        send_message(chat_id, res_text)
                    else:
                        send_message(chat_id, "⚠️ Use format: `/deposit 100`")
                        
                elif text in ['/hb', '/housebal']:
                    if user_id == ADMIN_USER_ID:
                        hb_inr = HOUSE_BALANCE
                        hb_usdt = hb_inr / EXCHANGE_RATE
                        send_message(chat_id, f"🏦 *House Balance (HB):*\n- ₹{hb_inr:,.2f} INR\n- ${hb_usdt:,.2f} USDT\n- *Current Rate:* 1$ = ₹{EXCHANGE_RATE}")
                    else:
                        send_message(chat_id, "⛔ Unauthorized.")
                        
                elif text.startswith('/sethb '):
                    if user_id == ADMIN_USER_ID:
                        parts = text.split(' ')
                        if len(parts) == 2:
                            val_str = parts[1].replace('$', '').replace('₹', '')
                            if val_str.replace('.', '', 1).isdigit():
                                if '$' in parts[1] or 'usdt' in parts[1].lower():
                                    HOUSE_BALANCE = float(val_str) * EXCHANGE_RATE
                                else:
                                    HOUSE_BALANCE = float(val_str)
                                send_message(chat_id, f"✅ House Balance successfully updated to ₹{HOUSE_BALANCE:,.2f}")
                    else:
                        send_message(chat_id, "⛔ Unauthorized.")
                        
                elif text.startswith('/deducthb '):
                    if user_id == ADMIN_USER_ID:
                        parts = text.split(' ')
                        if len(parts) == 2:
                            val_str = parts[1].replace('$', '').replace('₹', '')
                            if val_str.replace('.', '', 1).isdigit():
                                deduct_amt = float(val_str)
                                if '$' in parts[1]:
                                    deduct_amt = deduct_amt * EXCHANGE_RATE
                                HOUSE_BALANCE -= deduct_amt
                                send_message(chat_id, f"✅ Deducted from House Balance. New HB: ₹{HOUSE_BALANCE:,.2f}")
                    else:
                        send_message(chat_id, "⛔ Unauthorized.")
                        
                elif text.startswith('/minbet '):
                    if user_id == ADMIN_USER_ID:
                        parts = text.split(' ')
                        if len(parts) == 2:
                            amt = parse_user_amount(parts[1], user_id)
                            if amt:
                                MIN_BET = amt
                                send_message(chat_id, f"✅ Minimum Bet set to {format_money(MIN_BET, user_id)}")
                    else:
                        send_message(chat_id, "⛔ Unauthorized.")
                        
                elif text.startswith('/maxbet '):
                    if user_id == ADMIN_USER_ID:
                        parts = text.split(' ')
                        if len(parts) == 2:
                            amt = parse_user_amount(parts[1], user_id)
                            if amt:
                                MAX_BET = amt
                                send_message(chat_id, f"✅ Maximum Bet set to {format_money(MAX_BET, user_id)}")
                    else:
                        send_message(chat_id, "⛔ Unauthorized.")
                        
                elif text.startswith('/setrate '):
                    if user_id == ADMIN_USER_ID:
                        parts = text.split(' ')
                        if len(parts) == 2 and parts[1].replace('.', '', 1).isdigit():
                            EXCHANGE_RATE = float(parts[1])
                            send_message(chat_id, f"✅ Exchange Rate updated successfully!\n1 USDT = ₹{EXCHANGE_RATE}")
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
                            send_message(chat_id, "❌ Insufficient balance! Use `/deposit <amount>` to add money.")
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
                        if text.startswith(cmd):
                            triggered_game = emoji
                            break
                    
                    if triggered_game:
                        parts = text.split(' ')
                        bet_inr = parse_user_amount("10", user_id)
                        mode = "normal"
                        
                        if len(parts) > 1:
                            if parts[1].lower() == 'crazy':
       
