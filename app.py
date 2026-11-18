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

ADMIN_USER_ID = 1822336097

user_balances = {}
user_currency = {}
user_stats = {}
user_deposits = {}
user_withdrawals = {}
active_games = {}
deposit_states = {}
withdrawal_states = {}

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
    payload = {"chat_id": chat_id, "text": text, "parse_mode": "Markdown"}
    if reply_markup:
        payload["reply_markup"] = reply_markup
    try:
        res = requests.post(url, json=payload, timeout=10)
        return res.json()
    except Exception as e:
        print(f"Error sending message: {e}")
        return None

def remove_inline_keyboard(chat_id, message_id):
    url = f"{TELEGRAM_API_URL}/editMessageReplyMarkup"
    payload = {
        "chat_id": chat_id,
        "message_id": message_id,
        "reply_markup": {"inline_keyboard": []}
    }
    try:
        requests.post(url, json=payload, timeout=5)
    except Exception as e:
        print(f"Error removing keyboard: {e}")

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
                
            # Handle Deposit Input State
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

            # Handle Withdrawal Flow (Amount -> UPI ID -> Confirm)
            if user_id in withdrawal_states and 'text' in message:
                state = withdrawal_states[user_id]
                text = message['text'].strip()
                
                if state['step'] == 'waiting_amount':
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

            # Handle Admin Reject Reason Input State
            if user_id == ADMIN_USER_ID and user_id in withdrawal_states and withdrawal_states[user_id].get('step') == 'waiting_reject_reason' and 'text' in message:
                reason = message['text'].strip()
                target_user = withdrawal_states[user_id]['target_user']
                amt_str = withdrawal_states[user_id]['amount_str']
                
                # Refund balance back to user
                user_balances[target_user] += withdrawal_states[user_id]['raw_amount']
                
                send_message(target_user, f"❌ *Withdrawal Request Rejected*\n\nAmount: {amt_str}\nReason: *{reason}*\n\nYour funds have been refunded to your wallet.")
                send_message(chat_id, f"✅ Rejection sent to user `{target_user}` with reason: _{reason}_")
                del withdrawal_states[user_id]
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
                        "- `/deposit <amount>` - Add money via ZapUPI\n"
                        "- `/withdraw` - Withdraw your winnings\n\n"
                        "🎮 *Versus Games (`/dice`, `/dart`, `/foot`, `/basket`, `/bowl`)*\n"
                        "_🔥 Add `crazy` for Lowest Win mode! (e.g. `/dice 50 crazy`)_\n\n"
                        "🔮 *Prediction Game (`/dr`):*\n"
                        "- `/dr 50 high` or `/dr 50 2,4,6`"
                    )
                    send_message(chat_id, help_text)
                    
                elif text == '/balance':
                    bal_str = format_money(user_balances[user_id], user_id)
                    send_message(chat_id, f"💰 *Your Wallet Balance:* {bal_str}\n\nUse `/deposit` or `/withdraw` for transactions.")
                    
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

                elif text == '/withdraw':
                    withdrawal_states[user_id] = {'step': 'waiting_amount'}
                    send_message(chat_id, "💸 *Withdrawal Flow*\n\nPlease enter the amount you want to withdraw:")
                    
                elif text.startswith('/dr '):
                    parts = text.split(' ')
                    if len(parts) == 3 and parts[1].replace('.', '', 1).isdigit():
                        bet_inr = parse_user_amount(parts[1], user_id)
                        arg = parts[2].lower()
                        
                        if bet_inr < MIN_BET or bet_inr > MAX_BET:
                            send_message(chat_id, f"⚠️ Bet out of limits! Min: {format_money(MIN_BET, user_id)} | Max: {format_money(MAX_BET, user_id)}")
                            return jsonify({'status': 'ok'}), 200
                        elif user_balances[user_id] < bet_inr:
                            send_message(chat_id, "❌ Insufficient balance! Use `/deposit` to add money.")
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
                                mode = "crazy"
                                if len(parts) > 2:
                                    bet_inr = parse_user_amount(parts[2], user_id)
                            else:
                                bet_inr = parse_user_amount(parts[1], user_id)
                                if len(parts) > 2 and parts[2].lower() == 'crazy':
                                    mode = "crazy"
                                    
                        if bet_inr is None or bet_inr <= 0:
                            send_message(chat_id, "⚠️ Enter a valid bet amount.")
                        elif bet_inr < MIN_BET or bet_inr > MAX_BET:
                            send_message(chat_id, f"⚠️ Bet out of limits! Min: {format_money(MIN_BET, user_id)} | Max: {format_money(MAX_BET, user_id)}")
                        elif user_balances[user_id] < bet_inr:
                            send_message(chat_id, "❌ Insufficient balance! Use `/deposit` to add money.")
                        else:
                            user_balances[user_id] -= bet_inr
                            active_games[user_id] = {"bet": bet_inr, "emoji": triggered_game, "mode": mode, "step": "selecting_turn"}
                            
                            mode_title = "🔥 CRAZY MODE (Lowest Wins)" if mode == "crazy" else "⚡ NORMAL MODE (Highest Wins)"
                            keyboard = {
                                "inline_keyboard": [
                                    [
                                        {"text": "🤖 Bot Roll First", "callback_data": "play_bot_first"},
                                        {"text": "👤 You Roll First", "callback_data": "play_user_first"}
                                    ]
                                ]
                            }
                            send_message(chat_id, f"🎮 *Game Started* ({triggered_game} | {mode_title})\n💰 Bet: {format_money(bet_inr, user_id)}\n\nChoose who rolls first:", reply_markup=keyboard)
                            
                    elif text in ['/panel', '/admin']:
                        if user_id == ADMIN_USER_ID:
                            panel_text = (
                                "👑 *Owner Admin Control Panel*\n\n"
                                "Commands:\n"
                                "- `/hb` - Check House Balance\n"
                                "- `/sethb <amount>` - Set House Balance\n"
                                "- `/deducthb <amount>` - Deduct HB\n"
                                "- `/minbet <amount>` - Set Min Bet\n"
                                "- `/maxbet <amount>` - Set Max Bet\n"
                                "- `/setrate <rate>` - Set USD/INR Rate\n"
                                "- `/addbalance <user_id> <amount>`\n"
                                "- `/users` - View all users\n"
                                "- `/sendto <user_id> <message>`"
                            )
                            send_message(chat_id, panel_text)
                        else:
                            send_message(chat_id, "⛔ Unauthorized.")
                            
                    elif text.startswith('/addbalance '):
                        if user_id == ADMIN_USER_ID:
                            parts = text.split(' ')
                            if len(parts) == 3 and parts[1].isdigit():
                                t_user = int(parts[1])
                                amt = parse_user_amount(parts[2], user_id)
                                if t_user not in user_balances: user_balances[t_user] = 0.0
                                user_balances[t_user] += amt
                                send_message(chat_id, f"✅ Updated User `{t_user}`. New Bal: {format_money(user_balances[t_user], t_user)}")
                                send_message(t_user, f"💰 *Admin updated your balance!* New Balance: {format_money(user_balances[t_user], t_user)}")
                            else:
                                send_message(chat_id, "⚠️ Format: `/addbalance <user_id> <amount>`")
                                
                    elif text == '/users':
                        if user_id == ADMIN_USER_ID:
                            txt = "👥 *Users & Balances:*\n"
                            for uid, bal in user_balances.items(): 
                                txt += f"- `{uid}`: {format_money(bal, uid)}\n"
                            send_message(chat_id, txt)
                            
                    elif text.startswith('/sendto '):
                        if user_id == ADMIN_USER_ID:
                            parts = text.split(' ', 2)
                            if len(parts) >= 3 and parts[1].isdigit():
                                send_message(int(parts[1]), f"📢 *Admin Message:*\n\n{parts[2]}")
                                send_message(chat_id, "✅ Message sent successfully!")

        elif 'callback_query' in data:
            query = data['callback_query']
            callback_data = query['data']
            chat_id = query['message']['chat']['id']
            message_id = query['message']['message_id']
            user_id = query['from']['id']
            
            remove_inline_keyboard(chat_id, message_id)
            
            if user_id not in user_balances:
                user_balances[user_id] = 0.0
                user_currency[user_id] = 'INR'
                
            if callback_data == "curr_inr":
                user_currency[user_id] = 'INR'
                send_message(chat_id, "✅ Currency successfully set to *INR (₹)*!")
            elif callback_data == "curr_usdt":
                user_currency[user_id] = 'USDT'
                send_message(chat_id, "✅ Currency successfully set to *USD ($)*!")
                
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
                    
                    amt_str = format_money(raw_amt, user_id)
                    upi_id = st['upi_id']
                    
                    send_message(chat_id, "📤 *Withdrawal Request Submitted!*\n\nYour request has been sent to the admin for verification. You will be notified once processed.")
                    
                    # Send to Admin with Paid and Reject buttons
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
                if user_id == ADMIN_USER_ID:
                    parts = callback_data.split('_')
                    action = parts[2]
                    target_user = int(parts[3])
                    raw_amt = float(parts[4])
                    amt_str = format_money(raw_amt, target_user)
                    
                    if action == "paid":
                        success_msg = (
                            "🎉 *Withdrawal Approved & Paid!* ✨\n\n"
                            f"Dear User, your withdrawal of *{amt_str}* has been successfully processed and transferred to your account/UPI ID. 🚀\n\n"
                            "Thank you for playing with *Xyren Pro Casino*! 🎰"
                        )
                        send_message(target_user, success_msg)
                        send_message(chat_id, f"✅ Successfully marked withdrawal for user `{target_user}` as Paid.")
                    elif action == "reject":
                        withdrawal_states[ADMIN_USER_ID] = {
                            'step': 'waiting_reject_reason',
                            'target_user': target_user,
                            'raw_amount': raw_amt,
                            'amount_str': amt_str
                        }
                        send_message(chat_id, f"✍️ *Please enter the rejection reason for user `{target_user}` in chat:*")
                else:
                    send_message(chat_id, "⛔ Unauthorized.")
                
            elif callback_data in ["play_user_first", "play_bot_first"]:
                if user_id not in active_games:
                    send_message(chat_id, "⚠️ Session expired. Start a new game.")
                    return jsonify({'status': 'ok'}), 200
                    
                game = active_games[user_id]
                emoji = game["emoji"]
                
                if callback_data == "play_user_first":
                    game["step"] = "waiting_user_first"
                    send_message(chat_id, f"👤 You chose to roll first!\n\n👉 *Please send the `{emoji}` emoji in chat now to make your throw!*")
                else:
                    game["step"] = "waiting_user_second"
                    send_message(chat_id, f"🤖 Bot is throwing {emoji} first...")
                    
                    res_b = send_animated_game(chat_id, emoji)
                    bot_val = res_b['result']['dice']['value'] if res_b and 'result' in res_b else random.randint(1, 6)
                    game["bot_val"] = bot_val
                    
                    time.sleep(1)
                    send_message(chat_id, f"🤖 Bot Roll: *{bot_val}*\n\n👉 *Now your turn! Please send the `{emoji}` emoji in chat to throw.*")
                
        return jsonify({'status': 'ok'}), 200
    except Exception as e:
        print(f"❌ Webhook Error: {e}")
        return jsonify({'status': 'error', 'message': str(e)}), 200

def finish_game(chat_id, user_id, user_val, bot_val, bet, emoji, mode):
    global HOUSE_BALANCE
    mode_tag = "🔥 (CRAZY MODE)" if mode == "crazy" else ""
    res_text = f"📊 *Game Results ({emoji}) {mode_tag}*\n\n👤 You: *{user_val}*\n🤖 Bot: *{bot_val}*\n\n"
    
    is_win = False
    is_tie = False
    
    if user_val == bot_val:
        is_tie = True
    elif mode == "crazy":
        if user_val < bot_val:
            is_win = True
    else:
        if user_val > bot_val:
            is_win = True
            
    if is_tie:
        user_balances[user_id] += bet
        update_user_stats(user_id, emoji, bet, 0.0, False)
        res_text += f"🤝 *It's a Tie!* Bet refunded.\n💰 Balance: {format_money(user_balances[user_id], user_id)}"
    elif is_win:
        win = bet * 1.94
        profit_inr = win - bet
        user_balances[user_id] += win
        HOUSE_BALANCE -= profit_inr
        update_user_stats(user_id, emoji, bet, profit_inr, True)
        res_text += f"🎉 *You WON {format_money(win, user_id)}* (`1.94x`)! 🥳\n💰 Balance: {format_money(user_balances[user_id], user_id)}"
    else:
        profit_inr = -bet
        HOUSE_BALANCE += bet
        update_user_stats(user_id, emoji, bet, profit_inr, False)
        res_text += f"😢 *You Lost!* Bot wins.\n💰 Balance: {format_money(user_balances[user_id], user_id)}"
        
    send_message(chat_id, res_text)
    if user_id in active_games:
        del active_games[user_id]

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
                user_balances[user_id] += amount
                
                if chat_id not in user_deposits: user_deposits[chat_id] = 0.0
                user_deposits[chat_id] += amount
                
                success_msg = f"✅ *Deposit Successful!* 🎉\n\nAdded: {format_money(amount, chat_id)}\nNew Balance: {format_money(user_balances[chat_id], chat_id)}\nOrder ID: `{order_id}`\nUTR: `{utr}`"
                send_message(chat_id, success_msg)
                    
        return jsonify({'status': 'ok'}), 200
    except Exception as e:
        print(f"❌ ZapUPI Webhook Error: {e}")
        return jsonify({'status': 'error', 'message': str(e)}), 200

if __name__ == '__main__':
    app.run(host='0.0.0.0', port=5000)
