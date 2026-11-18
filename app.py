import os
import time
import random
import requests
from flask import Flask, request, jsonify

app = Flask(__name__)

TELEGRAM_BOT_TOKEN = os.environ.get("TELEGRAM_BOT_TOKEN")
ZAPUPI_API_KEY = os.environ.get("ZAPUPI_API_KEY")

TELEGRAM_API_URL = f"https://api.telegram.org/bot{TELEGRAM_BOT_TOKEN}"

# Tera Admin User ID
ADMIN_USER_ID = 1822336097

user_balances = {}
active_games = {}

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

def send_animated_game(chat_id, emoji):
    """Bot apne taraf se animated game emoji bhejta hai"""
    url = f"{TELEGRAM_API_URL}/sendDice"
    payload = {
        "chat_id": chat_id,
        "emoji": emoji
    }
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
    return "Xyren True Turn-Based Casino Bot is Live!", 200

@app.route('/webhook', methods=['POST'])
def telegram_webhook():
    data = request.get_json()
    if not data:
        return jsonify({'status': 'error'}), 400
        
    if 'message' in data:
        message = data['message']
        chat_id = message['chat'].get('id')
        user_id = message['from'].get('id')
        
        if user_id not in user_balances:
            user_balances[user_id] = 100.0  # Free testing balance
            
        # 1. Handle User Manual Emoji Throw in Chat
        if 'dice' in message and user_id in active_games:
            game = active_games[user_id]
            expected_emoji = game['emoji']
            user_dice = message['dice']
            
            if user_dice.get('emoji') == expected_emoji:
                user_val = user_dice.get('value', 1)
                bet = game['bet']
                step = game['step']
                
                if step == 'waiting_user_first':
                    # User threw first, now bot throws second
                    game['user_val'] = user_val
                    send_message(chat_id, f"👤 Your Roll ({expected_emoji}): *{user_val}*\n\n🤖 Now bot is throwing...")
                    time.sleep(1)
                    
                    res_b = send_animated_game(chat_id, expected_emoji)
                    bot_val = res_b['result']['dice']['value'] if res_b and 'result' in res_b else random.randint(1, 6)
                    
                    finish_game(chat_id, user_id, user_val, bot_val, bet, expected_emoji)
                    return jsonify({'status': 'ok'}), 200
                    
                elif step == 'waiting_user_second':
                    # Bot had thrown first, now user threw second
                    bot_val = game['bot_val']
                    finish_game(chat_id, user_id, user_val, bot_val, bet, expected_emoji)
                    return jsonify({'status': 'ok'}), 200

        # 2. Handle Text Commands
        if 'text' in message:
            text = message['text'].strip()
            
            if text == '/start':
                help_text = (
                    "🎰 *Welcome to Xyren True Turn-Based Casino!* 🎲\n\n"
                    "Commands:\n"
                    "- `/balance` - Check wallet balance\n"
                    "- `/deposit <amount>` - Add money via ZapUPI\n\n"
                    "🎮 *Versus Games (1.94x Multiplier):*\n"
                    "- `/dice <amount>` 🎲\n"
                    "- `/dart <amount>` 🎯\n"
                    "- `/foot <amount>` ⚽\n"
                    "- `/basket <amount>` 🏀\n"
                    "- `/bowl <amount>` 🎳\n\n"
                    "🔮 *Advanced Dice Prediction (`/dr`):*\n"
                    "- High/Low/Odd/Even (1.92x): `/dr 50 high`\n"
                    "- Number Picks (1-5 numbers): `/dr 50 2,4,6`"
                )
                send_message(chat_id, help_text)
                
            elif text == '/balance':
                send_message(chat_id, f"💰 *Your Wallet Balance:* ₹{user_balances[user_id]:.2f}")
                
            elif text.startswith('/deposit '):
                parts = text.split(' ')
                if len(parts) > 1 and parts[1].isdigit():
                    send_message(chat_id, "⏳ Generating deposit link...")
                    res_text = create_zapupi_order(parts[1], user_id)
                    send_message(chat_id, res_text)
                else:
                    send_message(chat_id, "⚠️ Use format: `/deposit 100`")
                    
            # --- ADVANCED PREDICTION GAME: /dr ---
            elif text.startswith('/dr '):
                parts = text.split(' ')
                if len(parts) == 3 and parts[1].replace('.', '', 1).isdigit():
                    bet = float(parts[1])
                    arg = parts[2].lower()
                    
                    if user_balances[user_id] < bet:
                        send_message(chat_id, "❌ Insufficient balance! Use `/deposit <amount>` to add money.")
                        return jsonify({'status': 'ok'}), 200
                    elif bet <= 0:
                        send_message(chat_id, "⚠️ Enter a valid bet amount.")
                        return jsonify({'status': 'ok'}), 200
                        
                    is_win = False
                    multiplier = 0.0
                    win_desc = ""
                    
                    if arg in ['high', 'low', 'odd', 'even']:
                        user_balances[user_id] -= bet
                        send_message(chat_id, f"🎲 Rolling dice for Prediction (*{arg.upper()}* | Bet: ₹{bet})...")
                        
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
                                
                            user_balances[user_id] -= bet
                            send_message(chat_id, f"🎲 Rolling dice for Numbers (*{nums}* | Bet: ₹{bet})...")
                            
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
                        win_amt = bet * multiplier
                        user_balances[user_id] += win_amt
                        result_text += f"🎉 *Congratulations! You WON ₹{win_amt:.2f}* (`{multiplier}x`)! 🥳\n💰 Balance: ₹{user_balances[user_id]:.2f}"
                    else:
                        result_text += f"😢 *You Lost!* Better luck next time.\n💰 Balance: ₹{user_balances[user_id]:.2f}"
                        
                    send_message(chat_id, result_text)
                else:
                    send_message(chat_id, "⚠️ Format error! Use: `/dr <amount> <choice>`\nExample: `/dr 50 high` or `/dr 50 1,3,5`")
                    
            # --- VERSUS GAMES COMMANDS ---
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
                    bet = 10.0
                    if len(parts) > 1 and parts[1].replace('.', '', 1).isdigit():
                        bet = float(parts[1])
                        
                    if user_balances[user_id] < bet:
                        send_message(chat_id, "❌ Insufficient balance! Use `/deposit <amount>` to add money.")
                    elif bet <= 0:
                        send_message(chat_id, "⚠️ Enter a valid bet amount.")
                    else:
                        user_balances[user_id] -= bet
                        active_games[user_id] = {"bet": bet, "emoji": triggered_game, "step": "selecting_turn"}
                        
                        keyboard = {
                            "inline_keyboard": [
                                [
                                    {"text": "🤖 Bot Roll First", "callback_data": "play_bot_first"},
                                    {"text": "👤 You Roll First", "callback_data": "play_user_first"}
                                ]
                            ]
                        }
                        send_message(chat_id, f"🎮 *Game Started* ({triggered_game} | Bet: ₹{bet})\n\nChoose who rolls first:", reply_markup=keyboard)
                        
                # --- ADMIN PANEL (/panel) ---
                elif text in ['/panel', '/admin']:
                    if user_id == ADMIN_USER_ID:
                        panel_text = (
                            "👑 *Owner Admin Control Panel*\n\n"
                            "Commands:\n"
                            "- `/addbalance <user_id> <amount>`\n"
                            "- `/users`\n"
                            "- `/sendto <user_id> <message>`"
                        )
                        send_message(chat_id, panel_text)
                    else:
                        send_message(chat_id, "⛔ Unauthorized.")
                        
                elif text.startswith('/addbalance '):
                    if user_id == ADMIN_USER_ID:
                        parts = text.split(' ')
                        if len(parts) == 3 and parts[1].isdigit():
                            t_user, amt = int(parts[1]), float(parts[2])
                            if t_user not in user_balances: user_balances[t_user] = 0.0
                            user_balances[t_user] += amt
                            send_message(chat_id, f"✅ Updated User `{t_user}`. New Bal: ₹{user_balances[t_user]}")
                            send_message(t_user, f"💰 *Admin updated your balance!* New Balance: ₹{user_balances[t_user]}")
                        else:
                            send_message(chat_id, "⚠️ Format: `/addbalance <user_id> <amount>`")
                            
                elif text == '/users':
                    if user_id == ADMIN_USER_ID:
                        txt = "👥 *Users & Balances:*\n"
                        for uid, bal in user_balances.items(): txt += f"- `{uid}`: ₹{bal}\n"
                        send_message(chat_id, txt)
                        
                elif text.startswith('/sendto '):
                    if user_id == ADMIN_USER_ID:
                        parts = text.split(' ', 2)
                        if len(parts) >= 3 and parts[1].isdigit():
                            send_message(int(parts[1]), f"📢 *Admin Message:*\n\n{parts[2]}")
                            send_message(chat_id, "✅ Message sent successfully!")

    # --- INLINE BUTTON CALLBACKS FOR TURN SELECTION ---
    elif 'callback_query' in data:
        query = data['callback_query']
        callback_data = query['data']
        chat_id = query['message']['chat']['id']
        user_id = query['from']['id']
        
        if user_id not in active_games:
            send_message(chat_id, "⚠️ Session expired. Start a new game using game commands like `/dice 50`.")
            return jsonify({'status': 'ok'}), 200
            
        game = active_games[user_id]
        emoji = game["emoji"]
        
        if callback_data == "play_user_first":
            game["step"] = "waiting_user_first"
            send_message(chat_id, f"👤 You chose to roll first!\n\n👉 *Please send the `{emoji}` emoji in chat now to make your throw!*")
            
        elif callback_data == "play_bot_first":
            game["step"] = "waiting_user_second"
            send_message(chat_id, f"🤖 Bot is throwing {emoji} first...")
            
            res_b = send_animated_game(chat_id, emoji)
            bot_val = res_b['result']['dice']['value'] if res_b and 'result' in res_b else random.randint(1, 6)
            game["bot_val"] = bot_val
            
            time.sleep(1)
            send_message(chat_id, f"🤖 Bot Roll: *{bot_val}*\n\n👉 *Now your turn! Please send the `{emoji}` emoji in chat to throw.*")
            
    return jsonify({'status': 'ok'}), 200

def finish_game(chat_id, user_id, user_val, bot_val, bet, emoji):
    """Calculates winner and updates balance with 1.94x multiplier"""
    res_text = f"📊 *Game Results ({emoji})*\n\n👤 You: *{user_val}*\n🤖 Bot: *{bot_val}*\n\n"
    
    if user_val > bot_val:
        win = bet * 1.94
        user_balances[user_id] += win
        res_text += f"🎉 *You WON ₹{win:.2f}* (`1.94x`)! 🥳\n💰 Balance: ₹{user_balances[user_id]:.2f}"
    elif user_val < bot_val:
        res_text += f"😢 *You Lost!* Bot wins.\n💰 Balance: ₹{user_balances[user_id]:.2f}"
    else:
        user_balances[user_id] += bet  # Refund on tie
        res_text += f"🤝 *It's a Tie!* Bet refunded.\n💰 Balance: ₹{user_balances[user_id]:.2f}"
        
    send_message(chat_id, res_text)
    if user_id in active_games:
        del active_games[user_id]

@app.route('/zapupi-webhook', methods=['POST'])
def zapupi_webhook():
    data = request.get_json()
    print(f"📥 ZapUPI Webhook Received: {data}")
    
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
            user_balances[chat_id] += amount
            
            success_msg = f"✅ *Deposit Successful!* 🎉\n\nAdded: ₹{amount}\nNew Balance: ₹{user_balances[chat_id]:.2f}\nOrder ID: `{order_id}`\nUTR: `{utr}`"
            send_message(chat_id, success_msg)
            print(f"✅ Balance ₹{amount} added successfully to user {chat_id}")
        else:
            print(f"⚠️ Webhook error: Could not extract chat_id from remark: {remark}")
                
    return jsonify({'status': 'ok'}), 200

if __name__ == '__main__':
    app.run(host='0.0.0.0', port=5000)
    
