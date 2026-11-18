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
    return "Xyren Interactive Casino Bot is Live!", 200

@app.route('/webhook', methods=['POST'])
def telegram_webhook():
    data = request.get_json()
    if not data:
        return jsonify({'status': 'error'}), 400
        
    # 1. Handle User Sending Dice/Emoji manually in chat
    if 'message' in data:
        message = data['message']
        chat_id = message['chat'].get('id')
        user_id = message['from'].get('id')
        
        if user_id not in user_balances:
            user_balances[user_id] = 100.0  # Free testing balance
            
        # Agar user ne khud dice/emoji throw kiya hai aur uska active game chal raha hai
        if 'dice' in message and user_id in active_games and active_games[user_id].get('step') == 'waiting_user_throw':
            game = active_games[user_id]
            expected_emoji = game['emoji']
            user_dice = message['dice']
            
            # Match emoji type
            if user_dice.get('emoji') == expected_emoji:
                user_val = user_dice.get('value', 1)
                bet = game['bet']
                
                send_message(chat_id, f"👤 Your Roll ({expected_emoji}): *{user_val}*\n\n🤖 Now it's my turn...")
                time.sleep(1)
                
                # Bot throws its own emoji
                res_b = send_animated_game(chat_id, expected_emoji)
                bot_val = res_b['result']['dice']['value'] if res_b and 'result' in res_b else random.randint(1, 6)
                
                # Results calculation
                res_text = f"📊 *Game Results ({expected_emoji})*\n\n👤 You: *{user_val}*\n🤖 Bot: *{bot_val}*\n\n"
                if user_val > bot_val:
                    win = bet * 2
                    user_balances[user_id] += win
                    res_text += f"🎉 *You WON ₹{win}!* 🥳\n💰 Balance: ₹{user_balances[user_id]}"
                elif user_val < bot_val:
                    res_text += f"😢 *You Lost!* Bot wins.\n💰 Balance: ₹{user_balances[user_id]}"
                else:
                    user_balances[user_id] += bet  # Refund on tie
                    res_text += f"🤝 *It's a Tie!* Bet refunded.\n💰 Balance: ₹{user_balances[user_id]}"
                    
                send_message(chat_id, res_text)
                del active_games[user_id]
                return jsonify({'status': 'ok'}), 200

        # 2. Handle Text Messages / Commands
        if 'text' in message:
            text = message['text'].strip()
            
            if text == '/start':
                help_text = (
                    "🎰 *Welcome to Xyren Interactive Casino!*\n\n"
                    "Commands:\n"
                    "- `/balance` - Check wallet balance\n"
                    "- `/deposit <amount>` - Add money via ZapUPI\n\n"
                    "🎮 *Versus Games (You throw your own emoji!):*\n"
                    "- `/dice <amount>` 🎲\n"
                    "- `/dart <amount>` 🎯\n"
                    "- `/foot <amount>` ⚽\n"
                    "- `/basket <amount>` 🏀\n"
                    "- `/bowl <amount>` 🎳\n\n"
                    "🔮 *Prediction Game:*\n"
                    "- `/dr <amount> <high/low/odd/even>` (e.g., `/dr 50 high`)"
                )
                send_message(chat_id, help_text)
                
            elif text == '/balance':
                send_message(chat_id, f"💰 *Your Wallet Balance:* ₹{user_balances[user_id]}")
                
            elif text.startswith('/deposit '):
                parts = text.split(' ')
                if len(parts) > 1 and parts[1].isdigit():
                    send_message(chat_id, "⏳ Generating deposit link...")
                    res_text = create_zapupi_order(parts[1], user_id)
                    send_message(chat_id, res_text)
                else:
                    send_message(chat_id, "⚠️ Use format: `/deposit 100`")
                    
            # --- PREDICTION GAME: /dr ---
            elif text.startswith('/dr '):
                parts = text.split(' ')
                if len(parts) == 3 and parts[1].replace('.', '', 1).isdigit():
                    bet = float(parts[1])
                    choice = parts[2].lower()
                    
                    valid_choices = ['high', 'low', 'odd', 'even']
                    if choice not in valid_choices:
                        send_message(chat_id, "⚠️ Invalid choice! Use: `high`, `low`, `odd`, or `even`.\nExample: `/dr 50 high`")
                    elif user_balances[user_id] < bet:
                        send_message(chat_id, "❌ Insufficient balance! Use `/deposit <amount>` to add money.")
                    elif bet <= 0:
                        send_message(chat_id, "⚠️ Enter a valid bet amount.")
                    else:
                        user_balances[user_id] -= bet
                        send_message(chat_id, f"🎲 Rolling dice for Prediction (*{choice.upper()}* | Bet: ₹{bet})...")
                        
                        res = send_animated_game(chat_id, '🎲')
                        dice_val = res['result']['dice']['value'] if res and 'result' in res else random.randint(1, 6)
                        time.sleep(1)
                        
                        is_win = False
                        if choice == 'high' and dice_val in [4, 5, 6]:
                            is_win = True
                        elif choice == 'low' and dice_val in [1, 2, 3]:
                            is_win = True
                        elif choice == 'odd' and dice_val in [1, 3, 5]:
                            is_win = True
                        elif choice == 'even' and dice_val in [2, 4, 6]:
                            is_win = True
                            
                        result_text = f"📊 *Dice Prediction Result*\n\n🎲 Rolled Number: *{dice_val}*\n🎯 Your Pick: *{choice.upper()}*\n\n"
                        if is_win:
                            win_amt = bet * 2
                            user_balances[user_id] += win_amt
                            result_text += f"🎉 *Congratulations! You WON ₹{win_amt}!* 🥳\n💰 Balance: ₹{user_balances[user_id]}"
                        else:
                            result_text += f"😢 *You Lost!* Better luck next time.\n💰 Balance: ₹{user_balances[user_id]}"
                            
                        send_message(chat_id, result_text)
                else:
                    send_message(chat_id, "⚠️ Format error! Use: `/dr <amount> <choice>`\nExample: `/dr 50 high`")
                    
            # --- VERSUS GAMES COMMANDS (User throws manually) ---
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
                        # Deduct bet and set waiting state for user throw
                        user_balances[user_id] -= bet
                        active_games[user_id] = {
                            "bet": bet,
                            "emoji": triggered_game,
                            "step": "waiting_user_throw"
                        }
                        send_message(chat_id, f"🎮 *Game Started* ({triggered_game} | Bet: ₹{bet})\n\n👉 *Now please send the `{triggered_game}` emoji in chat to make your throw!*")
                        
                # --- ADMIN PANEL ---
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

    return jsonify({'status': 'ok'}), 200

@app.route('/zapupi-webhook', methods=['POST'])
def zapupi_webhook():
    data = request.get_json()
    if not data: return jsonify({'status': 'error'}), 400
    
    if data.get('status') == 'Success':
        remark = data.get('remark', '')
        if '|' in remark:
            parts = remark.split('|')
            if len(parts) > 1 and parts[1].isdigit():
                chat_id = int(parts[1])
                amt = float(data.get('amount', 0))
                if chat_id not in user_balances: user_balances[user_id] = 0.0
                user_balances[user_id] += amt
                send_message(chat_id, f"✅ *Deposit Successful!* Added: ₹{amt}\n💰 New Balance: ₹{user_balances[user_id]}")
                
    return jsonify({'status': 'ok'}), 200

if __name__ == '__main__':
    app.run(host='0.0.0.0', port=5000)
                
