import os
import time
import requests
from flask import Flask, request, jsonify

app = Flask(__name__)

TELEGRAM_BOT_TOKEN = os.environ.get("TELEGRAM_BOT_TOKEN")
ZAPUPI_API_KEY = os.environ.get("ZAPUPI_API_KEY")

TELEGRAM_API_URL = f"https://api.telegram.org/bot{TELEGRAM_BOT_TOKEN}"

# Tera Telegram Admin User ID set kar diya hai
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
        requests.post(url, json=payload, timeout=10)
    except Exception as e:
        print(f"Error sending message: {e}")

def send_animated_game(chat_id, emoji):
    """Telegram ka native animated game/emoji bhejta hai"""
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
    return "Xyren Multi-Game Casino Bot with Panel is Live!", 200

@app.route('/webhook', methods=['POST'])
def telegram_webhook():
    data = request.get_json()
    if not data:
        return jsonify({'status': 'error'}), 400
        
    if 'message' in data:
        message = data['message']
        chat_id = message['chat'].get('id')
        user_id = message['from'].get('id')
        text = message.get('text', '').strip()
        
        if user_id not in user_balances:
            user_balances[user_id] = 100.0  # Free testing balance
            
        if text == '/start':
            help_text = (
                "🎰 *Welcome to Xyren Multi-Game Casino!*\n\n"
                "Commands:\n"
                "- `/balance` - Check wallet balance\n"
                "- `/deposit <amount>` - Add money via ZapUPI\n"
                "- `/games` - View & Play Casino Games (Dice 🎲, Dart 🎯, Bowling 🎳, Basketball 🏀, Football ⚽)"
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
                
        elif text.startswith('/games') or text.startswith('/dice'):
            parts = text.split(' ')
            bet = 10.0
            if len(parts) > 1 and parts[1].replace('.', '', 1).isdigit():
                bet = float(parts[1])
                
            if user_balances[user_id] < bet:
                send_message(chat_id, "❌ Insufficient balance! Use `/deposit <amount>` to add money.")
            elif bet <= 0:
                send_message(chat_id, "⚠️ Enter a valid bet amount.")
            else:
                active_games[user_id] = {"bet": bet}
                keyboard = {
                    "inline_keyboard": [
                        [
                            {"text": "🎲 Dice", "callback_data": "game_dice"},
                            {"text": "🎯 Dart", "callback_data": "game_dart"}
                        ],
                        [
                            {"text": "🎳 Bowling", "callback_data": "game_bowling"},
                            {"text": "🏀 Basketball", "callback_data": "game_basketball"}
                        ],
                        [
                            {"text": "⚽ Football", "callback_data": "game_football"}
                        ]
                    ]
                }
                send_message(chat_id, f"🎮 *Select a Game to Play* (Bet: ₹{bet})\nChoose your favorite game below:", reply_markup=keyboard)
                
        # --- ADMIN PANEL (/panel) ---
        elif text in ['/panel', '/admin']:
            if user_id == ADMIN_USER_ID:
                panel_text = (
                    "👑 *Owner Admin Control Panel*\n\n"
                    "Commands:\n"
                    "- `/addbalance <user_id> <amount>` - Add/Subtract balance\n"
                    "- `/users` - View all active users & balances\n"
                    "- `/sendto <user_id> <message>` - Send DM to user"
                )
                send_message(chat_id, panel_text)
            else:
                send_message(chat_id, "⛔ You are not authorized to access the admin panel.")
                
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

    elif 'callback_query' in data:
        query = data['callback_query']
        callback_data = query['data']
        chat_id = query['message']['chat']['id']
        user_id = query['from']['id']
        
        if user_id not in active_games:
            send_message(chat_id, "⚠️ Session expired. Type `/games` to play again.")
            return jsonify({'status': 'ok'}), 200
            
        bet = active_games[user_id]["bet"]
        if user_balances.get(user_id, 0) < bet:
            send_message(chat_id, "❌ Insufficient balance!")
            return jsonify({'status': 'ok'}), 200
            
        emoji_map = {
            "game_dice": "🎲",
            "game_dart": "🎯",
            "game_bowling": "🎳",
            "game_basketball": "🏀",
            "game_football": "⚽"
        }
        
        if callback_data in emoji_map:
            selected_emoji = emoji_map[callback_data]
            active_games[user_id]["emoji"] = selected_emoji
            
            keyboard = {
                "inline_keyboard": [
                    [
                        {"text": "👤 You Roll First", "callback_data": "roll_user"},
                        {"text": "🤖 Bot Roll First", "callback_data": "roll_bot"}
                    ]
                ]
            }
            send_message(chat_id, f"You selected {selected_emoji} (Bet: ₹{bet}). Who wants to play first?", reply_markup=keyboard)
            
        elif callback_data in ["roll_user", "roll_bot"]:
            emoji = active_games[user_id].get("emoji", "🎲")
            user_balances[user_id] -= bet
            
            if callback_data == "roll_user":
                send_message(chat_id, f"Your turn ({emoji})...")
                res_u = send_animated_game(chat_id, emoji)
                val_u = res_u['result']['dice']['value'] if res_u and 'result' in res_u else 1
                
                time.sleep(1)
                send_message(chat_id, f"Bot's turn ({emoji})...")
                res_b = send_animated_game(chat_id, emoji)
                val_b = res_b['result']['dice']['value'] if res_b and 'result' in res_b else 1
            else:
                send_message(chat_id, f"Bot's turn ({emoji})...")
                res_b = send_animated_game(chat_id, emoji)
                val_b = res_b['result']['dice']['value'] if res_b and 'result' in res_b else 1
                
                time.sleep(1)
                send_message(chat_id, f"Your turn ({emoji})...")
                res_u = send_animated_game(chat_id, emoji)
                val_u = res_u['result']['dice']['value'] if res_u and 'result' in res_u else 1
                
            res_text = f"📊 *Game Results ({emoji})*\n\n👤 You: *{val_u}*\n🤖 Bot: *{val_b}*\n\n"
            if val_u > val_b:
                win = bet * 2
                user_balances[user_id] += win
                res_text += f"🎉 *You WON ₹{win}!* 🥳\n💰 Balance: ₹{user_balances[user_id]}"
            elif val_u < val_b:
                res_text += f"😢 *You Lost!* Bot wins.\n💰 Balance: ₹{user_balances[user_id]}"
            else:
                user_balances[user_id] += bet
                res_text += f"🤝 *It's a Tie!* Bet refunded.\n💰 Balance: ₹{user_balances[user_id]}"
                
            send_message(chat_id, res_text)
            del active_games[user_id]
            
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
                if chat_id not in user_balances: user_balances[chat_id] = 0.0
                user_balances[chat_id] += amt
                send_message(chat_id, f"✅ *Deposit Successful!* Added: ₹{amt}\n💰 New Balance: ₹{user_balances[chat_id]}")
                
    return jsonify({'status': 'ok'}), 200

if __name__ == '__main__':
    app.run(host='0.0.0.0', port=5000)
            
