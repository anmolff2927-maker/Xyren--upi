import os
import time
import random
import requests
from flask import Flask, request, jsonify

app = Flask(__name__)

TELEGRAM_BOT_TOKEN = os.environ.get("TELEGRAM_BOT_TOKEN")
ZAPUPI_API_KEY = os.environ.get("ZAPUPI_API_KEY")

TELEGRAM_API_URL = f"https://api.telegram.org/bot{TELEGRAM_BOT_TOKEN}"

# User balances storage
user_balances = {}

def send_message(chat_id, text):
    url = f"{TELEGRAM_API_URL}/sendMessage"
    payload = {
        "chat_id": chat_id,
        "text": text,
        "parse_mode": "Markdown"
    }
    try:
        requests.post(url, json=payload, timeout=10)
    except Exception as e:
        print(f"Error sending telegram message: {e}")

def send_dice(chat_id):
    """Telegram par animated dice bhejne ke liye"""
    url = f"{TELEGRAM_API_URL}/sendDice"
    payload = {
        "chat_id": chat_id,
        "emoji": "🎲"
    }
    try:
        res = requests.post(url, json=payload, timeout=10)
        return res.json()
    except Exception as e:
        print(f"Error sending dice: {e}")
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
            payment_url = data.get("payment_url")
            return f"🔗 *Deposit Link Generated!*\n\nAmount: ₹{amount}\nOrder ID: `{order_id}`\n\n[Click here to Pay & Add Money]({payment_url})"
        else:
            return f"❌ Failed: {data.get('message', 'Unknown error')}"
    except Exception as e:
        return "⚠️ Failed to connect to payment gateway."

@app.route('/')
def index():
    return "Xyren Casino Bot is running live with Games!", 200

@app.route('/webhook', methods=['POST'])
def telegram_webhook():
    data = request.get_json()
    if not data:
        return jsonify({'status': 'error'}), 400
        
    if 'message' in data:
        message = data['message']
        chat_id = message['chat'].get('id')
        text = message.get('text', '').strip()
        
        if chat_id not in user_balances:
            user_balances[chat_id] = 100.0  # Testing ke liye starting mein ₹100 free balance de sakte hain, ya 0.0 kar sakte ho
            
        if text == '/start':
            send_message(chat_id, "🎰 *Welcome to Xyren Casino!*\n\nCommands:\n- `/balance` - Check wallet\n- `/deposit <amount>` - Add money\n- `/dice <amount>` - Play Dice Game (Roll > 3 to Win Double!)")
        elif text == '/balance':
            send_message(chat_id, f"💰 *Your Wallet Balance:* ₹{user_balances[chat_id]}")
        elif text.startswith('/deposit '):
            parts = text.split(' ')
            if len(parts) > 1 and parts[1].isdigit():
                send_message(chat_id, "⏳ Generating deposit link...")
                res_text = create_zapupi_order(parts[1], chat_id)
                send_message(chat_id, res_text)
            else:
                send_message(chat_id, "⚠️ Use format: `/deposit 100`")
        elif text.startswith('/dice '):
            parts = text.split(' ')
            if len(parts) > 1 and parts[1].replace('.', '', 1).isdigit():
                bet_amount = float(parts[1])
                if user_balances[chat_id] < bet_amount:
                    send_message(chat_id, "❌ Insufficient balance! Please deposit money first using `/deposit <amount>`.")
                elif bet_amount <= 0:
                    send_message(chat_id, "⚠️ Enter a valid bet amount.")
                else:
                    # Balance deduct karo bet ke liye
                    user_balances[chat_id] -= bet_amount
                    send_message(chat_id, f"🎲 Rolling dice for bet of ₹{bet_amount}...")
                    
                    # Random dice roll simulate karte hain (1 to 6)
                    dice_result = random.randint(1, 6)
                    
                    if dice_result > 3:
                        winnings = bet_amount * 2
                        user_balances[chat_id] += winnings
                        send_message(chat_id, f"🎉 *You Rolled: {dice_result}*\n\n🥳 Congratulations! You WON ₹{winnings}!\n💰 New Balance: ₹{user_balances[chat_id]}")
                    else:
                        send_message(chat_id, f"😢 *You Rolled: {dice_result}*\n\n💥 You lost the bet of ₹{bet_amount}.\n💰 New Balance: ₹{user_balances[chat_id]}")
            else:
                send_message(chat_id, "⚠️ Use format: `/dice 50`")
        else:
            send_message(chat_id, "💡 Type `/start` to see available casino commands.")
            
    return jsonify({'status': 'ok'}), 200

@app.route('/zapupi-webhook', methods=['POST'])
def zapupi_webhook():
    data = request.get_json()
    if not data:
        return jsonify({'status': 'error'}), 400
        
    order_id = data.get('order_id')
    status = data.get('status')
    amount = float(data.get('amount', 0))
    utr = data.get('utr', '')
    
    if status == 'Success':
        remark = data.get('remark', '')
        if '|' in remark:
            parts = remark.split('|')
            if len(parts) > 1 and parts[1].isdigit():
                chat_id = int(parts[1])
                if chat_id not in user_balances:
                    user_balances[chat_id] = 0.0
                user_balances[chat_id] += amount
                send_message(chat_id, f"✅ *Deposit Successful!* 🎉\n\nAdded: ₹{amount}\nNew Balance: ₹{user_balances[chat_id]}\nOrder ID: `{order_id}`")
                
    return jsonify({'status': 'ok'}), 200

if __name__ == '__main__':
    app.run(host='0.0.0.0', port=5000)
    
