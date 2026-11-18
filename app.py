import os
import time
import requests
from flask import Flask, request, jsonify

app = Flask(__name__)

# Render Environment Variables se tokens uthayega
TELEGRAM_BOT_TOKEN = os.environ.get("TELEGRAM_BOT_TOKEN")
ZAPUPI_API_KEY = os.environ.get("ZAPUPI_API_KEY")

TELEGRAM_API_URL = f"https://api.telegram.org/bot{TELEGRAM_BOT_TOKEN}"

def send_message(chat_id, text):
    """Telegram par user ko message bhejne ke liye function"""
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

def create_zapupi_order(amount, chat_id):
    """ZapUPI se payment link generate karne ke liye function"""
    url = "https://pay.zapupi.com/api/create-order"
    order_id = "ORD" + str(int(time.time() * 1000))
    
    payload = {
        "zap_key": ZAPUPI_API_KEY,
        "order_id": order_id,
        "amount": str(amount),
        "remark": f"Telegram|{chat_id}",
        "webhook_url": "https://xyren-upi.onrender.com/zapupi-webhook"
    }
    
    headers = {
        "Content-Type": "application/json"
    }
    
    try:
        response = requests.post(url, json=payload, headers=headers, timeout=15)
        data = response.json()
        if data.get("status") == "success":
            payment_url = data.get("payment_url")
            return f"🔗 *Payment Link Generated!*\n\nAmount: ₹{amount}\nOrder ID: `{order_id}`\n\n[Click here to Pay]({payment_url})"
        else:
            return f"❌ Failed to generate payment link: {data.get('message', 'Unknown error')}"
    except Exception as e:
        return "⚠️ Failed to connect to payment gateway. Try again later."

@app.route('/')
def index():
    return "Xyren UPI Bot is running live!", 200

@app.route('/webhook', methods=['POST'])
def telegram_webhook():
    """Telegram se aane wale messages ko handle karne ke liye"""
    data = request.get_json()
    if not data:
        return jsonify({'status': 'error'}), 400
        
    if 'message' in data:
        message = data['message']
        chat_id = message['chat'].get('id')
        text = message.get('text', '').strip()
        
        if text == '/start':
            send_message(chat_id, "👋 Welcome to Xyren UPI Bot!\n\nPlease send the amount in INR (e.g., `100`) to generate a payment link.")
        elif text.isdigit():
            send_message(chat_id, "⏳ Generating your payment link, please wait...")
            response_text = create_zapupi_order(text, chat_id)
            send_message(chat_id, response_text)
        else:
            send_message(chat_id, "💡 Please send a valid numeric amount (e.g., `100`) or type /start.")
            
    return jsonify({'status': 'ok'}), 200

@app.route('/zapupi-webhook', methods=['POST'])
def zapupi_webhook():
    """ZapUPI payment success/failure callback handle karne ke liye"""
    data = request.get_json()
    if not data:
        return jsonify({'status': 'error', 'message': 'No data'}), 400
        
    order_id = data.get('order_id')
    status = data.get('status')   # Success | Failed
    utr = data.get('utr', '')
    
    if status == 'Success':
        print(f"Payment Successful for Order: {order_id}, UTR: {utr}")
        remark = data.get('remark', '')
        if '|' in remark:
            parts = remark.split('|')
            if len(parts) > 1 and parts[1].isdigit():
                chat_id = int(parts[1])
                send_message(chat_id, f"✅ *Payment Received Successfully!*\n\nOrder ID: `{order_id}`\nUTR: `{utr}`")
                
    return jsonify({'status': 'ok'}), 200

if __name__ == '__main__':
    app.run(host='0.0.0.0', port=5000)
    
