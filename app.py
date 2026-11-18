import os
import logging
from flask import Flask, request, jsonify
import requests

app = Flask(__name__)

# LOGGING SETUP
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)

# CONFIGURATIONS FROM RENDER ENVIRONMENT VARIABLES
TELEGRAM_TOKEN = os.environ.get("TELEGRAM_BOT_TOKEN")
ZAPUPI_API_KEY = os.environ.get("ZAPUPI_API_KEY")

TELEGRAM_URL = f"https://api.telegram.org/bot{TELEGRAM_TOKEN}/sendMessage"

def send_telegram_message(chat_id, text):
    try:
        requests.post(
            TELEGRAM_URL,
            json={"chat_id": chat_id, "text": text},
            timeout=20
        )
    except Exception:
        logger.exception("Telegram send error")

@app.route("/", methods=["GET"])
def home():
    return "ZapUPI Telegram Payment Bot is running!"

@app.route("/health", methods=["GET"])
def health():
    return jsonify({"status": "online", "bot": "ZapUPI Payment Bot"})

# 1. TELEGRAM WEBHOOK (Handles user messages)
@app.route("/webhook", methods=["POST"])
def telegram_webhook():
    if not TELEGRAM_TOKEN:
        return jsonify({"error": "Bot token missing"}), 500

    try:
        update = request.get_json(silent=True) or {}
        message = update.get("message", {})

        if not message:
            return jsonify({"ok": True})

        chat_id = message.get("chat", {}).get("id")
        text = message.get("text", "").strip()

        if not chat_id or not text:
            return jsonify({"ok": True})

        # Start Command
        if text == "/start":
            send_telegram_message(
                chat_id,
                "Welcome to ZapUPI Payment Bot 🚀\n\n"
                "Please send the amount you want to pay (e.g., 50, 100, 500) to generate your payment link."
            )
            return jsonify({"ok": True})

        # Check if user sent an amount (digits only)
        if text.isdigit():
            amount = text
            
            # ZapUPI API Request to generate payment link
            # Note: Adjust the endpoint URL if ZapUPI documentation specifies a different one
            zapupi_endpoint = "https://panel.zapupi.com/api/create_link" # Replace with exact ZapUPI endpoint if different
            
            payload = {
                "api_key": ZAPUPI_API_KEY,
                "amount": amount,
                "customer_note": str(chat_id) # Passing chat_id in note to track payment later
            }
            
            try:
                zapupi_res = requests.post(zapupi_endpoint, json=payload, timeout=20)
                res_data = zapupi_res.json()
                
                # Assuming ZapUPI returns a payment link in response (e.g., res_data['payment_url'])
                payment_url = res_data.get("payment_url") or res_data.get("link")
                
                if payment_url:
                    send_telegram_message(
                        chat_id, 
                        f"🔗 Payment Link Generated for ₹{amount}:\n{payment_url}\n\n"
                        f"Please complete the payment. We will notify you here once successful!"
                    )
                else:
                    send_telegram_message(chat_id, "Error generating payment link from gateway. Please try again.")
            except Exception:
                logger.exception("ZapUPI API call failed")
                send_telegram_message(chat_id, "Failed to connect to payment gateway. Try again later.")

            return jsonify({"ok": True})

        send_telegram_message(chat_id, "Please send a valid amount in numbers (e.g., 100) to proceed.")
        return jsonify({"ok": True})

    except Exception:
        logger.exception("Telegram webhook error")
        return jsonify({"ok": True})

# 2. ZAPUPI CALLBACK / WEBHOOK (Handles payment success notification from gateway)
@app.route("/zapupi-webhook", methods=["POST"])
def zapupi_callback():
    try:
        data = request.get_json(silent=True) or {}
        logger.info(f"Received ZapUPI webhook data: {data}")
        
        # Extract fields based on ZapUPI callback structure
        status = data.get("status") # e.g., "SUCCESS" or "success"
        amount = data.get("amount")
        chat_id = data.get("customer_note") # Retrieving the chat_id we passed earlier

        if str(status).upper() == "SUCCESS" and chat_id:
            send_telegram_message(
                int(chat_id), 
                f"✅ Payment of ₹{amount} Successful!\nYour account has been credited."
            )

        return jsonify({"status": "received"}), 200
    except Exception:
        logger.exception("ZapUPI callback error")
        return jsonify({"status": "error"}), 500

if __name__ == "__main__":
    port = int(os.environ.get("PORT", 10000))
    app.run(host="0.0.0.0", port=port)
      
