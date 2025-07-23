from flask import Flask, render_template, request, redirect, url_for, session
import re
import base64
import os
import pickle
import time
import logging
import html
from urllib.parse import urlparse
from dotenv import load_dotenv
from datetime import datetime, timedelta
from zoneinfo import ZoneInfo
import pytz
import json
from functools import wraps
from googleapiclient.discovery import build
from google_auth_oauthlib.flow import InstalledAppFlow
from google.oauth2.credentials import Credentials
from google.auth.transport.requests import Request
from googleapiclient.errors import HttpError
from email.mime.text import MIMEText
from email.mime.multipart import MIMEMultipart
import atexit
from apscheduler.schedulers.background import BackgroundScheduler
import tenacity
from selenium import webdriver
from selenium.webdriver.common.by import By
from selenium.webdriver.chrome.service import Service
from webdriver_manager.chrome import ChromeDriverManager
from selenium.webdriver.support.ui import WebDriverWait
from selenium.webdriver.support import expected_conditions as EC
from bs4 import BeautifulSoup
import platform
import hashlib
from supabase import create_client
import sys
from io import StringIO
import requests
import threading
import email.utils

# Import platform-specific modules
if platform.system() == "Windows":
    import msvcrt
else:
    import fcntl

# Load environment variables with enhanced error handling
def load_environment_files():
    """Load environment variables from .env files and verify their presence."""
    if not os.path.exists('supabase.env'):
        logger.error("supabase.env file not found in the project directory.")
        print("❌ Error: supabase.env file not found in the project directory.")
        raise FileNotFoundError("supabase.env file not found")
    if not os.path.exists('credentials.env'):
        logger.error("credentials.env file not found in the project directory.")
        print("❌ Error: credentials.env file not found in the project directory.")
        raise FileNotFoundError("credentials.env file not found")

    load_dotenv('supabase.env')
    load_dotenv('credentials.env')

    # Verify critical environment variables
    required_vars = ['SUPABASE_URL', 'SUPABASE_KEY', 'GOV_USERNAME', 'GOV_PASSWORD']
    missing_vars = [var for var in required_vars if not os.environ.get(var)]
    if missing_vars:
        error_msg = f"Missing environment variables: {', '.join(missing_vars)}"
        logger.error(error_msg)
        print(f"❌ {error_msg}")
        raise ValueError(error_msg)

# Initialize Flask app
app = Flask(__name__)
app.secret_key = os.urandom(24)

# Global log capture system
class LogCapture:
    def __init__(self):
        self.logs = []
        self.original_stdout = sys.stdout
        self.original_stderr = sys.stderr
    
    def write(self, text):
        if text.strip():
            timestamp = datetime.now().strftime('%Y-%m-%d %H:%M:%S')
            log_entry = f"[{timestamp}] {text.strip()}"
            self.logs.append(log_entry)
            if len(self.logs) > 1000:
                self.logs = self.logs[-1000:]
        self.original_stdout.write(text)
    
    def flush(self):
        self.original_stdout.flush()
    
    def get_logs(self):
        return self.logs[-500:]

# Initialize log capture
log_capture = LogCapture()

# Configure logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s',
    filename='app.log',
    filemode='a'
)
logger = logging.getLogger(__name__)

# Redirect stdout to capture print statements
sys.stdout = log_capture

# Load environment variables
load_environment_files()

# Supabase configuration
SUPABASE_URL = os.environ.get("SUPABASE_URL")
SUPABASE_KEY = os.environ.get("SUPABASE_KEY")
supabase = create_client(SUPABASE_URL, SUPABASE_KEY)

# Google API scopes
SCOPES = ['https://www.googleapis.com/auth/gmail.send']
SCOPES_GMAIL_READ = ['https://www.googleapis.com/auth/gmail.readonly']

# Global variables
gmail_service = None
time_interval = 30  # Default interval in hours

# Lock file for alert checks
LOCK_FILE = 'alerts.lock'

def acquire_lock():
    """Acquire a file lock to prevent concurrent alert processing."""
    lock_fd = open(LOCK_FILE, 'w')
    try:
        if platform.system() == "Windows":
            msvcrt.locking(lock_fd.fileno(), msvcrt.LK_NBLCK, 1)
        else:
            fcntl.flock(lock_fd.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
        return lock_fd
    except (IOError, OSError):
        logger.warning("Failed to acquire file lock, another process may be handling alerts")
        lock_fd.close()
        return None

def release_lock(lock_fd):
    """Release the file lock."""
    if lock_fd:
        try:
            if platform.system() == "Windows":
                msvcrt.locking(lock_fd.fileno(), msvcrt.LK_UNLCK, 1)
            else:
                fcntl.flock(lock_fd.fileno(), fcntl.LOCK_UN)
            lock_fd.close()
            os.remove(LOCK_FILE)
            logger.info("File lock released")
        except (IOError, OSError) as e:
            logger.error(f"Failed to release lock: {e}")

def retry_on_transient_error(max_attempts=3, backoff_factor=2):
    def decorator(func):
        @wraps(func)
        def wrapper(*args, **kwargs):
            attempts = 0
            while attempts < max_attempts:
                try:
                    return func(*args, **kwargs)
                except HttpError as e:
                    transient_codes = {429, 500, 502, 503, 504}
                    if e.resp.status not in transient_codes:
                        raise
                    attempts += 1
                    if attempts == max_attempts:
                        logger.error(f"Max retries ({max_attempts}) reached for {func.__name__}: {e}")
                        raise
                    sleep_time = backoff_factor * (2 ** (attempts - 1))
                    logger.warning(f"Transient error {e.resp.status} in {func.__name__}, retrying in {sleep_time}s (attempt {attempts}/{max_attempts})")
                    time.sleep(sleep_time)
                except ConnectionError as e:
                    attempts += 1
                    if attempts == max_attempts:
                        logger.error(f"Max retries ({max_attempts}) reached for {func.__name__}: {e}")
                        raise
                    sleep_time = backoff_factor * (2 ** (attempts - 1))
                    logger.warning(f"Connection error in {func.__name__}, retrying in {sleep_time}s (attempt {attempts}/{max_attempts})")
                    time.sleep(sleep_time)
            return func(*args, **kwargs)
        return wrapper
    return decorator

def authenticate_google():
    """Authenticate with Google API and return Gmail service for sending emails."""
    global gmail_service
    logger.debug("Attempting to authenticate Google API for sending emails")
    creds = None
    token_path = 'token.json'
    
    if os.path.exists(token_path):
        try:
            with open(token_path, 'r') as token:
                creds = Credentials.from_authorized_user_file(token_path, SCOPES)
                logger.debug("Loaded existing token for sending emails")
        except Exception as e:
            logger.error(f"Error reading token file {token_path}: {e}")
            os.remove(token_path)
            creds = None

    if not creds or not creds.valid:
        if creds and creds.expired and creds.refresh_token:
            try:
                creds.refresh(Request())
                logger.debug("Refreshed expired token for sending emails")
            except Exception as e:
                logger.error(f"Failed to refresh token: {e}")
                creds = None
        if not creds:
            try:
                logger.debug("Initiating new authentication flow for sending emails")
                flow = InstalledAppFlow.from_client_secrets_file('client.json', SCOPES)
                creds = flow.run_local_server(port=0, access_type='offline', prompt='consent')
                with open(token_path, 'w') as token:
                    token.write(creds.to_json())
                logger.debug("Saved new token for sending emails")
            except FileNotFoundError:
                logger.error("client.json not found. Please ensure it exists in the project directory.")
                raise FileNotFoundError("client.json not found")
            except Exception as e:
                logger.error(f"Authentication flow failed for sending emails: {e}")
                raise Exception(f"Authentication flow failed: {e}")

    try:
        gmail_service = build('gmail', 'v1', credentials=creds)
        logger.debug("Google API authentication successful for sending emails")
        return gmail_service
    except Exception as e:
        logger.error(f"Failed to build Gmail service for sending emails: {e}")
        raise Exception(f"Failed to build Gmail service: {e}")

def authenticate_gmail_read(scopes, token_file):
    """Authenticate with Google API for read-only access and return Gmail service."""
    logger.debug(f"Attempting to authenticate Google API for read-only access with token file {token_file}")
    creds = None
    
    if os.path.exists(token_file):
        try:
            with open(token_file, 'r') as token:
                creds = Credentials.from_authorized_user_file(token_file, scopes)
                logger.debug(f"Loaded existing token from {token_file}")
        except Exception as e:
            logger.error(f"Error reading token file {token_file}: {e}")
            os.remove(token_file)
            creds = None

    if not creds or not creds.valid:
        if creds and creds.expired and creds.refresh_token:
            try:
                creds.refresh(Request())
                logger.debug(f"Refreshed expired token from {token_file}")
            except Exception as e:
                logger.error(f"Failed to refresh token from {token_file}: {e}")
                creds = None
        if not creds:
            try:
                logger.debug(f"Initiating new authentication flow for {token_file}")
                flow = InstalledAppFlow.from_client_secrets_file('client.json', scopes)
                creds = flow.run_local_server(port=0, access_type='offline', prompt='consent')
                with open(token_file, 'w') as token:
                    token.write(creds.to_json())
                logger.debug(f"Saved new token to {token_file}")
            except FileNotFoundError:
                logger.error("client.json not found. Please ensure it exists in the project directory.")
                raise FileNotFoundError("client.json not found")
            except Exception as e:
                logger.error(f"Authentication flow failed for read-only access: {e}")
                raise Exception(f"Authentication flow failed: {e}")

    try:
        service = build('gmail', 'v1', credentials=creds)
        logger.debug("Google API authentication successful for read-only access")
        return service
    except Exception as e:
        logger.error(f"Failed to build Gmail service for read-only access: {e}")
        raise Exception(f"Failed to build Gmail service: {e}")

def get_due_rfps(filter_option):
    """Fetch RFPs based on the filter option."""
    try:
        response = supabase.table('rfpproject').select('*').execute()
        rfps = response.data or []
        logger.info(f"Fetched {len(rfps)} RFPs from rfpproject table")
        print(f"📊 Fetched {len(rfps)} RFPs from rfpproject table")
        
        current_date = datetime.now(ZoneInfo('Asia/Kolkata')).date()
        filtered_rfps = []
        
        for rfp in rfps:
            formatted_date = rfp.get('formatted_date')
            if not formatted_date or formatted_date == 'NOT AVAILABLE':
                logger.warning(f"Skipping RFP with missing or invalid formatted_date: {rfp.get('subject', 'N/A')}")
                print(f"⚠️ Skipping RFP with missing or invalid formatted_date: {rfp.get('subject', 'N/A')}")
                continue
            try:
                rfp_date = datetime.strptime(formatted_date, '%Y-%m-%d').date()
                if filter_option == 'Due Today' and rfp_date == current_date:
                    filtered_rfps.append(rfp)
                elif filter_option == 'Due Within 3 Days' and current_date <= rfp_date <= current_date + timedelta(days=2):
                    filtered_rfps.append(rfp)
                elif filter_option == 'Due This Week' and current_date <= rfp_date <= current_date + timedelta(days=6):
                    filtered_rfps.append(rfp)
                elif filter_option == 'All RFPs':
                    filtered_rfps.append(rfp)
            except ValueError as e:
                logger.warning(f"Invalid date format for RFP {rfp.get('subject', 'N/A')}: {formatted_date}, error: {e}")
                print(f"⚠️ Invalid date format for RFP {rfp.get('subject', 'N/A')}: {formatted_date}, error: {e}")
                continue

        if not filtered_rfps and filter_option != 'All RFPs':
            logger.info(f"No RFPs found for {filter_option}, falling back to all RFPs with valid dates")
            print(f"⚠️ No RFPs found for {filter_option}, falling back to all RFPs with valid dates")
            filtered_rfps = [rfp for rfp in rfps if rfp.get('formatted_date') and rfp.get('formatted_date') != 'NOT AVAILABLE']

        logger.info(f"Returning {len(filtered_rfps)} RFPs for filter {filter_option}")
        print(f"✅ Returning {len(filtered_rfps)} RFPs for filter {filter_option}")
        return filtered_rfps
    except Exception as e:
        logger.error(f"Error fetching due RFPs: {e}")
        print(f"❌ Error fetching due RFPs: {e}")
        return []

def send_email(recipient, subject, html_body):
    """Send an email using Gmail API."""
    message = MIMEText(html_body, 'html')
    message['to'] = recipient
    message['from'] = "rfp@iitlabs.com"
    message['subject'] = subject
    raw_message = base64.urlsafe_b64encode(message.as_bytes()).decode()
    message = {'raw': raw_message}
    
    try:
        service = authenticate_google()
        sent_message = service.users().messages().send(userId='me', body=message).execute()
        logger.info(f"Email sent successfully to {recipient}, Message ID: {sent_message['id']}")
        return True, "Email sent successfully"
    except Exception as e:
        logger.error(f"Failed to send email: {e}")
        return False, f"Failed to send email: {e}"

def check_and_send_alerts():
    """Check for scheduled alerts and send emails."""
    print("🔔 Starting alert check...")
    logger.info("Starting alert check")
    
    lock_fd = acquire_lock()
    if not lock_fd:
        print("⚠️ Failed to acquire file lock, another process may be handling alerts")
        logger.warning("Failed to acquire file lock, skipping alert check")
        return
    
    try:
        print("📊 Fetching alerts from database...")
        response = supabase.table('time').select('*').execute()
        alerts = response.data or []
        print(f"📋 Retrieved {len(alerts)} alerts")
        logger.info(f"Retrieved {len(alerts)} alerts")
        
        current_time = datetime.now(pytz.UTC)
        for alert in alerts:
            recipient = alert.get('recipient_email')
            alert_time = alert.get('alert_time')
            timezone = alert.get('timezone', 'UTC')
            
            try:
                alert_tz = pytz.timezone(timezone)
                current_time_in_tz = current_time.astimezone(alert_tz)
                alert_hour, alert_minute = map(int, alert_time.split(':'))
                
                if (current_time_in_tz.hour == alert_hour and 
                    current_time_in_tz.minute >= alert_minute and 
                    current_time_in_tz.minute < alert_minute + 5):
                    print(f"⏰ Sending alert to {recipient} for time {alert_time} in {timezone}")
                    logger.info(f"Sending alert to {recipient} for time {alert_time} in {timezone}")
                    
                    filter_option = 'Due Within 3 Days'
                    due_rfps = get_due_rfps(filter_option)
                    print(f"📊 Fetched {len(due_rfps)} RFPs for {filter_option}")
                    logger.debug(f"Fetched {len(due_rfps)} RFPs for {filter_option}")
                    
                    if due_rfps:
                        subject = f"RFPs {filter_option}"
                        html_body = f"""
<!DOCTYPE html>
<html>
<head>
    <title>{subject}</title>
    <style>
        body {{ font-family: Arial, sans-serif; margin: 0; padding: 0; background-color: #f4f4f4; }}
        .header {{ background-color: #f8f9fa; padding: 10px; text-align: center; border-bottom: 1px solid #ddd; }}
        table {{ width: 100%; border-collapse: collapse; margin-top: 20px; background-color: #fff; }}
        th, td {{ border: 1px solid #ddd; padding: 8px; text-align: left; }}
        th {{ background-color: #f2f2f2; font-weight: bold; }}
        td a {{ color: #007bff; text-decoration: none; }}
        td a:hover {{ text-decoration: underline; }}
        .footer {{ text-align: right; font-size: 12px; color: #6c757d; margin-top: 20px; }}
    </style>
</head>
<body>
    <div class="header">
        <h2>RFP Opportunities {filter_option}</h2>
    </div>
    <table>
        <tr>
            <th>Subject</th>
            <th>Online Link</th>
            <th>Due Date</th>
            <th>Agency</th>
            <th>Reference</th>
            <th>Contact</th>
        </tr>
"""
                        for rfp in due_rfps:
                            html_body += f"""
        <tr>
            <td>{rfp.get('subject', 'N/A')}</td>
            <td><a href="{rfp.get('online_link', '#')}">Link</a></td>
            <td>{rfp.get('formatted_date', 'N/A')}</td>
            <td>{rfp.get('agency', 'N/A')}</td>
            <td>{rfp.get('reference', 'N/A')}</td>
            <td>{rfp.get('contact', 'N/A')}</td>
        </tr>
"""
                        html_body += f"""
    </table>
    <div class="footer">
        Last updated: {datetime.now(ZoneInfo('Asia/Kolkata')).strftime('%m/%d/%Y, %I:%M:%S %p')} IST
    </div>
</body>
</html>
"""
                        success, message = send_email(recipient, subject, html_body)
                        if success:
                            print(f"✅ Sent alert email to {recipient}")
                            logger.info(f"Sent alert email to {recipient}")
                        else:
                            print(f"❌ Failed to send alert email to {recipient}: {message}")
                            logger.error(f"Failed to send alert email to {recipient}: {message}")
            except Exception as e:
                print(f"❌ Error processing alert for {recipient}: {e}")
                logger.error(f"Error processing alert for {recipient}: {e}")
    finally:
        release_lock(lock_fd)

def start_scheduler():
    """Start the background scheduler for alerts."""
    scheduler = BackgroundScheduler()
    scheduler.add_job(check_and_send_alerts, 'interval', minutes=5)
    scheduler.start()
    atexit.register(lambda: scheduler.shutdown())
    print("📅 Scheduler started, checking alerts every 5 minutes")
    logger.info("Scheduler started, checking alerts every 5 minutes")

def setup_driver():
    """Set up Selenium WebDriver with enhanced options."""
    options = webdriver.ChromeOptions()
    options.add_argument("--headless")
    options.add_argument("--no-sandbox")
    options.add_argument("--disable-dev-shm-usage")
    options.add_argument("--ignore-certificate-errors")
    options.add_argument("--disable-notifications")
    options.add_argument("--disable-gpu")
    options.add_argument("--window-size=1920,1080")
    try:
        driver = webdriver.Chrome(service=Service(ChromeDriverManager().install()), options=options)
        logger.info("WebDriver initialized successfully")
        return driver
    except Exception as e:
        print(f"❌ Failed to initialize WebDriver: {e}")
        logger.error(f"Failed to initialize WebDriver: {e}")
        return None

@retry_on_transient_error(max_attempts=5)
def list_daily_bids_emails(service):
    """List emails from Daily Bids that arrived since the last processed email and extract URLs."""
    try:
        if not hasattr(service, 'users') or not callable(service.users):
            raise ValueError("Invalid Gmail service object")

        messages = []
        next_page_token = None
        total_emails_processed = 0
        skipped_count = 0
        all_opportunities = []

        # Load last processed timestamp
        last_processed_time = None
        last_processed_file = 'last_processed_time.pickle'
        if os.path.exists(last_processed_file):
            with open(last_processed_file, 'rb') as f:
                last_processed_time = pickle.load(f)
                logger.info(f"Loaded last processed timestamp: {last_processed_time}")
                print(f"📅 Loaded last processed timestamp: {last_processed_time}")
        else:
            # Default to 24 hours ago for first run
            last_processed_time = datetime.now(pytz.UTC) - timedelta(hours=24)
            logger.info(f"No last processed timestamp found, defaulting to 24 hours ago: {last_processed_time}")
            print(f"📅 No last processed timestamp found, defaulting to 24 hours ago: {last_processed_time}")

        # Convert last processed time to Gmail query format (epoch seconds)
        after_timestamp = int(last_processed_time.timestamp())
        query = f"govdirections.com after:{after_timestamp}"

        # Track the newest email timestamp
        newest_timestamp = last_processed_time

        # Fetch message IDs with timestamp filter
        def fetch_messages(page_token):
            return service.users().messages().list(
                userId='me',
                q=query,
                maxResults=1000,
                pageToken=page_token
            ).execute()

        while True:
            try:
                result = fetch_messages(next_page_token)
                messages.extend(result.get('messages', []))
                next_page_token = result.get('nextPageToken')
                logger.info(f"Fetched {len(result.get('messages', []))} messages. Next page token: {next_page_token}")
                print(f"📩 Fetched {len(result.get('messages', []))} messages. Next page token: {next_page_token}")
                if not next_page_token:
                    break
            except HttpError as e:
                if e.resp.status == 429:
                    logger.error(f"Quota exceeded: {e}")
                    print(f"❌ Error: Gmail API quota exceeded: {e}. Try again later or increase quota in Google Cloud Console.")
                    return [], last_processed_time
                raise

        print(f"📩 Total Emails Found: {len(messages)}")
        logger.info(f"Total Emails Found: {len(messages)}")

        # Process messages in batches
        message_data_dict = {}
        batch_requests = 0

        def batch_callback(request_id, response, exception):
            nonlocal skipped_count
            if exception is not None:
                skipped_count += 1
                message_data_dict[request_id] = {
                    'error': f"Batch request error: {str(exception)}"
                }
                logger.error(f"Error processing email {request_id}: {str(exception)}")
                print(f"❌ Error processing email {request_id}: {str(exception)}")
            else:
                message_data_dict[request_id] = response

        batch = service.new_batch_http_request(callback=batch_callback)
        for msg in messages:
            batch.add(
                service.users().messages().get(
                    userId='me',
                    id=msg['id'],
                    format='full'
                ),
                request_id=msg['id']
            )
            batch_requests += 1
            if batch_requests >= 100:
                batch.execute()
                batch = service.new_batch_http_request(callback=batch_callback)
                batch_requests = 0
        if batch_requests > 0:
            batch.execute()

        unique_urls = set()
        for i, msg in enumerate(messages, 1):
            print(f"🔍 Processing email {i}/{len(messages)}...", end="", flush=True)
            msg_data = message_data_dict.get(msg['id'], {})
            if 'error' in msg_data:
                skipped_count += 1
                continue

            # Extract email timestamp
            headers = msg_data.get('payload', {}).get('headers', [])
            email_date = None
            for header in headers:
                if header.get('name', '').lower() == 'date':
                    email_date = header.get('value')
                    break
            if email_date:
                try:
                    parsed_date = email.utils.parsedate_to_datetime(email_date)
                    if parsed_date:
                        if parsed_date.tzinfo is None:
                            parsed_date = parsed_date.replace(tzinfo=pytz.UTC)
                        if parsed_date > newest_timestamp:
                            newest_timestamp = parsed_date
                except Exception as e:
                    logger.warning(f"Failed to parse email date for message {msg['id']}: {e}")
                    print(f"⚠️ Failed to parse email date for message {msg['id']}: {e}")

            payload = msg_data.get('payload', {})
            parts = payload.get('parts', [])
            email_content = ""

            for part in parts:
                if part.get('mimeType') == 'text/html':
                    data = part.get('body', {}).get('data', '')
                    if data:
                        try:
                            html_content = base64.urlsafe_b64decode(data).decode('utf-8', errors='ignore')
                            email_content += html_content
                        except Exception as e:
                            logger.error(f"Error decoding HTML part for email {msg['id']}: {e}")
                            print(f"⚠️ Error decoding HTML part for email {msg['id']}: {e}")
                            continue
                elif part.get('mimeType') == 'text/plain':
                    data = part.get('body', {}).get('data', '')
                    if data:
                        try:
                            plain_content = base64.urlsafe_b64decode(data).decode('utf-8', errors='ignore')
                            email_content += plain_content
                        except Exception as e:
                            logger.error(f"Error decoding plain text part for email {msg['id']}: {e}")
                            print(f"⚠️ Error decoding plain text part for email {msg['id']}: {e}")
                            continue

            logger.debug(f"Email content snippet (ID: {msg['id']}): {email_content[:500]}...")
            soup = BeautifulSoup(email_content, 'html.parser')
            links = soup.find_all('a', href=True)
            for link in links:
                href = link['href']
                if 'govdirections.com' in href and '/bids/view/' in href:
                    unique_urls.add(href)
                    logger.debug(f"Found URL via BeautifulSoup: {href}")

            url_pattern = re.compile(r'https?://(?:[-\w.]|(?:%[\da-fA-F]{2}))+[govdirections.com][/\w .-]*/bids/view/\d+')
            urls = url_pattern.findall(email_content)
            for url in urls:
                unique_urls.add(url)
                logger.debug(f"Found URL via regex: {url}")

        print("\n📊 EMAIL PROCESSING RESULTS:")
        print(f"Total emails processed: {len(messages)}")
        print(f"Emails skipped due to errors: {skipped_count}")
        print(f"Unique URLs found: {len(unique_urls)}")
        logger.info(f"EMAIL PROCESSING RESULTS: Total emails processed: {len(messages)}, Skipped: {skipped_count}, Unique URLs: {len(unique_urls)}")

        if not unique_urls:
            logger.warning("No bid URLs extracted from emails")
            print("⚠️ No bid URLs extracted from emails")
        else:
            logger.info(f"Extracted {len(unique_urls)} unique bid URLs")

        return list(unique_urls), newest_timestamp
    except Exception as e:
        print(f"❌ Error listing emails: {e}")
        logger.error(f"Error listing emails: {e}")
        return [], last_processed_time

@tenacity.retry(
    stop=tenacity.stop_after_attempt(3),
    wait=tenacity.wait_fixed(2),
    retry=tenacity.retry_if_exception_type(Exception),
    before_sleep=lambda retry_state: logger.warning(f"Retrying login attempt {retry_state.attempt_number}...")
)
def login_to_govdirections(driver, url, is_first_login=False):
    """Attempt login to govdirections.com with session persistence."""
    username = os.environ.get('GOV_USERNAME')
    password = os.environ.get('GOV_PASSWORD')

    if not username or not password:
        error_msg = "GOV_USERNAME or GOV_PASSWORD not found in credentials.env"
        print(f"❌ {error_msg}")
        logger.error(error_msg)
        raise ValueError(error_msg)

    if not is_first_login:
        try:
            driver.get(url)
            WebDriverWait(driver, 20).until(
                EC.presence_of_element_located((By.XPATH, "//*[contains(text(), 'Event Date') or contains(text(), 'Agency Sponsor')]"))
            )
            logger.info("Session still active, no login required")
            print("✅ Session still active, no login required")
            return True
        except:
            logger.info("Session expired or invalid, attempting login")
            print("⚠️ Session expired or invalid, attempting login")

    try:
        driver.get("https://govdirections.com/users/login")
        logger.info(f"Navigated to login page: https://govdirections.com/users/login")
        print(f"🌐 Navigated to login page: https://govdirections.com/users/login")
        
        WebDriverWait(driver, 30).until(
            EC.presence_of_element_located((By.TAG_NAME, "body"))
        )
        time.sleep(2)

        email_locators = [
            (By.NAME, "data[User][email]"),
            (By.CSS_SELECTOR, "input[name*='email'], input[id*='email'], input[type='email']"),
            (By.XPATH, "//input[contains(@name, 'email') or contains(@id, 'email') or @type='email']")
        ]
        email_field = None
        for locator_type, locator_value in email_locators:
            try:
                email_field = WebDriverWait(driver, 20).until(
                    EC.presence_of_element_located((locator_type, locator_value))
                )
                if email_field:
                    break
            except:
                continue

        if not email_field:
            driver.save_screenshot("email_field_failure.png")
            logger.error("All email locators failed")
            print(f"❌ Failed to locate email field")
            raise Exception("Failed to locate email field")

        email_field.clear()
        email_field.send_keys(username)
        logger.info("Entered username")
        print("✍️ Entered username")

        password_locators = [
            (By.NAME, "data[User][passwd]"),
            (By.CSS_SELECTOR, "input[name*='pass'], input[id*='pass'], input[type='password']"),
            (By.XPATH, "//input[contains(@name, 'pass') or contains(@id, 'pass') or @type='password']")
        ]
        password_field = None
        for locator_type, locator_value in password_locators:
            try:
                password_field = WebDriverWait(driver, 20).until(
                    EC.presence_of_element_located((locator_type, locator_value))
                )
                if password_field:
                    break
            except:
                continue

        if not password_field:
            driver.save_screenshot("password_field_failure.png")
            logger.error("All password locators failed")
            print(f"❌ Failed to locate password field")
            raise Exception("Failed to locate password field")

        password_field.clear()
        password_field.send_keys(password)
        logger.info("Entered password")
        print("🔑 Entered password")

        login_locators = [
            (By.XPATH, "//input[contains(translate(@value, 'ABCDEFGHIJKLMNOPQRSTUVWXYZ', 'abcdefghijklmnopqrstuvwxyz'), 'log in')]"),
            (By.CSS_SELECTOR, "input[type='submit'], button[type='submit'], input[value*='Log'], button[contains(text(), 'Log')]"),
            (By.XPATH, "//button[contains(text(), 'Login') or contains(text(), 'Sign In')]")
        ]
        login_button = None
        for locator_type, locator_value in login_locators:
            try:
                login_button = WebDriverWait(driver, 20).until(
                    EC.element_to_be_clickable((locator_type, locator_value))
                )
                if login_button:
                    break
            except:
                continue

        if not login_button:
            driver.save_screenshot("login_button_failure.png")
            logger.error("All login button locators failed")
            print(f"❌ Failed to locate login button")
            raise Exception("Failed to locate login button")

        login_button.click()
        logger.info("Clicked login button")
        print("✅ Clicked login button")

        try:
            captcha = WebDriverWait(driver, 10).until(
                EC.presence_of_element_located((By.CSS_SELECTOR, "div.g-recaptcha, iframe[src*='captcha']"))
            )
            if captcha:
                logger.error("CAPTCHA detected, automated login not possible")
                driver.save_screenshot("captcha_detected.png")
                print("❌ CAPTCHA detected on login page")
                raise Exception("CAPTCHA detected on login page")
        except:
            pass

        driver.get(url)
        WebDriverWait(driver, 20).until(
            EC.presence_of_element_located((By.XPATH, "//*[contains(text(), 'Event Date') or contains(text(), 'Agency Sponsor')]"))
        )
        logger.info("Login successful and bid content page loaded")
        print("✅ Login successful and bid content page loaded")
        return True

    except Exception as e:
        page_source = driver.page_source
        logger.error(f"Login failed: {e}\nPage source: {page_source[:1000]}...")
        print(f"❌ Login failed: {e}")
        try:
            driver.save_screenshot("login_failure.png")
            logger.info("Saved screenshot as login_failure.png")
            print("📸 Saved screenshot as login_failure.png")
        except Exception as screenshot_error:
            logger.error(f"Failed to save screenshot: {screenshot_error}")
            print(f"❌ Failed to save screenshot: {screenshot_error}")
        raise Exception(f"Login failed: {e}")

def extract_opportunity_details(driver, url):
    """Extract information from the bid details page."""
    try:
        driver.get(url)
        current_url = driver.current_url
        logger.info(f"Extracting details from URL: {current_url}")
        print(f"🔍 Extracting details from URL: {current_url}")
        
        WebDriverWait(driver, 10).until(
            EC.presence_of_element_located((By.CSS_SELECTOR, "body"))
        )
        soup = BeautifulSoup(driver.page_source, 'html.parser')

        with open('page_source.html', 'w', encoding='utf-8') as f:
            f.write(driver.page_source)
        logger.info("Page source saved to page_source.html")
        print("📝 Page source saved to page_source.html")

        details = {}

        def clean_text(text):
            return html.unescape(text.strip()) if text else "Not Available"

        title_element = soup.select_one('h1') or soup.select_one('h2')
        details['title'] = clean_text(title_element.get_text()) if title_element else "Not Available"

        view_link = soup.find('a', string=re.compile(r'view all.*opportunities', re.I))
        details['view_link'] = view_link['href'] if view_link and 'href' in view_link.attrs else "Not Available"

        doc_link = None
        if_online_text = soup.find(string=re.compile(r'If online, then documents are here:', re.I))
        if if_online_text:
            next_sibling = if_online_text.find_next(string=True)
            if next_sibling and 'http' in next_sibling:
                doc_link = re.search(r'https?://[^\s]+', next_sibling).group(0)

        if not doc_link:
            url_pattern = re.compile(r'https?://(?:[-\w.]|(?:%[\da-fA-F]{2}))+[/\w .-]*/?')
            url_match = url_pattern.search(soup.get_text())
            if url_match:
                doc_link = url_match.group(0)

        details['document_link'] = doc_link if doc_link else "Not Available"

        event_date_label = soup.find('dt', string=re.compile(r'event\s*date', re.I))
        if event_date_label:
            next_dd = event_date_label.find_next('dd')
            details['event_date'] = clean_text(next_dd.get_text()) if next_dd else "Not Available"
        else:
            date_match = re.search(r'(Mon|Tue|Wed|Thu|Fri|Sat|Sun),?\s+\w+\s+\d{1,2}(?:st|nd|rd|th)?\s+\d{4}', soup.get_text())
            details['event_date'] = date_match.group(0) if date_match else "Not Available"

        agency_label = soup.find('dt', string=re.compile(r'agency\s*sponsor', re.I))
        if agency_label:
            next_dd = agency_label.find_next('dd')
            details['agency_sponsor'] = clean_text(next_dd.get_text()) if next_dd else "Not Available"
        else:
            agency_match = re.search(r'The agency sponsor is:\s*(.*?)(?=\n|$)', soup.get_text())
            details['agency_sponsor'] = agency_match.group(1).strip() if agency_match else "Not Available"

        reference_label = soup.find('dt', string=re.compile(r'reference|id\s*number|solicitation\s*number', re.I))
        if reference_label:
            next_dd = reference_label.find_next('dd')
            details['reference'] = clean_text(next_dd.get_text()) if next_dd else "Not Available"
        else:
            ref_match = re.search(r'The reference for this notice \(if available\):\s*(.*?)(?=\n|$)', soup.get_text())
            details['reference'] = ref_match.group(1).strip() if ref_match else "Not Available"

        contact_label = soup.find('dt', string=re.compile(r'contact\s*(information|info)', re.I))
        if contact_label:
            contact_dd = contact_label.find_next('dd')
            if contact_dd:
                contact_text = clean_text(contact_dd.get_text(separator=' '))
                phone_match = re.search(r'\(?\d{3}\)?[-.\s]?\d{3}[-.\s]?\d{4}', contact_text)
                details['contact_phone'] = phone_match.group(0) if phone_match else "Not Available"
                email_match = re.search(r'[a-zA-Z0-9._%+-]+@[a-zA-Z0-9.-]+\.[a-zA-Z]{2,}', contact_text)
                details['contact_email'] = email_match.group(0) if email_match else "Not Available"
                next_dd = contact_dd.find_next('dd')
                details['contact_dept'] = clean_text(next_dd.get_text()) if next_dd else "Not Available"
                details['contact_name'] = "Not Available"
        else:
            contact_text = soup.get_text()
            phone_match = re.search(r'\(?\d{3}\)?[-.\s]?\d{3}[-.\s]?\d{4}', contact_text)
            details['contact_phone'] = phone_match.group(0) if phone_match else "Not Available"
            email_match = re.search(r'[a-zA-Z0-9._%+-]+@[a-zA-Z0-9.-]+\.[a-zA-Z]{2,}', contact_text)
            details['contact_email'] = email_match.group(0) if email_match else "Not Available"
            dept_match = re.search(r'Agency Contact Information:\s*(.*?)(?=\n|$)', contact_text)
            details['contact_dept'] = dept_match.group(1).strip() if dept_match else "Not Available"
            details['contact_name'] = "Not Available"

        print("\nExtracted Opportunity Details:")
        print("=" * 50)
        for key, value in details.items():
            print(f"{key.replace('_', ' ').title()}: {value}")
        print("=" * 50)
        logger.info(f"Extracted Opportunity Details: {details}")

        if all(value == "Not Available" for key, value in details.items() if key != 'document_link'):
            logger.warning("No meaningful data extracted")
            print("⚠️ No meaningful data extracted")
            return None

        return details
    except Exception as e:
        print(f"❌ Error extracting details: {e}")
        logger.error(f"Error extracting details: {e}")
        return None

@retry_on_transient_error()
def send_automation_email(details):
    """Send email with formatted details using Gmail API."""
    sender_email = "rfp@iitlabs.com"
    to_email = "rfp@iitlabs.com"
    subject = f"{details.get('title', 'Opportunity Details')}"

    email_body = f"""
<html>
  <body style="font-family: Arial, sans-serif;">
    <div style="background-color: #E6F3FA; padding: 10px; margin-bottom: 10px;">
      <p>The RFP: Learn to Read and Respond to a Request for Proposal - Available at Amazon</p>
    </div>
    <div style="background-color: #F5F5F5; padding: 10px; margin-bottom: 10px;">
      <h2>{details.get('title', 'Not Available')}</h2>
      <p><strong>★ Capture this Bid</strong></p>
      <p><a href="{details.get('view_link', 'Not Available')}">View all of your Captured Opportunities</a></p>
      <p>If online, then documents are here: <a href="{details.get('document_link', 'Not Available')}">{details.get('document_link', 'Not Available')}</a></p>
      <p><strong>Event Date:</strong> {details.get('event_date', 'Not Available')}</p>
      <p><strong>The agency sponsor is:</strong> {details.get('agency_sponsor', 'Not Available')}</p>
      <p><strong>The reference for this notice (if available):</strong> {details.get('reference', 'Not Available')}</p>
      <p><strong>Agency Contact Information:</strong></p>
      <p>☎ {details.get('contact_phone', 'Not Available')}</p>
      <p>{details.get('contact_dept', 'Not Available')}</p>
      <p>{details.get('contact_email', 'Not Available')}</p>
      <p><a href="#">Learn to Do Business with this Agency</a></p>
    </div>
  </body>
</html>
"""

    message = MIMEText(email_body, 'html')
    message['to'] = to_email
    message['from'] = sender_email
    message['subject'] = subject

    raw_message = base64.urlsafe_b64encode(message.as_bytes()).decode()
    message = {'raw': raw_message}

    try:
        service = authenticate_google()
        sent_message = service.users().messages().send(userId='me', body=message).execute()
        logger.info(f"Email sent successfully to {to_email}, Message ID: {sent_message['id']}")
        print(f"✅ Email sent successfully to {to_email}, Message ID: {sent_message['id']}")
        return True, "Email sent successfully"
    except Exception as e:
        print(f"❌ Failed to send email: {e}")
        logger.error(f"Failed to send email: {e}")
        return False, f"Failed to send email: {e}"

@tenacity.retry(
    stop=tenacity.stop_after_attempt(3),
    wait=tenacity.wait_fixed(5),
    retry=tenacity.retry_if_exception_type(requests.RequestException),
    before_sleep=lambda retry_state: logger.warning(f"Retrying URL validation attempt {retry_state.attempt_number}...")
)
def validate_url(url):
    """Validate URL with retry logic."""
    try:
        response = requests.head(url, timeout=10, allow_redirects=True, verify=True)
        if response.status_code == 200:
            return True
        logger.warning(f"Invalid or inaccessible URL: {url} (Status: {response.status_code})")
        print(f"⚠️ Invalid or inaccessible URL: {url} (Status: {response.status_code})")
        return False
    except requests.exceptions.RequestException as e:
        logger.error(f"Failed to validate URL {url}: {e}")
        print(f"❌ Failed to validate URL {url}: {e}")
        raise

def process_daily_bids(interval_minutes=None):
    """Process Daily Bids emails and extract opportunities with configurable interval in minutes."""
    global time_interval
    if interval_minutes is not None:
        if isinstance(interval_minutes, int) and interval_minutes > 0:
            time_interval = interval_minutes / 60.0
            print(f"⏰ Using mail automation interval of {interval_minutes} minutes ({time_interval} hours)")
            logger.info(f"Using mail automation interval of {interval_minutes} minutes ({time_interval} hours)")
        elif isinstance(interval_minutes, str):
            try:
                if interval_minutes.endswith('m'):
                    minutes = int(interval_minutes[:-1])
                    if minutes > 0:
                        time_interval = minutes / 60.0
                        print(f"⏰ Using mail automation interval of {minutes} minutes ({time_interval} hours)")
                        logger.info(f"Using mail automation interval of {minutes} minutes ({time_interval} hours)")
                elif interval_minutes.endswith('h'):
                    hours = int(interval_minutes[:-1])
                    if hours > 0:
                        time_interval = hours
                        print(f"⏰ Using mail automation interval of {hours} hours")
                        logger.info(f"Using mail automation interval of {hours} hours")
            except ValueError:
                print(f"⚠️ Invalid interval format: {interval_minutes}, using default {time_interval} hours")
                logger.warning(f"Invalid interval format: {interval_minutes}, using default {time_interval} hours")
    else:
        print(f"⏰ Using default mail automation interval of {time_interval} hours")
        logger.info(f"Using default mail automation interval of {time_interval} hours")

    driver = None
    try:
        gmail_service = authenticate_gmail_read(SCOPES_GMAIL_READ, 'token_read.json')
        if not gmail_service:
            print("❌ Failed to authenticate Gmail API for reading")
            logger.error("Failed to authenticate Gmail API for reading")
            return None, "Failed to authenticate Gmail API for reading"

        unique_urls, newest_timestamp = list_daily_bids_emails(gmail_service)
        if not unique_urls:
            print("⚠️ No new bid opportunity URLs found in Gmail.")
            logger.warning("No new bid opportunity URLs found in Gmail.")
            return [], "No new bid opportunity URLs found in Gmail."

        valid_urls = []
        for url in unique_urls:
            try:
                if validate_url(url):
                    valid_urls.append(url)
            except Exception as e:
                logger.error(f"Skipping URL {url} after retries: {e}")
                print(f"⚠️ Skipping URL {url} after retries: {e}")
                continue
        print(f"✅ Validated {len(valid_urls)} URLs")
        logger.info(f"Validated {len(valid_urls)} URLs")

        driver = setup_driver()
        if not driver:
            return None, "Failed to initialize WebDriver"

        processed_urls = set()
        if os.path.exists('processed_urls.pickle'):
            with open('processed_urls.pickle', 'rb') as f:
                processed_urls = pickle.load(f)
                print(f"📋 Loaded {len(processed_urls)} processed URLs")
                logger.info(f"Loaded {len(processed_urls)} processed URLs")

        opportunities = []
        duplicate_count = 0
        login_successful = False

        for i, url in enumerate(valid_urls, 1):
            if url in processed_urls:
                duplicate_count += 1
                print(f"⚠️ Duplicate opportunity for URL {url}")
                logger.info(f"Skipping already processed URL: {url}")
                continue

            print(f"🔍 Processing URL {i}/{len(valid_urls)}: {url}")
            try:
                if login_to_govdirections(driver, url, is_first_login=not login_successful):
                    login_successful = True
                    details = extract_opportunity_details(driver, url)
                    if details:
                        success, message = send_automation_email(details)
                        if success:
                            processed_urls.add(url)
                            opportunities.append({
                                'subject': details.get('title', 'Not Available'),
                                'online_link': details.get('document_link', 'Not Available'),
                                'formatted_date': details.get('event_date', 'Not Available'),
                                'agency': details.get('agency_sponsor', 'Not Available'),
                                'reference': details.get('reference', 'Not Available'),
                                'contact': details.get('contact_email', 'Not Available')
                            })
                            supabase.table('rfpproject').insert({
                                'subject': details.get('title', 'Not Available'),
                                'online_link': details.get('document_link', 'Not Available'),
                                'formatted_date': details.get('event_date', 'Not Available'),
                                'agency': details.get('agency_sponsor', 'Not Available'),
                                'reference': details.get('reference', 'Not Available'),
                                'contact': details.get('contact_email', 'Not Available')
                            }).execute()
                            logger.info(f"Inserted opportunity into Supabase: {details.get('title')}")
                            print(f"✅ Inserted opportunity into Supabase: {details.get('title')}")
                        else:
                            print(f"❌ Failed to send email for URL: {url}: {message}")
                            logger.error(f"Failed to send email for URL: {url}: {message}")
                        time.sleep(1)
                    else:
                        print(f"❌ Failed to extract details for URL: {url}")
                        logger.error(f"Failed to extract details for URL: {url}")
                else:
                    print(f"❌ Failed to access bid content page for URL: {url}")
                    logger.error(f"Failed to access bid content page for URL: {url}")
            except Exception as e:
                print(f"⚠️ Error processing URL {url}: {e}, continuing with next URL")
                logger.error(f"Error processing URL {url}: {e}")
                continue

        if newest_timestamp > last_processed_time:
            with open('last_processed_time.pickle', 'wb') as f:
                pickle.dump(newest_timestamp, f)
            logger.info(f"Updated last processed timestamp to {newest_timestamp}")
            print(f"📅 Updated last processed timestamp to {newest_timestamp}")

        print(f"\n📊 PROCESSING SUMMARY:")
        print(f"Total URLs processed: {len(valid_urls)}")
        print(f"Duplicate URLs skipped: {duplicate_count}")
        print(f"New opportunities found: {len(opportunities)}")
        print(f"🕒 Timezone: America/New_York")
        print(f"🟢 ACTIVE RFP OPPORTUNITIES ({len(opportunities)} found):")
        logger.info(f"PROCESSING SUMMARY: Total URLs processed: {len(valid_urls)}, Duplicates skipped: {duplicate_count}, New opportunities: {len(opportunities)}")

        with open('processed_urls.pickle', 'wb') as f:
            pickle.dump(processed_urls, f)
        return opportunities, f"Processed {len(opportunities)} opportunities"

    except Exception as e:
        print(f"❌ Processing failed: {e}")
        logger.error(f"Processing failed: {e}")
        return None, f"Processing failed: {e}"
    finally:
        if driver:
            driver.quit()
            logger.info("WebDriver closed")
            print("🛑 WebDriver closed")

def run_process_daily_bids_in_background(interval_minutes=None):
    """Run process_daily_bids in a background thread."""
    def target():
        opportunities, message = process_daily_bids(interval_minutes)
        if opportunities is not None:
            print(f"✅ Background task completed: {message}")
            logger.info(f"Background task completed: {message}")
        else:
            print(f"❌ Background task failed: {message}")
            logger.error(f"Background task failed: {message}")
    thread = threading.Thread(target=target, daemon=True)
    thread.start()
    return "Processing started in background", None

@app.route('/mail_automation', methods=['GET', 'POST'])
def mail_automation():
    user = session.get('user', {'username': 'Guest', 'is_admin': False})
    if not user or 'username' not in user:
        return redirect(url_for('index'))

    current_datetime = datetime.now(ZoneInfo('Asia/Kolkata'))
    opportunities = []
    global time_interval

    if request.method == 'POST':
        action = request.form.get('action')
        if action == 'process_emails':
            new_interval = request.form.get('time_interval')
            if new_interval and (new_interval.endswith('m') or new_interval.endswith('h')):
                time_interval = new_interval
                logger.info(f"User set mail automation interval to {time_interval}")
                print(f"📅 User set mail automation interval to {time_interval}")
            opportunities, message = process_daily_bids(time_interval)
            if opportunities is None:
                return render_template('mail_automation.html', user=user, error=message, current_datetime=current_datetime, time_interval=time_interval)
            return render_template('mail_automation.html', user=user, opportunities=opportunities, message=message, current_datetime=current_datetime, time_interval=time_interval)
        elif action == 'run_now':
            message, _ = run_process_daily_bids_in_background(time_interval)
            return render_template('mail_automation.html', user=user, message=message, current_datetime=current_datetime, time_interval=time_interval)
        elif action == 'view_processed':
            response = supabase.table('rfpproject').select('*').execute()
            opportunities = response.data or []
            return render_template('mail_automation.html', user=user, opportunities=opportunities, message="Showing processed opportunities", current_datetime=current_datetime, time_interval=time_interval)
        elif action == 'view_logs':
            logs = log_capture.get_logs()
            return render_template('mail_automation.html', user=user, logs=logs, show_logs=True, current_datetime=current_datetime, time_interval=time_interval)
        else:
            return render_template('mail_automation.html', user=user, error="Invalid action", current_datetime=current_datetime, time_interval=time_interval)

    return render_template('mail_automation.html', user=user, current_datetime=current_datetime, time_interval=time_interval)

@app.route('/view_logs')
def view_logs():
    user = session.get('user', {'username': 'Guest', 'is_admin': False})
    if not user or 'username' not in user:
        return redirect(url_for('index'))

    logs = log_capture.get_logs()
    return render_template('viewlogs.html', user=user, logs=logs, current_datetime=datetime.now(ZoneInfo('Asia/Kolkata')))

@app.route('/mail_alerts', methods=['GET', 'POST'])
def mail_alerts():
    user = session.get('user', {'username': 'Guest', 'is_admin': False})
    if not user or 'username' not in user:
        logger.warning("Unauthorized access to /mail_alerts, redirecting to index")
        print("⚠️ Unauthorized access to /mail_alerts, redirecting to index")
        return redirect(url_for('index'))
    
    timezones = ['UTC', 'US/Pacific', 'US/Eastern', 'America/New_York', 'Asia/Kolkata', 'Europe/London']
    
    try:
        response = supabase.table('time').select('id', 'recipient_email', 'alert_time', 'timezone').execute()
        alerts = response.data or []
        alerts_list = [(alert.get('id'), alert.get('recipient_email', 'Unknown'), 
                        alert.get('alert_time', 'N/A'), alert.get('timezone', 'UTC')) for alert in alerts]
    except Exception as e:
        logger.error(f"Error fetching alerts: {e}")
        print(f"❌ Error fetching alerts: {e}")
        return render_template('mail_alerts.html', user=user, alerts=alerts_list, timezones=timezones,
                              error=f"Error fetching alerts: {e}", current_datetime=datetime.now(ZoneInfo('Asia/Kolkata')))

    current_datetime = datetime.now(ZoneInfo('Asia/Kolkata'))

    if request.method == 'POST':
        action = request.form.get('action')
        
        if action == 'edit':
            alert_id = request.form.get('alert_id')
            new_time = request.form.get('new_time')
            send_now_edit = 'send_now_edit' in request.form
            filter_option = request.form.get('filter_option', 'Due Within 3 Days')

            if alert_id and new_time:
                try:
                    supabase.table('time').update({'alert_time': new_time}).eq('id', alert_id).execute()
                    print(f"✅ Updated alert {alert_id} time to {new_time}")
                    logger.info(f"Updated alert {alert_id} time to {new_time}")

                    if send_now_edit:
                        response = supabase.table('time').select('recipient_email', 'timezone').eq('id', alert_id).execute()
                        if response.data and len(response.data) > 0:
                            recipient = response.data[0].get('recipient_email')
                            print(f"📧 Send Now triggered for updated alert {alert_id} to {recipient} with filter {filter_option}")
                            logger.debug(f"Send Now triggered for updated alert {alert_id} to {recipient} with filter {filter_option}")
                            
                            due_rfps = get_due_rfps(filter_option)
                            print(f"📊 Fetched {len(due_rfps)} RFPs for {filter_option}")
                            logger.debug(f"Fetched {len(due_rfps)} RFPs for {filter_option}")
                            
                            subject = f"RFPs {filter_option}"
                            html_body = f"""
<!DOCTYPE html>
<html>
<head>
    <title>{subject}</title>
    <style>
        body {{ font-family: Arial, sans-serif; margin: 0; padding: 0; background-color: #f4f4f4; }}
        .header {{ background-color: #f8f9fa; padding: 10px; text-align: center; border-bottom: 1px solid #ddd; }}
        table {{ width: 100%; border-collapse: collapse; margin-top: 20px; background-color: #fff; }}
        th, td {{ border: 1px solid #ddd; padding: 8px; text-align: left; }}
        th {{ background-color: #f2f2f2; font-weight: bold; }}
        td a {{ color: #007bff; text-decoration: none; }}
        td a:hover {{ text-decoration: underline; }}
        .footer {{ text-align: right; font-size: 12px; color: #6c757d; margin-top: 20px; }}
    </style>
</head>
<body>
    <div class="header">
        <h2>RFP Opportunities {filter_option}</h2>
    </div>
    <table>
        <tr>
            <th>Subject</th>
            <th>Online Link</th>
            <th>Due Date</th>
            <th>Agency</th>
            <th>Reference</th>
            <th>Contact</th>
        </tr>
"""
                            if due_rfps:
                                for rfp in due_rfps:
                                    html_body += f"""
        <tr>
            <td>{rfp.get('subject', 'N/A')}</td>
            <td><a href="{rfp.get('online_link', '#')}">Link</a></td>
            <td>{rfp.get('formatted_date', 'N/A')}</td>
            <td>{rfp.get('agency', 'N/A')}</td>
            <td>{rfp.get('reference', 'N/A')}</td>
            <td>{rfp.get('contact', 'N/A')}</td>
        </tr>
"""
                            else:
                                html_body += f"""
        <tr>
            <td colspan="6">No RFP opportunities found for {filter_option}.</td>
        </tr>
"""
                            html_body += f"""
    </table>
    <div class="footer">
        Last updated: {datetime.now(ZoneInfo('Asia/Kolkata')).strftime('%m/%d/%Y, %I:%M:%S %p')} IST
    </div>
</body>
</html>
"""
                            success, message = send_email(recipient, subject, html_body)
                            if not success:
                                logger.error(f"Failed to send immediate email for updated alert {alert_id}: {message}")
                                print(f"❌ Failed to send immediate email for updated alert {alert_id}: {message}")
                                return render_template('mail_alerts.html', user=user, alerts=alerts_list, timezones=timezones,
                                                    error=f"Failed to send immediate email: {message}", current_datetime=current_datetime)
                            print(f"✅ Immediate email sent for updated alert {alert_id} to {recipient}")
                            logger.info(f"Immediate email sent for updated alert {alert_id} to {recipient}")
                            return render_template('mail_alerts.html', user=user, alerts=alerts_list, timezones=timezones,
                                                message=f"Alert time updated and email sent immediately to {recipient}", current_datetime=current_datetime)
                    return redirect(url_for('mail_alerts'))
                except Exception as e:
                    logger.error(f"Error updating alert time or sending email: {e}")
                    print(f"❌ Error updating alert time or sending email: {e}")
                    return render_template('mail_alerts.html', user=user, alerts=alerts_list, timezones=timezones,
                                        error=f"Error updating alert time or sending email: {e}", current_datetime=current_datetime)
        else:
            new_recipient = request.form.get('recipient')
            new_time = request.form.get('alert_time')
            new_timezone = request.form.get('timezone', 'UTC')
            send_now = 'send_now' in request.form
            filter_option = request.form.get('filter_option', 'Due Within 3 Days')

            if new_recipient and new_time:
                response = supabase.table('time').select('*').eq('recipient_email', new_recipient).execute()
                current_alerts = response.data or []
                if len(current_alerts) < 20:
                    try:
                        supabase.table('time').insert({
                            'recipient_email': new_recipient,
                            'alert_time': new_time,
                            'timezone': new_timezone
                        }).execute()
                        print(f"✅ Successfully added alert for {new_recipient} at {new_time} ({new_timezone})")
                        logger.info(f"Successfully added alert for {new_recipient} at {new_time} ({new_timezone})")
                        
                        if send_now:
                            print(f"📧 Send Now triggered for {new_recipient} with filter {filter_option}")
                            logger.debug(f"Send Now triggered for {new_recipient} with filter {filter_option}")
                            due_rfps = get_due_rfps(filter_option)
                            print(f"📊 Fetched {len(due_rfps)} RFPs for {filter_option}")
                            logger.debug(f"Fetched {len(due_rfps)} RFPs for {filter_option}")
                            
                            subject = f"RFPs {filter_option}"
                            html_body = f"""
<!DOCTYPE html>
<html>
<head>
    <title>{subject}</title>
    <style>
        body {{ font-family: Arial, sans-serif; margin: 0; padding: 0; background-color: #f4f4f4; }}
        .header {{ background-color: #f8f9fa; padding: 10px; text-align: center; border-bottom: 1px solid #ddd; }}
        table {{ width: 100%; border-collapse: collapse; margin-top: 20px; background-color: #fff; }}
        th, td {{ border: 1px solid #ddd; padding: 8px; text-align: left; }}
        th {{ background-color: #f2f2f2; font-weight: bold; }}
        td a {{ color: #007bff; text-decoration: none; }}
        td a:hover {{ text-decoration: underline; }}
        .footer {{ text-align: right; font-size: 12px; color: #6c757d; margin-top: 20px; }}
    </style>
</head>
<body>
    <div class="header">
        <h2>RFP Opportunities {filter_option}</h2>
    </div>
    <table>
        <tr>
            <th>Subject</th>
            <th>Online Link</th>
            <th>Due Date</th>
            <th>Agency</th>
            <th>Reference</th>
            <th>Contact</th>
        </tr>
"""
                            if due_rfps:
                                for rfp in due_rfps:
                                    html_body += f"""
        <tr>
            <td>{rfp.get('subject', 'N/A')}</td>
            <td><a href="{rfp.get('online_link', '#')}">Link</a></td>
            <td>{rfp.get('formatted_date', 'N/A')}</td>
            <td>{rfp.get('agency', 'N/A')}</td>
            <td>{rfp.get('reference', 'N/A')}</td>
            <td>{rfp.get('contact', 'N/A')}</td>
        </tr>
"""
                            else:
                                html_body += f"""
        <tr>
            <td colspan="6">No RFP opportunities found for {filter_option}.</td>
        </tr>
"""
                            html_body += f"""
    </table>
    <div class="footer">
        Last updated: {datetime.now(ZoneInfo('Asia/Kolkata')).strftime('%m/%d/%Y, %I:%M:%S %p')} IST
    </div>
</body>
</html>
"""
                            success, message = send_email(new_recipient, subject, html_body)
                            if not success:
                                logger.error(f"Failed to send immediate email for new alert to {new_recipient}: {message}")
                                print(f"❌ Failed to send immediate email for new alert to {new_recipient}: {message}")
                                return render_template('mail_alerts.html', user=user, alerts=alerts_list, timezones=timezones,
                                                    error=f"Failed to send immediate email: {message}", current_datetime=current_datetime)
                            print(f"✅ Alert saved and email sent immediately to {new_recipient}")
                            logger.info(f"Alert saved and email sent immediately to {new_recipient}")
                            return render_template('mail_alerts.html', user=user, alerts=alerts_list, timezones=timezones,
                                                message="Alert saved and email sent immediately.", current_datetime=current_datetime)
                        return redirect(url_for('mail_alerts'))
                    except Exception as e:
                        logger.error(f"Error saving to Supabase or sending email: {e}")
                        print(f"❌ Error saving to Supabase or sending email: {e}")
                        return render_template('mail_alerts.html', user=user, alerts=alerts_list, timezones=timezones,
                                            error=f"Error saving alert or sending email: {e}", current_datetime=current_datetime)
                else:
                    return render_template('mail_alerts.html', user=user, alerts=alerts_list, timezones=timezones,
                                        message="Maximum 20 recipients allowed.", current_datetime=current_datetime)
        return redirect(url_for('mail_alerts'))

    return render_template('mail_alerts.html', user=user, alerts=alerts_list, timezones=timezones, current_datetime=current_datetime)
@app.route('/delete_alert/<alert_id>', methods=['POST'])
def delete_alert(alert_id):
    user = session.get('user', {'username': 'Guest', 'is_admin': False})
    if not user or 'username' not in user:
        logger.warning("Unauthorized access to /delete_alert, redirecting to index")
        print("⚠️ Unauthorized access to /delete_alert, redirecting to index")
        return redirect(url_for('index'))
    try:
        supabase.table('time').delete().eq('id', alert_id).execute()
        print(f"🗑️ Deleted alert with id {alert_id}")
        logger.info(f"Deleted alert with id {alert_id}")
        return redirect(url_for('mail_alerts'))
    except Exception as e:
        print(f"❌ Error deleting alert: {e}")
        logger.error(f"Error deleting alert: {e}")
        return render_template('mail_alerts.html', user=user, error=f"Error deleting alert: {e}")

@app.route('/')
def index():
    user = session.get('user', {'username': 'Guest', 'is_admin': False})
    return render_template('index.html', user=user)

@app.route('/login', methods=['POST'])
def login():
    username = request.form['username']
    password = request.form['password']
    response = supabase.table('users').select('*').eq('username', username).execute()
    users = response.data
    if users and users[0]['password'] == password:
        session['user'] = {'username': username, 'is_admin': users[0].get('is_admin', False)}
        return redirect(url_for('dashboard'))
    return render_template('index.html', user={'username': 'Guest', 'is_admin': False}, error='Invalid username or password')

@app.route('/dashboard', methods=['GET', 'POST'])
def dashboard():
    user = session.get('user', {'username': 'Guest', 'is_admin': False})
    if not user or 'username' not in user:
        return redirect(url_for('index'))
    
    response = supabase.table('rfpproject').select('*').execute()
    rfps = response.data or []
    current_datetime = datetime.now(ZoneInfo('Asia/Kolkata'))
    current_date = current_datetime.date()
    
    all_rfps = []
    for rfp in rfps:
        formatted_date = rfp.get('formatted_date')
        if formatted_date and formatted_date != 'NOT AVAILABLE':
            try:
                if datetime.strptime(formatted_date, '%Y-%m-%d').date() >= current_date:
                    all_rfps.append(rfp)
            except ValueError:
                continue

    all_rfps.sort(key=lambda x: datetime.strptime(x['formatted_date'], '%Y-%m-%d').date())

    filter_option = request.args.get('filter', 'All RFPs')
    if filter_option == 'Due Today':
        filtered_rfps = [rfp for rfp in all_rfps if datetime.strptime(rfp['formatted_date'], '%Y-%m-%d').date() == current_date]
    elif filter_option == 'Due Within 3 Days':
        end_date = current_date + timedelta(days=2)
        filtered_rfps = [rfp for rfp in all_rfps if current_date <= datetime.strptime(rfp['formatted_date'], '%Y-%m-%d').date() <= end_date]
    elif filter_option == 'Due This Week':
        end_date = current_date + timedelta(days=6)
        filtered_rfps = [rfp for rfp in all_rfps if current_date <= datetime.strptime(rfp['formatted_date'], '%Y-%m-%d').date() <= end_date]
    elif filter_option == 'Interested':
        filtered_rfps = [rfp for rfp in all_rfps if rfp.get('status') == 'Interested']
    elif filter_option == 'Not Interested':
        filtered_rfps = [rfp for rfp in all_rfps if rfp.get('status') == 'Not Interested']
    else:
        filtered_rfps = all_rfps

    search_query = request.args.get('search', '').lower()
    if search_query:
        filtered_rfps = [rfp for rfp in filtered_rfps if search_query in rfp.get('subject', '').lower() or
                         search_query in rfp.get('agency', '').lower() or
                         search_query in rfp.get('reference', '').lower()]

    if request.method == 'POST':
        rfp_id = request.form.get('rfp_id')
        status = request.form.get('status')
        if rfp_id and status:
            try:
                supabase.table('rfpproject').update({'status': status}).eq('reference', rfp_id).execute()
                logger.info(f"Updated RFP {rfp_id} status to {status}")
                print(f"✅ Updated RFP {rfp_id} status to {status}")
            except Exception as e:
                logger.error(f"Error updating RFP status: {e}")
                print(f"❌ Error updating RFP status: {e}")
                return render_template('dashboard.html', user=user, rfps=filtered_rfps, filter_option=filter_option,
                                     active_rfps=len(all_rfps), due_this_week=len([r for r in all_rfps if current_date <= datetime.strptime(r['formatted_date'], '%Y-%m-%d').date() <= current_date + timedelta(days=6)]),
                                     interested=len([r for r in all_rfps if r.get('status') == 'Interested']),
                                     total=len(rfps), current_datetime=current_datetime, error=f"Error updating status: {e}")
            return redirect(url_for('dashboard', filter=filter_option))

    return render_template('dashboard.html', user=user, rfps=filtered_rfps, filter_option=filter_option,
                         active_rfps=len(all_rfps),
                         due_this_week=len([r for r in all_rfps if current_date <= datetime.strptime(r['formatted_date'], '%Y-%m-%d').date() <= current_date + timedelta(days=6)]),
                         interested=len([r for r in all_rfps if r.get('status') == 'Interested']),
                         total=len(rfps), current_datetime=current_datetime)

@app.route('/user_management', methods=['GET', 'POST'])
def user_management():
    user = session.get('user', {'username': 'Guest', 'is_admin': False})
    if not user or 'username' not in user or not user.get('is_admin'):
        logger.warning("Unauthorized access to /user_management, redirecting to index")
        print("⚠️ Unauthorized access to /user_management, redirecting to index")
        return redirect(url_for('index'))

    response = supabase.table('users').select('username', 'is_admin').execute()
    users = response.data or []
    current_datetime = datetime.now(ZoneInfo('Asia/Kolkata'))
    edit_username = request.args.get('edit_username', None)

    if request.method == 'POST':
        action = request.form.get('action')
        if action == 'add_user':
            username = request.form.get('username')
            password = request.form.get('password')
            is_admin = 'is_admin' in request.form

            if username and password:
                response = supabase.table('users').select('*').eq('username', username).execute()
                if response.data:
                    return render_template('user_management.html', user=user, users=users, error="Username already exists", current_datetime=current_datetime, edit_username=edit_username)
                try:
                    supabase.table('users').insert({
                        'username': username,
                        'password': password,
                        'is_admin': is_admin
                    }).execute()
                    logger.info(f"Added new user: {username}, is_admin: {is_admin}")
                    print(f"✅ Added new user: {username}, is_admin: {is_admin}")
                    response = supabase.table('users').select('username', 'is_admin').execute()
                    users = response.data or []
                    return render_template('user_management.html', user=user, users=users, message="User added successfully", current_datetime=current_datetime, edit_username=edit_username)
                except Exception as e:
                    logger.error(f"Error adding user: {e}")
                    print(f"❌ Error adding user: {e}")
                    return render_template('user_management.html', user=user, users=users, error=f"Error adding user: {e}", current_datetime=current_datetime, edit_username=edit_username)
        elif action == 'edit_password':
            username = request.form.get('username')
            new_password = request.form.get('new_password')
            if username and new_password:
                try:
                    supabase.table('users').update({'password': new_password}).eq('username', username).execute()
                    logger.info(f"Updated password for user: {username}")
                    print(f"✅ Updated password for user: {username}")
                    response = supabase.table('users').select('username', 'is_admin').execute()
                    users = response.data or []
                    return render_template('user_management.html', user=user, users=users, message=f"Password updated for {username}", current_datetime=current_datetime)
                except Exception as e:
                    logger.error(f"Error updating password: {e}")
                    print(f"❌ Error updating password: {e}")
                    return render_template('user_management.html', user=user, users=users, error=f"Error updating password: {e}", current_datetime=current_datetime, edit_username=edit_username)

    return render_template('user_management.html', user=user, users=users, current_datetime=current_datetime, edit_username=edit_username)

@app.route('/delete_user/<username>', methods=['POST'])
def delete_user(username):
    user = session.get('user', {'username': 'Guest', 'is_admin': False})
    if not user or 'username' not in user or not user.get('is_admin'):
        logger.warning("Unauthorized access to /delete_user, redirecting to index")
        print("⚠️ Unauthorized access to /delete_user, redirecting to index")
        return redirect(url_for('index'))
    
    if username == user['username']:
        logger.warning("Attempt to delete current user blocked")
        print("⚠️ Attempt to delete current user blocked")
        response = supabase.table('users').select('username', 'is_admin').execute()
        users = response.data or []
        return render_template('user_management.html', user=user, users=users, error="Cannot delete your own account", current_datetime=datetime.now(ZoneInfo('Asia/Kolkata')))
    
    try:
        supabase.table('users').delete().eq('username', username).execute()
        logger.info(f"Deleted user: {username}")
        print(f"🗑️ Deleted user: {username}")
        response = supabase.table('users').select('username', 'is_admin').execute()
        users = response.data or []
        return render_template('user_management.html', user=user, users=users, message=f"User {username} deleted successfully", current_datetime=datetime.now(ZoneInfo('Asia/Kolkata')))
    except Exception as e:
        logger.error(f"Error deleting user: {e}")
        print(f"❌ Error deleting user: {e}")
        response = supabase.table('users').select('username', 'is_admin').execute()
        users = response.data or []
        return render_template('user_management.html', user=user, users=users, error=f"Error deleting user: {e}", current_datetime=datetime.now(ZoneInfo('Asia/Kolkata')))

@app.route('/edit_password/<username>', methods=['GET'])
def edit_password(username):
    user = session.get('user', {'username': 'Guest', 'is_admin': False})
    if not user or 'username' not in user or not user.get('is_admin'):
        logger.warning("Unauthorized access to /edit_password, redirecting to index")
        print("⚠️ Unauthorized access to /edit_password, redirecting to index")
        return redirect(url_for('index'))
    
    response = supabase.table('users').select('username', 'is_admin').execute()
    users = response.data or []
    return render_template('user_management.html', user=user, users=users, edit_username=username, current_datetime=datetime.now(ZoneInfo('Asia/Kolkata')))

@app.route('/logout')
def logout():
    session.pop('user', None)
    return redirect(url_for('index'))
    
if __name__ == '__main__':
    start_scheduler()
    print(f"🌐 Starting HTTP server for UI...")
    print(f" * Running on http://127.0.0.1:5000/ (Press CTRL+C to quit)")
    
    app.run(debug=True)
            