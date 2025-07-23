from flask import Flask, render_template, request, redirect, url_for, session, jsonify
from supabase import create_client, Client
from dotenv import load_dotenv
import os
import platform
from datetime import datetime, timedelta
from zoneinfo import ZoneInfo
from googleapiclient.discovery import build
from google_auth_oauthlib.flow import InstalledAppFlow
from google.oauth2.credentials import Credentials
from google.auth.transport.requests import Request
from email.mime.multipart import MIMEMultipart
from email.mime.text import MIMEText
import base64
import atexit
import logging
from apscheduler.schedulers.background import BackgroundScheduler
import json
import time
import hashlib
import threading
import subprocess
import sys
import os
from datetime import datetime
import io
import contextlib
import threading
import pickle
import re
import html
from urllib.parse import urlparse
from typing import List, Dict
import pytz
from functools import wraps
from googleapiclient.errors import HttpError
from googleapiclient.http import BatchHttpRequest
from tabulate import tabulate
import textwrap
import tenacity
import schedule
from selenium import webdriver
from selenium.webdriver.common.by import By
from selenium.webdriver.chrome.service import Service
from webdriver_manager.chrome import ChromeDriverManager
from selenium.webdriver.support.ui import WebDriverWait
from selenium.webdriver.support import expected_conditions as EC
from bs4 import BeautifulSoup

# Import platform-specific modules
if platform.system() == "Windows":
    import msvcrt
else:
    import fcntl

# Load environment variables
load_dotenv('supabase.env')

# Initialize Flask app
app = Flask(__name__)
app.secret_key = os.urandom(24)

# Configure logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s',
    handlers=[
        logging.FileHandler('app.log'),
        logging.StreamHandler()
    ]
)
logger = logging.getLogger(__name__)

# Supabase configuration
SUPABASE_URL = os.environ.get("SUPABASE_URL")
SUPABASE_KEY = os.environ.get("SUPABASE_KEY")
if not SUPABASE_URL or not SUPABASE_KEY:
    logger.error("Supabase credentials are missing. Please check supabase.env file.")
    raise ValueError("Supabase credentials are missing")
supabase: Client = create_client(SUPABASE_URL, SUPABASE_KEY)

# Google API Scopes
SCOPES = ['https://www.googleapis.com/auth/gmail.send']
SCOPES_GMAIL_READ = ['https://www.googleapis.com/auth/gmail.readonly']
SCOPES_GMAIL_SEND = ['https://www.googleapis.com/auth/gmail.send']

# Global variables
gmail_service = None
CACHE_FILE = 'sent_emails_cache.json'
LOCK_FILE = 'email_lock.lock'
scheduler_started = False
scheduler_instance = None

# Mail automation globals
automation_running = False
automation_thread = None
automation_interval = 60  # Default 1 hour in minutes
log_buffer = io.StringIO()
log_lock = threading.Lock()

# Mail automation globals
automation_running = False
automation_thread = None
automation_interval = 60  # Default 1 hour in minutes

# Constants for mail automation
US_STATES = [
    'Alabama', 'Alaska', 'Arizona', 'Arkansas', 'California', 'Colorado',
    'Connecticut', 'Delaware', 'Florida', 'Georgia', 'Hawaii', 'Idaho',
    'Illinois', 'Indiana', 'Iowa', 'Kansas', 'Kentucky', 'Louisiana',
    'Maine', 'Maryland', 'Massachusetts', 'Michigan', 'Minnesota',
    'Mississippi', 'Missouri', 'Montana', 'Nebraska', 'Nevada',
    'New Hampshire', 'New Jersey', 'New Mexico', 'New York',
    'North Carolina', 'North Dakota', 'Ohio', 'Oklahoma', 'Oregon',
    'Pennsylvania', 'Rhode Island', 'South Carolina', 'South Dakota',
    'Tennessee', 'Texas', 'Utah', 'Vermont', 'Virginia', 'Washington',
    'West Virginia', 'Wisconsin', 'Wyoming', 'District of Columbia'
]

FOOTER_KEYWORDS = {
    'copyright': ['copyright', 'all rights reserved'],
    'company': ['govdirections', 'llc', 'atlanta', 'georgia'],
    'membership': ['member home page', 'premium membership'],
    'contact': ['customercare', 'email', 'call', 'phone'],
    'navigation': ['unsubscribe', 'preferences', 'account settings']
}

def get_file_lock():
    """Get exclusive file lock to prevent concurrent email sending"""
    logger.debug("Attempting to acquire file lock")
    try:
        lock_file = open(LOCK_FILE, 'wb+')
        if platform.system() == "Windows":
            msvcrt.locking(lock_file.fileno(), msvcrt.LK_NBLCK, 1)
        else:
            fcntl.flock(lock_file.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
        logger.debug("File lock acquired successfully")
        return lock_file
    except ( MOError, OSError) as e:
        logger.warning(f"Failed to acquire file lock: {e}")
        return None

def release_file_lock(lock_file):
    """Release file lock"""
    if lock_file:
        try:
            if platform.system() == "Windows":
                lock_file.seek(0)
                msvcrt.locking(lock_file.fileno(), msvcrt.LK_UNLCK, 1)
            else:
                fcntl.flock(lock_file.fileno(), fcntl.LOCK_UN)
            lock_file.close()
            logger.debug("File lock released successfully")
        except Exception as e:
            logger.error(f"Error releasing file lock: {e}")

def load_cache():
    """Load cache with file locking"""
    logger.debug("Loading email cache")
    if os.path.exists(CACHE_FILE):
        try:
            with open(CACHE_FILE, 'r') as f:
                cache = json.load(f)
                logger.info(f"Loaded cache with {len(cache)} entries")
                return cache
        except Exception as e:
            logger.error(f"Error loading cache: {e}")
            return {}
    logger.debug("No cache file found, returning empty cache")
    return {}

def save_cache(cache_data):
    """Save cache with atomic write"""
    logger.debug("Saving email cache")
    temp_file = CACHE_FILE + '.tmp'
    try:
        with open(temp_file, 'w') as f:
            json.dump(cache_data, f, indent=2)
        os.rename(temp_file, CACHE_FILE)
        logger.debug("Cache saved successfully")
    except Exception as e:
        logger.error(f"Error saving cache: {e}")
        if os.path.exists(temp_file):
            os.remove(temp_file)

def create_email_hash(alert_id, date, hour, minute):
    """Create unique hash for email to prevent duplicates"""
    data = f"{alert_id}_{date}_{hour:02d}_{minute:02d}"
    email_hash = hashlib.md5(data.encode()).hexdigest()
    logger.debug(f"Created email hash: {email_hash}")
    return email_hash

def authenticate_google():
    global gmail_service
    logger.info("Attempting Google API authentication")
    creds = None
    token_path = 'token.json'
    if os.path.exists(token_path):
        try:
            with open(token_path, 'r') as token:
                creds = Credentials.from_authorized_user_file(token_path, SCOPES)
            logger.debug("Loaded credentials from token.json")
        except Exception as e:
            logger.error(f"Error reading token file: {e}")
            if os.path.exists(token_path):
                os.remove(token_path)
    if not creds or not creds.valid:
        if creds and creds.expired and creds.refresh_token:
            try:
                creds.refresh(Request())
                logger.debug("Refreshed Google API credentials")
            except Exception as e:
                logger.error(f"Error refreshing Google API credentials: {e}")
                creds = None
        if not creds:
            try:
                flow = InstalledAppFlow.from_client_secrets_file('client.json', SCOPES)
                creds = flow.run_local_server(port=0)
                with open(token_path, 'w') as token:
                    token.write(creds.to_json())
                logger.info(" facilitering Google API authentication successful, saved token.json")
            except Exception as e:
                logger.error(f"Error authenticating Google API: {e}")
                return False
    try:
        gmail_service = build('gmail', 'v1', credentials=creds)
        logger.info("Gmail service initialized successfully")
        return True
    except Exception as e:
        logger.error(f"Error building Gmail service: {e}")
        return False

def send_email(recipient, subject, body):
    global gmail_service
    logger.info(f"Attempting to send email to {recipient} with subject '{subject}'")
    if not gmail_service:
        logger.debug("Gmail service not initialized, attempting authentication")
        if not authenticate_google():
            logger.error("Failed to authenticate Google API")
            return False, "Failed to authenticate Google API"
    message = MIMEMultipart()
    message['to'] = recipient
    message['subject'] = subject
    message['from'] = 'rfp@iitlabs.com'
    message.attach(MIMEText(body, 'html'))
    raw_message = base64.urlsafe_b64encode(message.as_bytes()).decode()
    try:
        logger.debug(f"Sending email to {recipient} via Gmail API")
        gmail_service.users().messages().send(userId='me', body={'raw': raw_message}).execute()
        logger.info(f"Email successfully sent to {recipient}")
        return True, "Email sent successfully"
    except Exception as e:
        logger.error(f"Failed to send email to {recipient}: {str(e)}")
        return False, f"Failed to send email: {str(e)}"

def get_due_rfps():
    current_date = datetime.now(ZoneInfo('UTC')).date()
    logger.debug(f"Fetching RFPs due on {current_date}")
    response = supabase.table('rfpproject').select('*').execute()
    rfps = response.data or []
    due_rfps = [rfp for rfp in rfps if rfp.get('formatted_date') and rfp['formatted_date'] != 'NOT AVAILABLE' and
                datetime.strptime(rfp['formatted_date'], '%Y-%m-%d').date() == current_date]
    logger.info(f"Found {len(due_rfps)} RFPs due on {current_date}")
    return due_rfps

def check_and_send_alerts():
    """Check all alerts and send emails with file-based locking to prevent duplicates"""
    logger.debug("Starting check_and_send_alerts job")
    
    lock_file = get_file_lock()
    if not lock_file:
        logger.warning("Failed to acquire file lock, another process may be handling alerts")
        return
    
    try:
        logger.info("Fetching alerts from Supabase")
        response = supabase.table('time').select('id', 'recipient_email', 'alert_time', 'timezone').execute()
        alerts = response.data or []
        logger.info(f"Retrieved {len(alerts)} alerts from Supabase: {alerts}")
        if not alerts:
            logger.warning("No alerts found in the database")
            return

        current_utc = datetime.now(ZoneInfo('UTC'))
        current_date = current_utc.date()
        
        sent_emails_cache = load_cache()
        logger.info(f"Loaded cache with {len(sent_emails_cache)} entries")
        
        today_str = current_date.strftime('%Y-%m-%d')
        old_cache = sent_emails_cache.copy()
        sent_emails_cache = {k: v for k, v in sent_emails_cache.items() 
                           if isinstance(v, dict) and v.get('date') == today_str}
        
        if len(sent_emails_cache) != len(old_cache):
            logger.info("Cache cleaned, saving updated cache")
            save_cache(sent_emails_cache)

        for alert in alerts:
            alert_id = alert.get('id')
            recipient = alert.get('recipient_email')
            alert_time_str = alert.get('alert_time')
            timezone_str = alert.get('timezone', 'UTC')

            if not recipient or not alert_time_str or not timezone_str or not alert_id:
                logger.warning(f"Invalid alert data: {alert}")
                continue

            try:
                alert_hour, alert_minute = map(int, alert_time_str.split(':'))
                tz = ZoneInfo(timezone_str)
                current_in_tz = current_utc.astimezone(tz)
                
                current_hour = current_in_tz.hour
                current_minute = current_in_tz.minute
                
                logger.debug(f"Alert {alert_id}: Current time {current_hour:02d}:{current_minute:02d} ({timezone_str}), Alert time {alert_hour:02d}:{alert_minute:02d}")
                
                if current_hour == alert_hour and current_minute == alert_minute:
                    logger.info(f"EXACT TIME MATCH! Processing alert {alert_id} for {recipient}")
                    
                    email_hash = create_email_hash(alert_id, today_str, current_hour, current_minute)
                    logger.debug(f"Generated email hash: {email_hash}")
                    
                    if email_hash in sent_emails_cache:
                        logger.info(f"Email with hash {email_hash} already sent for alert {alert_id}, skipping")
                        continue
                    
                    sent_emails_cache[email_hash] = {
                        'alert_id': alert_id,
                        'recipient': recipient,
                        'date': today_str,
                        'time': f"{current_hour:02d}:{current_minute:02d}",
                        'sent_at': current_utc.isoformat(),
                        'status': 'sent'
                    }
                    
                    logger.debug("Saving cache after marking email as sent")
                    save_cache(sent_emails_cache)
                    
                    time.sleep(0.1)
                    
                    due_rfps = get_due_rfps()
                    html_body = """
                    <h2>RFP Opportunities Due Soon</h2>
                    """
                    if due_rfps:
                        html_body += """
                        <table border="1" style="width:100%; border-collapse: collapse;">
                            <tr>
                                <th style="padding: 8px; border: 1px solid #ddd;">Subject</th>
                                <th style="padding: 8px; border: 1px solid #ddd;">Online Link</th>
                                <th style="padding: 8px; border: 1px solid #ddd;">Due Date</th>
                                <th style="padding: 8px; border: 1px solid #ddd;">Agency</th>
                                <th style="padding: 8px; border: 1px solid #ddd;">Reference</th>
                                <th style="padding: 8px; border: 1px solid #ddd;">Contact</th>
                            </tr>
                        """
                        for rfp in due_rfps:
                            html_body += f"""
                            <tr>
                                <td style="padding: 8px; border: 1px solid #ddd;">{rfp.get('subject', 'N/A')}</td>
                                <td style="padding: 8px; border: 1px solid #ddd;">{rfp.get('online_link', 'N/A')}</td>
                                <td style="padding: 8px; border: 1px solid #ddd;">{rfp.get('formatted_date', 'N/A')}</td>
                                <td style="padding: 8px; border: 1px solid #ddd;">{rfp.get('agency', 'N/A')}</td>
                                <td style="padding: 8px; border: 1px solid #ddd;">{rfp.get('reference', 'N/A')}</td>
                                <td style="padding: 8px; border: 1px solid #ddd;">{rfp.get('contact', 'N/A')}</td>
                            </tr>
                            """
                        html_body += """
                        </table>
                        """
                    else:
                        html_body += """
                        <p>No RFP opportunities due today.</p>
                        """
                    
                    logger.debug(f"Sending email to {recipient} with {len(due_rfps)} RFPs")
                    success, message = send_email(recipient, "RFP Opportunities Due Soon", html_body)
                    
                    sent_emails_cache[email_hash]['email_result'] = 'success' if success else f'failed: {message}'
                    sent_emails_cache[email_hash]['completed_at'] = datetime.now(ZoneInfo('UTC')).isoformat()
                    logger.debug("Saving cache with email result")
                    save_cache(sent_emails_cache)
                    
                    if success:
                        logger.info(f"Scheduled RFP email sent successfully to {recipient} for alert {alert_id}")
                    else:
                        logger.error(f"Failed to send scheduled email to {recipient}: {message}")
                        
                else:
                    logger.debug(f"Alert {alert_id}: Time mismatch - Current: {current_hour:02d}:{current_minute:02d}, Alert: {alert_hour:02d}:{alert_minute:02d}")
                        
            except ValueError as e:
                logger.error(f"Error parsing alert time for {recipient}: {e}")
                continue
            except Exception as e:
                logger.error(f"Unexpected error processing alert for {recipient}: {e}")
                continue

    except Exception as e:
        logger.error(f"Error fetching alerts from Supabase: {e}")
    finally:
        logger.debug("Releasing file lock")
        release_file_lock(lock_file)

def init_scheduler():
    """Initialize scheduler only once"""
    global scheduler_started, scheduler_instance
    
    if scheduler_started:
        logger.info("Scheduler already started, skipping initialization")
        return
    
    try:
        if scheduler_instance:
            try:
                scheduler_instance.shutdown(wait=False)
                logger.debug("Shut down existing scheduler")
            except Exception as e:
                logger.error(f"Error shutting down existing scheduler: {e}")
        
        scheduler_instance = BackgroundScheduler(
            daemon=True,
            job_defaults={
                'coalesce': True,
                'max_instances': 1,
                'misfire_grace_time': 5
            }
        )
        
        scheduler_instance.add_job(
            check_and_send_alerts, 
            'interval', 
            minutes=1,
            id='email_alert_job',
            replace_existing=True
        )
        
        scheduler_instance.start()
        scheduler_started = True
        logger.info("Background scheduler started successfully")
        
        atexit.register(lambda: scheduler_instance.shutdown(wait=False) if scheduler_instance else None)
        
    except Exception as e:
        logger.error(f"Error starting scheduler: {e}")

# Mail Automation Functions
def retry_on_transient_error(max_attempts=3, backoff_factor=1):
    """Decorator to retry on transient HttpError with exponential backoff."""
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
                        raise
                    sleep_time = backoff_factor * (2 ** (attempts - 1))
                    logger.warning(f"Transient error {e.resp.status} in {func.__name__}, retrying in {sleep_time}s (attempt {attempts}/{max_attempts})")
                    time.sleep(sleep_time)
        return wrapper
    return decorator

@retry_on_transient_error()
def authenticate_gmail_automation(scopes: list, token_path: str = 'token_read.json') -> build:
    """Authenticates Gmail API using token-based credentials for automation."""
    creds = None
    token_creation_time = None
    six_months = timedelta(days=183)

    if os.path.exists(token_path):
        try:
            with open(token_path, 'r') as token_file:
                token_data = json.load(token_file)
            creds = Credentials.from_authorized_user_info(token_data, scopes)
            token_creation_time = token_data.get('creation_time')
            logger.info(f"Loaded credentials from {token_path}. Refresh token present: {creds.refresh_token is not None}")
            if not all(scope in creds.scopes for scope in scopes):
                logger.warning(f"Credentials in {token_path} lack required scopes: {scopes}. Forcing re-authentication.")
                os.remove(token_path)
                creds = None
                token_creation_time = None
        except (ValueError, json.JSONDecodeError) as e:
            logger.error(f"Failed to load credentials from {token_path}: {e}")
            print(f"Error: Invalid {token_path} file. Deleting and re-authenticating...")
            os.remove(token_path)
            creds = None
            token_creation_time = None

    if token_creation_time:
        try:
            creation_dt = datetime.fromisoformat(token_creation_time)
            current_dt = datetime.now(pytz.UTC)
            if current_dt - creation_dt > six_months:
                logger.info(f"Token is older than 6 months (created: {token_creation_time}). Forcing re-authentication.")
                print("Token expired (older than 6 months). Re-authenticating...")
                os.remove(token_path)
                creds = None
        except ValueError as e:
            logger.error(f"Invalid creation_time in {token_path}: {e}. Deleting and re-authenticating...")
            os.remove(token_path)
            creds = None

    if not creds or not creds.valid:
        if creds and creds.expired and creds.refresh_token:
            try:
                creds.refresh(Request())
                logger.info("Successfully refreshed access token.")
            except Exception as e:
                logger.error(f"Failed to refresh token: {e}")
                print(f"Error: Failed to refresh token ({e}). Re-authenticating...")
                if os.path.exists(token_path):
                    os.remove(token_path)
                creds = None
        
        if not creds:
            try:
                flow = InstalledAppFlow.from_client_secrets_file('client.json', scopes)
                creds = flow.run_local_server(
                    port=8080,
                    access_type='offline',
                    prompt='consent'
                )
                logger.info(f"OAuth flow completed. Refresh token obtained: {creds.refresh_token is not None}")
            except FileNotFoundError:
                print("Error: 'client.json' file not found. Please download OAuth 2.0 credentials from Google Cloud Console.")
                raise
            except Exception as e:
                print(f"Error: OAuth flow failed: {e}. Ensure your Google account is authorized and the browser flow completes successfully.")
                raise
        
        if creds:
            try:
                token_data = json.loads(creds.to_json())
                token_data['creation_time'] = datetime.now(pytz.UTC).isoformat()
                with open(token_path, 'w') as token:
                    json.dump(token_data, token, indent=2)
                print(f"Credentials saved to {token_path}")
                logger.info(f"Saved credentials to {token_path}. Refresh token: {creds.refresh_token is not None}, Creation time: {token_data['creation_time']}")
            except Exception as e:
                logger.error(f"Failed to save credentials to {token_path}: {e}")
                print(f"Warning: Failed to save credentials to {token_path}: {e}")
        else:
            print("Error: No valid credentials obtained from OAuth flow.")
            raise ValueError("Authentication failed: No valid credentials obtained.")

    try:
        return build('gmail', 'v1', credentials=creds)
    except Exception as e:
        print(f"Error: Failed to build Gmail API service: {e}")
        raise

def get_email_body(payload: dict) -> str:
    """Extract email body from payload."""
    def decode_body(data):
        try:
            return base64.urlsafe_b64decode(data).decode('utf-8', errors="ignore")
        except:
            return None

    if 'parts' in payload:
        for part in payload['parts']:
            if part['mimeType'] in ['text/plain', 'text/html']:
                if 'body' in part and 'data' in part['body']:
                    body = decode_body(part['body']['data'])
                    if body:
                        return body
    if 'body' in payload and 'data' in payload['body']:
        return decode_body(payload['body']['data']) or "No body content available."
    return "No body content available."

def is_state_header(line: str) -> bool:
    """Check if line is a state header."""
    return line.upper() in [state.upper() for state in US_STATES]

def is_special_line(line: str) -> bool:
    """Check if line should be skipped (footer, separator, etc.)."""
    line_lower = line.lower()
    if not line.strip() or re.match(r'^[<>*]+$', line):
        return True
    if any(keyword in line_lower for category in FOOTER_KEYWORDS.values() for keyword in category):
        return True
    return False

def is_new_opportunity(line: str) -> bool:
    """Check if line starts a new opportunity."""
    return re.match(r'^[*-•]\s*', line) is not None

def extract_opportunities(body: str) -> List[Dict[str, str]]:
    """Extract complete opportunities (including due dates) without duplicates."""
    opportunities = []
    current_state = None
    lines = [line.strip() for line in body.split('\n') if line.strip()]

    url_pattern = re.compile(r'\[(\d+)\]\s*(https?://\S+)')
    url_map = {}
    for line in lines:
        for ref_num, url in url_pattern.findall(line):
            url_map[ref_num] = url

    i = 0
    while i < len(lines):
        line = lines[i]

        if is_state_header(line):
            current_state = line.upper()
            i += 1
            continue

        if not current_state or is_special_line(line):
            i += 1
            continue

        if is_new_opportunity(line):
            opportunity_lines = [line]
            j = i + 1
            while j < len(lines) and not is_new_opportunity(lines[j]) and not is_state_header(lines[j]):
                if lines[j].strip() and not is_special_line(lines[j]):
                    opportunity_lines.append(lines[j])
                j += 1

            full_text = " ".join(opportunity_lines)
            title = clean_title(full_text)

            ref_num = re.search(r'\[(\d+)\]', full_text)
            ref_num = ref_num.group(1) if ref_num else None

            if len(title) > 10 and ref_num in url_map:
                opportunities.append({
                    "state": current_state,
                    "opportunity_title": title,
                    "link": url_map[ref_num]
                })

            i = j
        else:
            i += 1

    return opportunities

def clean_title(title: str) -> str:
    """Clean but preserve full opportunity text (including due dates)."""
    title = re.sub(r'^[*-•]\s*', '', title)
    title = re.sub(r'\[\d+\]', '', title)
    title = re.sub(r'\s+', ' ', title).strip()
    return title

@retry_on_transient_error()
def list_daily_bids_emails(service: build) -> List[str]:
    """Process ALL Daily Bids Alert emails and return unique URLs using batch requests."""
    try:
        messages = []
        next_page_token = None
        total_emails_processed = 0
        skipped_count = 0
        all_opportunities = []

        @retry_on_transient_error()
        def fetch_messages(page_token):
            return service.users().messages().list(
                userId='me',
                q="subject:'Daily Bids Alert'",
                maxResults=1000,
                pageToken=page_token
            ).execute()

        while True:
            try:
                result = fetch_messages(next_page_token)
                messages.extend(result.get('messages', []))
                next_page_token = result.get('nextPageToken')
                logger.info(f"Fetched {len(result.get('messages', []))} messages. Next page token: {next_page_token}")
                if not next_page_token:
                    break
            except HttpError as e:
                if e.resp.status == 403:
                    logger.error(f"Quota exceeded: {e}")
                    print("Error: Gmail API quota exceeded. Try again later or increase quota in Google Cloud Console.")
                    raise
                raise

        print(f"📩 Total Emails Found: {len(messages)}")

        message_data_dict = {}
        batch_requests = 0

        def batch_callback(request_id, response, exception):
            nonlocal skipped_count
            if exception is not None:
                skipped_count += 1
                message_data_dict[request_id] = {
                    'error': f"Batch request error: {str(exception)}"
                }
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

        for i, msg in enumerate(messages, 1):
            print(f"\r🔍 Processing email {i}/{len(messages)}...", end="", flush=True)
            msg_data = message_data_dict.get(msg['id'], {})
            if 'error' in msg_data:
                skipped_count += 1
                logger.error(f"Error processing email {msg['id']}: {msg_data['error']}")
                continue

            body = get_email_body(msg_data.get('payload', {}))
            if body == "No body content available.":
                continue

            opportunities = extract_opportunities(body)
            all_opportunities.extend(opportunities)

        seen = set()
        unique_urls = []
        for opp in all_opportunities:
            key = opp['link'].lower()
            if key not in seen:
                seen.add(key)
                unique_urls.append(opp['link'])

        print("\n📊 EMAIL PROCESSING RESULTS:")
        print(f"Total emails processed: {len(messages)}")
        print(f"Emails skipped due to errors: {skipped_count}")
        print(f"Total opportunities found: {len(all_opportunities)}")
        print(f"Unique URLs found: {len(unique_urls)}")

        return unique_urls

    except HttpError as error:
        logger.error(f"Gmail API Error: {error}")
        print(f"❌ Gmail API Error: {error}")
        return []
    except Exception as error:
        logger.error(f"Unexpected error: {error}")
        print(f"❌ Unexpected error: {error}")
        return []

def setup_driver():
    """Set up Selenium WebDriver."""
    options = webdriver.ChromeOptions()
    options.add_argument("--headless")
    options.add_argument("--no-sandbox")
    options.add_argument("--disable-dev-shm-usage")
    try:
        driver = webdriver.Chrome(service=Service(ChromeDriverManager().install()), options=options)
        logger.info("WebDriver initialized successfully")
        return driver
    except Exception as e:
        logger.error(f"Failed to initialize WebDriver: {e}")
        raise

@tenacity.retry(
    stop=tenacity.stop_after_attempt(3),
    wait=tenacity.wait_fixed(2),
    retry=tenacity.retry_if_exception_type(Exception),
    before_sleep=lambda retry_state: logger.warning(f"Retrying login attempt {retry_state.attempt_number}...")
)
def login_to_govdirections(driver, url):
    """Attempt login to govdirections.com with enhanced reliability and network retries."""
    load_dotenv('credentials.env')
    username = os.environ.get('GOV_USERNAME')
    password = os.environ.get('GOV_PASSWORD')

    if not username or not password:
        logger.error("GOV_USERNAME or GOV_PASSWORD not found in credentials.env")
        raise ValueError("Missing credentials in environment")

    # Pre-check DNS and connectivity
    try:
        import socket
        socket.gethostbyname('govdirections.com')  # DNS resolution check
        socket.create_connection(("www.google.com", 80), timeout=5)  # Basic connectivity check
        logger.debug("DNS and network connectivity confirmed")
    except socket.gaierror:
        logger.error("DNS resolution failed for govdirections.com")
        return False
    except socket.error:
        logger.error("Network connectivity issue detected")
        return False

    # Pre-check URL accessibility with enhanced retry logic
    max_attempts = 6
    for attempt in range(max_attempts):
        try:
            import requests
            response = requests.head(url, timeout=30, allow_redirects=True)
            if response.status_code == 200:
                logger.info(f"URL {url} is accessible after attempt {attempt + 1}")
                break
            else:
                logger.warning(f"URL {url} returned status {response.status_code}, retrying...")
        except requests.RequestException as e:
            logger.warning(f"Failed to access URL {url} on attempt {attempt + 1}: {str(e)}")
        if attempt < max_attempts - 1:
            wait_time = min(2 ** attempt * 10, 120)  # Exponential backoff with max 120 seconds
            logger.info(f"Retrying URL {url} in {wait_time} seconds...")
            time.sleep(wait_time)
        else:
            logger.error(f"Failed to access URL {url} after {max_attempts} attempts")
            # Proceed to WebDriver attempt despite pre-check failure
            logger.warning("Proceeding to WebDriver navigation despite pre-check failure")

    driver.get(url)
    current_url = driver.current_url
    logger.info(f"Navigated to URL: {current_url}")

    try:
        email_field = WebDriverWait(driver, 120).until(  # Kept at 120 seconds
            EC.presence_of_element_located((By.NAME, "data[User][email]"))
        )
        logger.info("Login form detected")

        email_field.send_keys(username)
        password_field = driver.find_element(By.NAME, "data[User][passwd]")
        password_field.send_keys(password)

        login_button = driver.find_element(By.XPATH, "//input[contains(translate(@value, 'ABCDEFGHIJKLMNOPQRSTUVWXYZ', 'abcdefghijklmnopqrstuvwxyz'), 'log in')]")
        login_button.click()

        WebDriverWait(driver, 120).until(  # Kept at 120 seconds
            EC.presence_of_element_located((By.XPATH, "//*[contains(text(), 'Event Date') or contains(text(), 'Agency Sponsor')]"))
        )
        logger.info("Login successful and bid content page loaded")
        return True
    except Exception as e:
        logger.error(f"Login failed: {str(e)}")
        current_url = driver.current_url
        if 'login' in current_url.lower():
            logger.error("Redirected to login page after login attempt")
            return False
        try:
            WebDriverWait(driver, 5).until(
                EC.presence_of_element_located((By.XPATH, "//*[contains(text(), 'Event Date') or contains(text(), 'Agency Sponsor')]"))
            )
            logger.info("Bid content found after login attempt, proceeding")
            return True
        except:
            logger.error("No bid content found after login attempt")
            return False
        
def extract_opportunity_details(driver, url):
    """Extract information from the bid details page."""
    try:
        current_url = driver.current_url
        logger.info(f"Extracting details from URL: {current_url}")
        if 'login' in current_url.lower():
            logger.error("Extraction aborted: Still on login page")
            return None

        WebDriverWait(driver, 10).until(
            EC.presence_of_element_located((By.CSS_SELECTOR, "body"))
        )
        soup = BeautifulSoup(driver.page_source, 'html.parser')

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
                details['contact_dept'] = clean_text(next_dd.get_text()) if next_dd and ('Purchasing' in next_dd.get_text() or 'Procurement' in next_dd.get_text()) else "Not Available"

                details['contact_name'] = "Not Available"
            else:
                details['contact_phone'] = "Not Available"
                details['contact_email'] = "Not Available"
                details['contact_dept'] = "Not Available"
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

        summary_section = soup.find('div', class_='well well-sm text-left', string=re.compile(r'summary', re.I))
        if summary_section:
            summary_text = summary_section.find_next('p').get_text(separator='\n').strip() if summary_section.find_next('p') else ""
            details['summary'] = clean_text(summary_text) if summary_text else "Not Available"
        else:
            details['summary'] = "Not Available"

        comp_intel_section = soup.find('div', class_='well well-sm text-left', string=re.compile(r'competitive\s*intelligence', re.I))
        if comp_intel_section:
            comp_text = comp_intel_section.get_text(separator='\n').strip()
            details['competitive_intel'] = clean_text(comp_text) if comp_text else "Not Available"
        else:
            details['competitive_intel'] = "Not Available"

        if all(value == "Not Available" for key, value in details.items() if key != 'document_link'):
            logger.warning("No meaningful data extracted, page may not contain bid details")
            return None

        return details
    except Exception as e:
        logger.error(f"Error extracting details: {e}")
        return None

@retry_on_transient_error()
@tenacity.retry(
    stop=tenacity.stop_after_attempt(5),
    wait=tenacity.wait_fixed(12 * 60 * 60),
    retry=tenacity.retry_if_exception_type(HttpError),
    before_sleep=lambda retry_state: logger.warning(
        f"Email sending failed. Retrying in 12 hours (attempt {retry_state.attempt_number})..."
    ),
)

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
        service = authenticate_gmail_api_send(token_path='token_send.json')
        sent_message = service.users().messages().send(userId='me', body=message).execute()
        logger.info(f"Email sent successfully to {to_email}, Message ID: {sent_message['id']}")
    except HttpError as error:
        logger.error(f"Failed to send email: {error}")
        raise
    except Exception as e:
        logger.error(f"Unexpected error sending email: {e}")
        raise

def run_automation_once():
    """Run the automation process once."""
    driver = None
    try:
        logger.info("Starting automation run...")
        
        gmail_service = authenticate_gmail_automation(SCOPES_GMAIL_READ, token_path='token_read.json')
        unique_urls = list_daily_bids_emails(gmail_service)
        if not unique_urls:
            logger.info("No new bid opportunity URLs found in Gmail.")
            return

        driver = setup_driver()
        processed_urls = set()

        if os.path.exists('processed_urls.pickle'):
            with open('processed_urls.pickle', 'rb') as f:
                processed_urls = pickle.load(f)
                logger.info(f"Loaded {len(processed_urls)} processed URLs from pickle file.")

        for url in unique_urls:
            if url in processed_urls:
                logger.info(f"Skipping already processed URL: {url}")
                continue

            logger.info(f"Processing URL: {url}")
            if login_to_govdirections(driver, url):
                details = extract_opportunity_details(driver, url)
                if details:
                    logger.info("\nExtracted Opportunity Details:")
                    logger.info("=" * 50)
                    for key, value in details.items():
                        logger.info(f"{key.replace('_', ' ').title()}: {value}")
                    logger.info("=" * 50)
                    try:
                        send_automation_email(details)
                        processed_urls.add(url)
                        with open('processed_urls.pickle', 'wb') as f:
                            pickle.dump(processed_urls, f)
                        logger.info(f"URL: {url} processed and email sent.")
                        time.sleep(5)
                    except Exception as e:
                        logger.error(f"Failed to send email for URL: {url}. Error: {e}")
                else:
                    logger.error(f"Failed to extract opportunity details for URL: {url}")
            else:
                logger.error(f"Failed to access bid content page for URL: {url}")
            
            with open('processed_urls.pickle', 'wb') as f:
                pickle.dump(processed_urls, f)

    except Exception as e:
        logger.error(f"Automation execution failed: {e}")
    finally:
        if driver:
            driver.quit()
            logger.info("WebDriver closed")

def automation_scheduler():
    """Scheduler function for automation."""
    global automation_running, automation_interval
    
    while automation_running:
        try:
            logger.info(f"Running automation (interval: {automation_interval} minutes)")
            run_automation_once()
            logger.info(f"Automation completed. Next run in {automation_interval} minutes.")
            
            # Sleep in small intervals to allow for stopping
            sleep_time = automation_interval * 60  # Convert to seconds
            for _ in range(int(sleep_time)):
                if not automation_running:
                    break
                time.sleep(1)
                
        except Exception as e:
            logger.error(f"Error in automation scheduler: {e}")
            time.sleep(60)  # Wait 1 minute before retrying

# Flask Routes
@app.route('/')
def index():
    user = session.get('user', {'username': 'Guest', 'is_admin': False})
    logger.debug(f"Rendering index page for user: {user['username']}")
    return render_template('index.html', user=user)

@app.route('/login', methods=['POST'])
def login():
    username = request.form['username']
    password = request.form['password']
    logger.info(f"Login attempt for username: {username}")
    response = supabase.table('users').select('*').eq('username', username).execute()
    users = response.data or []
    if users and users[0]['password'] == password:
        session['user'] = {'username': username, 'is_admin': users[0].get('is_admin', False)}
        logger.info(f"Successful login for {username}")
        return redirect(url_for('dashboard'))
    logger.warning(f"Failed login attempt for {username}")
    return render_template('index.html', user={'username': 'Guest', 'is_admin': False}, error='Invalid username or password')

@app.route('/logout', methods=['GET', 'POST'])
def logout():
    username = session.get('user', {}).get('username', 'Guest')
    logger.info(f"Logging out user: {username}")
    session.clear()
    return redirect(url_for('index'))

@app.route('/dashboard')
def dashboard():
    user = session.get('user', {'username': 'Guest', 'is_admin': False})
    if not user or 'username' not in user:
        logger.warning("Unauthorized access to /dashboard, redirecting to index")
        return redirect(url_for('index'))
    response = supabase.table('rfpproject').select('*').execute()
    rfps = response.data or []
    current_date = datetime.now(ZoneInfo('UTC')).date()
    current_datetime = datetime.now(ZoneInfo('UTC'))
    active_rfps = [rfp for rfp in rfps if rfp.get('formatted_date') and rfp['formatted_date'] != 'NOT AVAILABLE' and
                   datetime.strptime(rfp['formatted_date'], '%Y-%m-%d').date() >= current_date]
    search_query = request.args.get('search', '')
    filter_option = request.args.get('filter', 'All RFPs')
    if search_query:
        active_rfps = [rfp for rfp in active_rfps if search_query.lower() in (rfp.get('subject', '').lower() or rfp.get('agency', '').lower())]
    if filter_option == 'Due Today':
        active_rfps = [rfp for rfp in active_rfps if datetime.strptime(rfp['formatted_date'], '%Y-%m-%d').date() == current_date]
    elif filter_option == 'Due This Week':
        week_end = current_date + timedelta(days=7)
        active_rfps = [rfp for rfp in active_rfps if current_date <= datetime.strptime(rfp['formatted_date'], '%Y-%m-%d').date() <= week_end]
    
    logger.info(f"Rendering dashboard with {len(active_rfps)} RFPs, search: {search_query}, filter: {filter_option}")
    return render_template('dashboard.html', user=user, rfps=active_rfps, search_query=search_query, filter_option=filter_option, current_datetime=current_datetime)

@app.route('/mail_alerts', methods=['GET', 'POST'])
def mail_alerts():
    user = session.get('user', {'username': 'Guest', 'is_admin': False})
    if not user or 'username' not in user:
        logger.warning("Unauthorized access to /mail_alerts, redirecting to index")
        return redirect(url_for('index'))
    
    timezones = ['UTC', 'US/Pacific', 'US/Eastern', 'America/New_York','Asia/Kolkata', 'Europe/London']
    response = supabase.table('time').select('id', 'recipient_email', 'alert_time', 'timezone').execute()
    alerts = response.data or []
    alerts_list = [(alert.get('id'), alert.get('recipient_email', 'Unknown'), alert.get('alert_time', 'N/A'), alert.get('timezone', 'UTC')) for alert in alerts]
    logger.info(f"Initial alerts list: {alerts_list}")

    if request.method == 'POST':
        action = request.form.get('action')
        
        if action == 'delete':
            alert_id = request.form.get('alert_id')
            try:
                supabase.table('time').delete().eq('id', alert_id).execute()
                logger.info(f"Deleted alert with id {alert_id}")
                return redirect(url_for('mail_alerts'))
            except Exception as e:
                logger.error(f"Error deleting alert: {e}")
                return render_template('mail_alerts.html', user=user, alerts=alerts_list, timezones=timezones,
                                      error=f"Error deleting alert: {e}")

        elif action == 'send_rfp':
            recipient = request.form.get('recipient')
            if recipient:
                logger.info(f"Manually sending RFP email to {recipient}")
                due_rfps = get_due_rfps()
                if due_rfps:
                    html_body = """
                    <h2>RFP Opportunities Due Soon</h2>
                    <table border="1" style="width:100%; border-collapse: collapse;">
                        <tr>
                            <th style="padding: 8px; border: 1px solid #ddd;">Subject</th>
                            <th style="padding: 8px; border: 1px solid #ddd;">Online Link</th>
                            <th style="padding: 8px; border: 1px solid #ddd;">Due Date</th>
                            <th style="padding: 8px; border: 1px solid #ddd;">Agency</th>
                            <th style="padding: 8px; border: 1px solid #ddd;">Reference</th>
                            <th style="padding: 8px; border: 1px solid #ddd;">Contact</th>
                        </tr>
                    """
                    for rfp in due_rfps:
                        html_body += f"""
                        <tr>
                            <td style="padding: 8px; border: 1px solid #ddd;">{rfp.get('subject', 'N/A')}</td>
                            <td style="padding: 8px; border: 1px solid #ddd;">{rfp.get('online_link', 'N/A')}</td>
                            <td style="padding: 8px; border: 1px solid #ddd;">{rfp.get('formatted_date', 'N/A')}</td>
                            <td style="padding: 8px; border: 1px solid #ddd;">{rfp.get('agency', 'N/A')}</td>
                            <td style="padding: 8px; border: 1px solid #ddd;">{rfp.get('reference', 'N/A')}</td>
                            <td style="padding: 8px; border: 1px solid #ddd;">{rfp.get('contact', 'N/A')}</td>
                        </tr>
                        """
                    html_body += """
                    </table>
                    """
                    success, message = send_email(recipient, "RFP Opportunities Due Soon", html_body)
                    if success:
                        logger.info(f"RFP Opportunities email sent to {recipient}")
                        return render_template('mail_alerts.html', user=user, alerts=alerts_list, timezones=timezones,
                                              message="Email sent successfully")
                    else:
                        logger.error(f"Failed to send manual email: {message}")
                        return render_template('mail_alerts.html', user=user, alerts=alerts_list, timezones=timezones,
                                              error=message)
                else:
                    logger.info("No RFPs due today for manual email")
                    return render_template('mail_alerts.html', user=user, alerts=alerts_list, timezones=timezones,
                                          message="No RFP opportunities due today")

        new_recipient = request.form.get('recipient')
        new_time = request.form.get('alert_time')
        new_timezone = request.form.get('timezone', 'UTC')

        if new_recipient and new_time:
            response = supabase.table('time').select('*').eq('recipient_email', new_recipient).execute()
            current_alerts = response.data or []
            if len(current_alerts) < 5:
                try:
                    supabase.table('time').insert({
                        'recipient_email': new_recipient,
                        'alert_time': new_time,
                        'timezone': new_timezone
                    }).execute()
                    logger.info(f"Successfully added alert for {new_recipient} at {new_time} ({new_timezone})")
                    response = supabase.table('time').select('id', 'recipient_email', 'alert_time', 'timezone').execute()
                    alerts = response.data or []
                    alerts_list = [(alert.get('id'), alert.get('recipient_email', 'Unknown'), alert.get('alert_time', 'N/A'), alert.get('timezone', 'UTC')) for alert in alerts]
                    logger.info(f"Updated alerts list: {alerts_list}")
                    return render_template('mail_alerts.html', user=user, alerts=alerts_list, timezones=timezones,
                                          message="Alert saved successfully")
                except Exception as e:
                    logger.error(f"Error saving to Supabase: {e}")
                    return render_template('mail_alerts.html', user=user, alerts=alerts_list, timezones=timezones,
                                          error=f"Error saving alert: {e}")
            else:
                logger.warning(f"Maximum 5 alerts reached for {new_recipient}")
                return render_template('mail_alerts.html', user=user, alerts=alerts_list, timezones=timezones,
                                      message="Maximum 5 alerts allowed per recipient.")
        return redirect(url_for('mail_alerts'))

    return render_template('mail_alerts.html', user=user, alerts=alerts_list, timezones=timezones)

@app.route('/mail_automation', methods=['GET', 'POST'])
def mail_automation():
    global automation_running, automation_thread, automation_interval
    
    user = session.get('user', {'username': 'Guest', 'is_admin': False})
    if not user or 'username' not in user:
        logger.warning("Unauthorized access to /mail_automation, redirecting to index")
        return redirect(url_for('index'))

    message = None
    error = None

    if request.method == 'POST':
        action = request.form.get('action')
        interval = request.form.get('interval', '60')
        
        try:
            automation_interval = int(interval)
        except ValueError:
            automation_interval = 60

        if action == 'start_automation':
            if not automation_running:
                automation_running = True
                automation_thread = threading.Thread(target=automation_scheduler, daemon=True)
                automation_thread.start()
                logger.info(f"Mail automation started with {automation_interval} minute interval")
                message = f"Mail automation started successfully with {automation_interval} minute interval"
            else:
                message = "Mail automation is already running"

        elif action == 'stop_automation':
            if automation_running:
                automation_running = False
                if automation_thread and automation_thread.is_alive():
                    automation_thread.join(timeout=5)
                logger.info("Mail automation stopped")
                message = "Mail automation stopped successfully"
            else:
                message = "Mail automation is not running"

        elif action == 'run_once':
            try:
                logger.info("Running mail automation once")
                threading.Thread(target=run_automation_once, daemon=True).start()
                message = "Mail automation executed once successfully"
            except Exception as e:
                logger.error(f"Error running automation once: {e}")
                error = f"Error running automation: {str(e)}"

    return render_template('mail_automation.html', 
                         user=user, 
                         automation_running=automation_running,
                         message=message,
                         error=error)

@app.route('/view_logs')
def view_logs():
    user = session.get('user', {'username': 'Guest', 'is_admin': False})
    if not user or 'username' not in user:
        logger.warning("Unauthorized access to /view_logs, redirecting to index")
        return redirect(url_for('index'))

    try:
        with open('app.log', 'r') as f:
            logs = f.read()
    except FileNotFoundError:
        logs = "No logs available yet."
    except Exception as e:
        logs = f"Error reading logs: {str(e)}"

    last_updated = datetime.now(ZoneInfo('UTC')).strftime('%Y-%m-%d %H:%M:%S')
    return render_template('view_logs.html', user=user, logs=logs, last_updated=last_updated)
@app.route('/api/logs')
def api_logs():
    user = session.get('user', {'username': 'Guest', 'is_admin': False})
    if not user or 'username' not in user:
        return jsonify({'error': 'Unauthorized'}), 401

    try:
        with open('app.log', 'r') as f:
            logs = f.read()
        return jsonify({'logs': logs})
    except FileNotFoundError:
        return jsonify({'logs': 'No logs available yet.'})
    except Exception as e:
        return jsonify({'logs': f'Error reading logs: {str(e)}'})

@app.route('/update_status/<rfp_id>', methods=['POST'])
def update_status(rfp_id):
    user = session.get('user', {'username': 'Guest', 'is_admin': False})
    if not user or 'username' not in user:
        logger.warning("Unauthorized access to /update_status, redirecting to index")
        return redirect(url_for('index'))
    
    status = request.form.get('status')
    if status not in ['Interested', 'Not Interested']:
        logger.warning(f"Invalid status {status} for RFP {rfp_id}")
        return redirect(url_for('dashboard'))
    
    try:
        supabase.table('rfpproject').update({'status': status}).eq('id', rfp_id).execute()
        logger.info(f"Updated status for RFP {rfp_id} to {status}")
        return redirect(url_for('dashboard'))
    except Exception as e:
        logger.error(f"Error updating status for RFP {rfp_id}: {e}")
        return redirect(url_for('dashboard'))

@app.route('/reports', methods=['GET'])
def reports():
    user = session.get('user', {'username': 'Guest', 'is_admin': False})
    if not user or 'username' not in user:
        logger.warning("Unauthorized access to /reports, redirecting to index")
        return redirect(url_for('index'))
    
    status_filter = request.args.get('status', 'All')
    response = supabase.table('rfpproject').select('*').execute()
    rfps = response.data or []
    current_date = datetime.now(ZoneInfo('UTC')).date()
    
    active_rfps = [rfp for rfp in rfps if rfp.get('formatted_date') and rfp['formatted_date'] != 'NOT AVAILABLE' and
                   datetime.strptime(rfp['formatted_date'], '%Y-%m-%d').date() >= current_date]
    
    if status_filter == 'Interested':
        active_rfps = [rfp for rfp in active_rfps if rfp.get('status') == 'Interested']
    elif status_filter == 'Not Interested':
        active_rfps = [rfp for rfp in active_rfps if rfp.get('status') == 'Not Interested']
    
    logger.info(f"Rendering reports with {len(active_rfps)} RFPs, status filter: {status_filter}")
    return render_template('reports.html', user=user, rfps=active_rfps, status_filter=status_filter,
                          current_datetime=datetime.now(ZoneInfo('UTC')))

@app.route('/delete_alert/<alert_id>', methods=['POST'])
def delete_alert(alert_id):
    user = session.get('user', {'username': 'Guest', 'is_admin': False})
    if not user or 'username' not in user:
        logger.warning("Unauthorized access to /delete_alert, redirecting to index")
        return redirect(url_for('index'))
    try:
        supabase.table('time').delete().eq('id', alert_id).execute()
        logger.info(f"Deleted alert with id {alert_id}")
        return redirect(url_for('mail_alerts'))
    except Exception as e:
        logger.error(f"Error deleting alert: {e}")
        return redirect(url_for('mail_alerts'))

@app.route('/user_management', methods=['GET', 'POST'])
def user_management():
    user = session.get('user', {'username': 'Guest', 'is_admin': False})
    if not user or 'username' not in user:
        logger.warning("Unauthorized access to /user_management, redirecting to index")
        return redirect(url_for('index'))
    
    if not user['is_admin']:
        logger.warning(f"Non-admin user {user['username']} attempted to access /user_management")
        return redirect(url_for('dashboard'))
    
    response = supabase.table('users').select('username', 'is_admin').execute()
    users = response.data or []
    logger.info(f"Retrieved {len(users)} users for user management")

    if request.method == 'POST':
        username = request.form.get('username')
        password = request.form.get('password')
        is_admin = 'is_admin' in request.form

        if username and password:
            try:
                supabase.table('users').insert({
                    'username': username,
                    'password': password,
                    'is_admin': is_admin
                }).execute()
                logger.info(f"Added user {username} with admin status {is_admin}")
                return redirect(url_for('user_management'))
            except Exception as e:
                logger.error(f"Error adding user: {e}")
                return render_template('user_management.html', user=user, users=users, error=f"Error adding user: {e}")

    return render_template('user_management.html', user=user, users=users)

if __name__ == '__main__':
    logger.info("Starting Flask application")
    init_scheduler()
    app.run(debug=True, use_reloader=False, threaded=True)