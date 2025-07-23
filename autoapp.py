
from flask import Flask, render_template, request, redirect, url_for, session
import re
import base64
import os
import pickle
import time
import logging
import html
from urllib.parse import urlparse
from typing import List, Dict
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
import logging
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

# Import platform-specific modules
if platform.system() == "Windows":
    import msvcrt
else:
    import fcntl

# Load environment variables
load_dotenv('supabase.env')
load_dotenv('credentials.env')

# Initialize Flask app
app = Flask(__name__)
app.secret_key = os.urandom(24)

# Configure logging
logging.basicConfig(
    level=logging.DEBUG,
    format='%(asctime)s - %(levelname)s - %(message)s',
    filename='app.log',
    filemode='a'
)
logger = logging.getLogger(__name__)

# Supabase configuration
SUPABASE_URL = os.environ.get("SUPABASE_URL")
SUPABASE_KEY = os.environ.get("SUPABASE_KEY")
if not SUPABASE_URL or not SUPABASE_KEY:
    logger.error("Supabase credentials are missing. Please check supabase.env file.")
    raise ValueError("Supabase credentials are missing")
supabase = create_client(SUPABASE_URL, SUPABASE_KEY)

# Google API Scopes
SCOPES = ['https://www.googleapis.com/auth/gmail.send']
SCOPES_GMAIL_READ = ['https://www.googleapis.com/auth/gmail.readonly']
SCOPES_GMAIL_SEND = ['https://www.googleapis.com/auth/gmail.send']

# Global variables
gmail_service = None
CACHE_FILE = 'sent_emails_cache.json'
LOCK_FILE = 'email_lock.lock'
scheduler = None
scheduler_started = False
time_interval = 1  # Default interval in hours

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
    except (IOError, OSError) as e:
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
                logger.debug(f"Loaded cache with {len(cache)} entries")
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
        os.replace(temp_file, CACHE_FILE)
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
    logger.debug("Attempting to authenticate Google API")
    creds = None
    token_path = 'token.json'
    if os.path.exists(token_path):
        try:
            with open(token_path, 'r') as token:
                creds = Credentials.from_authorized_user_file(token_path, SCOPES)
                logger.debug("Loaded existing token")
        except Exception as e:
            logger.error(f"Error reading token file: {e}")
            if os.path.exists(token_path):
                os.remove(token_path)
    if not creds or not creds.valid:
        if creds and creds.expired and creds.refresh_token:
            creds.refresh(Request())
            logger.debug("Refreshed expired token")
        else:
            logger.debug("Initiating new authentication flow")
            flow = InstalledAppFlow.from_client_secrets_file('client.json', SCOPES)
            creds = flow.run_local_server(port=0)
        with open(token_path, 'w') as token:
            token.write(creds.to_json())
            logger.debug("Saved new token")
    try:
        gmail_service = build('gmail', 'v1', credentials=creds)
        logger.debug("Google API authentication successful")
        return True
    except Exception as e:
        logger.error(f"Failed to build Gmail service: {e}")
        return False

def send_email(recipient, subject, body):
    global gmail_service
    logger.debug(f"Attempting to send email to {recipient}")
    if not gmail_service:
        if not authenticate_google():
            raise Exception("Failed to authenticate Google API")
    message = MIMEMultipart()
    message['to'] = recipient
    message['subject'] = subject
    message['from'] = 'rfp@iitlabs.com'
    message.attach(MIMEText(body, 'html'))
    raw_message = base64.urlsafe_b64encode(message.as_bytes()).decode()
    try:
        gmail_service.users().messages().send(userId='me', body={'raw': raw_message}).execute()
        logger.info(f"Email sent successfully to {recipient}")
        return True, "Email sent successfully"
    except Exception as e:
        logger.error(f"Failed to send email to {recipient}: {e}")
        return False, f"Failed to send email: {e}"

def get_due_rfps(filter_option="Due Within 3 Days"):
    """Fetch RFPs based on the specified filter option, sorted by due date"""
    current_date = datetime.now(ZoneInfo('UTC')).date()
    response = supabase.table('rfpproject').select('*').execute()
    rfps = response.data or []
    all_rfps = [rfp for rfp in rfps if rfp.get('formatted_date') and rfp['formatted_date'] != 'NOT AVAILABLE' and
                datetime.strptime(rfp['formatted_date'], '%Y-%m-%d').date() >= current_date]
    all_rfps.sort(key=lambda x: datetime.strptime(x['formatted_date'], '%Y-%m-%d').date())

    if filter_option == "Due Today":
        due_rfps = [rfp for rfp in all_rfps if datetime.strptime(rfp['formatted_date'], '%Y-%m-%d').date() == current_date]
    elif filter_option == "Due Within 3 Days":
        end_date = current_date + timedelta(days=2)
        due_rfps = [rfp for rfp in all_rfps if current_date <= datetime.strptime(rfp['formatted_date'], '%Y-%m-%d').date() <= end_date]
    elif filter_option == "Due This Week":
        end_date = current_date + timedelta(days=6)
        due_rfps = [rfp for rfp in all_rfps if current_date <= datetime.strptime(rfp['formatted_date'], '%Y-%m-%d').date() <= end_date]
    else:
        due_rfps = all_rfps

    logger.debug(f"Found {len(due_rfps)} RFPs for filter {filter_option}")
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
        logger.info(f"Retrieved {len(alerts)} alerts")
        if not alerts:
            logger.warning("No alerts found in the database")
            return

        current_utc = datetime.now(ZoneInfo('UTC'))
        current_date = current_utc.date()
        today_str = current_date.strftime('%Y-%m-%d')
        
        sent_emails_cache = load_cache()
        sent_emails_cache = {k: v for k, v in sent_emails_cache.items() 
                           if isinstance(v, dict) and v.get('date') == today_str}
        save_cache(sent_emails_cache)

        due_periods = ["Due Today", "Due Within 3 Days", "Due This Week"]
        current_period_index = int(time.time()) % len(due_periods)
        due_period = due_periods[current_period_index]

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
                
                logger.debug(f"Processing alert {alert_id} for {recipient}: Current time {current_hour:02d}:{current_minute:02d} ({timezone_str}), Alert time {alert_hour:02d}:{alert_minute:02d}")
                
                if current_hour == alert_hour and current_minute == alert_minute:
                    email_hash = create_email_hash(alert_id, today_str, current_hour, current_minute)
                    if email_hash in sent_emails_cache:
                        logger.info(f"Email with hash {email_hash} already sent for alert {alert_id}, skipping")
                        continue
                    
                    logger.info(f"Sending email for alert {alert_id} to {recipient}")
                    sent_emails_cache[email_hash] = {
                        'alert_id': alert_id,
                        'recipient': recipient,
                        'date': today_str,
                        'time': f"{current_hour:02d}:{current_minute:02d}",
                        'sent_at': current_utc.isoformat(),
                        'status': 'sent'
                    }
                    save_cache(sent_emails_cache)
                    time.sleep(0.2)
                    
                    due_rfps = get_due_rfps(due_period)
                    subject = "RFPs Due Soon"
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
        <h2>RFP Opportunities {due_period}</h2>
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
            <td colspan="6">No RFP opportunities {due_period.lower()}.</td>
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
                    sent_emails_cache[email_hash]['email_result'] = 'success' if success else f'failed: {message}'
                    sent_emails_cache[email_hash]['completed_at'] = datetime.now(ZoneInfo('UTC')).isoformat()
                    save_cache(sent_emails_cache)
                    
                    if success:
                        logger.info(f"Scheduled RFP email sent successfully to {recipient} for alert {alert_id}")
                    else:
                        logger.error(f"Failed to send scheduled email to {recipient}: {message}")
                        
            except ValueError as e:
                logger.error(f"Error parsing alert time for {recipient}: {e}")
            except Exception as e:
                logger.error(f"Unexpected error processing alert for {recipient}: {e}")

    except Exception as e:
        logger.error(f"Error fetching alerts from Supabase: {e}")
    finally:
        release_file_lock(lock_file)

def start_scheduler():
    """Initialize scheduler only once"""
    global scheduler, scheduler_started
    if scheduler_started:
        logger.info("Scheduler already started, skipping initialization")
        return
    
    try:
        scheduler = BackgroundScheduler(
            daemon=True,
            job_defaults={
                'coalesce': True,
                'max_instances': 1,
                'misfire_grace_time': 5
            }
        )
        scheduler.add_job(
            check_and_send_alerts,
            'interval',
            minutes=1,  # Check every minute, but process only at scheduled intervals
            id='email_alert_job',
            replace_existing=True
        )
        scheduler.start()
        scheduler_started = True
        logger.info("Background scheduler started successfully")
        
        atexit.register(lambda: scheduler.shutdown(wait=False) if scheduler else None)
    except Exception as e:
        logger.error(f"Error starting scheduler: {e}")

# --- Mail Automation Functions ---
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
def authenticate_gmail_read(scopes: list, token_path: str = 'token_read.json') -> build:
    """
    Authenticates Gmail API using token-based credentials for reading emails.
    """
    creds = None
    token_creation_time = None
    six_months = timedelta(days=183)

    if os.path.exists(token_path):
        try:
            with open(token_path, 'r') as token_file:
                token_data = json.load(token_file)
            creds = Credentials.from_authorized_user_info(token_data, scopes)
            token_creation_time = token_data.get('creation_time')
            logger.info(f"Loaded credentials from {token_path}")
        except (ValueError, json.JSONDecodeError) as e:
            logger.error(f"Failed to load credentials from {token_path}: {e}")
            os.remove(token_path)
            creds = None
            token_creation_time = None

    if token_creation_time:
        try:
            creation_dt = datetime.fromisoformat(token_creation_time)
            current_dt = datetime.now(pytz.UTC)
            if current_dt - creation_dt > six_months:
                logger.info(f"Token is older than 6 months (created: {token_creation_time}). Forcing re-authentication.")
                os.remove(token_path)
                creds = None
        except ValueError as e:
            logger.error(f"Invalid creation_time in {token_path}: {e}")
            os.remove(token_path)
            creds = None

    if not creds or not creds.valid:
        if creds and creds.expired and creds.refresh_token:
            try:
                creds.refresh(Request())
                logger.info("Successfully refreshed access token.")
            except Exception as e:
                logger.error(f"Failed to refresh token: {e}")
                os.remove(token_path)
                creds = None
        
        if not creds:
            try:
                flow = InstalledAppFlow.from_client_secrets_file('client.json', scopes)
                creds = flow.run_local_server(port=8080, access_type='offline', prompt='consent')
                logger.info(f"OAuth flow completed for {token_path}")
            except FileNotFoundError:
                logger.error("client.json not found")
                return None
            except Exception as e:
                logger.error(f"OAuth flow failed: {e}")
                return None
        
        if creds:
            try:
                token_data = json.loads(creds.to_json())
                token_data['creation_time'] = datetime.now(pytz.UTC).isoformat()
                with open(token_path, 'w') as token:
                    json.dump(token_data, token, indent=2)
                logger.info(f"Saved credentials to {token_path}")
            except Exception as e:
                logger.error(f"Failed to save credentials to {token_path}: {e}")

    try:
        return build('gmail', 'v1', credentials=creds)
    except Exception as e:
        logger.error(f"Failed to build Gmail API service: {e}")
        return None

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

    url_pattern = re.compile(r'\[(\d+)\s*(https?://\S+)')
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
    """Process Daily Bids Alert emails and return unique URLs."""
    try:
        messages = []
        next_page_token = None
        total_emails_processed = 0
        skipped_count = 0
        all_opportunities = []

        # Configurable query with default
        query = "subject:'Daily Bids Alert' -in:trash"  # Exclude trash, adjust subject if needed
        logger.info(f"Starting email fetch with query: {query}")

        while True:
            try:
                result = service.users().messages().list(
                    userId='me',
                    q=query,
                    maxResults=1000,
                    pageToken=next_page_token
                ).execute()
                messages.extend(result.get('messages', []))
                next_page_token = result.get('nextPageToken')
                logger.info(f"Fetched {len(result.get('messages', []))} messages, next page token: {next_page_token}")
                if not next_page_token:
                    break
            except HttpError as e:
                logger.error(f"Gmail API Error during fetch: {e}")
                return []

        if not messages:
            logger.warning("No messages found matching the query.")
            return []

        message_data_dict = {}
        batch_requests = 0

        def batch_callback(request_id, response, exception):
            nonlocal skipped_count
            if exception is not None:
                skipped_count += 1
                message_data_dict[request_id] = {'error': str(exception)}
                logger.error(f"Batch error for message {request_id}: {exception}")
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
            msg_data = message_data_dict.get(msg['id'], {})
            if 'error' in msg_data:
                skipped_count += 1
                logger.error(f"Error processing email {msg['id']}: {msg_data['error']}")
                continue

            body = get_email_body(msg_data.get('payload', {}))
            logger.debug(f"Email {msg['id']} body: {body[:200]}...")  # Log first 200 chars of body
            if body == "No body content available.":
                logger.warning(f"No body content for email {msg['id']}")
                continue

            opportunities = extract_opportunities(body)
            if not opportunities:
                # Fallback: Use regex to extract URLs if extract_opportunities fails
                import re
                urls = re.findall(r'http[s]?://(?:[a-zA-Z]|[0-9]|[$-_@.&+]|[!*\\(\\),]|(?:%[0-9a-fA-F][0-9a-fA-F]))+', body)
                if urls:
                    opportunities = [{'link': url} for url in urls]
                    logger.info(f"Fallback URL extraction for email {msg['id']} found {len(urls)} URLs")
                else:
                    logger.warning(f"No opportunities or URLs found in email {msg['id']}")
            all_opportunities.extend(opportunities)

        seen = set()
        unique_urls = []
        for opp in all_opportunities:
            key = opp.get('link', '').lower()
            if key and key not in seen:
                seen.add(key)
                unique_urls.append(opp['link'])

        logger.info(f"Processed {len(messages)} emails, skipped {skipped_count}, found {len(unique_urls)} unique URLs")
        return unique_urls

    except HttpError as error:
        logger.error(f"Gmail API Error: {error}")
        return []
    except Exception as error:
        logger.error(f"Unexpected error: {error}")
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
        return None

@tenacity.retry(
    stop=tenacity.stop_after_attempt(3),
    wait=tenacity.wait_fixed(2),
    retry=tenacity.retry_if_exception_type(Exception),
    before_sleep=lambda retry_state: logger.warning(f"Retrying login attempt {retry_state.attempt_number}...")
)
def login_to_govdirections(driver, url):
    """Attempt login to govdirections.com."""
    username = os.environ.get('GOV_USERNAME')
    password = os.environ.get('GOV_PASSWORD')

    if not username or not password:
        logger.error("GOV_USERNAME or GOV_PASSWORD not found in credentials.env")
        return False

    driver.get(url)
    try:
        email_field = WebDriverWait(driver, 10).until(
            EC.presence_of_element_located((By.NAME, "data[User][email]"))
        )
        email_field.send_keys(username)
        password_field = driver.find_element(By.NAME, "data[User][passwd]")
        password_field.send_keys(password)

        login_button = driver.find_element(By.XPATH, "//input[contains(translate(@value, 'ABCDEFGHIJKLMNOPQRSTUVWXYZ', 'abcdefghijklmnopqrstuvwxyz'), 'log in')]")
        login_button.click()

        WebDriverWait(driver, 10).until(
            EC.presence_of_element_located((By.XPATH, "//*[contains(text(), 'Event Date') or contains(text(), 'Agency Sponsor')]"))
        )
        logger.info("Login successful")
        return True
    except Exception as e:
        logger.error(f"Login failed: {e}")
        return False

def extract_opportunity_details(driver, url):
    """Extract information from the bid details page."""
    try:
        driver.get(url)
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

        if all(value == "Not Available" for key, value in details.items() if key != 'document_link'):
            logger.warning("No meaningful data extracted")
            return None

        return details
    except Exception as e:
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
        return True, "Email sent successfully"
    except Exception as e:
        logger.error(f"Failed to send email: {e}")
        return False, f"Failed to send email: {e}"

import threading
import time

def process_daily_bids(interval_minutes=None):
    """Process Daily Bids emails and extract opportunities with configurable interval in minutes."""
    global time_interval
    if interval_minutes is not None:
        if isinstance(interval_minutes, int) and interval_minutes > 0:
            time_interval = interval_minutes / 60.0
            logger.info(f"Using mail automation interval of {interval_minutes} minutes ({time_interval} hours)")
        elif isinstance(interval_minutes, str):
            try:
                if interval_minutes.endswith('m'):
                    minutes = int(interval_minutes[:-1])
                    if minutes > 0:
                        time_interval = minutes / 60.0
                        logger.info(f"Using mail automation interval of {minutes} minutes ({time_interval} hours)")
                elif interval_minutes.endswith('h'):
                    hours = int(interval_minutes[:-1])
                    if hours > 0:
                        time_interval = hours
                        logger.info(f"Using mail automation interval of {hours} hours")
            except ValueError:
                logger.warning(f"Invalid interval format: {interval_minutes}, using default {time_interval} hours")
    else:
        logger.info(f"Using default mail automation interval of {time_interval} hours")

    driver = None
    try:
        gmail_service = authenticate_gmail_read(SCOPES_GMAIL_READ, token_path='token_read.json')
        if not gmail_service:
            logger.error("Failed to authenticate Gmail API for reading")
            return None, "Failed to authenticate Gmail API for reading"

        unique_urls = list_daily_bids_emails(gmail_service)
        if not unique_urls:
            logger.warning("No new bid opportunity URLs found in Gmail.")
            return [], "No new bid opportunity URLs found in Gmail."

        driver = setup_driver()
        if not driver:
            return None, "Failed to initialize WebDriver"

        processed_urls = set()
        if os.path.exists('processed_urls.pickle'):
            with open('processed_urls.pickle', 'rb') as f:
                processed_urls = pickle.load(f)
                logger.info(f"Loaded {len(processed_urls)} processed URLs")

        opportunities = []
        for url in unique_urls:
            if url in processed_urls:
                logger.info(f"Skipping already processed URL: {url}")
                continue

            if login_to_govdirections(driver, url):
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
                    else:
                        logger.error(f"Failed to send email for URL: {url}: {message}")
                    time.sleep(1)  # Reduced from 5 to 1 second to speed up
                else:
                    logger.error(f"Failed to extract details for URL: {url}")
            else:
                logger.error(f"Failed to access bid content page for URL: {url}")

        with open('processed_urls.pickle', 'wb') as f:
            pickle.dump(processed_urls, f)
        return opportunities, f"Processed {len(opportunities)} opportunities"

    except Exception as e:
        logger.error(f"Processing failed: {e}")
        return None,(f"Processing failed: {e}")
    finally:
        if driver:
            driver.quit()
            logger.info("WebDriver closed")

def run_process_daily_bids_in_background(interval_minutes=None):
    """Run process_daily_bids in a background thread."""
    def target():
        opportunities, message = process_daily_bids(interval_minutes)
        if opportunities is not None:
            logger.info(f"Background task completed: {message}")
        else:
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
            return redirect(url_for('view_logs'))
        else:
            return render_template('mail_automation.html', user=user, error="Invalid action", current_datetime=current_datetime, time_interval=time_interval)

    return render_template('mail_automation.html', user=user, current_datetime=current_datetime, time_interval=time_interval)

@app.route('/view_logs')
def view_logs():
    user = session.get('user', {'username': 'Guest', 'is_admin': False})
    if not user or 'username' not in user:
        return redirect(url_for('index'))

    log_lines = []
    log_file_path = 'app.log'
    try:
        with open(log_file_path, 'r') as f:
            lines = f.readlines()
            log_lines = lines[-50:]  # Get last 50 lines
            logger.info("Successfully retrieved last 50 log lines")
    except FileNotFoundError:
        logger.error(f"Log file {log_file_path} not found")
        return render_template('viewlogs.html', user=user, error="Log file not found", logs=[], current_datetime=datetime.now(ZoneInfo('Asia/Kolkata')))
    except Exception as e:
        logger.error(f"Error reading log file: {e}")
        return render_template('viewlogs.html', user=user, error=f"Error reading logs: {e}", logs=[], current_datetime=datetime.now(ZoneInfo('Asia/Kolkata')))

    return render_template('viewlogs.html', user=user, logs=log_lines, current_datetime=datetime.now(ZoneInfo('Asia/Kolkata')))

@app.route('/mail_alerts', methods=['GET', 'POST'])
def mail_alerts():
    user = session.get('user', {'username': 'Guest', 'is_admin': False})
    if not user or 'username' not in user:
        return redirect(url_for('index'))
    
    timezones = ['UTC', 'US/Pacific', 'US/Eastern', 'America/New_York', 'Asia/Kolkata', 'Europe/London']
    response = supabase.table('time').select('id', 'recipient_email', 'alert_time', 'timezone').execute()
    alerts = response.data or []
    alerts_list = [(alert.get('id'), alert.get('recipient_email', 'Unknown'), alert.get('alert_time', 'N/A'), alert.get('timezone', 'UTC')) for alert in alerts]

    current_datetime = datetime.now(ZoneInfo('Asia/Kolkata'))

    if request.method == 'POST':
        new_recipient = request.form.get('recipient')
        new_time = request.form.get('alert_time')
        new_timezone = request.form.get('timezone', 'UTC')
        send_now = 'send_now' in request.form
        due_period = request.form.get('due_period', 'Due Within 3 Days')

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
                    logger.info(f"Successfully added alert for {new_recipient} at {new_time} ({new_timezone})")
                    if send_now:
                        logger.debug(f"Send Now triggered for {new_recipient} with due_period {due_period}")
                        if not authenticate_google():
                            return render_template('mail_alerts.html', user=user, alerts=alerts_list, timezones=timezones,
                                                error="Failed to authenticate Google API", current_datetime=current_datetime)
                        due_rfps = get_due_rfps(due_period)
                        logger.debug(f"Fetched {len(due_rfps)} RFPs for {due_period}")
                        if not due_rfps:
                            return render_template('mail_alerts.html', user=user, alerts=alerts_list, timezones=timezones,
                                                error=f"No RFPs found for {due_period}", current_datetime=current_datetime)
                        subject = "RFPs Due Soon"
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
        <h2>RFP Opportunities {due_period}</h2>
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
            <td colspan="6">No RFP opportunities {due_period.lower()}.</td>
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
                            return render_template('mail_alerts.html', user=user, alerts=alerts_list, timezones=timezones,
                                                error=message, current_datetime=current_datetime)
                        return render_template('mail_alerts.html', user=user, alerts=alerts_list, timezones=timezones,
                                            message="Alert saved and email sent immediately.", current_datetime=current_datetime)
                    return redirect(url_for('mail_alerts'))
                except Exception as e:
                    logger.error(f"Error saving to Supabase: {e}")
                    return render_template('mail_alerts.html', user=user, alerts=alerts_list, timezones=timezones,
                                        error=f"Error saving alert: {e}", current_datetime=current_datetime)
            else:
                return render_template('mail_alerts.html', user=user, alerts=alerts_list, timezones=timezones,
                                    message="Maximum 20 recipients allowed.", current_datetime=current_datetime)
        elif request.form.get('action') == 'edit' and request.form.get('alert_id'):
            alert_id = request.form.get('alert_id')
            new_time = request.form.get('new_time')
            if new_time:
                try:
                    supabase.table('time').update({'alert_time': new_time}).eq('id', alert_id).execute()
                    logger.info(f"Updated alert {alert_id} time to {new_time}")
                    return redirect(url_for('mail_alerts'))
                except Exception as e:
                    logger.error(f"Error updating alert time: {e}")
                    return render_template('mail_alerts.html', user=user, alerts=alerts_list, timezones=timezones,
                                        error=f"Error updating alert time: {e}", current_datetime=current_datetime)
        return redirect(url_for('mail_alerts'))

    return render_template('mail_alerts.html', user=user, alerts=alerts_list, timezones=timezones, current_datetime=current_datetime)

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
            except Exception as e:
                logger.error(f"Error updating RFP status: {e}")
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
                    response = supabase.table('users').select('username', 'is_admin').execute()
                    users = response.data or []
                    return render_template('user_management.html', user=user, users=users, message="User added successfully", current_datetime=current_datetime, edit_username=edit_username)
                except Exception as e:
                    logger.error(f"Error adding user: {e}")
                    return render_template('user_management.html', user=user, users=users, error=f"Error adding user: {e}", current_datetime=current_datetime, edit_username=edit_username)
        elif action == 'edit_password':
            username = request.form.get('username')
            new_password = request.form.get('new_password')
            if username and new_password:
                try:
                    supabase.table('users').update({'password': new_password}).eq('username', username).execute()
                    logger.info(f"Updated password for user: {username}")
                    response = supabase.table('users').select('username', 'is_admin').execute()
                    users = response.data or []
                    return render_template('user_management.html', user=user, users=users, message=f"Password updated for {username}", current_datetime=current_datetime)
                except Exception as e:
                    logger.error(f"Error updating password: {e}")
                    return render_template('user_management.html', user=user, users=users, error=f"Error updating password: {e}", current_datetime=current_datetime, edit_username=edit_username)

    return render_template('user_management.html', user=user, users=users, current_datetime=current_datetime, edit_username=edit_username)

@app.route('/delete_user/<username>', methods=['POST'])
def delete_user(username):
    user = session.get('user', {'username': 'Guest', 'is_admin': False})
    if not user or 'username' not in user or not user.get('is_admin'):
        logger.warning("Unauthorized access to /delete_user, redirecting to index")
        return redirect(url_for('index'))
    
    if username == user['username']:
        logger.warning("Attempt to delete current user blocked")
        response = supabase.table('users').select('username', 'is_admin').execute()
        users = response.data or []
        return render_template('user_management.html', user=user, users=users, error="Cannot delete your own account", current_datetime=datetime.now(ZoneInfo('Asia/Kolkata')))
    
    try:
        supabase.table('users').delete().eq('username', username).execute()
        logger.info(f"Deleted user: {username}")
        response = supabase.table('users').select('username', 'is_admin').execute()
        users = response.data or []
        return render_template('user_management.html', user=user, users=users, message=f"User {username} deleted successfully", current_datetime=datetime.now(ZoneInfo('Asia/Kolkata')))
    except Exception as e:
        logger.error(f"Error deleting user: {e}")
        response = supabase.table('users').select('username', 'is_admin').execute()
        users = response.data or []
        return render_template('user_management.html', user=user, users=users, error=f"Error deleting user: {e}", current_datetime=datetime.now(ZoneInfo('Asia/Kolkata')))

@app.route('/edit_password/<username>', methods=['GET'])
def edit_password(username):
    user = session.get('user', {'username': 'Guest', 'is_admin': False})
    if not user or 'username' not in user or not user.get('is_admin'):
        logger.warning("Unauthorized access to /edit_password, redirecting to index")
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
    print(f" * Running on http://127.0.0.1:5000/ (Press CTRL+C to quit)")
    import webbrowser
    webbrowser.open('http://127.0.0.1:5000/')
    app.run(debug=True)
