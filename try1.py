from flask import Flask, render_template, request, redirect, url_for, session
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
logging.basicConfig(level=logging.INFO)
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

# Global variables
gmail_service = None
CACHE_FILE = 'sent_emails_cache.json'
LOCK_FILE = 'email_lock.lock'
scheduler_started = False
scheduler_instance = None

def get_file_lock():
    """Get exclusive file lock to prevent concurrent email sending"""
    logger.debug("Attempting to acquire file lock")
    try:
        lock_file = open(LOCK_FILE, 'wb+')  # Open in binary mode for Windows compatibility
        if platform.system() == "Windows":
            # Use msvcrt for Windows file locking
            msvcrt.locking(lock_file.fileno(), msvcrt.LK_NBLCK, 1)
        else:
            # Use fcntl for Unix-like systems
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
                # Rewind file pointer to start before unlocking
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
                logger.info("Google API authentication successful, saved token.json")
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
    
    # Get exclusive file lock
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
        
        # Load cache
        logger.debug("Loading email cache")
        sent_emails_cache = load_cache()
        logger.info(f"Loaded cache with {len(sent_emails_cache)} entries")
        
        # Clean old cache entries (older than today)
        today_str = current_date.strftime('%Y-%m-%d')
        old_cache = sent_emails_cache.copy()
        sent_emails_cache = {k: v for k, v in sent_emails_cache.items() 
                           if isinstance(v, dict) and v.get('date') == today_str}
        
        # Save cleaned cache if changed
        if len(sent_emails_cache) != len(old_cache):
            logger.info("Cache cleaned, saving updated cache")
            save_cache(sent_emails_cache)

        for alert in alerts:
            alert_id = alert.get('id')
            recipient = alert.get('recipient_email')
            alert_time_str = alert.get('alert_time')
            timezone_str = alert.get('timezone', 'UTC')

            # Validate alert data
            if not recipient or not alert_time_str or not timezone_str or not alert_id:
                logger.warning(f"Invalid alert data: {alert}")
                continue

            try:
                # Parse alert_time and current time in alert's timezone
                alert_hour, alert_minute = map(int, alert_time_str.split(':'))
                tz = ZoneInfo(timezone_str)
                current_in_tz = current_utc.astimezone(tz)
                
                # Get current hour and minute
                current_hour = current_in_tz.hour
                current_minute = current_in_tz.minute
                
                logger.debug(f"Alert {alert_id}: Current time {current_hour:02d}:{current_minute:02d} ({timezone_str}), Alert time {alert_hour:02d}:{alert_minute:02d}")
                
                # Check if current time EXACTLY matches alert time
                if current_hour == alert_hour and current_minute == alert_minute:
                    logger.info(f"EXACT TIME MATCH! Processing alert {alert_id} for {recipient}")
                    
                    # Create unique hash for this email
                    email_hash = create_email_hash(alert_id, today_str, current_hour, current_minute)
                    logger.debug(f"Generated email hash: {email_hash}")
                    
                    # Check if this exact email was already sent
                    if email_hash in sent_emails_cache:
                        logger.info(f"Email with hash {email_hash} already sent for alert {alert_id}, skipping")
                        continue
                    
                    # Mark as sent IMMEDIATELY to prevent any duplicates
                    sent_emails_cache[email_hash] = {
                        'alert_id': alert_id,
                        'recipient': recipient,
                        'date': today_str,
                        'time': f"{current_hour:02d}:{current_minute:02d}",
                        'sent_at': current_utc.isoformat(),
                        'status': 'sent'
                    }
                    
                    # Save cache immediately
                    logger.debug("Saving cache after marking email as sent")
                    save_cache(sent_emails_cache)
                    
                    # Small delay to ensure cache is written
                    time.sleep(0.1)
                    
                    # Get RFPs and send email
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
                    
                    # Update cache with result
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
            except Exception as e:
                logger.error(f"Unexpected error processing alert for {recipient}: {e}")

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
        # Shutdown any existing scheduler first
        if scheduler_instance:
            try:
                scheduler_instance.shutdown(wait=False)
                logger.debug("Shut down existing scheduler")
            except Exception as e:
                logger.error(f"Error shutting down existing scheduler: {e}")
        
        # Initialize and start the scheduler
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
        
        # Shutdown scheduler gracefully when app exits
        atexit.register(lambda: scheduler_instance.shutdown(wait=False) if scheduler_instance else None)
        
    except Exception as e:
        logger.error(f"Error starting scheduler: {e}")

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
            if len(current_alerts) < 5:  # Allow up to 5 alerts per recipient
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

if __name__ == '__main__':
    logger.info("Starting Flask application")
    # Initialize scheduler only when running the main app
    init_scheduler()
    app.run(debug=True, use_reloader=False, threaded=True)