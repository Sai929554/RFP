import os
from dotenv import load_dotenv

print(f"Current working directory: {os.getcwd()}")
print(f"Checking for credentials.env at: {os.path.abspath('credentials.env')}")
if not os.path.exists('credentials.env'):
    print("❌ Error: credentials.env file not found")
else:
    print("✅ Found credentials.env")

load_dotenv('credentials.env')
print(f"Loaded GOV_USERNAME: {os.environ.get('GOV_USERNAME')}")
print(f"Loaded GOV_PASSWORD: {os.environ.get('GOV_PASSWORD')}")