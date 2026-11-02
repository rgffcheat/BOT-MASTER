import asyncio
import os
import sys
import logging
import subprocess
import re
import importlib.util
import psutil
import sqlite3
import hashlib
import json
import zipfile
import shutil
import signal
import time
import html as html_lib
from datetime import datetime, timedelta
from aiogram import Bot, Dispatcher, types, F
from aiogram.filters import Command
from aiogram.types import InlineKeyboardMarkup, InlineKeyboardButton, FSInputFile
from aiogram.fsm.storage.memory import MemoryStorage
from aiogram.exceptions import TelegramRetryAfter
from aiohttp import web
import aiohttp
from pathlib import Path
from dotenv import load_dotenv, dotenv_values
import venv
import socket

load_dotenv()

logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)

TOKEN = os.getenv('BOT_TOKEN')
OWNER_ID_STR = os.getenv('OWNER_ID')
ADMIN_ID_STR = os.getenv('ADMIN_ID')
YOUR_USERNAME = os.getenv('YOUR_USERNAME')
UPDATE_CHANNEL = os.getenv('UPDATE_CHANNEL')

if not TOKEN:
    logger.error("BOT_TOKEN not found in environment variables!")
    raise ValueError("BOT_TOKEN is required. Please set it in .env file or environment variables.")

if not OWNER_ID_STR or not ADMIN_ID_STR:
    logger.error("OWNER_ID or ADMIN_ID not found in environment variables!")
    raise ValueError("OWNER_ID and ADMIN_ID are required. Please set them in .env file.")

try:
    OWNER_ID = int(OWNER_ID_STR)
    ADMIN_ID = int(ADMIN_ID_STR)
except ValueError:
    logger.error("OWNER_ID or ADMIN_ID must be valid integers!")
    raise

YOUR_USERNAME = '@RGCHEAT99'
UPDATE_CHANNEL = 'https://t.me/+gxNKatV44H8xYWJl'
YOUTUBE_CHANNEL = 'https://youtube.com/@geniushacker29'
CHANNEL_USERNAME = '@' + UPDATE_CHANNEL.rstrip('/').split('/')[-1]

BASE_DIR = Path(__file__).parent.absolute()
UPLOAD_BOTS_DIR = BASE_DIR / 'upload_bots'
IROTECH_DIR = BASE_DIR / 'inf'
DATABASE_PATH = IROTECH_DIR / 'bot_data.db'

FREE_USER_LIMIT = float('inf')
SUBSCRIBED_USER_LIMIT = float('inf')
ADMIN_LIMIT = 999
OWNER_LIMIT = float('inf')
USER_RUN_LIMIT = 2   # normal users: max 2 bots running at the same time (admins/owner: unlimited)

UPLOAD_BOTS_DIR.mkdir(parents=True, exist_ok=True)
IROTECH_DIR.mkdir(exist_ok=True)

bot = Bot(token=TOKEN)
dp = Dispatcher(storage=MemoryStorage())
BOT_START_TIME = datetime.now()

bot_scripts = {}
_bot_start_lock = asyncio.Lock()

def _project_id(user_id: int, file_name: str) -> str:
    digest = hashlib.sha256(f"{user_id}:{file_name}".encode()).hexdigest()[:12]
    return f"{re.sub(r'[^A-Za-z0-9_-]', '_', Path(file_name).stem)[:32]}_{digest}"

def _project_workspace(user_id: int, file_name: str) -> Path:
    return UPLOAD_BOTS_DIR / str(user_id) / "projects" / _project_id(user_id, file_name)
user_subscriptions = {}
user_files = {}
user_favorites = {}
banned_users = set()
active_users = set()
admin_ids = {ADMIN_ID, OWNER_ID}
bot_locked = False
bot_stats = {'total_uploads': 0, 'total_downloads': 0, 'total_runs': 0}

def migrate_db():
    logger.info("Running database migrations...")
    try:
        conn = sqlite3.connect(DATABASE_PATH)
        c = conn.cursor()
        
        c.execute("PRAGMA table_info(user_files)")
        columns = [row[1] for row in c.fetchall()]
        if 'upload_date' not in columns:
            logger.info("Adding upload_date column to user_files table...")
            c.execute('ALTER TABLE user_files ADD COLUMN upload_date TEXT')
            logger.info("upload_date column added successfully.")
        
        c.execute("PRAGMA table_info(active_users)")
        columns = [row[1] for row in c.fetchall()]
        if 'join_date' not in columns:
            logger.info("Adding join_date column to active_users table...")
            c.execute('ALTER TABLE active_users ADD COLUMN join_date TEXT')
            logger.info("join_date column added successfully.")
        if 'last_active' not in columns:
            logger.info("Adding last_active column to active_users table...")
            c.execute('ALTER TABLE active_users ADD COLUMN last_active TEXT')
            logger.info("last_active column added successfully.")
        
        conn.commit()
        conn.close()
        logger.info("Database migrations completed successfully.")
    except Exception as e:
        logger.error(f"Database migration error: {e}", exc_info=True)

def init_db():
    logger.info(f"Initializing database at: {DATABASE_PATH}")
    try:
        conn = sqlite3.connect(DATABASE_PATH)
        c = conn.cursor()
        c.execute('''CREATE TABLE IF NOT EXISTS subscriptions
                     (user_id INTEGER PRIMARY KEY, expiry TEXT)''')
        c.execute('''CREATE TABLE IF NOT EXISTS user_files
                     (user_id INTEGER, file_name TEXT, file_type TEXT, upload_date TEXT,
                      PRIMARY KEY (user_id, file_name))''')
        c.execute('''CREATE TABLE IF NOT EXISTS active_users
                     (user_id INTEGER PRIMARY KEY, join_date TEXT, last_active TEXT)''')
        c.execute('''CREATE TABLE IF NOT EXISTS admins
                     (user_id INTEGER PRIMARY KEY)''')
        c.execute('''CREATE TABLE IF NOT EXISTS banned_users
                     (user_id INTEGER PRIMARY KEY, banned_date TEXT, reason TEXT)''')
        c.execute('''CREATE TABLE IF NOT EXISTS favorites
                     (user_id INTEGER, file_name TEXT, PRIMARY KEY (user_id, file_name))''')
        c.execute('''CREATE TABLE IF NOT EXISTS bot_stats
                     (stat_name TEXT PRIMARY KEY, stat_value INTEGER)''')
        
        c.execute('INSERT OR IGNORE INTO admins (user_id) VALUES (?)', (OWNER_ID,))
        if ADMIN_ID != OWNER_ID:
            c.execute('INSERT OR IGNORE INTO admins (user_id) VALUES (?)', (ADMIN_ID,))
        
        for stat in ['total_uploads', 'total_downloads', 'total_runs']:
            c.execute('INSERT OR IGNORE INTO bot_stats (stat_name, stat_value) VALUES (?, 0)', (stat,))
        c.execute('''CREATE TABLE IF NOT EXISTS bot_run_history
                     (id INTEGER PRIMARY KEY AUTOINCREMENT, user_id INTEGER, file_name TEXT,
                      project_type TEXT, status TEXT, started_at TEXT, finished_at TEXT,
                      exit_code INTEGER, log_path TEXT)''')
        
        conn.commit()
        conn.close()
        logger.info("Database initialized successfully.")
    except Exception as e:
        logger.error(f"Database initialization error: {e}", exc_info=True)

def load_data():
    logger.info("Loading data from database...")
    try:
        conn = sqlite3.connect(DATABASE_PATH)
        c = conn.cursor()
        
        c.execute('SELECT user_id, expiry FROM subscriptions')
        for user_id, expiry in c.fetchall():
            try:
                user_subscriptions[user_id] = {'expiry': datetime.fromisoformat(expiry)}
            except ValueError:
                logger.warning(f"Invalid expiry date for user {user_id}")
        
        c.execute('SELECT user_id, file_name, file_type FROM user_files')
        for user_id, file_name, file_type in c.fetchall():
            if user_id not in user_files:
                user_files[user_id] = []
            user_files[user_id].append((file_name, file_type))
        
        c.execute('SELECT user_id FROM active_users')
        active_users.update(user_id for (user_id,) in c.fetchall())
        
        c.execute('SELECT user_id FROM admins')
        admin_ids.update(user_id for (user_id,) in c.fetchall())
        
        c.execute('SELECT user_id FROM banned_users')
        banned_users.update(user_id for (user_id,) in c.fetchall())
        
        c.execute('SELECT user_id, file_name FROM favorites')
        for user_id, file_name in c.fetchall():
            if user_id not in user_favorites:
                user_favorites[user_id] = []
            user_favorites[user_id].append(file_name)
        
        c.execute('SELECT stat_name, stat_value FROM bot_stats')
        for stat_name, stat_value in c.fetchall():
            bot_stats[stat_name] = stat_value
        
        conn.close()
        logger.info(f"Data loaded: {len(active_users)} users, {len(banned_users)} banned, {len(admin_ids)} admins.")
    except Exception as e:
        logger.error(f"Error loading data: {e}", exc_info=True)

init_db()
migrate_db()
load_data()

# ── AUTO DEPENDENCY INSTALLER ────────────────────────
# Import name → actual pip package name (jab dono alag hote hain)
IMPORT_TO_PIP = {
    'telebot': 'pyTelegramBotAPI',
    'telegram': 'python-telegram-bot',
    'pyrogram': 'pyrogram',
    'tgcrypto': 'TgCrypto',
    'PIL': 'Pillow',
    'cv2': 'opencv-python-headless',
    'bs4': 'beautifulsoup4',
    'yaml': 'PyYAML',
    'dotenv': 'python-dotenv',
    'Crypto': 'pycryptodome',
    'Cryptodome': 'pycryptodomex',
    'jwt': 'PyJWT',
    'dateutil': 'python-dateutil',
    'discord': 'discord.py',
    'yt_dlp': 'yt-dlp',
    'youtube_dl': 'youtube-dl',
    'sklearn': 'scikit-learn',
    'websocket': 'websocket-client',
    'serial': 'pyserial',
}

# Python built-in modules — inhe kabhi install karne ki koshish nahi karni
STDLIB_MODULES = set(sys.stdlib_module_names) if hasattr(sys, 'stdlib_module_names') else {
    'os', 'sys', 'time', 'json', 're', 'math', 'random', 'datetime', 'collections',
    'itertools', 'functools', 'subprocess', 'threading', 'asyncio', 'socket', 'io',
    'sqlite3', 'hashlib', 'base64', 'logging', 'pathlib', 'shutil', 'zipfile',
    'urllib', 'http', 'email', 'csv', 'string', 'copy', 'typing', 'traceback',
    'signal', 'struct', 'queue', 'multiprocessing', 'abc', 'enum', 'uuid', 'glob'
}

def extract_imports(file_path):
    """File ke andar se saare top-level 'import X' / 'from X import Y' nikalta hai"""
    modules = set()
    try:
        content = Path(file_path).read_text(errors='ignore')
        for match in re.finditer(r'^\s*(?:import|from)\s+([a-zA-Z0-9_\.]+)', content, re.MULTILINE):
            top_module = match.group(1).split('.')[0]
            modules.add(top_module)
    except Exception as e:
        logger.error(f"Import extraction error: {e}")
    return modules

def install_missing_dependencies(file_path, timeout=90):
    """Script mein use ho rahi libraries check karke jo missing hain unhe pip se install karta hai.
    Returns: (installed_list, failed_list)"""
    modules = extract_imports(file_path)
    installed, failed = [], []

    for mod in modules:
        if mod in STDLIB_MODULES or mod in ('__future__',):
            continue
        if importlib.util.find_spec(mod) is not None:
            continue  # already installed

        pip_name = IMPORT_TO_PIP.get(mod, mod)
        try:
            result = subprocess.run(
                [sys.executable, '-m', 'pip', 'install', pip_name, '--break-system-packages', '--quiet'],
                capture_output=True, text=True, timeout=timeout
            )
            if result.returncode == 0:
                installed.append(pip_name)
            else:
                failed.append(pip_name)
        except Exception as e:
            logger.error(f"pip install error for {pip_name}: {e}")
            failed.append(pip_name)

    return installed, failed

def get_user_file_limit(user_id):
    return OWNER_LIMIT  # Sabke liye unlimited — koi upload limit nahi

def format_limit(limit):
    return "Unlimited ♾️" if limit == float('inf') else f"{limit} files"

def get_main_keyboard(user_id):
    if user_id in admin_ids:
        keyboard = InlineKeyboardMarkup(inline_keyboard=[
            [InlineKeyboardButton(text="📢 Updates", url=UPDATE_CHANNEL)],
            [InlineKeyboardButton(text="📤 Upload File", callback_data="upload_file"),
             InlineKeyboardButton(text="📁 My Files", callback_data="check_files")],
            [InlineKeyboardButton(text="🔍 Search Files", callback_data="search_files"),
             InlineKeyboardButton(text="⚡ Bot Speed", callback_data="bot_speed")],
            [InlineKeyboardButton(text="📊 My Stats", callback_data="statistics"),
             InlineKeyboardButton(text="👑 Admin Panel", callback_data="admin_panel")],
            [InlineKeyboardButton(text="💬 Contact", url=f"https://t.me/{YOUR_USERNAME.replace('@', '')}")]
        ])
    else:
        keyboard = InlineKeyboardMarkup(inline_keyboard=[
            [InlineKeyboardButton(text="📢 Updates Channel", url=UPDATE_CHANNEL)],
            [InlineKeyboardButton(text="📤 Upload File", callback_data="upload_file"),
             InlineKeyboardButton(text="📁 My Files", callback_data="check_files")],
            [InlineKeyboardButton(text="🔍 Search Files", callback_data="search_files"),
             InlineKeyboardButton(text="⚡ Bot Speed", callback_data="bot_speed")],
            [InlineKeyboardButton(text="📊 My Stats", callback_data="statistics")],
            [InlineKeyboardButton(text="💬 Contact Owner", url=f"https://t.me/{YOUR_USERNAME.replace('@', '')}")]
        ])
    return keyboard

def get_admin_panel_keyboard():
    keyboard = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="⏱️ Bot Uptime", callback_data="admin_bot_uptime")],
        [InlineKeyboardButton(text="👥 Total Users", callback_data="admin_total_users_simple")],
        [InlineKeyboardButton(text="📝 Logs", callback_data="admin_view_logs")],
        [InlineKeyboardButton(text="🏠 Main Menu", callback_data="back_to_main")]
    ])
    return keyboard

def build_welcome_text(user_id: int, full_name: str) -> str:
    return f"""╔═══════════════════════╗
    🚀 <b>RG CHEAT</b> 🚀
    ⚡ <i>Script Runner Bot</i>
╚═══════════════════════╝

👋 <b>Welcome, {full_name}!</b>

🆔 <b>Your ID:</b> <code>{user_id}</code>
📦 <b>Upload Limit:</b> Unlimited ♾️
🤖 <b>Running Bots:</b> {'Unlimited ♾️' if user_id in admin_ids else str(USER_RUN_LIMIT) + ' bots at a time'}

━━━━━━━━━━━━━━━━━━━━
<b>🔥 AVAILABLE FEATURES</b>

📤 <b>Upload Files</b> — Python (.py), ZIP Python projects
📁 <b>Manage Files</b> — View, delete, organize
🔍 <b>Search Files</b> — Find by name/type
▶️ <b>Run Scripts</b> — Execute Python
🛑 <b>Stop Scripts</b> — Force stop running
📊 <b>View Stats</b> — Usage & storage
⚡ <b>Speed Test</b> — Bot response time
💾 <b>File Info</b> — Size, type, date
ℹ️ <b>Help &amp; Support</b> — Get assistance

━━━━━━━━━━━━━━━━━━━━
⚡ <b>Developed by</b> RG CHEAT
🔒 <b>Version:</b> 2.0"""

@dp.message(Command("start"))
async def cmd_start(message: types.Message):
    user_id = message.from_user.id
    
    if user_id in banned_users:
        await message.answer("🚫 <b>You are banned from using this bot!</b>\n\nContact admin for more info.", parse_mode="HTML")
        return
    
    active_users.add(user_id)
    
    try:
        conn = sqlite3.connect(DATABASE_PATH)
        c = conn.cursor()
        now = datetime.now().isoformat()
        c.execute('INSERT OR IGNORE INTO active_users (user_id, join_date, last_active) VALUES (?, ?, ?)', 
                  (user_id, now, now))
        c.execute('UPDATE active_users SET last_active = ? WHERE user_id = ?', (now, user_id))
        conn.commit()
        conn.close()
    except Exception as e:
        logger.error(f"Error saving active user: {e}")
    
    welcome_text = build_welcome_text(user_id, message.from_user.full_name)
    await message.answer(welcome_text, reply_markup=get_main_keyboard(user_id), parse_mode="HTML")

@dp.callback_query(F.data == "back_to_main")
async def callback_back_to_main(callback: types.CallbackQuery):
    user_id = callback.from_user.id
    
    welcome_text = f"""
╔═══════════════════════╗
    🏠 <b>MAIN MENU</b> 🏠
╚═══════════════════════╝

👤 <b>User:</b> {callback.from_user.full_name}
🆔 <b>ID:</b> <code>{user_id}</code>
📦 <b>Files:</b> {len(user_files.get(user_id, []))} (Unlimited ♾️)

Use buttons below to navigate 👇
"""
    await callback.message.edit_text(welcome_text, reply_markup=get_main_keyboard(user_id), parse_mode="HTML")
    await callback.answer()

@dp.callback_query(F.data == "upload_file")
async def callback_upload_file(callback: types.CallbackQuery):
    user_id = callback.from_user.id
    
    if bot_locked and user_id not in admin_ids:
        await callback.answer("🔒 Bot is locked for maintenance!", show_alert=True)
        return
    
    current_files = len(user_files.get(user_id, []))
    limit = get_user_file_limit(user_id)
    
    upload_text = f"""
╔═══════════════════════╗
    📤 <b>UPLOAD FILES</b> 📤
╚═══════════════════════╝

📊 <b>Current Usage:</b> {current_files} files (Unlimited ♾️)

📝 <b>Supported Formats:</b>
🐍 Python (.py)

📦 ZIP Archives (.zip)

━━━━━━━━━━━━━━━━━━━━
<b>💡 How to Upload:</b>

1️⃣ Send your file to the bot
2️⃣ Wait for upload confirmation
3️⃣ File will be saved automatically

⚡ <b>Upload limit:</b> {limit} files
🔥 <b>Quick & Easy!</b>
"""
    
    back_keyboard = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🏠 Main Menu", callback_data="back_to_main")]
    ])
    
    await callback.message.edit_text(upload_text, reply_markup=back_keyboard, parse_mode="HTML")
    await callback.answer()

@dp.callback_query(F.data == "check_files")
async def callback_check_files(callback: types.CallbackQuery):
    user_id = callback.from_user.id
    files = user_files.get(user_id, [])
    
    if not files:
        text = """
╔═══════════════════════╗
    📁 <b>MY FILES</b> 📁
╚═══════════════════════╝

📭 <b>No files found!</b>

Upload your first file to get started! 🚀
"""
        back_keyboard = InlineKeyboardMarkup(inline_keyboard=[
            [InlineKeyboardButton(text="📤 Upload File", callback_data="upload_file")],
            [InlineKeyboardButton(text="🏠 Main Menu", callback_data="back_to_main")]
        ])
    else:
        text = f"""
╔═══════════════════════╗
    📁 <b>MY FILES ({len(files)})</b> 📁
╚═══════════════════════╝

"""
        buttons = []
        for i, (file_name, file_type) in enumerate(files, 1):
            icon = "🐍" if file_type == "py" else "🟨" if file_type == "js" else "📦"
            text += f"{i}. {icon} <code>{file_name}</code>\n"
            
            is_favorite = file_name in user_favorites.get(user_id, [])
            star = "⭐" if is_favorite else "☆"
            
            run_callback = f"run_project:{file_name}" if file_type == 'zip' else f"run_script:{file_name}"
            run_label = f"🚀 Run Bot {file_name[:13]}" if file_type == 'zip' else f"▶️ Run {file_name[:15]}"
            buttons.append([
                InlineKeyboardButton(text=run_label, callback_data=run_callback),
                InlineKeyboardButton(text=f"{star}", callback_data=f"toggle_fav:{file_name}")
            ])
            buttons.append([
                InlineKeyboardButton(text=f"ℹ️ Info {file_name[:15]}", callback_data=f"file_info:{file_name}"),
                InlineKeyboardButton(text=f"🗑️ Delete", callback_data=f"delete_file:{file_name}")
            ])
        
        buttons.append([InlineKeyboardButton(text="🏠 Main Menu", callback_data="back_to_main")])
        back_keyboard = InlineKeyboardMarkup(inline_keyboard=buttons)
    
    await callback.message.edit_text(text, reply_markup=back_keyboard, parse_mode="HTML")
    await callback.answer()

@dp.callback_query(F.data == "my_favorites")
async def callback_my_favorites(callback: types.CallbackQuery):
    user_id = callback.from_user.id
    favorites = user_favorites.get(user_id, [])
    
    if not favorites:
        text = """
╔═══════════════════════╗
    ⭐ <b>FAVORITES</b> ⭐
╚═══════════════════════╝

💭 No favorite files yet!

Add files to favorites for quick access! 🚀
"""
        buttons = [[InlineKeyboardButton(text="🏠 Main Menu", callback_data="back_to_main")]]
    else:
        text = f"""
╔═══════════════════════╗
    ⭐ <b>FAVORITES ({len(favorites)})</b> ⭐
╚═══════════════════════╝

"""
        buttons = []
        for i, file_name in enumerate(favorites, 1):
            text += f"{i}. ⭐ <code>{file_name}</code>\n"
            fav_type = next((ft for fn, ft in user_files.get(user_id, []) if fn == file_name), 'py')
            fav_callback = f"run_project:{file_name}" if fav_type == 'zip' else f"run_script:{file_name}"
            buttons.append([
                InlineKeyboardButton(text=f"🚀 {file_name[:18]}", callback_data=fav_callback),
                InlineKeyboardButton(text=f"❌", callback_data=f"toggle_fav:{file_name}")
            ])
        
        buttons.append([InlineKeyboardButton(text="🏠 Main Menu", callback_data="back_to_main")])
    
    back_keyboard = InlineKeyboardMarkup(inline_keyboard=buttons)
    await callback.message.edit_text(text, reply_markup=back_keyboard, parse_mode="HTML")
    await callback.answer()

@dp.callback_query(F.data == "search_files")
async def callback_search_files(callback: types.CallbackQuery):
    user_id = callback.from_user.id
    files = user_files.get(user_id, [])
    
    text = f"""
╔═══════════════════════╗
    🔍 <b>SEARCH FILES</b> 🔍
╚═══════════════════════╝

📊 <b>Total Files:</b> {len(files)}

<b>File Types:</b>
🐍 Python: {sum(1 for f in files if f[1] == 'py')}
📦 ZIP: {sum(1 for f in files if f[1] == 'zip')}

━━━━━━━━━━━━━━━━━━━━
To search, use:
<code>/search filename</code>
"""
    
    back_keyboard = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="📁 View All Files", callback_data="check_files")],
        [InlineKeyboardButton(text="🏠 Main Menu", callback_data="back_to_main")]
    ])
    
    await callback.message.edit_text(text, reply_markup=back_keyboard, parse_mode="HTML")
    await callback.answer()

@dp.callback_query(F.data == "bot_speed")
async def callback_bot_speed(callback: types.CallbackQuery):
    start_time = datetime.now()
    await callback.answer("⚡ Testing...")
    end_time = datetime.now()
    speed = (end_time - start_time).total_seconds() * 1000
    
    if speed < 100:
        status = "🟢 Excellent"
        emoji = "🚀"
    elif speed < 300:
        status = "🟡 Good"
        emoji = "⚡"
    else:
        status = "🔴 Slow"
        emoji = "🐌"
    
    text = f"""
╔═══════════════════════╗
    ⚡ <b>SPEED TEST</b> ⚡
╚═══════════════════════╝

{emoji} <b>Response Time:</b> {speed:.2f}ms
📊 <b>Status:</b> {status}

🖥️ <b>Server Info:</b>
• CPU: {psutil.cpu_percent()}%
• Memory: {psutil.virtual_memory().percent}%
• Uptime: Online ✅

✨ Bot is running smoothly!
"""
    
    back_keyboard = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🔄 Test Again", callback_data="bot_speed"),
         InlineKeyboardButton(text="🏠 Home", callback_data="back_to_main")]
    ])
    
    await callback.message.edit_text(text, reply_markup=back_keyboard, parse_mode="HTML")

@dp.callback_query(F.data == "statistics")
async def callback_statistics(callback: types.CallbackQuery):
    user_id = callback.from_user.id
    
    user_file_count = len(user_files.get(user_id, []))
    user_fav_count = len(user_favorites.get(user_id, []))
    limit = get_user_file_limit(user_id)
    is_premium = user_id in user_subscriptions
    
    text = f"""
╔═══════════════════════╗
    📊 <b>YOUR STATISTICS</b> 📊
╚═══════════════════════╝

👤 <b>User:</b> {callback.from_user.full_name}
🆔 <b>ID:</b> <code>{user_id}</code>

━━━━━━━━━━━━━━━━━━━━
📦 <b>FILE STATISTICS:</b>

📁 Total Files: {user_file_count} (Unlimited ♾️)
⭐ Favorites: {user_fav_count}
💎 Account: Free 🆓 (Unlimited ♾️)
🚀 Running: {sum(1 for k in bot_scripts if k.startswith(f"{user_id}_"))}

━━━━━━━━━━━━━━━━━━━━
📈 <b>USAGE:</b>

📤 Uploads: {bot_stats.get('total_uploads', 0)}
📥 Downloads: {bot_stats.get('total_downloads', 0)}
▶️ Script Runs: {bot_stats.get('total_runs', 0)}

{'✅ Bot Status: Active' if not bot_locked else '🔒 Bot: Maintenance'}
"""
    
    if user_id in admin_ids:
        text += f"\n━━━━━━━━━━━━━━━━━━━━\n👑 <b>ADMIN STATS:</b>\n"
        text += f"👥 Total Users: {len(active_users)}\n"
        text += f"📁 Total Files: {sum(len(files) for files in user_files.values())}\n"
    
    back_keyboard = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🏠 Main Menu", callback_data="back_to_main")]
    ])
    
    await callback.message.edit_text(text, reply_markup=back_keyboard, parse_mode="HTML")
    await callback.answer()

@dp.callback_query(F.data == "help_info")
async def callback_help_info(callback: types.CallbackQuery):
    text = """
╔═══════════════════════╗
    ℹ️ <b>HELP & INFO</b> ℹ️
╚═══════════════════════╝

<b>🎯 HOW TO USE:</b>

1️⃣ <b>Upload Files:</b>
   • Click 'Upload File'
   • Send your .py or .zip Python project
   • File will be saved automatically

2️⃣ <b>Run Scripts:</b>
   • Go to 'My Files'
   • Click 'Run' on any file
   • Monitor script execution

3️⃣ <b>Manage Files:</b>
   • View all files in 'My Files'
   • Add to favorites with ⭐
   • Delete unwanted files

4️⃣ <b>Search:</b>
   • Use /search [filename]
   • Quick file lookup

━━━━━━━━━━━━━━━━━━━━
<b>💡 COMMANDS:</b>

/start - Start the bot
/help - Show this help
/search - Search files
/stats - Your statistics
/premium - Free info

<b>Need help? Contact owner! 💬</b>
"""
    
    back_keyboard = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🎯 Features", callback_data="all_features")],
        [InlineKeyboardButton(text="🏠 Main Menu", callback_data="back_to_main")]
    ])
    
    await callback.message.edit_text(text, reply_markup=back_keyboard, parse_mode="HTML")
    await callback.answer()

@dp.callback_query(F.data == "all_features")
async def callback_all_features(callback: types.CallbackQuery):
    text = """
╔═══════════════════════╗
    🎯 <b>ALL FEATURES</b> 🎯
╚═══════════════════════╝

<b>✨ FREE USER FEATURES (12+):</b>

1. 📤 Upload Files (Python (.py), ZIP Python projects)
2. 📁 View & Manage Files
3. ⭐ Add to Favorites
4. 🔍 Search Files by Name
5. ▶️ Run Python Scripts
6. ▶️ Run Python Bots
7. 🛑 Stop Running Scripts
8. 📊 View Your Statistics
9. ⚡ Bot Speed Test
10. 📥 Download Your Files
11. 💾 View File Information
12. ℹ️ Help & Support
13. 🎯 Feature Discovery

━━━━━━━━━━━━━━━━━━━━
<b>🆓 SAB KUCH FREE HAI!</b>

• Unlimited file uploads
• Koi premium plan nahi
• Sabke liye same features
"""
    
    back_keyboard = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🏠 Main Menu", callback_data="back_to_main")]
    ])
    
    await callback.message.edit_text(text, reply_markup=back_keyboard, parse_mode="HTML")
    await callback.answer()

@dp.callback_query(F.data == "get_premium")
async def callback_get_premium(callback: types.CallbackQuery):
    text = """
╔═══════════════════════╗
    🆓 <b>100% FREE</b> 🆓
╚═══════════════════════╝

Is bot mein <b>koi premium plan nahi</b> hai.
✅ Unlimited uploads
✅ Saare features sabke liye free

Help chahiye? Owner se contact karo 💬
"""
    back_keyboard = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="💬 Contact Owner", url=f"https://t.me/{YOUR_USERNAME.replace('@', '')}")],
        [InlineKeyboardButton(text="🏠 Main Menu", callback_data="back_to_main")]
    ])
    await callback.message.edit_text(text, reply_markup=back_keyboard, parse_mode="HTML")
    await callback.answer()

@dp.callback_query(F.data == "admin_panel")
async def callback_admin_panel(callback: types.CallbackQuery):
    user_id = callback.from_user.id
    
    if user_id not in admin_ids:
        await callback.answer("❌ Admin access required!", show_alert=True)
        return
    
    text = """
╔═══════════════════════╗
    👑 <b>ADMIN PANEL</b> 👑
╚═══════════════════════╝

Select an option below 👇
"""
    
    await callback.message.edit_text(text, reply_markup=get_admin_panel_keyboard(), parse_mode="HTML")
    await callback.answer()

@dp.callback_query(F.data == "admin_bot_uptime")
async def callback_admin_bot_uptime(callback: types.CallbackQuery):
    user_id = callback.from_user.id
    if user_id not in admin_ids:
        await callback.answer("❌ Admin access required!", show_alert=True)
        return

    delta = datetime.now() - BOT_START_TIME
    days = delta.days
    hours, rem = divmod(delta.seconds, 3600)
    minutes, seconds = divmod(rem, 60)

    text = f"""╔═══════════════════════╗
    ⏱️ <b>BOT UPTIME</b> ⏱️
╚═══════════════════════╝

🟢 <b>Status:</b> Running
📅 <b>Started:</b> {BOT_START_TIME.strftime('%d %b %Y, %I:%M %p')}
⏳ <b>Uptime:</b> {days}d {hours}h {minutes}m {seconds}s"""

    back_keyboard = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🔙 Back", callback_data="admin_panel")]
    ])
    await callback.message.edit_text(text, reply_markup=back_keyboard, parse_mode="HTML")
    await callback.answer()

@dp.callback_query(F.data == "admin_total_users_simple")
async def callback_admin_total_users_simple(callback: types.CallbackQuery):
    user_id = callback.from_user.id
    if user_id not in admin_ids:
        await callback.answer("❌ Admin access required!", show_alert=True)
        return

    total_users = len(active_users)
    total_active_scripts = len(bot_scripts)

    text = f"""╔═══════════════════════╗
    👥 <b>TOTAL USERS</b> 👥
╚═══════════════════════╝

👤 <b>Total Users:</b> {total_users}
▶️ <b>Currently Running Scripts:</b> {total_active_scripts}"""

    back_keyboard = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🔙 Back", callback_data="admin_panel")]
    ])
    await callback.message.edit_text(text, reply_markup=back_keyboard, parse_mode="HTML")
    await callback.answer()

@dp.callback_query(F.data.startswith("toggle_fav:"))
async def callback_toggle_favorite(callback: types.CallbackQuery):
    user_id = callback.from_user.id
    file_name = callback.data.split(":", 1)[1]
    
    if user_id not in user_favorites:
        user_favorites[user_id] = []
    
    try:
        conn = sqlite3.connect(DATABASE_PATH)
        c = conn.cursor()
        
        if file_name in user_favorites[user_id]:
            user_favorites[user_id].remove(file_name)
            c.execute('DELETE FROM favorites WHERE user_id = ? AND file_name = ?', (user_id, file_name))
            await callback.answer("❌ Removed from favorites!", show_alert=True)
        else:
            user_favorites[user_id].append(file_name)
            c.execute('INSERT OR IGNORE INTO favorites (user_id, file_name) VALUES (?, ?)', (user_id, file_name))
            await callback.answer("⭐ Added to favorites!", show_alert=True)
        
        conn.commit()
        conn.close()
        
        await callback_check_files(callback)
        
    except Exception as e:
        logger.error(f"Error toggling favorite: {e}")
        await callback.answer(f"❌ Error: {str(e)}", show_alert=True)

@dp.callback_query(F.data.startswith("file_info:"))
async def callback_file_info(callback: types.CallbackQuery):
    user_id = callback.from_user.id
    file_name = callback.data.split(":", 1)[1]
    
    user_folder = UPLOAD_BOTS_DIR / str(user_id)
    file_path = user_folder / file_name
    
    if not file_path.exists():
        await callback.answer("❌ File not found!", show_alert=True)
        return
    
    file_size = file_path.stat().st_size
    file_size_mb = file_size / (1024 * 1024)
    file_ext = file_path.suffix
    modified_time = datetime.fromtimestamp(file_path.stat().st_mtime)
    
    is_favorite = file_name in user_favorites.get(user_id, [])
    
    text = f"""
╔═══════════════════════╗
    ℹ️ <b>FILE INFO</b> ℹ️
╚═══════════════════════╝

📄 <b>Name:</b> <code>{file_name}</code>

📦 <b>Type:</b> {file_ext.upper()} File
💾 <b>Size:</b> {file_size_mb:.2f} MB ({file_size} bytes)
📅 <b>Modified:</b> {modified_time.strftime('%Y-%m-%d %H:%M')}
⭐ <b>Favorite:</b> {'Yes ✨' if is_favorite else 'No'}

🔐 <b>MD5:</b> <code>{hashlib.md5(file_path.read_bytes()).hexdigest()[:16]}...</code>
"""
    
    back_keyboard = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="▶️ Run", callback_data=f"run_script:{file_name}"),
         InlineKeyboardButton(text="🗑️ Delete", callback_data=f"delete_file:{file_name}")],
        [InlineKeyboardButton(text="📁 My Files", callback_data="check_files"),
         InlineKeyboardButton(text="🏠 Home", callback_data="back_to_main")]
    ])
    
    await callback.message.edit_text(text, reply_markup=back_keyboard, parse_mode="HTML")
    await callback.answer()

@dp.message(F.document)
async def handle_document(message: types.Message):
    user_id = message.from_user.id
    
    if user_id in banned_users:
        await message.answer("🚫 You are banned from using this bot!")
        return
    
    if bot_locked and user_id not in admin_ids:
        await message.answer("🔒 Bot is currently locked!")
        return
    
    document = message.document
    original_name = Path(document.file_name or "uploaded_file").name
    original_suffix = Path(original_name).suffix.lower()
    safe_stem = re.sub(r"[^A-Za-z0-9_. -]", "_", Path(original_name).stem)[:34].strip(" ._") or "uploaded"
    file_name = safe_stem + original_suffix
    file_ext = original_suffix
    if user_id in admin_ids and file_ext == '.zip' and original_name.upper().startswith('RG_FULL_BACKUP'):
        await _restore_full_backup(message, document)
        return
    # Keep repeated uploads as separate projects instead of overwriting an existing bot.
    if (UPLOAD_BOTS_DIR / str(user_id) / file_name).exists():
        suffix = hashlib.sha256(f"{user_id}:{document.file_unique_id}:{time.time_ns()}".encode()).hexdigest()[:6]
        file_name = f"{safe_stem[:26]}_{suffix}{original_suffix}"
    
    if file_ext not in ['.py', '.zip']:
        await message.answer("❌ Only Python .py files and complete Python .zip projects are supported!")
        return
    
    current_files = len(user_files.get(user_id, []))
    limit = get_user_file_limit(user_id)
    
    if current_files >= limit:
        await message.answer(f"❌ Upload limit reached! ({current_files}/{limit})")
        return
    
    user_folder = UPLOAD_BOTS_DIR / str(user_id)
    user_folder.mkdir(exist_ok=True)
    
    file_path = user_folder / file_name
    
    try:
        file_size_kb = document.file_size / 1024
        
        status_msg = await message.answer(
            f"📤 <b>Preparing upload...</b>\n\n"
            f"📄 File: <code>{file_name}</code>\n"
            f"💾 Size: {file_size_kb:.2f} KB\n\n"
            f"▓░░░░░░░░░ 0%",
            parse_mode="HTML"
        )
        
        await asyncio.sleep(0.3)
        await status_msg.edit_text(
            f"📥 <b>Downloading...</b>\n\n"
            f"📄 File: <code>{file_name}</code>\n"
            f"💾 Size: {file_size_kb:.2f} KB\n\n"
            f"▓▓▓░░░░░░░ 30%",
            parse_mode="HTML"
        )
        
        await bot.download(document, destination=file_path)
        
        await status_msg.edit_text(
            f"💾 <b>Saving to database...</b>\n\n"
            f"📄 File: <code>{file_name}</code>\n"
            f"💾 Size: {file_size_kb:.2f} KB\n\n"
            f"▓▓▓▓▓▓▓░░░ 70%",
            parse_mode="HTML"
        )
        
        if user_id not in user_files:
            user_files[user_id] = []
        
        user_files[user_id].append((file_name, file_ext[1:]))
        
        conn = sqlite3.connect(DATABASE_PATH)
        c = conn.cursor()
        now = datetime.now().isoformat()
        c.execute('INSERT OR REPLACE INTO user_files (user_id, file_name, file_type, upload_date) VALUES (?, ?, ?, ?)',
                  (user_id, file_name, file_ext[1:], now))
        c.execute('UPDATE bot_stats SET stat_value = stat_value + 1 WHERE stat_name = ?', ('total_uploads',))
        conn.commit()
        conn.close()
        
        bot_stats['total_uploads'] = bot_stats.get('total_uploads', 0) + 1
        
        await status_msg.edit_text(
            f"✅ <b>Finalizing...</b>\n\n"
            f"📄 File: <code>{file_name}</code>\n"
            f"💾 Size: {file_size_kb:.2f} KB\n\n"
            f"▓▓▓▓▓▓▓▓▓▓ 100%",
            parse_mode="HTML"
        )
        
        await asyncio.sleep(0.5)
        
        if file_ext == '.zip':
            keyboard = InlineKeyboardMarkup(inline_keyboard=[
                [InlineKeyboardButton(text="🚀 Run Bot Project", callback_data=f"run_project:{file_name}"),
                 InlineKeyboardButton(text="📦 Extract ZIP", callback_data=f"extract_zip:{file_name}")],
                [InlineKeyboardButton(text="⭐ Add Favorite", callback_data=f"toggle_fav:{file_name}"),
                 InlineKeyboardButton(text="ℹ️ File Info", callback_data=f"file_info:{file_name}")],
                [InlineKeyboardButton(text="🗑️ Delete", callback_data=f"delete_file:{file_name}")],
                [InlineKeyboardButton(text="📁 My Files", callback_data="check_files"),
                 InlineKeyboardButton(text="🏠 Main Menu", callback_data="back_to_main")]
            ])
        else:
            keyboard = InlineKeyboardMarkup(inline_keyboard=[
                [InlineKeyboardButton(text="▶️ Run Now", callback_data=f"run_script:{file_name}"),
                 InlineKeyboardButton(text="⭐ Add Favorite", callback_data=f"toggle_fav:{file_name}")],
                [InlineKeyboardButton(text="ℹ️ File Info", callback_data=f"file_info:{file_name}"),
                 InlineKeyboardButton(text="🗑️ Delete", callback_data=f"delete_file:{file_name}")],
                [InlineKeyboardButton(text="📁 My Files", callback_data="check_files"),
                 InlineKeyboardButton(text="🏠 Main Menu", callback_data="back_to_main")]
            ])
        
        await status_msg.edit_text(
            f"""
╔═══════════════════════╗
    ✅ <b>UPLOAD SUCCESS!</b> ✅
╚═══════════════════════╝

📄 <b>File:</b> <code>{file_name}</code>
📦 <b>Type:</b> {file_ext[1:].upper()}
💾 <b>Size:</b> {document.file_size / 1024:.2f} KB
📊 <b>Usage:</b> {current_files + 1} files (Unlimited ♾️)

🎉 File uploaded successfully!
""",
            reply_markup=keyboard,
            parse_mode="HTML"
        )
    except Exception as e:
        logger.error(f"Error uploading file: {e}")
        await message.answer(f"❌ Upload failed: {str(e)}")

def _safe_child_path(base: Path, relative: str) -> Path:
    """Resolve an archive member and reject paths escaping the project directory."""
    target = (base / relative).resolve()
    root = base.resolve()
    if target != root and root not in target.parents:
        raise ValueError("Unsafe path in ZIP archive")
    return target


def _extract_project_archive(zip_path: Path, project_dir: Path):
    """Safely extract a Python project while preserving its directory structure."""
    max_files = 5000
    max_uncompressed = 500 * 1024 * 1024
    with zipfile.ZipFile(zip_path, 'r') as archive:
        entries = archive.infolist()
        if len(entries) > max_files:
            raise ValueError("ZIP contains too many files (limit 5000)")
        total_size = sum(item.file_size for item in entries)
        if total_size > max_uncompressed:
            raise ValueError("ZIP expands beyond the 500 MB safety limit")
        for item in entries:
            parts = Path(item.filename).parts
            if any(part in ('.venv', 'venv', 'site-packages', '__pycache__', '.git') for part in parts):
                continue
            if item.is_dir():
                continue
            dest = _safe_child_path(project_dir, item.filename)
            dest.parent.mkdir(parents=True, exist_ok=True)
            with archive.open(item, 'r') as src, open(dest, 'wb') as dst:
                shutil.copyfileobj(src, dst)


def _find_project_entry(project_dir: Path) -> Path:
    py_files = [x for x in project_dir.rglob('*.py') if x.is_file() and not any(part in ('__pycache__', '.venv', 'venv', 'site-packages') for part in x.parts)]
    if not py_files:
        raise FileNotFoundError("ZIP archive ke andar koi .py file nahi mili")
    # Prefer conventional entry points, then a root-level Python file, then first nested file.
    priority = ('main.py', 'bot.py', 'app.py', 'run.py', 'start.py', '__main__.py')
    for name in priority:
        matches = [x for x in py_files if x.name.lower() == name]
        if matches:
            return sorted(matches, key=lambda x: (len(x.parts), str(x).lower()))[0]
    root_files = [x for x in py_files if x.parent == project_dir]
    if root_files:
        return sorted(root_files, key=lambda x: x.name.lower())[0]
    return sorted(py_files, key=lambda x: (len(x.parts), str(x).lower()))[0]


def _record_run(user_id, file_name, project_type, status, started_at, finished_at=None, exit_code=None, log_path=None):
    try:
        with sqlite3.connect(DATABASE_PATH) as conn:
            conn.execute("INSERT INTO bot_run_history (user_id,file_name,project_type,status,started_at,finished_at,exit_code,log_path) VALUES (?,?,?,?,?,?,?,?)",
                (user_id, file_name, project_type, status, started_at.isoformat(),
                 finished_at.isoformat() if finished_at else None, exit_code, str(log_path) if log_path else None))
    except Exception:
        logger.exception("Could not save bot run history")


def _project_control_keyboard(script_key, file_name):
    return InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🛑 Stop", callback_data=f"stop_script:{script_key}"),
         InlineKeyboardButton(text="🔄 Restart", callback_data=f"restart_script:{script_key}")],
        [InlineKeyboardButton(text="📊 Status", callback_data=f"bot_status:{script_key}"),
         InlineKeyboardButton(text="📋 Live Logs", callback_data=f"view_log:{file_name}")],
        [InlineKeyboardButton(text="🧹 Reset Project", callback_data=f"reset_project:{file_name}")],
        [InlineKeyboardButton(text="💾 Backup ZIP", callback_data=f"backup_project:{file_name}"),
         InlineKeyboardButton(text="🗄️ Download DB", callback_data=f"download_project_db:{file_name}")],
        [InlineKeyboardButton(text="📜 Run History", callback_data=f"run_history:{file_name}"),
         InlineKeyboardButton(text="📁 My Files", callback_data="check_files")]
    ])


def _project_env_and_ports(project_dir: Path, entry_file: Path, venv_dir: Path, log_handle):
    """Build a child-only environment: never leak the Master Bot's credentials/PORT."""
    env = os.environ.copy()
    sensitive = {
        'BOT_TOKEN', 'TELEGRAM_BOT_TOKEN', 'API_TOKEN', 'BOT_API_TOKEN',
        'OWNER_ID', 'ADMIN_ID', 'YOUR_USERNAME', 'UPDATE_CHANNEL',
        'PYTHONPATH', 'PORT', 'WEB_PORT', 'SERVER_PORT', 'API_PORT',
        'HTTP_PORT', 'FLASK_RUN_PORT'
    }
    for key in list(env):
        if key.upper() in sensitive or key.upper().endswith('_BOT_TOKEN'):
            env.pop(key, None)

    # Read only this uploaded project's .env files. The nearest file wins.
    env_files = []
    for candidate in (project_dir / '.env', entry_file.parent / '.env'):
        if candidate.is_file() and candidate not in env_files:
            env_files.append(candidate)
    project_values = {}
    for env_file in env_files:
        try:
            values = dotenv_values(env_file)
            project_values.update({k: str(v) for k, v in values.items() if v is not None})
        except Exception as exc:
            log_handle.write(f"[ENV WARNING] Could not read {env_file.name}: {exc}\n")
    env.update(project_values)

    # Avoid accidentally launching a second copy of the Master Bot.
    master_token = os.getenv('BOT_TOKEN', '').strip()
    project_token = next((env.get(k, '').strip() for k in
                          ('BOT_TOKEN', 'TELEGRAM_BOT_TOKEN', 'API_TOKEN', 'BOT_API_TOKEN')
                          if env.get(k, '').strip()), '')
    token_candidates = set(re.findall(r'\b\d{6,}:[A-Za-z0-9_-]{20,}\b', project_token))
    try:
        source = entry_file.read_text(errors='ignore')
        token_candidates.update(re.findall(r'\b\d{6,}:[A-Za-z0-9_-]{20,}\b', source))
    except Exception:
        pass
    if master_token and master_token in token_candidates:
        raise RuntimeError(
            'This project contains the same Telegram Bot Token as the Master Bot. '
            'Use a different token for the uploaded bot; Telegram allows only one active getUpdates poller per token.'
        )
    token_fingerprint = hashlib.sha256(sorted(token_candidates)[0].encode()).hexdigest() if token_candidates else None

    # Give each hosted project its own ports. PORT inherited from the Master host
    # was making child web/API servers collide with the Master web server.
    for key in ('PORT', 'WEB_PORT', 'SERVER_PORT', 'API_PORT', 'HTTP_PORT', 'FLASK_RUN_PORT'):
        with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as sock:
            sock.bind(('0.0.0.0', 0))
            env[key] = str(sock.getsockname()[1])
    env['PYTHONUNBUFFERED'] = '1'
    env['PYTHONDONTWRITEBYTECODE'] = '1'
    bin_dir = venv_dir / ('Scripts' if os.name == 'nt' else 'bin')
    env['PATH'] = str(bin_dir) + os.pathsep + env.get('PATH', '')
    return env, token_fingerprint


def _ensure_project_venv(project_dir: Path, log_handle):
    """Create a separate virtual environment for each uploaded project."""
    venv_dir = project_dir / '.venv'
    python_bin = venv_dir / ('Scripts/python.exe' if os.name == 'nt' else 'bin/python')
    if not python_bin.exists():
        log_handle.write('[ENVIRONMENT] Creating isolated virtual environment...\n')
        log_handle.flush()
        venv.EnvBuilder(with_pip=True, clear=False).create(str(venv_dir))
    return venv_dir, python_bin


def _install_project_imports(project_dir: Path, python_bin: Path, log_handle, timeout=600):
    """Best-effort install of imports for projects without requirements.txt, inside .venv only."""
    modules = set()
    for source_file in project_dir.rglob('*.py'):
        if any(part in ('.venv', 'venv', 'site-packages', '__pycache__') for part in source_file.parts):
            continue
        modules.update(extract_imports(source_file))
    local_names = {p.stem for p in project_dir.rglob('*.py')}
    local_names.update(p.name for p in project_dir.iterdir() if p.is_dir())
    packages = set()
    for module in modules:
        if module in STDLIB_MODULES or module in local_names or module == '__future__':
            continue
        packages.add(IMPORT_TO_PIP.get(module, module))
    if not packages:
        log_handle.write('[DEPENDENCIES] No external imports detected.\n')
        return
    log_handle.write('[DEPENDENCIES] Installing detected imports into this project .venv: ' + ', '.join(sorted(packages)) + '\n')
    log_handle.flush()
    result = subprocess.run([str(python_bin), '-m', 'pip', 'install', '--disable-pip-version-check', '--quiet', *sorted(packages)],
                            cwd=str(project_dir), capture_output=True, text=True, timeout=timeout)
    if result.returncode != 0:
        log_handle.write('[DEPENDENCY INSTALL WARNING]\n' + (result.stderr or result.stdout or 'pip install failed')[-10000:] + '\n')
        log_handle.flush()
    else:
        log_handle.write('[DEPENDENCIES] Detected imports installed successfully.\n')


async def _start_python_process(user_id, display_name, entry_file: Path, working_dir: Path, project_type: str, callback):
    # Serialize start requests so rapid/double taps cannot race process registration.
    async with _bot_start_lock:
        script_key = f"{user_id}_{_project_id(user_id, display_name)}"
        old = bot_scripts.get(script_key)
        if old:
            old_process = old.get('process')
            if old_process and old_process.poll() is None:
                await callback.message.answer("⚠️ This project is already running. Use Restart or Stop first.")
                return
            old_handle = old.get('log_file')
            if old_handle and not old_handle.closed:
                old_handle.close()
            bot_scripts.pop(script_key, None)

        if user_id not in admin_ids:
            running_now = sum(1 for k, i in bot_scripts.items()
                              if i.get('script_owner_id') == user_id and k != script_key
                              and i.get('process') and i['process'].poll() is None)
            if running_now >= USER_RUN_LIMIT:
                await callback.message.answer(f"🚫 Limit reached: normal users can run only {USER_RUN_LIMIT} bots at a time. Stop one bot first.")
                return

        working_dir = working_dir.resolve()
        entry_file = entry_file.resolve()
        if not working_dir.is_dir() or (entry_file != working_dir and working_dir not in entry_file.parents):
            await callback.message.answer("❌ Project entry must be inside its isolated project folder.")
            return

        log_path = working_dir / "hostbot.log"
        started = datetime.now()
        log_handle = open(log_path, 'a', encoding='utf-8', errors='replace')
        log_handle.write(f"\n\n===== START {started.isoformat()} | {display_name} =====\n")
        log_handle.flush()
        status_msg = await callback.message.answer("⏳ <b>Preparing isolated Python environment...</b>", parse_mode="HTML")
        try:
            venv_dir, python_bin = await asyncio.to_thread(_ensure_project_venv, working_dir, log_handle)
            requirements = working_dir / 'requirements.txt'
            if not requirements.exists() and project_type == 'zip':
                nested_requirements = sorted(working_dir.rglob('requirements.txt'))
                if nested_requirements:
                    requirements = nested_requirements[0]
            if requirements.exists():
                await status_msg.edit_text("📦 <b>Installing this project's requirements in its own environment...</b>", parse_mode="HTML")
                def _install_requirements():
                    return subprocess.run([str(python_bin), '-m', 'pip', 'install', '-r', str(requirements), '--disable-pip-version-check', '--quiet'],
                                          cwd=str(requirements.parent), capture_output=True, text=True, timeout=600)
                result = await asyncio.to_thread(_install_requirements)
                if result.returncode != 0:
                    log_handle.write("\n[DEPENDENCY INSTALL ERROR]\n" + (result.stderr or result.stdout or "pip install failed")[-12000:] + "\n")
                    log_handle.flush()
                    raise RuntimeError("requirements.txt install failed in this project's isolated environment. Open Live Logs for details.")
                log_handle.write("[DEPENDENCIES] requirements.txt installed in project .venv\n")
            else:
                await status_msg.edit_text("🔎 <b>Checking Python imports and preparing dependencies...</b>", parse_mode="HTML")
                await asyncio.to_thread(_install_project_imports, working_dir, python_bin, log_handle)

            child_env, token_fingerprint = _project_env_and_ports(working_dir, entry_file, venv_dir, log_handle)
            if token_fingerprint:
                for active_key, active_info in bot_scripts.items():
                    if active_key != script_key and active_info.get('token_fingerprint') == token_fingerprint and active_info.get('process') and active_info['process'].poll() is None:
                        raise RuntimeError('Another hosted project is already using this Telegram Bot Token. Each running bot needs its own unique token.')
            run_cwd = requirements.parent if requirements.exists() else entry_file.parent
            await status_msg.edit_text("🚀 <b>Starting uploaded bot with its own Python environment...</b>", parse_mode="HTML")
            process = subprocess.Popen(
                [str(python_bin), '-u', str(entry_file)], cwd=str(run_cwd), env=child_env,
                stdout=log_handle, stderr=subprocess.STDOUT,
                stdin=subprocess.DEVNULL, close_fds=True, start_new_session=(os.name != 'nt'),
                preexec_fn=(_child_preexec if os.name != 'nt' else None)
            )
            await asyncio.sleep(2.5)
            exit_code = process.poll()
            if exit_code is not None:
                log_handle.flush()
                _record_run(user_id, display_name, project_type, 'FAILED', started, datetime.now(), exit_code, log_path)
                excerpt = log_path.read_text(errors='replace')[-3000:]
                log_handle.close()
                await status_msg.edit_text(
                    "❌ <b>BOT START FAILED</b>\n"
                    f"Exit code: <code>{exit_code}</code>\n\n<pre>{html_lib.escape(excerpt[-3000:])}</pre>", parse_mode="HTML")
                return

            bot_scripts[script_key] = {
                'process': process, 'file_name': display_name, 'script_owner_id': user_id,
                'start_time': started, 'user_folder': str(working_dir), 'type': 'py',
                'log_file': log_handle, 'log_path': str(log_path), 'entry_file': str(entry_file),
                'project_type': project_type, 'python_bin': str(python_bin), 'run_cwd': str(run_cwd),
                'token_fingerprint': token_fingerprint
            }
            _autostart_save(user_id, display_name, project_type)
            with sqlite3.connect(DATABASE_PATH) as conn:
                conn.execute("UPDATE bot_stats SET stat_value = stat_value + 1 WHERE stat_name = 'total_runs'")
            bot_stats['total_runs'] = bot_stats.get('total_runs', 0) + 1
            _record_run(user_id, display_name, project_type, 'RUNNING', started, log_path=log_path)
            await status_msg.edit_text(
                f"✅ <b>PROCESS STARTED</b>\n\n"
                f"📄 Project: <code>{html_lib.escape(display_name)}</code>\n"
                f"🐍 Entry: <code>{html_lib.escape(entry_file.name)}</code>\n"
                f"🆔 PID: <code>{process.pid}</code>\n"
                f"📂 Workspace: <code>{html_lib.escape(str(working_dir))}</code>\n"
                f"🐍 Environment: <code>.venv (isolated)</code>\n"
                f"ℹ️ Check Live Logs to confirm the bot's own Telegram polling/service is ready.",
                reply_markup=_project_control_keyboard(script_key, display_name), parse_mode="HTML")
        except Exception as exc:
            log_handle.write(f"\n[HOST ERROR] {type(exc).__name__}: {exc}\n")
            log_handle.flush()
            if not log_handle.closed:
                log_handle.close()
            try:
                await status_msg.edit_text(f"❌ <b>START ERROR</b>\n{html_lib.escape(str(exc))}\n\nUse Logs to inspect the error.", parse_mode="HTML")
            except Exception:
                pass
            logger.exception("Bot start failed for %s", display_name)


@dp.callback_query(F.data.startswith("run_script:"))
async def callback_run_script(callback: types.CallbackQuery):
    user_id = callback.from_user.id
    file_name = callback.data.split(":", 1)[1]
    if Path(file_name).name != file_name or file_name in ('.', '..'):
        await callback.answer("❌ Invalid file name", show_alert=True)
        return
    user_folder = UPLOAD_BOTS_DIR / str(user_id)
    file_path = user_folder / file_name
    if not file_path.is_file() or file_path.suffix.lower() != '.py':
        await callback.answer("❌ Only uploaded Python .py files can run directly. For ZIP use Run Bot Project.", show_alert=True)
        return
    await callback.answer("⏳ Preparing isolated Python project...")
    project_dir = _project_workspace(user_id, file_name)
    project_dir.mkdir(parents=True, exist_ok=True)
    staged_entry = project_dir / file_name
    shutil.copy2(file_path, staged_entry)
    # Include common non-code sidecar files (config/database/assets) without mixing Python scripts or ZIP projects.
    for item in user_folder.iterdir():
        if item.is_file() and item.name != file_name and item.suffix.lower() not in ('.py', '.zip', '.log'):
            try:
                shutil.copy2(item, project_dir / item.name)
            except OSError:
                logger.warning("Could not stage sidecar file %s", item.name)
    await _start_python_process(user_id, file_name, staged_entry, project_dir, 'py', callback)


@dp.callback_query(F.data.startswith("run_project:"))
async def callback_run_project(callback: types.CallbackQuery):
    user_id = callback.from_user.id
    zip_name = callback.data.split(":", 1)[1]
    if Path(zip_name).name != zip_name or not zip_name.lower().endswith('.zip'):
        await callback.answer("❌ Invalid ZIP name", show_alert=True)
        return
    user_folder = UPLOAD_BOTS_DIR / str(user_id)
    zip_path = user_folder / zip_name
    if not zip_path.is_file() or not zipfile.is_zipfile(zip_path):
        await callback.answer("❌ ZIP file not found or invalid", show_alert=True)
        return
    project_dir = _project_workspace(user_id, zip_name)
    try:
        await callback.answer("📦 Preparing ZIP project...")
        if not project_dir.exists():
            project_dir.mkdir(parents=True, exist_ok=True)
            await asyncio.to_thread(_extract_project_archive, zip_path, project_dir)
        entry_file = _find_project_entry(project_dir)
        await _start_python_process(user_id, zip_name, entry_file, project_dir, 'zip', callback)
    except Exception as exc:
        logger.exception("ZIP project preparation failed")
        shutil.rmtree(project_dir, ignore_errors=True)
        await callback.message.answer(f"❌ ZIP project error: {html_lib.escape(str(exc)[:180])}")


@dp.callback_query(F.data.startswith("restart_script:"))
async def callback_restart_script(callback: types.CallbackQuery):
    script_key = callback.data.split(":", 1)[1]
    info = bot_scripts.get(script_key)
    if not info:
        await callback.answer("❌ Bot is not running. Start it again from My Files.", show_alert=True)
        return
    if callback.from_user.id != info.get('script_owner_id') and callback.from_user.id not in admin_ids:
        await callback.answer("❌ You cannot control another user's bot", show_alert=True)
        return
    await callback.answer("🔄 Restarting bot...")
    owner = info['script_owner_id']
    name = info['file_name']
    entry = Path(info['entry_file'])
    workdir = Path(info['user_folder'])
    p = info['process']
    try:
        if p.poll() is None:
            if os.name == 'nt':
                p.terminate()
            else:
                os.killpg(os.getpgid(p.pid), signal.SIGTERM)
            try:
                p.wait(timeout=5)
            except subprocess.TimeoutExpired:
                p.kill()
        handle = info.get('log_file')
        if handle and not handle.closed:
            handle.close()
        bot_scripts.pop(script_key, None)
        await _start_python_process(owner, name, entry, workdir, info.get('project_type', 'py'), callback)
    except Exception as exc:
        await callback.answer(f"❌ Restart failed: {str(exc)[:150]}", show_alert=True)


@dp.callback_query(F.data.startswith("bot_status:"))
async def callback_bot_status(callback: types.CallbackQuery):
    key = callback.data.split(":", 1)[1]
    info = bot_scripts.get(key)
    if not info:
        await callback.answer("Bot is stopped or not found", show_alert=True)
        return
    if callback.from_user.id != info.get('script_owner_id') and callback.from_user.id not in admin_ids:
        await callback.answer("Not allowed", show_alert=True)
        return
    process = info['process']
    running = process.poll() is None
    elapsed = int((datetime.now() - info['start_time']).total_seconds())
    await callback.message.answer(
        f"📊 <b>BOT STATUS</b>\nStatus: {'🟢 RUNNING' if running else '🔴 STOPPED'}\n"
        f"PID: <code>{process.pid}</code>\nRuntime: <code>{elapsed}s</code>\n"
        f"Exit code: <code>{process.poll() if process.poll() is not None else 'N/A'}</code>",
        parse_mode="HTML", reply_markup=_project_control_keyboard(key, info['file_name']))
    await callback.answer()


@dp.callback_query(F.data.startswith("view_log:"))
async def callback_view_log(callback: types.CallbackQuery):
    user_id = callback.from_user.id
    file_name = callback.data.split(":", 1)[1]
    user_folder = UPLOAD_BOTS_DIR / str(user_id)
    file_stem = Path(file_name).stem
    log_path = _project_workspace(user_id, file_name) / 'hostbot.log'
    if not log_path.exists():
        log_path = user_folder / f"{file_stem}.log"

    if not log_path.exists():
        await callback.answer("❌ Koi log nahi mila. Pehle script run karo.", show_alert=True)
        return

    try:
        content = log_path.read_text(errors='replace').strip()
        matching = next((v for v in bot_scripts.values()
                         if v.get('script_owner_id') == user_id and v.get('file_name') == file_name), None)
        running_note = "🟢 Status: Running" if matching and matching["process"].poll() is None else "🔴 Status: Stopped/Exited"

        if not content:
            content = "(Abhi tak koi output nahi — script chup-chaap chal rahi hai)"
        elif len(content) > 3500:
            content = "...(truncated)...\n" + content[-3500:]

        text = f"""╔═══════════════════════╗
    📋 <b>SCRIPT OUTPUT</b> 📋
╚═══════════════════════╝

📄 <b>File:</b> <code>{html_lib.escape(file_name)}</code>
{running_note}

<pre>{html_lib.escape(content)}</pre>"""

        back_keyboard = InlineKeyboardMarkup(inline_keyboard=[
            [InlineKeyboardButton(text="🔄 Refresh", callback_data=f"view_log:{file_name}")],
            [InlineKeyboardButton(text="📁 My Files", callback_data="check_files")]
        ])
        await callback.message.answer(text, reply_markup=back_keyboard, parse_mode="HTML")
        await callback.answer()
    except Exception as e:
        await callback.answer(f"❌ Log read error: {str(e)}", show_alert=True)

@dp.callback_query(F.data.startswith("stop_script:"))
async def callback_stop_script(callback: types.CallbackQuery):
    script_key = callback.data.split(":", 1)[1]
    info = bot_scripts.get(script_key)
    if not info:
        await callback.answer("❌ Bot not running or already stopped", show_alert=True)
        return
    if callback.from_user.id != info.get('script_owner_id') and callback.from_user.id not in admin_ids:
        await callback.answer("❌ You cannot control another user's bot", show_alert=True)
        return
    try:
        process = info['process']
        if process.poll() is None:
            if os.name == 'nt':
                process.terminate()
            else:
                try:
                    os.killpg(os.getpgid(process.pid), signal.SIGTERM)
                except ProcessLookupError:
                    pass
            try:
                process.wait(timeout=8)
            except subprocess.TimeoutExpired:
                if os.name == 'nt':
                    process.kill()
                else:
                    try: os.killpg(os.getpgid(process.pid), signal.SIGKILL)
                    except ProcessLookupError: pass
                process.wait(timeout=3)
        handle = info.get('log_file')
        if handle and not handle.closed:
            handle.flush(); handle.close()
        _record_run(info['script_owner_id'], info['file_name'], info.get('project_type','py'),
                    'STOPPED', info['start_time'], datetime.now(), process.returncode, info.get('log_path'))
        bot_scripts.pop(script_key, None)
        _autostart_remove(info['script_owner_id'], info['file_name'])
        await callback.answer("🛑 Bot stopped successfully", show_alert=True)
        await callback.message.answer(f"🛑 <b>{html_lib.escape(info['file_name'])}</b> stopped.",
                                      reply_markup=InlineKeyboardMarkup(inline_keyboard=[
                                          [InlineKeyboardButton(text="▶️ Start Again", callback_data=(f"run_project:{info['file_name']}" if info.get('project_type') == 'zip' else f"run_script:{info['file_name']}"))],
                                          [InlineKeyboardButton(text="📁 My Files", callback_data="check_files")]
                                      ]), parse_mode="HTML")
    except Exception as exc:
        logger.exception("Error stopping script")
        await callback.answer(f"❌ Stop error: {str(exc)[:150]}", show_alert=True)


@dp.callback_query(F.data.startswith("reset_project:"))
async def callback_reset_project(callback: types.CallbackQuery):
    user_id = callback.from_user.id
    name = callback.data.split(":", 1)[1]
    # Stop matching active process first.
    for key, info in list(bot_scripts.items()):
        if info.get('script_owner_id') == user_id and info.get('file_name') == name:
            p = info['process']
            if p.poll() is None:
                try:
                    if os.name == 'nt': p.terminate()
                    else: os.killpg(os.getpgid(p.pid), signal.SIGTERM)
                    p.wait(timeout=5)
                except Exception:
                    try: p.kill()
                    except Exception: pass
            h = info.get('log_file')
            if h and not h.closed: h.close()
            bot_scripts.pop(key, None)
            _autostart_remove(info.get('script_owner_id'), info.get('file_name'))
    project_dir = _project_workspace(user_id, name)
    if project_dir.exists():
        shutil.rmtree(project_dir, ignore_errors=True)
    await callback.answer("🧹 Extracted project reset. Original ZIP/file is kept.", show_alert=True)


@dp.callback_query(F.data.startswith("backup_project:"))
async def callback_backup_project(callback: types.CallbackQuery):
    user_id = callback.from_user.id
    name = callback.data.split(":", 1)[1]
    user_folder = UPLOAD_BOTS_DIR / str(user_id)
    project_dir = _project_workspace(user_id, name)
    source = project_dir if project_dir.is_dir() else user_folder
    if not source.exists():
        await callback.answer("❌ Project files not found", show_alert=True); return
    backup_dir = project_dir / 'backups'
    backup_dir.mkdir(parents=True, exist_ok=True)
    backup_path = backup_dir / f"{Path(name).stem}_backup_{datetime.now().strftime('%Y%m%d_%H%M%S')}.zip"
    try:
        def _make_backup():
            with zipfile.ZipFile(backup_path, 'w', zipfile.ZIP_DEFLATED) as zf:
                if source == user_folder and Path(name).suffix.lower() == '.py':
                    selected = [user_folder / name]
                else:
                    selected = list(source.rglob('*'))
                for item in selected:
                    if (item.is_file() and item.exists() and item.resolve() != backup_path.resolve()
                            and item.suffix.lower() != '.log'
                            and not any(part in ('__pycache__', '.venv', 'venv', 'site-packages', 'backups') for part in item.parts)):
                        zf.write(item, item.relative_to(source))
        await asyncio.to_thread(_make_backup)
        await callback.message.answer_document(FSInputFile(backup_path), caption="💾 Project backup (source + database files)")
        await callback.answer("✅ Backup created")
    except Exception as exc:
        await callback.answer(f"❌ Backup failed: {str(exc)[:150]}", show_alert=True)
    finally:
        try: backup_path.unlink(missing_ok=True)
        except Exception: pass


@dp.callback_query(F.data.startswith("download_project_db:"))
async def callback_download_project_db(callback: types.CallbackQuery):
    user_id = callback.from_user.id
    name = callback.data.split(":", 1)[1]
    root = _project_workspace(user_id, name)
    if not root.exists(): root = UPLOAD_BOTS_DIR / str(user_id)
    candidates = [x for x in root.rglob('*') if x.is_file() and (x.suffix.lower() in ('.db','.sqlite','.sqlite3','.json') or x.name.lower().endswith('.db-wal'))]
    if not candidates:
        await callback.answer("No .db/.sqlite/.sqlite3/.json database file found in this project", show_alert=True); return
    for db_file in candidates[:5]:
        await callback.message.answer_document(FSInputFile(db_file), caption=f"🗄️ {db_file.name}")
    await callback.answer("✅ Database file(s) sent")


@dp.callback_query(F.data.startswith("run_history:"))
async def callback_run_history(callback: types.CallbackQuery):
    user_id = callback.from_user.id
    name = callback.data.split(":", 1)[1]
    with sqlite3.connect(DATABASE_PATH) as conn:
        rows = conn.execute("SELECT status,started_at,finished_at,exit_code FROM bot_run_history WHERE user_id=? AND file_name=? ORDER BY id DESC LIMIT 10", (user_id,name)).fetchall()
    if not rows:
        body = "No run history found yet."
    else:
        body = "\n".join(f"• {html_lib.escape(str(a))} | {html_lib.escape(str(b))} | exit={c if c is not None else '-'}" for a,b,_,c in rows)
    await callback.message.answer(f"📜 <b>RUN HISTORY</b>\n<pre>{body[:3500]}</pre>", parse_mode="HTML")
    await callback.answer()


@dp.callback_query(F.data.startswith("extract_zip:"))
async def callback_extract_zip(callback: types.CallbackQuery):
    user_id = callback.from_user.id
    file_name = callback.data.split(":", 1)[1]
    if Path(file_name).name != file_name:
        await callback.answer("❌ Invalid ZIP name", show_alert=True)
        return
    user_folder = UPLOAD_BOTS_DIR / str(user_id)
    zip_path = user_folder / file_name
    if not zip_path.is_file() or not zipfile.is_zipfile(zip_path):
        await callback.answer("❌ ZIP file not found or invalid", show_alert=True)
        return
    project_dir = user_folder / (Path(file_name).stem[:60] + '_project')
    try:
        await callback.answer("📦 Safely extracting project...")
        if project_dir.exists():
            shutil.rmtree(project_dir, ignore_errors=True)
        project_dir.mkdir(parents=True, exist_ok=True)
        await asyncio.to_thread(_extract_project_archive, zip_path, project_dir)
        py_count = sum(1 for item in project_dir.rglob('*.py') if item.is_file())
        all_count = sum(1 for item in project_dir.rglob('*') if item.is_file())
        try:
            entry = _find_project_entry(project_dir)
            entry_label = html_lib.escape(str(entry.relative_to(project_dir)))
        except FileNotFoundError:
            entry_label = "No Python entry file found"
        keyboard = InlineKeyboardMarkup(inline_keyboard=[
            [InlineKeyboardButton(text="🚀 Run Bot Project", callback_data=f"run_project:{file_name}")],
            [InlineKeyboardButton(text="📁 My Files", callback_data="check_files"),
             InlineKeyboardButton(text="🏠 Main Menu", callback_data="back_to_main")]
        ])
        await callback.message.answer(
            f"✅ <b>ZIP EXTRACTED SAFELY</b>\nFiles: <code>{all_count}</code>\n"
            f"Python files: <code>{py_count}</code>\nEntry candidate: <code>{entry_label}</code>\n"
            "Original ZIP and folder structure have been kept.",
            reply_markup=keyboard, parse_mode="HTML")
    except Exception as exc:
        shutil.rmtree(project_dir, ignore_errors=True)
        logger.exception("Safe ZIP extraction failed")
        await callback.message.answer(f"❌ Extraction failed: {html_lib.escape(str(exc)[:200])}")

@dp.callback_query(F.data.startswith("delete_file:"))
async def callback_delete_file(callback: types.CallbackQuery):
    user_id = callback.from_user.id
    file_name = callback.data.split(":", 1)[1]
    
    user_folder = UPLOAD_BOTS_DIR / str(user_id)
    file_path = user_folder / file_name
    
    try:
        if file_path.exists():
            file_path.unlink()
        
        try:
            _stop_script(_script_key(user_id, file_name))
            _autostart_remove(user_id, file_name)
        except Exception:
            logger.exception('cleanup on delete failed')
        if user_id in user_files:
            user_files[user_id] = [f for f in user_files[user_id] if f[0] != file_name]
        
        if file_name in user_favorites.get(user_id, []):
            user_favorites[user_id].remove(file_name)
        
        conn = sqlite3.connect(DATABASE_PATH)
        c = conn.cursor()
        c.execute('DELETE FROM user_files WHERE user_id = ? AND file_name = ?', (user_id, file_name))
        c.execute('DELETE FROM favorites WHERE user_id = ? AND file_name = ?', (user_id, file_name))
        conn.commit()
        conn.close()
        
        await callback.answer("✅ File deleted successfully!", show_alert=True)
        await callback_check_files(callback)
        
    except Exception as e:
        logger.error(f"Error deleting file: {e}")
        await callback.answer(f"❌ Error: {str(e)}", show_alert=True)

@dp.callback_query(F.data == "admin_total_users")
async def callback_admin_total_users(callback: types.CallbackQuery):
    if callback.from_user.id not in admin_ids:
        await callback.answer("❌ Admin only!", show_alert=True)
        return
    
    user_list = "\n".join([f"• <code>{uid}</code>" for uid in list(active_users)[:15]])
    text = f"""
╔═══════════════════════╗
    👥 <b>USER STATISTICS</b> 👥
╚═══════════════════════╝

📊 <b>Total Users:</b> {len(active_users)}
🚫 <b>Banned:</b> {len(banned_users)}
✅ <b>Active:</b> {len(active_users) - len(banned_users)}

<b>📝 Recent Users (15):</b>
{user_list}

{'...' if len(active_users) > 15 else ''}
"""
    
    back_keyboard = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🔙 Admin Panel", callback_data="admin_panel")]
    ])
    
    await callback.message.edit_text(text, reply_markup=back_keyboard, parse_mode="HTML")
    await callback.answer()

@dp.callback_query(F.data == "admin_total_files")
async def callback_admin_total_files(callback: types.CallbackQuery):
    if callback.from_user.id not in admin_ids:
        await callback.answer("❌ Admin only!", show_alert=True)
        return
    
    total_files = sum(len(files) for files in user_files.values())
    py_files = sum(1 for files in user_files.values() for f in files if f[1] == 'py')
    js_files = 0
    zip_files = sum(1 for files in user_files.values() for f in files if f[1] == 'zip')
    
    text = f"""
╔═══════════════════════╗
    📁 <b>FILE STATISTICS</b> 📁
╚═══════════════════════╝

📊 <b>Total Files:</b> {total_files}

<b>📦 By Type:</b>
🐍 Python: {py_files}
📦 ZIP: {zip_files}

<b>📈 Top Users:</b>
"""
    
    top_users = sorted(user_files.items(), key=lambda x: len(x[1]), reverse=True)[:5]
    for user_id, files in top_users:
        text += f"• User <code>{user_id}</code>: {len(files)} files\n"
    
    back_keyboard = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🔙 Admin Panel", callback_data="admin_panel")]
    ])
    
    await callback.message.edit_text(text, reply_markup=back_keyboard, parse_mode="HTML")
    await callback.answer()

@dp.callback_query(F.data == "admin_running_scripts")
async def callback_admin_running_scripts(callback: types.CallbackQuery):
    if callback.from_user.id not in admin_ids:
        await callback.answer("❌ Admin only!", show_alert=True)
        return
    
    if not bot_scripts:
        text = """
╔═══════════════════════╗
    🚀 <b>RUNNING SCRIPTS</b> 🚀
╚═══════════════════════╝

💤 No scripts running currently
"""
        buttons = []
    else:
        text = f"""
╔═══════════════════════╗
    🚀 <b>RUNNING ({len(bot_scripts)})</b> 🚀
╚═══════════════════════╝

"""
        buttons = []
        for script_key, info in bot_scripts.items():
            runtime = (datetime.now() - info['start_time']).total_seconds()
            text += f"🔸 <code>{info['file_name']}</code>\n"
            text += f"   PID: {info['process'].pid} | User: {info['script_owner_id']}\n"
            text += f"   Runtime: {int(runtime)}s\n\n"
            buttons.append([InlineKeyboardButton(
                text=f"🛑 Stop {info['file_name'][:15]}", 
                callback_data=f"stop_script:{script_key}"
            )])
    
    buttons.append([InlineKeyboardButton(text="🔙 Admin Panel", callback_data="admin_panel")])
    back_keyboard = InlineKeyboardMarkup(inline_keyboard=buttons)
    
    await callback.message.edit_text(text, reply_markup=back_keyboard, parse_mode="HTML")
    await callback.answer()

@dp.callback_query(F.data == "admin_premium_users")
async def callback_admin_premium_users(callback: types.CallbackQuery):
    if callback.from_user.id not in admin_ids:
        await callback.answer("❌ Admin only!", show_alert=True)
        return
    
    premium_users = [(u, data) for u, data in user_subscriptions.items() if data['expiry'] > datetime.now()]
    
    if not premium_users:
        text = """
╔═══════════════════════╗
    💎 <b>PREMIUM USERS</b> 💎
╚═══════════════════════╝

No active premium subscriptions.
"""
    else:
        text = f"""
╔═══════════════════════╗
    💎 <b>PREMIUM ({len(premium_users)})</b> 💎
╚═══════════════════════╝

"""
        for user_id, data in premium_users:
            expiry_date = data['expiry'].strftime('%Y-%m-%d')
            text += f"💎 User <code>{user_id}</code>\n   Expires: {expiry_date}\n\n"
    
    back_keyboard = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="➕ Add Premium", callback_data="add_premium")],
        [InlineKeyboardButton(text="🔙 Admin Panel", callback_data="admin_panel")]
    ])
    
    await callback.message.edit_text(text, reply_markup=back_keyboard, parse_mode="HTML")
    await callback.answer()

@dp.callback_query(F.data == "admin_analytics")
async def callback_admin_analytics(callback: types.CallbackQuery):
    if callback.from_user.id not in admin_ids:
        await callback.answer("❌ Admin only!", show_alert=True)
        return
    
    text = f"""
╔═══════════════════════╗
    📊 <b>BOT ANALYTICS</b> 📊
╚═══════════════════════╝

<b>📈 GLOBAL STATS:</b>

📤 Total Uploads: {bot_stats.get('total_uploads', 0)}
📥 Total Downloads: {bot_stats.get('total_downloads', 0)}
▶️ Script Runs: {bot_stats.get('total_runs', 0)}
👥 Total Users: {len(active_users)}
📁 Total Files: {sum(len(files) for files in user_files.values())}
🚀 Running Now: {len(bot_scripts)}
⭐ Total Favorites: {sum(len(favs) for favs in user_favorites.values())}

<b>💎 PREMIUM:</b>
Active: {len([u for u in user_subscriptions if user_subscriptions[u]['expiry'] > datetime.now()])}
Expired: {len([u for u in user_subscriptions if user_subscriptions[u]['expiry'] <= datetime.now()])}

<b>🛡️ SECURITY:</b>
Banned Users: {len(banned_users)}
Admins: {len(admin_ids)}
Bot Status: {'🔒 Locked' if bot_locked else '✅ Active'}
"""
    
    back_keyboard = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🔙 Admin Panel", callback_data="admin_panel")]
    ])
    
    await callback.message.edit_text(text, reply_markup=back_keyboard, parse_mode="HTML")
    await callback.answer()

@dp.callback_query(F.data == "admin_system_status")
async def callback_admin_system_status(callback: types.CallbackQuery):
    if callback.from_user.id not in admin_ids:
        await callback.answer("❌ Admin only!", show_alert=True)
        return
    
    cpu = psutil.cpu_percent(interval=1)
    memory = psutil.virtual_memory()
    disk = psutil.disk_usage('/')
    
    text = f"""
╔═══════════════════════╗
    ⚙️ <b>SYSTEM STATUS</b> ⚙️
╚═══════════════════════╝

<b>💻 CPU:</b>
Usage: {cpu}%
{'🟢 Normal' if cpu < 70 else '🟡 High' if cpu < 90 else '🔴 Critical'}

<b>🧠 MEMORY:</b>
Used: {memory.percent}%
Free: {memory.available / (1024**3):.1f} GB
Total: {memory.total / (1024**3):.1f} GB

<b>💾 DISK:</b>
Used: {disk.percent}%
Free: {disk.free / (1024**3):.1f} GB
Total: {disk.total / (1024**3):.1f} GB

<b>🤖 BOT STATUS:</b>
Status: {'🔒 Locked' if bot_locked else '✅ Running'}
Scripts: {len(bot_scripts)} active
Uptime: ✅ Online
"""
    
    back_keyboard = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🔄 Refresh", callback_data="admin_system_status")],
        [InlineKeyboardButton(text="🔙 Admin Panel", callback_data="admin_panel")]
    ])
    
    await callback.message.edit_text(text, reply_markup=back_keyboard, parse_mode="HTML")
    await callback.answer()

@dp.callback_query(F.data == "admin_add_admin")
async def callback_admin_add_admin(callback: types.CallbackQuery):
    if callback.from_user.id not in admin_ids:
        await callback.answer("❌ Admin only!", show_alert=True)
        return
    
    text = """
╔═══════════════════════╗
    ➕ <b>ADD ADMIN</b> ➕
╚═══════════════════════╝

To add a new admin, use:
<code>/addadmin USER_ID</code>

<b>Example:</b>
<code>/addadmin 123456789</code>

The user will get full admin privileges!
"""
    
    back_keyboard = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🔙 Admin Panel", callback_data="admin_panel")]
    ])
    
    await callback.message.edit_text(text, reply_markup=back_keyboard, parse_mode="HTML")
    await callback.answer()

@dp.callback_query(F.data == "admin_remove_admin")
async def callback_admin_remove_admin(callback: types.CallbackQuery):
    if callback.from_user.id not in admin_ids:
        await callback.answer("❌ Admin only!", show_alert=True)
        return
    
    text = f"""
╔═══════════════════════╗
    ➖ <b>REMOVE ADMIN</b> ➖
╚═══════════════════════╝

<b>Current Admins ({len(admin_ids)}):</b>

"""
    
    for admin_id in admin_ids:
        text += f"👑 <code>{admin_id}</code>\n"
    
    text += "\n<b>To remove:</b>\n<code>/removeadmin USER_ID</code>"
    
    back_keyboard = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🔙 Admin Panel", callback_data="admin_panel")]
    ])
    
    await callback.message.edit_text(text, reply_markup=back_keyboard, parse_mode="HTML")
    await callback.answer()

@dp.callback_query(F.data == "admin_ban_user")
async def callback_admin_ban_user(callback: types.CallbackQuery):
    if callback.from_user.id not in admin_ids:
        await callback.answer("❌ Admin only!", show_alert=True)
        return
    
    text = f"""
╔═══════════════════════╗
    🚫 <b>BAN USER</b> 🚫
╚═══════════════════════╝

<b>Currently Banned:</b> {len(banned_users)} users

To ban a user, use:
<code>/ban USER_ID REASON</code>

<b>Example:</b>
<code>/ban 123456789 Spam</code>

Banned users cannot use the bot!
"""
    
    back_keyboard = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🔙 Admin Panel", callback_data="admin_panel")]
    ])
    
    await callback.message.edit_text(text, reply_markup=back_keyboard, parse_mode="HTML")
    await callback.answer()

@dp.callback_query(F.data == "admin_unban_user")
async def callback_admin_unban_user(callback: types.CallbackQuery):
    if callback.from_user.id not in admin_ids:
        await callback.answer("❌ Admin only!", show_alert=True)
        return
    
    text = f"""
╔═══════════════════════╗
    ✅ <b>UNBAN USER</b> ✅
╚═══════════════════════╝

<b>Banned Users:</b> {len(banned_users)}

"""
    
    if banned_users:
        text += "<b>List:</b>\n"
        for ban_id in list(banned_users)[:10]:
            text += f"🚫 <code>{ban_id}</code>\n"
    
    text += "\n<b>To unban:</b>\n<code>/unban USER_ID</code>"
    
    back_keyboard = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🔙 Admin Panel", callback_data="admin_panel")]
    ])
    
    await callback.message.edit_text(text, reply_markup=back_keyboard, parse_mode="HTML")
    await callback.answer()

@dp.callback_query(F.data == "lock_bot")
async def callback_lock_bot(callback: types.CallbackQuery):
    global bot_locked
    
    if callback.from_user.id not in admin_ids:
        await callback.answer("❌ Admin only!", show_alert=True)
        return
    
    bot_locked = not bot_locked
    status = "🔒 LOCKED" if bot_locked else "🔓 UNLOCKED"
    
    await callback.answer(f"Bot is now {status}!", show_alert=True)
    await callback_admin_panel(callback)

@dp.callback_query(F.data == "broadcast")
async def callback_broadcast(callback: types.CallbackQuery):
    if callback.from_user.id not in admin_ids:
        await callback.answer("❌ Admin only!", show_alert=True)
        return
    
    text = f"""
╔═══════════════════════╗
    📢 <b>BROADCAST</b> 📢
╚═══════════════════════╝

Send a message to all users!

<b>Total Recipients:</b> {len(active_users)}

<b>Command:</b>
<code>/broadcast Your message here</code>

⚠️ Use this feature responsibly!
"""
    
    back_keyboard = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🔙 Admin Panel", callback_data="admin_panel")]
    ])
    
    await callback.message.edit_text(text, reply_markup=back_keyboard, parse_mode="HTML")
    await callback.answer()

@dp.callback_query(F.data == "add_premium")
async def callback_add_premium(callback: types.CallbackQuery):
    if callback.from_user.id not in admin_ids:
        await callback.answer("❌ Admin only!", show_alert=True)
        return
    
    text = """
╔═══════════════════════╗
    💎 <b>ADD PREMIUM</b> 💎
╚═══════════════════════╝

Give premium access to users!

<b>Command:</b>
<code>/addpremium USER_ID DAYS</code>

<b>Examples:</b>
<code>/addpremium 123456789 30</code> (30 days)
<code>/addpremium 987654321 7</code> (7 days)

Premium benefits:
• 50 file limit (vs 20)
• Priority support
• Premium badge
"""
    
    back_keyboard = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🔙 Admin Panel", callback_data="admin_panel")]
    ])
    
    await callback.message.edit_text(text, reply_markup=back_keyboard, parse_mode="HTML")
    await callback.answer()

@dp.callback_query(F.data == "admin_clean_files")
async def callback_admin_clean_files(callback: types.CallbackQuery):
    if callback.from_user.id not in admin_ids:
        await callback.answer("❌ Admin only!", show_alert=True)
        return
    
    text = """
╔═══════════════════════╗
    🗑️ <b>CLEAN FILES</b> 🗑️
╚═══════════════════════╝

Clean old or unused files from the system.

<b>Options:</b>
• Delete files older than 30 days
• Remove files from banned users
• Clean temp/log files

<b>Command:</b>
<code>/clean OPTION</code>

⚠️ This action cannot be undone!
"""
    
    back_keyboard = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🔙 Admin Panel", callback_data="admin_panel")]
    ])
    
    await callback.message.edit_text(text, reply_markup=back_keyboard, parse_mode="HTML")
    await callback.answer()

@dp.callback_query(F.data == "admin_backup_db")
async def callback_admin_backup_db(callback: types.CallbackQuery):
    if callback.from_user.id not in admin_ids:
        await callback.answer("❌ Admin only!", show_alert=True)
        return
    
    try:
        backup_path = IROTECH_DIR / f"backup_{datetime.now().strftime('%Y%m%d_%H%M%S')}.db"
        
        conn = sqlite3.connect(DATABASE_PATH)
        backup_conn = sqlite3.connect(backup_path)
        conn.backup(backup_conn)
        backup_conn.close()
        conn.close()
        
        await callback.answer("✅ Database backed up!", show_alert=True)
        
        await callback.message.answer_document(
            FSInputFile(backup_path),
            caption="💾 <b>Database Backup</b>\n\nCreated: " + datetime.now().strftime('%Y-%m-%d %H:%M:%S'),
            parse_mode="HTML"
        )
        
        backup_path.unlink()
        
    except Exception as e:
        logger.error(f"Backup error: {e}")
        await callback.answer(f"❌ Backup failed: {str(e)}", show_alert=True)

@dp.callback_query(F.data == "admin_view_logs")
async def callback_admin_view_logs(callback: types.CallbackQuery):
    if callback.from_user.id not in admin_ids:
        await callback.answer("❌ Admin only!", show_alert=True)
        return
    
    text = """
╔═══════════════════════╗
    📝 <b>SYSTEM LOGS</b> 📝
╚═══════════════════════╝

View bot logs and activity.

<b>Available Logs:</b>
• Error logs
• User activity
• Script executions
• Admin actions

Logs are stored in the system directory.
"""
    
    back_keyboard = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🔙 Admin Panel", callback_data="admin_panel")]
    ])
    
    await callback.message.edit_text(text, reply_markup=back_keyboard, parse_mode="HTML")
    await callback.answer()

@dp.callback_query(F.data == "admin_restart_bot")
async def callback_admin_restart_bot(callback: types.CallbackQuery):
    if callback.from_user.id != OWNER_ID:
        await callback.answer("❌ Owner only!", show_alert=True)
        return
    
    text = """
╔═══════════════════════╗
    🔄 <b>RESTART BOT</b> 🔄
╚═══════════════════════╝

⚠️ <b>WARNING:</b>
This will restart the entire bot!

All running scripts will be stopped.
Users may experience brief downtime.

<b>Only use if necessary!</b>

Use <code>/restart</code> to confirm.
"""
    
    back_keyboard = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🔙 Admin Panel", callback_data="admin_panel")]
    ])
    
    await callback.message.edit_text(text, reply_markup=back_keyboard, parse_mode="HTML")
    await callback.answer()

@dp.message(Command("addadmin"))
async def cmd_add_admin(message: types.Message):
    if message.from_user.id not in admin_ids:
        await message.answer("❌ Permission denied!")
        return
    
    try:
        args = message.text.split()
        if len(args) != 2:
            await message.answer("Usage: /addadmin USER_ID")
            return
        
        new_admin_id = int(args[1])
        
        if new_admin_id in admin_ids:
            await message.answer(f"✅ User {new_admin_id} is already an admin!")
            return
        
        admin_ids.add(new_admin_id)
        
        conn = sqlite3.connect(DATABASE_PATH)
        c = conn.cursor()
        c.execute('INSERT OR IGNORE INTO admins (user_id) VALUES (?)', (new_admin_id,))
        conn.commit()
        conn.close()
        
        await message.answer(f"✅ User <code>{new_admin_id}</code> added as admin!", parse_mode="HTML")
        
    except ValueError:
        await message.answer("❌ Invalid USER_ID!")
    except Exception as e:
        logger.error(f"Error adding admin: {e}")
        await message.answer(f"❌ Error: {str(e)}")

@dp.message(Command("removeadmin"))
async def cmd_remove_admin(message: types.Message):
    if message.from_user.id != OWNER_ID:
        await message.answer("❌ Only owner can remove admins!")
        return
    
    try:
        args = message.text.split()
        if len(args) != 2:
            await message.answer("Usage: /removeadmin USER_ID")
            return
        
        remove_admin_id = int(args[1])
        
        if remove_admin_id == OWNER_ID:
            await message.answer("❌ Cannot remove owner!")
            return
        
        if remove_admin_id not in admin_ids:
            await message.answer(f"❌ User {remove_admin_id} is not an admin!")
            return
        
        admin_ids.remove(remove_admin_id)
        
        conn = sqlite3.connect(DATABASE_PATH)
        c = conn.cursor()
        c.execute('DELETE FROM admins WHERE user_id = ?', (remove_admin_id,))
        conn.commit()
        conn.close()
        
        await message.answer(f"✅ User <code>{remove_admin_id}</code> removed from admins!", parse_mode="HTML")
        
    except ValueError:
        await message.answer("❌ Invalid USER_ID!")
    except Exception as e:
        logger.error(f"Error removing admin: {e}")
        await message.answer(f"❌ Error: {str(e)}")

@dp.message(Command("addpremium"))
async def cmd_add_premium(message: types.Message):
    if message.from_user.id not in admin_ids:
        await message.answer("❌ Permission denied!")
        return
    
    try:
        args = message.text.split()
        if len(args) != 3:
            await message.answer("Usage: /addpremium USER_ID DAYS")
            return
        
        user_id = int(args[1])
        days = int(args[2])
        
        if days <= 0:
            await message.answer("❌ Days must be greater than 0!")
            return
        
        expiry = datetime.now() + timedelta(days=days)
        user_subscriptions[user_id] = {'expiry': expiry}
        
        conn = sqlite3.connect(DATABASE_PATH)
        c = conn.cursor()
        c.execute('INSERT OR REPLACE INTO subscriptions (user_id, expiry) VALUES (?, ?)',
                  (user_id, expiry.isoformat()))
        conn.commit()
        conn.close()
        
        await message.answer(
            f"✅ <b>Premium Added!</b>\n\n"
            f"User: <code>{user_id}</code>\n"
            f"Duration: {days} days\n"
            f"Expires: {expiry.strftime('%Y-%m-%d %H:%M')}",
            parse_mode="HTML"
        )
        
    except ValueError:
        await message.answer("❌ Invalid input!")
    except Exception as e:
        logger.error(f"Error adding premium: {e}")
        await message.answer(f"❌ Error: {str(e)}")

@dp.message(Command("ban"))
async def cmd_ban_user(message: types.Message):
    if message.from_user.id not in admin_ids:
        await message.answer("❌ Permission denied!")
        return
    
    try:
        args = message.text.split(maxsplit=2)
        if len(args) < 2:
            await message.answer("Usage: /ban USER_ID [REASON]")
            return
        
        ban_user_id = int(args[1])
        reason = args[2] if len(args) > 2 else "No reason provided"
        
        if ban_user_id in admin_ids:
            await message.answer("❌ Cannot ban an admin!")
            return
        
        banned_users.add(ban_user_id)
        
        conn = sqlite3.connect(DATABASE_PATH)
        c = conn.cursor()
        c.execute('INSERT OR REPLACE INTO banned_users (user_id, banned_date, reason) VALUES (?, ?, ?)',
                  (ban_user_id, datetime.now().isoformat(), reason))
        conn.commit()
        conn.close()
        
        await message.answer(f"🚫 User <code>{ban_user_id}</code> has been banned!\n\nReason: {reason}", parse_mode="HTML")
        
    except ValueError:
        await message.answer("❌ Invalid USER_ID!")
    except Exception as e:
        logger.error(f"Error banning user: {e}")
        await message.answer(f"❌ Error: {str(e)}")

@dp.message(Command("unban"))
async def cmd_unban_user(message: types.Message):
    if message.from_user.id not in admin_ids:
        await message.answer("❌ Permission denied!")
        return
    
    try:
        args = message.text.split()
        if len(args) != 2:
            await message.answer("Usage: /unban USER_ID")
            return
        
        unban_user_id = int(args[1])
        
        if unban_user_id not in banned_users:
            await message.answer(f"❌ User {unban_user_id} is not banned!")
            return
        
        banned_users.remove(unban_user_id)
        
        conn = sqlite3.connect(DATABASE_PATH)
        c = conn.cursor()
        c.execute('DELETE FROM banned_users WHERE user_id = ?', (unban_user_id,))
        conn.commit()
        conn.close()
        
        await message.answer(f"✅ User <code>{unban_user_id}</code> has been unbanned!", parse_mode="HTML")
        
    except ValueError:
        await message.answer("❌ Invalid USER_ID!")
    except Exception as e:
        logger.error(f"Error unbanning user: {e}")
        await message.answer(f"❌ Error: {str(e)}")

@dp.message(Command("broadcast"))
async def cmd_broadcast(message: types.Message):
    if message.from_user.id not in admin_ids:
        await message.answer("❌ Permission denied!")
        return
    
    try:
        broadcast_text = message.text.replace("/broadcast", "", 1).strip()
        
        if not broadcast_text:
            await message.answer("Usage: /broadcast Your message here")
            return
        
        sent_count = 0
        failed_count = 0
        
        status_msg = await message.answer(f"📢 Broadcasting to {len(active_users)} users...")
        
        for user_id in active_users:
            if user_id in banned_users:
                continue
            
            try:
                await bot.send_message(user_id, f"📢 <b>Announcement:</b>\n\n{broadcast_text}", parse_mode="HTML")
                sent_count += 1
                await asyncio.sleep(0.05)
            except Exception as e:
                logger.error(f"Failed to send to {user_id}: {e}")
                failed_count += 1
        
        await status_msg.edit_text(
            f"✅ <b>Broadcast Complete!</b>\n\n"
            f"✅ Sent: {sent_count}\n"
            f"❌ Failed: {failed_count}",
            parse_mode="HTML"
        )
        
    except Exception as e:
        logger.error(f"Error broadcasting: {e}")
        await message.answer(f"❌ Error: {str(e)}")

@dp.message(Command("search"))
async def cmd_search_files(message: types.Message):
    user_id = message.from_user.id
    
    try:
        args = message.text.split(maxsplit=1)
        if len(args) < 2:
            await message.answer("Usage: /search filename")
            return
        
        search_term = args[1].lower()
        user_file_list = user_files.get(user_id, [])
        
        matches = [f for f in user_file_list if search_term in f[0].lower()]
        
        if not matches:
            await message.answer(f"🔍 No files found matching '<code>{search_term}</code>'", parse_mode="HTML")
            return
        
        text = f"🔍 <b>Search Results ({len(matches)}):</b>\n\n"
        
        for file_name, file_type in matches:
            icon = "🐍" if file_type == "py" else "🟨" if file_type == "js" else "📦"
            text += f"{icon} <code>{file_name}</code>\n"
        
        await message.answer(text, parse_mode="HTML")
        
    except Exception as e:
        logger.error(f"Search error: {e}")
        await message.answer(f"❌ Error: {str(e)}")

@dp.message(Command("help"))
async def cmd_help(message: types.Message):
    text = """
╔═══════════════════════╗
    ℹ️ <b>HELP & INFO</b> ℹ️
╚═══════════════════════╝

<b>🎯 HOW TO USE:</b>

1️⃣ <b>Upload Files:</b>
   • Click 'Upload File'
   • Send your .py or .zip Python project
   • File will be saved automatically

2️⃣ <b>Run Scripts:</b>
   • Go to 'My Files'
   • Click 'Run' on any file
   • Monitor script execution

3️⃣ <b>Manage Files:</b>
   • View all files in 'My Files'
   • Add to favorites with ⭐
   • Delete unwanted files

4️⃣ <b>Search:</b>
   • Use /search [filename]
   • Quick file lookup

━━━━━━━━━━━━━━━━━━━━
<b>💡 COMMANDS:</b>

/start - Start the bot
/help - Show this help
/search - Search files
/stats - Your statistics
/premium - Free info

<b>Need help? Contact owner! 💬</b>
"""
    
    back_keyboard = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🎯 Features", callback_data="all_features")],
        [InlineKeyboardButton(text="🏠 Main Menu", callback_data="back_to_main")]
    ])
    
    await message.answer(text, reply_markup=back_keyboard, parse_mode="HTML")

@dp.message(Command("stats"))
async def cmd_stats(message: types.Message):
    user_id = message.from_user.id
    user_file_count = len(user_files.get(user_id, []))
    user_fav_count = len(user_favorites.get(user_id, []))
    is_premium = user_id in user_subscriptions and user_subscriptions[user_id]['expiry'] > datetime.now()
    
    text = f"""
╔═══════════════════════╗
    📊 <b>YOUR STATISTICS</b> 📊
╚═══════════════════════╝

<b>👤 USER INFO:</b>

🆔 User ID: <code>{user_id}</code>
👤 Name: {message.from_user.full_name}
📦 Files Uploaded: {user_file_count} (Unlimited ♾️)
⭐ Favorites: {user_fav_count}
💎 Account: Free 🆓 (Unlimited ♾️)
🚀 Running: {sum(1 for k in bot_scripts if k.startswith(f"{user_id}_"))}

━━━━━━━━━━━━━━━━━━━━
📈 <b>USAGE:</b>

📤 Uploads: {bot_stats.get('total_uploads', 0)}
📥 Downloads: {bot_stats.get('total_downloads', 0)}
▶️ Script Runs: {bot_stats.get('total_runs', 0)}

{'✅ Bot Status: Active' if not bot_locked else '🔒 Bot: Maintenance'}
"""
    
    if user_id in admin_ids:
        text += f"\n━━━━━━━━━━━━━━━━━━━━\n👑 <b>ADMIN STATS:</b>\n"
        text += f"👥 Total Users: {len(active_users)}\n"
        text += f"📁 Total Files: {sum(len(files) for files in user_files.values())}\n"
    
    back_keyboard = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🏠 Main Menu", callback_data="back_to_main")]
    ])
    
    await message.answer(text, reply_markup=back_keyboard, parse_mode="HTML")


# ── WEBSITE: LANDING PAGE + ADMIN PANEL ──────────────
import base64
import hmac
import html as html_lib

ADMIN_PASSWORD = os.getenv('ADMIN_PASSWORD', '')
_BOT_USERNAME = None

def _auth_ok(request):
    if not ADMIN_PASSWORD:
        return True  # password set nahi hai to panel open rahega
    h = request.headers.get('Authorization', '')
    if not h.startswith('Basic '):
        return False
    try:
        pwd = base64.b64decode(h[6:]).decode('utf-8').partition(':')[2]
    except Exception:
        return False
    return hmac.compare_digest(pwd.encode(), ADMIN_PASSWORD.encode())

def _deny():
    if not ADMIN_PASSWORD:
        return web.Response(text="Panel off hai. Render Environment mein ADMIN_PASSWORD set karo.", status=503)
    return web.Response(status=401, headers={'WWW-Authenticate': 'Basic realm="Admin"'}, text="Login required")

def _running_list():
    out = []
    for key, info in list(bot_scripts.items()):
        try:
            if info['process'].poll() is None:
                out.append({'key': key, 'owner': info['script_owner_id'], 'file': info['file_name'],
                            'type': info['type'], 'since': info['start_time'].strftime('%d %b %H:%M')})
        except Exception:
            pass
    return out

def _collect():
    now = datetime.now()
    running = _running_list()
    users = []
    try:
        conn = sqlite3.connect(DATABASE_PATH)
        c = conn.cursor()
        c.execute('SELECT user_id, join_date, last_active FROM active_users ORDER BY COALESCE(last_active, join_date) DESC LIMIT 300')
        for uid, jd, la in c.fetchall():
            users.append({'id': uid, 'joined': (jd or '-')[:16].replace('T', ' '), 'last': (la or '-')[:16].replace('T', ' '),
                          'files': len(user_files.get(uid, [])), 'banned': uid in banned_users, 'admin': uid in admin_ids,
                          'sub': uid in user_subscriptions and user_subscriptions[uid]['expiry'] > now,
                          'running': sum(1 for r in running if r['owner'] == uid)})
        conn.close()
    except Exception as e:
        logger.error(f"Panel user fetch error: {e}")
    extra = {'joins7': [], 'new_today': 0, 'active24': 0}
    try:
        conn = sqlite3.connect(DATABASE_PATH)
        c = conn.cursor()
        d6 = (now - timedelta(days=6)).strftime('%Y-%m-%d')
        c.execute("SELECT substr(join_date,1,10), COUNT(*) FROM active_users WHERE join_date >= ? GROUP BY 1", (d6,))
        cnt = dict(c.fetchall())
        days = [now - timedelta(days=i) for i in range(6, -1, -1)]
        extra['joins7'] = [[x.strftime('%d %b'), cnt.get(x.strftime('%Y-%m-%d'), 0)] for x in days]
        extra['new_today'] = cnt.get(now.strftime('%Y-%m-%d'), 0)
        c.execute("SELECT COUNT(*) FROM active_users WHERE last_active >= ?", ((now - timedelta(hours=24)).isoformat(),))
        extra['active24'] = c.fetchone()[0]
        conn.close()
    except Exception as e:
        logger.error(f"Panel stats error: {e}")
    types = {}
    for fl in user_files.values():
        for f in fl:
            types[f[1]] = types.get(f[1], 0) + 1
    top = sorted(((u, len(fl)) for u, fl in user_files.items()), key=lambda x: -x[1])[:5]
    try:
        ram = round(psutil.Process().memory_info().rss / 1024 / 1024, 1)
    except Exception:
        ram = 0
    up = now - BOT_START_TIME
    return {'total_users': len(active_users), 'banned': len(banned_users), 'admins': len(admin_ids),
            'total_files': sum(len(f) for f in user_files.values()), 'running_now': len(running),
            'uploads': bot_stats.get('total_uploads', 0), 'downloads': bot_stats.get('total_downloads', 0),
            'runs': bot_stats.get('total_runs', 0), 'locked': bot_locked,
            'uptime': f"{up.days}d {up.seconds // 3600}h {(up.seconds % 3600) // 60}m",
            'files_list': [{'owner': u, 'name': f[0], 'type': f[1], 'on': f'{u}_{f[0]}' in bot_scripts and bot_scripts[f'{u}_{f[0]}']['process'].poll() is None} for u, fl in user_files.items() for f in fl][:500], 'ram_mb': ram, 'cpu': psutil.cpu_percent(interval=None), 'running': running, 'users': users, 'types': types, 'top': top, **extra}

def _stop_script(key):
    info = bot_scripts.get(key)
    if not info:
        return False
    try:
        lf = info.get('log_file')
        if lf and not lf.closed:
            lf.close()
        parent = psutil.Process(info['process'].pid)
        for ch in parent.children(recursive=True):
            ch.terminate()
        parent.terminate()
    except Exception:
        pass
    bot_scripts.pop(key, None)
    try:
        _autostart_remove(info.get('script_owner_id'), info.get('file_name'))
    except Exception:
        pass
    return True

def _db(sql, params=()):
    conn = sqlite3.connect(DATABASE_PATH)
    conn.execute(sql, params)
    conn.commit()
    conn.close()

async def _broadcast(text):
    sent = 0
    for uid in list(active_users):
        if uid in banned_users:
            continue
        try:
            await bot.send_message(uid, text)
            sent += 1
        except Exception:
            pass
        await asyncio.sleep(0.06)
    logger.info(f"Broadcast finished: {sent} users")

async def panel_action(request):
    global bot_locked
    if not _auth_ok(request):
        return _deny()
    if request.headers.get('X-Panel') != '1':
        return web.json_response({'ok': False, 'msg': 'Bad request'}, status=400)
    try:
        d = await request.json()
        act = d.get('action')
        uid = int(d['user_id']) if d.get('user_id') not in (None, '') else None
    except Exception:
        return web.json_response({'ok': False, 'msg': 'Invalid data'}, status=400)

    if act in ('ban', 'unban', 'stop_user') and uid is None:
        return web.json_response({'ok': False, 'msg': 'User ID chahiye'})
    if act == 'ban':
        if uid in admin_ids:
            return web.json_response({'ok': False, 'msg': 'Admin ko ban nahi kar sakte'})
        banned_users.add(uid)
        _db('INSERT OR REPLACE INTO banned_users (user_id, banned_date, reason) VALUES (?, ?, ?)',
            (uid, datetime.now().isoformat(), 'Banned from web panel'))
        for r in _running_list():
            if r['owner'] == uid:
                _stop_script(r['key'])
        return web.json_response({'ok': True, 'msg': f'{uid} banned'})
    if act == 'unban':
        banned_users.discard(uid)
        _db('DELETE FROM banned_users WHERE user_id = ?', (uid,))
        return web.json_response({'ok': True, 'msg': f'{uid} unbanned'})
    if act == 'stop_user':
        n = sum(1 for r in _running_list() if r['owner'] == uid and _stop_script(r['key']))
        return web.json_response({'ok': True, 'msg': f'{n} bot(s) stop kiye'})
    if act == 'stop_script':
        return web.json_response({'ok': _stop_script(d.get('key')), 'msg': 'Script stop kiya'})
    if act == 'stop_all':
        n = sum(1 for r in _running_list() if _stop_script(r['key']))
        return web.json_response({'ok': True, 'msg': f'{n} bot(s) stop kiye'})
    if act == 'lock':
        bot_locked = not bot_locked
        return web.json_response({'ok': True, 'msg': 'Bot LOCKED' if bot_locked else 'Bot UNLOCKED'})
    if act == 'broadcast':
        text = (d.get('text') or '').strip()
        if not text or len(text) > 3500:
            return web.json_response({'ok': False, 'msg': 'Message khali ya bahut lamba hai'})
        asyncio.create_task(_broadcast(text))
        return web.json_response({'ok': True, 'msg': f'Broadcast shuru: {len(active_users)} users ko'})
    return web.json_response({'ok': False, 'msg': 'Unknown action'})

async def panel_api(request):
    if not _auth_ok(request):
        return _deny()
    return web.json_response(_collect())

ADMIN_HTML = """<!DOCTYPE html><html><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>Genius HostBot - Dashboard</title><style>
*{box-sizing:border-box}body{margin:0;font-family:system-ui,sans-serif;background:#0b0f17;color:#e6edf3;display:flex;min-height:100vh}
#side{width:220px;background:#111826;border-right:1px solid #1f2a3d;padding:16px 10px;position:fixed;top:0;bottom:0;left:0;z-index:20;transition:.2s}
.logo{font-weight:800;font-size:17px;padding:4px 10px 16px}.logo span{color:#58a6ff}
.nav{display:block;width:100%;text-align:left;background:none;border:0;color:#9aa7b5;padding:11px 12px;border-radius:8px;font-size:14px;cursor:pointer;margin-bottom:3px}
.nav:hover{background:#1a2438}.nav.on{background:#1f6feb;color:#fff}
.side-foot{position:absolute;bottom:14px;left:14px;font-size:11px;color:#6b7785}
#main{margin-left:220px;flex:1;padding:18px;min-width:0}
#top{display:none;align-items:center;gap:10px;margin-bottom:12px}
h2{margin:0 0 4px;font-size:20px}.sub{color:#8b949e;font-size:12px;margin-bottom:16px}
.grid{display:grid;grid-template-columns:repeat(auto-fit,minmax(135px,1fr));gap:10px;margin-bottom:18px}
.card{background:#111826;border:1px solid #1f2a3d;border-radius:12px;padding:14px}.n{font-size:22px;font-weight:700}.l{font-size:12px;color:#8b949e;margin-top:3px}
.box{background:#111826;border:1px solid #1f2a3d;border-radius:12px;padding:14px;margin-bottom:14px}
.wrap{overflow-x:auto}table{width:100%;border-collapse:collapse;font-size:13px}th,td{text-align:left;padding:8px;border-bottom:1px solid #1f2a3d;white-space:nowrap}th{color:#8b949e;font-weight:600}
button.a{background:#21262d;color:#e6edf3;border:1px solid #30363d;border-radius:6px;padding:6px 10px;font-size:12px;cursor:pointer}
.r{background:#da3633!important;border-color:#da3633!important}.g{background:#238636!important;border-color:#238636!important}.b{background:#1f6feb!important;border-color:#1f6feb!important}
input,textarea{background:#0b0f17;color:#e6edf3;border:1px solid #30363d;border-radius:8px;padding:9px;font-size:13px;width:100%}
.row{display:flex;gap:8px;flex-wrap:wrap;margin-bottom:10px}.row input{flex:1;min-width:120px}
.tag{padding:2px 8px;border-radius:20px;font-size:11px}.on{}.t-on{background:#12361f;color:#3fb950}.t-off{background:#2a2f38;color:#8b949e}
.two{display:grid;grid-template-columns:repeat(auto-fit,minmax(280px,1fr));gap:14px}.bars{display:flex;align-items:flex-end;gap:8px;height:130px;margin-top:12px}
.bc{flex:1;text-align:center;display:flex;flex-direction:column;justify-content:flex-end;align-items:center}.bc i{font-style:normal;font-size:11px;color:#9aa7b5}.bc small{font-size:10px;color:#6b7785}
.bar{width:100%;background:linear-gradient(#58a6ff,#1f6feb);border-radius:5px 5px 0 0}.hb{display:flex;align-items:center;gap:8px;margin-top:8px;font-size:12px}.hb span{width:56px;overflow:hidden;text-overflow:ellipsis}
.hb div{flex:1;background:#1a2438;border-radius:4px;height:8px}.hb div div{background:#1f6feb;height:8px}.hb em{font-style:normal;color:#9aa7b5;width:28px;text-align:right}
#toast{position:fixed;bottom:16px;left:50%;transform:translateX(-50%);padding:10px 18px;border-radius:8px;display:none;font-size:13px;z-index:99}
@media(max-width:760px){#side{left:-230px}#side.open{left:0}#main{margin-left:0}#top{display:flex}}
</style></head><body>
<div id="side"><div class="logo">🚀 Genius <span>HostBot</span></div>
<button class="nav on" data-p="over">📊 Overview</button><button class="nav" data-p="bots">🤖 Running Bots</button>
<button class="nav" data-p="files">📁 All Files</button><button class="nav" data-p="users">👥 Users</button>
<button class="nav" data-p="cast">📢 Broadcast</button><button class="nav" data-p="set">⚙️ Settings</button>
<a class="nav" href="/" style="text-decoration:none">🌐 Website</a><div class="side-foot">Developed by RG CHEAT</div></div>
<div id="main"><div id="top"><button class="a b" onclick="$('side').classList.toggle('open')">☰ Menu</button><b>Genius HostBot</b></div>
<h2 id="ttl"></h2><div class="sub" id="st"></div><div id="view"></div></div><div id="toast"></div>
<script>
const $=id=>document.getElementById(id);let D=null,P='over',Q='';
const esc=s=>String(s).replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
function toast(m,ok=true){const t=$('toast');t.textContent=m;t.style.background=ok?'#238636':'#da3633';t.style.display='block';setTimeout(()=>t.style.display='none',2600)}
async function act(b){try{const r=await fetch('/admin/action',{method:'POST',headers:{'Content-Type':'application/json','X-Panel':'1'},body:JSON.stringify(b)});const j=await r.json();toast(j.msg||'Done',j.ok);load()}catch(e){toast('Error',false)}}
document.querySelectorAll('button.nav').forEach(b=>b.onclick=()=>{P=b.dataset.p;document.querySelectorAll('button.nav').forEach(x=>x.classList.toggle('on',x==b));$('side').classList.remove('open');render()});
const card=(l,n)=>`<div class="card"><div class="n">${esc(n)}</div><div class="l">${l}</div></div>`;
function bots(){return `<div class="box wrap"><table><tr><th>User</th><th>File</th><th>Type</th><th>Start</th><th></th></tr>`+(D.running.map(r=>`<tr><td>${r.owner}</td><td>${esc(r.file)}</td><td>${esc(r.type)}</td><td>${esc(r.since)}</td><td><button class="a r" onclick='act({action:"stop_script",key:${JSON.stringify(r.key)}})'>Stop</button></td></tr>`).join('')||'<tr><td colspan=5>Koi bot nahi chal raha</td></tr>')+`</table></div>`}
function render(){if(!D)return;const T={over:'Overview',bots:'Running Bots',files:'All Files',users:'Users',cast:'Broadcast',set:'Settings'};$('ttl').textContent=T[P];
$('st').textContent=(D.locked?'🔒 Maintenance mode':'✅ Bot active')+' • uptime '+D.uptime+' • auto-refresh 15s';let h='';
if(P=='over'){const mx=Math.max(1,...D.joins7.map(x=>x[1])),tt=Math.max(1,...Object.values(D.types));
h=`<div class="grid">${card('👥 Total Members',D.total_users)}${card('🆕 New today',D.new_today)}${card('🔥 Active 24h',D.active24)}${card('🟢 Bots running',D.running_now)}${card('📁 Files',D.total_files)}${card('🚫 Banned',D.banned)}${card('👑 Admins',D.admins)}${card('📤 Uploads',D.uploads)}${card('📥 Downloads',D.downloads)}${card('▶️ Script runs',D.runs)}${card('🧠 RAM MB',D.ram_mb)}${card('⚙️ CPU %',D.cpu)}</div>
<div class="two"><div class="box"><b>📈 Naye members (7 din)</b><div class="bars">${D.joins7.map(x=>`<div class="bc"><i>${x[1]}</i><div class="bar" style="height:${8+x[1]/mx*80}px"></div><small>${x[0]}</small></div>`).join('')}</div></div>
<div class="box"><b>🗂 File types</b>${Object.entries(D.types).map(([k,v])=>`<div class="hb"><span>${esc(k)}</span><div><div style="width:${v/tt*100}%"></div></div><em>${v}</em></div>`).join('')||'<p class="sub">Abhi koi file nahi</p>'}
<b style="display:block;margin-top:14px">🏆 Top users (files)</b>${D.top.map(t=>`<div class="hb"><span>${t[0]}</span><div><div style="width:${t[1]/Math.max(1,D.top[0][1])*100}%"></div></div><em>${t[1]}</em></div>`).join('')||'<p class="sub">-</p>'}</div></div>
<h3>🤖 Abhi chal rahe bots</h3>`+bots()}
if(P=='bots')h=bots();
if(P=='files')h=`<input placeholder="🔍 File ya user ID search..." value="${esc(Q)}" oninput="Q=this.value;render()" style="margin-bottom:10px"><div class="box wrap"><table><tr><th>User</th><th>File</th><th>Type</th><th>Status</th></tr>`+(D.files_list.filter(f=>(f.name+f.owner).toLowerCase().includes(Q.toLowerCase())).map(f=>`<tr><td>${f.owner}</td><td>${esc(f.name)}</td><td>${esc(f.type)}</td><td><span class="tag ${f.on?'t-on':'t-off'}">${f.on?'Running':'Stopped'}</span></td></tr>`).join('')||'<tr><td colspan=4>Koi file nahi</td></tr>')+`</table></div>`;
if(P=='users')h=`<input placeholder="🔍 User ID search..." value="${esc(Q)}" oninput="Q=this.value;render()" style="margin-bottom:10px"><div class="box wrap"><table><tr><th>User ID</th><th>Joined</th><th>Last active</th><th>Files</th><th>Run</th><th>Tags</th><th></th></tr>`+(D.users.filter(u=>String(u.id).includes(Q)).map(u=>`<tr><td>${u.id}</td><td>${esc(u.joined)}</td><td>${esc(u.last)}</td><td>${u.files}</td><td>${u.running}</td><td>${u.banned?'🚫':''}${u.admin?'👑':''}</td><td>${u.banned?`<button class="a g" onclick="act({action:'unban',user_id:${u.id}})">Unban</button>`:`<button class="a r" onclick="act({action:'ban',user_id:${u.id}})">Ban</button>`} <button class="a" onclick="act({action:'stop_user',user_id:${u.id}})">Stop bots</button></td></tr>`).join('')||'<tr><td colspan=7>Koi user nahi</td></tr>')+`</table></div>`;
if(P=='cast')h=`<div class="box"><b>📢 Saare users ko message</b><textarea id="bc" rows="5" placeholder="Message likho..." style="margin:10px 0"></textarea><button class="a b" onclick="cast()">Send to all users</button></div>`;
if(P=='set')h=`<div class="box"><b>Bot control</b><div class="row" style="margin-top:10px"><button class="a b" onclick="act({action:'lock'})">🔒 Lock / Unlock bot</button><button class="a r" onclick="if(confirm('Saare bots stop karein?'))act({action:'stop_all'})">🛑 Stop ALL bots</button></div></div><div class="box"><b>Manual ban / unban</b><div class="row" style="margin-top:10px"><input id="uid" placeholder="User ID" inputmode="numeric"><button class="a r" onclick="m('ban')">Ban</button><button class="a g" onclick="m('unban')">Unban</button></div></div>`;
$('view').innerHTML=h;const i=document.querySelector('#view input[oninput]');if(i&&Q){i.focus();i.setSelectionRange(Q.length,Q.length)}}
function m(a){const u=$('uid').value.trim();if(!u)return toast('User ID daalo',false);act({action:a,user_id:u})}
function cast(){const t=$('bc').value.trim();if(!t)return toast('Message likho',false);if(confirm('Sabko bhejein?')){act({action:'broadcast',text:t});$('bc').value=''}}
async function load(){try{D=await (await fetch('/admin/api')).json();const a=document.activeElement;if(a&&(a.tagName=='TEXTAREA'||a.id=='uid'))return;render()}catch(e){$('st').textContent='Load error'}}
load();setInterval(load,15000);
</script></body></html>"""

async def admin_page(request):
    if not _auth_ok(request):
        return _deny()
    return web.Response(text=ADMIN_HTML, content_type='text/html')

LANDING_HTML = """<!DOCTYPE html><html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>Genius HostBot - Free Telegram Bot Hosting</title><meta name="description" content="Python bots ko Telegram se host karo. Unlimited uploads, koi premium nahi.">
<style>
*{box-sizing:border-box}html{scroll-behavior:smooth}body{margin:0;font-family:system-ui,sans-serif;background:#070b12;color:#e6edf3;line-height:1.55}
nav{display:flex;justify-content:space-between;align-items:center;padding:14px 22px;position:sticky;top:0;background:#070b12ee;backdrop-filter:blur(8px);border-bottom:1px solid #151d2c;z-index:5}
nav b{font-size:18px}nav b span,h1 span,h2 span{color:#58a6ff}nav a{color:#9aa7b5;text-decoration:none;margin-left:16px;font-size:14px}
.hero{text-align:center;padding:70px 20px 40px;background:radial-gradient(circle at 50% 0,#14366a 0,#070b12 62%)}
.badge{display:inline-block;background:#12361f;color:#3fb950;border-radius:20px;padding:5px 14px;font-size:13px;margin-bottom:16px}
h1{font-size:40px;margin:0 0 12px;line-height:1.15}.hero p{color:#9aa7b5;max-width:560px;margin:0 auto 26px;font-size:17px}
.btn{display:inline-block;padding:13px 24px;border-radius:10px;text-decoration:none;font-weight:600;margin:5px;font-size:15px}.p{background:#1f6feb;color:#fff}.s{border:1px solid #2b374d;color:#e6edf3}
.stats{display:flex;justify-content:center;gap:12px;flex-wrap:wrap;padding:6px 20px 30px}.st{background:#0f1624;border:1px solid #1f2a3d;border-radius:14px;padding:16px 30px;text-align:center}.st b{font-size:26px;display:block}.st small{color:#8b949e}
section{max-width:900px;margin:0 auto;padding:36px 20px}h2{text-align:center;font-size:26px;margin:0 0 22px}
.g{display:grid;grid-template-columns:repeat(auto-fit,minmax(230px,1fr));gap:14px}.f{background:#0f1624;border:1px solid #1f2a3d;border-radius:14px;padding:18px}.f h3{margin:0 0 6px;font-size:16px}.f p{margin:0;color:#9aa7b5;font-size:14px}
.step{display:flex;gap:14px;align-items:flex-start;background:#0f1624;border:1px solid #1f2a3d;border-radius:14px;padding:16px;margin-bottom:10px}.num{background:#1f6feb;border-radius:50%;min-width:34px;height:34px;display:flex;align-items:center;justify-content:center;font-weight:700}
details{background:#0f1624;border:1px solid #1f2a3d;border-radius:12px;padding:14px;margin-bottom:10px}summary{cursor:pointer;font-weight:600}details p{color:#9aa7b5;margin:10px 0 0}
.cta{text-align:center;background:linear-gradient(135deg,#12315f,#0f1624);border-radius:18px;padding:34px 20px}
footer{text-align:center;color:#6b7785;padding:28px 10px;font-size:13px;border-top:1px solid #151d2c}footer a{color:#58a6ff;text-decoration:none;margin:0 6px}
</style></head><body>
<nav><b>🚀 Genius <span>HostBot</span></b><div><a href="#features">Features</a><a href="#how">How it works</a><a href="#faq">FAQ</a></div></nav>
<div class="hero"><div class="badge">🆓 100% Free &bull; Unlimited Uploads</div>
<h1>Apne Bots ko <span>24/7</span> Host Karo<br>Seedha Telegram Se</h1>
<p>Python (.py),  ya ZIP file bhejo, dependencies khud install hongi aur bot chalu. Koi premium plan nahi, koi limit nahi.</p>
<a class="btn p" href="__BOTLINK__">🚀 Start on Telegram</a><a class="btn s" href="__CHANNEL__">📢 Updates Channel</a></div>
<div class="stats"><div class="st"><b>__USERS__</b><small>Users</small></div><div class="st"><b>__RUNNING__</b><small>Bots running now</small></div><div class="st"><b>__FILES__</b><small>Files hosted</small></div></div>
<section id="features"><h2>Features</h2><div class="g">
<div class="f"><h3>📤 Easy Upload</h3><p>.py aur .zip Python projects seedha Telegram chat se upload karo.</p></div>
<div class="f"><h3>⚙️ Auto Install</h3><p>Zaroori Python packages apne aap install ho jate hain.</p></div>
<div class="f"><h3>▶️ Run &amp; Stop</h3><p>Bot ke buttons se script start, stop aur manage karo.</p></div>
<div class="f"><h3>📁 File Manager</h3><p>Files dekho, search karo, download aur delete karo.</p></div>
<div class="f"><h3>⭐ Favorites</h3><p>Apni important scripts ko favorite mein rakho.</p></div>
<div class="f"><h3>🆓 Totally Free</h3><p>Unlimited uploads, sabke liye same features.</p></div></div></section>
<section id="how"><h2>Kaise use karein</h2>
<div class="step"><div class="num">1</div><div><b>Bot kholo</b><br><span style="color:#9aa7b5">Telegram pe bot open karke /start dabao.</span></div></div>
<div class="step"><div class="num">2</div><div><b>File upload karo</b><br><span style="color:#9aa7b5">Apni .py ya .zip Python project file bhejo.</span></div></div>
<div class="step"><div class="num">3</div><div><b>Run dabao</b><br><span style="color:#9aa7b5">Bot chalu, aur stop bhi kabhi bhi kar sakte ho.</span></div></div></section>
<section id="faq"><h2>FAQ</h2>
<details><summary>Kya ye sach mein free hai?</summary><p>Haan, koi premium plan ya upload limit nahi hai.</p></details>
<details><summary>Kaunsi files chalti hain?</summary><p>Python (.py) aur complete ZIP Python projects.</p></details>
<details><summary>Problem aaye to?</summary><p>Telegram pe owner @Hackerwibes2 se contact karo.</p></details></section>
<section><div class="cta"><h2 style="margin-bottom:8px">Ready to host? 🚀</h2><p style="color:#9aa7b5;margin:0 0 16px">Abhi Telegram pe bot kholo.</p><a class="btn p" href="__BOTLINK__">Open Bot</a></div></section>
<footer>Developed by <b>RG CHEAT</b><br><a href="__YT__">YouTube</a>&bull;<a href="__CHANNEL__">Telegram Channel</a>&bull;<a href="https://t.me/__OWNER__">Contact</a></footer></body></html>"""

async def landing_page(request):
    global _BOT_USERNAME
    if not _BOT_USERNAME:
        try:
            _BOT_USERNAME = (await bot.get_me()).username
        except Exception:
            _BOT_USERNAME = ''
    ch = UPDATE_CHANNEL if UPDATE_CHANNEL.startswith('http') else 'https://t.me/' + UPDATE_CHANNEL.lstrip('@')
    page = (LANDING_HTML.replace('__BOTLINK__', f'https://t.me/{_BOT_USERNAME}' if _BOT_USERNAME else ch)
            .replace('__CHANNEL__', html_lib.escape(ch)).replace('__YT__', html_lib.escape(YOUTUBE_CHANNEL))
            .replace('__OWNER__', html_lib.escape(YOUR_USERNAME.lstrip('@')))
            .replace('__USERS__', str(len(active_users))).replace('__RUNNING__', str(len(_running_list())))
            .replace('__FILES__', str(sum(len(f) for f in user_files.values()))))
    return web.Response(text=page, content_type='text/html')

async def keep_alive():
    """Render free service ko sone se bachane ke liye khud ko ping karta hai"""
    url = os.getenv('RENDER_EXTERNAL_URL')
    if not url:
        return
    await asyncio.sleep(60)
    while True:
        try:
            async with aiohttp.ClientSession() as session:
                async with session.get(url + '/health', timeout=aiohttp.ClientTimeout(total=20)) as r:
                    logger.info(f"Keep-alive ping: {r.status}")
        except Exception as e:
            logger.warning(f"Keep-alive failed: {e}")
        await asyncio.sleep(600)  # har 10 minute

async def web_server():
    app = web.Application()
    
    async def health(request):
        return web.Response(text="ok")
    
    app.router.add_get('/', landing_page)
    app.router.add_get('/health', health)
    app.router.add_get('/admin', admin_page)
    app.router.add_get('/admin/api', panel_api)
    app.router.add_post('/admin/action', panel_action)
    
    runner = web.AppRunner(app)
    await runner.setup()
    port = int(os.getenv('PORT', 5000))
    site = web.TCPSite(runner, '0.0.0.0', port)
    await site.start()
    logger.info(f"🌐 Web server started on port {port}")


# ═══════════════════════════════════════════════════════════════
#  RG CHEAT — STABILITY · AUTO-RESTART · AUTO-START · AUTO-BACKUP
# ═══════════════════════════════════════════════════════════════
MAX_AUTO_RESTARTS = 5            # crash হলে সর্বোচ্চ কতবার auto-restart (backoff সহ)
WATCHDOG_INTERVAL = 15           # সেকেন্ড
MEM_GUARD_PERCENT = 90           # RAM এর বেশি হলে সবচেয়ে ভারী *normal user* বট বন্ধ হবে (admin বট না)
AUTOSTART_STAGGER = 3            # রিস্টোরের সময় এক বট থেকে আরেক বটের মাঝে বিরতি
BACKUP_INTERVAL = 3600           # প্রতি 1 ঘন্টা
BACKUP_KEEP = 3                  # সার্ভারে প্রতি বটের শেষ কতটা ব্যাকআপ রাখবে
BACKUP_SEND_TO_USERS = True      # ইউজারকেও তার নিজের বটের ব্যাকআপ পাঠাবে
BACKUP_FULL_TO_OWNER = True      # Owner/Admin কে একটা FULL ব্যাকআপ (DB + সব বট)
TG_UPLOAD_LIMIT = 49 * 1024 * 1024
BACKUP_DIR = IROTECH_DIR / 'backups'
BACKUP_SKIP_PARTS = {'__pycache__', '.venv', 'venv', 'site-packages', 'backups', '.git', 'node_modules'}

_restarting = set()
_cancelled = set()
_bg_tasks = set()


def _spawn(coro):
    t = asyncio.create_task(coro)
    _bg_tasks.add(t)
    t.add_done_callback(_bg_tasks.discard)
    return t


def _sql(sql, params=(), fetch=False):
    conn = sqlite3.connect(DATABASE_PATH, timeout=20)
    try:
        cur = conn.execute(sql, params)
        rows = cur.fetchall() if fetch else None
        conn.commit()
        return rows
    finally:
        conn.close()


def _ensure_autostart_table():
    _sql('CREATE TABLE IF NOT EXISTS autostart (user_id INTEGER, file_name TEXT, project_type TEXT, '
         'saved_at TEXT, PRIMARY KEY (user_id, file_name))')


def _script_key(user_id, file_name):
    return f"{user_id}_{_project_id(user_id, file_name)}"


def _autostart_save(user_id, file_name, project_type):
    _cancelled.discard(_script_key(user_id, file_name))
    try:
        _sql('INSERT OR REPLACE INTO autostart (user_id, file_name, project_type, saved_at) VALUES (?,?,?,?)',
             (user_id, file_name, project_type, datetime.now().isoformat()))
    except Exception:
        logger.exception('autostart save failed')


def _autostart_remove(user_id, file_name):
    if user_id is None or not file_name:
        return
    _cancelled.add(_script_key(user_id, file_name))
    try:
        _sql('DELETE FROM autostart WHERE user_id=? AND file_name=?', (user_id, file_name))
    except Exception:
        logger.exception('autostart remove failed')


def _child_preexec():
    """Hosted bot: কম priority + RAM কম পড়লে kernel আগে এটাকেই মারবে, মূল Host Bot কে না।"""
    try:
        os.nice(5)
    except Exception:
        pass
    try:
        with open('/proc/self/oom_score_adj', 'w') as f:
            f.write('700')
    except Exception:
        pass


def _read_int(path):
    with open(path) as f:
        return f.read().strip()


def _mem_percent():
    """Container (cgroup) এর আসল RAM ব্যবহার %, না পেলে পুরো সিস্টেমের।"""
    try:
        v2 = os.path.exists('/sys/fs/cgroup/memory.current')
        cur_p = '/sys/fs/cgroup/memory.current' if v2 else '/sys/fs/cgroup/memory/memory.usage_in_bytes'
        lim_p = '/sys/fs/cgroup/memory.max' if v2 else '/sys/fs/cgroup/memory/memory.limit_in_bytes'
        if os.path.exists(cur_p) and os.path.exists(lim_p):
            lim = _read_int(lim_p)
            if lim != 'max' and int(lim) < (1 << 50):
                cur = int(_read_int(cur_p))
                stat_p = '/sys/fs/cgroup/memory.stat' if v2 else '/sys/fs/cgroup/memory/memory.stat'
                cache = 0
                try:
                    for line in open(stat_p):
                        k, _, v = line.partition(' ')
                        if k in ('inactive_file', 'total_inactive_file'):
                            cache = int(v)
                            break
                except Exception:
                    pass
                return max(0.0, (cur - cache) / int(lim) * 100)
    except Exception:
        pass
    return psutil.virtual_memory().percent


def _tree_rss(pid):
    try:
        p = psutil.Process(pid)
        total = p.memory_info().rss
        for c in p.children(recursive=True):
            try:
                total += c.memory_info().rss
            except Exception:
                pass
        return total
    except Exception:
        return 0


def _kill_tree(proc, timeout=6):
    try:
        if proc.poll() is None:
            if os.name == 'nt':
                proc.terminate()
            else:
                try:
                    os.killpg(os.getpgid(proc.pid), signal.SIGTERM)
                except ProcessLookupError:
                    pass
            try:
                proc.wait(timeout=timeout)
            except subprocess.TimeoutExpired:
                if os.name == 'nt':
                    proc.kill()
                else:
                    try:
                        os.killpg(os.getpgid(proc.pid), signal.SIGKILL)
                    except ProcessLookupError:
                        pass
                proc.wait(timeout=3)
    except Exception:
        pass


async def _notify(uid, text):
    try:
        await bot.send_message(uid, text, parse_mode='HTML')
    except Exception:
        pass


async def _notify_admins(text):
    for uid in {OWNER_ID, ADMIN_ID}:
        await _notify(uid, text)


# ── headless start (no button press needed) ─────────────────────
class _SilentMsg:
    def __init__(self, sink):
        self._sink = sink

    async def edit_text(self, text=None, *a, **k):
        if text:
            self._sink['text'] = text
        return self

    async def answer(self, text=None, *a, **k):
        if text:
            self._sink['text'] = text
        return self


class _SilentCallback:
    def __init__(self):
        self.sink = {'text': ''}
        self.message = _SilentMsg(self.sink)

    async def answer(self, *a, **k):
        return None


async def _launch_by_name(user_id, file_name, project_type):
    """একটা বট চালু করে (বাটন ছাড়াই). return (ok, message)."""
    key = _script_key(user_id, file_name)
    cb = _SilentCallback()
    try:
        file_path = UPLOAD_BOTS_DIR / str(user_id) / file_name
        if not file_path.is_file():
            return False, 'Source file not found'
        project_dir = _project_workspace(user_id, file_name)
        if project_type == 'zip':
            if not project_dir.exists() or not any(project_dir.iterdir()):
                if not zipfile.is_zipfile(file_path):
                    return False, 'Invalid ZIP'
                project_dir.mkdir(parents=True, exist_ok=True)
                await asyncio.to_thread(_extract_project_archive, file_path, project_dir)
            entry = _find_project_entry(project_dir)
        else:
            project_dir.mkdir(parents=True, exist_ok=True)
            entry = project_dir / file_name
            if not entry.exists():
                shutil.copy2(file_path, entry)
                user_folder = UPLOAD_BOTS_DIR / str(user_id)
                for item in user_folder.iterdir():
                    if item.is_file() and item.name != file_name and item.suffix.lower() not in ('.py', '.zip', '.log'):
                        try:
                            shutil.copy2(item, project_dir / item.name)
                        except OSError:
                            pass
        await _start_python_process(user_id, file_name, entry, project_dir, project_type, cb)
    except Exception as exc:
        logger.exception('headless launch failed')
        return False, f'{type(exc).__name__}: {exc}'
    info = bot_scripts.get(key)
    ok = bool(info and info['process'].poll() is None)
    return ok, re.sub(r'<[^>]+>', '', cb.sink.get('text', ''))[:600]


# ── auto-start everything that was running (boot / after update / after restore) ──
async def _restore_all_bots(initial=False):
    if initial:
        await asyncio.sleep(8)
    try:
        rows = _sql('SELECT user_id, file_name, project_type FROM autostart', fetch=True) or []
    except Exception:
        logger.exception('autostart read failed')
        return
    if not rows:
        return
    rows.sort(key=lambda r: (r[0] not in admin_ids, r[0]))
    started, failed = 0, []
    logger.info(f"♻️ Auto-starting {len(rows)} saved bots...")
    for uid, name, ptype in rows:
        if uid in banned_users:
            continue
        key = _script_key(uid, name)
        cur = bot_scripts.get(key)
        if cur and cur['process'].poll() is None:
            continue
        for _ in range(12):               # RAM ভরে গেলে একটু অপেক্ষা
            if _mem_percent() < 85:
                break
            await asyncio.sleep(5)
        ok, text = await _launch_by_name(uid, name, ptype or 'py')
        if ok:
            started += 1
        else:
            failed.append((uid, name, text))
            if 'not found' in text:
                try:
                    _sql('DELETE FROM autostart WHERE user_id=? AND file_name=?', (uid, name))
                except Exception:
                    pass
        await asyncio.sleep(AUTOSTART_STAGGER)
    msg = f"♻️ <b>Auto-Start complete</b>\n✅ Started: <b>{started}</b>\n❌ Failed: <b>{len(failed)}</b>"
    for uid, name, text in failed[:10]:
        msg += f"\n• <code>{uid}</code> / <code>{html_lib.escape(name)}</code> — {html_lib.escape(text[:80])}"
    await _notify_admins(msg)


# ── watchdog: crash হলে auto-restart, RAM guard, log trim ───────
async def _auto_restart(key, info):
    uid = info['script_owner_id']
    name = info['file_name']
    ptype = info.get('project_type', 'py')
    _restarting.add(key)
    try:
        for attempt in range(MAX_AUTO_RESTARTS):
            delay = min(5 * 2 ** attempt, 120) + (info.get('extra_delay', 0) if attempt == 0 else 0)
            await asyncio.sleep(delay)
            if key in _cancelled:
                _cancelled.discard(key)
                return
            cur = bot_scripts.get(key)
            if cur is not None and cur is not info and cur['process'].poll() is None:
                return          # ইউজার নিজেই আবার চালু করেছে
            ok, text = await _launch_by_name(uid, name, ptype)
            if ok:
                await _notify(uid, f"🔄 <b>{html_lib.escape(name)}</b> crash করেছিল — auto-restart হয়েছে ✅")
                return
            logger.warning(f"Auto-restart attempt {attempt + 1} failed for {name}: {text}")
        stale = bot_scripts.get(key)
        if stale is not None and stale['process'].poll() is not None:
            h = stale.get('log_file')
            if h and not h.closed:
                h.close()
            bot_scripts.pop(key, None)
        _record_run(uid, name, ptype, 'CRASHED', info['start_time'], datetime.now(), info['process'].returncode, info.get('log_path'))
        await _notify(uid, f"❌ <b>{html_lib.escape(name)}</b> বারবার crash করছে — auto-restart বন্ধ।\n"
                           f"Logs দেখে code ঠিক করে আবার Run করুন।")
        if uid not in admin_ids:
            await _notify_admins(f"⚠️ User <code>{uid}</code> এর <code>{html_lib.escape(name)}</code> বারবার crash করছে।")
    finally:
        _restarting.discard(key)


async def _watchdog_tick(tick):
    pct = _mem_percent()
    if pct >= MEM_GUARD_PERCENT:
        cands = []
        for key, info in list(bot_scripts.items()):
            p = info.get('process')
            if p and p.poll() is None and info.get('script_owner_id') not in admin_ids:
                cands.append((_tree_rss(p.pid), key, info))
        if cands:
            rss, key, info = max(cands, key=lambda x: x[0])
            await asyncio.to_thread(_kill_tree, info['process'])
            info['extra_delay'] = 600
            logger.warning(f"RAM {pct:.0f}% — stopped heaviest user bot {info['file_name']} ({rss // 1048576} MB)")
            await _notify(info['script_owner_id'],
                          f"⚠️ Server RAM full হওয়ায় <b>{html_lib.escape(info['file_name'])}</b> সাময়িক বন্ধ হয়েছে। "
                          f"১০ মিনিট পর auto-start হবে।")

    for key, info in list(bot_scripts.items()):
        p = info.get('process')
        if not p or p.poll() is None or key in _restarting:
            continue
        if p.returncode == 0:      # স্বাভাবিকভাবে শেষ হয়েছে (one-shot script)
            h = info.get('log_file')
            if h and not h.closed:
                h.close()
            _record_run(info['script_owner_id'], info['file_name'], info.get('project_type', 'py'),
                        'FINISHED', info['start_time'], datetime.now(), 0, info.get('log_path'))
            bot_scripts.pop(key, None)
            _autostart_remove(info['script_owner_id'], info['file_name'])
            continue
        _spawn(_auto_restart(key, info))

    if tick % 20 == 0:              # প্রতি ~5 মিনিটে log বেশি বড় হলে ছোট করে
        for info in list(bot_scripts.values()):
            lp = info.get('log_path')
            try:
                if lp and os.path.getsize(lp) > 8 * 1024 * 1024:
                    with open(lp, 'rb') as f:
                        f.seek(-1024 * 1024, 2)
                        tail = f.read()
                    with open(lp, 'r+b') as f:
                        f.truncate(0)
                    with open(lp, 'ab') as f:
                        f.write(b'[LOG TRIMMED]\n' + tail)
            except Exception:
                pass


async def _watchdog_loop():
    tick = 0
    while True:
        await asyncio.sleep(WATCHDOG_INTERVAL)
        tick += 1
        try:
            await _watchdog_tick(tick)
        except Exception:
            logger.exception('watchdog error')


# ── auto-backup (প্রতি ঘন্টায়) ─────────────────────────────────
def _iter_files(root: Path):
    for dirpath, dirnames, filenames in os.walk(root):
        dirnames[:] = [d for d in dirnames if d not in BACKUP_SKIP_PARTS]
        for fn in filenames:
            if fn.lower().endswith(('.log', '.pyc')):
                continue
            p = Path(dirpath) / fn
            if p.is_file() and not p.is_symlink():
                yield p


def _prune(folder: Path, pattern: str, keep: int):
    files = sorted(folder.glob(pattern), key=lambda x: x.stat().st_mtime, reverse=True)
    for old in files[keep:]:
        try:
            old.unlink()
        except Exception:
            pass


def _build_bot_backup(user_id, file_name):
    src = UPLOAD_BOTS_DIR / str(user_id) / file_name
    project_dir = _project_workspace(user_id, file_name)
    if not src.is_file() and not project_dir.is_dir():
        return None
    out_dir = BACKUP_DIR / str(user_id) / _project_id(user_id, file_name)
    out_dir.mkdir(parents=True, exist_ok=True)
    out = out_dir / f"{Path(file_name).stem}_{datetime.now().strftime('%Y%m%d_%H%M%S')}.zip"
    with zipfile.ZipFile(out, 'w', zipfile.ZIP_DEFLATED) as zf:
        if src.is_file():
            zf.write(src, f"upload/{file_name}")
        if project_dir.is_dir():
            for f in _iter_files(project_dir):
                try:
                    zf.write(f, f"project/{f.relative_to(project_dir).as_posix()}")
                except Exception:
                    pass
    _prune(out_dir, '*.zip', BACKUP_KEEP)
    return out


def _build_full_backup():
    BACKUP_DIR.mkdir(parents=True, exist_ok=True)
    out = BACKUP_DIR / f"RG_FULL_BACKUP_{datetime.now().strftime('%Y%m%d_%H%M%S')}.zip"
    tmp_db = BACKUP_DIR / '_db_snapshot.db'
    s = sqlite3.connect(DATABASE_PATH)
    d = sqlite3.connect(tmp_db)
    try:
        s.backup(d)
    finally:
        d.close()
        s.close()
    with zipfile.ZipFile(out, 'w', zipfile.ZIP_DEFLATED) as zf:
        zf.write(tmp_db, 'bot_data.db')
        if UPLOAD_BOTS_DIR.is_dir():
            for f in _iter_files(UPLOAD_BOTS_DIR):
                try:
                    zf.write(f, 'upload_bots/' + f.relative_to(UPLOAD_BOTS_DIR).as_posix())
                except Exception:
                    pass
    try:
        tmp_db.unlink()
    except Exception:
        pass
    _prune(BACKUP_DIR, 'RG_FULL_BACKUP_*.zip', 2)
    return out


async def _send_doc(chat_id, path, caption):
    for _ in range(2):
        try:
            await bot.send_document(chat_id, FSInputFile(path), caption=caption)
            return True
        except TelegramRetryAfter as e:
            await asyncio.sleep(e.retry_after + 1)
        except Exception as e:
            logger.warning(f"backup send to {chat_id} failed: {e}")
            return False
    return False


async def _run_backup_cycle():
    recipients = {OWNER_ID, ADMIN_ID}
    now_txt = datetime.now().strftime('%d %b %Y %H:%M')
    sent = skipped = 0
    if BACKUP_FULL_TO_OWNER:
        try:
            full = await asyncio.to_thread(_build_full_backup)
            if full.stat().st_size <= TG_UPLOAD_LIMIT:
                for r in recipients:
                    if await _send_doc(r, full, f"💾 FULL BACKUP\n🕒 {now_txt}\n\nRestore: এই ZIP ফাইলটা বটে (Admin হিসেবে) আপলোড করুন — সব বট আবার auto-start হবে।"):
                        sent += 1
                    await asyncio.sleep(1.1)
            else:
                skipped += 1
                await _notify_admins("⚠️ Full backup 49MB এর বেশি — Telegram এ পাঠানো যায়নি। সার্ভারে সেভ আছে। Per-bot backup পাঠানো হচ্ছে।")
        except Exception:
            logger.exception('full backup failed')
    for uid, files in list(user_files.items()):
        for file_name, _ftype in list(files):
            try:
                path = await asyncio.to_thread(_build_bot_backup, uid, file_name)
            except Exception:
                logger.exception('bot backup failed')
                continue
            if not path:
                continue
            if path.stat().st_size > TG_UPLOAD_LIMIT:
                skipped += 1
                continue
            info = bot_scripts.get(_script_key(uid, file_name))
            running = bool(info and info['process'].poll() is None)
            caption = (f"💾 Auto Backup\n👤 User: {uid}\n📄 Bot: {file_name}\n"
                       f"{'🟢 Running' if running else '⚪ Stopped'}\n🕒 {now_txt}")
            targets = set(recipients)
            if BACKUP_SEND_TO_USERS and uid not in banned_users:
                targets.add(uid)
            for t in targets:
                if await _send_doc(t, path, caption):
                    sent += 1
                await asyncio.sleep(1.1)
    logger.info(f"💾 Backup cycle done: sent={sent} skipped={skipped}")


async def _backup_loop():
    await asyncio.sleep(300)
    while True:
        try:
            await _run_backup_cycle()
        except Exception:
            logger.exception('backup cycle error')
        await asyncio.sleep(BACKUP_INTERVAL)


async def _restore_full_backup(message: types.Message, document):
    tmp = IROTECH_DIR / 'restore_upload.zip'
    status = await message.answer("♻️ <b>Restoring full backup...</b>", parse_mode="HTML")
    try:
        await bot.download(document, destination=tmp)

        def _do():
            count = 0
            with zipfile.ZipFile(tmp) as zf:
                if 'bot_data.db' not in zf.namelist():
                    raise ValueError('এটা valid RG_FULL_BACKUP ফাইল না (bot_data.db নেই)')
                for item in zf.infolist():
                    if item.is_dir():
                        continue
                    if item.filename == 'bot_data.db':
                        if DATABASE_PATH.exists():
                            shutil.copy2(DATABASE_PATH, str(DATABASE_PATH) + '.bak')
                        with zf.open(item) as s, open(DATABASE_PATH, 'wb') as d:
                            shutil.copyfileobj(s, d)
                    elif item.filename.startswith('upload_bots/'):
                        dest = _safe_child_path(UPLOAD_BOTS_DIR, item.filename[len('upload_bots/'):])
                        dest.parent.mkdir(parents=True, exist_ok=True)
                        with zf.open(item) as s, open(dest, 'wb') as d:
                            shutil.copyfileobj(s, d)
                        count += 1
            return count

        count = await asyncio.to_thread(_do)
        user_subscriptions.clear(); user_files.clear(); user_favorites.clear()
        active_users.clear(); banned_users.clear()
        admin_ids.clear(); admin_ids.update({ADMIN_ID, OWNER_ID})
        init_db(); migrate_db(); _ensure_autostart_table(); load_data()
        n = len(_sql('SELECT 1 FROM autostart', fetch=True) or [])
        await status.edit_text(f"✅ <b>Restore complete</b>\n📁 Files restored: <b>{count}</b>\n"
                               f"🤖 Bots to auto-start: <b>{n}</b>\n\nএকে একে সব বট চালু হচ্ছে...", parse_mode="HTML")
        _spawn(_restore_all_bots())
    except Exception as exc:
        logger.exception('restore failed')
        await status.edit_text(f"❌ Restore failed: {html_lib.escape(str(exc)[:300])}\n\n"
                               f"(Bot API দিয়ে সর্বোচ্চ 20MB ফাইল ডাউনলোড করা যায়)", parse_mode="HTML")
    finally:
        try:
            tmp.unlink(missing_ok=True)
        except Exception:
            pass


@dp.message(Command("backup"))
async def cmd_backup_now(message: types.Message):
    if message.from_user.id not in admin_ids:
        return
    await message.answer("💾 Backup শুরু হচ্ছে... সব বটের ব্যাকআপ আসবে।")
    _spawn(_run_backup_cycle())


@dp.message(Command("startall"))
async def cmd_start_all_bots(message: types.Message):
    if message.from_user.id not in admin_ids:
        return
    await message.answer("♻️ সেভ করা সব বট আবার চালু করা হচ্ছে...")
    _spawn(_restore_all_bots())


async def main():
    logger.info("🚀 Starting Advanced File Host Bot...")
    _ensure_autostart_table()

    _spawn(web_server())
    _spawn(keep_alive())
    _spawn(_watchdog_loop())
    _spawn(_backup_loop())
    _spawn(_restore_all_bots(initial=True))

    while True:      # polling কখনো ক্র্যাশ করলে নিজে আবার চালু হবে
        try:
            await dp.start_polling(bot)
            break
        except Exception:
            logger.exception("Polling crashed — restarting in 5s")
            await asyncio.sleep(5)

if __name__ == "__main__":
    asyncio.run(main())
