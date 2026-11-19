import os
import re
import shutil
import traceback
import threading
import tkinter as tk
from tkinter import ttk, filedialog, scrolledtext, messagebox, colorchooser, simpledialog
import sys
import queue
import json
import random
import colorsys

try:
    from PIL import Image, ImageTk, ImageDraw
    import numpy as np
    PIL_AVAILABLE = True
except ImportError:
    PIL_AVAILABLE = False

# =============================================================================
#  CORE LOGIC
# =============================================================================


# V3MT 2: lossless script utilities. Offsets always refer to the original text.
from pathlib import Path
import tempfile
import hashlib
import math
import uuid

APP_VERSION = "2.4.0"
MOD_DIRECTORIES = (
    "common/country_definitions", "common/history/countries", "common/history/states",
    "common/history/pops", "common/history/population", "common/history/buildings",
    "common/history/military_formations", "common/history/characters",
    "common/history/diplomacy", "common/history/treaties", "common/history/trade",
    "common/history/power_blocs", "common/history/lobbies", "common/history/companies",
    "common/cultures", "common/religions", "common/coat_of_arms/coat_of_arms",
    "common/strategic_regions", "common/journal_entries", "common/static_modifiers",
    "events", "localization/english", "map_data/state_regions"
)


def script_tokens(text):
    """Skip comments; keep escaped strings and all token offsets intact."""
    i = 0
    while i < len(text):
        c = text[i]
        if c.isspace() or c == '\ufeff':
            i += 1
        elif c == '#':
            end = text.find('\n', i)
            i = len(text) if end < 0 else end + 1
        elif c == '"':
            start = i
            i += 1
            while i < len(text):
                if text[i] == '\\':
                    i += 2
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
            else:
                raise ValueError(f'Unclosed string at character {start}')
            yield text[start:i], start, i
        elif text[i:i+2] in ('?=', '>=', '<=', '!=', '=='):
            yield text[i:i+2], i, i+2
            i += 2
        elif c in '{}=<>':
            yield c, i, i+1
            i += 1
        else:
            start = i
            while i < len(text) and not text[i].isspace() and text[i] not in '{}=<>#"':
                if text[i:i+2] in ('?=', '!='): break
                i += 1
            if i == start: i += 1
            yield text[start:i], start, i


def script_blocks(text, key=None, depth=None):
    tokens = list(script_tokens(text))
    stack, result = [], []
    for i, (token, start, end) in enumerate(tokens):
        if token == '{':
            name = tokens[i-2][0] if i >= 2 and tokens[i-1][0] in ('=', '?=') else None
            begin = tokens[i-2][1] if name else start
            stack.append((name, begin, start, len(stack)))
        elif token == '}':
            if not stack: raise ValueError(f'Unexpected closing brace at character {start}')
            name, begin, opening, level = stack.pop()
            if (key is None or name == key) and (depth is None or level == depth):
                result.append(dict(key=name, start=begin, opening=opening, end=end, depth=level))
    if stack: raise ValueError('Unclosed script block')
    return sorted(result, key=lambda b: b['start'])


def script_fields(body):
    """Direct scalar assignments only; never confuse a unit's type with its formation."""
    tokens = list(script_tokens(body))
    level, result = 0, {}
    for i, (token, start, end) in enumerate(tokens):
        if token == '{': level += 1
        elif token == '}': level -= 1
        elif level == 0 and i+2 < len(tokens) and tokens[i+1][0] in ('=', '?='):
            value, a, b = tokens[i+2]
            if value != '{': result[token] = (value, start, b)
    return result


def field(body, key, default=''):
    value = script_fields(body).get(key, (default, 0, 0))[0]
    return value[1:-1].replace('\\"', '"').replace('\\\\', '\\') if value.startswith('"') else value


def put_field(body, key, value):
    entry = script_fields(body).get(key)
    line = key + ' = ' + str(value)
    return body[:entry[1]] + line + body[entry[2]:] if entry else body.rstrip() + '\n    ' + line + '\n'


def quoted(value):
    return '"' + str(value).replace('\\', '\\\\').replace('"', '\\"').replace('\r', '').replace('\n', '\\n') + '"'


def identifier(value, label='Identifier'):
    value = str(value).strip()
    if not re.fullmatch(r'[A-Za-z_][A-Za-z0-9_]*', value):
        raise ValueError(f'{label} must contain letters, digits and underscores, and start with a letter or underscore.')
    return value


def nonnegative(value, label='Count'):
    if isinstance(value, bool) or not re.fullmatch(r'\d+', str(value).strip()):
        raise ValueError(f'{label} must be a non-negative integer.')
    return int(value)


def atomic_text(path, text, localization=False):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    if path.suffix == '.txt': script_blocks(text)
    fd, temporary = tempfile.mkstemp(prefix='.' + path.name, suffix='.tmp', dir=path.parent)
    try:
        with os.fdopen(fd, 'w', encoding='utf-8-sig' if localization else 'utf-8', newline='\n') as handle:
            handle.write(text)
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temporary, path)
    finally:
        if os.path.exists(temporary): os.unlink(temporary)


def apportion(total, weights):
    """Largest remainders: deterministic integer counts that add to the requested total."""
    total = nonnegative(total, 'Total')
    if not weights or sum(weights) <= 0:
        if total: raise ValueError('Cannot distribute a positive total across zero population.')
        return [0] * len(weights)
    if any(w < 0 or not math.isfinite(w) for w in weights): raise ValueError('Invalid weights')
    values = [total*w/sum(weights) for w in weights]
    result = [math.floor(v) for v in values]
    for i in sorted(range(len(weights)), key=lambda i: (-(values[i]-result[i]), i))[:total-sum(result)]:
        result[i] += 1
    return result



import functools
import inspect


def mod_operation(function):
    """Serialize edits; rollback text changes if validation or an operation fails."""
    signature=inspect.signature(function)
    @functools.wraps(function)
    def run(self,*args,**kwargs):
        logic=self if isinstance(self,Vic3Logic) else self.logic
        logic._require_mod()
        bound=signature.bind(self,*args,**kwargs); bound.apply_defaults()
        for name,value in bound.arguments.items():
            if value is None or value=='': continue
            if name in {'tag','new_tag','old_tag','target_tag','source_tag','land_owner_tag','building_owner_tag','region_tag','owner_tag','donor_tag'}:
                identifier(logic.format_tag_clean(value),'Country tag')
            elif name in {'key','je_id','namespace','mod_name','building_type','new_culture','new_religion'} and isinstance(value,str): identifier(value,name)
            elif name in {'new_total','new_size','total_pop','new_level','level'}: nonnegative(value,name)
        if function.__name__=='save_event':
            if not re.fullmatch(re.escape(bound.arguments['namespace'])+r'\.\d+',bound.arguments['event_id']): raise ValueError('Event ID must be namespace.number, matching the namespace.')
            if not bound.arguments['options']: raise ValueError('Add at least one event option.')
        if function.__name__ in {'set_relations','add_diplomatic_pact'}:
            if logic.format_tag_clean(bound.arguments['tag'])==logic.format_tag_clean(bound.arguments['target']): raise ValueError('Choose two different countries.')
        if function.__name__=='set_relations' and not -100<=int(bound.arguments['value'])<=100: raise ValueError('Relations must be between -100 and 100.')
        if not hasattr(logic,'_operation_lock'): logic._operation_lock=threading.RLock()
        with logic._operation_lock:
            if getattr(logic,'_operation_depth',0): return function(self,*args,**kwargs)
            root=Path(logic.mod_path)
            def files(): return {p for p in root.rglob('*') if p.is_file() and p.suffix.lower() in {'.txt','.yml','.json'} and not p.is_symlink()}
            before={p:p.read_bytes() for p in files()}
            logic._operation_depth=1; logic._backup_done=False
            original_log=logic.log; errors=[]
            def record(message,level='info'):
                if level=='error': errors.append(str(message))
                original_log(message,level)
            logic.log=record
            try:
                logic.perform_auto_backup()
                result=function(self,*args,**kwargs)
                if errors: raise ValueError('\n'.join(errors))
                for path in files():
                    raw=path.read_bytes()
                    if before.get(path)==raw: continue
                    text=raw.decode('utf-8-sig')
                    if path.suffix=='.txt': script_blocks(text)
                    elif path.suffix=='.json': json.loads(text)
                    elif path.suffix=='.yml':
                        if not raw.startswith(b'\xef\xbb\xbf'): raise ValueError(f'{path.name}: localization needs UTF-8 BOM.')
                        for line in text.splitlines():
                            if re.match(r'^\s+[^\s:]+:\d*\s',line):
                                value=re.split(r':\d*\s*',line,maxsplit=1)[1]
                                tokens=list(script_tokens(value))
                                if len(tokens)!=1 or not tokens[0][0].startswith('"'): raise ValueError(f'{path.name}: malformed localization value.')
                return result
            except Exception:
                for path in files()-before.keys(): path.unlink()
                for path,raw in before.items():
                    if not path.exists() or path.read_bytes()!=raw:
                        path.parent.mkdir(parents=True,exist_ok=True); path.write_bytes(raw)
                logic.state_manager.load_state_regions()
                original_log('Edit failed; text files were restored to their previous contents.','warn')
                raise
            finally:
                logic.log=original_log; logic._operation_depth=0; logic._backup_done=False
    return run

def culture_suggestions(combo, choices, accept):
    """Show prefix matches while keeping keyboard focus in the editable field."""
    popup = None
    def close(event=None):
        nonlocal popup
        if popup is not None:
            popup.destroy()
            popup = None
    def update(event):
        if event.keysym in ('Down','Up','Return','Escape','Tab','Shift_L','Shift_R'):
            return
        close()
        prefix = combo.get().strip().casefold()
        matches = [v for v in choices if v.casefold().startswith(prefix)]
        combo.configure(values=matches)
        if not prefix or not matches:
            return
        nonlocal popup
        popup = tk.Toplevel(combo)
        popup.overrideredirect(True)
        popup.transient(combo.winfo_toplevel())
        popup.geometry(f"{combo.winfo_width()}x{min(7,len(matches))*24}+{combo.winfo_rootx()}+{combo.winfo_rooty()+combo.winfo_height()}")
        listing = tk.Listbox(popup, exportselection=False, bg='#473a2b', fg='#f3e7ce')
        listing.pack(fill='both',expand=True)
        for value in matches:
            listing.insert('end',value)
        def choose(click):
            combo.set(matches[listing.nearest(click.y)])
            close()
            accept(None)
        listing.bind('<ButtonPress-1>',choose)
    combo.bind('<KeyRelease>',update)
    combo.bind('<FocusOut>',close,add='+')
    combo.bind('<Escape>',close,add='+')
    combo.bind('<Down>',close,add='+')
    combo.bind('<ButtonPress-1>',close,add='+')

class Vic3Logic:
    def effective_files(self, relative):
        """Same relative mod filename shadows vanilla, then files load in sorted order."""
        paths = {}
        roots = ([Path(self.vanilla_path)/'game'] if self.vanilla_path else []) + ([Path(self.mod_path)] if self.mod_path else [])
        for root in roots:
            folder = root / relative
            if folder.is_dir():
                for path in sorted(folder.rglob('*.txt')):
                    paths[path.relative_to(folder).as_posix()] = path
        return [paths[k] for k in sorted(paths)]

    def definition_keys(self, relative):
        result = set()
        for path in self.effective_files(relative):
            result.update(b['key'] for b in script_blocks(path.read_text(encoding='utf-8-sig'), depth=0) if b['key'])
        return sorted(result)

    def _require_mod(self):
        if not self.mod_path or not Path(self.mod_path).is_dir(): raise ValueError('Select a mod folder first.')

    @mod_operation
    def _write_formation(self, tag, name, state, units, fleet=False):
        self._require_mod()
        tag = identifier(self.format_tag_clean(tag), 'Country tag')
        if not name.strip(): raise ValueError('A formation name is required.')
        units = {identifier(k): nonnegative(v) for k,v in units.items()}
        if not sum(units.values()): raise ValueError('Add at least one unit or ship.')
        final_state, region = self._get_location_data(tag, state)
        if not final_state: raise ValueError('Could not resolve a valid state and strategic region.')
        database = 'common/ship_types' if fleet else 'common/combat_unit_types'
        known = self.definition_keys(database)
        if not known: raise ValueError(f'Load current game files first: {database} is unavailable.')
        for key, count in units.items():
            if count and key not in known: raise ValueError(f'{key} is absent from the selected game/mod definitions.')
        kind = 'fleet' if fleet else 'army'
        uid = uuid.uuid4().hex[:12]
        lines = []
        for key, count in units.items():
            if not count: continue
            if fleet:
                lines.append(f'            ship = {{ type = ship_type:{key} count = {count} }}')
            else:
                lines.append(f'            combat_unit = {{ type = unit_type:{key} state_region = s:{final_state} count = {count} }}')
        text = ('MILITARY_FORMATIONS = {\n    c:'+tag+' ?= {\n        create_military_formation = {\n'
                +f'            name = {quoted(name)}\n            type = {kind}\n            hq_region = {region}\n'
                +f'            save_scope_as = v3mt_{kind}_{tag.lower()}_{uid}\n'+'\n'.join(lines)+'\n        }\n    }\n}\n')
        self.perform_auto_backup()
        path = Path(self.mod_path)/'common/history/military_formations'/f'99_v3mt_{kind}_{tag.lower()}_{uid}.txt'
        atomic_text(path, text)
        self.log(f'[SUCCESS] Created {kind}: {name}', 'success')
        return str(path)

    def _formation_snapshot(self, data):
        path = Path(data['file']).resolve()
        if not path.is_relative_to(Path(self.mod_path).resolve()): raise ValueError('Only mod files can be edited.')
        content = path.read_text(encoding='utf-8-sig')
        if hashlib.sha256(content.encode()).hexdigest() != data['fingerprint']:
            raise ValueError('This file changed since loading. Reload formations before editing.')
        return path, content

    def _localize(self, filename, entries):
        path=Path(self.mod_path)/'localization/english'/f'{filename}_l_english.yml'
        text=path.read_text(encoding='utf-8-sig') if path.exists() else 'l_english:\n'
        for key,value in entries.items():
            line=f' {key}:0 {quoted(value)}'
            pattern=r'^\s*'+re.escape(key)+r':[^\n]*$'
            if re.search(pattern,text,re.M): text=re.sub(pattern,lambda m:line,text,flags=re.M)
            else: text=text.rstrip()+'\n'+line+'\n'
        atomic_text(path,text,localization=True)

    def validate_mod(self):
        self._require_mod()
        issues=[]
        root=Path(self.mod_path)
        def add(level,path,message): issues.append(dict(level=level,file=str(path.relative_to(root)),message=message))
        metadata=root/'.metadata/metadata.json'
        try:
            meta=json.loads(metadata.read_text(encoding='utf-8-sig'))
            if not meta.get('name'): add('error',metadata,'Missing mod name.')
            if not meta.get('supported_game_version'): add('warn',metadata,'Supported game version is unspecified.')
        except (OSError,ValueError) as exc: add('error',metadata,f'Metadata cannot be read: {exc}')
        if (root/'game').exists(): add('error',root/'game','Mod contents belong at the root, without a game/ wrapper.')
        if (root/'map/data').exists(): add('error',root/'map/data','Use map_data/ for Victoria 3 map files.')
        wrappers={'states':'STATES','countries':'COUNTRIES','pops':'POPS','population':'POPULATION','buildings':'BUILDINGS','military_formations':'MILITARY_FORMATIONS','diplomacy':'DIPLOMACY','power_blocs':'POWER_BLOCS'}
        known_ships=set(self.definition_keys('common/ship_types'))
        known_regions=set(self.definition_keys('common/strategic_regions'))
        for path in sorted(root.rglob('*.txt')):
            rel=path.relative_to(root)
            if rel.parts[0] not in ('common','events','map_data'): continue
            try:
                text=path.read_text(encoding='utf-8-sig'); blocks=script_blocks(text)
            except (OSError,ValueError) as exc:
                add('error',path,str(exc)); continue
            if len(rel.parts)>3 and rel.parts[:2]==('common','history') and rel.parts[2] in wrappers:
                expected=wrappers[rel.parts[2]]
                has_wrapper = any(b['key'] == expected and b['depth'] == 0 for b in blocks)
                if not has_wrapper and next(script_tokens(text), None) is not None:
                    # Some shipped auxiliary files use a different top-level structure.
                    original = Path(self.vanilla_path) / 'game' / rel if self.vanilla_path else None
                    try:
                        unchanged = original is not None and original.read_text(encoding='utf-8-sig') == text
                    except (OSError, UnicodeError):
                        unchanged = False
                    if not unchanged:
                        add('error', path, f'Missing {expected} history wrapper.')
            for b in blocks:
                body=text[b['opening']+1:b['end']-1]
                if b['key']=='create_military_formation':
                    typ=field(body,'type'); hq=field(body,'hq_region').removeprefix('sr:')
                    if known_regions and hq not in known_regions: add('error',path,f'Unknown HQ: {hq}')
                    if typ=='fleet' and script_blocks(body,'combat_unit',0): add('error',path,'Legacy naval combat_unit entries: migrate manually to 1.13 ship entries.')
                    for unit in script_blocks(body,'ship',0):
                        key=field(body[unit['opening']+1:unit['end']-1],'type').removeprefix('ship_type:')
                        if known_ships and key not in known_ships: add('error',path,f'Unknown ship type: {key}')
                if b['key']=='create_power_bloc' and not field(body,'principle'): add('error',path,'Power bloc is missing a primary principle.')
            # Check retired identifiers as tokens, not comments or localization strings.
            deprecated={'has_role','is_ruler','is_heir','should_be_pinned_by_default'}
            for token,_,_ in script_tokens(text):
                if token in deprecated: add('warn',path,f'Review pre-1.13 field: {token}')
        ids,provinces={},{}
        for path in self.effective_files('map_data/state_regions'):
            text=path.read_text(encoding='utf-8-sig')
            for b in script_blocks(text,depth=0):
                if not b['key'] or not b['key'].startswith('STATE_'): continue
                body=text[b['opening']+1:b['end']-1]; number=field(body,'id')
                if number in ids and ids[number]!=b['key']: issues.append(dict(level='error',file=str(path),message=f'Duplicate state ID {number}: {ids[number]}, {b["key"]}'))
                ids[number]=b['key']
                for pb in script_blocks(body,'provinces',0):
                    for value,_,_ in script_tokens(body[pb['opening']+1:pb['end']-1]):
                        value=value.strip('"').lower()
                        if value in provinces and provinces[value]!=b['key']: issues.append(dict(level='error',file=str(path),message=f'Province {value} belongs to multiple states.'))
                        provinces[value]=b['key']
        for path in sorted((root/'localization').rglob('*.yml')) if (root/'localization').exists() else []:
            raw=path.read_bytes()
            if not raw.startswith(b'\xef\xbb\xbf'): add('error',path,'Localization must be UTF-8 with BOM.')
            text=raw.decode('utf-8-sig')
            if not re.search(r'^l_[a-z_]+:\s*$',text,re.M): add('error',path,'Missing language header.')
            if not re.search(r'_l_[a-z_]+\.yml$',path.name): add('error',path,'Filename needs _l_<language>.yml suffix.')
            seen=set()
            for match in re.finditer(r'^\s+([^\s:]+):',text,re.M):
                if match[1] in seen: add('warn',path,f'Duplicate localization key: {match[1]}')
                seen.add(match[1])
        return issues

    def _editable_copy(self, source):
        self._require_mod(); source=Path(source).resolve(); mod=Path(self.mod_path).resolve()
        if source.is_relative_to(mod): return source
        game=(Path(self.vanilla_path)/'game').resolve() if self.vanilla_path else None
        if not game or not source.is_relative_to(game): raise ValueError('File is outside the game and mod folders.')
        target=mod/source.relative_to(game)
        if not target.exists():
            target.parent.mkdir(parents=True,exist_ok=True); shutil.copy2(source,target)
        return target

    CAT_A_STATE = ["building_government_administration", "building_construction_sector", "building_university", "building_barrack", "building_port", "building_conscription_center", "building_naval_base", "building_naval_administration"]
    CAT_B_RURAL = ["building_wheat_farm", "building_rye_farm", "building_rice_farm", "building_maize_farm", "building_millet_farm", "building_livestock_ranch", "building_logging_camp", "building_rubber_plantation", "building_cotton_plantation", "building_coffee_plantation", "building_tea_plantation", "building_tobacco_plantation", "building_sugar_plantation", "building_vineyard", "building_fruit_plantation", "building_silk_plantation", "building_dye_plantation", "building_opium_plantation", "building_fishing_wharf", "building_whaling_station"]

    def __init__(self, log_callback):
        self.log = log_callback
        self.mod_path = ""
        self.vanilla_path = ""
        self.auto_backup_enabled = True
        self.stop_event = threading.Event()
        self.state_manager = StateManager(self)

    def set_mod_path(self, path):
        target = Path(path).expanduser().resolve()
        if not target.is_dir(): raise ValueError('Select an existing mod folder.')
        if (target / 'binaries').is_dir() or (target / 'launcher').is_dir() or (target / 'game' / 'common').is_dir():
            raise ValueError('This is a game installation, not a mod folder.')
        if self.vanilla_path and target.is_relative_to(Path(self.vanilla_path).resolve()):
            raise ValueError('The mod folder must be outside the game installation.')
        self.mod_path = str(target)
        self.state_manager.load_state_regions()

    def set_vanilla_path(self, path):
        selected = Path(path).expanduser().resolve()
        game = selected / 'game' if (selected / 'game' / 'common').is_dir() else selected
        if not (game / 'common').is_dir(): raise ValueError('Select the Victoria 3 installation or its game folder.')
        if self.mod_path and Path(self.mod_path).resolve().is_relative_to(game):
            raise ValueError('The mod folder must be outside the game installation.')
        # Existing readers consistently append game/; retain this internal convention.
        if game.name != 'game': raise ValueError('The selected game data folder must be named game.')
        self.vanilla_path = str(game.parent)
        self.state_manager.load_state_regions()

    def safe_str(self, s):
        return quoted(s or '')[1:-1]

    def format_tag_clean(self, user_input):
        cleaned = user_input.strip()
        if cleaned.lower().startswith("c:"):
            cleaned = cleaned[2:]
        return cleaned.upper()

    def format_state_clean(self, user_input):
        return self.normalize_state_key(user_input)

    def normalize_state_key(self, state_name):
        """Standardizes state names to STATE_NAME format (strips quotes, s: prefix, adds STATE_)."""
        clean = state_name.strip()
        # Remove quotes
        clean = clean.replace('"', '')
        # Remove s: prefix if present (case insensitive)
        if clean.lower().startswith("s:"):
            clean = clean[2:]

        clean = clean.upper().strip()
        clean = clean.replace(" ", "_")
        if not clean: return ""
        if not clean.startswith("STATE_"):
            clean = f"STATE_{clean}"
        return clean

    # --- TAG VALIDATION & CREATION ---
    def tag_exists(self, tag):
        return self.format_tag_clean(tag) in self.definition_keys('common/country_definitions')

    def scan_all_country_colors(self):
        """Scans both mod and vanilla for country colors. Returns {tag: (r,g,b)}."""
        colors = {}
        paths = []
        if self.mod_path: paths.append(os.path.join(self.mod_path, "common/country_definitions"))
        if self.vanilla_path: paths.append(os.path.join(self.vanilla_path, "game/common/country_definitions"))

        for p in paths:
            if not os.path.exists(p): continue
            for root, _, files in os.walk(p):
                for file in files:
                    if not file.endswith(".txt"): continue
                    try:
                        with open(os.path.join(root, file), 'r', encoding='utf-8-sig') as f: content = f.read()
                    except:
                        with open(os.path.join(root, file), 'r', encoding='utf-8') as f: content = f.read()

                    # Find tags and colors
                    # c:TAG = { ... color = { r g b } ... }
                    cursor = 0
                    while True:
                        # Find tag definition start
                        # Matches start of line or space + TAG + space + =
                        # But more reliably: TAG = {
                        # Standard paradox syntax: TAG = { ... }
                        m = re.search(r"(?:^|\s)([A-Za-z0-9_]{3,})\s*=\s*\{", content[cursor:])
                        if not m: break
                        tag = m.group(1).upper()
                        if tag in ["AGENTS", "TIERS", "TYPES", "CULTURES", "RELIGIONS"]: # Skip non-country blocks if any
                             cursor += m.end()
                             continue

                        start_idx = cursor + m.end() - 1
                        _, end_idx = self.find_block_content(content, start_idx)

                        if end_idx:
                            block = content[start_idx:end_idx]
                            # Look for color
                            # color = { r g b } or color = rgb { r g b } or color = hsv { ... } or color = hsv360 { ... }
                            c_match = re.search(r"color\s*=\s*(hsv360|hsv|rgb)?\s*\{\s*([0-9.]+)\s+([0-9.]+)\s+([0-9.]+)\s*\}", block, re.IGNORECASE)
                            if c_match:
                                c_type = c_match.group(1)
                                v1, v2, v3 = float(c_match.group(2)), float(c_match.group(3)), float(c_match.group(4))
                                rgb = (0,0,0)
                                if c_type and c_type.lower() == 'hsv360':
                                    h = v1 / 360.0
                                    s = v2 / 100.0
                                    v = v3 / 100.0
                                    r, g, b = colorsys.hsv_to_rgb(h, s, v)
                                    rgb = (int(r * 255), int(g * 255), int(b * 255))
                                elif c_type and c_type.lower() == 'hsv':
                                    h = v1 if v1 <= 1.0 else v1/360.0
                                    s = v2 if v2 <= 1.0 else v2/100.0
                                    v = v3 if v3 <= 1.0 else v3/100.0
                                    r, g, b = colorsys.hsv_to_rgb(h, s, v)
                                    rgb = (int(r * 255), int(g * 255), int(b * 255))
                                else:
                                    # rgb 0-255 or 0-1
                                    if v1 <= 1.0 and v2 <= 1.0 and v3 <= 1.0 and (v1 > 0 or v2 > 0 or v3 > 0):
                                         rgb = (int(v1*255), int(v2*255), int(v3*255))
                                    else:
                                         rgb = (int(v1), int(v2), int(v3))

                                # Mod overrides vanilla
                                if tag not in colors or p.startswith(self.mod_path):
                                    colors[tag] = rgb

                            cursor = end_idx
                        else:
                            cursor += m.end()
        return colors

    def scan_definitions_for_options(self):
        tiers,types=set(),set()
        for path in self.effective_files('common/country_definitions'):
            text=path.read_text(encoding='utf-8-sig')
            for b in script_blocks(text,depth=0):
                body=text[b['opening']+1:b['end']-1]
                if field(body,'tier'): tiers.add(field(body,'tier'))
                if field(body,'country_type'): types.add(field(body,'country_type'))
        return self.definition_keys('common/cultures'),self.definition_keys('common/religions'),sorted(tiers),sorted(types)

    def get_country_data(self, tag):
        data=dict(cultures=None,religion=None,capital=None)
        for path in self.effective_files('common/country_definitions'):
            text=path.read_text(encoding='utf-8-sig')
            for b in script_blocks(text,self.format_tag_clean(tag),0):
                body=text[b['opening']+1:b['end']-1]
                cultures=[t.strip('"') for cb in script_blocks(body,'cultures',0) for t,_,_ in script_tokens(body[cb['opening']+1:cb['end']-1])]
                data=dict(cultures=' '.join(cultures),religion=field(body,'religion') or None,capital=field(body,'capital') or None)
        return data

    def get_capital_hq(self, tag):
        """Finds the Strategic Region of a country's capital state."""
        data = self.get_country_data(tag)
        capital_state = data.get("capital")
        if not capital_state: return None

        # Ensure state key format
        if not capital_state.startswith("s:"):
            # Capital might be returned as "STATE_X" or "X"
            if not capital_state.startswith("STATE_"):
                capital_state = f"STATE_{capital_state}"
            capital_state = f"s:{capital_state}"

        return self.find_strategic_region(capital_state)

    def get_religion_by_culture(self, culture):
        """Scans common/cultures to find the default religion for a given culture."""
        cult_dir = os.path.join(self.mod_path, "common/cultures")
        if not os.path.exists(cult_dir): return None

        # Matches: start of line or whitespace + culture + whitespace + = + whitespace + {
        pat = re.compile(r"(?:^|\s)" + re.escape(culture) + r"\s*=\s*\{", re.MULTILINE)

        for root, _, files in os.walk(cult_dir):
            for file in files:
                if not file.endswith(".txt"): continue
                try:
                    with open(os.path.join(root, file), 'r', encoding='utf-8-sig') as f: content = f.read()
                except:
                    with open(os.path.join(root, file), 'r', encoding='utf-8') as f: content = f.read()

                match = pat.search(content)
                if match:
                    # Found start of culture block. Find the block content.
                    start_brace = match.end() - 1
                    _, end_brace = self.find_block_content(content, start_brace)
                    
                    if end_brace:
                        block = content[start_brace:end_brace]
                        rel_match = re.search(r"religion\s*=\s*([A-Za-z0-9_]+)", block)
                        if rel_match:
                            return rel_match.group(1).strip()
        return None

    def get_tech_tier_from_history(self, tag):
        """Scans history/countries for tech tier."""
        hist_dir = os.path.join(self.mod_path, "common/history/countries")
        if not os.path.exists(hist_dir): return None

        clean_tag = tag.replace("c:", "").strip()

        for root, _, files in os.walk(hist_dir):
            for file in files:
                if not file.endswith(".txt"): continue
                path = os.path.join(root, file)
                try:
                    with open(path, 'r', encoding='utf-8-sig') as f: content = f.read()
                except:
                    with open(path, 'r', encoding='utf-8') as f: content = f.read()

                # Check for country block c:TAG
                if re.search(r"c:" + re.escape(clean_tag) + r"\b", content):
                     match = re.search(r"effect_starting_technology_tier_\d+_tech\s*=\s*yes", content)
                     if match:
                         return match.group(0)
        return None

    def get_pop_history_data(self, tag):
        """Scans history/population for wealth and literacy effects."""
        pop_dir = os.path.join(self.mod_path, "common/history/population")
        if not os.path.exists(pop_dir): return None

        clean_tag = tag.replace("c:", "").strip()
        effects = []

        for root, _, files in os.walk(pop_dir):
            for file in files:
                if not file.endswith(".txt"): continue

                path = os.path.join(root, file)
                try:
                    with open(path, 'r', encoding='utf-8-sig') as f: content = f.read()
                except:
                    with open(path, 'r', encoding='utf-8') as f: content = f.read()

                current_idx = 0
                while True:
                    c_start, c_end = self.get_block_range_safe(content, f"c:{clean_tag}", current_idx)
                    if c_start is None: break

                    block = content[c_start:c_end]
                    wealth = re.search(r"effect_starting_pop_wealth_[a-z_]+\s*=\s*yes", block)
                    if wealth and wealth.group(0) not in effects: effects.append(wealth.group(0))

                    literacy = re.search(r"effect_starting_pop_literacy_[a-z_]+\s*=\s*yes", block)
                    if literacy and literacy.group(0) not in effects: effects.append(literacy.group(0))

                    current_idx = c_end

        if effects:
            return "\n\t\t".join(effects)
        return None

    def get_pop_history_settings(self, tag):
        """Scans history/population for wealth and literacy settings dictionary."""
        clean_tag = tag.replace("c:", "").strip()
        settings = {"wealth": "", "literacy": ""}

        paths = []
        if self.mod_path: paths.append(os.path.join(self.mod_path, "common/history/population"))
        if self.vanilla_path: paths.append(os.path.join(self.vanilla_path, "game/common/history/population"))

        for p in paths:
             if not os.path.exists(p): continue
             for root, _, files in os.walk(p):
                for file in files:
                    if not file.endswith(".txt"): continue
                    path = os.path.join(root, file)
                    try:
                        with open(path, 'r', encoding='utf-8-sig') as f: content = f.read()
                    except:
                        with open(path, 'r', encoding='utf-8') as f: content = f.read()

                    current_idx = 0
                    while True:
                        s, e = self.get_block_range_safe(content, f"c:{clean_tag}", current_idx)
                        if s is None: break

                        block = content[s:e]

                        w_match = re.search(r"(effect_starting_pop_wealth_[a-z_]+)\s*=\s*yes", block)
                        if w_match: settings["wealth"] = w_match.group(1)

                        l_match = re.search(r"(effect_starting_pop_literacy_[a-z_]+)\s*=\s*yes", block)
                        if l_match: settings["literacy"] = l_match.group(1)

                        current_idx = e

        return settings

    @mod_operation
    def save_pop_history_settings(self, tag, wealth, literacy):
        self.perform_auto_backup()
        clean_tag = tag.replace("c:", "").strip()
        pop_dir = os.path.join(self.mod_path, "common/history/population")
        os.makedirs(pop_dir, exist_ok=True)

        target_file = None
        target_content = None

        # 1. Find existing file in mod
        for root, _, files in os.walk(pop_dir):
            for file in files:
                if not file.endswith(".txt"): continue
                path = os.path.join(root, file)
                try:
                    with open(path, 'r', encoding='utf-8-sig') as f: c = f.read()
                except:
                    with open(path, 'r', encoding='utf-8') as f: c = f.read()

                if re.search(r"c:" + re.escape(clean_tag) + r"\b", c):
                    target_file = path
                    target_content = c
                    break
            if target_file: break

        # 2. If not found, create new file
        if not target_file:
            # Check if name is known for cleaner filename
            # But prompt says: "find the file named 'tur - ottoman empire.txt' ... If the tag doesnt have a file ... simply create one"
            # We will name it "tag.txt" or try to find name
            target_file = os.path.join(pop_dir, f"{clean_tag}.txt")
            target_content = f"POPULATION = {{\n\tc:{clean_tag} ?= {{\n\t}}\n}}"
            if os.path.exists(target_file):
                 with open(target_file, 'r', encoding='utf-8-sig') as f: target_content = f.read()

        # 3. Edit content
        s, e = self.get_block_range_safe(target_content, f"c:{clean_tag}")
        if s is not None:
            block = target_content[s:e]

            # Remove existing lines
            block = re.sub(r"\s*effect_starting_pop_wealth_[a-z_]+\s*=\s*yes", "", block)
            block = re.sub(r"\s*effect_starting_pop_literacy_[a-z_]+\s*=\s*yes", "", block)

            # Add new
            additions = ""
            if wealth: additions += f"\n\t\t{wealth} = yes"
            if literacy: additions += f"\n\t\t{literacy} = yes"

            # Insert
            last_brace = block.rfind('}')
            new_block = block[:last_brace] + additions + "\n\t}"

            target_content = target_content[:s] + new_block + target_content[e:]

            with open(target_file, 'w', encoding='utf-8-sig') as f: f.write(target_content)
            self.log(f"[SAVE] Pop settings saved to {os.path.basename(target_file)}", 'success')

    def get_extended_history_data(self, tag):
        """Scans history/countries for extended data (tech, laws, politics, institutions)."""
        hist_dir = os.path.join(self.mod_path, "common/history/countries")
        if not os.path.exists(hist_dir): return None

        clean_tag = tag.replace("c:", "").strip()
        data = {
            "tech_tier": [],
            "techs_researched": [],
            "politics": [],
            "laws": [],
            "institutions": []
        }

        found_any = False

        # Optimization: Prioritize file named "TAG - ..." or "TAG.txt"
        target_files = []
        all_files_map = {} # path -> filename

        for root, _, files in os.walk(hist_dir):
            for file in files:
                if not file.endswith(".txt"): continue
                fpath = os.path.join(root, file)
                all_files_map[fpath] = file

                # Check for "TAG - *" or "TAG.txt" (case insensitive)
                # This ensures we look for the specific file first
                fname_lower = file.lower()
                tag_lower = clean_tag.lower()

                if fname_lower.startswith(f"{tag_lower} -") or fname_lower == f"{tag_lower}.txt":
                    target_files.append(fpath)

        # If specific files found, scan ONLY those. Otherwise scan ALL.
        files_to_scan = target_files if target_files else list(all_files_map.keys())

        for path in files_to_scan:
            try:
                with open(path, 'r', encoding='utf-8-sig') as f: content = f.read()
            except:
                with open(path, 'r', encoding='utf-8') as f: content = f.read()

            current_idx = 0
            while True:
                c_start, c_end = self.get_block_range_safe(content, f"c:{clean_tag}", current_idx)
                if c_start is None: break
                found_any = True

                sb, _ = self.find_block_content(content, c_start)
                if sb is not None:
                    block_inner = content[sb+1 : c_end-1]

                    data["tech_tier"].extend(re.findall(r"effect_starting_technology_tier_\d+_tech\s*=\s*yes", block_inner))
                    data["politics"].extend(re.findall(r"effect_starting_politics_[a-z_]+\s*=\s*yes", block_inner))
                    data["techs_researched"].extend(re.findall(r"add_technology_researched\s*=\s*[a-zA-Z0-9_]+", block_inner))
                    data["laws"].extend([l.strip() for l in re.findall(r"^\s*(activate_law\s*=\s*.*)$", block_inner, re.MULTILINE)])

                    inst_pattern = re.compile(r"(set_institution_[a-zA-Z0-9_]+)\s*=\s*", re.MULTILINE)
                    cursor = 0
                    while True:
                        match = inst_pattern.search(block_inner, cursor)
                        if not match: break

                        next_char_idx = match.end()
                        while next_char_idx < len(block_inner) and block_inner[next_char_idx].isspace():
                            next_char_idx += 1

                        if next_char_idx < len(block_inner) and block_inner[next_char_idx] == '{':
                            b_start, b_end = self.find_block_content(block_inner, next_char_idx)
                            if b_start is not None:
                                data["institutions"].append(block_inner[match.start():b_end].strip())
                                cursor = b_end
                            else:
                                cursor = match.end()
                        else:
                            line_end = block_inner.find('\n', match.end())
                            if line_end == -1: line_end = len(block_inner)
                            data["institutions"].append(block_inner[match.start():line_end].strip())
                            cursor = line_end
                current_idx = c_end

        if not found_any: return None
        return data

    def get_nearest_vic3_color(self, rgb):
        colors = {
            "white": (255, 255, 255), "black": (10, 10, 10), "red": (180, 0, 0),
            "green": (0, 180, 0), "blue": (0, 0, 180), "yellow": (255, 255, 0),
            "gold": (212, 175, 55), "orange": (255, 140, 0), "pink": (255, 105, 180),
            "purple": (128, 0, 128), "brown": (139, 69, 19), "grey": (128, 128, 128),
            "dark_red": (100, 0, 0), "dark_blue": (0, 0, 100), "dark_green": (0, 80, 0),
            "light_blue": (135, 206, 235)
        }
        r, g, b = rgb
        min_dist = float('inf')
        closest_name = "white"
        for name, c_rgb in colors.items():
            dist = (r - c_rgb[0])**2 + (g - c_rgb[1])**2 + (b - c_rgb[2])**2
            if dist < min_dist:
                min_dist = dist
                closest_name = name
        return closest_name

    @mod_operation
    def create_country_files(self, tag, name, adjective, capital, color_rgb, cultures_list, religion, tier, country_type, old_tag, wealth=None, literacy=None):
        self.perform_auto_backup()
        self.log(f"[GEN] Creating core files for {tag} ({name})...")
        r_i, g_i, b_i = int(color_rgb[0]), int(color_rgb[1]), int(color_rgb[2])
        flag_color_name = self.get_nearest_vic3_color((r_i, g_i, b_i))
        self.log(f"   [COLOR] Mapped selection {color_rgb} to flag color: '{flag_color_name}'")

        cultures_str = " ".join(cultures_list)

        # Definition
        def_dir = os.path.join(self.mod_path, "common/country_definitions")
        os.makedirs(def_dir, exist_ok=True)
        def_file = os.path.join(def_dir, f"99_auto_{tag.lower()}.txt")
        def_content = f"""{tag} = {{
    color = {{ {r_i} {g_i} {b_i} }}
    country_type = {country_type}
    tier = {tier}
    cultures = {{ {cultures_str} }}
    religion = {religion}
    capital = {capital}
}}
"""
        with open(def_file, 'w', encoding='utf-8-sig') as f: f.write(def_content)

        # Localization
        loc_dir = os.path.join(self.mod_path, "localization/english")
        os.makedirs(loc_dir, exist_ok=True)
        loc_file = os.path.join(loc_dir, f"auto_{tag.lower()}_l_english.yml")
        loc_content = f"""l_english:
 {tag}:0 "{self.safe_str(name)}"
 {tag}_ADJ:0 "{self.safe_str(adjective)}"
 {tag}_DEF:0 "{self.safe_str(name)}"
"""
        with open(loc_file, 'w', encoding='utf-8-sig') as f: f.write(loc_content)

        # History
        hist_dir = os.path.join(self.mod_path, "common/history/countries")
        os.makedirs(hist_dir, exist_ok=True)
        hist_file = os.path.join(hist_dir, f"{tag} - v3mt.txt")

        # Extended Data Extraction
        ext_data = self.get_extended_history_data(old_tag)
        old_tag_details = self.load_country_history_details(old_tag)
        gov_type = old_tag_details.get("gov_type", "monarchy")

        laws_block = ""
        tech_tier_str = ""
        techs_res_str = ""
        politics_str = ""
        inst_str = ""

        if ext_data:
            if ext_data["laws"]:
                laws_block = "\n\t" + "\n\t".join(list(dict.fromkeys(ext_data["laws"])))
            if ext_data["tech_tier"]:
                tech_tier_str = "\n\t" + "\n\t".join(list(dict.fromkeys(ext_data["tech_tier"])))
            if ext_data["techs_researched"]:
                techs_res_str = "\n\t" + "\n\t".join(list(dict.fromkeys(ext_data["techs_researched"])))
            if ext_data["politics"]:
                politics_str = "\n\t" + "\n\t".join(list(dict.fromkeys(ext_data["politics"])))
            if ext_data["institutions"]:
                inst_str = "\n\t" + "\n\t".join(list(dict.fromkeys(ext_data["institutions"])))

        if not laws_block:
            laws_block = """
    activate_law = law_type:law_monarchy
    activate_law = law_type:law_autocracy
    activate_law = law_type:law_peasant_levies
    activate_law = law_type:law_land_tax
""" if gov_type == "monarchy" else """
    activate_law = law_type:law_presidential_republic
    activate_law = law_type:law_census_voting
    activate_law = law_type:law_national_militia
    activate_law = law_type:law_per_capita_tax
    activate_law = law_type:law_appointed_bureaucrats
"""

        if not tech_tier_str:
             tech_tier_str = "effect_starting_technology_tier_1_tech = yes"

        ig_ruler = "ig_landowners" if gov_type == "monarchy" else "ig_intelligentsia"

        hist_content = f"""COUNTRIES = {{
    c:{tag} ?= {{
        {tech_tier_str}
        set_tax_level = medium
        {laws_block}
        {politics_str}
        {techs_res_str}
        {inst_str}

        create_character = {{
            first_name = "Alexander"
            last_name = "Modman"
            birth_date = 1800.1.1
            ruler = yes
            interest_group = {ig_ruler}
        }}
    }}
}}
"""
        with open(hist_file, 'w', encoding='utf-8-sig') as f: f.write(hist_content)

        # Population History
        pop_dir = os.path.join(self.mod_path, "common/history/population")
        os.makedirs(pop_dir, exist_ok=True)
        pop_file = os.path.join(pop_dir, f"{tag} - v3mt.txt")

        if wealth or literacy:
            # Use provided settings
            pop_effects = ""
            if wealth: pop_effects += f"{wealth} = yes"
            if literacy:
                if pop_effects: pop_effects += "\n\t\t"
                pop_effects += f"{literacy} = yes"

            # Use defaults if one is missing but other is provided?
            # Or just use what is given.
            if not pop_effects: # Should not happen if wealth or literacy is true
                 pop_effects = "effect_starting_pop_wealth_medium = yes\n\t\teffect_starting_pop_literacy_medium = yes"
        else:
            # Fallback to copy from old tag
            pop_effects = self.get_pop_history_data(old_tag)
            if not pop_effects:
                 pop_effects = "effect_starting_pop_wealth_medium = yes\n\t\teffect_starting_pop_literacy_medium = yes"

        pop_content = f"""POPULATION = {{
    c:{tag} = {{
        {pop_effects}
    }}
}}
"""
        with open(pop_file, 'w', encoding='utf-8-sig') as f: f.write(pop_content)

        # Flag
        flag_dir = os.path.join(self.mod_path, "common/coat_of_arms/coat_of_arms")
        os.makedirs(flag_dir, exist_ok=True)
        flag_file = os.path.join(flag_dir, f"99_auto_{tag.lower()}.txt")
        flag_content = f"""{tag} = {{
    pattern = "pattern_solid.tga"
    color1 = "{flag_color_name}"
}}
"""
        with open(flag_file, 'w', encoding='utf-8-sig') as f: f.write(flag_content)

    def _get_location_data(self, tag, target_state):
        owned = set(self.get_all_owned_states(tag))
        state = self.normalize_state_key(target_state) if target_state else self.get_country_data(tag).get('capital')
        if not state or state not in owned: raise ValueError('Choose a state owned by this country (or leave blank for its owned capital).')
        region = self.find_strategic_region(state)
        if not region: raise ValueError(f'No strategic region contains {state}; load current game definitions.')
        return state, 'sr:'+region.removeprefix('sr:')

    @mod_operation
    def create_army_file(self, tag, army_name, target_state, inf, art, cav):
        return self._write_formation(tag, army_name, target_state, dict(combat_unit_type_line_infantry=inf, combat_unit_type_cannon_artillery=art, combat_unit_type_hussars=cav))

    @mod_operation
    def create_navy_file(self, tag, navy_name, target_state, manowar, frigate, ironclad):
        return self._write_formation(tag, navy_name, target_state, dict(ship_type_ship_of_the_line=manowar, ship_type_frigate=frigate, ship_type_ironclad=ironclad), fleet=True)

    # --- EXISTING TRANSFER LOGIC ---
    def find_strategic_region(self, state_key):
        state = self.normalize_state_key(state_key)
        regions = {}
        for path in self.effective_files('common/strategic_regions'):
            text = path.read_text(encoding='utf-8-sig')
            for b in script_blocks(text, depth=0):
                if not b['key']: continue
                body = text[b['opening']+1:b['end']-1]
                regions[b['key']] = {t.strip('"').removeprefix('s:') for sb in script_blocks(body, 'states', 0)
                                     for t,_,_ in script_tokens(body[sb['opening']+1:sb['end']-1])}
        for key, states in regions.items():
            if state in states: return key
        return None

    def get_states_in_region(self, region_name):
        result = []
        for path in self.effective_files('common/strategic_regions'):
            text = path.read_text(encoding='utf-8-sig')
            for b in script_blocks(text, region_name.removeprefix('sr:'), 0):
                body = text[b['opening']+1:b['end']-1]
                result = [self.normalize_state_key(t) for sb in script_blocks(body, 'states', 0)
                          for t,_,_ in script_tokens(body[sb['opening']+1:sb['end']-1])]
        return result

    def find_block_content(self, text, start_index):
        try:
            tokens = script_tokens(text[start_index:])
            start, depth = None, 0
            for token, a, b in tokens:
                if token == '{':
                    if start is None: start = start_index+a
                    depth += 1
                elif token == '}' and start is not None:
                    depth -= 1
                    if depth == 0: return start, start_index+b
        except ValueError:
            pass
        return None, None

    def get_block_range_safe(self, content, start_pattern, start_search_idx=0):
        for block in script_blocks(content):
            if block['key'] and block['key'].lower() == start_pattern.lower() and block['start'] >= start_search_idx:
                return block['start'], block['end']
        return None, None

    def collect_valid_scopes(self):
        valid_scopes = set()
        paths = [
            os.path.join(self.mod_path, "common/history/military_formations"),
            os.path.join(self.mod_path, "common/history/characters")
        ]
        scope_regex = re.compile(r"save_scope_as\s*=\s*([A-Za-z0-9_]+)", re.IGNORECASE)

        for p in paths:
            if not os.path.exists(p): continue
            for root, _, files in os.walk(p):
                if self.stop_event.is_set(): return valid_scopes
                for file in files:
                    if not file.endswith(".txt"): continue
                    path = os.path.join(root, file)
                    try:
                        with open(path, 'r', encoding='utf-8-sig') as f: content = f.read()
                    except:
                        with open(path, 'r', encoding='utf-8') as f: content = f.read()
                    valid_scopes.update(scope_regex.findall(content))
        return valid_scopes

    def clean_trade_history(self, state_list):
        self.log("[TRADE] Scanning historical trade for cleanup...")
        trade_file = os.path.join(self.mod_path, "common/history/trade/00_historical_trade.txt")
        if not os.path.exists(trade_file): return

        try:
            with open(trade_file, 'r', encoding='utf-8-sig') as f: content = f.read()
        except: return

        # Iterate states to remove
        changed = False
        for state in state_list:
            # We look for s:STATE_NAME = { ... }
            # User example: s:STATE_WEST_PRUSSIA={ ... }

            # Need to match strictly s:STATE_NAME\s*=\s*\{
            # We will use re.search to find start, then block helper
            # Standardize state name input (usually STATE_NAME) to regex
            # state_list passed here are from transfer list, usually formatted cleanly

            # Regex: s:STATE_NAME\s*=\s*\{
            pattern = re.compile(r"s:" + re.escape(state) + r"\s*=\s*\{")

            # We need to remove the whole block.
            while True:
                m = pattern.search(content)
                if not m: break

                # Find block end
                s_idx = m.end() - 1
                _, e_idx = self.find_block_content(content, s_idx)

                if e_idx:
                    # Remove block including key
                    content = content[:m.start()] + content[e_idx:]
                    changed = True
                else:
                    break

        if changed:
            with open(trade_file, 'w', encoding='utf-8-sig') as f: f.write(content)
            self.log("[TRADE] Cleaned up trade routes.")

    def prune_orphaned_commanders(self, valid_scopes):
        paths = [
            os.path.join(self.mod_path, "common/history/characters"),
            os.path.join(self.mod_path, "common/history/military_formations")
        ]

        link_regex = re.compile(r"((?:commander_formation|transfer_to_formation)\s*=\s*scope:)([A-Za-z0-9_]+)", re.IGNORECASE)
        orphans_removed = 0
        self.log("[FIX] Checking for orphaned formation links...")

        for p in paths:
            if not os.path.exists(p): continue
            for root, _, files in os.walk(p):
                if self.stop_event.is_set(): return
                for file in files:
                    if not file.endswith(".txt"): continue
                    path = os.path.join(root, file)
                    try:
                        with open(path, 'r', encoding='utf-8-sig') as f: content = f.read()
                    except:
                        with open(path, 'r', encoding='utf-8') as f: content = f.read()
                    new_lines = []
                    file_changed = False
                    for line in content.splitlines():
                        match = link_regex.search(line)
                        if match:
                            scope_id = match.group(2)
                            if scope_id not in valid_scopes:
                                new_lines.append(f"# {line.strip()} (FIXED: Orphaned link)")
                                orphans_removed += 1
                                file_changed = True
                            else:
                                new_lines.append(line)
                        else:
                            new_lines.append(line)
                    if file_changed:
                        with open(path, 'w', encoding='utf-8-sig') as f: f.write("\n".join(new_lines))
        if orphans_removed > 0: self.log(f"[SUCCESS] Removed {orphans_removed} orphaned links.", 'success')

    def get_all_owned_states(self, tag):
        tag=self.format_tag_clean(tag);result=set()
        for path in self.effective_files('common/history/states'):
            text=path.read_text(encoding='utf-8-sig')
            for state in script_blocks(text):
                if not state['key'] or not state['key'].startswith('s:STATE_'): continue
                body=text[state['opening']+1:state['end']-1]
                for creation in script_blocks(body,'create_state',0):
                    if field(body[creation['opening']+1:creation['end']-1],'country').removeprefix('c:')==tag:result.add(state['key'][2:])
        return sorted(result)

    def get_ownership_content(self, building_type, owner_tag, level, state_name):
        """Returns the inner content for an ownership block."""
        # Ensure prefix
        if not building_type.startswith("building_"):
            building_type = f"building_{building_type}"

        clean_owner = owner_tag.replace("c:", "").strip()
        # Ensure state name is just the name, no s: prefix
        clean_state = state_name.replace("s:", "").strip()

        if building_type in self.CAT_A_STATE:
             return f'country = {{ country = "c:{clean_owner}" levels = {level} }}'

        elif building_type in self.CAT_B_RURAL:
             return f'building = {{\n\t\t\t\t\t\ttype = "building_manor_house"\n\t\t\t\t\t\tcountry = "c:{clean_owner}"\n\t\t\t\t\t\tlevels = {level}\n\t\t\t\t\t\tregion = "{clean_state}"\n\t\t\t\t\t}}'

        else: # Category C or Fallback
             return f'building = {{\n\t\t\t\t\t\ttype = "building_financial_district"\n\t\t\t\t\t\tcountry = "c:{clean_owner}"\n\t\t\t\t\t\tlevels = {level}\n\t\t\t\t\t\tregion = "{clean_state}"\n\t\t\t\t\t}}'

    def get_ownership_block(self, building_type, owner_tag, level, state_name):
        inner = self.get_ownership_content(building_type, owner_tag, level, state_name)
        if building_type in self.CAT_A_STATE:
            return f'\n\t\t\t\tadd_ownership = {{ {inner} }}'
        else:
            return f'\n\t\t\t\tadd_ownership = {{\n\t\t\t\t\t{inner}\n\t\t\t\t}}'

    def consolidate_ownership(self, content):
        """Merges duplicate ownership entries in add_ownership block."""
        blocks = []
        cursor = 0
        while True:
            m = re.search(r"(building|country)\s*=\s*\{", content[cursor:])
            if not m: break

            abs_start = cursor + m.start()
            s, e = self.find_block_content(content, cursor + m.end() - 1)

            if s is not None:
                block_type = m.group(1)
                inner = content[s+1:e-1]

                parsed = {}
                t_m = re.search(r'type\s*=\s*"?([A-Za-z0-9_]+)"?', inner)
                parsed['type'] = t_m.group(1) if t_m else (block_type if block_type == "country" else "unknown")

                c_m = re.search(r'country\s*=\s*"?([A-Za-z0-9_:]+)"?', inner)
                parsed['country'] = c_m.group(1) if c_m else None

                r_m = re.search(r'region\s*=\s*"?([A-Za-z0-9_:]+)"?', inner)
                parsed['region'] = r_m.group(1) if r_m else None

                cp_m = re.search(r'company\s*=\s*"?([A-Za-z0-9_:]+)"?', inner)
                parsed['company'] = cp_m.group(1) if cp_m else None

                l_m = re.search(r'levels\s*=\s*(\d+)', inner)
                parsed['levels'] = int(l_m.group(1)) if l_m else 0

                blocks.append(parsed)
                cursor = e
            else:
                cursor = abs_start + 1

        merged = {}
        # Dicts preserve insertion order (Python 3.7+)

        for b in blocks:
            # Key tuple: type, country, region, company
            key = (b['type'], b['country'], b['region'], b['company'])

            if key in merged:
                merged[key] += b['levels']
            else:
                merged[key] = b['levels']

        lines = []
        for key, levels in merged.items():
            b_type, b_country, b_region, b_company = key

            wrapper = "building"
            if b_type == "country":
                wrapper = "country"

            inner_parts = []
            if b_type != "country" and b_type != "unknown":
                inner_parts.append(f'type = "{b_type}"')

            if b_country:
                inner_parts.append(f'country = "{b_country}"')

            if b_region:
                inner_parts.append(f'region = "{b_region}"')

            if b_company:
                inner_parts.append(f'company = "{b_company}"')

            inner_parts.append(f'levels = {levels}')

            inner_str = " ".join(inner_parts)
            lines.append(f'\t\t\t\t\t{wrapper} = {{ {inner_str} }}')

        return "\n".join(lines)

    def fix_building_ownership(self, block_content, owner_tag, state_name):
        """Ensures all create_building blocks in the target region have explicit ownership."""

        # Find region_state block for owner_tag
        cursor = 0
        while True:
            is_region_block = block_content.strip().startswith("region_state:")
            region_start = -1
            region_end = -1

            if is_region_block:
                region_start = 0
                region_end = len(block_content)
            else:
                pat = re.compile(r"region_state:\s*(?:c:)?" + re.escape(owner_tag) + r"\s*=\s*\{", re.IGNORECASE)
                m = pat.search(block_content, cursor)
                if not m: break

                region_start = cursor + m.start()
                _, region_end = self.find_block_content(block_content, cursor + m.end() - 1)
                if not region_end:
                    cursor = region_start + 1
                    continue

            if region_start != -1 and region_end != -1:
                inner_region = block_content[region_start:region_end]
                inner_cursor = 0
                inner_modified = False
                new_inner_parts = []
                last_inner_idx = 0

                while True:
                    m_cb = re.search(r"create_building\s*=\s*\{", inner_region[inner_cursor:])
                    if not m_cb:
                        new_inner_parts.append(inner_region[last_inner_idx:])
                        break

                    cb_abs_start = inner_cursor + m_cb.start()
                    new_inner_parts.append(inner_region[last_inner_idx:cb_abs_start])

                    cb_s, cb_e = self.find_block_content(inner_region, inner_cursor + m_cb.end() - 1)

                    if cb_s:
                        cb_full = inner_region[cb_abs_start:cb_e]
                        cb_inner = inner_region[cb_s+1:cb_e-1]

                        # Detect Type
                        b_type = "unknown"
                        tm = re.search(r"building\s*=\s*\"?([A-Za-z0-9_]+)\"?", cb_inner)
                        if tm: b_type = tm.group(1).lower()

                        # SKIP Subsistence Farms and other auto-managed buildings to prevent crashes
                        if b_type in ["building_subsistence_farms", "building_urban_center", "building_trade_center"]:
                            new_inner_parts.append(cb_full)
                            inner_cursor = cb_e
                            last_inner_idx = cb_e
                            continue

                        # Check for ownership using regex to avoid matching comments
                        has_ownership = bool(re.search(r"(^|\s)add_ownership\s*=\s*\{", cb_inner))
                        level_match = re.search(r"\blevel\s*=\s*(\d+)", cb_inner)
                        level_val = int(level_match.group(1)) if level_match else 1

                        if not has_ownership:
                            # Must fix
                            new_cb_inner = cb_inner
                            if level_match:
                                new_cb_inner = re.sub(r"\blevel\s*=\s*\d+\s*", "", new_cb_inner)

                            ownership_block = self.get_ownership_block(b_type, owner_tag, level_val, state_name)

                            new_cb_block = inner_region[cb_abs_start:cb_s+1] + new_cb_inner.rstrip() + ownership_block + "\n\t\t\t}"
                            new_inner_parts.append(new_cb_block)
                            inner_modified = True
                        else:
                            # Existing ownership found.
                            ao_m = re.search(r"add_ownership\s*=\s*\{", cb_inner)
                            should_rewrite = False

                            if ao_m:
                                ao_s, ao_e = self.find_block_content(cb_inner, ao_m.end()-1)
                                if ao_s:
                                    ao_content = cb_inner[ao_s+1:ao_e-1]

                                    # CONSOLIDATE FIRST: Merge duplicates caused by replacements
                                    consolidated = self.consolidate_ownership(ao_content)

                                    # If consolidation resulted in empty (invalid/empty input), force rewrite
                                    if not consolidated.strip():
                                        should_rewrite = True
                                        total_levels = 1 # Default if unknown
                                        # Try to salvage levels from raw string if possible
                                        raw_lvl = re.findall(r"levels\s*=\s*(\d+)", ao_content)
                                        if raw_lvl:
                                            total_levels = sum(int(x) for x in raw_lvl)
                                    else:
                                        total_levels = 0
                                        levels_matches = re.findall(r"levels\s*=\s*(\d+)", consolidated)
                                        for l in levels_matches: total_levels += int(l)

                                        is_country_type = "country =" in consolidated and "type =" not in consolidated
                                        is_company_type = "company" in consolidated

                                        requires_special = b_type not in self.CAT_A_STATE

                                        # If strict rewrite needed (converting old format to new format)
                                        if (is_country_type and requires_special) or is_company_type:
                                            should_rewrite = True

                                    if should_rewrite:
                                        # Regenerate completely
                                        new_cb_inner_base = cb_inner[:ao_m.start()].rstrip() + cb_inner[ao_e:]
                                        ownership_block = self.get_ownership_block(b_type, owner_tag, total_levels, state_name)

                                        new_cb_block = inner_region[cb_abs_start:cb_s+1] + new_cb_inner_base + ownership_block + "\n\t\t\t}"
                                        new_inner_parts.append(new_cb_block)
                                        inner_modified = True
                                    else:
                                        # Just inject the consolidated content if it changed
                                        new_ao_block = f"add_ownership = {{\n{consolidated}\n\t\t\t\t}}"

                                        # Reconstruct create_building block with new add_ownership
                                        new_cb_inner = cb_inner[:ao_m.start()] + new_ao_block + cb_inner[ao_e:]
                                        new_cb_block = inner_region[cb_abs_start:cb_s+1] + new_cb_inner + "\n\t\t\t}"

                                        new_inner_parts.append(new_cb_block)
                                        inner_modified = True
                                else:
                                    # Parse failed, preserve original
                                    new_inner_parts.append(cb_full)
                            else:
                                new_inner_parts.append(cb_full)

                        inner_cursor = cb_e
                        last_inner_idx = cb_e
                    else:
                        new_inner_parts.append(inner_region[last_inner_idx:cb_abs_start+1])
                        inner_cursor = cb_abs_start + 1
                        last_inner_idx = inner_cursor

                if inner_modified:
                    new_region_block = "".join(new_inner_parts)

                    # --- SAFETY CHECK: Brace Balance ---
                    if new_region_block.count('{') != new_region_block.count('}'):
                        self.log(f"[CRITICAL] Brace mismatch detected in fix_building_ownership for {owner_tag}. Aborting edit to prevent corruption.", 'error')
                        cursor = region_end
                    else:
                        block_content = block_content[:region_start] + new_region_block + block_content[region_end:]
                        diff = len(new_region_block) - (region_end - region_start)
                        cursor = region_end + diff
                else:
                    cursor = region_end

            if is_region_block: break

        return block_content

    def sanitize_block_content(self, content, state_str, old_tag, new_tag, is_building_file):
        content = re.sub(r"region_state:\s*(c:)?" + re.escape(old_tag), f"region_state:{new_tag}", content, flags=re.IGNORECASE)
        content = re.sub(f"c:{re.escape(old_tag)}", f"c:{new_tag}", content, flags=re.IGNORECASE)
        if is_building_file:
            target_region_str = f'region="{state_str}"'
            content = re.sub(r'region\s*=\s*"(s:)?STATE_[A-Za-z0-9_]+"', target_region_str, content, flags=re.IGNORECASE)
            # Fix ownership
            clean_new = new_tag.replace("c:", "").strip()
            content = self.fix_building_ownership(content, clean_new, state_str)
        return content

    def merge_split_state(self, content, state_name, old_tag, new_tag, folder):
        clean_old = old_tag.replace("c:", "").strip()
        clean_new = new_tag.replace("c:", "").strip()

        if folder == "states":
            old_range, new_range = None, None
            cursor = 0
            while True:
                m = re.search(r"create_state\s*=\s*\{", content[cursor:])
                if not m: break
                abs_start = cursor + m.start()
                s, e = self.find_block_content(content, cursor + m.end() - 1)
                if s is not None:
                    block_inner = content[s:e]
                    c_match = re.search(r"country\s*=\s*c:([A-Za-z0-9_]+)", block_inner)
                    if c_match:
                        tag = c_match.group(1)
                        if tag.upper() == clean_old.upper(): old_range = (abs_start, e)
                        elif tag.upper() == clean_new.upper(): new_range = (abs_start, e)
                    cursor = e
                else: cursor = abs_start + 1

            if old_range and new_range:
                old_c = content[old_range[0]:old_range[1]]
                pm = re.search(r"owned_provinces\s*=\s*\{", old_c)
                if pm:
                    ps, pe = self.find_block_content(old_c, pm.end() - 1)
                    if ps is not None:
                        provinces = old_c[ps+1:pe-1].strip()
                        new_c = content[new_range[0]:new_range[1]]
                        if "owned_provinces" in new_c:
                             npm = re.search(r"owned_provinces\s*=\s*\{", new_c)
                             ns, ne = self.find_block_content(new_c, npm.end()-1)
                             new_c = new_c[:ne-1] + " " + provinces + new_c[ne-1:]
                        else:
                             lb = new_c.rfind('}')
                             new_c = new_c[:lb] + f"\n\t\towned_provinces = {{ {provinces} }}\n" + new_c[lb:]

                    first = old_range if old_range[0] < new_range[0] else new_range
                    second = new_range if old_range[0] < new_range[0] else old_range
                    if first == old_range:
                        return content[:first[0]] + content[first[1]:second[0]] + new_c + content[second[1]:]
                    else:
                        return content[:first[0]] + new_c + content[first[1]:second[0]] + content[second[1]:]

            return self.sanitize_block_content(content, state_name, old_tag, new_tag, False)

        else:
            old_range, new_range = None, None
            cursor = 0
            while True:
                m = re.search(r"region_state:([A-Za-z0-9_]+)\s*=\s*\{", content[cursor:], re.IGNORECASE)
                if not m: break
                tag = m.group(1)
                abs_start = cursor + m.start()
                s, e = self.find_block_content(content, cursor + m.end() - 1)
                if s is not None:
                    if tag.upper() == clean_old.upper(): old_range = (abs_start, e)
                    elif tag.upper() == clean_new.upper(): new_range = (abs_start, e)
                    cursor = e
                else: cursor = abs_start + 1

            if old_range and new_range:
                old_c = content[old_range[0]:old_range[1]]
                fb = old_c.find('{')
                inner = old_c[fb+1:-1]
                new_c = content[new_range[0]:new_range[1]]
                lb = new_c.rfind('}')
                new_c = new_c[:lb] + "\n" + inner + "\n" + new_c[lb:]

                new_c = re.sub(f"c:{re.escape(clean_old)}", f"c:{clean_new}", new_c, flags=re.IGNORECASE)

                if folder == "buildings":
                    new_c = self.fix_building_ownership(new_c, clean_new, state_name)

                first = old_range if old_range[0] < new_range[0] else new_range
                second = new_range if old_range[0] < new_range[0] else old_range
                if first == old_range:
                    return content[:first[0]] + content[first[1]:second[0]] + new_c + content[second[1]:]
                else:
                    return content[:first[0]] + new_c + content[first[1]:second[0]] + content[second[1]:]

            return self.sanitize_block_content(content, state_name, old_tag, new_tag, (folder=="buildings"))

    def _detect_owners(self, block_content, folder):
        owners = set()
        if folder == "states":
             matches = re.findall(r"country\s*=\s*c:([A-Za-z0-9_]+)", block_content)
             owners.update(matches)
        else:
             matches = re.findall(r"region_state:([A-Za-z0-9_]+)", block_content)
             owners.update(matches)
        return list(owners)

    @mod_operation
    def transfer_ownership_batch(self, state_list, old_owners, new_tag):
        # Auto-backup handled by caller or usually this is part of a larger operation like Create Country
        # If used standalone via "Transfer States", we should backup.
        self.perform_auto_backup()
        folders = ["states", "pops", "buildings"]
        results = {s: [] for s in state_list}
        railway_recipients = set()

        for folder in folders:
            target_dir = os.path.join(self.mod_path, "common/history", folder)
            if not os.path.exists(target_dir): continue
            for root, _, files in os.walk(target_dir):
                if self.stop_event.is_set(): return results, railway_recipients
                for file in files:
                    if not file.endswith(".txt"): continue
                    filepath = os.path.join(root, file)
                    try:
                        with open(filepath, 'r', encoding='utf-8-sig') as f: content = f.read()
                    except:
                        with open(filepath, 'r', encoding='utf-8') as f: content = f.read()
                    file_changed = False
                    for state in state_list:
                        s_start, s_end = self.get_block_range_safe(content, f"s:{state}")
                        if s_start is not None:
                            block_content = content[s_start:s_end]

                            owners_to_process = []
                            if old_owners:
                                if isinstance(old_owners, list):
                                    owners_to_process = old_owners
                                else:
                                    owners_to_process = [old_owners]
                            else:
                                detected = self._detect_owners(block_content, folder)
                                owners_to_process = [o for o in detected if o.upper() != new_tag.upper()]

                            current_block = block_content
                            changed_block = False

                            for owner in owners_to_process:
                                new_block_content = self.merge_split_state(
                                    current_block, state, owner, new_tag, folder
                                )
                                if new_block_content != current_block:
                                     current_block = new_block_content
                                     changed_block = True

                            if changed_block:
                                content = content[:s_start] + current_block + content[s_end:]
                                file_changed = True
                                if folder not in results[state]: results[state].append(folder)

                                # Check for railways in transferred block
                                if folder == "buildings":
                                    if "building_railway" in current_block:
                                        railway_recipients.add(new_tag)

                    if file_changed:
                        self.log(f"   [UPDATED] {folder}/{file}")
                        with open(filepath, 'w', encoding='utf-8-sig') as f: f.write(content)
        return results, railway_recipients

    def clean_unit_string(self, unit_block):
        cleaned = re.sub(r"id\s*=\s*\d+", "", unit_block, flags=re.IGNORECASE)
        cleaned = "\n".join([line for line in cleaned.split('\n') if line.strip()])
        return cleaned

    def transferred_names(self, tag):
        """Allocate names lazily so a file with no transferred units needs no scan."""
        from collections import Counter
        used = set()
        patterns = {'army': Counter(), 'fleet': Counter()}
        loaded = False
        fallback = None
        number_token = re.compile(r'(?<!\w)([0-9]+)(st|nd|rd|th|re|er|ère|ème|e)?(?!\w)|\b([IVXLCDM]+)\b')

        def roman(number):
            result = ''
            for value, letters in ((1000,'M'),(900,'CM'),(500,'D'),(400,'CD'),(100,'C'),(90,'XC'),(50,'L'),(40,'XL'),(10,'X'),(9,'IX'),(5,'V'),(4,'IV'),(1,'I')):
                count, number = divmod(number, value)
                result += letters * count
            return result

        def read_examples():
            localization = {}
            for path in self.effective_files('common/history/military_formations'):
                text = path.read_text(encoding='utf-8-sig')
                for country in script_blocks(text, 'c:'+tag):
                    body = text[country['opening']+1:country['end']-1]
                    for form in script_blocks(body, 'create_military_formation', 0):
                        inner = body[form['opening']+1:form['end']-1]
                        kind = field(inner, 'type')
                        name = field(inner, 'name')
                        if kind not in patterns or not name or name.casefold().startswith('transferred '):
                            continue
                        token = script_fields(inner)['name'][0]
                        if not token.startswith('"') or '_' in name:
                            if name not in localization:
                                localization[name] = self.get_loc_text(name)
                            translated = localization[name]
                            if translated == name and not token.startswith('"'):
                                continue
                            name = translated
                        if any(c in name for c in '[]$') or '_' in name:
                            continue
                        used.add(name.casefold())
                        match = number_token.search(name)
                        if match:
                            prefix, tail = name[:match.start()], name[match.end():]
                            suffix = match[2] or ''
                            style = 'roman' if match[3] else 'decimal'
                            if suffix in ('st','nd','rd','th'):
                                style, suffix = 'english', ''
                            elif suffix in ('re','er','ère'):
                                style = 'french'
                            width = len(match[1]) if match[1] and match[1].startswith('0') else 0
                            patterns[kind][(prefix, tail, style, suffix, width)] += 1
                        else:
                            patterns[kind][(name+' ', '', 'series', '', 0)] += 1

        def allocate(kind):
            nonlocal loaded, fallback
            if not loaded:
                read_examples()
                loaded = True
            examples = patterns.get(kind, {})
            if examples:
                prefix, tail, style, suffix, width = max(examples, key=lambda k: (k[2]!='series', examples[k]))
            else:
                if fallback is None:
                    fallback = self.get_loc_text(tag+'_ADJ')
                    if fallback == tag+'_ADJ' or '$' in fallback:
                        fallback = tag
                prefix, tail, style, suffix, width = '', ' '+fallback+(' Fleet' if kind=='fleet' else ' Army'), 'english', '', 0
            number = 2 if style == 'series' else 1
            while True:
                ending = suffix
                if style == 'english':
                    ending = 'th' if 10 < number % 100 < 14 else {1:'st',2:'nd',3:'rd'}.get(number % 10,'th')
                elif style == 'french' and number > 1:
                    ending = 'e'
                digits = roman(number) if style in ('roman','series') else str(number).zfill(width)
                name = prefix + digits + ending + tail
                if name.casefold() not in used:
                    used.add(name.casefold())
                    return name
                number += 1
        return allocate

    @mod_operation
    def rename_transfer_placeholders(self, tag):
        tag = self.format_tag_clean(tag)
        allocate = self.transferred_names(tag)
        edits = {}
        for form in self.scan_military_formations(tag):
            if form['name'] in ('Transferred army', 'Transferred fleet', 'Transferred navy'):
                edits.setdefault(Path(form['file']), []).append((form, allocate(form['type'])))
        for path, updates in edits.items():
            text = path.read_text(encoding='utf-8-sig')
            for form, name in reversed(updates):
                start, end = form['opening']+1, form['end']-1
                text = text[:start]+put_field(text[start:end], 'name', quoted(name))+text[end:]
            atomic_text(path, text)
        self.log(f"Renamed {sum(map(len, edits.values()))} transferred formations for {tag}.")

    def process_military_extraction_multi_pass(self, filepath, old_tag, new_tag, region, state_list, force_move=False, dest_hq_region=None, dest_home_state=None):
        path=Path(filepath); text=path.read_text(encoding='utf-8-sig'); edits=[]; transferred=[]
        states={self.normalize_state_key(st) for st in state_list}; new_tag=self.format_tag_clean(new_tag)
        allocate = self.transferred_names(new_tag)
        countries=[b for b in script_blocks(text) if b['key'] and b['key'].startswith('c:')]
        for cb in countries:
            tag=cb['key'][2:]
            if tag==new_tag or (old_tag and tag!=self.format_tag_clean(old_tag)): continue
            base=cb['opening']+1; body=text[base:cb['end']-1]
            for form in script_blocks(body,'create_military_formation',0):
                offset=base+form['opening']+1; inner=text[offset:base+form['end']-1]
                kind=field(inner,'type'); hq=field(inner,'hq_region').removeprefix('sr:')
                if kind=='fleet' and script_blocks(inner,'ship',0):
                    # Modern ships have no state_region. Territorial edits do not delete or divide them.
                    if force_move and hq==(region or '').removeprefix('sr:'):
                        remaining=self.get_all_owned_states(tag)
                        if remaining:
                            new_hq=self.find_strategic_region(remaining[0])
                            if new_hq:
                                changed=put_field(inner,'hq_region','sr:'+new_hq.removeprefix('sr:'))
                                edits.append((offset,base+form['end']-1,changed))
                        else:
                            transferred.append(text[base+form['start']:offset] + put_field(inner, 'name', quoted(allocate(kind))) + '}')
                            edits.append((base+form['start'],base+form['end'],''))
                    continue
                moved=[]; unit_edits=[]
                for unit in script_blocks(inner,'combat_unit',0):
                    raw=inner[unit['opening']+1:unit['end']-1]
                    unit_state=field(raw,'state_region').removeprefix('s:')
                    if unit_state not in states: continue
                    if dest_home_state: raw=put_field(raw,'state_region','s:'+self.normalize_state_key(dest_home_state))
                    moved.append('combat_unit = {'+raw+'}')
                    unit_edits.append((unit['start'],unit['end']))
                if not moved:
                    if force_move and region and hq == region.removeprefix('sr:'):
                        homes = self.get_all_owned_states(tag)
                        replacement = next((r for home in homes if (r := self.find_strategic_region(home))), None)
                        if replacement:
                            edits.append((offset,base+form['end']-1,put_field(inner,'hq_region','sr:'+replacement.removeprefix('sr:'))))
                    continue
                for a,b in reversed(unit_edits): inner=inner[:a]+inner[b:]
                if script_blocks(inner,'combat_unit',0):
                    if force_move and hq==(region or '').removeprefix('sr:'):
                        remaining=script_blocks(inner,'combat_unit',0)[0]
                        home=field(inner[remaining['opening']+1:remaining['end']-1],'state_region')
                        new_hq=self.find_strategic_region(home)
                        if new_hq: inner=put_field(inner,'hq_region','sr:'+new_hq.removeprefix('sr:'))
                    edits.append((offset,base+form['end']-1,inner))
                else: edits.append((base+form['start'],base+form['end'],''))
                target=dest_hq_region or self.find_strategic_region(dest_home_state or next(iter(states))) or region
                if not target: raise ValueError('Cannot transfer units without a valid destination HQ.')
                transferred.append('create_military_formation = {\n    name = '+quoted(allocate(kind))+'\n    type = '+kind+'\n    hq_region = sr:'+target.removeprefix('sr:')+'\n    '+'\n    '.join(moved)+'\n}')
        if not edits: return False
        for a,b,replacement in sorted(edits,reverse=True): text=text[:a]+replacement+text[b:]
        if transferred:
            block='\n    c:'+new_tag+' ?= {\n        '+'\n        '.join(transferred)+'\n    }\n'
            wrappers=script_blocks(text,'MILITARY_FORMATIONS',0)
            if not wrappers: raise ValueError('Missing MILITARY_FORMATIONS wrapper.')
            pos=wrappers[0]['end']-1; text=text[:pos]+block+text[pos:]
        atomic_text(path,text)
        return True

    def scan_state_resources(self, state_name):
        state=self.normalize_state_key(state_name)
        result=dict(arable_land=0,capped={},arable=[],discoverable=[])
        for path in self.effective_files('map_data/state_regions'):
            text=path.read_text(encoding='utf-8-sig')
            for b in script_blocks(text,state,0):
                body=text[b['opening']+1:b['end']-1]
                result=dict(arable_land=int(field(body,'arable_land','0')),capped={},arable=[],discoverable=[])
                for child in script_blocks(body,depth=0):
                    inner=body[child['opening']+1:child['end']-1]
                    if child['key']=='capped_resources': result['capped']={k:int(v[0]) for k,v in script_fields(inner).items()}
                    elif child['key']=='arable_resources': result['arable']=[t.strip('"') for t,_,_ in script_tokens(inner)]
                    elif child['key']=='resource':
                        result['discoverable'].append(dict(type=field(inner,'type'),amount=int(field(inner,'undiscovered_amount','0')),raw=inner))
        return result

    @mod_operation
    def save_state_resources(self, state_name, data):
        self._require_mod()
        state=self.normalize_state_key(state_name)
        selected=None
        for path in self.effective_files('map_data/state_regions'):
            text=path.read_text(encoding='utf-8-sig')
            matches=script_blocks(text,state,0)
            if matches: selected=(path,text,matches[0])
        if not selected: raise ValueError(f'State definition missing: {state}')
        path,text,b=selected
        mod=Path(self.mod_path).resolve()
        target=path if path.resolve().is_relative_to(mod) else mod/path.relative_to(Path(self.vanilla_path)/'game')
        body=text[b['opening']+1:b['end']-1]
        body=put_field(body,'arable_land',nonnegative(data['arable_land'],'Arable land'))
        capped='capped_resources = {\n'+''.join(f'        {identifier(k)} = {nonnegative(v)}\n' for k,v in data['capped'].items())+'    }'
        arable='arable_resources = { '+' '.join(quoted(identifier(k)) for k in data['arable'])+' }'
        existing_resources={}
        for child in script_blocks(body,'resource',0):
            raw=body[child['opening']+1:child['end']-1]
            existing_resources.setdefault(field(raw,'type'),[]).append(raw)
        # Preserve discovered_amount, depletion and unknown fields for retained resource types.
        resources=[]
        for entry in data['discoverable']:
            key=identifier(entry['type'])
            candidates=existing_resources.get(key,[])
            raw=candidates.pop(0) if candidates else '\n        type = '+quoted(key)+'\n'
            resources.append('resource = {'+put_field(raw,'undiscovered_amount',nonnegative(entry['amount']))+'}')
        for child in reversed(script_blocks(body,depth=0)):
            if child['key'] in ('capped_resources','arable_resources','resource'):
                body=body[:child['start']]+body[child['end']:]
        body+='\n    '+capped+'\n    '+arable+'\n    '+'\n    '.join(resources)+'\n'
        self.perform_auto_backup()
        atomic_text(target,text[:b['opening']+1]+body+text[b['end']-1:])
        self.state_manager.load_state_regions()
        self.log(f'[RES] Saved resources for {state}', 'success')

    def clean_military_smart(self, old_tag, new_tag, region, state_list, force_move=False, dest_hq_region=None, dest_home_state=None):
        # Auto-backup usually done before this in transfer flow
        if not region and not state_list: return

        target_states = state_list
        if force_move and region:
             # Fetch all states in the region to ensure we capture everything
             target_states = self.get_states_in_region(region)
             if not target_states:
                 target_states = state_list # Fallback

        mil_dir = os.path.join(self.mod_path, "common/history/military_formations")
        files_processed = 0
        if os.path.exists(mil_dir):
            for root, _, files in os.walk(mil_dir):
                if self.stop_event.is_set(): return
                for file in files:
                    if not file.endswith(".txt"): continue
                    filepath = os.path.join(root, file)
                    files_processed += 1
                    self.process_military_extraction_multi_pass(filepath, old_tag, new_tag, region, target_states, force_move=force_move, dest_hq_region=dest_hq_region, dest_home_state=dest_home_state)

        # Warning if nothing found
        if files_processed == 0 and self.vanilla_path:
             self.log(f"[WARN] No military files in mod. {old_tag} armies may be stuck in vanilla. Copy 'common/history/military_formations' from game to mod.", 'warn')

    def move_military_from_deleted_state(self, old_state_key, new_state_key):
        # 1. Normalize
        old_clean = self.normalize_state_key(old_state_key).replace("s:", "")
        new_clean = self.normalize_state_key(new_state_key).replace("s:", "")

        mil_dir = os.path.join(self.mod_path, "common/history/military_formations")
        if not os.path.exists(mil_dir): return

        touched_formations = set()

        for root, _, files in os.walk(mil_dir):
            for file in files:
                if not file.endswith(".txt"): continue
                path = os.path.join(root, file)
                try:
                    with open(path, 'r', encoding='utf-8-sig') as f: content = f.read()
                except:
                    with open(path, 'r', encoding='utf-8') as f: content = f.read()

                files_changed = False
                new_content = content
                cursor = 0
                while True:
                    m = re.search(r"(?:^|\s)create_military_formation\s*=\s*\{", new_content[cursor:])
                    if not m: break

                    abs_start = cursor + m.start()
                    s, e = self.find_block_content(new_content, cursor + m.end() - 1)

                    if s is not None:
                        block = new_content[s:e]
                        # Check for units in old state
                        pat = re.compile(r"state_region\s*=\s*\"?(s:)?" + re.escape(old_clean) + r"\"?\b")

                        if pat.search(block):
                            updated_block = pat.sub(f'state_region = s:{new_clean}', block)

                            # Get Scope ID
                            scope_m = re.search(r"save_scope_as\s*=\s*([A-Za-z0-9_]+)", updated_block)
                            if scope_m:
                                touched_formations.add(scope_m.group(1))

                            # Inline commander removal
                            if "commander = {" in updated_block:
                                temp_block = updated_block
                                while "commander = {" in temp_block:
                                    cm = re.search(r"commander\s*=\s*\{", temp_block)
                                    if cm:
                                        cs, ce = self.find_block_content(temp_block, cm.end()-1)
                                        if cs:
                                            # Remove including the closing brace. ce is index of closing brace + 1?
                                            # find_block_content returns (start_brace_idx, end_brace_idx+1)
                                            # Wait, check find_block_content implementation.
                                            # It returns (start_brace, i) where i is after the closing brace.
                                            # So text[cs:ce] is "{ ... }".
                                            # We want to remove "commander = { ... }".
                                            # cm.start() is start of "commander"
                                            # ce is end of the block.
                                            temp_block = temp_block[:cm.start()] + temp_block[ce:]
                                        else: break
                                    else: break
                                updated_block = temp_block

                            files_changed = True
                            new_content = new_content[:s] + updated_block + new_content[e:]
                            cursor = s + len(updated_block)
                        else:
                            cursor = e
                    else:
                        cursor += 1

                if files_changed:
                    with open(path, 'w', encoding='utf-8-sig') as f: f.write(new_content)
                    self.log(f"[MIL] Moved units from {old_clean} to {new_clean} in {file}")

        if touched_formations:
            self.disconnect_commanders_from_formations(list(touched_formations))

    def disconnect_commanders_from_formations(self, formation_ids):
        char_dir = os.path.join(self.mod_path, "common/history/characters")
        if not os.path.exists(char_dir): return

        for root, _, files in os.walk(char_dir):
            for file in files:
                if not file.endswith(".txt"): continue
                path = os.path.join(root, file)
                try:
                    with open(path, 'r', encoding='utf-8-sig') as f: content = f.read()
                except:
                    with open(path, 'r', encoding='utf-8') as f: content = f.read()

                new_lines = []
                changed = False
                for line in content.splitlines():
                    found = False
                    for fid in formation_ids:
                        if re.search(r"(commander_formation|transfer_to_formation)\s*=\s*scope:" + re.escape(fid) + r"\b", line):
                            found = True
                            break
                    if found:
                        new_lines.append(f"# {line.strip()} (Disconnected due to state deletion)")
                        changed = True
                    else:
                        new_lines.append(line)

                if changed:
                    with open(path, 'w', encoding='utf-8-sig') as f: f.write("\n".join(new_lines))
                    self.log(f"[CHAR] Disconnected commanders in {file}")

    def flag_catalog(self):
        catalog = {}
        for path in self.effective_files('common/coat_of_arms/coat_of_arms'):
            content = path.read_text(encoding='utf-8-sig')
            for block in script_blocks(content, depth=0):
                key = block['key']
                if key:
                    catalog[key] = (path, content[block['opening']+1:block['end']-1])
        return catalog

    @mod_operation
    def save_flag(self, key, previous, draft):
        identifier(key, 'Flag key')
        script_blocks(draft)
        entry = self.flag_catalog().get(key)
        if (entry[1] if entry else None) != previous:
            raise ValueError('Flag changed on disk. Reload before saving.')
        root = Path(self.mod_path)
        if entry:
            source = entry[0]
            target = source if source.is_relative_to(root) else root/source.relative_to(Path(self.vanilla_path)/'game')
            content = source.read_text(encoding='utf-8-sig')
            block = script_blocks(content,key,0)[-1]
            content = content[:block['opening']+1]+draft+content[block['end']-1:]
        else:
            target = root/'common/coat_of_arms/coat_of_arms'/('99_v3mt_'+key+'.txt')
            content = target.read_text(encoding='utf-8-sig') if target.exists() else ''
            content += '\n'+key+' = {'+draft+'}\n'
        atomic_text(target,content)

    def resolve_transfer_technologies(self, states, recipient, donors):
        recipient = self.format_tag_clean(recipient)
        donors = {self.format_tag_clean(tag) for tag in donors}
        entries = [entry for state in dict.fromkeys(states) for entry in self.scan_state_buildings(state)
                   if entry['region_tag'] in donors and entry['region_tag'] != recipient]
        if not entries:
            return
        def definitions(folder):
            result = {}
            for path in self.effective_files(folder):
                text = path.read_text(encoding='utf-8-sig')
                for block in script_blocks(text, depth=0):
                    result[block['key']] = text[block['opening']+1:block['end']-1]
            return result

        def members(body, key):
            return {token.strip('"') for block in script_blocks(body,key,0)
                    for token,_,_ in script_tokens(body[block['opening']+1:block['end']-1])
                    if re.fullmatch(r'"?[A-Za-z0-9_]+"?',token)}

        buildings = definitions('common/buildings')
        methods = definitions('common/production_methods')
        required = []
        for entry in entries:
            needs = members(buildings.get(entry['type'],''),'unlocking_technologies')
            block = script_blocks(entry['snapshot'], 'create_building',0)[0]
            inner = entry['snapshot'][block['opening']+1:block['end']-1]
            for method in members(inner,'activate_production_methods'):
                needs.update(members(methods.get(method,''),'unlocking_technologies'))
            if needs:
                required.append((entry,needs))
        if not required:
            return
        effects = definitions('common/scripted_effects')
        known = set()
        visited = set()
        def read_grants(body):
            # Repeated assignments matter. Inspect only unconditional direct effects.
            tokens = list(script_tokens(body))
            depth = 0
            for i,(key,_,_) in enumerate(tokens):
                if key == '{': depth += 1
                elif key == '}': depth -= 1
                elif depth == 0 and i+2 < len(tokens) and tokens[i+1][0] == '=':
                    value = tokens[i+2][0].strip('"')
                    if key == 'add_technology_researched':
                        known.add(value.removeprefix('tech:'))
                    elif key in effects and value == 'yes' and key not in visited:
                        visited.add(key)
                        read_grants(effects[key])
        for path in self.effective_files('common/history/countries'):
            text = path.read_text(encoding='utf-8-sig')
            for country in script_blocks(text,'c:'+recipient,1):
                read_grants(text[country['opening']+1:country['end']-1])
        conflicts = [(entry,needs-known) for entry,needs in required if needs-known]
        if not conflicts:
            return
        choose = getattr(self,'choose_transfer_technology',None)
        if choose is None:
            raise ValueError('A building technology decision is required for '+recipient)
        decision = choose(recipient,conflicts)
        if decision == 'grant':
            folder = Path(self.mod_path)/'common/history/countries'
            path = folder/('zz_v3mt_transfer_tech_'+recipient+'.txt')
            text = path.read_text(encoding='utf-8-sig') if path.exists() else ''
            missing = sorted(set.union(*(needs for _,needs in conflicts)))
            grants = '\n'.join('    add_technology_researched = '+identifier(tech) for tech in missing)
            atomic_text(path,text+f'\nCOUNTRIES = {{ c:{recipient} ?= {{\n{grants}\n}} }}\n')
        elif decision == 'delete':
            for entry,_ in sorted(conflicts,key=lambda pair:(pair[0]['file'],pair[0]['indices']['start']),reverse=True):
                self.save_state_building(entry,delete=True)
        else:
            raise ValueError('Transfer cancelled at the building technology decision.')

    @mod_operation
    def perform_transfer_sequence(self, states_clean, new_tag, known_old_owners=None, prune_refs=True):
        self.log("--- Processing Map Data ---")

        # 0. Detect Owners (Before Transfer modifies files)
        target_owners = known_old_owners
        if target_owners is None:
            owners_found = set()
            for state in states_clean:
                owners_found.update(self.scan_state_region_owners(state))
            # Exclude new_tag
            clean_new = new_tag.replace("c:", "").strip().upper()
            owners_found.discard(f"c:{clean_new}")
            owners_found.discard(clean_new)
            target_owners = list(owners_found)

        # 1. Transfer Ownership
        # If known_old_owners is provided (Targeted Transfer), we restrict to those.
        # Otherwise (None), we let transfer_ownership_batch detect owners per-block (Auto Transfer).
        owners_to_pass = known_old_owners if known_old_owners else None

        self.resolve_transfer_technologies(states_clean,new_tag,target_owners or [])
        self.transfer_ownership_batch(states_clean, owners_to_pass, new_tag)

        self.clean_transferred_state_references(states_clean)

        # 1c. Clean Trade History for transferred states
        self.clean_trade_history(states_clean)

        # 2. Military Logic
        # Group transferred states by region
        regions_to_process = {}
        for state in states_clean:
            reg = self.find_strategic_region(f"s:{state}")
            # If region not found, use None key to still process unit removal
            key = reg if reg else "UNKNOWN_REGION"
            if key not in regions_to_process: regions_to_process[key] = []
            regions_to_process[key].append(state)

        self.log("--- Processing Military Formations ---")

        for reg_key, states in regions_to_process.items():
            reg = reg_key if reg_key != "UNKNOWN_REGION" else None
            self.log(f" -> Scanning region: {reg if reg else 'Unknown (Vanilla path missing?)'}")
            home_state = states[0] if states else None

            if target_owners:
                for owner in target_owners:
                    if owner.upper() == new_tag.upper(): continue

                    has_presence = True # Default to True if region unknown (safer, prevents deletion)

                    if reg:
                        # Check abandonment: Does owner retain ANY states in this region?
                        all_reg_states = self.get_states_in_region(reg)
                        owner_owned = self.get_all_owned_states(owner)
                        has_presence = any(s in owner_owned for s in all_reg_states)

                    if not has_presence and reg:
                        self.log(f"    [INFO] {owner} abandoning {reg}. Force moving all units.")
                        self.clean_military_smart(owner, new_tag, reg, states, force_move=True, dest_home_state=home_state)
                    else:
                        if reg:
                            self.log(f"    [INFO] {owner} remains in {reg}. Scanning for displaced units.")
                        else:
                            self.log(f"    [INFO] Region unknown for {owner}. Scanning for displaced units only.")
                        self.clean_military_smart(owner, new_tag, reg, states, force_move=False, dest_home_state=home_state)
            else:
                # Fallback: Scan ALL tags
                self.clean_military_smart(None, new_tag, reg, states, force_move=False, dest_home_state=home_state)

        # 3. Prune Orphans
        if prune_refs:
            self.log("--- Validating Character Links ---")
            valid_scopes = self.collect_valid_scopes()
            self.prune_orphaned_commanders(valid_scopes)
        self.log("Done.", 'success')

    # --- COUNTRY MODIFICATION LOGIC ---
    def load_country_localization(self, tag):
        return self.get_loc_text(tag),self.get_loc_text(tag+'_ADJ')

    @mod_operation
    def save_country_localization(self, tag, name, adj):
        tag=identifier(self.format_tag_clean(tag))
        self._localize('replace/'+tag.lower(),{tag:name,tag+'_ADJ':adj,tag+'_DEF':name})

    def load_country_definition_data(self, tag):
        def_path = os.path.join(self.mod_path, "common", "country_definitions")
        if not os.path.exists(def_path): return None, None, None
        clean_tag = tag.strip()
        for root, _, files in os.walk(def_path):
            for file in files:
                if not file.endswith(".txt"): continue
                path = os.path.join(root, file)
                try:
                    with open(path, 'r', encoding='utf-8-sig') as f: content = f.read()
                except:
                    with open(path, 'r', encoding='utf-8') as f: content = f.read()
                match = re.search(r"(^|\s)" + re.escape(clean_tag) + r"\s*=\s*\{", content, re.MULTILINE)
                if match:
                    start = match.end() - 1
                    _, end = self.find_block_content(content, start)
                    if end:
                        block = content[start:end]
                        c_match = re.search(r"color\s*=\s*(hsv360|hsv|rgb)?\s*\{\s*([0-9.]+)\s+([0-9.]+)\s+([0-9.]+)\s*\}", block, re.IGNORECASE)
                        rgb = (0,0,0)
                        if c_match:
                            c_type = c_match.group(1)
                            v1, v2, v3 = float(c_match.group(2)), float(c_match.group(3)), float(c_match.group(4))

                            if c_type and c_type.lower() == 'hsv360':
                                h = v1 / 360.0
                                s = v2 / 100.0
                                v = v3 / 100.0
                                r, g, b = colorsys.hsv_to_rgb(h, s, v)
                                rgb = (int(r * 255), int(g * 255), int(b * 255))
                            elif c_type and c_type.lower() == 'hsv':
                                h = v1 % 1.0
                                r, g, b = colorsys.hsv_to_rgb(h, v2, v3)
                                rgb = (int(r * 255), int(g * 255), int(b * 255))
                            else:
                                rgb = (int(v1), int(v2), int(v3))

                        cap_match = re.search(r"(capital|capital_state)\s*=\s*([A-Za-z0-9_]+)", block)
                        capital = cap_match.group(2) if cap_match else ""
                        return rgb, capital, path
        return None, None, None

    @mod_operation
    def save_country_definition(self, tag, rgb, capital, filepath, cultures=None, religion=None):
        self.perform_auto_backup()
        if not filepath or not os.path.exists(filepath):
            self.log("[ERROR] Definition file not found to update.", 'error')
            return
        try:
            with open(filepath, 'r', encoding='utf-8-sig') as f: content = f.read()
        except:
            with open(filepath, 'r', encoding='utf-8') as f: content = f.read()
        match = re.search(r"(^|\s)" + re.escape(tag) + r"\s*=\s*\{", content, re.MULTILINE)
        if match:
            start = match.end() - 1
            _, end = self.find_block_content(content, start)
            if end:
                block = content[start:end]
                new_block = block
                r, g, b = rgb
                if re.search(r"color\s*=", new_block):
                    new_block = re.sub(r"color\s*=\s*(?:hsv360|hsv|rgb)?\s*\{[^}]+\}", f"color = {{ {r} {g} {b} }}", new_block)
                else:
                    new_block = new_block[:new_block.rfind('}')] + f"\n\tcolor = {{ {r} {g} {b} }}\n}}"
                if capital:
                    if re.search(r"(capital|capital_state)\s*=", new_block):
                         new_block = re.sub(r"(capital|capital_state)\s*=\s*[A-Za-z0-9_]+", f"capital = {capital}", new_block)
                    else:
                         new_block = new_block[:new_block.rfind('}')] + f"\n\tcapital = {capital}\n}}"
                if cultures:
                    # cultures is a list of strings
                    c_str = " ".join(cultures)
                    if re.search(r"cultures\s*=", new_block):
                         new_block = re.sub(r"cultures\s*=\s*\{[^}]+\}", f"cultures = {{ {c_str} }}", new_block)
                    else:
                         new_block = new_block[:new_block.rfind('}')] + f"\n\tcultures = {{ {c_str} }}\n}}"
                if religion:
                    if re.search(r"religion\s*=", new_block):
                         new_block = re.sub(r"religion\s*=\s*[A-Za-z0-9_]+", f"religion = {religion}", new_block)
                    else:
                         new_block = new_block[:new_block.rfind('}')] + f"\n\treligion = {religion}\n}}"

                # Fix Bug: is_named_from_capital should be yes, not a state name
                if re.search(r"is_named_from_capital\s*=\s*(?!yes\b)[A-Za-z0-9_]+", new_block):
                    new_block = re.sub(r"is_named_from_capital\s*=\s*(?!yes\b)[A-Za-z0-9_]+", "is_named_from_capital = yes", new_block)

                content = content[:start] + new_block + content[end:]
                with open(filepath, 'w', encoding='utf-8-sig') as f: f.write(content)
                self.log(f"[SAVE] Updated definitions in {filepath}", 'success')

    def load_character_template(self, template_name):
        result=None
        for path in self.effective_files('common/character_templates'):
            text=path.read_text(encoding='utf-8-sig')
            for b in script_blocks(text,template_name,0):
                body=text[b['opening']+1:b['end']-1]
                result=dict(first=field(body,'first_name'),last=field(body,'last_name'),ig=field(body,'interest_group'),ideology=field(body,'ideology') or field(body,'trait'),is_ruler=field(body,'ruler')=='yes',file=str(path),key=template_name)
        return result

    def load_country_history_details(self, tag):
        info = { "gov_type": "monarchy", "laws": [], "ruler": {"first": "", "last": "", "ig": "", "ideology": ""} }
        clean_tag = tag.replace("c:", "").strip()

        # 1. Load Laws/Gov from history/countries
        hist_dir = os.path.join(self.mod_path, "common", "history", "countries")
        if os.path.exists(hist_dir):
            for root, _, files in os.walk(hist_dir):
                for file in files:
                    if not file.endswith(".txt"): continue
                    path = os.path.join(root, file)
                    try:
                        with open(path, 'r', encoding='utf-8-sig') as f: content = f.read()
                    except:
                        with open(path, 'r', encoding='utf-8') as f: content = f.read()

                    idx = 0
                    while True:
                        s, e = self.get_block_range_safe(content, f"c:{clean_tag}", idx)
                        if s is None: break
                        block = content[s:e]
                        laws = re.findall(r"activate_law\s*=\s*([A-Za-z0-9_:]+)", block)
                        info["laws"].extend(laws)

                        # Also check for inline rulers here (legacy/simple mod support)
                        char_idx = 0
                        while True:
                            m = re.search(r"create_character\s*=\s*\{", block[char_idx:], re.IGNORECASE)
                            if not m: break
                            abs_start = char_idx + m.start()
                            bs, be = self.find_block_content(block, char_idx + m.end() - 1)
                            if bs is not None:
                                char_block = block[bs:be]
                                if re.search(r"ruler\s*=\s*yes", char_block, re.IGNORECASE):
                                    fn = re.search(r'first_name\s*=\s*(?:"([^"]+)"|([^\s#]+))', char_block)
                                    ln = re.search(r'last_name\s*=\s*(?:"([^"]+)"|([^\s#]+))', char_block)
                                    ig = re.search(r'interest_group\s*=\s*([A-Za-z0-9_]+)', char_block)
                                    ideo = re.search(r'trait\s*=\s*(ideology_[A-Za-z0-9_]+)', char_block)
                                    if fn: info["ruler"]["first"] = fn.group(1) if fn.group(1) else fn.group(2)
                                    if ln: info["ruler"]["last"] = ln.group(1) if ln.group(1) else ln.group(2)
                                    if ig: info["ruler"]["ig"] = ig.group(1)
                                    if ideo: info["ruler"]["ideology"] = ideo.group(1)
                                char_idx = be
                            else: break
                        idx = e

        # 2. Check history/characters for templates (Overwrites inline if found)
        char_hist_dir = os.path.join(self.mod_path, "common", "history", "characters")
        if os.path.exists(char_hist_dir):
            for root, _, files in os.walk(char_hist_dir):
                for file in files:
                    if not file.endswith(".txt"): continue
                    path = os.path.join(root, file)
                    try:
                        with open(path, 'r', encoding='utf-8-sig') as f: content = f.read()
                    except:
                        with open(path, 'r', encoding='utf-8') as f: content = f.read()

                    idx = 0
                    while True:
                        s, e = self.get_block_range_safe(content, f"c:{clean_tag}", idx)
                        if s is None: break
                        block = content[s:e]

                        # Scan for create_character with templates
                        c_cursor = 0
                        while True:
                            m = re.search(r"create_character\s*=\s*\{", block[c_cursor:], re.IGNORECASE)
                            if not m: break
                            start = c_cursor + m.start()
                            bs, be = self.find_block_content(block, c_cursor + m.end() - 1)
                            if bs is not None:
                                inner = block[bs:be]
                                tmpl_match = re.search(r"template\s*=\s*([A-Za-z0-9_.-]+)", inner, re.IGNORECASE)
                                if tmpl_match:
                                    template_name = tmpl_match.group(1)
                                    t_data = self.load_character_template(template_name)
                                    if t_data and t_data["is_ruler"]:
                                        info["ruler"]["first"] = t_data["first"]
                                        info["ruler"]["last"] = t_data["last"]
                                        info["ruler"]["ig"] = t_data["ig"]
                                        info["ruler"]["ideology"] = t_data["ideology"]
                                c_cursor = be
                            else: break
                        idx = e

        # Normalize laws
        info["laws"] = [l.replace("law_type:", "") for l in info["laws"]]

        # 3. Fallback: Check character_templates directly for "country_tag" file if no ruler found yet
        # (This handles cases where history files are hard to parse or missing, but templates exist)
        if not info["ruler"]["first"]:
            tmpl_dir = os.path.join(self.mod_path, "common", "character_templates")
            if os.path.exists(tmpl_dir):
                target_fname = f"country_{clean_tag}"
                for root, _, files in os.walk(tmpl_dir):
                    for file in files:
                        if not file.endswith(".txt"): continue
                        # loose match for filename
                        if target_fname.lower() in file.lower() or clean_tag.lower() in file.lower():
                            path = os.path.join(root, file)
                            try:
                                with open(path, 'r', encoding='utf-8-sig') as f: content = f.read()
                            except:
                                with open(path, 'r', encoding='utf-8') as f: content = f.read()

                            # Scan all top-level blocks
                            cursor = 0
                            while cursor < len(content):
                                # Find start of a block: KEY = {
                                m = re.search(r"([A-Za-z0-9_.-]+)\s*=\s*\{", content[cursor:])
                                if not m: break
                                start = cursor + m.start()
                                bs, be = self.find_block_content(content, cursor + m.end() - 1)
                                if bs is not None:
                                    block_inner = content[bs:be]
                                    if re.search(r"ruler\s*=\s*yes", block_inner, re.IGNORECASE):
                                        # Found a ruler definition!
                                        fn = re.search(r'first_name\s*=\s*(?:"([^"]+)"|([^\s#]+))', block_inner)
                                        if fn: info["ruler"]["first"] = fn.group(1) if fn.group(1) else fn.group(2)

                                        ln = re.search(r'last_name\s*=\s*(?:"([^"]+)"|([^\s#]+))', block_inner)
                                        if ln: info["ruler"]["last"] = ln.group(1) if ln.group(1) else ln.group(2)

                                        ig = re.search(r'interest_group\s*=\s*([A-Za-z0-9_]+)', block_inner)
                                        if ig: info["ruler"]["ig"] = ig.group(1)

                                        ideo = re.search(r'(trait|ideology)\s*=\s*(ideology_[A-Za-z0-9_]+)', block_inner)
                                        if ideo: info["ruler"]["ideology"] = ideo.group(2)

                                        # Stop after finding the first ruler in the file
                                        break
                                    cursor = be
                                else:
                                    # Should not happen if well formed, but skip forward
                                    cursor = start + 1

                            if info["ruler"]["first"]: break
                    if info["ruler"]["first"]: break

        if "law_monarchy" in info["laws"]: info["gov_type"] = "monarchy"
        elif "law_presidential_republic" in info["laws"] or "law_parliamentary_republic" in info["laws"]: info["gov_type"] = "republic"
        elif "law_theocracy" in info["laws"]: info["gov_type"] = "theocracy"
        return info

    @mod_operation
    def save_country_history(self, tag, laws, ruler_info):
        tag=self.format_tag_clean(tag)
        # Resolve law groups from the installed definitions; hardcoded lists miss new laws.
        groups={}
        for path in self.effective_files('common/laws'):
            text=path.read_text(encoding='utf-8-sig')
            for b in script_blocks(text,depth=0):
                groups[b['key']]=field(text[b['opening']+1:b['end']-1],'group')
        laws=[identifier(l.removeprefix('law_type:')) for l in laws]
        if any(not groups.get(l) for l in laws): raise ValueError('Load current law definitions before changing laws.')
        if len({groups[l] for l in laws})!=len(laws): raise ValueError('Choose one law per law group.')
        selected_groups={groups[l] for l in laws}
        inserted=False
        for source in self.effective_files('common/history/countries'):
            original=source.read_text(encoding='utf-8-sig')
            countries=script_blocks(original,'c:'+tag)
            if not countries: continue
            target=self._editable_copy(source); text=target.read_text(encoding='utf-8-sig')
            for country in reversed(script_blocks(text,'c:'+tag)):
                body=text[country['opening']+1:country['end']-1]
                # Remove only direct activate_law assignments in the selected groups.
                tokens=list(script_tokens(body)); depth=0; edits=[]
                for i,(token,a,b) in enumerate(tokens):
                    if token=='{': depth+=1
                    elif token=='}': depth-=1
                    elif depth==0 and token=='activate_law' and i+2<len(tokens) and tokens[i+1][0]=='=':
                        law=tokens[i+2][0].removeprefix('law_type:')
                        if groups.get(law) in selected_groups: edits.append((a,tokens[i+2][2]))
                for a,b in reversed(edits):body=body[:a]+body[b:]
                if not inserted:
                    body+='\n'+''.join(f'        activate_law = law_type:{law}\n' for law in laws);inserted=True
                text=text[:country['opening']+1]+body+text[country['end']-1:]
            atomic_text(target,text)
        if laws and not inserted: raise ValueError('Import the country history before changing laws.')
        if not any(ruler_info.get(k) for k in ('first','last','ig','ideology')): return
        candidates=[]
        for rel in ('common/history/countries','common/history/characters'):
            for path in self.effective_files(rel):
                text=path.read_text(encoding='utf-8-sig')
                for cb in script_blocks(text,'c:'+tag):
                    offset=cb['opening']+1;body=text[offset:cb['end']-1]
                    for char in script_blocks(body,'create_character',0):
                        raw=body[char['opening']+1:char['end']-1]; template=field(raw,'template')
                        data=self.load_character_template(template) if template else None
                        if field(raw,'ruler')=='yes':candidates.append((path,offset+char['opening']+1,offset+char['end']-1,None))
                        elif data and data['is_ruler']:candidates.append((Path(data['file']),None,None,template))
        if len(candidates)!=1: raise ValueError('Cannot identify exactly one starting ruler. Check character history/templates before editing.')
        source,a,b,template=candidates[0];target=self._editable_copy(source);text=target.read_text(encoding='utf-8-sig')
        if template:
            block=script_blocks(text,template,0)[0];a,b=block['opening']+1,block['end']-1
        body=text[a:b]
        for key,argument in [('first_name','first'),('last_name','last'),('interest_group','ig'),('ideology','ideology')]:
            value=ruler_info.get(argument)
            if value:
                if key=='ideology' and field(body,'trait').startswith('ideology_'):
                    old=script_fields(body)['trait']; body=body[:old[1]]+body[old[2]:]
                body=put_field(body,key,quoted(value) if argument in ('first','last') else identifier(value))
        atomic_text(target,text[:a]+body+text[b:])

    # --- DIPLOMACY LOGIC ---
    # --- DIPLOMACY LOGIC ---
    SUBJECT_TYPES = ["colony", "puppet", "dominion", "protectorate", "tributary", "vassal", "personal_union"]

    def find_and_remove_subject_status(self, tag_to_free):
        """Scans all diplomacy files and removes any subject pact where tag_to_free is the target."""
        dip_dir = os.path.join(self.mod_path, "common", "history", "diplomacy")
        if not os.path.exists(dip_dir): return
        clean_target = tag_to_free.replace("c:", "").strip()

        for root, _, files in os.walk(dip_dir):
            for file in files:
                if not file.endswith(".txt"): continue
                path = os.path.join(root, file)
                try:
                    with open(path, 'r', encoding='utf-8-sig') as f: content = f.read()
                except:
                    with open(path, 'r', encoding='utf-8') as f: content = f.read()

                original_content = content
                file_changed = False

                # We need to scan ALL country blocks, because any country could be the overlord
                idx = 0
                while True:
                    # Find next country block
                    match = re.search(r"c:([A-Za-z0-9_]+)\s*\??=\s*\{", content[idx:])
                    if not match: break

                    overlord_tag = match.group(1)
                    abs_start = idx + match.start()
                    s, e = self.find_block_content(content, idx + match.end() - 1)

                    if s is not None:
                        block_body = content[s:e]

                        # Check for subject pacts targeting our tag
                        # create_diplomatic_pact = { country = c:TARGET type = TYPE }
                        new_body_parts = []
                        cursor = 0
                        block_changed = False

                        while cursor < len(block_body):
                            m = re.search(r"create_diplomatic_pact\s*=\s*\{", block_body[cursor:])
                            if not m:
                                new_body_parts.append(block_body[cursor:])
                                break

                            pact_start = cursor + m.start()
                            new_body_parts.append(block_body[cursor:pact_start])

                            bs, be = self.find_block_content(block_body, cursor + m.end() - 1)
                            if bs is not None:
                                pact_inner = block_body[bs:be]
                                is_target = re.search(r"country\s*=\s*c:" + re.escape(clean_target) + r"\b", pact_inner)

                                type_match = re.search(r"type\s*=\s*([A-Za-z0-9_]+)", pact_inner)
                                pact_type = type_match.group(1) if type_match else ""

                                if is_target and pact_type in self.SUBJECT_TYPES:
                                    # This is the pact to remove!
                                    self.log(f"[DIP] Freed {clean_target} from being a {pact_type} of {overlord_tag}", 'warn')
                                    block_changed = True
                                else:
                                    new_body_parts.append(block_body[pact_start:be])
                                cursor = be
                            else:
                                new_body_parts.append(block_body[pact_start:])
                                break

                        if block_changed:
                            # Reconstruct the country block
                            new_block_body = "".join(new_body_parts)
                            # Replace in content (careful with indices, content hasn't changed length yet in loop but we are rebuilding)
                            # To handle this safely in a loop, we usually do one pass or complex offset tracking.
                            # Simpler: If changed, update 'content' and restart loop or adjust offsets?
                            # Since we are iterating top-level blocks, replacing 'content' invalidates 'idx'.

                            # Strategy: Reconstruct the whole file content after processing all blocks?
                            # Or just update this block and update 'e'.

                            # Let's splice it in now
                            prefix = content[:s]
                            suffix = content[e:]
                            content = prefix + new_block_body + suffix
                            file_changed = True

                            # Update e to reflect new length
                            diff = len(new_block_body) - len(block_body)
                            e += diff

                        idx = e
                    else:
                        idx = abs_start + 1 # Should not happen if regex matched

                if file_changed:
                    with open(path, 'w', encoding='utf-8-sig') as f: f.write(content)

    def load_diplomacy_data(self, tag):
        dip_dir = os.path.join(self.mod_path, "common", "history", "diplomacy")
        info = { "subjects": [], "rivals": [], "embargos": [], "truces": [], "relations": [] }
        if not os.path.exists(dip_dir): return info
        clean_tag = tag.replace("c:", "").strip()

        for root, _, files in os.walk(dip_dir):
            for file in files:
                if not file.endswith(".txt"): continue
                path = os.path.join(root, file)
                try:
                    with open(path, 'r', encoding='utf-8-sig') as f: content = f.read()
                except:
                    with open(path, 'r', encoding='utf-8') as f: content = f.read()

                idx = 0
                while True:
                    s, e = self.get_block_range_safe(content, f"c:{clean_tag}", idx)
                    if s is None: break
                    block = content[s:e]

                    # Subjects
                    for m in re.finditer(r"create_diplomatic_pact\s*=\s*\{([^}]+)\}", block):
                        inner = m.group(1)
                        cty = re.search(r"country\s*=\s*c:([A-Za-z0-9_]+)", inner)
                        typ = re.search(r"type\s*=\s*([A-Za-z0-9_]+)", inner)
                        if cty and typ:
                            if typ.group(1) in ["rivalry", "embargo"]: continue # Handled elsewhere usually, but check file
                            info["subjects"].append({"target": cty.group(1), "type": typ.group(1)})

                    # Rivals/Embargos (often same structure as pact)
                    # Check filename or explicit types if they are pacts
                    if "rival" in file or "embargo" in file:
                         for m in re.finditer(r"create_diplomatic_pact\s*=\s*\{([^}]+)\}", block):
                            inner = m.group(1)
                            cty = re.search(r"country\s*=\s*c:([A-Za-z0-9_]+)", inner)
                            typ = re.search(r"type\s*=\s*([A-Za-z0-9_]+)", inner)
                            if cty and typ:
                                if typ.group(1) == "rivalry": info["rivals"].append(cty.group(1))
                                elif typ.group(1) == "embargo": info["embargos"].append(cty.group(1))

                    # Truces
                    for m in re.finditer(r"create_bidirectional_truce\s*=\s*\{([^}]+)\}", block):
                        inner = m.group(1)
                        cty = re.search(r"country\s*=\s*c:([A-Za-z0-9_]+)", inner)
                        dur = re.search(r"months\s*=\s*(\d+)", inner)
                        if cty:
                            info["truces"].append({"target": cty.group(1), "months": dur.group(1) if dur else "12"})

                    # Relations
                    for m in re.finditer(r"set_relations\s*=\s*\{([^}]+)\}", block):
                        inner = m.group(1)
                        cty = re.search(r"country\s*=\s*c:([A-Za-z0-9_]+)", inner)
                        val = re.search(r"value\s*=\s*(-?\d+)", inner)
                        if cty and val:
                            info["relations"].append({"target": cty.group(1), "value": val.group(1)})

                    idx = e
        return info

    @mod_operation
    def add_diplomatic_pact(self, tag, target, pact_type, category):
        self.perform_auto_backup()
        # category: subject, rival, embargo, truce
        clean_tag = tag.replace("c:", "").strip()
        clean_target = target.replace("c:", "").strip()

        # VALIDATION: If creating a subject, ensure no conflicts
        if category == "subject":
            # 1. Target cannot already be a subject
            self.find_and_remove_subject_status(clean_target)
            # 2. Actor (Overlord) cannot be a subject themselves
            self.find_and_remove_subject_status(clean_tag)

        dip_dir = os.path.join(self.mod_path, "common", "history", "diplomacy")
        os.makedirs(dip_dir, exist_ok=True)
        filename = "00_subject_relationships.txt"
        if category == "rival": filename = "00_rivalries.txt"
        elif category == "embargo": filename = "00_embargos.txt"
        elif category == "truce": filename = "00_truces.txt"

        filepath = os.path.join(dip_dir, filename)
        if not os.path.exists(filepath):
             with open(filepath, 'w', encoding='utf-8-sig') as f: f.write("DIPLOMACY = {\n}")

        try:
            with open(filepath, 'r', encoding='utf-8-sig') as f: content = f.read()
        except:
            with open(filepath, 'r', encoding='utf-8') as f: content = f.read()

        # Build entry
        entry = ""
        if category == "truce":
             entry = f"\t\tcreate_bidirectional_truce = {{ country = c:{clean_target} months = 60 }}"
        else:
             entry = f"\t\tcreate_diplomatic_pact = {{ country = c:{clean_target} type = {pact_type} }}"

        # Insert
        s, e = self.get_block_range_safe(content, f"c:{clean_tag}")
        if s is not None:
            # Append to existing block
            block = content[s:e]
            new_block = block[:block.rfind('}')] + "\n" + entry + "\n\t}"
            content = content[:s] + new_block + content[e:]
        else:
            # Create new block
            # Find DIPLOMACY block
            d_s, d_e = self.get_block_range_safe(content, "DIPLOMACY")
            if d_s is not None:
                new_block = f"\n\tc:{clean_tag} ?= {{\n{entry}\n\t}}"
                content = content[:d_e-1] + new_block + "\n}" + content[d_e:]
            else:
                content += f"\nDIPLOMACY = {{\n\tc:{clean_tag} ?= {{\n{entry}\n\t}}\n}}"

        with open(filepath, 'w', encoding='utf-8-sig') as f: f.write(content)
        self.log(f"[DIP] Added {pact_type} with {clean_target} in {filename}", 'success')

    @mod_operation
    def remove_diplomatic_pact(self, tag, target, pact_type):
        country='c:'+self.format_tag_clean(tag); target='c:'+self.format_tag_clean(target)
        for path in sorted((Path(self.mod_path)/'common/history/diplomacy').rglob('*.txt')):
            text=path.read_text(encoding='utf-8-sig'); edits=[]
            for cb in script_blocks(text,country):
                offset=cb['opening']+1; body=text[offset:cb['end']-1]
                for pact in script_blocks(body,depth=0):
                    inner=body[pact['opening']+1:pact['end']-1]
                    matching_type=(pact['key']=='create_bidirectional_truce') if pact_type=='truce' else (pact['key']=='create_diplomatic_pact' and field(inner,'type')==pact_type)
                    if matching_type and field(inner,'country')==target: edits.append((offset+pact['start'],offset+pact['end']))
            for a,b in sorted(edits,reverse=True): text=text[:a]+text[b:]
            if edits: atomic_text(path,text)

    @mod_operation
    def set_relations(self, tag, target, value):
        self.perform_auto_backup()
        dip_dir = os.path.join(self.mod_path, "common", "history", "diplomacy")
        os.makedirs(dip_dir, exist_ok=True)
        fpath = os.path.join(dip_dir, "00_relations.txt")
        if not os.path.exists(fpath):
             with open(fpath, 'w', encoding='utf-8-sig') as f: f.write("DIPLOMACY = {\n}")

        try:
            with open(fpath, 'r', encoding='utf-8-sig') as f: content = f.read()
        except:
            with open(fpath, 'r', encoding='utf-8') as f: content = f.read()

        clean_tag = tag.replace("c:", "").strip()
        clean_target = target.replace("c:", "").strip()

        # We need to remove existing set_relations for this target first
        s, e = self.get_block_range_safe(content, f"c:{clean_tag}")

        entry = f"\t\tset_relations = {{ country = c:{clean_target} value = {value} }}"

        if s is not None:
            block = content[s:e]
            # Remove existing relation to target
            # Regex: set_relations = { country = c:TARGET value = ... }
            block = re.sub(r"set_relations\s*=\s*\{[^}]*c:" + re.escape(clean_target) + r"\b[^}]*\}", "", block)
            # Append new
            new_block = block[:block.rfind('}')] + "\n" + entry + "\n\t}"
            content = content[:s] + new_block + content[e:]
        else:
             # Create new block
            d_s, d_e = self.get_block_range_safe(content, "DIPLOMACY")
            if d_s is not None:
                new_block = f"\n\tc:{clean_tag} ?= {{\n{entry}\n\t}}"
                content = content[:d_e-1] + new_block + "\n}" + content[d_e:]
            else:
                content += f"\nDIPLOMACY = {{\n\tc:{clean_tag} ?= {{\n{entry}\n\t}}\n}}"

        with open(fpath, 'w', encoding='utf-8-sig') as f: f.write(content)
        self.log(f"[DIP] Relations set to {value} with {clean_target}", 'success')

    # --- MOD MANAGER LOGIC ---
    def copy_tree_content(self, src, dst):
        for source in sorted(Path(src).rglob('*')):
            if source.is_file():
                target = Path(dst)/source.relative_to(src)
                if target.exists(): continue
                target.parent.mkdir(parents=True,exist_ok=True)
                shutil.copy2(source,target)

    def create_new_mod(self, name, location):
        name = name.strip()
        if not name or name in ('.', '..') or re.search(r'[<>:"/\\|?*\x00-\x1f]', name) or name.endswith(('.', ' ')):
            raise ValueError('Choose a valid folder name without slashes or reserved filename characters.')
        if name.split('.')[0].upper() in {'CON','PRN','AUX','NUL',*[f'COM{i}' for i in range(1,10)],*[f'LPT{i}' for i in range(1,10)]}:
            raise ValueError('This name is reserved by Windows.')
        root = Path(location).expanduser().resolve() / name
        if self.vanilla_path and root.is_relative_to(Path(self.vanilla_path).resolve()):
            raise ValueError('Create mods outside the game installation.')
        if root.exists(): raise ValueError('That folder already exists. Open it instead.')
        root.mkdir(parents=True)
        for rel in MOD_DIRECTORIES: (root / rel).mkdir(parents=True, exist_ok=True)
        metadata = dict(name=name, id='', version='1.0.0', supported_game_version='1.15.*',
                        short_description='', tags=[], relationships=[], game_custom_data=dict(multiplayer_synchronized=True))
        atomic_text(root / '.metadata/metadata.json', json.dumps(metadata, indent=2, ensure_ascii=False)+'\n')
        atomic_text(root / 'localization/english/v3mt_l_english.yml', 'l_english:\n', localization=True)
        self.set_mod_path(str(root))
        self.log(f'[SUCCESS] Created mod scaffold: {root}', 'success')
        return True

    def copy_vanilla_files(self, vanilla_path, mod_path):
        self.set_vanilla_path(vanilla_path)
        self.set_mod_path(mod_path)
        root=Path(self.vanilla_path)/'game'
        # History is edited as a coordinated scenario; definitions remain live read-only fallbacks.
        folders=['common/history','common/country_definitions','common/strategic_regions','map_data/state_regions']
        for rel in folders:
            if (root/rel).is_dir(): self.copy_tree_content(root/rel,Path(mod_path)/rel)
        self.state_manager.load_state_regions()
        self.log('[SUCCESS] Imported missing scenario files. Existing mod files were preserved.', 'success')

    def backup_mod(self, mod_path):
        """Creates a numbered backup of the current mod."""
        if not mod_path or not os.path.exists(mod_path):
            self.log("[ERROR] Current mod path invalid.", 'error')
            return

        parent_dir = os.path.dirname(mod_path)
        mod_dirname = os.path.basename(mod_path)

        # Scan for existing backups
        idx = 1
        while True:
            backup_name = f"{mod_dirname}_backup_{idx}"
            backup_path = os.path.join(parent_dir, backup_name)
            if not os.path.exists(backup_path):
                break
            idx += 1

        target_backup_path = os.path.join(parent_dir, f"{mod_dirname}_backup_{idx}")

        try:
            self.log(f"[BACKUP] Creating backup at {target_backup_path}...", 'info')
            shutil.copytree(mod_path, target_backup_path)
            self.log(f"[SUCCESS] Backup created: {os.path.basename(target_backup_path)}", 'success')
        except Exception as e:
            self.log(f"[ERROR] Backup failed: {e}", 'error')

    def perform_auto_backup(self):
        if not self.auto_backup_enabled or not self.mod_path or getattr(self,'_backup_done',False): return
        import zipfile
        from datetime import datetime, timezone
        root=Path(self.mod_path)
        folder=root.parent/(root.name+'_backups'); folder.mkdir(exist_ok=True)
        stamp=datetime.now(timezone.utc).strftime('%Y%m%d_%H%M%S_%f')
        path=folder/f'{stamp}.zip'
        with zipfile.ZipFile(path,'w',zipfile.ZIP_DEFLATED) as archive:
            for file in sorted(root.rglob('*')):
                if file.is_file() and not file.is_symlink(): archive.write(file,file.relative_to(root))
        if getattr(self,'_operation_depth',0): self._backup_done=True
        self.log(f'[BACKUP] Saved {path.name}', 'success')

    # --- RELIGION & CULTURE LOGIC ---
    def scan_culture_definitions(self):
        cultures={}; options={key:set() for key in ('heritage','language','traditions','graphics','ethnicities')}
        names=('male_common_first_names','female_common_first_names','noble_last_names','common_last_names','male_regal_first_names','female_regal_first_names')
        for path in self.effective_files('common/cultures'):
            text=path.read_text(encoding='utf-8-sig')
            for b in script_blocks(text,depth=0):
                body=text[b['opening']+1:b['end']-1];data={}
                for key in ('heritage','language','graphics'):
                    if field(body,key): options[key].add(field(body,key))
                for child in script_blocks(body,depth=0):
                    raw=body[child['opening']+1:child['end']-1]
                    if child['key'] in names:data[child['key']]=raw.strip()
                    elif child['key']=='traditions':options['traditions'].update(t.strip('"') for t,_,_ in script_tokens(raw))
                    elif child['key']=='ethnicities':options['ethnicities'].update(v[0].strip('"') for v in script_fields(raw).values())
                cultures[b['key']]=data
        return (cultures,*(sorted(options[key]) for key in ('heritage','language','traditions','graphics','ethnicities')))

    def scan_all_religions_and_heritages(self):
        religions=set();heritages=set()
        for path in self.effective_files('common/religions'):
            text=path.read_text(encoding='utf-8-sig')
            for b in script_blocks(text,depth=0):
                religions.add(b['key']);value=field(text[b['opening']+1:b['end']-1],'heritage')
                if value:heritages.add(value)
        return sorted(religions),sorted(heritages)

    @mod_operation
    def save_new_culture(self, key, name, color, religion, heritage, language, traditions, graphics, ethnicities, name_data):
        self.perform_auto_backup()
        mod_name = os.path.basename(self.mod_path)

        # 1. Definitions
        cul_dir = os.path.join(self.mod_path, "common", "cultures")
        os.makedirs(cul_dir, exist_ok=True)
        fpath = os.path.join(cul_dir, f"{mod_name}_cultures.txt")

        # Build block
        t_str = " ".join(traditions)

        eth_str = ""
        for i, eth in enumerate(ethnicities):
            eth_str += f"\t\t10 = {eth}\n" # Default weight 10

        name_keys = ["male_common_first_names", "female_common_first_names", "noble_last_names", "common_last_names", "male_regal_first_names", "female_regal_first_names"]
        names_block = ""
        for k in name_keys:
            v = name_data.get(k, "")
            names_block += f"\t{k} = {{ {v} }}\n"

        content_block = f"""
{key} = {{
\tcolor = rgb{{ {color[0]} {color[1]} {color[2]} }}
\treligion = {religion}
\theritage = {heritage}
\tlanguage = {language}
\ttraditions = {{ {t_str} }}
\tgraphics = {graphics}
\tobsessions = {{}}
\tethnicities = {{
{eth_str}\t}}
{names_block}}}
"""
        # Append or Create
        mode = 'a' if os.path.exists(fpath) else 'w'
        try:
            current = Path(fpath).read_text(encoding='utf-8-sig') if Path(fpath).exists() else ''
            blocks = script_blocks(current, key, 0)
            if blocks:
                b = blocks[0]; current = current[:b['start']] + content_block.strip() + current[b['end']:]
            else: current += "\n" + content_block
            atomic_text(fpath, current)
        except Exception as e:
            self.log(f"[ERROR] Failed to save culture: {e}", 'error')
            return

        # 2. Localization
        loc_dir = os.path.join(self.mod_path, "localization", "english")
        os.makedirs(loc_dir, exist_ok=True)
        lpath = os.path.join(loc_dir, f"{mod_name}_cultures_l_english.yml")

        if not os.path.exists(lpath):
             with open(lpath, 'w', encoding='utf-8-sig') as f: f.write("l_english:\n")

        self._localize(Path(lpath).name.removesuffix('_l_english.yml'), {key: name})

        self.log(f"[SUCCESS] Saved culture {key}", 'success')

    @mod_operation
    def save_new_religion(self, key, name, color, heritage, icon_path):
        self.perform_auto_backup()
        mod_name = os.path.basename(self.mod_path)

        # 1. Definitions
        rel_dir = os.path.join(self.mod_path, "common", "religions")
        os.makedirs(rel_dir, exist_ok=True)
        fpath = os.path.join(rel_dir, f"{mod_name}_religions.txt")

        r, g, b = color[0]/255.0, color[1]/255.0, color[2]/255.0

        content_block = f"""
{key} = {{
\ticon = "{icon_path}"
\theritage = {heritage}
\tcolor = {{ {r:.2f} {g:.2f} {b:.2f} }}
}}
"""
        mode = 'a' if os.path.exists(fpath) else 'w'
        try:
            current = Path(fpath).read_text(encoding='utf-8-sig') if Path(fpath).exists() else ''
            blocks = script_blocks(current, key, 0)
            if blocks:
                b = blocks[0]; current = current[:b['start']] + content_block.strip() + current[b['end']:]
            else: current += "\n" + content_block
            atomic_text(fpath, current)
        except Exception as e:
            self.log(f"[ERROR] Failed to save religion: {e}", 'error')
            return

        # 2. Localization
        loc_dir = os.path.join(self.mod_path, "localization", "english")
        os.makedirs(loc_dir, exist_ok=True)
        lpath = os.path.join(loc_dir, f"{mod_name}_religions_l_english.yml")

        if not os.path.exists(lpath):
             with open(lpath, 'w', encoding='utf-8-sig') as f: f.write("l_english:\n")

        self._localize(Path(lpath).name.removesuffix('_l_english.yml'), {key: name})

        self.log(f"[SUCCESS] Saved religion {key}", 'success')

    # --- POWER BLOC LOGIC ---
    def get_all_power_blocs(self):
        """Scans history/global for existing power blocs."""
        blocs = []
        hist_dir = os.path.join(self.mod_path, "common/history/power_blocs")
        if not os.path.exists(hist_dir): return blocs

        for root, _, files in os.walk(hist_dir):
            for file in files:
                if not file.endswith(".txt"): continue
                path = os.path.join(root, file)
                try:
                    with open(path, 'r', encoding='utf-8-sig') as f: content = f.read()
                except:
                    with open(path, 'r', encoding='utf-8') as f: content = f.read()

                # We look for c:TAG ?= { ... create_power_bloc = { name = XXX ... } ... }
                idx = 0
                while True:
                    m = re.search(r"c:([A-Za-z0-9_]+)\s*\??=\s*\{", content[idx:])
                    if not m: break
                    tag = m.group(1)
                    start = idx + m.start()
                    _, end = self.find_block_content(content, idx + m.end() - 1)
                    if end:
                        block = content[start:end]
                        pb_match = re.search(r"create_power_bloc\s*=\s*\{", block)
                        if pb_match:
                            # Extract name
                            pb_start = pb_match.start()
                            _, pb_end = self.find_block_content(block, pb_match.end() - 1)
                            if pb_end:
                                pb_block = block[pb_start:pb_end]
                                name_m = re.search(r"name\s*=\s*([A-Za-z0-9_]+)", pb_block)
                                name = name_m.group(1) if name_m else "Unknown"
                                blocs.append({"tag": tag, "name": name})
                        idx = end
                    else:
                        idx = start + 1
        return blocs

    PB_IDENTITIES = [
        "identity_trade_league",
        "identity_sovereign_empire",
        "identity_ideological_union",
        "identity_military_treaty_organization",
        "identity_religious",
        "identity_cultural"
    ]

    PB_EXCLUSIVE_PRINCIPLES = {
        "identity_trade_league": ["principle_internal_trade", "principle_external_trade"],
        "identity_sovereign_empire": ["principle_vassalization", "principle_exploit_members"],
        "identity_ideological_union": ["principle_ideological_truth", "principle_creative_legislature"],
        "identity_religious": ["principle_divine_economics", "principle_sacred_civics"],
        "identity_military_treaty_organization": ["principle_aggressive_coordination", "principle_defensive_cooperation"],
        "identity_cultural": ["principle_shared_canon"]
    }

    PB_GLOBAL_PRINCIPLES = [
        "principle_construction",
        "principle_foreign_investment",
        "principle_police_coordination",
        "principle_freedom_of_movement",
        "principle_food_standardization",
        "principle_advanced_research",
        "principle_colonial_offices",
        "principle_transport",
        "principle_military_industry",
        "principle_market_unification",
        "principle_companies"
    ]

    PB_PRIMARY_PRINCIPLE_OPTIONS = {
        "identity_trade_league": [
            "principle_external_trade",
            "principle_internal_trade"
        ],
        "identity_sovereign_empire": [
            "principle_vassalization",
            "principle_exploit_members"
        ],
        "identity_ideological_union": [
            "principle_creative_legislature",
            "principle_ideological_truth"
        ],
        "identity_religious": [
            "principle_divine_economics",
            "principle_sacred_civics"
        ],
        "identity_military_treaty_organization": [
            "principle_defensive_cooperation",
            "principle_aggressive_coordination"
        ],
        "identity_cultural": [
            "principle_shared_canon",
            "principle_freedom_of_movement"
        ]
    }

    def get_power_bloc_data(self, tag):
        """Parses power bloc data for a specific tag from history/global."""
        clean_tag = tag.replace("c:", "").strip()
        hist_dir = os.path.join(self.mod_path, "common/history/power_blocs")
        if not os.path.exists(hist_dir): return None

        data = {
            "key": "", "name": "", "loc_name": "", "loc_adj": "",
            "identity": "", "map_color": "", "date": "1836.1.1",
            "principles": [], "members": []
        }

        for root, _, files in os.walk(hist_dir):
            for file in files:
                if not file.endswith(".txt"): continue
                path = os.path.join(root, file)
                try:
                    with open(path, 'r', encoding='utf-8-sig') as f: content = f.read()
                except:
                    with open(path, 'r', encoding='utf-8') as f: content = f.read()

                s, e = self.get_block_range_safe(content, f"c:{clean_tag}")
                if s is not None:
                    block = content[s:e]
                    pb_match = re.search(r"create_power_bloc\s*=\s*\{", block)
                    if pb_match:
                        # Found it!
                        pb_s, pb_e = self.find_block_content(block, pb_match.end() - 1)
                        if pb_s:
                            pb_inner = block[pb_s:pb_e]

                            nm = re.search(r"name\s*=\s*([A-Za-z0-9_]+)", pb_inner)
                            if nm:
                                data["name"] = nm.group(1)
                                data["key"] = nm.group(1)

                            im = re.search(r"identity\s*=\s*([A-Za-z0-9_]+)", pb_inner)
                            if im: data["identity"] = im.group(1)

                            dm = re.search(r"founding_date\s*=\s*([\d\.]+)", pb_inner)
                            if dm: data["date"] = dm.group(1)

                            # Map Color - capture whole value block or string
                            cm = re.search(r"map_color\s*=\s*(\{.+?\}|hsv\s*\{.+?\})", pb_inner, re.DOTALL)
                            if cm:
                                data["map_color"] = " ".join(cm.group(1).split()) # Normalize whitespace

                            # Members
                            mem_matches = re.finditer(r"member\s*=\s*([A-Za-z0-9_:]+)", pb_inner)
                            for mm in mem_matches:
                                data["members"].append(mm.group(1))

                            # Primary Principle
                            pm = re.search(r"principle\s*=\s*([A-Za-z0-9_]+)", pb_inner)
                            if pm:
                                full = pm.group(1)
                                m_lev = re.match(r"(.*)_(\d+)$", full)
                                if m_lev:
                                    data["principles"].append({"key": m_lev.group(1), "level": int(m_lev.group(2))})
                                else:
                                    data["principles"].append({"key": full, "level": 1})

                            # DLC Principles (sibling `if` block)
                            # We search for 'if = { limit = { has_dlc_feature = power_bloc_features } ... }'
                            # inside the COUNTRY block (sibling to create_power_bloc)

                            # Scan for if blocks
                            cursor = 0
                            while cursor < len(block):
                                if_m = re.search(r"\bif\s*=\s*\{", block[cursor:])
                                if not if_m: break
                                if_start = cursor + if_m.start()
                                if_s, if_e = self.find_block_content(block, cursor + if_m.end() - 1)
                                if if_s:
                                    if_inner = block[if_s:if_e]
                                    if "power_bloc_features" in if_inner:
                                        # Check inside for power_bloc = { add_principle = ... }
                                        pb_eff_m = re.search(r"power_bloc\s*=\s*\{", if_inner)
                                        if pb_eff_m:
                                            pe_s, pe_e = self.find_block_content(if_inner, pb_eff_m.end() - 1)
                                            if pe_s:
                                                eff_inner = if_inner[pe_s:pe_e]
                                                # extract all add_principle
                                                for apm in re.finditer(r"add_principle\s*=\s*([A-Za-z0-9_]+)", eff_inner):
                                                    full = apm.group(1)
                                                    m_lev = re.match(r"(.*)_(\d+)$", full)
                                                    if m_lev:
                                                        data["principles"].append({"key": m_lev.group(1), "level": int(m_lev.group(2))})
                                                    else:
                                                        data["principles"].append({"key": full, "level": 1})
                                    cursor = if_e
                                else:
                                    cursor = if_start + 1

                            # De-dupe by key (keep last? or first? usually first is primary)
                            # Actually, list of dicts isn't hashable for set().
                            # We'll just keep them all for now, UI can handle uniqueness validation.

                            # Load localization for the parsed key
                            if data["key"]:
                                loc_name, loc_adj = self.load_power_bloc_localization(data["key"])
                                data["loc_name"] = loc_name
                                data["loc_adj"] = loc_adj

                            return data
        return None

    def load_power_bloc_localization(self, key):
        loc_dir = os.path.join(self.mod_path, "localization", "english")
        target_file = os.path.join(loc_dir, "mod_power_blocs_l_english.yml")
        if not os.path.exists(target_file): return "", ""

        name = ""
        adj = ""
        try:
            with open(target_file, 'r', encoding='utf-8-sig') as f: content = f.read()
        except:
            with open(target_file, 'r', encoding='utf-8') as f: content = f.read()

        m_name = re.search(r'^\s*' + re.escape(key) + r':\d?\s*"(.*)"', content, re.MULTILINE | re.IGNORECASE)
        if m_name: name = m_name.group(1)

        m_adj = re.search(r'^\s*' + re.escape(key) + r'_adj:\d?\s*"(.*)"', content, re.MULTILINE | re.IGNORECASE)
        if m_adj: adj = m_adj.group(1)

        return name, adj

    def save_power_bloc_localization(self, key, name, adj):
        self._localize('mod_power_blocs', {key:name,key+'_adj':adj})

    @mod_operation
    def save_power_bloc_data(self, tag, data):
        """Saves power bloc data to history/global."""
        self.perform_auto_backup()
        hist_dir = os.path.join(self.mod_path, "common/history/power_blocs")
        os.makedirs(hist_dir, exist_ok=True)
        target_file = os.path.join(hist_dir, "00_power_blocs.txt")

        # If file doesn't exist, create it with wrapper
        if not os.path.exists(target_file):
            with open(target_file, 'w', encoding='utf-8-sig') as f: f.write("POWER_BLOCS = {\n}\n")

        try:
            with open(target_file, 'r', encoding='utf-8-sig') as f: content = f.read()
        except:
            with open(target_file, 'r', encoding='utf-8') as f: content = f.read()

        clean_tag = tag.replace("c:", "").strip()

        # Sanitize name for key
        name_key = data['key'].strip()

        # Update localization
        self.save_power_bloc_localization(name_key, data['loc_name'], data['loc_adj'])

        # Prepare content strings
        # FIX: Ensure the identity's core required principle is first
        pb_identity = data.get("identity", "")
        req_principles = self.PB_PRIMARY_PRINCIPLE_OPTIONS.get(pb_identity, [])

        principles_sorted = data["principles"][:]
        # Find if any principle is in req_principles
        found_idx = -1
        for i, p in enumerate(principles_sorted):
            if p["key"] in req_principles:
                found_idx = i
                break

        if found_idx > 0:
            # Move to front
            p = principles_sorted.pop(found_idx)
            principles_sorted.insert(0, p)

        princ_strs = [f"{p['key']}_{p['level']}" for p in principles_sorted]

        if not princ_strs: raise ValueError("Choose at least one primary principle.")
        principle_1 = princ_strs[0]
        extra_principles = princ_strs[1:] if len(princ_strs) > 1 else []

        map_col_str = data["map_color"]
        if not map_col_str: map_col_str = "{ 255 255 255 }"

        # Reconstruct members
        members_list = data.get("members", [])
        # User requested NOT to auto-add leader as member, so we filter it out if present
        filtered_members = [
            m for m in members_list
            if m.replace("c:", "").strip() != clean_tag
        ]

        members_str = "\n\t\t\t".join([f"member = c:{self.format_tag_clean(m)}" for m in filtered_members])

        create_block = f"""
\t\tcreate_power_bloc = {{
\t\t\tname = {name_key}
\t\t\tmap_color = {map_col_str}
\t\t\tfounding_date = {data['date']}
\t\t\tidentity = {data['identity']}
\t\t\tprinciple = {principle_1}
\t\t\t{members_str}
\t\t}}"""

        extra_block = ""
        if extra_principles:
            adds = "\n\t\t\t\t".join([f"add_principle = {p}" for p in extra_principles])
            extra_block = f"""
\t\tif = {{
\t\t\tlimit = {{
\t\t\t\thas_dlc_feature = power_bloc_features
\t\t\t}}
\t\t\tpower_bloc = {{
\t\t\t\t{adds}
\t\t\t}}
\t\t}}"""

        # Locate country block
        s, e = self.get_block_range_safe(content, f"c:{clean_tag}")

        if s is not None:
            # Modify existing country block
            block = content[s:e]

            # Remove existing create_power_bloc and if-dlc blocks from within this country block
            # This is tricky with regex. Best to rebuild the block content.
            # We want to preserve other things? Usually nothing else is in c:TAG block in 00_power_blocs.txt except comments/members
            # But users might put stuff there.

            # Strategy: Replace the entire block content with our new content
            # Assuming the user only uses this file for power blocs as per vanilla structure.

            opening = block.find('{')
            retained = block[opening+1:-1]
            for child in reversed(script_blocks(retained, depth=0)):
                raw = retained[child['start']:child['end']]
                if child['key'] == 'create_power_bloc' or (child['key'] == 'if' and 'has_dlc_feature = power_bloc_features' in raw and 'add_principle' in raw):
                    retained = retained[:child['start']] + retained[child['end']:]
            new_inner = retained + create_block + extra_block + "\n"
            new_block = f"c:{clean_tag} ?= {{{new_inner}\t}}"

            content = content[:s] + new_block + content[e:]

        else:
            # Create new country block inside POWER_BLOCS
            # Find POWER_BLOCS wrapper
            pbs, pbe = self.get_block_range_safe(content, "POWER_BLOCS")
            if pbs is not None:
                new_entry = f"\n\tc:{clean_tag} ?= {{{create_block}{extra_block}\n\t}}"
                # Insert before closing brace
                content = content[:pbe-1] + new_entry + "\n}" + content[pbe:]
            else:
                # Wrap everything? Or append?
                content += f"\nPOWER_BLOCS = {{\n\tc:{clean_tag} ?= {{{create_block}{extra_block}\n\t}}\n}}"

        with open(target_file, 'w', encoding='utf-8-sig') as f: f.write(content)
        self.log(f"[SAVE] Power Bloc saved for {clean_tag}", 'success')

    @mod_operation
    def remove_power_bloc(self, tag):
        """Removes power bloc definition for a tag."""
        self.perform_auto_backup()
        hist_dir = os.path.join(self.mod_path, "common/history/power_blocs")
        if not os.path.exists(hist_dir): return
        clean_tag = tag.replace("c:", "").strip()

        for root, _, files in os.walk(hist_dir):
            for file in files:
                if not file.endswith(".txt"): continue
                path = os.path.join(root, file)
                try:
                    with open(path, 'r', encoding='utf-8-sig') as f: content = f.read()
                except:
                    with open(path, 'r', encoding='utf-8') as f: content = f.read()

                s, e = self.get_block_range_safe(content, f"c:{clean_tag}")
                if s is not None:
                    content = content[:s] + content[e:]
                    with open(path, 'w', encoding='utf-8-sig') as f: f.write(content)
                    self.log(f"[REMOVE] Power Bloc removed for {clean_tag}", 'success')
                    return

    # --- STATE MANAGER LOGIC ---
    def cleanup_trade_routes(self, source_tag):
        """Removes trade routes involving the source tag."""
        clean_tag = source_tag.replace("c:", "").strip()
        path = os.path.join(self.mod_path, "common/history/trade")
        if not os.path.exists(path): return

        for root, _, files in os.walk(path):
            for file in files:
                if not file.endswith(".txt"): continue
                fpath = os.path.join(root, file)
                try:
                    with open(fpath, 'r', encoding='utf-8-sig') as f: content = f.read()
                except:
                    with open(fpath, 'r', encoding='utf-8') as f: content = f.read()

                new_content = content
                file_changed = False
                
                cursor = 0
                new_parts = []
                last_idx = 0
                
                while True:
                    m = re.search(r"create_trade_route\s*=\s*\{", new_content[cursor:])
                    if not m:
                        new_parts.append(new_content[last_idx:])
                        break
                    
                    abs_start = cursor + m.start()
                    s, e = self.find_block_content(new_content, cursor + m.end() - 1)
                    
                    if s is not None:
                        block = new_content[s:e]
                        if re.search(r"(owner|target|source)\s*=\s*c:" + re.escape(clean_tag) + r"\b", block, re.IGNORECASE):
                            new_parts.append(new_content[last_idx:abs_start])
                            file_changed = True
                        else:
                            new_parts.append(new_content[last_idx:e])
                        
                        cursor = e
                        last_idx = e
                    else:
                        cursor = abs_start + 1
                
                if file_changed:
                    with open(fpath, 'w', encoding='utf-8-sig') as f: f.write("".join(new_parts))
                    self.log(f"   [CLEAN] Removed trade routes for {clean_tag} in {file}")

    def cleanup_treaties(self, source_tag):
        """Removes treaties involving the source tag."""
        clean_tag = source_tag.replace("c:", "").strip()
        path = os.path.join(self.mod_path, "common/history/treaties")
        if not os.path.exists(path): return

        for root, _, files in os.walk(path):
            for file in files:
                if not file.endswith(".txt"): continue
                fpath = os.path.join(root, file)
                try:
                    with open(fpath, 'r', encoding='utf-8-sig') as f: content = f.read()
                except:
                    with open(fpath, 'r', encoding='utf-8') as f: content = f.read()

                new_content = content
                file_changed = False
                
                cursor = 0
                new_parts = []
                last_idx = 0
                
                while True:
                    m = re.search(r"create_treaty\s*=\s*\{", new_content[cursor:])
                    if not m:
                        new_parts.append(new_content[last_idx:])
                        break
                    
                    abs_start = cursor + m.start()
                    s, e = self.find_block_content(new_content, cursor + m.end() - 1)
                    
                    if s is not None:
                        block = new_content[s:e]
                        if re.search(r"\bc:" + re.escape(clean_tag) + r"\b", block, re.IGNORECASE):
                            new_parts.append(new_content[last_idx:abs_start])
                            file_changed = True
                        else:
                            new_parts.append(new_content[last_idx:e])
                        cursor = e
                        last_idx = e
                    else:
                        cursor = abs_start + 1

                if file_changed:
                    with open(fpath, 'w', encoding='utf-8-sig') as f: f.write("".join(new_parts))
                    self.log(f"   [CLEAN] Removed treaties for {clean_tag} in {file}")

    def clean_annexed_relations(self, old_tag):
        country = 'c:' + self.format_tag_clean(old_tag)
        folder = Path(self.mod_path) / 'common/history/diplomacy'
        for path in sorted(folder.rglob('*.txt')):
            content = path.read_text(encoding='utf-8-sig')
            edits = []
            for wrapper in script_blocks(content, 'DIPLOMACY', 0):
                start = wrapper['opening'] + 1
                body = content[start:wrapper['end'] - 1]
                for owner in script_blocks(body, depth=0):
                    if not owner['key'].startswith('c:'):
                        continue
                    offset = start + owner['opening'] + 1
                    effects = content[offset:start + owner['end'] - 1]
                    for relation in script_blocks(effects, 'set_relations', 0):
                        args = effects[relation['opening'] + 1:relation['end'] - 1]
                        if owner['key'] == country or field(args, 'country') == country:
                            edits.append((offset + relation['start'], offset + relation['end']))
            for start, end in reversed(edits):
                content = content[:start] + content[end:]
            if edits:
                atomic_text(path, content)

    def update_military_formations(self, source_tag, target_tag):
        source=self.format_tag_clean(source_tag); target=self.format_tag_clean(target_tag)
        if source==target: return
        allocate = self.transferred_names(target)
        for path in sorted((Path(self.mod_path)/'common/history/military_formations').rglob('*.txt')):
            text=path.read_text(encoding='utf-8-sig'); result=text
            # Country-level retag preserves complete fleets, ship modifications and saved scopes.
            for b in reversed(script_blocks(text,'c:'+source,1)):
                body = text[b['opening']+1:b['end']-1]
                for form in reversed(script_blocks(body, 'create_military_formation', 0)):
                    start, end = form['opening']+1, form['end']-1
                    inner = body[start:end]
                    body = body[:start]+put_field(inner, 'name', quoted(allocate(field(inner, 'type'))))+body[end:]
                result = result[:b['start']]+'c:'+target+text[b['start']+len(source)+2:b['opening']+1]+body+result[b['end']-1:]
            if result!=text: atomic_text(path,result)

    def clean_transferred_state_references(self, transferred_states):
        """Correct only ownership seats whose country lost its part of a moved state."""
        moved = {self.normalize_state_key(state) for state in transferred_states}
        owned = {}
        for path in self.effective_files('common/history/states'):
            text = path.read_text(encoding='utf-8-sig')
            for state in script_blocks(text):
                if not (state['key'] or '').startswith('s:STATE_'):
                    continue
                body = text[state['opening']+1:state['end']-1]
                for creation in script_blocks(body, 'create_state', 0):
                    tag = field(body[creation['opening']+1:creation['end']-1], 'country').removeprefix('c:')
                    owned.setdefault(tag, set()).add(state['key'][2:])
        for path in (Path(self.mod_path)/'common/history/buildings').rglob('*.txt'):
            text = path.read_text(encoding='utf-8-sig')
            edits = []
            for state in script_blocks(text):
                if not (state['key'] or '').startswith('s:STATE_'):
                    continue
                start = state['opening']+1
                body = text[start:state['end']-1]
                for local in script_blocks(body, depth=0):
                    if not (local['key'] or '').startswith('region_state:'):
                        continue
                    offset = start+local['opening']+1
                    buildings = text[offset:start+local['end']-1]
                    for ownership in script_blocks(buildings, 'add_ownership'):
                        base = offset+ownership['opening']+1
                        shares = text[base:offset+ownership['end']-1]
                        for entry in script_blocks(shares, depth=0):
                            i,j = base+entry['opening']+1,base+entry['end']-1
                            share = text[i:j]
                            seat = field(share,'region').removeprefix('s:')
                            owner = field(share,'country').removeprefix('c:')
                            if not owner or seat not in moved or seat in owned.get(owner, set()):
                                continue
                            local_tag = local['key'].split(':',1)[1]
                            if owned.get(owner):
                                seat = sorted(owned[owner])[0]
                            elif state['key'][2:] in owned.get(local_tag,set()):
                                seat = state['key'][2:]
                                share = put_field(share,'country',quoted('c:'+local_tag))
                            else:
                                continue
                            edits.append((i,j,put_field(share,'region',quoted(seat))))
            for i,j,value in reversed(edits):
                text = text[:i]+value+text[j:]
            if edits:
                atomic_text(path,text)

    def sanitize_buildings(self, old_tag, target_tag, transferred_states):
        self.perform_auto_backup()
        self.log(f"[ANNEX] Sanitizing buildings: {old_tag} -> {target_tag}")
        
        buildings_dir = os.path.join(self.mod_path, "common/history/buildings")
        if not os.path.exists(buildings_dir): return

        clean_old = old_tag.replace("c:", "").strip()
        clean_target = target_tag.replace("c:", "").strip()

        for root, _, files in os.walk(buildings_dir):
            for file in files:
                if not file.endswith(".txt"): continue
                filepath = os.path.join(root, file)
                
                try:
                    with open(filepath, 'r', encoding='utf-8-sig') as f: content = f.read()
                except:
                    with open(filepath, 'r', encoding='utf-8') as f: content = f.read()
                
                new_content = content
                file_changed = False
                
                # Outer Loop: s:STATE
                cursor = 0
                while True:
                    m_state = re.search(r"s:(STATE_[A-Za-z0-9_]+)\s*=\s*\{", new_content[cursor:])
                    if not m_state: break
                    
                    state_name = m_state.group(1)
                    state_abs_start = cursor + m_state.start()
                    
                    s_inner_start, s_inner_end = self.find_block_content(new_content, cursor + m_state.end() - 1)
                    
                    if s_inner_start:
                        state_body = new_content[s_inner_start:s_inner_end]
                        state_body_new = state_body
                        
                        # Inner Loop: region_state
                        rs_cursor = 0
                        rs_changed = False
                        
                        # We process region_states sequentially inside the extracted body string
                        # Since we modify it, we use a while loop with re-search on remaining part
                        
                        # Strategy: Split into parts or rebuild
                        parts = []
                        last_idx = 0

                        # Find all region_states first? No, modifications shift indices.
                        # Iterative approach on state_body_new

                        temp_cursor = 0
                        while True:
                            m_rs = re.search(r"region_state:\s*(?:c:)?([A-Za-z0-9_]+)\s*=\s*\{", state_body_new[temp_cursor:], re.IGNORECASE)
                            if not m_rs: break

                            rs_owner_raw = m_rs.group(1)
                            rs_owner = self.format_tag_clean(rs_owner_raw)

                            effective_owner = rs_owner
                            if rs_owner == clean_old:
                                effective_owner = clean_target

                            rs_start = temp_cursor + m_rs.start()
                            rs_inner_start, rs_inner_end = self.find_block_content(state_body_new, temp_cursor + m_rs.end() - 1)

                            if rs_inner_start:
                                rs_content = state_body_new[rs_inner_start:rs_inner_end]
                                original_rs_content = rs_content

                                # 1. Nationalize
                                if re.search(r"\bc:" + re.escape(clean_old) + r"\b", rs_content, re.IGNORECASE):
                                    pattern_generic = re.compile(r"\bc:" + re.escape(clean_old) + r"\b", re.IGNORECASE)
                                    rs_content = pattern_generic.sub(f"c:{effective_owner}", rs_content)

                                # 2. Cleanup Empty
                                rs_content = re.sub(r"add_ownership\s*=\s*\{\s*\}", "", rs_content)
                                rs_content = re.sub(r"create_building\s*=\s*\{\s*\}", "", rs_content)

                                # 3. Fix Ownership (Pass State Name!)
                                rs_content = self.fix_building_ownership(rs_content, effective_owner, state_name)

                                if rs_content != original_rs_content:
                                    # Replace in state_body_new
                                    state_body_new = state_body_new[:rs_inner_start] + rs_content + state_body_new[rs_inner_end:]
                                    rs_changed = True
                                    # Advance cursor
                                    temp_cursor = rs_inner_start + len(rs_content)
                                else:
                                    temp_cursor = rs_inner_end
                            else:
                                temp_cursor = rs_start + 1

                        if rs_changed:
                            new_content = new_content[:s_inner_start] + state_body_new + new_content[s_inner_end:]
                            file_changed = True
                            # Adjust main cursor based on length diff
                            diff = len(state_body_new) - len(state_body)
                            cursor = s_inner_end + diff
                        else:
                            cursor = s_inner_end
                    else:
                        cursor = state_abs_start + 1
                
                if file_changed:
                    with open(filepath, 'w', encoding='utf-8-sig') as f: f.write(new_content)
                    self.log(f"   [FIXED] Updated buildings in {file}")

    def scan_state_region_owners(self, state_name):
        """Scans history/states to find which countries own land (create_state) in the state."""
        clean_state = self.format_state_clean(state_name)
        if not clean_state: return []

        paths = []
        if self.mod_path: paths.append(os.path.join(self.mod_path, "common/history/states"))
        if self.vanilla_path: paths.append(os.path.join(self.vanilla_path, "game/common/history/states"))

        owners = set()

        for p in paths:
            if not os.path.exists(p): continue
            for root, _, files in os.walk(p):
                for file in files:
                    if not file.endswith(".txt"): continue
                    try:
                        with open(os.path.join(root, file), 'r', encoding='utf-8-sig') as f: content = f.read()
                    except:
                        with open(os.path.join(root, file), 'r', encoding='utf-8') as f: content = f.read()

                    s, e = self.get_block_range_safe(content, f"s:{clean_state}")
                    if s is None and clean_state.startswith("STATE_"):
                        # Fallback: Try searching for raw state name (without STATE_ prefix)
                        s, e = self.get_block_range_safe(content, f"s:{clean_state[6:]}")

                    if s is not None:
                        block = content[s:e]
                        # Find create_state blocks
                        cursor = 0
                        while True:
                            m = re.search(r"create_state\s*=\s*\{", block[cursor:])
                            if not m: break
                            cs_s, cs_e = self.find_block_content(block, cursor + m.end() - 1)
                            if cs_s:
                                cs_inner = block[cs_s:cs_e]
                                c_match = re.search(r"country\s*=\s*c:([A-Za-z0-9_]+)", cs_inner)
                                if c_match:
                                    owners.add(c_match.group(1))
                                cursor = cs_e
                            else:
                                cursor += 1
                        return sorted(list(owners))
        return sorted(list(owners))

    def get_state_homelands(self, state_name):
        """Scans history/states for add_homeland lines."""
        # Check mod first, then vanilla
        paths = []
        if self.mod_path: paths.append(os.path.join(self.mod_path, "common/history/states"))
        if self.vanilla_path: paths.append(os.path.join(self.vanilla_path, "game/common/history/states"))

        clean_state = self.format_state_clean(state_name)
        if not clean_state: return None, []

        for p in paths:
            if not os.path.exists(p): continue
            for root, _, files in os.walk(p):
                for file in files:
                    if not file.endswith(".txt"): continue
                    fpath = os.path.join(root, file)
                    try:
                        with open(fpath, 'r', encoding='utf-8-sig') as f: content = f.read()
                    except:
                        with open(fpath, 'r', encoding='utf-8') as f: content = f.read()

                    s, e = self.get_block_range_safe(content, f"s:{clean_state}")
                    if s is not None:
                        # Found the state block
                        block = content[s:e]
                        # Extract homelands (allow colons for cu:culture)
                        homelands = re.findall(r"add_homeland\s*=\s*([A-Za-z0-9_:]+)", block)
                        return fpath, list(set(homelands)) # unique
        return None, []

    @mod_operation
    def save_state_homelands(self, state_name, homelands_list):
        self.perform_auto_backup()
        clean_state = self.format_state_clean(state_name)

        # 1. Find existing file or determine where to create
        fpath, _ = self.get_state_homelands(clean_state)

        if not fpath:
            # Need to copy from vanilla? Or create new?
            # Creating new file for homelands requires defining s:STATE = { ... }
            # If we don't have the original file path, we check vanilla again to copy it.
            if self.vanilla_path:
                v_path = os.path.join(self.vanilla_path, "game/common/history/states")
                for root, _, files in os.walk(v_path):
                    for file in files:
                        if not file.endswith(".txt"): continue
                        vf = os.path.join(root, file)
                        with open(vf, 'r', encoding='utf-8', errors='ignore') as f: c = f.read()
                        if f"s:{clean_state}" in c:
                            # Found in vanilla, copy to mod
                            mod_rel = os.path.relpath(vf, os.path.join(self.vanilla_path, "game"))
                            fpath = os.path.join(self.mod_path, mod_rel)
                            os.makedirs(os.path.dirname(fpath), exist_ok=True)
                            shutil.copy2(vf, fpath)
                            break

            if not fpath:
                # Still not found? Create generic
                fpath = os.path.join(self.mod_path, "common/history/states/99_mod_states.txt")
                os.makedirs(os.path.dirname(fpath), exist_ok=True)
                if not os.path.exists(fpath):
                    with open(fpath, 'w', encoding='utf-8-sig') as f: f.write("STATES = {\n}")

        # 2. Modify file
        try:
            with open(fpath, 'r', encoding='utf-8-sig') as f: content = f.read()
        except:
            with open(fpath, 'r', encoding='utf-8') as f: content = f.read()

        s, e = self.get_block_range_safe(content, f"s:{clean_state}")

        new_homelands_str = "\n".join([f"\t\tadd_homeland = {h}" for h in homelands_list])

        if s is not None:
            block = content[s:e]
            # Remove existing add_homeland lines
            block = re.sub(r"\s*add_homeland\s*=\s*[A-Za-z0-9_:]+", "", block)
            # Insert new ones before closing brace
            last_brace = block.rfind('}')
            new_block = block[:last_brace] + "\n" + new_homelands_str + "\n\t}"
            content = content[:s] + new_block + content[e:]
        else:
            # Create block if new file
            new_entry = f"\n\ts:{clean_state} = {{\n{new_homelands_str}\n\t}}"
            # Append to STATES block if exists, or append to file
            ss, se = self.get_block_range_safe(content, "STATES")
            if ss is not None:
                content = content[:se-1] + new_entry + "\n}" + content[se:]
            else:
                content += f"\nSTATES = {{{new_entry}\n}}"

        with open(fpath, 'w', encoding='utf-8-sig') as f: f.write(content)
        self.log(f"[SAVE] Homelands for {clean_state} saved to {os.path.basename(fpath)}", 'success')

    def get_state_pop_aggregates(self, state, region_tag=None):
        pops = self.get_state_pops(state)
        if region_tag:
            clean_tag = region_tag.replace("c:", "").upper()
            pops = [p for p in pops if p['region_tag'].upper() == clean_tag]

        total = sum(p['size'] for p in pops)
        agg = {}
        for p in pops:
            key = (p['culture'], p['religion'])
            if key not in agg: agg[key] = 0
            agg[key] += p['size']

        result = []
        for (c, r), size in agg.items():
            if size <= 0: continue
            result.append({
                "culture": c,
                "religion": r,
                "size": size,
                "percent": (size / total * 100) if total > 0 else 0
            })

        # Sort by size desc
        result.sort(key=lambda x: x['size'], reverse=True)
        return result, total

    @mod_operation
    def save_state_demographics(self, state, region_tag, demographic_data, total_pop, retain_location=False):
        state=self.normalize_state_key(state); total=nonnegative(total_pop,'Population')
        pops=self.get_state_pops(state); owner=self.format_tag_clean(region_tag) if region_tag else None
        targets=[p for p in pops if not owner or p['region_tag']==owner]
        shares={}
        for pop in targets: shares[pop['region_tag']]=shares.get(pop['region_tag'],0)+pop['size']
        if not shares:
            owners=[owner] if owner else [self.format_tag_clean(t) for t in self.scan_state_region_owners(state)]
            shares={tag:1 for tag in owners}
        if not shares: raise ValueError('State has no owner. Set ownership first.')
        demos=[]
        for d in demographic_data:
            weight=float(d['percent'])
            if not math.isfinite(weight) or weight<0: raise ValueError('Demographic percentages must be finite and non-negative.')
            if weight: demos.append((identifier(d['culture']),identifier(d['religion']) if d['religion'] else '',weight))
        if total and not demos: raise ValueError('Add a demographic group before replacing the population.')
        plans=[]
        for tag,size in zip(shares,apportion(total,list(shares.values()))):
            available={(p['culture'],p['religion']) for p in targets if p['region_tag']==tag}
            eligible=[d for d in demos if not retain_location or d[:2] in available]
            if size and not eligible: raise ValueError(f'No selected demographic exists in {tag}; change the mix or disable Retain location.')
            for d,count in zip(eligible,apportion(size,[d[2] for d in eligible])):
                if count: plans.append((tag,d[0],d[1],count))
        # All validation and allocation happens before removing existing pops.
        for source in sorted({p['file'] for p in targets}):
            target=self._editable_copy(Path(source)); text=target.read_text(encoding='utf-8-sig')
            atomic_text(target,self._remove_pops_from_text(text,state,owner))
        destination=Path(self.mod_path)/'common/history/pops/99_v3mt_demographics.txt'
        if not destination.exists(): atomic_text(destination,'POPS = {\n}\n')
        for tag,culture,religion,size in plans: self.add_pop_to_file(str(destination),state,tag,culture,religion,size)

    def _remove_pops_from_text(self, content, state, tag):
        cursor = 0
        while True:
            s, e = self.get_block_range_safe(content, f"s:{state}", cursor)
            if s is None: break

            state_block = content[s:e]

            rs_cursor = 0
            new_state_parts = []
            last_idx = 0

            while True:
                m = re.search(r"region_state:([A-Za-z0-9_]+)\s*=\s*\{", state_block[rs_cursor:])
                if not m:
                    new_state_parts.append(state_block[last_idx:])
                    break

                found_tag = m.group(1).upper()
                abs_start = rs_cursor + m.start()
                new_state_parts.append(state_block[last_idx:abs_start])

                rs_s, rs_e = self.find_block_content(state_block, rs_cursor + m.end() - 1)

                if rs_s:
                    if not tag or found_tag == tag:
                        inner = state_block[rs_s+1:rs_e-1]

                        pop_cursor = 0
                        new_inner_parts = []
                        last_p_idx = 0
                        while True:
                             pm = re.search(r"create_pop\s*=\s*\{", inner[pop_cursor:])
                             if not pm:
                                 new_inner_parts.append(inner[last_p_idx:])
                                 break

                             p_start = pop_cursor + pm.start()
                             new_inner_parts.append(inner[last_p_idx:p_start])

                             p_bs, p_be = self.find_block_content(inner, pop_cursor + pm.end()-1)
                             if p_bs:
                                 pop_cursor = p_be
                                 last_p_idx = p_be
                             else:
                                 pop_cursor += 1

                        rebuilt_inner = "".join(new_inner_parts)
                        new_state_parts.append("{" + rebuilt_inner + "}")
                    else:
                         new_state_parts.append(state_block[abs_start:rs_e])

                    rs_cursor = rs_e
                    last_idx = rs_e
                else:
                    rs_cursor += 1

            rebuilt_state = "".join(new_state_parts)
            if rebuilt_state != state_block:
                content = content[:s] + rebuilt_state + content[e:]
                cursor = s + len(rebuilt_state)
            else:
                cursor = e

        return content

    def get_state_pops(self, state_name):
        state=self.normalize_state_key(state_name); result=[]
        for path in self.effective_files('common/history/pops'):
            text=path.read_text(encoding='utf-8-sig')
            for st in script_blocks(text,'s:'+state):
                start=st['opening']+1; body=text[start:st['end']-1]
                for owner in script_blocks(body,depth=0):
                    if not owner['key'] or not owner['key'].startswith('region_state:'): continue
                    tag=owner['key'].split(':',1)[1]; offset=start+owner['opening']+1; inner=text[offset:start+owner['end']-1]
                    for pop in script_blocks(inner,'create_pop',0):
                        a=offset+pop['opening']+1; b=offset+pop['end']-1; raw=text[a:b]
                        result.append(dict(file=str(path),state=state,region_tag=tag,culture=field(raw,'culture'),religion=field(raw,'religion'),size=int(field(raw,'size','0')),
                            indices=dict(pop_content_start=a,pop_content_end=b),snapshot=raw))
        return result

    @mod_operation
    def save_state_pops_total(self, state_name, new_total, pop_data_list):
        sizes=apportion(new_total,[p['size'] for p in pop_data_list])
        grouped={}
        for pop,size in zip(pop_data_list,sizes): grouped.setdefault(pop['file'],[]).append((pop,size))
        for source,entries in grouped.items():
            target=self._editable_copy(Path(source)); text=target.read_text(encoding='utf-8-sig')
            for pop,size in sorted(entries,key=lambda x:x[0]['indices']['pop_content_start'],reverse=True):
                a,b=pop['indices']['pop_content_start'],pop['indices']['pop_content_end']
                if 'snapshot' not in pop or text[a:b]!=pop['snapshot']: raise ValueError('Population changed since loading. Reload before editing.')
                text=text[:a]+put_field(text[a:b],'size',size)+text[b:]
            atomic_text(target,text)

    @mod_operation
    def save_single_pop(self, pop_entry, new_culture, new_religion, new_size):
        size=nonnegative(new_size,'Population')
        culture=identifier(new_culture,'Culture'); religion=identifier(new_religion,'Religion') if new_religion else ''
        source=Path(pop_entry['file']); target=self._editable_copy(source)
        text=target.read_text(encoding='utf-8-sig'); a=pop_entry['indices']['pop_content_start']; b=pop_entry['indices']['pop_content_end']
        old=text[a:b]
        if 'snapshot' not in pop_entry or old!=pop_entry['snapshot']: raise ValueError('Population changed since loading. Reload before editing.')
        new=put_field(put_field(old,'culture',culture),'size',size)
        if religion: new=put_field(new,'religion',religion)
        atomic_text(target,text[:a]+new+text[b:])

    def get_country_total_pop(self, tag):
        clean_tag = tag.replace("c:", "").strip()
        total = 0
        state_pops_map = {} # state -> pops list

        # Scan only mod pops files to find ALL pops for this tag, regardless of state ownership
        # Strictly no vanilla scanning as requested
        files_to_scan = []

        if self.mod_path:
            m_dir = os.path.join(self.mod_path, "common/history/pops")
            if os.path.exists(m_dir):
                for root, _, files in os.walk(m_dir):
                    for file in files:
                        if not file.endswith(".txt"): continue
                        full_path = os.path.join(root, file)
                        files_to_scan.append(full_path)

        # Scan Content
        for fpath in files_to_scan:
            try:
                with open(fpath, 'r', encoding='utf-8-sig') as f: content = f.read()
            except:
                with open(fpath, 'r', encoding='utf-8') as f: content = f.read()

            cursor = 0
            while True:
                # Find s:STATE
                m_state = re.search(r"(s:STATE_[A-Za-z0-9_]+)\s*=\s*\{", content[cursor:])
                if not m_state: break

                state_key = m_state.group(1).replace("s:", "")
                state_abs_start = cursor + m_state.start()

                s_s, s_e = self.find_block_content(content, cursor + m_state.end() - 1)
                if s_s:
                    state_block = content[s_s:s_e]

                    # Find region_state:TAG inside
                    rs_cursor = 0
                    while True:
                        m_rs = re.search(r"region_state:([A-Za-z0-9_]+)\s*=\s*\{", state_block[rs_cursor:], re.IGNORECASE)
                        if not m_rs: break

                        found_tag = m_rs.group(1).upper()
                        rs_s, rs_e = self.find_block_content(state_block, rs_cursor + m_rs.end() - 1)

                        if found_tag == clean_tag and rs_s:
                            rs_block = state_block[rs_s:rs_e]

                            # Parse pops
                            cp_cursor = 0
                            while True:
                                m_cp = re.search(r"create_pop\s*=\s*\{", rs_block[cp_cursor:])
                                if not m_cp: break

                                cp_s, cp_e = self.find_block_content(rs_block, cp_cursor + m_cp.end() - 1)
                                if cp_s:
                                    cp_inner = rs_block[cp_s:cp_e]

                                    size_m = re.search(r"size\s*=\s*(\d+)", cp_inner)
                                    cul_m = re.search(r"culture\s*=\s*([A-Za-z0-9_]+)", cp_inner)
                                    rel_m = re.search(r"religion\s*=\s*([A-Za-z0-9_]+)", cp_inner)

                                    if size_m:
                                        sz = int(size_m.group(1))
                                        total += sz

                                        # Store info compatible with save_state_pops_total
                                        # Note: indices must be absolute to file content
                                        pop_data = {
                                            "file": fpath,
                                            "is_mod": (self.mod_path in fpath),
                                            "region_tag": clean_tag,
                                            "culture": cul_m.group(1) if cul_m else "",
                                            "religion": rel_m.group(1) if rel_m else "",
                                            "size": sz,
                                            "indices": {
                                                "state_block_start": state_abs_start,
                                                "pop_content_start": s_s + rs_s + cp_s,
                                                "pop_content_end": s_s + rs_s + cp_e
                                            }
                                        }

                                        if state_key not in state_pops_map: state_pops_map[state_key] = []
                                        state_pops_map[state_key].append(pop_data)

                                    cp_cursor = cp_e
                                else:
                                    cp_cursor += 1

                            rs_cursor = rs_e
                        else:
                            if rs_e: rs_cursor = rs_e
                            else: rs_cursor += 1

                    cursor = s_e
                else:
                    cursor = state_abs_start + 1

        return total, state_pops_map

    @mod_operation
    def set_country_total_pop(self, tag, new_total):
        current_total, state_pops_map = self.get_country_total_pop(tag)
        if current_total == 0: return

        ratio = new_total / current_total
        running_total = 0

        items = list(state_pops_map.items())
        for i, (state, pops) in enumerate(items):
            if not pops: continue

            if i == len(items) - 1:
                new_state_total = int(new_total - running_total)
            else:
                current_state_total = sum(p['size'] for p in pops)
                new_state_total = int(current_state_total * ratio)
                running_total += new_state_total

            self.save_state_pops_total(state, new_state_total, pops)

    def convert_state_pops_religion(self, state_name, new_religion):
        pops = self.get_state_pops(state_name)
        for p in pops:
            self.save_single_pop(p, p['culture'], new_religion, p['size'])

    def convert_state_pops_culture(self, state_name, new_culture):
        pops = self.get_state_pops(state_name)
        for p in pops:
            self.save_single_pop(p, new_culture, p['religion'], p['size'])

    @mod_operation
    def convert_country_identity(self, tag, new_culture, new_religion, mode, value_str=None):
        self.perform_auto_backup()
        owned_states = self.get_all_owned_states(tag)
        clean_tag = tag.replace("c:", "").strip()

        # Pre-calculate Percentages per State if partial
        state_pct_map = {}
        if mode == "partial" and value_str:
            min_pct = 0.0
            max_pct = 0.0
            is_range = "-" in value_str
            try:
                if is_range:
                    parts = value_str.split("-")
                    min_pct = float(parts[0]) / 100.0
                    max_pct = float(parts[1]) / 100.0
                else:
                    min_pct = float(value_str) / 100.0
            except:
                self.log("[ERROR] Invalid value format.", 'error')
                return

            for state in owned_states:
                if is_range:
                    state_pct_map[state] = random.uniform(min_pct, max_pct)
                else:
                    state_pct_map[state] = min_pct

        # Collect Pops
        pops_to_process = []
        for state in owned_states:
            pops = self.get_state_pops(state)
            my_pops = [p for p in pops if p['region_tag'].upper() == clean_tag.upper()]
            for p in my_pops: p['state'] = state
            pops_to_process.extend(my_pops)

        if not pops_to_process:
            raise ValueError(f"No starting pops found for {clean_tag}. Check state ownership and imported pop history.")
        # Group by File
        files_map = {}
        for p in pops_to_process:
            if p['file'] not in files_map: files_map[p['file']] = []
            files_map[p['file']].append(p)

        # Process Files
        for fpath, pops_in_file in files_map.items():
            target_path = fpath
            if self.vanilla_path and fpath.startswith(self.vanilla_path):
                mod_rel = os.path.relpath(fpath, os.path.join(self.vanilla_path, "game"))
                target_path = os.path.join(self.mod_path, mod_rel)
                os.makedirs(os.path.dirname(target_path), exist_ok=True)
                if not os.path.exists(target_path):
                    shutil.copy2(fpath, target_path)

            try:
                with open(target_path, 'r', encoding='utf-8-sig') as f: content = f.read()
            except:
                with open(target_path, 'r', encoding='utf-8') as f: content = f.read()

            # Reverse sort for safe in-place modification
            pops_in_file.sort(key=lambda x: x['indices']['pop_content_start'], reverse=True)

            new_pops_queue = [] # (state, cul, rel, size)

            for p in pops_in_file:
                s = p['indices']['pop_content_start']
                e = p['indices']['pop_content_end']

                # Check existing religion for 'maintain' feature
                has_religion = bool(p.get('religion'))

                if mode == "full":
                    block = content[s:e]
                    if new_culture:
                        block = put_field(block, 'culture', identifier(new_culture))
                    if new_religion:
                        block = put_field(block, 'religion', identifier(new_religion))
                    content = content[:s] + block + content[e:]

                else:
                    # Partial
                    pct = state_pct_map.get(p['state'], 0.0)
                    move_amount = int(p['size'] * pct)
                    if move_amount <= 0: continue

                    remain = p['size'] - move_amount

                    # Update current
                    block = content[s:e]
                    block = re.sub(r"size\s*=\s*\d+", f"size = {remain}", block)
                    content = content[:s] + block + content[e:]

                    target_c = new_culture if new_culture else p['culture']
                    target_r = new_religion if new_religion else p['religion']

                    new_pops_queue.append((p['state'], target_c, target_r, move_amount))

            # Apply additions
            for state, nc, nr, ns in new_pops_queue:
                 s_state, e_state = self.get_block_range_safe(content, f"s:{state}")
                 if s_state is None: continue

                 block = content[s_state:e_state]

                 # Find region_state:clean_tag
                 cursor = 0
                 found = False
                 insert_pos = -1

                 while True:
                     m = re.search(r"region_state:([A-Za-z0-9_]+)\s*=\s*\{", block[cursor:])
                     if not m: break
                     rt = m.group(1)
                     rs_s, rs_e = self.find_block_content(block, cursor + m.end() - 1)
                     if rt.upper() == clean_tag.upper():
                         insert_pos = s_state + rs_e - 1
                         found = True
                         break
                     cursor = rs_e

                 if found:
                     rel_str = f" religion = {nr}" if nr else ""
                     entry = f"\n\t\t\tcreate_pop = {{ culture = {nc}{rel_str} size = {ns} }}"
                     content = content[:insert_pos] + entry + content[insert_pos:]

            with open(target_path, 'w', encoding='utf-8-sig') as f: f.write(content)
            self.log(f"[CONVERT] Processed {os.path.basename(target_path)}", 'success')

        self.log(f"[CONVERT] Processed {len(pops_to_process)} pop groups across {len({p['state'] for p in pops_to_process})} states for {clean_tag}.", 'success')

    @mod_operation
    def add_pop_to_file(self, fpath, state, region_tag, culture, religion, size):
        path=Path(fpath).resolve()
        if not path.is_relative_to(Path(self.mod_path).resolve()): raise ValueError('Population output must be inside the mod.')
        state=self.normalize_state_key(state); tag=identifier(self.format_tag_clean(region_tag))
        culture=identifier(culture); religion=identifier(religion) if religion else ''
        text=path.read_text(encoding='utf-8-sig') if path.exists() else 'POPS = {\n}\n'
        line='\n            create_pop = { culture = '+culture+(' religion = '+religion if religion else '')+f' size = {nonnegative(size)} }}\n'
        states=script_blocks(text,'s:'+state)
        if states:
            b=states[0]; body=text[b['opening']+1:b['end']-1]
            owners=script_blocks(body,'region_state:'+tag,0)
            if owners:
                pos=b['opening']+owners[0]['end']; text=text[:pos]+line+text[pos:]
            else:
                pos=b['end']-1; text=text[:pos]+'\n        region_state:'+tag+' = {'+line+'        }\n'+text[pos:]
        else:
            wrappers=script_blocks(text,'POPS',0)
            if not wrappers: raise ValueError('Population file is missing its POPS wrapper.')
            pos=wrappers[0]['end']-1
            text=text[:pos]+'\n    s:'+state+' = {\n        region_state:'+tag+' = {'+line+'        }\n    }\n'+text[pos:]
        atomic_text(path,text)

    # --- JOURNAL MANAGER LOGIC ---
    def _scan_folder_for_keys(self, rel_path, regex_pattern):
        return self.definition_keys(rel_path)

    def scan_technologies(self):
        return self._scan_folder_for_keys("common/technology/technologies", r"^\s*([a-z0-9_]+)\s*=\s*\{")

    def scan_laws(self):
        return self._scan_folder_for_keys("common/laws", r"^\s*(law_[a-z0-9_]+)\s*=\s*\{")

    def scan_buildings(self):
        return self._scan_folder_for_keys("common/buildings", r"^\s*(building_[a-z0-9_]+)\s*=\s*\{")

    def scan_all_tags(self):
        return self._scan_folder_for_keys("common/country_definitions", r"^\s*([A-Z][A-Z0-9_]{1,4})\s*=\s*\{")

    def add_journal_entry_to_history(self, tag, je_id):
        """Adds a journal entry to the country's history file."""
        self.perform_auto_backup()
        hist_dir = os.path.join(self.mod_path, "common", "history", "countries")
        clean_tag = tag.replace("c:", "").strip()

        target_path = None
        target_content = None

        if not os.path.exists(hist_dir):
            return # Can't add if directory doesn't exist (or empty mod)

        for root, _, files in os.walk(hist_dir):
            for file in files:
                if not file.endswith(".txt"): continue
                path = os.path.join(root, file)
                try:
                    with open(path, 'r', encoding='utf-8-sig') as f: content = f.read()
                except:
                    with open(path, 'r', encoding='utf-8') as f: content = f.read()

                # Look for c:TAG block
                if re.search(r"c:" + re.escape(clean_tag) + r"\b", content):
                    target_path = path; target_content = content; break
            if target_path: break

        if not target_path:
            self.log(f"[WARN] No history file found for {clean_tag}. Journal entry not added to history.", 'warn')
            return

        # Check if already present
        if f"type = {je_id}" in target_content:
            return # Already there

        s, e = self.get_block_range_safe(target_content, f"c:{clean_tag}")
        if s is not None:
            block = target_content[s:e]
            # Insert before closing brace
            new_line = f"\n\t\tadd_journal_entry = {{ type = {je_id} }}"
            new_block = block[:block.rfind('}')] + new_line + "\n\t}"

            new_content = target_content[:s] + new_block + target_content[e:]

            with open(target_path, 'w', encoding='utf-8-sig') as f: f.write(new_content)
            self.log(f"[HISTORY] Added {je_id} to {os.path.basename(target_path)}", 'success')

    EVENT_IMAGE_ALIASES = [
        "europenorthamerica_military_parade", "unspecific_naval_battle",
        "middleeast_battlefield_trenches", "unspecific_armored_train",
        "europenorthamerica_politicians_arguing", "europenorthamerica_courtroom_upheaval",
        "unspecific_ruler_speaking_to_people", "unspecific_signed_contract",
        "europenorthamerica_public_protest", "europenorthamerica_rich_and_poor",
        "unspecific_fire", "unspecific_devastation",
        "europenorthamerica_factory_interior", "unspecific_construction_site",
        "unspecific_busy_port", "unspecific_trains"
    ]

    POPULAR_MODIFIERS = [
    # --- Military (Combat & Training) ---
    ("Military - Army Offense", "unit_offense_mult", "Country"),
    ("Military - Army Defense", "unit_defense_mult", "Country"),
    ("Military - Navy Offense", "unit_navy_offense_mult", "Country"),
    ("Military - Morale Recovery", "unit_morale_recovery_mult", "Country"),
    ("Military - Training Rate", "building_training_rate_mult", "Country"),
    
    # --- Military (Logistics & Prestige) ---
    ("Military - Convoy Capacity", "country_convoys_capacity_add", "Country"),
    ("Military - Convoy Raiding Defense", "country_convoy_damage_taken_mult", "Country"),
    ("Military - Army Prestige (%)", "country_prestige_from_army_power_projection_mult", "Country"),
    ("Military - Navy Prestige (%)", "country_prestige_from_navy_power_projection_mult", "Country"),
    ("Military - Wage Cost (%)", "country_military_wages_mult", "Country"),
    ("Military - Officer Political Strength (%)", "country_officers_pol_str_mult", "Country"),

    # --- Political Capacities (Percentage Based) ---
    ("Political - Bureaucracy (%)", "country_bureaucracy_mult", "Country"),
    ("Political - Authority (%)", "country_authority_mult", "Country"),
    ("Political - Influence (%)", "country_influence_mult", "Country"),
    
    # --- Political Status ---
    ("Political - Prestige (%)", "country_prestige_mult", "Country"),
    ("Political - Legitimacy (Flat)", "country_legitimacy_base_add", "Country"),
    ("Political - Conquest Radicals (%)", "country_radicals_from_conquest_mult", "Country"),

    # --- Economic ---
    ("Economic - Construction Points (Flat)", "country_construction_add", "Country"),
    ("Economic - Minting (Flat)", "country_minting_add", "Country"),
    ("Economic - Loan Interest Rate (%)", "country_loan_interest_rate_mult", "Country"),

    # --- Research ---
    ("Research - Innovation Speed (Flat)", "country_weekly_innovation_add", "Country"),
    ]
    @mod_operation
    def save_journal_entry(self, entry_data):
        self._require_mod()
        key=identifier(entry_data['id'],'Journal ID')
        activation='\n        '.join(entry_data['activation']) or 'always = yes'
        completion='\n        '.join(entry_data['completion']) or 'always = no'
        rewards='\n        '.join(entry_data['rewards'])
        def update_block(body, name, value):
            replacement = name + ' = {\n        ' + value + '\n    }'
            matches = script_blocks(body, name, 0)
            if not matches:
                return body + '\n    ' + replacement + '\n'
            first = matches[0]
            return body[:first['start']] + replacement + body[first['end']:]

        def completion_outcome(body):
            outcomes = script_blocks(body, 'outcome', 0)
            for item in outcomes:
                inner = body[item['opening']+1:item['end']-1]
                if field(inner, 'header') == 'je_standard_completion_header':
                    return item, inner
            return None, ('header = je_standard_completion_header\n'
                          '        effect_header = je_standard_on_completion_header\n'
                          f'        conclusion_desc = {key}_completed_desc\n')

        text=(f'{key} = {{\n    group = je_group_objectives\n    can_revolution_inherit = yes\n'
              f'    is_shown_when_inactive = {{\n        {activation}\n    }}\n'
              f'    possible = {{\n        {activation}\n    }}\n'
              '}\n')
        script_blocks(text)
        self.perform_auto_backup()
        folder=Path(self.mod_path)/'common/journal_entries'
        path=folder/f'{Path(self.mod_path).name}_journals.txt'
        matches=[]
        for candidate in sorted(folder.rglob('*.txt')):
            content=candidate.read_text(encoding='utf-8-sig')
            for block in script_blocks(content,key,0): matches.append((candidate,content,block))
        if len(matches)>1: raise ValueError('Duplicate journal ID; resolve it before editing.')
        if matches:
            path,current,block=matches[0]
            body=current[block['opening']+1:block['end']-1]
        else:
            current=path.read_text(encoding='utf-8-sig') if path.exists() else ''
            current+='\n'+text
            block=script_blocks(current,key,0)[-1]
            body=current[block['opening']+1:block['end']-1]
        for item in reversed(script_blocks(body)):
            if item['depth']==0 and item['key'] in ('complete','on_complete'):
                body=body[:item['start']]+body[item['end']:]
        body = update_block(body, 'possible', activation)
        item, inner = completion_outcome(body)
        inner = update_block(update_block(inner, 'trigger', completion), 'effect', rewards)
        if item:
            body = body[:item['opening']+1] + inner + body[item['end']-1:]
        else:
            body += '\n    outcome = {\n        ' + inner + '    }\n'
        current=current[:block['opening']+1]+body+current[block['end']-1:]
        atomic_text(path,current)
        self._localize(f'{Path(self.mod_path).name}_journals', {key:entry_data['title'],key+'_reason':entry_data['desc'],key+'_completed_desc':entry_data['title']})
        self.log(f'[SUCCESS] Saved journal {key}', 'success')

    @mod_operation
    def save_event(self, namespace, event_id, title, desc, flavor, image, options):
        self.perform_auto_backup()
        # 1. Ensure directory
        evt_dir = os.path.join(self.mod_path, "events")
        os.makedirs(evt_dir, exist_ok=True)

        # 2. Determine file
        # namespace usually determines file: namespace_events.txt
        safe_ns = namespace.strip().lower()
        evt_file = os.path.join(evt_dir, f"{safe_ns}_events.txt")
        existing_event = None
        for candidate in sorted(Path(evt_dir).rglob('*.txt')):
            candidate_text = candidate.read_text(encoding='utf-8-sig')
            matches = script_blocks(candidate_text, event_id, 0)
            if matches:
                if existing_event is not None: raise ValueError('Duplicate event ID; resolve it before editing.')
                existing_event = (candidate, candidate_text, matches[0])
        if existing_event: evt_file = str(existing_event[0])


        # 3. Format Options
        opt_str = ""
        loc_entries = []

        def safe_str(s):
            return quoted(s)[1:-1]

        # Add Title/Desc Loc
        loc_entries.append(f' {event_id}.t:0 "{safe_str(title)}"')
        loc_entries.append(f' {event_id}.d:0 "{safe_str(desc)}"')
        loc_entries.append(f' {event_id}.f:0 "{safe_str(flavor)}"')

        for idx, opt in enumerate(options):
            # Option Name ID: event_id.a, event_id.b, etc.
            suffix = chr(97 + idx) if idx < 26 else f"option_{idx+1}"
            opt_loc_id = f"{event_id}.{suffix}"
            loc_entries.append(f' {opt_loc_id}:0 "{safe_str(opt["name"])}"')

            effects = opt.get('effects', "")

            # Format IG effects
            for ig_eff in opt.get('ig_effects', []):
                ig_key = ig_eff['ig']
                val = ig_eff['value']
                effects += f"\n\t\tig:{ig_key} = {{ add_approval = {{ value = {val} }} }}"

            # Format Modifier effects
            for mod_eff in opt.get('mod_effects', []):
                m_name = mod_eff['name']
                m_dur = mod_eff['duration'] # months
                effects += f"\n\t\tadd_modifier = {{ name = {m_name} months = {m_dur} }}"

            # Format General effects
            for gen_eff in opt.get('general_effects', []):
                effects += f"\n\t\t{gen_eff}"

            opt_str += f"""
    option = {{
        name = {opt_loc_id}
        {effects}
    }}"""

        preserved = ''
        if existing_event:
            _, old_text, old = existing_event
            old_body = old_text[old['opening']+1:old['end']-1]
            if field(old_body, 'type', 'country_event') != 'country_event':
                raise ValueError('The event form supports country events only.')
            for child in reversed(script_blocks(old_body, depth=0)):
                if child['key'] in ('option', 'event_image'):
                    old_body = old_body[:child['start']] + old_body[child['end']:]
            for key in ('type', 'title', 'desc', 'flavor'):
                entry = script_fields(old_body).get(key)
                if entry: old_body = old_body[:entry[1]] + old_body[entry[2]:]
            preserved = old_body

        # 4. Construct Event Block
        # Update event_image to user specifications
        event_content = f"""
{event_id} = {{
    type = country_event
    {preserved}
    title = {event_id}.t
    desc = {event_id}.d
    flavor = {event_id}.f

    event_image = {{
        video = "{image}"
        icon = "gfx/interface/icons/event_icons/event_default.dds"
    }}

{opt_str}
}}
"""

        try:
            current_content = ""
            if os.path.exists(evt_file):
                try:
                    with open(evt_file, 'r', encoding='utf-8-sig') as f: current_content = f.read()
                except:
                    with open(evt_file, 'r', encoding='utf-8') as f: current_content = f.read()

            new_content = current_content

            # Check for existing block to replace
            s, e = self.get_block_range_safe(current_content, event_id)
            if s is not None:
                new_content = current_content[:s] + event_content.strip() + "\n" + current_content[e:]
            else:
                if not current_content.strip():
                    new_content = f"namespace = {namespace}\n\n" + event_content
                else:
                    if f"namespace = {namespace}" not in current_content:
                         new_content = f"namespace = {namespace}\n" + current_content + "\n" + event_content
                    else:
                         new_content = current_content + "\n" + event_content

            with open(evt_file, 'w', encoding='utf-8-sig') as f: f.write(new_content)
        except Exception as e:
            self.log(f"[ERROR] Failed to save Event: {e}", 'error')
            return

        # 5. Localization
        loc_dir = os.path.join(self.mod_path, "localization", "english")
        os.makedirs(loc_dir, exist_ok=True)
        loc_file = os.path.join(loc_dir, f"{safe_ns}_l_english.yml")

        try:
            loc_content = ""
            if os.path.exists(loc_file):
                try:
                    with open(loc_file, 'r', encoding='utf-8-sig') as f: loc_content = f.read()
                except:
                    with open(loc_file, 'r', encoding='utf-8') as f: loc_content = f.read()
            else:
                loc_content = "l_english:\n"

            for entry in loc_entries:
                key = entry.split(':')[0].strip()
                if re.search(r"^\s*" + re.escape(key) + r":", loc_content, re.MULTILINE):
                    loc_content = re.sub(r"^\s*" + re.escape(key) + r":.*", lambda m: entry, loc_content, flags=re.MULTILINE)
                else:
                    loc_content += entry + "\n"

            with open(loc_file, 'w', encoding='utf-8-sig') as f: f.write(loc_content)
        except Exception as e:
            self.log(f"[ERROR] Failed to save Event Localization: {e}", 'error')
            return

        self.log(f"[SUCCESS] Event {event_id} saved to {os.path.basename(evt_file)}", 'success')

    @mod_operation
    def save_modifier(self, mod_name, icon, effects, loc_name, loc_desc):
        self.perform_auto_backup()
        # Save to common/static_modifiers per request
        mod_dir = os.path.join(self.mod_path, "common", "static_modifiers")
        os.makedirs(mod_dir, exist_ok=True)

        mod_name_base = os.path.basename(self.mod_path).replace(" ", "_").lower()
        target_file = os.path.join(mod_dir, f"{mod_name_base}_modifiers.txt")

        # Ensure icon uses forward slashes
        icon = icon.replace("\\", "/")

        content = f"""
{mod_name} = {{
    icon = "{icon}"
    {effects}
}}
"""
        try:
            with open(target_file, 'a', encoding='utf-8-sig') as f:
                f.write(content)
            self.log(f"[SUCCESS] Modifier {mod_name} saved to static_modifiers.", 'success')
        except Exception as e:
            self.log(f"[ERROR] Failed to save Modifier: {e}", 'error')
            return

        # Save Localization
        loc_dir = os.path.join(self.mod_path, "localization", "english")
        os.makedirs(loc_dir, exist_ok=True)
        loc_file = os.path.join(loc_dir, f"{mod_name_base}_modifiers_l_english.yml")

        try:
            loc_content = ""
            if os.path.exists(loc_file):
                with open(loc_file, 'r', encoding='utf-8-sig') as f: loc_content = f.read()
            else:
                loc_content = "l_english:\n"

            # Prepare entries
            # key:0 "Name"
            # key_desc:0 "Desc"
            entries = []
            if loc_name: entries.append(f' {mod_name}:0 "{self.safe_str(loc_name)}"')
            if loc_desc: entries.append(f' {mod_name}_desc:0 "{self.safe_str(loc_desc)}"')

            for entry in entries:
                key = entry.split(':')[0].strip()
                if re.search(r"^\s*" + re.escape(key) + r":", loc_content, re.MULTILINE):
                    loc_content = re.sub(r"^\s*" + re.escape(key) + r":.*", lambda m: entry, loc_content, flags=re.MULTILINE)
                else:
                    loc_content += entry + "\n"

            with open(loc_file, 'w', encoding='utf-8-sig') as f: f.write(loc_content)
        except Exception as e:
            self.log(f"[ERROR] Failed to save Modifier Localization: {e}", 'error')

    def scan_modifiers(self):
        """Scans all modifiers in mod directory."""
        mods = []
        # Check both legacy folder and correct folder
        paths = [
            os.path.join(self.mod_path, "common", "static_modifiers")
        ]

        for mod_dir in paths:
            if not os.path.exists(mod_dir): continue

            for root, _, files in os.walk(mod_dir):
                for file in files:
                    if not file.endswith(".txt"): continue
                    try:
                        with open(os.path.join(root, file), 'r', encoding='utf-8-sig') as f: content = f.read()
                    except:
                        with open(os.path.join(root, file), 'r', encoding='utf-8') as f: content = f.read()

                    # Regex for key = { ... }
                    # Note: this is loose, might match inside blocks, but modifiers are usually top level
                    matches = re.finditer(r"(^|\s)([A-Za-z0-9_.-]+)\s*=\s*\{", content)
                    for m in matches:
                        key = m.group(2)
                        if key not in mods: mods.append(key)
        return sorted(mods)

    def scan_events(self):
        """Scans all events in mod directory."""
        events = []
        evt_dir = os.path.join(self.mod_path, "events")
        if not os.path.exists(evt_dir): return []

        for root, _, files in os.walk(evt_dir):
            for file in files:
                if not file.endswith(".txt"): continue
                try:
                    with open(os.path.join(root, file), 'r', encoding='utf-8-sig') as f: content = f.read()
                except:
                    with open(os.path.join(root, file), 'r', encoding='utf-8') as f: content = f.read()

                cursor = 0
                while True:
                    m = re.search(r"(^|\s)([A-Za-z0-9_.]+)\s*=\s*\{", content[cursor:])
                    if not m: break

                    key = m.group(2)
                    if key.lower() not in ["namespace", "on_action"]:
                        if key not in events: events.append(key)

                    s_idx = cursor + m.end() - 1
                    _, e_idx = self.find_block_content(content, s_idx)

                    if e_idx:
                        cursor = e_idx
                    else:
                        cursor += m.end()
        return sorted(events)

    def scan_journal_entries(self):
        """Scans all journal entries in mod directory."""
        entries = []
        je_dir = os.path.join(self.mod_path, "common", "journal_entries")
        if not os.path.exists(je_dir): return []

        mod_name = os.path.basename(self.mod_path)

        for root, _, files in os.walk(je_dir):
            for file in files:
                if not file.endswith(".txt"): continue
                # Filter to only show entries created in the mod (matching mod name)
                # This assumes standard naming convention [modname]_*.txt
                if not file.lower().startswith(mod_name.lower()): continue

                try:
                    with open(os.path.join(root, file), 'r', encoding='utf-8-sig') as f: content = f.read()
                except:
                    with open(os.path.join(root, file), 'r', encoding='utf-8') as f: content = f.read()

                cursor = 0
                while True:
                    m = re.search(r"(^|\s)([A-Za-z0-9_]+)\s*=\s*\{", content[cursor:])
                    if not m: break

                    key = m.group(2)
                    if key not in entries: entries.append(key)

                    s_idx = cursor + m.end() - 1
                    _, e_idx = self.find_block_content(content, s_idx)

                    if e_idx:
                        cursor = e_idx
                    else:
                        cursor += m.end()
        return sorted(entries)

    def get_journal_entry_data(self, je_id):
        je_dir = os.path.join(self.mod_path, "common", "journal_entries")
        if not os.path.exists(je_dir): return None

        for root, _, files in os.walk(je_dir):
            for file in files:
                if not file.endswith(".txt"): continue
                path = os.path.join(root, file)
                try:
                    with open(path, 'r', encoding='utf-8-sig') as f: content = f.read()
                except:
                    with open(path, 'r', encoding='utf-8') as f: content = f.read()

                s, e = self.get_block_range_safe(content, je_id)
                if s is not None:
                    block = content[s:e]
                    data = {"id": je_id, "activation": [], "completion": [], "rewards": []}

                    def extract_lines(key):
                        m = re.search(key + r"\s*=\s*\{", block)
                        if m:
                            bs, be = self.find_block_content(block, m.end() - 1)
                            if bs is not None:
                                inner = block[bs+1:be-1]
                                return [line.strip() for line in inner.split('\n') if line.strip() and not line.strip().startswith('#')]
                        return []

                    data["activation"] = extract_lines("possible")
                    data["completion"] = extract_lines("complete")
                    data["rewards"] = extract_lines("on_complete")

                    for outcome in script_blocks(block, 'outcome', 1):
                        inner = block[outcome['opening']+1:outcome['end']-1]
                        if field(inner, 'header') == 'je_standard_completion_header':
                            for name, target in [('trigger', 'completion'), ('effect', 'rewards')]:
                                parts = script_blocks(inner, name, 0)
                                value = inner[parts[0]['opening']+1:parts[0]['end']-1] if parts else ''
                                data[target] = [line.strip() for line in value.splitlines() if line.strip()]
                            break

                    loc_name, loc_desc = self.get_je_localization(je_id)
                    data["title"] = loc_name
                    data["desc"] = loc_desc

                    return data
        return None

    def get_je_localization(self, je_id):
        return self.get_loc_text(je_id),self.get_loc_text(je_id+'_reason')

    def get_event_data(self, event_id):
        for path in sorted((Path(self.mod_path)/'events').rglob('*.txt')):
            text=path.read_text(encoding='utf-8-sig');matches=script_blocks(text,event_id,0)
            if not matches:continue
            b=matches[0];body=text[b['opening']+1:b['end']-1]
            data=dict(id=event_id,namespace=event_id.rsplit('.',1)[0],options=[],image='')
            for key in ('title','desc','flavor'):data[key]=self.get_loc_text(field(body,key))
            for child in script_blocks(body,depth=0):
                raw=body[child['opening']+1:child['end']-1]
                if child['key']=='event_image':data['image']=field(raw,'video')
                elif child['key']=='option':
                    name=script_fields(raw).get('name')
                    effects=raw[:name[1]]+raw[name[2]:] if name else raw
                    data['options'].append(dict(name=self.get_loc_text(field(raw,'name')),effects=effects,ig_effects=[],mod_effects=[],general_effects=[]))
            return data
        return None

    def get_loc_text(self, key):
        result=key
        roots=([Path(self.vanilla_path)/'game'] if self.vanilla_path else [])+([Path(self.mod_path)] if self.mod_path else [])
        for root in roots:
            folder=root/'localization/english'
            if not folder.exists():continue
            for path in sorted(folder.rglob('*.yml'),key=lambda p:('replace' in p.parts,p.as_posix())):
                text=path.read_text(encoding='utf-8-sig')
                match=re.search(r'^\s*'+re.escape(key)+r':\d*\s*"((?:\\.|[^"\\])*)"',text,re.M)
                if match:result=re.sub(r'\\([n"\\])',lambda m:'\n' if m[1]=='n' else m[1],match[1])
        return result

    # --- BUILDING LOGIC ---
    def scan_history_building_types(self):
        """Scans history/buildings for all used building types."""
        types = set()
        paths = []
        if self.mod_path: paths.append(os.path.join(self.mod_path, "common/history/buildings"))

        for p in paths:
            if not os.path.exists(p): continue
            for root, _, files in os.walk(p):
                for file in files:
                    if not file.endswith(".txt"): continue
                    try:
                         with open(os.path.join(root, file), 'r', encoding='utf-8-sig') as f: content = f.read()
                    except:
                         with open(os.path.join(root, file), 'r', encoding='utf-8') as f: content = f.read()

                    matches = re.findall(r'building\s*=\s*"([^"]+)"', content)
                    # Strip building_ prefix
                    clean_matches = [m.replace("building_", "") for m in matches]
                    types.update(clean_matches)
        return sorted(list(types))

    def _scan_file_for_buildings(self, fpath, clean_state, buildings_list, is_mod):
        try:
             with open(fpath, 'r', encoding='utf-8-sig') as f: content = f.read()
        except:
             with open(fpath, 'r', encoding='utf-8') as f: content = f.read()

        # Search s:STATE
        cursor = 0
        while True:
            s, e = self.get_block_range_safe(content, f"s:{clean_state}", cursor)
            if s is None: break

            state_block = content[s:e]

            # Search region_state:TAG inside state_block
            rs_cursor = 0
            while True:
                m_rs = re.search(r"region_state:([A-Za-z0-9_]+)\s*=\s*\{", state_block[rs_cursor:])
                if not m_rs: break

                tag = m_rs.group(1)
                rs_s, rs_e = self.find_block_content(state_block, rs_cursor + m_rs.end() - 1)

                if rs_s:
                    rs_inner = state_block[rs_s:rs_e]

                    # Search create_building inside region_state
                    cb_cursor = 0
                    while True:
                        m_cb = re.search(r"create_building\s*=\s*\{", rs_inner[cb_cursor:])
                        if not m_cb: break

                        cb_s, cb_e = self.find_block_content(rs_inner, cb_cursor + m_cb.end() - 1)

                        if cb_s:
                            cb_inner = rs_inner[cb_s:cb_e]

                            b_type_m = re.search(r'building\s*=\s*"([^"]+)"', cb_inner)
                            # Try finding 'level' first, then 'levels' (from ownership)
                            level_m = re.search(r'level\s*=\s*(\d+)', cb_inner)
                            levels_m = re.search(r'levels\s*=\s*(\d+)', cb_inner)

                            b_type = b_type_m.group(1) if b_type_m else "Unknown"

                            # Check for override owner (Legacy 'owner' or new 'add_ownership')
                            owner_m = re.search(r"owner\s*=\s*c:([A-Za-z0-9_]+)", cb_inner)

                            # Check add_ownership block
                            ownership_owner = None
                            ao_m = re.search(r"add_ownership\s*=\s*\{", cb_inner)
                            if ao_m:
                                ao_s, ao_e = self.find_block_content(cb_inner, ao_m.end() - 1)
                                if ao_s:
                                    ao_inner = cb_inner[ao_s:ao_e]
                                    c_m = re.search(r"country\s*=\s*c:([A-Za-z0-9_]+)", ao_inner)
                                    if c_m: ownership_owner = c_m.group(1)

                            final_owner = ownership_owner if ownership_owner else (owner_m.group(1) if owner_m else tag)

                            level = 1
                            if level_m:
                                level = int(level_m.group(1))
                            elif levels_m:
                                level = int(levels_m.group(1))

                            abs_start = s + rs_s + cb_cursor + m_cb.start()
                            abs_end = s + rs_s + cb_e

                            buildings_list.append({
                                "file": fpath,
                                "is_mod": is_mod,
                                "state": clean_state,
                                "owner": final_owner,
                                "region_tag": tag,
                                "type": b_type,
                                "level": level,
                                "indices": {
                                    "start": abs_start,
                                    "end": abs_end
                                }
                            })

                            cb_cursor = cb_e
                        else:
                            cb_cursor += 1
                    rs_cursor = rs_e
                else:
                    rs_cursor += 1

            cursor = e

    def scan_state_buildings(self, state_name):
        state=self.normalize_state_key(state_name); result=[]
        for path in self.effective_files('common/history/buildings'):
            text=path.read_text(encoding='utf-8-sig')
            for st in script_blocks(text,'s:'+state):
                start=st['opening']+1; body=text[start:st['end']-1]
                for owner in script_blocks(body,depth=0):
                    if not owner['key'] or not owner['key'].startswith('region_state:'): continue
                    tag=owner['key'].split(':',1)[1]; offset=start+owner['opening']+1; inner=text[offset:start+owner['end']-1]
                    for building in script_blocks(inner,'create_building',0):
                        a=offset+building['start']; b=offset+building['end']; raw=text[a:b]
                        content=inner[building['opening']+1:building['end']-1]
                        owners=[]
                        for ob in script_blocks(content,'add_ownership',0):
                            ownership=content[ob['opening']+1:ob['end']-1]
                            for item in script_blocks(ownership,depth=0):
                                fields=ownership[item['opening']+1:item['end']-1]
                                owners.append((field(fields,'country').removeprefix('c:'),int(field(fields,'levels','0'))))
                        level=int(field(content,'level',str(sum(v for _,v in owners) or 1)))
                        owner_tags={t for t,v in owners if v}
                        result.append(dict(file=str(path),is_mod=path.resolve().is_relative_to(Path(self.mod_path).resolve()),state=state,region_tag=tag,
                            type=field(content,'building'),level=level,owner=next(iter(owner_tags)) if len(owner_tags)==1 else 'MIXED' if owner_tags else tag,
                            indices=dict(start=a,end=b),snapshot=raw))
        return result

    @mod_operation
    def save_state_building(self, building_entry, new_level=None, new_land_owner=None, new_building_owner=None, delete=False):
        """Updates or deletes a building entry."""
        self.perform_auto_backup()
        fpath = building_entry['file']
        target_path = fpath

        # Copy to mod if vanilla
        if self.vanilla_path and fpath.startswith(self.vanilla_path):
            mod_rel = os.path.relpath(fpath, os.path.join(self.vanilla_path, "game"))
            target_path = os.path.join(self.mod_path, mod_rel)
            os.makedirs(os.path.dirname(target_path), exist_ok=True)
            if not os.path.exists(target_path):
                shutil.copy2(fpath, target_path)

        try:
            with open(target_path, 'r', encoding='utf-8-sig') as f: content = f.read()
        except:
            with open(target_path, 'r', encoding='utf-8') as f: content = f.read()

        s = building_entry['indices']['start']
        e = building_entry['indices']['end']

        if 'snapshot' not in building_entry or content[s:e] != building_entry['snapshot']:
            raise ValueError('Building changed since loading. Reload before editing.')

        if delete:
            # Remove the block
            content = content[:s].rstrip() + content[e:]
            self.log(f"[BUILDING] Removed {building_entry['type']} from {os.path.basename(target_path)}", 'success')
            with open(target_path, 'w', encoding='utf-8-sig') as f: f.write(content)
            return

        # --- UPDATE LOGIC ---
        # 1. Extract block
        block = content[s:e]

        # 2. Check if moving region state (Land Owner)
        # If new_land_owner provided and differs from stored region_tag
        moving_region = False
        if new_land_owner:
            clean_new_land = self.format_tag_clean(new_land_owner)
            current_region = building_entry.get("region_tag", "")
            if clean_new_land != current_region:
                moving_region = True

        # Ownership levels represent shares, not three independent building totals.
        if new_level is not None:
            new_level = nonnegative(new_level, 'Building level')
            opening = block.find('{')
            body = block[opening+1:-1]
            shares = []
            for ownership in script_blocks(body, 'add_ownership', 0):
                offset = ownership['opening']+1
                inner = body[offset:ownership['end']-1]
                for owner in script_blocks(inner, depth=0):
                    start = offset+owner['opening']+1
                    end = offset+owner['end']-1
                    owner_body = body[start:end]
                    shares.append((start,end,owner_body,int(field(owner_body,'levels','0'))))
            if shares:
                values = apportion(new_level,[item[3] for item in shares])
                for item,value in reversed(list(zip(shares,values))):
                    a,b,raw,_ = item
                    body = body[:a]+put_field(raw,'levels',value)+body[b:]
                if 'level' in script_fields(body): body = put_field(body,'level',new_level)
            else: body = put_field(body,'level',new_level)
            block = block[:opening+1]+body+'}'

        # 4. Update Ownership (Building Owner)
        if new_building_owner:
            clean_new_b_owner = self.format_tag_clean(new_building_owner)
            target_land_owner = clean_new_land if moving_region else building_entry.get("region_tag", "")

            # Remove existing ownership blocks/lines
            block = re.sub(r"\s*owner\s*=\s*c:[A-Za-z0-9_]+", "", block)
            # Remove add_ownership block (complex due to braces)
            # We use a pattern that attempts to match add_ownership = { ... }
            # Since regex is not great for nested braces, we assume standard formatting or simple nesting
            # Actually, parsing it out with find_block_content is safer, but we are editing a string.
            # Let's try to remove it if it exists.

            # Simple removal strategy: Use get_block_range_safe on the block string?
            # No, get_block_range_safe works on full content.
            # Let's use logic similar to get_block_range_safe but on 'block' string
            while True:
                ao_m = re.search(r"add_ownership\s*=\s*\{", block)
                if not ao_m: break
                ao_s, ao_e = self.find_block_content(block, ao_m.end() - 1)
                if ao_s:
                    # Remove it including preceding whitespace/newline if possible
                    # This is simple string slicing
                    # Check for preceding whitespace/newline
                    prefix = block[:ao_m.start()]
                    suffix = block[ao_e:]
                    block = prefix.rstrip() + suffix
                else:
                    break # Should not happen

            # Add new ownership if needed (Foreign)
            if clean_new_b_owner != target_land_owner:
                # Use add_ownership syntax
                level_val = new_level if new_level is not None else building_entry['level']

                # Retrieve state name from building entry
                current_state = building_entry.get("state", "")

                ownership_block = self.get_ownership_block(building_entry['type'], clean_new_b_owner, level_val, current_state)

                # Insert before closing brace
                last_brace = block.rfind('}')
                block = block[:last_brace] + ownership_block + "\n\t\t\t}"

        # 5. Apply Changes
        if moving_region:
            # Delete old block from file first
            content_without_old = content[:s].rstrip() + content[e:]

            # Now we need to insert 'block' into the new region_state
            # We can reuse add_state_building logic or replicate insertion
            # Replicating insertion is safer to avoid re-reading file immediately

            # Find new location in content_without_old
            # We need to find s:STATE -> region_state:NEW_TAG
            # We can use logic similar to add_state_building but working on string

            # We need 'clean_state'
            clean_state = building_entry['state']

            s_idx, e_idx = self.get_block_range_safe(content_without_old, f"s:{clean_state}")
            if s_idx is not None:
                state_block = content_without_old[s_idx:e_idx]

                # Search for region_state:NEW_TAG
                rs_cursor = 0
                found_rs = False
                rs_insert_idx = -1

                while True:
                    m_rs = re.search(r"region_state:([A-Za-z0-9_]+)\s*=\s*\{", state_block[rs_cursor:])
                    if not m_rs: break

                    curr_tag = m_rs.group(1)
                    rs_s, rs_e = self.find_block_content(state_block, rs_cursor + m_rs.end() - 1)

                    if curr_tag == clean_new_land:
                        found_rs = True
                        rs_insert_idx = rs_e - 1
                        break

                    rs_cursor = rs_e

                if found_rs:
                    # Insert into existing region_state
                    new_state_block = state_block[:rs_insert_idx] + "\n" + block + state_block[rs_insert_idx:]
                    content = content_without_old[:s_idx] + new_state_block + content_without_old[e_idx:]
                else:
                    # Create new region_state
                    new_rs = f"""
\t\tregion_state:{clean_new_land}={{
{block}
\t\t}}"""
                    # Insert at end of state block
                    last_sb_brace = state_block.rfind('}')
                    new_state_block = state_block[:last_sb_brace] + new_rs + "\n\t}"
                    content = content_without_old[:s_idx] + new_state_block + content_without_old[e_idx:]
            else:
                # State not found? Should not happen since we just read it.
                # Unless file is corrupted or logic fail.
                # Fallback: append
                self.log("Error finding state block for move, aborting move.", "error")
                return

            self.log(f"[BUILDING] Moved {building_entry['type']} to {clean_new_land}", 'success')

        else:
            # Just replace in place
            content = content[:s] + block + content[e:]
            self.log(f"[BUILDING] Updated {building_entry['type']}", 'success')

        with open(target_path, 'w', encoding='utf-8-sig') as f: f.write(content)

    @mod_operation
    def add_state_building(self, state_name, land_owner_tag, building_owner_tag, building_type, level):
        """Adds a new building to a state."""
        self.perform_auto_backup()
        clean_state = self.format_state_clean(state_name)
        clean_land_owner = land_owner_tag.replace("c:", "").strip()
        clean_building_owner = building_owner_tag.replace("c:", "").strip()

        fpath = None
        target_content = None

        # Check Mod First
        if self.mod_path:
            mod_b = os.path.join(self.mod_path, "common/history/buildings")
            if os.path.exists(mod_b):
                for root, _, files in os.walk(mod_b):
                    for file in files:
                        if not file.endswith(".txt"): continue
                        curr_path = os.path.join(root, file)
                        try:
                            with open(curr_path, 'r', encoding='utf-8-sig') as f: c = f.read()
                        except:
                            with open(curr_path, 'r', encoding='utf-8') as f: c = f.read()

                        if f"s:{clean_state}" in c:
                            fpath = curr_path
                            target_content = c
                            break
                    if fpath: break

        if fpath:
            target_path = fpath
        else:
            target_path = os.path.join(self.mod_path, "common/history/buildings/99_mod_buildings.txt")
            os.makedirs(os.path.dirname(target_path), exist_ok=True)
            if not os.path.exists(target_path):
                with open(target_path, 'w', encoding='utf-8-sig') as f: f.write("BUILDINGS = {\n}")
            target_content = "BUILDINGS = {\n}"

        # Re-read
        try:
            with open(target_path, 'r', encoding='utf-8-sig') as f: target_content = f.read()
        except:
            with open(target_path, 'r', encoding='utf-8') as f: target_content = f.read()

        # Construct Building Block
        ownership_block = self.get_ownership_block(building_type, clean_building_owner, level, clean_state)

        new_b_block = f"""
\t\t\tcreate_building = {{
\t\t\t\tbuilding = "{building_type}"
\t\t\t\treserves = 1
\t\t\t\tactivate_production_methods = {{ }}{ownership_block}
\t\t\t}}"""

        s, e = self.get_block_range_safe(target_content, f"s:{clean_state}")

        if s is not None:
            state_block = target_content[s:e]

            rs_cursor = 0
            found_rs = False
            rs_insert_idx = -1

            while True:
                m_rs = re.search(r"region_state:([A-Za-z0-9_]+)\s*=\s*\{", state_block[rs_cursor:])
                if not m_rs: break

                curr_tag = m_rs.group(1)
                rs_s, rs_e = self.find_block_content(state_block, rs_cursor + m_rs.end() - 1)

                if curr_tag == clean_land_owner:
                    found_rs = True
                    rs_insert_idx = rs_e - 1
                    break

                rs_cursor = rs_e

            if found_rs:
                new_state_block = state_block[:rs_insert_idx] + new_b_block + state_block[rs_insert_idx:]
                target_content = target_content[:s] + new_state_block + target_content[e:]
            else:
                new_rs = f"""
\t\tregion_state:{clean_land_owner}={{
{new_b_block}
\t\t}}"""
                new_state_block = state_block[:state_block.rfind('}')] + new_rs + "\n\t}"
                target_content = target_content[:s] + new_state_block + target_content[e:]
        else:
            new_entry = f"\n\ts:{clean_state}={{\n\t\tregion_state:{clean_land_owner}={{\n{new_b_block}\n\t\t}}\n\t}}"
            bs, be = self.get_block_range_safe(target_content, "BUILDINGS")
            if bs is not None:
                target_content = target_content[:be-1] + new_entry + "\n}" + target_content[be:]
            else:
                target_content += f"\nBUILDINGS = {{{new_entry}\n}}"

        with open(target_path, 'w', encoding='utf-8-sig') as f: f.write(target_content)
        self.log(f"[BUILDING] Added {building_type} to {clean_state} (Land: {clean_land_owner}, Owner: {clean_building_owner})", 'success')

    def cleanup_power_bloc_membership(self, tag):
        """Removes tag from power blocs or deletes bloc if leader."""
        clean_tag = tag.replace("c:", "").strip()
        all_blocs = self.get_all_power_blocs()

        for bloc in all_blocs:
            leader = bloc['tag']
            clean_leader = leader.replace("c:", "").strip()

            if clean_leader.upper() == clean_tag.upper():
                self.log(f"[PB] {clean_tag} is leader of bloc {bloc['name']}. Deleting bloc...", 'warn')
                self.remove_power_bloc(leader)
            else:
                # Check membership
                data = self.get_power_bloc_data(leader)
                if not data: continue

                members = data.get('members', [])
                original_len = len(members)
                # Filter out the annexed tag (handle c: prefix variants)
                new_members = [
                    m for m in members
                    if m.replace("c:", "").strip().upper() != clean_tag.upper()
                ]

                if len(new_members) < original_len:
                    self.log(f"[PB] Removing {clean_tag} from bloc {bloc['name']} (Leader: {leader})", 'info')
                    data['members'] = new_members
                    self.save_power_bloc_data(leader, data)

    @mod_operation
    def perform_annexation_cleanup(self, old_tag, new_tag, transferred_states):
        self.log(f"--- Performing Annexation Cleanup: {old_tag} -> {new_tag} ---", 'info')
        self.cleanup_trade_routes(old_tag)
        self.cleanup_treaties(old_tag)
        self.clean_annexed_relations(old_tag)
        self.log(f"[WARN] Review company-owned buildings after annexing {old_tag}. Company ownership requires an existing company in its home country.", 'warn')
        self.update_military_formations(old_tag, new_tag)
        self.cleanup_power_bloc_membership(old_tag)
        self.clean_transferred_state_references(transferred_states)
        self.sanitize_buildings(old_tag, new_tag, transferred_states)
        self.clean_lobbies_for_annexed(old_tag)

    def clean_lobbies_for_annexed(self, tag):
        """Scans lobbies file and removes any lobby for or targeting the annexed tag."""
        lobby_file = os.path.join(self.mod_path, "common/history/lobbies/00_lobbies.txt")
        if not os.path.exists(lobby_file): return

        clean_tag = tag.replace("c:", "").strip()

        try:
            with open(lobby_file, 'r', encoding='utf-8-sig') as f: content = f.read()
        except:
            with open(lobby_file, 'r', encoding='utf-8') as f: content = f.read()

        changed = False

        # 1. Remove entire lobby blocks for the annexed tag (c:TAG = { ... })
        cursor = 0
        while True:
            # Search for c:TAG ?= { or c:TAG = {
            m = re.search(r"(?:^|\s)c:" + re.escape(clean_tag) + r"\s*(\?=|:|=)?\s*\{", content[cursor:], re.IGNORECASE)
            if not m: break

            s_idx = cursor + m.start()
            # find block content from start of brace
            brace_pos = cursor + m.end() - 1
            _, e_idx = self.find_block_content(content, brace_pos)

            if e_idx:
                # Remove the block
                content = content[:s_idx] + content[e_idx:]
                changed = True
                # Reset cursor to s_idx to continue searching from deletion point
                cursor = s_idx
            else:
                cursor = brace_pos + 1

        # 2. Remove specific lobby definitions targeting the annexed tag (target = c:TAG)
        # We need to iterate through all country blocks
        cursor = 0
        while True:
            # Find any country block c:TAG = {
            m = re.search(r"(?:^|\s)c:([A-Za-z0-9_]+)\s*(\?=|:|=)?\s*\{", content[cursor:], re.IGNORECASE)
            if not m: break

            country_tag_start = cursor + m.start()
            brace_pos = cursor + m.end() - 1
            s_inner, e_inner = self.find_block_content(content, brace_pos)

            if s_inner:
                block_inner = content[s_inner+1:e_inner-1]

                # Check if this block contains a lobby targeting our tag
                # Regex for: create_political_lobby = { ... target = c:TAG ... }
                # We need to parse individual create_political_lobby blocks

                new_inner_parts = []
                inner_cursor = 0
                inner_changed = False

                while True:
                    lm = re.search(r"create_political_lobby\s*=\s*\{", block_inner[inner_cursor:])
                    if not lm:
                        new_inner_parts.append(block_inner[inner_cursor:])
                        break

                    lobby_start = inner_cursor + lm.start()
                    new_inner_parts.append(block_inner[inner_cursor:lobby_start])

                    l_brace = lobby_start + lm.end() - 1
                    ls, le = self.find_block_content(block_inner, l_brace)

                    if ls:
                        lobby_content = block_inner[ls+1:le-1]

                        # Check target
                        if re.search(r"target\s*=\s*c:" + re.escape(clean_tag) + r"\b", lobby_content, re.IGNORECASE):
                            self.log(f"[LOBBY] Removing lobby in owner block targeting {clean_tag}")
                            inner_changed = True
                            # Skip adding this lobby block
                        else:
                            new_inner_parts.append(block_inner[lobby_start:le])

                        inner_cursor = le
                    else:
                        new_inner_parts.append(block_inner[lobby_start:])
                        break

                if inner_changed:
                    new_inner_block = "".join(new_inner_parts)
                    content = content[:s_inner+1] + new_inner_block + content[e_inner-1:]
                    changed = True
                    # Recalculate e_idx based on length change
                    diff = len(new_inner_block) - len(block_inner)
                    cursor = e_inner + diff
                else:
                    cursor = e_inner
            else:
                cursor = brace_pos + 1

        if changed:
            with open(lobby_file, 'w', encoding='utf-8-sig') as f: f.write(content)
            self.log(f"[LOBBY] Cleaned up lobbies associated with {clean_tag}", 'success')

# =============================================================================
#  GUI IMPLEMENTATION
    def scan_military_formations(self, tag):
        tag = self.format_tag_clean(tag)
        formations = []
        folder = Path(self.mod_path)/'common/history/military_formations'
        if not self.mod_path or not folder.is_dir(): return []
        for path in sorted(folder.rglob('*.txt')):
            text = path.read_text(encoding='utf-8-sig')
            fingerprint = hashlib.sha256(text.encode()).hexdigest()
            for country in script_blocks(text, 'c:'+tag):
                body_start = country['opening']+1
                body = text[body_start:country['end']-1]
                for form in script_blocks(body, 'create_military_formation', 0):
                    inner = body[form['opening']+1:form['end']-1]
                    records, units = [], {}
                    for unit in script_blocks(inner, depth=0):
                        if unit['key'] not in ('ship','combat_unit'): continue
                        ubody = inner[unit['opening']+1:unit['end']-1]
                        key = field(ubody, 'type')
                        count = nonnegative(field(ubody, 'count','1'))
                        records.append(dict(key=key, count=count, start=unit['start'], end=unit['end'], opening=unit['opening'], body=ubody))
                        units[key] = units.get(key,0)+count
                    formations.append(dict(file=str(path), tag=tag, fingerprint=fingerprint,
                        start=body_start+form['start'], end=body_start+form['end'], opening=body_start+form['opening'],
                        id=field(inner,'save_scope_as',f'__offset_{body_start+form["start"]}'),
                        name=field(inner,'name','Unnamed formation'), type=field(inner,'type','army'),
                        hq=field(inner,'hq_region'), units=units, records=records,
                        name_token=script_fields(inner).get('name',('"Unnamed formation"',0,0))[0]))
        return formations

    @mod_operation
    def delete_military_formation(self, file_path, scope_id):
        text = Path(file_path).read_text(encoding='utf-8-sig')
        tags = {b['key'][2:] for b in script_blocks(text) if b['key'] and b['key'].startswith('c:')}
        found = [f for tag in tags for f in self.scan_military_formations(tag) if Path(f['file']).resolve()==Path(file_path).resolve() and f['id']==scope_id]
        if len(found)!=1: raise ValueError('Formation ID is missing or ambiguous. Reload the list.')
        return self.delete_formation_ui(found[0])

    @mod_operation
    def delete_formation_ui(self, formation_data):
        path, text = self._formation_snapshot(formation_data)
        self.perform_auto_backup()
        atomic_text(path,text[:formation_data['start']]+text[formation_data['end']:])
        if not formation_data['id'].startswith('__offset_'):
            self.disconnect_commanders_from_formations([formation_data['id']])
        return True

    @mod_operation
    def save_military_formation(self, formation_data, new_name, new_units):
        data = formation_data
        path, text = self._formation_snapshot(data)
        if not new_name.strip(): raise ValueError('A formation name is required.')
        if set(new_units) != set(data['units']): raise ValueError('Reload the exact unit types before editing.')
        counts = {key: nonnegative(value) for key,value in new_units.items()}
        if not sum(counts.values()): raise ValueError('Use Delete Formation to remove an empty formation.')
        inner = text[data['opening']+1:data['end']-1]
        edits = []
        for key, total in counts.items():
            records = [r for r in data['records'] if r['key']==key]
            # Preserve each state, ship modification, name and unknown field, even with mixed unit types.
            allocated = apportion(total,[r['count'] for r in records]) if sum(r['count'] for r in records) else [total]+[0]*(len(records)-1)
            for record, count in zip(records,allocated):
                if count == record['count']: continue
                replacement = '' if count == 0 else inner[record['start']:record['opening']+1]+put_field(record['body'],'count',count)+'}'
                edits.append((record['start'],record['end'],replacement))
        for a,b,replacement in sorted(edits,reverse=True): inner=inner[:a]+replacement+inner[b:]
        if new_name != data['name']: inner=put_field(inner,'name',quoted(new_name))
        self.perform_auto_backup()
        atomic_text(path,text[:data['opening']+1]+inner+text[data['end']-1:])
        return True
# =============================================================================

class DemographicsMixer(ttk.Frame):
    def __init__(self, parent, on_change_callback=None):
        super().__init__(parent)
        self.on_change = on_change_callback
        self.rows = []
        self.initial_data = []
        self.weights_snapshot = {}
        self.total_pop = 0
        self.is_updating = False

        # Header
        h_frame = ttk.Frame(self)
        h_frame.pack(fill=tk.X, pady=5)
        ttk.Label(h_frame, text="Group (Culture/Religion)", width=30).pack(side=tk.LEFT, padx=5)
        ttk.Label(h_frame, text="Percentage", width=20).pack(side=tk.LEFT, padx=5)
        ttk.Label(h_frame, text="Population", width=15).pack(side=tk.LEFT, padx=5)
        ttk.Label(h_frame, text="Lock").pack(side=tk.LEFT, padx=5)
        ttk.Button(h_frame, text="Reset", command=self.reset).pack(side=tk.RIGHT, padx=5)

        # Scrollable Area
        self.canvas = tk.Canvas(self, height=200) # Slightly reduced height
        self.scrollbar = ttk.Scrollbar(self, orient="vertical", command=self.canvas.yview)
        self.scroll_frame = ttk.Frame(self.canvas)

        self.scroll_frame.bind(
            "<Configure>",
            lambda e: self.canvas.configure(scrollregion=self.canvas.bbox("all"))
        )

        self.win_id = self.canvas.create_window((0, 0), window=self.scroll_frame, anchor="nw")
        self.canvas.bind("<Configure>", self.on_canvas_configure)
        self.canvas.configure(yscrollcommand=self.scrollbar.set)

        self.canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        self.scrollbar.pack(side=tk.RIGHT, fill=tk.Y)

    def on_canvas_configure(self, event):
        self.canvas.itemconfig(self.win_id, width=event.width)

    def clear(self):
        for w in self.scroll_frame.winfo_children():
            w.destroy()
        self.rows = []

    def load_data(self, demographics, total_pop):
        self.clear()
        self.total_pop = total_pop
        # Deep copy for reset (using list comp since copy isn't always available on dicts depending on import, but simple dict copy is fine)
        self.initial_data = [d.copy() for d in demographics]

        for d in demographics:
            # Skip 0% rows (ignoring existing 0s)
            pct = d.get('percent', 0)
            size = d.get('size', 0)
            # Filter 0 population if requested (percent > 0 OR size > 0)
            if pct > 0 or size > 0:
                self.add_row(d.get('culture', ''), d.get('religion', ''), pct)

    def reset(self):
        # Restore initial data
        # We need to pass a copy of initial_data so subsequent modifications don't corrupt the master reset state
        restored = [d.copy() for d in self.initial_data]
        self.load_data(restored, self.total_pop)
        if self.on_change: self.on_change()

    def set_total_pop(self, total):
        self.total_pop = total
        self.update_calc_labels()

    def add_row(self, cul, rel, percent):
        idx = len(self.rows)
        row_f = ttk.Frame(self.scroll_frame)
        row_f.pack(fill=tk.X, pady=2)

        label_text = f"{cul}"
        if rel: label_text += f" / {rel}"

        ttk.Label(row_f, text=label_text, width=30).pack(side=tk.LEFT, padx=5)

        # Slider
        # Using Scale with IntVar for integer steps
        var_pct = tk.IntVar(value=int(round(percent)))
        scale = tk.Scale(row_f, from_=0, to=100, orient=tk.HORIZONTAL, variable=var_pct, showvalue=1, length=150)
        scale.pack(side=tk.LEFT, padx=5)

        # Bind event
        scale.bind("<ButtonPress-1>", lambda e, i=idx: self.snapshot_weights(i))
        scale.bind("<ButtonRelease-1>", lambda e, i=idx: self.on_slider_release(i))
        scale.bind("<B1-Motion>", lambda e, i=idx: self.on_slider_move(i))

        # Calc Label
        lbl_calc = ttk.Label(row_f, text="0", width=15)
        lbl_calc.pack(side=tk.LEFT, padx=5)

        # Lock
        var_lock = tk.BooleanVar(value=False)
        chk = ttk.Checkbutton(row_f, variable=var_lock)
        chk.pack(side=tk.LEFT, padx=5)

        # Delete btn
        btn_del = ttk.Button(row_f, text="X", width=3, command=lambda i=idx: self.delete_row(i))
        btn_del.pack(side=tk.LEFT, padx=5)

        row_data = {
            "culture": cul,
            "religion": rel,
            "var_pct": var_pct,
            "lbl_calc": lbl_calc,
            "var_lock": var_lock,
            "frame": row_f,
            "scale": scale
        }
        self.rows.append(row_data)
        self.update_calc_labels()

    def delete_row(self, idx):
        if 0 <= idx < len(self.rows):
            self.rows[idx]["frame"].destroy()
            self.rows.pop(idx)
            # Rebind indices logic is complex with lambdas.
            # Easiest is to regenerate from data, but sliders might lose state if not careful.
            # But here we just removed one.
            # The indices in lambdas are stale.
            # We MUST reload or update lambdas.
            # Simplest: get data, clear, reload.
            data = self.get_data()
            self.load_data(data, self.total_pop)

    def snapshot_weights(self, idx):
        # Capture current weights before dragging starts to maintain weighted distribution
        self.weights_snapshot = {}
        for i, r in enumerate(self.rows):
            self.weights_snapshot[i] = r["var_pct"].get()

    def on_slider_move(self, idx):
        self.rebalance(idx)

    def on_slider_release(self, idx):
        self.rebalance(idx)
        self.weights_snapshot = {} # Clear snapshot on release
        if self.on_change: self.on_change()

    def rebalance(self, source_idx):
        if self.is_updating: return
        self.is_updating = True

        if source_idx >= len(self.rows):
             self.is_updating = False
             return

        # 1. Calculate residual needed for others
        target_val = self.rows[source_idx]["var_pct"].get()
        others = [i for i in range(len(self.rows)) if i != source_idx]
        unlocked_others = [i for i in others if not self.rows[i]["var_lock"].get()]
        locked_others = [i for i in others if self.rows[i]["var_lock"].get()]

        sum_locked = sum(self.rows[i]["var_pct"].get() for i in locked_others)

        # Max allowed for source + unlocked_others = 100 - sum_locked
        available_pool = 100 - sum_locked

        # Clamp target_val if it exceeds available
        if target_val > available_pool:
            target_val = available_pool
            self.rows[source_idx]["var_pct"].set(target_val)

        # Residual to distribute among unlocked others
        residual = available_pool - target_val

        if not unlocked_others:
            # If no one to distribute to, force source to match available (revert)
            if target_val != available_pool:
                self.rows[source_idx]["var_pct"].set(available_pool)
            self.is_updating = False
            self.update_calc_labels()
            return

        # 2. Determine weights for distribution
        # Use snapshot if available and valid (contains all keys)
        # If snapshot missing (e.g. external update), use current values
        use_snapshot = (self.weights_snapshot and all(i in self.weights_snapshot for i in unlocked_others))

        weights = {}
        for i in unlocked_others:
            if use_snapshot:
                weights[i] = self.weights_snapshot[i]
            else:
                weights[i] = self.rows[i]["var_pct"].get()

        total_weight = sum(weights.values())

        # If total weight is 0 (all were 0), distribute equally
        if total_weight == 0:
            count = len(unlocked_others)
            per_item = residual // count
            rem = residual % count
            for idx, i in enumerate(unlocked_others):
                val = per_item + (1 if idx < rem else 0)
                self.rows[i]["var_pct"].set(val)
        else:
            # Weighted distribution (Hamilton Method)
            distribution = []
            for i in unlocked_others:
                w = weights[i]
                ideal = residual * (w / total_weight)
                int_part = int(ideal)
                rem = ideal - int_part
                distribution.append({"i": i, "int": int_part, "rem": rem})

            allocated = sum(x["int"] for x in distribution)
            leftover = residual - allocated

            # Distribute leftover to highest remainders
            distribution.sort(key=lambda x: x["rem"], reverse=True)

            for k in range(leftover):
                distribution[k % len(distribution)]["int"] += 1

            # Apply
            for item in distribution:
                self.rows[item["i"]]["var_pct"].set(item["int"])

        self.update_calc_labels()
        self.is_updating = False

    def update_calc_labels(self):
        for r in self.rows:
            pct = r["var_pct"].get()
            size = int(self.total_pop * (pct / 100.0))
            r["lbl_calc"].config(text=str(size))

    def get_data(self):
        res = []
        for r in self.rows:
            res.append({
                "culture": r["culture"],
                "religion": r["religion"],
                "percent": r["var_pct"].get()
            })
        return res

class StateObject:
    def __init__(self, state_id):
        self.id = state_id
        self.provinces = set()
        self.hubs = {
            "city": None,
            "port": None,
            "farm": None,
            "mine": None,
            "wood": None
        }
        self.naval_exit_id = None
        self.file_path = ""
        self.impassable = []  # List of impassable provinces if any
        self.prime_land = []  # List of prime provinces if any
        self.arable_land = None
        self.numeric_id = 0

class StateManager:
    def __init__(self, vic3_logic):
        self.logic = vic3_logic
        self.states = {}  # "STATE_ID": StateObject
        self.province_owner_map = {}  # "x1A2B3": "STATE_TEXAS"
        # We load on init to populate the registry
        self.load_state_regions()

    def load_state_regions(self):
        self.states, self.province_owner_map = {}, {}
        for path in self.logic.effective_files('map_data/state_regions'):
            text = path.read_text(encoding='utf-8-sig')
            for b in script_blocks(text, depth=0):
                if not b['key'] or not b['key'].startswith('STATE_'): continue
                obj = StateObject(b['key'])
                obj.file_path = str(path)
                body = text[b['opening']+1:b['end']-1]
                obj.numeric_id = int(field(body,'id','0'))
                for key, attr in [('provinces','provinces'),('impassable','impassable'),('prime_land','prime_land')]:
                    values = [t.strip('"').lower() for block in script_blocks(body,key,0) for t,_,_ in script_tokens(body[block['opening']+1:block['end']-1])]
                    setattr(obj,attr,set(values) if key=='provinces' else values)
                obj.hubs = {key:field(body,key) or None for key in obj.hubs}
                obj.naval_exit_id = field(body,'naval_exit_id') or None
                obj.arable_land = int(field(body,'arable_land','0'))
                self.states[obj.id] = obj
        # Rebuild after overrides so removed provinces do not remain mapped to old states.
        for state,obj in self.states.items():
            for province in obj.provinces: self.province_owner_map[province.lower()] = state

    @mod_operation
    def transfer_state_assets(self, new_state_id, new_owner_tag=None, source_ratios=None):
        if not source_ratios: return 0

        # 1. Pops Transfer
        new_pops_list = []

        for old_state, ratio in source_ratios.items():
            if ratio <= 0.001: continue

            pops = self.logic.get_state_pops(old_state)
            if not pops: continue

            # Group by file to minimize I/O
            pops_by_file = {}
            for p in pops:
                f = p['file']
                if f not in pops_by_file: pops_by_file[f] = []
                pops_by_file[f].append(p)

            for fpath, file_pops in pops_by_file.items():
                # Sort descending by start index to keep offsets valid during edits
                file_pops.sort(key=lambda x: x['indices']['pop_content_start'], reverse=True)

                # Ensure we are editing the mod file (copy if vanilla)
                target_path = fpath
                if self.logic.vanilla_path and fpath.startswith(self.logic.vanilla_path):
                    mod_rel = os.path.relpath(fpath, os.path.join(self.logic.vanilla_path, "game"))
                    target_path = os.path.join(self.logic.mod_path, mod_rel)
                    os.makedirs(os.path.dirname(target_path), exist_ok=True)
                    if not os.path.exists(target_path):
                        shutil.copy2(fpath, target_path)

                try:
                    with open(target_path, 'r', encoding='utf-8-sig') as f: content = f.read()
                except:
                    with open(target_path, 'r', encoding='utf-8') as f: content = f.read()

                file_changed = False
                for p in file_pops:
                    move_size = int(p['size'] * ratio)
                    # Ignore small transfers to prevent micro-pops
                    if move_size >= 1000:
                        new_size = max(0, p['size'] - move_size)

                        # Extract block for editing
                        s, e = p['indices']['pop_content_start'], p['indices']['pop_content_end']
                        block = content[s:e]

                        # Replace size
                        if re.search(r"size\s*=\s*\d+", block):
                            new_block = re.sub(r"size\s*=\s*\d+", f"size = {new_size}", block)
                            content = content[:s] + new_block + content[e:]
                            file_changed = True

                            # Add to new list
                            target_owner = new_owner_tag if new_owner_tag else p.get('region_tag', 'unknown')
                            new_pops_list.append({
                                'owner': target_owner,
                                'culture': p['culture'],
                                'religion': p['religion'],
                                'size': move_size
                            })

                if file_changed:
                    with open(target_path, 'w', encoding='utf-8-sig') as f: f.write(content)

        # Write new pops
        if new_pops_list:
            pop_dir = os.path.join(self.logic.mod_path, "common/history/pops")
            os.makedirs(pop_dir, exist_ok=True)
            new_pop_file = os.path.join(pop_dir, f"99_custom_{new_state_id}.txt")

            # Group by owner
            pops_by_owner = {}
            for p in new_pops_list:
                o = p['owner']
                if o not in pops_by_owner: pops_by_owner[o] = []
                pops_by_owner[o].append(p)

            # Ensure proper s:STATE_ID format
            s_key = new_state_id if new_state_id.startswith("STATE_") else f"STATE_{new_state_id}"

            # Prepare new pops string per owner
            pops_to_add_by_owner = {} # owner -> str
            for owner, p_list in pops_by_owner.items():
                pop_str = ""
                for p in p_list:
                    # Only write religion if valid
                    rel_line = f"\n\t\t\treligion = {p['religion']}" if p['religion'] else ""
                    pop_str += f"\n\t\t\tcreate_pop = {{\n\t\t\t\tculture = {p['culture']}{rel_line}\n\t\t\t\tsize = {p['size']}\n\t\t\t}}"
                pops_to_add_by_owner[owner] = pop_str

            # Read Existing
            existing_content = ""
            if os.path.exists(new_pop_file):
                try:
                    with open(new_pop_file, 'r', encoding='utf-8-sig') as f: existing_content = f.read()
                except: pass

            if not existing_content.strip():
                existing_content = "POPS = {\n}"

            if "POPS" not in existing_content:
                existing_content += "\nPOPS = {\n}"

            final_content = existing_content

            # Inject into correct structure
            # 1. Find s:STATE
            s_start, s_end = self.logic.get_block_range_safe(final_content, f"s:{s_key}")

            if s_start is None:
                # Append s:STATE block to POPS
                p_s, p_e = self.logic.get_block_range_safe(final_content, "POPS")
                if p_s is not None:
                    # Append inside POPS
                    insert_pos = p_e - 1
                    new_state_block = f"\n\ts:{s_key} = {{\n\t}}"
                    final_content = final_content[:insert_pos] + new_state_block + final_content[insert_pos:]
                    # Update s_start/end
                    s_start = insert_pos + 1 # rough approx, will find next

            # Re-find state block after possible insertion
            s_start, s_end = self.logic.get_block_range_safe(final_content, f"s:{s_key}")

            if s_start is not None:
                state_block = final_content[s_start:s_end]

                # For each owner, find or create region_state
                for owner, p_str in pops_to_add_by_owner.items():
                    # Regex for region_state:TAG
                    rs_pat = re.compile(r"region_state:(c:)?" + re.escape(owner) + r"\s*=\s*\{", re.IGNORECASE)
                    m = rs_pat.search(state_block)

                    if m:
                        # Append to existing region_state
                        rs_s, rs_e = self.logic.find_block_content(state_block, m.end()-1)
                        if rs_s:
                            # Insert before closing brace of region_state
                            state_block = state_block[:rs_e-1] + p_str + "\n\t\t" + state_block[rs_e-1:]
                    else:
                        # Append new region_state to state block
                        last_brace = state_block.rfind('}')
                        new_rs = f"\n\t\tregion_state:{owner} = {{{p_str}\n\t\t}}"
                        state_block = state_block[:last_brace] + new_rs + "\n\t" + state_block[last_brace:]

                final_content = final_content[:s_start] + state_block + final_content[s_end:]

            with open(new_pop_file, 'w', encoding='utf-8-sig') as f: f.write(final_content)
            self.logic.log(f"[ASSETS] Transferred {len(new_pops_list)} pop groups to {new_state_id}")

        # 2. Buildings Transfer
        new_b_list = []

        for old_state, ratio in source_ratios.items():
            if ratio <= 0.001: continue

            bldgs = self.logic.scan_state_buildings(old_state)
            if not bldgs: continue

            b_by_file = {}
            for b in bldgs:
                f = b['file']
                if f not in b_by_file: b_by_file[f] = []
                b_by_file[f].append(b)

            for fpath, file_bldgs in b_by_file.items():
                file_bldgs.sort(key=lambda x: x['indices']['start'], reverse=True)

                target_path = fpath
                if self.logic.vanilla_path and fpath.startswith(self.logic.vanilla_path):
                    mod_rel = os.path.relpath(fpath, os.path.join(self.logic.vanilla_path, "game"))
                    target_path = os.path.join(self.logic.mod_path, mod_rel)
                    os.makedirs(os.path.dirname(target_path), exist_ok=True)
                    if not os.path.exists(target_path):
                        shutil.copy2(fpath, target_path)

                try:
                    with open(target_path, 'r', encoding='utf-8-sig') as f: content = f.read()
                except:
                    with open(target_path, 'r', encoding='utf-8') as f: content = f.read()

                file_changed = False
                for b in file_bldgs:
                    # Skip if level 0 or invalid
                    if b['level'] <= 0: continue

                    move_level = int(b['level'] * ratio)
                    if move_level > 0:
                        new_level = max(0, b['level'] - move_level)

                        s, e = b['indices']['start'], b['indices']['end']
                        block = content[s:e]

                        # Modify old block
                        updated = False
                        if re.search(r"level\s*=\s*\d+", block):
                            block = re.sub(r"level\s*=\s*\d+", f"level = {new_level}", block)
                            updated = True
                        elif re.search(r"levels\s*=\s*\d+", block):
                            block = re.sub(r"levels\s*=\s*\d+", f"levels = {new_level}", block, count=1)
                            updated = True

                        if updated:
                            content = content[:s] + block + content[e:]
                            file_changed = True

                            target_owner = new_owner_tag if new_owner_tag else b.get('region_tag', 'unknown')
                            new_b_list.append({
                                'owner': target_owner,
                                'type': b['type'],
                                'level': move_level
                            })

                if file_changed:
                    with open(target_path, 'w', encoding='utf-8-sig') as f: f.write(content)

        if new_b_list:
            b_dir = os.path.join(self.logic.mod_path, "common/history/buildings")
            os.makedirs(b_dir, exist_ok=True)
            new_b_file = os.path.join(b_dir, f"99_custom_{new_state_id}.txt")

            # Group by owner
            b_by_owner = {}
            for b in new_b_list:
                o = b['owner']
                if o not in b_by_owner: b_by_owner[o] = []
                b_by_owner[o].append(b)

            b_content = "\nBUILDINGS = {\n"
            b_content += f"\ts:{new_state_id} = {{\n"

            for owner, b_list in b_by_owner.items():
                b_content += f"\t\tregion_state:{owner} = {{\n"

                # Aggregate
                agg_b = {}
                for b in b_list:
                    t = b['type']
                    if t not in agg_b: agg_b[t] = 0
                    agg_b[t] += b['level']

                for b_type, lvl in agg_b.items():
                    # Generate ownership block using logic helper
                    # Using 'owner' as both Land and Building owner (nationalized)
                    ownership = self.logic.get_ownership_block(b_type, owner, lvl, new_state_id)
                    b_content += f"\t\t\tcreate_building = {{\n\t\t\t\tbuilding = \"{b_type}\"\n{ownership}\n\t\t\t}}\n"

                b_content += "\t\t}\n"
            b_content += "\t}\n}\n"

            final_content = b_content
            if os.path.exists(new_b_file):
                try:
                    with open(new_b_file, 'r', encoding='utf-8-sig') as f: existing = f.read()
                    final_content = existing + "\n" + b_content
                except: pass

            with open(new_b_file, 'w', encoding='utf-8-sig') as f: f.write(final_content)
            self.logic.log(f"[ASSETS] Transferred {len(new_b_list)} building levels to {new_state_id}")

        return sum(p['size'] for p in new_pops_list)

    @mod_operation
    def transfer_province(self, province_hex, target_state_id):
        province_hex = province_hex.lower()
        current_state_id = self.province_owner_map.get(province_hex)

        # If already there, done.
        if current_state_id == target_state_id: return True

        loser = self.states.get(current_state_id) if current_state_id else None
        winner = self.states.get(target_state_id)

        # Check if winner exists. If not, we cannot transfer.
        # This prevents leaving a province unassigned (deleted from map).
        if not winner:
            return False

        # 1. Remove from Loser (if it has a loser)
        was_impassable = False
        share = 0

        # Capture port status before displacement modifies it
        was_loser_port = False
        loser_naval_exit = None
        if loser:
            if loser.hubs["port"] == province_hex:
                was_loser_port = True
                loser_naval_exit = loser.naval_exit_id

            # Calculate Arable Land Share
            if loser.arable_land is None: loser.arable_land = 30 # Default fallback

            count = len(loser.provinces)
            if count > 0:
                share = int(round(loser.arable_land / count))
                # Update Loser Arable Land
                loser.arable_land = max(0, loser.arable_land - share)

            if province_hex in loser.provinces:
                loser.provinces.remove(province_hex)
                if province_hex in loser.impassable:
                    loser.impassable.remove(province_hex)
                    was_impassable = True

            # 2. Handle Hub Displacement (Loser)
            for htype, h_hex in loser.hubs.items():
                if h_hex == province_hex:
                    if htype == 'port':
                        loser.hubs['port'] = None
                        loser.naval_exit_id = None
                        continue
                    used_hubs = set(v for k, v in loser.hubs.items() if v and k != htype)
                    # Filter out used hubs AND impassable terrain
                    candidates = [p for p in loser.provinces if p not in used_hubs and p not in loser.impassable]

                    new_hub = None
                    if candidates:
                        new_hub = candidates[0]
                    elif htype in ["city", "farm", "mine", "wood"]:
                        # Fallback: Mandatory hubs must exist. Collide with existing if necessary.
                        valid_all = [p for p in loser.provinces if p not in loser.impassable]
                        if valid_all:
                            new_hub = valid_all[0]

                    if new_hub:
                        loser.hubs[htype] = new_hub
                        self.logic.log(f"Hub '{htype}' for {loser.id} moved to {new_hub}.")
                    else:
                        loser.hubs[htype] = None

        # 3. Handle Hub Initialization (Winner)
        # Winner is guaranteed to exist due to check above
        winner.provinces.add(province_hex)
        if loser and province_hex in loser.prime_land:
            loser.prime_land.remove(province_hex)
            if province_hex not in winner.prime_land: winner.prime_land.append(province_hex)

        # Update Winner Arable Land
        if winner.arable_land is None: winner.arable_land = 0
        winner.arable_land += share

        if was_impassable:
            winner.impassable.append(province_hex)
        if not winner.hubs["city"]:
            winner.hubs["city"] = province_hex
            winner.hubs["farm"] = province_hex
            winner.hubs["mine"] = province_hex
            winner.hubs["wood"] = province_hex
            # Do NOT set port blindly. Only set if we stole a port or know it's coastal.
            # winner.hubs["port"] = province_hex

        # Check if we stole the port from the loser
        if was_loser_port:
            if not winner.hubs["port"]:
                winner.hubs["port"] = province_hex
                if loser_naval_exit:
                    winner.naval_exit_id = loser_naval_exit
        self.province_owner_map[province_hex] = target_state_id
        return True

    def delete_state_history_entries(self, state_id):
        """Removes all references to the state from states, pops, and buildings history files."""
        dirs = ["states", "pops", "buildings"]

        for folder in dirs:
            hist_dir = os.path.join(self.logic.mod_path, "common", "history", folder)
            if not os.path.exists(hist_dir): continue

            for root, _, files in os.walk(hist_dir):
                for file in files:
                    if not file.endswith(".txt"): continue
                    fpath = os.path.join(root, file)

                    try:
                        with open(fpath, 'r', encoding='utf-8-sig') as f: content = f.read()
                    except:
                        with open(fpath, 'r', encoding='utf-8') as f: content = f.read()

                    # Find s:STATE_ID = { ... }
                    s_start, s_end = self.logic.get_block_range_safe(content, f"s:{state_id}")

                    if s_start is not None:
                        # Remove the block
                        new_content = content[:s_start] + content[s_end:]
                        with open(fpath, 'w', encoding='utf-8-sig') as f: f.write(new_content)
                        self.logic.log(f"[CLEANUP] Removed {state_id} from history/{folder}/{file}")

    @mod_operation
    def create_new_state(self, state_name_key, owner_data, province_list):
        state_id = self.logic.normalize_state_key(state_name_key)
        identifier(state_id, 'State key')
        if state_id in self.states: raise ValueError('State already exists; use the move/merge action.')
        if not province_list: raise ValueError('Select at least one province.')
        if any(p.lower() not in self.province_owner_map for p in province_list): raise ValueError('Every selected province must belong to a loaded state.')
        province_list = sorted(set(p.lower() for p in province_list))
        source_arable = set()
        for source_id in {self.province_owner_map[p] for p in province_list}:
            source_arable.update(self.logic.scan_state_resources(source_id)['arable'])


        if state_id not in self.states:
            sobj = StateObject(state_id)
            # Default file path to mod/map_data/state_regions/99_custom_regions.txt
            sobj.file_path = os.path.join(self.logic.mod_path, "map_data", "state_regions", "99_custom_regions.txt")
            self.states[state_id] = sobj
            self.logic.log(f"Created new StateObject: {state_id}")

        # Determine Strategic Region from "Loser" of first province
        strategic_region = None
        if province_list:
            first_p = province_list[0]
            old_state_id = self.province_owner_map.get(first_p)
            if old_state_id:
                strategic_region = self.logic.find_strategic_region(f"s:{old_state_id}")

        # Prepare Owner Data
        # owner_data can be string (tag) or dict {tag: [provs]}
        primary_owner = "unknown"
        history_additions = {}

        if isinstance(owner_data, dict):
            # Split state creation
            history_additions = owner_data
            # Heuristic for primary owner for asset transfer: whoever gets the most provinces
            if owner_data:
                primary_owner = max(owner_data, key=lambda k: len(owner_data[k]))
        else:
            # Single owner
            primary_owner = owner_data if owner_data else "unknown"
            history_additions = {primary_owner: province_list}

        modified_states = set()
        history_removals = {} # old_state -> list of provinces

        # Calculate Asset Transfer Ratios
        source_counts = {} # old_state -> count of provinces being TAKEN
        old_state_totals = {} # old_state -> total provinces BEFORE transfer

        for p in province_list:
            old_state_id = self.province_owner_map.get(p)
            if old_state_id and old_state_id != state_id:
                modified_states.add(old_state_id)
                if old_state_id not in history_removals:
                    history_removals[old_state_id] = []
                    source_counts[old_state_id] = 0
                    # Capture total before we start removing them from StateObject
                    if old_state_id in self.states:
                        old_state_totals[old_state_id] = len(self.states[old_state_id].provinces)
                    else:
                        old_state_totals[old_state_id] = 0

                history_removals[old_state_id].append(p)
                source_counts[old_state_id] += 1

            self.transfer_province(p, state_id)

        source_ratios = {}
        for os_id, count in source_counts.items():
            total = old_state_totals.get(os_id, 0)
            if total > 0:
                source_ratios[os_id] = count / total
            else:
                source_ratios[os_id] = 0.0
            self.logic.log(f"[TRANSFER] Taking {count}/{total} ({source_ratios[os_id]:.2%}) from {os_id}")

        self._update_localization(state_id, state_name_key)

        # Initialize history logic (create empty block if needed)
        # Note: _init_history assumed single owner_tag. We now handle complex ownership via update_history_provinces.
        # But we still need to ensure the state block exists in history.

        hist_dir = os.path.join(self.logic.mod_path, "common", "history", "states")
        os.makedirs(hist_dir, exist_ok=True)
        # Check if any file contains s:STATE_ID
        found_hist = False
        for root, _, files in os.walk(hist_dir):
            for f in files:
                if f.endswith(".txt"):
                    with open(os.path.join(root, f), 'r', encoding='utf-8', errors='ignore') as fh:
                        # Use regex to avoid partial matches (e.g. s:STATE_1 inside s:STATE_10)
                        if re.search(r"s:" + re.escape(state_id) + r"\s*(=|\?=)\s*\{", fh.read()):
                            found_hist = True
                            break
            if found_hist: break

        if not found_hist:
            # Create new history file
            new_hist_path = os.path.join(hist_dir, "99_custom_states.txt")
            # If 99_custom_states exists, append. Else create.
            if not os.path.exists(new_hist_path):
                with open(new_hist_path, 'w', encoding='utf-8-sig') as f:
                    f.write("STATES = {\n")
                    f.write(f"\ts:{state_id} = {{\n\t}}\n")
                    f.write("}\n")
            else:
                # Append if not present in file, otherwise rely on update
                with open(new_hist_path, 'r', encoding='utf-8-sig') as f: content = f.read()
                # Use regex to avoid partial matches
                if not re.search(r"s:" + re.escape(state_id) + r"\s*(=|\?=)\s*\{", content):
                    idx = content.rfind('}')
                    if idx != -1:
                        new_content = content[:idx] + f"\n\ts:{state_id} = {{\n\t}}\n" + content[idx:]
                        with open(new_hist_path, 'w', encoding='utf-8-sig') as f: f.write(new_content)

        # Transfer Assets (Pops & Buildings)
        total_pop = self.transfer_state_assets(state_id, primary_owner, source_ratios)

        if strategic_region:
            self._add_to_strategic_region(state_id, strategic_region)
        else:
            self.logic.log(f"[WARN] Could not determine Strategic Region for {state_id}. Please add manually.", 'warn')

        # Save Geometry Changes
        # We save the new state region immediately
        self.save_state_region(state_id)

        # Save all modified old states to ensure provinces are removed from them
        for old_s in modified_states:
            self.save_state_region(old_s)

            if old_s in self.states:
                sobj = self.states[old_s]
                if len(sobj.provinces) == 0:
                    self.logic.log(f"[INFO] State {old_s} is fully deleted. Moving military to {state_id}...")
                    self.logic.move_military_from_deleted_state(old_s, state_id)

        resources = self.logic.scan_state_resources(state_id)
        resources['arable'] = sorted(source_arable)
        self.logic.save_state_resources(state_id, resources)

        # Update History (Ownership)
        # Remove from old
        for os_id, removals in history_removals.items():
            self.update_history_provinces(os_id, [], removals)

        # Add to new
        self.update_history_provinces(state_id, history_additions, [])

    def _update_localization(self, state_id, name):
        self.logic._localize('map',{state_id:name})

    def _init_history(self, state_id, owner_tag):
        hist_dir = os.path.join(self.logic.mod_path, "common", "history", "states")
        os.makedirs(hist_dir, exist_ok=True)
        fpath = os.path.join(hist_dir, f"99_custom_{state_id}.txt")

        sobj = self.states.get(state_id)
        if not sobj: return

        # Only new states generally have one owner covering all provinces initially
        prov_str = " ".join(f'"{p}"' for p in sobj.provinces)

        content = f"""STATES = {{
    s:{state_id} = {{
        create_state = {{
            country = c:{owner_tag}
            owned_provinces = {{ {prov_str} }}
        }}
    }}
}}
"""
        with open(fpath, 'w', encoding='utf-8-sig') as f: f.write(content)

    def _add_to_strategic_region(self, state_id, region_name):
        clean_reg = region_name.replace("sr:", "").strip()

        paths = []
        if self.logic.mod_path: paths.append(os.path.join(self.logic.mod_path, "common/strategic_regions"))
        if self.logic.vanilla_path: paths.append(os.path.join(self.logic.vanilla_path, "game/common/strategic_regions"))

        target_file = None
        target_content = None

        for p in paths:
            if not os.path.exists(p): continue
            for root, _, files in os.walk(p):
                for file in files:
                    if not file.endswith(".txt"): continue
                    filepath = os.path.join(root, file)
                    try:
                        with open(filepath, 'r', encoding='utf-8-sig') as f: content = f.read()
                    except:
                        with open(filepath, 'r', encoding='utf-8') as f: content = f.read()

                    if re.search(r"(^|\s)" + re.escape(clean_reg) + r"\s*=\s*\{", content):
                        target_file = filepath
                        target_content = content
                        break
                if target_file: break
            if target_file: break

        if target_file and target_content:
            # Check if it's a vanilla file, if so copy to mod
            if self.logic.vanilla_path and target_file.startswith(self.logic.vanilla_path):
                rel_path = os.path.relpath(target_file, os.path.join(self.logic.vanilla_path, "game"))
                mod_target = os.path.join(self.logic.mod_path, rel_path)
                os.makedirs(os.path.dirname(mod_target), exist_ok=True)
                target_file = mod_target

            # Insert state
            m = re.search(r"(^|\s)" + re.escape(clean_reg) + r"\s*=\s*\{", target_content)
            if m:
                s, e = self.logic.find_block_content(target_content, m.end() - 1)
                if s is not None:
                    block = target_content[s:e]
                    sm = re.search(r"states\s*=\s*\{", block)
                    if sm:
                        ss, se = self.logic.find_block_content(block, sm.end() - 1)
                        if ss is not None:
                            states_inner = block[ss + 1:se - 1]
                            if state_id not in states_inner:
                                new_states = states_inner + f" {state_id} "
                                new_block = block[:ss + 1] + new_states + block[se - 1:]
                                target_content = target_content[:s] + new_block + target_content[e:]

                                with open(target_file, 'w', encoding='utf-8-sig') as f: f.write(target_content)
                                self.logic.log(f"Added {state_id} to {clean_reg} in {os.path.basename(target_file)}")

    @mod_operation
    def update_history_provinces(self, state_id, added_data, removed_list):
        """
        Updates ownership in history files for specific provinces (adds or removes).
        added_data can be:
          - A list of provinces (legacy/single owner mode, adds to ANY existing block or creates new default)
          - A dict { owner_tag: [provinces] } for split ownership.
        """
        if not added_data and not removed_list: return

        # Normalize added_data to dict if it's a list
        added_map = {}
        if isinstance(added_data, list):
            if added_data:
                added_map["__ANY__"] = {p.lower() for p in added_data}
        elif isinstance(added_data, dict):
            for tag, provs in added_data.items():
                if provs:
                    added_map[tag] = {p.lower() for p in provs}

        removed_set = {r.lower() for r in removed_list}

        # Scan all history files for this state
        hist_dir = os.path.join(self.logic.mod_path, "common", "history", "states")
        if not os.path.exists(hist_dir): return

        files_to_check = []
        for root, _, files in os.walk(hist_dir):
            for file in files:
                if file.endswith(".txt"):
                    files_to_check.append(os.path.join(root, file))

        for fpath in files_to_check:
            try:
                with open(fpath, 'r', encoding='utf-8-sig') as f: content = f.read()
            except:
                with open(fpath, 'r', encoding='utf-8') as f: content = f.read()

            file_changed = False
            cursor = 0
            while True:
                # Find s:STATE_ID = {
                pat = re.compile(r"s:" + re.escape(state_id) + r"\s*=\s*\{")
                m = pat.search(content, cursor)
                if not m: break

                s_start = cursor + m.start()
                s_idx, e_idx = self.logic.find_block_content(content, cursor + m.end() - 1)

                if s_idx is not None:
                    block_content = content[s_idx:e_idx]

                    # Track which owners we have processed/added to in this file
                    owners_processed = set()

                    # Iterate create_state inside
                    inner_cursor = 0
                    new_block_parts = []
                    last_inner_idx = 0
                    block_modified = False

                    while True:
                        cs = re.search(r"create_state\s*=\s*\{", block_content[inner_cursor:])
                        if not cs:
                            new_block_parts.append(block_content[last_inner_idx:])
                            break

                        cs_abs_start = inner_cursor + cs.start()
                        new_block_parts.append(block_content[last_inner_idx:cs_abs_start])

                        cs_s, cs_e = self.logic.find_block_content(block_content, inner_cursor + cs.end() - 1)

                        if cs_s:
                            cs_inner_full = block_content[cs_abs_start:cs_e]
                            cs_body = block_content[cs_s+1:cs_e-1]

                            # Determine owner of this block
                            block_owner = None
                            c_tag_m = re.search(r"country\s*=\s*c:([A-Za-z0-9_]+)", cs_body)
                            if c_tag_m:
                                block_owner = c_tag_m.group(1).upper()

                            # Determine if we should add provinces to this block
                            to_add = set()
                            if "__ANY__" in added_map:
                                if "__ANY__" not in owners_processed:
                                    to_add = added_map["__ANY__"]
                                    owners_processed.add("__ANY__") # Marked as done to prevent duplicate adding
                            elif block_owner:
                                # Check if we have specific provinces for this owner
                                # Also check clean tag
                                clean_tag = block_owner.replace("C:", "")
                                for k, v in added_map.items():
                                    if k.upper().replace("C:", "") == clean_tag:
                                        to_add = v
                                        owners_processed.add(k)
                                        break

                            op_m = re.search(r"owned_provinces\s*=\s*\{", cs_body)
                            if op_m:
                                op_s, op_e = self.logic.find_block_content(cs_body, op_m.end() - 1)
                                if op_s:
                                    prov_str = cs_body[op_s+1:op_e-1]
                                    # Normalized read: lower case
                                    current_provs = set()
                                    found_quoted = re.findall(r'"([^"]+)"', prov_str)
                                    if found_quoted:
                                        current_provs = {p.lower() for p in found_quoted}
                                    else:
                                        current_provs = {p.lower() for p in prov_str.replace('"', ' ').split()}

                                    original_len = len(current_provs)

                                    # REMOVE
                                    if removed_set:
                                        current_provs -= removed_set

                                    # ADD
                                    if to_add:
                                        current_provs.update(to_add)

                                    if len(current_provs) != original_len or (to_add & current_provs):
                                        if not current_provs:
                                            # Bug 4: Remove empty ownership block
                                            block_modified = True
                                            # Do not append anything to new_block_parts
                                        else:
                                            new_prov_str = " ".join([f'"{p.lower()}"' for p in sorted(list(current_provs))])
                                            new_cs_body = cs_body[:op_s+1] + " " + new_prov_str + " " + cs_body[op_e-1:]
                                            new_block_parts.append(f"create_state = {{{new_cs_body}}}")
                                            block_modified = True
                                    else:
                                        new_block_parts.append(cs_inner_full)
                                else:
                                    new_block_parts.append(cs_inner_full)
                            else:
                                # Implicit ownership block.
                                # If we are REMOVING from implicit OR if we are adding explicit blocks for OTHER owners,
                                # we must convert this implicit block to explicit to prevent duplicate ownership.
                                should_convert = False

                                # Case 1: Direct removal
                                if removed_set:
                                    should_convert = True

                                # Case 2: New explicit blocks for others will be added (added_map has entries for others)
                                # We need to check if any other owner is getting provinces in this state
                                if not should_convert:
                                    for k in added_map:
                                        if k != "__ANY__" and k.upper().replace("C:", "") != clean_tag:
                                            should_convert = True
                                            break

                                if should_convert and state_id in self.states:
                                    # Convert to explicit
                                    all_provs = {p.lower() for p in self.states[state_id].provinces}

                                    # Determine what "others" own to subtract from "all"
                                    # "others" includes:
                                    # 1. removed_set (provinces leaving this owner)
                                    # 2. provinces explicitly given to others in added_map

                                    provinces_claimed_by_others = set(removed_set)

                                    for k, v in added_map.items():
                                        if k != "__ANY__" and k.upper().replace("C:", "") != clean_tag:
                                            provinces_claimed_by_others.update({p.lower() for p in v})

                                    current_provs = all_provs - provinces_claimed_by_others

                                    # If we are also adding to THIS owner, ensure they are included
                                    if to_add:
                                        current_provs.update(to_add)

                                    if not current_provs:
                                        # Empty after conversion -> remove block
                                        block_modified = True
                                    else:
                                        new_prov_str = " ".join([f'"{p.lower()}"' for p in sorted(list(current_provs))])
                                        # Construct new explicit body
                                        # Inject owned_provinces before closing brace
                                        new_cs_body = cs_body.rstrip() + f"\n\t\towned_provinces = {{ {new_prov_str} }}\n"
                                        new_block_parts.append(f"create_state = {{{new_cs_body}}}")
                                        block_modified = True
                                else:
                                    new_block_parts.append(cs_inner_full)

                            inner_cursor = cs_e
                            last_inner_idx = cs_e
                        else:
                            inner_cursor += 1

                    # After iterating existing blocks, check if any owners in added_map were NOT processed.
                    # If so, we need to create NEW create_state blocks for them.
                    # Ignore "__ANY__" if we processed at least one block? Or if it was handled?
                    # If __ANY__ was passed and we found NO create_state blocks, we should probably create one?
                    # But usually __ANY__ attaches to existing.

                    pending_new_blocks = []
                    for owner, provs in added_map.items():
                        if owner == "__ANY__": continue
                        if owner not in owners_processed and provs:
                            # Create new block for this owner
                            p_str = " ".join([f'"{p.lower()}"' for p in sorted(list(provs))])
                            clean_tag = owner if owner.startswith("c:") else f"c:{owner}"
                            block_str = f'\n\tcreate_state = {{\n\t\tcountry = {clean_tag}\n\t\towned_provinces = {{ {p_str} }}\n\t}}'
                            pending_new_blocks.append(block_str)
                            block_modified = True

                    if block_modified:
                        # Append new blocks before the closing brace of s:STATE
                        reconstructed = "".join(new_block_parts)
                        # Remove the last closing brace from the reconstructed block to append new items
                        # reconstructed mimics block_content which includes outer braces { ... }
                        final_block = reconstructed[:-1]

                        if pending_new_blocks:
                            final_block += "".join(pending_new_blocks)

                        final_block += "}"

                        content = content[:s_idx] + final_block + content[e_idx:]

                        file_changed = True
                        diff = len(final_block) - (e_idx - s_idx)
                        cursor = e_idx + diff
                    else:
                        cursor = e_idx
                else:
                    cursor += 1

            if file_changed:
                with open(fpath, 'w', encoding='utf-8-sig') as f: f.write(content)
                self.logic.log(f"[HIST] Updated owned_provinces in {os.path.basename(fpath)} for {state_id}")

    @mod_operation
    def save_state_region(self, state_id):
        self.logic._require_mod()
        obj = self.states.get(state_id)
        if not obj: raise ValueError('State is not loaded.')
        source = Path(obj.file_path) if obj.file_path else None
        mod = Path(self.logic.mod_path).resolve()
        if source and source.resolve().is_relative_to(mod): target = source
        elif source and self.logic.vanilla_path:
            target = mod/source.resolve().relative_to((Path(self.logic.vanilla_path)/'game').resolve())
        else: target = mod/'map_data/state_regions/99_custom_regions.txt'
        text = target.read_text(encoding='utf-8-sig') if target.exists() else source.read_text(encoding='utf-8-sig') if source and source.exists() else ''
        blocks = script_blocks(text,state_id,0)
        existing = blocks[0] if blocks else None
        if not obj.provinces:
            if existing: atomic_text(target,text[:existing['start']]+text[existing['end']:])
            self.delete_state_history_entries(state_id)
            return
        if not all(re.fullmatch(r'x[0-9a-fA-F]{6}',p) for p in obj.provinces): raise ValueError('Province IDs must be x followed by six hex digits.')
        if any(v and v.lower() not in obj.provinces for v in obj.hubs.values()): raise ValueError('Every hub must belong to its state.')
        if existing: body=text[existing['opening']+1:existing['end']-1]
        else:
            used = {getattr(o,'numeric_id',0) for o in self.states.values()}
            obj.numeric_id = max(used|{0})+1
            body=f'\n    id = {obj.numeric_id}\n    subsistence_building = "building_subsistence_farm"\n    arable_resources = {{ }}\n    capped_resources = {{ }}\n'
        for key,values in [('provinces',obj.provinces),('impassable',obj.impassable),('prime_land',obj.prime_land)]:
            value = key+' = { '+' '.join(quoted(v) for v in sorted(values))+' }'
            matches=script_blocks(body,key,0)
            if matches:
                b=matches[0]; body=body[:b['start']]+value+body[b['end']:]
            elif values: body += '\n    '+value+'\n'
        body=put_field(body,'arable_land',nonnegative(obj.arable_land or 0,'Arable land'))
        for key,value in dict(obj.hubs, naval_exit_id=obj.naval_exit_id).items():
            old=script_fields(body).get(key)
            if value is not None: body=put_field(body,key,str(nonnegative(value)) if key=='naval_exit_id' else quoted(value))
            elif old: body=body[:old[1]]+body[old[2]:]
        block=state_id+' = {'+body+'}\n'
        result=text[:existing['start']]+block+text[existing['end']:] if existing else text+'\n'+block
        atomic_text(target,result)
        obj.file_path=str(target)
        self.logic.log(f'[MAP] Saved {state_id}', 'success')

    def validate_state(self, state_id):
        sobj = self.states.get(state_id)
        if not sobj: return

        if len(sobj.provinces) == 0:
            self.logic.log(f"[ERROR] State {state_id} has 0 provinces. It should be deleted.", 'error')

        if sobj.naval_exit_id and not sobj.hubs['port']:
            self.logic.log(f"[WARN] State {state_id} has naval exit but no port hub.", 'warn')

    def move_orphaned_region_state(self, old_state_id, tag, new_state_id):
        """Moves entire region_state contents (Pops, Buildings) and Military Units from old to new state."""
        self.logic.log(f"[CLEANUP] {tag} has no land left in {old_state_id}. Moving assets to {new_state_id}...")

        # 1. POPS & BUILDINGS
        folders = ["pops", "buildings"]
        for folder in folders:
            target_dir = os.path.join(self.logic.mod_path, "common/history", folder)
            if not os.path.exists(target_dir): continue

            # Find file containing s:OLD_STATE
            old_file_path = None
            old_file_content = None

            for root, _, files in os.walk(target_dir):
                for file in files:
                    if not file.endswith(".txt"): continue
                    path = os.path.join(root, file)
                    try:
                        with open(path, 'r', encoding='utf-8-sig') as f: c = f.read()
                    except:
                        with open(path, 'r', encoding='utf-8') as f: c = f.read()

                    if re.search(r"s:" + re.escape(old_state_id) + r"\s*=\s*\{", c):
                        old_file_path = path
                        old_file_content = c
                        break
                if old_file_path: break

            if old_file_path and old_file_content:
                s, e = self.logic.get_block_range_safe(old_file_content, f"s:{old_state_id}")
                if s is not None:
                    state_block = old_file_content[s:e]

                    # Find region_state:TAG block inside
                    rs_pat = re.compile(r"region_state:" + re.escape(tag) + r"\s*=\s*\{")
                    m_rs = rs_pat.search(state_block)

                    if m_rs:
                        rs_s, rs_e = self.logic.find_block_content(state_block, m_rs.end() - 1)
                        if rs_s:
                            rs_full = state_block[m_rs.start():rs_e]
                            rs_body = state_block[rs_s+1:rs_e-1]

                            # Remove from old file
                            new_state_block = state_block[:m_rs.start()] + state_block[rs_e:]
                            new_file_content = old_file_content[:s] + new_state_block + old_file_content[e:]
                            with open(old_file_path, 'w', encoding='utf-8-sig') as f: f.write(new_file_content)

                            # Add to new state file
                            new_file_path = None
                            new_file_content = None

                            for root, _, files in os.walk(target_dir):
                                for file in files:
                                    if not file.endswith(".txt"): continue
                                    path = os.path.join(root, file)
                                    try:
                                        with open(path, 'r', encoding='utf-8-sig') as f: c = f.read()
                                    except:
                                        with open(path, 'r', encoding='utf-8') as f: c = f.read()

                                    if re.search(r"s:" + re.escape(new_state_id) + r"\s*=\s*\{", c):
                                        new_file_path = path
                                        new_file_content = c
                                        break
                                if new_file_path: break

                            if not new_file_path:
                                new_file_path = os.path.join(target_dir, f"99_custom_{new_state_id}.txt")
                                wrapper = "POPS" if folder == "pops" else "BUILDINGS"
                                new_file_content = f"{wrapper} = {{\n\ts:{new_state_id} = {{\n\t}}\n}}"
                                if os.path.exists(new_file_path):
                                     with open(new_file_path, 'r', encoding='utf-8-sig') as f: new_file_content = f.read()

                            ns, ne = self.logic.get_block_range_safe(new_file_content, f"s:{new_state_id}")
                            if ns is not None:
                                ns_block = new_file_content[ns:ne]
                                nm_rs = rs_pat.search(ns_block)
                                if nm_rs:
                                    nrs_s, nrs_e = self.logic.find_block_content(ns_block, nm_rs.end()-1)
                                    if nrs_s:
                                        to_append = rs_body
                                        if folder == "buildings":
                                            to_append = re.sub(r'region\s*=\s*"(s:)?' + re.escape(old_state_id) + r'"', f'region = "{new_state_id}"', to_append)

                                        updated_ns_rs = ns_block[nm_rs.start():nrs_e-1] + "\n" + to_append + "\n\t\t}"
                                        updated_ns_block = ns_block[:nm_rs.start()] + updated_ns_rs + ns_block[nrs_e:]
                                        new_file_content = new_file_content[:ns] + updated_ns_block + new_file_content[ne:]
                                else:
                                    to_append = rs_full
                                    if folder == "buildings":
                                        to_append = re.sub(r'region\s*=\s*"(s:)?' + re.escape(old_state_id) + r'"', f'region = "{new_state_id}"', to_append)

                                    last_brace = ns_block.rfind('}')
                                    updated_ns_block = ns_block[:last_brace] + "\n\t\t" + to_append + "\n\t}"
                                    new_file_content = new_file_content[:ns] + updated_ns_block + new_file_content[ne:]

                                with open(new_file_path, 'w', encoding='utf-8-sig') as f: f.write(new_file_content)
                                self.logic.log(f"Moved orphaned {folder} for {tag} from {old_state_id} to {new_state_id}")

        # 2. MILITARY
        self._move_orphaned_military(old_state_id, tag, new_state_id)

    def _move_orphaned_military(self, old_state, tag, new_state):
        mil_dir = os.path.join(self.logic.mod_path, "common/history/military_formations")
        if not os.path.exists(mil_dir): return

        old_clean = self.logic.normalize_state_key(old_state).replace("s:", "")
        new_clean = self.logic.normalize_state_key(new_state).replace("s:", "")
        clean_tag = tag.replace("c:", "")

        for root, _, files in os.walk(mil_dir):
            for file in files:
                if not file.endswith(".txt"): continue
                path = os.path.join(root, file)
                try:
                    with open(path, 'r', encoding='utf-8-sig') as f: content = f.read()
                except:
                    with open(path, 'r', encoding='utf-8') as f: content = f.read()

                current_idx = 0
                file_mod = False
                new_content = content

                while True:
                    c_start, c_end = self.logic.get_block_range_safe(new_content, f"c:{clean_tag}", current_idx)
                    if c_start is None: break

                    block = new_content[c_start:c_end]

                    pat = re.compile(r"state_region\s*=\s*(?:s:)?\"?" + re.escape(old_clean) + r"\"?\b")

                    if pat.search(block):
                        new_block = pat.sub(f"state_region = s:{new_clean}", block)
                        new_content = new_content[:c_start] + new_block + new_content[c_end:]
                        file_mod = True
                        diff = len(new_block) - len(block)
                        current_idx = c_end + diff
                    else:
                        current_idx = c_end

                if file_mod:
                    with open(path, 'w', encoding='utf-8-sig') as f: f.write(new_content)
                    self.logic.log(f"Moved military units for {tag} from {old_clean} to {new_clean}")

class App(tk.Tk):
    def config_path(self):
        base=Path(os.environ.get('APPDATA') or os.environ.get('XDG_CONFIG_HOME') or Path.home()/'.config')
        return base/'v3mt'/'config.json'

    def report_callback_exception(self, exc_type, exc, tb):
        self.log_message(str(exc),'error')
        traceback.print_exception(exc_type,exc,tb)
        messagebox.showerror('Unable to complete action',str(exc),parent=self)

    def navigate(self, title, command):
        if self.is_processing:
            self.log_message('Wait for the current operation to finish.','warn'); return
        command()
        self.page_title.configure(text=title)
        for name,button in self.nav_buttons.items(): button.configure(style='Active.Nav.TButton' if name==title else 'Nav.TButton')
        self.canvas.yview_moveto(0)

    def _scroll_page(self, event):
        # Native list/text widgets retain their own wheel behavior.
        if not isinstance(event.widget, tk.Misc): return
        if event.widget.winfo_class() in ('Text','Listbox','Treeview','TCombobox','Entry','TEntry'): return
        if str(event.widget).startswith(str(self.scrollable_frame)) or event.widget==self.canvas:
            amount=-1 if getattr(event,'num',0)==4 else 1 if getattr(event,'num',0)==5 else (-1 if event.delta>0 else 1)
            self.canvas.yview_scroll(amount*3,'units')

    def show_validation_ui(self):
        self.clear_content(); self.run_btn.pack_forget()
        ttk.Label(self.content_frame,text='Check files before starting the game',font=('Segoe UI',15,'bold')).pack(anchor='w',pady=(10,8))
        ttk.Label(self.content_frame,text='Checks structure, braces, localization, state IDs, province duplication, fleet syntax and HQ references.\nRun the game in debug mode to check effect semantics and gameplay.',style='Muted.TLabel',wraplength=780).pack(anchor='w',pady=(0,16))
        toolbar=ttk.Frame(self.content_frame); toolbar.pack(fill='x')
        ttk.Button(toolbar,text='Run validation',style='Accent.TButton',command=self.run_validation).pack(side='left')
        self.validation_status=tk.StringVar(value='Ready')
        ttk.Label(toolbar,textvariable=self.validation_status,style='Muted.TLabel').pack(side='left',padx=16)
        self.validation_tree=ttk.Treeview(self.content_frame,columns=('level','file','message'),show='headings',height=16)
        for key,width in [('level',70),('file',250),('message',450)]:
            self.validation_tree.heading(key,text=key.title()); self.validation_tree.column(key,width=width)
        self.validation_tree.pack(fill='both',expand=True,pady=16)
        scroll=ttk.Scrollbar(self.content_frame,orient='horizontal',command=self.validation_tree.xview); scroll.pack(fill='x')
        self.validation_tree.configure(xscrollcommand=scroll.set)

    def run_validation(self):
        if self.is_processing: return
        self.logic._require_mod(); self.is_processing=True; self.validation_status.set('Checking files…')
        def complete(issues,error=None):
            self.is_processing=False
            for row in self.validation_tree.get_children(): self.validation_tree.delete(row)
            for issue in issues: self.validation_tree.insert('', 'end',values=(issue['level'],issue['file'],issue['message']))
            self.validation_status.set(error or f'{sum(i["level"]=="error" for i in issues)} errors · {sum(i["level"]=="warn" for i in issues)} warnings')
        def work():
            try:
                issues=self.logic.validate_mod(); self.ui_queue.put(lambda:complete(issues))
            except Exception as exc:
                error=str(exc); self.ui_queue.put(lambda:complete([],error))
        threading.Thread(target=work,daemon=True).start()

    def __init__(self):
        super().__init__()
        self.title("Victoria 3 Modding Tool")
        self.geometry("850x700")
        self.configure(bg="#28231d")
        self.style = ttk.Style()
        self.style.theme_use('clam')
        self._configure_dark_theme()

        self.log_queue = queue.Queue()
        self.ui_queue = queue.Queue()
        self.logic = Vic3Logic(self.log_message)
        self.logic.choose_transfer_technology = self.choose_building_technology
        self.is_processing = False
        self.cr_rgb = [random.randint(0,255), random.randint(0,255), random.randint(0,255)]

        self._build_ui()
        self.load_config()
        self.after(100, self.process_log_queue)

    def _configure_dark_theme(self):
        bg, panel, entry, line, fg, muted, accent = '#28231d','#352b21','#473a2b','#796341','#f3e7ce','#d4c2a4','#e6bc74'
        self.configure(bg=bg)
        self.option_add('*Font', ('Segoe UI',10))
        self.style.configure('.',background=bg,foreground=fg,font=('Segoe UI',10),borderwidth=0)
        for name in ('TFrame','TLabel','TCheckbutton','TRadiobutton'): self.style.configure(name,background=bg,foreground=fg)
        self.style.configure('TLabelframe',background=bg,bordercolor=line,relief='solid',borderwidth=1)
        self.style.configure('TLabelframe.Label',background=bg,foreground=accent,font=('Segoe UI',10,'bold'))
        self.style.configure('TButton',background=entry,foreground=fg,padding=(12,8),borderwidth=0,focuscolor=line)
        self.style.map('TButton',background=[('active',line),('disabled',panel)],foreground=[('disabled',muted)])
        self.style.configure('Accent.TButton',background=accent,foreground=bg,font=('Segoe UI',10,'bold'))
        self.style.map('Accent.TButton',background=[('active','#f2d298')],foreground=[('active',bg)])
        self.style.configure('Nav.TButton',anchor='w',padding=(14,10),background=panel)
        self.style.configure('Active.Nav.TButton',anchor='w',padding=(14,10),background='#574125',foreground=accent)
        self.style.configure('Sidebar.TFrame',background=panel)
        self.style.configure('Sidebar.TLabel',background=panel,foreground=muted)
        self.style.configure('Title.TLabel',font=('Segoe UI',22,'bold'),foreground=fg)
        self.style.configure('Muted.TLabel',foreground=muted)
        self.style.configure('TEntry',fieldbackground=entry,foreground=fg,insertcolor=fg,bordercolor=line,padding=6)
        self.style.configure('TCombobox',fieldbackground=entry,foreground=fg,background=entry,arrowcolor=accent,padding=5)
        self.style.map('TCombobox',fieldbackground=[('readonly',entry)],foreground=[('readonly',fg)])
        self.option_add('*TCombobox*Listbox.background',entry)
        self.option_add('*TCombobox*Listbox.foreground',fg)
        self.option_add('*TCombobox*Listbox.selectBackground',line)
        self.style.configure('TNotebook',background=bg)
        self.style.configure('TNotebook.Tab',background=panel,foreground=muted,padding=(14,9))
        self.style.map('TNotebook.Tab',background=[('selected',entry)],foreground=[('selected',accent)])
        self.style.configure('Treeview',background=panel,fieldbackground=panel,foreground=fg,rowheight=29)
        self.style.configure('Treeview.Heading',background=entry,foreground=fg,padding=6)
        self.style.map('Treeview',background=[('selected','#574125')],foreground=[('selected','#ffffff')])
        self.style.configure('BlackText.TButton',background=entry,foreground=fg,padding=(12,8))
        self.style.configure('WhiteBorder.TFrame',background=line)
        for name in ('TCheckbutton','TRadiobutton'):
            self.style.map(name,background=[('active',bg)],indicatorcolor=[('selected',accent)])

    def load_config(self):
        path=self.config_path()
        if not path.exists(): return
        try:
            data=json.loads(path.read_text(encoding='utf-8'))
            if data.get('vanilla_path') and Path(data['vanilla_path']).exists():
                self.logic.set_vanilla_path(data['vanilla_path']); self.vanilla_path_var.set(self.logic.vanilla_path)
            if data.get('mod_path') and Path(data['mod_path']).exists():
                self.logic.set_mod_path(data['mod_path']); self.path_var.set(self.logic.mod_path)
        except (OSError,ValueError) as exc: self.log_message(f'Settings could not be loaded: {exc}','warn')

    def save_config(self):
        atomic_text(self.config_path(),json.dumps(dict(mod_path=self.logic.mod_path,vanilla_path=self.logic.vanilla_path),indent=2))

    def _on_canvas_configure(self, event):
        self.canvas.itemconfig(self.canvas.find_withtag("all")[0], width=event.width)

    def _build_ui(self):
        self.title('V3MT 2 • Victoria 3 Modding Studio')
        self.geometry('1280x880')
        self.minsize(1100,800)
        self.path_var, self.vanilla_path_var = tk.StringVar(), tk.StringVar()
        self.autobackup_var = tk.BooleanVar(value=True)
        sidebar=ttk.Frame(self,style='Sidebar.TFrame',padding=(16,24),width=225)
        sidebar.pack(side='left',fill='y'); sidebar.pack_propagate(False)
        ttk.Label(sidebar,text='V3MT',font=('Georgia',27,'bold'),foreground='#e6bc74',background='#352b21').pack(anchor='w')
        ttk.Label(sidebar,text='VICTORIA 3 MODDING STUDIO',style='Sidebar.TLabel',font=('Segoe UI',8)).pack(anchor='w',pady=(2,25))
        self.nav_buttons={}
        sections=[('WORKSPACE',[('Overview',self.show_mod_manager_ui),('Validate mod',self.show_validation_ui)]),
                  ('WORLD',[('Transfer states',self.show_transfer_ui),('Create country',self.show_create_ui),('Modify country',self.show_country_mod_ui),('Flag maker',self.show_flag_ui),('States & population',self.show_state_manager_ui),('Map & custom states',self.show_custom_states_ui)]),
                  ('SOCIETY & POWER',[('Military',self.show_military_ui),('Diplomacy',self.show_diplomacy_ui),('Power blocs',self.show_power_bloc_ui),('Cultures & religions',self.show_rel_cul_ui),('Journals & events',self.show_journal_ui)])]
        for group,items in sections:
            ttk.Label(sidebar,text=group,style='Sidebar.TLabel',font=('Segoe UI',8,'bold')).pack(anchor='w',pady=(12,6))
            for title,command in items:
                button=ttk.Button(sidebar,text=title,style='Nav.TButton',command=lambda t=title,c=command:self.navigate(t,c))
                button.pack(fill='x',pady=2); self.nav_buttons[title]=button
        ttk.Label(sidebar,text=f'{APP_VERSION}  /  Victoria 3 1.15',style='Sidebar.TLabel').pack(side='bottom',anchor='w',pady=8)
        workspace=ttk.Frame(self,padding=(24,18)); workspace.pack(side='left',fill='both',expand=True)
        top=ttk.Frame(workspace); top.pack(fill='x')
        self.page_title=ttk.Label(top,text='Overview',style='Title.TLabel'); self.page_title.pack(side='left')
        ttk.Button(top,text='Backup',command=self.start_backup).pack(side='right')
        ttk.Checkbutton(top,text='Auto-backup',variable=self.autobackup_var,command=self.toggle_auto_backup).pack(side='right',padx=12)
        paths=ttk.Frame(workspace,padding=(0,16)); paths.pack(fill='x')
        paths.columnconfigure(1,weight=1)
        for row,(label,var,callback) in enumerate([('MOD',self.path_var,self.browse_folder),('GAME',self.vanilla_path_var,self.browse_vanilla_folder)]):
            ttk.Label(paths,text=label,style='Muted.TLabel',width=7).grid(row=row,column=0,sticky='w',pady=4)
            ttk.Entry(paths,textvariable=var,state='readonly').grid(row=row,column=1,sticky='ew',padx=8,pady=4)
            ttk.Button(paths,text='Choose…',command=callback).grid(row=row,column=2)
        center=ttk.Frame(workspace); center.pack(fill='both',expand=True)
        self.canvas=tk.Canvas(center,bg='#28231d',highlightthickness=0)
        self.scrollbar=ttk.Scrollbar(center,orient='vertical',command=self.canvas.yview)
        self.scrollbar.pack(side='right',fill='y'); self.canvas.pack(side='left',fill='both',expand=True)
        self.scrollable_frame=ttk.Frame(self.canvas)
        self.canvas.create_window((0,0),window=self.scrollable_frame,anchor='nw')
        self.scrollable_frame.bind('<Configure>',lambda e:self.canvas.configure(scrollregion=self.canvas.bbox('all')))
        self.canvas.configure(yscrollcommand=self.scrollbar.set)
        self.canvas.bind('<Configure>',self._on_canvas_configure)
        self.bind_all('<MouseWheel>',self._scroll_page,add='+')
        self.bind_all('<Button-4>',self._scroll_page,add='+'); self.bind_all('<Button-5>',self._scroll_page,add='+')
        self.content_frame=ttk.Frame(self.scrollable_frame,padding=(0,4,14,8)); self.content_frame.pack(fill='both',expand=True)
        self.action_frame=ttk.Frame(workspace,padding=(0,10)); self.action_frame.pack(fill='x')
        self.run_btn=ttk.Button(self.action_frame,text='Execute',style='Accent.TButton'); self.run_btn.pack(side='right')
        log_frame=ttk.LabelFrame(workspace,text='Activity',padding=10); log_frame.pack(fill='x',pady=(6,0))
        self.log_area=scrolledtext.ScrolledText(log_frame,state='disabled',height=5,bg='#352b21',fg='#e6d7bc',font=('Consolas',9),insertbackground='white',relief='flat',wrap='word')
        self.log_area.pack(fill='x')
        for level,color in [('info','#e6d7bc'),('warn','#efc079'),('error','#ff8c8c'),('success','#e6bc74')]: self.log_area.tag_config(level,foreground=color)
        self.navigate('Overview',self.show_mod_manager_ui)

    def clear_content(self):
        for widget in self.content_frame.winfo_children():
            widget.destroy()
        self.run_btn.pack(side=tk.RIGHT, padx=20) # Restore run button visibility

    # --- MODE 0: MOD MANAGER ---
    def show_mod_manager_ui(self):
        self.clear_content(); self.mode='MOD_MANAGER'; self.run_btn.pack_forget()
        ttk.Label(self.content_frame,text='Build your next alternate history.',font=('Segoe UI',16,'bold')).pack(anchor='w',pady=(14,6))
        ttk.Label(self.content_frame,text='Choose your game installation, open a mod, or start a new project.',style='Muted.TLabel').pack(anchor='w',pady=(0,22))
        f=ttk.LabelFrame(self.content_frame,text='New project',padding=20); f.pack(fill='x',pady=8); f.columnconfigure(1,weight=1)
        self.mm_name=tk.StringVar(); self.mm_loc=tk.StringVar(value=str(Path(self.path_var.get()).parent) if self.path_var.get() else str(Path.home()/'Documents/Paradox Interactive/Victoria 3/mod'))
        ttk.Label(f,text='Mod name').grid(row=0,column=0,sticky='w',pady=8)
        ttk.Entry(f,textvariable=self.mm_name).grid(row=0,column=1,columnspan=2,sticky='ew',padx=(16,0))
        ttk.Label(f,text='Parent folder').grid(row=1,column=0,sticky='w',pady=8)
        ttk.Entry(f,textvariable=self.mm_loc).grid(row=1,column=1,sticky='ew',padx=16)
        ttk.Button(f,text='Choose…',command=self.browse_mod_parent).grid(row=1,column=2)
        ttk.Button(f,text='Create project',style='Accent.TButton',command=self.start_create_mod).grid(row=2,column=1,columnspan=2,sticky='e',pady=(15,0))
        f=ttk.LabelFrame(self.content_frame,text='Scenario setup',padding=20); f.pack(fill='x',pady=16)
        ttk.Label(f,text='Import current starting history before changing countries, ownership or the map.\nExisting mod files are kept. Game definitions stay available as read-only references.',style='Muted.TLabel',wraplength=700).pack(anchor='w')
        ttk.Button(f,text='Import missing scenario files',command=self.start_copy_vanilla).pack(anchor='w',pady=(16,0))
        ttk.Label(self.content_frame,text='Before playing',font=('Segoe UI',12,'bold')).pack(anchor='w',pady=(10,8))
        ttk.Label(self.content_frame,text='Run Validate mod, enable the mod in a launcher playset, then start a fresh game in debug mode.\nReview error.log for script, map and database errors. Static checks cannot replace an in-game test.',style='Muted.TLabel',wraplength=760).pack(anchor='w')

    def browse_mod_parent(self):
        folder = filedialog.askdirectory()
        if folder:
            self.mm_loc.set(folder)

    def ensure_vanilla_path(self):
        path = self.vanilla_path_var.get()
        if path and os.path.exists(path):
            return path

        messagebox.showinfo("Setup", r"Select the victoria 3/game folder, e.g: C:\Program Files (x86)\Steam\steamapps\common\Victoria 3\game")
        folder = filedialog.askdirectory(title="Select Vanilla Game Directory")
        if folder:
            self.vanilla_path_var.set(folder)
            self.logic.set_vanilla_path(folder)
            self.save_config()
            self.log_message(f"Selected Vanilla Path: {folder}")
            return folder
        return None

    def start_create_mod(self):
        if self.is_processing: return
        if self.logic.create_new_mod(self.mm_name.get(),self.mm_loc.get()):
            self.path_var.set(self.logic.mod_path); self.save_config()
            self.log_message('Project created. Import scenario files before editing existing states and countries.','success')

    def start_copy_vanilla(self):
        if self.is_processing: return
        if not self.logic.mod_path or not self.logic.vanilla_path: raise ValueError('Choose both the mod and game folders first.')
        self.is_processing=True
        def work():
            try: self.logic.copy_vanilla_files(self.logic.vanilla_path,self.logic.mod_path)
            except Exception as exc: self.log_message(str(exc),'error')
            finally: self.ui_queue.put(lambda:setattr(self,'is_processing',False))
        threading.Thread(target=work,daemon=True).start()

    def start_backup(self):
        mod_path = self.path_var.get()
        if not mod_path:
             messagebox.showerror("Error", "Mod path not selected.")
             return
        self.logic.backup_mod(mod_path)

    def toggle_auto_backup(self):
        self.logic.auto_backup_enabled = self.autobackup_var.get()
        self.log_message(f"Auto-backup {'enabled' if self.logic.auto_backup_enabled else 'disabled'}.", 'info')

    def choose_building_technology(self, recipient, conflicts):
        def prompt():
            lines = [f"{entry['state']} · {entry['type']} · {', '.join(sorted(needs))}" for entry,needs in conflicts]
            details = '\n'.join(lines[:12])
            if len(lines)>12:
                details += f"\n… and {len(lines)-12} more building entries."
            result = messagebox.askyesnocancel("Transferred buildings",
                f"{recipient}: {len(lines)} incoming building entries require technology that could not be confirmed in starting history.\n\n"
                + details + "\n\nYes — grant the required technologies.\nNo — delete these building entries.\nCancel — stop this transfer.",
                parent=self, default='cancel')
            return 'grant' if result is True else 'delete' if result is False else 'cancel'
        if threading.current_thread() is threading.main_thread():
            return prompt()
        answer = queue.Queue()
        def show():
            try:
                answer.put(prompt())
            except tk.TclError:
                answer.put('cancel')
        self.after(0,show)
        return answer.get()

    def open_editor_picker(self, kind, on_pick):
        if not self.logic.mod_path:
            return messagebox.showinfo("Select from map", "Choose a mod first.")
        if not PIL_AVAILABLE:
            return messagebox.showerror("Select from map", "The map requires Pillow and NumPy.")
        picker = Vic3ProvincePainter(self, self.logic, "PICK_" + kind.upper())
        picker.on_pick = on_pick
        picker.title("Select " + kind + " from map")
        picker.transient(self)
        picker.grab_set()

    def map_field_button(self, parent, variable, load=None):
        def select(owner, state):
            variable.set(owner)
            if load:
                load()
        return ttk.Button(parent, text="Select from map",
                          command=lambda: self.open_editor_picker("country", select))

    def select_map_state(self, owner, state):
        self.sm_state_name.set(state)
        self.load_state_manager_data()

    def select_formation_location(self, owner, state):
        self.mil_tag.set(owner)
        self.mil_state.set(state)
        self.load_military_formations()

    def show_flag_ui(self):
        self.clear_content()
        self.run_btn.pack_forget()
        if not self.logic.mod_path or not PIL_AVAILABLE:
            ttk.Label(self.content_frame,text="Choose a mod and install Pillow and NumPy to edit flags.").pack()
            return
        from PIL import ImageColor
        logic = self.logic
        catalog = logic.flag_catalog()
        textures = {}
        for folder in ('patterns','colored_emblems','textured_emblems'):
            items = textures[folder] = {}
            roots = ([Path(logic.vanilla_path)/'game'] if logic.vanilla_path else [])+[Path(logic.mod_path)]
            for root in roots:
                for path in sorted((root/'gfx/coat_of_arms'/folder).rglob('*')):
                    if path.suffix.lower() in ('.dds','.tga','.png'):
                        items[path.name] = path
        box = ttk.LabelFrame(self.content_frame,text='Flag maker',padding=12)
        box.pack(fill='x')
        bar = ttk.Frame(box)
        bar.pack(anchor='w')
        tag = tk.StringVar()
        ttk.Label(bar,text='Country tag').pack(side='left')
        ttk.Entry(bar,textvariable=tag,width=8).pack(side='left',padx=6)
        draft = ''
        key = ''
        previous = None
        status = tk.StringVar(value='Load a country to edit its base flag.')
        def load():
            nonlocal key, previous, draft
            candidate = logic.format_tag_clean(tag.get())
            identifier(candidate,'Country tag')
            if not logic.tag_exists(candidate):
                raise ValueError('Country tag not found.')
            history.clear()
            key = candidate
            previous = catalog.get(key,(None,None))[1]
            draft = previous if previous is not None else '\n    pattern = "pattern_solid.tga"\n    color1 = "white"\n'
            refresh()
        ttk.Button(bar,text='Load flag',command=load).pack(side='left')
        self.map_field_button(bar,tag,load).pack(side='left')
        canvas = tk.Canvas(box,width=450,height=300,bg='#382e23',highlightthickness=0)
        canvas.pack(anchor='w',pady=8)
        controls = ttk.Frame(box)
        controls.pack(anchor='w')
        def combo(row,label,values):
            ttk.Label(controls,text=label).grid(row=row,column=0,sticky='w')
            widget = ttk.Combobox(controls,values=sorted(values),width=39,state='readonly')
            widget.grid(row=row,column=1,sticky='w',pady=2)
            return widget
        preset = combo(0,'Game flag preset',catalog)
        pattern = combo(1,'Pattern',textures['patterns'])
        palette = ['white','black','red','yellow','green','blue','orange','purple','brown','grey','gold']
        colors = [combo(i+2,f'Pattern colour {i+1}',palette) for i in range(3)]
        emblem = combo(5,'Emblem to place',textures['colored_emblems'])
        ink = combo(6,'Emblem colour',palette)
        ink.set('white')
        scale = tk.DoubleVar(value=0.35)
        ttk.Label(controls,text='Emblem size').grid(row=7,column=0,sticky='w')
        ttk.Scale(controls,from_=0.05,to=1.0,variable=scale).grid(row=7,column=1,sticky='ew')
        ttk.Label(box,text='Select an emblem, then click the preview to place it.').pack(anchor='w')
        history = []
        def rgb(value):
            try: return ImageColor.getrgb(value.replace('_',''))
            except ValueError: return (140,140,140)
        def render(folder,name,size,cols):
            path = textures[folder].get(name)
            if not path: return None
            with Image.open(path) as source:
                image = source.convert('RGBA').resize(size,Image.Resampling.BILINEAR)
            if folder == 'textured_emblems': return image
            pixels = np.asarray(image)
            # Pattern masks use red/yellow/white. Coloured emblems use green/blue channels.
            g,b = (pixels[:,:,i:i+1].astype(float)/255 for i in (1,2))
            base,second,third = (np.array(rgb(c)) for c in cols)
            out = base*(1-g)+second*g
            out = out*(1-b)+third*b
            result = Image.fromarray(out.astype('uint8')).convert('RGBA')
            result.putalpha(image.getchannel('A'))
            return result
        def vector(body,name,default):
            found = script_blocks(body,name,0)
            if found:
                item=found[0]
                try:
                    x,y=map(float,body[item['opening']+1:item['end']-1].split())
                    return x,y
                except ValueError: pass
            return default
        def refresh():
            pattern.set(field(draft,'pattern'))
            cols=[field(draft,'color'+str(i),'white') for i in range(1,4)]
            for widget,c in zip(colors,cols): widget.set(c)
            image=render('patterns',pattern.get(),(450,300),cols)
            missing=image is None
            if missing: image=Image.new('RGBA',(450,300),rgb(cols[0]))
            for layer in script_blocks(draft,depth=0):
                if layer['key'] not in ('colored_emblem','textured_emblem'): continue
                body=draft[layer['opening']+1:layer['end']-1]
                inks=[field(body,'color'+str(i),cols[i-1]) for i in range(1,4)]
                inks=[cols[int(c[-1])-1] if c in ('color1','color2','color3') else c for c in inks]
                instances=[body[n['opening']+1:n['end']-1] for n in script_blocks(body,'instance',0)] or ['']
                for inst in instances:
                    x,y=vector(inst,'position',(0.5,0.5))
                    w,h=vector(inst,'scale',(1,1))
                    stamp=render(layer['key']+'s',field(body,'texture'),(max(1,min(1200,int(abs(w)*450))),max(1,min(1200,int(abs(h)*300)))),inks)
                    if stamp is None:
                        missing=True
                        continue
                    if w<0: stamp=stamp.transpose(Image.Transpose.FLIP_LEFT_RIGHT)
                    if h<0: stamp=stamp.transpose(Image.Transpose.FLIP_TOP_BOTTOM)
                    try: stamp=stamp.rotate(-float(field(inst,'rotation','0')),expand=True)
                    except ValueError: pass
                    image.alpha_composite(stamp,(int(x*450-stamp.width/2),int(y*300-stamp.height/2)))
            canvas.photo=ImageTk.PhotoImage(image)
            canvas.delete('all')
            canvas.create_image(0,0,image=canvas.photo,anchor='nw')
            status.set(f'{key} · Base flag preview'+(' · Some textures unavailable' if missing else ''))
        def update(value):
            nonlocal draft
            if not key: return
            history.append((key,draft))
            draft=value
            refresh()
        def apply_color(i):
            # Replace a scalar or a structured RGB/HSV colour.
            name='color'+str(i+1)
            blocks=script_blocks(draft,name,0)
            value=draft
            if blocks:
                item=blocks[0]
                value=value[:item['start']]+value[item['end']:]
            entry=script_fields(value).get(name)
            if entry and entry[0] in ('rgb','hsv','hsv360'):
                close=value.find('}',entry[2])
                if close>=0: value=value[:entry[1]]+value[close+1:]
            update(put_field(value,name,quoted(colors[i].get())))
        preset.bind('<<ComboboxSelected>>',lambda e:update(catalog[preset.get()][1]))
        pattern.bind('<<ComboboxSelected>>',lambda e:update(put_field(draft,'pattern',quoted(pattern.get()))))
        for i,widget in enumerate(colors):
            widget.bind('<<ComboboxSelected>>',lambda e,i=i:apply_color(i))
        def place(event):
            if emblem.get() and key:
                size=scale.get()
                update(draft+'\n    colored_emblem = { texture = '+quoted(emblem.get())+' color1 = '+quoted(ink.get())+
                       f' instance = {{ position = {{ {event.x/450:.4f} {event.y/300:.4f} }} scale = {{ {size:.4f} {size:.4f} }} }} }}\n')
        canvas.bind('<Button-1>',place)
        def undo():
            nonlocal draft
            if history and history[-1][0]==key:
                _,draft=history.pop()
                refresh()
        def save():
            nonlocal previous
            if not key or logic.format_tag_clean(tag.get())!=key: raise ValueError('Load the country first.')
            logic.save_flag(key,previous,draft)
            catalog.update(logic.flag_catalog())
            previous=draft
            status.set(f'Saved base flag for {key}.')
        actions=ttk.Frame(box)
        actions.pack(anchor='w',pady=6)
        ttk.Button(actions,text='Undo edit',command=undo).pack(side='left')
        ttk.Button(actions,text='Save flag',command=save).pack(side='left',padx=6)
        ttk.Label(box,textvariable=status).pack(anchor='w')

    def open_visual_painter(self):
        if not PIL_AVAILABLE:
            messagebox.showerror("Error", "Pillow (PIL) is not installed. Visual Painter is unavailable.")
            return

        Vic3ProvincePainter(self, self.logic)

    def open_custom_state_painter(self):
        if not PIL_AVAILABLE:
            messagebox.showerror("Error", "Pillow (PIL) is not installed. Visual Painter is unavailable.")
            return

        Vic3ProvincePainter(self, self.logic, start_mode="CUSTOM_STATE")

    # --- MODE 1: TRANSFER STATES ---
    def show_transfer_ui(self):
        self.clear_content()
        self.mode = "TRANSFER"
        f = ttk.LabelFrame(self.content_frame, text="Transfer States Mode", padding=15)
        f.pack(fill=tk.X)

        self.tr_old_tag_lbl = ttk.Label(f, text="Old Owner Tag (e.g. fra):")
        self.tr_old_tag_lbl.grid(row=0, column=0, sticky=tk.W, pady=5)
        self.tr_old_tag = tk.StringVar()
        self.tr_old_tag_entry = ttk.Entry(f, textvariable=self.tr_old_tag, width=25)
        self.tr_old_tag_entry.grid(row=0, column=1, sticky=tk.W, pady=5, padx=5)

        ttk.Label(f, text="New Owner Tag (e.g. gbr):").grid(row=1, column=0, sticky=tk.W, pady=5)
        self.tr_new_tag = tk.StringVar()
        ttk.Entry(f, textvariable=self.tr_new_tag, width=15).grid(row=1, column=1, sticky=tk.W, pady=5, padx=5)

        self.tr_states_lbl = ttk.Label(f, text="States (Space separated):")
        self.tr_states_lbl.grid(row=2, column=0, sticky=tk.NW, pady=8)
        self.tr_states = tk.Text(f, height=4, width=50, bg="#473a2b", fg="#f3e7ce", insertbackground="white", relief="flat", padx=5, pady=5)
        self.tr_states.grid(row=2, column=1, columnspan=2, sticky=tk.W, pady=8, padx=5)

        # Mode Selection
        ttk.Label(f, text="Transfer Mode:").grid(row=3, column=0, sticky=tk.W, pady=5)
        self.tr_mode = tk.StringVar(value="auto")

        m_frame = ttk.Frame(f)
        m_frame.grid(row=3, column=1, columnspan=2, sticky=tk.W, pady=5)

        ttk.Radiobutton(m_frame, text="Auto (All Owners)", variable=self.tr_mode, value="auto", command=self.update_transfer_ui_visibility).pack(side=tk.LEFT, padx=(0,10))
        ttk.Radiobutton(m_frame, text="Targeted (Split State)", variable=self.tr_mode, value="split", command=self.update_transfer_ui_visibility).pack(side=tk.LEFT, padx=(0,10))
        ttk.Radiobutton(m_frame, text="Full Annexation", variable=self.tr_mode, value="annex", command=self.update_transfer_ui_visibility).pack(side=tk.LEFT)

        if PIL_AVAILABLE:
            ttk.Button(m_frame, text="Open Visual Map Painter", command=self.open_visual_painter).pack(side=tk.LEFT, padx=20)

        self.run_btn.config(text="Execute Transfer", command=self.start_transfer, state='normal')
        self.update_transfer_ui_visibility()

    def update_transfer_ui_visibility(self):
        mode = self.tr_mode.get()
        if mode == "annex":
            self.tr_states_lbl.grid_remove()
            self.tr_states.grid_remove()
            self.tr_old_tag_lbl.config(text="Old Owner Tag(s) (Space sep):")
            self.tr_old_tag_lbl.grid()
            self.tr_old_tag_entry.grid()
        elif mode == "split":
            self.tr_states_lbl.grid()
            self.tr_states.grid()
            self.tr_old_tag_lbl.config(text="Old Owner Tag (e.g. fra):")
            self.tr_old_tag_lbl.grid()
            self.tr_old_tag_entry.grid()
        else: # auto
            self.tr_states_lbl.grid()
            self.tr_states.grid()
            self.tr_old_tag_lbl.grid_remove()
            self.tr_old_tag_entry.grid_remove()

    # --- MODE 2: CREATE COUNTRY ---
    def show_create_ui(self):
        self.clear_content()
        self.mode = "CREATE"
        self.country_state_owners = {}

        all_cultures, all_religions, all_tiers, all_types = self.logic.scan_definitions_for_options()

        if not all_tiers: all_tiers = ["empire", "kingdom", "grand_principality", "principality", "city_state"]
        if not all_types: all_types = ["recognized", "unrecognized", "colonial"]

        f = ttk.LabelFrame(self.content_frame, text="Create Country Mode", padding=15)
        f.pack(fill=tk.X)

        def open_country_map():
            if not self.logic.mod_path:
                return messagebox.showinfo("Country map", "Choose a mod first.")
            painter = Vic3ProvincePainter(self, self.logic, "COUNTRY")
            painter.transient(self)
            painter.grab_set()
        ttk.Button(f, text="Choose capital and states on map", command=open_country_map).grid(row=8,column=0,columnspan=4,sticky="ew",pady=8)

        # Row 0
        ttk.Label(f, text="New Country Tag (3 chars):").grid(row=0, column=0, sticky=tk.W, pady=5)
        self.cr_tag = tk.StringVar()
        ttk.Entry(f, textvariable=self.cr_tag, width=10).grid(row=0, column=1, sticky=tk.W, pady=5)

        ttk.Label(f, text="Country Name:").grid(row=0, column=2, sticky=tk.W, pady=5, padx=10)
        self.cr_name = tk.StringVar()
        ttk.Entry(f, textvariable=self.cr_name, width=25).grid(row=0, column=3, sticky=tk.W, pady=5)

        # Row 1
        ttk.Label(f, text="Adjective:").grid(row=1, column=0, sticky=tk.W, pady=5)
        self.cr_adj = tk.StringVar()
        ttk.Entry(f, textvariable=self.cr_adj, width=25).grid(row=1, column=1, sticky=tk.W, pady=5)

        ttk.Label(f, text="Taken From (Old Tag):").grid(row=1, column=2, sticky=tk.W, pady=5, padx=10)
        self.cr_old_owner = tk.StringVar()
        e_old = ttk.Entry(f, textvariable=self.cr_old_owner, width=10)
        e_old.grid(row=1, column=3, sticky=tk.W, pady=5)
        e_old.bind("<FocusOut>", self.on_old_owner_change)
        
        # Row 2
        ttk.Label(f, text="Capital State (e.g. aquitaine):").grid(row=2, column=0, sticky=tk.W, pady=5)
        self.cr_capital = tk.StringVar()
        ttk.Entry(f, textvariable=self.cr_capital, width=25).grid(row=2, column=1, sticky=tk.W, pady=5)
        
        self.cr_annex = tk.BooleanVar()
        self.cr_annex_button = ttk.Checkbutton(f, text="Full Annexation", variable=self.cr_annex, command=self.toggle_annex_ui)
        self.cr_annex_button.grid(row=2, column=2, columnspan=2, sticky=tk.W, padx=10)

        # Row 3
        ttk.Label(f, text="Tier:").grid(row=3, column=0, sticky=tk.W, pady=5)
        self.cr_tier = tk.StringVar(value="principality")
        ttk.Combobox(f, textvariable=self.cr_tier, values=all_tiers, state="readonly").grid(row=3, column=1, sticky=tk.W, pady=5)

        ttk.Label(f, text="Type:").grid(row=3, column=2, sticky=tk.W, pady=5, padx=10)
        self.cr_type = tk.StringVar(value="recognized")
        ttk.Combobox(f, textvariable=self.cr_type, values=all_types, state="readonly").grid(row=3, column=3, sticky=tk.W, pady=5)

        # Row 4 (Gov Type Removed - Auto-Inherit)
        ttk.Button(f, text="Pick Color", command=self.pick_color).grid(row=4, column=0, sticky=tk.W, padx=5, pady=5)
        self.color_preview = tk.Label(f, text="     ", bg=self._rgb_to_hex(self.cr_rgb), relief="solid", borderwidth=1)
        self.color_preview.grid(row=4, column=1, sticky=tk.W)

        # Row 5: Cultures
        self.all_cultures_data = all_cultures
        self.country_religions = all_religions
        f_cult = ttk.LabelFrame(f, text="Cultures (Defaults to old tag's default culture)", padding=5)
        f_cult.grid(row=5, column=0, columnspan=2, sticky=tk.NSEW, pady=5)

        self.cr_cult_search = tk.StringVar()
        self.cb_cultures = ttk.Combobox(f_cult, textvariable=self.cr_cult_search, values=all_cultures)
        self.cb_cultures.pack(fill=tk.X)
        self.cb_cultures.bind("<<ComboboxSelected>>", self.add_culture_from_combo)
        culture_suggestions(self.cb_cultures, all_cultures, self.add_culture_from_combo)

        self.lb_cultures = tk.Listbox(f_cult, height=4, bg="#473a2b", fg="#f3e7ce", selectmode=tk.SINGLE)
        self.lb_cultures.pack(fill=tk.BOTH, expand=True, pady=2)

        ttk.Button(f_cult, text="Remove Selected", command=self.remove_culture).pack(fill=tk.X)
        self.selected_cultures = []

        # Row 5: Religion
        f_rel = ttk.LabelFrame(f, text="Religion (Defaults to old tag's default religion)", padding=5)
        f_rel.grid(row=5, column=2, columnspan=2, sticky=tk.NSEW, pady=5, padx=5)

        canvas = tk.Canvas(f_rel, bg="#28231d", height=100)
        scrollbar = ttk.Scrollbar(f_rel, orient="vertical", command=canvas.yview)
        self.scrollable_rel_frame = ttk.Frame(canvas)

        self.scrollable_rel_frame.bind("<Configure>", lambda e: canvas.configure(scrollregion=canvas.bbox("all")))
        canvas.create_window((0, 0), window=self.scrollable_rel_frame, anchor="nw")
        canvas.configure(yscrollcommand=scrollbar.set)

        canvas.pack(side="left", fill="both", expand=True)
        scrollbar.pack(side="right", fill="y")

        self.cr_religion = tk.StringVar()
        for r in all_religions:
            ttk.Radiobutton(self.scrollable_rel_frame, text=r, variable=self.cr_religion, value=r).pack(anchor=tk.W)

        # Row 6
        self.lbl_others = ttk.Label(f, text="Other States (Space sep.):\n(Choose states and owners on the map)")
        self.lbl_others.grid(row=6, column=0, sticky=tk.NW, pady=5)
        self.cr_others = tk.Text(f, height=3, width=40, bg="#473a2b", fg="#f3e7ce", insertbackground="white", relief="flat")
        self.cr_others.grid(row=6, column=1, columnspan=3, sticky=tk.W, pady=5)

        # Row 7: Population Settings
        pop_frame = ttk.LabelFrame(f, text="Population Settings (Defaults to old tag's by default)", padding=5)
        pop_frame.grid(row=7, column=0, columnspan=4, sticky=tk.NSEW, pady=5)

        ttk.Label(pop_frame, text="Starting Wealth:").grid(row=0, column=0, sticky=tk.W)
        self.cr_pop_wealth = tk.StringVar()
        w_opts = [
            "effect_starting_pop_wealth_low",
            "effect_starting_pop_wealth_medium",
            "effect_starting_pop_wealth_high",
            "effect_starting_pop_wealth_very_high"
        ]
        ttk.Combobox(pop_frame, textvariable=self.cr_pop_wealth, values=w_opts, state="readonly", width=35).grid(row=0, column=1, sticky=tk.W, padx=5)

        ttk.Label(pop_frame, text="Starting Literacy:").grid(row=0, column=2, sticky=tk.W, padx=(10,0))
        self.cr_pop_lit = tk.StringVar()
        l_opts = [
            "effect_starting_pop_literacy_baseline",
            "effect_starting_pop_literacy_very_low",
            "effect_starting_pop_literacy_low",
            "effect_starting_pop_literacy_middling",
            "effect_starting_pop_literacy_high",
            "effect_starting_pop_literacy_very_high"
        ]
        ttk.Combobox(pop_frame, textvariable=self.cr_pop_lit, values=l_opts, state="readonly", width=35).grid(row=0, column=3, sticky=tk.W, padx=5)

        self.run_btn.config(text="Create & Transfer", command=self.start_create, state='normal')

    def toggle_annex_ui(self):
        if self.cr_annex.get():
            self.lbl_others.grid_remove()
            self.cr_others.grid_remove()
        else:
            self.lbl_others.grid()
            self.cr_others.grid()

    def on_old_owner_change(self, event):
        # User requested to NOT populate the UI boxes automatically to keep them blank.
        # The background logic in start_create will handle defaults if these remain empty.
        pass
    
    def filter_culture_options(self, event):
        typed = self.cr_cult_search.get().strip().lower()
        if not typed:
            self.cb_cultures['values'] = self.all_cultures_data
        else:
            filtered = [c for c in self.all_cultures_data if c.lower().startswith(typed)]
            self.cb_cultures['values'] = filtered

            # Optional: Open the dropdown if there are matches (can be intrusive, but user requested 'visible')
            # if filtered:
            #     self.cb_cultures.event_generate('<Down>')

    def add_culture_from_combo(self, event):
        val = self.cr_cult_search.get()
        self.add_culture(val)
        self.cr_cult_search.set("")
        self.cb_cultures['values'] = self.all_cultures_data

    def add_culture(self, culture):
        if culture and culture not in self.selected_cultures:
            self.selected_cultures.append(culture)
            self.lb_cultures.insert(tk.END, culture)

    def remove_culture(self):
        sel = self.lb_cultures.curselection()
        if sel:
            idx = sel[0]
            val = self.lb_cultures.get(idx)
            self.selected_cultures.remove(val)
            self.lb_cultures.delete(idx)

    # --- MODE 3: MILITARY CREATOR ---
    def show_military_ui(self):
        self.clear_content()
        self.mode = "MILITARY"

        # --- Frame 1: Create New ---
        f = ttk.LabelFrame(self.content_frame, text="Create Military Formation", padding=15)
        f.pack(fill=tk.X, pady=(0, 10))

        # Basic Info
        ttk.Label(f, text="Country Tag:").grid(row=0, column=0, sticky=tk.W, pady=5)
        self.mil_tag = tk.StringVar()
        ttk.Entry(f, textvariable=self.mil_tag, width=10).grid(row=0, column=1, sticky=tk.W, pady=5, padx=5)

        ttk.Label(f, text="Formation Name:").grid(row=0, column=2, sticky=tk.W, pady=5)
        self.mil_name = tk.StringVar(value="First Army")
        ttk.Entry(f, textvariable=self.mil_name, width=20).grid(row=0, column=3, sticky=tk.W, pady=5, padx=5)

        ttk.Label(f, text="Target State:").grid(row=1, column=0, sticky=tk.W, pady=5)
        self.mil_state = tk.StringVar()
        ttk.Entry(f, textvariable=self.mil_state, width=20).grid(row=1, column=1, sticky=tk.W, pady=5, padx=5)

        self.mil_loc_lbl = ttk.Label(f, text="(Leave blank for capital; explicit state must be owned)")
        self.mil_loc_lbl.grid(row=1, column=2, columnspan=2, sticky=tk.W)
        ttk.Button(f, text="Select from map", command=lambda: self.open_editor_picker("state", self.select_formation_location)).grid(row=2,column=3,sticky=tk.W)

        # Type Selection
        ttk.Label(f, text="Formation Type:").grid(row=2, column=0, sticky=tk.W, pady=10)
        self.mil_type = tk.StringVar(value="army")
        tf = ttk.Frame(f)
        tf.grid(row=2, column=1, columnspan=3, sticky=tk.W, pady=10)
        ttk.Radiobutton(tf, text="Army", variable=self.mil_type, value="army", command=self.update_mil_inputs).pack(side=tk.LEFT, padx=(0, 10))
        ttk.Radiobutton(tf, text="Navy", variable=self.mil_type, value="navy", command=self.update_mil_inputs).pack(side=tk.LEFT)

        # Units Frame
        self.mil_unit_frame = ttk.LabelFrame(f, text="Composition", padding=10)
        self.mil_unit_frame.grid(row=3, column=0, columnspan=4, sticky=tk.W+tk.E, pady=10)

        ttk.Button(f, text="Create New Formation", command=self.start_create_military).grid(row=4, column=0, columnspan=4, pady=10)

        # Initialize inputs
        self.update_mil_inputs()

        self.run_btn.pack_forget() # Hide the main run button as we use local ones

        # --- Frame 2: Manage Existing ---
        m = ttk.LabelFrame(self.content_frame, text="Manage Existing Formations", padding=15)
        m.pack(fill=tk.BOTH, expand=True, pady=10)

        # Controls
        mc = ttk.Frame(m)
        mc.pack(fill=tk.X, pady=(0, 5))
        
        ttk.Label(mc, text="Tag to Manage:").pack(side=tk.LEFT)
        # Reuse mil_tag or separate? Let's reuse for convenience
        ttk.Entry(mc, textvariable=self.mil_tag, width=10).pack(side=tk.LEFT, padx=5)
        ttk.Button(mc, text="Load Formations", command=self.load_military_formations).pack(side=tk.LEFT, padx=5)
        self.map_field_button(mc, self.mil_tag, self.load_military_formations).pack(side=tk.LEFT,padx=5)

        def rename_transferred():
            tag = self.mil_tag.get().strip()
            if tag:
                self.logic.rename_transfer_placeholders(tag)
                self.load_military_formations()
        ttk.Button(mc, text="Rename transferred formations", command=rename_transferred).pack(side=tk.LEFT, padx=5)

        # List
        self.mil_listbox = tk.Listbox(m, height=8, bg="#473a2b", fg="#f3e7ce")
        self.mil_listbox.pack(fill=tk.BOTH, expand=True, pady=5)
        self.mil_listbox.bind('<<ListboxSelect>>', self.on_formation_select)

        # Edit Area
        self.mil_edit_frame = ttk.LabelFrame(m, text="Edit Selected", padding=10)
        self.mil_edit_frame.pack(fill=tk.X, pady=5)

        # Name
        ttk.Label(self.mil_edit_frame, text="Name:").grid(row=0, column=0, sticky=tk.W)
        self.mil_edit_name = tk.StringVar()
        ttk.Entry(self.mil_edit_frame, textvariable=self.mil_edit_name, width=25).grid(row=0, column=1, sticky=tk.W, padx=5)

        # Dynamic Unit Edits
        # Instead of fixed fields, let's use a text representation or a small dynamic grid?
        # Fixed fields are safer for simple edits.
        # We can detect type from selection and show Army/Navy fields.
        self.mil_edit_units_frame = ttk.Frame(self.mil_edit_frame)
        self.mil_edit_units_frame.grid(row=1, column=0, columnspan=4, pady=5, sticky=tk.W)

        # Buttons
        btn_f = ttk.Frame(self.mil_edit_frame)
        btn_f.grid(row=2, column=0, columnspan=4, pady=5, sticky=tk.E)
        
        ttk.Button(btn_f, text="Delete Formation", command=self.execute_delete_formation).pack(side=tk.RIGHT, padx=5)
        ttk.Button(btn_f, text="Update Formation", command=self.execute_update_formation).pack(side=tk.RIGHT, padx=5)

        self.current_formations = [] # Data cache
        self.selected_formation_index = -1
        
        # Unit Vars for Edit
        self.mil_edit_u1 = tk.IntVar()
        self.mil_edit_u2 = tk.IntVar()
        self.mil_edit_u3 = tk.IntVar()
    def update_mil_inputs(self):
        for widget in self.mil_unit_frame.winfo_children(): widget.destroy()
        navy=self.mil_type.get()=='navy'
        self.mil_name.set('First Fleet' if navy else 'First Army')
        self.mil_loc_lbl.configure(text='Leave blank for the owned capital; HQ comes from current regions.',foreground='#d4c2a4')
        keys=self.logic.definition_keys('common/ship_types' if navy else 'common/combat_unit_types')
        if not navy: keys=[k for k in keys if not any(x in k for x in ('man_o_war','frigate','ironclad','monitor','dreadnought','submarine','carrier','battleship'))]
        defaults=['ship_type_ship_of_the_line','ship_type_frigate','ship_type_ironclad'] if navy else ['combat_unit_type_line_infantry','combat_unit_type_cannon_artillery','combat_unit_type_hussars']
        self.mil_create_rows=[]
        if not keys:
            ttk.Label(self.mil_unit_frame,text='Choose current game files to load available unit types.',foreground='#efc079').grid(row=0,column=0,columnspan=3,sticky='w')
        for row in range(3):
            key=tk.StringVar(value=defaults[row] if defaults[row] in keys else (keys[0] if keys else ''))
            count=tk.StringVar(value='5' if row==0 else '0')
            self.mil_create_rows.append((key,count))
            ttk.Label(self.mil_unit_frame,text='Ship type' if navy else 'Unit type').grid(row=row+1,column=0,sticky='w',pady=3)
            ttk.Combobox(self.mil_unit_frame,textvariable=key,values=keys,state='readonly',width=40).grid(row=row+1,column=1,padx=10,sticky='ew')
            ttk.Entry(self.mil_unit_frame,textvariable=count,width=8).grid(row=row+1,column=2)
        self.mil_unit_frame.columnconfigure(1,weight=1)

    def start_create_military(self):
        if self.is_processing: return
        units={}
        for key,count in self.mil_create_rows:
            value=nonnegative(count.get())
            if value: units[key.get()]=units.get(key.get(),0)+value
        self.logic._write_formation(self.mil_tag.get(),self.mil_name.get(),self.mil_state.get(),units,fleet=self.mil_type.get()=='navy')
        self.load_military_formations()
    def load_military_formations(self):
        tag = self.logic.format_tag_clean(self.mil_tag.get())
        if not tag: return messagebox.showerror("Error", "Tag required.")
        
        self.current_formations = self.logic.scan_military_formations(tag)
        self.mil_listbox.delete(0, tk.END)
        
        for f in self.current_formations:
            # Format: Name (Type) - HQ - X units
            total_units = sum(f['units'].values())
            display = f"{f['name']} ({f['type']}) - {f['hq']} - {total_units} units"
            self.mil_listbox.insert(tk.END, display)
            
        self.log_message(f"Loaded {len(self.current_formations)} formations for {tag}", 'success')

    def on_formation_select(self, event=None):
        selection=self.mil_listbox.curselection()
        if not selection: return
        self.selected_formation_index=selection[0]
        data=self.current_formations[selection[0]]
        self.mil_edit_name.set(data['name'])
        for widget in self.mil_edit_units_frame.winfo_children(): widget.destroy()
        self.mil_edit_vars={}
        for row,(key,value) in enumerate(data['units'].items()):
            var=tk.StringVar(value=str(value)); self.mil_edit_vars[key]=var
            ttk.Label(self.mil_edit_units_frame,text=key.split(':')[-1]).grid(row=row,column=0,sticky='w',pady=3)
            ttk.Entry(self.mil_edit_units_frame,textvariable=var,width=10).grid(row=row,column=1,padx=12)

    def execute_update_formation(self):
        if self.is_processing or self.selected_formation_index<0: return
        data=self.current_formations[self.selected_formation_index]
        new_units={key:nonnegative(var.get()) for key,var in self.mil_edit_vars.items()}
        self.logic.save_military_formation(data,self.mil_edit_name.get(),new_units)
        self.load_military_formations()
        self.selected_formation_index=-1
        self.log_message('Formation saved; unit types and extra fields preserved.','success')

    def execute_delete_formation(self):
        if self.selected_formation_index < 0: return
        data = self.current_formations[self.selected_formation_index]
        
        if messagebox.askyesno("Confirm", f"Delete formation '{data['name']}'?"):
            success = self.logic.delete_formation_ui(data)
            if success:
                messagebox.showinfo("Success", "Formation deleted.")
                self.load_military_formations()
            else:
                messagebox.showerror("Error", "Could not delete formation.")
    def _rgb_to_hex(self, rgb):
        return f'#{rgb[0]:02x}{rgb[1]:02x}{rgb[2]:02x}'

    def pick_color(self):
        init_color = self._rgb_to_hex(self.cr_rgb)
        color = colorchooser.askcolor(color=init_color, title="Choose Country Color")
        if color[0]:
            self.cr_rgb = [int(x) for x in color[0]]
            self.color_preview.config(bg=color[1])

    # --- MODE 5: COUNTRY MODIFICATION ---
    def show_country_mod_ui(self):
        self.clear_content()
        self.mode = "MOD_COUNTRY"
        f = ttk.LabelFrame(self.content_frame, text="Modify Country", padding=15)
        f.pack(fill=tk.BOTH, expand=True)

        # Tag Input & Load
        top_frame = ttk.Frame(f)
        top_frame.pack(fill=tk.X, pady=5)
        ttk.Label(top_frame, text="Country Tag:").pack(side=tk.LEFT)
        self.mc_tag = tk.StringVar()
        ttk.Entry(top_frame, textvariable=self.mc_tag, width=10).pack(side=tk.LEFT, padx=5)
        ttk.Button(top_frame, text="Load Data", command=self.load_country_mod_data).pack(side=tk.LEFT, padx=5)
        self.map_field_button(top_frame, self.mc_tag, self.load_country_mod_data).pack(side=tk.LEFT, padx=5)

        # Identity
        id_frame = ttk.LabelFrame(f, text="Country Identity", padding=5)
        id_frame.pack(fill=tk.X, pady=5)

        ttk.Label(id_frame, text="Name:").grid(row=0, column=0, sticky=tk.W)
        self.mc_name = tk.StringVar()
        ttk.Entry(id_frame, textvariable=self.mc_name, width=30).grid(row=0, column=1, sticky=tk.W, padx=5)

        ttk.Label(id_frame, text="Adjective:").grid(row=0, column=2, sticky=tk.W)
        self.mc_adj = tk.StringVar()
        ttk.Entry(id_frame, textvariable=self.mc_adj, width=30).grid(row=0, column=3, sticky=tk.W, padx=5)

        ttk.Button(id_frame, text="Color Picker", command=self.pick_color_mod).grid(row=0, column=4, padx=5)
        self.mc_rgb = [255, 255, 255]
        self.mc_color_prev = tk.Label(id_frame, text="     ", bg="#FFFFFF", relief="solid", borderwidth=1)
        self.mc_color_prev.grid(row=0, column=5)

        # Cultural & Religious Identity
        cr_frame = ttk.LabelFrame(f, text="Culture & Religion", padding=5)
        cr_frame.pack(fill=tk.X, pady=5)

        ttk.Label(cr_frame, text="Primary Cultures:").grid(row=0, column=0, sticky=tk.NW, pady=2)

        # Primary Cultures Listbox & Controls
        pc_frame = ttk.Frame(cr_frame)
        pc_frame.grid(row=0, column=1, sticky=tk.W, padx=5)

        self.lb_mc_cultures = tk.Listbox(pc_frame, height=4, width=30, bg="#473a2b", fg="#f3e7ce")
        self.lb_mc_cultures.pack(side=tk.LEFT, fill=tk.BOTH)

        pc_ctrl = ttk.Frame(pc_frame)
        pc_ctrl.pack(side=tk.LEFT, fill=tk.Y, padx=(2,0))

        self.mc_cul_add_var = tk.StringVar()
        self.cb_mc_cul_add = ttk.Combobox(pc_ctrl, textvariable=self.mc_cul_add_var, width=15)
        self.cb_mc_cul_add.pack(pady=(0,2))

        ttk.Button(pc_ctrl, text="Add", width=8, command=self.add_mc_culture).pack(pady=1)
        ttk.Button(pc_ctrl, text="Remove", width=8, command=self.remove_mc_culture).pack(pady=1)

        ttk.Label(cr_frame, text="State Religion:").grid(row=0, column=2, sticky=tk.NW, padx=(10,0), pady=2)
        self.mc_religion = tk.StringVar()
        # Will populate this on load usually, or init
        self.mc_religion_cb = ttk.Combobox(cr_frame, textvariable=self.mc_religion, state="normal", width=20)
        self.mc_religion_cb.grid(row=0, column=3, sticky=tk.NW, padx=5, pady=2)

        # Conversion Tools
        conv_frame = ttk.LabelFrame(cr_frame, text="Population Conversion Tool", padding=5)
        conv_frame.grid(row=1, column=0, columnspan=4, sticky=tk.NSEW, pady=5)

        # Row 0
        ttk.Label(conv_frame, text="New Culture:").grid(row=0, column=0, sticky=tk.W)
        self.mc_conv_cul = tk.StringVar()
        self.cb_conv_cul = ttk.Combobox(conv_frame, textvariable=self.mc_conv_cul, state="readonly", width=25)
        self.cb_conv_cul.grid(row=0, column=1, padx=5, sticky=tk.W)

        ttk.Label(conv_frame, text="New Religion:").grid(row=0, column=2, sticky=tk.W, padx=(10,0))
        self.mc_conv_rel = tk.StringVar()
        self.cb_conv_rel = ttk.Combobox(conv_frame, textvariable=self.mc_conv_rel, state="readonly", width=25)
        self.cb_conv_rel.grid(row=0, column=3, padx=5, sticky=tk.W)
        ttk.Button(conv_frame, text="Deselect", command=self.deselect_conversion).grid(row=0, column=4, padx=5)

        # Row 1: Mode + Value (Dynamic)
        f_mode = ttk.Frame(conv_frame)
        f_mode.grid(row=1, column=0, columnspan=4, sticky=tk.W, pady=(5,0))
        
        self.mc_conv_mode = tk.StringVar(value="full")
        ttk.Radiobutton(f_mode, text="Full", variable=self.mc_conv_mode, value="full", command=self.toggle_conv_mode).pack(side=tk.LEFT, padx=(0, 10))
        ttk.Radiobutton(f_mode, text="Partial", variable=self.mc_conv_mode, value="partial", command=self.toggle_conv_mode).pack(side=tk.LEFT, padx=(0, 10))

        # Dynamic Value Entry Frame
        self.f_val = ttk.Frame(f_mode)
        self.mc_conv_lbl = ttk.Label(self.f_val, text='Value (%, or a range ie: 50-70%):')
        self.mc_conv_lbl.pack(side=tk.LEFT, padx=(0, 5))
        self.mc_conv_val = tk.StringVar()
        self.mc_conv_ent = ttk.Entry(self.f_val, textvariable=self.mc_conv_val, width=10)
        self.mc_conv_ent.pack(side=tk.LEFT)
        # self.f_val.pack() # Hide initially by not packing

        # Row 2: Execute
        f_actions = ttk.Frame(conv_frame)
        f_actions.grid(row=2, column=0, columnspan=4, sticky=tk.W+tk.E, pady=(5,0))

        ttk.Button(f_actions, text="Execute Conversion", command=self.execute_country_conversion).pack(side=tk.LEFT)

        # Internal Politics
        pol_frame = ttk.LabelFrame(f, text="Internal Politics", padding=5)
        pol_frame.pack(fill=tk.X, pady=5)

        ttk.Label(pol_frame, text="Government:").grid(row=0, column=0, sticky=tk.W)
        self.mc_law_gov = tk.StringVar()
        ttk.Combobox(pol_frame, textvariable=self.mc_law_gov, values=["law_monarchy", "law_presidential_republic", "law_parliamentary_republic", "law_theocracy", "law_council_republic"], state="readonly").grid(row=0, column=1, sticky=tk.W, padx=5)

        ttk.Label(pol_frame, text="Economic System:").grid(row=1, column=0, sticky=tk.W)
        self.mc_law_eco = tk.StringVar()
        ttk.Combobox(pol_frame, textvariable=self.mc_law_eco, values=["law_interventionism", "law_laissez_faire", "law_command_economy", "law_traditionalism", "law_agrarianism"], state="readonly").grid(row=1, column=1, sticky=tk.W, padx=5)

        ttk.Label(pol_frame, text="Trade Policy:").grid(row=1, column=2, sticky=tk.W)
        self.mc_law_trade = tk.StringVar()
        ttk.Combobox(pol_frame, textvariable=self.mc_law_trade, values=["law_free_trade", "law_protectionism", "law_isolationism", "law_mercantilism"], state="readonly").grid(row=1, column=3, sticky=tk.W, padx=5)

        ttk.Label(pol_frame, text="Power Structure:").grid(row=2, column=0, sticky=tk.W)
        self.mc_law_power = tk.StringVar()
        ttk.Combobox(pol_frame, textvariable=self.mc_law_power, values=["law_autocracy", "law_oligarchy", "law_landed_voting", "law_wealth_voting", "law_census_voting", "law_universal_suffrage", "law_anarchy", "law_single_party_state"], state="readonly").grid(row=2, column=1, sticky=tk.W, padx=5)

        ttk.Label(pol_frame, text="Capital State:").grid(row=2, column=2, sticky=tk.W)
        self.mc_capital = tk.StringVar()
        ttk.Entry(pol_frame, textvariable=self.mc_capital, width=20).grid(row=2, column=3, sticky=tk.W, padx=5)

        # Ruler Designer
        rul_frame = ttk.LabelFrame(f, text="Ruler Designer", padding=5)
        rul_frame.pack(fill=tk.X, pady=5)

        ttk.Label(rul_frame, text="First Name:").grid(row=0, column=0, sticky=tk.W)
        self.mc_r_first = tk.StringVar()
        ttk.Entry(rul_frame, textvariable=self.mc_r_first).grid(row=0, column=1, padx=5)

        ttk.Label(rul_frame, text="Last Name:").grid(row=0, column=2, sticky=tk.W)
        self.mc_r_last = tk.StringVar()
        ttk.Entry(rul_frame, textvariable=self.mc_r_last).grid(row=0, column=3, padx=5)

        ttk.Label(rul_frame, text="Interest Group:").grid(row=1, column=0, sticky=tk.W)
        self.mc_r_ig = tk.StringVar()
        igs = ["ig_landowners", "ig_industrialists", "ig_intelligentsia", "ig_armed_forces", "ig_devout", "ig_petty_bourgeoisie", "ig_trade_unions", "ig_rural_folk"]
        ttk.Combobox(rul_frame, textvariable=self.mc_r_ig, values=igs, state="readonly").grid(row=1, column=1, padx=5)

        ttk.Label(rul_frame, text="Ideology:").grid(row=1, column=2, sticky=tk.W)
        self.mc_r_ideo = tk.StringVar()
        ideos = ["ideology_traditionalist", "ideology_slaver", "ideology_royalist", "ideology_theocrat", "ideology_liberal", "ideology_market_liberal", "ideology_protectionist", "ideology_abolitionist", "ideology_radical", "ideology_republican", "ideology_democrat", "ideology_jingoist", "ideology_pacifist", "ideology_moderate"]
        ttk.Combobox(rul_frame, textvariable=self.mc_r_ideo, values=ideos, state="readonly").grid(row=1, column=3, padx=5)

        # Population Settings
        pop_frame = ttk.LabelFrame(f, text="Population Settings", padding=5)
        pop_frame.pack(fill=tk.X, pady=5)

        ttk.Label(pop_frame, text="Starting Wealth:").grid(row=0, column=0, sticky=tk.W)
        self.mc_pop_wealth = tk.StringVar()
        w_opts = [
            "effect_starting_pop_wealth_low",
            "effect_starting_pop_wealth_medium",
            "effect_starting_pop_wealth_high",
            "effect_starting_pop_wealth_very_high"
        ]
        ttk.Combobox(pop_frame, textvariable=self.mc_pop_wealth, values=w_opts, state="readonly", width=35).grid(row=0, column=1, sticky=tk.W, padx=5)

        ttk.Label(pop_frame, text="Starting Literacy:").grid(row=0, column=2, sticky=tk.W, padx=(10,0))
        self.mc_pop_lit = tk.StringVar()
        l_opts = [
            "effect_starting_pop_literacy_baseline",
            "effect_starting_pop_literacy_very_low",
            "effect_starting_pop_literacy_low",
            "effect_starting_pop_literacy_middling",
            "effect_starting_pop_literacy_high",
            "effect_starting_pop_literacy_very_high"
        ]
        ttk.Combobox(pop_frame, textvariable=self.mc_pop_lit, values=l_opts, state="readonly", width=35).grid(row=0, column=3, sticky=tk.W, padx=5)

        # Copy from tag
        ttk.Label(pop_frame, text="Copy From Tag:").grid(row=1, column=0, sticky=tk.W, pady=5)
        self.mc_pop_copy_tag = tk.StringVar()
        ttk.Entry(pop_frame, textvariable=self.mc_pop_copy_tag, width=10).grid(row=1, column=1, sticky=tk.W, padx=5, pady=5)
        ttk.Button(pop_frame, text="Copy Settings", command=self.copy_pop_settings).grid(row=1, column=2, sticky=tk.W, padx=5, pady=5)

        ttk.Label(pop_frame, text="Total Population:").grid(row=2, column=0, sticky=tk.W, pady=5)
        self.mc_total_pop = tk.StringVar()
        ttk.Entry(pop_frame, textvariable=self.mc_total_pop, width=15).grid(row=2, column=1, sticky=tk.W, padx=5, pady=5)
        ttk.Button(pop_frame, text="Distribute New Total", command=self.update_country_total_pop).grid(row=2, column=2, sticky=tk.W, padx=5, pady=5)

        self.run_btn.config(text="Save Changes", command=self.save_country_mod_changes, state='normal')

    def add_mc_culture(self):
        val = self.mc_cul_add_var.get().strip()
        if val:
            # Check duplicates
            current = self.lb_mc_cultures.get(0, tk.END)
            if val not in current:
                self.lb_mc_cultures.insert(tk.END, val)
                self.mc_cul_add_var.set("")

    def remove_mc_culture(self):
        sel = self.lb_mc_cultures.curselection()
        if sel:
            self.lb_mc_cultures.delete(sel[0])

    def deselect_conversion(self):
        self.mc_conv_cul.set("")
        self.mc_conv_rel.set("")

    def load_country_mod_data(self):
        tag = self.logic.format_tag_clean(self.mc_tag.get())
        if not tag: return messagebox.showerror("Error", "Enter a tag.")

        # Identity
        name, adj = self.logic.load_country_localization(tag)
        self.mc_name.set(name)
        self.mc_adj.set(adj)

        # Get extended definition data (includes cultures, religion)
        def_data = self.logic.get_country_data(tag)
        self.lb_mc_cultures.delete(0, tk.END)
        if def_data["cultures"]:
            for c in def_data["cultures"].split():
                self.lb_mc_cultures.insert(tk.END, c)
        if def_data["religion"]: self.mc_religion.set(def_data["religion"])

        # Populate religion options dynamically
        _, rels, _, _ = self.logic.scan_definitions_for_options()
        # Also include any scanned from files
        r_scanned, _ = self.logic.scan_all_religions_and_heritages()
        all_rels = sorted(list(set(rels + r_scanned)))
        self.mc_religion_cb['values'] = all_rels

        rgb, cap, _ = self.logic.load_country_definition_data(tag)
        if rgb:
            self.mc_rgb = list(rgb)
            self.mc_color_prev.config(bg=self._rgb_to_hex(rgb))
        if cap:
            # strip STATE_ and lower
            clean_cap_display = cap.replace("STATE_", "").lower()
            self.mc_capital.set(clean_cap_display)

        # History
        hist = self.logic.load_country_history_details(tag)

        # Populate laws if found
        for l in hist["laws"]:
            if "monarchy" in l or "republic" in l or "theocracy" in l: self.mc_law_gov.set("law_" + l if not l.startswith("law_") else l)
            if "interventionism" in l or "laissez" in l or "command" in l or "traditionalism" in l or "agrarianism" in l: self.mc_law_eco.set("law_" + l if not l.startswith("law_") else l)
            if "free_trade" in l or "protectionism" in l or "isolationism" in l or "mercantilism" in l: self.mc_law_trade.set("law_" + l if not l.startswith("law_") else l)
            if "autocracy" in l or "voting" in l or "anarchy" in l or "oligarchy" in l or "party" in l: self.mc_law_power.set("law_" + l if not l.startswith("law_") else l)

        self.mc_r_first.set(hist["ruler"]["first"])
        self.mc_r_last.set(hist["ruler"]["last"])
        self.mc_r_ig.set(hist["ruler"]["ig"])
        self.mc_r_ideo.set(hist["ruler"]["ideology"])

        # Population
        pop_settings = self.logic.get_pop_history_settings(tag)
        self.mc_pop_wealth.set(pop_settings["wealth"])
        self.mc_pop_lit.set(pop_settings["literacy"])

        # Populate conversion dropdowns
        c_opts, _, _, _, _, _ = self.logic.scan_culture_definitions()
        all_culs = sorted(list(c_opts.keys()))
        self.cb_conv_cul['values'] = all_culs
        self.cb_mc_cul_add['values'] = all_culs
        self.cb_conv_rel['values'] = all_rels

        # Load total pop
        tot, _ = self.logic.get_country_total_pop(tag)
        self.mc_total_pop.set(str(tot))

        self.log_message(f"Loaded data for {tag}", 'success')

    def copy_pop_settings(self):
        src_tag = self.logic.format_tag_clean(self.mc_pop_copy_tag.get())
        if not src_tag: return

        settings = self.logic.get_pop_history_settings(src_tag)
        if settings["wealth"]: self.mc_pop_wealth.set(settings["wealth"])
        if settings["literacy"]: self.mc_pop_lit.set(settings["literacy"])

        self.log_message(f"Copied pop settings from {src_tag}", 'info')

    @mod_operation
    def save_country_mod_changes(self):
        tag = self.logic.format_tag_clean(self.mc_tag.get())
        if not tag: return

        # Save Loc
        self.logic.save_country_localization(tag, self.mc_name.get(), self.mc_adj.get())

        # Save Def
        _, _, path = self.logic.load_country_definition_data(tag) # Get path
        clean_cap = self.logic.format_state_clean(self.mc_capital.get())

        culs = list(self.lb_mc_cultures.get(0, tk.END))
        rel = self.mc_religion.get().strip()

        self.logic.save_country_definition(tag, self.mc_rgb, clean_cap, path, cultures=culs, religion=rel)

        # Save History
        laws = []
        if self.mc_law_gov.get(): laws.append(self.mc_law_gov.get())
        if self.mc_law_eco.get(): laws.append(self.mc_law_eco.get())
        if self.mc_law_trade.get(): laws.append(self.mc_law_trade.get())
        if self.mc_law_power.get(): laws.append(self.mc_law_power.get())

        ruler = {
            "first": self.mc_r_first.get(),
            "last": self.mc_r_last.get(),
            "ig": self.mc_r_ig.get(),
            "ideology": self.mc_r_ideo.get()
        }

        self.logic.save_country_history(tag, laws, ruler)

        # Save Pop Settings
        self.logic.save_pop_history_settings(tag, self.mc_pop_wealth.get(), self.mc_pop_lit.get())

        messagebox.showinfo("Success", "Country modifications saved.")

    def pick_color_mod(self):
        init_color = self._rgb_to_hex(self.mc_rgb)
        color = colorchooser.askcolor(color=init_color, title="Choose Country Color")
        if color[0]:
            self.mc_rgb = [int(x) for x in color[0]]
            self.mc_color_prev.config(bg=color[1])

    # --- MODE 6: DIPLOMACY MANAGER ---
    def show_diplomacy_ui(self):
        self.clear_content()
        self.mode = "DIPLOMACY"
        f = ttk.LabelFrame(self.content_frame, text="Diplomacy Manager", padding=15)
        f.pack(fill=tk.BOTH, expand=True)

        # Tag & Load
        top_frame = ttk.Frame(f)
        top_frame.pack(fill=tk.X, pady=5)
        ttk.Label(top_frame, text="Country Tag:").pack(side=tk.LEFT)
        self.dip_tag = tk.StringVar()
        ttk.Entry(top_frame, textvariable=self.dip_tag, width=10).pack(side=tk.LEFT, padx=5)
        ttk.Button(top_frame, text="Load Data", command=self.load_diplomacy_ui_data).pack(side=tk.LEFT, padx=5)
        self.map_field_button(top_frame, self.dip_tag, self.load_diplomacy_ui_data).pack(side=tk.LEFT,padx=5)

        # Lists
        list_frame = ttk.Frame(f)
        list_frame.pack(fill=tk.BOTH, expand=True, pady=5)

        # Subjects
        sf = ttk.LabelFrame(list_frame, text="Subject Relationships", padding=5)
        sf.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=(0,5))
        self.lb_subjects = tk.Listbox(sf, height=8, bg="#473a2b", fg="#f3e7ce")
        self.lb_subjects.pack(fill=tk.BOTH, expand=True)
        ttk.Button(sf, text="Remove Selected", command=lambda: self.remove_dip_item("subject")).pack(fill=tk.X)

        # Hostiles
        hf = ttk.LabelFrame(list_frame, text="Hostile / Truces", padding=5)
        hf.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=(5,0))
        self.lb_hostiles = tk.Listbox(hf, height=8, bg="#473a2b", fg="#f3e7ce")
        self.lb_hostiles.pack(fill=tk.BOTH, expand=True)
        ttk.Button(hf, text="Remove Selected", command=lambda: self.remove_dip_item("hostile")).pack(fill=tk.X)

        # Add New
        add_frame = ttk.LabelFrame(f, text="Add New Relationship", padding=5)
        add_frame.pack(fill=tk.X, pady=5)

        ttk.Label(add_frame, text="Target Tag:").grid(row=0, column=0, sticky=tk.W)
        self.dip_target = tk.StringVar()
        ttk.Entry(add_frame, textvariable=self.dip_target, width=10).grid(row=0, column=1, sticky=tk.W, padx=5)

        self.dip_cat = tk.StringVar(value="subject")
        ttk.Radiobutton(add_frame, text="Subject", variable=self.dip_cat, value="subject", command=self.update_dip_type_options).grid(row=0, column=2)
        ttk.Radiobutton(add_frame, text="Hostile/Truce", variable=self.dip_cat, value="hostile", command=self.update_dip_type_options).grid(row=0, column=3)

        self.dip_type_opts = self.logic.SUBJECT_TYPES
        self.dip_type = tk.StringVar()
        self.cb_dip_type = ttk.Combobox(add_frame, textvariable=self.dip_type, values=self.dip_type_opts, state="readonly")
        self.cb_dip_type.grid(row=0, column=4, padx=5)
        self.cb_dip_type.current(0)

        ttk.Button(add_frame, text="Create", command=self.create_diplomacy_pact).grid(row=0, column=5, padx=5)
        self.map_field_button(add_frame, self.dip_target).grid(row=1,column=1,sticky=tk.W)

        # Relations Value
        rel_frame = ttk.LabelFrame(f, text="Set Relations", padding=5)
        rel_frame.pack(fill=tk.X, pady=5)

        ttk.Label(rel_frame, text="Target Tag:").grid(row=0, column=0)
        self.dip_rel_target = tk.StringVar()
        ttk.Entry(rel_frame, textvariable=self.dip_rel_target, width=10).grid(row=0, column=1, padx=5)

        ttk.Label(rel_frame, text="Value (-100 to 100):").grid(row=0, column=2)
        self.dip_rel_val = tk.IntVar(value=0)
        ttk.Entry(rel_frame, textvariable=self.dip_rel_val, width=5).grid(row=0, column=3, padx=5)

        ttk.Button(rel_frame, text="Set Relation", command=self.set_relation_val).grid(row=0, column=4, padx=5)
        self.map_field_button(rel_frame, self.dip_rel_target).grid(row=1,column=1,sticky=tk.W)

        self.run_btn.config(text="Refresh Data", command=self.load_diplomacy_ui_data, state='normal')

    def update_dip_type_options(self):
        cat = self.dip_cat.get()
        if cat == "subject":
            self.dip_type_opts = self.logic.SUBJECT_TYPES
        else:
            self.dip_type_opts = ["rivalry", "embargo", "truce"]
        self.cb_dip_type['values'] = self.dip_type_opts
        self.cb_dip_type.current(0)

    def load_diplomacy_ui_data(self):
        tag = self.logic.format_tag_clean(self.dip_tag.get())
        if not tag: return messagebox.showerror("Error", "Enter a tag.")

        data = self.logic.load_diplomacy_data(tag)

        self.lb_subjects.delete(0, tk.END)
        for s in data["subjects"]:
            self.lb_subjects.insert(tk.END, f"{s['target']} ({s['type']})")

        self.lb_hostiles.delete(0, tk.END)
        for r in data["rivals"]: self.lb_hostiles.insert(tk.END, f"{r} (Rival)")
        for e in data["embargos"]: self.lb_hostiles.insert(tk.END, f"{e} (Embargo)")
        for t in data["truces"]: self.lb_hostiles.insert(tk.END, f"{t['target']} (Truce: {t['months']}m)")

        self.log_message(f"Loaded diplomacy for {tag}", 'success')

    def create_diplomacy_pact(self):
        tag = self.logic.format_tag_clean(self.dip_tag.get())
        target = self.logic.format_tag_clean(self.dip_target.get())
        dtype = self.dip_type.get()
        cat = self.dip_cat.get() # subject or hostile

        if not tag or not target: return messagebox.showerror("Error", "Tags required.")

        real_cat = "subject"
        if cat == "hostile":
            if dtype == "rivalry": real_cat = "rival"
            elif dtype == "embargo": real_cat = "embargo"
            elif dtype == "truce": real_cat = "truce"

        self.logic.add_diplomatic_pact(tag, target, dtype, real_cat)
        self.load_diplomacy_ui_data()

    def remove_dip_item(self, list_type):
        tag = self.logic.format_tag_clean(self.dip_tag.get())
        if not tag: return

        sel = None
        if list_type == "subject":
            sel = self.lb_subjects.curselection()
        else:
            sel = self.lb_hostiles.curselection()

        if not sel: return

        text = self.lb_subjects.get(sel[0]) if list_type == "subject" else self.lb_hostiles.get(sel[0])
        # Parse text: "TARGET (TYPE)" or "TARGET (Truce: 12m)"
        target = text.split()[0]
        dtype = ""
        if "Rival" in text: dtype = "rivalry"
        elif "Embargo" in text: dtype = "embargo"
        elif "Truce" in text: dtype = "truce"
        else:
            # Subject type
            dtype = text.split('(')[1].replace(')', '')

        self.logic.remove_diplomatic_pact(tag, target, dtype)
        self.load_diplomacy_ui_data()

    def set_relation_val(self):
        tag = self.logic.format_tag_clean(self.dip_tag.get())
        target = self.logic.format_tag_clean(self.dip_rel_target.get())
        try:
            val = self.dip_rel_val.get()
        except: return

        if not tag or not target: return

        self.logic.set_relations(tag, target, val)
        self.log_message(f"Set relations {tag}<->{target} to {val}")

    # --- MODE 7: POWERBLOCK MANAGER ---
    def show_power_bloc_ui(self):
        self.clear_content()
        self.mode = "POWERBLOC"
        f = ttk.LabelFrame(self.content_frame, text="Powerbloc Manager", padding=15)
        f.pack(fill=tk.BOTH, expand=True)

        # 1. Selector (Tag or Existing Bloc)
        sel_frame = ttk.Frame(f)
        sel_frame.pack(fill=tk.X, pady=5)

        ttk.Label(sel_frame, text="Target Tag:").pack(side=tk.LEFT)
        self.pb_tag = tk.StringVar()
        e_tag = ttk.Entry(sel_frame, textvariable=self.pb_tag, width=10)
        e_tag.pack(side=tk.LEFT, padx=5)
        e_tag.bind("<FocusOut>", lambda e: self.load_pb_data_by_tag())
        self.map_field_button(sel_frame, self.pb_tag, self.load_pb_data_by_tag).pack(side=tk.LEFT,padx=5)

        ttk.Label(sel_frame, text="OR Select Bloc:").pack(side=tk.LEFT, padx=(15, 5))
        self.pb_select_var = tk.StringVar()
        self.cb_pb_select = ttk.Combobox(sel_frame, textvariable=self.pb_select_var, state="readonly", width=30)
        self.cb_pb_select.pack(side=tk.LEFT, padx=5)
        self.cb_pb_select.bind("<<ComboboxSelected>>", self.on_pb_select)

        ttk.Button(sel_frame, text="Refresh List", command=self.refresh_pb_list).pack(side=tk.LEFT, padx=5)

        # 2. Details Form
        det_frame = ttk.LabelFrame(f, text="Bloc Details", padding=10)
        det_frame.pack(fill=tk.X, pady=5)

        # Key
        ttk.Label(det_frame, text="Key:").grid(row=0, column=0, sticky=tk.W)
        self.pb_key = tk.StringVar()
        ttk.Entry(det_frame, textvariable=self.pb_key, width=25).grid(row=0, column=1, sticky=tk.W, padx=5, pady=2)

        # Identity
        ttk.Label(det_frame, text="Identity:").grid(row=0, column=2, sticky=tk.W, padx=(10,0))
        self.pb_identity = tk.StringVar()
        self.cb_pb_identity = ttk.Combobox(det_frame, textvariable=self.pb_identity, state="readonly", width=30)
        self.cb_pb_identity.grid(row=0, column=3, sticky=tk.W, padx=5, pady=2)
        self.cb_pb_identity.bind("<<ComboboxSelected>>", self.refresh_principle_options)

        # Name Loc
        ttk.Label(det_frame, text="Name:").grid(row=1, column=0, sticky=tk.W)
        self.pb_loc_name = tk.StringVar()
        ttk.Entry(det_frame, textvariable=self.pb_loc_name, width=25).grid(row=1, column=1, sticky=tk.W, padx=5, pady=2)

        # Adjective Loc
        ttk.Label(det_frame, text="Adjective:").grid(row=1, column=2, sticky=tk.W, padx=(10,0))
        self.pb_loc_adj = tk.StringVar()
        ttk.Entry(det_frame, textvariable=self.pb_loc_adj, width=30).grid(row=1, column=3, sticky=tk.W, padx=5, pady=2)

        # Color
        ttk.Label(det_frame, text="Color:").grid(row=2, column=0, sticky=tk.W)
        self.pb_color = tk.StringVar()
        self.pb_color_preview = tk.Label(det_frame, text="     ", bg="#FFFFFF", relief="solid", borderwidth=1, width=10)
        self.pb_color_preview.grid(row=2, column=1, sticky=tk.W, padx=5, pady=2)
        ttk.Button(det_frame, text="Pick Color", command=self.pick_pb_color).grid(row=2, column=2, padx=2)

        # Founding Date
        ttk.Label(det_frame, text="Founding Date:").grid(row=3, column=0, sticky=tk.W)
        self.pb_date = tk.StringVar(value="1836.1.1")
        ttk.Entry(det_frame, textvariable=self.pb_date, width=15).grid(row=3, column=1, sticky=tk.W, padx=5, pady=2)

        # Tag Leader (Info)
        ttk.Label(det_frame, text="Leader Tag:").grid(row=3, column=2, sticky=tk.W, padx=(10,0))
        self.pb_leader_var = tk.StringVar()
        ttk.Entry(det_frame, textvariable=self.pb_leader_var, width=10).grid(row=3, column=3, sticky=tk.W, padx=5)

        # 3. Main Body (Principles + Members)
        main_body = ttk.Frame(f)
        main_body.pack(fill=tk.BOTH, expand=True, pady=5)

        # Left: Principles
        princ_frame = ttk.LabelFrame(main_body, text="Principles", padding=10)
        princ_frame.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=(0, 5))

        self.pb_tree = ttk.Treeview(princ_frame, columns=("key", "level"), show="headings", height=6)
        self.pb_tree.heading("key", text="Principle Key"); self.pb_tree.heading("level", text="Level")
        self.pb_tree.column("key", width=200); self.pb_tree.column("level", width=50, anchor="center")
        self.pb_tree.pack(fill=tk.BOTH, expand=True, pady=(0, 5))

        p_ctrl = ttk.Frame(princ_frame)
        p_ctrl.pack(fill=tk.X)
        ttk.Label(p_ctrl, text="Add:").pack(side=tk.LEFT)
        self.pb_princ_add_var = tk.StringVar()
        self.cb_pb_princ_add = ttk.Combobox(p_ctrl, textvariable=self.pb_princ_add_var, state="readonly", width=25)
        self.cb_pb_princ_add.pack(side=tk.LEFT, padx=5)
        self.pb_princ_level = tk.StringVar(value="1")
        ttk.Combobox(p_ctrl, textvariable=self.pb_princ_level, values=["1", "2", "3"], state="readonly", width=3).pack(side=tk.LEFT)
        ttk.Button(p_ctrl, text="+", width=3, command=self.add_pb_principle).pack(side=tk.LEFT, padx=5)
        ttk.Button(p_ctrl, text="Remove", width=7, command=self.remove_pb_principle).pack(side=tk.RIGHT)

        # Right: Members
        memb_frame = ttk.LabelFrame(main_body, text="Members (Subjects are automatically made members)", padding=10)
        memb_frame.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=(5, 0))

        self.lb_members = tk.Listbox(memb_frame, height=6, bg="white", fg="black")
        self.lb_members.pack(fill=tk.BOTH, expand=True, pady=(0, 5))

        m_ctrl = ttk.Frame(memb_frame)
        m_ctrl.pack(fill=tk.X)
        ttk.Label(m_ctrl, text="Add Tag:").pack(side=tk.LEFT)
        self.pb_member_add_var = tk.StringVar()
        ttk.Entry(m_ctrl, textvariable=self.pb_member_add_var, width=8).pack(side=tk.LEFT, padx=5)
        ttk.Button(m_ctrl, text="+", width=3, command=self.add_pb_member).pack(side=tk.LEFT)
        self.map_field_button(m_ctrl, self.pb_member_add_var).pack(side=tk.LEFT,padx=5)
        ttk.Button(m_ctrl, text="Remove", width=7, command=self.remove_pb_member).pack(side=tk.RIGHT)

        # 4. Actions
        action_bar = ttk.Frame(f)
        action_bar.pack(fill=tk.X, pady=10)

        ttk.Button(action_bar, text="Create / Modify", command=self.save_power_bloc).pack(side=tk.RIGHT, padx=5)
        ttk.Button(action_bar, text="Remove Power Bloc", command=self.delete_power_bloc).pack(side=tk.RIGHT, padx=5)

        # Init
        self.refresh_pb_list()
        self.load_pb_definitions()

    def refresh_pb_list(self):
        blocs = self.logic.get_all_power_blocs()
        self.pb_list_data = blocs
        values = [f"{b['name']} ({b['tag']})" for b in blocs]
        self.cb_pb_select['values'] = values

    def load_pb_definitions(self):
        # Format identities for display
        self.identity_key_map = {}
        self.identity_display_map = {}
        display_values = []

        for key in self.logic.PB_IDENTITIES:
            # identity_trade_league -> Trade League
            clean = key.replace("identity_", "").replace("_", " ").title()
            self.identity_key_map[clean] = key
            self.identity_display_map[key] = clean
            display_values.append(clean)

        self.cb_pb_identity['values'] = display_values

    def refresh_principle_options(self, event=None):
        current_display = self.pb_identity.get()
        # Map back to raw key
        current_id = getattr(self, 'identity_key_map', {}).get(current_display, current_display)

        options = list(self.logic.PB_GLOBAL_PRINCIPLES)

        if current_id in self.logic.PB_EXCLUSIVE_PRINCIPLES:
            options.extend(self.logic.PB_EXCLUSIVE_PRINCIPLES[current_id])

        options = sorted(options)

        # Create map and display list
        self.principle_key_map = {}
        display_values = []
        for key in options:
            clean = key.replace("principle_", "").replace("_", " ").title()
            self.principle_key_map[clean] = key
            display_values.append(clean)

        self.cb_pb_princ_add['values'] = display_values

        # Validate and remove incompatible principles
        exclusive_map = self.logic.PB_EXCLUSIVE_PRINCIPLES
        items_to_remove = []

        for item in self.pb_tree.get_children():
            vals = self.pb_tree.item(item)['values']
            if not vals: continue
            key = vals[0]

            # Check Redundancy
            if current_id == "identity_trade_league" and key == "principle_market_unification":
                items_to_remove.append(item)
                continue

            # Check Exclusive
            is_exclusive = False
            allowed = False
            for ident, p_list in exclusive_map.items():
                if key in p_list:
                    is_exclusive = True
                    if ident == current_id:
                        allowed = True

            if is_exclusive and not allowed:
                items_to_remove.append(item)

        for item in items_to_remove:
            self.pb_tree.delete(item)

    def on_pb_select(self, event):
        idx = self.cb_pb_select.current()
        if idx >= 0:
            tag = self.pb_list_data[idx]['tag']
            self.pb_tag.set(tag)
            self.load_pb_data_by_tag()

    def load_pb_data_by_tag(self):
        tag = self.logic.format_tag_clean(self.pb_tag.get())
        if not tag: return

        self.pb_leader_var.set(tag)

        data = self.logic.get_power_bloc_data(tag)
        # Clear Tree
        for item in self.pb_tree.get_children():
            self.pb_tree.delete(item)

        if data:
            key = data['name']
            self.pb_key.set(key)

            # Load locs
            loc_name, loc_adj = self.logic.load_power_bloc_localization(key)
            self.pb_loc_name.set(loc_name)
            self.pb_loc_adj.set(loc_adj)

            # Map raw key to display name
            raw_ident = data['identity']
            self.pb_identity.set(getattr(self, 'identity_display_map', {}).get(raw_ident, raw_ident))
            self.pb_color.set(data['map_color'])

            # Parse color for preview
            try:
                vals = re.findall(r"[\d\.]+", data['map_color'])
                if len(vals) >= 3:
                    # Vic3 often uses 0-1 float or 0-255 int or hsv
                    # Simple heuristic: if any > 1, assume int. Else float.
                    # Wait, hsv uses float usually. { 0.99 0.7 0.9 }
                    v1, v2, v3 = float(vals[0]), float(vals[1]), float(vals[2])
                    if "hsv" in data['map_color'].lower():
                        # hsv to rgb conversion is complex, for now let's just skip or default white if hsv
                        # Tkinter doesn't do HSV easily.
                        # If user used Pick Color, we saved as { r g b } ints.
                        # If loading vanilla file, it might be hsv.
                        # Just show white if complex.
                        self.pb_color_preview.config(bg="#FFFFFF")
                    else:
                        if v1 <= 1.0 and v2 <= 1.0 and v3 <= 1.0:
                            v1, v2, v3 = int(v1*255), int(v2*255), int(v3*255)
                        else:
                            v1, v2, v3 = int(v1), int(v2), int(v3)
                        hex_col = f'#{v1:02x}{v2:02x}{v3:02x}'
                        self.pb_color_preview.config(bg=hex_col)
            except:
                self.pb_color_preview.config(bg="#FFFFFF")

            self.pb_date.set(data['date'])
            self.pb_current_members = data.get("members", [])

            for p in data['principles']:
                self.pb_tree.insert("", tk.END, values=(p["key"], p["level"]))

            self.refresh_principle_options()
            self.refresh_members_list()
            self.log_message(f"Loaded Power Bloc for {tag}", 'success')
        else:
            self.pb_key.set("")
            self.pb_loc_name.set("")
            self.pb_loc_adj.set("")
            self.pb_identity.set("")
            self.pb_color.set("")
            self.pb_color_preview.config(bg="#FFFFFF")
            self.pb_date.set("1836.1.1")
            self.pb_current_members = []
            self.refresh_members_list()
            self.refresh_principle_options()
            self.log_message(f"No existing Power Bloc for {tag}. Ready to create.", 'info')

    def refresh_members_list(self):
        self.lb_members.delete(0, tk.END)
        for m in self.pb_current_members:
            self.lb_members.insert(tk.END, m)

    def add_pb_member(self):
        val = self.logic.format_tag_clean(self.pb_member_add_var.get())
        if val:
            full_val = f"c:{val}" if not val.startswith("c:") else val
            if full_val not in self.pb_current_members:
                self.pb_current_members.append(full_val)
                self.refresh_members_list()
                self.pb_member_add_var.set("")

    def remove_pb_member(self):
        sel = self.lb_members.curselection()
        if sel:
            idx = sel[0]
            val = self.lb_members.get(idx)
            if val in self.pb_current_members:
                self.pb_current_members.remove(val)
                self.refresh_members_list()

    def pick_pb_color(self):
        color = colorchooser.askcolor(title="Choose Map Color")
        if color[0]:
            r, g, b = int(color[0][0]), int(color[0][1]), int(color[0][2])
            self.pb_color.set(f"{{ {r} {g} {b} }}")
            self.pb_color_preview.config(bg=color[1])

    def add_pb_principle(self):
        display = self.pb_princ_add_var.get()
        # Look up key from display map, or use as is if not found (fallback)
        key = getattr(self, 'principle_key_map', {}).get(display, display)

        try:
            level = int(self.pb_princ_level.get())
        except: level = 1

        if not key: return

        current_display = self.pb_identity.get()
        current_id = getattr(self, 'identity_key_map', {}).get(current_display, current_display)

        # VALIDATION RULES

        # 1. Identity Lock
        exclusive_map = self.logic.PB_EXCLUSIVE_PRINCIPLES
        is_exclusive = False
        allowed_for_current = False

        for ident, p_list in exclusive_map.items():
            if key in p_list:
                is_exclusive = True
                if ident == current_id:
                    allowed_for_current = True

        if is_exclusive and not allowed_for_current:
            return messagebox.showerror("Validation Error", f"Principle '{key}' is not allowed for identity '{current_id}'.")

        # 2. Uniqueness
        for item in self.pb_tree.get_children():
            vals = self.pb_tree.item(item)['values']
            if vals[0] == key:
                return messagebox.showerror("Validation Error", f"Principle '{key}' is already added.")

        # 3. Trade League Redundancy
        if current_id == "identity_trade_league" and key == "principle_market_unification":
            return messagebox.showerror("Validation Error", "Trade Leagues automatically function as a Customs Union; this principle is redundant.")

        # Add to Tree
        self.pb_tree.insert("", tk.END, values=(key, level))

    def remove_pb_principle(self):
        sel = self.pb_tree.selection()
        if sel:
            self.pb_tree.delete(sel[0])

    def save_power_bloc(self):
        # Original tag loaded/selected
        orig_tag = self.logic.format_tag_clean(self.pb_tag.get())

        # New tag from leader field
        new_tag = self.logic.format_tag_clean(self.pb_leader_var.get())

        if not new_tag: return messagebox.showerror("Error", "Leader Tag required.")

        key = self.pb_key.get().strip()
        loc_name = self.pb_loc_name.get().strip()
        loc_adj = self.pb_loc_adj.get().strip()
        display_identity = self.pb_identity.get().strip()
        identity = getattr(self, 'identity_key_map', {}).get(display_identity, display_identity)
        color = self.pb_color.get().strip()
        date = self.pb_date.get().strip()

        principles = []
        for item in self.pb_tree.get_children():
            vals = self.pb_tree.item(item)['values']
            principles.append({"key": vals[0], "level": int(vals[1])})

        if not key or not identity: return messagebox.showerror("Error", "Key and Identity required.")

        # Check Primary Principle Requirement
        req_principles = self.logic.PB_PRIMARY_PRINCIPLE_OPTIONS.get(identity, [])
        has_req = False
        for p in principles:
            if p["key"] in req_principles:
                has_req = True
                break

        if req_principles and not has_req:
             # Create nice string for warning
             req_names = [p.replace("principle_", "").replace("_", " ").title() for p in req_principles]
             msg = f"The identity '{identity}' requires at least one of these principles:\n" + "\n".join(req_names)
             messagebox.showwarning("Validation Error", msg)
             return

        if not hasattr(self, 'pb_current_members'):
             self.pb_current_members = []

        data = {
            "key": key,
            "loc_name": loc_name,
            "loc_adj": loc_adj,
            "identity": identity,
            "map_color": color,
            "date": date,
            "principles": principles,
            "members": self.pb_current_members
        }

        # If tag changed, remove old and save new
        if orig_tag and orig_tag != new_tag:
            if messagebox.askyesno("Confirm", f"Move Power Bloc from {orig_tag} to {new_tag}?"):
                self.logic.remove_power_bloc(orig_tag)
                self.pb_tag.set(new_tag) # Update current tag

        self.logic.save_power_bloc_data(new_tag, data)
        self.refresh_pb_list()
        messagebox.showinfo("Success", f"Power Bloc saved for {new_tag}.")

    def delete_power_bloc(self):
        tag = self.logic.format_tag_clean(self.pb_tag.get())
        if not tag: return

        if messagebox.askyesno("Confirm", f"Remove Power Bloc for {tag}?"):
            self.logic.remove_power_bloc(tag)
            self.refresh_pb_list()
            self.load_pb_data_by_tag()

    def refresh_all_dropdowns(self):
        """Re-scans data and updates dropdowns across the application."""
        # 1. Religions & Cultures
        c_opts, _, _, _, _, _ = self.logic.scan_culture_definitions()
        all_culs = sorted(list(c_opts.keys()))

        _, r_opts = self.logic.scan_all_religions_and_heritages()
        r_all, _ = self.logic.scan_all_religions_and_heritages()
        _, def_rels, _, _ = self.logic.scan_definitions_for_options()
        all_rels = sorted(list(set(r_all + def_rels)))

        # State Manager Dropdowns
        if hasattr(self, 'cb_homeland_add'): self.cb_homeland_add['values'] = all_culs
        if hasattr(self, 'cb_pop_cul'): self.cb_pop_cul['values'] = all_culs
        if hasattr(self, 'cb_pop_rel'): self.cb_pop_rel['values'] = all_rels

        # Culture/Religion Creator Dropdowns
        if hasattr(self, 'rc_c_rel'):
             # Update scanning for just keys if needed, but r_keys var was local.
             # scan_all_religions returns keys, heritages
             keys, _ = self.logic.scan_all_religions_and_heritages()
             self.rc_c_rel['values'] = keys

        # Create Country Dropdowns if needed
        if hasattr(self, 'cb_cultures'):
             # Create country uses scan_definitions_for_options mostly, but could benefit from new ones
             # Re-run scan_definitions_for_options
             all_c, _, _, _ = self.logic.scan_definitions_for_options()
             # We should probably merge scanned cultures from definitions AND files if creating new ones
             # For now, let's just stick to the requested scope
             pass

        if hasattr(self, 'cb_mc_cul_add'): self.cb_mc_cul_add['values'] = all_culs

        self.log_message("Dropdowns refreshed with latest data.", 'info')

    # --- SHARED FUNCTIONS ---
    def browse_folder(self):
        if self.is_processing: return
        folder=filedialog.askdirectory(title='Choose mod root folder')
        if folder:
            self.logic.set_mod_path(folder); self.path_var.set(self.logic.mod_path); self.save_config()
            self.navigate('Overview',self.show_mod_manager_ui)

    def browse_vanilla_folder(self):
        if self.is_processing: return
        folder=filedialog.askdirectory(title='Choose Victoria 3 installation or game folder')
        if folder:
            self.logic.set_vanilla_path(folder); self.vanilla_path_var.set(self.logic.vanilla_path); self.save_config()
            self.navigate('Overview',self.show_mod_manager_ui)

    def log_message(self, message, level='info'):
        self.log_queue.put((message, level))

    def process_log_queue(self):
        while not self.ui_queue.empty(): self.ui_queue.get_nowait()()
        for _ in range(200):
            try: msg,level=self.log_queue.get_nowait()
            except queue.Empty: break
            self.log_area.configure(state='normal'); self.log_area.insert('end',str(msg).strip()+'\n',level)
            self.log_area.see('end'); self.log_area.configure(state='disabled')
        self.after(100,self.process_log_queue)

    def start_transfer(self):
        if self.is_processing: return
        mod_path = self.path_var.get()
        if not mod_path: return messagebox.showerror("Error", "Select mod path first.")

        mode = self.tr_mode.get()
        new = self.logic.format_tag_clean(self.tr_new_tag.get())

        if not new: return messagebox.showerror("Error", "New Tag required.")

        old_input = self.tr_old_tag.get()
        raw_st = self.tr_states.get("1.0", tk.END)

        old_tags = []
        if mode == "annex":
            parts = old_input.split()
            old_tags = [self.logic.format_tag_clean(t) for t in parts if t.strip()]
            if not old_tags: return messagebox.showerror("Error", "Old Owner Tag(s) required for Annexation.")
        elif mode == "split":
            tag = self.logic.format_tag_clean(old_input)
            if not tag: return messagebox.showerror("Error", "Old Owner Tag required for Targeted Transfer.")
            old_tags = [tag]

        self.is_processing = True
        self.run_btn.config(state='disabled')
        self.log_area.config(state='normal'); self.log_area.delete('1.0', tk.END); self.log_area.config(state='disabled')
        threading.Thread(target=self.run_transfer_logic, args=(old_tags, new, mode, raw_st), daemon=True).start()

    def start_create(self):
        if self.is_processing: return
        mod_path = self.path_var.get()
        if not mod_path: return messagebox.showerror("Error", "Select mod path first.")
        tag = self.logic.format_tag_clean(self.cr_tag.get())
        name = self.cr_name.get().strip()
        adj = self.cr_adj.get().strip()
        old_owner = self.logic.format_tag_clean(self.cr_old_owner.get())
        capital = self.logic.format_state_clean(self.cr_capital.get())
        others_raw = self.cr_others.get("1.0", tk.END)
        rgb = self.cr_rgb
        is_annex = self.cr_annex.get() and not self.country_state_owners

        tier = self.cr_tier.get()
        country_type = self.cr_type.get()
        cultures = self.selected_cultures
        religion = self.cr_religion.get()

        pop_wealth = self.cr_pop_wealth.get()
        pop_lit = self.cr_pop_lit.get()

        if not tag or not name or not old_owner: return messagebox.showerror("Error", "Tag, Name, and Old Owner are required.")
        if not is_annex and not capital: return messagebox.showerror("Error", "Capital State ID required unless Full Annexation.")
        if len(tag) != 3: return messagebox.showerror("Error", "Tag must be exactly 3 characters.")

        # Pre-fetch old owner data to minimize redundant calls
        data = self.logic.get_country_data(old_owner)

        # If cultures were not manually selected, default to old owner's data
        if not cultures:
            if data["cultures"]:
                cultures = data["cultures"].split()

        # If religion is not manually selected, check old owner, then check culture
        if not religion:
            if data["religion"]:
                religion = data["religion"]
            else:
                # Attempt to find religion from the primary culture
                found_rel = None
                if cultures:
                    prim_culture = cultures[0]
                    self.log_message(f"[INFO] Religion missing. searching in culture '{prim_culture}'...", 'info')
                    found_rel = self.logic.get_religion_by_culture(prim_culture)
                
                if found_rel:
                    religion = found_rel
                    self.log_message(f"[INFO] Found religion '{religion}' from culture '{prim_culture}'.", 'success')
                else:
                    self.log_message(f"[WARN] Religion not found for {old_owner} or culture. Defaulting to 'catholic'.", 'warn')
                    religion = "catholic"

        if not cultures: return messagebox.showerror("Error", "At least one culture required.")
        # Religion check removed, effectively allowing the process to continue even if religion wasn't found (defaulted to catholic)

        self.is_processing = True
        self.run_btn.config(state='disabled')
        self.log_area.config(state='normal'); self.log_area.delete('1.0', tk.END); self.log_area.config(state='disabled')
        threading.Thread(target=self.run_create_logic, args=(tag, name, adj, old_owner, capital, others_raw, rgb, is_annex, cultures, religion, tier, country_type, pop_wealth, pop_lit, dict(self.country_state_owners)), daemon=True).start()

    # --- LOGIC THREADS ---
    def run_transfer_logic(self, old_tags_input, new_tag, mode, raw_states):
        try:
            if mode == "annex":
                for old_tag in old_tags_input:
                    self.log_message(f"--- Processing Annexation: {old_tag} -> {new_tag} ---", 'info')
                    self.log_message(f"[INFO] Detecting states owned by {old_tag}...", 'info')
                    states_clean = self.logic.get_all_owned_states(old_tag)
                    if not states_clean:
                        self.log_message(f"[WARN] No states found for {old_tag}.", 'warn')
                        continue
                    self.logic.perform_transfer_sequence(states_clean, new_tag, known_old_owners=[old_tag])
                    self.logic.perform_annexation_cleanup(old_tag, new_tag, states_clean)

            elif mode == "split":
                old_tag = old_tags_input[0]
                self.log_message(f"--- Processing Targeted Transfer: {old_tag} -> {new_tag} ---", 'info')
                states_clean = [self.logic.format_state_clean(s) for s in raw_states.split() if s.strip()]
                if not states_clean: return self.log_message("[ERROR] No states provided.", 'error')

                # Check for full annexation
                current_owned = self.logic.get_all_owned_states(old_tag)
                set_current = set(s.upper() for s in current_owned)
                set_transfer = set(s.upper() for s in states_clean)

                self.logic.perform_transfer_sequence(states_clean, new_tag, known_old_owners=[old_tag])

                if set_current and set_current.issubset(set_transfer):
                     self.log_message(f"[INFO] Full annexation detected for {old_tag} via Split Transfer.", 'info')
                     self.logic.perform_annexation_cleanup(old_tag, new_tag, states_clean)

            else: # auto
                self.log_message(f"--- Processing Auto-Transfer -> {new_tag} ---", 'info')
                states_clean = [self.logic.format_state_clean(s) for s in raw_states.split() if s.strip()]
                if not states_clean: return self.log_message("[ERROR] No states provided.", 'error')

                # Auto-detect annexation for all affected owners
                owners_found = set()
                annex_list = []
                for state in states_clean:
                    owners = self.logic.scan_state_region_owners(state)
                    owners_found.update(owners)
                
                # Cleanup self-reference
                owners_found.discard(new_tag)
                owners_found.discard(new_tag.replace("c:", "").upper())

                for owner in owners_found:
                    current_owned = self.logic.get_all_owned_states(owner)
                    set_current = set(s.upper() for s in current_owned)
                    set_transfer = set(s.upper() for s in states_clean)

                    if set_current and set_current.issubset(set_transfer):
                         annex_list.append(owner)

                self.logic.perform_transfer_sequence(states_clean, new_tag, known_old_owners=None)

                for owner in annex_list:
                     self.log_message(f"[INFO] Full annexation detected for {owner} via Auto Transfer.", 'info')
                     self.logic.perform_annexation_cleanup(owner, new_tag, states_clean)

        except Exception as e:
            self.log_message(f"CRITICAL ERROR: {str(e)}", 'error')
            traceback.print_exc()
        finally:
            self.is_processing = False
            self.after(0, lambda: self.run_btn.config(state='normal'))

    def run_create_logic(self, tag, name, adj, old_owner, capital, others_raw, rgb, is_annex, cultures, religion, tier, country_type, pop_wealth, pop_lit, state_owners=None):
        try:
            self.log_message(f"--- Creating Country: {tag} ({name}) ---", 'info')
            if self.logic.tag_exists(tag):
                self.log_message(f"[ERROR] Tag {tag} already exists in common/country_definitions!", 'error')
                return

            # (Old owner data logic is now partly in UI for prepopulation, but we still need capital logic if annexing)
            data = self.logic.get_country_data(old_owner)
            
            all_states = []
            should_cleanup = False
            if is_annex:
                self.log_message(f"[INFO] Full Annexation selected. Detecting all states for {old_owner}...", 'info')
                found_states = self.logic.get_all_owned_states(old_owner)
                if not found_states:
                    self.log_message(f"[WARN] No states found for {old_owner} to annex.", 'warn')
                    return
                all_states = found_states
                should_cleanup = True
                
                # If capital input is blank, use old owner's capital
                if not capital:
                    if data["capital"]:
                        capital = data["capital"]
                        self.log_message(f"[INFO] Auto-detected capital: {capital}", 'info')
                    elif all_states:
                        capital = all_states[0] # Fallback to first found state
                        self.log_message(f"[WARN] Capital undefined in old owner. Using first state: {capital}", 'warn')
                    else:
                        self.log_message("[ERROR] Cannot determine capital state.", 'error')
                        return
            else:
                others = [self.logic.format_state_clean(s) for s in others_raw.split() if s.strip()]
                all_states = [capital] + others
                
                # Check for implicit full annexation
                current_owned = self.logic.get_all_owned_states(old_owner)
                set_current = set(s.upper() for s in current_owned)
                set_transfer = set(s.upper() for s in all_states)
                
                if set_current and set_current.issubset(set_transfer):
                     self.log_message(f"[INFO] Full annexation detected (implicit).", 'info')
                     should_cleanup = True

            grouped = {}
            for state in dict.fromkeys(all_states):
                owner = old_owner if is_annex or state == capital else (state_owners or {}).get(state, old_owner)
                grouped.setdefault(owner, []).append(state)
            for owner, states in grouped.items():
                missing = set(states) - set(self.logic.get_all_owned_states(owner))
                if missing:
                    raise ValueError(f"{owner} does not own the selected territory: {', '.join(sorted(missing))}")
            self.logic.create_country_files(tag, name, adj, capital, rgb, cultures, religion, tier, country_type, old_owner, pop_wealth, pop_lit)
            
            self.log_message("--- Transferring Land & Units ---", 'info')

            for owner, states in grouped.items():
                self.logic.perform_transfer_sequence(states, tag, known_old_owners=[owner])
                if not self.logic.get_all_owned_states(owner):
                    self.logic.perform_annexation_cleanup(owner, tag, states)
        except Exception as e:
            self.log_message(f"CRITICAL ERROR: {str(e)}", 'error')
            traceback.print_exc()
        finally:
            self.is_processing = False
            self.after(0, lambda: self.run_btn.config(state='normal'))

    def run_army_logic(self, tag, name, state, inf, art, cav):
        try:
            self.log_message(f"--- Creating Army Template for {tag} ---", 'info')
            self.logic.create_army_file(tag, name, state, inf, art, cav)
        except Exception as e:
            self.log_message(f"CRITICAL ERROR: {str(e)}", 'error')
            traceback.print_exc()
        finally:
            self.is_processing = False
            self.after(0, lambda: self.run_btn.config(state='normal'))

    def run_navy_logic(self, tag, name, state, man, frig, iron):
        try:
            self.log_message(f"--- Creating Navy Template for {tag} ---", 'info')
            self.logic.create_navy_file(tag, name, state, man, frig, iron)
        except Exception as e:
            self.log_message(f"CRITICAL ERROR: {str(e)}", 'error')
            traceback.print_exc()
        finally:
            self.is_processing = False
            self.after(0, lambda: self.run_btn.config(state='normal'))

    # --- MODE 8: RELIGION & CULTURE ---
    def show_rel_cul_ui(self):
        self.clear_content()
        self.mode = "REL_CUL"
        f = ttk.LabelFrame(self.content_frame, text="Religion & Culture Creator", padding=15)
        f.pack(fill=tk.BOTH, expand=True)

        tabs = ttk.Notebook(f)
        tabs.pack(fill=tk.BOTH, expand=True, pady=5)

        tab_cult = ttk.Frame(tabs)
        tab_rel = ttk.Frame(tabs)
        tabs.add(tab_cult, text="Create Culture")
        tabs.add(tab_rel, text="Create Religion")

        # --- Create Culture UI ---
        # Scan data
        c_data, c_heritages, c_langs, c_trads, c_graphics, c_eths = self.logic.scan_culture_definitions()
        # Scan religions for dropdown
        r_keys, r_heritages = self.logic.scan_all_religions_and_heritages()

        # Store data for use
        self.cult_scan_data = c_data

        # Build maps for clean display
        self.heritage_map = {h.replace("heritage_", "").replace("_", " ").title(): h for h in c_heritages}
        self.lang_map = {l.replace("language_", "").replace("_", " ").title(): l for l in c_langs}
        self.trad_map = {t.replace("tradition_", "").replace("_", " ").title(): t for t in c_trads}

        # Form
        cf = ttk.Frame(tab_cult, padding=10)
        cf.pack(fill=tk.BOTH, expand=True)

        ttk.Label(cf, text="Internal Key (e.g. new_culture):").grid(row=0, column=0, sticky=tk.W)
        self.rc_c_key = tk.StringVar()
        ttk.Entry(cf, textvariable=self.rc_c_key, width=20).grid(row=0, column=1, sticky=tk.W, padx=5, pady=2)

        ttk.Label(cf, text="Localization Name:").grid(row=0, column=2, sticky=tk.W)
        self.rc_c_name = tk.StringVar()
        ttk.Entry(cf, textvariable=self.rc_c_name, width=20).grid(row=0, column=3, sticky=tk.W, padx=5, pady=2)

        ttk.Label(cf, text="Color:").grid(row=1, column=0, sticky=tk.W)
        self.rc_c_rgb = [255, 255, 255]
        self.rc_c_color_prev = tk.Label(cf, text="     ", bg="#FFFFFF", relief="solid", borderwidth=1)
        self.rc_c_color_prev.grid(row=1, column=1, sticky=tk.W, padx=5)
        ttk.Button(cf, text="Pick", command=self.pick_cult_color).grid(row=1, column=2, sticky=tk.W)

        # Dropdowns
        ttk.Label(cf, text="Religion:").grid(row=2, column=0, sticky=tk.W)
        self.rc_c_rel = tk.StringVar()
        ttk.Combobox(cf, textvariable=self.rc_c_rel, values=r_keys, state="readonly").grid(row=2, column=1, sticky=tk.W, padx=5, pady=2)

        ttk.Label(cf, text="Heritage:").grid(row=2, column=2, sticky=tk.W)
        self.rc_c_her = tk.StringVar()
        ttk.Combobox(cf, textvariable=self.rc_c_her, values=sorted(list(self.heritage_map.keys())), state="readonly").grid(row=2, column=3, sticky=tk.W, padx=5, pady=2)

        ttk.Label(cf, text="Language:").grid(row=3, column=0, sticky=tk.W)
        self.rc_c_lang = tk.StringVar()
        ttk.Combobox(cf, textvariable=self.rc_c_lang, values=sorted(list(self.lang_map.keys())), state="readonly").grid(row=3, column=1, sticky=tk.W, padx=5, pady=2)

        ttk.Label(cf, text="Graphics:").grid(row=3, column=2, sticky=tk.W)
        self.rc_c_graph = tk.StringVar()
        ttk.Combobox(cf, textvariable=self.rc_c_graph, values=c_graphics, state="readonly").grid(row=3, column=3, sticky=tk.W, padx=5, pady=2)

        # Names Source
        ttk.Label(cf, text="Copy Names From (Existing Culture):").grid(row=4, column=0, sticky=tk.W, pady=(10, 2))
        self.rc_c_namesrc = tk.StringVar()
        ttk.Combobox(cf, textvariable=self.rc_c_namesrc, values=sorted(list(c_data.keys())), state="readonly").grid(row=4, column=1, sticky=tk.W, padx=5)

        # Traditions & Ethnicities (Lists)
        list_frame = ttk.Frame(cf)
        list_frame.grid(row=5, column=0, columnspan=4, sticky=tk.NSEW, pady=10)

        # Traditions
        tf = ttk.LabelFrame(list_frame, text="Traditions", padding=5)
        tf.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=(0, 5))
        self.rc_c_trad_list = tk.Listbox(tf, height=6, bg="white", fg="black", selectmode=tk.MULTIPLE, exportselection=False)
        self.rc_c_trad_list.pack(fill=tk.BOTH, expand=True)
        for t in sorted(list(self.trad_map.keys())): self.rc_c_trad_list.insert(tk.END, t)

        # Ethnicities
        ef = ttk.LabelFrame(list_frame, text="Ethnicities", padding=5)
        ef.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=(5, 0))
        self.rc_c_eth_list = tk.Listbox(ef, height=6, bg="white", fg="black", selectmode=tk.MULTIPLE, exportselection=False)
        self.rc_c_eth_list.pack(fill=tk.BOTH, expand=True)
        for e in c_eths: self.rc_c_eth_list.insert(tk.END, e)

        ttk.Button(cf, text="Save New Culture", command=self.save_new_culture_ui).grid(row=6, column=3, sticky=tk.E, pady=10)

        # --- Create Religion UI ---
        rf = ttk.Frame(tab_rel, padding=10)
        rf.pack(fill=tk.BOTH, expand=True)

        ttk.Label(rf, text="Internal Key (e.g. protestant):").grid(row=0, column=0, sticky=tk.W)
        self.rc_r_key = tk.StringVar()
        ttk.Entry(rf, textvariable=self.rc_r_key, width=20).grid(row=0, column=1, sticky=tk.W, padx=5, pady=2)

        ttk.Label(rf, text="Localization Name:").grid(row=0, column=2, sticky=tk.W)
        self.rc_r_name = tk.StringVar()
        ttk.Entry(rf, textvariable=self.rc_r_name, width=20).grid(row=0, column=3, sticky=tk.W, padx=5, pady=2)

        ttk.Label(rf, text="Color:").grid(row=1, column=0, sticky=tk.W)
        self.rc_r_rgb = [255, 255, 255]
        self.rc_r_color_prev = tk.Label(rf, text="     ", bg="#FFFFFF", relief="solid", borderwidth=1)
        self.rc_r_color_prev.grid(row=1, column=1, sticky=tk.W, padx=5)
        ttk.Button(rf, text="Pick", command=self.pick_rel_color).grid(row=1, column=2, sticky=tk.W)

        ttk.Label(rf, text="Heritage:").grid(row=2, column=0, sticky=tk.W)
        self.rc_r_her = tk.StringVar()
        ttk.Combobox(rf, textvariable=self.rc_r_her, values=r_heritages, state="readonly").grid(row=2, column=1, sticky=tk.W, padx=5, pady=2)

        ttk.Label(rf, text="Icon Path:").grid(row=3, column=0, sticky=tk.W)
        self.rc_r_icon = tk.StringVar(value="gfx/interface/icons/religion_icons/protestant.dds")
        ttk.Entry(rf, textvariable=self.rc_r_icon, width=40).grid(row=3, column=1, columnspan=3, sticky=tk.W, padx=5, pady=2)

        ttk.Button(rf, text="Save New Religion", command=self.save_new_religion_ui).grid(row=4, column=3, sticky=tk.E, pady=10)

        self.run_btn.pack_forget()

    def pick_cult_color(self):
        color = colorchooser.askcolor(title="Culture Color")
        if color[0]:
            self.rc_c_rgb = [int(x) for x in color[0]]
            self.rc_c_color_prev.config(bg=color[1])

    def pick_rel_color(self):
        color = colorchooser.askcolor(title="Religion Color")
        if color[0]:
            self.rc_r_rgb = [int(x) for x in color[0]]
            self.rc_r_color_prev.config(bg=color[1])

    def save_new_culture_ui(self):
        key = self.rc_c_key.get().strip()
        name = self.rc_c_name.get().strip()
        if not key or not name: return messagebox.showerror("Error", "Key and Name required.")

        if not self.rc_c_rel.get(): return messagebox.showerror("Error", "Religion required.")
        if not self.rc_c_her.get(): return messagebox.showerror("Error", "Heritage required.")
        if not self.rc_c_lang.get(): return messagebox.showerror("Error", "Language required.")
        if not self.rc_c_graph.get(): return messagebox.showerror("Error", "Graphics required.")

        # Map values back from display names
        display_her = self.rc_c_her.get()
        raw_her = self.heritage_map.get(display_her, display_her)

        display_lang = self.rc_c_lang.get()
        raw_lang = self.lang_map.get(display_lang, display_lang)

        # Get list selections and map back
        trads = []
        for i in self.rc_c_trad_list.curselection():
            display_t = self.rc_c_trad_list.get(i)
            trads.append(self.trad_map.get(display_t, display_t))

        eths = [self.rc_c_eth_list.get(i) for i in self.rc_c_eth_list.curselection()]

        # Names
        name_src = self.rc_c_namesrc.get()
        name_data = {}
        if name_src and name_src in self.cult_scan_data:
             name_data = self.cult_scan_data[name_src]

        self.logic.save_new_culture(
             key, name, self.rc_c_rgb,
             self.rc_c_rel.get(), raw_her, raw_lang,
             trads, self.rc_c_graph.get(), eths, name_data
        )
        self.refresh_all_dropdowns()
        messagebox.showinfo("Success", f"Culture {key} saved.")

    def save_new_religion_ui(self):
        key = self.rc_r_key.get().strip()
        name = self.rc_r_name.get().strip()
        if not key or not name: return messagebox.showerror("Error", "Key and Name required.")

        if not self.rc_r_her.get(): return messagebox.showerror("Error", "Heritage required.")

        self.logic.save_new_religion(
             key, name, self.rc_r_rgb, self.rc_r_her.get(), self.rc_r_icon.get()
        )
        self.refresh_all_dropdowns()
        messagebox.showinfo("Success", f"Religion {key} saved.")

    # --- MODE 9: JOURNAL & EVENT MANAGER ---
    def show_journal_ui(self):
        self.clear_content()
        self.mode = "JOURNAL_MANAGER"
        f = ttk.LabelFrame(self.content_frame, text="Journal/Event Manager", padding=15)
        f.pack(fill=tk.BOTH, expand=True)

        tabs = ttk.Notebook(f)
        tabs.pack(fill=tk.BOTH, expand=True)

        tab_journal = ttk.Frame(tabs)
        tab_event = ttk.Frame(tabs)

        tabs.add(tab_journal, text="Journal Manager")
        tabs.add(tab_event, text="Event Manager")

        # === TAB 1: JOURNAL ENTRIES ===
        self.build_journal_tab(tab_journal)

        # === TAB 2: EVENTS & MODIFIERS ===
        self.build_event_tab(tab_event)

        # Set main button for currently visible tab?
        # Actually each tab has save buttons usually, or shared button changes context.
        # Original JE used self.run_btn.
        # Let's hide the shared button for this complex view and put buttons inside tabs.
        self.run_btn.pack_forget()

        # Init lists
        self.refresh_je_list()
        self.refresh_evt_list()

    def build_journal_tab(self, parent):
        # Columns
        col1 = ttk.Frame(parent)
        col1.pack(side=tk.LEFT, fill=tk.BOTH, expand=False, padx=5, pady=10)

        col2 = ttk.Frame(parent)
        col2.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=5, pady=10)

        col3 = ttk.Frame(parent)
        col3.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=5, pady=10)

        # --- Column 1: Settings ---
        ttk.Label(col1, text="Settings", font=('Segoe UI', 10, 'bold')).pack(anchor=tk.W, pady=5)

        # Load Existing
        load_frame = ttk.Frame(col1)
        load_frame.pack(anchor=tk.W, fill=tk.X, pady=(0, 10))

        row1 = ttk.Frame(load_frame)
        row1.pack(fill=tk.X, anchor=tk.W)
        ttk.Label(row1, text="Load Entry:").pack(side=tk.LEFT)
        self.je_load_var = tk.StringVar()
        self.cb_je_load = ttk.Combobox(row1, textvariable=self.je_load_var, state="readonly", width=25)
        self.cb_je_load.pack(side=tk.LEFT, padx=5, fill=tk.X, expand=True)

        row2 = ttk.Frame(load_frame)
        row2.pack(fill=tk.X, anchor=tk.W, pady=(5,0))
        ttk.Button(row2, text="Load", command=self.load_journal_entry_ui).pack(side=tk.LEFT)
        ttk.Button(row2, text="Refresh", command=self.refresh_je_list).pack(side=tk.LEFT, padx=5)

        ttk.Label(col1, text="ID (e.g. je_unite_tribes):").pack(anchor=tk.W)
        self.je_id = tk.StringVar()
        ttk.Entry(col1, textvariable=self.je_id, width=25).pack(anchor=tk.W, pady=2)

        ttk.Label(col1, text="Title:").pack(anchor=tk.W)
        self.je_title = tk.StringVar()
        ttk.Entry(col1, textvariable=self.je_title, width=25).pack(anchor=tk.W, pady=2)

        ttk.Label(col1, text="Description:").pack(anchor=tk.W)
        self.je_desc = tk.Text(col1, height=5, width=25, bg="#473a2b", fg="#f3e7ce", relief="flat")
        self.je_desc.pack(anchor=tk.W, pady=2)

        ttk.Label(col1, text="Icon: event_default.dds").pack(anchor=tk.W, pady=10)

        # --- Column 2: Triggers ---
        ttk.Label(col2, text="Triggers", font=('Segoe UI', 10, 'bold')).pack(anchor=tk.W, pady=5)

        # Activation
        ttk.Label(col2, text="Activation (Possible):").pack(anchor=tk.W)
        self.lb_je_activation = tk.Listbox(col2, height=6, bg="#473a2b", fg="#f3e7ce")
        self.lb_je_activation.pack(fill=tk.X, pady=2)

        act_ctrl = ttk.Frame(col2)
        act_ctrl.pack(fill=tk.X)
        self.je_act_type = tk.StringVar()
        self.cb_je_act = ttk.Combobox(act_ctrl, textvariable=self.je_act_type, state="readonly", width=15)
        self.cb_je_act.pack(side=tk.LEFT, fill=tk.X, expand=True)
        ttk.Button(act_ctrl, text="+", width=3, command=lambda: self.add_je_item("activation")).pack(side=tk.LEFT)
        ttk.Button(act_ctrl, text="-", width=3, command=lambda: self.remove_je_item("activation")).pack(side=tk.LEFT)

        # Completion
        ttk.Label(col2, text="Completion (Complete):").pack(anchor=tk.W, pady=(10, 0))
        self.lb_je_completion = tk.Listbox(col2, height=6, bg="#473a2b", fg="#f3e7ce")
        self.lb_je_completion.pack(fill=tk.X, pady=2)

        comp_ctrl = ttk.Frame(col2)
        comp_ctrl.pack(fill=tk.X)
        self.je_comp_type = tk.StringVar()
        self.cb_je_comp = ttk.Combobox(comp_ctrl, textvariable=self.je_comp_type, state="readonly", width=15)
        self.cb_je_comp.pack(side=tk.LEFT, fill=tk.X, expand=True)
        ttk.Button(comp_ctrl, text="+", width=3, command=lambda: self.add_je_item("completion")).pack(side=tk.LEFT)
        ttk.Button(comp_ctrl, text="-", width=3, command=lambda: self.remove_je_item("completion")).pack(side=tk.LEFT)

        # --- Column 3: Rewards ---
        ttk.Label(col3, text="Rewards (On Complete)", font=('Segoe UI', 10, 'bold')).pack(anchor=tk.W, pady=5)

        self.lb_je_rewards = tk.Listbox(col3, height=15, bg="#473a2b", fg="#f3e7ce")
        self.lb_je_rewards.pack(fill=tk.X, pady=2)

        rew_ctrl = ttk.Frame(col3)
        rew_ctrl.pack(fill=tk.X)
        self.je_rew_type = tk.StringVar()
        self.cb_je_rew = ttk.Combobox(rew_ctrl, textvariable=self.je_rew_type, state="readonly", width=15)
        self.cb_je_rew.pack(side=tk.LEFT, fill=tk.X, expand=True)
        ttk.Button(rew_ctrl, text="+", width=3, command=lambda: self.add_je_item("reward")).pack(side=tk.LEFT)
        ttk.Button(rew_ctrl, text="-", width=3, command=lambda: self.remove_je_item("reward")).pack(side=tk.LEFT)

        # Populate Options
        self.je_act_opts = ["Is Country (Tag)", "Primary Culture", "Has Technology", "Has Law", "Is Great Power", "Is At War", "GDP Check"]
        self.je_comp_opts = ["Own State Region", "Building Count", "Literacy Rate", "Gold Reserves", "Battalion Count"]
        self.je_rew_opts = ["Interest Group Approval", "Add Treasury", "Add Prestige", "Add Loyalists", "Add Radicals", "Trigger Event", "Add Modifier"]

        self.cb_je_act['values'] = self.je_act_opts
        self.cb_je_act.current(0)
        self.cb_je_comp['values'] = self.je_comp_opts
        self.cb_je_comp.current(0)
        self.cb_je_rew['values'] = self.je_rew_opts
        self.cb_je_rew.current(0)

        # Save Button inside tab
        ttk.Button(col3, text="Save Journal Entry", command=self.save_journal_entry_ui).pack(fill=tk.X, pady=10)

    def build_event_tab(self, parent):
        # Layout: Left (Settings), Right (Options/Buttons), Bottom (Modifier Manager)

        main_pane = ttk.PanedWindow(parent, orient=tk.VERTICAL)
        main_pane.pack(fill=tk.BOTH, expand=True)

        top_pane = ttk.Frame(main_pane)
        main_pane.add(top_pane, weight=3)

        # --- Event Settings (Left) ---
        left_f = ttk.LabelFrame(top_pane, text="Event Settings", padding=10)
        left_f.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=5, pady=5)

        # Load Existing
        load_frame = ttk.Frame(left_f)
        load_frame.grid(row=0, column=0, columnspan=2, sticky=tk.EW, pady=(0, 10))
        ttk.Label(load_frame, text="Load Event:").pack(side=tk.LEFT)
        self.evt_load_var = tk.StringVar()
        self.cb_evt_load = ttk.Combobox(load_frame, textvariable=self.evt_load_var, state="readonly", width=25)
        self.cb_evt_load.pack(side=tk.LEFT, padx=5)
        ttk.Button(load_frame, text="Load", command=self.load_event_ui).pack(side=tk.LEFT)
        ttk.Button(load_frame, text="Refresh", command=self.refresh_evt_list).pack(side=tk.LEFT, padx=5)

        ttk.Label(left_f, text="Namespace (e.g. event_namespace):").grid(row=1, column=0, sticky=tk.W)
        self.evt_ns_input = tk.StringVar()
        ttk.Entry(left_f, textvariable=self.evt_ns_input).grid(row=1, column=1, sticky=tk.EW, pady=2)

        ttk.Label(left_f, text="Event ID (e.g. event_namespace.1):").grid(row=2, column=0, sticky=tk.W)
        self.evt_id_input = tk.StringVar()
        ttk.Entry(left_f, textvariable=self.evt_id_input).grid(row=2, column=1, sticky=tk.EW, pady=2)

        ttk.Label(left_f, text="Title:").grid(row=3, column=0, sticky=tk.W)
        self.evt_title = tk.StringVar()
        ttk.Entry(left_f, textvariable=self.evt_title).grid(row=3, column=1, sticky=tk.EW, pady=2)

        ttk.Label(left_f, text="Description:").grid(row=4, column=0, sticky=tk.NW)
        self.evt_desc = tk.Text(left_f, height=3, width=30, bg="#473a2b", fg="#f3e7ce", relief="flat")
        self.evt_desc.grid(row=4, column=1, sticky=tk.EW, pady=2)

        ttk.Label(left_f, text="Flavor Text:").grid(row=5, column=0, sticky=tk.NW)
        self.evt_flav = tk.Text(left_f, height=2, width=30, bg="#473a2b", fg="#f3e7ce", relief="flat")
        self.evt_flav.grid(row=5, column=1, sticky=tk.EW, pady=2)

        ttk.Label(left_f, text="Event video key:").grid(row=6,column=0,sticky=tk.W)
        self.evt_video = tk.StringVar(value="ep1_clandestine_meeting")
        ttk.Entry(left_f,textvariable=self.evt_video).grid(row=6,column=1,sticky=tk.EW,pady=2)

        # --- Event Options (Right) ---
        right_f = ttk.LabelFrame(top_pane, text="Options (Buttons)", padding=10)
        right_f.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=5, pady=5)

        self.evt_opts_list = tk.Listbox(right_f, height=8, bg="#473a2b", fg="#f3e7ce")
        self.evt_opts_list.pack(fill=tk.BOTH, expand=True, pady=2)

        btn_ctrl = ttk.Frame(right_f)
        btn_ctrl.pack(fill=tk.X)
        ttk.Button(btn_ctrl, text="Add Option", command=self.add_event_option_popup).pack(side=tk.LEFT, fill=tk.X, expand=True)
        ttk.Button(btn_ctrl, text="Remove", command=self.remove_event_option).pack(side=tk.LEFT, fill=tk.X, expand=True)

        # Save Event Button
        ttk.Button(right_f, text="Save Event", command=self.save_event_ui).pack(fill=tk.X, pady=10)

        # --- Modifiers Manager (Bottom) ---
        bot_pane = ttk.LabelFrame(main_pane, text="Modifier Manager", padding=10)
        main_pane.add(bot_pane, weight=1)

        # Preset Selector
        mod_sel_f = ttk.Frame(bot_pane)
        mod_sel_f.pack(fill=tk.X, pady=5)
        ttk.Label(mod_sel_f, text="Popular Modifiers:").pack(side=tk.LEFT)

        # Format presets for dropdown: "Category - Name"
        self.mod_presets_map = {f"{m[0]}": m for m in self.logic.POPULAR_MODIFIERS}
        self.mod_preset_var = tk.StringVar()
        cb_presets = ttk.Combobox(mod_sel_f, textvariable=self.mod_preset_var, values=list(self.mod_presets_map.keys()), state="readonly", width=40)
        cb_presets.pack(side=tk.LEFT, padx=5)
        ttk.Button(mod_sel_f, text="Load Preset", command=self.load_mod_preset).pack(side=tk.LEFT)

        # Custom Definition
        def_f = ttk.Frame(bot_pane)
        def_f.pack(fill=tk.X, pady=5)

        ttk.Label(def_f, text="Modifier Key:").grid(row=0, column=0, sticky=tk.W)
        self.mod_key = tk.StringVar()
        ttk.Entry(def_f, textvariable=self.mod_key, width=25).grid(row=0, column=1, padx=5)

        ttk.Label(def_f, text="Name:").grid(row=1, column=0, sticky=tk.W)
        self.mod_loc_name = tk.StringVar()
        ttk.Entry(def_f, textvariable=self.mod_loc_name, width=25).grid(row=1, column=1, padx=5)

        ttk.Label(def_f, text="Description:").grid(row=1, column=2, sticky=tk.W)
        self.mod_loc_desc = tk.StringVar()
        ttk.Entry(def_f, textvariable=self.mod_loc_desc, width=30).grid(row=1, column=3, padx=5)

        ttk.Label(def_f, text="Effects (e.g. unit_offense_mult = 0.1):").grid(row=2, column=0, sticky=tk.NW, pady=5)
        self.mod_effects = tk.Text(def_f, height=3, width=50, bg="#473a2b", fg="#f3e7ce", relief="flat")
        self.mod_effects.grid(row=2, column=1, columnspan=3, sticky=tk.W, padx=5, pady=5)

        ttk.Button(def_f, text="Save Modifier", command=self.save_modifier_ui).grid(row=3, column=3, sticky=tk.E)

        # Init option storage
        self.current_event_options = []

    def add_event_option_popup(self):
        # Popup to define an option (Name, IG Effects, Modifiers)
        win = tk.Toplevel(self)
        win.title("Add Option")
        win.geometry("500x600")
        win.configure(bg="#28231d")

        # Name
        ttk.Label(win, text="Option Name (Button Text):").pack(pady=5)
        name_var = tk.StringVar()
        ttk.Entry(win, textvariable=name_var, width=40).pack()

        # Modifier Effects
        mod_frame = ttk.LabelFrame(win, text="Apply Modifier", padding=5)
        mod_frame.pack(fill=tk.X, padx=10, pady=5)

        mod_rows = []
        def add_mod_row():
            r = ttk.Frame(mod_frame)
            r.pack(fill=tk.X, pady=2)

            # Scanned modifiers
            scanned_mods = self.logic.scan_modifiers()

            m_var = tk.StringVar()
            cb = ttk.Combobox(r, textvariable=m_var, values=scanned_mods, width=25)
            cb.pack(side=tk.LEFT)

            ttk.Label(r, text="Months:").pack(side=tk.LEFT, padx=2)
            d_var = tk.IntVar(value=60)
            ttk.Entry(r, textvariable=d_var, width=5).pack(side=tk.LEFT)
            mod_rows.append((m_var, d_var))

        ttk.Button(mod_frame, text="+ Add Modifier", command=add_mod_row).pack()

        # General Effects (Now includes IG Approval)
        gen_frame = ttk.LabelFrame(win, text="General Effects & Rewards", padding=5)
        gen_frame.pack(fill=tk.X, padx=10, pady=5)

        gen_rows = []
        def add_gen_row():
            r = ttk.Frame(gen_frame)
            r.pack(fill=tk.X, pady=2)

            g_type = tk.StringVar()
            val1_var = tk.StringVar()
            val2_var = tk.StringVar()

            # Treasury, Prestige, Loyalists, Radicals, Trigger Event, IG Approval
            opts = ["Add Treasury", "Add Prestige", "Add Loyalists", "Add Radicals", "Trigger Event", "Interest Group Approval"]
            cb = ttk.Combobox(r, textvariable=g_type, values=opts, width=23, state="readonly")
            cb.pack(side=tk.LEFT)

            # Container for dynamic inputs
            input_frame = ttk.Frame(r)
            input_frame.pack(side=tk.LEFT, padx=5)

            # Widgets
            entry_v1 = ttk.Entry(input_frame, textvariable=val1_var, width=15)

            igs = ["armed_forces", "industrialists", "intelligentsia", "landowners", "devout", "petty_bourgeoisie", "rural_folk", "trade_unions"]
            cb_ig = ttk.Combobox(input_frame, textvariable=val1_var, values=igs, width=15, state="readonly")

            entry_v2 = ttk.Entry(input_frame, textvariable=val2_var, width=5)

            def on_type_change(event=None):
                t = g_type.get()
                # Reset view
                entry_v1.pack_forget()
                cb_ig.pack_forget()
                entry_v2.pack_forget()

                if t == "Interest Group Approval":
                    cb_ig.pack(side=tk.LEFT)
                    ttk.Label(input_frame, text="Val:").pack(side=tk.LEFT)
                    entry_v2.pack(side=tk.LEFT)
                else:
                    entry_v1.pack(side=tk.LEFT)

            cb.bind("<<ComboboxSelected>>", on_type_change)
            entry_v1.pack(side=tk.LEFT) # Default

            gen_rows.append((g_type, val1_var, val2_var))

        ttk.Button(gen_frame, text="+ Add Effect", command=add_gen_row).pack()

        def save_opt():
            opt_data = {
                "name": name_var.get(),
                "effects": "",
                "ig_effects": [],
                "mod_effects": [],
                "general_effects": []
            }

            for m_v, d_v in mod_rows:
                if m_v.get():
                    opt_data["mod_effects"].append({"name": m_v.get(), "duration": d_v.get()})

            for g_t, g_v1, g_v2 in gen_rows:
                t = g_t.get()
                v1 = g_v1.get().strip()
                v2 = g_v2.get().strip()

                if t:
                    formatted = ""
                    if t == "Add Treasury": formatted = f"add_treasury = {v1}"
                    elif t == "Add Prestige": formatted = f"add_prestige = {v1}"
                    elif t == "Add Loyalists": formatted = f"add_loyalists = {{ value = {v1} }}"
                    elif t == "Add Radicals": formatted = f"add_radicals = {{ value = {v1} }}"
                    elif t == "Trigger Event": formatted = f"trigger_event = {v1}"
                    elif t == "Interest Group Approval":
                         if v1 and v2:
                             opt_data["ig_effects"].append({"ig": v1, "value": v2})

                    if formatted:
                        opt_data["general_effects"].append(formatted)

            self.current_event_options.append(opt_data)
            self.evt_opts_list.insert(tk.END, opt_data["name"])
            win.destroy()

        ttk.Button(win, text="Add", command=save_opt).pack(pady=10)

    def remove_event_option(self):
        sel = self.evt_opts_list.curselection()
        if sel:
            idx = sel[0]
            self.evt_opts_list.delete(idx)
            self.current_event_options.pop(idx)

    def load_mod_preset(self):
        sel = self.mod_preset_var.get()
        if sel in self.mod_presets_map:
            # Tuple: (Desc, Code, Scope)
            p = self.mod_presets_map[sel]
            code_key = p[1]

            current_txt = self.mod_effects.get("1.0", tk.END).strip()
            new_line = f"{code_key} = 0.1  # {p[2]}"
            if current_txt:
                self.mod_effects.insert(tk.END, "\n" + new_line)
            else:
                self.mod_effects.insert(tk.END, new_line)

    def save_modifier_ui(self):
        key = self.mod_key.get().strip()
        icon = "gfx/interface/icons/timed_modifier_icons/modifier_documents_negative.dds"
        eff = self.mod_effects.get("1.0", tk.END).strip()
        lname = self.mod_loc_name.get().strip()
        ldesc = self.mod_loc_desc.get().strip()

        if not key or not eff: return messagebox.showerror("Error", "Key and Effects required.")

        self.logic.save_modifier(key, icon, eff, lname, ldesc)
        messagebox.showinfo("Success", f"Modifier {key} saved to static_modifiers.")

    def save_event_ui(self):
        namespace = self.evt_ns_input.get().strip()
        eid = self.evt_id_input.get().strip()
        tit = self.evt_title.get().strip()
        desc = self.evt_desc.get("1.0", tk.END).strip()
        flav = self.evt_flav.get("1.0", tk.END).strip()
        img = self.evt_video.get().strip()

        if not namespace or not eid or not tit: return messagebox.showerror("Error", "Namespace, Event ID, and Title required.")

        self.logic.save_event(namespace, eid, tit, desc, flav, img, self.current_event_options)
        messagebox.showinfo("Success", f"Event {eid} saved.")

    def refresh_je_list(self):
        entries = self.logic.scan_journal_entries()
        self.cb_je_load['values'] = entries
        if entries: self.cb_je_load.current(0)

    def load_journal_entry_ui(self):
        je_id = self.je_load_var.get()
        if not je_id: return

        data = self.logic.get_journal_entry_data(je_id)
        if not data: return messagebox.showerror("Error", "Could not load data.")

        self.je_id.set(data['id'])
        self.je_title.set(data.get('title', ''))
        self.je_desc.delete("1.0", tk.END)
        self.je_desc.insert(tk.END, data.get('desc', ''))

        self.lb_je_activation.delete(0, tk.END)
        for x in data['activation']: self.lb_je_activation.insert(tk.END, x)

        self.lb_je_completion.delete(0, tk.END)
        for x in data['completion']: self.lb_je_completion.insert(tk.END, x)

        self.lb_je_rewards.delete(0, tk.END)
        for x in data['rewards']: self.lb_je_rewards.insert(tk.END, x)

        self.log_message(f"Loaded Journal Entry {je_id}", 'success')

    def refresh_evt_list(self):
        events = self.logic.scan_events()
        self.cb_evt_load['values'] = events
        if events: self.cb_evt_load.current(0)

    def load_event_ui(self):
        evt_id = self.evt_load_var.get()
        if not evt_id: return

        data = self.logic.get_event_data(evt_id)
        if not data: return messagebox.showerror("Error", "Could not load event.")

        self.evt_ns_input.set(data.get('namespace', ''))
        self.evt_id_input.set(evt_id)
        self.evt_title.set(data.get('title', ''))
        self.evt_video.set(data.get('image', ''))

        self.evt_desc.delete("1.0", tk.END)
        self.evt_desc.insert(tk.END, data.get('desc', ''))

        self.evt_flav.delete("1.0", tk.END)
        self.evt_flav.insert(tk.END, data.get('flavor', ''))

        self.current_event_options = data.get('options', [])
        self.evt_opts_list.delete(0, tk.END)
        for opt in self.current_event_options:
            self.evt_opts_list.insert(tk.END, opt.get('name', 'Option'))

        self.log_message(f"Loaded Event {evt_id}", 'success')

    def add_je_item(self, list_type):
        # Dialog for input
        val = None
        sel_type = ""

        if list_type == "activation":
            sel_type = self.je_act_type.get()
            if sel_type == "Is Country (Tag)":
                tags = self.logic.scan_all_tags()
                val = self.ask_popup_input("Select Tag", tags)
                if val: val = f"this = c:{val.upper()}"
            elif sel_type == "Primary Culture":
                c_opts, _, _, _, _, _ = self.logic.scan_culture_definitions()
                all_culs = sorted(list(c_opts.keys()))
                val = self.ask_popup_input("Select Culture", all_culs)
                if val: val = f"country_has_primary_culture = cu:{val}"
            elif sel_type == "Has Technology":
                techs = self.logic.scan_technologies()
                val = self.ask_popup_input("Select Technology", techs)
                if val: val = f"has_technology = {val}"
            elif sel_type == "Has Law":
                laws = self.logic.scan_laws()
                val = self.ask_popup_input("Select Law", laws)
                if val: val = f"has_law = {val}"
            elif sel_type == "Is Great Power":
                val = "is_great_power = yes"
            elif sel_type == "Is At War":
                val = "is_at_war = yes"
            elif sel_type == "GDP Check":
                num = simpledialog.askfloat("Input", "GDP Value:")
                if num: val = f"gdp > {int(num)}"

        elif list_type == "completion":
            sel_type = self.je_comp_type.get()
            if sel_type == "Own State Region":
                # Assuming state scanning logic is generic or we have a list of states
                # Using hardcoded or existing scan? logic.format_state_clean implies input string
                # Let's ask for string or offer list if we can easily get all states (Vic3Logic doesn't have scan_all_states yet but Transfer uses input)
                # Let's stick to text input for state for now or scan file names in history/states?
                # Actually, logic.get_state_homelands uses scan.
                # Let's ask for simple text input for simplicity
                st = simpledialog.askstring("Input", "State Name (e.g. california):")
                if st: val = f"owns_entire_state_region = STATE_{st.upper()}"
            elif sel_type == "Building Count":
                bldgs = self.logic.scan_buildings()
                b = self.ask_popup_input("Select Building", bldgs)
                lvl = simpledialog.askinteger("Input", "Level >=")
                if b and lvl: val = f"scope:country = {{ has_building_level = {{ building = {b} level >= {lvl} }} }}"
            elif sel_type == "Literacy Rate":
                r = simpledialog.askfloat("Input", "Rate (0.0 - 1.0):")
                if r: val = f"literacy_rate >= {r}"
            elif sel_type == "Gold Reserves":
                num = simpledialog.askinteger("Input", "Amount:")
                if num: val = f"gold_reserves >= {num}"
            elif sel_type == "Battalion Count":
                num = simpledialog.askinteger("Input", "Count:")
                if num: val = f"army_size >= {num}"

        elif list_type == "reward":
            sel_type = self.je_rew_type.get()
            if sel_type == "Add Treasury":
                num = simpledialog.askinteger("Input", "Amount:")
                if num: val = f"add_treasury = {num}"
            elif sel_type == "Add Prestige":
                num = simpledialog.askinteger("Input", "Amount:")
                if num: val = f"add_prestige = {num}"
            elif sel_type == "Add Loyalists":
                r = simpledialog.askfloat("Input", "Value (0.0 - 1.0):")
                if r: val = f"add_loyalists = {{ value = {r} }}"
            elif sel_type == "Add Radicals":
                r = simpledialog.askfloat("Input", "Value (0.0 - 1.0):")
                if r: val = f"add_radicals = {{ value = {r} }}"
            elif sel_type == "Trigger Event":
                evts = self.logic.scan_events()
                evt = self.ask_popup_input("Event ID", evts)
                if evt: val = f"trigger_event = {evt}"
            elif sel_type == "Add Modifier":
                mods = self.logic.scan_modifiers()
                name = self.ask_popup_input("Select Modifier", mods)
                dur = simpledialog.askinteger("Input", "Months:")
                if name and dur: val = f"add_modifier = {{ name = {name} months = {dur} }}"
            elif sel_type == "Interest Group Approval":
                igs = ["armed_forces", "industrialists", "intelligentsia", "landowners", "devout", "petty_bourgeoisie", "rural_folk", "trade_unions"]
                ig = self.ask_popup_input("Select IG", igs)
                val_int = simpledialog.askinteger("Input", "Value (can be negative):")
                if ig and val_int is not None:
                    val = f"ig:{ig} = {{ add_approval = {{ value = {val_int} }} }}"

        if val:
            if list_type == "activation": self.lb_je_activation.insert(tk.END, val)
            elif list_type == "completion": self.lb_je_completion.insert(tk.END, val)
            elif list_type == "reward": self.lb_je_rewards.insert(tk.END, val)

    def remove_je_item(self, list_type):
        lb = None
        if list_type == "activation": lb = self.lb_je_activation
        elif list_type == "completion": lb = self.lb_je_completion
        elif list_type == "reward": lb = self.lb_je_rewards

        sel = lb.curselection()
        if sel: lb.delete(sel[0])

    def ask_popup_input(self, title, options):
        # A simple dialog to select from list
        # Since simpledialog doesn't support Combobox, we build a custom toplevel

        result = [None]

        win = tk.Toplevel(self)
        win.title(title)
        win.geometry("300x100")
        win.transient(self)
        win.grab_set()

        # Center on parent
        x = self.winfo_rootx() + 50
        y = self.winfo_rooty() + 50
        win.geometry(f"+{x}+{y}")

        cb = ttk.Combobox(win, values=options, state="normal") # Allow typing for filter
        cb.pack(pady=10, padx=10, fill=tk.X)
        cb.focus_set()

        def on_ok():
            result[0] = cb.get()
            win.destroy()

        ttk.Button(win, text="OK", command=on_ok).pack()
        self.wait_window(win)
        return result[0]

    def save_journal_entry_ui(self):
        if not self.je_id.get(): return messagebox.showerror("Error", "ID required.")
        if not self.je_title.get(): return messagebox.showerror("Error", "Title required.")

        data = {
            "id": self.je_id.get().strip(),
            "title": self.je_title.get().strip(),
            "desc": self.je_desc.get("1.0", tk.END).strip(),
            "activation": self.lb_je_activation.get(0, tk.END),
            "completion": self.lb_je_completion.get(0, tk.END),
            "rewards": self.lb_je_rewards.get(0, tk.END)
        }

        self.logic.save_journal_entry(data)
        messagebox.showinfo("Success", f"Journal Entry {data['id']} saved.")

    # --- MODE 10: STATE MANAGER (Index shifted) ---
    def show_state_manager_ui(self):
        self.clear_content()
        self.mode = "STATE_MANAGER"
        f = ttk.LabelFrame(self.content_frame, text="State Manager", padding=15)
        f.pack(fill=tk.BOTH, expand=True)

        # 1. State Selector
        sel_frame = ttk.Frame(f)
        sel_frame.pack(fill=tk.X, pady=5)
        ttk.Label(sel_frame, text="State Name (e.g. texas):").pack(side=tk.LEFT)
        self.sm_state_name = tk.StringVar()
        e_st = ttk.Entry(sel_frame, textvariable=self.sm_state_name, width=20)
        e_st.pack(side=tk.LEFT, padx=5)
        e_st.bind("<Return>", lambda e: self.load_state_manager_data())
        ttk.Button(sel_frame, text="Load State Data", command=self.load_state_manager_data).pack(side=tk.LEFT, padx=5)
        ttk.Button(sel_frame, text="Select from map", command=lambda: self.open_editor_picker("state", self.select_map_state)).pack(side=tk.LEFT, padx=5)

        # 2. Homelands & Buildings
        hb_container = ttk.Frame(f)
        hb_container.pack(fill=tk.BOTH, expand=True, pady=5)

        # --- Homelands (Left) ---
        h_frame = ttk.LabelFrame(hb_container, text="Homelands", padding=10)
        h_frame.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=(0, 5))

        self.lb_homelands = tk.Listbox(h_frame, height=6, bg="#473a2b", fg="#f3e7ce")
        self.lb_homelands.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=(0,5))

        h_ctrl = ttk.Frame(h_frame)
        h_ctrl.pack(side=tk.LEFT, fill=tk.Y)

        self.sm_homeland_add = tk.StringVar()
        self.cb_homeland_add = ttk.Combobox(h_ctrl, textvariable=self.sm_homeland_add, width=15)
        # Will populate on scan
        self.cb_homeland_add.pack(pady=2)

        ttk.Button(h_ctrl, text="Add", command=self.add_state_homeland).pack(fill=tk.X, pady=2)
        ttk.Button(h_ctrl, text="Remove", command=self.remove_state_homeland).pack(fill=tk.X, pady=2)
        ttk.Button(h_ctrl, text="Save", command=self.save_state_homelands_ui).pack(fill=tk.X, pady=(10, 2))

        # --- Buildings (Right) ---
        b_frame = ttk.LabelFrame(hb_container, text="Buildings", padding=10)
        b_frame.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=(5, 0))

        self.lb_buildings = tk.Listbox(b_frame, height=6, bg="#473a2b", fg="#f3e7ce", selectmode=tk.EXTENDED, exportselection=False)
        self.lb_buildings.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=(0,5))
        self.lb_buildings.bind('<<ListboxSelect>>', self.on_building_select)

        b_ctrl = ttk.Frame(b_frame)
        b_ctrl.pack(side=tk.LEFT, fill=tk.Y)

        ttk.Label(b_ctrl, text="Region Owner (Land):").pack(pady=(2,0))
        self.sm_land_owner = tk.StringVar()
        self.cb_land_owner = ttk.Combobox(b_ctrl, textvariable=self.sm_land_owner, width=15, state="readonly")
        self.cb_land_owner.pack(pady=2)

        ttk.Label(b_ctrl, text="Buildings:").pack(pady=(2,0))
        self.sm_building_add = tk.StringVar()
        self.cb_building_add = ttk.Combobox(b_ctrl, textvariable=self.sm_building_add, width=15, state="readonly")
        self.cb_building_add.pack(pady=2)

        self.sm_building_level = tk.StringVar(value="1")
        lvl_frame = ttk.Frame(b_ctrl)
        lvl_frame.pack(pady=2)
        ttk.Label(lvl_frame, text="Level:").pack(side=tk.LEFT, padx=(0, 5))
        ttk.Entry(lvl_frame, textvariable=self.sm_building_level, width=5).pack(side=tk.LEFT)

        ttk.Button(b_ctrl, text="Add", command=self.add_state_building_ui).pack(fill=tk.X, pady=2)
        ttk.Button(b_ctrl, text="Remove", command=self.remove_state_building_ui).pack(fill=tk.X, pady=2)
        ttk.Button(b_ctrl, text="Update", command=self.update_state_building_level_ui).pack(fill=tk.X, pady=2)

        # 3. Resources (New Section)
        r_frame = ttk.LabelFrame(f, text="Resources", padding=10)
        r_frame.pack(fill=tk.BOTH, expand=True, pady=5)

        # Arable Land at top
        r_top = ttk.Frame(r_frame)
        r_top.pack(fill=tk.X, pady=(0, 5))
        ttk.Label(r_top, text="Arable Land:").pack(side=tk.LEFT)
        self.sm_arable_land = tk.StringVar(value="0")
        ttk.Entry(r_top, textvariable=self.sm_arable_land, width=8).pack(side=tk.LEFT, padx=5)
        ttk.Button(r_top, text="Save Resources", command=self.save_state_resources_ui).pack(side=tk.RIGHT)

        # Tabs for resource types
        r_tabs = ttk.Notebook(r_frame)
        r_tabs.pack(fill=tk.BOTH, expand=True)

        tab_capped = ttk.Frame(r_tabs)
        tab_arable = ttk.Frame(r_tabs)
        tab_disc = ttk.Frame(r_tabs)

        r_tabs.add(tab_capped, text="Capped (Mines/Forestry)")
        r_tabs.add(tab_arable, text="Arable (Farms)")
        r_tabs.add(tab_disc, text="Discoverable (Oil/Gold)")

        # Lists for options
        # Prompt lists:
        self.RES_CAPPED_OPTS = sorted([
            "building_iron_mine", "building_coal_mine", "building_lead_mine",
            "building_sulfur_mine", "building_gold_mine", "building_logging_camp",
            "building_fishing_wharf", "building_whaling_station"
        ])
        self.RES_ARABLE_OPTS = sorted([
            "building_rye_farm", "building_wheat_farm", "building_rice_farm", "building_maize_farm", "building_millet_farm",
            "building_livestock_ranch", "building_vineyard",
            "building_cotton_plantation", "building_silk_plantation", "building_dye_plantation",
            "building_opium_plantation", "building_tea_plantation", "building_coffee_plantation",
            "building_tobacco_plantation", "building_sugar_plantation", "building_fruit_plantation",
            "building_rubber_plantation"
        ])
        self.RES_DISC_OPTS = ["building_oil_rig", "building_gold_fields", "building_rubber_plantation"]

        # -- Tab Capped --
        self.tv_capped = ttk.Treeview(tab_capped, columns=("type", "amount"), show="headings", height=5)
        self.tv_capped.heading("type", text="Resource"); self.tv_capped.column("type", width=200)
        self.tv_capped.heading("amount", text="Amount"); self.tv_capped.column("amount", width=80)
        self.tv_capped.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

        c_ctrl = ttk.Frame(tab_capped)
        c_ctrl.pack(side=tk.RIGHT, fill=tk.Y, padx=5)
        self.sm_res_cap_type = tk.StringVar()
        ttk.Combobox(c_ctrl, textvariable=self.sm_res_cap_type, values=self.RES_CAPPED_OPTS, width=25).pack(pady=2)
        self.sm_res_cap_amt = tk.StringVar(value="10")
        ttk.Entry(c_ctrl, textvariable=self.sm_res_cap_amt, width=10).pack(pady=2)
        ttk.Button(c_ctrl, text="Add/Update", command=lambda: self.add_resource_ui("capped")).pack(fill=tk.X, pady=2)
        ttk.Button(c_ctrl, text="Remove", command=lambda: self.remove_resource_ui("capped")).pack(fill=tk.X, pady=2)

        # -- Tab Arable --
        self.lb_arable = tk.Listbox(tab_arable, height=5)
        self.lb_arable.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

        a_ctrl = ttk.Frame(tab_arable)
        a_ctrl.pack(side=tk.RIGHT, fill=tk.Y, padx=5)
        self.sm_res_ara_type = tk.StringVar()
        ttk.Combobox(a_ctrl, textvariable=self.sm_res_ara_type, values=self.RES_ARABLE_OPTS, width=25).pack(pady=2)
        ttk.Button(a_ctrl, text="Add", command=lambda: self.add_resource_ui("arable")).pack(fill=tk.X, pady=2)
        ttk.Button(a_ctrl, text="Remove", command=lambda: self.remove_resource_ui("arable")).pack(fill=tk.X, pady=2)

        # -- Tab Discoverable --
        self.tv_disc = ttk.Treeview(tab_disc, columns=("type", "amount"), show="headings", height=5)
        self.tv_disc.heading("type", text="Resource"); self.tv_disc.column("type", width=200)
        self.tv_disc.heading("amount", text="Undiscovered"); self.tv_disc.column("amount", width=100)
        self.tv_disc.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

        d_ctrl = ttk.Frame(tab_disc)
        d_ctrl.pack(side=tk.RIGHT, fill=tk.Y, padx=5)
        self.sm_res_disc_type = tk.StringVar()
        ttk.Combobox(d_ctrl, textvariable=self.sm_res_disc_type, values=self.RES_DISC_OPTS, width=25).pack(pady=2)
        self.sm_res_disc_amt = tk.StringVar(value="20")
        ttk.Entry(d_ctrl, textvariable=self.sm_res_disc_amt, width=10).pack(pady=2)
        ttk.Button(d_ctrl, text="Add/Update", command=lambda: self.add_resource_ui("discoverable")).pack(fill=tk.X, pady=2)
        ttk.Button(d_ctrl, text="Remove", command=lambda: self.remove_resource_ui("discoverable")).pack(fill=tk.X, pady=2)

        # 4. Population
        p_frame = ttk.LabelFrame(f, text="Population", padding=10)
        p_frame.pack(fill=tk.BOTH, expand=True, pady=5)

        # Notebook for modes
        pop_tabs = ttk.Notebook(p_frame)
        pop_tabs.pack(fill=tk.BOTH, expand=True, pady=5)

        tab_mix = ttk.Frame(pop_tabs)
        tab_man = ttk.Frame(pop_tabs)
        pop_tabs.add(tab_mix, text="Demographics Mixer (Automatic)")
        pop_tabs.add(tab_man, text="Manual Edit")

        # --- TAB 1: MIXER ---
        mix_ctrl = ttk.Frame(tab_mix, padding=5)
        mix_ctrl.pack(fill=tk.X)

        ttk.Label(mix_ctrl, text="Scope:").pack(side=tk.LEFT)
        self.sm_mix_scope = tk.StringVar(value="full")
        self.sm_mix_scope.trace("w", self.on_sm_mix_scope_change)
        ttk.Radiobutton(mix_ctrl, text="Full State", variable=self.sm_mix_scope, value="full").pack(side=tk.LEFT, padx=5)
        ttk.Radiobutton(mix_ctrl, text="Specific Region Owner", variable=self.sm_mix_scope, value="owner").pack(side=tk.LEFT, padx=5)

        self.sm_mix_owner = tk.StringVar()
        self.cb_mix_owner = ttk.Combobox(mix_ctrl, textvariable=self.sm_mix_owner, state="readonly", width=15)
        self.cb_mix_owner.pack(side=tk.LEFT, padx=5)
        self.cb_mix_owner.bind("<<ComboboxSelected>>", self.on_sm_mix_owner_change)

        ttk.Label(mix_ctrl, text="Total Pop:").pack(side=tk.LEFT, padx=(10, 0))
        self.sm_mix_total = tk.StringVar()
        self.sm_mix_total.trace("w", self.on_sm_mix_total_change)
        ttk.Entry(mix_ctrl, textvariable=self.sm_mix_total, width=12).pack(side=tk.LEFT, padx=5)

        # Mixer UI
        self.sm_mixer = DemographicsMixer(tab_mix)
        self.sm_mixer.pack(fill=tk.BOTH, expand=True, pady=5)

        mix_bot = ttk.Frame(tab_mix, padding=5)
        mix_bot.pack(fill=tk.X)

        ttk.Button(mix_bot, text="Add Group", command=self.add_demographic_group_ui).pack(side=tk.LEFT)

        self.sm_retain_loc = tk.BooleanVar(value=False)
        ttk.Checkbutton(mix_bot, text="Retain Demographic Location", variable=self.sm_retain_loc).pack(side=tk.LEFT, padx=10)

        ttk.Button(mix_bot, text="Apply Changes", command=self.apply_demographics_ui).pack(side=tk.RIGHT)

        # --- TAB 2: MANUAL ---
        # Total (Moved here or duplicated? Original had total outside. I'll keep total inside or sync it)
        # Original UI for manual edit

        ind_frame = ttk.Frame(tab_man, padding=5)
        ind_frame.pack(fill=tk.BOTH, expand=True)

        tot_frame = ttk.Frame(ind_frame)
        tot_frame.pack(fill=tk.X, pady=5)
        ttk.Label(tot_frame, text="Total State Population (Manual Dist):").pack(side=tk.LEFT)
        self.sm_total_pop = tk.StringVar()
        ttk.Entry(tot_frame, textvariable=self.sm_total_pop, width=15).pack(side=tk.LEFT, padx=5)
        ttk.Button(tot_frame, text="Update Total", command=self.update_state_total_pop).pack(side=tk.LEFT, padx=5)

        ind_sub = ttk.LabelFrame(ind_frame, text="Edit Individual Pop Block", padding=5)
        ind_sub.pack(fill=tk.BOTH, expand=True, pady=5)

        ttk.Label(ind_sub, text="Select Pop Block:").grid(row=0, column=0, sticky=tk.W)
        self.sm_pop_select = tk.StringVar()
        self.cb_pop_select = ttk.Combobox(ind_sub, textvariable=self.sm_pop_select, state="readonly", width=60)
        self.cb_pop_select.grid(row=0, column=1, columnspan=5, sticky=tk.W, padx=5, pady=2)
        self.cb_pop_select.bind("<<ComboboxSelected>>", self.on_state_pop_select)

        ttk.Label(ind_sub, text="Culture:").grid(row=1, column=0, sticky=tk.W)
        self.sm_pop_cul = tk.StringVar()
        self.cb_pop_cul = ttk.Combobox(ind_sub, textvariable=self.sm_pop_cul, width=20)
        self.cb_pop_cul.grid(row=1, column=1, sticky=tk.W, padx=5)
        ttk.Button(ind_sub, text="Full Conversion", command=self.convert_state_pops_culture_ui).grid(row=1, column=2, padx=5)

        ttk.Label(ind_sub, text="Religion:").grid(row=1, column=3, sticky=tk.W)
        self.sm_pop_rel = tk.StringVar()
        self.cb_pop_rel = ttk.Combobox(ind_sub, textvariable=self.sm_pop_rel, width=20)
        self.cb_pop_rel.grid(row=1, column=4, sticky=tk.W, padx=5)
        ttk.Button(ind_sub, text="Full Conversion", command=self.convert_state_pops_religion_ui).grid(row=1, column=5, padx=5)

        ttk.Label(ind_sub, text="Size:").grid(row=2, column=0, sticky=tk.W)
        self.sm_pop_size = tk.StringVar()
        ttk.Entry(ind_sub, textvariable=self.sm_pop_size, width=15).grid(row=2, column=1, sticky=tk.W, padx=5, pady=2)

        ttk.Button(ind_sub, text="Update This Pop", command=self.save_single_pop_ui).grid(row=2, column=5, sticky=tk.E, pady=2)

        # Init options
        c_opts, _, _, _, _, _ = self.logic.scan_culture_definitions()
        all_culs = sorted(list(c_opts.keys()))
        self.cb_homeland_add['values'] = all_culs
        self.cb_pop_cul['values'] = all_culs

        _, r_opts = self.logic.scan_all_religions_and_heritages()
        # Need religions not heritages
        r_all, _ = self.logic.scan_all_religions_and_heritages()
        # scan_definitions_for_options also gives used religions
        _, def_rels, _, _ = self.logic.scan_definitions_for_options()
        self.cb_pop_rel['values'] = sorted(list(set(r_all + def_rels)))

        self.current_state_homelands = []
        self.current_state_buildings = []
        self.current_state_pops = []

        # Populate building types
        self.cb_building_add['values'] = self.logic.scan_history_building_types()

        self.run_btn.config(text="Reload Data", command=self.load_state_manager_data, state='normal')

    def load_state_manager_data(self):
        state = self.sm_state_name.get().strip()
        if not state: return

        # Homelands
        _, homelands = self.logic.get_state_homelands(state)
        self.current_state_homelands = homelands
        self.refresh_homelands_list()

        # Buildings
        buildings = self.logic.scan_state_buildings(state)
        self.current_state_buildings = buildings
        self.refresh_buildings_list()

        # Land Owners (for new building dropdown)
        land_owners = self.logic.scan_state_region_owners(state)
        self.cb_land_owner['values'] = land_owners
        if land_owners:
            self.cb_land_owner.current(0)

        # Update Mixer Owner Dropdown
        self.cb_mix_owner['values'] = land_owners
        if land_owners:
             self.cb_mix_owner.current(0)

        # Pops
        pops = self.logic.get_state_pops(state)
        self.current_state_pops = pops

        total = sum(p['size'] for p in pops)
        self.sm_total_pop.set(str(total))

        # Populate selector
        pop_list = []
        for i, p in enumerate(pops):
            # "size, religion, culture, region_state:TAG"
            s = f"{p['size']}, {p['religion']}, {p['culture']}, region_state:{p['region_tag']}"
            pop_list.append(s)
        self.cb_pop_select['values'] = pop_list
        if pop_list:
            self.cb_pop_select.current(0)
            self.on_state_pop_select()
        else:
            self.sm_pop_cul.set("")
            self.sm_pop_rel.set("")
            self.sm_pop_size.set("")

        # Refresh Mixer
        self.load_demographics_for_scope()

        # Load Resources
        self.load_state_resources_ui()

        self.log_message(f"Loaded data for {state}", 'success')

    def refresh_homelands_list(self):
        self.lb_homelands.delete(0, tk.END)
        for h in self.current_state_homelands:
            # Display without prefix for readability, but keep internal list intact
            display_val = h.replace("cu:", "").replace("c:", "")
            self.lb_homelands.insert(tk.END, display_val)

    def add_state_homeland(self):
        val = self.sm_homeland_add.get().strip()
        if val:
            # Check if it needs prefix (it's a culture)
            # We assume the dropdown values are cultures
            prefixed_val = f"cu:{val}" if not val.startswith("cu:") and not val.startswith("c:") else val

            if prefixed_val not in self.current_state_homelands:
                self.current_state_homelands.append(prefixed_val)
                self.refresh_homelands_list()

    def remove_state_homeland(self):
        sel = self.lb_homelands.curselection()
        if sel:
            display_val = self.lb_homelands.get(sel[0])
            # We need to find the matching entry in the internal list
            # Try reconstructing likely prefixes or search
            to_remove = None
            if display_val in self.current_state_homelands:
                to_remove = display_val
            elif f"cu:{display_val}" in self.current_state_homelands:
                to_remove = f"cu:{display_val}"
            elif f"c:{display_val}" in self.current_state_homelands:
                to_remove = f"c:{display_val}"

            if to_remove:
                self.current_state_homelands.remove(to_remove)
                self.refresh_homelands_list()

    def save_state_homelands_ui(self):
        state = self.sm_state_name.get().strip()
        if not state: return
        self.logic.save_state_homelands(state, self.current_state_homelands)
        messagebox.showinfo("Success", "Homelands saved.")

    def refresh_buildings_list(self):
        self.lb_buildings.delete(0, tk.END)
        for b in self.current_state_buildings:
            clean_type = b['type'].replace("building_", "")
            display_val = f"{clean_type} - Lvl {b['level']} ({b['owner']})"
            self.lb_buildings.insert(tk.END, display_val)

    def on_building_select(self, event=None):
        sel = self.lb_buildings.curselection()
        if sel:
            idx = sel[0]
            if idx < len(self.current_state_buildings):
                b = self.current_state_buildings[idx]
                self.sm_building_level.set(str(b['level']))
                # If we tracked region_tag in scan_state_buildings (which we added in scan_file_for_buildings), use it
                if 'region_tag' in b:
                    self.sm_land_owner.set(b['region_tag'])

    def add_state_building_ui(self):
        state = self.sm_state_name.get().strip()
        if not state: return messagebox.showerror("Error", "Load a state first.")

        land_owner = self.sm_land_owner.get().strip()
        b_type = self.sm_building_add.get().strip()

        if not land_owner: return messagebox.showerror("Error", "Select Region Land Owner.")
        if not b_type: return messagebox.showerror("Error", "Select Building Type.")

        try:
            lvl = int(self.sm_building_level.get())
        except: return messagebox.showerror("Error", "Level must be integer.")

        clean_land_owner = self.logic.format_tag_clean(land_owner)

        # Prepend building_ if missing
        if not b_type.startswith("building_"):
            b_type = f"building_{b_type}"

        # Building owner is same as land owner
        self.logic.add_state_building(state, clean_land_owner, clean_land_owner, b_type, lvl)
        self.load_state_manager_data() # Refresh

    def remove_state_building_ui(self):
        sel = self.lb_buildings.curselection()
        if not sel: return

        to_delete = []
        for idx in sel:
            if idx < len(self.current_state_buildings):
                to_delete.append(self.current_state_buildings[idx])

        # Sort by start index descending to preserve file offsets
        to_delete.sort(key=lambda b: b['indices']['start'], reverse=True)

        for b in to_delete:
            self.logic.save_state_building(b, delete=True)

        self.load_state_manager_data()

    def update_state_building_level_ui(self):
        sel = self.lb_buildings.curselection()
        if not sel: return

        idx = sel[0]
        if idx < len(self.current_state_buildings):
            b = self.current_state_buildings[idx]

            # Read all fields
            try:
                new_lvl = int(self.sm_building_level.get())
            except: return messagebox.showerror("Error", "Level must be integer.")

            new_land = self.sm_land_owner.get().strip()

            if not new_land: return messagebox.showerror("Error", "Land Owner required.")

            # Building owner is updated to match land owner (removes foreign ownership)
            self.logic.save_state_building(b, new_level=new_lvl, new_land_owner=new_land, new_building_owner=new_land)
            self.load_state_manager_data()

    def on_state_pop_select(self, event=None):
        idx = self.cb_pop_select.current()
        if idx >= 0 and idx < len(self.current_state_pops):
            p = self.current_state_pops[idx]
            self.sm_pop_cul.set(p['culture'])
            self.sm_pop_rel.set(p['religion'])
            self.sm_pop_size.set(p['size'])

    def update_state_total_pop(self):
        state = self.sm_state_name.get().strip()
        if not state or not self.current_state_pops: return

        try:
            new_total = int(self.sm_total_pop.get())
        except: return messagebox.showerror("Error", "Invalid number")

        self.logic.save_state_pops_total(state, new_total, self.current_state_pops)
        messagebox.showinfo("Success", "Total population updated.")
        self.load_state_manager_data() # Refresh to verify

    def save_single_pop_ui(self):
        idx = self.cb_pop_select.current()
        if idx < 0 or idx >= len(self.current_state_pops):
            messagebox.showerror("Error", "Please select a pop block from the list.")
            return

        p = self.current_state_pops[idx]

        new_c = self.sm_pop_cul.get().strip()
        new_r = self.sm_pop_rel.get().strip()
        try:
            new_s = int(self.sm_pop_size.get())
        except: return messagebox.showerror("Error", "Invalid size")

        if not new_c: return

        self.logic.save_single_pop(p, new_c, new_r, new_s)
        messagebox.showinfo("Success", "Pop block updated.")
        self.load_state_manager_data() # Refresh

    def convert_state_pops_religion_ui(self):
        state = self.sm_state_name.get().strip()
        rel = self.sm_pop_rel.get().strip()
        if not state or not rel: return messagebox.showerror("Error", "State and Religion required.")

        if messagebox.askyesno("Confirm", f"Convert all pops in {state} to {rel}?"):
            self.logic.convert_state_pops_religion(state, rel)
            self.load_state_manager_data()
            messagebox.showinfo("Success", "Conversion complete.")

    def convert_state_pops_culture_ui(self):
        state = self.sm_state_name.get().strip()
        cul = self.sm_pop_cul.get().strip()
        if not state or not cul: return messagebox.showerror("Error", "State and Culture required.")

        if messagebox.askyesno("Confirm", f"Convert all pops in {state} to {cul}?"):
            self.logic.convert_state_pops_culture(state, cul)
            self.load_state_manager_data()
            messagebox.showinfo("Success", "Conversion complete.")

    def toggle_conv_mode(self):
        mode = self.mc_conv_mode.get()
        if mode == "partial":
            self.f_val.pack(side=tk.LEFT, padx=(5, 0))
        else:
            self.f_val.pack_forget()

    def execute_country_conversion(self):
        tag = self.logic.format_tag_clean(self.mc_tag.get())
        if not tag: return

        cul = self.mc_conv_cul.get().strip()
        rel = self.mc_conv_rel.get().strip()
        mode = self.mc_conv_mode.get()
        val = self.mc_conv_val.get().strip()

        if not cul and not rel: return messagebox.showerror("Error", "Select Culture or Religion.")
        if mode == "partial" and not val: return messagebox.showerror("Error", "Enter Value for partial conversion.")

        if messagebox.askyesno("Confirm", f"Execute {mode} conversion for {tag}?"):
            self.logic.convert_country_identity(tag, cul, rel, mode, val)
            self.log_message(f"Converted identity for {tag}", 'success')
            messagebox.showinfo("Success", "Conversion complete.")

    def update_country_total_pop(self):
        tag = self.logic.format_tag_clean(self.mc_tag.get())
        if not tag: return

        try:
            new_tot = int(self.mc_total_pop.get())
        except: return messagebox.showerror("Error", "Invalid Total")

        self.logic.set_country_total_pop(tag, new_tot)
        self.log_message(f"Updated total population for {tag}", 'success')
        messagebox.showinfo("Success", "Country population updated.")

    # --- RESOURCE UI HANDLERS ---
    def load_state_resources_ui(self):
        state = self.sm_state_name.get().strip()
        if not state: return

        data = self.logic.scan_state_resources(state)
        self.current_state_resources = data # Store for editing

        # Populate Fields
        self.sm_arable_land.set(str(data["arable_land"]))

        # Capped
        for i in self.tv_capped.get_children(): self.tv_capped.delete(i)
        for k, v in data["capped"].items():
            self.tv_capped.insert("", tk.END, values=(k, v))

        # Arable
        self.lb_arable.delete(0, tk.END)
        for r in data["arable"]:
            self.lb_arable.insert(tk.END, r)

        # Discoverable
        for i in self.tv_disc.get_children(): self.tv_disc.delete(i)
        for d in data["discoverable"]:
            self.tv_disc.insert("", tk.END, values=(d["type"], d["amount"]))

    def add_resource_ui(self, r_type):
        if not hasattr(self, 'current_state_resources'): return

        if r_type == "capped":
            t = self.sm_res_cap_type.get().strip()
            try:
                amt = int(self.sm_res_cap_amt.get())
            except: return messagebox.showerror("Error", "Amount must be integer.")

            if t:
                # If adding manually typed one, ensure prefix?
                if not t.startswith("building_"): t = f"building_{t}"
                self.current_state_resources["capped"][t] = amt
                # Refresh UI
                for i in self.tv_capped.get_children(): self.tv_capped.delete(i)
                for k, v in self.current_state_resources["capped"].items():
                    self.tv_capped.insert("", tk.END, values=(k, v))

        elif r_type == "arable":
            t = self.sm_res_ara_type.get().strip()
            if t:
                if not t.startswith("building_"): t = f"building_{t}"
                if t not in self.current_state_resources["arable"]:
                    self.current_state_resources["arable"].append(t)
                    self.current_state_resources["arable"].sort()
                    # Refresh UI
                    self.lb_arable.delete(0, tk.END)
                    for r in self.current_state_resources["arable"]:
                        self.lb_arable.insert(tk.END, r)

        elif r_type == "discoverable":
            t = self.sm_res_disc_type.get().strip()
            try:
                amt = int(self.sm_res_disc_amt.get())
            except: return messagebox.showerror("Error", "Amount must be integer.")

            if t:
                if not t.startswith("building_"): t = f"building_{t}"
                # Update existing or add new
                found = False
                for item in self.current_state_resources["discoverable"]:
                    if item["type"] == t:
                        item["amount"] = amt
                        found = True
                        break
                if not found:
                    self.current_state_resources["discoverable"].append({"type": t, "amount": amt})

                # Refresh UI
                for i in self.tv_disc.get_children(): self.tv_disc.delete(i)
                for d in self.current_state_resources["discoverable"]:
                    self.tv_disc.insert("", tk.END, values=(d["type"], d["amount"]))

    def remove_resource_ui(self, r_type):
        if not hasattr(self, 'current_state_resources'): return

        if r_type == "capped":
            sel = self.tv_capped.selection()
            if sel:
                item = self.tv_capped.item(sel[0])
                key = item['values'][0]
                if key in self.current_state_resources["capped"]:
                    del self.current_state_resources["capped"][key]
                    self.tv_capped.delete(sel[0])

        elif r_type == "arable":
            sel = self.lb_arable.curselection()
            if sel:
                val = self.lb_arable.get(sel[0])
                if val in self.current_state_resources["arable"]:
                    self.current_state_resources["arable"].remove(val)
                    self.lb_arable.delete(sel[0])

        elif r_type == "discoverable":
            sel = self.tv_disc.selection()
            if sel:
                item = self.tv_disc.item(sel[0])
                key = item['values'][0]
                # Filter list
                self.current_state_resources["discoverable"] = [d for d in self.current_state_resources["discoverable"] if d["type"] != key]
                self.tv_disc.delete(sel[0])

    def save_state_resources_ui(self):
        state = self.sm_state_name.get().strip()
        if not state: return messagebox.showerror("Error", "Load a state first.")

        if not hasattr(self, 'current_state_resources'): return

        try:
            al = int(self.sm_arable_land.get())
            self.current_state_resources["arable_land"] = al
        except: return messagebox.showerror("Error", "Arable Land must be integer.")

        self.logic.save_state_resources(state, self.current_state_resources)
        messagebox.showinfo("Success", "Resources updated.")

# =============================================================================
#  VISUAL MAP PAINTER
# =============================================================================

    # --- DEMOGRAPHICS HANDLERS ---
    def on_sm_mix_scope_change(self, *args):
        self.load_demographics_for_scope()

    def on_sm_mix_owner_change(self, event=None):
        self.load_demographics_for_scope()

    def on_sm_mix_total_change(self, *args):
        try:
            val = int(self.sm_mix_total.get())
            self.sm_mixer.set_total_pop(val)
        except: pass

    def load_demographics_for_scope(self):
        state = self.sm_state_name.get().strip()
        if not state: return

        scope = self.sm_mix_scope.get()
        owner = None
        if scope == "owner":
            owner = self.sm_mix_owner.get().strip()
            # If no owner selected, clear
            if not owner:
                self.sm_mixer.clear()
                return

        # Get data
        data, total = self.logic.get_state_pop_aggregates(state, region_tag=owner)

        # Update Total Field
        self.sm_mix_total.set(str(total))

        # Populate Mixer
        self.sm_mixer.load_data(data, total)

    def add_demographic_group_ui(self):
        # Popup to select Culture/Religion
        win = tk.Toplevel(self)
        win.title("Add Group")
        win.configure(bg="#28231d")

        c_opts, _, _, _, _, _ = self.logic.scan_culture_definitions()
        all_culs = sorted(list(c_opts.keys()))

        _, r_opts = self.logic.scan_all_religions_and_heritages()
        _, def_rels, _, _ = self.logic.scan_definitions_for_options()
        all_rels = sorted(list(set(r_opts + def_rels)))

        ttk.Label(win, text="Culture:", background="#28231d", foreground="white").pack(pady=5)
        cb_c = ttk.Combobox(win, values=all_culs)
        cb_c.pack(padx=10)

        ttk.Label(win, text="Religion:", background="#28231d", foreground="white").pack(pady=5)
        cb_r = ttk.Combobox(win, values=all_rels)
        cb_r.pack(padx=10)

        def add():
            c = cb_c.get()
            r = cb_r.get()
            if c and r:
                self.sm_mixer.add_row(c, r, 0)
                win.destroy()

        ttk.Button(win, text="Add", command=add).pack(pady=10)

    def apply_demographics_ui(self):
        state = self.sm_state_name.get().strip()
        if not state: return

        scope = self.sm_mix_scope.get()
        owner = None
        if scope == "owner":
            owner = self.sm_mix_owner.get().strip()
            if not owner: return messagebox.showerror("Error", "Select Owner.")

        try:
            total = int(self.sm_mix_total.get())
        except: return messagebox.showerror("Error", "Invalid Total")

        data = self.sm_mixer.get_data()
        retain = self.sm_retain_loc.get()

        self.logic.save_state_demographics(state, owner, data, total, retain_location=retain)
        messagebox.showinfo("Success", "Demographics updated.")
        self.load_state_manager_data() # Refresh

    # --- MODE 11: CUSTOM STATES ---
    def show_custom_states_ui(self):
        self.clear_content()
        self.mode = "CUSTOM_STATES"
        f = ttk.LabelFrame(self.content_frame, text="Custom State Creator", padding=15)
        f.pack(fill=tk.BOTH, expand=True)

        info = """
        Use this tool to create new states or modify existing ones by stealing provinces.

        Workflows:
        1. Modifying Existing States:
           - Open Map Editor.
           - Right-click a state to set it as Target.
           - Left-click provinces to 'steal' them for the target.
           - Click 'Transfer Selected to Target'.

        2. Creating New States:
           - Open Map Editor.
           - Left-click provinces to select them.
           - Click 'Create State from Selected'.
           - Enter Name and Owner Tag.
        """
        ttk.Label(f, text=info, justify=tk.LEFT).pack(pady=10)

        if PIL_AVAILABLE:
            ttk.Button(f, text="Open Visual Map Editor", command=self.open_custom_state_painter).pack(pady=10)
        else:
            ttk.Label(f, text="Pillow (PIL) library required for map editor.", foreground="red").pack(pady=10)

        self.run_btn.pack_forget()


class Vic3ProvincePainter(tk.Toplevel):
    def __init__(self, parent, logic, start_mode="POLITICAL"):
        super().__init__(parent)
        self.title("Visual Map Painter")
        self.geometry("800x600")
        self.logic = logic
        self.parent = parent
        self.start_mode = start_mode
        self.configure(bg="#28231d")

        if not PIL_AVAILABLE:
            tk.Label(self, text="Error: Pillow (PIL) or Numpy not installed.\nCannot open map painter.", fg="red", bg="#28231d").pack(expand=True)
            return

        # Data Containers
        self.original_map_image = None # Original Full-Res PIL Image
        self.display_image = None # Tkinter Image
        self.province_to_state = {} # hex -> state_name
        self.state_province_map = {} # state_name -> [hex, hex, ...]
        self.province_owner_map = {} # hex -> owner_tag
        self.country_colors = {} # tag -> (r,g,b)
        self.province_indices = None # Numpy array of hex colors (or mapped indices)
        self.map_width = 0
        self.map_height = 0
        self.scale_factor = 0.25

        self.pending_transfers = [] # List of (state, old_tag, new_tag)

        # View Mode State
        self.view_mode = "POLITICAL" # POLITICAL, PROVINCE, CUSTOM_STATE
        self.selected_provinces = set() # Set of hex strings
        self.custom_target_state = None # For Custom State Mode

        if self.start_mode == "CUSTOM_STATE":
            self.view_mode = "PROVINCE" # Start showing provinces

        self._build_ui()
        self.after(100, self.start_loading)

    def ask_split_choice(self, owners, options=None, default_tag=None):
        """Helper to ask user how to handle multiple owners."""
        choice = [None]
        tag = [None]

        if options is None:
            options = owners

        win = tk.Toplevel(self)
        win.title("Multiple Owners Detected")
        win.geometry("400x230")
        win.transient(self)
        win.grab_set()
        win.configure(bg="#28231d")

        # Center
        x = self.winfo_rootx() + 100
        y = self.winfo_rooty() + 100
        win.geometry(f"+{x}+{y}")

        tk.Label(win, text=f"Multiple owners detected for selected provinces:\n{', '.join(owners)}",
                 wraplength=380, justify=tk.CENTER, bg="#28231d", fg="white").pack(pady=10)

        tk.Label(win, text="How do you wish to proceed?", font=("Segoe UI", 10, "bold"),
                 bg="#28231d", fg="white").pack(pady=5)

        # Split
        def on_split():
            choice[0] = "split"
            win.destroy()

        btn_bg = "#473a2b"
        btn_fg = "white"

        tk.Button(win, text="Maintain Split State\n(Each tag keeps its provinces)", command=on_split,
                  bg=btn_bg, fg=btn_fg, relief="raised", bd=1).pack(fill=tk.X, padx=20, pady=5)

        # Single
        f_single = tk.Frame(win, bg="#28231d")
        f_single.pack(fill=tk.X, padx=20, pady=5)

        tk.Button(f_single, text="Transfer All To:", command=lambda: on_single(),
                  bg=btn_bg, fg=btn_fg, relief="raised", bd=1).pack(side=tk.LEFT)

        cb_tag = ttk.Combobox(f_single, values=sorted(list(options)), width=10)
        cb_tag.pack(side=tk.LEFT, padx=5)

        if default_tag and default_tag in options:
             cb_tag.set(default_tag)
        elif options:
             cb_tag.current(0)

        def on_single():
            t = cb_tag.get().strip()
            if t:
                choice[0] = "single"
                tag[0] = t
                win.destroy()

        self.wait_window(win)
        return choice[0], tag[0]

    def _build_ui(self):
        # Toolbar
        toolbar = tk.Frame(self, bg="#352b21", height=40)
        toolbar.pack(fill=tk.X, side=tk.TOP)

        if self.start_mode.startswith("PICK_"):
            kind = self.start_mode[5:].lower()
            ttk.Label(toolbar, text=f"Click a province to open its {kind}.").pack(side=tk.LEFT,padx=8)
            ttk.Button(toolbar,text="Cancel",command=self.destroy).pack(side=tk.LEFT)
            self.bind("<Escape>",lambda event: self.destroy())
        elif self.start_mode == "COUNTRY":
            self.pick_mode = tk.StringVar(value="Capital" if not self.parent.cr_capital.get() else "States")
            for mode in ("Capital", "States"):
                ttk.Radiobutton(toolbar, text=mode, variable=self.pick_mode, value=mode).pack(side=tk.LEFT, padx=5)
            ttk.Button(toolbar, text="Country details", command=self.destroy).pack(side=tk.LEFT)
            self.country_summary = ttk.Label(self, wraplength=740)
            self.country_summary.pack(side=tk.BOTTOM, fill=tk.X)
            self.update_country_summary()
            self.geometry("1080x680")
            form = self.parent
            side = ttk.LabelFrame(self, text="Country details", padding=10)
            side.pack(side=tk.RIGHT, fill=tk.Y)
            for label, variable in (("Tag",form.cr_tag),("Name",form.cr_name),("Adjective",form.cr_adj)):
                ttk.Label(side,text=label).pack(anchor="w")
                ttk.Entry(side,textvariable=variable).pack(fill="x",pady=(0,5))
            ttk.Label(side,text="Religion").pack(anchor="w")
            ttk.Combobox(side, textvariable=form.cr_religion, values=["",*form.country_religions],state="readonly").pack(fill="x")
            ttk.Label(side,text="Add culture").pack(anchor="w")
            culture = ttk.Combobox(side, values=form.all_cultures_data)
            culture.pack(fill="x")
            chosen = ttk.Label(side,text=", ".join(form.selected_cultures),wraplength=180)
            chosen.pack(anchor="w")
            def add_selected(event):
                form.add_culture(culture.get())
                chosen.configure(text=", ".join(form.selected_cultures))
            culture.bind("<<ComboboxSelected>>", add_selected)
            culture_suggestions(culture, form.all_cultures_data, add_selected)
            def pick_country_colour():
                choice = colorchooser.askcolor(color=form._rgb_to_hex(form.cr_rgb), parent=self)
                if choice[0]:
                    form.cr_rgb = [int(v) for v in choice[0]]
                    form.color_preview.configure(bg=choice[1])
                    swatch.configure(bg=choice[1])
                    self.refresh_map()
            swatch = tk.Button(side,text="Country colour",bg=form._rgb_to_hex(form.cr_rgb),command=pick_country_colour)
            swatch.pack(fill="x",pady=6)

            ttk.Button(side,text="Review all options",command=self.destroy).pack(fill="x",pady=8)

        elif self.start_mode == "CUSTOM_STATE":
            tk.Label(toolbar, text="Target State (Right-Click):", bg="#352b21", fg="white").pack(side=tk.LEFT, padx=5)
            self.target_state_var = tk.StringVar(value="None")
            tk.Label(toolbar, textvariable=self.target_state_var, bg="#473a2b", fg="#e6bc74", width=15).pack(side=tk.LEFT, padx=5)

            tk.Button(toolbar, text="Transfer Selected to Target", command=self.modify_state_action, bg="#FFA726", fg="black").pack(side=tk.LEFT, padx=10)
            tk.Button(toolbar, text="Create New State", command=self.create_new_state_action, bg="#66BB6A", fg="black").pack(side=tk.LEFT, padx=5)
            tk.Button(toolbar, text="Clear Selection", command=self.clear_selection, bg="#473a2b", fg="white").pack(side=tk.LEFT, padx=5)

        else:
            tk.Label(toolbar, text="Paint Tag:", bg="#352b21", fg="white").pack(side=tk.LEFT, padx=5)
            self.paint_tag_var = tk.StringVar()
            tk.Entry(toolbar, textvariable=self.paint_tag_var, width=10, bg="#473a2b", fg="white", insertbackground="white").pack(side=tk.LEFT, padx=5)

            tk.Button(toolbar, text="Reload Data", command=self.reload_data, bg="#473a2b", fg="white").pack(side=tk.LEFT, padx=10)
            tk.Button(toolbar, text="Execute Pending", command=self.execute_changes, bg="#e6bc74", fg="white").pack(side=tk.LEFT, padx=10)

        # Zoom Controls
        tk.Button(toolbar, text="-", command=self.zoom_out, width=3, bg="#473a2b", fg="white").pack(side=tk.LEFT, padx=(20, 0))
        tk.Button(toolbar, text="+", command=self.zoom_in, width=3, bg="#473a2b", fg="white").pack(side=tk.LEFT, padx=(0, 10))

        # View Mode Controls
        self.btn_prov_mode = tk.Button(toolbar, text="Province Selector", command=self.toggle_view_mode, bg="#473a2b", fg="white")
        if self.start_mode == "POLITICAL":
            self.btn_prov_mode.pack(side=tk.LEFT, padx=10)

        self.btn_export = tk.Button(toolbar, text="Export Selected", command=self.export_selected_provinces, bg="#43A047", fg="white")
        if self.start_mode == "CUSTOM_STATE":
            self.btn_export.pack(side=tk.LEFT, padx=5)
        # Hidden by default otherwise

        # Status Bar
        status_bar = tk.Frame(self, bg="#352b21", height=25)
        status_bar.pack(fill=tk.X, side=tk.BOTTOM)

        self.status_var = tk.StringVar(value="Initializing...")
        tk.Label(status_bar, textvariable=self.status_var, bg="#352b21", fg="#B0BEC5").pack(side=tk.LEFT, padx=10)

        # Canvas Area
        self.canvas_frame = tk.Frame(self, bg="#28231d")
        self.canvas_frame.pack(fill=tk.BOTH, expand=True)

        self.h_scroll = tk.Scrollbar(self.canvas_frame, orient=tk.HORIZONTAL)
        self.v_scroll = tk.Scrollbar(self.canvas_frame, orient=tk.VERTICAL)

        self.canvas = tk.Canvas(self.canvas_frame, bg="#101010", highlightthickness=0,
                                xscrollcommand=lambda *v: self.scroll_changed(self.h_scroll, v), yscrollcommand=lambda *v: self.scroll_changed(self.v_scroll, v))

        self.h_scroll.config(command=self.canvas.xview)
        self.v_scroll.config(command=self.canvas.yview)

        self.h_scroll.pack(side=tk.BOTTOM, fill=tk.X)
        self.v_scroll.pack(side=tk.RIGHT, fill=tk.Y)
        self.canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

        self.canvas.bind("<Configure>", lambda e: self.queue_view())
        self.canvas.bind("<Button-1>", self.on_click)
        self.canvas.bind("<Button-3>", self.on_right_click)

        self.canvas.bind("<MouseWheel>", self.on_mousewheel)
        self.canvas.bind("<Button-4>", self.on_mousewheel)
        self.canvas.bind("<Button-5>", self.on_mousewheel)
        self.canvas.bind("<ButtonPress-2>", self.start_pan)
        self.canvas.bind("<B2-Motion>", self.do_pan)

    def start_pan(self, event):
        self.canvas.scan_mark(event.x, event.y)

    def do_pan(self, event):
        self.canvas.scan_dragto(event.x, event.y, gain=1)

    def on_mousewheel(self, event):
        num = getattr(event, 'num', None)
        delta = getattr(event, 'delta', 0)
        if num == 4 or delta > 0:
            self.zoom_in()
        elif num == 5 or delta < 0:
            self.zoom_out()

    def start_loading(self, reload_image=True):
        self.status_var.set("Loading Data...")
        threading.Thread(target=self.load_data, args=(reload_image,), daemon=True).start()

    def load_data(self, reload_image):
        try:
            # Sync backend state manager first
            self.logic.state_manager.load_state_regions()

            # Clear caches to ensure reload works
            self.country_colors = {}
            self.province_to_state = {}
            self.state_province_map = {}
            self.province_owner_map = {}
            self.pending_transfers = []

            # 1. Colors
            self.country_colors = self.logic.scan_all_country_colors()

            # 2. State Regions (Hex -> State)
            self.parse_state_regions()

            # 3. History (State+Hex -> Owner)
            self.parse_history_states()

            # 4. Map Image (Only if needed)
            if reload_image or self.province_indices is None:
                self.load_province_map()

            # 5. Render (Schedule on Main Thread)
            self.after(0, self.finish_loading_success)

        except Exception as e:
            self.after(0, lambda message=str(e): self.status_var.set(f"Error: {message}"))
            traceback.print_exc()

    def finish_loading_success(self):
        self.refresh_map()
        if self.start_mode.startswith("PICK_"):
            self.status_var.set("Middle-drag to pan. Scroll to zoom.")
            return
        self.status_var.set("Click the capital, then click additional states. Middle-drag to pan." if self.start_mode == "COUNTRY" else "Ready. Left Click to Paint, Right Click to Pick.")

    def parse_state_regions(self):
        self.province_to_state=dict(self.logic.state_manager.province_owner_map)
        self.state_province_map={key:list(obj.provinces) for key,obj in self.logic.state_manager.states.items()}

    def parse_history_states(self):
        # Scan common/history/states
        paths = []
        if self.logic.mod_path: paths.append(os.path.join(self.logic.mod_path, "common/history/states"))
        if self.logic.vanilla_path: paths.append(os.path.join(self.logic.vanilla_path, "game/common/history/states"))

        # We process vanilla first, then mod to override
        # Actually simplest is just process all, mod overwrites in dictionary
        # But for states, ownership is per-state. Mod file usually replaces vanilla file for that state completely or edits it.
        # Vic3 merges history files? No, usually replaces definitions if same ID?
        # History files add to history.
        # We will scan all. Mod entries should be processed last.

        # Optimization: Map State -> {Owner -> [Hexes]}
        # If no explicit hexes, it implies "all remaining".

        for p in reversed(paths): # Reverse so mod comes last in loop? No, paths has mod first.
             pass
        # Actually loop order: Vanilla then Mod is better for overwrite logic if using dicts.
        # paths = [mod, vanilla] -> reverse to [vanilla, mod]

        for p in reversed(paths):
            if not os.path.exists(p): continue
            for root, _, files in os.walk(p):
                for file in files:
                    if not file.endswith(".txt"): continue
                    with open(os.path.join(root, file), 'r', encoding='utf-8', errors='ignore') as f:
                        content = f.read()

                    # s:STATE = { create_state = { country = c:TAG owned_provinces = { ... } } }
                    cursor = 0
                    while True:
                        m = re.search(r"s:(STATE_[A-Za-z0-9_]+)\s*=\s*\{", content[cursor:])
                        if not m: break
                        state_name = m.group(1)
                        s_idx, e_idx = self.logic.find_block_content(content, cursor + m.end() - 1)

                        if s_idx is not None:
                            block = content[s_idx:e_idx]
                            # Find all create_state
                            cs_cursor = 0
                            claimed_hexes = set()
                            implicit_owners = [] # (tag, timestamp?)

                            while True:
                                cs = re.search(r"create_state\s*=\s*\{", block[cs_cursor:])
                                if not cs: break
                                cs_s, cs_e = self.logic.find_block_content(block, cs_cursor + cs.end() - 1)
                                if cs_s:
                                    cs_inner = block[cs_s:cs_e]
                                    c_tag_m = re.search(r"country\s*=\s*c:([A-Za-z0-9_]+)", cs_inner)
                                    if c_tag_m:
                                        tag = c_tag_m.group(1).upper()
                                        op_m = re.search(r"owned_provinces\s*=\s*\{", cs_inner)
                                        if op_m:
                                            ops, ope = self.logic.find_block_content(cs_inner, op_m.end() - 1)
                                            if ops:
                                                hexes = [h.lower() for h in cs_inner[ops+1:ope-1].replace('"', '').split()]
                                                for h in hexes:
                                                    self.province_owner_map[h] = tag
                                                    claimed_hexes.add(h)
                                        else:
                                            # Implicit ownership of remaining
                                            implicit_owners.append(tag)
                                    cs_cursor = cs_e
                                else:
                                    cs_cursor += 1

                            # Handle implicit
                            if implicit_owners and state_name in self.state_province_map:
                                all_provs = self.state_province_map[state_name]
                                # Assign remaining to last implicit owner found? Or first?
                                # Usually there's only one "main" owner if split.
                                owner = implicit_owners[-1]
                                for h in all_provs:
                                    if h not in claimed_hexes:
                                        self.province_owner_map[h] = owner

                            cursor = e_idx
                        else:
                            cursor += 1

    def load_province_map(self):
        # Load cached or from disk
        if self.original_map_image is None:
            # Try mod then vanilla
            candidates = []
            if self.logic.mod_path:
                candidates.append(os.path.join(self.logic.mod_path, "map/data/provinces.png"))
                candidates.append(os.path.join(self.logic.mod_path, "map_data/provinces.png"))
            if self.logic.vanilla_path: candidates.append(os.path.join(self.logic.vanilla_path, "game/map_data/provinces.png"))

            path = next((x for x in candidates if os.path.exists(x)), None)
            if not path:
                raise FileNotFoundError("provinces.png not found")

            self.original_map_image = Image.open(path).convert("RGB")
            self.original_map_image.load() # Ensure loaded

        self.map_width, self.map_height = self.original_map_image.size
        self.province_indices = True  # Image loaded; hit testing reads the source pixel.

    def update_country_summary(self):
        form = self.parent
        self.country_summary.configure(text=f"Donor: {form.cr_old_owner.get() or '—'}    Capital: {form.cr_capital.get() or '—'}    Additional states: {form.cr_others.get('1.0','end').strip() or '—'}")

    def pick_country_state(self, state, owner):
        if not state or not owner or owner == 'None':
            return
        form = self.parent
        form.cr_annex.set(False)
        form.cr_annex_button.grid_remove()
        form.toggle_annex_ui()
        if self.pick_mode.get() == 'Capital':
            form.cr_old_owner.set(owner)
        others = form.cr_others.get('1.0', 'end').split()
        if self.pick_mode.get() == 'Capital':
            previous = form.cr_capital.get()
            if previous and previous != state and previous not in others:
                others.append(previous)
            form.cr_capital.set(state)
            self.pick_mode.set('States')
        elif state != form.cr_capital.get():
            if state in others and form.country_state_owners.get(state) == owner:
                others.remove(state)
            else:
                if state not in others: others.append(state)
        if state == form.cr_capital.get() or state in others:
            if state != form.cr_capital.get() or owner == form.cr_old_owner.get():
                form.country_state_owners[state] = owner
        else:
            form.country_state_owners.pop(state,None)
        form.cr_others.delete('1.0', 'end')
        form.cr_others.insert('1.0', ' '.join(k for k in others if k != form.cr_capital.get()))
        self.update_country_summary()
        self.refresh_map()

    def scroll_changed(self, scrollbar, values):
        scrollbar.set(*values)
        self.queue_view()

    def queue_view(self):
        if self.original_map_image is not None and not getattr(self, '_draw_pending', False):
            self._draw_pending = True
            self.after_idle(self.draw_view)

    def zoom_in(self):
        self.zoom_by(1.25)

    def zoom_out(self):
        self.zoom_by(0.8)

    def zoom_by(self, factor):
        if not self.map_width:
            return
        w, h = self.canvas.winfo_width(), self.canvas.winfo_height()
        old = self.scale_factor
        cx = (self.canvas.canvasx(0) + w/2) / old
        cy = (self.canvas.canvasy(0) + h/2) / old
        self.scale_factor = max(0.05, min(2.0, old * factor))
        width, height = self.update_extent()
        self.canvas.xview_moveto((cx*self.scale_factor-w/2)/width)
        self.canvas.yview_moveto((cy*self.scale_factor-h/2)/height)
        self.queue_view()

    def update_extent(self):
        width = max(1, round(self.map_width*self.scale_factor))
        height = max(1, round(self.map_height*self.scale_factor))
        self.canvas.configure(scrollregion=(0,0,width,height))
        return width, height

    def refresh_map(self):
        if not self.map_width:
            return
        # Rebuild the province palette only after data or selections change.
        if not hasattr(self, '_palette'):
            self._palette = np.empty((1 << 24, 3), dtype=np.uint8)
        if self.view_mode == 'POLITICAL':
            self._palette[:] = 50
            for province, owner in self.province_owner_map.items():
                if not re.fullmatch(r"x[0-9a-fA-F]{6}", province): continue
                self._palette[int(province[1:],16)] = self.country_colors.get(owner,(150,150,150))
            if self.start_mode == 'COUNTRY':
                form = self.parent
                for state in form.cr_others.get('1.0','end').split()+[form.cr_capital.get()]:
                    for province in self.state_province_map.get(state, ()):
                        if self.province_owner_map.get(province) == form.country_state_owners.get(state, form.cr_old_owner.get()):
                            self._palette[int(province[1:],16)] = form.cr_rgb
        self.update_extent()
        self.queue_view()

    def draw_view(self):
        self._draw_pending = False
        if not self.map_width or not hasattr(self, '_palette'):
            return
        scale = self.scale_factor
        x = max(0,int(self.canvas.canvasx(0)))
        y = max(0,int(self.canvas.canvasy(0)))
        w = min(self.canvas.winfo_width()+1, int(self.map_width*scale)-x)
        h = min(self.canvas.winfo_height()+1, int(self.map_height*scale)-y)
        if min(w,h) <= 0:
            return
        box = (x/scale,y/scale,min(self.map_width,(x+w)/scale),min(self.map_height,(y+h)/scale))
        tile = self.original_map_image.resize((w,h),Image.Resampling.NEAREST,box=box)
        if self.view_mode == 'POLITICAL' or self.selected_provinces:
            arr = np.asarray(tile,dtype=np.uint32)
            keys = (arr[:,:,0]<<16) | (arr[:,:,1]<<8) | arr[:,:,2]
            if self.view_mode == 'POLITICAL':
                pixels = self._palette[keys]
                if self.start_mode == 'COUNTRY':
                    form = self.parent
                    capital = [int(h[1:],16) for h in self.state_province_map.get(form.cr_capital.get(),())
                               if self.province_owner_map.get(h) == form.cr_old_owner.get()]
                    if capital:
                        mask = np.isin(keys,capital)
                        edge = np.zeros_like(mask)
                        edge[1:] |= mask[1:] != mask[:-1]
                        edge[:,1:] |= mask[:,1:] != mask[:,:-1]
                        rows, cols = np.ogrid[y:y+h,x:x+w]
                        pixels[edge & (((rows+cols)//3)%2 == 0)] = (255,205,78)
                tile = Image.fromarray(pixels)
            else:
                pixels = np.array(tile)
                pixels[np.isin(keys,[int(p[1:],16) for p in self.selected_provinces])] = 255
                tile = Image.fromarray(pixels)
        self.display_image = ImageTk.PhotoImage(tile)
        if hasattr(self, '_tile_id'):
            self.canvas.coords(self._tile_id,x,y)
            self.canvas.itemconfigure(self._tile_id,image=self.display_image)
        else:
            self._tile_id = self.canvas.create_image(x,y,image=self.display_image,anchor="nw")

    def on_click(self, event):
        x = self.canvas.canvasx(event.x)
        y = self.canvas.canvasy(event.y)

        ix, iy = int(x/self.scale_factor), int(y/self.scale_factor)
        if ix < 0 or ix >= self.map_width or iy < 0 or iy >= self.map_height: return

        # Identify Province from packed index
        r, g, b = self.original_map_image.getpixel((ix, iy))
        hex_code = "x{:02X}{:02X}{:02X}".format(r, g, b).lower()

        state = self.province_to_state.get(hex_code)
        owner = self.province_owner_map.get(hex_code, "None")

        if self.start_mode.startswith("PICK_"):
            country = self.start_mode == "PICK_COUNTRY"
            value = owner if country else state
            if not value or value == "None" or not owner or owner == "None":
                self.status_var.set("Choose a land province with an owner.")
                return
            callback = self.on_pick
            self.destroy()
            callback(owner, state)
            return
        if self.start_mode == "COUNTRY":
            self.pick_country_state(state, owner)
            return
        if self.view_mode == "PROVINCE" or self.start_mode == "CUSTOM_STATE":
            # Toggle Selection
            if hex_code in self.selected_provinces:
                self.selected_provinces.remove(hex_code)
                self.status_var.set(f"Deselected {hex_code}")
            else:
                self.selected_provinces.add(hex_code)
                self.status_var.set(f"Selected {hex_code}")
            self.refresh_map()
        else:
            # Political Paint Mode
            new_tag = self.logic.format_tag_clean(self.paint_tag_var.get())

            if new_tag and state:
                # Queue Transfer
                # We are transferring [State] from [Owner] to [NewTag]
                self.pending_transfers.append((state, owner, new_tag))

                # Local update for visual feedback
                # Update all provinces in that state currently owned by 'owner'
                if state in self.state_province_map:
                    for h in self.state_province_map[state]:
                        if self.province_owner_map.get(h) == owner:
                            self.province_owner_map[h] = new_tag

                self.refresh_map()
                self.status_var.set(f"Painted {state} ({owner} -> {new_tag})")
            else:
                self.status_var.set(f"Province: {hex_code} | State: {state} | Owner: {owner}")

    def on_right_click(self, event):
        if self.start_mode == "COUNTRY" or self.start_mode.startswith("PICK_"): return
        x = self.canvas.canvasx(event.x)
        y = self.canvas.canvasy(event.y)
        ix, iy = int(x/self.scale_factor), int(y/self.scale_factor)
        if ix < 0 or ix >= self.map_width or iy < 0 or iy >= self.map_height: return

        r, g, b = self.original_map_image.getpixel((ix, iy))
        hex_code = "x{:02X}{:02X}{:02X}".format(r, g, b).lower()

        owner = self.province_owner_map.get(hex_code)

        if self.start_mode == "CUSTOM_STATE":
            # Select Target State
            state = self.province_to_state.get(hex_code)
            if state:
                if state == self.custom_target_state:
                    self.custom_target_state = None
                    self.target_state_var.set("None")
                    self.status_var.set("Target State Deselected")
                    self.selected_provinces.clear()
                    self.refresh_map()
                else:
                    self.custom_target_state = state
                    self.target_state_var.set(state)
                    self.status_var.set(f"Target State Set: {state}")

                    # Auto-highlight provinces of the selected state
                    if state in self.state_province_map:
                        self.selected_provinces.clear()
                        for p in self.state_province_map[state]:
                            self.selected_provinces.add(p)
                        self.refresh_map()
        else:
            if owner and owner != "None":
                self.paint_tag_var.set(owner)
                self.status_var.set(f"Picked Tag: {owner}")

    def reload_data(self):
        self.start_loading(reload_image=False)

    def is_state_owned_by(self, state, tag):
        """Checks if a tag owns any land in the given state (using local map cache)."""
        if state not in self.state_province_map: return False
        hexes = self.state_province_map[state]
        for h in hexes:
            if self.province_owner_map.get(h) == tag:
                return True
        return False

    @mod_operation
    def execute_changes(self):
        if not self.pending_transfers:
            return messagebox.showinfo("Info", "No pending changes.")

        # Optimization: Flatten transfer chains to only execute the latest instruction
        # Map: (state, original_owner) -> final_owner
        consolidated = {}

        for state, old, new in self.pending_transfers:
            if not old or old == "None": continue
            if old == new: continue

            # 1. Update existing chains ending at 'old'
            for key, target in list(consolidated.items()):
                s, orig = key
                if s == state and target == old:
                    consolidated[key] = new

            # 2. Start/Update chain for 'old'
            consolidated[(state, old)] = new

        # Filter out self-transfers and build final list
        final_moves = []
        for (state, old), new in consolidated.items():
            if old != new:
                final_moves.append((state, old, new))

        if not final_moves:
            self.pending_transfers = []
            return messagebox.showinfo("Info", "All changes cancelled out.")

        # Group by (NewTag) -> (OldTag) -> [States]
        # logic.transfer_ownership_batch(states_list, old_tag, new_tag)

        grouped = {} # new -> { old -> set(states) }

        for state, old, new in final_moves:
            if new not in grouped: grouped[new] = {}
            if old not in grouped[new]: grouped[new][old] = set()
            grouped[new][old].add(state)

        count = 0
        deferred_cleanups = {} # old_tag -> {new: tag, states: []}

        for new, old_dict in grouped.items():
            for old, states in old_dict.items():
                state_list = list(states)

                # Perform transfer and military logic using the centralized method
                # We know the old owner here (from the clicked province), so we pass it to restrict transfer
                # to just that owner's part of the state, preserving split states.
                # perform_transfer_sequence can also verify abandonment.
                # prune_refs=False because we do it once at the end
                self.logic.perform_transfer_sequence(state_list, new, known_old_owners=[old], prune_refs=False)

                # --- Detect Full Annexation (Defer Cleanup) ---
                has_any_land = False
                for h, owner in self.province_owner_map.items():
                    if owner == old:
                        has_any_land = True
                        break

                if not has_any_land:
                    if old not in deferred_cleanups:
                        deferred_cleanups[old] = {"new": new, "states": []}
                    deferred_cleanups[old]["states"].extend(state_list)
                    # Update new tag to latest (in case of partition, last one gets global assets like companies)
                    deferred_cleanups[old]["new"] = new
                else:
                    # Even if not full annexation, we should clean references for these specific states
                    self.logic.clean_transferred_state_references(state_list)

                count += 1

        # Execute Deferred Cleanups (Ensures all military moves happen before deletion)
        for old_tag, data in deferred_cleanups.items():
            self.logic.perform_annexation_cleanup(old_tag, data["new"], data["states"])

        # Validate Character Links (Prune orphaned commanders)
        valid_scopes = self.logic.collect_valid_scopes()
        self.logic.prune_orphaned_commanders(valid_scopes)

        self.pending_transfers = []
        messagebox.showinfo("Success", f"Executed {count} batch transfers.")
        self.reload_data()

    def toggle_view_mode(self):
        if self.view_mode == "POLITICAL":
            self.view_mode = "PROVINCE"
            self.btn_prov_mode.config(text="Political Mode", bg="#e6bc74")
            self.btn_export.pack(side=tk.LEFT, padx=10)
        else:
            self.view_mode = "POLITICAL"
            self.btn_prov_mode.config(text="Province Selector", bg="#473a2b")
            self.btn_export.pack_forget()
        self.refresh_map()

    def export_selected_provinces(self):
        if not self.selected_provinces:
            return messagebox.showinfo("Info", "No provinces selected.")

        sorted_provs = sorted(list(self.selected_provinces))
        content = "provinces = { " + " ".join(sorted_provs) + " }"

        win = tk.Toplevel(self)
        win.title("Exported Provinces")
        win.geometry("400x300")

        txt = tk.Text(win, wrap=tk.WORD, height=10)
        txt.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        txt.insert(tk.END, content)

        # Select all for convenience
        txt.tag_add(tk.SEL, "1.0", tk.END)
        txt.focus_set()

    def clear_selection(self):
        self.selected_provinces.clear()
        self.refresh_map()

    @mod_operation
    def modify_state_action(self):
        if not self.custom_target_state:
            messagebox.showerror("Error", "No Target State selected (Right-Click a state).")
            return

        # Ensure StateManager has the target state loaded (sync check)
        if self.custom_target_state not in self.logic.state_manager.states:
            self.logic.state_manager.load_state_regions()

        if not self.selected_provinces:
            messagebox.showerror("Error", "No provinces selected.")
            return

        # Calculate truly new provinces (excluding ones already in target state)
        new_provinces = [p for p in self.selected_provinces if self.province_to_state.get(p) != self.custom_target_state]
        count = len(new_provinces)

        if count == 0:
            messagebox.showinfo("Info", "All selected provinces are already in the target state.")
            return

        # Detect Owners involved
        moving_provinces = {} # hex -> old_owner_tag
        found_owners = set()
        for p in new_provinces:
            # We use the local painter map for tag ownership
            owner = self.province_owner_map.get(p)
            if owner and owner != "None":
                moving_provinces[p] = owner
                found_owners.add(owner)

        # Decide Strategy
        split_strategy = "single"
        target_owner = None

        # Gather all relevant tags (selected owners + target state owners)
        all_options = set(found_owners)
        target_state_owners = set()

        if self.custom_target_state in self.state_province_map:
            for p in self.state_province_map[self.custom_target_state]:
                o = self.province_owner_map.get(p)
                if o and o != "None":
                    target_state_owners.add(o)
                    all_options.add(o)

        if len(all_options) > 1:
            # Construct ordered list: Target owners first
            sorted_target = sorted(list(target_state_owners))
            sorted_found = sorted(list(found_owners))

            # Combine
            display_owners = sorted_target + [o for o in sorted_found if o not in target_state_owners]

            # Default
            default_tag = sorted_target[0] if sorted_target else None

            choice, tag = self.ask_split_choice(display_owners, sorted(list(all_options)), default_tag=default_tag)
            if not choice: return # Cancelled
            split_strategy = choice
            target_owner = tag
        else:
            # Single option available, auto-select it
            if all_options:
                target_owner = list(all_options)[0]

        if messagebox.askyesno("Confirm", f"Transfer {count} provinces to {self.custom_target_state}?"):
            affected_states = {self.custom_target_state}

            # Track history changes: old_state -> {added: [], removed: []}
            # added can now be dict or list
            history_changes = {}

            # Smart Transfer: Calculate Ratios
            source_counts = {}
            old_state_totals = {}

            # Prepare structure for target state additions
            target_additions = [] # default list
            if split_strategy == "split":
                target_additions = {} # dict for split
                for o in found_owners: target_additions[o] = []
            elif split_strategy == "single" and target_owner:
                target_additions = {target_owner: []}

            # Use a copy to iterate safely
            provinces_copy = list(self.selected_provinces)

            for p in provinces_copy:
                # Get old state from StateManager logic to ensure we dirty the right source objects
                old_state = self.logic.state_manager.province_owner_map.get(p)

                # Check if this province is actually moving
                if old_state and old_state != self.custom_target_state:
                    affected_states.add(old_state)

                    # Track Removal
                    if old_state not in history_changes:
                        history_changes[old_state] = {"added": [], "removed": []}
                        source_counts[old_state] = 0
                        # Capture totals before mod
                        if old_state in self.logic.state_manager.states:
                            old_state_totals[old_state] = len(self.logic.state_manager.states[old_state].provinces)
                        else:
                            old_state_totals[old_state] = 0

                    history_changes[old_state]["removed"].append(p)
                    source_counts[old_state] += 1

                    # Track Addition to Target
                    if self.custom_target_state not in history_changes:
                        history_changes[self.custom_target_state] = {"added": target_additions, "removed": []}

                    # Add p to appropriate added structure
                    # Reference to the structure stored in history_changes
                    current_adds = history_changes[self.custom_target_state]["added"]

                    if isinstance(current_adds, list):
                        current_adds.append(p)
                    elif isinstance(current_adds, dict):
                        # Determine which key to use
                        if split_strategy == "single":
                            key = target_owner
                        else:
                            key = moving_provinces.get(p, "unknown")
                            if key not in current_adds: current_adds[key] = []

                        current_adds[key].append(p)

                success = self.logic.state_manager.transfer_province(p, self.custom_target_state)
                if not success:
                    messagebox.showwarning("Warning", f"Operation aborted for province {p}.\nIt would be left unassigned from original state: {old_state}")
                    return

            # Smart Transfer: Calculate and Execute
            source_ratios = {}
            for os_id, count in source_counts.items():
                total = old_state_totals.get(os_id, 0)
                if total > 0:
                    source_ratios[os_id] = count / total
                else:
                    source_ratios[os_id] = 0.0

            if source_ratios:
                # If single owner transfer selected, we hint that for asset transfer too
                asset_owner = target_owner if split_strategy == "single" else None
                self.logic.state_manager.transfer_state_assets(self.custom_target_state, asset_owner, source_ratios)

            for s in affected_states:
                self.logic.state_manager.save_state_region(s)

            # Apply History Changes
            for state_id, changes in history_changes.items():
                self.logic.state_manager.update_history_provinces(state_id, changes["added"], changes["removed"])

            # Check for orphaned region_states in split states
            for old_state_id in affected_states:
                if old_state_id == self.custom_target_state: continue

                # Identify tags that lost land in this state
                lost_tags = set()
                if old_state_id in history_changes:
                    for p in history_changes[old_state_id]["removed"]:
                        owner = moving_provinces.get(p)
                        if owner: lost_tags.add(owner)

                # Check if they remain in the state
                if old_state_id in self.logic.state_manager.states:
                    remaining_provinces = self.logic.state_manager.states[old_state_id].provinces
                    remaining_owners = set()
                    for p in remaining_provinces:
                        # Use current map owner (cache)
                        # Note: cache is stale for moved provinces, but valid for non-moved ones
                        o = self.province_owner_map.get(p)
                        if o: remaining_owners.add(o)

                    for tag in lost_tags:
                        if tag not in remaining_owners:
                            self.logic.state_manager.move_orphaned_region_state(old_state_id, tag, self.custom_target_state)

            self.selected_provinces.clear()
            self.reload_data()
            messagebox.showinfo("Success", "Transferred provinces.")

    @mod_operation
    def create_new_state_action(self):
        if not self.selected_provinces:
            messagebox.showerror("Error", "No provinces selected.")
            return

        # Detect Owners involved
        moving_provinces = {} # hex -> old_owner_tag
        found_owners = set()
        for p in self.selected_provinces:
            owner = self.province_owner_map.get(p)
            if owner and owner != "None":
                moving_provinces[p] = owner
                found_owners.add(owner)

        split_strategy = "single"
        target_owner = None

        if len(found_owners) > 1:
            choice, tag = self.ask_split_choice(list(found_owners))
            if not choice: return
            split_strategy = choice
            target_owner = tag

        name = simpledialog.askstring("Create State", "Enter State Name (e.g. Texas):")
        if not name: return

        if split_strategy == "single":
            if target_owner:
                owner = target_owner
            else:
                owner = simpledialog.askstring("Create State", "Enter Owner Tag (e.g. USA):")
                if not owner: return

            clean_owner = self.logic.format_tag_clean(owner)
            self.logic.state_manager.create_new_state(name, clean_owner, list(self.selected_provinces))

        else: # split
            # Build dict {tag: [provs]}
            owner_data = {}
            for tag in found_owners:
                owner_data[tag] = []

            # Handle unowned provinces (implicitly assigned to majority or need prompt? Assume 'unknown' or skipped?)
            # Or just assign them to the owner of the majority?
            # We iterate selected provinces
            for p in self.selected_provinces:
                curr = moving_provinces.get(p)
                if curr:
                    owner_data[curr].append(p)
                else:
                     # Unowned? Assign to first or ignore?
                     # Let's assign to first found owner to avoid data loss
                     if found_owners:
                         first = list(found_owners)[0]
                         owner_data[first].append(p)

            self.logic.state_manager.create_new_state(name, owner_data, list(self.selected_provinces))

        self.selected_provinces.clear()
        self.reload_data()
        messagebox.showinfo("Success", f"Created state {name}.")

def main():
    import argparse
    parser = argparse.ArgumentParser(description='Victoria 3 Modding Studio')
    parser.add_argument('--version',action='version',version=APP_VERSION)
    parser.add_argument('--validate',metavar='MOD',help='Validate a mod and print JSON instead of opening the GUI')
    parser.add_argument('--game',metavar='INSTALL',help='Victoria 3 installation or game folder for validation')
    args=parser.parse_args()
    if args.validate:
        logic=Vic3Logic(lambda *args:None)
        if args.game:logic.set_vanilla_path(args.game)
        logic.set_mod_path(args.validate)
        issues=logic.validate_mod()
        print(json.dumps(issues,indent=2,ensure_ascii=False))
        return int(any(issue['level']=='error' for issue in issues))
    app=App()
    app.mainloop()
    return 0

if __name__ == '__main__':
    raise SystemExit(main())
