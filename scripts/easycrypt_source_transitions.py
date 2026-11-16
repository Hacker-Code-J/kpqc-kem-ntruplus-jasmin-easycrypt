#!/usr/bin/env python3
"""Authenticate the explicitly reviewed EasyCrypt 2026.10 proof-body ports.

This preserves a historical import's declaration provenance. It does not turn
that historical record into a fresh replay under a different checker.
"""
import hashlib
import json
from pathlib import Path
import re


MANIFEST = Path('tests/ntruplus768/easycrypt-2026.10-proof-transitions.json')
BEFORE = Path('evidence/easycrypt-2026.10-20261116/before')
MANIFEST_SHA256 = '0953b70a46431627c416455d6b413b3f3a3824cac3bb9da475c806b78c963e73'


def sha(data):
    return hashlib.sha256(data).hexdigest()


def declarations(text):
    depth, parts = 0, []
    for token in re.split(r'(\(\*|\*\))', text):
        if token == '(*':
            depth += 1
            parts.append(' ')
        elif token == '*)':
            if depth == 0:
                raise ValueError('unmatched EasyCrypt comment')
            depth -= 1
        elif depth == 0:
            parts.append(token)
    if depth:
        raise ValueError('unclosed EasyCrypt comment')
    code = ''.join(parts)
    if re.search(r'\b(admit|admitted|abort|assume|axiom|sorry|pragma)\b', code):
        raise ValueError('proof transition contains an escape or assumption')
    code = re.sub(r'\bproof\.(.*?)\bqed\.', 'proof. qed.', code, flags=re.S)
    return re.sub(r'\s+', '', code)


def metadata_paths(root):
    root = Path(root).resolve()
    data = (root / MANIFEST).read_bytes()
    if sha(data) != MANIFEST_SHA256:
        raise ValueError('reviewed proof-transition manifest changed')
    manifest = json.loads(data)
    paths = {root / MANIFEST, root / 'scripts/easycrypt_source_transitions.py'}
    paths.update(root / BEFORE / name for name in manifest['files'])
    return paths


def reviewed_import(root, relative, historical_hash, current_hash):
    """Return a transition record only for an exact authenticated proof pair."""
    root = Path(root).resolve()
    relative = Path(relative)
    if relative.is_absolute() or '..' in relative.parts:
        raise ValueError('invalid proof transition path')
    metadata_paths(root)
    manifest = json.loads((root / MANIFEST).read_text())
    record = manifest['files'].get(relative.as_posix())
    if record is None:
        raise ValueError('unreviewed imported-source transition: ' + str(relative))
    if (historical_hash, current_hash) != (record['before_sha256'], record['after_sha256']):
        raise ValueError('imported-source transition hash mismatch: ' + str(relative))
    before_path, after_path = root / BEFORE / relative, root / relative
    if (before_path.is_symlink() or after_path.is_symlink()
            or not before_path.resolve().is_relative_to(root)
            or not after_path.resolve().is_relative_to(root)):
        raise ValueError('symlink proof transition input')
    before, after = before_path.read_bytes(), after_path.read_bytes()
    if sha(before) != historical_hash or sha(after) != current_hash:
        raise ValueError('proof transition input bytes changed: ' + str(relative))
    old_declarations, new_declarations = declarations(before.decode()), declarations(after.decode())
    if old_declarations != new_declarations:
        raise ValueError('proof transition changes declarations: ' + str(relative))
    if sha(new_declarations.encode()) != record['declarations_sha256']:
        raise ValueError('proof transition declaration fingerprint mismatch')
    return {'source': relative.as_posix(), 'historical_sha256': historical_hash,
            'current_sha256': current_hash, 'declarations_sha256': record['declarations_sha256'],
            'scope': 'reviewed proof-body port; historical declaration provenance, not a fresh imported-proof replay'}
