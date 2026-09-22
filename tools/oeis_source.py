"""Lossless OEIS field parsing and exact decimal-term normalization."""
from __future__ import annotations

from collections import defaultdict
import hashlib
import re

AID = re.compile(r'(?<![A-Za-z0-9])A[0-9]{6}(?![0-9])')
FIELD = re.compile(r'^%([A-Za-z]) (A[0-9]{6})(?: (.*))?$')
FIELDS = {
    'I': 'metadata', 'S': 'terms', 'T': 'terms', 'U': 'terms', 'N': 'name',
    'C': 'comments', 'D': 'references', 'H': 'links', 'F': 'formulas',
    'e': 'examples', 'p': 'programs', 't': 'programs', 'o': 'programs',
    'Y': 'crossrefs', 'K': 'keywords', 'O': 'offset', 'A': 'author',
    'E': 'extensions', 'W': 'links',
}
SEARCH_FIELDS = ('name', 'comments', 'formulas', 'references', 'links', 'examples',
                 'programs', 'crossrefs', 'other')


def aid(value: str) -> str:
    value = value.strip().upper()
    if not re.fullmatch(r'A[0-9]{6}', value):
        raise ValueError('Use an OEIS identifier such as A094683 (A followed by six digits)')
    return value


def integer(value: str) -> str:
    """Canonical decimal strings avoid machine integer limits and floating-point loss."""
    if not isinstance(value, str) or not re.fullmatch(r'[+-]?[0-9]+', value.strip()):
        raise ValueError('Terms must be decimal integer strings, with no floats or exponents')
    value = value.strip()
    digits = value.lstrip('+-').lstrip('0') or '0'
    return ('-' if value.startswith('-') and digits != '0' else '') + digits


def term_key(value: str) -> str:
    # FTS tokenization would otherwise discard minus signs. Candidate matches are
    # always verified against the original decimal strings, including collisions.
    return 't' + hashlib.blake2b(value.encode('ascii'), digest_size=12).hexdigest()


def parse_record(identifier: str, text: str) -> dict:
    identifier = aid(identifier)
    rows, issues = [], []
    for number, line in enumerate(text.splitlines(), 1):
        match = FIELD.fullmatch(line)
        if match:
            code, reference, value = match.groups()
            if reference != identifier:
                issues.append(f'Line {number} names {reference}, not {identifier}')
            rows.append({'code': code, 'field': FIELDS.get(code, 'other'),
                         'line': number, 'text': value or ''})
        elif line.strip():
            rows.append({'code': None, 'field': 'other', 'line': number, 'text': line})
            issues.append(f'Unrecognized field syntax at line {number}')
    groups = defaultdict(list)
    for row in rows:
        groups[row['field']].append(row['text'])
    terms = []
    term_error = False
    for value in ','.join(groups['terms']).split(','):
        if value.strip():
            try:
                terms.append(integer(value))
            except ValueError:
                term_error = True
                issues.append(f'Non-integer term token: {value[:80]}')
    # Never join the terms either side of a missing token into a spurious run.
    if term_error:
        terms = []
    raw_offset = ' '.join(groups['offset'])
    try:
        first_index = int(raw_offset.split(',')[0]) if raw_offset else None
    except ValueError:
        first_index = None
        issues.append('Unrecognized offset')
    references = sorted({(m.group(), row['field']) for row in rows
                         if row['field'] not in {'metadata', 'terms', 'offset'}
                         for m in AID.finditer(row['text']) if m.group() != identifier})
    searchable = {field: '\n'.join(groups[field]) for field in SEARCH_FIELDS}
    searchable['other'] = '\n'.join(text for field, texts in groups.items()
                                   if field not in SEARCH_FIELDS and field != 'terms'
                                   for text in texts) + '\n' + searchable['other']
    return {'aid': identifier, 'name': ' '.join(groups['name']), 'fields': rows,
            'terms': terms, 'first_index': first_index, 'offset_raw': raw_offset,
            'keywords': ','.join(groups['keywords']), 'revision': ' '.join(groups['metadata']),
            'issues': issues, 'references': references, 'searchable': searchable,
            'sha256': hashlib.sha256(text.encode('utf-8')).hexdigest()}
