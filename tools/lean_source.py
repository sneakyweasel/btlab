"""Source identities and complete headers for regular, named Lean declarations.

This is a lexical catalogue, not elaboration. Private identities are source IDs;
generated declarations and resolved types belong to the separate Lean export.
"""
from __future__ import annotations

import re

import trust_boundary as tb

SEGMENT = rf'(?:{tb._ID_SEGMENT}|«[^»\n]+»)'
NAME = rf'{SEGMENT}(?:\.{SEGMENT})*'
MODIFIER = r'(?:(?:private|protected|noncomputable|unsafe|partial|public|nonrec)\s+)*'
HEAD = re.compile(
    rf'^(?:@\[[^\]]*\]\s*)*(?P<modifiers>{MODIFIER})'
    rf'(?P<kind>theorem|lemma|def|abbrev|instance|structure|class|inductive|opaque|axiom)\s+'
    rf'(?P<name>{NAME})(?=$|[\s:({{\[]|\.\{{)')
SCOPE = re.compile(
    rf'^(?P<mods>(?:(?:noncomputable|public|private)\s+)*)'
    rf'(?P<kind>namespace|section|end)(?:\s+(?P<name>{NAME}))?\s*$')
TOP = re.compile(r'^(?:#|namespace\b|section\b|end\b|open\b|variable\b|include\b|'
                 r'omit\b|attribute\b|export\b|example\b|set_option\b|notation\b)')


def name_parts(name: str) -> list[str]:
    return re.findall(SEGMENT, name)


def context_lines(text: str, masked_lines: list[str] | None = None) -> list[tuple[int, str, str, bool, int]]:
    namespace, private = '', False
    stack = []
    pending, first = '', 0
    result = []
    for number, raw in enumerate(masked_lines if masked_lines is not None else tb.source_commands(text), 1):
        command = raw.strip()
        if not command:
            continue
        if tb.MODIFIERS_ONLY.fullmatch(command) or tb.ATTRIBUTES_ONLY.fullmatch(command):
            first = first or number
            pending += command + ' '
            continue
        command = pending + command
        start = first or number
        pending, first = '', 0
        scope = SCOPE.fullmatch(command)
        if scope:
            kind, name, mods = scope['kind'], scope['name'], scope['mods'].split()
            if kind == 'end':
                if stack:
                    namespace, private = stack.pop()
            else:
                stack.append((namespace, private))
                if 'private' in mods:
                    private = True
                elif 'public' in mods:
                    private = False
                if kind == 'namespace' and name:
                    namespace = (name.removeprefix('_root_.') if name.startswith('_root_.')
                                 else '.'.join(filter(None, (namespace, name))))
            continue
        if re.match(r'^(?:(?:noncomputable|public|private)\s+)*(namespace|section|end)\b', command):
            raise ValueError(f'Unsupported scope at line {number}: {command}')
        result.append((number, command, namespace, private, start))
    return result


def header(text: str, masked: str) -> tuple[str, bool]:
    """Stop at a top-level implementation delimiter, not a binder's default value."""
    depth = 0
    for i, char in enumerate(masked):
        if char in '([{⦃':
            depth += 1
        elif char in ')]}⦄':
            depth = max(0, depth - 1)
        elif depth == 0:
            if masked.startswith(':=', i) or masked.startswith('where', i) and (
                    i == 0 or masked[i - 1].isspace()) and (
                    i + 5 == len(masked) or masked[i + 5].isspace()):
                return text[:i].rstrip(), True
            if char == '|' and not masked.startswith(('||', '|>'), i) and (
                    i == 0 or masked[i - 1].isspace()):
                return text[:i].rstrip(), True
    return text.rstrip(), True


def result_type(signature: str) -> str | None:
    """Read only an explicit top-level type annotation; never infer a type."""
    masked = '\n'.join(tb.source_commands(signature))
    depth = 0
    for i, char in enumerate(masked):
        if char in '([{⦃':
            depth += 1
        elif char in ')]}⦄':
            depth = max(0, depth - 1)
        elif char == ':' and depth == 0 and not masked.startswith(':=', i):
            return signature[i + 1:].strip()
    return None


def doc_before(lines: list[str], start: int) -> str:
    prefix = ''.join(lines[:start - 1]).rstrip()
    if not prefix.endswith('-/'):
        return ''
    # Balance backwards so a nested comment does not terminate the docstring.
    depth, pos = 1, len(prefix) - 2
    while pos > 0:
        pos -= 1
        if prefix[max(0, pos - 1):pos + 1] == '-/':
            depth += 1
            pos -= 1
        elif prefix[max(0, pos - 1):pos + 1] == '/-':
            depth -= 1
            if depth == 0:
                opening = pos - 1
                return (' '.join(prefix[opening + 3:-2].split())
                        if prefix.startswith('/--', opening) else '')
            pos -= 1
    return ''


def scan(text: str, module: str, file: str) -> list[dict]:
    lines = text.splitlines(keepends=True)
    masked_lines = tb.source_commands(text)
    contexts = context_lines(text, masked_lines)
    heads = [(number, command, namespace, private, start, match)
             for number, command, namespace, private, start in contexts
             if (match := HEAD.match(command))]
    boundaries = sorted({start for _, command, _, _, start in contexts
                         if HEAD.match(command) or TOP.match(command)} | {len(lines) + 1})
    rows = []
    for number, command, namespace, private, start, match in heads:
        stop = next(n for n in boundaries if n > number)
        source = ''.join(lines[start - 1:stop - 1])
        masked = '\n'.join(masked_lines[start - 1:stop - 1])
        sig, complete = header(source, masked)
        modifiers = match['modifiers'].split()
        private = 'private' in modifiers or (private and 'public' not in modifiers)
        name = match['name']
        full = (name.removeprefix('_root_.') if name.startswith('_root_.')
                else '.'.join(filter(None, (namespace, name))))
        body_tokens = set(tb.identifier_tokens(masked))
        trust = ('open' if match['kind'] == 'axiom' or body_tokens & {'sorry', 'admit'} else
                 'compiler' if 'native_decide' in body_tokens else 'kernel')
        attrs = re.findall(r'@\[([^\]]+)\]', source[:max(len(sig), len(command))])
        rows.append({
            'id': f'{module}::private::{full}@{number}' if private else full,
            'qualified_name': None if private else full,
            'source_name': full, 'name': name, 'namespace': namespace,
            'visibility': 'private' if private else 'public',
            'kind': match['kind'], 'module': module, 'file': file, 'line': number,
            'end_line': stop - 1, 'doc': doc_before(lines, start),
            'signature': sig, 'signature_complete': complete, 'signature_kind': 'source',
            'attributes': attrs, 'deprecated': any('deprecated' in a for a in attrs),
            'trust': trust, 'trust_basis': 'source markers only; not an axiom/dependency audit',
        })
    return rows
