"""Change-aware verification plans and explicit CLI execution of trusted local gates."""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import time
import uuid
import xml.etree.ElementTree as ET

from lab_environment import ROOT, doctor, environment, executable
from lab_impact import analyze, fingerprint, impact, inventory, git
from lab_selection import PROFILES, select_tests

LIMITATIONS = ('Checks apply to the selected checkout and recorded inputs. Focused verification '
               'is iteration feedback, not a replacement for default full verification; static '
               'and recorded test links cannot establish complete dynamic/file coverage. '
               'Slow experiments, arbitrary theorem axiom '
               'audits, paper rebuilding and external publication are not performed. '
               'No evidence labels are promoted.')


def plan(root: Path = ROOT, *, since: str = 'HEAD', paths: list[str] | None = None,
         profile: str = 'full') -> dict:
    if profile not in PROFILES:
        raise ValueError('Verification profile must be full or focused')
    root = root.resolve()
    change = analyze(root, since=since, paths=paths, test_attribution=profile == 'focused')
    changed = change['changed_files']
    selection = select_tests(root, change, profile)
    checks = []

    def add(identifier, argv, reason, *, cwd='.', needs=None, no_skips=False):
        checks.append({'id': identifier, 'argv': argv, 'cwd': cwd, 'reason': reason,
                       'needs': needs or [], 'require_no_skips': no_skips, 'status': 'not_checked'})

    if changed:
        add('research_structure', ['python', 'tools/lab.py', 'check', '--hashes'],
            'Validate canonical research references and hashes of registered output manifests.')
        add('branch_index', ['python', 'tools/lab.py', 'run', 'research.juggler_sequence.branch_index', '--check'],
            'Reject stale Juggler registration.')
        add('claim_ledger', ['python', 'tools/render_theorem_ledger.py', '--check'],
            'Reject a stale rendered claim ledger.')
        add('preprints', ['python', 'tools/preprints.py', '--check'],
            'Check all five releases and kits, including dependencies not captured by imports.')

        add('python_tests', ['python', '-m', 'pytest', '-m', 'not slow', *selection['paths']],
            selection['basis'], no_skips=selection['mode'] == 'affected',
            needs=['lake', 'lean_packages'] if selection['mode'] == 'full'
            and (root / 'formal/lake-manifest.json').is_file() else [])
        python_files = [p for p in changed if p.endswith('.py') and (root / p).is_file()]
        if python_files or any(Path(p).name in {'pyproject.toml', 'ruff.toml', '.ruff.toml'} for p in changed):
            # Whole-tree lint avoids OS argument limits for a large mechanical refactor.
            add('python_lint', ['python', '-m', 'ruff', 'check', '.'], 'Repository Python runtime/style gate.')
        lean_changed = any(p.startswith('formal/') or p == 'tools/lab_scope.py' for p in changed)
        if lean_changed:
            add('lean_style', ['python', 'tools/lean_style.py'], 'Naming/docs baseline must not expand.')
            if any(Path(p).name in {'lakefile.toml', 'lakefile.lean', 'lean-toolchain', 'lake-manifest.json'}
                   or p == 'tools/lab_scope.py' for p in changed):
                add('lean_build', ['python', 'tools/lab.py', 'build'],
                    'Toolchain or build graph changed: build the complete active graph.', needs=['lake', 'lean_packages'])
            else:
                modules = [m for m in change['lean_targets'] if '.' in m or m in
                           {'Core', 'Representation', 'Operators', 'BTCalculus', 'Problems'}]
                if modules:
                    add('lean_build', ['python', 'tools/lab.py', 'build',
                                       *(arg for m in modules for arg in ('--module', m))],
                        'Compile changed modules and transitive local import consumers; '
                        'refresh their semantic records only after successful compilation.',
                        needs=['lake', 'lean_packages'])
                for target in change['lean_targets']:
                    if target not in modules:
                        add('lean_file_' + target, ['lake', 'env', 'lean', target + '.lean'],
                            'Elaborate affected standalone audit/consumer source.',
                            cwd='formal', needs=['lake', 'lean_packages'])
            add('lean_contracts', ['python', '-m', 'pytest', '-m', 'not slow',
                                  'tests/research/juggler_sequence/test_lean_interface_contracts.py'],
                'Compile public Juggler consumers and validate their exact allowed axiom sets.',
                needs=['lake', 'lean_packages'], no_skips=True)
    return {'status': 'planned' if checks else 'no_changes', 'snapshot': change['snapshot'],
            'profile': profile, 'purpose': 'iteration' if profile == 'focused' else 'acceptance',
            'test_selection': selection,
            'checkout_head': git(root, 'rev-parse', 'HEAD').decode().strip(),
            'extra_watch_paths': change['extra_watch_paths'],
            'base_commit': change['base_commit'], 'comparison': change['comparison'],
            'changed_file_count': len(changed), 'affected_test_count': len(change['affected_tests']),
            'affected_papers': change['affected_papers'], 'checks': checks,
            'uncertainties': change['uncertainties'], 'limitations': LIMITATIONS}


def plan_page(root: Path = ROOT, *, since='HEAD', paths=None, profile='full', limit=20, offset=0, snapshot=None) -> dict:
    """Bounded read-only MCP plan, including bounded previews of long command lines."""
    from research_catalog import page
    page([], limit, offset)
    result = plan(root, since=since, paths=paths, profile=profile)
    # Pagination belongs to one query, including its profile and explicit scope.
    result['snapshot'] = hashlib.sha256(json.dumps({
        'source': result['snapshot'], 'base': result['base_commit'], 'profile': profile,
        'paths': sorted(paths) if paths is not None else None}, sort_keys=True).encode()).hexdigest()[:24]
    if snapshot is not None and snapshot != result['snapshot']:
        raise ValueError('Verification snapshot changed; restart pagination')
    checks = result.pop('checks')
    result['extra_watch_path_count'] = len(result.pop('extra_watch_paths'))
    for check in checks:
        check['argument_count'] = len(check['argv'])
        check['argv_truncated'] = len(check['argv']) > 24
        check['argv'] = check['argv'][:24]
    uncertainties = result.pop('uncertainties')
    result['uncertainty_count'] = len(uncertainties)
    result['uncertainties'] = uncertainties[:5]
    selection = result['test_selection']
    for name in ('paths', 'fallback_reasons'):
        values = selection[name]
        selection[name + '_count'] = len(values)
        selection[name + '_truncated'] = len(values) > 10
        selection[name] = values[:10]
    return result | page(checks, limit, offset)


def prerequisites(check: dict, root: Path) -> list[str]:
    missing = []
    for name in check['needs']:
        if name == 'lean_packages':
            lock = root / 'formal/lake-manifest.json'
            if not lock.is_file():
                missing.append('Lean package lock is missing; install prerequisites explicitly.')
            else:
                from lab_dependencies import package_state
                try:
                    absent = [p['name'] + ':' + p['status'] for p in package_state(root, probe=True) if p['status'] != 'ready']
                    if absent:
                        missing.append('Lean dependencies not ready: ' + ', '.join(absent) + '; run lab.py prepare --apply.')
                except (ValueError, OSError, subprocess.SubprocessError) as exc:
                    missing.append(str(exc))
        elif not executable(name, root):
            missing.append(f'{name}: pinned local executable is unavailable.')
    return missing


def junit_summary(path: Path) -> dict:
    suites = ET.parse(path).getroot()
    cases = list(suites.iter('testcase'))
    skipped = [c for c in cases if c.find('skipped') is not None]
    return {'collected': len(cases), 'skipped': len(skipped),
            'failures': len(list(suites.iter('failure'))), 'errors': len(list(suites.iter('error'))),
            'skip_examples': [{'test': c.get('classname', '') + '.' + c.get('name', ''),
                               'reason': c.find('skipped').get('message', '')[:300]} for c in skipped[:10]]}


def content_state(root: Path, files: set[str]) -> dict:
    """Hash verification inputs so identical report rewrites do not invalidate a run."""
    result = {}
    for name in sorted(files):
        path = root / name
        if path.is_file():
            with path.open('rb') as stream:
                result[name] = hashlib.file_digest(stream, 'sha256').hexdigest()
        else:
            result[name] = None
    return result


def execute(report: dict, root: Path = ROOT, *, timeout: float = 1200, workers: int = 0) -> dict:
    """Only execute plans generated in this process, never a plan loaded from a file/MCP."""
    root = root.resolve()
    from lab_prepare import runtime_python, python_inventory, managed_python, readiness
    python = runtime_python(root)
    if Path(python).absolute() == managed_python(root).absolute():
        prepared = readiness(root, probe=True, lean=False)
        if prepared['status'] != 'ready':
            return report | {'status': 'incomplete', 'reason': 'Managed Python drifted; run lab.py prepare --apply.',
                             'preparation': prepared}
    runtime_before = python_inventory(Path(python))
    head_before = git(root, 'rev-parse', 'HEAD').decode().strip()
    if report.get('checkout_head', head_before) != head_before:
        return report | {'status': 'stale', 'reason': 'Checkout HEAD changed after planning.'}
    watched = set(report.get('extra_watch_paths', []))
    if fingerprint(root, inventory(root) | watched) != report['snapshot']:
        return report | {'status': 'stale', 'reason': 'Checkout changed before execution; regenerate the plan.'}
    if not report['checks']:
        return report
    initial = content_state(root, inventory(root) | watched)
    if fingerprint(root, inventory(root) | watched) != report['snapshot']:
        return report | {'status': 'stale', 'reason': 'Checkout changed while capturing verification inputs.'}
    run = root / '.build/lab' / (datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%SZ') + '-' + uuid.uuid4().hex[:8])
    run.mkdir(parents=True)
    env = environment(root)
    # Do not inherit command provenance from an enclosing experiment.
    env.pop('BTLAB_RUN_COMMAND', None)
    for check in report['checks']:
        missing = prerequisites(check, root)
        if missing:
            check.update(status='not_checked', reason=' '.join(missing))
            continue
        argv = list(check['argv'])
        argv[0] = python if argv[0] == 'python' else executable(argv[0], root) or argv[0]
        junit = None
        if argv[1:3] == ['-m', 'pytest']:
            junit = run / (check['id'] + '.xml')
            argv += ['--junitxml', str(junit), '--basetemp', str(run / (check['id'] + '-tmp')),
                     '-o', 'cache_dir=' + str(run / (check['id'] + '-cache'))]
            if workers:
                argv += ['-n', str(workers), '--dist', 'loadfile']
        log = run / (check['id'] + '.log')
        check['log'] = log.relative_to(root).as_posix()
        print('Checking ' + check['id'] + ' ...', file=sys.stderr, flush=True)
        started = time.monotonic()
        try:
            with log.open('wb') as output:
                result = subprocess.run(argv, cwd=root / check['cwd'], env=env, stdin=subprocess.DEVNULL,
                                        stdout=output, stderr=subprocess.STDOUT, timeout=timeout)
            check.update(status='passed' if result.returncode == 0 else 'failed', exit_code=result.returncode)
        except subprocess.TimeoutExpired:
            check.update(status='failed', reason=f'Timed out after {timeout:g} seconds.')
        except OSError as exc:
            check.update(status='not_checked', reason=str(exc))
        check['seconds'] = round(time.monotonic() - started, 2)
        if junit is not None and junit.is_file():
            try:
                check['tests'] = junit_summary(junit)
                if check['require_no_skips'] and check['tests']['skipped'] and check['status'] == 'passed':
                    check.update(status='not_checked', reason='Required selected tests were skipped.')
            except ET.ParseError:
                check.update(status='failed', reason='Incomplete or malformed pytest result report.')
        elif junit is not None and check['status'] == 'passed':
            check.update(status='not_checked', reason='No pytest result report was produced.')
        if check['status'] != 'passed' and log.is_file():
            with log.open('rb') as stream:
                stream.seek(max(0, log.stat().st_size - 3000))
                check['output_tail'] = stream.read().decode('utf-8', 'replace')
    report['status'] = ('failed' if any(c['status'] == 'failed' for c in report['checks']) else
                        'incomplete' if any(c['status'] != 'passed' for c in report['checks']) else 'passed')
    final = content_state(root, inventory(root) | watched)
    changed = sorted(p for p in initial.keys() | final.keys()
                     if p not in initial or p not in final or initial[p] != final[p])
    report['head_changed'] = head_before != git(root, 'rev-parse', 'HEAD').decode().strip()
    report['runtime_changed'] = runtime_before != python_inventory(Path(python))
    report['runtime'] = {'interpreter': python, 'version': runtime_before['version'],
                         'package_inventory_sha256': hashlib.sha256(json.dumps(runtime_before, sort_keys=True).encode()).hexdigest()}
    report['checkout_changed'] = bool(changed) or report['head_changed'] or report['runtime_changed']
    report['changed_during_checks_count'] = len(changed)
    report['changed_during_checks'] = changed[:30]
    report['changed_during_checks_truncated'] = len(changed) > 30
    if report['checkout_changed']:
        report['status'] = 'stale'
    report['report'] = (run / 'report.json').relative_to(root).as_posix()
    report['input_check'] = 'SHA-256 before and after execution; identical rewrites are allowed. Not an atomic execution certificate.'
    (root / report['report']).write_text(json.dumps(report, indent=2), encoding='utf-8')
    return report


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest='command', required=True)
    doc = commands.add_parser('doctor', help='inspect local prerequisites without installation')
    doc.add_argument('--probe', action='store_true', help='also try bounded executable --version calls')
    imp = commands.add_parser('impact', help='bounded static/recorded impact of selected changes')
    imp.add_argument('--limit', type=int, default=20)
    imp.add_argument('--offset', type=int, default=0)
    imp.add_argument('--snapshot')
    verify = commands.add_parser('verify', help='run trusted verification gates for selected changes')
    verify.add_argument('--changed', action='store_true', required=True)
    verify.add_argument('--plan', action='store_true', help='show a plan without executing checks')
    verify.add_argument('--timeout', type=float, default=1200, help='seconds per check')
    verify.add_argument('--workers', type=int, default=0, help='explicit pytest-xdist worker count')
    verify.add_argument('--profile', choices=PROFILES, default='full',
                        help='full acceptance gates (default), or focused iteration with conservative fallbacks')
    for sub in (imp, verify):
        sub.add_argument('--since', default='HEAD', help='base commit; compared to the working tree')
        sub.add_argument('--path', action='append', dest='paths', help='explicit file/directory scope; repeatable')
    args = parser.parse_args(argv)
    try:
        if args.command == 'doctor':
            result = doctor(probe=args.probe)
        elif args.command == 'impact':
            result = impact(since=args.since, paths=args.paths, limit=args.limit,
                            offset=args.offset, snapshot=args.snapshot)
        else:
            if args.timeout <= 0 or args.workers < 0:
                parser.error('timeout must be positive and workers nonnegative')
            result = plan(since=args.since, paths=args.paths, profile=args.profile)
            if not args.plan:
                result = execute(result, timeout=args.timeout, workers=args.workers)
    except (ValueError, OSError, subprocess.SubprocessError) as exc:
        result = {'status': 'failed', 'reason': str(exc)}
    print(json.dumps(result, ensure_ascii=False, indent=2))
    return 0 if result['status'] in {'passed', 'planned', 'no_changes'} else 1


if __name__ == '__main__':
    raise SystemExit(main())
