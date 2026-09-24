# Stage research outputs before promotion

Use `lab.py artifacts` when generating new research reports. The explicit producer
runs in this checkout with its output directed into ignored scratch space. The
wrapper validates provenance, copies the candidate into a separate sealed tree,
and leaves the canonical destination for an explicit local promotion.

```powershell
python tools/lab.py artifacts stage --target data/research/juggler/paper_c_audit -- python tools/check_paper_c_intervals.py --output '{stage}/data/research/juggler/paper_c_audit/intervals.json'
python tools/lab.py artifacts list
python tools/lab.py artifacts inspect <stage-id>
python tools/lab.py artifacts promote <stage-id>
```

The stage ID is printed before execution and in the result. `inspect` is read-only;
it reports changed files, manifest integrity, and whether the current state permits
promotion. `list` shows recent receipts without freshness checks. Both accept
`--limit` (1–200). A recorded `running` status after interruption is not proof that
a process remains alive. Failed/interrupted producers are never promotable: rerun
the explicit command to create a new stage.

Only explicit `python` producer commands are accepted; the selected checkout's
interpreter and imports are used. Commands from saved receipts and manifests are
never executed. `{stage}` expands to a checkout-relative scratch root. Producers
must support an explicit output destination and retain the checkout-relative
layout under that root. For example, `check_papers_arb.py --output-root '{stage}'`
already supports this layout; repeat `--target` for its selected programme output
directories. `--timeout` bounds the direct producer process (default 1,200 seconds).
Producers must wait for any child writers before returning.

Targets must be nonoverlapping directories under `data/research/juggler/<topic>`,
`data/research/collatz/<topic>`, or `docs/theory/figures`. Every promoted file must
be a valid research sidecar or an output covered by exactly one sidecar. Sidecars
must record commands, Git revision, source files and valid input/output hashes.
Unknown provenance, source warnings, changed byte representations, output escapes,
links/junctions and unmanifested outputs fail staging. Diagnostic files under the
scratch root's `.build/` remain local and are not promoted.

The receipt snapshots Git-visible files outside the target directories, Git HEAD,
the selected Python package inventory, and existing destination files before the
run. Use repeatable `--input path/to/file` for ignored input files; manifest inputs
must have been captured before execution. Any snapshot drift blocks promotion,
including a commit or unrelated source edit. Prefer a quiet isolated checkout and
promote before committing the resulting evidence. Do not edit receipts or update
hashes to bypass a failed check. These snapshots do not audit external services,
undeclared ignored inputs, native library state, or changes that were reverted
between observations.

Promotion takes a checkout-local OS lock, backs up overwritten files, writes a
recovery journal, replaces output files, and replaces manifests last. Unmentioned
historical files remain untouched. Each replacement is atomic; the group of files
is **not** a filesystem transaction. Other tools can see an intermediate state.
Do not run consumers of the destination concurrently with promotion. The journal
records completion before the receipt status; interrupted receipt updates cannot
cause a completed promotion to be rolled back.

```powershell
python tools/lab.py artifacts recover <stage-id>
```

Recovery restores previous bytes, or removes files introduced by that promotion.
It first checks every affected file and backup. If someone has written different
bytes since the attempted promotion, recovery stops and preserves their work.
An unfinished journal blocks subsequent promotions until recovered. Recovery
does not undo completed promotions; use normal Git review/recovery for those.
Receipts, logs, sealed candidates and backups stay in `.build/artifacts/<stage-id>`.
Keep them while investigating interrupted work; they are not public provenance.

This is a workflow for cooperating producers, not an OS sandbox. A producer that
ignores its output flags can still write elsewhere; the wrapper detects captured
state drift but does not undo arbitrary producer side effects. A timeout kills the
direct process, not necessarily its descendants. Hashes establish file integrity,
not mathematical correctness, analytic hypotheses, or Lean verification. No claim
labels change. Review the artifact scope and run the normal
[acceptance checks](agent_workflow.md) before committing.
