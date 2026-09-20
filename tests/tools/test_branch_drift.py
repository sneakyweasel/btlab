"""A branch must not quietly hold results that main does not.

Three times in September 2026 the same finding was made twice, weeks apart,
because the first one sat on a branch nobody merged. This gate does not forbid
that -- branches are where work happens -- it forbids *nobody having looked*.
Every branch carrying a ledger row or an artifact main lacks must appear in
ACKNOWLEDGED with a reason. A new one fails the suite until someone reads it
and writes down what it is.

Acknowledging is cheap and is meant to be: one line saying superseded,
pending, or abandoned. The expensive thing is the rediscovery it prevents.
"""

from __future__ import annotations

import sys
from pathlib import Path

import pytest

REPO = Path(__file__).resolve().parents[2]
TOOLS = REPO / "tools"
if str(TOOLS) not in sys.path:
    sys.path.insert(0, str(TOOLS))

import branch_drift as BD  # noqa: E402

#: Branches whose drift has been read, with what was found. Keyed by the
#: trailing part of the ref, so a local checkout and its origin/ copy match the
#: same entry. Remove an entry when the branch is merged or deleted; do not add
#: one without looking at what the branch holds.
#:
#: Assessed 14 September 2026.
#: The commit each acknowledgement was read AT. An acknowledgement is about a
#: branch's CONTENTS, so it expires when the contents change; without this the
#: gate stays green while an acknowledged branch grows, which is how
#: latest-progress-summary reached +8 unread on 2026-09-20 after being
#: acknowledged at +5. Update the sha in the same commit as the reason.
READ_AT: dict[str, str] = {
    "claude/exponent-floor-3n1-2adic-mvwa96": "e21a1091",
    "claude/latest-progress-summary-s011un": "99e846db",
    "claude/goofy-kare-1a92fd": "8aad2aae",
    "claude/elated-hopper-e20999": "86247b5d",
}

ACKNOWLEDGED: dict[str, str] = {
    "claude/goofy-kare-1a92fd": (
        "PENDING EXTRACTION, and it answers a question main spent a whole "
        "session treating as open. Read 2026-09-20. It CORRECTS two rows. "
        "J-proposition-j-on-collatz-is-terras: the mechanism is Terras 1976 "
        "(the parity bijection on Z/2^d, hence density one, with Everett 1977) "
        "but the exponent 0.050044 is LAGARIAS 1985, Theorem D -- 'known since "
        "1976' holds for the density and not for the rate. It also corrects "
        "J-paper-b-survivors-are-oeis-a076227. Seven literature records, of "
        "which two matter most: nakanishi-2026-parity-vector-structure is on "
        "Jxiv (not blocked) and was READ IN FULL -- it classifies parity "
        "vectors by number of 1s rather than length and contains NO ASYMPTOTIC "
        "ANYWHERE; and hikawa-2026-parity-vector-structures records the "
        "author's version note, whose Section 6 PROVES "
        "log_2 W(d) = gamma d + O(log d) with gamma = lambda H(1/lambda), and "
        "whose Conjecture 7.1 states W(d) = Theta(d^(-3/2) 2^(gamma d)) -- THE "
        "PRIOR STATEMENT OF THE d^(-3/2), in the weight basis, numerical and "
        "unproved, with no oscillation, no almost-periodicity and no "
        "amplitude. REGISTRY COLLISION AT MERGE: its "
        "hikawa-2026-parity-vector-structures carries DOI .../29894.84804/1, "
        "the same work as main's hikawa-2026-parity-vector-structures -- main has "
        "taken that id deliberately so the merge conflicts visibly -- "
        "and hikawa-nakanishi-2026-parity-vector-analysis exists on both sides "
        "under one id. Reconcile into single records; "
        "test_literature_records_are_unique_by_id_and_by_doi will fail until "
        "someone does."
    ),
    "claude/elated-hopper-e20999": (
        "PENDING MERGE, and it clears main's last red Paper C gate. Read "
        "2026-09-20. 86247b5d closes two verification gaps. First, Corollaries "
        "5.4 and 5.5 sat inside Theorem 1's sentence with no verification-table "
        "row: the answer is a split, not an either/or -- "
        "Production.failures_logMass_ge IS 5.5(2)'s log-mass clause, "
        "kernel-checked for 0 < lambda <= 13/40, while 5.4 is formalized "
        "nowhere because its dyadic-block pigeonhole does not exist in Lean, "
        "and 5.5(1) and (3) are one unwritten instantiation away. The barrel "
        "had contradicted itself on this since failures_logMass_ge landed. "
        "Second, Appendix A claimed thirty imports while naming 29; wiring in "
        "FateProductionWords makes it thirty-one named and thirty-one "
        "imported. Also corrects J-paper-c-production-words-are-prefix-free "
        "and J-paper-c-trust-surface. Merging is a decision for Philippe, not "
        "a gate."
    ),
    "claude/exponent-floor-3n1-2adic-mvwa96": (
        "PENDING EXTRACTION. Re-read 2026-09-20 at e21a1091, having grown by a "
        "commit since the previous reading. SIX rows main lacks and twelve "
        "probe, test and dossier files. The original content stands: it answers "
        "whether the exponential bridge removes the 2-adic rigidity -- it does "
        "not, it RELOCATES it, since conjugating Collatz's odd step by u = x+1 "
        "gives u -> 3u/2 and the Juggler's exact odd step on n = a^e gives "
        "e -> 3e/2 on the exponent, the same map on the same prime, with "
        "Collatz carrying the 2-adic integer in the VALUE and Juggler in the "
        "EXPONENT. "
        "NEW AT e21a1091, three results. (1) The 3x-1 verification floor was "
        "RUN: every 1 <= y < 2^38 reaches 1, 5 or 17 under y/2 and (3y-1)/2, "
        "certified by 8 disjoint chunks of 2^35 with 0 failures and 0 new "
        "cycles, verifier archived and re-runnable. That turns the finance "
        "mirror's period table into a statement -- a fourth cycle of the 3x-1 "
        "shortcut, equivalently a fourth negative cycle of shortcut 3x+1, has "
        "period at least 4404167 with 2778720 odd steps, by kernel-checked "
        "neg_cycle_finance at that floor. Only the floor is empirical. (2) A "
        "THEOREM: for even a >= 2, floor((2^a - 1)^(3/2)) = 2^(3a/2) - "
        "3*2^(a/2-1), so the floor charge against the top of the cell is "
        "exactly 3*2^(a/2-1); one binomial tail, verified to a = 400. For odd "
        "a the value is a Beatty value in sqrt 2. By Catalan-Mihailescu 2^a - 1 "
        "is never a perfect power, so the repunits are maximally INEXACT starts "
        "and the charge is exact anyway -- the floor charge is not intrinsically "
        "unknowable off the perfect powers, only generically. (3) NEGATIVE: the "
        "Mersenne primality is decorative, the floor is attained at every "
        "2^a - 1 including 15, 63, 255, 511; what is structural is u = x+1 = "
        "2^a, and under the bridge the extremal transports to e = 2^r, one bit "
        "rather than a repunit, so the all-ones pattern does not survive. Same "
        "verdict on the Fermat reading of -5 and -17. "
        "The branch reports the Paper B kit gate failing at HEAD too, untouched."
    ),
    "claude/latest-progress-summary-s011un": (
        "PENDING EXTRACTION, and it has GROWN since it was first acknowledged "
        "at +5; this entry now covers +8, read 2026-09-20 at 99e846db. The "
        "original reading stands: it proves the low-share decay by one "
        "inequality at every convergent denominator with no exponential sum, "
        "because P has FINITE TOTAL LOGARITHMIC MASS -- so nothing needs "
        "planting, no backward closure is required, and it holds for every set "
        "of integers. That superseded main's whole Erdos-Turan averaging "
        "route, now in negative_knowledge.md. Three rows main lacks "
        "(J-oe-fiber-block-lock, J-oe-poor-fiber-tail, "
        "J-oe-averaged-two-productions-reach-the-depth-two-ceiling) and a "
        "correction to J-oe-low-share-weight-decays-polynomially. "
        "WHAT IS NEW SINCE +5, and it is the Lean: a Mathlib-from-source build "
        "finished and the written Lean now has a verdict. Lemma 3 is verified "
        "-- FateResonanceCount compiles and resonance_count_le, "
        "resonance_count_one and resonant_mem_arc each print the standard "
        "three axioms. The fiber instantiation is verified -- FateFiberLock "
        "compiles, evenImageCount_eq_fract is the parity bridge and "
        "fiber_block_lock puts BlockLock.block_lock on the fiber. And "
        "exists_coprime_approx gives Dirichlet in lowest terms, which "
        "block_lock needs because coprimality is what makes the q points a "
        "full 1/q-grid. Both modules are now in the barrel. Left in the note: "
        "Lemma 2's arithmetic and Theorem 4, which the branch says carry no "
        "new mathematical content. The newest commit was read in full here; "
        "the five before it were read by subject line and by this summary."
    ),
}


def _key(ref: str) -> str:
    return ref.split("origin/", 1)[-1]


@pytest.fixture(scope="module")
def drifts() -> list[BD.Drift]:
    if not BD.refs_are_visible(REPO):
        pytest.skip("no remote refs at all (shallow or single-branch clone)")
    return BD.report(REPO)


def test_every_drifting_branch_has_been_read(drifts: list[BD.Drift]) -> None:
    """A branch holding a row or artifact main lacks must be acknowledged."""

    unread = [d for d in drifts if _key(d.ref) not in ACKNOWLEDGED]
    assert not unread, (
        "branch(es) carry laboratory results main does not have, and nobody has "
        "recorded what they are:\n\n"
        + BD.render(unread)
        + "\n\nRead them, then add an entry to ACKNOWLEDGED in this file saying "
        "superseded, pending extraction, or abandoned. Run "
        "`python tools/branch_drift.py` for the full report."
    )


def test_acknowledgements_are_not_stale(drifts: list[BD.Drift]) -> None:
    """Entries for branches that no longer drift should be removed."""

    live = {_key(d.ref) for d in drifts}
    stale = sorted(set(ACKNOWLEDGED) - live)
    assert not stale, (
        f"{stale} no longer carry anything main lacks -- merged, deleted, or "
        "extracted. Remove them from ACKNOWLEDGED so the list stays a list of "
        "real outstanding work."
    )



def test_files_are_counted_against_the_merge_base_not_main() -> None:
    """The calibration that cost the orphan gate its first two readings.

    Measuring "present on the branch, absent from main" counts every file main
    has since *deleted*. The August cursor/* branches each scored 17 Lean files
    and 102 sources that way -- all casualties of the src/bt restructure, none
    of them the branch's work. Counting additions since the merge base gives
    zero, which is the truth.

    Those branches are merged and gone, so the property is exercised against a
    throwaway ref at an ancestor commit rather than against whichever branch
    happens to illustrate it. An ancestor is the sharpest case: its merge base
    is itself, so it added nothing, while it still carries files main no longer
    has. The naive metric is computed alongside to show the two disagree --
    without that, a metric that always returned zero would pass.
    """

    import subprocess

    ancestor = subprocess.run(
        ["git", "rev-list", "-1", "HEAD", "--", "src/automata/modular.py"],
        capture_output=True, cwd=REPO, text=True,
    ).stdout.strip()
    if not ancestor:
        pytest.skip("pre-restructure history not present in this clone")

    ref = "refs/drift-calibration"
    subprocess.run(["git", "update-ref", ref, ancestor], cwd=REPO, check=True)
    try:
        on_ref = set(subprocess.run(
            ["git", "ls-tree", "-r", "--name-only", ancestor], capture_output=True,
            cwd=REPO, text=True).stdout.split())
        on_main = set(subprocess.run(
            ["git", "ls-tree", "-r", "--name-only", "main"], capture_output=True,
            cwd=REPO, text=True).stdout.split())
        naive = {f for f in on_ref - on_main if f.startswith(("src/", "formal/"))}
        assert naive, "the control needs an ancestor that main has since pruned"

        drift = BD.drift_for(REPO, ref)
        assert drift.ahead == 0, "an ancestor is behind main, never ahead"
        assert not any(drift.files.values()), (
            f"the merge-base metric must ignore main's own deletions; naive would "
            f"have reported {len(naive)} files"
        )
    finally:
        subprocess.run(["git", "update-ref", "-d", ref], cwd=REPO, check=False)

def test_artifacts_are_counted_and_not_only_ledger_rows() -> None:
    """The other calibration: a branch can carry a module and no ledger row.

    information-field-dynamics was the live example -- a 938-line Lean module
    and not one ledger id, invisible to a rows-only gate. Extracting it in
    7b93d626 dissolved that example, which is the point of extracting it, so
    the property is asserted against the classifier rather than against
    whichever branch happens to illustrate it today.
    """

    rows_only = BD.Drift(ref="x", ahead=1, behind=0, last_commit="2026-09-07")
    assert not rows_only.carries_work, "a branch adding nothing must not register"

    module_only = BD.Drift(
        ref="x",
        ahead=1,
        behind=0,
        last_commit="2026-09-07",
        ledger_ids=[],
        files={"lean": ["formal/Problems/Engine/Whatever.lean"], "probe": [], "test": [], "dossier": []},
    )
    assert module_only.carries_work, "a Lean module with no ledger row must register"

    row_only = BD.Drift(
        ref="x", ahead=1, behind=0, last_commit="2026-09-07", ledger_ids=["J-something"]
    )
    assert row_only.carries_work, "a ledger row with no files must register"

    assert {"lean", "probe", "test", "dossier"} <= set(BD.ARTIFACTS), (
        "the artifact classes a branch can strand must all be scanned"
    )

def test_acknowledgements_name_the_commit_they_read(drifts: list[BD.Drift]) -> None:
    """An acknowledgement expires when the branch moves past what was read.

    ACKNOWLEDGED describes a branch's CONTENTS, so a branch that grows after
    being acknowledged is unread again while the gate stays green. That is not
    hypothetical: `latest-progress-summary` was acknowledged at +5 and reached
    +8 with three more kernel-checked results before anyone looked, because
    nothing tied the entry to a commit.
    """
    heads = {_key(d.ref): BD.head_sha(REPO, d.ref) for d in drifts}

    missing = sorted(set(ACKNOWLEDGED) - set(READ_AT))
    assert not missing, (
        f"{missing} are acknowledged without naming the commit read. Add a "
        "short sha to READ_AT."
    )

    moved = [
        (key, READ_AT[key], heads[key])
        for key in sorted(set(ACKNOWLEDGED) & set(heads))
        if not heads[key].startswith(READ_AT[key])
    ]
    assert not moved, (
        "branch(es) have new commits since the acknowledgement was written, "
        "so what is recorded no longer describes them:\n"
        + "\n".join(
            f"    {k}: read at {r}, now at {h}" for k, r, h in moved
        )
        + "\n\nRead the new commits, update the reason, move the sha."
    )
