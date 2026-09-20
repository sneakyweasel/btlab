"""Schema consistency for conjecture and literature registries."""

from __future__ import annotations

from research.conjectures import REQUIRED as CONJ_REQUIRED
from research.conjectures import STATUSES, get_conjecture, list_conjectures
import re

from research.literature import REQUIRED as LIT_REQUIRED
from research.literature import get_reference, list_references


def test_conjectures_have_required_fields_and_valid_status():
    rows = list_conjectures()
    assert rows
    ids = [r["id"] for r in rows]
    assert len(ids) == len(set(ids))
    for rec in rows:
        for key in CONJ_REQUIRED:
            assert key in rec
        assert rec["status"] in STATUSES


def test_refuted_hypotheses_are_present():
    for cid in (
        "W_not_involution",
        "W_three_n",
        "W_commutes_T",
        "BT_R_suffix_determines_next_valuation",
        "n_star_le_n",
        "H_BT_independence",
        "S_circ_D_id",
    ):
        rec = get_conjecture(cid)
        assert rec["status"] == "REFUTED"
        assert rec["counterexamples"]


def test_nk_is_not_silently_a_theorem():
    rec = get_conjecture("Nk_state_count")
    assert rec["status"] == "COMPUTATIONALLY_SUPPORTED"


def test_literature_records_have_required_fields():
    rows = list_references()
    assert rows
    for rec in rows:
        for key in LIT_REQUIRED:
            assert key in rec
    assert get_reference("kramer-2026")["project_relationship"] == "reproduced"

def _normalised_doi(rec: dict) -> str | None:
    """Lowercased DOI, with a ResearchGate version segment removed.

    ResearchGate hands out `.../RG.2.2.29894.84804` and `.../RG.2.2.29894.84804/1`
    for the same work, so a literal comparison misses the pair. The stripping is
    scoped to the `10.13140/` prefix on purpose: a first attempt removed any
    trailing `/<digits>` and collapsed three unrelated pairs, because JSTOR and
    arXiv DOIs are `10.2307/2371062` and `10.48550/arXiv.math/0501241` -- their
    whole suffix is digits and they are different works.
    """
    doi = (rec.get("identifiers") or {}).get("doi")
    if not doi:
        return None
    doi = doi.strip().lower()
    if doi.startswith("10.13140/"):
        doi = re.sub(r"/\d+$", "", doi)
    return doi


def test_literature_records_are_unique_by_id_and_by_doi():
    """One work, one record -- the invariant a merge is most likely to break.

    Two sessions recorded the same Hikawa and Winkler preprints independently
    on 20 September, one on main and one on `claude/goofy-kare-1a92fd`, under
    ids that differ by a word. Identical ids collide as a merge conflict and
    get resolved; DIFFERENT ids for the same DOI merge silently into two
    records for one work, and nothing downstream notices.

    If this fails after a merge, the fix is to reconcile the two records into
    one -- not to rename one of them.
    """
    rows = list_references()

    ids = [rec["id"] for rec in rows]
    assert len(set(ids)) == len(ids), sorted(
        {name for name in ids if ids.count(name) > 1}
    )

    seen: dict[str, str] = {}
    collisions = []
    for rec in rows:
        doi = _normalised_doi(rec)
        if doi is None:
            continue
        if doi in seen:
            collisions.append((doi, seen[doi], rec["id"]))
        seen[doi] = rec["id"]
    assert not collisions, collisions
