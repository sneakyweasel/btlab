"""Finite-dynamics companion, merged into the laboratory Streamlit app."""

from __future__ import annotations

import altair as alt
import pandas as pd
import streamlit as st

from visualization.juggler_finite_dynamics import (
    BEST_V,
    BLOCKER_FAN,
    CENSUS_LEDGER_IDS,
    CLAIM_ROWS,
    CYCLE_WORD_MAX,
    CYCLE_WORD_PRESETS,
    DESCENT_WINDOW_MAX,
    DK_BREAKEVEN_FLOOR,
    EEEE_N0,
    EEEE_THRESHOLD,
    EEEE_WORD,
    INSTANCE_ROWS,
    INTERNAL_E_MARGIN,
    INTERNAL_E_WORD,
    LAB_FLOOR,
    LAB_LEFTOVER_DECISIONS,
    LAB_PARITY_PERIOD,
    LAB_WALK_PERIOD,
    LEFTOVER_CUTOFF,
    LEFTOVER_FAMILY_LEDGER_IDS,
    N_PRESETS,
    NOTE_TRAJECTORY_3,
    NOTE_PEAK_37,
    TRAJECTORY_STEPS_MAX,
    PAPER_EXCEPTION_COUNT,
    PAPER_FLOOR,
    PAPER_L_CAP,
    PAPER_PERIOD,
    PRINTED_FLOOR,
    PRINTED_KILL_COUNT,
    PRINTED_PERIOD,
    RECORD_LENGTHS,
    SPOT_WITNESS,
    WALK_CHARGE_LEDGER_IDS,
    WALK_WINDOW_HI,
    WALK_WINDOW_LO,
    WORD_MAX,
    WORD_PRESETS,
    census_inventory,
    classify_word,
    compose_view,
    cycle_class_view,
    descent_view,
    descent_window,
    envelope_view,
    even_preimage_view,
    finance_chart_rows,
    finance_view,
    format_int,
    four_block_replay,
    lab_walk_survey,
    leftover_table,
    leftover_words,
    length11_inventory,
    length_eight_status_rows,
    next_square_view,
    odd_preimage_view,
    paper_exception_lengths,
    parse_cycle_word,
    parse_word,
    printed_floor_kill_rows,
    try_cycle_word,
    walk_trajectory,
)
from visualization.theorem_ledger import badge_payload

VIEWS = (
    "Claim map",
    "Finance",
    "Walk charge",
    "Trajectory",
    "Envelope",
    "Preimages and census",
    "Cycle words",
    "Leftover families",
    "Descent",
)
VIEW_LABEL = {
    "Claim map": "Status",
    "Finance": "Finance",
    "Walk charge": "Walk",
    "Trajectory": "Trajectory",
    "Envelope": "Envelope",
    "Preimages and census": "Preimages",
    "Cycle words": "Cycle",
    "Leftover families": "Leftovers",
    "Descent": "Descent",
}
VIEWS_WITH_START = frozenset(
    {"Trajectory", "Envelope", "Preimages and census", "Cycle words", "Descent"}
)
VIEW_BLURB = {
    "Claim map": (
        "Paper A scoreboard. The printed theorem is a period lower bound, "
        "not a halt proof. Lean is the authority for the exact claims; "
        "Theorem 4.6 and Corollary 5.11 are verified computations."
    ),
    "Finance": (
        "The engine of Sections 2–4: at a cycle minimum the surplus "
        "$3^o-2^L$ must be paid by floor errors. Combined with the "
        "verified descent floor $10^6$, every period at most $25780$ "
        "is excluded (Theorem 4.6)."
    ),
    "Walk charge": (
        "Section 5 couples the floor losses through one exponent walk. "
        "At the laboratory floor the envelope gives period "
        f"$\\ge {LAB_WALK_PERIOD}$; the third certified floor prints "
        f"period $\\ge {PRINTED_PERIOD}$ (Corollary 5.11)."
    ),
    "Trajectory": (
        "Start at **n** and apply the Juggler map. **O** is an odd step "
        "(the number grows); **E** is an even step (it shrinks). The "
        "word is just that sequence of steps."
    ),
    "Envelope": (
        "Type a short **O/E** recipe. If your start actually follows it, "
        "a proved bound says the result cannot be too large. Slack **Δ** "
        "is how much room is left. Section 4 uses the envelope, not the "
        "defect composition."
    ),
    "Preimages and census": (
        "Work backwards: which numbers land on a given image? Then see "
        "which short loop-shapes are already ruled out."
    ),
    "Cycle words": (
        "A **cycle word** is a loop of **O** and **E** letters. Rotating "
        "it is the same loop started at a different letter. The page "
        "says whether that loop is already impossible."
    ),
    "Leftover families": (
        "Local leftover spellings the easy one-step preimages did not kill. Paper A "
        "already excludes every cycle word with fewer than four evens, "
        "and Theorem 4.6 excludes every period at most 25780. These "
        "thirty words are a lab gate, not open cycles."
    ),
    "Descent": (
        "Even starts drop in one even step. Odd-then-even starts drop "
        "in two. The leftovers are the odd-to-odd cases. A count in a "
        "window is not a density proof."
    ),
}
CLAIM_PLAIN = {
    "J-fixed-word-image-monotone": "Same word, bigger start never finishes smaller.",
    "J-power-envelope-contraction": "After a word, the result cannot outrun a known power bound.",
    "J-global-defect-identity": "The leftover slack after a word can be written exactly.",
    "J-inverse-preimage-asymmetry": "Going backwards, an odd image has at most one odd parent.",
    "J-cycle-finite-structure": "A real loop must mix O and E, and grow more than it shrinks.",
    "J-leftover-length-six-orientations": "The two leftover length-6 loops cannot close.",
    "J-small-cycle-census": "No loop of length 6 or less.",
    "J-leftover-length-seven-orientations": "The two leftover length-7 loops cannot close.",
    "J-small-cycle-census-seven": "No loop of length 7 or less.",
    "J-small-cycle-census-eight": "No loop of length 8 or less (implied by period ≥ 11).",
    "J-two-even-leftover-ee": "The two-even leftover families cannot close.",
    "J-first-e-transport-ee": "Gapped three-even CycleMin loops cannot close.",
    "J-three-even-eee": "Bunched last-cluster leftovers cannot close.",
    "J-gapped-cycle-word-ee": "Gapped three-even CycleWord loops cannot close.",
    "J-even-count-le-three": "Every real loop has at least four even letters, so the period is at least 11.",
    "J-cycle-finance-inequality": "At a cycle minimum, n log n times the surplus cannot exceed L 3^o.",
    "J-cycle-word-eliahou-leftover-instance": "With the verified descent floor 10^6, there is no period ≤ 25780.",
    "J-cycle-period-fifty-thousand": "At the laboratory floor 26254995 the same table gives period ≥ 50508.",
    "J-cyclemin-walk-charge-instance": "Walk charge at that floor kills the parity leftovers below 176251.",
    "J-cycle-period-four-hundred-seventy-eight-thousand": "At the second certified floor 162849448, period ≥ 478245.",
    "J-residual-floor-three-hundred-fifty-million": "Every start through 350000000 reaches 1 by first-passage descent.",
    "J-cycle-period-seven-hundred-eighty-thousand": "At the third certified floor 350000000, period ≥ 780239.",
    "J-finite-progress-boundary": "Even starts drop in one step; odd-then-even starts drop in two.",
}
_BADGE_COLOR = {
    "exact": "green",
    "computed": "blue",
    "conjecture": "orange",
    "refuted": "red",
    "reparameterization": "violet",
    "other": "gray",
}


def _init_state() -> None:
    defaults = {
        "juggler_view": "Claim map",
        "juggler_n": 3,
        "juggler_word": "OOE",
        "juggler_cycle_word": "OEO",
        "juggler_cycle_shift": 0,
        "juggler_cycle_slider": 0,
        "juggler_steps": 20,
        "juggler_split": 1,
        "juggler_goto_cycle": False,
        "juggler_finance_L": PAPER_PERIOD,
    }
    for key, value in defaults.items():
        if key not in st.session_state:
            st.session_state[key] = value
    st.session_state.shared_integer = int(st.session_state.juggler_n)


def _blurb(view: str) -> None:
    st.caption(VIEW_BLURB[view])


def _lazy_expander(label: str, *, icon: str, key: str):
    return st.expander(
        label,
        icon=icon,
        key=key,
        on_change="rerun",
        type="compact",
    )


def _glossary() -> None:
    box = _lazy_expander("Word list", icon=":material/menu_book:", key="juggler_glossary")
    if not box.open:
        return
    with box:
        st.markdown(
            """
- **O / E** — odd step (cube, then floor) / even step (square root, then floor).
- **Cycle word** — a loop of those letters. Rotating it is the same loop
  started at a different letter.
- **Expanding** — more odd letters than the even shrinks can cancel. A
  real loop must be expanding.
- **Leftover** — a word the easy filters did not kill. It needs a leftover
  cell or a finite table.
- **N0** — a verified descent floor: every start $2\\le n\\le N_0$
  reaches 1. Paper A uses $10^6$, then $26254995$, then $162849448$, then $350000000$.
- **CycleMin** — the rotation that starts at the smallest value on the loop.
- **Finance** — the cycle-minimum inequality
  $n\\log n\\cdot(3^o-2^L)\\le L\\cdot 3^o$.
- **$n_{\\max}(L)$** — largest minimum the parity $6/5$ bound still allows.
- **$\\mathcal E$** — the 141 lengths $\\le 10^5$ still admissible to
  that bound at the verified descent floor $10^6$. Membership is not
  evidence for a cycle.
- **Walk charge** — the Section 5 refinement: floor losses are
  transported to a reduced base and priced on the hug (rotation) word.
- **Verified descent floor** — every start through the named $N_0$
  reaches 1. The $10^6$ floor is Weisstein, recomputed here; the two
  laboratory floors are first-passage certificates. Not a halt theorem.
- **Reached 1** — this walk hit 1. That is not a proof that every start does.
            """
        )


def _proof_tags(*theorem_ids: str) -> None:
    payloads = [badge_payload(tid) for tid in theorem_ids]
    payloads = [payload for payload in payloads if payload]
    if not payloads:
        return
    box = st.expander(
        "Proof tags",
        icon=":material/verified:",
        type="compact",
    )
    with box:
        for payload in payloads:
            color = _BADGE_COLOR.get(payload["kind"], "gray")
            lean = ""
            if payload.get("lean"):
                lean = f" · Lean `{payload['lean']}`"
            row = st.container(
                horizontal=True,
                vertical_alignment="center",
                gap="small",
            )
            with row:
                st.badge(payload["tag"], color=color)
                st.caption(f"{payload['id']}{lean}")


def _set_n(n: int) -> None:
    st.session_state.juggler_n = n
    st.session_state.shared_integer = n


def _n_controls() -> int:
    def _apply_preset() -> None:
        name = st.session_state.get("juggler_n_preset")
        if name:
            _set_n(N_PRESETS[name])

    row = st.container(horizontal=True, vertical_alignment="bottom", gap="small")
    with row:
        st.pills(
            "Start presets",
            list(N_PRESETS),
            selection_mode="single",
            key="juggler_n_preset",
            on_change=_apply_preset,
        )
        n = int(
            st.number_input(
                "Start n",
                min_value=1,
                step=1,
                key="juggler_n",
                width=160,
                persist_state="session",
                help="Positive integer. Shared with the rest of the laboratory.",
            )
        )
    st.session_state.shared_integer = n
    return n


def _word_controls() -> str:
    def _apply_preset() -> None:
        name = st.session_state.get("juggler_word_preset")
        if name:
            st.session_state.juggler_word = name

    if not str(st.session_state.get("juggler_word") or "").strip():
        st.session_state.juggler_word = (
            st.session_state.get("juggler_word_preset") or "OOE"
        )

    row = st.container(horizontal=True, vertical_alignment="bottom", gap="small")
    with row:
        st.pills(
            "Word presets",
            list(WORD_PRESETS),
            selection_mode="single",
            key="juggler_word_preset",
            on_change=_apply_preset,
        )
        raw = st.text_input(
            "Parity word",
            key="juggler_word",
            help=f"Letters O and E only, length at most {WORD_MAX}.",
        )
    word = parse_word(raw)
    if word is None:
        st.warning(
            f"Use only O and E, with length at most {WORD_MAX}.",
            icon=":material/warning:",
        )
        return "OOE"
    return word


def _cycle_word_controls() -> str:
    def _apply_preset() -> None:
        name = st.session_state.get("juggler_cycle_example")
        if name:
            st.session_state.juggler_cycle_word = name
            st.session_state.juggler_cycle_shift = 0
            st.session_state.juggler_cycle_slider = 0

    if not str(st.session_state.get("juggler_cycle_word") or "").strip():
        st.session_state.juggler_cycle_word = (
            st.session_state.get("juggler_cycle_example") or "OEO"
        )

    row = st.container(horizontal=True, vertical_alignment="bottom", gap="small")
    with row:
        st.selectbox(
            "Example loop",
            list(CYCLE_WORD_PRESETS),
            key="juggler_cycle_example",
            on_change=_apply_preset,
            width=220,
        )
        raw = st.text_input(
            "Cycle word",
            key="juggler_cycle_word",
            help=(
                f"Letters O and E only, length at most {CYCLE_WORD_MAX}. "
                "Rotations are the same loop."
            ),
        )
    word = parse_cycle_word(raw)
    if word is None:
        st.warning(
            f"Use only O and E, with length at most {CYCLE_WORD_MAX}.",
            icon=":material/warning:",
        )
        return "OEO"
    return word


def _yes_no(flag: bool | None) -> str:
    if flag is True:
        return "yes"
    if flag is False:
        return "no"
    return "—"


def _claim_map() -> None:
    _blurb("Claim map")
    _proof_tags(
        "J-even-count-le-three",
        "J-cycle-word-eliahou-leftover-instance",
        "J-cyclemin-walk-charge-instance",
        "J-cycle-period-four-hundred-seventy-eight-thousand",
        "J-cycle-period-seven-hundred-eighty-thousand",
    )
    cards = st.container(horizontal=True)
    with cards:
        st.metric(
            "Period",
            f"≥ {PRINTED_PERIOD:,}",
            border=True,
            help="Corollary 5.11. Not evidence for a 780239-cycle.",
        )
        st.metric(
            "Printed floor N0",
            f"{PRINTED_FLOOR:,}",
            border=True,
            help="Third certified descent floor. Every start through this n reaches 1.",
        )
        st.metric(
            "Even letters",
            "≥ 4",
            border=True,
            help="Theorem 3.22. Implies period ≥ 11 with no floor.",
        )
        st.metric("Arrival at 1", "not claimed", border=True)
    st.markdown(
        r"""
```mermaid
flowchart LR
  envelope[Word envelope] --> min[Cycle minimum]
  min --> finance[Finance]
  finance --> nmax["n_max(L)"]
  nmax --> base["N0 = 10^6"]
  base --> thm46["L ≥ 25781"]
  thm46 --> lab["N0 = 26254995"]
  lab --> walk[Walk charge]
  walk --> thm59["L ≥ 176251"]
  thm59 --> floor2["N0 = 162849448"]
  floor2 --> cor510["L ≥ 478245"]
  cor510 --> printed["N0 = 350000000"]
  printed --> cor511["L ≥ 780239"]
```
        """
    )
    st.dataframe(
        pd.DataFrame(
            [
                {
                    "theorem": row["theorem"],
                    "floor N0": f"{row['floor']:,}",
                    "period": f"≥ {row['period']:,}",
                    "mechanism": row["mechanism"],
                }
                for row in INSTANCE_ROWS
            ]
        ),
        hide_index=True,
        width="stretch",
    )
    rows = [
        {
            "in plain English": CLAIM_PLAIN.get(row["ledger"], row["text"]),
            "theorem": row["text"],
            "Lean": row["lean"],
        }
        for row in CLAIM_ROWS
    ]
    st.dataframe(pd.DataFrame(rows), hide_index=True, width="stretch", height=360)
    with st.expander("What this does not claim", icon=":material/info:"):
        st.caption(
            "This is not a termination proof and not progress toward the "
            "Juggler conjecture. Membership in ℰ means only that the "
            "Theorem 4.6 bound does not exclude the length. The thirty "
            "length-11 short-gap words are a laboratory leftover gate, "
            "not Paper A open cycles: period 11 is already excluded. "
            "The walk program is terminal: killing 780239 is Diophantine."
        )


def _finance() -> None:
    _blurb("Finance")
    _proof_tags(
        "J-cycle-finance-inequality",
        "J-cycle-word-eliahou-leftover-instance",
    )
    st.latex(r"n\log n\cdot(3^o-2^L)\le L\cdot 3^o")
    st.caption(
        "Theorem 4.4, constant 1 in Lean. The printed table is the "
        "weaker parity $6/5$ form of Theorem 4.6: replacing $6/5$ by "
        "$1$ does not change the first survivor $25781$. This view is "
        "the $N_0=10^6$ instance, not Corollary 5.10."
    )
    cards = st.container(horizontal=True)
    with cards:
        st.metric("Verified descent floor", f"{PAPER_FLOOR:,}", border=True)
        st.metric("First unexcluded length", f"{PAPER_PERIOD:,}", border=True)
        st.metric("|ℰ| through 10⁵", str(PAPER_EXCEPTION_COUNT), border=True)
        st.metric("Arrival at 1", "not claimed", border=True)

    def _apply_record() -> None:
        name = st.session_state.get("juggler_finance_record")
        if name is not None:
            st.session_state.juggler_finance_L = int(name)

    row = st.container(horizontal=True, vertical_alignment="bottom", gap="small")
    with row:
        st.selectbox(
            "Record length",
            RECORD_LENGTHS,
            index=None,
            placeholder="Jump to a record length",
            key="juggler_finance_record",
            on_change=_apply_record,
            width=220,
            help="One-sided best-approximation lengths, not ordinary CF denominators.",
        )
        length = int(
            st.number_input(
                "Period L",
                min_value=1,
                max_value=PAPER_L_CAP,
                step=1,
                key="juggler_finance_L",
                width=160,
            )
        )
    view = finance_view(length)
    status_row = st.container(horizontal=True)
    with status_row:
        st.metric("This L", view.status, border=True)
        st.metric(
            "o_min",
            view.o_min if view.o_min is not None else "—",
            border=True,
            help="Least odd count with 3^o > 2^L.",
        )
        st.metric(
            "n_max",
            f"{view.n_max:,}" if view.n_max is not None else "—",
            border=True,
            help="Largest cycle minimum the 6/5 bound still allows.",
        )
        st.metric("In ℰ?", "yes" if view.in_exception_set else "no", border=True)
    if view.admissible:
        st.info(
            f"L = {length} is admissible to the Theorem 4.6 table at "
            f"the descent floor {PAPER_FLOOR:,}. That is not evidence "
            "for a cycle.",
            icon=":material/info:",
        )
    elif view.excluded_by_floor:
        st.success(
            f"L = {length} is excluded: n_max is at most the verified "
            f"descent floor {PAPER_FLOOR:,}, or the length lies below "
            f"{PAPER_PERIOD:,}.",
            icon=":material/check:",
        )
    chart_df = pd.DataFrame(finance_chart_rows())
    chart = (
        alt.Chart(chart_df)
        .mark_line(point=True)
        .encode(
            x=alt.X("L:Q", title="period L"),
            y=alt.Y("n_max:Q", title="n_max", scale=alt.Scale(type="log")),
            color=alt.Color("record:N", title="record length"),
            tooltip=["L", "n_max", "record"],
        )
    )
    floor_line = (
        alt.Chart(pd.DataFrame({"n_max": [PAPER_FLOOR]}))
        .mark_rule(strokeDash=[4, 4])
        .encode(y="n_max:Q")
    )
    st.altair_chart(chart + floor_line, width="stretch")
    st.caption(
        f"Parity $n_{{\\max}}(L)$ for $L\\le {chart_df['L'].max()}$. "
        "Spikes are one-sided best-approximation lengths. The dashed "
        f"line is the Theorem 4.6 floor {PAPER_FLOOR:,}; the first "
        f"survivor {PAPER_PERIOD:,} is off this chart."
    )

    records = _lazy_expander(
        "Printed record lengths",
        icon=":material/table:",
        key="juggler_finance_records",
    )
    if records.open:
        with records:
            st.dataframe(
                pd.DataFrame(
                    [
                        {
                            "L": length,
                            "o_min": finance_view(length).o_min,
                            "n_max": finance_view(length).n_max,
                            "status": finance_view(length).status,
                        }
                        for length in RECORD_LENGTHS
                    ]
                ),
                hide_index=True,
                width="stretch",
            )
            st.caption(
                "11 and 569 are not ordinary continued-fraction "
                "denominators of log 2 / log 3."
            )

    leftovers = _lazy_expander(
        "First lengths in ℰ",
        icon=":material/list:",
        key="juggler_finance_exceptions",
    )
    if leftovers.open:
        with leftovers:
            shown = paper_exception_lengths()[:20]
            st.dataframe(
                pd.DataFrame({"L": list(shown)}),
                hide_index=True,
                width="stretch",
                height=240,
            )
            st.caption(
                f"{PAPER_EXCEPTION_COUNT} lengths through {PAPER_L_CAP:,}. "
                "Run packing thins this set to 99 without raising the "
                "cutoff. Full list: "
                "data/research/juggler/cycle_finance/exceptions_parity.json."
            )


def _walk_charge() -> None:
    _blurb("Walk charge")
    _proof_tags(*WALK_CHARGE_LEDGER_IDS)
    survey = lab_walk_survey()
    kills = printed_floor_kill_rows()
    below = [row for row in kills if row.length < PRINTED_PERIOD]
    blocker = next(row for row in kills if row.length == PRINTED_PERIOD)
    cards = st.container(horizontal=True)
    with cards:
        st.metric(
            "Printed period",
            f"≥ {PRINTED_PERIOD:,}",
            border=True,
            help="Corollary 5.11. Not evidence for a cycle of that length.",
        )
        st.metric(
            "Third certified floor",
            f"{PRINTED_FLOOR:,}",
            border=True,
        )
        st.metric(
            "Walk kills below the blocker",
            f"{sum(1 for row in below if row.excluded)} / {PRINTED_KILL_COUNT}",
            border=True,
            help="Certified evaluations of the Theorem 5.9 comparison.",
        )
        st.metric("Arrival at 1", "not claimed", border=True)
    st.markdown(
        r"""
```mermaid
flowchart LR
  transport[Transport] --> hug[Hug adversary]
  hug --> identity[Word identity]
  identity --> dk[Denjoy–Koksma]
  dk --> window["Window 50508, 301994"]
  window --> lab["L ≥ 176251"]
  lab --> floor2["N0 = 162849448"]
  floor2 --> cor510["L ≥ 478245"]
  cor510 --> printed["N0 = 350000000"]
  printed --> cor511["L ≥ 780239"]
```
        """
    )
    ladder = st.container(horizontal=True)
    with ladder:
        st.metric("Theorem 4.6 at 10^6", f"≥ {PAPER_PERIOD:,}", border=True)
        st.metric(
            f"Theorem 5.2 at {LAB_FLOOR:,}",
            f"≥ {LAB_PARITY_PERIOD:,}",
            border=True,
        )
        st.metric(
            "Theorem 5.9 walk charge",
            f"≥ {LAB_WALK_PERIOD:,}",
            border=True,
        )
        st.metric(
            "Corollary 5.11",
            f"≥ {PRINTED_PERIOD:,}",
            border=True,
        )
    st.caption(
        f"Theorem 5.9 at N0 = {LAB_FLOOR:,} leaves the single walk "
        f"survivor {int(survey['combined_first_survivor']):,}. "
        f"The census-free window is [{WALK_WINDOW_LO}, {WALK_WINDOW_HI}). "
        f"The blocker is the k=2 fan member "
        f"{PRINTED_PERIOD:,} = {LAB_WALK_PERIOD:,} + 2·{BLOCKER_FAN:,}."
    )
    with st.container(border=True, gap="small"):
        st.markdown("**Blocker**")
        block_row = st.container(horizontal=True)
        with block_row:
            st.metric("Length", f"{blocker.length:,}", border=True)
            st.metric(
                "Required over parity",
                f"{blocker.required_improvement:.2f}",
                border=True,
            )
            st.metric(
                "Walk margin",
                f"{blocker.kill_margin:.3f}" if blocker.kill_margin is not None else "—",
                border=True,
                help="Below 1 means the hug charge does not kill this length.",
            )
            st.metric("Status", blocker.status, border=True)
        st.caption(
            f"The obstruction is Diophantine: $|3^o-2^L|$ along the fan. "
            f"The next useful floor is about ${DK_BREAKEVEN_FLOOR:,}$; "
            "further $N_0$ campaigns are parked. This is not a halt theorem."
        )
    table = _lazy_expander(
        "Kill table at the printed floor",
        icon=":material/table:",
        key="juggler_walk_kills",
    )
    if table.open:
        with table:
            shown = [row for row in kills if row.length <= PRINTED_PERIOD]
            st.dataframe(
                pd.DataFrame(
                    [
                        {
                            "L": row.length,
                            "o": row.odd_count,
                            "required": round(row.required_improvement, 3),
                            "walk margin": (
                                None
                                if row.kill_margin is None
                                else round(row.kill_margin, 3)
                            ),
                            "status": row.status,
                        }
                        for row in shown
                    ]
                ),
                hide_index=True,
                width="stretch",
            )
            st.caption(
                f"{PRINTED_KILL_COUNT} lengths below {PRINTED_PERIOD:,} "
                "are walk-killed. Lengths above the blocker are "
                "finance-survivors, not candidate cycles."
            )
    later = _lazy_expander(
        "Finance survivors above the printed cutoff",
        icon=":material/more_horiz:",
        key="juggler_walk_beyond",
    )
    if later.open:
        with later:
            rest = [row for row in kills if row.length > PRINTED_PERIOD]
            st.dataframe(
                pd.DataFrame(
                    [
                        {
                            "L": row.length,
                            "o": row.odd_count,
                            "required": round(row.required_improvement, 3),
                            "status": row.status,
                        }
                        for row in rest
                    ]
                ),
                hide_index=True,
                width="stretch",
            )
            st.caption(
                "These lengths lie beyond Corollary 5.11. They are not "
                "open cycles."
            )


def _trajectory() -> None:
    _blurb("Trajectory")
    _proof_tags("J-itinerary-semantics")
    n = int(st.session_state.juggler_n)
    steps = int(
        st.slider(
            "Step cap",
            min_value=1,
            max_value=TRAJECTORY_STEPS_MAX,
            key="juggler_steps",
            help="Stop after this many steps, or sooner at 1.",
        )
    )
    view = walk_trajectory(n, steps)
    metrics = st.container(horizontal=True)
    with metrics:
        st.metric("Word so far", view.word or "—", border=True)
        st.metric("Steps", len(view.states) - 1, border=True)
        st.metric("Hit 1?", _yes_no(view.reached_one), border=True)
        st.metric("Last value", format_int(view.states[-1]), border=True)
    if view.too_large or view.bit_capped:
        st.warning(
            "A value got too big to display. The walk stopped.",
            icon=":material/warning:",
        )
    if n == 3 and view.states[: len(NOTE_TRAJECTORY_3)] == NOTE_TRAJECTORY_3:
        st.success("This is the note trajectory of 3: 3, 5, 11, 36, 6, 2, 1.", icon=":material/check:")
    if n == 37 and NOTE_PEAK_37 in view.states:
        st.success("The recorded peak of 37 is on this walk.", icon=":material/check:")
    chart_df = pd.DataFrame(view.rows)
    chart = (
        alt.Chart(chart_df)
        .mark_line(point=True)
        .encode(
            x=alt.X("step:Q", title="step"),
            y=alt.Y("state:Q", title="value", scale=alt.Scale(type="log")),
            color=alt.Color("parity:N", title="parity"),
            tooltip=["step", "state", "letter", "bits"],
        )
    )
    st.altair_chart(chart, width="stretch")
    with st.expander("Step table", icon=":material/table:"):
        st.dataframe(chart_df, hide_index=True, width="stretch")


def _envelope() -> None:
    _blurb("Envelope")
    _proof_tags("J-power-envelope-contraction", "J-global-defect-identity")
    n = int(st.session_state.juggler_n)
    word = _word_controls()
    view = envelope_view(n, word)
    metrics = st.container(horizontal=True)
    with metrics:
        st.metric("Odd letters", view.odd, border=True, help="How many O steps in the word.")
        st.metric("Regime", view.regime, border=True)
        st.metric(
            "Follows this word?",
            _yes_no(view.follows),
            border=True,
            help="Does the walk from n actually take these O/E steps?",
        )
        st.metric(
            "Image vs n",
            f"{format_int(view.image)} {view.compared} {n}" if view.image is not None else "—",
            border=True,
        )
    if not view.follows:
        st.warning(
            f"Letter {view.fail_index} fails at {view.fail_state}. "
            "The start is the wrong parity for that letter.",
            icon=":material/warning:",
        )
    slack_row = st.container(horizontal=True)
    with slack_row:
        if view.slack is not None:
            slack_value = format_int(view.slack)
        elif view.slack_too_large:
            slack_value = "too large"
        else:
            slack_value = "—"
        if view.delta is not None:
            delta_value = format_int(view.delta)
        elif view.delta_too_large:
            delta_value = "too large"
        else:
            delta_value = "—"
        st.metric(
            "Envelope slack Δ",
            slack_value,
            border=True,
            help="Room left under the proved power bound.",
        )
        st.metric(
            "Recurrence Δ",
            delta_value,
            border=True,
            help="The exact leftover after composing the steps.",
        )
        st.metric("Vanishing", view.vanishing, border=True)
    if view.follows and view.slack is not None and view.delta is not None:
        if view.slack == view.delta:
            st.success("The two Δ numbers match on this pair.", icon=":material/check:")
    if view.steps:
        with st.expander("Step-by-step slack", icon=":material/table:"):
            st.dataframe(pd.DataFrame(view.steps), hide_index=True, width="stretch")

    with st.expander("Split the word", icon=":material/content_cut:"):
        st.caption(
            "Cut the recipe in two. The leftover of the whole word is not "
            "just the sum of the two leftovers — it is a two-term power gap."
        )
        if not word:
            st.caption("Enter a nonempty word to split it.")
            return
        if st.session_state.juggler_split > len(word):
            st.session_state.juggler_split = len(word)
        split = int(
            st.slider(
                "Split after this many letters",
                min_value=0,
                max_value=len(word),
                key="juggler_split",
            )
        )
        composed = compose_view(n, word[:split], word[split:])
        if not composed.follows:
            st.caption("The concatenated word is not realized at this start.")
        elif composed.too_large:
            st.caption("The composition gaps are too large to show.")
        else:
            row = st.container(horizontal=True)
            with row:
                st.metric("Δ first half", composed.delta_u, border=True)
                st.metric("Δ second half", composed.delta_v, border=True)
                st.metric("Δ whole word", composed.delta_uv, border=True)
                st.metric(
                    "Compose formula",
                    composed.composed if composed.composed is not None else "—",
                    border=True,
                )
            if composed.composed is not None and composed.composed == composed.delta_uv:
                st.success("The two-term formula matches Δ of the whole word.", icon=":material/check:")


def _preimages() -> None:
    _blurb("Preimages and census")
    _proof_tags(*CENSUS_LEDGER_IDS)
    left, right = st.columns(2, gap="small")
    with left:
        with st.container(border=True, gap="small"):
            st.markdown("**Even one-step preimage**")
            st.caption("Even parents of an image sit in one square interval.")
            q = int(st.number_input("Image q", min_value=0, step=1, value=6, key="juggler_q"))
            cell = even_preimage_view(q)
            st.metric("Interval", f"[{cell.lo}, {cell.hi})", border=True)
            st.caption(f"{cell.even_count} even predecessors.")
            st.dataframe(
                pd.DataFrame({"even n": list(cell.evens)}),
                hide_index=True,
                width="stretch",
                height=160,
            )
            if cell.truncated:
                st.caption("List truncated.")
    with right:
        with st.container(border=True, gap="small"):
            st.markdown("**Odd one-step preimage**")
            st.caption("An odd image has at most one odd parent.")
            m = int(st.number_input("Image m", min_value=0, step=1, value=11, key="juggler_m"))
            odd = odd_preimage_view(m)
            st.metric("Odd parents", len(odd.integers), border=True)
            if odd.integers:
                st.dataframe(
                    pd.DataFrame({"odd n": list(odd.integers)}),
                    hide_index=True,
                    width="stretch",
                    height=160,
                )
            else:
                st.caption("Empty odd one-step preimage.")

    with st.expander("Word playground", icon=":material/tune:"):
        st.caption(
            "Classify a short word, then test the next-square prefix from "
            "the shared start n."
        )
        word = _word_controls()
        info = classify_word(word)
        kind_row = st.container(horizontal=True)
        with kind_row:
            st.metric("Expanding?", _yes_no(info.expanding), border=True)
            st.metric("Ends even?", _yes_no(info.even_terminating), border=True)
            st.metric("Kind", info.kind, border=True)
        st.caption(info.reason)
        n = int(st.session_state.juggler_n)
        prefix = st.segmented_control(
            "Next-square prefix",
            ["OO", "OOO"],
            default="OO",
            key="juggler_prefix",
        )
        if prefix is None:
            prefix = "OO"
        square = next_square_view(n, prefix)
        sq_row = st.container(horizontal=True)
        with sq_row:
            st.metric("Follows prefix?", _yes_no(square.follows), border=True)
            st.metric(
                "Image",
                format_int(square.image) if square.image is not None else "—",
                border=True,
            )
            st.metric("Threshold (n+1)²", square.threshold, border=True)
            st.metric("Image ≥ threshold?", _yes_no(square.met), border=True)

    with st.expander("Leftover tables", icon=":material/table:"):
        st.caption(
            "Replay the finite checks under the cutoff. "
            "Lemma 3.5 uses 2 ≤ n < 256. Lemma 3.7 uses 2 ≤ n < 14. "
            "These are tables, not a halt proof."
        )
        with st.form("juggler_leftover_form", border=False):
            leftover = st.selectbox(
                "Leftover word",
                leftover_words(),
                index=0,
                key="juggler_leftover",
            )
            submitted = st.form_submit_button("Replay leftover table", icon=":material/table:")
        if submitted:
            table = leftover_table(leftover)
            hits = st.container(horizontal=True)
            with hits:
                st.metric("Checked", table.checked, border=True)
                st.metric("Followed the word", table.follows, border=True)
                st.metric("Returned to n", len(table.hits), border=True)
                st.metric("Cutoff n", table.n_hi, border=True)
            if table.hits:
                st.error(f"Unexpected return at {table.hits}.", icon=":material/block:")
            else:
                st.success(
                    f"No return on 2 ≤ n < {table.n_hi} for {table.word}.",
                    icon=":material/check:",
                )
            st.dataframe(pd.DataFrame(table.rows), hide_index=True, width="stretch")
        else:
            st.caption(
                "Submit to evaluate "
                + ", ".join(f"{word} below {cut}" for word, cut in LEFTOVER_CUTOFF.items())
                + "."
            )

    census = _lazy_expander(
        "Census inventory",
        icon=":material/inventory_2:",
        key="juggler_census",
    )
    if census.open:
        with census:
            st.caption(
                "Every even-ending expanding word of length at most 8, and why "
                "it cannot be a loop. Theorem 3.22 gives four evens, hence "
                "period ≥ 11; Theorem 4.6 then excludes every period ≤ 25780."
            )
            st.dataframe(
                pd.DataFrame(census_inventory()),
                hide_index=True,
                width="stretch",
            )
            st.markdown("**Length-eight expanding even-terminating words**")
            st.caption(
                "Two-even leftovers of length eight are Theorem 3.12. The "
                "square spellings OOOOEOOE and OOOEOOOE are OO/OOO bootstrap, "
                "not leftovers."
            )
            st.dataframe(
                pd.DataFrame(length_eight_status_rows()),
                hide_index=True,
                width="stretch",
            )


def _descent() -> None:
    _blurb("Descent")
    _proof_tags("J-finite-progress-boundary")
    n = int(st.session_state.juggler_n)
    view = descent_view(n)
    bucket_plain = {
        "EVEN_PROGRESS": "even start — drops in one E",
        "OE_PROGRESS": "odd-to-even — drops in OE",
        "ODD_ODD": "odd-to-odd leftover",
    }.get(view.bucket, view.bucket)
    row = st.container(horizontal=True)
    with row:
        st.metric("This n", bucket_plain, border=True)
        st.metric("Short certificate", view.certificate, border=True)
    if view.residual:
        with st.expander("Residual after the first even", icon=":material/more_horiz:"):
            st.dataframe(pd.DataFrame([view.residual]), hide_index=True, width="stretch")

    window = int(
        st.slider(
            "Count starts up to",
            min_value=2,
            max_value=DESCENT_WINDOW_MAX,
            value=80,
            key="juggler_window",
        )
    )
    counts = descent_window(window)
    st.dataframe(
        pd.DataFrame(
            [
                {
                    "even": counts["EVEN_PROGRESS"],
                    "odd-to-even": counts["OE_PROGRESS"],
                    "odd-to-odd leftover": counts["ODD_ODD"],
                    "n_max": counts["n_max"],
                }
            ]
        ),
        hide_index=True,
        width="stretch",
    )
    st.caption("Bounded window counts only. Not a density theorem.")

    with st.expander("Four-block chain at 1999", icon=":material/link:"):
        st.caption(
            "One example of four expanding blocks in a row. It is not a "
            "uniform run bound."
        )
        chain = four_block_replay()
        st.dataframe(
            pd.DataFrame(
                [
                    {
                        "start": step.start,
                        "word": step.word,
                        "image": step.image,
                        "followed the word": step.follows,
                        "matches note": step.matches,
                    }
                    for step in chain
                ]
            ),
            hide_index=True,
            width="stretch",
        )
        if all(step.matches for step in chain):
            st.success(
                "1999 —OOE→ 5169 —OOOOEE→ 50093 —OOE→ 193753 —OOE→ 887471.",
                icon=":material/check:",
            )


def _cycle_words() -> None:
    _blurb("Cycle words")
    _proof_tags(
        "J-cycle-finite-structure",
        "J-even-count-le-three",
        "J-cycle-word-eliahou-leftover-instance",
        "J-gapped-cycle-word-ee",
    )
    word = _cycle_word_controls()
    if len(word) >= 2:
        if st.session_state.juggler_cycle_shift >= len(word):
            st.session_state.juggler_cycle_shift = 0
        st.session_state.juggler_cycle_slider = int(st.session_state.juggler_cycle_shift)

        def _sync_slider() -> None:
            st.session_state.juggler_cycle_shift = int(
                st.session_state.juggler_cycle_slider
            )

        def _rotate_left() -> None:
            nxt = (int(st.session_state.juggler_cycle_shift) + 1) % len(word)
            st.session_state.juggler_cycle_shift = nxt
            st.session_state.juggler_cycle_slider = nxt

        def _rotate_right() -> None:
            nxt = (int(st.session_state.juggler_cycle_shift) - 1) % len(word)
            st.session_state.juggler_cycle_shift = nxt
            st.session_state.juggler_cycle_slider = nxt

        rotate_row = st.container(horizontal=True, vertical_alignment="bottom", gap="small")
        with rotate_row:
            st.button(
                "Rotate left",
                icon=":material/rotate_left:",
                key="juggler_rot_left",
                on_click=_rotate_left,
                help="Same loop, started one letter later.",
            )
            st.button(
                "Rotate right",
                icon=":material/rotate_right:",
                key="juggler_rot_right",
                on_click=_rotate_right,
            )
            shift = int(
                st.slider(
                    "Left rotation",
                    min_value=0,
                    max_value=len(word) - 1,
                    key="juggler_cycle_slider",
                    on_change=_sync_slider,
                    help="The same cyclic class; only the base letter changes.",
                )
            )
        st.session_state.juggler_cycle_shift = shift
    else:
        shift = 0
    view = cycle_class_view(word, shift)
    metrics = st.container(horizontal=True)
    with metrics:
        st.metric("This spelling", view.current or "—", border=True)
        st.metric("Odds / evens", f"{view.odd} / {view.even}", border=True)
        st.metric("Expanding?", _yes_no(view.expanding), border=True)
        st.metric(
            "This loop",
            "cannot exist" if view.verdict == "excluded" else view.verdict,
            border=True,
        )
    if view.verdict == "excluded":
        st.error(view.verdict_reason, icon=":material/block:")
    elif view.verdict == "open":
        st.warning(view.verdict_reason, icon=":material/help:")
    else:
        st.info("Enter a nonempty O/E word.", icon=":material/info:")

    spelling, trial_col = st.columns(2, gap="small")
    with spelling:
        with st.container(border=True, gap="small"):
            st.markdown("**This spelling**")
            st.caption("One way of writing the loop, after the current rotation.")
            st.metric("Kind", view.current_kind, border=True)
            st.metric("Legal CycleMin?", _yes_no(view.current_legal), border=True)
            st.metric("Blocked by", view.current_blocked_by or "—", border=True)
            st.caption(view.current_reason)
    with trial_col:
        with st.container(border=True, gap="small"):
            st.markdown("**Try at the shared start n**")
            st.caption(
                "If this spelling were a loop at n, the image after the "
                "word would equal n. A miss here is only a witness at this n."
            )
            trial = try_cycle_word(int(st.session_state.juggler_n), view.current)
            st.metric("Followed the word?", _yes_no(trial.follows), border=True)
            st.metric(
                "Image",
                format_int(trial.image) if trial.image is not None else "—",
                border=True,
            )
            st.metric("Returned to n?", _yes_no(trial.returned), border=True)
            if trial.bit_capped:
                st.warning(
                    "A value got too big to display. The walk stopped.",
                    icon=":material/warning:",
                )
            elif not trial.follows and trial.fail_index is not None:
                st.caption(
                    f"Letter {trial.fail_index} fails at "
                    f"{format_int(trial.fail_state) if trial.fail_state is not None else '—'}."
                )
            elif trial.returned and trial.word:
                st.error(
                    "Unexpected return at this n. The recorded census claims none.",
                    icon=":material/block:",
                )
            elif trial.follows and trial.word:
                st.success(
                    "This spelling is realized at n and does not return.",
                    icon=":material/check:",
                )

    why = _lazy_expander(
        "Why this loop is excluded",
        icon=":material/rule:",
        key="juggler_why",
    )
    if why.open:
        with why:
            st.caption("The census argument, one filter at a time.")
            st.dataframe(
                pd.DataFrame(
                    [
                        {
                            "check": step.title,
                            "status": step.status,
                            "why": step.body,
                        }
                        for step in view.steps
                    ]
                ),
                hide_index=True,
                width="stretch",
            )

    rotations = _lazy_expander(
        "All rotations",
        icon=":material/360:",
        key="juggler_rotations",
    )
    if rotations.open:
        with rotations:
            st.caption("Every starting letter of the same loop.")
            st.dataframe(
                pd.DataFrame(
                    [
                        {
                            "shift": row.shift,
                            "word": row.word,
                            "ends E": row.even_terminating,
                            "expanding": row.expanding,
                            "CycleMin": row.legal_cyclemin,
                            "blocked by": row.blocked_by or "—",
                            "kind": row.kind,
                            "why": row.reason,
                            "selected": row.selected,
                        }
                        for row in view.rotations
                    ]
                ),
                hide_index=True,
                width="stretch",
            )


def _open_cycle_word(word: str) -> None:
    st.session_state.juggler_cycle_word = word
    st.session_state.juggler_cycle_shift = 0
    st.session_state.juggler_cycle_slider = 0
    st.session_state.juggler_goto_cycle = True


def _leftover_families() -> None:
    _blurb("Leftover families")
    _proof_tags(*LEFTOVER_FAMILY_LEDGER_IDS)
    cards = st.container(horizontal=True)
    with cards:
        st.metric("Even letters ≤ 3", "ruled out", border=True)
        st.metric("Period ≤ 25780", "excluded by Theorem 4.6", border=True)
        st.metric("Lab leftover spellings", "30", border=True)
        st.metric("Arrival at 1", "not claimed", border=True)

    with st.container(border=True, gap="small"):
        st.markdown("**Inspect a length-11 spelling**")
        st.caption(
            "Each of these is a surviving CycleMin spelling for the local "
            "cells, so rotation cannot kill it. Period 11 is already "
            "excluded by Theorem 4.6. Open one in Cycle words to spin it."
        )
        inventory = length11_inventory()
        words = [row["word"] for row in inventory]
        default = words.index(EEEE_WORD) if EEEE_WORD in words else 0
        chosen = st.selectbox(
            "Length-11 leftover",
            words,
            index=default,
            key="juggler_length11_word",
        )
        inspect = st.container(horizontal=True)
        with inspect:
            st.metric("Spelling", chosen, border=True)
            st.metric(
                "Family",
                next(row["family"] for row in inventory if row["word"] == chosen),
                border=True,
            )
            st.metric(
                "Cell",
                EEEE_THRESHOLD if chosen == EEEE_WORD else "Z4 pullback",
                border=True,
            )
        st.button(
            "Open in cycle words",
            icon=":material/rotate_right:",
            key="juggler_open_length11",
            on_click=_open_cycle_word,
            args=(chosen,),
        )

    leftovers = _lazy_expander(
        "The thirty first-expanding lab leftovers",
        icon=":material/table:",
        key="juggler_length11",
    )
    if leftovers.open:
        with leftovers:
            st.caption(
                f"{EEEE_WORD} is the sharp r=4 cell {EEEE_THRESHOLD}, first at "
                f"n={EEEE_N0:,}. That n is N0: the first start where the cell holds."
            )
            st.dataframe(pd.DataFrame(inventory), hide_index=True, width="stretch")

    with st.expander("Lab decisions", icon=":material/gavel:"):
        st.dataframe(pd.DataFrame(LAB_LEFTOVER_DECISIONS), hide_index=True, width="stretch")

    with st.expander("Why the local cells miss these 30", icon=":material/help:"):
        gate = st.container(horizontal=True)
        with gate:
            with st.container(border=True, gap="small"):
                st.markdown("**EEEE last-cluster**")
                st.caption(
                    f"`{EEEE_WORD}` uses the r=4 trailing-even cell. "
                    f"Ideal cell {EEEE_THRESHOLD}; first fire n={EEEE_N0:,}."
                )
            with st.container(border=True, gap="small"):
                st.markdown("**Internal-E next-square**")
                st.caption(
                    f"Closest suffix `{BEST_V}` on `{INTERNAL_E_WORD}` is "
                    f"{INTERNAL_E_MARGIN}. At m={SPOT_WITNESS:,} the image "
                    "still undershoots (m+1)²."
                )
            with st.container(border=True, gap="small"):
                st.markdown("**Rotation**")
                st.caption(
                    "These thirty words are the CycleMin spellings the "
                    "local cells miss, in 30 distinct necklaces. They are "
                    "not Paper A open cycles."
                )


def juggler_finite_dynamics_page() -> None:
    _init_state()
    if st.session_state.pop("juggler_goto_cycle", False):
        st.session_state.juggler_view = "Cycle words"
    st.caption(
        "Companion to Paper A: local word obstructions plus finance give "
        f"period ≥ {PAPER_PERIOD:,} at $N_0=10^6$; the walk-charge "
        f"envelope at the third certified floor $N_0={PRINTED_FLOOR:,}$ "
        f"prints period ≥ {PRINTED_PERIOD:,} (Corollary 5.11). Lean is "
        "the authority through Theorem 4.4; the numerical cutoffs are "
        "verified computations. Arrival at 1 is not claimed."
    )
    _glossary()
    view = st.segmented_control(
        "View",
        VIEWS,
        key="juggler_view",
        format_func=lambda name: VIEW_LABEL.get(name, name),
        label_visibility="collapsed",
        persist_state="session",
    )
    if view is None:
        view = "Trajectory"
    if view in VIEWS_WITH_START:
        _n_controls()
    if view == "Claim map":
        _claim_map()
    elif view == "Finance":
        _finance()
    elif view == "Walk charge":
        _walk_charge()
    elif view == "Trajectory":
        _trajectory()
    elif view == "Envelope":
        _envelope()
    elif view == "Preimages and census":
        _preimages()
    elif view == "Cycle words":
        _cycle_words()
    elif view == "Leftover families":
        _leftover_families()
    else:
        _descent()


juggler_finite_dynamics_page()
