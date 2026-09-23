"""Balanced-ternary warp / Collatz commutator commands."""

from __future__ import annotations

from research.collatz.warp import (
    palindrome_along_trajectory,
    preserved_counterexamples,
    warp_state,
    warped_trajectory,
)
from research.experiments.paths import collatz_data_dir


def _warp(n: int) -> int:
    state = warp_state(n)
    print("Balanced-ternary warp  [EXACT; T only on positive odds]")
    print(f"n={state.n}  BT(n)={state.bt_n}  palindrome={state.palindrome_n}")
    print(f"W(n)={state.W_n}  BT(W(n))={state.bt_W}")
    print(f"T defined={str(state.t_defined).lower()}  T(n)={state.T_n}")
    print(f"W(T(n))={state.W_T}")
    print(
        f"T(W(n)) defined={str(state.t_of_W_defined).lower()}  "
        f"T(W(n))={state.T_W}"
    )
    print(f"Comm_WT={state.Comm_WT}")
    print(
        f"s3(n)={state.s3_n}  s3(T(n))={state.s3_T}  "
        f"delta_s={state.delta_s}  [delta_s = s3(T)-s3(n)-1]"
    )
    print(
        f"L3(n)={state.L3_n}  L3(T(n))={state.L3_T}  delta_L={state.delta_L}"
    )
    print("W is A134028; it is not an involution when 3 divides n ≠ 0.")
    return 0


def _warp_census(limit: int, write: bool, identity_length: int) -> int:
    from research.collatz.experiments.bt_warp import run_bt_warp_census

    output = collatz_data_dir() if write else None
    result = run_bt_warp_census(
        limit, identity_length=identity_length, output_dir=output
    )
    census = result.census
    print("BT warp commutator census  [COMPUTATIONALLY VERIFIED]")
    print(f"limit={result.limit}  odds={census['odd_count']}  schema={result.schema_version}")
    print(
        f"commutator defined={census['commutator_defined']}  "
        f"zero={census['commutator_zero']}  nonzero={census['commutator_nonzero']}"
    )
    print(
        f"defined density among odds={census['defined_density_among_odds']:.6f}  "
        f"zero density among defined={census['zero_density_among_defined']:.6f}"
    )
    print(f"smallest defined={census['smallest_defined']}  smallest zero={census['smallest_zero']}")
    print(f"smallest nonzero={census['smallest_nonzero']}")
    print(
        f"delta_L range=[{census['delta_L_min']}, {census['delta_L_max']}]  "
        "(integer length change, not log3 2)"
    )
    for record in result.identities["naive_identities"]:
        print(
            f"  {record['name']}: counterexample={record['smallest_counterexample']}  "
            f"{record['status']}"
        )
    if result.paths:
        print(f"outputs: {result.paths}")
    return 0


def _warp_realizer(ks: str) -> int:
    from research.collatz.warp import realizer_warp_row

    row = realizer_warp_row(ks)
    print("Warp of a canonical realizer  [EXACT ROW]")
    print(f"itinerary={row['itinerary']}  R={row['R']}  BT(R)={row['BT(R)']}")
    print(f"W(R)={row['W(R)']}  next_k={row['next_k']}  lift_digit={row['lift_digit']}")
    print(
        f"W(R)=R(reverse itinerary)? {row['W_R_equals_R_reverse']}  "
        f"R_reverse={row['R_reverse_itinerary']}"
    )
    print(
        f"W(R)=R(tail-reverse itinerary)? {row['W_R_equals_R_tail']}  "
        f"R_tail={row['R_tail_itinerary']}"
    )
    print("Finite agreement is not a theorem; counterexamples are preserved.")
    return 0


def _warp_realizer_census(max_length: int, max_k: int, write: bool) -> int:
    from research.collatz.experiments.bt_warp import run_bt_warp_realizer

    output = collatz_data_dir() if write else None
    result = run_bt_warp_realizer(max_length, max_k, output_dir=output)
    report = result.report
    print("Canonical-realizer warp census  [BOUNDED COMPUTATION]")
    print(f"rows={result.report['row_count']} schema={result.schema_version}")
    print(
        f"reverse-itinerary hits={report['reverse_itinerary_hits']}  "
        f"tail-itinerary hits={report['tail_itinerary_hits']}"
    )
    print(f"smallest reverse counterexample={report['smallest_reverse_counterexample']}")
    print(f"smallest tail counterexample={report['smallest_tail_counterexample']}")
    if result.paths:
        print(f"outputs: {result.paths}")
    return 0


def _warp_semigroup(max_length: int, sample_limit: int) -> int:
    from research.collatz.experiments.bt_warp import semigroup_agreement_sample

    result = semigroup_agreement_sample(max_length, sample_limit)
    print("Composition semigroup of T, W, Wt  [BOUNDED SAMPLE]")
    print(
        f"max_length={result['max_length']}  words={result['word_count']}  "
        f"sample odds <= {result['sample_limit']}"
    )
    print(f"clusters={result['cluster_count']}")
    print(f"W W vs id counterexample={result['W_W_counterexample']}")
    print(f"Wt Wt vs id counterexample={result['Wt_Wt_counterexample']}")
    print("Sample agreement is not an identity theorem.")
    return 0


def _warp_palindrome(n: int, max_steps: int) -> int:
    rows = palindrome_along_trajectory(n, max_steps)
    print("Palindrome flags along T  [EXACT FLAGS ON A BOUNDED ORBIT]")
    print(f"start={n}  steps={len(rows) - 1}")
    for row in rows[:30]:
        print(f"  n={row['n']}  BT={row['BT(n)']}  palindrome={row['palindrome']}")
    pal = sum(1 for row in rows if row["palindrome"])
    print(f"palindrome count={pal}/{len(rows)}")
    return 0


def _warp_trajectory(n: int, max_steps: int) -> int:
    state = warp_state(n)
    warped = warped_trajectory(n, max_steps)
    print("Warped trajectory n -> W(n) -> T(W(n)) -> ...")
    print(f"start={n}  W(n)={warped.W_start}  t_started={warped.t_started}")
    print(f"values={list(warped.values)}")
    print(f"pair (n, W(n))=({n}, {state.W_n})")
    print(f"truncated={warped.truncated}")
    return 0


def _warp_counterexamples() -> int:
    print("Preserved counterexamples to naive W/T identities")
    for name, record in preserved_counterexamples().items():
        print(f"  {name}: {record}")
    return 0
