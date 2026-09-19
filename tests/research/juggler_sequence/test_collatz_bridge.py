"""The Juggler/Collatz bridge: verified both ways, and the audit it forces."""

from __future__ import annotations

import json
import math
from fractions import Fraction

import pytest

from research.juggler_sequence.collatz_bridge import (
    CLASS_BRIDGE,
    barren_chain_is_backward_closed,
    collatz_backward_log_mass,
    collatz_preimages,
    collatz_theorem_one_counterexample,
    contagion_mgf_shift,
    even_block_log_mass,
    ideal_coefficient,
    log_mass_census,
    collatz_is_proposition_j_at_delta_one,
    density_exponent,
    good_set_wiener_norm,
    walsh_conversion_penalty,
    JSON_PATH,
    STEP_EVEN,
    STEP_ODD,
    big_log,
    collatz,
    collatz_reachable,
    juggler,
    loglog_increments,
    parity_map_is_bijective,
    parity_word,
    probe_payload,
    undecided_classes,
)
from research.juggler_sequence.jump_spectrum import survivor_counts
from research.juggler_sequence.lean_paths import REPO_ROOT


def test_the_two_walks_have_the_same_steps() -> None:
    """`log(3/2)` and `-log 2`, on `log x` for Collatz and `log log n` for Juggler."""
    assert STEP_ODD == pytest.approx(math.log(1.5), abs=1e-15)
    assert STEP_EVEN == pytest.approx(-math.log(2.0), abs=1e-15)
    # the drift is the same too, which is why both have the same survival rate
    assert 0.5 * (STEP_ODD + STEP_EVEN) == pytest.approx(0.5 * math.log(0.75), abs=1e-15)


def test_juggler_increments_hit_those_steps_from_a_large_seed() -> None:
    """The floor costs `O(1)` in `n`, so the agreement is only as good as `n` is large.

    At `n = 7` the error is a percent; from twenty-one digits it is at the last bit.
    Asserting both keeps the size condition visible instead of implied.
    """
    small = loglog_increments(7, steps=2, floor=3)
    assert small and max(abs(m - t) for _, m, t in small) > 1e-3

    large = loglog_increments(10**20 + 1, steps=2)
    assert len(large) == 2
    assert max(abs(m - t) for _, m, t in large) < 1e-14


def test_big_log_survives_values_past_the_float_range() -> None:
    """Juggler values are doubly exponential, so `float(n)` is not an option.

    A seed can still descend -- `10^20 + 1` reaches eight digits in three steps -- so
    the guard is tested on a value chosen to be large rather than on an orbit.
    """
    n = 10**400
    with pytest.raises(OverflowError):
        float(n)
    assert big_log(n) == pytest.approx(400 * math.log(10), rel=1e-12)
    assert big_log(7) == pytest.approx(math.log(7), rel=1e-15)


def test_the_parity_map_is_bijective_which_juggler_has_no_analogue_of() -> None:
    """Terras. This is the asymmetry: Collatz's word statistics are free, Juggler's
    are Hypothesis FD."""
    for depth in (4, 6, 8):
        assert parity_map_is_bijective(depth), depth
    assert parity_word(1, 4) == (1, 0, 1, 0)   # 1 -> 2 -> 1 -> 2
    assert collatz(7) == 11 and collatz(8) == 4


def test_the_survivor_count_is_the_undecided_collatz_class_count() -> None:
    """Checked by running Collatz, not by quoting OEIS.

    A class whose word has already dropped gives every member the same stopping time;
    a class whose word never drops does not. The second kind is counted by `N_d`.
    """
    counts = survivor_counts(10)
    for depth in range(4, 11):
        assert undecided_classes(depth) == counts[depth], depth
    assert [counts[d] for d in range(4, 11)] == [3, 4, 8, 13, 19, 38, 64]


def test_the_audit_separates_shared_results_from_juggler_ones() -> None:
    """Results that use only word densities belong to Collatz too.

    This is the uncomfortable half of the identification and the reason it is recorded:
    a Juggler-shaped wording does not make a claim Juggler-specific.
    """
    assert collatz_reachable("the survivor count recursion N_(d+1) + M_(d+1) = 2 N_d")
    assert collatz_reachable("the jump spectrum amplitude a_1")
    assert collatz_reachable("the certificate word count at each barrier")
    assert not collatz_reachable("Hypothesis FD gives equidistribution of parity words")
    assert not collatz_reachable("the Weyl differencing kernel bound")


def test_committed_artifact_records_the_bridge_and_its_limits() -> None:
    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["decision"]["classification"] == CLASS_BRIDGE
    assert data["shared_count"]["agree"] is True
    assert data["shared_walk"]["worst_increment_error"] < 1e-8
    text = data["anti_overclaim"]
    assert "not an equivalence and not a conjugacy" in text
    assert "moves no bound in either problem" in text
    assert "not an easier Collatz" in text


def test_a_cheap_run_reaches_the_same_answer() -> None:
    payload = probe_payload(max_depth=7)
    assert payload["decision"]["classification"] == CLASS_BRIDGE
    assert payload["shared_count"]["agree"] is True


def test_proposition_j_on_collatz_is_terras() -> None:
    """The calibration. `E_d(N) = O(1)` is the `delta = 1` case, and it gives Terras.

    If this ever stops holding, the claim that FD buys Juggler exactly Collatz-parity
    stops holding with it, and the roadmap it implies goes too.
    """
    terras = collatz_is_proposition_j_at_delta_one()
    assert terras["delta"] == 1.0
    assert terras["density_exponent"] == pytest.approx(0.050044, abs=1e-6)
    assert terras["non_descenders"] == pytest.approx(0.949956, abs=1e-6)


def test_fd_buys_a_delta_fraction_of_that() -> None:
    """The density exponent is linear in `delta`, so FD is a fraction of Terras."""
    full = density_exponent(1.0)
    for delta in (1.0, 0.5, 1 / 24, 1 / 96):
        assert density_exponent(delta) == pytest.approx(delta * full, rel=1e-12)
    # reaching even N^0.99 needs delta near 1/5, far past what is proved at depth four
    assert density_exponent(1 / 96) < 0.01 < density_exponent(0.2)


def test_the_union_bound_costs_twenty_times_the_exponent_work() -> None:
    """Where Proposition J's loss sits.

    Combining the `N_d` word classes better is worth about `20x`; improving the
    exponent from `1/96` to `1/72` is worth `1.33x`. A direct estimate at the printed
    exponent beats a union bound at `delta = 1/5`.
    """
    union = density_exponent(1.0, "union")
    sqrt_ = density_exponent(1.0, "sqrt")
    direct = density_exponent(1.0, "direct")
    assert union < sqrt_ < direct
    assert sqrt_ / union == pytest.approx(1.90, abs=0.02)
    assert direct / union == pytest.approx(19.98, abs=0.05)
    assert direct / union > 96 / 72 * 10, "the combination step must dominate"
    assert density_exponent(1 / 96, "direct") > density_exponent(0.2, "union")
    with pytest.raises(ValueError):
        density_exponent(0.5, "wishful")


def test_the_wiener_norm_comes_from_the_library_not_from_new_code() -> None:
    """`bad_set_spectrum(d, 0.0)` has computed this since the Paper C collision branch.

    A fresh transform was written for it anyway -- the fifth duplication in a week. The
    guard is that the library path keeps reproducing the values, so nobody writes a
    sixth.
    """
    for depth, expected in ((8, 2.906250), (12, 6.316406),
                            (16, 17.114990), (20, 44.315536)):
        assert good_set_wiener_norm(depth) == pytest.approx(expected, abs=1e-5), depth


def test_the_walsh_route_is_worse_under_the_hypothesis_we_actually_have() -> None:
    """The decisive fact, and the reason `J-proposition-j-loss-is-the-union-bound` fell.

    `E_d <= max_(S != 0)|W_S| <= 2^d E_d`, both ends attained. A Walsh estimate needs the
    second bound; Proposition J supplies the first. The conversion costs `2^d`, so the
    route loses by a factor growing like `1.44^d` instead of winning by 20.
    """
    counts = survivor_counts(20)
    penalties = {d: walsh_conversion_penalty(counts, d) for d in (12, 16, 20)}
    assert penalties[12] == pytest.approx(114.5, rel=0.02)
    assert penalties[20] == pytest.approx(1700.4, rel=0.02)
    for d in (12, 16, 20):
        assert penalties[d] > 1.0, "the route must be recorded as losing, not winning"
    growth = (penalties[20] / penalties[12]) ** (1 / 8)
    assert growth == pytest.approx(1.40, abs=0.03), "penalty grows like (gamma/theta)^d"


def test_parseval_caps_the_gain_so_the_direct_reading_was_never_available() -> None:
    """`||ghat||_1 <= sqrt(N_d)` is a theorem, so `gamma <= sqrt(2 theta)` and the
    `direct` column of the old table was unreachable from the start."""
    counts = survivor_counts(20)
    for d in (8, 12, 16, 20):
        assert good_set_wiener_norm(d) <= counts[d] ** 0.5 + 1e-9, d
    assert density_exponent(1.0, "sqrt") < density_exponent(1.0, "direct")


def test_the_free_step_lemma_holds_in_the_direction_it_is_proved() -> None:
    """At a free step the Wiener norm does not move, and the proof is one line:
    `Good_d = Good_(d-1) x {0,1}`, so `ghat_d(S,1) = 0` and the L1 norm is unchanged.

    The converse is FALSE and the test says so: `d = 5` is not free -- `N_5 = 4` against
    `2 N_4 = 6` -- yet the norm still does not move. So a repeated value is evidence of
    a free step and not proof of one, and an earlier wording here claiming the lemma
    accounts for "every repeated value" was too strong.
    """
    counts = survivor_counts(22)
    unexplained = []
    for d in range(3, 23):
        free = counts[d] == 2 * counts[d - 1]
        same = abs(good_set_wiener_norm(d) - good_set_wiener_norm(d - 1)) < 1e-12
        if free:
            assert same, f"d={d}: free step must leave the Wiener norm exactly unchanged"
        elif same:
            unexplained.append(d)
    assert unexplained == [5], f"the only non-free plateau should be d=5, got {unexplained}"


def test_winklers_sandwich_holds_on_the_laboratory_counts() -> None:
    """A Collatz-side import: Winkler's 2026 rational-Catalan bounds on A100982 hold on `M_d`.

    `(1/n) C(m_n - 1, n - 1) <= M_{A020914(n)} <= (1/n) C(m_n, n - 1)` for every order checked,
    with equality exactly at his record minima and maxima of `{n log2 3}` -- the one-sided
    convergents. It confirms, from the Collatz literature, the Sturmian structure this laboratory
    reads on the same words, and it pins `M` only to a factor `2.7`: nothing about the
    `d^(-3/2)` or the prefactor follows from it.
    """
    from research.juggler_sequence.collatz_bridge import winkler_sandwich

    w = winkler_sandwich(2213)
    assert w["holds"] and w["lengths_are_a020914"] and w["nonzero_lengths"] == 2214
    assert w["a100982_head"] == [1, 1, 2, 3, 7, 12, 30, 85, 173, 476, 961, 2652]
    assert w["lower_equality"] == [1, 2, 7, 12, 53, 359, 665]
    assert w["upper_equality"] == [1, 3, 5, 17, 29, 41, 94, 147, 200, 253, 306, 971, 1636]
    assert w["lower_matches_record_minima"] and w["upper_matches_record_maxima"]

def test_the_collatz_analogue_of_theorem_one_is_false_by_exhibit() -> None:
    """`{3 * 2^k}`, and the reason the working notes gave was the wrong one.

    Paper C's Theorem 1 says every nonempty backward-closed set has divergent
    logarithmic count. For accelerated Collatz that is false, and not by a
    delicate estimate: multiples of three have no odd preimage, because
    `2(3 * 2^k) - 1` is `2 mod 3`. So `{3 * 2^k}` is backward-closed, infinite,
    counted by `log_2 x`, and has reciprocal sum exactly `2/3`.

    Three working artifacts instead said the analogue fails "because Collatz
    backward trees are thin (x^0.84, Krasikov--Lagarias)". `x^0.84` is a LOWER
    bound on preimage counts; it cannot establish thinness of anything, and
    conjecturally the tree is everything. The published manuscript never said
    it -- `juggler_fate_almost_all_note.md` says only that an `x^0.84` lower
    bound is compatible with a bounded reciprocal sum, which is right.
    """
    c = collatz_theorem_one_counterexample(60)
    assert c["backward_closed"]
    assert c["reciprocal_sum"] == pytest.approx(2 / 3, abs=1e-12)
    assert barren_chain_is_backward_closed(200)
    # the chain is exactly the multiples of three with no odd parent
    for k in range(20):
        assert collatz_preimages(3 * 2**k) == [3 * 2 ** (k + 1)]


def test_the_dichotomy_is_log_mass_not_fibre_thickness() -> None:
    """Juggler is critical uniformly; Collatz is critical on average only.

    The fibre *counts* differ hugely -- `|J^-1(m)|` grows like `m`, `|C^-1(m)|`
    is at most two -- but that is not what the contagion recursion consumes. It
    consumes harmonic mass, and there the two are much closer than the counts
    suggest: both are critical in the mean, at exactly `1/m`.

    What separates them is the worst case. Juggler's even block gives exactly
    `1/m` for *every* `m` with no exceptions; accelerated Collatz gives `1/(2m)`
    on two residues in three, and Theorem 1 quantifies over every backward-closed
    set, so the worst case governs and the mean is irrelevant. The previous
    session's reason for the failure -- "Collatz has no fat fibres" -- was the
    wrong invariant, and this test is what replaces it.
    """
    census = log_mass_census(20_000)
    assert census["collatz_mean"] == pytest.approx(1.0, abs=1e-3)
    assert census["collatz_min"] == pytest.approx(0.5, abs=1e-15)
    assert census["collatz_min_is_on_multiples_of_three"]
    # the worst case is exactly a half, and it is attained on every multiple of 3
    for m in (3, 6, 9, 300, 3000):
        assert collatz_backward_log_mass(m) == Fraction(1, 2)
    # Juggler's block is exactly 1/m in the limit and never below it
    for m in (10, 100, 1000, 5000):
        mass = even_block_log_mass(m)
        assert mass >= 1
        assert float(mass) == pytest.approx(1.0, abs=4.0 / m)


def test_the_ideal_coefficient_is_three_to_the_minus_odd_count() -> None:
    """`c_w = 2^(-|w|)/rho_w = 3^(-b(w))`, and it reproduces Paper C's table.

    Exact algebra: `2^(-(a+b)) * 2^a * (2/3)^b = 3^(-b)`. The coefficient is
    blind to everything about the word except how many odd letters it has, and
    `3^(-b)` is the probability that the Collatz backward step along `w` exists
    -- the `b`-fold divisibility by three. Juggler is handed as fibre geometry
    what Collatz must pay for arithmetically.
    """
    assert ideal_coefficient("E") == 1
    assert ideal_coefficient("OE") == Fraction(1, 3)
    assert ideal_coefficient("OEE") == Fraction(1, 3)
    assert ideal_coefficient("OOEE") == Fraction(1, 9)
    assert ideal_coefficient("OOEEE") == Fraction(1, 9)

    # The V_k ladder is printed AT ideal, not below it. Paper C gives
    # c_k = 3^(-k) for V_k = (OE)^(k-1) OEE (note line 1470), and b(V_k) = k, so
    # every coefficient the paper prints equals the Collatz-side ideal exactly.
    for k in range(1, 7):
        word = "OE" * (k - 1) + "OEE"
        assert word.count("O") == k, word
        assert ideal_coefficient(word) == Fraction(1, 3) ** k, word

    # The 3^(-(k+1)) that reaches the lambda** equation is the INCREMENT, not
    # the coefficient: c_k - (2/9) c_{k-1}, removing the V_k-starts already
    # counted in family 3 (note line 1478). A first draft of this test read that
    # factor of three as a parity shortfall, which had the paper losing ground it
    # never lost; the peer session caught the index. The subtraction is
    # inclusion-exclusion, so the ladder's distance from the ceiling is overlap
    # and truncation, not weak coefficients.
    for k in range(2, 7):
        c_k = Fraction(1, 3) ** k
        c_prev = Fraction(1, 3) ** (k - 1)
        assert c_k - Fraction(2, 9) * c_prev == Fraction(1, 3) ** (k + 1), k

    with pytest.raises(ValueError):
        ideal_coefficient("OEX")


def test_paper_c_ceiling_is_the_collatz_walk_mgf_shifted_by_one() -> None:
    """`F_J(lambda) = F_C(lambda - 1)`, exactly.

    `F_C(s) = sum_w 2^(-|w|) rho_w^s` is the Collatz walk's moment generating
    function. Its two classical roots are `F_C(0) = 1` (Kraft) and `F_C(1) = 1`
    (`E[rho] = 1`, the martingale identity). Under the shift they sit at
    `lambda = 1` and `lambda = 2`.

    So Paper C's ceiling `lambda = 1` (Proposition 5.12) is a Collatz identity
    read one exponential level up, and the whole shortfall from `1` down to
    `lambda** = 0.4926` is the Juggler-side realized parity share `eta_0 = 0`.
    This is a reparameterization, not a bound: it moves no constant in either
    problem, and it is recorded because it says *which half* of Paper C the
    bridge reaches.
    """
    for depth in (1, 3, 5, 8):
        shift = contagion_mgf_shift(depth)
        assert shift["worst_gap"] < 1e-12, depth
        assert shift["kraft"] == pytest.approx(1.0, abs=1e-12), depth
        assert shift["coefficient_sum"] == pytest.approx(
            shift["four_thirds_power"], rel=1e-12), depth


def test_the_published_manuscript_is_correct_and_the_working_notes_were_not() -> None:
    """The errata, guarded so it cannot silently come back.

    `x^0.84` is Krasikov--Lagarias's lower bound on preimage counts. The three
    working artifacts that called the trees "thin" on the strength of it had the
    direction backwards; the Zenodo manuscript did not and needs no revision.
    """
    published = (REPO_ROOT / "docs" / "theory"
                 / "juggler_fate_almost_all_note.md").read_text(encoding="utf-8")
    assert "lower bound is compatible with a bounded reciprocal" in published
    assert "lower bound for Collatz preimage counts" in published

    for name in ("juggler_fate_contagion_note.md", "juggler_tao_reduction_note.md"):
        text = (REPO_ROOT / "docs" / "theory" / name).read_text(encoding="utf-8")
        assert "trees are thin" not in text, name
        assert "thin Collatz preimage trees" not in text, name

def test_psi_is_the_two_adic_tail_of_winklers_sequence() -> None:
    """`N_d / 2^d = sum_{j>d} 2^-j m_j`, and the nonzero `m_j` are A100982.

    This is a telescoping of `J-count-recursion-is-the-boundary-mass`, not a new
    identity: that row gives `P_(d+1) = P_d - b_d Q_d / 2`, and summing it is the
    whole proof. What the telescoped form says is worth a test anyway, because it
    is the bridge between a Collatz-side preprint and Paper B's prefactor.

    `N_d / 2^d` is the quantity whose asymptotic IS `psi(frac(d BETA)) theta^d
    d^(-3/2)`. So `psi` is the 2-adic tail of Winkler's `a_3(r)`, and his
    oscillation theorem for A100982 transmits to `psi` exactly when its error
    term is uniform in `r` and summable against `2^(-j)`. Since `theta = 0.9659`
    the tail runs to about `1/(1-theta) = 29` times its leading term, so a
    per-term relative accuracy `eps` buys `psi` only to about `29 eps`.
    """
    cap = 120
    counts = survivor_counts(cap)
    lost = {d: 2 * counts[d - 1] - counts[d] for d in range(1, cap)}

    # exact, in rationals: the residual after truncating at K is N_K / 2^K
    k = cap - 1
    for d in (4, 12, 24, 40, 60):
        residual = Fraction(counts[d], 2**d) - sum(
            Fraction(lost[j], 2**j) for j in range(d + 1, k + 1))
        assert residual == Fraction(counts[k], 2**k), d

    # the lost extensions vanish exactly at the free steps, and what is left is
    # the sequence the sandwich above is stated on
    nonzero = [lost[d] for d in range(1, cap) if lost[d]]
    assert nonzero[:12] == [1, 1, 1, 2, 3, 7, 12, 30, 85, 173, 476, 961]
    assert nonzero[1:12] == [1, 1, 2, 3, 7, 12, 30, 85, 173, 476, 961]

    # and the closure, which pins the normalisation
    assert sum(Fraction(lost[j], 2**j) for j in range(1, k + 1))         == counts[0] - Fraction(counts[k], 2**k)

def test_the_sandwich_equality_sets_are_exactly_the_record_indices() -> None:
    """And Winkler's fifth preprint lives on a strictly larger family than ours.

    The equality sets this laboratory measured are precisely the one-sided
    record indices of `{n log2 3}` and nothing more. That much was already in
    `test_winklers_sandwich_holds_on_the_laboratory_counts`; this test pins it
    against the records computed here rather than against stored lists, so the
    comparison below rests on something recomputed.

    The comparison: "Marked Rotations and Factorization Heights for Dual Beatty
    Passage Counts" (Winkler, 13 Sep 2026, doi 10.13140/RG.2.2.22015.57761)
    classifies a DIFFERENT identity -- the midpoint `f_r + c_r = (2/r)
    C(m_r - 1, r - 1)` between two passage families -- and it holds on the
    record indices TOGETHER WITH their doubles `2 q_k` and the consecutive sums
    `q_k + q_(k+1)`. That larger family has no counterpart here, and `f_r`,
    `c_r` are not defined for us: ResearchGate embeds only page 1 and the prefix
    conditions are on page 2. Nothing here checks his theorem.

    It also does not reach `psi`: `psi` needs an asymptotic for `a_3(r)` with
    error uniform in `r` and summable against `2^(-j)`, and exact identities on
    a sparse index set are not that.
    """
    from research.juggler_sequence.collatz_bridge import winkler_sandwich

    alpha = math.log(3.0) / math.log(2.0)
    limit = 2000
    rec_min, rec_max = [], []
    lo, hi = 2.0, -1.0
    for n in range(1, limit + 1):
        f = (n * alpha) % 1.0
        if f < lo:
            lo = f
            rec_min.append(n)
        if f > hi:
            hi = f
            rec_max.append(n)

    w = winkler_sandwich(2213)
    assert w["lower_equality"] == rec_min[:len(w["lower_equality"])]
    assert w["upper_equality"] == rec_max[:len(w["upper_equality"])]

    # the larger family is strictly larger, which is the whole point
    def family(q: list[int]) -> set[int]:
        return set(q) | {2 * x for x in q} | {a + b for a, b in zip(q, q[1:])}

    bigger = family(rec_min)
    assert set(w["lower_equality"]) < bigger
    assert {4, 9, 14, 19, 24, 65, 106, 412} <= bigger
    assert not ({4, 9, 14} & set(w["lower_equality"]))

    # These records index ORDERS, not LENGTHS, and an earlier version of this
    # cluster conflated them with the empty-window structure. Carrying the
    # record orders through A020914 does NOT land on the free lengths -- the
    # two index sets are unrelated, and both being statements about the Beatty
    # boundary of log2 3 is all they share.
    record_lengths = [(3**r).bit_length() for r in rec_min[:6]]
    assert record_lengths == [2, 4, 12, 20, 85, 570]
    free_lengths_at_level_zero = {3, 5, 6, 9, 11, 14, 17, 19, 22}
    assert not (set(record_lengths) & free_lengths_at_level_zero)


def test_the_telescoped_tail_is_now_a_lean_theorem_over_the_naturals() -> None:
    """`2^(K-d) N_d = sum_{j=d+1}^{K} 2^(K-j) M_j + N_K`, proved in Lean for all `d <= K`.

    The test above checks the tail identity in rational arithmetic at five depths against a
    cap of 200. That is a spot check of an identity that holds for every pair, and the gap
    mattered once the identity became load-bearing: Paper B's Section 6 now rests on it when
    it argues that Winkler's envelope pins `psi` only within a factor 2.71.

    `Problems.Juggler.neverNegCount_telescope` closes the gap. Cleared of division it is a
    statement about natural numbers, so no rational, no limit and no real number appears in
    it, and the proof is `neverNegCount_add_minimalCertCount` under `Nat.le_induction` and
    nothing else. The analytic reading -- divide by `2^K`, let `K` run off, and the survivor
    density is the tail mass of the minimal certificates -- is a remark about the statement
    rather than part of it.

    Checked here in exact integer arithmetic, in the same form the Lean theorem states, so a
    drift in either would show up as a disagreement rather than as two independent truths.
    """
    from research.juggler_sequence import paper_b_prefix_count as B

    depth = 120
    n = [B.non_contracting(d) for d in range(depth + 1)]
    m = [0] + [2 * n[d - 1] - n[d] for d in range(1, depth + 1)]

    for d in range(0, 60):
        for k in (d, d + 1, d + 7, 60, depth):
            if k < d:
                continue
            lhs = 2 ** (k - d) * n[d]
            rhs = sum(2 ** (k - j) * m[j] for j in range(d + 1, k + 1)) + n[k]
            assert lhs == rhs, (d, k, lhs, rhs)

    # the Lean statement is present and says what this checks
    src = (REPO_ROOT / "formal" / "Problems" / "Juggler"
           / "PaperBCertificateRecursion.lean").read_text(encoding="utf-8")
    assert "theorem neverNegCount_telescope" in src
    assert "2 ^ (K - d) * neverNegCount d" in src
    assert "theorem minimalCert_tail_eq" in src
    for banned in ("sorry", "admit"):
        assert banned not in src, banned
