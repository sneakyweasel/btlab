# The Walsh estimate of the good set is in the wrong basis

Proposition J's error term `N_d E_d(N)` sums a per-word equidistribution error
over all `N_d` good words. Expanding the good-set indicator in Walsh characters
instead gives `S(N,d) = sum_S ghat(S) W_S(N)`, which looks like it replaces `N_d`
by the Wiener norm `||ghat||_1`. It does not, for two independent reasons.

**The gain is capped and the cap is attained.** Parseval gives
`||ghat||_1 <= sqrt(N_d)` unconditionally, so `gamma <= sqrt(2 theta)` is a
theorem. Measured to `d = 386` by four independent methods, `gamma` saturates it.
The structure is real but polynomial -- `||ghat_d||_1 ~ Phi(frac(d beta))
sqrt(N_d) d^(-0.83)` -- and a polynomial factor does not move an exponential rate.

**And the basis is wrong.** `E_d <= max_(S != 0)|W_S| <= 2^d E_d`, both ends
attained. A Walsh estimate needs the upper bound on `max|W_S|` and Proposition J
supplies only the lower, so the conversion costs `2^d`: measured `114x` worse at
`d = 12`, `8199x` at `d = 24`. Paper B's identity (2.1) is itself a Walsh
expansion in the `(w,A)` formal-chain basis with Wiener norm exactly
`N_d(1 - 2^(-(d-1)))`, so the union bound already IS the L1 bound in the basis
the hypothesis controls, and it is termwise sharp there.

Kind: `REFUTED` route. `J-good-set-walsh-route-is-refuted`. It also withdraws
`J-proposition-j-loss-is-the-union-bound`, recorded the previous day, which read
the union bound as a loss worth `20x`.

Do not re-open as: a direct estimate of the good set, a Wiener-norm or Hoelder
bound on the count, a low-degree or spectral-concentration argument, or "combine
the word classes better". The one thing that would revive it is a version of
Hypothesis FD stated as a uniform character bound `max_(S != 0)|W_S(N)| <= B`
rather than per-word -- a different hypothesis, not a better bound, and the
laboratory's machinery controls formal-chain correlations `R_(w,A)` per word, not
global characters.

The general lesson, which is not about this route: before preferring one basis to
another, check which basis the available hypothesis is stated in. An L1 bound is
cheap in whichever basis you like and useless in the one whose inputs you cannot
estimate.

