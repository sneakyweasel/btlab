# Paper B audit ledger

Companion to [juggler_parity_discrepancy_note.md](juggler_parity_discrepancy_note.md). This is a research-discipline record, not an independent verification and not part of the journal text. Probe: `research.juggler_sequence.paper_b_audit`. Theorem 5.3 is the monomial `c = (3k/4) n^{9/8}`. The printed Step 5b `|B|<1` claim is withdrawn: frozen `B = (9/32) k β1 β2 ν^{-9/8}` has constant size `|B| ≤ 6`; Lemma 3.7 at `T = P^{1/2}` still applies. The `ρ₀` ratios of Lemma 5.2b are `O(P^{-1/4})` and sit under `1/2304` for `P ≥ P₀`. Exponent checks: 119.


This file records a re-derivation of the kernel argument, in the form
one row per displayed estimate. Two kinds of check appear. *Hand*: the
estimate was re-derived from its stated inputs, with the constant
recomputed. *Script*: the exact identities were evaluated at \(60\)–\(120\)
digits on \(360\) random odd starts across \(10^4\le n\le 2\cdot10^{14}\),
the standing estimates and inventories on the blocks
\(P=10^6,10^8,10^{10}\) (and, for cell counts, exhaustively at
\(P=10^5\)), and every displayed \(P\)-power comparison
as an exact rational statement
(`research.juggler_sequence.paper_b_audit`, \(119\) exponent checks;
artifact `data/research/juggler/paper_b_audit/summary.json`). A
script check confirms consistency of what is printed; it is not a
proof, and this file is not an independent human verification.
The printed Theorem 5.3 is now the monomial \(c=\tfrac{3k}4 n^{9/8}\);
the exponent \(1-1/96\) and the statements of Theorem 6.1 are unchanged.

| Item | Check | Outcome |
|---|---|---|
| Lemma 4.3(i), one-signed remainder \(0\le E\le\tfrac38(X-1)^{-1/2}\) | hand; script (360 samples) | **corrected proof text**: \(f''=\tfrac34(X-t)^{-1/2}\), so the Lagrange term is \(\tfrac38(X-\xi)^{-1/2}\theta^2\) directly; the statement was already right and the former "missing factor of 2" sentence is removed |
| Lemma 4.3(ii), gap identity \(g=\lfloor\delta\rfloor+\kappa\) | hand; script; Lean `floor_gap_eq_carry` | consistent |
| Lemma 5.1(i), \(0\le R\le\tfrac3{16}v^{-1/2}\) | hand (Taylor of \((v+\theta_2)^{3/2}\)); script | consistent |
| Lemma 5.1(ii), double-gap identity and carry as sawtooth difference | hand (two applications of the gap identity); script; Lean `seq_floor_gap_second`, `carry_eq_fract_add_sub_fract` | consistent |
| Lemma 5.1(iii), \(\Delta\Delta Y=F_{\boldsymbol\kappa}(m)\), \(\lvert j\rvert\le3\), split into offset and second-difference brackets with bounds \([1.5,2.6]\lvert j\rvert P^{3/4}\), \([1.4,15]h_1h_2P^{1/4}\), \(\lvert G'\rvert\), \(\lvert G''\rvert\), run count \(22(\lvert j\rvert{+}1)P^{3/4}\) | hand (mean values: \([1.5,2.52]\), \([4.0,13.5]\), \(\lvert G'\rvert\le1.6\lvert j\rvert P^{-1/4}+14.4h_1h_2P^{-3/4}\)); script (all samples in range; \(\lvert G'\rvert\) at most \(0.56\) of the bound; runs \(\le\) bound at \(P=10^5\)) | consistent |
| Lemma 5.1(iv), master identity, brackets \(\le2\), product rule over four base points | hand (four-point expansion); script (exact on 360 samples); Lean `second_difference_product_rule` (the algebraic skeleton) | consistent |
| Standing estimates (E1)–(E6) | hand ((E5) speed constant \(\tfrac{27}8h_1n^{1/4}\in(3.4,4.0]h_1P^{1/4}\); (E6) constant \(\tfrac98\cdot\tfrac{15}8\cdot\tfrac78=\tfrac{945}{512}\)); script (observed ranges inside every printed interval at three scales; (E6) ratio within \(10^{-3}\) of \(1\)) | consistent |
| Cell inventory \(1.5hP^{1/2}+1\), lengths \([\tfrac23,0.95]P^{1/2}/h\) | hand (\(\delta_h'\in(1.06,1.5]hP^{-1/2}\)); script (exhaustive at \(P=10^5\), \(h\le3\): \(394\), \(787\), \(1179\) cells against \(475\), \(950\), \(1424\)) | consistent |
| Lemma 5.2(ii) from (i): Claims A–H; telescoping with signs \(\sigma_{d,e_1}\); recorded \(A\)-process \(2P^2/H_3+4P/H_3\sum|V|\); \(h_3<H_3\) so \(h_3\le t^{1/3}P^{1/12}\le2.52P^{7/72}\le P^{1/8}\); (D3) closed under one difference (\(3\to6\)); (D1) remainder printed in (i) and averaged at \(h_3=1\) (not at typical \(h_3\sim H_3\)) | hand; script | consistent |
| Standing constraint (C4): \(h_1,h_2\le P^{1/24}\), hence \(h_1+h_2\le 2P^{1/24}\) | hand (not implied by (C1)--(C3) alone; D1 class and the (ii)\(\to\)(i) telescoping need it); script | consistent; Theorem 5.3 has \(H_1=P^{1/48}\), \(H_2=P^{1/24}\) |
| Lemma 5.2(i) Stage 1: \(A_h=-\tfrac{27}8h^2\nu^{1/4}(1+O(hP^{-1}))\), \(B\in(1.89,2.25]uhP^{-1/4}\) | hand (second-order Taylor; the two \(\nu^{5/4}\) terms cancel exactly) | consistent |
| Stage 2: cells, majorant \(4P^{3/4}\), exact shift device | hand (cells, majorant); the shift device is the Theorem 4.4 Step 4 argument, cited not re-derived | consistent |
| Stage 3: (s1) \(\lvert B\rvert\le2.25P^{-1/16}\), \(T\ge8(1+\lvert B\rvert)\); (s2) windows \(0.6P^{1/4}+1\), boundary \(2.1P^{17/32}\), flat \(27P^{3/4}\) | hand (boundary recomputed as \(2.0P^{17/32}\)) | consistent |
| Stage 4: curvature \([0.30,1.35]uhP^{-3/4}\), sums \(2.3(uh)^{1/2}P^{5/8}+2.8(h/u)^{1/2}P^{7/8}\) | hand (\([0.354,1.21]\); \(1.16\), \(2.74\)) | consistent |
| Stage 5: thresholds \(10.2\), \(0.1\); collision sums \(3.4\), \(4.5\), \(2.5\); exponent \(37/48\) | hand (\(3.3\), \(3.5\), \(1.9\)) | consistent |
| Stage 6: (D1) coefficients \(24P^{-5/24}\), \(160P^{-13/24}\), ratios \(80P^{1/24-1/2}\), \(672P^{1/12-1}\); (D2)(a) flat \(23P^{19/24}\); (D2)(b) drift \(13hP^{-1/4}\); (D3) printed ratio \(40P^{-3/4}\) (input-\(3\) tightens to \(20\)) | hand (\(667\) for \(672\)) | consistent |
| Theorem 5.3 Step 1: (C1)–(C4) room \(P^{-1/48}\); balance \(23/24\to1-1/48\to1-1/96\) | hand; script | consistent |
| Theorem 5.3 Step 3c: window \(T=P^{1/2}/(2h_2)\ge\tfrac12 P^{11/24}\) against \(15P^{9/48}\); boundaries \(\le7P^{11/16}\) | hand; script | consistent |
| Step 2: \(\lvert M_1\rvert\le0.43kh_1h_2P^{-7/8}\), deletion cost \(2.7P^{1/4}\) | hand; script (\(M_1\) bound on all samples) | consistent |
| Step 3a: windows \(2kh_2P^{1/4}+1\), hypothesis \(T\ge8(1+\lvert B\rvert)\), flat \(46P^{3/4}\), modes \(uh_1\le P^{1/2}\), boundaries \(7P^{17/24}\); 3b: \(\lvert(\Delta_2c)''\rvert\le0.19kh_2P^{-15/8}\), majorant \(4P^{23/24}\) | hand (window count \(0.22kh_2P^{1/4}+1\)) | consistent |
| Step 4: weight sum \(\sum_t t^{-7/6}\log^2t<\infty\); \(\lvert t\rvert\le3P^{1/24}\) inside the Lemma 5.2 budget; leftover \(uW,u'W'\) are large-\(\lvert q'\rvert\) (D1); good \(h_3\) with \(th_3h'\ge80\) dominate at margin \(\ge4\); bad union \(\le160\) integers, trivial \(\lvert V\rvert\le P\), A-process \(640\,t^{-1/3}P^{23/12}\) | hand; script | consistent |
| Step 5a: \(\lambda_a\) constant \(\tfrac{945}{512}-\tfrac{27}{64}=\tfrac{729}{512}\), range \([1.2,1.5]k\lvert j\rvert P^{-1/8}\); competitor ratios; windows \(1.2k\lvert j\rvert P^{3/8}+1\); boundary \(1.1(k\lvert j\rvert)^{1/2}P^{7/16}\); collision sums \(2.5\), \(2.2\), \(1.8\); run sums \(1.3\), \(21\); total \(1.8P^{23/24}\) | hand (range \([1.31,1.42]\); windows \(0.17k\lvert j\rvert P^{3/8}+1\); sums \(2.45\), \(2.2\), \(1.8\); runs \(1.22\), \(20.2\)) | consistent |
| Step 5b / Lemma 5.2b: local frozen \((cG)''=-\tfrac{135}{1024}k\beta_1\beta_2\nu^{-13/8}\); \(\lambda_0\in[0.35,2.6]kh_1h_2P^{-5/8}\); interpolant is frozen-shape; \(a=-\tfrac{27}{10}\), \(b=-\tfrac{405}{176}\); \(\rho_0\) ratios \(O(P^{-1/4})\le1/2304\); zero-offset \(B=-\tfrac9{32}k\beta_1\beta_2\nu^{-9/8}\) with \(\lvert B\rvert\le6\) | hand; script (frozen \((cF)''\) matches \(135/1024\); frozen \(B\) matches \(9/32\) and \(\lvert B\rvert\le6\)) | **corrected**: the printed \(\lvert B\rvert<1\) dropped \(h_1h_2\) from (C1); the sawtooth is constant-size; Lemma 3.7 at \(T=P^{1/2}\) still applies. Theorem 5.3 is the monomial \(c=\tfrac{3k}4n^{9/8}\) |
| Lemma 3.9 constant for the triple \((\tfrac54,\tfrac{11}8,\tfrac32)\) | hand and exact inverse | **corrected**: the inverse's \(\ell^\infty\) operator norm is \(232\); the printed \(288\) is its \(\ell^1\) norm; \(c_7=1/288\le1/232\) remains valid, so Step 5b is unchanged |
| Lemma 5.2(ii)\(\to\)(i), Claim G identity list | **second reading** (4 Sep 2026); script | **corrected**: the list printed \(1/12+13/8=5/3\) and \(1/12+15/8=23/12\); the exponent \(H_3^{1/2}\) contributes is \(1/24\), and \(1/12\) closes neither identity. The four *displayed* bounds \(S_1\)–\(S_4\) were already right (the probe had \(1/24\) throughout), so no estimate changes. The balance is now printed explicitly: only \(2P^2/H_3\) and \(S_2\) survive with \(O(1)\) prefactors, constants \(2\) and \(4\sqrt2\le6\), giving \(\lvert U\rvert\le(2.83+o(1))t^{-1/6}P^{23/24+\varepsilon}\), and \(H_3=\lceil t^{1/3}P^{1/12}\rceil\) is exactly the balancing choice |
| Lemma 3.8, the constant \(c_6(E)\) | **hand, closed form**; Lean `c6_eleven_eighths_five_fourths`, `c6_eleven_eighths_five_fourths_attained` | **extended**: \(c_6\) is now tabulated over all twenty ordered pairs of \(E=\{\tfrac34,\tfrac54,\tfrac{11}8,\tfrac32,\tfrac{15}8\}\); the minimum is \(\tfrac1{14}\), attained only at \((\tfrac{11}8,\tfrac54)\) with crossing \(s=\tfrac{13}{14}\). Hence the explicit \(\rho_0(E)=\tfrac1{112}\) replaces "sufficiently small in terms of \(E\) alone" |
| Lemma 3.9, the constant \(c_7(E)\) | **hand, exact inverses**; Lean `step5b_curvature_inverse`, `step5b_curvature_norm`, `step5b_c7_printed` | **extended**: \(\lVert M^{-1}\rVert_\infty\) computed for all ten triples of \(E\); the Step-5b triple \((\tfrac54,\tfrac{11}8,\tfrac32)\) is the **extremal** one at \(232\), so \(c_7(E)=\tfrac1{232}\) serves uniformly and \(\rho_0\le\tfrac1{1856}\). The \(\ell^\infty\)/\(\ell^1\) step where the earlier error arose is now machine-checked |
| Step 6 assembly | hand; script | consistent |
| Theorem 6.1 Step E: frozen-shape total phase \(\Delta\Delta(\tfrac k2 m^{9/4})-\Delta\Delta(c\theta_2)\); offset leftover \(\tfrac{81}{512}\), window-centre \(\tfrac{81}{128}\), composite \(\tfrac{243}{512}\); \(B=\tfrac{27}{32}kj\nu^{3/8}\); zero-offset \(\lambda_0'=\tfrac{1095}{1024}kh_1h_2\nu^{-5/8}\); interpolant \(b'=-\tfrac{365}{176}\) | hand; script (offset tot/81 and \(B/(kj\nu^{3/8})\) near \(1\) and \(27/32\); zero-offset tot against \(16929/2048\) near \(2190/16929\)) | **corrected architecture**: the previous composites \(405/512\) and \(8.27\) differentiated the moving total phase \(\tfrac k2\nu^{27/8}\); the \(1-1/96\) exponent is unchanged |
| Lemma 6.2, remainder bounds | hand | **corrected**: the two Lagrange remainders (orders \(n^{-45/16}\), \(n^{-81/16}\)) are now displayed instead of being absorbed into coefficients that have no slack when \(\theta_2\) or \(\theta_z\) is close to \(1\); Theorem 6.3 uses only the order of magnitude |
| Kernel sum \(K_c(P)\), \(k=1\), \(P\le3\cdot10^5\), and the wave \(\sum e(Y(n))\) | script, OBSERVATION | \(\lvert K_c\rvert\) between \(0.4\) and \(1.2\) times \(\sqrt{P/2}\): square-root scale, far below \(P^{1-1/96}\); the wave likewise; neither is evidence for the theorem's exponent, only consistent with it |

*Second reading, 4 September 2026.* The \((ii)\Rightarrow(i)\)
reduction of Lemma 5.2 (Claims A–H) was read line by line against an
independent re-derivation of its exponent budget. The reduction is
correct and its assembly is tight — the \(23/24\) is forced by the
balance of two terms, not fitted — and one annotation error was found
and corrected (row above). The constants of Lemmas 3.8 and 3.9 were
computed in closed form over the exponent set actually used and moved
into the manuscript, with the two finite computations they rest on
formalised in `formal/Problems/Juggler/MonomialSplitting.lean`
(builds against Mathlib `v4.33.0`).

**Still outstanding, and still the most valuable check this paper can
receive:** a second human reading of the *six-stage proof of
Lemma 5.2(i)* and of *Theorem 5.3, Steps 5a–5b*. The reading above
covers the reduction that consumes (i), not (i) itself.

*What was not re-derived.* The \(\rho_0\) ratios
of Lemma 5.2b are now displayed and sit under \(1/2304\). The exact
shift device of Theorem 4.4, Step 4, and the
\(O(\log^3P)\) coefficient-mass bookkeeping were read and accepted,
not re-derived; Lemma 3.7 was re-read and found consistent. The
ineffective threshold \(P_0\) is not estimated. Claims A–H of Lemma 5.2(ii)\(\to\)(i), the (D3) closure
\(3\to6\), the printed (D1) remainder, and the Theorem 5.3
Step 4 leftover-mode split are now written on the manuscript.
A second human reading of the six-stage proof of Lemma 5.2(i)
and of Steps 5a–5b remains the most valuable check this paper
can receive; this file is not that reading.
