# Paper B audit ledger

Companion to [juggler_parity_discrepancy_note.md](juggler_parity_discrepancy_note.md). This is a research-discipline record, not an independent verification and not part of the journal text. Probe: `research.juggler_sequence.paper_b_audit`. Theorem 5.3 is the monomial `c = (3k/4) n^{9/8}`. The printed Step 5b `|B|<1` claim is withdrawn: frozen `B = (9/32) k β1 β2 ν^{-9/8}` has constant size `|B| ≤ 6`; Lemma 3.7 at `T = P^{1/2}` still applies. The `ρ₀` ratios of Lemma 5.2b are `O(P^{-1/4})` and sit under `1/2304` for `P ≥ P₀`. Exponent checks: 150.


This file records a re-derivation of the kernel argument, in the form
one row per displayed estimate. Two kinds of check appear. *Hand*: the
estimate was re-derived from its stated inputs, with the constant
recomputed. *Script*: the exact identities were evaluated at \(60\)–\(120\)
digits on \(360\) random odd starts across \(10^4\le n\le 2\cdot10^{14}\),
the standing estimates and inventories on the blocks
\(P=10^6,10^8,10^{10}\) (and, for cell counts, exhaustively at
\(P=10^5\)), and every displayed \(P\)-power comparison
as an exact rational statement
(`research.juggler_sequence.paper_b_audit`, \(150\) exponent checks;
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
| Stage 3: (s1) \(\lvert B\rvert\le2.25P^{-1/16}\), \(T\ge8(1+\lvert B\rvert)\); (s2) windows \(0.6P^{1/4}+1\), boundary \(1.1P^{17/32}\), flat \(19P^{3/4}\) | hand | consistent; **tightened** from \(2.1\) and \(27\) — the boundary display had duplicated \((0.30)^{-1/2}\) as a separate factor \(1.83\), and the flat cost needed only \(8P^{1/2}+18P^{3/4}\le19P^{3/4}\) (\(P\ge4096\)) |
| Stage 4: curvature \([0.35,1.20]uhP^{-3/4}\), ratio \(\le3.5\), sums \(1.1(uh)^{1/2}P^{5/8}+2.6(h/u)^{1/2}P^{7/8}\) | hand (\([0.35475,1.19324]\); \(1.096\), \(2.536\)) | **tightened**: the curvature range is the root constant of Stages 4–6 and was printed \([0.30,1.35]\); the exact range is \([0.3548,1.1932]\). Everything below is rekeyed to \(0.35\) |
| Stage 5: thresholds \(9.1\), \(0.11\); collision sums \(3.1\), \(0.37\), \(0.47\); exponent \(37/48\) | hand (\(3.017\), \(0.367\), \(0.470\)) | **tightened**: rekeying to \([0.35,1.20]\) moves the upper threshold \(4(1.20)/0.5303=9.05\) (was \(10.2\)) and the lower \(0.35/3=0.1167\) (was \(0.1\)); with \(M\in[4.4,9.1]uhP^{-3/4}\), \(M\le9.1P^{-1/4}\le1\) for \(P\ge6857\) |
| Stage 6: (D1) coefficients \(24P^{-5/24}\), \(160P^{-13/24}\), ratios \(69P^{1/24-1/2}\), \(572P^{1/12-1}\); (D2)(a) flat \(23P^{19/24}\); (D2)(b) drift \(13hP^{-1/4}\); (D3) ratio \(35P^{-3/4}\) (input-\(3\) tightens to \(18\)) | hand | **tightened** throughout by rekeying to \(0.35\): (D1) boundary \(2.6\)/\(5.1\)/\(11\) (was \(5.1\)/\(10.3\)/\(21\)); (D1) ratios \(69\), \(572\) (was \(80\), \(672\)); (D2)(a) smooth \(60\) (was \(72\)), boundary \(3.4\) (was \(7\)), mode ratio \(52\) (was \(60\)); (D2)(b) \(1.2\) (was \(1.4\)); (D3) \(35\)/\(18\) (was \(40\)/\(20\)); the \(P^{-9/8}\) ratio \(26\) (was \(30\)) |
| Theorem 5.3 Step 1: (C1)–(C4) room \(P^{-1/48}\); balance \(23/24\to1-1/48\to1-1/96\) | hand; script | consistent |
| Theorem 5.3 Step 3c: window \(T=P^{1/2}/(2h_2)\ge\tfrac12 P^{11/24}\) against \(15P^{9/48}\); boundaries \(\le7P^{11/16}\) | hand; script | consistent |
| Step 2: \(\lvert M_1\rvert\le0.43kh_1h_2P^{-7/8}\), deletion cost \(2.7P^{1/4}\) | hand; script (\(M_1\) bound on all samples) | consistent |
| Step 3a: windows \(2kh_2P^{1/4}+1\), hypothesis \(T\ge8(1+\lvert B\rvert)\), flat \(46P^{3/4}\), modes \(uh_1\le P^{1/2}\), boundaries \(7P^{17/24}\); 3b: \(\lvert(\Delta_2c)''\rvert\le0.19kh_2P^{-15/8}\), majorant \(4P^{23/24}\) | hand (window count \(0.22kh_2P^{1/4}+1\)) | consistent |
| Step 4: weight sum \(\sum_t t^{-7/6}\log^2t<\infty\); \(\lvert t\rvert\le3P^{1/24}\) inside the Lemma 5.2 budget; leftover \(uW,u'W'\) are large-\(\lvert q'\rvert\) (D1); good \(h_3\) with \(th_3h'\ge72\) dominate at margin \(\ge4\); bad union \(\le144\) integers, trivial \(\lvert V\rvert\le P\), A-process \(576\,t^{-1/3}P^{23/12}\) | hand; script | **tightened**: this split keys off the same Stage-4 curvature, so \(6/0.35\le18\) and \(25/0.35\le71.5\) replace \(20\) and \(83.4\); the good-set threshold falls \(80\to72\), the bad union \(160\to144\), the \(A\)-process constant \(640\to576\) |
| Step 5a: \(\lambda_a\) constant \(\tfrac{945}{512}-\tfrac{27}{64}=\tfrac{729}{512}\), range \([1.30,1.43]k\lvert j\rvert P^{-1/8}\); windows \(0.17k\lvert j\rvert P^{3/8}+1\) of length \(\ge4.7P^{5/8}/(k\lvert j\rvert)\); boundary \(0.15(k\lvert j\rvert)^{1/2}P^{7/16}\); collision \(M\in[1.30,5.75]\), sums \(2.4\), \(0.15\), \(0.16\); run sums \(1.2\), \(20\) | **second reading** (4 Sep 2026); script (9 new rows) | **corrected**: the printed per-step drift of the anchor \(\theta\)-sawtooth was \(0.2k\lvert j\rvert P^{-5/8}\), but \(B'=\tfrac{27}{128}k\lvert j\rvert\nu^{-5/8}\) and \(\tfrac{27}{128}=0.2109>0.2\) — understated by \(5\%\), now \(0.22\). **Tightened**: the window count is the *total* drift \(\tfrac9{16}(2^{3/8}{-}1)=0.167\), not \(1.2\) (a \(7\times\) overcount that multiplied the boundary cost and both window-summed collision terms); the window length \(1/B'(P)=\tfrac{128}{27}=4.74\), not \(0.8\); \(\lambda_a\) range \([1.2,1.5]\to[1.30,1.43]\) exactly; collision \(M\in[0.3,6]\to[1.30,5.75]\). Downstream: boundary \(1.1\to0.15\), collision sums \(2.5,2.2,1.8\to2.4,0.15,0.16\) (and \(3.8\to0.33\)), run sums \(1.3,21\to1.2,20\). The \(1.8P^{23/24}\) total is unchanged and now has large margin |
| Step 5b / Lemma 5.2b: local frozen \((cG)''=-\tfrac{135}{1024}k\beta_1\beta_2\nu^{-13/8}\); \(\lambda_0\in[0.35,2.6]kh_1h_2P^{-5/8}\); interpolant is frozen-shape; \(a=-\tfrac{27}{10}\), \(b=-\tfrac{405}{176}\); \(\rho_0\) ratios \(O(P^{-1/4})\le1/2304\); zero-offset \(B=-\tfrac9{32}k\beta_1\beta_2\nu^{-9/8}\) with \(\lvert B\rvert\le6\) | hand; script (frozen \((cF)''\) matches \(135/1024\); frozen \(B\) matches \(9/32\) and \(\lvert B\rvert\le6\)) | **corrected**: the printed \(\lvert B\rvert<1\) dropped \(h_1h_2\) from (C1); the sawtooth is constant-size; Lemma 3.7 at \(T=P^{1/2}\) still applies. Theorem 5.3 is the monomial \(c=\tfrac{3k}4n^{9/8}\) |
| Lemma 3.9 constant for the triple \((\tfrac54,\tfrac{11}8,\tfrac32)\) | hand and exact inverse | **corrected**: the inverse's \(\ell^\infty\) operator norm is \(232\); the printed \(288\) is its \(\ell^1\) norm; \(c_7=1/288\le1/232\) remains valid, so Step 5b is unchanged |
| Lemma 5.2(ii)\(\to\)(i), Claim G identity list | **second reading** (4 Sep 2026); script | **corrected**: the list printed \(1/12+13/8=5/3\) and \(1/12+15/8=23/12\); the exponent \(H_3^{1/2}\) contributes is \(1/24\), and \(1/12\) closes neither identity. The four *displayed* bounds \(S_1\)–\(S_4\) were already right (the probe had \(1/24\) throughout), so no estimate changes. The balance is now printed explicitly: only \(2P^2/H_3\) and \(S_2\) survive with \(O(1)\) prefactors, constants \(2\) and \(4\sqrt2\le6\), giving \(\lvert U\rvert\le(2.83+o(1))t^{-1/6}P^{23/24+\varepsilon}\), and \(H_3=\lceil t^{1/3}P^{1/12}\rceil\) is exactly the balancing choice |
| Lemma 5.2(i), Stages 1–6 | **second reading** (4 Sep 2026); script (16 new exponent rows) | see the four rows below |
| — Stage 1 | second reading | consistent, and *exact*: the two \(\nu^{5/4}\) contributions to \(A_h\) are both \(\tfrac94h\nu^{5/4}\) and cancel identically, leaving \(A_h=-\tfrac{27}8h^2\nu^{1/4}\) with **zero** \(h^1\) term (symbolic expansion). \(\lvert A_h''\rvert=\tfrac{81}{128}h^2\nu^{-7/4}\), and \(\tfrac{81}{128}=0.6328\le0.64\) printed. \(B\in[(\tfrac94)2^{-1/4},\tfrac94]uhP^{-1/4}=[1.892,2.25]\), printed \([1.89,2.25]\) |
| — Stages 2, 3 | second reading | consistent: \(\delta_h'\in[1.0607,1.5]hP^{-1/2}\) gives cell lengths \([0.6667,0.9428]P^{1/2}/h\), printed \([\tfrac23,0.95]\); the shift device \(e(r\nu^{3/2}+r\delta_h)=e(r(\nu{+}2h)^{3/2})\) is an exact identity; the (s1) drift is \((\tfrac94)(1-2^{-1/4})=0.358\le0.6\) printed |
| — Stages 4, 5 | second reading | consistent, constants recomputed. Stage 4 curvature \([0.3548,1.1932]uhP^{-3/4}\) inside printed \([0.30,1.35]\); **tightened**: the curvature range was printed \([0.30,1.35]\) against the exact \([0.3548,1.1932]\); rekeying to \([0.35,1.20]\) gives cell sums \(1.096\) and \(2.536\), printed \(1.1\) and \(2.6\) (were \(2.3\) and \(2.8\)), with the one-line reasons added (the cells partition the block; there are at most \(1.5hP^{1/2}+1\) of them). Stage 5 mode curvature \((\tfrac34)2^{-1/2}=0.5303\ge0.53\); thresholds \(9.1\) and \(0.11\); \(\tfrac56-\tfrac13\cdot\tfrac3{16}=\tfrac{37}{48}<\tfrac78\) |
| — Stage 5, the collision band | second reading | **corrected**: \(M\) was printed as \([0.03,11]uhP^{-3/4}\), but it is pinned from below by the \(\nu^{3/4}\) scale alone, whose curvature carries \(G=\lfloor\delta_h\rfloor>3hP^{1/2}-1\): \(\lvert a\rvert P^{-5/4}>uhP^{-3/4}(4.5-1.5/(hP^{1/2}))\ge4.4uhP^{-3/4}\), and \(\le6.37uhP^{-3/4}\), against \(\lvert w\rvert P^{-1/2}\in[0.1,10.2]uhP^{-3/4}\). Hence \(M\in[4.4,9.1]uhP^{-3/4}\) — the low end was \(\sim150\times\) conservative. The three collision sums improve from \(3.4,4.5,2.5\) to \(\mathbf{3.1,0.37,0.47}\) (factors \(1.1\), \(12\), \(5.3\)), the collision-band total is now \(\le C((uh)^{1/2}P^{5/8}+P^{37/48})\log P\) — the sharper \(P^{37/48}\) replacing the printed \(P^{5/6}\), which the line above already derived — and \(M\le9.1P^{-1/4}\le1\) makes Lemma 3.8's hypothesis explicit, which the text had never checked |
| — Stage 6 | second reading | (D1) consistent: boundary constants \(5.01\), \(10.02\) against printed \(5.1\), \(10.3\); exponents \(-\tfrac5{24},-\tfrac{13}{24},-\tfrac{11}{24},-\tfrac{11}{12}\); \(4\cdot25\cdot2/0.30=667\le672\). (D2)(a) flat cost \(\tfrac1{24}+\tfrac18+\tfrac58=\tfrac{19}{24}<\tfrac78\) with constant \(23\). **corrected**: the (D2)(a) mode-curvature display carried the *window parameter* \(T=P^{1/2}\) where the Lemma 3.7 *truncation* \(J=R_0=P^{1/4}\) belongs. With \(J\): \(\lvert q''\rvert\le\lvert B_0\rvert+J\le3P^{7/24}\), curvature \(\le18P^{-23/24}\), ratio \(\le60P^{-5/24}\le60P^{-1/16}\) — the printed conclusion, and conservative. With \(T\) the display yields only \(9P^{-3/4}\), whose ratio \(30/(uh)\) is **not** \(o(1)\) at \(uh=O(1)\). The constant \(18/0.30=60\) is unchanged either way, and no estimate downstream moves |
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

The *six-stage proof of Lemma 5.2(i)* has now also been read
(rows above): every displayed constant was recomputed from its stated
inputs, one further misprint was found and corrected, and sixteen new
exponent rows pin the stages in the probe.

*Theorem 5.3, Step 5a* has now been read as well, with one further
misprint corrected and its window count tightened by \(7\times\).

**Still outstanding:** a second human reading of *Theorem 5.3,
Step 5b* (and Lemma 5.2b). That is now the only part of the kernel
argument without an independent second pass.

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
