# Paper B audit ledger

Companion to [juggler_parity_discrepancy_note.md](juggler_parity_discrepancy_note.md). This is a research-discipline record, not an independent verification and not part of the journal text. Probe: `research.juggler_sequence.paper_b_audit`. Theorem 5.3 is the monomial `c = (3k/4) n^{9/8}`. The printed Step 5b `|B|<1` claim is withdrawn: frozen `B = (9/32) k β1 β2 ν^{-9/8}` has constant size `|B| ≤ 6`; Lemma 3.7 at `T = P^{1/2}` still applies. The `ρ₀` ratios of Lemma 5.2b are `O(P^{-1/4})` and sit under `1/2304` for `P ≥ P₀`. Exponent checks: 166.


This file records a re-derivation of the kernel argument, in the form
one row per displayed estimate. Two kinds of check appear. *Hand*: the
estimate was re-derived from its stated inputs, with the constant
recomputed. *Script*: the exact identities were evaluated at \(60\)–\(120\)
digits on \(360\) random odd starts across \(10^4\le n\le 2\cdot10^{14}\),
the standing estimates and inventories on the blocks
\(P=10^6,10^8,10^{10}\) (and, for cell counts, exhaustively at
\(P=10^5\)), and every displayed \(P\)-power comparison
as an exact rational statement
(`research.juggler_sequence.paper_b_audit`, \(166\) exponent checks;
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
| Lemma 5.2b / Step 5b — **adversarial audit**, target 1 (interpolation identity) | **second reading** (4 Sep 2026); script (16 new rows) | **corrected premise**: step (i) read \(\lvert G_i-\delta_{h_i}\rvert<2\), which yields \(\tfrac9{16}(u{+}u')P^{-5/4}\), twice the bound then used. The gap identity \(G_i=\lfloor\delta_{h_i}\rfloor+\kappa_i\), \(\kappa_i\in\{0,1\}\), gives \(\lvert G_i-\delta_{h_i}\rvert=\lvert\kappa_i-\{\delta_{h_i}\}\rvert\le1\), which is what the printed \(\tfrac9{32}\) needs. Steps (ii) and (iii) verified with margin (\(0.567\) against the printed \(8\); \(\lvert c''\rvert=\tfrac{27}{256}k\nu^{-7/8}=0.1055\le0.11\), and the true factor is \(\lvert c''\rvert/2\)). The total \(202.5+16=218.5\le219\) is exactly where \(219\) comes from |
| Lemma 5.2b / Step 5b — target 2 (**uniformity**) | second reading | **corrected statement — the material finding**: the bound \(\lvert f''-\Lambda\rvert\le219P^{-25/24}+0.11P^{-5/6}\) was asserted under (C1)–(C4) and \(j=0\) alone, but its proof uses \(u,u'\le360P^{5/24}\), a *middle-band* fact. Under (C1)–(C4) Lemma 5.2(i) admits \(uh_1\le P^{1/2}\), hence \(u\) up to \(P^{1/2}\), where the first error term is \(\tfrac9{16}P^{-3/4}\) — larger by \(P^{7/24}\). **As stated the lemma was false outside the band.** It is invoked only inside it, so no estimate changes; the hypothesis is now printed as (C5), with the derivation \(u\le200kh_2P^{1/8}\le200P^{5/24}\) from \(kh_2\le P^{1/12}\) (exactly (C3)+(C4)) recorded alongside |
| Lemma 5.2b / Step 5b — target 3 (three-term sublevel step) | second reading | consistent: \(a=-\tfrac{27}{32}\cdot\tfrac{16}5=-\tfrac{27}{10}\) and \(b=-\tfrac{1215}{1024}\cdot\tfrac{64}{33}=-\tfrac{405}{176}\) both match; \(\lambda_0\in[0.385,2.438]\) inside printed \([0.35,2.6]\); \(V/S=3(0.35)^{-1/2}P^{-7/48}=5.07\le5.1\); \(V\ge1.775P^{-37/48}\ge1.7\), and \(V\ge10\lvert f''-\Lambda\rvert\) from \(P\approx4\cdot10^{12}\). **Noted**: \(V\le c_7S/2\) needs \(P\ge5.8\cdot10^{23}\) at the printed \(c_7=\tfrac1{288}\) — inside \(P_0\approx10^{24}\) but only just; switched to the exact \(c_7=\tfrac1{232}\) (Lean `step5b_curvature_norm`), which relaxes it to \(1.3\cdot10^{23}\) |
| Lemma 5.2b / Step 5b — target 4 (final partition) | second reading | \(\lvert\Omega\rvert\le2.252P^{89/96}\le2.3\), boundaries \(3.185\le3.2\), exponents \(1-\tfrac7{96}=\tfrac{89}{96}\) and \(\tfrac{13}{24}+\tfrac{37}{96}=\tfrac{89}{96}\): all consistent. **Two corrections**: (a) \(S\le300P^{-1/2}\) does not follow — \(\lvert uh_1{+}u'h_2\rvert\le2\mu P^{3/4}/0.84\) with \(\mu\le60\lambda_0\le156kh_1h_2P^{-5/8}\) gives \(372\), so the entry is now \(380\) and the good-pieces constant \(18\to21\) (it feeds only the \(P^{3/4}\) term); (b) "\(\le P^{15/16}\) for \(P\ge P_0\)" is **false at \(P_0\)**: absorbing \(C(E)\log P\) into \(P^{1/96}\) needs \(\ln P\ge96\ln\ln P\), i.e. \(P\approx10^{274}\), whereas at \(10^{24}\) one has \(\ln P=55.3\) against \(P^{1/96}=1.78\). Step 6 uses only the \(\varepsilon\)-form, so nothing downstream depends on it; the display is now \(O_E(P^{89/96+\varepsilon})\) |
| Step 5b, implicit dependency | second reading | **made explicit**: the mode-dominant run-boundary count \(22h_1h_2P^{1/4}\le22P^{5/16}\) uses the Theorem 5.3 caps \(H_1=P^{1/48}\), \(H_2=P^{1/24}\) (so \(h_1h_2\le P^{1/16}\)), not (C4) alone — under (C4) \(h_1h_2\le P^{1/12}\) and the count is only \(22P^{1/3}>22P^{5/16}\). The \(N\le3.5P^{13/24}\) piece count does hold under (C4) alone |
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
misprint corrected and its window count tightened by \(7\times\); and
*Lemma 5.2b / Step 5b* has had an adversarial pass against the four
targets (interpolation identity, uniformity, three-term sublevel step,
final partition), recorded in the five rows above.

**Status.** Every stage of the kernel argument has now had an
independent second pass. The one *material* finding is the missing
hypothesis (C5) in Lemma 5.2b: as stated the lemma was false outside
the middle band, though it is applied only inside it. Two further
displays were false as printed (the \(<2\) premise, and
"\(\le P^{15/16}\) for \(P\ge P_0\)"), and one constant did not follow
(\(S\le300P^{-1/2}\)); none changes an estimate. **No
conclusion-breaking error was found**, and the \(1-1/96\) exponent is
untouched throughout.

**\(P_0\) is now effective and homogeneous.** The threshold has been
computed: each of the thirty printed threshold inequalities of
Sections 4--6 was transcribed as a predicate in \(P\) and solved
separately, and the maximum is
\[
P_0=8.9\cdot10^{13},
\]
attained at the Lemma 3.9 hypothesis \(V\le c_7S/2\) of Step 5b. The
computation is in `src/research/juggler_sequence/p0_certificate.py`,
which also generates the Appendix A table, so the paper and the probe
cannot drift apart. Three findings came out of it.

*The normalisation of \(V\) was carrying the whole threshold.* With
\(V=\kappa S^{1/2}P^{-11/24}\), the comparison \(V\le c_7S/2\)
needs \(P\ge(784\kappa)^{48/7}\), while \(\kappa\) controls only
the coefficient of \(C(E)P^{89/96}\), which is absorbed into
\(C(E)\). The draft's \(\kappa=3\) is near the coefficient optimum
(\(5.02\) against the best possible \(4.99\)) and put \(P_0\) at
\(1.3\cdot10^{23}\). Retuning to \(\kappa=\tfrac13\) costs a
factor \(9.06/5.02<2\) in that coefficient and buys six and a half
orders of magnitude. The exponent \(89/96\) is independent of
\(\kappa\). Steps 5a and 5b were retuned accordingly.

*\(P_0\) does not depend on \(\varepsilon\).* No divisor sum, gcd
sum or large-sieve average occurs anywhere in Sections 3--6 (checked:
zero occurrences), so every \(\ll_\varepsilon\) there is a power of
\(\log P\). Counting them gives the \(\varepsilon\)-free forms
\(K_c(P)\ll P^{1-1/96}\log^{3/4}P\) and
\(\#\mathrm{OOOEE}(N)=\tfrac N{32}+O(N^{1-1/96}(\log N)^{15/4})\).
The threshold for absorbing \(\log^AP\) into \(P^\varepsilon\)
(\(1.5\cdot10^{190}\), and beyond \(10^{300}\) for \(A=15/4\)) is
a fact about \(\varepsilon\), not about the proof, and is excluded
from \(P_0\) — as is the \(10^{274}\) of the \(P^{15/16}\)
reading, which Step 6 does not use.

*\(c_7\) itself is not the place to push (Appendix A.5).* Since \(P_0\) is
carried entirely by \(V\le c_7S/2\), the constant was attacked
directly. Two results. (a) **Not by the exponent triple.**
\(c_7=1/\lVert M^{-1}\rVert_\infty\) depends only on the exponents,
through \(\det M=\prod_{i<j}(x_j-x_i)\), and scales as the *square* of
their gap: for an equally spaced triple of gap \(\delta\) about
\(x_0\), \(\delta^2/c_7=x_0^2-2x_0+c\) with \(c\in[1.75,2]\) on
\(\delta\in[\tfrac18,\tfrac12]\). Step 5b's triple
\((\tfrac54,\tfrac{11}8,\tfrac32)\) is \((10,11,12)/8\), adjacent
on the lattice \(\tfrac18\mathbb Z\) the paper lives on, and each
entry is forced (level-1 wave; frozen-shape model; differenced-wave
monomial). Over all \(165\) triples of the paper's inventory \(c_7\)
runs from \(1/259\) to \(144/287\). (b) **By dropping the uniform
constant, at most a factor \(232/24<10\), and not for free.** Lemma
3.9's proof needs only \(\lvert M^{-1}\rvert c\le1\) for a vector
\(c=(c_2,c_3,c_4)\), and only \(c_2\) gates the hypothesis. But the
uniform choice saturates the middle row *exactly*, \(24+144+64=232\),
so every gain in \(c_2\) is paid out of \(c_3,c_4\) — which sit in
\(C\), via the \(r=3\) length \(2PV/(c_3S)\) and the \(r=4\)
length \(P(V/(c_4S))^{1/2}\). Three facts are Lean-checked
(`step5b_vector_transfer`, `step5b_uniform_saturates`,
`step5b_c2_ceiling`, `step5b_c2_optimum_feasible`).

*A second threshold, and a correction of scope.* The trade is only
visible against a quantity the first pass did not compute. \(P_0\)
certifies that the printed inequalities hold; it does not say when the
bound beats the trivial one. The middle band totals
\(\le CP^{89/96}\log P\), which beats \(P\) only from
\(P_1:=C^{96/7}\) on — at the present operating point
\(C\approx542\) and \(P_1\approx3.2\cdot10^{37}\). Minimising
\(P_0\) alone reaches \(4.6\cdot10^{13}\) (a factor \(820\)) but
sends \(P_1\) to \(10^{56}\); holding \(P_1\) fixed buys only a
factor \(1.9\) in \(P_0\). The uniform constant is therefore kept.
The \(P_1\) floor is intrinsic: absorbing any constant \(C\) into a
\(P^{1/96}\) saving needs \(P\ge C^{96/7}\), so even \(C=10\)
costs \(10^{13.7}\). At the \(P_0\)-optimal point the binding
comparison is no longer the curvature inverse but
\(V\ge10\lvert f''-\Lambda\rvert\) — the Lemma 5.2b interpolant
error \(219P^{-25/24}\), and its safety factor \(10\). Those are the
next targets.

*The interpolant error, and the comparison beside it (Appendix A.5).*
The \(219\) of Lemma 5.2b was attacked next, and the comparison it
feeds turned out to matter more than the constant. Three results.
(a) **\(219\to106\), a factor \(2.07\).** The printed
\(219=202.5+16\) opened the middle-band cap \(\tfrac{60\cdot2.6}{0.84}
=185.7\) first to \(200\) and then, in (C5), to \(360\); and step (ii)
carried \(8\) where the computation gives
\(\tfrac{135}{1024}\cdot4.3=0.567\). Restating (C5) in its native
form \(u\le186kh_2P^{1/8}\), \(u'\le186kh_1P^{1/8}\) keeps the
shifts visible, so the two error terms share the shape
\(k(h_1{+}h_2)P^{-9/8}\) and combine: \(52.9\,k(h_1{+}h_2)P^{-9/8}
\le106P^{-25/24}\). (b) **The factor \(10\) is not needed at all.**
The comparison \(V\ge10\lvert f''-\Lambda\rvert\) exists only to
transfer the sublevel structure from \(\Lambda\) to \(f''\); running
Lemma 3.9 at the *raised* threshold \(W=V+E\) does that directly,
since \(\lvert\Lambda\rvert\ge W\) off \(\Omega_W\) gives
\(\lvert f''\rvert\ge W-E=V\). Its single hypothesis
\(W\le c_7S/2\) replaces the former pair. The factor \(10\) was not
merely margin, it was harmful: it forced \(V\) *up* exactly where
\(c_7\) wanted it down, so the two comparisons fought and pinned
\(\kappa\) near \(\tfrac13\). (c) **With them no longer fighting,
\(\kappa\) falls to \(\tfrac1{12}\)** and \(P_0\) and \(P_1\)
improve *together*:
\[
P_0:\ 3.8\cdot10^{16}\to8.9\cdot10^{13},
\qquad
P_1:\ 2.1\cdot10^{21}\to5.0\cdot10^{19}.
\]
At the new threshold \(V\) and \(E\) split the budget \(60{:}40\)
and \(E\) splits \(54{:}46\) between its terms, so both halves of the
interpolant error are now load-bearing --- they were not before.

*Tier 2 formalisation (`formal/Problems/Juggler/PaperBAssembly.lean`,
15 theorems; `ThresholdCertificate.lean`, 10).* The analytic inputs are
hypotheses and the assembly is proved, which is where every error in this
audit has lived. Four blocks, and two of them changed the manuscript.

(a) **Lemma 4.3(i) has a closed form.** The manuscript proves it by
second-order Taylor with an unspecified mean value \(\xi\). Writing
\(a=\sqrt m\), \(b=\sqrt X=n^{3/4}\), the remainder is *identically*
\(E=a^3-\tfrac32a^2b+\tfrac12b^3=\tfrac12(a-b)^2(2a+b)\). Both printed
bounds follow with no analysis: \(E\ge0\) by inspection, and
\(Ea\le\tfrac38\theta^2\) reduces to \((5a+3b)(a-b)\le0\). This is
sharper than the printed bound at every \(n\), not just asymptotically,
and it is now in the manuscript.

(b) **A rounding slip caught by the formalisation.** Step (i) of Lemma 5.2b
is \(\tfrac9{32}\cdot186=52.3125\), which the draft printed as
\(52.3\); and with step (ii) printed as \(0.6\) the sum is
\(52.9125\), past the \(52.9\) the next line uses. Corrected to
\(52.3125\) and \(0.57\), sum \(52.8795\le52.9\). The probe was
also carrying \(105.6\) for the combined constant where the honest value
is \(2\times52.8795=105.759\) --- an *under*-estimate; now \(105.8\).
\(P_0\) moves from \(8.929\cdot10^{13}\) to \(8.946\cdot10^{13}\),
so no printed figure changes.

(c) **Lemma 4.3(ii)** is a pure floor identity,
\(\lfloor x+\delta\rfloor-\lfloor x\rfloor-\lfloor\delta\rfloor
=[\,\{x\}+\{\delta\}\ge1\,]\), proved outright.

(d) **Lemma 3.9's two length bounds.** The \(r=3\) case is proved from
the mean value theorem (used, not assumed): any two points of
\(\{|f''|\le V\}\) lie within \(2V/c\). The \(r=4\) case is proved
from strong convexity in midpoint form, giving diameter
\(4\sqrt{V/c}\) --- the \((V/S)^{1/2}\) that produces \(89/96\).
The step from \(f''''\ge c\) to convexity is a hypothesis.

*The Appendix A certificate is now proved, not bisected.* All thirty
threshold rows are in
`formal/Problems/Juggler/ThresholdCertificate.lean` (32 theorems; the
window-boundary and \(\lambda_0\)-range rows split in two), together
with the raised-threshold device and the sharpness of
\(\lvert G-\delta\rvert\le1\) --- 40 theorems in the file. The
enabling observation is that every exponent in the paper lies in
\(\tfrac1{96}\mathbb Z\), so \(P=t^n\) makes each row polynomial in
\(t\) and no `Real.rpow` is needed anywhere. Certified
\(P_0\le1.96^{48}=1.07\cdot10^{14}\) against the bisected
\(8.9\cdot10^{13}\) --- the rational thresholds cost under
\(20\%\). A test pins each Lean row's \(t_0^n\) against the probe's
bisected value, so the two artifacts cannot drift.

Writing them out caught three things. The draft's `row_5b_Npieces` used
\(t\ge2.4\), certifying \(P\ge1.8\cdot10^{18}\) --- above
\(P_0\) itself, so as stated it would have *set* the threshold;
tightened to \(t\ge1.46\), i.e. \(7.7\cdot10^7\). And two hand
arithmetic slips: \(1.89^7=86.1\), not \(94\), and
\(105.8/698896=1.51382\cdot10^{-4}\), just above the
\(1.5138\cdot10^{-4}\) written. None changes a printed figure; all
three were caught only because the statements had to pass `linarith`.

*Lemma 5.1's master identity is proved, not sampled
(`formal/Problems/Juggler/MasterIdentity.lean`, 10 theorems).* This was
the last place in Sections 4--6 where a claim rested on the probe's
60-digit sampling on random odd \(n\). The identities are exact, so
they are now theorems. Three pieces.

(a) **(iv) reduces to one substitution plus `ring`.** The four-point
product rule
\(\Delta\Delta(cf)=c_{11}\Delta\Delta f+(\Delta_2c)(n{+}d_1)\Delta_1f
+(\Delta_1c)(n{+}d_2)\Delta_2f+(\Delta\Delta c)f\), which the
manuscript verifies "by expanding both sides", is `ring` on eight reals.
Every carry substitution in (iv) is the single lemma
\(\{y{+}w\}-\{y\}=\{w\}-\kappa\), itself a corollary of the
Lemma 4.3(ii) carry identity proved earlier. The master identity is those
two, and the bracket bound \(\le2\) follows from
\(\{\cdot\}\in[0,1)\) and \(\kappa\in\{0,1\}\).

(b) **(i) has a closed form, like Lemma 4.3(i).** With \(a=\sqrt v\),
\(b=\sqrt Y\) the remainder is exactly
\(R=\tfrac14(b-a)^2(2b+a)\); \(R\ge0\) by inspection and
\(Ra\le\tfrac3{16}\theta_2^2\) reduces to \((a+3b)(a-b)\le0\). No
Taylor expansion, no mean value. The printed \(\tfrac3{16}\) is nearly
sharp --- sampling odd \(n\le10^7\) reaches \(0.1867\).

(c) **What is still not covered.** Lemma 5.1(iii)'s branch-freeze
inventory is analytic (two mean value theorems and the numerical ranges
of \(\beta_i\)) and remains outside. So does everything downstream.

*Lemma 5.1(iii) (`formal/Problems/Juggler/BranchFreeze.lean`, 16
theorems).* The last analytic part of Lemma 5.1. The two mean value
theorems producing \(\xi_1,\xi_2\) are hypotheses; everything on top
of them is proved: the exact regrouping, the offset bound
\(|j|\le3\), the \(\beta\)-product bound, all four printed
derivative estimates, and the run-length conclusion. The substitution
\(n=s^4\) again keeps everything polynomial.

**Finding: the printed \(|G''|\le2|j|P^{-5/4}+25h_1h_2P^{-7/4}\) is
not valid term by term.** The two \(\beta_1\beta_2\) contributions to
\(G''=F''(X)X'^2+F'(X)X''\) are \(+\tfrac{81}{64}\) and
\(-\tfrac9{32}\), of opposite sign, leaving \(\tfrac{63}{64}\).
With \(\beta_1\beta_2\le19h_1h_2P\) that gives
\(18.7\le25\); bounding the two separately gives
\(\tfrac{99}{64}\cdot19=29.4>25\). The bound is correct, its obvious
derivation is not, and nothing in the manuscript pointed at the
cancellation. The same happens for the \(j\)-terms
(\(-\tfrac{27}{32}+\tfrac9{16}=-\tfrac9{32}\), against a printed
\(2\)). Now recorded in the manuscript and in Lean
(`Gsecond_beta_cancellation`, `Gsecond_naive_bound_fails`).

Two smaller things. The manuscript's \((3\sqrt2)^2=18\) for
\(\beta_1\beta_2\) drops the \(+1\)s in
\(\beta_i\le3\sqrt2h_iP^{1/2}+1\); carried honestly the product is
\(\le19h_1h_2P\) for \(P\ge100\), which every later constant
absorbs. And on \(300\) sampled \((P,n,h_1,h_2)\) the printed offset
range is nearly attained at the bottom --- ratio to \(|j|P^{3/4}\) over
\([1.510,2.514]\) against the printed \([1.5,2.6]\) --- while the
second-difference range \([1.4,15]\) is never tested below \(6.75\).

*The two mean value theorems of Lemma 5.1(iii) are discharged
(`formal/Problems/Juggler/MeanValues.lean`, 9 theorems). Lemma 5.1 is now
unconditional.* Two of the three ingredients turn out to need no analysis:
\(x^{3/2}\) has *explicit* mean values in root coordinates. With
\(a=\sqrt A\), \(b=\sqrt{A+j}\), the first is
\(c=\tfrac23(a^2{+}ab{+}b^2)/(a{+}b)\), and \(a\le c\le b\)
reduces to \((2b{+}a)(b{-}a)\ge0\), \((2a{+}b)(a{-}b)\le0\). The
inner step of the second is the **arithmetic mean of the square roots**:
\(F'(A{+}B)-F'(A)=BF''(\eta)\) with
\(\sqrt\eta=\tfrac12(\sqrt A+\sqrt{A{+}B})\), identically. Only the
outer step uses a genuine mean value theorem (Mathlib's, applied to
\(g(t)=F(t{+}\beta_2)-F(t)\)); rationalising its increment gives the
two-sided bound the inventory uses, and \(\xi_2\) itself as
\(\sqrt{m{+}\xi_2}=\tfrac34\beta_1\beta_2/\Delta\Delta\).

Throughout, \(x^{3/2}\) is written \(x\sqrt x\), so the derivative
comes from `Real.hasDerivAt_sqrt` and no real-power machinery enters.
Sampling puts \(\xi_2\) at \(0.32\)--\(0.52\) of
\(\beta_1{+}\beta_2\), well inside the claimed \((0,\beta_1{+}\beta_2)\).

*Lemma 5.2(i): the six stages, attacked.* Stages 1--5 recompute clean
from their stated inputs. Stage 1's \(A_h=-\tfrac{27}8h^2\nu^{1/4}\)
is right (the \(h^2\) terms are \(-\tfrac9{16}\) and
\(-\tfrac{45}{16}\), and the \(\nu^{5/4}\) parts cancel exactly);
Stage 4's \([0.35,1.20]\), Stage 5's \([4.4,9.1]\) band, \(3.1\),
\(0.37\), \(0.47\) and \(37/48<7/8\) all check.

**Material finding, in Stage 6 / the class (D3).** The decoration class
(D3) was stated with \(|\varphi''|\le3kh_1h_2P^{-5/8}\), but Stage 6
never uses that budget: it dominates via \(2h|\varphi'''|\), which
bounds \(|(\Delta_{2h}\varphi)''|\) and *not* a general class-(D3)
\(|\varphi''|\). Claim E in fact delivers
\(|(\Delta_{2h_3}\varphi)''|\le6kh_1h_2h_3P^{-13/8}\) and then
*relaxes* it to the printed budget --- which is larger by
\(P/(2h_3)\), a factor \(\ge\tfrac12P^{7/8}\). Inside the printed
class the ratio to the Stage-4 curvature is
\(8.6\,kh_1h_2P^{1/8}/(uh)\), reaching \(8.6P^{1/4}\) at
\(uh=1\); at any \(uh\le8.6P^{1/4}\) such a \(\varphi''\) cancels
the Stage-4 curvature outright and Lemma 3.3 at that scale does not
apply. So **(i) as stated admitted decorations its own Stage 6 cannot
handle** --- the (C5) pattern again: statement wider than proof, every
actual application inside the narrow class.

Fixed by giving (D3) the differenced budget
\(|\varphi''|\le6kh_1h_2h\,P^{-13/8}\) (with \(2h\) the shift of
(i)), which is exactly what Claim E has in hand; the Stage-6 ratio is
then \(18P^{-3/4}\), matching the manuscript's own parenthetical.
Part (ii)'s input \(\varphi\) is decoupled from (D3) and stated
directly by \(|\varphi'''|\le3kh_1h_2P^{-13/8}\), which is what
Claim E says every application supplies. No constant downstream moves;
the checked invocations --- Claim F, and Step 5b(3b) where
\(|(\Delta_2c)''|\le0.19kh_2P^{-15/8}\) --- are both inside the new
budget with room. Lean `stage6_D3_differenced_dominated`,
`stage6_D3_printed_not_dominated`, `stage6_D3_gap`.

Two rounding slips beside it: Stage 3(s1) prints
\(\min(2,2\pi|B|)\le14P^{-1/16}\) where \(2\pi\cdot2.25=14.14\)
(now \(14.2\)); Stage 5 prints the intermediate
\((1/4.4)^{1/3}=0.62\) where it is \(0.611\) --- with \(0.62\) the
displayed chain gives \(0.77\cdot0.62=0.477>0.47\), though the final
\(0.47\) is correct from the exact value. Neither changes an estimate.

*The wide (D3) case: partially closed, and the remainder named.* Asked
to close it properly, the honest outcome is: **not closed**, but the
boundary is now exact and one earlier claim of mine was wrong.

*Correction.* I suggested last entry that (i) might be *false* on the
wide class. It is not, on the evidence: the natural counterexample
\(\varphi=\tfrac{27}{10}\nu^{5/4}\) --- which lies in the wide class
at \(u=h=k=h_1=h_2=1\) and cancels the smooth part of the Stage-4
curvature exactly --- gives block sums \(36,12,220,479,385\) at
\(P=2\cdot10^3\dots5\cdot10^5\), i.e. \(\approx P^{1/2}\), far
inside \(P^{7/8}\). So (i) is *unproved* on the wide class, not false.

*Why it survives.* Cancelling the curvature does not help the adversary,
because it moves the problem into a regime where a *different* test
applies. The frozen \(G=\lfloor\delta_h\rfloor\) steps by exactly
\(1\) at each cell boundary, so \(f''\) carries a sawtooth of
amplitude \(\tfrac9{32}u(\nu{+}2h)^{-5/4}\) that no continuous
\(\varphi''\) can follow, and \(f'\) jumps by
\(\tfrac98u(\nu{+}2h)^{-1/4}\) at every boundary. Consequently the
cells are *flat* (\(\mathrm{amp}\cdot\ell^2\le0.26uP^{-1/4}h^{-2}<1\)
in regime B once \(h\ge3\); measured \(\approx3\cdot10^{-3}\)), so
Kusmin--Landau replaces van der Corput; and \(f'\) sweeps
\(\ge1.17uhP^{1/4}\) full periods across the cells (measured: \(19\)
to \(37\)), so the cell frequencies are spread.

*What is proved.* Regime A, \(uh\ge34.3kh_1h_2P^{1/8}\): the
undifferenced budget is dominated and Stage 6 applies verbatim (Lean
`wideD3_regimeA_dominated`). Regime B is a small-\(uh\) regime,
\(uh<34.3P^{1/4}\) by (C1) (`wideD3_regimeB_small`); there the cells
are flat (`wideD3_cells_flat`) and the frequency sweep is bounded below
(`wideD3_frequency_sweep`).

*Regime B, closed but for a sliver.* The obstruction is sharper than
"an equidistribution input". Writing \(t=\{\delta_h\}\) and
\(q=\tfrac98u(\nu{+}2h)^{-1/4}\), one has
\(f'=\Psi-qt\) with \(\Psi=\tfrac{27}8uh\nu^{1/4}+uA_h'+\varphi'\):
the decoration enters *only* through \(\Psi\), and \(-qt\) comes from
the frozen \(G\). Since \(t\) sweeps \([0,1)\) on every cell, the
dichotomy is whether \(\Psi'\) cancels that sweep. Put
\(D_i=\Psi'-q/\ell\).

**(a) \(|D_i|\ge q/(2\ell)\): closed.** \(f'\) is monotone and sweeps
\(\ge q/2\) on the cell; the dyadic Kusmin--Landau split (piece \(j\)
has length \(\ll2^{-j}\ell\) and bound \(\ll2^j/q\), balanced at
\(2^j=(\ell q)^{1/2}\)) gives a cell total
\(\ll(\ell/q)^{1/2}\le1.01(uh)^{-1/2}P^{3/8}\), hence
\(\ll1.6(h/u)^{1/2}P^{7/8}\) over the block --- *exactly* the second
printed term of (i). This holds for every \(u\).

**(b) \(|D_i|<q/(2\ell)\): closed for \(u\le P^{1/8}\).** The case is
confined to \(uh\le6kh_1h_2P^{1/8}\) by the budget. There \(f'\) is
nearly constant per cell at \(\alpha_i=\Psi(\nu_i)\), with
\(\alpha_{i+1}-\alpha_i\asymp q\asymp uP^{-1/4}\), and \(\Psi\)
monotone sweeping \(V\asymp uhP^{1/4}\) periods, giving
\(\sum_i\min(\ell,\lVert\alpha_i\rVert^{-1})
\ll P^{5/8}\log P+1.1uP^{3/4}\). The second term is \(\le P^{7/8}\)
iff \(u\le0.9P^{1/8}\).

**What is left** is the sliver \(P^{1/8}<u\le6kh_1h_2P^{1/8}/h\) inside
case (b), where the argument charges a whole cell to each of the \(V\)
crossings of \(\Psi\) through \(\mathbb Z\). Those cells carry
different constant terms and should not add coherently, so the \(V\ell\)
is lossy; making the saving explicit needs the classical
\(\sum_{i<N}\min(\ell,\lVert iq\rVert^{-1})\) estimate for a
*slowly varying* \(q\), which is not carried out here.

*The sliver is a narrow-class problem (this turn).* Case (b) looks like
the wide class but is not. Its defining condition \(|D_i|<q/(2\ell)\)
reads \(\Psi'\in(q/2\ell,3q/2\ell)\), and with
\(q/\ell=\tfrac{27}{16}uh\nu^{-3/4}\),
\(\Psi'=\tfrac{27}{32}uh\nu^{-3/4}+\varphi''\), this pins
\[
0<\varphi''<\tfrac{27}{16}uh\nu^{-3/4}.
\]
So in the only case left open, \(|\varphi''|\) is at most \(4.83\)
times the Stage-4 curvature --- the wide budget \(\Phi_2\), larger by
\(P/(2h)\), is *never* attained there. The wide class collapses to a
narrow one exactly where it mattered (Lean
`wideD3_caseB_confines_phi`, `wideD3_caseB_ratio`).

Two consequences. \(\Psi\) is strictly increasing with
\(\Psi'\in[0.84,2.53]uh\nu^{-3/4}\), so the cell frequencies
\(\alpha_i\) increase with gaps in \([0.562,1.688]uP^{-1/4}\), of
bounded ratio \(3\) (`wideD3_caseB_gaps`). And in the extreme sub-case
\(\Psi'\equiv q/\ell\) one has \(\Psi'=q\delta_h'\), so
\(\alpha_i\approx qG_i+\)const with \(G_i\) consecutive integers:
an approximate arithmetic progression of difference
\(q\asymp uP^{-1/4}\) that *drifts by \(19\%\)* across the block,
since \(q=\tfrac98u(\nu{+}2h)^{-1/4}\). That drift is what stops the
progression locking onto a rational, and it is precisely the saving the
crude \(V\ell\) discards.

*The sliver, measured.* At \(h=1\), maximising over the free linear
term, for \(u\) up to the top of the sliver: case (b) gives
\(192,234\) at \(P=8\cdot10^3\) (\(u=1,13\)) and
\(475,546,544\) at \(P=3.2\cdot10^4\) (\(u=1,7,13\)), against
printed bounds \(5478,4315,18154,13788,13536\) --- ratios
\(0.035,0.054,0.026,0.040,0.040\), stable across the sliver and falling
with \(P\). At \(P=3.2\cdot10^4\), \(u=13\) the crude \(V\ell\)
is \(34\,214\) against an actual \(544\): the period-counting step is
lossy by a factor \(63\) there, and that factor is the whole of the
remaining gap.

*The adversary, measured.* The decoration may carry a linear term, so
the honest test maximises over it --- on the natural grid, a DFT of
\(e(f(n))\). At \(u=h=k=h_1=h_2=1\) the optimum over all class-(D3)
linear shifts is, for the undecorated phase and the two extremal
decorations \(\varphi=\pm\tfrac{27}{10}\nu^{5/4}\):
\(169/192/397\) at \(P=8\cdot10^3\), \(383/475/1035\) at
\(3.2\cdot10^4\), \(792/958/2536\) at \(1.28\cdot10^5\), against
\(P^{7/8}=2601,8750,29431\). The worst case grows like \(P^{0.67}\)
and its ratio to \(P^{7/8}\) *falls*: \(0.152,0.118,0.086\). The
drift-cancelling decoration is the stronger of the two, as the analysis
predicts. Lean `wideD3_caseA_total`, `wideD3_caseB_confined`,
`wideD3_caseB_closes`.

*Correction to the previous entry.* The \(P_1\) recorded above as
\(3.2\cdot10^{37}\) was wrong. It collected the three middle-band
costs into a single coefficient of \(P^{89/96}\), but the \(r=3\)
transition is \(\asymp P^{41/48}=P^{82/96}\); collecting it
over-counts by \(P^{7/96}\). Computed honestly --- least \(P\) with
\(4PW/(c_7S)+P(W/(c_7S))^{1/2}+3.5P^{13/24}V^{-1/2}\le P\) --- the
value at the old operating point was \(2.1\cdot10^{21}\). The
direction of the \(c_7\) trade is unchanged (raising \(c_2\) still
sends \(P_1\) from \(5.0\cdot10^{19}\) to \(5.3\cdot10^{23}\)),
so the decision to keep the uniform constant stands.

*The thresholds stratify.* Twenty-eight of the thirty-one hold from
\(2.9\cdot10^{10}\) on, and that value is set by a soft
regime-naming inequality (\(2.25P^{-1/16}<\tfrac12\), Stage 3(s1)).
The four Lemma 3.9 balance comparisons of Steps 5a and 5b carry the
remaining six orders alone. That is a statement about one lemma:
\(V\le c_7S/2\) is a *hypothesis* of Lemma 3.9, and its size is
fixed by \(c_7=1/\lVert M^{-1}\rVert_\infty=1/232\), exact at the
Step 5b exponent triple and so not improvable there.

*What was not re-derived.* The \(\rho_0\) ratios
of Lemma 5.2b are now displayed and sit under \(1/2304\). The exact
shift device of Theorem 4.4, Step 4, and the
\(O(\log^3P)\) coefficient-mass bookkeeping were read and accepted,
not re-derived; Lemma 3.7 was re-read and found consistent. The
\(P_0\) certificate transcribes each printed inequality into a
predicate; it does not certify that they are the right inequalities,
and two of its inputs (the \(\tilde\beta\)-substitution error and
the wave remainder) are conservative substitutes for statements the
paper leaves in \(O(\cdot)\) form, both clearing \(\rho_0\) by
more than nine orders. Claims A–H of Lemma 5.2(ii)\(\to\)(i), the (D3) closure
\(3\to6\), the printed (D1) remainder, and the Theorem 5.3
Step 4 leftover-mode split are now written on the manuscript.
A second human reading of the six-stage proof of Lemma 5.2(i)
and of Steps 5a–5b remains the most valuable check this paper
can receive; this file is not that reading.


## Section 6, audited

Section 6 carries the headline density results and was the least-audited
part of the paper. Every constant it prints was recomputed from its
stated inputs. The bookkeeping is sound throughout --- in particular the
whole `OOEO*` branch of Theorem 6.3, twelve constants from `B'\asymp
kn^{-7/16}` to the balance `J_*=P^{5/48}`, is exactly right --- and four
things were wrong.

*Theorem 6.1, Step B: the depth-four identity is correct, and sharper
than it looks.* The six-term expansion of `v^{3/2}` as a polynomial of
degree \((2,1)\) in \((m,v)\) is not an ad hoc fit. Its \(m\)-block is
the degree-2 Taylor polynomial of \(-\tfrac12(1+\varepsilon)^{9/4}\) and
its \(v\)-coefficient is that of \(\tfrac32(1+\varepsilon)^{3/4}\), with
\(\varepsilon=(m-n^{3/2})/n^{3/2}\); that is why the six coefficients sum
to \(1\) at the base point, why the \(m\)-derivative vanishes there (it
must: \(v^{3/2}\) does not depend on \(m\)), and why the error is
\(O(n^{-9/8})\). Checked numerically at 60 digits on \(n\) up to
\(10^7\): the worst \(|\mathrm{err}|\,n^{9/8}\) is \(0.375\), exactly the
predicted leading constant \(\tfrac38\), against the printed \(\tfrac34\).
Lean `stepB_exact_at_base`, `stepB_m_derivative_vanishes`,
`stepB_v_coefficient`, `stepB_m_block_in_epsilon`, `stepB_v_block_in_epsilon`.

*The cost of discarding that error was over-stated by a factor \(P\).*
The draft printed \(\le2\pi kP^{-1/8}\cdot P\le7P^{7/8}\). But
\(P^{-9/8}\cdot P=P^{-1/8}\) already *is* the sum over the block; the
line multiplies by the block length twice. It also needs \(2\pi k\le7\),
i.e. \(k\le1.11\), while \(k\) runs to \(2P^{1/96}\). The true cost is
\(2\pi\cdot\tfrac k2\cdot\tfrac34P^{-9/8}\cdot P=\tfrac{3\pi k}4P^{-1/8}
\le4.8P^{-11/96}\), which is under **one unit** from \(P\ge7.6\cdot10^5\)
--- and \(0.12\) at \(P_0\), against a printed bound of \(7\cdot10^{12}\).
Corrected. Probe row `t61-stepB-discard`, Lean `stepB_discard`.

*Theorem 6.1, Step E: `V >= 0.065 P^{-37/48}` is false; the value is
\(0.0645\).* At \(S\ge0.60P^{-5/8}\), \(V=\tfrac1{12}S^{1/2}P^{-11/24}\)
gives \(\tfrac1{12}\sqrt{0.60}=0.06455\). Off by \(0.7\%\) in the unsafe
direction; corrected to \(0.064\). The threshold it feeds,
\(1.6\cdot10^{13}\), is unaffected and was confirmed exactly
(\(1.612\cdot10^{13}\), probe row `5a-W<=c7S`). Lean
`stepE_j0_V_constant`, which brackets \(\tfrac1{12}\sqrt{0.6}\) by
squaring rather than by taking a root.

*Everything else in Step E checks.* \(945/512-864/512=81/512\);
\(B=\tfrac{27}{32}\) is \(\tfrac32\) times the bare kernel \(\tfrac9{16}\);
the composite \(81/512-324/512=-243/512\) is single-signed. Both printed
\(\lambda\) ranges are *safe but loose* on \(\nu\in(P,2P]\): the true
ranges are \((0.4352,0.4746]\) inside the printed \([0.40,0.52]\), and
\((0.6934,1.0694]\) inside \([0.60,1.25]\). They were left loose, since
the slack absorbs corrections the paper states only as \(O(\cdot)\);
tightening \(\lambda_0'\) to \([0.69,1.07]\) would drop the \(j=0\)
threshold from \(1.61\cdot10^{13}\) to \(1.03\cdot10^{13}\) and does not
move \(P_0\). The interpolant coefficient \(b'=-365/176\) is *exactly*
\(405\cdot1095/1215\), so it scales with the anchor it is built from ---
a good sign that \(1095/1024\) was propagated and not guessed. Lean
`stepE_offset_survivor`, `stepE_B_ratio`, `stepE_offset_composite`,
`stepE_lambda_a_range`, `stepE_lambda_0_range`, `stepE_b_scales_with_anchor`.

*Lemma 6.2 is correct.* Both identities, all nine remainder terms and
all four orders were re-derived. One gap in the prose: the enumeration
"the last three terms are \(O(n^{-21/16})\), \(O(n^{-45/16})\),
\(O(n^{-81/16})\)" skips the second term, \(\tfrac12v^{-3/4}=O(n^{-27/16})\).
Added.

*Theorem 6.3 cites a superseded (D3) budget, and the ratio is garbled.*
The passenger check reads "inside class (D3)
\((|\varphi''|\le3kh_1h_2P^{-5/8})\) by
\(P^{-35/16}/P^{-9/16}=P^{-13/8}\)". Under that budget the ratio would be
\(P^{-25/16}\); the printed \(-9/16\) and \(-13/8\) are the ratio and the
exponent of the *current* budget \(6kh_1h_2hP^{-13/8}\), written into
each other's slots. Corrected to
\(P^{-35/16}/P^{-26/16}=P^{-9/16}\); the conclusion holds, with more room
than claimed. (The \(P^{-5/8}\) budget elsewhere in the paper is the
deliberately *wide* class of the Stage 6 discussion and is correct there.)

*Theorem 6.3's Lemma 3.7 window is not legal at \(P_0\).* This is the
substantive finding. The fifth-letter sawtooth coefficient is
\(|C|\le1.30P^{19/96}\) and the window is opened at \(T=P^{1/4}\), so the
hypothesis \(T\ge8(1+|C|)\) has a margin of only \(P^{5/96}\) --- and at
\(P_0=8.9\cdot10^{13}\) it *fails*: \(T=3.07\cdot10^3\) against
\(8(1+|C|)=5.92\cdot10^3\), short by a factor \(1.93\). The draft's
"since \(8|C|/T\le16P^{-5/96}\to0\)" is an asymptotic argument, correct
as such, printed under a heading that claims effectivity at \(P_0\).
The hypothesis first holds at \(2.55\cdot10^{19}\).

Fixed, provisionally, by giving Theorem 6.3 its own threshold
\(P_0^{(5)}=2.6\cdot10^{19}\). **Superseded by the next entry**, which found
a second and worse failure at the same site and repaired both by raising
\(R_0\); the figure \(2.6\cdot10^{19}\) was too small, and Theorem 6.3 now
carries no threshold of its own. The alternative was checked
and recorded: opening the window at \(T=P^{5/16}\) restores \(P_0\) (the
hypothesis then holds from \(7.5\cdot10^8\)), at the price of carrying
\(R_0=P^{5/16}\) through Stage 2 of Theorem 5.3, where the collision-band
term grows from \(3P^{7/8}\log P\) to \(3P^{29/32}\log P\) --- still
inside \(P^{23/24}\) --- and the Stage 5a slow-mode bound loses
\(P^{5/96}\). Whether that trade is worth taking needs a re-reading of
Stage 2 that was not done here, so it is left as a recorded option.
**No exponent in any statement changes**; \(P_0\) itself is untouched at
\(8.9458\cdot10^{13}\). Probe `depth5_thresholds`, Lean
`row_t63_window`, `row_t63_window_fails_at_P0`,
`row_t63_window_alternative`.

*Corollary 6.4 is correct*, including the disjointness of the five
prefixes and \(\tfrac12+\tfrac14+\tfrac1{16}+\tfrac1{32}+\tfrac1{32}
=\tfrac78\), and the error is indeed the worse of the two fifth-letter
exponents.

*A cosmetic defect not repaired.* Item numbers run one block ahead of
their section numbers in Sections 2--5 (Lemma 3.3 is in \S2, Lemma 5.1
in \S4, Theorem 6.1 in \S5, while Lemma 6.2 onwards is in \S6): the
numbering is a legacy of an earlier sectioning. Every "Section \(N\)"
cross-reference in the prose was checked and every one is consistent
with the *headers*, so nothing points anywhere wrong. Renumbering would
rename `Lemma 5.2b` and its siblings across the manuscript, the Lean
development, the probe and this ledger, which is a large mechanical
change with no mathematical content; left as it stands, and recorded
here so a referee's first remark has an answer.

## The depth-five threshold, resolved: \(R_0=P^{5/16}\)

The previous entry recorded that Theorem 6.3's Lemma 3.7 window is not legal
at \(P_0\), and left the repair --- raising Stage 2's truncation \(R_0\) ---
as an option needing a re-reading of Stage 2. That reading was done. Two
things came out of it.

*The window was not the binding requirement.* The same fifth-letter Lemma 3.7
application has a second cost, the flat cost \(8(1+\lvert C\rvert)/T\) per
point, which over a block must stay inside \(P^{1-1/96}\). At \(T=P^{1/4}\)
that reads \(10.25\,P^{1-5/96}\le P^{1-1/96}\): the *exponent* clears, but
only by \(4/96\), so the constant \(10.25\) is not absorbed until
\(10.25^{24}=1.8\cdot10^{24}\). That is five orders worse than the window's
\(2.55\cdot10^{19}\) and ten orders above \(P_0\). The
\(P_0^{(5)}=2.6\cdot10^{19}\) recorded in the previous entry was therefore
**too small**; the honest figure at \(R_0=P^{1/4}\) is \(1.8\cdot10^{24}\).
This is the same defect as the window, at the same site, and it was missed the
first time because the printed line stops at the exponent comparison
\(O(P^{1-5/96})\subseteq P^{1-1/96}\), which is true and, for an effective
threshold, not enough.

*Raising \(R_0\) is affordable, and \(5/16\) is the right value.* Four printed
inequalities depend on \(a\) where \(R_0=P^a\), two paid for by raising \(a\)
and two bought by it, so \(a\) is pinned from both sides:

| \(a\) | collision | \(q''\) | window | flat cost | worst |
|---|---|---|---|---|---|
| \(1/4\) | \(5.3\cdot10^{5}\) | \(3.0\cdot10^{10}\) | \(2.5\cdot10^{19}\) | \(1.8\cdot10^{24}\) | \(1.8\cdot10^{24}\) |
| \(9/32\) | \(1.1\cdot10^{7}\) | \(6.6\cdot10^{10}\) | \(1.4\cdot10^{12}\) | \(7.4\cdot10^{13}\) | \(7.4\cdot10^{13}\) |
| \(5/16\) | \(1.4\cdot10^{9}\) | \(3.0\cdot10^{11}\) | \(7.4\cdot10^{8}\) | \(5.5\cdot10^{9}\) | \(3.0\cdot10^{11}\) |
| \(1/3\) | \(2.8\cdot10^{11}\) | \(1.6\cdot10^{12}\) | \(3.5\cdot10^{7}\) | \(1.4\cdot10^{8}\) | \(1.6\cdot10^{12}\) |
| \(3/8\) | \(8.0\cdot10^{22}\) | \(1.1\cdot10^{15}\) | \(6.9\cdot10^{5}\) | \(1.5\cdot10^{6}\) | \(8.0\cdot10^{22}\) |

\(5/16\) minimises the last column. \(9/32\) also clears \(P_0\), but by less
than a factor \(1.3\), which is not a margin worth printing; \(1/3\) clears it
too and is worse. The substitution was made throughout: Stage 2, Stage 3(s1)'s
majorant, Stage 5's collision band, Step 5b(a)'s \(q''\), and both
\(R_0\)-dependent bullets of Theorem 6.3.

*What it costs.* The Stage 2 majorant *improves*, \(4P^{3/4}\to4P^{11/16}\).
The collision-band sum degrades, \(3P^{7/8}\log P\to3P^{29/32}\log P\), and
stays inside \(P^{23/24}\) with exactly \(P^{5/96}\) to spare. The \(q''\)
curvature ratio degrades from \(52P^{-5/24}\) to \(48.9P^{-3/16}\), which at
\(P_0\) is \(0.12\) against the margin \(\tfrac14\). That last row,
\(3.0\cdot10^{11}\), is now the worst threshold in the certificate outside the
three Lemma 3.9 balance comparisons --- it displaces \(2.9\cdot10^{10}\) --- and
it is still two and a half orders below \(P_0\).

*What it buys.* Theorem 6.3 no longer carries a threshold of its own. Every
threshold in the paper is \(P_0=8.9458\cdot10^{13}\), unchanged, still binding
at Step 5b's \(W\le c_7S/2\). (**Superseded by the constants sweep below**,
which found a larger row: \(P_0=2.82\cdot10^{14}\), binding at Claim D. The
statement that Theorem 6.3 needs no threshold of its own still holds.) No exponent in any statement moves: \(1/96\),
\(23/24\), \(43/48\) and \(7/8\) are all as printed.

New: Appendix A.6; four probe rows (`st2-collision`, `st5b-qpp`,
`t63-window`, `t63-flat`), taking the certificate from 31 to 35; `r0_tradeoff`
in the probe; Lean `row_st2_collision`, `row_st5b_qpp`, `row_t63_window`,
`row_t63_flat`, `row_t63_window_fails_at_quarter`; 14 more exponent checks
(208 to 222).

*The general lesson, recorded because it recurred twice at the same site.*
Both defects were exponent comparisons that are correct asymptotically and
insufficient effectively: \(O(P^{-5/96})\to0\) for the window, and
\(O(P^{1-5/96})\subseteq P^{1-1/96}\) for the flat cost. In a paper claiming
an explicit \(P_0\), every \(\to0\) and every \(\subseteq\) between two powers
whose gap is a small fraction needs its constant carried, because the crossing
is the constant raised to the reciprocal of that gap. A gap of \(4/96\) turns
a constant of \(10\) into \(10^{24}\). The probe now transcribes such lines
with their constants rather than their exponents.


## The constants sweep: P_0 was wrong by a factor 3.2

The Theorem 6.3 defects were both of one shape --- a comparison of two powers,
correct asymptotically, whose constant is not carried at the printed threshold.
The general rule is that a gap \(g\) between two exponents turns a constant
\(c\) into a threshold \(c^{1/g}\). This entry sweeps the manuscript for that
shape systematically (`research.juggler_sequence.paper_b_constants_sweep`),
in two forms: a decaying term against a fixed margin, and a cost claimed
*inside* a larger power. Twenty-five distinct comparisons; two above \(P_0\),
both real.

*The binding one: Claim D's shift range --- found, then resolved.* (The entry
below records the finding as it stood; the resolution is the section after
it. Net effect on \(P_0\): none.)
Claim D of Lemma 5.2(ii)\(\to\)(i) checks that every index of the Claim C sum
is a legal shift for part (i), i.e. \(h_3\le P^{1/8}\). The available bound is
\(h_3\le t^{1/3}P^{1/12}\le16^{1/3}P^{7/72}=2.52P^{7/72}\), so the requirement
is
\[
2.52\,P^{7/72}\le P^{1/8},
\qquad\text{gap}\ \tfrac18-\tfrac7{72}=\tfrac1{36},
\qquad\text{threshold}\ 2.52^{36}=2.8211\cdot10^{14}.
\]
The manuscript stated the threshold correctly and then wrote that it "sits
under the standing \(P_0\) of size \(10^{24}\)" --- a \(P_0\) from a much
earlier draft. At the present \(P_0=8.9458\cdot10^{13}\) the comparison
**fails**, and it fails narrowly: \(P_0^{1/36}=2.441\) against \(2.52\), a
miss of \(3\%\). So \(P_0\) rises from \(8.9\cdot10^{13}\) to
\(2.82\cdot10^{14}\), a factor \(3.15\), and the binding row is no longer the
Lemma 3.9 balance but a hypothesis-admissibility check with a mild constant on
a tiny gap.

Three consequences, all now printed. The Lemma 3.9 balance
\(W\le c_7S/2\) is second at \(8.9\cdot10^{13}\), so A.5's "\(P_0\) is carried
entirely by \(W\le c_7S/2\)" is no longer true and is qualified. The
\(\kappa\)-optimisation **saturates**: since Claim D's row does not involve
\(\kappa\), lowering \(\kappa\) below \(\tfrac18\) no longer moves \(P_0\) at
all (the A.2 table now shows both columns), and the operating point
\(\kappa=\tfrac1{12}\) is justified by \(P_1\) alone. And the \(c_2\) lever of
A.5 no longer improves \(P_0\) either --- only \(P_1\), which it worsens.

The cheapest way to undo this would be to sharpen \(t\le16P^{1/24}\): a bound
\(t\le cP^{1/24}\) moves \(P_0\) to \(c^{12}\), so \(c=8\) would give
\(6.9\cdot10^{10}\) and hand the threshold back to the balance row. Not
attempted here. Lean `claimD_shift_range`, `claimD_shift_fails_below`; probe
row `claimD-shift`.

*The second one: Step 3(a)'s flat cost.* The manuscript printed
\(23P^{19/24}\le P^{7/8}\). The gap is \(\tfrac1{12}\), so that needs
\(23^{12}=2.2\cdot10^{16}\) --- false at \(P_0\) by a factor \(245\). But
\(P^{7/8}\) is not the operative budget: Step 6 assembles against
\(P^{23/24}\), and \(23P^{19/24}\le P^{23/24}\) holds from
\(23^{6}=1.5\cdot10^{8}\). Restated; no threshold impact. Lean
`st3a_flat_cost`.

*A third, cosmetic but worth removing.* Step 5b(a) printed its ratio as
\(\le48.9P^{-3/16}\le49P^{-1/16}\). The weaker form is true and was meant as a
"at least this small" remark, but a constant of \(49\) on a gap of
\(\tfrac1{16}\) does not clear \(\tfrac14\) until \(10^{36}\): quoting it as
the conclusion would be a fourth instance of exactly this error. Dropped, with
the reason printed.

*What the sweep did not find.* Everything else is clear of \(P_0\) with room:
the next largest are \(96P^{-5/24}\) (Claim G, \(2.5\cdot10^{12}\)) and the
Step 5b(a) \(q''\) ratio (\(1.7\cdot10^{12}\)). Shape A now flags nothing above
\(P_0\); shape B flags only Claim D, which is \(P_0\) by definition. The sweep
is a regression test (`test_paper_b_constants_sweep.py`), so a new comparison of
this shape cannot enter the manuscript unnoticed.


## Claim D resolved: the sharp \(t\), and \(P_0\) stays at \(8.9\cdot10^{13}\)

The sweep's binding finding turned out to be a slack bound, not a real
constraint, and removing the slack is free.

Claim D bounds the Claim C index by \(h_3\le t^{1/3}P^{1/12}\) and needs it
under \(P^{1/8}\). Which bound on \(t\) is carried decides the row, because the
gap \(\tfrac18-\tfrac7{72}=\tfrac1{36}\) pays any constant at the thirty-sixth
power:
\[
|t|\le16P^{1/24}\ \Rightarrow\ 16^{12}=2.8\cdot10^{14},
\qquad
|t|\le3P^{1/24}\ \Rightarrow\ 3^{12}=5.3\cdot10^{5}.
\]
The \(16\) is the *individual* hypothesis \(|q_d|\le4P^{1/24}\) summed over the
four elements of \(\mathcal D\) --- the worst case the lemma's statement
permits. But Lemma 5.2(ii) is invoked exactly once, in Step 4 of Theorem 5.3,
and that invocation already prints its own bound: \(|t|\le3J_2\le3P^{1/24}\),
because the wave modes arrive one per expansion layer from three layers at
truncation \(J_2=P^{1/24}\). The total frequency is five times smaller than the
sum of the individual budgets, and it always was.

So the fix is to carry it: Lemma 5.2(ii) now has \(0<|t|\le3P^{1/24}\) among
its hypotheses, alongside the unchanged \(|q_d|\le4P^{1/24}\). Every invocation
supplies it --- Theorem 5.3 Step 4 directly, and the Theorem 6.1 and 6.3
passengers because both explicitly leave \(t\) unchanged while growing the
individual \(q_d\) to \(4P^{1/24}\). Claim D's row falls from
\(2.82\cdot10^{14}\) to \(6.4\cdot10^{5}\), and:

\[
P_0=8.9458\cdot10^{13},
\]
unchanged, binding again at Step 5b's \(W\le c_7S/2\). The \(\kappa\) table,
the \(c_2\) lever and A.5's "\(P_0\) is carried entirely by \(W\le c_7S/2\)"
all revert to what they were. The product-range check of Claim D improves too,
from \(41P^{5/36}\) (threshold \(2.9\cdot10^4\)) to \(4.33P^{5/36}\)
(threshold \(58\)).

*What was actually learned.* Nothing in the analysis changed; a hypothesis was
stated more weakly than the only application requires, and on a gap of
\(\tfrac1{36}\) that cost a factor \(3.15\) in the paper's headline constant.
The general lesson for Appendix A is now printed in A.2: a constant is harmless
only when the gap is wide, so a lemma used once should carry the bound its
caller supplies, not the loosest bound its statement admits. Lean
`claimD_shift_range` (sharp) and `claimD_loose_bound_fails_at_P0` (which
certifies that the loose version really does fail at \(P_0\), so the finding was
not spurious).
