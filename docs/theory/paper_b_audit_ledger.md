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
| Lemma 6.2, remainder bounds | hand; script `lemma_6_2_margin_certificate` | **corrected**: the two Lagrange remainders (orders \(n^{-45/16}\), \(n^{-81/16}\)) are now displayed instead of being absorbed into coefficients that have no slack when \(\theta_2\) or \(\theta_z\) is close to \(1\); Theorem 6.3 uses only the order of magnitude. **Extended**: the pre-correction form was true anyway -- the Lagrange term in the bound covers both omitted remainders from n = 5 up -- so the edge search cannot fail at any range; the six printed orders are confirmed |
| Kernel sum \(K_c(P)\), \(k=1\), \(P\le3\cdot10^6\), and the wave \(\sum e(Y(n))\) | script, OBSERVATION; `kernel_block_scaling`, `kernel_observation_reach` | **corrected reading**: "far below \(P^{1-1/96}\)" was vacuous --- that benchmark is *above* the trivial bound \(P/2\) until \(P=2^{96}\), so the ratio could not have exceeded \(1\). Both sums do sit at square-root scale, but one number per \(P\) cannot say so (local slopes scatter \(-0.13\) to \(+1.56\)); 256 block samples give exponents \(0.38\)--\(0.52\) and \(0.29\)--\(0.47\) against \(\tfrac12\) and \(1\). Still not evidence for the theorem's exponent |

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


## Proposition 7.1: the Hoeffding step replaced by the exact count

Proposition 7.1 is the paper's reduction: depth-\(d\) equidistribution gives a bound
on the starts with no contracting prefix of length \(\le d\). Its combinatorial
input was Hoeffding applied to the endpoint,
\[
\#\{w:\text{no contracting prefix}\}\ \le\ 2^{d}e^{-cd},
\qquad c=2\bigl(\tfrac{\log2}{\log3}-\tfrac12\bigr)^{2},
\]
and the conclusion carried \(2^{d}E_d(N)\) as its error term.

Two things were given away. Hoeffding keeps only \(o_d\ge\beta d\) and drops the
requirement that \(3^{o_t}\ge2^{t}\) hold at *every* \(t\le d\); and the exponential
form drops the local-limit factor. But the constraint depends on nothing beyond
\((t,o_t)\), so the count \(N_d\) is a two-line dynamic program, exact in integers at
any depth the paper will use. Both terms improve: the density becomes \(N_d/2^d\) and
the error term becomes \(N_dE_d(N)\).

*How much.* The ratio \(e^{-cd}2^{d}/N_d\) is \(6.7\) at \(d=5\), \(43.6\) at
\(d=40\), and \(1.3\cdot10^{4}\) at \(d=1600\); the error term carries \(4\) instead
of \(32\) at \(d=5\) and \(2114\) instead of \(65536\) at \(d=16\).

*Where the loss comes from, and where it does not.* Not from the rate. The sharp
value \(\rho=\min_\theta\tfrac12((3/2)^\theta+2^{-\theta})=0.965907\) gives
\(-\log\rho=0.034688\) against Hoeffding's \(0.034285\), one part in eighty. The whole
loss is polynomial:
\[
\frac{N_d}{2^{d}}\ \sim\ C\rho^{d}d^{-3/2},\qquad C\approx11,
\]
with \(d^{-1/2}\) for staying nonnegative under the zero-drift tilt and a further
\(d^{-1}\) because the tilted endpoint sits at height \(\asymp\sqrt d\). Over every
depth a theorem could occupy that factor is the whole story: the observed per-letter
rate is \(0.1696\) at \(d=24\), \(0.0635\) at \(d=200\) and still \(0.0401\) at
\(d=1600\).

*Consistency.* Two independent checks. The \(d=5\) row gives four surviving words ---
\(OOOOO\), \(OOOOE\), \(OOOEO\), \(OOEOO\) --- hence certificate density \(1-4/32=7/8\),
which is Corollary 6.4's figure reached by counting words instead of contractors. And
\(N_{200}/2^{200}=3.06\cdot10^{-6}\) with observed rate \(0.0635\) reproduces the
figures recorded independently in the theorem ledger row `J-rate-free-density-one`.

*A second, smaller correction in the same section.* Proposition 7.4's off-diagonal
integral was bounded using "at most three arcs". The two jump points do cut
\([0,1)\) into three intervals, but the first and last carry the same linear branch ---
their constants differ by exactly the slope --- so on the circle there are two arcs.
The error term falls from \(\tfrac6\pi\) to \(\tfrac4\pi\), and the Markov consequence
with it. Checked numerically: the worst of 120 random instances of
\(|\int_0^1e(A\{x+\lambda\}-B\{y+\lambda\})d\lambda|\cdot|A-B|\) is \(0.612\), against
\(2/\pi=0.6366\) and the old \(3/\pi=0.9549\).

Regression: `test_paper_b_prefix_count.py`, 14 tests, including the two consistency
checks above and the \(d^{-3/2}\) exponent.

## The development log, moved out of the manuscript (referee item 14)

Sections 3–6 carried a running account of what earlier drafts got
wrong. It is useful, and it does not belong in the statement of a
theorem. Four passages are recorded here and removed from the body;
four kept their mathematics and lost the attribution; two stayed,
because they warn rather than reminisce.

**Claim C's constant, and the threshold it hid.** The Claim C index
bound is paid at the thirty-sixth power, so the constant in front of
\(P^{7/72}\) matters. A draft used \(16^{1/3}\) and checked the result
against a standing \(P_0\) *"of size \(10^{24}\)"*, which silently
carried a threshold of \(2.8\cdot10^{14}\). The manuscript keeps the
reason — the thirty-sixth power — and drops the story.

**The curvature range on the \(\nu^{3/4}\) band.** A draft printed
\(M\in[0.03,11]\,uhP^{-3/4}\), far weaker than the truth, at a cost of
a factor \(12\) in one sum and \(5\) in another. The current range is
the one Lemma 3.8 is applied at; the weak one bought nothing.

**Lemma 5.2b's third displayed term.** A draft carried \(8\) where the
value is \(0.567\,k(h_1{+}h_2)P^{-9/8}\) — fourteen times the truth —
and \(219\) in place of \(106\) in the term above it.

**Where \(P_0\) used to sit.** The earlier reading \(c_7=1/288\)
together with the earlier normalisation \(V=3S^{1/2}P^{-11/24}\) put
\(P_0\) at \(5.9\cdot10^{23}\). The manuscript printed
\(5.8\cdot10^{23}\); recomputing from the two superseded constants
gives \(5.884\cdot10^{23}\), so the printed figure was a misrounding of
the same species as the \(2.9/2.8\) slip in Section 4. Recorded here at
the computed value. (This is not the \(c_7=1/288\) of Lemma 3.9, which
is a live statement about what Step 5b uses and stays in the
manuscript.)

**Kept in the body, and why.** Two passages read as development log and
are not. Stage 6's *"it must not be relaxed to a budget of the shape
\(3kh_1h_2P^{-5/8}\)"* is a warning to anyone tempted to weaken the
hypothesis, with the factor \(P/(2h_3)\) that would follow; it is the
"hypotheses inherit strength" trap read in reverse, and a reader who
loses it will re-derive the error. And *"the honest test is to maximise
over it"* describes the right numerical test — the decoration carries a
free linear term — rather than a past wrong one.

**Reworded rather than moved.** Four passages kept their content and
lost the draft: the \(P^{7/8}\) reading at \(R_0=P^{1/4}\) (now stated
as the trade Appendix A.6 makes); \(1/4\) failing the four-site
condition; the uselessness of \(49P^{-1/16}\); and the fact that
\(23P^{19/24}\) is *not* below \(P^{7/8}\). In each the warning is the
content and the attribution was not.

## The localized-kernel dividend 0.5561 does not reconcile

Section 8 states the production rule — a word \(w\) of fair
probability \(P_w\) landing at scale \(x^{e_w}\) contributes
\((P_w/e_w)\,g(e_wt)\) — and the rule checks against the one
production the paper writes out in full. For \(OOEEE\): \(d=5\),
\(P_w=2^{-5}=\tfrac1{32}\), landing scale \(e_w=\tfrac9{32}\) (the
word's final scale exponent), so \((P_w/e_w)=\tfrac19\) at scale
\(\tfrac9{32}\) — exactly the printed \(\tfrac19(\tfrac9{32})^{\lambda}\)
term. Both halves of the rule confirmed.

The recursion itself also checks. Solving
\[
2^{-\lambda}+\tfrac19\bigl(\tfrac38\bigr)^{\lambda}
+\tfrac29\bigl(\tfrac34\bigr)^{\lambda}
+\tfrac19\bigl(\tfrac9{32}\bigr)^{\lambda}=1
\]
gives \(0.539180\), against the printed \(\lambda^{***}=0.5392\); and
dropping the last term gives \(0.448017\) against \(\lambda^{**}=0.4480\).

**What does not reconcile is \(0.5561\).** The two words a localized
Theorem 5.3 would add, \(OOOEEE\) and \(OOEOEE\), both have \(d=6\) and
both land at \(e_w=27/64\), so the rule gives each a coefficient
\(2^{-6}/(27/64)=\tfrac1{27}\). Re-solving with both added returns
\(0.606635\). The printed \(0.5561\) instead requires an added
coefficient of \(0.01812\) at that scale, against the rule's
\(\tfrac2{27}=0.07407\) — a ratio of \(0.245\), near a quarter.

Three readings, and this ledger does not choose between them: the
figure may be stale; the localization may recover only part of each
cylinder, so that \(P_w\) is not the fair \(2^{-6}\); or \(0.5561\) may
already net off a loss the sentence does not mention. Two points in
mitigation. The discrepancy runs in the conservative direction — the
rule would give a *larger* dividend than the paper claims, so nothing
is overstated. And the quantity is [24]'s, not this paper's: what
weight a localized cylinder contributes is fixed there.

Recorded so that a reader who recomputes hits the same wall knowingly.

## The Lemma 6.2 edge search hunts for something that cannot exist

`lemma_6_2_edge_search` draws random odd \(n\) on \((10^6,2\cdot10^6)\)
and looks for a failure of the *printed* bound of Lemma 6.2(i). It has
never found one, and it never will --- at that range or any other.

Write \(A=\tfrac34m^{-3/8}\), \(B=\tfrac12v^{-3/4}\),
\(C=\tfrac9{128}(X-1)^{-7/8}\), so that \(b_{\mathrm{print}}=A+B+C\).
The identity is
\(D_5=\tfrac9{128}\theta^2(X-\xi)^{-7/8}-A\theta_2-E_2-B\theta_z-E_z\).
The term \(C\) is in the bound for the sake of the *positive* side of
\(D_5\) and is pure surplus on the negative side, where the true
supremum is \(A+B+E_2+E_z\). Hence the printed bound holds exactly when
\(C\ge E_2+E_z\), i.e. \(n^{-21/16}\) against \(n^{-45/16}\): a ratio
tending to \(\tfrac34n^{3/2}\), and already \(8.23\) at the smallest
admissible \(n=5\). Part (ii) is safe twice over --- \(A\) covers \(C\)
and the \(\theta_w\) coefficient \(\tfrac38(U-1)^{-1/2}\) covers
\(E_2\), both by \(n^{3/4}\) or better.

So \(\lvert D_5\rvert/b_{\mathrm{print}}\) carries the hard ceiling
\(1-\tfrac3{32}n^{-3/4}\bigl(1+o(1)\bigr)<1\), which is
\(1-2.2\cdot10^{-6}\) in the middle of the search's own range. What the
search reports instead is its worst sampled ratio, \(0.99973\) at
\(4000\) trials --- and \((1-\text{worst})\cdot\text{trials}\) stays near
\(1\) across \(400\), \(4000\), \(8000\), \(32000\) trials, because the
ratio is a monotone reading of \(\max\theta_2\) over the sample. The
headline number measured the sample size. The search also sat outside
the classification gate, so its verdict never mattered either way.

**What the correction did.** The absorption step it removed was
genuinely invalid: \(E_2\) cannot be folded into \(\tfrac34\) when
\(\theta_2\) is near \(1\). But the inequality that step was used to
reach was true regardless, by the surplus above. The correction repaired
the derivation, not the statement --- and the displayed form is still
the right call, since its constants are the sharp ones:
\(\sup\lvert D_5\rvert/b_{\mathrm{corr}}\to1\).

**What is load-bearing.** Theorem 6.3 uses only the order of each
remainder. All six coefficients were differentiated against their
printed exponents and match \(-\tfrac9{16}\), \(-\tfrac{27}{16}\),
\(-\tfrac{21}{16}\), \(-\tfrac{45}{16}\), \(-\tfrac{81}{16}\) --- and
\(-\tfrac9{16}\) for the \(\theta_w\) coefficient of (ii) --- to under
\(10^{-6}\) at \(n=10^8\). Below \(10^4\) the two floors and the \(-1\)
shifts are still worth \(10^{-3}\) of slope, so the order test is gated
there and the margin tests carry the small \(n\) alone; they are exact
at every \(n\).

`lemma_6_2_margin_certificate` records all of this and *is* in the
classification gate; `lemma_6_2_ratio_ceiling` gives the ceiling at a
single \(n\), and the edge search now returns it beside its own worst
ratio so the number cannot be read as evidence again. COMPUTATIONALLY
VERIFIED at nine points from \(n=5\) to \(10^{16}\); the all-\(n\)
statement is routine rather than machine-checked, the three exponents
being separated by \(\tfrac{24}{16}\) while the floors perturb each term
by a relative \(O(n^{-3/2})\).

**A directed family, where the random hunt was blind.** Random \(n\) buy
nothing better than \(\theta_2\) within \(1/\text{trials}\) of \(1\).
The family \(n=10^k+1\) with \(4\mid k\) instead pins
\(1-\theta_2=\tfrac{27}{128}n^{-3/4}\) *exactly* --- the same order as
the ceiling deficit \(\tfrac3{32}=\tfrac{12}{128}\) --- so the printed
ratio sits at \(1-\tfrac{39}{128}n^{-3/4}\), that is at \(\tfrac4{13}\)
of the ceiling, at every member and to twelve digits, independently of
\(\theta_z\) (which is \(O(n^{-27/16})\) here and contributes nothing).
The deficit splits exactly: \(\tfrac{12}{128}\) from the ceiling,
\(\tfrac{27}{128}\) from \(1-\theta_2\) charged through \(A/b\). Three
fixed constants, so `lemma_6_2_directed_search` detects a change in the
bound where the random hunt could not; it is in the gate.

**A precision hazard, closed.** The bound terms need only relative
precision, but \(D_5\) is a difference of two terms of size
\(n^{27/16}\) and is itself of size \(n^{-9/16}\), so it needs
\(\tfrac94\log_{10}n\) digits before its first one is right, and
\(\theta_z\) needs \(\tfrac{27}8\). At the module's 60 digits both run
out near \(n=10^{27}\), and the failure is not silent but *false*: at
\(n=10^{28}+1\) the checker returned \(\theta_2=5.0\) --- a fractional
part of five --- and declared the corrected bound violated, slack ratio
\(106\). `identity_census` had always scaled precision with its range,
which is why no census ever hit this; `check_lemma_6_2` and
`lemma_6_2_edge_search` now scale by the same
\(60+4\log_{10}\) rule, so the protection no longer depends on the
caller knowing about it. Results at every existing range are unchanged.

## The observation layer's two printed ratios could not have come out otherwise

`kernel_sum` reports \(\lvert K_c(P)\rvert/P^{1-1/96}\) and
\(\lvert\sum e(Y(n))\rvert/P^{23/24}\). Both sums are over
\(N=P/2\) unit vectors, so both are at most \(N\) whatever the summand
does, and a benchmark \(P^{1-\delta}\) carries information only once
\(P^{\delta}>2\).

| benchmark | \(\delta\) | says anything past | a factor of two past |
|---|---|---|---|
| \(P^{1-1/96}\), Theorem 5.3 | \(1/96\) | \(2^{96}=7.9\cdot10^{28}\) | \(2^{192}=6.3\cdot10^{57}\) |
| \(P^{23/24}\), the level-2 wave | \(1/24\) | \(2^{24}=1.7\cdot10^{7}\) | \(2^{48}=2.8\cdot10^{14}\) |

The ladder stops at \(3\cdot10^5\). At every point on it the trivial
bound is *below* both benchmarks --- \(0.55\) and \(0.73\) of them at
\(10^4\), \(0.57\) and \(0.85\) at \(3\cdot10^5\) --- so the two printed
ratios are under \(1\) by arithmetic and cannot fail. For the kernel
that is permanent: \(2^{96}\) terms will not be summed. EXACT.

The OBSERVATION label was doing its work --- it says the layer proves
nothing --- and the manuscript is stricter still: \S1 states that no
numerical computation is a proof step, and the repository paragraph
that these checks "are not proofs and are not an independent
verification of Lemma 5.2". The gap was only that the two ratios *look*
like a test. `kernel_observation_reach` now records why they are not.

**What is falsifiable is the scale, and one number per \(P\) could not
measure it.** Extending the ladder to \(3\cdot10^6\):

| \(P\) | \(10^4\) | \(3\cdot10^4\) | \(10^5\) | \(3\cdot10^5\) | \(10^6\) | \(3\cdot10^6\) |
|---|---|---|---|---|---|---|
| \(\lvert K_c\rvert/\sqrt N\) | 0.73 | 1.18 | 0.56 | 0.40 | 1.44 | 0.83 |
| wave\(/\sqrt N\) | 0.34 | 0.74 | 0.86 | 0.50 | 2.11 | 1.51 |

The local slopes of \(\log\lvert K_c\rvert\) against \(\log P\) scatter
from \(-0.13\) to \(+1.56\): a single sample per \(P\) cannot separate
\(1/2\) from \(1\), and the printed band \(0.4\)--\(1.2\) was a
statement about four draws.

`kernel_block_scaling` splits the same single pass into 256 consecutive
blocks and aggregates them to 256, 64, 16, 4 and 1, giving five block
lengths at no extra cost. Root-mean-square block sum against block
length stays in \([0.34,1.27]\sqrt L\), and the fitted exponents over
\(P=10^4\ldots3\cdot10^5\) are \(0.38\)--\(0.52\) for \(K_c\) and
\(0.29\)--\(0.47\) for the wave, against \(\tfrac12\) for square-root
cancellation and \(1\) for none. Not an unbiased estimator --- the
longest block length is one sample --- but it discriminates the two
hypotheses by a factor of hundreds where the old statistic discriminated
nothing. OBSERVATION, and still no evidence for the theorem's exponent:
the exponent it would need to test lives past \(2^{96}\).

Also fixed: `kernel_sum` set `mp.mp.dps` to 40 and then to 60 rather
than restoring it, so it silently lowered any caller working at higher
precision. It now uses `mp.workdps`.

## Conjecture 7.3 has a computable object, and nothing had evaluated it

Every open claim in the paper is asymptotic, so none can be settled by
computation --- but one of them names a sum. By Lemma 7.2 the level-3
kernel is
\(K_3(P)=\sum_{n\sim P\ \mathrm{odd}}e(\varrho(n)\theta_3)\) with
\(\theta_3=\{v^{3/2}\}\) and the true weight
\(\varrho=\tfrac{3k}4z^{1/2}\asymp kn^{27/16}\), and Conjecture 7.3
asserts \(K_3\ll P^{1-\delta}\) for some \(\delta>0\). The sum costs one
pass. `level3_kernel_block_scaling` evaluates it for both the
floor-shaped weight of Lemma 7.2 and the smooth \(n^{27/16}\) of the
conjecture's own family, and reads the exponent off 256 block samples
rather than one number.

| \(P\) | \(10^4\) | \(3\cdot10^4\) | \(10^5\) | \(3\cdot10^5\) |
|---|---|---|---|---|
| \(\lvert K_3\rvert/\sqrt N\), floor weight | 0.61 | 0.18 | 1.33 | 1.26 |
| \(\lvert K_3\rvert/\sqrt N\), smooth weight | 0.84 | 0.76 | 0.12 | 1.16 |
| block exponent, floor | 0.42 | 0.24 | 0.54 | 0.56 |
| block exponent, smooth | 0.47 | 0.43 | 0.18 | 0.52 |

Against \(\tfrac12\) for square-root cancellation and \(1\) for none.
Every point is at square-root scale, on both weights;
\(\lvert K_3\rvert/N\) runs \(1.5\cdot10^{-3}\) to \(8.6\cdot10^{-3}\).
OBSERVATION, and it cannot be otherwise: the conjecture's quantifier is
asymptotic, the exponents scatter by \(\pm0.15\) between adjacent \(P\),
and the longest of the five block lengths is a single sample.

What the measurement does say is where the frontier's deficit is not.
A bound with \(\delta=\tfrac12\) is informative from \(P>4\); Theorem
5.3's \(\delta=\tfrac1{96}\) is informative only past \(2^{96}\). The
sum behaves, at every scale reachable, like the strongest end of what
the conjecture asks --- so what is missing at level three is a method,
not the phenomenon. That agrees with the reading of Proposition 7.4
recorded above: the deficit is the quantifier, not the strength.

Also: Section 7's displayed exponents had never been transcribed. Ten
are now in `exponent_checks` --- \(z^{1/2}\asymp n^{27/16}\) from
\(z\asymp n^{27/8}\); \(\varrho'\) at \(11/16\); the level-3 model's
\(G'''\asymp P^{3/8}\) against \(G^{(4)}\asymp P^{-5/8}\) and the
level-2 \(Y''\asymp P^{1/4}\), \(Y'''\asymp P^{-3/4}\) behind "three
differencings against two"; \(v\) jumping by \(n^{5/4}\); the traded
family at \(\varrho m^{3/4}=n^{45/16}\) and \(45/16>9/4\); the model
dichotomy \(\mathcal A'\gg1\iff c>1\) and the table's \(3/16\), \(9/16\)
against \(33/32\), \(45/32\); and \(\tfrac1{32}+\tfrac1{32}+\tfrac1{16}
=\tfrac18\). All exact; the layer now stands at 232 checks. EXACT.

### The three composites are quadratics in the weight exponent

The Step 5a composite \(\tfrac{729}{512}\), the Step E composite
\(-\tfrac{243}{512}\) and Lemma 5.2b's zero-offset \(-\tfrac{135}{1024}\)
were each verified above as arithmetic at \(\alpha=\tfrac98\). They are
not isolated rationals. Against the geometry the map fixes
(\(X=\nu^{3/2}\), \(F=\tfrac32jm^{1/2}\)) a weight \(c=a\nu^{\alpha}\)
gives
\[
\tfrac32(\alpha+\tfrac34)(\alpha-\tfrac14)-\tfrac9{16},\qquad
\tfrac32\alpha(\alpha-1)-\tfrac{27}{32},\qquad
(\alpha-\tfrac34)(\alpha-\tfrac74),
\]
which return \(\tfrac{243}{128}\), \(-\tfrac{81}{128}\),
\(-\tfrac{15}{64}\) at \(\tfrac98\) --- and, times \(a=\tfrac{3k}4\) and
(for the third) \(\tfrac34\beta_1\beta_2\), the three printed constants,
plus \(-\tfrac{1215}{1024}\) after \(\beta_1\beta_2\to9h_1h_2\nu\). Also
the printed two-way splits: \(\tfrac{945}{512}-\tfrac{27}{64}\) and
\(\tfrac{81}{512}-\tfrac{81}{128}\). EXACT.

Consequences recorded in Section 7: the composites vanish at
\(\tfrac{\sqrt{10}-1}4\), \(\tfrac{2+\sqrt{13}}4\), \(\tfrac34\) and
\(\tfrac74\), so the paper's "showing they do not vanish" is a real
condition; at \(\tfrac{33}{32}\) none does, with cancellation factors
\(1.74,1.12,14.3\) against the proved exponent's \(1.59,1.67,13.4\); and
over the 222 blocked exponents carried by contractors of depth
\(\le13\) the worst factors are \(1.78\), \(129\) and \(539\), inside
ceilings of \(3071\) and \(1.2\cdot10^{13}\) set by the
\((1+O(P^{-1/4}))\) of (E6) and Lemma 5.2b's \(O(hP^{-1})\). The
condition never binds.

**One gap.** Step E's zero-offset \(\tfrac{1095}{1024}\) has no
displayed derivation. The manuscript derives \(\tfrac{1215}{1024}\) in
full (three chain-rule terms, then \(\beta_1\beta_2\to9h_1h_2\nu\)) and
then states \(\tfrac{1095}{1024}\) for the frozen-shape difference
without showing the \(\tfrac{120}{1024}\) that separates them. The audit
checks it only for consistency --- \(b'=-\tfrac{365}{176}\) is exactly
\(405\cdot1095/1215\) --- which shows it was propagated, not that it is
right. So the \(\alpha\)-form above covers three of the four Step 5/Step
E composites and not that one. GAP (documentation).

## Four of the six parameter caps pin their parameter to 1 wherever the audit runs

A displayed cap \(1\le x\le CP^{e}\) lets \(x\) take a second value only
once \(CP^{e}\ge2\), that is from \(P=(2/C)^{1/e}\). Tabulating every
such cap in Sections 5--6:

| parameter | cap | second value from | at \(P_0=8.9\cdot10^{13}\) |
|---|---|---|---|
| \(k\), (C3), Theorem 5.3's uniformity | \(P^{1/24}\) | \(2^{24}=1.7\cdot10^{7}\) | 3 values |
| \(h_1\), (C4), outer differencing | \(P^{1/48}\) | \(2^{48}=2.8\cdot10^{14}\) | **1 value** |
| \(h_2\), (C4), inner differencing | \(P^{1/24}\) | \(2^{24}\) | 3 values |
| \(\lvert\ell\rvert\), Step 5a class | \(P^{1/24}\) | \(2^{24}\) | 3 values |
| \(h\), Step 3 (\(h^{1/2}\le P^{1/24}\)) | \(P^{1/12}\) | \(2^{12}=4096\) | 14 values |
| \(j\), Step 5b (\(j\le2P^{1/24}\)) | \(2P^{1/24}\) | \(P\ge1\) | 7 values |

EXACT. Two readings follow, one about the audit and one about the paper.

**The audit.** Its ladder tops out at \(3\cdot10^5\), below \(2^{24}\),
so \(k\), \(h_1\), \(h_2\) and \(\lvert\ell\rvert\) are all pinned to
\(1\) at every \(P\) it has ever run. The identity census was widened
two passes ago for exactly this reason at \(h_1\); the same defect was
still standing at \(k\), where every kernel sum in the module uses
\(k=1\) and Theorem 5.3's "uniformly in \(k\)" had never been touched.

**The paper.** \(h_1\) is the one cap whose threshold, \(2^{48}\), lies
*above* the effective \(P_0=8.9\cdot10^{13}\) --- by a factor of
\(3.16\). At \(P_0\) the Step-1 outer differencing therefore averages
over \(\lfloor P_0^{1/48}\rfloor=1\) shift, and the inner over
\(\lfloor P_0^{1/24}\rfloor=3\). Nothing is wrong: Weyl differencing is
an inequality for any \(H_1\ge1\), and \(P_0\) certifies that the
displayed margins hold, not that the conclusion is strong there --- the
conclusion beats the trivial bound only past \(2^{96}\). But the
threshold and the machinery it certifies do not meet: at \(P_0\) the
outer average has one term. OBSERVATION.

**Sweeping \(k\) past the cap.** Leaving the hypothesis is not a test of
the theorem, but it is the only way to see whether the phenomenon
depends on \(k\) at all. At \(P=10^5\), over \(k=1,2,3,4,7,8,16,32,64\):

| | \(k=1\) | 2 | 3 | 4 | 7 | 8 | 16 | 32 | 64 |
|---|---|---|---|---|---|---|---|---|---|
| level 2, \(\lvert K_c\rvert/\sqrt N\) | 0.56 | 1.43 | 0.25 | 0.56 | 1.16 | 0.91 | 1.22 | 0.65 | 0.09 |
| level 3, \(\lvert K_3\rvert/\sqrt N\) | 1.33 | 0.98 | 1.06 | 0.99 | 0.65 | 1.31 | 0.24 | 0.61 | 0.93 |

and the block exponents stay in \([0.13,0.57]\) and \([0.31,0.56]\)
against \(\tfrac12\) for square root and \(1\) for none. No \(k\) loses
the cancellation at either level; nothing resonates. OBSERVATION.
**The clause, exercised.** The least \(P\) at which (C3) admits
\(k=2\) is exactly \(2^{24}=16777216\), where \(P^{1/24}=2\) on the
nose. Summed there --- \(8388608\) terms, \(688\) s ---
\(\lvert K_c\rvert/\sqrt N\) is \(1.036\) at \(k=1\) and \(1.082\) at
\(k=2\), with block exponents \(0.5226\) and \(0.5202\) over 256 blocks
of \(32768\) terms each: the sharpest statistics in this record, and the
first evaluation ever made inside Theorem 5.3's own uniformity clause.
Both values behave alike and at square-root scale. OBSERVATION --- one
\(P\), and the theorem is asymptotic.

## The exponents in the three entries above were partly the instrument

Three entries have now read a cancellation exponent off five block
lengths and compared it against \(\tfrac12\) and \(1\). None of them
asked what the fit returns on data whose exponent is known.

**Calibrated.** Sums of iid unit phases have exponent exactly
\(\tfrac12\). Running the same fit on 200 such samples at \(N=50000\):

| estimator | mean | bias | sd | 5--95% |
|---|---|---|---|---|
| block counts \(256,64,16,4,1\) (as used above) | 0.455 | \(-0.045\) | 0.109 | \([0.27,0.60]\) |
| counts with \(\ge16\) samples: \(256,128,64,32,16\) | 0.493 | \(-0.007\) | 0.048 | \([0.41,0.56]\) |

COMPUTATIONALLY VERIFIED (`block_exponent_calibration`, Monte Carlo).
The one-block point is a single Rayleigh sample sitting at the extreme
of the lever arm, and \(\log\) of one sample is biased low; dropping it
and the four-block point removes six sevenths of the bias and more than
half the spread.

**What that means for what was written.** The readings of \(0.18\)
(level-3 smooth at \(10^5\)), \(0.24\) (level-3 floor at
\(3\cdot10^4\)) and \(0.13\) (level-2 at \(k=64\)) were inside the
noise of exact square-root behaviour --- the old estimator returns
below \(0.27\) five times in a hundred on data that is exactly square
root. They were reported as measurements. They were not.

**Re-measured.** With the calibrated estimator:

| \(P\) | \(K_c\) | wave | \(K_3\) floor | \(K_3\) smooth |
|---|---|---|---|---|
| \(10^4\) | 0.449 | 0.439 | 0.436 | 0.502 |
| \(3\cdot10^4\) | 0.482 | 0.529 | 0.464 | 0.439 |
| \(10^5\) | 0.552 | 0.409 | 0.552 | 0.506 |
| \(3\cdot10^5\) | 0.460 | 0.475 | 0.540 | 0.489 |

Sixteen readings, all within \(1.2\) standard deviations of
\(\tfrac12\), mean \(0.485\). The \(k\)-sweep at \(10^5\) likewise
tightens to \([0.36,0.56]\) at level two and \([0.45,0.55]\) at level
three, from the \([0.13,0.57]\) and \([0.31,0.56]\) recorded above.

The conclusions of those entries do not change --- both kernels cancel
at square-root scale, no \(k\) breaks it, and the frontier's deficit is
still the method rather than the phenomenon. What changes is that the
scatter was mine, and the corrected readings say so more sharply than
the originals did: nothing in this data is distinguishable from exact
square root. OBSERVATION.
The \(2^{24}\) run was repeated under the calibrated estimator, all
\(8388608\) terms of it: \(k=1\) moves from \(0.5226\) to \(0.5195\) and
\(k=2\) from \(0.5202\) to \(0.5078\). At that sample size the estimator
barely matters, which is itself the point --- the bias lives at small
block counts, and the earlier ladder had far fewer terms to spend.

### Lemma 5.2b's zero-offset anchor is off by 8/5, and the foil hid it

**ERRATUM (confirmed; constants only).** The lemma displays

>  2c'G_F' + c G_F'' = -(135/1024) k b1 b2 nu^{-13/8}

and derives it from three terms, \(c''G_F=\tfrac{81}{1024}\),
\(2c'G_F'=-\tfrac{972}{1024}\), \(cG_F''=\tfrac{756}{1024}\), summing to
\(-\tfrac{135}{1024}\). Those three sum to \((cG_F)''\), not to the two
on the left. The anchor is \(c(G_F-J_F)\) --- the lemma's own \(f''\)
display, Step 5b's \(f''\) display, the definition
\(\lambda_0:=\lvert(c(G_F-J_F))''\rvert\) and proof step (iii) all say
so --- and with \(J_F\) frozen its first term is \(c''(G_F-J_F)\),
\(O(kP^{-7/8})\), not \(c''G_F\). Removing the term the phase does not
carry leaves
\[
2c'G_F'+cG_F''=-\tfrac{216}{1024}=-\tfrac{27}{128},
\]
a factor \(\tfrac85\) larger in magnitude. Step 5a performs exactly
this subtraction correctly on the offset branch,
\(\tfrac{945}{512}-\tfrac{81}{512}=\tfrac{864}{512}\), where
\(\tfrac{81}{512}\) is \(J_Fc''\); the zero-offset branch does not.

*Measured.* At \(P=10^8\), over twelve \(j=0\) samples with the true
integer gaps, \(\lvert(c(G_F-J_F))''\rvert/(k\lvert\beta_1\beta_2\rvert
\nu^{-13/8})\) runs \(0.210876\)--\(0.210937\) against
\(216/1024=0.210938\), while \(\lvert(cG_F)''\rvert\) over the same unit
is \(0.131836=135/1024\) at every sample. The existing probe
`frozen_anchor_curvature_samples` builds \(cG_F\) with no \(J_F\)
subtracted, which is why it confirmed the printed constant.

**And the foil is wrong too.** The lemma warns that "a model that
differentiates the moving gaps produces a different, positive leading
coefficient \(\tfrac{243}{128}\)". Measured, that model
\(F_{\mathrm{sm}}=\tfrac34(\Delta_1X)(\Delta_2X)X^{-1/2}\) gives
\(\tfrac{2673}{1024}=2.610352\) at every sample --- and
\(\tfrac{243}{128}\) is exactly \(9\cdot\tfrac{216}{1024}\), the
magnitude of the *corrected* anchor after
\(\beta_1\beta_2\to9h_1h_2\nu\). The right answer was printed as the
wrong model's, which is why the discrepancy survived an audit that
checked \(81-972+756=-135\) and \(135\cdot9=1215\) and
\(b\cdot\tfrac{11}8\cdot\tfrac38=-\tfrac{1215}{1024}\): every one of
those is arithmetic about the wrong object.

**It is not cosmetic.** With the printed \(b=-\tfrac{405}{176}\) the
residue \(r=\Lambda-\Phi''\) keeps a leading term of size
\(\tfrac{729}{1024}kh_1h_2\nu^{-5/8}\), comparable to \(S\) itself, and
the three \(\rho_0(E)\) ratios of Lemma 3.9 fail outright. The
corrected \(b\) is \(-\tfrac{81}{22}\), from
\(-\tfrac{243}{128}\cdot\tfrac{64}{33}\).

**What moves.**

| quantity | printed | corrected |
|---|---|---|
| anchor curvature | \(-\tfrac{135}{1024}\) | \(-\tfrac{27}{128}\) |
| after \(\beta_1\beta_2\to9h_1h_2\nu\) | \(-\tfrac{1215}{1024}\) | \(-\tfrac{243}{128}\) |
| interpolant \(b\) | \(-\tfrac{405}{176}\) | \(-\tfrac{81}{22}\) |
| \(\lambda_0\) exact range | \([0.38,2.44]\) | \([0.62,3.90]\) |
| \(\lambda_0\) opened | \([0.35,2.6]\) | \([0.56,4.2]\) |
| (C5) cap | \(186\) | \(300\) |
| \(\beta\)-product term | \(0.567\) | \(0.907\) |
| \(\lvert f''-\Lambda\rvert\) constant | \(52.9\), \(106\) | \(85.3\), \(171\) |
| moving-gap foil | \(\tfrac{243}{128}\) | \(\tfrac{2673}{1024}\) |

**What does not move.** The exponent \(1-\tfrac1{96}\), and \(P_0\).
Every A.5 threshold is monotone in \(P\); `corrected_certificate`
reruns the eight rows that touch \(\lambda_0\) or \(E\) and they close
at

```text
   5a-W<=c7S  2.91e13     39-c2   9.5e8      5b-wave  9.7e6
   5b-W<=c7S  3.59e13     39-c3   5.9e8      5b-beta  7.2e6
   5b-E<=c7S  4.10e12     39-c4   4.5e8
```

against the printed \(1.61\cdot10^{13}\), \(8.93\cdot10^{13}\),
\(5.68\cdot10^{12}\), \(6.2\cdot10^{9}\), \(3.9\cdot10^{9}\),
\(3.0\cdot10^{9}\), \(1.7\cdot10^{7}\), \(1.8\cdot10^{7}\). The
maximum falls from \(8.9\cdot10^{13}\) to \(3.6\cdot10^{13}\): \(S\)
rises by \(\tfrac85\) while \(V=\kappa S^{1/2}P^{-11/24}\) rises only
by \(\sqrt{8/5}\), which more than pays for \(E\) growing with the
\(u\)-cap. So \(P_0=8.9\cdot10^{13}\) is still valid and is no longer
tight; the correction *improves* the threshold by a factor \(2.5\).

Recorded, not propagated. Lowering the printed \(P_0\) touches
seventeen sites in the manuscript, the certificate module, the audit
module, one Lean file and four test files, and belongs in its own pass.
`bare_anchor_curvature`, `anchor_curvature`, `moving_gap_curvature`,
`anchor_range`, `corrected_certificate` in `p0_certificate.py`; the
\(\alpha\)-forms `composite("anchor")` and `composite("cG")` in
`paper_b_prefix_count.py`. ERRATUM.

## What the census can police, and the two constants it turned out to measure

The identity census was the last instrument here with no calibration.
Its *identities* have total power: they compare integers, so any
perturbation whatever is caught. Its *inequalities* have only the power
the samples give them --- for an upper bound \(Cf(n)\) the census sees a
change only once \(C\) drops below the largest observed \(value/f(n)\).
That extreme ratio is exactly the fraction the printed constant could be
cut to and still pass, and `census_constant_power` reports it.

| printed constant | side | extreme ratio | could move undetected by |
|---|---|---|---|
| L4.3(i) fine, \(\tfrac38(X-1)^{-1/2}\) | upper | 0.9992 | 0.1% |
| L4.3(i) coarse, \(\tfrac12n^{-3/4}\) | upper | 0.7494 | \(1.33\times\) |
| L5.1(i), \(\tfrac3{16}v^{-1/2}\) | upper | 0.9933 | 0.7% |
| L5.1(iv) \(M_1\), \(0.43\,kh_1h_2P^{-7/8}\) | upper | 0.9777 | 2.3% |
| L5.1(iv) brackets \(\le2\) | upper | 0.861 | \(1.16\times\) |
| L6.2(i) corrected bound | upper | 0.9966 | 0.3% |
| L6.2(ii) corrected bound | upper | 0.6429 | \(1.56\times\) |
| L5.1(iii) first, \(2.6\lvert j\rvert P^{3/4}\) | upper | 0.5771 | \(1.73\times\) |
| L5.1(iii) first, \(\tfrac32 2^{-3/4}\lvert j\rvert P^{3/4}\) | lower | 1.682 | \(1.68\times\) |
| L5.1(iii) second, \(15h_1h_2P^{1/4}\) | upper | 0.4515 | \(2.22\times\) |
| L5.1(iii) second, \(1.4\cdot2^{-1/4}h_1h_2P^{1/4}\) | lower | 5.712 | \(5.71\times\) |

COMPUTATIONALLY VERIFIED at 160 samples. Four constants are attained to
within a percent, so the census polices them tightly. The Lemma 5.1(iii)
band is the one it barely polices at all.

**And that band's two constants are exactly \(\tfrac32\) and
\(\tfrac{27}4\).** Both brackets converge, pointwise in \(n\), to a
single value:

| \(P\) | \(10^4\) | \(10^6\) | \(10^8\) | \(10^{10}\) | \(10^{12}\) | \(10^{14}\) |
|---|---|---|---|---|---|---|
| \(\lvert\text{first}\rvert/(\lvert j\rvert P^{3/4})\) | 1.50022--1.50043 | 1.500002--4 | 1.5000000 | 1.5000000 | 1.5000000 | 1.5000000 |
| second\(/(h_1h_2P^{1/4})\) | 6.7120--6.7811 | 6.7468--6.7526 | 6.74967--6.75027 | 6.74998--6.75003 | 6.750000 | 6.750000 |

which is what the derivatives give:
first \(\approx\tfrac32m^{1/2}j=\tfrac32jn^{3/4}\), and
second \(\approx\tfrac34m^{-1/2}\beta_1\beta_2\) with
\(\beta_i\approx3h_in^{1/2}\), i.e.
\(\tfrac34\cdot9=\tfrac{27}4\). Over a dyadic block with \(P\) the
start, \(n\in(P,2P]\) spreads these to \([\tfrac32,\tfrac32 2^{3/4}]
=[1.50,2.52]\) and \([\tfrac{27}4,\tfrac{27}42^{1/4}]=[6.75,8.03]\).

So the printed upper constants \(2.6\) and \(15\) sit \(1.03\times\) and
\(1.87\times\) above the true tops, and the printed lower constants
\(0.892\) and \(1.177\) sit \(1.68\times\) and \(5.74\times\) below the
true bottoms. Nothing is wrong --- the lemma needs a band, not a limit,
and a loose band is still a band. But the constants are known to seven
digits, and anyone tightening Step 5b now knows exactly how much room
each end has. OBSERVATION for the measurement, EXACT for the two
derivative computations, which are in `exponent_checks`.

### Step E's zero-offset is \(3^7/2^{11}\), and it vindicates the anchor correction

The previous entry left \(\tfrac{1095}{1024}\) underived. It has a
two-line derivation, and it is not \(\tfrac{1095}{1024}\).

*The two halves.* The total phase is
\(\Delta\Delta(\tfrac k2m^{9/4})-\Delta\Delta(c\theta_2)\). With the
gaps frozen the smooth double difference is \(\beta_1\beta_2f''(X)\),
and \(f(Z)=\tfrac k2Z^{9/4}\) gives \(f''=\tfrac{45k}{32}Z^{1/4}\), so
the first half is \(\tfrac{45k}{32}\beta_1\beta_2\nu^{3/8}\) with
\(\nu\)-curvature
\(\tfrac{45}{32}\cdot\tfrac38\cdot(-\tfrac58)=-\tfrac{675}{2048}\) per
\(k\beta_1\beta_2\nu^{-13/8}\). The second half is the
\((c(G_F-J_F))''\) of Lemma 5.2b at its **corrected** value,
\(-\tfrac{432}{2048}\). Subtracting,
\[
\lambda_0'=\tfrac{243}{2048}\,k\beta_1\beta_2\nu^{-13/8}
=\tfrac{2187}{2048}\,kh_1h_2\nu^{-5/8},
\qquad
b'=-\tfrac{2187}{2048}\cdot\tfrac{64}{33}=-\tfrac{729}{352}.
\]

*Measured.* At \(P=10^8\) on real \(j=0\) branches with the true
integer gaps, the first half is \(-0.3295898=-675/2048\) at every
sample to seven figures, the second \(-0.2108\ldots\) against
\(-216/1024\), and the total \(\times9\) runs \(-1.06787\) to
\(-1.06843\) against \(-2187/2048=-1.0678711\). The printed
\(-1095/1024=-1.0693359\) is outside that spread.

*One slip, propagated.* \(\tfrac{1095}{1024}=\tfrac{2190}{2048}\) and
\(b'=-\tfrac{365}{176}=-\tfrac{730}{352}\): both are \(729\to730\). The
previous audit entry noted that \(b'\) "is *exactly* \(405\cdot
1095/1215\), so it scales with the anchor it is built from --- a good
sign that \(1095/1024\) was propagated and not guessed." That reading
was right about the propagation and wrong about what it certified: a
constant carried faithfully from a wrong source is still wrong, and
internal consistency was the only thing being checked.

*And the exact values are in the shape everything else in this paper
has.* \(2187=3^7\) and \(729=3^6\), over powers of two, and
\(\lambda_0'=\tfrac9{16}\lambda_0\) and
\(b'=\tfrac9{16}b\) in lowest terms --- against \(1095=3\cdot5\cdot73\),
\(365=5\cdot73\) and the ratio \(\tfrac{1095}{1215}=\tfrac{73}{81}\).
A factor \(73\) has no business in this computation.

*What this says about the previous erratum.* \(\tfrac{2190}{2048}\) is
already what the *corrected* anchor produces. Had Step E used Lemma
5.2b's printed \(-\tfrac{135}{1024}\), the difference would be
\(-\tfrac{3645}{2048}\), too large by \(\tfrac53\) and far outside the
printed bracket \([0.60,1.25]\). So Theorem 6.1 took the \(-J_Fc''\)
subtraction --- as its own offset branch does explicitly,
\(\tfrac{945}{512}-\tfrac{81}{512}=\tfrac{864}{512}\) --- and Lemma
5.2b's display did not. The two errata corroborate each other: the
correction was not a reinterpretation, it is what the later section
already computed.

*Nothing downstream moves.* The true range is \((0.6924,1.0679]\)
against the previous \((0.6934,1.0694]\), both inside the printed
\([0.60,1.25]\), and the lower end still clears the A.5 row that reads
\(S\ge0.60P^{-5/8}\). No threshold, no appendix row, no \(P_0\).

`smooth_double_difference_curvature`, `step_e_zero_offset`,
`step_e_interpolant_b` in `p0_certificate.py`; six tests, one of them
the direct measurement of both halves. ERRATUM (corrected in place).

## The band does not reach \(P_0\), and two printed thresholds are not in Appendix A

**The question answered.** The Lemma 5.1(iii) band feeds only
\(G'\), \(G''\) and the run-length constant \(\tfrac1{22}\); no row of
the \(P_0\) certificate mentions it, and the binding row is
`5b-W<=c7S`, Step 5b's curvature condition at \(c_7=\tfrac1{232}\).
Sharpening \(1.4\) and \(15\) to the true \(\tfrac{27}4\) and
\(\tfrac{27}42^{1/4}\) would therefore change no exponent and no
threshold: it would improve a constant inside Step 3's window counting
and nothing else. EXACT.

**A correction to the entry above.** That entry called the printed lower
constants \(0.892\) and \(1.177\) and read them as \(1.68\times\) and
\(5.74\times\) loose. The printed constants are \(\tfrac32\) and
\(1.4\); the factors \(2^{-3/4}\) and \(2^{-1/4}\) are the *audit's*
conversion of a band stated in the block start \(P\) into a pointwise
check at \(n\in(P,2P]\), not slack in the paper. In the paper's own
terms:

| bracket | printed band | true band over the block | slack |
|---|---|---|---|
| first, \(\lvert j\rvert P^{3/4}\) | \([\tfrac32,\,2.6]\) | \([\tfrac32,\,\tfrac322^{3/4}]=[1.50,2.52]\) | lower **exact**, upper \(1.03\times\) |
| second, \(h_1h_2P^{1/4}\) | \([1.4,\,15]\) | \([\tfrac{27}4,\,\tfrac{27}42^{1/4}]=[6.75,8.03]\) | lower \(4.82\times\), upper \(1.87\times\) |

So the first bracket's band is essentially sharp --- its lower constant
is attained exactly at \(n=P\) --- and only the second is loose. The
earlier entry understated the first and overstated the second's lower
end. The \(P\)-versus-\(n\) confusion is the same one this ledger keeps
finding in the paper; this time it was mine.

**Two printed thresholds Appendix A does not carry.** The appendix says
each printed threshold inequality is solved there for the least \(P\)
beyond which it holds. Its 37 rows omit:

| site | condition | first holds at |
|---|---|---|
| Lemma 5.1(iii) | \(\lvert G'\rvert\le2\lvert j\rvert P^{-1/4}+20h_1h_2P^{-3/4}<1\) | \(2.03\cdot10^{3}\) |
| Theorem 6.1 Step B | \(4.8\,P^{-11/96}<1\) | \(8.82\cdot10^{5}\) |

Both are eight to eleven orders below \(P_0=8.9458\cdot10^{13}\), so the
certificate's value stands; the enumeration does not. EXACT.

**And the Step B threshold is stale by a rounding.** With the mode cap
\(\lvert k\rvert\le2P^{1/96}\), the discard cost
\(\tfrac{3\pi k}4P^{-1/8}\) is *exactly*
\(\tfrac{3\pi}2P^{-11/96}=4.7124\,P^{-11/96}\), and the printed
"\(P\ge7.6\cdot10^{5}\)" is that constant's threshold ---
\(4.7124^{96/11}=7.51\cdot10^{5}\), and \(7.6\cdot10^{5}\) back-solves
to \(4.7189\). Printed as \(4.8\), the inequality first holds at
\(8.82\cdot10^{5}\), so as written the line is false on
\([7.6\cdot10^{5},8.8\cdot10^{5}]\). The constant was rounded up and the
threshold was not recomputed. Harmless --- both numbers are eight orders
below \(P_0\) --- but it is a printed statement that fails where it
claims to hold. EXACT; `appendix_a_gaps`, three tests, two exponent
checks (241 in the layer).

## The full count of printed thresholds, and a correction to the entry above

Scanning Sections 4--6 for displayed conditions of the form
\(\cdots<1\) or \(\cdots\le1\) carrying a power of \(P\) gives twelve
candidates. Eight are not thresholds: they hold for every \(P\ge1\)
(\(0.6P^{-1/16}<1\), \(0.22k\lvert j\rvert P^{-5/8}<1\)), or they are a
cited lemma's hypothesis rather than a condition on the regime
(\(M\le1\) in Lemma 3.8), or conclusions rather than conditions
(the window counts at "drift \(\le1\)"). Two are in Appendix A's
table. Two are not:

| site | condition | first true at |
|---|---|---|
| Lemma 5.1(iii) | \(\lvert G'\rvert\le2\lvert j\rvert P^{-1/4}+20h_1h_2P^{-3/4}<1\) | \(2.03\cdot10^{3}\) |
| Lemma 5.2(b) | \(13hP^{-1/4}+50h\,h_1h_2P^{-3/4}<1\) | \(4.96\cdot10^{6}\) |

**Nothing is near \(P_0\).** The larger of the two is close to seven orders
below \(P_0\) as it currently stands, so the certificate's value is
untouched and only its enumeration is short by two rows. EXACT. (The
probe now reads \(P_0\) from the certificate rather than pinning
\(8.9458\cdot10^{13}\): the Lemma 5.2b constants are under revision in
a concurrent pass --- the middle-band cap \(186\to300\), the
interpolant \(105.8\to170.6\), \(S_{5b}\) from \(0.35\) to
\(0.56\) --- and a hardcoded threshold would have gone stale the
moment they landed.)

**Correction to the entry above.** It listed Theorem 6.1 Step B as a
third missing row. It is not missing: the certificate carries it as
`t61-stepB-discard`, "\((3\pi k/4)P^{-1/8}\le1\) at \(k\le2P^{1/96}\)",
\(P_{\min}=7.5086\cdot10^{5}\). I had searched the rows' claim text for
the string \(4.8\) and found nothing, and concluded the row was absent
--- but the certificate states the *exact* form, \(3\pi k/4\), and never
writes \(4.8\). A search on one field, read as a fact about two.

What survives from that entry is the smaller half, and it is unchanged:
with \(\lvert k\rvert\le2P^{1/96}\) the discard cost is exactly
\(\tfrac{3\pi}2P^{-11/96}=4.7124\,P^{-11/96}\); the certificate uses
that constant and gets \(7.51\cdot10^{5}\), which the manuscript prints
as \(7.6\cdot10^{5}\). The manuscript also rounds the constant *up* to
\(4.8\), for which the inequality first holds at \(8.82\cdot10^{5}\).
So the displayed line, read with its own constant, is false on
\([7.6\cdot10^{5},8.8\cdot10^{5}]\): the rounding moved and the
threshold beside it did not. The appendix is right; the display is
inconsistent with itself. EXACT, and harmless --- \(P_0\) is eight
orders away.

## The binding row charges the interpolant at a setting no cell reaches

Step 5b compares \(W=V+E\) against \(c_7S/2\). The scale is
\[
S=\max\bigl(\lvert uh_1{+}u'h_2\rvert P^{-3/4},\;
kh_1h_2P^{-5/8},\;\lvert w\rvert P^{-1/2}\bigr),
\]
whose second entry gives \(S\ge0.56\,kh_1h_2P^{-5/8}\), and the
interpolant error is
\(85.3\,k(h_1{+}h_2)P^{-9/8}+0.11P^{-5/6}\). The manuscript converts the
error first --- \(k(h_1{+}h_2)\le2P^{1/12}\) by (C3), (C4), giving
\(171P^{-25/24}\) --- and then compares it against \(S\) taken at *its*
minimum, \(kh_1h_2=1\).

**No cell does both.** Over the integers \(kh_1h_2=1\) forces
\(k=h_1=h_2=1\), and then \(k(h_1{+}h_2)=2\), not \(2P^{1/12}\). Kept
symbolic, the ratio that decides the row is
\[
\frac{E_{\text{first}}}{S}
\le\frac{85.3}{0.56}\,\frac{h_1{+}h_2}{h_1h_2}\,P^{-1/2}
=152.3\Bigl(\frac1{h_1}+\frac1{h_2}\Bigr)P^{-1/2}
\le304.6\,P^{-1/2},
\]
maximised at \(h_1=h_2=1\) and *independent of \(k\)*, where the
certified pairing charges \(304.6\,P^{-5/12}\). The gap is exactly
\(P^{1/12}\): \(-\tfrac{25}{24}+\tfrac58=-\tfrac5{12}\) against
\(-\tfrac98+\tfrac58=-\tfrac12\). EXACT --- the identity
\(1/h_1+1/h_2\le2\) needs no constants.

**What it costs.** Solving the three rows that carry the interpolant
error both ways, with the coefficients read out of `p0_certificate`
rather than copied:

| row | as certified | at one cell | factor |
|---|---|---|---|
| `5b-W<=c7S` (binding) | \(3.59\cdot10^{13}\) | \(4.89\cdot10^{12}\) | \(7.33\) |
| `5a-W<=c7S` | \(2.91\cdot10^{13}\) | \(3.84\cdot10^{12}\) | \(7.58\) |
| `5b-E<=c7S` | \(4.10\cdot10^{12}\) | \(7.72\cdot10^{10}\) | \(53.1\) |

The largest row not carrying the error is `st5b-qpp` at
\(2.98\cdot10^{11}\), so the maximum still comes from `5b-W<=c7S` and
\(P_0\) would fall from \(3.59\cdot10^{13}\) to
\(4.89\cdot10^{12}\) --- **a factor of \(7.33\)**. COMPUTATIONALLY
VERIFIED at the constants now in the working tree; those are under
revision in a concurrent pass, which is why the probe recovers them from
`interpolant_error` instead of copying them. The \(P^{1/12}\) does not
move with them.

**The direction is safe.** The printed \(P_0\) is an over-estimate: the
pairing charges more than any cell can present, so every displayed
margin holds at least as far down as claimed. What is lost is only
sharpness --- and \(P_0\) is the number the paper leads with.

## The sweep: one justification sentence, two kinds of numerator

The last entry found the binding row charged at a cell that does not
exist. Sweeping the rest of the certificate for the same shape gives one
more, and locates the source of both.

**The source.** Section 5's justification is a single parenthesis:
"(The worst standing cell is \(kh_1h_2=1\); larger products only enlarge
\(S\).)" It covers two kinds of numerator and is right about one.

* **The \(c\)-derivative rows are right.** \(\lvert c''/2\rvert\le
  0.053\,kP^{-7/8}\) carries \(k\); \(S\ge0.56\,kh_1h_2P^{-5/8}\)
  carries \(kh_1h_2\); the ratio is
  \(0.095\,(h_1h_2)^{-1}P^{-1/4}\) --- the \(k\) cancels, and the worst
  cell is \(h_1=h_2=1\) at *any* \(k\). The certificate implements
  exactly that: no \(P^{1/24}\) rides along, and \(-\tfrac78+\tfrac58
  =-\tfrac14\) is the printed exponent. `39-c2`, `39-c3`, `39-c4`
  correctly paired.
* **The interpolant row is not**, as recorded above: \(k(h_1{+}h_2)\)
  over \(kh_1h_2\) leaves \(1/h_1+1/h_2\le2\), but the row converts
  \(k(h_1{+}h_2)\le2P^{1/12}\) before dividing. The sentence's word is
  "products", and for this numerator the product is not what matters.

**And a second row, for a plainer reason.** Step 5b(a)'s \(q''\)
curvature ratio is
\[
\frac{\bigl(1.85\,khP^{1/8}+R_0\bigr)6P^{-5/4}}{0.35\,uh\,P^{-3/4}},
\]
with \(h\) on both sides. In the first term it cancels ---
\(1.85\,khP^{1/8}/(uh)=1.85\,kP^{1/8}/u\) --- yet the row sets
\(h=P^{1/8}\) upstairs (giving \(1.85P^{7/24}\)) and \(uh=1\)
downstairs. The worst case is \(k=P^{1/24}\), \(u=h=1\), i.e.
\(1.85P^{1/6}\): \(\tfrac7{24}-\tfrac16=\tfrac18\) of over-charge.
EXACT.

| row | mismatch | as certified | paired | factor |
|---|---|---|---|---|
| `5b-W<=c7S` | \(k(h_1{+}h_2)\) vs \(kh_1h_2\) | \(3.59\cdot10^{13}\) | \(4.89\cdot10^{12}\) | \(7.33\) |
| `5a-W<=c7S` | same | \(2.91\cdot10^{13}\) | \(3.84\cdot10^{12}\) | \(7.58\) |
| `5b-E<=c7S` | same | \(4.10\cdot10^{12}\) | \(7.72\cdot10^{10}\) | \(53.1\) |
| `st5b-qpp` | \(kh\) vs \(uh\) | \(2.98\cdot10^{11}\) | \(8.71\cdot10^{9}\) | \(34.2\) |
| `39-c2/c3/c4` | \(k\) vs \(kh_1h_2\) | --- | correctly paired | --- |

With all four repaired, \(P_0\) is \(4.89\cdot10^{12}\), still set by
`5b-W<=c7S`, and the largest row untouched by any of this is
`s3s1-Bsmall` at \(2.83\cdot10^{10}\) --- a clearance of \(170\times\).
COMPUTATIONALLY VERIFIED at the constants now in the tree, which are
under revision; the two exponents, \(P^{1/12}\) and \(P^{1/8}\), are
not.

The manuscript is already alert to this site --- it notes that merging
\(1.85khP^{1/8}+R_0\) into \(2.85P^{5/16}\) "loses \(P^{1/48}\)" and
keeps the two terms apart for exactly that reason. It took the first
step and not the second: having split the sum, the \(h\) in the first
term still cancels.

## The loose route is in the prose, and the right form is three pages earlier

The two mispairings above are not the appendix's doing. The manuscript
takes the loose route itself, and it also states the correct form
elsewhere --- the two are three pages apart.

**The correct form, Step 5b's \(\rho\le\rho_0\) check.** "In the middle
band of Step 5b one has \(S\ge0.56\,kh_1h_2P^{-5/8}\) (and
\(S\ge0.56P^{-5/8}\) whenever \(kh_1h_2\ge1\))", and the three
\(c\)-derivative numerators carry \(k\), so the \(k\) cancels and the
ratios come out \(\le C_iP^{-1/4}\) with absolute \(C_i\). Symbolic on
both sides, correctly paired.

**The loose form, Step 5b's splitting.** Three pages later:
\(E:=\sup\lvert f''-\Lambda\rvert\le171P^{-25/24}+0.11P^{-5/6}\), the
converted form, and \(W\le c_7S/2\) is then checked "at the lower end
\(S\ge0.56P^{-5/8}\)". Step 5a does the same at
\(S\ge0.60P^{-5/8}\) against \(106P^{-25/24}+0.11P^{-5/6}\). The
appendix transcribes these faithfully, so a repair is a change to the
prose, not to the certificate.

**What the repair reads.** Keeping \(E\) symbolic through the division:
\[
\frac ES
\le\frac{85.3\,k(h_1{+}h_2)P^{-9/8}+0.11P^{-5/6}}{0.56\,kh_1h_2P^{-5/8}}
=152.3\Bigl(\frac1{h_1}{+}\frac1{h_2}\Bigr)P^{-1/2}
+\frac{0.196}{kh_1h_2}P^{-5/24}
\le304.6\,P^{-1/2}+0.196\,P^{-5/24},
\]
both maxima attained at the *same* cell \(k=h_1=h_2=1\), so the bound is
sharp as a pair and not merely termwise. EXACT.

**What it changes downstream.** The prose also reports the shape of the
budget at the threshold --- "\(V\) and \(E\) take \(55\%\) and \(45\%\)
of the budget \(c_7S/2\), and \(E\) itself splits \(70{:}30\) between
its two terms". Both are current under the constants now in the tree
(checked, `step5b_budget_split`). After the repair the threshold falls to
\(4.89\cdot10^{12}\) and the shape inverts:

| | \(V\) : \(E\) | \(E\)'s own split |
|---|---|---|
| as printed, at \(3.59\cdot10^{13}\) | \(55:45\) | \(70:30\) |
| repaired, at \(4.89\cdot10^{12}\) | \(73:27\) | \(24:76\) |

So after the repair the row is \(V\)-dominated, and inside \(E\) the
parameter-free \(0.11P^{-5/6}\) term overtakes the \(k(h_1{+}h_2)\) term
that used to carry it. The practical reading: sharpening \(E\) further
buys almost nothing once the pairing is fixed --- the next improvement
has to come from \(\kappa\) and \(c_7\), which is where the prose
already says the balance now lives. COMPUTATIONALLY VERIFIED at the
constants in the tree; the pairing exponents are not constant-dependent.

### The correction propagated: \(P_0=3.5858\cdot10^{13}\), \(P_1=9.8\cdot10^{18}\)

The two errata above are now carried through the manuscript, the
certificate module and the tests. Lemma 5.2b's constants are corrected
in place and its erratum note reduced to a record; Step E's
\(\tfrac{2187}{2048}\) and \(-\tfrac{729}{352}\) were already in place.

*What the threshold does.* Nine of the thirty-seven A.5 rows depend on
the anchor, through the middle-band floor \(S\ge\lambda_0^{\rm lo}\) and
through \(E\). Corrected,

```text
   P_0   8.9458e13  ->  3.5858e13     factor 2.49
   P_1   5.03e19    ->  9.84e18       factor 5.11
```

both binding where they did (\(W\le c_7S/2\) at Step 5b). The
mechanism is that \(S\) rises by \(\tfrac85\) while
\(V=\kappa S^{1/2}P^{-11/24}\) rises only by \(\sqrt{8/5}\), which more
than pays for \(E\) growing from \(106\) to \(171\) with the
\(u\)-cap. **\(\kappa=\tfrac1{12}\) is unchanged**: the \(P_1\) column
is minimised there before and after, so the operating point is set by
the geometry of the boundary term against the gate and not by the
constants.

*What else moved, and what did not.* The \(c_7\) lever's worth falls
from \(300\) to \(120\) and its saturation eases from \(c_7=1/54\) to
\(1/61\) --- both only because the base moved; the lever's floor is the
\(q''\) row, which divides by Theorem 4.1's Stage-4 curvature
\(0.35\,uh\,P^{-3/4}\) and not by \(\lambda_0\), and stays at
\(2.98\cdot10^{11}\). **That coincidence of value cost a wrong turn
here**: the two constants are both \(0.35\), and treating them as one
dropped the \(q''\) row an order, moved the \(R_0\) crossing from
\(0.29919\) to \(0.30667\) and rewrote A.6 around a conclusion that
does not hold. Caught by reading the surrounding derivation, which
names its denominator. The \(R_0\) analysis is unchanged in every
figure except those measured against \(P_0\).

One consequence at \(R_0\) is real: \(a=9/32\), whose worst site is
\(7.4\cdot10^{13}\), used to sit just under \(P_0\) by a factor
\(1.3\) --- "too close to print" --- and now sits a factor \(2.1\)
*above* it. The feasibility band tightens to \(a\in[0.283,0.346]\) and
no longer contains \(9/32\). \(5/16\) is unaffected at
\(2.98\cdot10^{11}\), now \(120\) below \(P_0\) rather than \(300\).

*The Lean certificate is now behind.* `ThresholdCertificate.lean`
encodes the pre-correction table: \(t=1.96\) on the binding row,
\(\sqrt{0.35}\ge0.5916\), \(\tfrac1{12}\sqrt{0.35}\le0.04931\). Those
rows remain true statements about the old inequalities, and
`test_lean_thresholds_cover_the_precorrection_probe_thresholds` pins
them to the pre-correction probe so the drift is asserted rather than
silent; exactly one row, `row_5a_binding`, fails to cover the corrected
table. A.1 says so in the manuscript. Regenerating it is the open item.

`thresholds` now takes an `anchor` tuple, so the pre-correction table
is a first-class object rather than a comment: `ANCHOR_CONSTANTS` and
`ANCHOR_CONSTANTS_PRECORRECTION`, and every row that carries the floor
or \(E\) reads them. PROPAGATED.

## The operating point does not move, and the repair is worth less than it looked

**The answer is no.** \(\kappa\) is pinned by \(P_1\) --- the point at
which the middle band beats the trivial bound --- whose piece-boundary
term carries \(\kappa^{-1/2}\) and turns it around. Scanning
\(1/\kappa\) over \([8,25]\), the minimum sits at \(1/11.50\) both with
the printed interpolant error and with the repaired one; the paper
operates at \(\tfrac1{12}\), within \(0.3\%\) of it. The optimum does
not move. EXACT to the grid.

**Why it does not.** The interpolant error does reach \(P_1\) --- it
enters through \(W=V+E\) in the two transition costs --- but its weight
there is small: \(E\) is \(45.5\%\) of \(W\) at \(P_0=3.59\cdot10^{13}\)
and \(11.8\%\) at \(P_1=9.81\cdot10^{18}\). So the same repair that is
worth a factor of \(7.33\) on \(P_0\) is worth \(1.06\) on \(P_1\).

| | printed | repaired | factor |
|---|---|---|---|
| \(P_0\) (the certified threshold) | \(3.59\cdot10^{13}\) | \(4.89\cdot10^{12}\) | \(7.33\) |
| \(P_1\) (where the band has content) | \(9.81\cdot10^{18}\) | \(9.25\cdot10^{18}\) | \(1.06\) |
| optimal \(1/\kappa\) | \(11.50\) | \(11.50\) | --- |

**And that is the honest reading of the four entries above.** The
pairing repair improves the *certified* threshold, not the point at
which Theorem 5.3's middle band says anything: \(P_1\) is five orders
above \(P_0\) and stays there. The paper is not hiding this --- Appendix
A.5 tabulates \(P_0\) and \(P_1\) side by side across \(\kappa\), and
the prose quotes \(P_0=3.6\cdot10^{13}\) against
\(P_1=9.8\cdot10^{18}\) at the operating point. A reader who takes
\(P_0\) for the paper's reach has misread the paper, not been misled by
it. COMPUTATIONALLY VERIFIED.

An earlier draft of this entry claimed \(E\) does not enter \(P_1\) at
all, from reading `log10_P1`'s signature rather than
`middle_band_cost`, which it calls. It does enter; the conclusion
survives because its *weight* is small, not because it is absent.

### The Lean certificate is regenerated, and nine rows kept their witnesses

`ThresholdCertificate.lean` now proves the corrected A.5 table. It builds
green (`lake build Problems.Juggler.ThresholdCertificate`, 23 s), so the
gap the previous entry recorded is closed rather than described.

*What changed.* Nine of the thirty-seven rows carry Lemma 5.2b's anchor:

```text
   5b-lam0-range   2.44/23.4 -> 3.90/37.8 ; 0.38/3.15 -> 0.62/5.04   t >= 17 (unchanged)
   39-c2           53/350 -> 53/560                                  t: 282 -> 176
   39-c3           47/350 -> 47/560                                  t: 250 -> 156
   39-c4           44/350 -> 44/560                                  t: 234 -> 146
   39-wave         4000/7 -> 3750/7                                  t: 16.1 -> 15.9
   5b-E<=c7S       105.8, 7/9280 -> 170.6, 7/5800                    t: 1.85 -> 1.84
   5a-W<=c7S       105.8 -> 170.6                                    t: 1.89 -> 1.91
   5b-W<=c7S       0.04931, 105.8, 7/9280 -> 0.06237, 170.6, 7/5800  t: 1.96 -> 1.92
```

plus the new `sqrt_0_56_lower : (0.7483)^2 <= 0.56`. `39-beta` is left at
`2.31`, which is conservative for the corrected `2.3048`.

*That every row kept a witness was not guaranteed.* The two balance rows
are tight to four figures in the coefficient budget: `5b-W<=c7S` needs
`6.4969 + 1.6177 + 3.6895 = 11.8041` against `7/5800 = 12.0690`, in units
of \(10^{-4}\). Both first **failed** on a rounding of one part in
\(4\cdot10^{5}\) --- `170.6/417316 = 4.08805\cdot10^{-4}` written as
`4.0880` rather than `4.0881`. Lean caught it; the arithmetic that
produced the coefficients had not.

*And two rows that look as though they carry the anchor do not.*
`row_s3s2_bdry_a` and the Step 5b(a) `q''` ratio divide by Theorem 4.1's
Stage-4 curvature `0.35 uh P^(-3/4)`. `sqrt_0_35_lower` therefore stays,
now beside `sqrt_0_56_lower`, and the file's header says which is which
--- the same coincidence of value that cost a wrong turn in the
propagation entry above, recorded now where a reader meets it.

The binding row is `row_5b_binding` at `t = 1.92`, i.e.
`P >= 1.92^48 = 4.0e13` against the probe's `3.5858e13`: a loss of under
11 per cent, down from the 20 per cent the pre-correction `t = 1.96`
carried. `LEAN_ROWS` in `test_p0_certificate.py` is updated and its
covering test compares against the corrected table again. VERIFIED.

## What binds \(P_1\), and what a 17% constant costs there

**The piece-boundary term binds.** Of A.5's three middle-band costs,
\(4PW/(c_7S)\) at \(P^{41/48}\), \(P(W/c_7S)^{1/2}\) at \(P^{89/96}\)
and \(3.5\,P^{13/24}V^{-1/2}\) at \(P^{89/96}\), the third is \(30.6\%\)
of the total at \(10^{13}\), \(57.8\%\) at \(P_1\), and \(63.5\%\) at
\(10^{22}\): it takes over and keeps growing.

**Its constant is \(3.5\) where the row itself gives \(3.0015\).** The
constant comes from `5b-Npieces`, "cells + anchor runs + windows
\(\le3.5P^{13/24}\)", whose left-hand side is
\[
3+2P^{-13/24}+22P^{-11/48}+5P^{-5/24},
\]
i.e. \(3.0329\) at \(10^{13}\), \(3.0015\) at \(P_1\) and \(3.0003\) at
\(10^{22}\). The printed \(3.5\) is \(16.6\%\) above it at \(P_1\).

**And 17% is worth a factor of two and a half.** The two \(P^{89/96}\)
terms decide the crossing, so \(P_1\) solves \(CP^{89/96}=P\) and
\[
P_1=C^{96/7},
\]
amplifying every constant in the total by a \(13.71\)st power. Carrying
\(3\) instead of \(3.5\) moves \(P_1\) from \(9.84\cdot10^{18}\) to
\(3.91\cdot10^{18}\): **a factor of \(2.52\)**, against the \(1.06\)
that the interpolant pairing repair is worth on the same number.
COMPUTATIONALLY VERIFIED; the exponents \(89/96\), \(41/48\) and
\(96/7\) are EXACT and in `exponent_checks`.

**Where the paper looks instead.** A.5's closing paragraph --- "What is
left" --- points at \(E\), the middle-band half-width \(60\) and the
\(\lambda_0\) range \([0.35,2.6]\). That is the right target for
\(P_0\), where \(E\) is \(45.5\%\) of \(W\). At \(P_1\), \(E\) is
\(11.8\%\) of \(W\) and the binding cost is the boundary term, whose
constant is loose by construction: \(3.5\) was chosen to dominate three
lower-order terms that together contribute \(0.0015\) at \(P_1\). The
sharp value is not an estimate to be improved --- it is the row's own
left-hand side, evaluated where it is used.

The two levers, side by side on the number that decides reach:

| lever | \(P_1\) | factor |
|---|---|---|
| as printed | \(9.84\cdot10^{18}\) | --- |
| interpolant pairing repaired | \(9.25\cdot10^{18}\) | \(1.06\) |
| piece constant carried sharp | \(3.91\cdot10^{18}\) | \(2.52\) |
