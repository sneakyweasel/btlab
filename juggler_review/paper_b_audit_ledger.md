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

## Three readings of the same two lengths, and they do not agree

This one runs against the paper, so it is stated as an apparent
inconsistency between three passages rather than as a verdict.

**The lemma.** Lemma 3.9(i) bounds the sublevel set by
\[
\lvert\Omega_V\rvert\le C(E)\Bigl(\frac{PV}S+P\Bigl(\frac VS\Bigr)^{1/2}\Bigr),
\]
with a *single* \(C(E)\), which \S3 says explicitly is "never assigned a
value anywhere in the paper".

**A.5 assigns two.** Its \(P_1\) computation carries
\(4P\,W/(c_7S)\) for the \(r=3\) term and \(P(W/(c_7S))^{1/2}\) for the
\(r=4\) term. The first implies \(C(E)=4/c_7=928\); the second implies
\(C(E)=c_7^{-1/2}=15.2\). No single \(C(E)\) gives both, so the display
is not an instance of Lemma 3.9(i) as the lemma is stated.

**The lemma's proof gives different numbers again.** On an \(r=3\)
piece, a single interval of length \(\le4PV/(c_7S)\) --- which is A.5's
coefficient. On an \(r=4\) piece, the second-difference identity forces
\((y-x)^2\le64VP^2/(c_7S)\), i.e. \(y-x\le8P(V/(c_7S))^{1/2}\), and
there may be *two* such intervals. So the proof's \(r=4\) constant is
\(8\) or \(16\) where A.5 carries \(1\).

**And A.6 gives a third.** It writes the \(r=3\) length as
\(2PV/(c_3S)\), half of what the proof and A.5 both have.

| reading | \((r{=}3,\,r{=}4)\) | \(P_1\) |
|---|---|---|
| Appendix A.5, as printed | \((4,1)\) | \(9.84\cdot10^{18}\) |
| Appendix A.6, as printed | \((2,1)\) | \(2.83\cdot10^{18}\) |
| Lemma 3.9's proof, one \(r{=}4\) interval | \((4,8)\) | \(1.42\cdot10^{24}\) |
| Lemma 3.9's proof, two \(r{=}4\) intervals | \((4,16)\) | \(1.99\cdot10^{27}\) |

**The direction matters.** Everything else this ledger has found ran the
safe way --- bounds charged more heavily than any cell can present. This
one runs the other way: on the paper's own proof constants, \(P_1\) is
\(5.2\) orders *above* the printed \(9.8\cdot10^{18}\), which would mean
the middle band beats the trivial bound far later than Appendix A.5
states. \(P_0\) is untouched: the transition lengths do not enter it.

**What would reconcile it.** A normalisation carried silently between
\S3 and A.5 --- the \(r=4\) constant absorbed into \(c_4\), say, or the
sublevel set measured against a rescaled \(V\) --- would close the gap,
and this probe cannot see one. The three loci are §3's proof of
Lemma 3.9(i), the display in A.5, and the sentence in A.6; a reader
checking \(P_1\) has to pick one. COMPUTATIONALLY VERIFIED for the four
\(P_1\) values; the algebra \((y-x)^2\le64VP^2/(c_7S)\Rightarrow8P\) is
EXACT.

## The whole ladder, and which rung governs

| threshold | \(P\) | what it certifies |
|---|---|---|
| \(P_0\) | \(10^{13.6}\) | the printed inequalities hold |
| \(P_1\), as A.5 prints it | \(10^{19.0}\) | the middle band beats counting |
| \(P_1\), at Lemma 3.9's proof constants | \(10^{24.2}\) | the same, one \(r{=}4\) interval |
| \(P_1\), those constants with two intervals | \(10^{27.3}\) | the same, worst reading |
| \(2^{96}\) | \(10^{28.9}\) | bare \(P^{1-1/96}\) beats \(P/2\) |
| sharp form vs \(P/2\) | \(10^{224.2}\) | \(P^{1-1/96}\log^{3/4}P\le P/2\) |
| Step 5b's log absorption | \(10^{267.9}\) | \(C\log P\le P^{1/96}\) |
| Theorem 6.3's | \(10^{1244.6}\) | \(\log^{15/4}P\le P^{1/96}\) |

**None of the internal rungs governs.** Every one of them --- \(P_0\),
and \(P_1\) on all three readings of the entry above --- sits below
\(2^{96}\), the point at which the bare exponent first beats counting.
The worst reading, \(10^{27.3}\), still leaves \(1.6\) orders of
headroom. So the \(r{=}4\) discrepancy recorded above, however it
resolves, cannot move where Theorem 5.3 starts to say something:
\(9.8\cdot10^{18}\) and \(2.0\cdot10^{27}\) are on the same side of the
line that matters. That is the most useful thing to know about it.

**What governs is the shape of the conclusion.** In the sharp form
\(K_c\ll P^{1-1/96}\log^{3/4}P\), the crossover with \(P/2\) is
\(10^{224}\) --- \(195\) orders past every internal threshold. In the
printed \(\varepsilon\)-form there is no finite crossover at all, since
the \(\varepsilon\) absorbs the log by construction; that is precisely
why \S3 says the \(\varepsilon\)-form is used at Step 5b rather than the
sharp one, and why Appendix A's log-absorption table is labelled a
diagnostic and kept out of \(P_0\).

**So what are \(P_0\) and \(P_1\) for?** Internal consistency, not
practical content, and the paper says so where it introduces \(P_1\):
"Between \(P_0\) and \(P_1\) the middle-band estimate is true but weaker
than the trivial bound; the theorem is asymptotic and its implied
constant absorbs the difference." Read that way the certificate is doing
exactly its job, and the four passes of this ledger that chased factors
of \(7\) and \(2.5\) were sharpening a number that was never the reach.
COMPUTATIONALLY VERIFIED; \(2^{96}\) and the exponent arithmetic are
EXACT.

### The audit module reaches the errata, and the probe now measures both objects

The last file the two errata had not reached. `paper_b_audit.py` asserted
`135/1024`, `1215/1024` and `b = -405/176` as the paper's constants, and
quoted `P_0 = 8.9e13` in ten places.

*The identity rows.* `81/1024 - 972/1024 + 756/1024 = -135/1024` is kept
--- it is correct arithmetic about \((cG_F)''\), and the point of the
erratum is that this is not the anchor --- and five rows are added beside
it: the anchor `-972/1024 + 756/1024 = -27/128`, the statement that the
two differ by \(c''G_F\) and by a factor \(8/5\) exactly, the global
monomial \(243/128\) beside the printed \(1215/1024\), the corrected
`b = -81/22`, Step E's \(2187/2048 = 3^7/2^{11}\) with
`b' = -729/352 = (9/16) b`, and the moving-gap foil \(2673/1024\) with the
assertion that it is *not* \(243/128\). The \(\Phi\)-coefficient row and
the \(\lambda_0\)-range row are corrected in place. 258 rows, none
failing.

*The probe now measures both.* `frozen_anchor_curvature_samples` built
\(cG_F\) with no \(J_F\) subtracted, which is why it confirmed the printed
constant for as long as it did. It now reports three ratios rather than
one:

```text
   frozen_ratio       |(c G_F)''|      / (135/1024 ...)   1.0000000 .. 1.0000002
   anchor_ratio       |(c(G_F-J_F))''| / (216/1024 ...)   0.9997072 .. 0.9999985
   anchor_over_bare   the quotient of the two             1.5995 .. 1.6000
```

The third is the erratum in one line: the anchor is \(8/5\) of what was
printed, measured, at every sample. `moving_gap_ratio` is now taken
against \(2673/1024\) and reads \(0.4545 = 1215/2673\), which is the
statement that the frozen and moving models are different functions
rather than a near miss.

*The \(P_0\) mentions.* Ten, now \(3.6\cdot10^{13}\); the \(c_7\) lever
row reads \(120\) instead of \(300\); the interpolant rows read
\(85.2820 \le 85.3\), doubled to \(170.6\) printed \(171\), and the third
displayed term \(0.9070\) printed \(0.91\). The comment beside the
certificate read --- "a hardcoded 8.9e13 would go stale the moment they
move" --- now records that it did.

Every surface the two errata touch is consistent: manuscript, both
mirrors, the certificate module, the audit module, the Lean certificate
and five test files. COMPLETE.

## The coverage map, and the headline density that had no probe

Mapping the audit's fifteen probes onto the twenty-one numbered results
of Sections 4--6: fourteen are probed, two carry only a \(P_0\) row
(Theorem 4.1, Proposition 4.5), and six had nothing at all --- all six
in Section 4, where the coverage stopped after Theorem 4.8.

**One of the six was a headline number.** Corollary 4.9 is the
certified-descent density \(13/16\), and with Theorem 6.3's two
length-five contractors it is the \(7/8\) the frontier figure quotes.
Neither had ever been counted. Counting words to depth five is one pass:

| prefix | count at \(N=10^5\) | density | printed target | deviation | printed error |
|---|---|---|---|---|---|
| \(E\) | \(50000\) | \(0.500000\) | \(\tfrac12\) | \(0\) exactly | \(0\) |
| \(OE\) | \(25015\) | \(0.250150\) | \(\tfrac14\) | \(+15\) | \(\ll N^{5/6}\) |
| \(OOEE\) | \(6176\) | \(0.061760\) | \(\tfrac1{16}\) | \(-74\) | \(\ll N^{23/24+\varepsilon}\) |
| \(OOOEE\) | \(3181\) | \(0.031810\) | \(\tfrac1{32}\) | \(+56\) | \(\ll N^{23/24+\varepsilon}\) |
| \(OOEOE\) | \(3153\) | \(0.031530\) | \(\tfrac1{32}\) | \(+28\) | \(\ll N^{23/24+\varepsilon}\) |

Totals \(0.811910\) against \(13/16=0.8125\), and \(0.875250\) against
\(7/8\). At \(N=10^6\) they sharpen to \(0.812486\) and \(0.874925\).
Every deviation is far inside its printed error term, and the \(E\)
count is \(\lfloor N/2\rfloor\) exactly, as the corollary says.
COMPUTATIONALLY VERIFIED; \(\tfrac12+\tfrac14+\tfrac1{16}=\tfrac{13}{16}\)
and \(\tfrac{13}{16}+\tfrac1{32}+\tfrac1{32}=\tfrac78\) are EXACT.

**What is still uncovered**, and why each is or is not reachable:

| result | why it has no probe |
|---|---|
| Lemma 4.6 | a pointwise two-sided identity, \(v^{1/2}=n^{9/8}+D\) with \(-\tfrac34n^{-3/8}-n^{-9/8}\le D\le0\) --- **checkable, and the obvious next one** |
| Lemma 4.10 | an abstract summation-by-parts inequality; checkable on synthetic \(a_n\) and \(\gamma\) |
| Corollary 4.13 | structural, \(J^4(n)\in[m'^2,(m'{+}1)^2)\) even on the \(OOEEE\) class --- checkable by iteration |
| Theorem 4.11, 4.12 | asymptotic \(\varepsilon\)-statements, the same class as Theorem 5.3: no finite check |

So three of the five remaining gaps are cheap and one pair is not
checkable in principle. The audit reaches everything in Sections 5 and 6
and has one Section 4 result left that is both uncovered and elementary.

## Lemma 4.6's two ends, and what saturates the lower one

The last elementary gap in the Section 4 coverage is closed, and the
answer to the census-power question is the sharpest instance of it yet.

**The upper end is a sign claim.** \(D\le0\) compares two exactly
computed quantities, so a census over it has total power: any
perturbation whatever is caught. Two hundred samples across
\(10^4\ldots2\cdot10^{16}\) give \(D\le0\) every time.

**The lower end is attained, and what attains it is \(\theta\).**
Expanding twice,
\[
D=-\tfrac34\,\theta\,n^{-3/8}-\frac{\theta_2}{2n^{9/8}}+O(n^{-15/8}),
\]
so
\[
\frac{D}{-\tfrac34n^{-3/8}-n^{-9/8}}=\theta+O(n^{-3/4}).
\]
Measured, the two agree to the digit: at \(10^{16}\) the largest ratio
is \(0.989292\) and the largest \(\theta\) is \(0.989292\), differing by
\(9.9\cdot10^{-13}\); at \(10^8\) by \(1.2\cdot10^{-6}\), the
\(n^{-3/4}\) exactly. The residual constant of the two-term model comes
out at \(0.0929\) against \(\tfrac3{32}=0.09375\) --- approached from
below because it carries \(\theta^2\).

**So the census-power reading applies, and gives \(1-\max\theta\).**
The printed \(\tfrac34\) could be cut to \(\tfrac34\max\theta\)
undetected, and \(\max\theta\) over a random sample is
\(1-O(1/\text{samples})\): at \(200\) samples the power is
\(6.0\cdot10^{-3}\). This is the Lemma 6.2 pattern one level down ---
the bound is sharp, the saturating configuration is a fractional part
approaching \(1\), and a directed family (any \(n\) with \(n^{3/2}\)
just below an integer) reaches it where random sampling cannot.
COMPUTATIONALLY VERIFIED; the exponents \(-\tfrac38\), \(-\tfrac98\),
\(-\tfrac{15}8\) and the \(-\tfrac34\) gap between the two ends are
EXACT.

Coverage after this entry: fifteen of the twenty-one results of Sections
4--6 probed, two with a \(P_0\) row only, and four uncovered --- of
which Lemma 4.10 and Corollary 4.13 are checkable and Theorems 4.11 and
4.12 are asymptotic \(\varepsilon\)-statements with no finite check.

## Corollary 4.13: the structure holds, the nesting constant is \(\tfrac38\), the error term does not reach

**The structural claim holds.** On the even blocks
\(I(m')=[m'^{32/9},(m'{+}1)^{32/9})\) at \(m'=60\) and \(m'=100\) ---
\(63573\) and \(232558\) odd starts --- every \(n\) whose first five
letters are \(OOEEE\) with \(J^5(n)=m'\) has \(J^4(n)\) even and inside
\([m'^2,(m'{+}1)^2)\). No exceptions. COMPUTATIONALLY VERIFIED.

**The density lands, and its printed error cannot be tested.** The class
holds \(3903\) of \(63573\) at \(m'=60\) (\(0.061394\)) and \(14534\) of
\(232558\) at \(m'=100\) (\(0.062496\)), against
\(\tfrac1{16}=0.0625\); at \(m'=200\) it is \(0.062724\). But the
printed error \(O(\lvert I\rvert m'^{-4/27+\varepsilon})\) has
\(m'^{-4/27}=0.55\) at \(m'=60\) and \(0.51\) at \(m'=100\): the error
term is half the block. It reaches \(10\%\) only at
\(m'=10^{27/4}=5.6\cdot10^{6}\), where the block holds \(2\cdot10^{17}\)
integers. So the count agrees with \(\tfrac1{16}\) to four digits and
the printed error is untestable --- the same reach reading as the
level-2 kernel benchmark, one section earlier.

**And claim (a)'s constant is \(\tfrac38\), not \(1\).** The nesting
\(0\le n^{9/16}-v^{1/4}\le n^{-15/16}\) holds at every sample, with the
ratio to the printed bound topping out at \(0.3742\)--\(0.3748\) across
four ranges from \(10^4\) to \(10^{14}\). Expanding twice,
\[
n^{9/16}-v^{1/4}
=\tfrac38\,\theta\,n^{-15/16}+\tfrac14\,\theta_2\,n^{-27/16}+\cdots,
\]
so the sharp constant is \(\tfrac38\), the saturation is \(\theta\)
again, and the printed \(1\) is loose by \(\tfrac83\). EXACT for the
expansion; the exponents \(-\tfrac{15}{16}\) and \(-\tfrac{27}{16}\) are
in `exponent_checks`.

That is the third bound in two entries whose saturation turns out to be
\(\theta\): Lemma 4.6's lower end at \(\tfrac34\), this one at
\(\tfrac38\), and Lemma 6.2's \(\theta_2\) end from further back. The
census-power reading is the same each time --- \(1-\max\theta\), of
order \(1/\text{samples}\).

**A slip worth recording.** My first pass at claim (a) used \(J^2(n)\)
for \(v\), which is right only when the first two letters are \(OO\);
\(v=\lfloor m^{3/2}\rfloor\) is defined for every odd \(n\), and off
that branch \(J^2\) is \(\lfloor\sqrt m\rfloor\) instead. The check
reported a violation by ten orders of magnitude, which is what made it
obvious.

Coverage after this entry: sixteen of twenty-one probed, two with a
\(P_0\) row only, and three uncovered --- Lemma 4.10, which is
checkable, and Theorems 4.11 and 4.12, which are not.

## Lemma 4.10's constant is sharp --- the first one that is --- and free where it is used

**Sharp.** Abel summation gives
\(\lvert\sum a_nw_n\rvert\le\max\lvert A\rvert\bigl(1+\sum\lvert
w(n)-w(n+1)\rvert\bigr)\), and the proof then uses
\(\lvert e(x)-e(y)\rvert\le2\pi\lvert x-y\rvert\), which is sharp only
as the step goes to zero. Both steps saturate together: take \(\gamma\)
linear with total variation \(T\) over \(L\) points and align the
partial sums so every term of the Abel expansion points the same way.

| | \(L=10\) | \(100\) | \(1000\) | \(10^4\) |
|---|---|---|---|---|
| \(T=0.5\) | 0.996155 | 0.999968 | 1.000000 | 1.000000 |
| \(T=2.0\) | 0.926569 | 0.999378 | 0.999994 | 1.000000 |

So \(1+2\pi\,\mathrm{TV}(\gamma)\) is attained in the limit. Random
\(a_n\) and \(\gamma\) reach only \(0.924\) over eight hundred
instances --- sharpness here needs a construction, not a census, which
is the fourth time in this ledger that a random search would have
reported a bound as loose when it is tight. COMPUTATIONALLY VERIFIED.

**And free.** In the application \(\mathrm{TV}\le2h\lvert I\rvert
\sup\lvert g''\rvert\le0.26P^{1/24+1/12+1-23/16}=0.26P^{-5/16}\), which
is \(1.5\cdot10^{-5}\) at \(P_0\): the factor is \(1.0000949\). The
constant is sharp and its sharpness does not matter where the lemma is
used --- the twist costs one part in ten thousand. The exponent
\(-\tfrac5{16}\) is EXACT and in `exponent_checks`.

**Which settles the four-in-a-row question.** Lemma 4.6's \(\tfrac34\),
Corollary 4.13(a)'s \(1\) against a sharp \(\tfrac38\), and Lemma 5.1(iii)'s
band are all loose; this one is not. The distinction is structural: the
first three bound a quantity whose saturating configuration is a
fractional part, and the printed constant is the sup over a variable the
proof then discards; Lemma 4.10 bounds a sum by a construction that can
be chosen, so its constant is attained by choosing it.

**Coverage.** Seventeen of the twenty-one results of Sections 4--6 are
probed, two carry a \(P_0\) row only, and the two that remain --- Theorems
4.11 and 4.12 --- are asymptotic \(\varepsilon\)-statements of Theorem 5.3's
class, which admit no finite check. Every checkable result in Sections 4
to 6 now has one.

## Section 3's two printed constants, checked

Of the ten Section 3 lemmas, two carry constants the rest of the paper
uses directly. Both hold.

**The A-process display (Lemma 3.3's used form).**
\(\lvert\sum a_n\rvert^2\le2P^2/H+(4P/H)\sum_{1\le h<H}\lvert\sum
a_{n+2h}\overline{a_n}\rvert\) holds on every family tried --- constant,
random, linear phase, quadratic phase --- and dominates the classical
inequality \(\tfrac{P+2H}H\sum_{|h|<H}(1-\tfrac{|h|}H)\sum
a_{n+h}\overline{a_n}\) it is said to come from. At the extremal
sequence \(a_n\equiv1\) the looseness factorises exactly:

| ratio at \(a_n\equiv1\) | value | limit |
|---|---|---|
| LHS / classical | 0.4873 | \(\tfrac12\) |
| printed / classical | 3.8221 | \(4\) |
| LHS / printed | 0.1275 | \(\tfrac18\) |

The \(4\) is two from \(2P^2/H\) against \(P^2/H\) and two from dropping
the weights \(1-\lvert h\rvert/H\) --- which the paper says it is doing.
So the display is loose by \(8\) at its worst input and by four to six
orders on the sequences it is actually applied to (random \(4\cdot
10^{-4}\), linear \(2\cdot10^{-6}\)): the constants are not where the
argument's strength lies, and the paper does not claim they are.
COMPUTATIONALLY VERIFIED; \(\tfrac12\cdot\tfrac14=\tfrac18\) is EXACT.

**Erdős--Turán (Lemma 3.4).** Printed as \(D\ll R/H+\sum_{h\le
H}\tfrac1h\lvert\sum e(hx_j)\rvert\), with no constant. Over random,
Kronecker, clustered and arithmetic point sets at three
\((R,H)\) settings, the constant the printed form needs is at most
\(0.38\) --- so it holds with an absolute constant below \(1\), and the
\(\ll\) is honest. COMPUTATIONALLY VERIFIED.

**Lemma 3.5 (Vaaler) is not checked here.** Its content is the existence
of the polynomials with \(\lvert a_q\rvert\le\min(1,2/\lvert q\rvert)\)
and \(\Delta_J\ge0\) of degree \(J\); verifying it means constructing the
Beurling--Selberg majorant, which is a different kind of exercise from
evaluating a printed inequality, and it is a cited classical result
rather than a constant of this paper.

## What a 1% cut would set off, and what it would not

The census-power reading applied to the audit as a whole. Four layers,
with quite different powers.

**1. The exact identities: total.** They compare integers or cancel to
\(10^{-40}\). Any perturbation whatever is caught, which is why 480
samples is enough and 4800 would buy nothing.

**2. The exponent layer: exact, and orthogonal.** 268 rational
statements. A wrong exponent is caught outright; a \(1\%\) numeric
change is not expressible in it, so the layer neither catches nor misses.

**3. The eleven policed constants: three regimes.** A \(1\%\) cut
multiplies the observed ratio by \(1.0101\), so it is caught only from
an extreme ratio of \(0.9901\) up. Sampling eight times harder separates
the constants sharply:

| constant | extreme at 768 samples | regime | smallest cut it can catch |
|---|---|---|---|
| L4.3(i) fine, \(\tfrac38(X{-}1)^{-1/2}\) | 0.9995 | saturating | \(0.05\%\) |
| L6.2(i) corrected | 0.9966 | saturating | \(0.3\%\) |
| L5.1(i), \(\tfrac3{16}v^{-1/2}\) | 0.9933 | saturating | \(0.7\%\) |
| L5.1(iv) \(M_1\), \(0.43\) | 0.9777 | creeping | \(2.2\%\) |
| L5.1(iv) brackets \(\le2\) | 0.8558 | creeping | \(14.4\%\) |
| L4.3(i) coarse, \(\tfrac12n^{-3/4}\) | 0.7497 | creeping to \(\tfrac34\) | \(25\%\) |
| L6.2(ii) corrected | 0.6626 | creeping | \(33.7\%\) |
| L5.1(iii) first bracket, \(2.6\) | 0.5771 | **structurally loose** | \(42.3\%\) |
| L5.1(iii) second bracket, \(15\) | 0.4523 | **structurally loose** | \(54.8\%\) |

The saturating three approach \(1\) as sampling grows --- their power is
\(1-\max\theta\approx1/\text{samples}\), so detecting a \(p\%\) cut needs
about \(1/p\) samples of the saturating configuration. The two
structurally loose ones do not move at all under eight times the
sampling (0.5771 at every size): their extremes are set by the
deterministic gap between the printed constant and the true one ---
\(\tfrac32\) against \(2.6\), \(\tfrac{27}4\) against \(15\) --- so no
sample size ever policies them. The coarse L4.3 bound creeps to exactly
\(\tfrac34\), which is \(\tfrac38/\tfrac12\): its \(25\%\) is structural
too. COMPUTATIONALLY VERIFIED.

**4. \(P_0\): any change moves it; the question is the rounding.** A
\(1\%\) cut in \(c_7\) moves the binding row by \(+4.3\%\), a \(1\%\)
rise in the interpolant error by \(+1.9\%\), in \(\kappa\) by
\(+2.3\%\). The manuscript quotes \(P_0\) to two significant figures,
which resolves \(1.4\%\) at a rounding boundary and \(2.8\%\)
guaranteed. So all three are caught here, two of them only because the
current value sits near a boundary --- the guard's real resolution is
\(2.8\%\), not \(1\%\).

**The summary of twenty-one entries, in one line.** This audit catches
any error in an identity, any error in an exponent, a sub-percent error
in three printed constants, a few-percent error in \(P_0\), and nothing
at all in the two bracket constants, whose looseness is structural and
whose sharp values --- \(\tfrac32\) and \(\tfrac{27}4\) --- were found
by expansion rather than by sampling.

## The \(r=4\) reading, settled on instances: A.5 is right

Two entries ago this ledger recorded three readings of the transition
lengths --- A.5's \((4,1)\), A.6's \((2,1)\), Lemma 3.9's proof
\((4,8\) per interval, up to two\()\) --- and said the direction ran
against the paper, with \(P_1\) five orders higher on the proof's
constants. That was a comparison of passages. This entry compares them
against the objects.

**The test.** Three-term monomials on the Step-5b triple
\((\tfrac54,\tfrac{11}8,\tfrac32)\) with a zero of \(f''\) inside
\((P,2P]\), kept only when Lemma 3.9's own hypothesis
\(\max(\lvert f''\rvert,n\lvert f'''\rvert,n^2\lvert f''''\rvert)\ge
c_7S\) holds across the block. On \(383\) admissible instances of
\(400\), with \(V=c_7S/2\):

| | value |
|---|---|
| instances with a nonempty sublevel set | \(383/383\) |
| instances with a point served only by \(f''''\) | \(7\) (\(1.8\%\)) |
| worst \(\lvert\Omega_V\rvert\) against A.5's bound | \(0.3699\) |

**A.5's display holds on every one, with a factor of \(2.7\) to spare.**
And the \(r=4\) branch is not vacuous --- it fires on about \(2\%\) of
admissible instances --- so the smaller constant is not surviving
because the case never arises. The proof's constants are what the
derivation gives; A.5's are what the objects need.

**What a violation requires.** Forcing a *double* zero of \(f''\) does
break A.5's bound --- the sublevel set fills the whole block, a factor
\(\sqrt2\) past it --- but every such instance fails the hypothesis:
\(\max(\lvert f''\rvert,n\lvert f'''\rvert,n^2\lvert f''''\rvert)/S\)
drops to \(0.002\)--\(0.004\) against \(c_7=0.0043\). That is what
\(c_7\) is for, and it is the first time in this ledger that a
constant's *purpose* has shown up in a measurement rather than in
prose.

**So the earlier entry stands corrected.** The three passages do differ,
and a reader reconstructing Lemma 3.9's proof gets \(16\) where A.5
carries \(1\); but A.5's number is not wrong, it is sharper than the
derivation that precedes it, and \(P_1=9.8\cdot10^{18}\) stands.
COMPUTATIONALLY VERIFIED on one family of instances --- three-term
monomials with a simple zero --- and not a proof; what it removes is the
suggestion that the paper's own proof contradicts its appendix.

## The \(r=3\) length: the measurement does separate the two constants

The same instances settle A.6 against Lemma 3.9's proof, and this time
the two are not equivalent.

**The local bound is the real one.** Near a simple zero \(n_0\) of
\(f''\), \(\lvert f''\rvert\approx\lvert f'''(n_0)\rvert\lvert
n-n_0\rvert\), and the hypothesis gives \(n\lvert f'''\rvert\ge c_7S\),
so the sublevel width is at most \(2Vn_0/(c_7S)\). Over \(1449\)
admissible instances the measured width reaches \(0.949\) of that ---
the local form is nearly attained.

**Which separates the two printed constants exactly.** \(n_0\) ranges
over \((P,2P]\), so the local bound ranges over
\([2PV/(c_7S),\,4PV/(c_7S)]\):

| constant | worst measured ratio | verdict |
|---|---|---|
| A.6's \(2PV/(c_3S)\) | \(1.0003\) | **exceeded** |
| Lemma 3.9's proof, \(4PV/(c_7S)\) | \(0.5002\) | holds, factor \(2\) spare |

A.6's constant is the \(n=P\) form. It is right at the bottom of a
dyadic block and wrong at the top, by exactly the factor \(n_0/P\) --- the
same \(P\)-versus-\(n\) slip this ledger has recorded three times in the
paper and twice in itself. The proof's \(4\) is the \(n\le2P\) form and
is safe. COMPUTATIONALLY VERIFIED; the ratio between the two verdicts is
exactly \(2\) at every sample size, as it must be.

**Nothing downstream moves.** A.6 uses its \(2PV/(c_3S)\) qualitatively,
in the sentence weighing what the per-order vector \((c_2,c_3,c_4)\)
buys and costs; \(P_1\) is computed in A.5, which carries the correct
\(4\). So this is an erratum in one sentence, not a change to any
number. Together with the entry above --- where A.5's \(r=4\) constant
turned out sharper than its own proof --- the pair reads: the appendix
that computes is right twice, and the two passages that describe it are
off by a dyadic factor in one direction and a worst-case derivation in
the other.

## A third \(P\)-versus-\(n\) slip, and this one was the audit's

The last two entries found the dyadic factor in A.6 and in Lemma 3.9's
proof. The third place it appears is here.

**The slip.** The printed band is in the block start \(P\), and a single
\(n\) pins \(P\) only to \([n/2,n)\). A check that cannot miss a
violation must therefore take the *largest* admissible \(P\) for a lower
bound and the *smallest* for an upper one --- \(P=n\) below, \(P=n/2\)
above. `check_lemma_5_1_ii_iv` used \(P=n\) on both sides, with a
comment saying so, which is loose by \(2^{3/4}\) in each direction.
(For a bound in a *negative* power, \(P=n\) is already strict, so the
\(M_1\) bound beside it needed no correction.)

**What it hid.** Under the strict transcription the census still holds
at every sample, and the four bracket ratios move:

| | as checked | strict | meaning |
|---|---|---|---|
| first bracket, upper \(2.6\) | 0.5771 | **0.9705** | the printed \(2.6\) has \(3.0\%\) of room, not \(42\%\) |
| first bracket, lower \(\tfrac32\) | 1.6818 | **1.0000** | exactly attained: the constant cannot be raised at all |
| second bracket, upper \(15\) | 0.4515 | 0.5378 | \(46\%\) |
| second bracket, lower \(1.4\) | 5.7125 | 4.7991 | could be \(4.8\times\) larger |

Both figures now agree with the manuscript-side reading recorded three
entries ago --- true band \([\tfrac32,\tfrac322^{3/4}]=[1.50,2.52]\)
against a printed \([\tfrac32,2.6]\) --- which the audit's own
transcription had been contradicting without either of us noticing.

**And it corrects the sensitivity table.** The entry "What a 1% cut would
set off" reported the first bracket as structurally loose with a
smallest detectable cut of \(42.3\%\). The true figure is \(2.9\%\), and
four constants rather than three detect a \(1\%\) cut. The regime is
still "does not move with sampling" --- but that regime splits: a
constant fixed by the deterministic gap to its true value can be
structurally *sharp*, as this one is, or structurally loose, as the
second bracket is at \(46\%\). The probe now says which.

EXACT for the transcription rule; COMPUTATIONALLY VERIFIED for the
ratios. Three slips of the same kind, two in the paper's prose and one
in the checker written to police it.

## The sweep: three bounds are stated in \(P\), and only they can carry the slip

Answering the last entry's question mechanically rather than by eye.
Scanning the pointwise checkers for a dependence on the block start:

| bound | exponent | side | strict transcription | extreme ratio |
|---|---|---|---|---|
| L5.1(iii) first bracket, lower | \(3/4\) | lower | \(P=n\) | \(1.0000\) |
| L5.1(iii) first bracket, upper | \(3/4\) | upper | \(P=n/2\) | \(0.9705\) |
| L5.1(iii) second bracket, lower | \(1/4\) | lower | \(P=n\) | \(4.7974\) |
| L5.1(iii) second bracket, upper | \(1/4\) | upper | \(P=n/2\) | \(0.5379\) |
| L5.1(iv) \(M_1\) | \(-7/8\) | upper | \(P=n\) | \(0.9613\) |

Everything else in `check_lemma_4_3`, `check_lemma_5_1_i` and
`check_lemma_6_2` is written in \(n\), \(m\), \(v\), \(X\) or \(Y\) ---
quantities a single \(n\) determines --- so no other pointwise bound can
carry the slip. Three bounds, five sides, all now on the strict
transcription and all respecting their side at every sample. EXACT for
the rule, COMPUTATIONALLY VERIFIED for the ratios.

**The sign of the exponent decides the direction.** With a positive
power the two ends differ and the strict choice is \(n\) below,
\(n/2\) above; with a negative power the ends swap, and \(P=n\) is
already the smallest admissible right-hand side --- which is why
\(M_1\), at \(-7/8\), needed no correction while the brackets did.

**And the surface is pinned.** `pointwise_bound_inventory` records which
\(P\)-symbols the checker's source uses (`P34`, `P34_lo`, `P14`,
`P14_lo`, `mp.power(P,`); a new \(P\)-dependent bound changes that set
and fails the guard until the table above is updated with its exponent
and side. That is the fourth guard in this ledger built the same way ---
pin the surface, force the next author to declare the thing that was
implicit --- after the constants guard, the escape guard and the
method-name guard.

Which closes the dyadic-factor thread: two errata in the paper's prose,
one in the audit, a rule that decides all three, and a guard so the next
occurrence has to be deliberate.

## Are the guards watching anything?  Four audited, none blind

A guard that quantifies over an empty collection passes while inspecting
nothing. Counting what each of the four actually sees:

| guard | what it quantifies over | size |
|---|---|---|
| escape, per manuscript | manuscript, mirror, satellites | \(\ge2\) each |
| escape, outside the manuscripts | `OTHER_LATEX_DOCS` | 6 |
| method names | tactic/identifier claims resolved through the import closure | **counted in the test** |
| cross-references | numbered results 37, bracketed citations 49, \S-references 27, numbered refs 11 | non-empty |
| "an earlier \(X\)" | phrase matches in Paper B | 2 |
| pointwise transcription | \(P\)-stated bound sides, sampled | 5 bounds, 322 samples |

**None is vacuous**, and the smallest collection is the two "an earlier
\(X\)" phrases --- small, but real.

**One of them already defends itself.** The method-name guard carries
`assert checked >= 20, "guard went blind: only {checked} claims
matched"`, which is exactly the right shape: it fails when the
manuscript's wording drifts far enough that the guard stops matching,
rather than passing quietly. That pattern is worth more than the guard
it sits in.

**So it has been copied.** `pointwise_bound_inventory` now counts the
ratio samples it inspects and reports `did_not_go_blind` at a floor of
100; the test asserts it. And the directed-family test, whose
`all(r["ok"] for r in rows)` had no companion count, now asserts the
ladder has at least five rungs --- an empty ladder would have satisfied
every `all()` beneath it.

Two of the six quantified assertions in the Paper B tests were relying
on a neighbouring index or `max()` to raise on an empty collection
rather than on an explicit count. That works, but only by accident of
what happens to be written next to them, which is the same reliance the
tactic guard's author decided not to accept. COMPUTATIONALLY VERIFIED
for the counts; the audit itself is EXACT --- either a collection is
empty or it is not.

## What the "an earlier" guard does not watch, and where the rest of it sits

The guard polices the phrase the referee named --- "earlier draft",
absent --- and whitelists two words after "an earlier". The family is
wider: "previously", "in an earlier", "used to", "no longer", "the
former". Nine occurrences survive, and *where* they sit decides what
they are.

| location | count | reading |
|---|---|---|
| Appendix A, A.5, A.6 | 5 | the appendix's own subject |
| body, mathematical | 2 | earlier in a chain, not in a draft |
| body, status | 2 | what the Lean layer covered before; a comparison the raised threshold retired |

**The five in the appendix are not residue.** A.5 exists to say why
\(\kappa=\tfrac1{12}\) rather than \(\tfrac13\), and A.6 why
\(R_0=P^{5/16}\) rather than \(P^{1/4}\); a sentence like "a band that
no longer contains \(9/32\), whose \(7.4\cdot10^{13}\) used to sit just
under the old \(P_0\)" is the comparison those sections are for.
Removing it would remove the argument.

**Two of the four in the body are mathematics.** "Linearizing the wave
in an earlier defect \(\theta_s\)" is earlier in the chain of defects,
and a term that is "no longer drift-blocked" has just been differenced
across the threshold. Neither is history.

**Two are status.** \S4 records that three Lean statements "were
previously supported only by the probe's 60-digit sampling", which is
about the repository rather than the theorem; and the Theorem 5.3
architecture note says the two comparisons "no longer conflict" under
the raised threshold, which describes the superseded design. Both are
defensible --- the first tells a reader what is proved and what is
sampled --- but they are the two sentences in the body that a referee
looking for the development log would stop at.

`draft_history_markers` reports the nine with their sections and flags
body occurrences that are neither mathematical nor in the appendix; the
test allows the two that are there and fails on a third. So the answer
to "did the lost phrases leave because they were fixed" is: the one the
referee named is gone, and its family did not follow it out --- it moved
to the appendix, where it belongs, except for two sentences that stayed.
COMPUTATIONALLY VERIFIED by location; the classification of the four
body occurrences is a judgement, recorded as one.

## The trust table read as data, and what it does not have a column for

**The \S4 sentence and the table agree.** Section 4 says five Lean
statements --- `fract_diff_level2`, `lemma51_double_gap`,
`double_difference_product`, `lemma51_master`, `lemma51_brackets_le_two`
--- "were previously supported only by the probe's 60-digit sampling
\ldots they are exact, so they are now proved rather than sampled". All
five sit in the table's Lemma 5.1 row, and all five are declared in
`formal/Problems/Juggler/MasterIdentity.lean`. (The entry above said
three; it is five.)

**The table's twenty rows, by warrant:**

| warrant | rows |
|---|---|
| a Lean identifier | 7 |
| this paper, and nothing else | 9 |
| quoted from elsewhere | 4 |

The largest Lean row is Lemma 5.1 with fourteen identifiers --- the
master identity's whole chain --- and the four quoted rows are
Proposition 3.1 (the companion) and the three classical inputs.

**And it has no "sampled" column at all.** Its three warrants are a
proof in this paper, a Lean identifier, and a classical result; the
preamble says the Lean layer checks identities, constants and thresholds
and "not any estimate". So nothing in the table is carried by sampling
*by construction* --- what sampling carries is this module, which the
paper's repository paragraph calls not a proof and not an independent
verification. The question "is anything else in that table still carried
by sampling" has the answer: nothing ever was, because the table does
not record that kind of warrant.

**What it does mark is where the proof stands alone.** Two rows are
bolded: Lemma 5.2(i)--(iii), with no Lean at all, and Theorem 5.3, whose
Lean is "Step 5b constants only, **no part of the assembly**". Those two
are the paper's own statement of where a reader has nothing but the
argument, and they are the two the ledger has spent the most passes
circling --- the middle band and the kernel theorem. COMPUTATIONALLY
VERIFIED: the table parses into 20 rows whose warrants partition, and
the five \S4 identifiers resolve in both directions.

## The row with the least company, and its engine counted

**Which row.** Of the nine statements the trust table rests on this
paper alone, measuring each one's numerical company --- probes plus
exponent checks:

| row | probe | exponent checks |
|---|---|---|
| Prop. 7.1 reduction | none | **0** |
| Thm. 4.11, 4.12 localization | none | 0 (asymptotic; no finite check exists) |
| Lem. 3.7 shifted window | none | 1 |
| Prop. 7.4 shift average | none | 2 |
| Thm. 4.4, 4.7, 4.8, Cor. 6.4 | probe | 1--2 each |
| Lem. 5.2, Thm. 6.1, Thm. 6.3 | probe | 17--55 each |

Proposition 7.1 had nothing at all, and unlike 4.11 and 4.12 its engine
is finite.

**What is checkable in it.** The conclusion is conditional and
asymptotic, but the count underneath is not: \(N_d\), the number of
length-\(d\) words with no contracting prefix, is claimed
\(\le2^de^{-cd}\) with
\(c=2(\tfrac{\log2}{\log3}-\tfrac12)^2>0.0342\), and a prefix contracts
exactly when its scale exponent falls below \(1\) --- which
`paper_b_prefix_count.iterate_exponents` computes.

| \(d\) | 1 | 4 | 8 | 12 | 16 | 18 |
|---|---|---|---|---|---|---|
| \(N_d\) | 1 | 3 | 19 | 226 | 2114 | 7495 |
| \(N_d/(2^de^{-cd})\) | 0.517 | 0.205 | 0.098 | 0.083 | 0.056 | 0.053 |

**The bound holds at every \(d\), and its slack grows.** The ratio falls
from \(0.52\) to \(0.053\); the observed decay rate is about \(0.21\),
some \(6\times\) the printed \(c=0.0343\). Proposition 7.1 needs only
\(c>0\), so nothing in the argument suffers --- what is loose is a
structural count the paper displays, and it is loose by a factor that
grows exponentially in \(d\).

COMPUTATIONALLY VERIFIED to \(d=18\) (262144 words); \(c\) matches
`HOEFFDING_C` in the prefix module to machine precision, so the paper,
that module and this probe agree on the constant and now on what it
bounds.

## Proposition 7.4's \(\tfrac4\pi\): where it comes from, and how much of it is reachable

**Where it comes from.** Write the cross term of a pair in
\(u=\{x_t+\lambda\}\); the shift \(x_{t'}-x_t\) splits the integral at
one point, so each pair contributes *two* geometric pieces, each of
modulus at most \(1/(\pi\lvert\Delta\rvert)\). With
\(\lvert\Delta\rvert\ge\mathcal A'_{\min}\lvert t-t'\rvert\) and both
orderings counted, the sum over pairs is at most
\[
\frac{2\cdot2}\pi\,\frac L{\mathcal A'_{\min}}\sum_{k<L}\frac1k
\le\frac4\pi\,\frac L{\mathcal A'_{\min}}(\log L+1).
\]
So \(\tfrac4\pi\) is two pieces times two orderings over \(\pi\) --- the
constant is what the derivation produces, not a choice. EXACT.

**The pairwise step is sharp.** At \(L=2\),
\(\mathcal A'_{\min}=1\), searching over the gap and the two shifts, the
largest off-diagonal found is \(1.2556\) against the pairwise ceiling
\(4/\pi=1.2732\): \(98.6\%\) of it, at
\(\Delta\approx1.01\) with the two shifts about \(0.5\) apart --- both
pieces saturating their sine at once.

**The assembled bound is not.** Its ratio to the printed right-hand side
runs \(0.29\) at \(L=2\), \(0.10\) at \(L=4\ldots32\) across integer and
jittered spacings at \(\mathcal A'_{\min}\in\{1,2\}\); integer spacing
gives exactly \(0\), since every cross integral vanishes. The gap is the
assembly: \((L-k)/k\le L/k\) overcounts, and the per-pair sines cannot
all saturate together. So the constant is sharp where it is derived and
loose where it is used, by a factor of about ten at the sizes tested.

**And that is the fourth of these.** Lemma 4.10's \(1+2\pi\mathrm{TV}\)
is sharp and attained; Lemma 4.6's \(\tfrac34\) and Corollary 4.13(a)'s
\(1\) are loose with sharp values \(\tfrac34\theta\) and \(\tfrac38\);
this one is sharp in its step and loose in its sum. The pattern across
all four: a constant is attained exactly when the configuration that
attains it is *choosable*, and here one pair is choosable while \(L\)
pairs at once are not. COMPUTATIONALLY VERIFIED.

**Correction, from a search rather than a sweep.** The families above do
not optimise. A hill climb on the gaps and the shifts reaches
\(0.333\), \(0.279\) and \(0.174\) at \(L=3,4,6\) --- two to three times
what the fixed families give at the same \(L\), and the probe now
carries a short version of it. The conclusion is unchanged and better
supported: the ratio still falls with \(L\), from a third at \(L=3\) to
a sixth by \(L=6\), so the assembled bound is approached at small \(L\)
and lost as the harmonic overcount grows. What was wrong in the entry
above was reporting \(0.10\) at \(L=4\) as *the* figure when it was only
what an unsearched family happened to give; the searched figure there is
\(0.279\).

## Two updates the concurrent revision forced, and one guard firing

**The pairing repair is now worth 8%, not a factor of seven.** The entry
"\(P_0\)'s binding row is charged at a cell that does not exist" reported
that repairing the interpolant pairing would drop \(P_0\) from
\(3.59\cdot10^{13}\) to \(4.89\cdot10^{12}\). The per-row arithmetic
still holds --- \(7.33\), \(7.58\) and \(53.1\) on the three rows that
carry the error --- but the consequence does not. A row added since,
`st6D1-modeindex` ("widened \(\lvert B_0\rvert\le R_0\):
\(7P^{1/4}\le P^{5/16}\)"), sits at \(3.32\cdot10^{13}\), just under the
binding row. With the pairing fixed it becomes the maximum, so \(P_0\)
falls only to \(3.32\cdot10^{13}\): a factor of \(1.079\).

The finding is unchanged and its value is not. Two tests that pinned the
old consequence --- "\(>2\)" and "\(>10\times\) the largest untouched
row" --- have been re-aimed at what is invariant: every pairing row
over-charges, and the direction is safe. What a repair is worth depends
on what sits underneath it, and something now does.

**Proposition 7.4's assembled bound is approached more closely than the
sweep said.** Reported at \(0.10\) for \(L=4\ldots32\) from fixed
families; a hill climb on the gaps and shifts reaches \(0.333\),
\(0.279\), \(0.174\) at \(L=3,4,6\). The conclusion is unchanged --- the
ratio still falls with \(L\) --- but \(0.10\) was what an unsearched
family happened to give.

**And the guard fired.** The phrase the referee named is back: at line
3070 of the working copy, inside an erratum block, "An earlier draft got
the window count from …". Both `draft_history_markers` here and
`test_paper_b_body_carries_no_draft_history` in the manuscript guards
report it. The erratum's content is a correction to the reason printed
for a window count, which is the ledger's kind of material rather than
the body's; the phrase is the referee's own marker, so it is worth
seeing before it is committed. Reported, not edited --- the manuscript
is the other session's, and the sentence is a minute old.

## A row that was in a proof and never in the table, and the two appendices written around its absence

**Lemma 5.2(iii) states a threshold that A.1 never collected.** Closing
its mode accounting needs the widened decoration's index under Stage 2's
truncation, `|w| <= |B_0| + R_0 <= 2 R_0`, and the proof says so with its
number: "because 7 P^(1/4) <= P^(5/16) once P >= 7^16 = 3.3e13". That
inequality is a certificate row. It was not in the thirty-seven. Added as
`p0_certificate.st6D1-modeindex` and `row_st6D1_modeindex`; the table is
thirty-eight rows and thirty-three theorems, and `lake build` is green.

`P_0` does not move. `7^16 = 33232930569601` sits under the binding row's
`3.5858e13` -- rank two of thirty-eight, at `92.7%` of it. Everything else
about the row moves something.

**It is the largest row that does not mention `c_7`, so it is A.5's
floor.** A.5 computed that floor from the table, and the table was short
one entry. The consequences, all of them arithmetic once the row is in:

```text
                          printed        with the row
  c_7 floor               2.98e11        3.32e13
  the whole c_7 lever     factor 120     factor 1.079
  lever spent at          c_7 = 1/61     c_7 = 1/228
  vector trade realises   8.9 of it      nothing at all
```

The vector trade is the sharpest of these. `(1/27, 1/1872, 1/1872)` was
recorded as moving `P_0` to `4.0e12` at a cost of four orders in `P_1`;
`4.0e12` is a statement about the gate, and the mode index holds `P_0` at
`3.32e13` whatever the gate does. The trade returns the same `P_0` it
started from. Keeping the uniform constant was right for a better reason
than the one printed.

**And it pins `R_0` from below, which is the question A.6 asks.** A.6
tabulates four `R_0`-sensitive sites and reports that `5/16` is feasible
but not optimal, the four-site minimax being `a* = 0.29919` at `1.40e11`.
The fifth site makes `0.29919` infeasible by four orders: it needs
`7^(1/(a-1/4)) = 1.5e17` there. The bands:

```text
  four sites   a in [0.2829, 0.3463]      5/16 clears the left end by 2.96e-2
  five sites   a in [0.3123, 0.3463]      5/16 clears the left end by 1.52e-4
```

No fraction of denominator `<= 32` lies in `[0.31235, 0.3125)`, so `5/16`
is the smallest simple truncation that closes by `P_0` -- which is a much
stronger statement about it than A.6 was making, and it comes with the
opposite moral. Against the four sites `5/16` is the robust choice, well
clear of the cliff. Against five it is the least robust admissible value:
the row needs `7 <= P_0^(1/16) = 7.0333`, so a widened coefficient of
`7.04` would carry it past the binding row and `R_0 = P^(5/16)` would be
*setting* the paper's threshold. Half of one percent.

The five-site minimax is `a* = 0.3218` at `5.79e11`, where the mode index
crosses the `q''` ratio. `5/16` is a factor `57` above that, not `2.13`;
`1/3` is `1.58e12`, a factor `21` better than `5/16` and with room on both
sides. Recorded, not taken.

**Two smaller things fall out.** At `a = 1/4` the row reads
`7 P^(1/4) <= P^(1/4)`, false at every `P` -- so the superseded truncation
does not merely delay Theorem 6.3 by ten orders, it stops Lemma 5.2(iii)
closing at all. And the row is `kappa`-free, so A.2's `kappa` table stops
falling: the entries at `1/16` and `1/20` read `2.0e13` and `1.5e13` from
the gate and `3.3e13` from the table, and `P_0` is the maximum. The gate
meets the row at `kappa = 1/12.42`. The operating point `1/12`, chosen
because the piece-boundary term turns `P_1` around there, is within
`7.9%` of the last `kappa` at which `P_0` is still moving. Two unrelated
mechanisms, one a piece boundary in `P_1` and one a Vaaler truncation in
Lemma 5.2(iii), agreeing to a factor `1.079`.

**The constant `7` is not sharp, and sharpening it would restore the
factor of 120.** It collects `6 P^(1/4)/h'` and `20 h P^(-1/4)`, and the
second is not of the first's order: `6 P^(1/4) + 20 P^(-1/8) <= (6+d)
P^(1/4)` from `P >= (20/d)^(8/3)`, so `6.001` serves from `2.95e11`, below
`P_0`. The row would fall to `2.83e12` -- a factor `12`, rank four, and
the floor would drop back to the `q''` row's `2.98e11`. Not taken here:
the downstream constants of that proof (`13.5`, `64`, `7/0.6`) are all
stated at `7` and all sit in absorbed or dominated positions, so
re-deriving them buys a floor and no theorem. The row is entered at `7`,
which is what the manuscript proves.

**One thing the row is, that no other row is: exact.** Every other
threshold is certified at a rational `t_0` at or just above the true
crossing. Substituting `P = t^16` turns this one into `7 t^4 <= t^5`,
whose crossing is `t = 7` on the nose.

## The drift sentence in the same proof, which does not follow

Two lines above the mode index, the window count is got from "since `B`
is monotone on the dyadic block its drift is at most `sup|B|`". The count
`7 P^(1/4) + 1` is right. That argument does not give it.

`B` is the widened `(D1)` theta-coefficient, `q'(2 j' f_1 + h h' f_2)`
with `f_1 <= P^(-1/4)` and `f_2 <= 20 P^(-3/4)`. `j'` is the branch offset
of Lemma 5.1(iii): frozen on each `b`-run and jumping between runs, so `B`
is not monotone on the block; and it takes both signs, so even a monotone
`B` would give `2 sup|B|` and not `sup|B|`. Both halves fail.

What does hold needs no sign at all. `f_1` and `f_2` are monotone and
single-signed on the whole block, total variation is additive over a
partition, and `|j'| <= 3` on each run, so the within-run variation sums
to `6|q'| Var(f_1) + |q'| h h' Var(f_2) <= 6|q'| sup f_1 + |q'| h h' sup
f_2 <= 7 P^(1/4)`. The jumps across runs are the `b`-run boundaries the
first bullet already inventories at the same Stage-4 curvature, so they
cost nothing further. Same numeral, and this time a proof.

Worth noting what the printed sentence would have cost had it been the
only route: `2 sup|B|` gives `14 P^(1/4) + 1` windows, boundary charge
`23.7 (uh)^(-1/2) P^(5/8)` instead of `13.5`, still dominated by the
fourth printed term of (i) since `5/8 < 1/24 + 7/8`. The factor two was
never going to bind. The reason still has to be a reason.

Recorded in the manuscript as a blockquote at the site, phrased without
the marker the referee named -- the guard the concurrent session's audit
raised on the first wording is clear.

## The mode-index row rests on `|j'| <= 3`, and `|j'| <= 3` is one more than the argument gives

The section above enters the row at `7`, prices the sharpening to
`6.001` at a factor `12`, and declines it for a stated reason. Two
things about that paragraph, one arithmetic and one structural.

**"The floor would drop back to the `q''` row's `2.98e11`" --- not at
`6.001`, it would not.** The sharpened row is `2.83e12` (`2.824e12`
with the exact `6 + 20P^(-3/8)`). The rows above it are `5b-W<=c7S` at
`3.59e13`, `5a-W<=c7S` at `2.91e13` and `5b-E<=c7S` at `4.10e12` ---
three rows, every one of them a `c_7` row, which is what "rank four"
in the same sentence already says. The sharpened row is still the
largest `c_7`-free row and still A.5's floor:

```text
                          floor        P_0/floor
  without the row        2.98e11         120.3
  printed, c = 7         3.32e13           1.079
  sharpened, c = 6.001   2.83e12          12.70
  hard floor, c = 6      2.82e12          12.71
```

`12.7` is not a stop on the way to `120`: it is a ceiling. For the
`q''` row to lead, the widened coefficient would have to fall below
`(2.98e11)^(1/16) = 5.214`, and it cannot, because the first summand
is `6 P^(1/4)/h'` with `h' >= 1`. Sharpening the *second* summand caps
the `c_7` lever at `P_0/6^16 = 12.71`, by Lemma 5.2(iii) alone.

**Which makes the question the right one to have asked: is `6` sharp?
It is `2|j'|` at `|j'| = 3`, and `3` is not what the object does.**
`j` is the Lemma 5.1(iii) offset
`beta_{d1+d2} - beta_{d1} - beta_{d2}`, and since `beta_d = m(n+d) -
m(n)` the `m(n)` cancel and `j` is exactly the double difference of
`floor(X)`, `X = n^(3/2)`. Write `floor(X) = X - {X}`. The four
fractional parts give a double difference in `(-2, 2)`; `X` is convex
with `Delta^2 X = (3/4) d1 d2 n^(-1/2) + ... <= 3 P^(-7/16) < 1` on the
admissible box. So `j` is an integer in `(-2, 3)`:

```text
  provable      -1 <= j <= 2          two lines, and not symmetric
  printed       |j'| <= 3
  observed       j in {-1, 0, 1}      240 samples, 1e4 to 2e14
                                      57.5% at zero, none at 2 or 3
```

`Delta^2 X` was measured alongside: `0.0300` at worst over the same
census, positive at every sample, three orders under the `1` the
argument needs.

**At `|j'| <= 2` the row leaves the table.** The coefficient is
`4 + 20P^(-3/8) <= 4.001` from the same `2.95e11`, the row is
`4.001^16 = 4.31e9` --- under `s3s1-Bsmall`'s `2.83e10`, rank fifteen
or so, out of the leading group entirely. A.5's floor returns to the
`q''` row's `2.98e11` and the `c_7` lever is worth `120.3` again. The
conclusion of the paragraph above is right; the route printed for it
is not, and the route that works is a change to the *first* summand,
not the second.

The exponent question reopens with it. The five-site left endpoint
falls from `0.31235` to `0.29443`, which is **below** A.6's recorded
four-site minimax `a* = 0.29919`. The fifth site stops making that
optimum infeasible, and stops forcing `5/16` from below. What still
holds at `|j'| <= 2`: `a = 1/4` reads `4 P^(1/4) <= P^(1/4)`, false at
every `P`, so the superseded truncation still stops Lemma 5.2(iii)
closing.

**Not a defect in the theorem.** `|j'| <= 3` is a valid bound and
every use of `7` downstream is a valid bound; the paper proves what it
says. What the census shows is that a cap nobody had reason to sharpen
is carrying two appendices, and that the two lines above are the whole
cost of sharpening it.

**One rounding in Section 7 goes the unsafe way.** "Of the
thirty-eight displayed inequalities, thirty-three hold from `2.8e10`
or below." Thirty-two do. The thirty-third is `s3s1-Bsmall` at
`2.8275e10`, above it: the sentence rounds its own maximum down.
`2.9e10` is the honest round and nothing else in the paragraph moves.

Confirmed at the same numbers while passing through: `7^16 = 3.3233e13`
at `92.68%` of `P_0`; the largest `c_7`-free row of the thirty-eight;
the pin `1/4 + log 7/log P_0 = 0.3123478` with `5/16` clearing it by
`1.522e-4` and being the least sixteenth above it; the five-site
minimax `0.321848` at `5.785e11`, a factor `57` under `5/16`;
`P_0^(1/16) = 7.03333`.

Probes: `mode_index_row_sharpness`, `branch_offset_range`. Six tests.
`P_0` unmoved at `3.5858e13`; no certificate row is edited.

## The printed hypothesis of Lemma 5.1(iii) is exactly the one that gives a narrower window than the printed conclusion

Last pass recorded `-1 <= j <= 2` against the printed `|j| <= 3` and
left one question open: `j'` in the Lemma 5.2(iii) proof is the offset
of the *widened* decoration, and the census measured the plain
level-1 `j`. The manuscript answers it. `(D1')` widens `|q'| h' <=
P^(1/2)`, `h' <= P^(1/24)` and nothing else; the offset bound `|j| <=
3` belongs to class `(D2)` and to Lemma 5.1(iii), neither of which
`(D1')` touches. The Stage-6 instance is the same net offset at the
shift pair `(2h, 2h')` instead of `(d_1, d_2)`. The object does not
change; only what it is quantified over does.

**Which makes the hypothesis the whole story.** Write `u = {X(n)}`,
`alpha = {Delta_1 X}`, `gamma = {Delta_2 X}`, `eps = Delta^2 X`. The
integer parts cancel and

```text
  j = floor(u + alpha + gamma + eps) - floor(u + alpha) - floor(u + gamma)
```

exactly, with `u, alpha, gamma` in `[0,1)`. And `Delta^2 X = (3/4) d_1
d_2 xi^(-1/2) <= 3 h_1 h_2 P^(-1/2)`, so the printed hypothesis
`h_1 h_2 <= P^(1/2)/3` **is** `eps <= 1`. Under it, `j = 3` would need
`u+alpha < 1` and `u+gamma < 1` with `u+alpha+gamma+eps >= 3`, and
those cannot hold together. So `-1 <= j <= 2`: the hypothesis the
lemma already assumes delivers a window one narrower than the
conclusion it states, and an asymmetric one.

**The top value has a support, and it is thin.** `j = 2` forces the
floor pattern `(2, 0, 0)`; then `alpha + gamma < 2 - 2u` gives `2 <=
u + alpha + gamma + eps < 2 - u + eps`, so

```text
  j = 2  ==>  {n^(3/2)} < Delta^2 X.
```

Verified on `167` instances found at `eps` of order one: `u < eps` at
every one, worst ratio `0.884`. On the admissible box `eps <= 3
P^(-7/16) = 3.5e-6` at `P_0`; on the Stage-6 `(D1)` instance, where
the shifts are `2h` and `2h'` with `h <= P^(1/8)` and `h' <= P^(1/24)`,
`eps <= 3 P^(-1/3) = 9.1e-5`.

```text
  family              eps      histogram of j              share at 2
  P=1e4  h=(3,3)     0.270    -1:61  0:253  1:179  2:7        1.4%
  P=1e5  h=(5,7)     0.332    -1:16  0:301  1:183             0
  P=1e6  h=(10,10)   0.300    -1:64  0:232  1:192  2:12       2.4%
  P=1e6  h=(16,20)   0.960           0:94   1:323  2:83      16.6%
  P=1e8  h=(30,100)  0.900           0:101  1:334  2:65      13.0%
```

`2500` points, never `3` and never `-2`. The window is sharp at both
ends once `eps` is of order one, so the worst-case coefficient really
is `4` and not `2`: the pointwise row stays `4.001^16 = 4.31e9`.

**But the pointwise worst case is not where the sum lives.** Off a set
of `n` of density at most `3 P^(-1/3)`, the widened coefficient is
`2 + 20 h h' P^(-3/4) <= 2.001` and the mode-index row is `2.001^16 =
66062` --- not a certificate row at all. Splitting the `(D1)` sum at
`{n^(3/2)} < 3P^(-1/3)` is the shape of the argument that would
retire the row; the exceptional set is small enough to take
trivially, and its density needs equidistribution of `{n^(3/2)}`,
which is classical but is an input the paper does not currently use.

```text
  |j'| bound      coefficient   row        A.5 floor    c_7 lever
  printed  3      7             3.32e13    3.32e13        1.079
  provable 2      4.001         4.31e9     2.98e11      120.3
  off the set 1   2.001         66062      2.98e11      120.3
```

Tags. EXACT: the three-floor identity for `j`; `eps <= 3 h_1 h_2
P^(-1/2)`, so the printed hypothesis is `eps <= 1`; `-1 <= j <= 2`
under it; `j = 2 ==> u < eps`; `(D1')` does not touch the offset, so
all of this transfers to `j'`. COMPUTATIONALLY VERIFIED: `167`
instances of `j = 2`, all with `u < eps`, max ratio `0.884`; `2500`
points inside the window; the five family histograms. OBSERVATION: the
density `3 P^(-1/3)` of the exceptional set, which is equidistribution
of `{n^(3/2)}` and not proved here. HUMAN PROOF: whether the `(D1)`
sum can be split on that set without disturbing the run structure the
Stage-6 bullet depends on.

Probe: `branch_offset_extremes`, two tests. Audit
`PAPER_B_AUDIT_CONSISTENT`; `P_0` unmoved at `3.5858e13`; no
manuscript or certificate edit.

## Both constants in the Lemma 5.1(iii) derivative bound are its own split, rounded up

The last two passes narrowed the offset window and left the coefficient
`6 = 2|j'|` alone. The `2` is not sharp either, and neither is the `20`
beside it. Both follow from the exact split the lemma already prints.

**The split, differentiated.** Lemma 5.1(iii) writes

```text
  F(m) = (3/2) j (m + beta_1 + beta_2 + xi_1)^(1/2)
       + (3/4) beta_1 beta_2 (m + xi_2)^(-1/2)
```

exactly. Differentiate and compose with `X`, using `X'(n) = (3/2)
n^(1/2)` and `m ~ X = n^(3/2)`:

```text
  offset term      (3/4) j m^(-1/2) . (3/2) n^(1/2)   =  (9/8) j n^(-1/4)
  curvature term   (3/8) b_1 b_2 m^(-3/2) . (3/2) n^(1/2),  b_i ~ 3 h_i n^(1/2)
                                                      =  (81/16) h_1h_2 n^(-3/4)
```

Both are decreasing in `n`, so the supremum over the block `(P, 2P]` is
at `n = P` and the constants are `9/8 = 1.125` and `81/16 = 5.0625`.
The printed bound is `2|j| P^(-1/4) + 20 h_1h_2 P^(-3/4)`.

```text
  term        printed   from the split   slack   measured sup   samples
  offset        2         9/8  = 1.1250  1.778     1.1216         35
  curvature    20        81/16 = 5.0625  3.951     5.0455         58
```

Measured on the admissible box across `1e6` to `2e14`: the offset
model is approached to `99.7%` and the curvature model to `99.7%`,
from below, at every range. The printed bound as a whole is never
above `0.560` of itself, and the ratio is flat in `P` --- constant
slack, not an asymptotic one.

**What the slack does where the constants are certified.** The widened
theta-coefficient of Lemma 5.2(iii) is
`|q'|(2|j'| P^(-1/4) + 20 h h' P^(-3/4))`, collected as `7 P^(1/4)`.
At the true constants, with `|q'| h' <= P^(1/2)`, `h' >= 1` and
`h <= P^(1/8)`, it is
`(9/8)|j'| P^(1/4)/h' + (81/16) h P^(-1/4) <= 3.375 P^(1/4)` at the
*printed* cap `|j'| <= 3`.

```text
  what is sharpened            coefficient   row        A.5 floor   c_7 lever
  nothing (printed)            7             3.32e13    3.32e13       1.079
  window to -1 <= j <= 2       4.001         4.31e9     2.98e11     120.3
  the two derivative constants 3.376         2.85e8     2.98e11     120.3
  both                         2.251         4.35e5     2.98e11     120.3
```

Either sharpening alone retires the row; they are independent, and the
constants one needs no new argument at all --- only the split the
lemma already proves, differentiated.

## And the run bound's `|j|+1` is the right shape only where the offset term leads

The recorded question was whether `22(|j|+1) P^(3/4)` is doing work at
the top of the window. It is not, and the reason is the sign structure
of the two terms above: they are *opposite* in sign, so the run count
is not monotone in `|j|`.

```text
  P = 1e5, runs of floor(G) over the half-block, betas frozen at n_0
  h_1h_2     j=-1     j=0     j=1     j=2     minimum at
     100    10618    4867    1513    6636      j = +1
     100*   11850    4866    1512    6636      j = +1
      25     6969    1218    4535   10285      j =  0
       4     5946     195    5557   11306      j =  0
  * the same product as (10,10), at (4,25)
```

At `h_1h_2 = 4` the offset term leads, the count is near-linear in
`|j|` and minimal at `j = 0`: `|j|+1` is the right shape. At
`h_1h_2 = 100` the curvature term is comparable and cancels the offset
term near `j = +1`, where the count falls to a third of its value at
`j = 0`. Reproduced at `P = 2e4`: minimum at `j = 0` for `h_1h_2 = 4`,
at `j = +1` for `h_1h_2 = 40`.

The two regimes are not independent. `j = 2` needs
`{n^(3/2)} < Delta^2 X` and therefore `h_1h_2` of order `P^(1/2)`, so
**the top of the window can only be observed where the curvature term
is competing** --- `|j|+1` is never tested at the top with the offset
term alone. The bound holds everywhere by a factor of at least `23`,
and the row that comes closest is `j = -1`, not `j = 2`.

**Overtaken mid-pass, in the direction of the first table.** While
this was being measured the concurrent session acted on the window
finding: `WIDENED_B_CONST` is `5`, the row reads `5 P^(1/4) <=
P^(5/16)` at `1.53e11`, and it now sits *below* the `q''` row, which
is again the largest `c_7`-free one. So the second line of the ladder
is the certificate's present state and the first is history. The
derivative constants are independent of that move and still apply on
top of it: with `|j'| <= 2` and `(9/8)`, the lead is `2.25` and the
collected constant `2.251` from `7.6e9`, for a row of `4.35e5`.

Two of my tests pinned the old placement and are re-aimed at what does
not move: the row is `c^16` at the truncation `5/16`, the superseded
constant put it above every `c_7`-free row and the current one does
not, and `4` is a floor on the collected constant so `4^16 = 4.29e9`
is a floor on the row. `mode_index_row_sharpness` now reads
`WIDENED_B_CONST`, `WIDENED_B_CONST_SUPERSEDED` and
`WIDENED_B_CONST_SHARP` from the certificate rather than carrying a
constant of its own; a third test that pinned how the draft-history
family splits between body and appendices is loosened for the same
reason.

Tags. EXACT: the two constants `9/8` and `81/16` from the printed
split; the coefficient `3.375 P^(1/4)` at the printed cap and the row
`2.85e8` it gives. COMPUTATIONALLY VERIFIED: the models hold and are
approached to `99.7%` on `93` samples over four ranges; the printed
bound's worst ratio `0.560`, flat in `P`; the run-count tables at
`P = 1e5` and `P = 2e4`, `bound_holds_everywhere`, slack `>= 23`.
OBSERVATION: the minimum of the run count sits at `j = +1` once
`h_1h_2` is of order `P^(1/2)`. HUMAN PROOF: the `xi_1`, `xi_2` of the
split are only known to lie in intervals, so `9/8` and `81/16` as
*stated bounds* need the mean-value points controlled --- which the
measurements say is where they already are, but the lemma does not say
so.

Probes: `lemma_5_1_derivative_constants`, `run_bound_shape`,
`RUN_BOUND_TABLE_AT_1E5`. Three tests. Audit
`PAPER_B_AUDIT_CONSISTENT`; `P_0` unmoved at `3.5858e13`; no
manuscript or certificate edit.

## Nothing stood between the measured constants and stated ones except one carry

The question left open last pass was whether `9/8` and `81/16` can be
*stated*, given that the split's mean-value points `xi_1` in `(0, j)`
and `xi_2` in `(0, beta_1+beta_2)` are only known to lie in intervals.
They can. The points never have to be located, and the one correction
that survives is not a mean-value point at all.

**Differentiate the exact `F`, then split again.** With no
approximation,

```text
  F'(m) = (3/2)[(m+b12)^(1/2) - (m+b1)^(1/2) - (m+b2)^(1/2) + m^(1/2)]
```

and the lemma's own splitting identity, applied a second time to that
double difference of the square root, gives

```text
  F'(m) = (3/4) j (m + b1 + b2 + xi)^(-1/2) - (3/8) b1 b2 (m + xi')^(-3/2)
```

with `xi` between `0` and `j` and `xi'` in `(0, b1+b2)`. Both factors
are **decreasing** in their mean-value point, so the supremum over the
admissible interval is at the endpoint: `xi = min(0, j)` and
`xi' = 0`. Nothing is located. Checked at `100` samples over four
ranges: `|G'(n)|` is under the two endpoint terms at every one.

**The offset constant is exact.** With `G = F o X`, `X'(n) = (3/2)
n^(1/2)`, and `b_1 + b_2 >= 2` against `j >= -1`,

```text
  |offset term of G'(n)|  <=  (9/8) |j| n^(-1/4)
```

outright, with no correction. The measured ratio to it is
`1 - 1.6e-14` --- at the endpoint, as expected.

**The curvature constant keeps one correction, and it is the level-1
carry.** `beta_i = floor(Delta_{2h_i} X) + kappa_i`, so it can exceed
the smooth `3 h_i n^(1/2)` by up to `1`: the worst sample has
`3h sqrt(n) = 4058.44` and `beta = 4059`. That is the entire `2.74e-4`
by which `81/16` is missed. The honest model

```text
  beta_i  <=  3 h_i (n + 2h_i)^(1/2) + 1
```

holds at every sample (worst ratio `1 - 1.3e-8`), and gives

```text
  |curvature term| <= (81/16)(1 + 1/(3h_1 n^(1/2)))(1 + 1/(3h_2 n^(1/2))) h_1h_2 n^(-3/4)
                   <= 5.07 h_1 h_2 n^(-3/4)     for n >= 1e6, h_i >= 1
```

The correction factor is `1.00067` at `1e6` and `1 + 5e-10` at `P_0`.

```text
  term        printed   statable                slack   what it costs to state
  offset        2       9/8 = 1.1250            1.778   nothing
  curvature    20       81/16 (1+1/3sqrtP)^2    3.948   one line on the carry
                        <= 5.07 from 1e6
```

So both sharpenings are available with no new estimate: the splitting
identity the lemma already proves, applied once more, plus one line
bounding `beta_i` above. The mean-value points, which looked like the
obstacle, are the part that costs nothing.

Tags. EXACT: `F'` as a second application of the split; both factors
decreasing in their mean-value point, so the sup is at the endpoint;
`(9/8)|j| n^(-1/4)` outright given `b_1+b_2 >= 2` and `j >= -1`;
`beta_i <= 3h_i(n+2h_i)^(1/2) + 1` from the floor and the carry.
COMPUTATIONALLY VERIFIED: the chain holds at all `100` samples; the
offset ratio is `1 - 1.6e-14` and the curvature ratio `1 + 2.74e-4`;
the carry model holds everywhere; the worst `beta` excess over the
smooth value is `0.849`. OBSERVATION: `5.07` covers the curvature term
from `1e6` on, and the correction is `1 + 5e-10` at `P_0`.

Probe: `derivative_bound_certificate`, two tests. Audit
`PAPER_B_AUDIT_CONSISTENT`; `P_0` unmoved at `3.5858e13`, binding row
`5b-W<=c7S`, thirty-eight rows, `WIDENED_B_CONST = 5`. No manuscript or
certificate edit.

## One integer in Lemma 5.1(iii), and everything the last entry said about A.5

The recorded next question was whether the widened constant `7` is sharp --
whether the `2|j'|` term has a mean beating the worst case `|j'| = 3`. A mean
would not have helped: the mode index needs a supremum. The worst case is what
is wrong.

**`|j| <= 2`, not `3`, and the proof is one line.** The net offset of
Lemma 5.1(iii) is `j = beta_12 - beta_1 - beta_2` with `beta_i = b_i + kappa_i`.
Since `m = floor(X)` and `theta = X - m`,

```text
  beta_i = m(n + d_i) - m(n) = floor(Delta_i X + theta)   exactly,
```

the level-1 carry being `floor({Delta_i X} + theta)`. And
`Delta_12 X = Delta_1 X + Delta_2 X + DeltaDelta X`. So the whole offset is a
single floor:

```text
  j = floor( {Delta_1 X + theta} + {Delta_2 X + theta} - theta + DeltaDelta X ).
```

The lemma's own hypothesis `h1 h2 <= P^(1/2)/3` gives
`DeltaDelta X = 3 h1 h2 xi^(-1/2)` in `(0,1)`, and `theta` is in `[0,1)`, so the
argument lies in `(-1,3)` and `j` is in `{-1,0,1,2}`. Both ends occur.

**What the printed 3 is.** It adds the corner-floor range `[-1,2]` of
`floor(A+B+eps) - floor(A) - floor(B)` to a carry vector `kappa` in `{0,1}^3` as
though the two were independent. They are not: all three carries are
`floor(. + theta)` at one `theta`, and folding `theta` in returns a single
corner floor at `eps - theta`. `3` is the bound at `h1 h2 <= 2 P^(1/2)/3`, where
`eps < 2`. An exact census confirms the pattern -- `max j = r + 1` and
`min j = -1` at `h1 h2 <= r P^(1/2)/3` for `r = 1, 2, 3, 6`:

```text
  r = 1 (the hypothesis)   j in [-1, 2]
  r = 2                    j in [-1, 3]     <- the printed bound
  r = 3                    j in [-1, 4]
  r = 6                    j in [-1, 7]
```

An off-by-one between a lemma's hypothesis and the conclusion printed beside it.

**The formalisation proved the printed bound, which is how it survived.**
`BranchFreeze.corner_floor_range` already had the sharp `[-1,2]`;
`offset_abs_le_three` then quantified `kappa` as a free vector and added
`[-2,1]` to it. The statement is true and the constant is not attained. Added
`carry_eq_floor_shifted` and `offset_abs_le_two`, the latter being
`corner_floor_range` applied at `(A + theta, B + theta, eps - theta)` -- the
sharp result was inside the file the whole time, one substitution away. Both
ends of `{-1,0,1,2}` are witnessed by `norm_num` examples. `offset_abs_le_three`
is kept beside it because it is what the manuscript printed. `lake build` green.

**And it undoes most of the last entry.** `2|j'| <= 4` makes the widened
`theta`-coefficient `4 P^(1/4)/h' + 20 h P^(-1/4) <= 5 P^(1/4)`, so the mode
index row is `5^16 = 1.53e11` and not `7^16 = 3.32e13`:

```text
                          at |j| <= 3    at |j| <= 2 (correct)
  mode-index row          3.32e13        1.53e11
  c_7 floor               3.32e13        2.98e11   (the q'' row again)
  the whole c_7 lever     1.079          120.3
  lever spent at          c_7 = 1/228    c_7 = 1/61
  vector trade realises   nothing        8.9
  kappa table 1/16, 1/20  3.3e13 both    2.0e13, 1.5e13 (the gate)
```

Every figure A.5 printed is restored. It needed two constants to be right and
only one of them had been checked: the row was missing from A.1, and the offset
bound feeding it was loose. The two errors pointed opposite ways and the printed
conclusion sat between them.

**What survives from the last entry.** The row is real and belongs in A.1
(thirty-eight rows, thirty-three Lean theorems). It is still the site that pins
`R_0` from below, and still unsatisfiable at every `P` when `a = 1/4`, since
`5 P^(1/4) <= P^(1/4)` is as false as `7 P^(1/4) <= P^(1/4)`. A.6's four-site
minimax `a* = 0.29919` is still infeasible, now by a factor `4.5` rather than
four orders, and `3/10` still fails by `2.66`. The band moves from
`[0.3123, 0.3463]` to `[0.3016, 0.3463]`.

What inverts is the verdict on `5/16`. At `|j| <= 3` it clears the band's left
endpoint by `1.5e-4` and sits a factor `57` above the five-site minimax
`a* = 0.3218` -- the least robust admissible value, half a percent from being
the paper's threshold. At `|j| <= 2` it clears by `0.0109`, the collected
constant has `41%` of room against `P_0^(1/16) = 7.0333`, and the five-site
minimax is `a* = 0.3111` at `2.73e11`, which `5/16` misses by `1.09`. Counting
the fifth site makes `5/16` a *better* choice than A.6 rated it, not a worse
one: `1.09` against the `2.13` it costs on the four.

**The sharpening is now worth naming rather than taking.** `5` collects
`4 P^(1/4)/h'` and `20 h P^(-1/4)`, and `4.001` serves from `2.95e11`. The row
would fall to `4.31e9` and the band's left endpoint to `0.29443` -- below
`0.29919`, so at the sharp constant, and only there, A.6's four-site crossing
and its `3/10` come back inside the band. Declined: the floor is already the
`q''` row, so it would move the band and not the threshold.

**Downstream, all of it arithmetic in `2|j'|`.** The (D1) curvature ratio's
first summand `18/(uhh')` becomes `11.5/(uhh')`, so the good-shift hypothesis
`uhh' >= 72` becomes `>= 46`, the bad sets `72` become `46`, their union `144`
becomes `92`, and the Step-4 `A`-process charge `576 P^2/H_3` becomes `368`.
The second summand's `72/u` is `25/0.35` and does not move -- two distinct `72`s
in one display, and only one of them is the offset. Also: `24 P^(-5/24)` to
`16`, `69 P^(1/24-1/2)` to `46`, window count `7P^(1/4)+1` to `5P^(1/4)+1`,
boundary charge `13.5` to `8.5`, flat cost `64 P^(3/4)` to `48`, the (s2) tail
factor `7/0.6 <= 12` to `5/0.6 <= 9`, and `row_st6D1_window` from `t >= 57` to
`t >= 41` (`P >= 2.6e6`, was `9.9e6`).

Caught on the way: the first draft of the A.6 passage said the four-site
crossing misses by a factor `4500`. It is `4.5`. The test that pinned it is what
found it.

### The census was already in the repository

`decoration_budget.orbit_j_census` has been computing exact `j` at the paper's
`(H1, H2)` since it was written, and it has always returned
`live_j = [-1, 0, 1, 2]`, `max_abs_j = 2`. The test beside it asserted
`max_abs_j <= 3` and `all(abs(j) <= 3 for j in live_j)`, because that is what
the manuscript prints. So a measurement that disagreed with the printed bound
sat in a green test suite, agreeing with it.

Nothing was hidden and nothing was wrong; the assertion was simply written to
the claim rather than to the data. Tightened to `max_abs_j == 2` and
`live_j == [-1, 0, 1, 2]`, with the reason in a comment. Worth the general
note: a test that transcribes a printed bound cannot find that the bound is
loose, and this development has a lot of tests that transcribe printed bounds.

One collision found while adding the new functions: `branch_offset(n, d1, d2)`
already existed in that module, taking full shifts, and the census added here
was written against half-shifts. The new definition shadowed the old one and
`orbit_j_census` silently began doubling its shifts -- with the test still
green, since the offsets stay small. Renamed to `offset_at(n, h1, h2)`, a thin
wrapper over the original. Caught by reading the module for prior art after the
fact, which is the wrong order.

## The third number is the first two added, and the addition is where the factor goes

The manuscript now derives `22`, which settles half the question at
once: with `M = max((|j|+1) P^(-1/4), h_1h_2 P^(-3/4))` the two parts
of the `G'` bound are `<= 2M` and `<= 20M`, so `|G'| <= 22M` and the
level sets of `floor(G)` have length `>= 1/(22M)`. So `22 = 2 + 20` --
the same two constants a third time, and the sharper pair fixes this
one too. But most of the factor is not in the constants.

**The minimum is decorative.** The lemma assumes `h_1h_2 <=
P^(1/2)/3`, so

```text
  P^(3/4)/(h_1h_2)  >=  3 P^(1/4)  >  P^(1/4)  >=  P^(1/4)/(|j|+1)
```

with room to spare: the second argument is at least `3(|j|+1)` times
the first. It never binds, at any admissible `(j, h_1, h_2, P)`. The
displayed bound is `(1/22) P^(1/4)/(|j|+1)` and nothing else.

**The regrouping is what costs, not the constants.** `M` charges both
parts at the larger of the two. Using the hypothesis instead bounds the
second part directly against the first --- `b h_1h_2 P^(-3/4) <= (b/3)
P^(-1/4)` --- so `|G'| <= (a|j| + b/3) P^(-1/4) <= max(a, b/3)(|j|+1)
P^(-1/4)`, and the run-length constant is `max(a, b/3)`:

```text
  a, b            by regrouping (a+b)   by the hypothesis max(a, b/3)
  2, 20            22                    20/3  = 6.6667
  9/8, 81/16       99/16 = 6.1875        27/16 = 1.6875
```

So `22` falls to `20/3` with no change to any constant --- a factor
`3.3` for a change of route --- and to `27/16` with the sharp pair, a
factor `13.04` in all. Note the crossing: at the printed constants the
regrouping costs more than the constants do, and at the sharp pair it
is the other way round.

**And `27/16` is not slack.** Against the run counts measured at
`P = 1e5` and `P = 2e4`, `24` rows in all:

```text
  route                 constant   worst row / bound
  printed regrouping    22           0.048
  printed hypothesis    20/3         0.158
  sharp regrouping      99/16        0.170
  sharp hypothesis      27/16        0.624
```

The worst row is `h_1h_2 = 100`, `j = -1` at `P = 1e5` --- the corner
where `h_1h_2` sits at the hypothesis cap and both terms have the same
sign. `27/16` is within `60%` of what the counts do there, so it is
close to the best constant of that shape.

```text
  the three printed numbers of Lemma 5.1(iii), as they now stand
  where            printed   statable          factor
  offset cap         3        2 (erratum in)     --
  |G'| offset        2        9/8 = 1.125       1.778
  |G'| curvature    20        81/16 <= 5.07     3.948
  run length        22        27/16 = 1.6875   13.037
```

Tags. EXACT: `22 = 2 + 20` (the manuscript's own derivation); the
second argument of the minimum exceeds the first by at least
`3(|j|+1)` under the lemma's hypothesis, so it never binds; the
hypothesis route gives `max(a, b/3)` in place of `a + b`, hence `20/3`
at the printed constants and `27/16` at the sharp pair.
COMPUTATIONALLY VERIFIED: all four routes hold on `24` measured rows;
worst ratios `0.048`, `0.158`, `0.170`, `0.624`. OBSERVATION: the
worst row is the corner `h_1h_2 = P^(1/2)/3`, `j = -1`, where the two
terms of `G'` share a sign; the cancelling corner `j = +1` is `8%` of
the same bound.

Probe: `run_length_constant`, two tests. Audit
`PAPER_B_AUDIT_CONSISTENT`; `P_0` unmoved at `3.5858e13`. No
manuscript or certificate edit.

### Two more, both found by running the checks rather than by reading

**`BranchFreeze` is now a cited module, and the barrel did not import it.** The
manuscript had referenced that file by path for as long as Lemma 5.1(iii) has
been written, but never named a declaration inside it, so the trust-boundary
audit -- which resolves backticked declaration names -- counted five modules.
Naming `carry_eq_floor_shifted` and `offset_abs_le_two` in the erratum makes it
six. `Problems.JugglerParityPaper` now imports it directly, the table says six,
and `lake build Problems.JugglerParityPaper` is green at 3101 jobs. It was
already reachable transitively and is still disjoint from Paper A's barrel, so
nothing about the boundary changes -- only what the table admits to.

**And a false green.** The full-suite run was issued as
`pytest tests/ -q 2>&1 | tail -10`, whose exit code is `tail`'s. It reported
`0` while two trust-boundary tests were failing in the captured output. This is
the second time in this audit that a pipeline has hidden a non-zero pytest exit
(the first was `--timeout` on an uninstalled plugin). Re-run with the output
redirected and the exit code read directly.

## Neither candidate was a maximum in disguise; the commoner loss is charging one point twice

The question was whether Stage 3(s2)'s `2.25` or the widened `5` hide
a maximum the way `22 = 2 + 20` does. Neither does.

**`2.25` is already sharp.** It is not a sum at all:
`B(nu) = (3u/2) Delta(nu^(3/4)) = (9/4) u h xi^(-1/4)`, one mean value,
and the printed range `(1.89, 2.25] u h P^(-1/4)` is that single term
at the two ends of the block --- `2.25 = 9/4` at `xi = P` and
`1.89 = (9/4) 2^(-1/4)` at `xi = 2P`. Both ends are attained. Nothing
to sharpen.

**The widened `5` is a genuine sum**, of a lead `2|j'| = 4` and a term
of lower order, `20 h P^(-1/4) <= 20 P^(-1/8)`. The two parameters `h`
and `h'` are independent, so both parts can sit at their caps at once;
the `+1` is rounding a vanishing term, worth `4.001` from `2.95e11`,
which the certificate already records as `WIDENED_B_CONST_SHARP`.

**But the search turned up the sibling pathology, and it is commoner.**
The fourth displayed estimate of Lemma 5.1(iii),
`|G''| <= 2|j| P^(-5/4) + 25 h_1h_2 P^(-7/4)`, is already known not to
be term by term: with `n = s^4` the two `beta_1beta_2` contributions to
`G'' = F''(X) X'^2 + F'(X) X''` are `81/64` and `-9/32`, and
`81/64 - 9/32 = 63/64`; the same for the `j` terms,
`-27/32 + 9/16 = -9/32`. The manuscript keeps that cancellation and
then puts `beta_1 beta_2 <= 19 h_1h_2 P`, reaching `(63/64)(19) = 18.7`.

That `19` is `beta` at the **top** of the block --- `beta_i <= 3 sqrt2
h_i P^(1/2) + 1`, attained at `nu = 2P` --- multiplying an `n^(-11/4)`
charged at the **bottom**, `n = P`. They are the same point. Charged
there, `beta_i ~ 3 h_i n^(1/2)` and `beta_1beta_2 n^(-11/4) ~ 9 h_1h_2
n^(-7/4)`, so the coefficient is `(63/64)(9) = 567/64 = 8.859` and the
`j` coefficient is `9/32 = 0.28125`.

```text
  |G''| / [ (9/32)|j| n^(-5/4) + (567/64) h_1h_2 n^(-7/4) ]   worst 1.00013
  |G''| / [ 2|j| n^(-5/4) + 25 h_1h_2 n^(-7/4) ]              worst 0.35442
```

`1.00013` is the same level-1 carry excess `derivative_bound_certificate`
isolates for `G'`; the model is otherwise exact. The printed pair is
loose by `7.111` on the offset and `2.822` on the curvature, and of the
latter a factor `19/9 = 2.11` is the two block ends alone.

**The inventory.** Seven collected constants, with what each is made of:

```text
  where                          printed   true     slack  loss
  Lem 5.1(iii) |G'| offset          2      9/8       1.78  rounding
  Lem 5.1(iii) |G'| curvature      20      81/16     3.95  block ends apart
  Lem 5.1(iii) |G''| offset         2      9/32      7.11  cancellation dropped
  Lem 5.1(iii) |G''| curvature     25      567/64    2.82  block ends apart
  Lem 5.1(iii) run length          22      27/16    13.04  max in disguise
  Thm 4.1 St.3(s2) |B|              2.25   9/4       1.00  none
  Lem 5.2(iii) widened              5      4.001     1.25  rounding a vanishing term
```

One row is already sharp, one is a maximum in disguise, two are the
block ends apart, and two are rounding. The pattern is not the `max`
regrouping specifically --- it is charging quantities that live at one
point at two separate worst points, of which the `max` is one form and
the block ends another.

Tags. EXACT: `B(nu) = (9/4) u h xi^(-1/4)` is a single mean value and
`(1.89, 2.25]` is its range over the block, so `2.25` is sharp; the
widened `5` is a lead plus a vanishing term with `h`, `h'`
independent; the `G''` coefficients `9/32` and `(63/64)(9) = 567/64`
from the `n = s^4` regrouping with `beta` and `n` at the same point.
COMPUTATIONALLY VERIFIED: `|G''|` against the model is at most
`1.00013` on `64` samples over four ranges and against the printed pair
at most `0.3544`; `beta_1beta_2` at the block top is `19 h_1h_2 P` and
at the point `9 h_1h_2 n`, a factor `19/9`. OBSERVATION: of seven
collected constants, `block ends apart` is the commonest loss.

Probes: `second_derivative_constants`, `collected_constant_inventory`,
`COLLECTED_CONSTANT_INVENTORY`. Two tests. Audit
`PAPER_B_AUDIT_CONSISTENT`; `P_0` unmoved at `3.5858e13`. No manuscript
or certificate edit.

## The interval exists for convenience: the decomposition freezes beta exactly where `n` cannot move

Every "block ends apart" row of the inventory traces to
`beta_i in [3 h_i P^(1/2) - 1, 3 sqrt2 h_i P^(1/2) + 1]` --- printed as
`4.3 h_i P^(1/2) + 1` in the `j = 0` band. The top of that interval is
`beta` at `nu = 2P`, and it multiplies a negative power of `n` charged
at `nu = P`. The question was whether anything forces the two apart.

**Nothing does, and the run structure is why.** `b_i = floor(Delta_{2h_i}
X)` advances by one exactly when `3 h_i n^(1/2)` does, so its runs have
length `2 n^(1/2)/(3 h_i)`:

```text
   P     h   runs   mean length   2 sqrt(n)/(3h)   ratio
  1e6    1     17       668.5         666.7        1.0027
  1e6    2     35       334.2         333.3        1.0027
  1e8    1      1      6666.0        6666.7        0.9999
  1e8    3      5      2221.6        2222.2        0.9997
```

Across such a run `n` moves by a *relative* `2/(3 h_i n^(1/2))`, so
`beta_i / (3 h_i n^(1/2))` never leaves `1 + O(1/(h_i n^(1/2)))`:
measured inside `[0.999678, 1.000323]` at `P = 1e6` and inside
`[0.999967, 1.000033]` at `1e8`. The branch decomposition freezes
`beta` precisely where `n` cannot move enough to matter, so the
pointwise value is available wherever the lemma is used.

**And nothing is lost by using it.** The estimates are decreasing in
`n`, so any block-uniform statement follows from the pointwise one at
`n = P`, with the pointwise constants. The interval is not a weaker
hypothesis --- it is the same fact stated over a range where one of the
factors has already moved.

**A third instance, which the inventory did not have.** On a zero-offset
branch of the mode-dominant band the anchor's `theta`-coefficient is
`B = -(9/32) k beta_1 beta_2 nu^(-9/8)`, and the manuscript reads it
off the interval: `|B| <= 5.3 k h_1h_2 P^(-1/8)`, opened to `6`.
Pointwise it is `81/32 = 2.5313`, measured at `2.5304` over `90`
samples --- `99.97%` of the model. The factor is `(4.3/3)^2 = 2.054`
from the interval, plus the two `+1`s and the opening.

Its one consequence: `5b-j0-window` reads `P^(1/2) >= 8(1+|B|)`, so the
row falls from `3136` to `798`. Both are twelve orders under `P_0`, and
the structural point the passage makes --- that the sawtooth is of
constant size and not sub-unit --- survives at `2.53`, which is still
above `1`. Nothing else moves.

```text
  the inventory, now eight rows
  where                              printed   true      slack  loss
  Lem 5.1(iii) |G'| offset              2       9/8       1.78  rounding
  Lem 5.1(iii) |G'| curvature          20       81/16     3.95  block ends apart
  Lem 5.1(iii) |G''| offset             2       9/32      7.11  cancellation dropped
  Lem 5.1(iii) |G''| curvature         25       567/64    2.82  block ends apart
  Lem 5.1(iii) run length              22       27/16    13.04  max in disguise
  Thm 4.1 St.3(s2) |B|                  2.25    9/4       1.00  none
  Lem 5.2(iii) widened                  5       4.001     1.25  rounding a vanishing term
  Thm 5.3 mode-dominant j=0 anchor      5.3     81/32     2.09  block ends apart
```

Tags. EXACT: `b_i` advances with `3 h_i n^(1/2)`, so its runs have
length `2 n^(1/2)/(3 h_i)` and `n` moves by a relative
`2/(3 h_i n^(1/2))` across one; the estimates are decreasing in `n`, so
the pointwise statement implies the block-uniform one at `n = P`;
`|B| = (9/32) k beta_1beta_2 nu^(-9/8)` is `81/32` pointwise.
COMPUTATIONALLY VERIFIED: the four run-length rows above;
`beta_i/(3 h_i n^(1/2))` inside `[0.999678, 1.000323]`; the `j = 0`
anchor measured at `2.5304` against `81/32 = 2.5313`; the window row
`3136 -> 798`. OBSERVATION: three of the eight inventory rows are now
this one loss, and all three would go together.

Probe: `beta_locality`, two tests; the inventory gains a row. Audit
`PAPER_B_AUDIT_CONSISTENT`; `P_0` unmoved at `3.5858e13`. No manuscript
or certificate edit.

## What the machine check was checking, and where the offset pattern recurs

The last entry ended by asking how many Lean theorems in this development take
a hypothesis vector the manuscript supplies as a function. The scan found one
thing of that kind and one worse thing of another.

**The worse thing first: the Lean interpolant chain proved the superseded
constants.** Lemma 5.2b's erratum lists its own consequences --- the (C5) cap
`186 -> 300`, step (ii)'s `0.567 -> 0.907`, the sum `52.9 -> 85.3`, and `E`'s
`106 -> 171`. `PaperBAssembly.lean` proved the left-hand column of every one:

```text
  interpolant_step_i           u <= 186 k h2 P^(1/8)   ->  52.32 k(h1+h2) P^(-9/8)
  interpolant_step_ii_constant (135/1024) * 4.3 <= 0.57
  interpolant_assembly         52.32 + 0.57 = 52.89    ->  106 P^(-25/24)
  interpolant_gain             2 < 219/106
```

and the manuscript, three lines under the corrected display of (i) and (ii),
said "Steps (i)-(iii) and the assembly are machine-checked in
`PaperBAssembly.lean` (`interpolant_step_i`, `interpolant_step_ii_constant`,
`interpolant_assembly`)". That sentence was true of a statement the erratum in
the same lemma had already replaced. It is the exact failure the trust table of
Section 1.1 exists to prevent, one section away from the table.

Regenerated on the corrected anchor `27/128`: cap `300` (which is
`60 * 4.2/0.84`, the band condition at the corrected `lambda_0` ceiling),
`(9/32)*300 = 84.375` printed `84.38`, `(27/128)*4.3 = 0.9070` printed `0.91`,
`(84.38 + 0.91) * 2 = 170.58 <= 170.6`. `interpolant_gain` now records
`1.28 < 219/170.6 < 1.284`, which is the factor A.5 claims, beside the
superseded `2 < 219/106`. The pre-correction chain is retained under
`_precorrection` names, as `step5b_c7_printed` retains `c_7 = 1/288`, so that a
reader checking the erratum's list finds both ends of it in Lean.
`lake build Problems.Juggler.PaperBAssembly` green at 3080 jobs.

`P_0` and `P_1` do not move: `p0_certificate.interpolant_error` was already
`170.6 P^(-25/24) + 0.11 P^(-5/6)`. What was wrong was the corroboration.
Two files were regenerated after the Lemma 5.2b erratum -- the threshold
certificate and the probe -- and this one was not, which is the sort of thing
that survives precisely because everything stays green.

**And the offset pattern does recur, three times, harmlessly.** Measured
exactly over `1 <= h1, h2 <= 7` (`decoration_budget.beta_inventory_attained`):

```text
  quantity                                         printed        attained
  (3/4) b1 b2 (m+xi2)^(-1/2) / (h1 h2 P^(1/4))     [1.4, 15]      [27/4, (27/4)2^(1/4)]
                                                                  = [6.750, 8.027]
  beta-part of |G'|  / (h1 h2 P^(-3/4))            20             81/16  = 5.0625
  beta-part of |G''| / (h1 h2 P^(-7/4))            25             567/64 = 8.8594
```

Same arithmetic in all three: `b1 b2 ~ 9 h1 h2 n` and the accompanying power of
`n` move together, and the printed forms take one at each end of the block. The
printed interval in the first row is `13.6` wide where the attained one is
`1.28`; the two derivative constants are `3.95` and `2.82` times what they
bound.

**And one place it looked like it should recur and does not.**
`beta_product_bound` hypothesises `beta_i <= 4.25 h_i q + 1` separately and
concludes `beta1 beta2 <= 19 h1 h2 q^2`. That is not an over-quantification:
both factors are extremal at the *same* `n = 2P`, `beta1 beta2/(h1 h2 P)`
attains `18 = (3 sqrt 2)^2` exactly, and `4.25^2 = 18.0625` is the whole of the
loss. Separate quantification costs nothing when the extremes coincide, which
is the distinction the offset erratum turns on and is worth having on record in
the affirmative as well.

Not sharpened, and costed rather than waved at. The `20` reaches the widened
`theta`-coefficient only through the lower-order `20 h P^(-1/4)`: at `81/16` the
collected constant `4 + delta` becomes valid from `7.6e9` instead of `2.95e11`,
and the collected constant itself is unchanged. The `25` reaches only
`25/0.35 <= 71.5`, whose certificate row moves from `8.2e4` to `1.0e4`. Both
are eight orders under `P_0`. A rigorous sharpening would also have to carry
the `O(1)` corrections in `beta_i = floor(Delta_i X + theta)` that the printed
constants currently absorb.

### A commit that was not the tree it was tested on

`520ab77b` shipped `JugglerParityPaper.lean` importing `BranchFreeze` --- which
makes the trust audit resolve six cited modules --- alongside
`test_trust_boundary.py` still asserting exactly five. Its tree therefore fails
`test_module_list_matches_what_the_citations_resolve_to` and
`test_paper_b_root_imports_exactly_its_own_modules` on a clean checkout, and
the commit message says the full suite is green on pytest's own exit code.

The suite *was* green, in the working tree. The tree that was committed was a
different one, because the file was edited and then left out of an explicit
`git add` list. The list is explicit on purpose here --- a second session is
committing into the same working tree, and blanket `git add -A` would sweep up
its files --- so the failure mode is structural rather than careless: every
file touched has to be enumerated, and one was not.

Fixed by including it in the next commit. Recorded because "the suite is green"
means nothing about a commit unless the two are the same tree, and nothing in
this workflow checks that they are.

## (C1) carries nine bounds, all of them at a corner the argument never reaches

The question was whether `(C1)`, `k h_1h_2 <= P^(1/8)`, is at the
`j = 0` band for that one bound. It is not: it is invoked at nine
displayed sites. What they share is more interesting than the count.

**Every one is applied at `(C1)`'s own corner, and the corner is
unreachable.** Theorem 6.1 enters with `k <= 2 P^(1/96)` and Theorem
5.3 takes `H_1 = P^(1/48)`, `H_2 = P^(1/24)`, so the load is
`2 P^(7/96)` against a cap of `P^(12/96)`. The manuscript records that
once, in the closing slack table --- "`7/96` of `12/96`" --- and does
not propagate it. Each of the nine constants is therefore over-charged
by `2 P^(-5/96)`, which is `1/2.54` at `P_0`.

```text
  line   printed form                 exponent   at the load   kind
  2532   8.6 k h1h2 P^(1/8)/(uh)       1/4        19/96        danger sizing
  2920   18 k h1h2 P^(-7/8)/u         -3/4       -77/96        dominated
  2938   34.3 k h1h2 P^(1/8)           1/4        19/96        regime boundary
  3663   2.7 k h1h2 P^(1/8)            1/4        19/96        error term
  3684   30 k h1h2 P^(5/8)             3/4        67/96        threshold row
  3715   1.85 k h1h2 P^(1/8)           1/4        19/96        mode cap
  3958   5.3 k h1h2 P^(-1/8)           0          -5/96        threshold row
  4018   600 k h1h2 P^(-5/8)          -1/2       -53/96        dominated
  4469   80 k h1h2 P^(-1/2)           -3/8       -41/96        dominated
```

(Line numbers as of this pass; eight of the nine still match, the
manuscript being edited alongside. The probe reports the drift instead
of failing on it.)

**What the slack is worth is not uniform.** Three sites are dominated
with room to spare and nothing changes. Two are certificate rows:
`st3a-flat`, which already holds at every `P`, and `5b-j0-window`,
which moves from `3136` to `798`. Neither is within twelve orders of
`P_0`, so nothing moves the threshold.

**One site has structural content.** Regime B --- the hard case, where
neither the second- nor the third-derivative test is available and
Lemmas 3.8--3.9 do not apply --- is declared as
`uh < 34.3 k h_1h_2 P^(1/8) <= 34.3 P^(1/4)`. At the load it is
`68.6 P^(19/96)`. The hard regime is `2.54` times narrower at `P_0`
than the paper states it to be, which is a strengthening at no cost.

**And one site would be *weakened* by sharpening.** At line 2532 `(C1)`
is used to bound how large an undifferenced `phi''` could be ---
`8.6 k h_1h_2 P^(1/8)/(uh)` reaching `8.6 P^(1/4)` at `uh = 1` --- in
order to justify why the budget carried must be the differenced one. A
smaller bound there is a smaller danger and a weaker motivation, not a
stronger theorem. Slack is not uniformly worth removing, and this is
the first site in the inventory where removing it would cost
something.

So the answer is no twice: `(C1)` is not there for one bound, and its
slack is not one quantity with one value.

Tags. EXACT: nine invocation sites; the load `2 P^(7/96)` against the
cap `P^(12/96)`, so the room is `P^(5/96)/2` at every one of them;
Regime B's boundary is `68.6 P^(19/96)` at the load against the printed
`34.3 P^(1/4)`. COMPUTATIONALLY VERIFIED: the over-charge is `2.5406`
at `P_0`, identical at all nine sites since all nine carry the same
product; `st3a-flat` holds at every `P` and `5b-j0-window` moves
`3136 -> 798`; no certificate row moves `P_0`. OBSERVATION: eight of
the nine recorded line numbers still match the working copy.

Probe: `c1_invocation_inventory`, `C1_INVOCATIONS`. Two tests. Audit
`PAPER_B_AUDIT_CONSISTENT`; `P_0` unmoved at `3.5858e13`. No manuscript
or certificate edit.

## The other half of the pairing table

`p0_certificate.LEAN_ROWS` pairs each of the thirty-eight threshold rows with its theorem, its
substitution and a rational witness. Nothing paired the rest, and the last entry recorded what
that cost: three theorems in `PaperBAssembly` proved Lemma 5.2b's superseded chain while the
manuscript displayed the corrected one, and the only reason it survived is that no check
compared a Lean numeral with the manuscript's value for it. `tools/lean_numeral_audit.py` is
the missing half.

**It pairs by value, not by string, and that distinction is the whole point.** A check of the
form "does this numeral occur in the manuscript" would have passed the interpolant chain:
`186` and `106` both occur there, inside the erratum's own list of what replaced them. So each
numeral in a non-certificate Paper B statement is classified as

* **paired** -- it implements a named quantity, with a predicate tying it to
  `p0_certificate`'s constants or to exact rational arithmetic; or
* **structural** -- it is a coefficient of the statement's own algebra, a matrix entry or an
  exponent, with nothing outside Lean to compare it against;

and anything else is **unclassified**, which fails the suite.

```text
  BranchFreeze, MonomialSplitting, PaperBAssembly
  317 numerals   62 paired   255 structural   0 unclassified   0 failing
```

**Zero failing is the finding.** Every other constant in those three modules agrees with the
value this paper carries. The interpolant chain was the only staleness, not the first of
several -- which was the open question and is now answered in the negative.

**The guard is tested against the bug it was built for.** One test doctors
`interpolant_step_i`'s statement back to `186` and `52.32` in memory and asserts the audit
reports both as unclassified. A guard that has never been shown to fire is a guard one is
guessing about.

**Two constants that share a value are named apart.** Theorem 4.1's Stage-4 curvature is
`0.35` and so was the pre-correction `lambda_0` floor. Conflating them cost an afternoon
earlier in this audit, so the table names the Stage-4 one on its own rather than reaching for
`ANCHOR_CONSTANTS_PRECORRECTION[0]`, and a test asserts that every `0.35` in the table is
attributed to Theorem 4.1.

One judgement worth stating. Nineteen theorems are exact identities or pure geometry --
Lemma 4.3's closed form, the carry identity, the sublevel diameter, the `G''` cancellation --
and their numerals are classified structural by a per-theorem wildcard rather than integer by
integer. That is weaker: a new empirical constant inside one of those statements would be
absorbed. It is recorded as a wildcard *per theorem*, so a new theorem is unclassified until
someone decides which list it belongs on, and the nineteen are named.

## (C2) is invoked nowhere below because both invocations are above

The standing constraints record `(C2) h_1h_2 <= P^(1/2)/3` and add that
it "is in fact invoked nowhere below; it is recorded because the
differencing steps are easier to read against a named bound on the
shift product". The literal claim survives inspection. The reason does
not.

**Four occurrences, and the two that matter precede the statement.**

```text
  line   form                     where
  1853   h_1h_2 <= P^(1/2)/3      Lemma 5.1(iii)'s hypothesis: "-1 <= j <= 2 ...
                                  for h_1h_2 <= P^(1/2)/3, both ends occurring"
  1970   3 h_1h_2 P^(-1/2)        |Delta Delta X| <= 4 h_1h_2 sup|X''| < 1
  2137   h_1h_2 <= P^(1/2)/3      the statement of (C2)
  3904   3 h_1h_2 P^(-1/2)        the (D3) content ratio, <= P^(-1/4)
```

The first two are the same inequality as `(C2)`, one of them
rearranged, and both are the step the offset window is read off. The
fourth is below the statement but is not a `(C2)` invocation: it wants
`3 h_1h_2 P^(-1/2) <= P^(-1/4)`, i.e. `h_1h_2 <= P^(1/4)/3`, which
`(C2)` cannot deliver. It follows from `(C3)` and `(C4)`, which give
`h_1h_2 <= P^(1/12)` and hence the ratio from `P >= 729`. So "nowhere
below" is correct as printed.

**What the sentence gets wrong is the standing.** `(C2)` is not a
reading convenience. It is the hypothesis of Lemma 5.1(iii)'s offset
bound, and the offset carries the widened constant of Lemma 5.2(iii),
the run-length constant, and the `st6D1-modeindex` certificate row.
Everything this ledger has recorded about those three rests on the
inequality that the only sentence about `(C2)` says is never used.

The mismatch is one of naming, not of mathematics: the paper's most
load-bearing shift-product hypothesis is stated twice before it is
given a name, and the name is then introduced with a note that it does
nothing.

**How much room the hypothesis has where it is used.**
`eps = 3 h_1h_2 P^(-1/2)` is at most `3 P^(-5/12) = 6.8e-6` under
`(C3)` and `(C4)`, and `3 P^(-7/16) = 3.5e-6` under Theorem 5.3's own
caps `H_1 = P^(1/48)`, `H_2 = P^(1/24)`. `(C2)` itself follows from the
caps once `P >= 3^(12/5) = 14`. That room is why `j = 2`, which needs
`{n^(3/2)} < eps`, is invisible inside the box even though the window
`-1 <= j <= 2` is sharp at both ends outside it.

Tags. EXACT: the four occurrences and their positions relative to the
statement; the occurrence below needs `h_1h_2 <= P^(1/4)/3`, which
`(C2)` cannot give, so the literal claim holds; `(C2)` is Lemma
5.1(iii)'s hypothesis verbatim. COMPUTATIONALLY VERIFIED: the scan
locates all four by pattern rather than line, so it survives the
concurrent edits; `eps <= 6.751e-6` under `(C3)`+`(C4)` and
`3.524e-6` under the Theorem 5.3 caps; `(C2)` from the caps at
`P >= 13.97`; the `(D3)` ratio from `P >= 729`. OBSERVATION: the only
sentence in the paper about `(C2)` says it does nothing, and it is the
hypothesis three of this ledger's findings depend on.

Probe: `c2_occurrence_audit`. Two tests. Audit
`PAPER_B_AUDIT_CONSISTENT`; `P_0` unmoved at `3.5858e13`. No manuscript
or certificate edit.

## The remark that outlived its own truth

The last entry asked whether "the manuscript does not state this" should be a third
classification in the numeral table, and named `Gsecond_beta_cancellation`'s `63/64` as the
case, on the strength of `BranchFreeze`'s header: "**One thing this file records that the
manuscript does not.**"

The header is wrong. The manuscript records the whole computation at Lemma 5.1(iii) --- the
two contributions `81/64` and `-9/32`, their sum `63/64`, `63/64 * 19 = 18.7 <= 25`, the naive
`99/64 * 19 = 29.4 > 25`, the phrase "of *opposite sign*" --- and cites
`Gsecond_beta_cancellation` and `Gsecond_naive_bound_fails` by name. The Lean file found the
cancellation, the manuscript adopted it, and the header went on claiming sole custody.

(The first search for it here used `grep -F` with `@|` alternation, which `-F` takes
literally, and reported zero hits in the manuscript. The premise survived one bad grep. It was
the ledger's own earlier entry --- "Now recorded in the manuscript and in Lean" --- that
contradicted it and forced the second look.)

**So the answer to the question is no, and the interesting class is the opposite one.** Not "a
Lean constant the manuscript does not state", but "a Lean *sentence* about the manuscript that
the manuscript has since made false". Three of them in `BranchFreeze`, all created by the file
being right:

```text
  claim                                              why it went stale
  "one thing this file records that the             the manuscript adopted the whole
   manuscript does not"                             computation and cites both theorems
  "the manuscript's (3 sqrt 2)^2 = 18 becomes 19"   the manuscript now prints 19 itself
  the naive coefficient is "27.8"                   that is 99/64 * 18; the file and the
                                                    manuscript both use 19, giving 29.4
```

The third is an internal inconsistency rather than a claim about the manuscript: the header
and the docstring of the theorem twelve lines below it gave two different values for the same
quantity, `27.8` and `29.3`, against the manuscript's `29.4`. All three corrected;
`lake build Problems.Juggler.BranchFreeze` green.

**And a checker, because this is the third staleness of the same species in three entries.**
`tools/lean_numeral_audit.py` now carries `MANUSCRIPT_CLAIMS`: nine rows, each an anchor
sentence that must still be in the Lean file and a predicate that must hold on the manuscript.
The anchor is the point --- rewording a sentence retires its row loudly instead of leaving a
predicate quietly guarding text that no longer exists. A test asserts every predicate is false
against an empty manuscript, so none of them is vacuous, and another doctors the manuscript
back to its pre-adoption state and asserts the two `BranchFreeze` rows fire.

```text
  317 numerals   62 paired   255 structural   0 unclassified   0 failing
    9 prose claims about the manuscript                        0 stale
```

The pattern across the last three entries is worth naming. A Lean file and a manuscript drift
apart in three ways: the constant moves and Lean keeps the old one (the interpolant chain);
the constant is right and nothing says so (the numeral table's gap); and the *paper* moves to
match Lean and Lean keeps describing the paper it corrected. The third is the one no amount of
care in the manuscript can catch, because the error is not in the manuscript.

## The uniformity clause is unexercised above `k = 2`, and at `P_0` there is nothing there to exercise

`kernel_k_uniformity` already records that no evaluation in this audit
sits inside `(C3)` above `k = 1`, and that the first that could is
`P = 2^24`, where `KERNEL_AT_C3_THRESHOLD` has `k = 1` and `2`. The
question was whether anything exercises the clause above `k = 2`. Nothing
does. But the reason is not that the audit is short.

**At the threshold the operating range is `{1, 2}`.**

```text
  k    least P under (C3) = k^24    least P under Thm 6.1 = (k/2)^96
  2    1.678e7                      1
  3    2.824e11                     8.031e16
  4    2.815e14                     7.923e28
  5    5.960e16                     1.593e38
```

At `P_0 = 3.5858e13` the two caps read `P^(1/24) = 3.6709` and
`2P^(1/96) = 2.7684`. So `(C3)` admits `k in {1, 2, 3}` and Theorem 6.1
admits `k in {1, 2}` --- exactly the two the audit has evaluated. The
clause first has to carry an integer the audit has not seen at
`(3/2)^96 = 8.03e16`, which is `2240` times `P_0`.

**Inside the lemmas the third value is real, and 4.2 orders away.**
`k = 3` enters `(C3)` at `3^24 = 2.82e11`, well below `P_0`, so the
uniformity clause does have work to do there --- just not at any point
where Theorem 6.1 applies it. Measuring it is out of reach: at the rate
of `KERNEL_AT_C3_THRESHOLD` (`8388608` terms in `688` s), a kernel sum
at `3^24` is `1.41e11` odd terms, about `134` days.

So the honest statement of the blindness is narrower than the one on
record. Not "the uniformity in `k` has never been exercised" full stop,
but: at the operating point there is nothing above `k = 2` to exercise,
the audit covers that range exactly, and the lemma's own wider range
first differs at `2.82e11` and cannot be evaluated there.

Tags. EXACT: least `P` admitting `k` is `k^24` under `(C3)` and
`(k/2)^96` under Theorem 6.1; at `P_0` the caps are `3.6709` and
`2.7684`, so the integer ranges are `{1,2,3}` and `{1,2}`; the first
`P` at which the operating range gains a value is `(3/2)^96 = 8.03e16`.
COMPUTATIONALLY VERIFIED: `2240 = 8.03e16 / P_0`; a `k = 3` kernel at
`3^24` is `1.41e11` terms and `134` days at the measured rate, `4.23`
orders beyond `KERNEL_AT_C3_THRESHOLD`. OBSERVATION: the audit's reach
in `k` coincides with the operating range at the threshold, which is
not something the audit was designed for.

Probe: `k_range_at_the_operating_point`. Two tests. Audit
`PAPER_B_AUDIT_CONSISTENT`; `P_0` unmoved at `3.5858e13`. No manuscript
or certificate edit.

## `h_1` is not pinned the way `k` is, and the claim that it was is mine

`k` is pinned at the operating point by Theorem 6.1's own cap:
`2 P^(1/96)` is `2.7684` at `P_0` and does not reach `3` until
`(3/2)^96 = 8.03e16`, a window of `2240` above the threshold. The first
shift is nothing like that.

**`h_1 = 1` holds on `[P_0, 2^48)`, and that is a window of `7.85`.**
Both `(C4)` and Theorem 5.3 cap `h_1` at `P^(1/48)`, so the second value
arrives at `2^48 = 2.815e14`. That is above `P_0 = 3.586e13`, so `h_1`
is `1` *at* the threshold --- but the claimed regime is `P >= P_0` and
does not stop there.

`parameter_cap_reach` said `h_1 = 1` "holds throughout the regime the
paper's own estimates are claimed in". That is my sentence and it is
wrong. Corrected, and the corrected fact is now a returned field
(`window_above_P0`) rather than prose, so it is checked rather than
asserted:

```text
  cap                       least P for a second value   window above P_0
  k    (C3)                 1.678e7                      --  (below P_0)
  h_1  (C4), outer shift    2.815e14                     7.85
  h_2  (C4), inner shift    1.678e7                      --  (below P_0)
```

**And the audit is not blind to it.** What each range actually draws,
rather than what the caps permit:

```text
    P       H_1   H_2    h_1 drawn      h_2 drawn
   1e4       1     1     [1]            [1]
   1e6       1     1     [1]            [1]
   1e8       1     2     [1]            [1, 2]
  1e10       1     2     [1]            [1, 2]
  1e12       1     3     [1]            [1, 2, 3]
  1e14       1     3     [1]            [1, 2, 3]
  1e15       2     4     [1, 2]         [1, 2, 3, 4]
  1e16       2     4     [1, 2]         [1, 2, 3, 4]
```

So `h_1 = 2` is exercised at the top two census ranges, and `h_2`
reaches `3` from `1e12` and `4` from `1e15`. At `P_0` itself the
admissible values are `h_1 = 1` and `h_2 in {1, 2, 3}`.

The contrast is the finding: the parameter the audit cannot exercise
inside its hypothesis is `k`, and the reason is that its operating cap
holds it at `{1, 2}` for `2240` times `P_0`. `h_1` is held at `1` for
`7.85` times `P_0` and then moves, and the audit crosses that point
twice.

Tags. EXACT: `h_1`'s second value is at `2^48 = 2.815e14`, a factor
`7.850` above `P_0`; at `P_0` the admissible sets are `h_1 = 1`,
`h_2 in {1,2,3}`, `k in {1,2}` under Theorem 6.1; `k`'s window above
`P_0` is `2240`, `285` times `h_1`'s. COMPUTATIONALLY VERIFIED: the
eight-range draw table above; `h_1 = 2` drawn at `1e15` and `1e16` and
nowhere below. OBSERVATION: the corrected claim is now a field of
`parameter_cap_reach` and a test, not a docstring sentence.

Probe: `shift_reach_in_the_audit`; `parameter_cap_reach` gains
`window_above_P0` and loses an overclaim. Two tests. Audit
`PAPER_B_AUDIT_CONSISTENT`; `P_0` unmoved at `3.5858e13`. No manuscript
or certificate edit.

## The probe citations, which nothing had ever checked

The manuscript names probe functions in running text and says what they return.
`trust_boundary` resolves *unqualified* backticked identifiers against Lean and skips
qualified ones, so `decoration_budget.branch_offset_ladder` and its four companions had no
check at all: not that the function exists, not that it still carries that name, and not that
the figures quoted beside it are what it gives.

All five resolve, which is the first thing worth recording, since one of them
(`decoration_budget`) had a function renamed underneath the manuscript two entries ago when
`branch_offset` was found to shadow an existing definition. Two of the five *claims* were
wrong, both mine:

**The measured exponent was quoted at the wrong setting.** The manuscript read "the instrument
reads `0.500 +- 0.043` on data whose exponent is exactly `1/2`". The instrument is seeded and
deterministic, and at its default `trials = 200` it reads `0.4973 +- 0.0430`. `0.500` is what
it gives at `trials = 120` -- the setting the *test* beside it uses, not the function's own.
Nothing was wrong with the measurement; the sentence quoted a number the reader running the
cited function would not see. Now `0.497 +- 0.043`, with the setting named.

**A census was called exact when only half of it is.** "Measured exactly over
`1 <= h1, h2 <= 7` (`decoration_budget.beta_inventory_attained`, integer arithmetic
throughout)". The `beta_i` and their products are exact integers through
`floor(n^(3/2)) = isqrt(n^3)`; the ratios reported beside them divide by `m^(1/2)`,
`n^(-7/4)` and `p^(1/4)` in floating point. The neighbouring citation of
`branch_offset_ladder` says "integer arithmetic through `floor(n^(3/2))`" and *is* exact --
that one only ever compares integers. The two sentences were written a paragraph apart and
only one of them was true.

**One discrepancy is not mine and is left for its owner.** The comment above `BLOCK_COUNTS` in
`paper_b_audit.py` says the fitted estimator "returns `0.4965 +- 0.047`". At the current block
counts it returns `0.4973 +- 0.0430`, and at the older `(256, 64, 16, 4, 1)` the same fit
gives `0.4970 +- 0.0429`; neither reproduces the `0.047`. No test pins it -- the calibration
test asserts only `|bias| < 0.03` and `sd < 0.07`, both of which hold. Reported, not edited;
that module is the other session's.

**The checker.** `PROBE_CITATIONS` in `tools/lean_numeral_audit.py`: five rows, each an anchor
sentence that must occur in the manuscript, a module and function that must resolve, and a
predicate that runs the function and checks what the sentence says about it. A test doctors
`decoration_budget` into an empty object and asserts both its citations break while the other
three do not -- the rename case, which is what motivated the row.

```text
  317 numerals   62 paired   255 structural   0 unclassified   0 failing
    9 prose claims about the manuscript                        0 stale
    5 probe citations                                          0 broken
```

Three audits now, in the three directions the same drift can run: Lean's constants against the
manuscript, Lean's prose about the manuscript, and the manuscript's prose about the probes.
Each was written after a failure of exactly its own kind, and each has since found one more.

## No draw from the caps can leave `(C1)`, and at the top the census over-covers what is applied

The question was how many census samples fall outside `(C1)` and
whether any probe should gate on the product. None do, and none should.

**`(C1)` is unviolatable by construction.** The census draws
`h_1 <= P^(1/48)`, `h_2 <= P^(1/24)`, `k <= P^(1/24)` independently, and
those three caps multiply to `P^(5/48)` against `(C1)`'s `P^(6/48)` ---
a factor `P^(1/48)` of room, which is the "`room P^(-1/48)`" the
manuscript records when it says `(C3)` and `(C4)` imply `(C1)`. Integer
flooring adds more: at `P_0` the real product bound is `25.8` and the
integer one is `1 * 3 * 3 = 9`. Even under `(C4)`'s own looser
`h_1 <= P^(1/24)` the product would be exactly `P^(1/8)`: equality,
never violation. `1600` draws, none outside, worst ratio `0.427`.

(The premise of the question was also wrong: `P^(1/8)` at `1e16` is
`100`, not `10`.)

**The comparison worth having is the other one.** Theorem 6.1 hands the
lemmas `k <= 2 P^(1/96)`, so the load it applies them at is
`2 P^(7/96)`:

```text
    P       product   (C1) P^(1/8)   ratio    load 2P^(7/96)   ratio
   1e4         1          3.162      0.316        3.915        0.255
   1e8         4         10.000      0.400        7.662        0.522
  1e12         9         31.623      0.285       14.998        0.600
  1e14         9         56.234      0.160       20.983        0.429
  1e15        32         74.989      0.427       24.819        1.289
  1e16        32        100.000      0.320       29.356        1.090
```

At the top two ranges the census reaches `32` against a load of `24.8`
and `29.4`. So it over-covers the operating range by `1.29` while
sitting at `0.43` of the hypothesis: it tests more than Theorem 6.1
needs and less than Lemma 5.2 permits, which is the right side of both.

That completes the parameter-reach picture the last three passes have
been assembling:

```text
  parameter   pinned at P_0 by        window above P_0   exercised by the audit
  k           Thm 6.1, 2P^(1/96)      2240               k = 1, 2 only
  h_1         P^(1/48)                7.85               h_1 = 2 at 1e15, 1e16
  h_2         P^(1/24)                --                 h_2 = 4 at 1e15, 1e16
  product     (C1) P^(1/8)            never binds        0.43 of it at worst
```

Tags. EXACT: the three caps multiply to `P^(5/48)` against `(C1)`'s
`P^(6/48)`, so no draw from them can violate `(C1)`; under `(C4)`
alone the product is exactly `P^(1/8)`, equality and not violation.
COMPUTATIONALLY VERIFIED: `1600` draws over eight ranges, zero outside
`(C1)`, worst ratio `0.4267` so the margin never falls below `2.343`;
the census exceeds the operating load `2P^(7/96)` at `1e15` and `1e16`,
by `1.289` and `1.090`. OBSERVATION: the audit tests strictly more than
Theorem 6.1 applies and strictly less than Lemma 5.2 allows, at every
range.

Probe: `census_admissibility`. Two tests. Audit
`PAPER_B_AUDIT_CONSISTENT`; `P_0` unmoved at `3.5858e13`. No manuscript
or certificate edit.

## The ranges, and the measurements that cite nothing at all

The last entry asked whether the ranges printed beside a probe citation match the defaults of
the function cited. Four do, and are now checked. The scan turned up a different problem on
the way: **three printed measurements name no function at all.**

```text
  printed                                              what is behind it
  "over P in [10^4,10^6] and k in {1,2,4}, twelve      level1_kernel_block_scaling takes one
   exponents with mean 0.49"                           (P,k); no sweep exists, and the four P
                                                       values are nowhere stated
  "on 20,000 samples the witness xi_2 sits between     no function produces it
   0.32 and 0.52 of beta_1 + beta_2"
  "measured at 0.989 times it over ten samples at      no function produces it
   n ~ 10^6"
```

Each is an honest number somebody ran. None can be re-run from the text: the reader is given
the answer and not the query. That is a weaker failure than a wrong number and a more durable
one, since nothing can go stale that nothing points at.

**One of the four could be anchored, and was.** The manuscript reported the offset term of
Lemma 5.1(iii) from a 300-point sample: "the ratio to `|j|P^(3/4)` runs over
`[1.510, 2.514]` against the printed `[1.5, 2.6]`". It has closed forms. The ratio is
`(3/2)(m + beta_1 + beta_2 + xi_1)^(1/2) P^(-3/4)`, and over `n` in `(P, 2P]` the bracket runs
from `m ~ P^(3/2)` to `m ~ (2P)^(3/2)`, so

```text
  [3/2, (3/2) 2^(3/4)] = [1.5000, 2.5227]   against the printed [1.5, 2.6]
```

the lower end *attained* -- which the sampled `1.510` had missed, and which is the sharper
statement -- and the upper carrying three percent. `decoration_budget.offset_term_attained`
computes it; the sampled figures are kept beside it, labelled as what a grid missed rather
than as the claim.

**And the ranges themselves.** `RANGE_CLAIMS` checks four printed quantifiers against the
signature defaults of the functions cited beside them: the beta inventory's
`1 <= h1, h2 <= 7`, the offset term's dyadic block, the ladder's `r = 1,2,3,6`, and the
calibration's `200` trials. A test doctors `branch_offset_ladder`'s default to `(1,2,3)` and
asserts exactly its row fires. `UNANCHORED` names the three measurements above, so the count
is visible in the audit's output rather than the claims being assumed reproducible; two of the
three are the other session's to anchor if it wants them.

```text
  317 numerals   62 paired   255 structural   0 unclassified   0 failing
    9 prose claims about the manuscript                        0 stale
    6 probe citations                                          0 broken
    4 printed ranges against the cited defaults                0 mismatched
    3 printed measurements citing no function
```

## Nine clauses, none of them protected by the caps, and one window that is

The census gates identities inside the caps, so it cannot say which of
its clauses the caps are protecting. Running the same check far outside
answers it. At `P = 1e6`, where the caps admit `h_1 = h_2 = k = 1`, the
families below reach `h_1 = h_2 = 500` and `k = 1000` --- a shift
product `1.78e6` times `(C1)`'s `P^(1/8) = 5.62`.

**Every clause survives.** Not one of the nine fails at any family.

```text
  clause                     kind         needs the caps?
  double_gap                 identity     no
  carry_sawtooth             identity     no
  F_equals_DDY               identity     no
  split_exact                identity     no
  master_identity            identity     no
  brackets_le_2              structural   no
  first_bracket_in_range     bound        no
  second_bracket_in_range    bound        no
  M1_bound                   bound        no
```

The five identities are algebra and hold for all reals. `brackets_le_2`
is structural: each bracket is a fractional part minus carries. What is
less obvious is that the three *bounds* survive too. The first bracket
is between `(3/2)|j| P^(3/4)` and `2.6|j| (P/2)^(3/4)`, the second
between `1.4 h_1h_2 P^(1/4)` and `15 h_1h_2 (P/2)^(1/4)`, and `M_1` is
at most `0.43 k h_1h_2 P^(-7/8)` --- all three stated in the very
parameters they bound, so they are scale-covariant. The caps do not make
them true; they make the quantities they bound *small*.

**The offset window is the one thing the hypothesis protects, and it
moves exactly as the algebra says.** With `u = {X(n)}`, `alpha`,
`gamma` the shifted fractional parts and `e = Delta^2 X`, the
constraints `u + alpha < 1` and `u + gamma < 1` give
`u + alpha + gamma + e < 2 - u + e <= 2 + eps`, so

```text
  -1 <= j <= floor(2 + eps),     eps = 3 h_1h_2 P^(-1/2),
```

which is `[-1, 2]` precisely while `eps < 1` --- that is `(C2)`.

```text
   h_1  h_2    k      eps      j observed     floor(2+eps)   [-1,2]?
     1    1    1      0.003    [ -1,   1]           2         yes
    10   10    1      0.300    [ -1,   1]           2         yes
    30   30    1      2.700    [  1,   4]           4         no
   100  100    1     30.000    [ 20,  29]          32         no
   100  100 1000     30.000    [ 21,  29]          32         no
   500  500    1    750.000    [531, 741]         752         no
```

Measured from `eps = 0.003` to `eps = 750`, the offset stays inside the
window at every family and leaves `[-1, 2]` exactly when `eps` does.

That is the whole answer: `(C2)` protects one clause, the identities
protect themselves, and the three bounds never needed protecting.

*Corrected in passing.* My first form of the window, `[-1, floor(eps) +
1]`, is wrong: at `eps = 2.7` the offset reaches `4` and that formula
gives `3`. `floor(2 + eps)` is what the algebra yields and it holds at
every family; the error showed up as a test failure at eight samples
before it reached the ledger.

Tags. EXACT: the five identities and `brackets_le_2` hold for all
parameters; the three bounds are stated in the parameters they bound and
so are scale-covariant; `-1 <= j <= floor(2 + eps)` from
`u + alpha + gamma + e < 2 - u + e`, and this is `[-1, 2]` iff
`eps < 1`. COMPUTATIONALLY VERIFIED: nine clauses over eight families,
six of them outside `(C1)` by up to `1.78e6`, zero failures at 8, 12 and
30 samples each; the window holds at every family and the printed one
fails exactly when `eps` passes `1`. OBSERVATION: `j` reaches `4` at
`eps = 2.7` and `741` at `eps = 750`.

Probe: `identity_clauses_outside_the_caps`, `IDENTITY_CLAUSES`. Two
tests. Audit `PAPER_B_AUDIT_CONSISTENT`; `P_0` unmoved at `3.5858e13`.
No manuscript or certificate edit.

## "Let `n >= 5` be odd" is a domain condition one value wide, and the bound under it is sharp

Two answers, pointing opposite ways.

**The threshold is one odd value wider than it needs to be.** At
`n = 3` both printed bounds of Lemma 6.2 hold, with slack ratios
`0.219` and `0.077` --- factors of `4.6` and `13` in hand. What fails at
`n = 1` is not the bound but its definition: there `X = m = v = U = 1`,
so the printed remainder's `(X-1)^(-7/8)`, `(U-1)^(-1/2)` and
`(v^(3/2)-1)^(-3/2)` are three divisions by zero at once. At `n = 3`
those denominators are `4.196`, `2.317` and `35.483`.

So the honest statement is "let `n >= 3` be odd", and `n = 1` is
excluded because the bound is not a statement there, not because it is
false. That is a *domain* condition and not a smallness one: where
`(C2)` controls the size of a quantity and is exactly the hypothesis
that makes the offset window `[-1, 2]`, this threshold only keeps three
denominators off zero, and `n = 3` already does that.

**And the bound it carries is the opposite of the ones in Lemma
5.1(iii).** Over every odd `n` in `[3, 200000]` --- `99999` points, no
violations --- part (i) is approached to

```text
  max slack ratio (i)   0.99997088   at n = 142915
  max slack ratio (ii)  0.66630931   at n = 105941
```

Part (i) has a margin of `2.9e-5`. Where the four displayed constants of
Lemma 5.1(iii) are loose by `1.78`, `3.95`, `7.11` and `2.82`, and its
run-length constant by `13.04`, this one has no room in it at all: any
weakening of any of its five remainder terms would break it. Part (ii)
keeps a factor `1.50`.

That is worth recording against the run of the last several passes. The
constants this ledger has been sharpening are the ones written for
convenience in a proof; this one was written to be true and is tight to
five figures. The two kinds are not distinguishable from the printed
page, and the difference matters: sharpening 5.1(iii)'s constants costs
nothing, and there is nothing to sharpen here.

Tags. EXACT: at `n = 1` the three printed denominators `X-1`, `U-1` and
`v^(3/2)-1` all vanish, so the bound is undefined and not false; at
`n = 3` they are `4.196`, `2.317`, `35.483`, so the honest threshold is
`n >= 3` odd. COMPUTATIONALLY VERIFIED: both bounds hold at `n = 3` with
ratios `0.2190` and `0.0770`; `99999` odd points in `[3, 200000]` with
zero violations; part (i) reaches `0.99997088` at `n = 142915` and part
(ii) `0.66630931` at `n = 105941`; the live `[3, 2000]` sweep reaches
`0.99940` at `n = 1517`. OBSERVATION: part (i) is sharp to `2.9e-5` and
so is not of the same kind as any constant this ledger has sharpened.

Probe: `lemma_6_2_least_n`, `LEMMA_6_2_WIDE_SWEEP`. Two tests. Audit
`PAPER_B_AUDIT_CONSISTENT`; `P_0` unmoved at `3.5858e13`. No manuscript
or certificate edit.

## The twelve exponents, and the interval that belonged to one P

The last entry left three printed measurements citing no function. The first of them is
Section 5's evidence that the level-1 kernel cancels at square root, and it is worth anchoring
rather than tolerating: "over `P in [10^4,10^6]` and `k in {1,2,4}`, twelve exponents with
mean `0.49`".

`decoration_budget.level1_exponent_sweep` is that ladder, stated:
`P in {10^4, 3e4, 10^5, 10^6}` against `k in {1,2,4}`. It calls across to
`paper_b_audit.level1_kernel_block_scaling` rather than adding to that module, which the other
session owns.

**The claim reproduces.** Twelve points, mean `0.4870`, which is the printed `0.49`.

```text
  P          k=1      k=2      k=4
  10^4     0.3866   0.4638   0.4472
  3e4      0.5081   0.5215   0.4461
  10^5     0.5178   0.5216   0.4682
  10^6     0.5139   0.5348   0.5144
```

Against square-root cancellation at `1/2` and no cancellation at `1`. The instrument's own 90%
interval on data that is exactly `1/2` is `[0.4268, 0.5684]`, and exactly one of the twelve
falls outside it -- `P = 10^4`, `k = 1`, at `0.3866` -- which is precisely what the sentence
claimed ("none outside ... except the smallest `P`"). The other eleven run `[0.446, 0.535]`,
and dropping the smallest `P` lifts the mean to `0.5052`.

**And the sweep found the clause next to it to be wrong.** "At `P >= 10^5` the ratio
`rms/sqrt(L)` sits in `[0.94, 1.12]`, flat in `L`." Over the thirty values that quantifier
covers, the ratio runs `[0.874, 1.150]`: `0.874` at `P = 10^5`, `k = 4`, and `1.150` at
`P = 10^5`, `k = 2`. `[0.94, 1.12]` is exactly -- to two decimals -- the range at `P = 10^6`
alone, where it is `[0.943, 1.121]`.

So the interval was right and its quantifier was not, in the same way and for the same reason
as everything else in these last few entries: a figure measured in one scope, printed in
another, with nothing comparing them. Corrected to say both, since both are informative: the
narrow one is a statement about the top of the ladder, the wide one about the range the
sentence quantifies over, and they agree about the object.

Two other things in that passage were checked and are exactly right. The five-number sequences
at `P = 10^6` -- the kernel's `0.943, 0.948, 0.947, 0.963, 0.981` and the unweighted defect's
`0.99, 1.07, 1.48, 2.09, 2.94` over block lengths `1953` to `31250` -- reproduce to every
printed digit, as does the control's `L^0.91` (measured `0.9099`). That contrast is the
passage's actual argument, and it stands.

```text
  317 numerals   62 paired   255 structural   0 unclassified   0 failing
    9 prose claims about the manuscript                        0 stale
    7 probe citations                                          0 broken
    5 printed ranges against the cited defaults                0 mismatched
    2 printed measurements citing no function
```

## Part (ii) stops at two thirds because it charges a term of the same order twice

Part (i) reaches `0.99997` of its bound and part (ii) only `0.66631`.
The difference is one term, and the number `2/3` is arithmetic.

**Part (i)'s bound is a leading term plus corrections.** Against a
leading `(3/4) m^(-3/8) = O(n^(-9/16))`, the other four are
`O(n^(-27/16))`, `O(n^(-21/16))`, `O(n^(-45/16))` and `O(n^(-81/16))`.
So the ratio is the leading term's own, and it reaches `1`.

**Part (ii)'s bound is two terms of the same order.** `U = v^(1/2)` and
`v ~ m^(3/2)`, so `(U-1)^(-1/2) ~ v^(-1/4) = m^(-3/8)`, and the second
term `(3/8)(U-1)^(-1/2)` is **exactly half** the first. Measured at the
argmax `n = 105941`:

```text
  |D_5'|                    1.117467e-3
  (3/4) m^(-3/8)            1.118054e-3     |D_5'| / this = 0.999475
  (3/8)(U-1)^(-1/2)         5.590276e-4     ratio to the first = 0.500001
  (9/128)(X-1)^(-7/8)       1.784991e-8
  (3/32)(Y-1)^(-5/4)        6.902058e-16
```

The remainder is `0.999475` of the **first term alone**. So the full
ratio is `(3/4)/(3/4 + 3/8) = 2/3 = 0.666667`, against the `0.666309`
measured --- to four figures. The cap is not an accident of the range;
it is what the bound is made of.

**And the second term is deletable.** Dropping it leaves
`(3/4) m^(-3/8) + (9/128)(X-1)^(-7/8) + (3/32)(Y-1)^(-5/4)`, which over
every odd `n` in `[3, 200000]` --- `99999` points --- is never violated
and is approached to `0.99945901`, at the same argmax `n = 105941`.

```text
  bound for part (ii)     violations   max ratio      margin
  as printed              0            0.66630931     factor 1.50
  with (3/8)(U-1)^(-1/2)  0            0.99945901     5.4e-4
  deleted
```

So the proof charges `1.5` times what it uses, and the reduced bound is
as sharp as part (i)'s. That is the one place in Lemma 6.2 where there
is anything to sharpen, and it is a deletion rather than a
re-derivation.

Tags. EXACT: `(U-1)^(-1/2) ~ v^(-1/4) = m^(-3/8)`, so `(3/8)(U-1)^(-1/2)`
is asymptotically half of `(3/4) m^(-3/8)` and the printed ratio caps at
`(3/4)/(9/8) = 2/3`; part (i)'s other four terms are of strictly lower
order, which is why its ratio reaches `1`. COMPUTATIONALLY VERIFIED: at
`n = 105941` the second-to-first ratio is `0.500001` and `|D_5'|` is
`0.999475` of the first term; the full ratio maxes at `0.66631` against
the arithmetic `0.66667`; the reduced bound holds at all `99999` odd
points of `[3, 200000]` with max ratio `0.99945901`. OBSERVATION: the
argmax of the reduced bound is the argmax of the printed one.

Probes: `lemma_6_2_part_ii_term_inventory`,
`LEMMA_6_2_REDUCED_WIDE_SWEEP`. Two tests. Audit
`PAPER_B_AUDIT_CONSISTENT`; `P_0` unmoved at `3.5858e13`. No manuscript
or certificate edit.

## The separation is not a feature of one P, and it opens where it must

Section 5 reads the level-1 kernel's cancellation off a contrast measured at one `P`: the
kernel's `rms/sqrt(L)` stays flat while the unweighted control's climbs like `L^0.91`. The
last entry asked whether that separation is stable in `P`, or whether the control's exponent
drifts toward `1/2` as `P` grows -- which would make the contrast a small-`P` artefact and
weaken the claim that the weight is what produces the cancellation.

**It is the opposite, and there is a mechanism.** The control is the Weyl sum itself, since
`e({n^(3/2)}) = e(n^(3/2))`. Over odd `n` with step `2` its curvature in the term index is
`lambda = 3 n^(-1/2) ~ 3 P^(-1/2)`, so a block sum of length `L` is
`<< L lambda^(1/2) + lambda^(-1/2)` by the second-derivative test. The first term is *linear*
in `L`, and it dominates once `L >> 1/lambda = sqrt(P)/3`. So the control's fitted exponent
runs to `1`, not to `1/2`.

The five fitted block lengths are `L in [P/512, P/32]`, so the whole window clears the
crossover once `sqrt(P) >= 2*256/3`, i.e. `P > (512/3)^2 = 2.91e4`. That is a prediction about
*where the separation begins*, and it can be checked.

```text
  P          kernel   control      gap    L_min/L*   window clears
  10^4       0.3866    0.4902    0.104        0.59   no
  3e4        0.5081    0.5733    0.065        1.01   yes
  10^5       0.5178    0.7252    0.207        1.85   yes
  3e5        0.4738    0.8181    0.344        3.21   yes
  10^6       0.5139    0.9099    0.396        5.86   yes
  3e6        0.5563    0.9852    0.429       10.15   yes
```

The kernel is flat at `1/2` -- mean `0.4928`, spread `0.170` across two and a half decades,
no trend. The control climbs monotonically to `0.9852`. The gap widens monotonically from
`3e4` on. And at `P = 10^4` there is no separation to speak of: the control reads `0.4902`
against the kernel's `0.3866`, and that is the one row whose window does not clear the
crossover (`L in [20, 312]` against `1/lambda = 33`).

So the contrast is absent below `2.91e4`, appears exactly there, and grows. `0.91` at `P = 10^6`
is not a plateau but a point on a curve going to `1`. That is a stronger statement than the
paragraph made, and it is the statement the paragraph wanted: the weight destroys the
smoothness that makes `e(n^(3/2))` a stationary-phase object, and the measurement now shows the
control becoming *more* stationary-phase-like as `P` grows while the kernel does not move.

`decoration_budget.level1_control_trend` and `level1_control_crossover`; the passage is added
to Section 5 beside the single-`P` contrast, and a citation row covers it.

One slip caught by its own test: the crossover condition `(P/2)/bins >= sqrt(P)/3` is
`sqrt(P) >= 2 bins/3`, so the threshold is `(2 bins/3)^2`. It was first written `(bins/6)^2`,
which gives `1820` instead of `29127` -- an order and a half, and it would have put the
crossover below every measured `P`, making the "appears exactly there" claim vacuous.

## Both bounds are attained in the limit: the argmaxes are where the sweep stopped, not where the bound is sharp

The two residuals at the end of the sweep --- `2.9e-5` for part (i) and
`5.4e-4` for the reduced part (ii) --- looked like a difference in kind.
They are not. Neither running maximum has plateaued.

```text
  points     max (i)      argmax     max (ii, reduced)   argmax
    1000     0.99939844     1517     0.98696599            421
    2500     0.99939844     1517     0.99707776           2833
    5000     0.99939844     1517     0.99833797           7573
   10000     0.99957657    10545     0.99833797           7573
   25000     0.99982449    20833     0.99833797           7573
   50000     0.99991806    89945     0.99931633          94851
   99999     0.99997088   142915     0.99945901         105941
```

Both climb across a sweep a hundred times longer than the first, and
every argmax moves up with the range. Fitting `1 - max` against the
number of points:

```text
  part (i)        1 - max  ~  0.11 N^(-0.664)
  part (ii) red.  1 - max  ~  0.41 N^(-0.584)
```

The same power to within the noise of a step function. So the two are
the same kind of object: **both bounds are asymptotically exact**, their
suprema tend to `1`, and neither has any constant to spare. The
`18.6`-fold gap between the two residuals is the constant in one power
law against the constant in the other.

That closes Lemma 6.2. The only improvement available anywhere in it is
the deletion of `(3/8)(U-1)^(-1/2)` from part (ii), recorded last pass;
after that deletion there is nothing left to shave, because what remains
is attained in the limit. The `n >= 5` threshold can go to `n >= 3` and
that is a domain condition, not a saving.

Set against the other half of this ledger's subject, the contrast is
now complete:

```text
  Lemma 5.1(iii)   four displayed constants and a run-length constant,
                   loose by 1.78, 3.95, 7.11, 2.82 and 13.04, all of
                   them the same two quantities charged at two points
  Lemma 6.2        one deletable term; the rest attained in the limit
```

Tags. EXACT: the argmax of each maximum moves with the range, so
neither is a sharpest point. COMPUTATIONALLY VERIFIED: the seven
checkpoints above over `[3, 200000)`; `1 - max` fits `0.11 N^(-0.664)`
and `0.41 N^(-0.584)`, and the live short sweep reproduces the first
checkpoint exactly; the final residuals are `2.912e-5` and `5.410e-4`,
a ratio of `18.58`. OBSERVATION: the two powers agree to within the
noise of a step function, so the residual gap is a constant and not a
difference in kind.

Probes: `lemma_6_2_approach_rate`, `LEMMA_6_2_APPROACH_CHECKPOINTS`.
Two tests. Audit `PAPER_B_AUDIT_CONSISTENT`; `P_0` unmoved at
`3.5858e13`. No manuscript or certificate edit.

## The kernel has no crossover, and the reading I explained away was a draw

The last entry ended by asking at what `P` the *kernel* enters its asymptotic regime, and
whether `10^4` is below it for the same kind of reason the control is. The question carried an
implication, and the implication is mine and is wrong: I had been calling `0.3866` "the
smallest `P`" as though that named a mechanism.

**There is no kernel crossover.** The coefficient is `c(n) = (27k/32) n^(33/32)`, so
`c'(n) = (891k/1024) n^(1/32)` and over odd `n` with step 2 the coefficient advances by
`2c' = (891k/512) n^(1/32)` per summand. "More than a whole period per step" is `2c' > 1`, and
that holds from `n = (512/891k)^32 ~ 2e-8` upward -- below every `P` anyone would run. Nothing
turns on at a threshold, which is exactly why the kernel column is flat where the control
column is not.

The condition is not comfortable, and that is worth printing. `2c'` runs `2.32` at `10^4` to
`2.77` at `3e6` and reaches `10` only near `2e24`, because it grows like `n^(1/32)` -- the same
`1/32` the drift threshold turns on. One exponent does both jobs: it is what puts `c` past the
drift-`1` window and what decorrelates the summands, and it does the second from the start and
the first only just. That is a sharper statement of the paragraph's "the same drift is what
makes the sum cancel" than the paragraph had.

**And the low reading is the estimator.** Across `k = 1..8` at `P = 10^4`:

```text
  0.387 0.464 0.511 0.447 0.551 0.439 0.436 0.584     mean 0.4771  sd 0.062
```

Two excursions from the instrument's 90% interval, one low (`k = 1`) and one *high*
(`k = 8`, at `0.584`) -- which is what a 90% interval predicts for eight draws. The spread
falls with `P`: `0.062`, `0.035`, `0.024` at `10^4`, `3e4`, `10^5`, and the means are `0.4771`,
`0.4927`, `0.5014`. That is a statement about terms per block and not about the sum: the
calibration was run at `N = 5000`, which is exactly the term count at `P = 10^4`.

So the kernel is at `1/2` at every `P` measured, including the one whose single `k = 1` reading
sits outside the interval. `decoration_budget.level1_kernel_condition` and
`level1_kernel_k_spread`; the manuscript carries both, beside the control's crossover, and a
citation row covers them.

Worth naming the error rather than only the fix. A single reading outside an interval invites a
mechanism, and the previous entry's own table -- where the control's outlier *did* have one --
made that invitation harder to refuse. Eight draws at the same `P` cost forty seconds and
settle it. The instrument had been calibrated two entries earlier precisely so that readings
could be told apart from noise, and I did not use it that way until the question forced it.

## The same term, sharp at the `m`-level and redundant at the `v`-level

Theorem 4.8 states `w^(3/2) = m^(3/4) - (3/2) m^(1/4) theta_w + E` with
`0 <= E <= (3/8)(U-1)^(-1/2)`, `U = m^(1/2)`, `w = floor(U)`. That upper
bound is the *same* `(3/8)(U-1)^(-1/2)` Lemma 6.2(ii) carries at the
`v`-level, and which the term inventory found redundant there. Here it
stands alone, and it is sharp.

**Where it comes from.** `w = U - theta_w`, so

```text
  w^(3/2) = U^(3/2) - (3/2) U^(1/2) theta_w + (3/8) U^(-1/2) theta_w^2 - ...
```

and `U^(3/2) = m^(3/4)`, `U^(1/2) = m^(1/4)`. So `E` is
`(3/8) theta_w^2 U^(-1/2)` to leading order, and the printed bound is
that with `theta_w^2 <= 1` and `U^(-1/2) <= (U-1)^(-1/2)`. The ratio
`E/bound` is therefore `theta_w^2`.

**Both ends are sharp, and in different ways.** The lower end is
attained *exactly*, at every even square: `m = w^2` gives `theta_w = 0`
and `E = w^(3/2) - (w^2)^(3/4) = 0`. The upper end is approached:

```text
  points     max E/bound     argmax     1 - max     ratio to the step before
    1000     0.96917912       1848     3.082e-2       --
   10000     0.99056142      19880     9.439e-3     3.265   (sqrt 10 = 3.162)
  100000     0.99701892     199808     2.981e-3     3.166   (sqrt 10 = 3.162)
  500000     0.99866569     998000     1.334e-3     2.234   (sqrt  5 = 2.236)
```

`1 - max` falls as `M^(-1/2)`, matching each step's own `sqrt` of the
points ratio to within `3%`. That is what `E/bound = theta_w^2`
predicts: consecutive `m^(1/2)` differ by about `1/(2 m^(1/2))`, so
`max theta_w = 1 - Theta(M^(-1/2))`.

**So the `v`-level's exactness is a property of the term, not of the
second nesting.** The same bound is asymptotically exact at both levels.
What differs is only the rate, and that is the spacing of the fractional
part being maximised: `M^(-1/2)` here against about `N^(-0.6)` at the
`v`-level. And the term is sharp where it is stated and superfluous only
where it was carried: at the `v`-level `(3/4) m^(-3/8)` is already the
same order and dominates, so the sum charges one order twice.

*An artefact, recorded so the next reader does not chase it.* A sweep at
`60` digits reports one `E < 0`, at `m = 256036 = 506^2`, of size
`-1.3e-57`. That is the equality case: `theta_w = 0` there and the true
`E` is exactly `0`, as a run at `200` digits confirms. The probe uses a
tolerance and counts the even squares it passes.

Tags. EXACT: `E = (3/8) theta_w^2 U^(-1/2) + ...` from `w = U -
theta_w`, so `E/bound = theta_w^2`; `E = 0` exactly at every even
square; `max theta_w = 1 - Theta(M^(-1/2))` from the spacing of
`m^(1/2)`. COMPUTATIONALLY VERIFIED: the four checkpoints above over
even `m` to `1e6`; the residual ratios `3.265`, `3.166`, `2.234`
against `sqrt` of the points ratios `3.162`, `3.162`, `2.236`; no sign
violation outside the round-off at `256036`; the live short sweep
reproduces the first checkpoint. OBSERVATION: the exactness of the
`v`-level bounds is not a feature of the second nesting.

Probes: `theorem_4_8_E_bound`, `THEOREM_4_8_E_CHECKPOINTS`. Two tests.
Audit `PAPER_B_AUDIT_CONSISTENT`; `P_0` unmoved at `3.5858e13`. No
manuscript or certificate edit.

## Mean or maximum: the mean settles first, the maximum needs no model, and on a fixed ratio they agree

The census reports maxima. The question was whether the mean ratio
would find a bound loose by a constant sooner, since a loose bound moves
the mean and a sharp one does not. Measured on the four ratios this
ledger uses:

```text
    N      4.8 E: mean/max     6.2(i)          6.2(ii) printed   6.2(ii) reduced
   200     0.3349 / 0.9807     0.4848/0.9859   0.2453/0.6294     0.3681/0.9439
  1000     0.3308 / 0.9949     0.5006/0.9994   0.2569/0.6581     0.3853/0.9870
  5000     0.3357 / 0.9985     0.4903/0.9994   0.2498/0.6656     0.3746/0.9983
```

**The mean settles much earlier.** Theorem 4.8's is `1/3` from two
hundred points and stays inside a percent of it, which is the
prediction: `E/bound = theta_w^2` with `theta_w` equidistributed gives
`int_0^1 t^2 dt = 1/3`. The maximum is still `1.5%` short at a thousand
points and `0.15%` short at five thousand, because it is waiting for
`theta_w` to come near `1`.

**But the mean needs a model and the maximum does not.** A sharp bound
has maximum `1` whatever the ratio's distribution; its *mean* is `1/3`
only when the ratio is `theta^2`. Lemma 6.2(i)'s mean is `0.5006` ---
its ratio is uniform, not a square --- and that is not looseness. So a
mean can only be read as a constant once the ratio's shape is known,
and the two bounds studied here have different shapes.

**On the question that actually arises, they agree.** "Is this term
redundant" is "are these two bounds on one quantity in a fixed ratio",
and for `6.2(ii)` printed against reduced:

```text
  ratio of means    0.666675
  ratio of maxima   0.666767
  the arithmetic    0.666667
```

Both to three figures. Whichever instrument is used, the redundant term
shows as the same `3/2`.

**The asymmetry that keeps the census on maxima.** A bound that is sharp
only on a sparse set has a small mean and a maximum at `1`. The mean
cannot separate "loose by a constant" from "sharp but rarely attained";
the maximum can. Every finding in this ledger about a loose constant was
of the first kind, and every one about a sharp bound was of the second,
and only the maximum distinguishes them without a distributional
assumption.

So the answer is: the mean is the better instrument for *measuring* a
constant when the ratio's shape is known, no better for *comparing* two
bounds, and not a substitute for the maximum as a test of sharpness.

Tags. EXACT: `E/bound = theta_w^2` with `theta_w` equidistributed gives
mean `1/3`; a sharp bound has maximum `1` for any ratio distribution,
which is why the maximum needs no model. COMPUTATIONALLY VERIFIED: the
table above; `4.8`'s mean stays within a percent of `1/3` from `200`
points while its maximum is `0.9807`, `0.9949`, `0.9985`; `6.2(i)`'s
mean is `0.5006`; the ratio of means `0.666675` and of maxima
`0.666767` against `2/3`. OBSERVATION: a sparse sharp bound has a small
mean and a maximum at `1`, so the mean cannot separate the two kinds of
looseness this ledger has been distinguishing.

Probe: `bound_ratio_instruments`. Two tests. Audit
`PAPER_B_AUDIT_CONSISTENT`; `P_0` unmoved at `3.5858e13`. No manuscript
or certificate edit.

## At most one, not none; and nothing printed depends on the size

The last entry asked whether `2c' ~ 3.4` at `P_0` is enough for the Kuzmin-Landau step that
uses it, and whether any printed constant depends on how much bigger than `1` it is. The
question is wrong twice over, and the second error is the interesting one.

**It is not a Kuzmin-Landau step.** Kusmin-Landau appears at Theorem 4.x and in Lemma 5.2's
Stage 3, where the relevant condition is that `||f'||` stays *away* from an integer. The
`c' >> 1` of Section 5 is the opposite situation -- the coefficient sweeping *through* periods
-- and feeds the drift threshold, not a Kusmin-Landau bound. Conflating them was mine.

**And `2c'` at `P_0` is `4.615`, not `3.4`.** I interpolated between `2.77` at `3e6` and `9.79`
at `1e24` as though the growth were faster than `n^(1/32)`. The exponent is small enough that
eyeballing it is not safe.

**The answer to the question as asked is no, and it is worth printing.** The condition enters
as the binary `2c' > 1`, which is window length against lattice spacing; no constant in
Sections 4-7 carries `c'` beyond that. What grows with `c'` is the occupancy `1/(2c')`, which
describes the situation rather than bounding anything. Worth saying because the margin is thin
and slow: `2c' = (891k/512) n^(1/32)` is `2.32` at `10^4`, `4.62` at `P_0`, and reaches `10`
only near `2e24`. A reader who assumed the drift condition was comfortable at `P_0` because the
exponent exceeds `1` would be assuming the wrong thing; it exceeds it by a factor under five,
and the argument is built so that this does not matter.

**Finding, in passing: "contains no integer at all" is too strong.** The manuscript read the
drift-1 window as "shorter than the spacing of the summation variable, so it contains no
integer at all". Shorter than the spacing gives *at most one*, not none. Over odd `n` the
spacing is `2`, so a window of length `1/c' < 2` holds one odd integer with density
`(1/c')/2 = 1/(2c')`:

```text
  P        1/c'      density   counted
  10^4    0.8618      0.4309    0.4309
  10^6    0.7463      0.3732    0.3732
  10^8    0.6463      0.3231    0.3231
  P_0     0.4334      0.2167       --
```

Tiling the block and counting reproduces `1/(2c')` to four figures
(`decoration_budget.level1_drift_window_occupancy`). The density falls only like `n^(-1/32)`,
so it is never zero: at `P_0` more than a fifth of drift-1 windows contain a summand.

The conclusion is untouched, and the correction sharpens why. What Lemma 3.7 expands is a sum
over a window; at most one summand per window is already fatal, and that is exactly what
"finer than the lattice" says. "No integer at all" would have been a stronger claim doing no
extra work, and it is false.

## `6.2(ii)`'s remainder is linear in one fractional part and quadratic in another, and they meet at the same order

`6.2(i)`'s ratio is uniform and `4.8`'s is a square. `6.2(ii)`'s is the
difference of the two, and writing it out identifies the remainder's
leading term.

**Split `D_5'` at the two nestings it crosses.** At the `v`-to-`w` step,
`w^(3/2) - (v^(3/4) - (3/2) v^(1/4) theta_w)` is Theorem 4.8's `E` with
base `v`, so it is `(3/8) theta_w^2 v^(-1/4)`. At the `m`-to-`v` step,
`v = Y - theta_2` with `Y = m^(3/2)`, so
`v^(3/4) = Y^(3/4) - (3/4) Y^(-1/4) theta_2 + ...`, and
`Y^(3/4) = m^(9/8) = n^(27/16) - (9/8) n^(3/16) theta + ...`. Both
corrections carry the same power, since `v^(-1/4)` and `Y^(-1/4)` are
each `m^(-3/8)`:

```text
  D_5'  =  m^(-3/8) [ (3/8) theta_w^2  -  (3/4) theta_2 ]  +  lower order
```

So the leading term is `-(3/4) theta_2 m^(-3/8)`, **linear** in
`theta_2 = {m^(3/2)}`, with a **quadratic** correction
`(3/8) theta_w^2 m^(-3/8)` of the same order, `theta_w = {v^(1/2)}`.
The reduced ratio is `|theta_w^2/2 - theta_2|`, with mean

```text
  int_0^1 int_0^1 |t^2/2 - u| du dt  =  23/60  =  0.383333
```

and supremum `1`, at `theta_2 -> 1` with `theta_w -> 0`.

**Measured.** The model matches the ratio sample by sample to
`9.3e-5` on `[10000, 12000)` and `4.1e-5` on `[30000, 32000)`, the
deviation being a genuine lower-order term --- worst at `n = 13`, where
it is `1.1e-2`. Over `[3, 6000)` the model's mean is `0.376359` against
the ratio's `0.376277`, a gap of `8.2e-5`. The remaining distance to
`23/60` is the finite range, not the model; a Monte Carlo of the model
with independent uniforms gives `0.383065`.

**Three things already recorded fall out of it.**

```text
  the reduced bound is asymptotically exact   because sup |thw^2/2 - th2| = 1
  the printed bound caps at 2/3               because |D_5'| <= (3/4) m^(-3/8)
                                              against a denominator (9/8) m^(-3/8)
  the mean is 0.3784, not 1/3 or 1/2          because the ratio is neither a
                                              square nor a uniform
```

And the structural reading: the two fractional parts come from
*different nestings* --- `theta_2` from `m -> v` and `theta_w` from
`v -> w` --- and they arrive at the same power of `m`. That is why the
term inventory found a same-order pair in the bound: the bound is
carrying one term for each nesting, and the remainder is their
difference.

Tags. EXACT: `D_5' = m^(-3/8)[(3/8) theta_w^2 - (3/4) theta_2] + lower
order` from the two-step split; the reduced ratio is
`|theta_w^2/2 - theta_2|` with closed-form mean `23/60` and supremum
`1`. COMPUTATIONALLY VERIFIED: the model matches sample by sample to
`9.3e-5` at `1e4` and `4.1e-5` at `3e4`, with the deviation falling as a
lower-order term; means `0.376277` measured against `0.376359` modelled,
gap `8.2e-5`; Monte Carlo of the model `0.383065` against `23/60`.
OBSERVATION: the two fractional parts enter from different nestings at
the same order, which is where the bound's same-order pair comes from.

Probe: `lemma_6_2_part_ii_leading_term`. Two tests. Audit
`PAPER_B_AUDIT_CONSISTENT`; `P_0` unmoved at `3.5858e13`. No manuscript
or certificate edit.

### And the guard on that sentence fired

Rewriting the drift-window sentence rewrapped it, and
`test_paper_states_what_the_level_one_kernel_is` pins the phrase "finer than the lattice it is
supposed to sit on" as a contiguous string. The rewrap put a line break inside it. Nothing was
wrong with the prose; the guard was watching the line, not the sentence.

Rewrapped so the phrase is contiguous again, rather than loosening the guard. A pinned phrase
that survives only until someone reflows a paragraph is a weak guard, but the alternative --
matching across line breaks -- makes every such test a regex, and the manuscript wraps at
seventy-two columns by hand. The cheaper discipline is to keep pinned phrases off line
boundaries, and this is the second time this session that a wrap has broken a check (the other
was `coincidence of a feasible choice`, in A.6).

## The exponent of the last step decides how many nestings reach the leading term

The same two-step split on part (i). `z = v^(3/2) - theta_z`, so
`z^(1/2) = v^(3/4) - (1/2) v^(-3/4) theta_z + ...`; then
`v = Y - theta_2` with `Y = m^(3/2)` gives
`v^(3/4) = m^(9/8) - (3/4) m^(-3/8) theta_2 + ...`; and `m = X - theta`
gives `m^(9/8) = n^(27/16) - (9/8) n^(3/16) theta + ...`. So

```text
  D_5  =  -(3/4) theta_2 m^(-3/8)  +  lower order
```

linear in the *single* fractional part `theta_2 = {m^(3/2)}`, and the
ratio `|D_5|/((3/4) m^(-3/8))` is `theta_2` itself: uniform, mean `1/2`,
which is the `0.5006` measured last pass.

**Why the last nesting drops out here and not in (ii).** Compare each
last step's coefficient against the lead `(3/4) m^(-3/8)`:

```text
  (i)   z = floor(v^(3/2))   theta_z enters at (1/2) v^(-3/4)
                             share of the lead = (2/3) m^(-3/4)  ->  0
  (ii)  w = floor(v^(1/2))   theta_w's linear term is (3/2) v^(1/4),
                             so large the identity subtracts it explicitly,
                             leaving (3/8) v^(-1/4)
                             share of the lead = 1/2, for every n
```

Taking a `3/2` power at the last step pushes its fractional part down to
`v^(-3/4)`; taking a `1/2` power leaves the quadratic at `v^(-1/4)`,
which is the lead's own order. At `n = 1e4` the shares are `2.108e-5`
and `0.5000000001`.

So the fifth-letter identity carries one nesting in (i) and two in (ii),
and that is a fact about the exponent, not about the letters. It also
finishes the account of the bound: `(i)` needs one leading term and four
corrections of strictly lower order, `(ii)` needs two leading terms, and
the second of them is the one the term inventory found deletable ---
deletable because what it bounds is a *difference*, and the difference
is bounded by the larger of the two.

**Measured.** The ratio matches `theta_2` to `8.96e-5` on
`[10000, 12000)` and `4.01e-5` on `[30000, 32000)`, the deviation
falling as a lower-order term (worst `9.66e-2`, at `n = 3`). Over
`[3, 6000)` the means are `0.493793` measured against `0.493682`
modelled, a gap of `1.1e-4`.

```text
  the three ratios of this ledger, now all accounted for
  Thm 4.8 E        theta_w^2                 mean 1/3     one nesting, quadratic
  Lem 6.2(i)       theta_2                   mean 1/2     one nesting, linear
  Lem 6.2(ii)      |theta_w^2/2 - theta_2|   mean 23/60   two nestings, both
```

Tags. EXACT: `D_5 = -(3/4) theta_2 m^(-3/8) + lower order` from the
three-step split, so the ratio is `theta_2`; the last-nesting share of
the lead is `(2/3) m^(-3/4)` in (i) and `1/2` in (ii), the latter
independent of `n`. COMPUTATIONALLY VERIFIED: the shares `2.108e-5` and
`0.5000000001` at `n = 1e4`; the ratio matches `theta_2` to `8.96e-5`
and `4.01e-5` in the two tail windows; means `0.493793` against
`0.493682`. OBSERVATION: which fractional parts reach the leading term
is decided by the exponent of the last nesting, not by the itinerary.

Probe: `lemma_6_2_part_i_leading_term`. Two tests. Audit
`PAPER_B_AUDIT_CONSISTENT`; `P_0` unmoved at `3.5858e13`. No manuscript
or certificate edit.

## What "fatal" costs, and why care does not help

The last entry left "at most one summand per window is already fatal to Lemma 3.7" as a
statement rather than a bound, and asked whether there is a sharper one and whether the paper
needs it. There is; it does not; and the sharper one explains something the weaker one does
not.

**The loss is not the flat cost.** Lemma 3.7's pointwise error carries `8(1+c)/U`, and the
lemma's own hypothesis is `U >= 8(1+c)`, so that term is at most `1` per point automatically.
Looking there for the failure finds nothing.

**The loss is the coefficient mass.** The expansion replaces one sum over a window by
`sum |b_u| + sum |v_q| <= 8 + 2 log(2 + c + U) + 4 H_J` sums over the same window. It beats the
trivial bound only if the individual mode sums do, and on a window of one term every mode sum
is a single unimodular term, of modulus exactly `1`. So the expansion returns the whole mass
against a trivial bound of `1`:

```text
  P          b-mass   v-mass    total
  10^6         40.5     19.6     60.1
  P_0          76.4     41.3    117.7
  10^24       126.0     71.4    197.4
```

Two orders worse than not expanding, at the frozen `c ~ (27k/32) P^(33/32)` the kernel would
need and `J = R_0`. So "no better than trivial" understates it.

**Two edges, not one.** At the hypothesis boundary `U = 8(1+c)` the flat error is exactly `1`
on its own -- the trivial bound, before a single mode is counted. Buying that term back means
raising `U`, and the `b`-mass carries `log U`: at `U` a hundred times the boundary the flat
term falls to `0.01` and the `b`-mass rises from `40.5` to `85.4`.

**And the two failures have one cause**, which is the part worth having. The window is short
because `c` is large, `1/c' ~ P^(-1/32)/k`; the mass is large because `c` is large,
`2 log c ~ (33/16) log P`. There is no setting of `U` or `J` that trades one against the other,
because both ends of the lemma are driven by the same quantity. That is what "no amount of care
with Lemma 3.7 recovers it" means, and it was previously asserted rather than shown.

The paper needs only the weaker statement and has it. `decoration_budget.lemma37_one_term_window_cost`;
the price goes into the erratum block beside the occupancy, with a citation row.

**The notation guard fired, correctly.** The passage sits in Section 7, where bare `A`, `B`,
`S`, `T` are reserved for that section's script letters, and Lemma 3.7's statement uses `B` for
the coefficient and `T` for the cutoff. Re-lettered to `c` and `U` -- which is truer to the
application anyway, since the lemma's `B` *is* this section's `c`. Third time this session the
notation scanner has caught a symbol imported from another section's statement; it is a good
guard and the failure mode is always the same, quoting a lemma in a section that has spent its
alphabet.

## Theorem 4.7 does not charge one order twice, and the rule I stated last pass was the wrong exponent

Theorem 4.7 reaches its `OOEE` class through Lemma 4.6:
`v^(1/2) = n^(9/8) + D` with
`-(3/4) n^(-3/8) - n^(-9/8) <= D <= 0`. That does end on a square root
--- but the square root is the *outer* function, not the one making the
floor. `D` expands as `-(3/4) theta n^(-3/8) - (1/2) theta_2 Y^(-1/2) +
...` with `Y^(-1/2) ~ n^(-9/8)`, so the last nesting arrives a factor
`n^(-3/4)` below the lead: measured share `6.666e-4` at `n = 1e4`. Its
printed bound is a lead plus a genuine lower-order correction, not one
order charged twice, and its ratio is `theta` --- uniform, mean `0.4534`
over `[3, 6000)`, maximum `0.9974`, the same shape as `6.2(i)`.

**And the rule needs restating.** A nesting expands

```text
  f(floor(g)) = f(g) - f'(g) theta + (1/2) f''(g) theta^2 - ...
```

With `f(x) = x^a` and `g ~ n^b`:

```text
  a < 1   the derivative shrinks; the linear term n^(b(a-1)) is the contribution
  a > 1   the derivative grows; the identity carries the linear term explicitly
          and the quadratic n^(b(a-2)) is what is left
```

So the **outer** exponent decides. Last pass I wrote that "the exponent
of the last step decides" and read it off the floor --- `v^(1/2)` in
(ii) against `v^(3/2)` in (i). That pairing is backwards: what matters
is the exponent applied *to* the floor, `3/2` in (ii) and `1/2` in (i).
The two are swapped between those lemmas, which is exactly why the wrong
reading fitted the two cases I had.

```text
  site           outer a   g~n^b     contribution        bound lead   at the lead
  Thm 4.8 E        3/2      3/4      n^(-3/8) quadratic   n^(-3/8)    yes (it is the bound)
  Lem 4.6 D        1/2      9/4      n^(-9/8) linear      n^(-3/8)    no, by n^(-3/4)
  Lem 6.2(i)       1/2     27/8      n^(-27/16) linear    n^(-9/16)   no, by n^(-9/8)
  Lem 6.2(ii)      3/2      9/8      n^(-9/16) quadratic  n^(-9/16)   yes
```

Measured shares at `n = 1e4`: `6.666e-4`, `2.108e-5`, `0.5000000001`.

Only `6.2(ii)` has a *second* nesting arriving at the leading order, and
it is the only one of the four whose bound charges one order twice.
Theorem 4.8's quadratic is at its bound's order because it *is* the
bound --- one nesting, one term.

So the deletion recorded four passes ago remains the only place in this
family with anything to remove, and now there is a reason it is the only
one rather than a census that found nothing else.

Tags. EXACT: `f(floor(g))` contributes `n^(b(a-1))` when `a < 1` and
`n^(b(a-2))` when `a > 1`, so the outer exponent decides; Lemma 4.6's
last nesting is at `n^(-9/8)` against a lead `n^(-3/8)`; the four-site
table above. COMPUTATIONALLY VERIFIED: shares `6.666e-4`, `2.108e-5`,
`0.5000000001` at `n = 1e4`; Lemma 4.6's ratio is `theta` to `8.67e-2`
at worst (at `n = 11`), mean `0.4534`, maximum `0.9974`. OBSERVATION:
`6.2(ii)` is the only site in the family with a second nesting at the
lead.

*Correction.* The formulation in the previous section --- "the exponent
of the last step decides" --- names the wrong exponent. The conclusions
drawn there are unaffected: the shares `2.108e-5` and `0.5` are
measured, and the table above gives them from the outer exponent
instead.

Probe: `nesting_contribution_rule`, `NESTING_CONTRIBUTIONS`. Two tests.
Audit `PAPER_B_AUDIT_CONSISTENT`; `P_0` unmoved at `3.5858e13`. No
manuscript or certificate edit.

## Lemma 3.7's mass at all ten sites, and where the log powers actually come from

The last entry asked whether Lemma 3.7's coefficient mass is absorbed correctly at the other
places the lemma is used -- it guessed four; there are ten -- given that the window parameter
is `P^(1/2)` at some and `R_0` at others.

**It is, uniformly, and the coefficients are worth printing.** The mass is
`8 + 2 log(2 + |B| + T) + 4 H_J`, so with `|B| = P^beta`, `T = P^tau`, `J = P^iota` the
coefficient of `log P` is `2 max(beta, tau) + 4 iota`:

```text
  site                      |B|              T                J        coeff
  Thm 4.1 St.3(s1)          2.25 P^(-1/16)   P^(1/2)          R_0       9/4
  Thm 4.1 St.3(s2)          2.25 P^(1/4)     P^(1/2)          --          1
  Thm 4.1 St.6(D1)          O(1)             P^(1/2)          --          1
  Thm 4.1 St.6(D2)          1.85 k h P^(1/8) P^(1/2)          R_0       9/4
  Thm 5.3 St.3(a)           (15/8) k h2 P^(1/8)  P^(1/2)/2h1  P^(1/4)  47/24
  Thm 5.3 St.3(b)           1.85 k h1 P^(1/8)    P^(1/2)/2h2  --      11/12
  Thm 5.3 St.5b (j=0)       <= 6             P^(1/2)          --          1
  Thm 6.1 Step E            <= 6             P^(1/2)          --          1
  Thm 6.3 depth five        2 P^(19/96)      R_0              --        5/8
  Lemma 5.2(iii)            5 P^(1/4)        P^(1/2)          --          1
```

Every site is `O(log P)`; the largest coefficient is `9/4` and the smallest `5/8`. The two that
reach `9/4` are exactly the two carrying Stage 2's truncation `J = R_0 = P^(5/16)`, where the
`v`-mass `4*(5/16) = 5/4` outweighs the `b`-mass `1`. So the absorption into `P^epsilon` is
sound and never close to failing.

**And one row is worth reading twice.** Theorem 6.3 carries the paper's largest log power,
`log^(15/4) P`, and has the *thinnest* Lemma 3.7 site of the ten, at `5/8` -- because its
window parameter is `R_0 = P^(5/16)` and not `P^(1/2)`. That log power is therefore not a fat
mass at one site; it is the count of applications at depth five. The two quantities are
independent, and only the second grows with depth. A reader tracing `log^(15/4)` back to a
single lemma invocation would be looking in the wrong place, and the thinnest site in the paper
is the one they would land on.

`decoration_budget.lemma37_site_masses`; the table goes into Section 3 beside the lemma, where
`B` and `T` are the lemma's own letters and no re-lettering is needed.

The count in the question was wrong -- four against ten -- and that is the second time in three
entries that my own estimate of how many sites something touches has been low. Grepping the
lemma's name takes a second and the estimate takes none, which is the wrong trade.

## Nothing is expanded above exponent two, and every remainder constant is a second derivative

The rule predicted that a floor expanded under an outer exponent above
`2` would put its quadratic *above* the lead and need a cubic. Nothing
in the paper does that, and the reason is a choice of variable.

**The kernel's `m^(9/4)` is never expanded as `x^(9/4)` around `m`.** It
is written `Y^(3/2)` and expanded around the floor `v`, which is exactly
what Lemma 5.1(i) is:

```text
  (v + theta_2)^(3/2) = v^(3/2) + (3/2) v^(1/2) theta_2
                                + (3/8) v^(-1/2) theta_2^2 - ...
```

so `(1/2)(m^(9/4) - v^(3/2)) - (3/4) v^(1/2) theta_2 = (3/16) v^(-1/2)
theta_2^2 + ...`, and the printed `0 <= R <= (3/16) v^(-1/2)` is that
quadratic with `theta_2^2 <= 1`. Outer exponent `3/2`, not `9/4`. The
`a > 2` case never arises, and no term anywhere carries a cubic.

**What the check turns up instead.** Every remainder constant in the
family is the same object. With `f(x) = x^a` the first neglected term is
`(1/2) f''(g) theta^2 = (1/2) a(a-1) g^(a-2) theta^2`, so the constant is
`(1/2) a(a-1)` times whatever factor the identity carries outside it:

```text
  site                 outer a   outer factor   (1/2)a(a-1)*factor   printed
  Lem 5.1(i) R           3/2        1/2               3/16            3/16
  Thm 4.8 E              3/2        1                 3/8             3/8
  Lem 6.2 theta term     9/8        1                 9/128           9/128
  Lem 6.2(ii) second     3/2        1                 3/8             3/8
```

Four constants, four second derivatives, no discretion anywhere. And
the ratio each bound carries follows from the same exponent: `theta^2`
with mean `1/3` when `a > 1`, `theta` with mean `1/2` when `a < 1`.

**Lemma 5.1(i) as the fifth measured site.** Its ratio is `theta_2^2` to
`5.19e-4` at worst (at `n = 5`) and `2.31e-9` in the tail; mean
`0.3296` against `1/3`; maximum `0.99959`. Asymptotically exact, like
every other bound in the family.

```text
  the five sites, complete
  Lem 4.6 D        a = 1/2   linear      ratio theta         mean 1/2
  Lem 6.2(i) D_5   a = 1/2   linear      ratio theta         mean 1/2
  Thm 4.8 E        a = 3/2   quadratic   ratio theta_w^2     mean 1/3
  Lem 5.1(i) R     a = 3/2   quadratic   ratio theta_2^2     mean 1/3
  Lem 6.2(ii) D_5' a = 3/2   quadratic   two nestings        mean 23/60
```

Every one is asymptotically exact and every constant is forced. The
single exception in the family remains `6.2(ii)`, and it is not a loose
constant but a second term of the same order, which is the deletion
recorded five passes ago.

Tags. EXACT: `(v + theta_2)^(3/2)` expands to give
`R = (3/16) v^(-1/2) theta_2^2 + ...`, so Lemma 5.1(i) is an outer
exponent `3/2` and not `9/4`; each printed constant equals
`(1/2) a(a-1)` times the identity's outer factor, checked as exact
rationals for all four. COMPUTATIONALLY VERIFIED: Lemma 5.1(i)'s ratio
is `theta_2^2` to `5.19e-4` at worst and `2.31e-9` in the tail, mean
`0.3296`, maximum `0.99959`. OBSERVATION: all five remainder sites in
the family are asymptotically exact, with ratio `theta` or `theta^2`
according to whether the outer exponent is below or above one.

Probes: `remainder_constants_are_second_derivatives`,
`REMAINDER_CONSTANTS`. Two tests. Audit `PAPER_B_AUDIT_CONSISTENT`;
`P_0` unmoved at `3.5858e13`. No manuscript or certificate edit.

## Where log^(15/4) comes from, and whose truncations they are

The last entry asked where Theorem 6.3's `log^(15/4)` comes from and whether it matches the
count of Lemma 3.7 and Lemma 3.5 applications. The manuscript already derives it, which the
question did not know:

```text
  |T_2| << P^(23/24) log^3 P     three expansion layers plus the shift devices
  Weyl step 1: log^(3/2)         the A-process squares, so the square root halves it
  Weyl step 2: log^(3/4)         and again -- this is K_c's power
  Theorem 6.3: + 3 = 15/4
```

`3/4 + 3 = 15/4` exactly, and `3/2/2 = 3/4` exactly. The arithmetic is right.

**What is worth adding is whose the three are.** From Theorem 6.3's own proof:

```text
  Vaaler, fifth wave     J_5 = 2 P^(1/96)                              its own
  Lemma 3.7 window       T = R_0 = P^(5/16) vs |C| <= 1.30 P^(19/96)   its own
  first-letter index     |i| <= 2 P^(1/96)                             Theorem 6.1's
```

Only two are Theorem 6.3's. The third is the first-letter expansion it inherits when it merges
the two indices into `|I_tot| <= 2 P^(5/16)`. Counting it is nevertheless right: `log^(3/4)` is
`K_c`'s power, and Theorem 6.1 is where `K_c` is *applied* rather than proved, so its own
expansion sits on top and is not already inside. The count of three stands; the phrase "its own
truncations" is what is loose, and the manuscript now names all three.

**And it could not matter numerically either way.** Absorption of `log^A P` into `P^(1/96)`:

```text
  A = 3/4    P >= 10^190      (the manuscript's 1.5e190)
  A = 1      P >= 10^268
  A = 11/4   P >= 10^872      the count without the inherited layer
  A = 15/4   P >= 10^1245     the count with it
```

A larger `A` is the *weaker* claim, so the generous count is the safe one, and both are
astronomically outside anything the paper touches. Sections 4-6 carry the `P^epsilon` rather
than spending it, so none of these numbers enters `P_0`.

`decoration_budget.log_power_ledger`, `LOG_POWER_CHAIN`, `THEOREM63_TRUNCATIONS`.

The question assumed the manuscript did not derive `15/4` and asked where it comes from. It
does derive it, in Appendix A.3, two lines after the sentence the question was reading. Third
entry running in which the useful work was not the thing asked for but a smaller thing beside
it -- here, whose truncations they are rather than how many.

## The denominator sorts them: eighteen constants, no exceptions

The question was whether a printed constant can be sorted sharp or loose
by its form alone. On everything this ledger has measured, one rule does
it: **a printed constant is sharp exactly when its lowest-terms
denominator exceeds `1`.**

```text
  site                          printed   den    slack    sharp
  Lem 5.1(i) R                   3/16      16    1.000    yes
  Thm 4.8 E                      3/8        8    1.000    yes
  Lem 6.2 theta term             9/128    128    1.000    yes
  Lem 6.2(i) lead                3/4        4    1.000    yes
  Lem 6.2(ii) lead               3/4        4    1.000    yes
  Lem 4.6 lead                   3/4        4    1.000    yes
  Lem 6.2(ii) second             3/8        8    1.000    yes
  Thm 4.1 St3(s2) B              9/4        4    1.000    yes
  Lem 5.1(iii) bracket 1 lower   3/2        2    1.000    yes
  Lem 5.1(iii) bracket 1 upper  13/5        5    1.031    yes
  Lem 5.1(iii) bracket 2 upper   15         1    1.868    no
  Lem 5.1(iii) G' offset          2         1    1.778    no
  Lem 5.1(iii) G' curvature      20         1    3.951    no
  Lem 5.1(iii) G'' offset         2         1    7.111    no
  Lem 5.1(iii) G'' curvature     25         1    2.822    no
  Lem 5.1(iii) run length        22         1   13.037    no
  Lem 5.2(iii) widened            5         1    1.250    no
  Thm 5.3 j=0 anchor              6         1    2.370    no
```

Eighteen for eighteen. The reason is editorial rather than
arithmetical: a constant written *as derived* --- a Taylor coefficient
`(1/2) a(a-1)`, a mean-value factor `3/2`, a product of them like `9/4`
--- keeps its denominator; a constant that collects several terms and is
then rounded up so the page reads cleanly becomes an integer. The
denominator is a proxy for "written as derived or rounded for the
reader", and that is what actually separates the two families.

**Three cautions, all of them real.**

The rule has a counterexample in the paper, which the paper itself
removes. The `j = 0` anchor constant is derived as `5.3` --- denominator
`10`, loose by `2.09` --- and then "opened to `6`". Read at `5.3` the
rule fails; read at the constant the proof carries, `6`, it holds. A
dyadic refinement (denominator a power of two above `1`) repairs that
case and breaks the bracket's `13/5 = 2.6`, which has denominator `5`
and is sharp to `1.031`. Neither refinement is free: `18/18` for the
plain rule, `17/18` for the dyadic one.

The two families are separated but not widely at the boundary: the
worst sharp constant is `1.031` and the best loose one `1.250`, a gap of
`1.21`. A constant rounded only slightly would land between them.

And sharpness is not the same as being needed. Lemma 6.2(ii)'s second
term is `3/8`, denominator `8`, attained --- and deletable, because what
it bounds is a difference already covered by the other term. The rule
sorts constants by whether they are tight, not by whether they earn
their place.

So the tell is real and it is a proxy. Used as a triage it would have
found every loose constant in this paper without a single measurement,
and it would also have flagged one term that is tight and unnecessary
--- which no measurement of that term alone would have caught either.

Tags. EXACT: the eighteen printed constants and their lowest-terms
denominators; the plain rule agrees with measured sharpness at all
eighteen, the dyadic refinement at seventeen, missing `13/5`.
COMPUTATIONALLY VERIFIED: the slacks in the table, from the sharpness
sweeps of the previous six passes and, for the two bracket constants,
`0.9703` and `0.5354` of their printed uppers over `160` samples.
OBSERVATION: worst sharp `1.031` against best loose `1.250`, a boundary
gap of `1.21`; `5.3` before opening is the rule's one counterexample in
the paper.

Probes: `constant_form_predicts_sharpness`, `MEASURED_CONSTANTS`. Two
tests. Audit `PAPER_B_AUDIT_CONSISTENT`; `P_0` unmoved at `3.5858e13`.
No manuscript or certificate edit.

## Out of sample the rule gets one of two, and the miss has a shape

The eighteen constants the denominator rule was fitted on were all
measured because something had drawn attention to them. This is the test
it did not get to choose: two printed constants nothing in this ledger
had measured, predicted from their form and then measured.

**`0.64`, in `|u A_h''| <= 0.64 u h^2 P^(-7/4)`. Denominator `25`, so:
sharp. Correct.** The true coefficient is exact and rational:
`A_h = -(27/8) h^2 nu^(1/4)` to leading order, so
`A_h'' = (81/128) h^2 nu^(-7/4)`, and the measured ratio to
`(81/128) h^2 P^(-7/4)` is `1.00000` at every `(P, h)` from `1e5` to
`1e8`. Printed `0.64` against `81/128 = 0.632812` is a slack of
`1.0114`.

**`1.5`, in the gap-cell count `1.5 h P^(1/2) + 1`. Denominator `2`, so:
sharp. Wrong.** The measured count is `0.8289` of the printed bound,
stable across `P` from `1e5` to `1e6` and `h` from `1` to `3`: a slack
of `1.206`.

The true count is the range of
`delta_h(nu) = (nu+2h)^(3/2) - nu^(3/2)` over a dyadic block, which runs
from `3h P^(1/2)` to `3h (2P)^(1/2)`, so it is

```text
  3(sqrt2 - 1) h P^(1/2)  =  1.242641 h P^(1/2)
```

and `0.8289 * 1.5 = 1.24332` confirms it.

**So the rule is `1/2` out of sample, `19/20` overall, and the failure
has a shape: the true constant is irrational.** `3(sqrt2 - 1)` has no
denominator to keep, so the printed number is a round-up to the nearest
convenient rational --- and `3/2` is exactly the kind of simple fraction
the rule reads as derived. The denominator separates "written as
derived" from "rounded" only when the derivation lands on a rational;
where a block endpoint contributes a `sqrt2`, a simple fraction is a
rounding like any integer.

That is worth more than the `18/18` was. The rule survives as triage
with a stated blind spot: **constants whose derivation crosses a dyadic
block boundary.** Every one of the eighteen it was fitted on is a
pointwise Taylor coefficient, evaluated at a point; this one is a range
over a block, and the block's two ends bring in `2^(1/2)`.

It is also a reminder about the shape of this ledger's evidence. Six
passes of sharpness sweeps produced a rule that fit everything it had
seen, and the first constant chosen without regard to whether it looked
interesting broke it. The eighteen were not a sample of the paper's
constants; they were a sample of the ones that had already caught
attention.

Tags. EXACT: `A_h'' = (81/128) h^2 nu^(-7/4)` from
`A_h = -(27/8) h^2 nu^(1/4)`, so `0.64` is a rounding by `1.0114`; the
cell count is `3(sqrt2 - 1) h P^(1/2)` from the range of `delta_h` over
a dyadic block, so `1.5` is a round-up by `1.2071`. COMPUTATIONALLY
VERIFIED: the curvature coefficient measures `0.6328125` at every
`(P, h)` from `1e5` to `1e8`; the cell ratio is `0.8283` to `0.8289`
across `P` from `1e5` to `3e6` and `h` from `1` to `3`, and
`0.8289 * 1.5` recovers `3(sqrt2 - 1)`. OBSERVATION: the rule is `1/2`
out of sample and `19/20` overall; its blind spot is a derivation that
crosses a block boundary.

Probe: `out_of_sample_constant_test`. Two tests. Audit
`PAPER_B_AUDIT_CONSISTENT`; `P_0` unmoved at `3.5858e13`. No manuscript
or certificate edit.

## The manuscript against itself

Every audit built here compares the manuscript with something outside it. The last entry
observed that three of this audit's findings were of a different kind -- the `0.35`
conflation, the interpolant chain that kept the constants its own lemma's erratum had
replaced, and a log count attributed to the wrong theorem -- and asked what a
manuscript-against-itself check would look like, and whether a tractable subset exists.

**The obvious check has a hundred percent false-positive rate**, which is the finding that
shapes the rest. Named constants are printed many times; do the printings agree?

```text
  P_0    3.6e13                                    7 occurrences, one value
  P_1    9.8e18                                    2 occurrences, one value
  c_7    1/232, 1/288, 1/61, 1/54                 10 occurrences, four values
  kappa  1/12, 1/16                                3 occurrences, two values
  R_0    5/16, 1/4                                20 occurrences, two values
```

Every multiplicity is legitimate. `1/288` is the weaker `c_7` the manuscript keeps on purpose;
`1/61` and `1/54` are where the lever saturates, before and after the Lemma 5.2b erratum;
`1/16` is a row of the kappa sweep; `1/4` is the superseded truncation, discussed at length.
So the check has to be a *declared* one: canonical value plus alternatives with reasons, and a
value outside the list is the failure. That is what a figure left behind after a correction
would look like, and it is what the guard now watches for.

**The other direction is where the real hazard lives.** A value naming more than one quantity:

```text
  0.35   Thm 4.1's Stage-4 curvature; Lemma 5.2b's pre-correction lambda_0 floor
  0.11   the smooth remnant |c''|, hence E's second term;
         the collision band's lower edge 0.11 uh P^(-1/4);
         Step 5a's ratio V/S <= 0.11 P^(-7/48) at S >= 0.60 P^(-5/8)
  1.2    the Stage-4 curvature's upper end [0.35, 1.20];
         the (s2) window length >= 1.2 P^(3/4); Step 5's cell sum 1.2 R^(1/2) Y' P^(-1/4)
  1.5    the cell count 1.5 h P^(1/2) + 1; the offset term's floor (3/2)|j|P^(3/4)
```

`0.35` is the one that cost an afternoon, and it was the only one the manuscript distinguished
-- implicitly, in Appendix A.1's remark that two certificate rows divide by the Stage-4
curvature rather than by the anchor. `0.11` names three unrelated quantities and carried no
warning at all; nor did `1.2` or `1.5`.

None of them is an error and none is avoidable by renaming: each constant is what its own
derivation produces. What is avoidable is reading across them. The table is now printed in
Appendix A.1 beside the `sqrt_0_35_lower` remark, and `tools/manuscript_self_audit.py` keeps
it current -- a numeral acquiring a new role has to be added, and a value leaving the table
fails the suite. Two tests demonstrate both guards firing: one deletes the table, one stales
`P_0` to its pre-erratum `8.9e13`.

The tractable subset the question asked for turns out to be the second direction, not the
first. The first needs a hand-written exception for every legitimate multiplicity and catches
only staleness; the second is a short closed list and catches the error that has actually
happened here.

## One opened constant reaches `P_0`, and it is worth a quarter of it

The block-range constants of the last pass reach no row that matters:
`1.5` for the cell count appears in no certificate row at all, `2.6` and
`15` are bracket endpoints the certificate does not cite, and `4.3`
feeds only `5b-j0-window` at `3136`. But the search for them turned up
one that does reach `P_0`.

**Lemma 5.2b's anchor range is `[0.62, 3.90]` and the proof opens it to
`[0.56, 4.2]`.** The opening is not slack in principle: the row
`5b-lam0-range` asks for

```text
  lam_exact_hi (1 + P^(-1/4))(1 + 1/(3 sqrt P))^2 <= lam_hi
  lam_exact_lo (1 - P^(-1/4))(1 - 1/(3 sqrt P))^2 >= lam_lo
```

so the finite-`P` corrections need room at both ends. At `P_0` they need
almost none:

```text
  high end   3.90 -> 3.901594    printed 4.2     opened 1.0765 beyond the need
  low  end   0.62 -> 0.619747    printed 0.56    opened 1.1067 beyond the need
```

**The low end reaches `P_0`,** through `S_5b = lam_lo P^(-5/8)` in the
binding row `5b-W<=c7S`:

```text
  lam_lo    P_0          binding row
  0.5600    3.5858e13    5b-W<=c7S      as printed
  0.5800    3.2251e13    5b-W<=c7S
  0.5900    3.0630e13    5b-W<=c7S
  0.6000    2.9117e13    5a-W<=c7S      the plateau begins
  0.6100    2.9117e13    5a-W<=c7S
  0.6197    2.9117e13    5a-W<=c7S      the correction's own limit
```

A factor **`1.2315`**, and then the binding row passes to Step 5a, whose
own constant `S >= 0.60 P^(-5/8)` is the next opening in line --- and one
whose exact value the certificate does not carry, so this is where the
gain stops without more information.

The high end does not reach `P_0` at all: `lam_hi` enters `V` and not
the comparison that binds, and tightening it to `3.902` leaves the
threshold where it was.

So the answer to the question is yes, on the second attempt: there is a
rounded constant where a factor of `1.2` matters, and it is the constant
in the row that sets the threshold. Every other rounding this ledger has
priced was worth nothing to `P_0`; this one is worth `23%` of it.

*What this is and is not.* The opening is deliberate --- the manuscript
records `[0.35, 2.6] -> [0.56, 4.2]` as an opening of
`[0.38, 2.44] -> [0.62, 3.90]` --- and a proof is entitled to round its
own constants for legibility. What the measurement says is only what the
legibility costs: `23%` of `P_0`, against corrections that need `0.04%`.
Whether to spend it is the author's call. The certificate is untouched
and still reports `3.5858e13`.

Tags. EXACT: the range row's two conditions, and the values they need at
`P_0`, `0.619747` and `3.901594`, against the printed `0.56` and `4.2`;
`lam_hi` does not enter the binding comparison. COMPUTATIONALLY
VERIFIED: the `lam_lo` sweep above; `P_0` falls to `2.9117e13` for every
`lam_lo` in `[0.60, 0.6197]`, a factor `1.2315`, with the binding row
passing to `5a-W<=c7S`; tightening `lam_hi` to `3.902` moves nothing.
OBSERVATION: the plateau means the gain is capped by Step 5a's own
opened constant `0.60`, whose exact value is not in the certificate.

Probe: `anchor_opening_reach`. Two tests. Audit
`PAPER_B_AUDIT_CONSISTENT`; `P_0` unmoved at `3.5858e13` --- nothing in
the certificate is edited. No manuscript edit.

## Step 5a's constant is a block range too, opened wider than 5b's, and the pair is worth `1.357`

The certificate carries no exact value for Step 5a's
`S >= 0.60 P^(-5/8)`. The manuscript does. The offset composite is

```text
  lambda_0' = (2187/2048) k h_1h_2 nu^(-5/8),    2187/2048 = 3^7/2^11 = 1.067871
```

and over a dyadic block `nu^(-5/8)` runs from `P^(-5/8)` down to
`2^(-5/8) P^(-5/8)`, so the coefficient lies in

```text
  [2^(-5/8), 1] * 2187/2048  =  [0.692429, 1.067871]
```

which is exactly the `(0.6924, 1.0679]` the erratum states. It is
printed as `[0.60, 1.25]`.

**So Step 5a's constant is a block-range constant, like the cell
count's `1.5`, and it is opened wider than 5b's:**

```text
  low end    0.692429  printed 0.60    opening 1.1540   (5b's 1.1067)
  high end   1.067871  printed 1.25    opening 1.1706
```

That is the family from two passes ago arriving at the threshold. Both
constants that reach `P_0` are block ranges rounded outward, and the
rounding is the whole of the gap.

**Priced together, against the whole certificate:**

```text
  lam_5b   lam_5a    P_0          binding
  0.5600   0.6000    3.5858e13    5b-W<=c7S     as printed
  0.6000   0.6000    2.9117e13    5a-W<=c7S     5b closed
  0.6000   0.6921    2.9117e13    5b-W<=c7S     they alternate
  0.6197   0.6921    2.6419e13    5b-W<=c7S     both closed
  0.6197   1.0000    2.6419e13    5b-W<=c7S     nothing further
```

A factor **`1.3573`**, from `3.5858e13` to `2.6419e13`. The two rows
alternate as each is closed, and past `0.6921` the gain saturates ---
raising 5a to `1.0` buys nothing --- which is what makes `2.6419e13` the
floor of this lever rather than an arbitrary stopping point.

So the `P_0` this paper reports is `1.36` times the one its own exact
constants support, and the whole difference is two outward roundings of
two block ranges. Neither is an error: the printed ranges contain the
exact ones, every row still holds, and the certificate is untouched at
`3.5858e13`. What the measurement adds is the price.

Tags. EXACT: `lambda_0' = (2187/2048) k h_1h_2 nu^(-5/8)` gives the block
range `[2^(-5/8), 1] * 2187/2048 = [0.692429, 1.067871]`, matching the
manuscript's `(0.6924, 1.0679]`; the printed `[0.60, 1.25]` opens it by
`1.1540` and `1.1706`. COMPUTATIONALLY VERIFIED: the five-row sweep
above; `P_0` falls to `2.6419e13` with both closed, a factor `1.3573`;
the gain saturates, since `lam_5a = 1.0` gives the same `P_0` as
`0.6921`. OBSERVATION: the two constants that reach `P_0` are both block
ranges rounded outward, which is the family the cell-count miss
identified two passes ago.

Probe: `step_5a_opening_reach`. Two tests. Audit
`PAPER_B_AUDIT_CONSISTENT`; `P_0` unmoved at `3.5858e13`. No manuscript
or certificate edit.

## Generating the shared-value list, and the two rows it agrees with by luck

The last entry curated four shared values by eye and asked whether the list could be generated
instead -- clustering each numeral's occurrences by the surrounding symbols.

**It can, partly, and the discriminator is what the numeral multiplies.** `0.11 k P^(-7/8)`
and `0.11 uh P^(-1/4)` fall into different clusters; a numeral with two clusters is a
candidate. Restricting to math mode removes section numbers and prose cross-references
("Theorem 4.7", "Section 1.2 Related work") at a stroke, which the first prototype did not and
which drowned it.

Of 356 math-mode decimals, 14 are flagged and three survive inspection:

```text
  0.11   uhP^(-1/4) | P^(-5/6) | kP^(-7/8)     three roles, already curated
  1.1    P^(17/32)  | uP^(3/4) | C             three roles, NOT curated
  1.2    Y'         | k                        a fourth role, NOT curated
```

**`1.1` names three constants** -- the (s2) window-boundary cost `1.1 P^(17/32)`, which is
`0.65/sqrt(0.35) = 1.0987`; Theorem 4.4's Lemma 3.3 sum `1.1 u P^(3/4)`; and Step 5b's good
pieces `(1.1 C(E) S)^(1/2)`. Three independent derivations rounding to the same two figures,
and no warning anywhere. **`1.2` has a fourth role**, the cross-coefficient bound
`45/64 + 9/32 = 63/64 <= 1.2`. Both found by the generator, both missed by eye.

**And the generator agrees with two of the curated rows by luck.** It flags `0.35` and `1.5`,
but the clusters it splits there are `0.35 uhP^(-3/4)` against `(0.35 uh)^(-1/2)`, and
`1.5 hP^(1/2)` against `1.5 hY'` -- two notations for one quantity in each case, not two
quantities. The roles that actually make them collisions are precisely what a check reading
*what a numeral multiplies* cannot see: `0.35`'s second is the endpoint of a bracket,
`[0.35, 2.6]`, which multiplies nothing, and `1.5`'s is written `3/2`.

So the two methods miss opposite things and neither replaces the other. Curation sees a role in
any notation but only where someone looked; clustering sees every occurrence but only where the
role multiplies something. The list is now kept by both, the manuscript says which rows are
coincidence, and `cluster_coverage` reports `genuinely_detected` separately from `flagged`.

One process note. Writing the tool's comment through a heredoc turned `\tfrac32` into a literal
tab, inside a sentence explaining that `1.5`'s second role is written as a fraction. Fourth
time this session the escape hazard has bitten, and the first time it has corrupted the very
example it was describing.

## The opening is slack in the lever, not in the threshold --- and the `1.357` was measured past the cliff

The previous section priced the two anchor openings at a factor `1.357`
on `P_0` and left it there. The figure is right and the reading was
incomplete. Closing the opening also raises the threshold of the row
that licenses it, `5b-lam0-range`, and that row is what the `c_7` lever
runs into.

**The floor first.** Taking `c_7` to `1` --- the whole lever spent ---
and asking what `P_0` remains:

```text
  lam_5b    P_0          floor at c_7 -> 1   lever    floor row
  0.5600    3.5858e13    2.9817e11           120.26   st5b-qpp     as printed
  0.5900    3.0630e13    2.9817e11           102.73   st5b-qpp
  0.6000    2.9117e13    2.9817e11            97.65   st5b-qpp
  0.6150    2.7031e13    2.9817e11            90.66   st5b-qpp
  0.6190    2.6509e13    2.9817e11            88.91   st5b-qpp
  0.6197    2.6419e13    1.8266e13             1.45   5b-lam0-range
```

So the floor is the Step 5b(a) `q''` row at `2.98e11`, not `5b-E<=c7S`
at `4.10e12` --- `5b-E` mentions `c_7` and vanishes with the lever, so
it was never a floor. That answers the question as asked.

**And the floor is fixed, which makes the trade exact.** For every
`lam_lo` up to about `0.619` the floor does not move, so the lever falls
by *exactly* the factor `P_0` falls by: the safe gain `1.3526` costs
`1.3526` of lever, `120.3` down to `88.9`. Nothing is gained on one side
that is not lost on the other.

**Then there is a cliff.** The range row's own threshold climbs steeply
as the opening closes:

```text
  lam_lo   0.600     0.610     0.615     0.619     0.6195    0.6197
  least P  1.00e6    1.54e7    2.41e8    1.48e11   2.37e12   1.83e13
```

crossing the `q''` row's `2.98e11` between `0.619` and `0.6195`. Past
that the range row is the floor and the lever collapses to `1.45`.

**Which is where the previous section measured.** Its `1.3573` is at
`lam_lo = 0.6197`, beyond the crossing. The usable figure is `1.3526` at
`0.619`, and it is not free: it is the lever, spent.

So an opening is not slack in the threshold. It is slack in the
*lever* --- room held for the paper's other constants to improve later.
A proof that rounds its constants outward is buying that room, and the
price of closing it is not `1.36` of `P_0` but `26%` of the lever, and
then a cliff a thousandth of the way further on.

Tags. EXACT: `5b-E<=c7S` mentions `c_7`, so it vanishes as the lever is
spent and cannot be the floor; with the floor fixed, the lever falls by
exactly the factor `P_0` falls by. COMPUTATIONALLY VERIFIED: the
six-row table above; the floor is `2.9817e11` (`st5b-qpp`) for every
`lam_lo <= 0.619` and `1.8266e13` (`5b-lam0-range`) at `0.6197`; the
range row's thresholds `1.00e6` to `1.83e13` across the same range;
`safe_gain = lever_cost = 1.3526`. OBSERVATION: the crossing sits
between `0.619` and `0.6195`, so the last thousandth of the opening
carries the entire lever.

*Correction.* The previous section's `1.3573` is measured at
`lam_lo = 0.6197`, past the crossing, where the lever is already gone.
Its arithmetic stands; its conclusion --- that the reported `P_0` is
`1.36` times what the exact constants support --- should read that the
paper trades that `1.36` for a lever of `120` against a fixed floor.

Probe: `opening_versus_lever`. Two tests. Audit
`PAPER_B_AUDIT_CONSISTENT`; `P_0` unmoved at `3.5858e13`. No manuscript
or certificate edit.

## The floor row's own constant is a third opened block range, and the lever is `739`

The lever runs into `st5b-qpp`. Two things about that row.

**Its text and its predicate are different bounds.** The claim reads
`|q''| curvature ratio 48.9 P^(-3/16) <= 1/4`, which clears at
`1.662e12`. The predicate is the two-term form

```text
  (1.85 P^(7/24) + R_0) * 6 P^(-5/4) / (0.35 P^(-3/4))  <=  1/4
```

which clears at `2.982e11`. Both are true, and the manuscript discusses
the difference --- merging the two terms "loses `P^(1/48)`" --- but the
row certifies the sharp form and describes the merged one, a factor
`5.574` apart. Anyone checking the printed claim against the printed
threshold finds them inconsistent, in the safe direction.

**And the `0.35` in it is an opened block range.** The Stage-4 curvature
is `-(9/32) u G (nu+2h)^(-5/4)` with `G ~ 3h nu^(1/2)`, so the
coefficient is `(27/32) u h nu^(-3/4)`, and over a dyadic block
`nu^(-3/4)` runs over `[2^(-3/4), 1]`:

```text
  true      (27/32)[2^(-3/4), 1]  =  [0.50170, 0.84375]
  printed                            [0.35,    1.20   ]
  opening                             1.4334    1.4222
```

Measured at `[0.50364, 0.82385]` over `80` samples --- the low end at
once, the high end from below, since it is attained only as `nu -> P`.
That is the third block range in the paper found rounded outward, after
the two anchor ranges.

**What it costs is larger here than anywhere else,** because the
curvature sits in a denominator under a `P^(-1/2)`: a `1.43` on the
constant is a `6.14` on the threshold.

```text
  curvature   qpp row clears at
  0.35        2.982e11    as printed
  0.5017      4.854e10    the block-range low end
  0.84375     3.542e09    at nu = P
```

**So the floor of the `c_7` lever is `4.854e10`, not `2.982e11`, and the
lever is `738.7` rather than `120.3`.** The previous section's relative
arithmetic is unaffected --- the floor is fixed, so closing the anchor
opening still costs exactly the factor it takes off `P_0` --- but the
lever it was spending is six times larger than stated, and so is every
figure in this ledger that used `120`.

The pattern is now three for three: every constant that reaches `P_0`
or its floor is a block range rounded outward. The cell count was the
first, found by an out-of-sample test; the two anchor ranges were the
second and third; this is the fourth, and the only one where the
rounding is amplified rather than passed through.

Tags. EXACT: the Stage-4 curvature coefficient is `(27/32) u h nu^(-3/4)`
from `-(9/32) u G (nu+2h)^(-5/4)` with `G ~ 3h nu^(1/2)`, so its block
range is `[0.50170, 0.84375]`; the row's claim text and predicate are
different inequalities, clearing at `1.662e12` and `2.982e11`.
COMPUTATIONALLY VERIFIED: measured range `[0.50364, 0.82385]` over `80`
samples; the qpp row clears at `2.982e11`, `4.854e10` and `3.542e09` at
curvature `0.35`, `0.5017` and `0.84375`; the floor moves by `6.143` and
the lever from `120.26` to `738.73`. OBSERVATION: the amplification is
the `P^(-1/2)` the ratio carries, which turns a `1.43` into a `6.14`.

Probe: `qpp_row_and_the_floor`. Two tests. Audit
`PAPER_B_AUDIT_CONSISTENT`; `P_0` unmoved at `3.5858e13`. No manuscript
or certificate edit.

## Reading the paper as arithmetic: eighty relations, one wrong, and a rounding convention nobody had stated

*Mathematical target.* Every previous audit here compares the
manuscript with something outside it --- Lean, the probes, the
certificate --- or with itself by *name*: a constant printed with two
values, a value naming two constants. None had asked the blunt
question. Take every relation the paper prints between numbers and
evaluate both sides.

*Novelty hypothesis.* The clusterer's blind spot is notation: it reads
`1.5` and `\tfrac32` as unrelated strings. A normaliser sending every
literal to a rational removes that, and answers a question nobody had
asked --- how many of the paper's constants are exact rationals printed
as decimals, and is any decimal printed inconsistently with its own
exact value?

*Falsifier.* Every relation checks out, in which case the normaliser is
a guard and not a finding.

*Existing machinery.* `_MATH`, `_split_top`, `paper_text` from
`manuscript_self_audit`; the exclusion-anchor pattern from the
shared-value table.

*Prior art.* `docs/negative_knowledge.md` has nothing on numeral
normalisation; `conjectures/refuted/` nothing; the ledger's own
shared-value entry is the nearest neighbour and explicitly notes that
the clusterer cannot see across notations.

**Result.** Eighty relations. Fifty-four exact --- including all of
Section 5's fraction algebra, `945/512-81/512=864/512`,
`675/2048-432/2048=243/2048`, `11/12-29/32=1/96`, `-365/176=-730/352`,
`27/16=864/512`. Not one arithmetic slip anywhere in it. Twenty-three
correctly rounded. One quoted in units of `10^{-4}`
(`7/5800=12.0690`), declared as an exception because the units are
stated in prose, outside the math span.

**The error.** Claim D's shift range printed its threshold `1.45^{36}`
as `1.1e6`. The value is `644537`, and Appendix A.1's own row for that
comparison already read `6.4e5`. The prose contradicted the table it
was summarising. Both figures sit far under `P_0 = 3.5858e13`, so
nothing downstream moves --- which is why it survived. Corrected in
place to `6.4\cdot10^{5}`, with the row A.1 prints for it named.

**The convention.** Two decimals are neither exact nor
nearest-rounded: `(1.20)^{1/2}=1.096` (nearest `1.095`) and
`1.5\cdot(0.35)^{-1/2}=2.536` (nearest `2.535`), both in the Stage 4
cell-sum display. Both are rounded *up*, and both feed upper bounds
(`1.1 (uh)^{1/2}P^{5/8}` and `2.6 (h/u)^{1/2}P^{7/8}`), so both are
rounded away from the inequality they serve. That is the safe
direction and it is the paper's practice throughout, but it had never
been written down as a claim, and so had never been checked.

It is worth checking because the unsafe direction is invisible to every
other test here. A decimal rounded *into* its own bound sits within a
unit of the last place, agrees with its constant to the precision
anyone would compare at, and is still a claim the line does not
support. `classify_equality` separates `bounded_up` from
`bounded_down`; `failures()` now carries a `rounded_into_a_bound` key,
and it is empty.

*Coverage.* The pure-number lines are few. Most of the displayed
algebra is a numeral times symbols, so `leading_literal` splits each
side into its numeric head and symbolic tail and compares the heads
when the tails agree: that is what raised the count from 72 to 80 and
what exposed the `1.096`, whose precision the first version read off
the whole side (four significant figures became one, and it passed as
"rounded" for no reason at all).

Tags. EXACT: the fifty-four identities, and `1.45^{36}=644537`.
COMPUTATIONALLY VERIFIED: the eighty-row census, `54/23/2/1`; the two
outward roundings and their gaps `+5.5e-4` and `+5.4e-4`, each under
its `1e-3` last place. OBSERVATION: outward rounding is a convention,
not a theorem --- two instances is not a proof that the paper never
rounds inward, only that it has not yet.

Probe: `manuscript_self_audit.to_expression`, `to_rational`,
`leading_literal`, `classify_equality`, `numeric_relations`,
`rounding_directions`, `wrong_relations`. Twelve new tests, twenty-five
in the file. Manuscript edit: the Claim D correction, and a passage in
the appendix stating the convention --- excluded from its own scan, as
the shared-value table is. `P_0` unmoved at `3.5858e13`. No
certificate edit.

## No shared opening --- but the width reads off the exponent, and one of the three is not a block range

**There is no single number behind the openings.** Across the three
ranges and the cell count they run:

```text
  Stage-4 curvature   low 1.4334   high 1.4222
  Step 5a anchor      low 1.1540   high 1.1706
  Step 5b anchor      low 1.1071   high 1.0769
  cell count          1.2071  (a count, not a range)
```

from `1.077` to `1.433`, with no shared value. The premise of the
question --- that they were "all `1.43` except the cell count's `1.21`"
--- is wrong: only the curvature sits at `1.43`, and the two anchors are
near `1.1`. Whatever the openings are, they are not one editorial habit
with one number behind it.

**What is shared is the mechanism, and it leaves a signature.** A
quantity carrying `nu^(-e)` has, over a dyadic block, a range of width
exactly `2^e`:

```text
  Stage-4 curvature   nu^(-3/4)   width 1.681793 = 2^0.75000    exact
  Step 5a anchor      nu^(-5/8)   width 1.542211 = 2^0.62500    exact
  Step 5b anchor      nu^(-5/8)   width 6.290323 = 2^2.65313    not a block range
```

So the width reads the exponent off directly --- and it says **Step 5b's
`[0.62, 3.90]` is not a block range.** Its quantity carries the same
`nu^(-5/8)` as Step 5a's, so a block range would be `1.5422` wide; the
printed exact range is `4.079` times that. Whatever else varies in it is
not the block. This ledger has been calling it a block range for two
sections; only two of the three are.

**And one opening is inherited rather than chosen.** The erratum states
the relation: `0.56 = 0.35 * 8/5` exactly. The 5b pair is the `8/5`
rescaling of an older printed pair `[0.35, 2.6]`, with `2.6 * 8/5 = 4.16`
rounded up again to `4.2`. So its openings are a superseded printing's,
carried through a correction --- which is why they match nothing else.
The `0.35` in that older pair is the same numeral as the Stage-4
curvature's low end, and the manuscript flags it: "the two constants
share a value and nothing else."

So the answer is three negatives and one positive. No shared opening; no
`sqrt2` behind them; `5b` is not the kind of object the last two
sections took it for. What survives is that a printed range's width,
divided by `2^e`, says whether it is a pure block range --- a one-line
test that needs no measurement and that would have caught the `5b`
misreading immediately.

Tags. EXACT: a quantity carrying `nu^(-e)` has block-range width `2^e`;
the Stage-4 curvature's width is `2^(3/4)` and Step 5a's `2^(5/8)`,
both exactly; Step 5b's is `2^2.653`, so it is not a block range, and it
is `4.079` times its block; `0.56 = 0.35 * 8/5` and `2.6 * 8/5 = 4.16`.
COMPUTATIONALLY VERIFIED: the six openings `1.4334`, `1.4222`, `1.1540`,
`1.1706`, `1.1071`, `1.0769`, and the cell count's `1.2071`; the widths
above. OBSERVATION: `5b`'s openings are inherited from a superseded
printing through the `8/5` correction, so they are not comparable with
the others.

*Correction.* The previous two sections call Step 5b's `[0.62, 3.90]` a
block range. It is not; the openings priced there are unaffected, since
they were measured against the stated exact endpoints and not against a
block model, but the description is wrong.

Probe: `block_range_widths`, `BLOCK_RANGES`. Two tests. Audit
`PAPER_B_AUDIT_CONSISTENT`; `P_0` unmoved at `3.5858e13`. No manuscript
or certificate edit.

## The factor four is the block ends apart, in the row that sets `P_0`

Neither `k h_1h_2` nor `|j|+1`. Lemma 5.2b's anchor is

```text
  lambda_0 = (27/128) k beta_1 beta_2 nu^(-13/8),    beta_i ~ 3 h_i nu^(1/2)
```

and the two factors live at the same `nu`. Charged there,
`beta_1beta_2 nu^(-13/8)` is `9 h_1h_2 nu^(-5/8)` and the range over a
dyadic block is

```text
  (27/128)(9) [2^(-5/8), 1]  =  [1.230984, 1.898438]     width 2^(5/8) = 1.5422
```

Charged apart --- `beta_1beta_2` over its own block range
`[9, 18] h_1h_2 P`, `nu^(-13/8)` over its own `[2^(-13/8), 1]` --- it is

```text
  (27/128)[9 * 2^(-13/8), 18]  =  [0.6155, 3.7969]       width 2 * 2^(13/8) = 6.1688
```

which is the printed exact range `[0.62, 3.90]`, rounded outward. The
ratio of widths is `2 * 2^(13/8 - 5/8) = 2 * 2 = 4` **exactly** --- the
`4.079` the width test measured last section.

**So this is the "block ends apart" loss again,** the same one behind
`|G'|`'s `20` against `81/16` and `|G''|`'s `25` against `567/64`. Four
sites now, and this one is in the row that sets `P_0`. Step 5a's range
is clean: its width is `2^(5/8)` exactly, so it is already charged at one
point.

**What co-locating is worth,** with Step 5a's opening closed alongside:

```text
  5b range                 5a lam     P_0          binding
  printed                  0.6000     3.5858e13    5b-W<=c7S
  printed                  0.6921     3.5858e13    5b-W<=c7S
  co-located [1.20, 1.95]  0.6000     2.9117e13    5a-W<=c7S
  co-located [1.20, 1.95]  0.6921     1.8971e13    5a-W<=c7S
```

A factor **`1.8902`** --- better than the `1.3573` the two openings alone
were worth, because co-location roughly doubles `S` in the binding
comparison rather than nudging it. The printed pair `[1.20, 1.95]`
leaves the range row room at both ends from a low `P`.

That is the largest single movement of `P_0` this ledger has priced, and
unlike the openings it is not a matter of taste: charging two factors of
one product at opposite ends of the same block is a loss, not a
rounding, and the manuscript's own erratum machinery is what makes the
exact range recoverable.

```text
  the four block-ends-apart sites, in one place
  Lem 5.1(iii) |G'|  curvature    20      81/16     3.95
  Lem 5.1(iii) |G''| curvature    25      567/64    2.82
  Thm 5.3 j=0 anchor              5.3     81/32     2.09
  Lem 5.2b lambda_0 range         width   width     4.00   <- reaches P_0
```

Tags. EXACT: `lambda_0 = (27/128) k beta_1beta_2 nu^(-13/8)` with
`beta_i ~ 3 h_i nu^(1/2)` gives the co-located range
`(27/128)(9)[2^(-5/8), 1] = [1.230984, 1.898438]` of width `2^(5/8)`;
charging the two factors at opposite block ends gives
`[0.6155, 3.7969]` of width `2 * 2^(13/8)`, and the ratio is exactly
`4`; Step 5a's width is `2^(5/8)`, so it carries no such loss.
COMPUTATIONALLY VERIFIED: the apart range matches the printed exact
`[0.62, 3.90]` to a rounding; the four-row grid above; `P_0` falls to
`1.8971e13`, a factor `1.8902`, binding on `5a-W<=c7S`. OBSERVATION:
this is the fourth block-ends-apart site and the only one that reaches
`P_0`.

Probe: `lambda0_range_is_block_ends_apart`. Two tests. Audit
`PAPER_B_AUDIT_CONSISTENT`; `P_0` unmoved at `3.5858e13` --- the
certificate is untouched. No manuscript edit.

## A threshold is not a measurement: A.1's column, three stale rows, and the direction rule I got backwards

*Mathematical target.* For every decimal printed in place of an exact
value, decide whether the rounding falls on the safe side of the
inequality it serves. Last tick asked only whether a decimal was
*nearest*, which is the wrong question: a nearest rounding can be
downward, and a downward rounding inside an upper-bound chain makes the
printed derivation bound a smaller quantity than the truth.

*Novelty hypothesis.* Some of the twenty-three nearest-rounded decimals
are rounded down inside upper chains, and every existing check passes
them.

*Falsifier.* All are up-or-exact, or the chains are `=`-only and
direction is undeterminable.

*Existing machinery.* `_split_top`, `classify_equality`,
`leading_literal`, `numeric_relations`; `p0_certificate.thresholds`.

*Prior art.* `docs/negative_knowledge.md` and `conjectures/refuted/`
have nothing on rounding direction. The nearest neighbour is this
ledger's own previous entry, which states the question and leaves it
open.

**The rule I had backwards.** The naive reading --- upper chains round
up, lower chains round down --- is wrong, and the paper contains four
cases that look like violations under it and are not. In a *conclusion*
`X <= E = v` the delivered claim is `X <= v`, which follows from
`X <= E` only if `v >= E`: round up. In a *threshold hypothesis*
`P >= T = v` the delivered statement is "assume `P >= v`", which gives
`P >= T` only if `v >= T`: round up as well. Both classes round up, for
opposite reasons --- one weakens a conclusion, the other strengthens a
hypothesis. Only a *derived* lower bound `S >= E = v` wants rounding
down, and the paper writes those with `\ge` rather than `=` (`128/27
\ge 4.7`), which is the honest form.

**Slack, not direction.** Direction alone over-reports anyway.
`\tfrac{63}{64}\cdot19=18.7\le25` rounds down in an upper chain, and is
sound because the chain's slack to `25` is `6.297` against a rounding
error of `0.003125`, a ratio of `2020`. Under exact substitution none
of the paper's printed numeric inequalities is false; the tightest is
`25/0.35 <= 71.5`, with `0.0999%` relative slack.

**Where the question bites: A.1.** The least-`P` column names a `P`
from which a row holds, so its entries are not measurements. Claim D's
shift range crosses at `644537`; the nearest four-figure decimal
`6.4e5` asserts the row over `[6.4e5, 644537)`, where it fails. Twenty
of the thirty-eight entries were nearest-rounded below their crossings.
The column is now the crossing rounded *up*, at the smallest precision
keeping the overshoot under one per cent: at most `0.8475%`
(`claimD-shift`), under `0.3%` in twenty-three of the thirty-five
printed rows, under `0.1%` in eleven.

**Three rows were not roundings.**

- `s3s2-bdry` was listed at `403`; the crossing is `1.50527e5`, a
  factor of `373`. The row is a conjunction, and `403` is neither
  conjunct's crossing: the second alone crosses at `1.1^{32/3}=2.76`,
  and the first has no crossing without the `0.35` factor. Provenance
  unknown; corrected to `1.51e5`.
- `st5b-qpp` carried the constant `30.5`, which appeared nowhere else
  in the paper. The constant is `48.9 = 17.1/0.35`, derived in Step
  5b(a) and used at three other sites. With it the crossing is
  `2.98166e11`, not the listed `2.8e10` --- a factor of `10.7`.
- `5b-lam0-range` carried `[0.62,3.94]` against Lemma 5.2b's own
  `[0.62,3.90]` (and `ANCHOR_CONSTANTS`'s `3.90`). With the correct
  endpoint the crossing falls from `6.1e4` to `35026.6`.

**Consistency swept with it.** `5^{16}` was printed `1.5e11` at four
prose sites and `1.53e11` at a fifth; all five now read `1.53e11`
(the value is `1.52588e11`). A.2's stratification cut moves `2.8e10`
to `2.83e10`, and the count it carries --- thirty-three of
thirty-eight from there on --- is unchanged and verified.

*Correction to the previous entry.* Last tick I changed the Claim D
prose from `1.1e6` to `6.4e5` and wrote that it now matched A.1's row.
It did match, and both were wrong in the same direction-blind way. The
prose now prints the exact `644537` and A.1 rounds it up to `6.5e5`.

Tags. EXACT: the direction rule for the three classes; `1.45^{36} =
644537`; `48.9 = 17.1/0.35`. COMPUTATIONALLY VERIFIED: all thirty-eight
A.1 entries at or above their crossings, max overshoot `0.8475%`; the
three corrected crossings `1.50527e5`, `2.98166e11`, `35026.6`; no
printed numeric inequality false under exact substitution; tightest
relative slack `0.0999%`. OBSERVATION: `403`'s provenance is not
recoverable from the row as stated.

Probe: `manuscript_self_audit.a1_rows`, `a1_threshold_audit`,
`a1_failures`; `failures()` gains an `a1_thresholds` key. Ten new
tests, thirty-five in the file. Manuscript: the column rebuilt, three
errata rows corrected and recorded in A.1, the convention stated, five
`5^{16}` sites unified, A.2's cut updated. `P_0` unmoved at
`3.5858e13`; the binding row `5b-W<=c7S` is untouched. No certificate
edit --- the certificate was right in all three cases and the table was
wrong.

## No freeze in the paper justifies charging apart, by a factor of four thousand

Charging a `beta` and a power of `nu` at opposite ends of a block would
be right if the two lived at different points --- if `beta` were frozen
over a range long enough for `nu` to move. So the question is how long
the paper's freezes are. Every one of them:

```text
  freeze                      length              rel. nu-variation   beta spread at P_0
  Lem 5.1(iii) b-runs         P^(1/2)/h           1.67e-07            1.00000008
  gap cells (Stage 2)         P^(1/2)/h           1.67e-07            1.00000008
  floor(G) runs (E6)          P^(1/4)/(|j|+1)     6.82e-11            1.00000000
  Thm 4.8 drift-1 intervals   P^(5/8)/k           8.26e-06            1.00000413
  Stage 3a windows            P^(3/4)/(2 k h_2)   4.09e-04            1.00020433
```

The longest is Stage 3a's windows, at `P^(3/4)`: across one of them `nu`
moves by a relative `4.09e-4`, and `beta`, going as `nu^(1/2)`, by
`2.04e-4`. Every other freeze is shorter, and the run structures that
carry the branch decomposition are shorter by four orders.

Against that, charging one `beta` at the two ends of a *block* costs
`sqrt2`, and a `beta` product costs `2`. So the apart-charging is
**`4894` times** the largest spread any freeze in the paper can justify.

There is no site where it is genuine. The four instances --- `|G'|`'s
`20` against `81/16`, `|G''|`'s `25` against `567/64`, the `j = 0`
anchor's `5.3` against `81/32`, and `lambda_0`'s range at four times its
block --- are four instances of one avoidable thing, not four different
compromises with four different reasons.

It closes the other way round too. A freeze long enough to justify the
apart-charging would have to run for a constant fraction of a block, and
nothing in Sections 4--6 does: the longest runs `P^(3/4)`, which is
`P^(-1/4)` of a block. The paper's whole method is to freeze on short
runs and difference across them, so the scales are structurally small,
and the apart-charging is structurally unjustified.

That completes the block-ends-apart account. The pattern was found in
`|G'|`, then `|G''|`, then the `j = 0` anchor, then `lambda_0` where it
reaches `P_0`; and now the question of whether any of them had a reason
is answered no, uniformly, with the margin measured.

Tags. EXACT: a freeze of length `P^e` lets `nu` vary by a relative
`P^(e-1)` and `beta ~ nu^(1/2)` by half that; the five freeze scales
above are the paper's, the longest at `e = 3/4`. COMPUTATIONALLY
VERIFIED: the relative variations and `beta` spreads at `P_0`, the
largest `1.000204`; the apart-charging costs `sqrt2` on one `beta` and
`2` on a product, so it exceeds the largest justified spread by `4894`.
OBSERVATION: the run structures carrying the branch decomposition are
four orders shorter than the longest freeze, so the margin is larger
still where the pattern actually appears.

Probe: `freeze_scales_justify_nothing`, `FREEZE_SCALES`. Two tests.
Audit `PAPER_B_AUDIT_CONSISTENT`; `P_0` unmoved at `3.5858e13`. No
manuscript or certificate edit.
