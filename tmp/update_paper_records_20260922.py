from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
def read(p): return (ROOT / p).read_text(encoding="utf-8")
def put(p, s): (ROOT / p).write_text(s, encoding="utf-8", newline="\n")

# Release guides explicitly distinguish the new local editions from deposits.
p = "docs/theory/PAPER_A_BUILD.md"
s = read(p).replace("This repository holds version 1.1.0", "This repository holds version 1.2.0")
s += "\n## Revision of 22 September 2026\n\nVersion 1.2.0 adds Corollary 4.11a, the Wu-Wang asymptotic exponent\n5.1163051 plus epsilon, alongside Rhin's explicit bound. The logarithmic\nmeasure remains an external theorem; its conditional Lean transfer is\nrecorded in the supplementary formalization map. The certified floor and\nall numerical cycle exclusions remain unchanged. The earlier provenance\ncorrection is retained. No new external deposit is performed.\n"
put(p, s)
p = "docs/theory/juggler_finite_dynamics_formalization.md"
s = read(p)
s += "\n## Supplement: Corollary 4.11a (22 September 2026)\n\nThe asymptotic Wu-Wang refinement is a written application of the classical\nmeasure in reference [31]. Its transfer declarations are\n`cycleMin_length_of_wuWang` and `cycleMin_period_ge_wuWang` in\n[GapTransferWW.lean](../../formal/Problems/Juggler/GapTransferWW.lean).\nThey retain the logarithmic lower bound as an explicit hypothesis;\nthey do not prove Wu and Wang's theorem. These supplementary declarations\nare outside the historical selected Paper A audit. The stronger exponent\nchanges no computed period floor.\n"
put(p,s)
p = "docs/theory/juggler_finite_dynamics_reviewer_packet.md"
s = read(p)
s += "\n## Revision of 22 September 2026\n\nPaper A 1.2.0 adds Corollary 4.11a. Review the substitution of height L\ninto Wu and Wang's external measure and the absorption of finitely many\nsmall heights into a positive constant. This is an asymptotic improvement;\nRhin's explicit constant 915 and the computed floor exclusions remain.\nThe supplementary formalization map separates the conditional transfer\nfrom the external transcendence estimate.\n"
put(p,s)
p = "docs/theory/PAPER_B_BUILD.md"
s = read(p).replace("Version: 2026-09-20-preprint.", "Version: 1.1.1; source edition: 22 September 2026.")
s += "\n## Revision of 22 September 2026\n\nThe prepared version 1.1.1 corrects the recursion's attribution to Terras\n(1976, Theorem 1.14, equation (11)) and cites Winkler's arXiv:2609.22303.\nThe mathematical theorems, proofs and five-step density 7/8 are unchanged.\nThe historical statement that pages 2--42 match the deposit pixel for pixel\napplies to local 1.1.0, not to this edition. The new source, PDF, validation\nrecord and both archives are rebuilt together. No deposit is performed.\n"
put(p,s)
p = "docs/theory/PAPER_C_BUILD.md"
s = read(p).replace("This repository holds version 1.1.1", "This repository holds version 1.2.0")
s += "\n## Revision of 22 September 2026: three productions\n\nVersion 1.2.0 incorporates the complete written OOEE poor-fiber argument\nas Appendix E and its physical-cutoff assembly as Theorem 5.19. Theorem 1\nnow reaches 5/8; Theorems 3 and 7.2--7.3 use the sufficient rate e > 3/8.\nThe earlier two-production exponent 100/203 remains the fully kernel-checked\nbaseline. The new analytic proof is AI-assisted and awaits independent\nreview and complete Lean verification. Theorem 9.4 adds the scale-average\npressure implication, separately Lean at r - eta > 103/203 and written\nat r - eta > 3/8 using the new contagion theorem.\n\nThe historical 37-module barrel and its 473 reports are unchanged. The\nsupplementary OOEE assembly, weighted OE, mixed-mode and scale-average\nmodules retain separate audits. Their transitive sources and the written\nproof notes are included in the release provenance. A conditional Lean\nassembly does not certify the complete analytic input. Earlier numerical\ndepth tables remain labelled comparisons at their original thresholds.\nThe dependency diagram and metadata now describe this edition.\n"
put(p,s)
for p in ("docs/theory/PAPER_E_BUILD.md", "docs/theory/paper_e_review.md"):
    s=read(p).replace("Version 0.5.0, 22 September 2026", "Version 0.6.0, 22 September 2026")
    if p.endswith("PAPER_E_BUILD.md"):
        s += "\n## Quantitative extension in 0.6.0\n\nTheorem 4.4 and Appendix C add the effective OOE counting error and\nfirst-witness bound, uniform in the modulus. These are written results\nusing Arias de Reyna's explicit derivative estimate; independent review\nand the complete quantitative Lean proof remain open. The existing\n49-declaration audit continues to certify the earlier qualitative\nresults only. Its inventory is not silently enlarged by the new prose.\nThe source archive includes the quantitative proof and audit notes.\n"
    else:
        s = s.replace("## Version history", "## Quantitative extension and review boundary\n\nTheorem 4.4 and Appendix C reproduce the effective OOE proof and explicit\nconstants. Review the derivative sign on both frequency axes, real dyadic\nendpoints, finite initial segment, saturated Fejer arcs and half-open\nbox boundaries. The current selected 49-declaration Lean audit does not\ninclude this theorem. Its internal audit is not independent review;\ncomplete quantitative formalization remains outstanding. The OOE word\nhas denominator one, so this does not quantify the large-denominator\nconstruction.\n\n## Version history\n\n### 0.6.0 - 22 September 2026\n\nAdded Theorem 4.4 and its full quantitative proof in Appendix C, including\nthe uniform counting error and first-witness bound. Preserved all earlier\ntheorem numbers and the selected qualitative Lean audit.\n")
    put(p,s)

p="docs/theory/paper_deposits.md"
s=read(p)
s=s.replace("| A | Lower Bounds for Cycle Lengths in the Juggler Map | 1.1.0,", "| A | Lower Bounds for Cycle Lengths in the Juggler Map | 1.2.0,")
s=s.replace("| B | Five-Step Descent Certificates for the Juggler Map: Parity Statistics of Nested Floor Powers | 1.1.0,", "| B | Five-Step Descent Certificates for the Juggler Map: Parity Statistics of Nested Floor Powers | 1.1.1,")
s=s.replace("| C | Fate Contagion and Termination Criteria for the Juggler Map | 1.1.1,", "| C | Fate Contagion and Termination Criteria for the Juggler Map | 1.2.0,")
s=s.replace("| E | The Juggler Map and the 3n±1 Maps: Exact Coding and Arithmetic Obstructions | 0.3.0,", "| E | The Juggler Map and the 3n±1 Maps: Exact Coding and Arithmetic Obstructions | 0.6.0,")
s=s.replace("### Paper E, The Juggler Map and the 3n±1 Maps\n", "### Paper E, The Juggler Map and the 3n±1 Maps\n\nVersion 0.6.0, 22 September 2026: adds the written effective OOE theorem\nand complete quantitative appendix. The selected 49-declaration Lean\naudit still covers the qualitative results; full quantitative verification\nand independent review are outstanding. No deposit has been made.\n\nVersion 0.5.0, 22 September 2026: exact counting and prescribed-residue\ncorollaries, with complete Lean proofs. No deposit has been made.\n\nVersion 0.4.0, 22 September 2026: completes Theorem 4.1 in Lean, including\nits analytic box-recurrence input. No deposit has been made.\n")
for letter, version, description in [
    ("A","1.2.0","Adds the Wu-Wang asymptotic refinement, retaining Rhin's explicit bound and the provenance correction. Numerical cycle exclusions are unchanged."),
    ("B","1.1.1","Corrects the recursion attribution to Terras (1976) and Winkler's arXiv citation. Mathematical results are unchanged."),
    ("C","1.2.0","Adds the full written OOEE proof, contagion at 5/8, rate threshold 3/8, and the scale-average pressure criterion. The fully machine-checked contagion baseline remains 100/203.")]:
    marker=f"### Paper {letter},"
    start=s.index(marker)
    insert=s.index("\n",start)+1
    s=s[:insert]+f"\nPrepared {version}, 22 September 2026. {description} No new deposit has been made.\n"+s[insert:]
put(p,s)

# Complete the new provenance inventory without widening claims of the selected audits.
p="tools/build_paper_a.py"
s=read(p).replace('BUILD_INPUTS = ["tools/build_paper_a.py",', 'BUILD_INPUTS = ["formal/Problems/Juggler/GapTransferWW.lean",\n                "literature/wu-wang-2014-irrationality-measure-log3.json",\n                "tools/build_paper_a.py",')
put(p,s)
p="tools/build_paper_c.py"
s=read(p)
s=s.replace('BUILD_INPUTS = ["tools/build_paper_c.py",', 'BUILD_INPUTS = ["docs/theory/juggler_ooee_poor_fibre_tail_note.md",\n                "docs/theory/juggler_ooee_contagion_note.md",\n                "docs/theory/juggler_ooee_mixed_modes_note.md",\n                "formal/AxiomCheckOOEEMixedModes.lean",\n                "formal/AxiomCheckOOEEMixedModes.expected",\n                "formal/AxiomCheckScaleAverage.lean",\n                "formal/AxiomCheckScaleAverage.expected",\n                "tools/build_paper_c.py",')
s=s.replace('pending = ["formal/Problems/JugglerFatePaper.lean"]', 'pending = ["formal/Problems/JugglerFatePaper.lean",\n               "formal/Problems/Juggler/FateOOEEAssembly.lean",\n               "formal/Problems/Juggler/FateOEWeighted.lean",\n               "formal/Problems/Juggler/OOEEMixedModes.lean",\n               "formal/Problems/Juggler/FateScaleAverage.lean"]')
s=s.replace(r'(Problems\.[\w.]+)', r'((?:Problems|BTCalculus)\.[\w.]+)')
put(p,s)

# Scope corrections discovered while comparing the proof maps.
p="docs/theory/juggler_signed_collatz_note.md"
s=read(p).replace("no new general distribution criterion\nor quantitative discrepancy estimate is claimed.", "no new general distribution criterion is claimed. Theorem 4.4 adds\na quantitative specialization for the single word OOE.")
put(p,s)
p="docs/theory/juggler_fate_almost_all_note.md"
s=read(p).replace(r"(\lambda^{**}\), Theorem 1; elementary, audited)", r"(\lambda^{**}\), earlier finite-production route; elementary, audited)")
s=s.replace("*Depth constants.* The least integer values below use the three", "Theorem 5.19 additionally gives the attained written exponent 5/8\nfrom coefficients 1, 33/100 and 11/100 at scales 1/2, 3/4 and 9/16.\nIts exact certificate is in Section 5.9; the new analytic input is not\nyet completely formalized.\n\n*Depth constants.* The historical least integer values below use the three")
s=s.replace("## Appendix C. A conditional strengthening", "## Appendix C. An earlier conditional strengthening")
put(p,s)
print("Updated release guides, proof maps, provenance inventories and deposit register.")
