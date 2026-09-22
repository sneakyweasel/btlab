from pathlib import Path
import json

root=Path(__file__).resolve().parents[1]
def read(p): return (root/p).read_text(encoding="utf-8")
def put(p,s):
    p=root/p; t=p.with_name(p.name+".publication-tmp")
    t.write_text(s,encoding="utf-8",newline="\n");t.replace(p)

p="docs/theory/paper_b_zenodo.json"
d=json.loads(read(p));d["metadata"]["version"]="1.1.1";d.pop("version",None)
put(p,json.dumps(d,ensure_ascii=False,indent=2)+"\n")

p="docs/theory/juggler_signed_collatz_note.md";s=read(p)
a=s.index("**Theorem 4.4"); b=s.index("## 5.",a)
part=s[a:b].replace(r"\tag{4.6}",r"\tag{4.7}")
s=s[:a]+part+s[b:]
a=s.index("## Appendix C.")
s=s[:a]+s[a:].replace("in (4.6)","in (4.7)")
put(p,s)

p="docs/theory/paper_deposits.md";s=read(p)
for paper, version in [("A","1.2.0"),("B","1.1.1"),("C","1.2.0")]:
    a=s.index(f"### Paper {paper},"); b=s.index("| --- | --- | --- |",a)+len("| --- | --- | --- |")
    s=s[:b]+f"\n| {version} | not deposited | 22 September 2026 |"+s[b:]
s=s.replace("The repository now pins `bf018a78`, where all 124 files the release", "The prepared 1.2.0 now pins `5a728d1d`, where all 126 files the release")
s=s.replace("correction goes up with the prepared 1.1.0", "correction is retained in the prepared 1.2.0")
put(p,s)

p="docs/README.md";s=read(p).replace("version 0.5.0; exact coding, signed ancestor counts,", "version 0.6.0; exact coding, signed ancestor counts,")
s=s.replace("and arithmetic obstructions. [Build and update guide]", "arithmetic obstructions, and explicit OOE return bounds. [Build and update guide]")
s=s.replace("3. [Paper C — fate contagion](theory/juggler_fate_almost_all_note.md)", "3. [Paper C — fate contagion](theory/juggler_fate_almost_all_note.md)\n   — local version 1.2.0: written exponent 5/8 and rate threshold 3/8;\n   fully machine-checked baseline 100/203; the new analytic proof awaits review")
put(p,s)
p="juggler_review/README.md";s=read(p).replace("version 0.3.0", "version 0.6.0")
s += "\n## Local revisions of 22 September 2026\n\nPaper A 1.2.0 adds the Wu-Wang asymptotic corollary without raising the\ncomputed floor. Paper B 1.1.1 corrects attribution and a source citation.\nPaper C 1.2.0 incorporates the written OOEE proof, contagion at 5/8 and\nthe sufficient rate threshold 3/8; its unconditional Lean baseline remains\n100/203. Paper D 1.1.0 already contains the m <= 61 extension. Paper E\n0.6.0 adds the written effective OOE theorem and quantitative appendix.\nThese packages are local revisions; no external deposit was performed.\nThe analytic review and formalization boundaries are stated in each paper.\n"
put(p,s)
p="attacks/juggler/AGENT.md";s=read(p)
s=s.replace("is Paper E, version 0.5.0", "is Paper E, version 0.6.0")
s=s.replace("Its quantitative argument is not yet in Lean\nor the version 0.5.0 manuscript.", "Its quantitative argument is included as Theorem 4.4 and Appendix C\nin version 0.6.0. Complete quantitative Lean verification remains open.")
s=s.replace("The constants are not practical search limits.", "The constants are not practical search limits.")
s=s.replace("Kills nothing; the deposited Corollary 4.11 text still prints\n  \\(14.3\\).", "Kills nothing; the local Paper A 1.2.0 adds Corollary 4.11a,\n  while retaining the explicit Rhin bound with exponent \\(14.3\\).")
s=s.replace("gives written contagion at 5/8 and a sufficient Tao-rate threshold e>3/8.", "gives written contagion at 5/8 and a sufficient Tao-rate threshold e>3/8.\n  Paper C 1.2.0 now includes the complete written input in Appendix E\n  and its assembly in Theorem 5.19; no new deposit was performed.")
put(p,s)
print("Synchronized versions, equation numbering and publication summaries.")
