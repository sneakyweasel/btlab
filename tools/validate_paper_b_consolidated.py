"""Run Paper B's exact controls and audit the consolidated source references."""
from pathlib import Path
from collections import Counter
import argparse
import hashlib
import importlib
import json
import re

HERE=Path(__file__).resolve().parent
STEM="juggler_parity_discrepancy_note"
MODULES=("validate_paper_b","validate_paper_b_repairs","validate_paper_b_ooeoe",
         "validate_paper_b_d2","validate_paper_b_signed_waves",
         "validate_paper_b_wave_bearing","validate_paper_b_offset_anchor",
         "validate_paper_b_kernel_assembly","validate_paper_b_oooee_transfer")


def validate(source):
    results={}
    for name in MODULES:
        module=importlib.import_module(name)
        fn=getattr(module,"validate",None) or module.check
        data=fn()
        assert data["status"]=="PASS",name
        results[name]={"status":"PASS","counts":data.get("counts",{
            k:v for k,v in data.items()
            if k.endswith(("_cases","_comparisons","_checks"))})}
    s=source.read_text(encoding="utf-8")
    assert s.index(r"\psi(t)=(-1)^{\lfloor t\rfloor}") < s.index(r"s_t^w(n)=\psi")
    assert s.index(r"e(t)=\exp(2\pi i t)") < s.index("**Theorem 3.1")
    urls=re.findall(r"\]\((https?://[^\n]*?)\)",s)
    assert urls and all(not re.search(r"\s|\\",url) for url in urls)
    assert r"\beta_12" not in s and "c_11" not in s
    assert "**Bounded-residual extension.**" in s
    assert "Monotonicity is not required for this extension." in s
    tags=re.findall(r"\\tag\{([^}]+)\}",s)
    assert not [k for k,v in Counter(tags).items() if v>1]
    refs=re.findall(r"\(([ABC]\.\d+)\)",s)
    assert not set(refs)-set(tags)
    assert "**Theorem 4.11 (OOOEE mixed modes)." in s
    assert "**Theorem 5.4 (full five-step certificate density)." in s
    assert not re.search(r"\((?:D|W|K|T|S|O)\d+\)",s)
    assert not re.search(r"\]\(paper_b_.*?_report\.md\)",s)
    assert all(ord(c)>=32 or c in "\n\r" for c in s)
    for display in re.findall(r"\\\[[\s\S]*?\\\]",s):
        assert not re.search(r"\n\s*\n",display)
        for split in re.findall(r"\\begin\{split\}[\s\S]*?\\end\{split\}",display):
            assert r"\tag{" not in split
    return {
        "status":"PASS","version":"2026-09-10-zenodo-preprint",
        "source_sha256":hashlib.sha256(source.read_bytes()).hexdigest(),
        "exact_control_modules":results,"equation_tags":len(tags),
        "appendix_equation_references":len(refs),
        "external_research_note_dependencies":False,
        "notation_defined_before_use":True,"external_links_well_formed":True,
        "bounded_residual_extension_present":True,
        "written_manuscript_result":"C_5 count 7N/8+O_epsilon(N^(127/128+epsilon))",
        "validation_scope":"Finite exact algebra and exponent controls, plus source structure; not an independent proof of asymptotic cancellation.",
        "historical_module_labels":"Individual earlier modules retain their original research-stage labels; these are not current theorem-status assertions.",
        "independent_mathematical_review":False,"lean_verification":False}


if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source",type=Path)
    parser.add_argument("--output",type=Path)
    args=parser.parse_args()
    source=args.source or HERE/f"{STEM}.md"
    if not source.exists():
        source=HERE.parent/"docs/theory"/f"{STEM}.md"
    rendered=json.dumps(validate(source),indent=2)+"\n"
    if args.output:args.output.write_text(rendered,encoding="utf-8")
    print(rendered,end="")
