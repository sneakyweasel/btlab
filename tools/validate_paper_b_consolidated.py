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
MONTHS=("January","February","March","April","May","June",
        "July","August","September","October","November","December")


def digest(path,mode="binary"):
    """SHA-256 of a recorded input, line endings normalised first in text mode.

    Hashing raw bytes records the checkout rather than the manuscript: the
    repository has no .gitattributes and core.autocrlf checks the Markdown out
    CRLF on Windows and LF elsewhere, so one source hashed two ways. CI reported
    exactly that on 14 September 2026; see tools/artifact_digest.py. The helper
    is copied rather than imported because the standalone source package ships
    this module without its siblings.
    """
    data=path.read_bytes()
    if mode=="text":
        data=data.replace(b"\r\n",b"\n").replace(b"\r",b"\n")
    return hashlib.sha256(data).hexdigest()


def edition(text):
    """The manuscript's edition stamp, read from its own YAML front matter.

    This was the literal "2026-09-19-preprint" until 21 September 2026, so the
    record printed an edition a day stale beside a current source_sha256: the
    manuscript moved to 20 September, the digest followed it, and the label did
    not. Deriving the stamp keeps the two describing one file.

    It is the EDITION, the value docs/theory/paper_b_release_check.json carries
    as "version" and PAPER_B_BUILD.md prints. It is deliberately not the Zenodo
    RECORD version in docs/theory/paper_b_zenodo.json: that one tracks the
    deposit, and on 21 September 2026 the title-page ORCID took it from 1.0.0 to
    1.0.1 over a byte-identical manuscript. A label printed beside source_sha256
    must not move when the source does not.

    Read from the manuscript rather than from the release check because the
    standalone source package ships this module and the manuscript without it.
    Month names are matched against MONTHS rather than parsed with %B, which
    follows LC_TIME and would read the packager's locale into the stamp.
    """
    front=re.match(r"---\n(.*?)\n---\n",text,re.S)
    assert front,"the manuscript carries no YAML front matter"
    stamp=re.search(r"^date:[ ]*(\d{1,2}) ([A-Za-z]+) (\d{4})[ ]*$",front.group(1),re.M)
    assert stamp,"the front matter carries no 'date: D Month YYYY' line"
    day,month,year=stamp.groups()
    assert month in MONTHS,f"unrecognised month {month!r} in the front matter date"
    return f"{year}-{MONTHS.index(month)+1:02d}-{int(day):02d}-preprint"


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
        "status":"PASS","source_edition":edition(s),
        "source_edition_definition":"The manuscript's own YAML front-matter date, rendered YYYY-MM-DD-preprint. This is the edition stamp, the value docs/theory/paper_b_release_check.json carries as \"source_edition\" and PAPER_B_BUILD.md prints. It is not the Zenodo record version in docs/theory/paper_b_zenodo.json, which tracks the deposit and moved from 1.0.0 to 1.0.1 on 2026-09-21 over a byte-identical manuscript. The field was a pinned literal until 2026-09-21 and had gone stale at 2026-09-19-preprint while source_sha256 beside it already described the 2026-09-20 manuscript.",
        "source_sha256":digest(source,"text"),
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
    if args.output:args.output.write_text(rendered,encoding="utf-8",newline="\n")
    print(rendered,end="")
