"""Transfer complete proof text while preserving function arguments and math."""
from pathlib import Path
import re

root=Path(__file__).resolve().parents[1]
def read(p): return (root/p).read_text(encoding="utf-8")
def put(p,s):
    p=root/p
    tmp=p.with_name(p.name+".publication-tmp")
    tmp.write_text(s,encoding="utf-8",newline="\n")
    tmp.replace(p)

def powers(s):
    # Source notes use balanced parenthesized exponents; retain their contents.
    result=""
    i=0
    while i<len(s):
        if s[i] in "^_" and i+1<len(s) and s[i+1]=="(":
            j=i+2; depth=1
            while j<len(s) and depth:
                depth += (s[j]=="(")-(s[j]==")")
                j+=1
            if depth==0:
                result+=s[i]+"{"+powers(s[i+2:j-1])+"}"
                i=j; continue
        result+=s[i]; i+=1
    return result

def math_token(token):
    token=powers(token)
    token=token.replace("<=",r"\le ").replace(">=",r"\ge ").replace("!=",r"\ne ")
    token=token.replace("*",r"\cdot ")
    token=re.sub(r"(?<![A-Za-z\\])(eta|epsilon|lambda|delta|pi|alpha|beta)(?![A-Za-z])",lambda m:"\\"+m[1],token)
    token=re.sub(r"(?<![A-Za-z\\])(log|exp|sin|cos|max|min)(?=\()",lambda m:"\\"+m[1],token)
    return r"\("+token+r"\)"

def notation(text):
    lines=[]; display=False
    for line in text.splitlines():
        if line.strip()==r"\[": display=True; lines.append(line); continue
        if line.strip()==r"\]": display=False; lines.append(line); continue
        if display or line.startswith("#"):
            lines.append(line); continue
        # Protect genuine Markdown links and existing inline math/code.
        pieces=re.split(r"(\[[^\]]*\]\([^)]*\)|`[^`]+`|\\\(.*?\\\))",line)
        for i in range(0,len(pieces),2):
            tokens=re.split(r"(\s+)",pieces[i])
            for j,t in enumerate(tokens):
                if not t or t.isspace() or "**" in t: continue
                if any(c in t for c in "_^*<>="):
                    tokens[j]=math_token(t)
            pieces[i]="".join(tokens)
        lines.append("".join(pieces))
    return "\n".join(lines)+"\n"

def extract(note,start,end,letter):
    text=start+read(note).split(start,1)[1].split(end,1)[0]
    text=re.sub(r"^## (\d+)\. (.+)$",lambda m:f"### {letter}.{m[1]} {m[2]}",text,flags=re.M)
    text=re.sub(r"^### (\d+)\.(\d+) (.+)$",lambda m:f"#### {letter}.{m[1]}.{m[2]} {m[3]}",text,flags=re.M)
    text=re.sub(r"\\tag\{(\d+)\}",lambda m:r"\tag{"+letter+"."+m[1]+"}",text)
    # A numbered reference is separated from its context. Function arguments,
    # derivative orders and powers are not equation references.
    text=re.sub(r"(?<![A-Za-z0-9_'{}^])\((\d+)\)",lambda m:"("+letter+"."+m[1]+")",text)
    return text

extra=extract("docs/theory/juggler_effective_modular_return_note.md","## 2. Explicit analytic input","## 6. Verification and value","C")
extra=extra.replace("in (C.1)","in (4.6)")
extra=extra.replace("giving (C.2) and (C.3)","giving the parameter and start bounds in Theorem 4.4")
extra=extra.replace("the box gives (C.4)","the box gives the exit congruence in Theorem 4.4")
extra=extra.replace("J. Arias de Reyna,\n[*Explicit van der Corput's d-th derivative estimate*, v1](https://arxiv.org/html/2407.02094v1),","J. Arias de Reyna [AR24],")
extra=notation(extra)
p="docs/theory/juggler_signed_collatz_note.md"; s=read(p)
a=s.index("### C.2 Explicit analytic input"); b=s.index("## References",a)
s=s[:a]+extra+"\n"+s[b:]
put(p,s)

extra=extract("docs/theory/juggler_ooee_poor_fibre_tail_note.md","## 1. Statement and exact objects","## 7. Audit and formalization boundary","E")
extra=extra.split("This is an actual two-consecutive-odd production",1)[0]
extra=extra.replace("Theorem 1", "Theorem E.1").replace("Lemma 2", "Lemma E.2")
extra=notation(extra)
extra+="\nThe physical source cutoffs and three-production recursion are proved\nin Section 5.9. This analytic input is a written proof pending independent\nreview. The main mixed-mode estimate has a separate Lean proof; the\ncomplete poor-target and production conclusions are not yet certified\nby that formalization.\n\n"
p="docs/theory/juggler_fate_almost_all_note.md"; s=read(p)
a=s.index("### E.1 Statement and exact objects"); b=s.index("## Acknowledgments and use of AI",a)
s=s[:a]+extra+s[b:]
put(p,s)
print("Rebuilt both complete proof appendices with scoped equation references and inline mathematics.")
