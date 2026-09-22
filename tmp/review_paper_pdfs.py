from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
import subprocess
import json
from PIL import Image, ImageOps, ImageDraw
from pypdf import PdfReader

root=Path(__file__).resolve().parents[1]
out=root/"tmp/papers_visual_20260922"
papers={"a":"juggler_finite_dynamics_note", "b":"juggler_parity_discrepancy_note",
        "c":"juggler_fate_almost_all_note", "d":"collatz_3n_minus_1_m_cycles_note",
        "e":"juggler_signed_collatz_note"}

def render(item):
    key,stem=item
    directory=out/key
    directory.mkdir(parents=True,exist_ok=True)
    pdf=root/"juggler_review"/(stem+".pdf")
    subprocess.run(["pdftoppm","-scale-to","1100","-png",str(pdf),str(directory/"page")],check=True,stdout=subprocess.DEVNULL,stderr=subprocess.PIPE)
    images=sorted(directory.glob("page-*.png"))
    reader=PdfReader(pdf)
    assert len(images)==len(reader.pages)
    markers={"a":["4.11a","5.1163051"],"b":["two-index antecedent","2609.22303"],
             "c":["5.19","9.4 (scale","Appendix E","5.12","5.13"],
             "d":["Theorem 8"],"e":["Theorem 4.4","Appendix C","C.5","C.12"]}[key]
    changed=[]
    for i,page in enumerate(reader.pages):
        text=page.extract_text()
        if any(marker in text for marker in markers): changed.append(i+1)
    sheets=[]
    for start in range(0,len(images),9):
        canvas=Image.new("RGB",(1080,1590),"#c6cbd0")
        draw=ImageDraw.Draw(canvas)
        for j,path in enumerate(images[start:start+9]):
            thumb=Image.open(path).convert("RGB")
            thumb.thumbnail((348,494))
            x=6+(j%3)*360; y=24+(j//3)*530
            canvas.paste(thumb,(x,y))
            draw.text((x,y-17),f"Paper {key.upper()} - page {start+j+1}",fill="black")
        sheet=directory/f"sheet-{start//9+1:02}.jpg"
        canvas.save(sheet,quality=90)
        sheets.append(str(sheet))
    return {"paper":key,"pages":len(reader.pages),"selected_pages":changed,"sheets":sheets}

import sys
keys=sys.argv[1:] or list(papers)
with ThreadPoolExecutor(max_workers=3) as pool:
    records=list(pool.map(render,[(k,papers[k]) for k in keys]))
for record in records:
    (out/record["paper"]/"inventory.json").write_text(json.dumps(record,indent=2),encoding="utf-8")
    print(json.dumps(record))
