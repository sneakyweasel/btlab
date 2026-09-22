from pathlib import Path
from PIL import Image
from pypdf import PdfReader

root = Path(__file__).resolve().parents[1]
qa = root / ".build/paper_e/qa"
pages = sorted(qa.glob("page-*.png"))
for i in range(0, len(pages), 2):
    left = Image.open(pages[i]).convert("RGB")
    right = Image.open(pages[i+1]).convert("RGB") if i+1 < len(pages) else None
    spread = Image.new("RGB", (left.width*2+20, left.height), "white")
    spread.paste(left, (0,0))
    if right:
        spread.paste(right, (left.width+20,0))
    spread.save(qa / f"spread-{i//2+1}.png")
reader = PdfReader(root / "juggler_review/juggler_signed_collatz_note.pdf")
print(f"pages={len(reader.pages)}")
for i, page in enumerate(reader.pages, 1):
    text = page.extract_text()
    print(i, len(text), text[:80].replace("\n"," "))
