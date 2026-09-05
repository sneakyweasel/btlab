"""Which LaTeX macros in Papers A and B does a non-raw Python string corrupt?"""

import collections
import io
import re

DANGEROUS = set("abfnrtv0x")          # \a \b \f \n \r \t \v \0.. \x..
PAPERS = ("docs/theory/juggler_parity_discrepancy_note.md",
          "docs/theory/juggler_finite_dynamics_note.md")

macros: collections.Counter = collections.Counter()
for path in PAPERS:
    text = io.open(path, encoding="utf-8").read()
    for name in re.findall(r"\\([A-Za-z]+)", text):
        if name[0] in DANGEROUS:
            macros[name] += 1

print("LaTeX macros in Papers A+B that a non-raw Python string corrupts:")
for name, count in macros.most_common(15):
    print("   backslash-%-12s %5d   eaten as \\%s" % (name, count, name[0]))
print("   %d distinct macros, %d occurrences in total"
      % (len(macros), sum(macros.values())))
