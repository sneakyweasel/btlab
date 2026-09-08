import { useMemo, useState } from "react";
import { Link } from "react-router-dom";
import { Disclaimer } from "../../components/Disclaimer";
import { Metric } from "../../components/Metric";
import { Tex } from "../../components/Tex";
import {
  LADDER_RUNGS,
  RHO_WORDS,
  TOUR_LADDER_ID,
  fiberExponent,
  idealCoeffOfWord,
  ladderRung,
  lambdaRoot,
  rhoIdeal,
  rhoOfWord,
  rungForWord,
  zetaOf,
  type LadderId,
} from "../../juggler/contagion";
import { RhoTest } from "../../visuals/RhoTest";
import { VLadder } from "../../visuals/VLadder";

function formatFrac(value: number): string {
  const known: [number, string][] = [
    [1, "1"],
    [1 / 2, "1/2"],
    [1 / 3, "1/3"],
    [2 / 9, "2/9"],
    [1 / 9, "1/9"],
    [3 / 8, "3/8"],
    [3 / 4, "3/4"],
    [9 / 32, "9/32"],
    [27 / 128, "27/128"],
    [81 / 512, "81/512"],
    [243 / 2048, "243/2048"],
    [729 / 8192, "729/8192"],
    [9 / 16, "9/16"],
    [1 / 27, "1/27"],
    [1 / 81, "1/81"],
    [1 / 243, "1/243"],
    [1 / 729, "1/729"],
    [1 / 2187, "1/2187"],
    [5 / 8, "5/8"],
    [1 / 4, "1/4"],
    [23 / 32, "23/32"],
    [7 / 16, "7/16"],
  ];
  const hit = known.find((row) => Math.abs(row[0] - value) < 1e-12);
  return hit ? hit[1] : value.toFixed(4);
}

export function VLadderTab() {
  const [rungId, setRungId] = useState<LadderId>(TOUR_LADDER_ID);
  const [word, setWord] = useState("OEOEOEOEOEOEE");
  const rung = ladderRung(rungId);
  const root = useMemo(() => lambdaRoot(rung.terms), [rung]);
  const rho = rhoOfWord(word);
  const entry = RHO_WORDS.find((row) => row.word === word) ?? RHO_WORDS[0];

  function loadRung(id: LadderId) {
    setRungId(id);
    const next = ladderRung(id);
    if (next.words[0]) setWord(next.words[0]);
  }

  function loadWord(next: string) {
    setWord(next);
    const match = rungForWord(next);
    if (match) setRungId(match);
  }

  return (
    <div className="space-y-6">
      <section className="space-y-3 rounded-xl border border-line bg-card p-4">
        <h2 className="font-serif text-2xl">V-ladder to {rung.name}</h2>
        <p className="text-sm text-muted">
          Theorem 5.3 uses the full list, not the{" "}
          <Link to="/play/three-sources">three sources</Link> alone. (5.1) is
          only <Tex>{String.raw`\lambda^*`}</Tex>. Adding item 3 is{" "}
          <Tex>{String.raw`\lambda_{\mathrm{pair}}`}</Tex>. Then the no-
          <Tex>{String.raw`OO`}</Tex> words{" "}
          <Tex>{String.raw`V_k=(OE)^{k-1}OEE`}</Tex> climb to official{" "}
          <Tex>{String.raw`\lambda^{**}=0.4926`}</Tex> at V6. The open mark
          is the depth-two ideal ceiling 0.4927, not a proved word list.
        </p>
        <div className="flex flex-wrap gap-2">
          {LADDER_RUNGS.map((row) => (
            <button
              key={row.id}
              type="button"
              title={row.added}
              className={`rounded-full px-3 py-1 text-sm ${
                rungId === row.id
                  ? "bg-deep text-card"
                  : row.muted
                    ? "border border-dashed border-line text-muted"
                    : "border border-line text-muted"
              }`}
              onClick={() => loadRung(row.id)}
            >
              {row.name}
            </button>
          ))}
        </div>
        <div className="grid gap-3 sm:grid-cols-4">
          <Metric
            label={rung.name}
            value={root.toFixed(4)}
            hint={`printed ${rung.printed.toFixed(4)}`}
          />
          <Metric
            label="added"
            value={rung.added}
            hint={rung.python}
          />
          <Metric
            label="terms"
            value={String(rung.terms.length)}
            hint={rung.official ? "official λ**" : rung.muted ? "not a word list" : "truncation"}
          />
          <Metric
            label="ζ at printed"
            value={Math.abs(zetaOf(rung.terms, rung.printed)).toFixed(4)}
            hint="should be ~0"
          />
        </div>
        <VLadder selected={rungId} onSelect={loadRung} />
      </section>

      <section className="space-y-3 rounded-xl border border-line bg-card p-4">
        <h2 className="font-serif text-2xl">
          <Tex>{String.raw`\rho_w`}</Tex> test for {entry.short}
        </h2>
        <p className="text-sm text-muted">
          Proposition 5.13: the fiber over a source is length{" "}
          <Tex>{String.raw`|I|\asymp P^{1-\rho_w}`}</Tex>, and the
          localized estimate needs <Tex>{String.raw`|I|\ge P^{1/2}`}</Tex>.
          The ideal share is available exactly when{" "}
          <Tex>{String.raw`\rho_w\le 1/2`}</Tex>. Formula (5.7) also
          returns <Tex>{String.raw`c_E=1`}</Tex>,{" "}
          <Tex>{String.raw`c_{OE}=c_{OEE}=1/3`}</Tex>. The recursion
          coefficients on later V-words are net after removing the word
          from family 3, not raw <Tex>{String.raw`c^{\mathrm{ideal}}`}</Tex>.
        </p>
        <div className="flex flex-wrap gap-2">
          {RHO_WORDS.map((row) => (
            <button
              key={row.word}
              type="button"
              title={row.hint}
              className={`rounded-full px-3 py-1 text-sm ${
                word === row.word
                  ? "bg-deep text-card"
                  : row.appendix
                    ? "border border-dashed border-line text-muted"
                    : "border border-line text-muted"
              }`}
              onClick={() => loadWord(row.word)}
            >
              {row.short}
            </button>
          ))}
        </div>
        <div className="grid gap-3 sm:grid-cols-4">
          <Metric
            label="ρ_w"
            value={formatFrac(rho)}
            hint={entry.hint}
          />
          <Metric
            label="|I| ~ P^"
            value={formatFrac(fiberExponent(rho))}
            hint="1 − ρ_w"
          />
          <Metric
            label="c^ideal"
            value={formatFrac(idealCoeffOfWord(word))}
            hint="2^{-|w|} / ρ_w"
          />
          <Metric
            label="test"
            value={rhoIdeal(rho) ? "ρ ≤ 1/2" : "ρ > 1/2"}
            hint={rhoIdeal(rho) ? "ideal share available" : "lossy"}
          />
        </div>
        <RhoTest selected={word} onSelect={loadWord} />
      </section>

      <Disclaimer>
        Official λ** is the V6 truncation. The ideal 0.4927 is a ceiling,
        not a theorem. The ladder excludes no fate and is not a halt
        theorem. Appendix C words are classification only.
      </Disclaimer>
    </div>
  );
}
