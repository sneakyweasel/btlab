import { Metric } from "../../components/Metric";
import { StartControl } from "../../components/StartControl";
import { SurplusScale } from "../../visuals/SurplusScale";
import { usePlayState } from "../../context/PlayState";
import { WORD_PRESETS } from "../../juggler/constants";
import { formatInt, parsePositiveInt } from "../../juggler/format";
import {
  compareImage,
  envelopeSlack,
  firstFail,
  followsWord,
  imageAfter,
  oddCount,
  parseWord,
  regimeOf,
} from "../../juggler/word";

export function WordTab() {
  const { nText, word, setWord } = usePlayState();
  const n = parsePositiveInt(nText);
  const parsed = parseWord(word);
  return (
    <div className="space-y-5">
      <StartControl />
      <div className="flex flex-wrap items-end gap-3">
        <label className="text-sm text-muted">
          Word
          <input
            className="ml-2 rounded border border-line bg-card px-2 py-1 font-mono uppercase"
            value={word}
            onChange={(event) => setWord(event.target.value.toUpperCase())}
          />
        </label>
        <select
          className="rounded border border-line bg-card px-2 py-1 font-mono text-sm"
          value=""
          onChange={(event) => {
            if (event.target.value) setWord(event.target.value);
          }}
        >
          <option value="">Presets</option>
          {WORD_PRESETS.map((preset) => (
            <option key={preset} value={preset}>
              {preset}
            </option>
          ))}
        </select>
      </div>
      {parsed === null ? (
        <p className="text-sm text-warn">Use only O and E, length at most 8.</p>
      ) : n === null ? null : (
        <WordResult n={n} word={parsed} />
      )}
    </div>
  );
}

function WordResult({ n, word }: { n: bigint; word: string }) {
  const odds = oddCount(word);
  const follows = followsWord(n, word);
  const fail = follows ? null : firstFail(n, word);
  const image = follows ? imageAfter(n, word) : null;
  const slack =
    image === null ? null : envelopeSlack(n, image, word.length, odds);
  return (
    <>
      <div className="grid gap-3 sm:grid-cols-4">
        <Metric label="Odd letters" value={String(odds)} />
        <Metric label="Regime" value={regimeOf(word.length, odds)} />
        <Metric label="Follows this word?" value={follows ? "yes" : "no"} />
        <Metric
          label="Image vs n"
          value={
            image === null ? "—" : `${formatInt(image)} ${compareImage(image, n)} ${n}`
          }
        />
      </div>
      {!follows && fail ? (
        <p className="text-sm text-warn">
          Letter {fail.index} fails at {formatInt(fail.state)}. The start is
          the wrong parity for that letter.
        </p>
      ) : null}
      <div className="grid gap-3 sm:grid-cols-2">
        <Metric
          label="Envelope slack Δ"
          value={
            !follows ? "—" : slack === null ? "too large to show" : formatInt(slack)
          }
          hint="n^{3^o} − image^{2^k}, when the powers fit in 80 bits"
        />
        <Metric
          label="Compared with n"
          value={image === null ? "—" : compareImage(image, n)}
        />
      </div>
      <div className="rounded-xl border border-line bg-card p-4">
        <SurplusScale odds={odds} length={word.length} />
      </div>
    </>
  );
}
