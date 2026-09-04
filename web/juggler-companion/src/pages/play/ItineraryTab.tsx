import { Metric } from "../../components/Metric";
import { StartControl } from "../../components/StartControl";
import { EnvelopeCeiling } from "../../visuals/EnvelopeCeiling";
import { SurplusScale } from "../../visuals/SurplusScale";
import { usePlayState } from "../../context/PlayState";
import { ITINERARY_PRESETS } from "../../juggler/constants";
import { formatInt, parsePositiveInt } from "../../juggler/format";
import { floorPower } from "../../juggler/map";
import {
  compareImage,
  envelopeSlack,
  firstFail,
  followsItinerary,
  imageAfter,
  oddCount,
  parseItinerary,
  regimeOf,
} from "../../juggler/itinerary";

export function ItineraryTab() {
  const { nText, itinerary, setItinerary } = usePlayState();
  const n = parsePositiveInt(nText);
  const parsed = parseItinerary(itinerary);
  return (
    <div className="space-y-5">
      <p className="text-sm text-muted">
        An itinerary is a finite string of O and E. It is realized at the start
        only when the trajectory actually follows those parities. The ideal
        exponent 3<sup>o</sup>/2<sup>k</sup> ignores floors: compare 3<sup>o</sup>{" "}
        with 2<sup>k</sup> for expanding versus contracting, then read the slack
        under the power envelope when the word is followed.
      </p>
      <StartControl />
      <div className="flex flex-wrap items-end gap-3">
        <label className="text-sm text-muted">
          Itinerary
          <input
            className="ml-2 rounded border border-line bg-card px-2 py-1 font-mono uppercase"
            value={itinerary}
            onChange={(event) => setItinerary(event.target.value.toUpperCase())}
          />
        </label>
        <select
          className="rounded border border-line bg-card px-2 py-1 font-mono text-sm"
          value=""
          onChange={(event) => {
            if (event.target.value) setItinerary(event.target.value);
          }}
        >
          <option value="">Presets</option>
          {ITINERARY_PRESETS.map((preset) => (
            <option key={preset} value={preset}>
              {preset}
            </option>
          ))}
        </select>
      </div>
      {parsed === null ? (
        <p className="text-sm text-warn">Use only O and E, length at most 8.</p>
      ) : n === null ? null : (
        <ItineraryResult n={n} itinerary={parsed} />
      )}
    </div>
  );
}

function ItineraryResult({ n, itinerary }: { n: bigint; itinerary: string }) {
  const odds = oddCount(itinerary);
  const follows = followsItinerary(n, itinerary);
  const fail = follows ? null : firstFail(n, itinerary);
  const image = follows ? imageAfter(n, itinerary) : null;
  const slack =
    image === null ? null : envelopeSlack(n, image, itinerary.length, odds);
  const path = [n];
  if (follows) {
    let current = n;
    for (let index = 0; index < itinerary.length; index += 1) {
      current = floorPower(current);
      path.push(current);
    }
  }
  const envelopePoints = path.map((value) => {
    const bits = value.toString(2).length;
    if (bits <= 53) return Number(value);
    return 2 ** (bits - 1);
  });
  return (
    <>
      <div className="grid gap-3 sm:grid-cols-4">
        <Metric label="Odd letters" value={String(odds)} />
        <Metric
          label="Ideal exponent"
          value={`3^${odds}/2^${itinerary.length}`}
          hint="before floors"
        />
        <Metric label="Regime" value={regimeOf(itinerary.length, odds)} />
        <Metric label="Follows this itinerary?" value={follows ? "yes" : "no"} />
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
      <div className="grid gap-3 sm:grid-cols-2">
        <div className="rounded-xl border border-line bg-card p-4">
          <SurplusScale odds={odds} length={itinerary.length} />
        </div>
        {follows ? (
          <div className="rounded-xl border border-line bg-card p-4">
            <EnvelopeCeiling points={envelopePoints} />
          </div>
        ) : null}
      </div>
    </>
  );
}
