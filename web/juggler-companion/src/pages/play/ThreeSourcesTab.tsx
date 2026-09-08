import { useMemo, useState } from "react";
import { Link } from "react-router-dom";
import { Disclaimer } from "../../components/Disclaimer";
import { Metric } from "../../components/Metric";
import { Tex } from "../../components/Tex";
import {
  lambdaRoot,
  RECURSIONS,
  type RecursionId,
  type SourceId,
  threeSourcesView,
} from "../../juggler/contagion";
import { SOURCE_SCALES, TOUR_SOURCE_X } from "../../juggler/constants";
import {
  ThreeSourcesScale,
  ThreeSourcesStacks,
} from "../../visuals/ThreeSourcesScale";
import { ZetaPlot } from "../../visuals/ZetaPlot";

function formatCoeff(value: number): string {
  if (value === 0) return "0";
  if (Math.abs(value - 1) < 1e-12) return "1";
  if (Math.abs(value - 1 / 3) < 1e-12) return "1/3";
  if (Math.abs(value - 1 / 9) < 1e-12) return "1/9";
  if (Math.abs(value - 2 / 9) < 1e-12) return "2/9";
  return value.toFixed(3);
}

export function ThreeSourcesTab() {
  const [x, setX] = useState(TOUR_SOURCE_X);
  const [recursion, setRecursion] = useState<RecursionId>("star");
  const [selected, setSelected] = useState<SourceId>(1);
  const view = useMemo(() => threeSourcesView(x), [x]);
  const spec = RECURSIONS[recursion];
  const root = useMemo(() => lambdaRoot(spec.terms), [spec]);
  const source = view.sources[selected - 1];
  const coeff = recursion === "star" ? source.coeffStar : source.coeffPair;

  return (
    <div className="space-y-6">
      <section className="space-y-3 rounded-xl border border-line bg-card p-4">
        <h2 className="font-serif text-2xl">Three sources at x = {x.toLocaleString("en-US")}</h2>
        <p className="text-sm text-muted">
          Section 5.1 splits{" "}
          <Tex>{String.raw`A\cap(\sqrt x,x]`}</Tex> into three pairwise
          disjoint families. Item 1 is even{" "}
          <Tex>{String.raw`E`}</Tex>-images; items 2–3 are odd{" "}
          <Tex>{String.raw`OE`}</Tex>-images. Equation (5.1) is items 1+2.
          Adding item 3 drops the{" "}
          <Tex>{String.raw`3t/8`}</Tex> coefficient from{" "}
          <Tex>{String.raw`1/3`}</Tex> to <Tex>{String.raw`1/9`}</Tex> and is
          (5.2). <Tex>{String.raw`\lambda`}</Tex> is the root of{" "}
          <Tex>{String.raw`\zeta`}</Tex>, not a slogan. The{" "}
          <Link to="/play/block-average">even-block average</Link> is the{" "}
          <Tex>{String.raw`1/3`}</Tex> in item 2. Official{" "}
          <Tex>{String.raw`\lambda^{**}`}</Tex> is the{" "}
          <Link to="/play/v-ladder">V-ladder</Link>.
        </p>
        <div className="flex flex-wrap items-end gap-3">
          <div className="flex flex-wrap gap-2">
            {SOURCE_SCALES.map((preset) => (
              <button
                key={preset.value}
                type="button"
                title={preset.note}
                className={`rounded-full px-3 py-1 text-sm ${
                  x === preset.value
                    ? "bg-deep text-card"
                    : "border border-line text-muted"
                }`}
                onClick={() => setX(preset.value)}
              >
                {preset.value.toLocaleString("en-US")}
              </button>
            ))}
          </div>
          <div className="flex flex-wrap gap-2">
            <button
              type="button"
              className={`rounded-full px-3 py-1 text-sm ${
                recursion === "star"
                  ? "bg-deep text-card"
                  : "border border-line text-muted"
              }`}
              onClick={() => setRecursion("star")}
            >
              (5.1) items 1+2
            </button>
            <button
              type="button"
              className={`rounded-full px-3 py-1 text-sm ${
                recursion === "pair"
                  ? "bg-deep text-card"
                  : "border border-line text-muted"
              }`}
              onClick={() => setRecursion("pair")}
            >
              (5.2) all three
            </button>
          </div>
        </div>
        <div className="grid gap-3 sm:grid-cols-4">
          <Metric
            label="x"
            value={x.toLocaleString("en-US")}
            hint={`√x = ${view.cuts.sqrt.toLocaleString("en-US")}`}
          />
          <Metric
            label={spec.name}
            value={root.toFixed(4)}
            hint={`printed ${spec.printed.toFixed(4)}`}
          />
          <Metric
            label="ζ(0)"
            value={(1 / 3).toFixed(3)}
            hint="Σ c − 1, both recursions"
          />
          <Metric
            label={`item ${selected} coeff`}
            value={formatCoeff(coeff)}
            hint={`scale ${source.scale === 0.5 ? "t/2" : source.scale === 0.375 ? "3t/8" : "3t/4"}`}
          />
        </div>
        <ThreeSourcesScale
          view={view}
          recursion={recursion}
          selected={selected}
          onSelect={setSelected}
        />
        <ThreeSourcesStacks
          view={view}
          recursion={recursion}
          selected={selected}
          onSelect={setSelected}
        />
      </section>

      <section className="space-y-3 rounded-xl border border-line bg-card p-4">
        <h2 className="font-serif text-2xl">
          <Tex>{String.raw`\zeta(\lambda)`}</Tex> for {spec.name}
        </h2>
        <p className="text-sm text-muted">
          Lemma 5.1 needs <Tex>{String.raw`\zeta>0`}</Tex> below the root.
          The plotted zeros are the printed Paper C values. Official{" "}
          <Tex>{String.raw`\lambda^{**}=0.4926`}</Tex> is a later-word root,
          not a three-source claim.{" "}
          <Tex>{String.raw`\zeta(0)=1/3`}</Tex> on both (5.1) and (5.2).
        </p>
        <p className="font-mono text-sm text-ink">{spec.equation}</p>
        <ZetaPlot recursion={recursion} onSelect={setRecursion} />
        <Metric
          label={`c e^λ at ${spec.name}`}
          value={
            coeff > 0
              ? (coeff * source.scale ** root).toFixed(4)
              : "0"
          }
          hint={
            coeff > 0
              ? `${formatCoeff(coeff)} · ${source.scale}^${root.toFixed(4)}`
              : "item 3 is off in (5.1)"
          }
        />
      </section>

      <Disclaimer>
        The three families exclude no fate and do not produce a halt theorem.
        The scale drawing is schematic. Official λ** is the V6 truncation.
      </Disclaimer>
    </div>
  );
}
