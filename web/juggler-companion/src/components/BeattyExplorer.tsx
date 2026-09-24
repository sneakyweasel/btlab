import { useState } from "react";
import { BEATTY, beattyBounds, beattyPhase, beattyRow, type BeattyLayers, type BeattySamples, type BeattySelection } from "../juggler/beatty";
import { BeattyProfile } from "../visuals/BeattyProfile";
import "./beatty.css";

const LAYERS: { key: keyof BeattyLayers; label: string; swatch: string }[] = [
  { key: "profile", label: "Profile F₅₀₄₇", swatch: "profile" },
  { key: "band", label: "Certified tail band", swatch: "band" },
  { key: "samples", label: "R⁺ samples", swatch: "sample" },
  { key: "gaps", label: "Certified gap interiors", swatch: "gap" },
];

export function BeattyExplorer() {
  const [selection, setSelection] = useState<BeattySelection>({ kind: "jump", order: 1 });
  const [orderText, setOrderText] = useState("1");
  const [focused, setFocused] = useState(false);
  const [range, setRange] = useState<BeattySamples>("late");
  const [layers, setLayers] = useState<BeattyLayers>({ profile: true, band: true, samples: true, gaps: true });
  const phase = beattyPhase(selection);
  const row = selection.kind === "jump" ? beattyRow(selection.order) : null;
  const bounds = beattyBounds(phase);
  const core = row && BEATTY.cores.find(c => c.order === row.order);
  const validOrder = orderText.trim() !== "" && Number.isInteger(Number(orderText)) && Number(orderText) >= 1 && Number(orderText) <= BEATTY.orders;

  function select(next: BeattySelection) {
    setSelection(next);
    if (next.kind === "jump") setOrderText(String(next.order));
  }

  return (
    <div className="beatty-explorer rounded-2xl border border-line bg-card p-3 sm:p-5">
      <div className="beatty-controls">
        <label>Jump order r
          <input type="number" min={1} max={BEATTY.orders} step={1} value={orderText} aria-invalid={!validOrder} aria-describedby={!validOrder ? "beatty-order-error" : undefined}
            onChange={event => {
              const value = event.target.value;
              setOrderText(value);
              const order = Number(value);
              if (value.trim() && Number.isInteger(order) && order >= 1 && order <= BEATTY.orders) setSelection({ kind: "jump", order });
            }} />
        </label>
        <label>View
          <select value={focused ? "focus" : "full"} onChange={event => setFocused(event.target.value === "focus")}>
            <option value="full">Whole profile</option><option value="focus">Around selection</option>
          </select>
        </label>
        <label>Exact-count samples
          <select value={range} onChange={event => setRange(event.target.value as BeattySamples)}>
            <option value="late">r = 4,048–5,047</option><option value="early">r = 1–1,000</option><option value="all">All 5,047 orders</option>
          </select>
        </label>
      </div>
      {!validOrder && <p id="beatty-order-error" role="alert" className="mt-2 text-sm text-warn">Choose an integer from 1 to 5,047. The plot keeps the last valid selection.</p>}
      <label className="mt-5 block text-sm">
        <span className="flex justify-between gap-3"><span>Phase t</span><output className="font-mono tabular-nums">{phase.toFixed(6)}</output></span>
        <input aria-label="Inspect Beatty phase" type="range" min={0} max={1} step={0.00001} value={phase}
          className="mt-2 w-full accent-even" onChange={event => select({ kind: "phase", phase: Number(event.target.value) })} />
      </label>
      <div className="beatty-legend" aria-label="Chart layers">
        {LAYERS.map(layer => <button key={layer.key} type="button" aria-pressed={layers[layer.key]} onClick={() => setLayers(previous => ({ ...previous, [layer.key]: !previous[layer.key] }))}>
          <span className={`beatty-swatch beatty-swatch-${layer.swatch}`} aria-hidden="true" />{layer.label}
        </button>)}
      </div>
      <BeattyProfile selection={selection} focused={focused} range={range} layers={layers} onSelect={select} />
      <div className="beatty-detail text-sm" aria-live="polite">
        <span>{row ? `Jump r = ${row.order}` : `Phase t = ${phase.toFixed(6)}`}</span>
        <span>F(t) ∈ [{bounds[0].toFixed(6)}, {bounds[1].toFixed(6)}]</span>
        {row && <><span>wᵣ ≈ {row.weight.toFixed(6)}</span><span>R⁺ᵣ ≈ {row.ratio.toFixed(6)}</span></>}
      </div>
      {row && <p className="mt-2 text-sm text-muted">{core ? "The selected jump’s certified gap interior is highlighted on the value axis." : "This jump is too small to resolve a certified gap interior with the current tail bound."}</p>}
      <div className="beatty-notes text-xs text-muted">
        <span>5,047 jumps · omitted tail &lt; 0.020220</span>
        <span>Filled: left value · hollow: right trace</span>
        <span><span className="beatty-swatch beatty-swatch-unresolved" aria-hidden="true" /> Remaining strip: unresolved</span>
      </div>
      <details className="mt-4 border-t border-line pt-3 text-xs text-muted">
        <summary className="cursor-pointer">Data and numerical scope</summary>
        <p className="mt-2">Figure snapshot: {BEATTY.generatedUtc.slice(0, 10)} · exact counts to depth {BEATTY.depth.toLocaleString("en-US")} · {BEATTY.precisionBits}-bit Arb enclosures.</p>
        <p className="mt-2">{BEATTY.scope}</p>
        <p className="mt-2 break-all">Source: {BEATTY.source}<br />SHA-256: <code>{BEATTY.sourceSha256}</code></p>
      </details>
    </div>
  );
}
