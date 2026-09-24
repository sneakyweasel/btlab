import { useState } from "react";
import { BEATTY, beattyBounds, beattyPhase, beattyResidualBounds, beattyRow, type BeattyLayers, type BeattySamples, type BeattySelection } from "../juggler/beatty";
import { BeattyProfile } from "../visuals/BeattyProfile";
import { BeattyDistribution } from "../visuals/BeattyDistribution";
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
  const [showDistribution, setShowDistribution] = useState(false);
  const [layers, setLayers] = useState<BeattyLayers>({ profile: true, band: true, samples: true, gaps: true });
  const phase = beattyPhase(selection);
  const row = selection.kind === "jump" ? beattyRow(selection.order) : null;
  const bounds = beattyBounds(phase);
  const residual = row ? beattyResidualBounds(row.order) : null;
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
            onKeyDown={event => { if (event.key === "Enter" && validOrder) select({ kind: "jump", order: Number(orderText) }); }}
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
      {row && residual ? <div className="mt-4" aria-live="polite">
        <p className="mb-2 text-sm text-muted">Selected index r = {row.order} · R⁺ᵣ ≈ {row.ratio.toFixed(9)}</p>
        <dl className="beatty-quantities">
          <div data-quantity="phase"><dt>δᵣ · phase</dt><dd>≈ {row.phase.toFixed(9)}</dd></div>
          <div data-quantity="weight"><dt>wᵣ · jump size</dt><dd>≈ {row.weight.toPrecision(8)}</dd></div>
          <div data-quantity="profile"><dt>F(δᵣ) · enclosure</dt><dd>[{bounds[0].toFixed(6)}, {bounds[1].toFixed(6)}]</dd><small>F₅₀₄₇(δᵣ) ≈ {row.left.toFixed(9)}</small></div>
          <div data-quantity="residual"><dt>R⁺ᵣ − F(δᵣ) · enclosure</dt><dd>[{residual[0].toFixed(6)}, {residual[1].toFixed(6)}]</dd><small>{residual[0] <= 0 && residual[1] >= 0 ? "Sign unresolved at this cutoff" : residual[1] < 0 ? "Negative throughout the enclosure" : "Positive throughout the enclosure"}</small></div>
        </dl>
        <p className="mt-2 text-xs text-muted">F and the residual use the omitted-tail bound; neither is presented as an exact point value.</p>
      </div> : <div className="beatty-detail text-sm" aria-live="polite">
        <span>Phase t = {phase.toFixed(6)}</span><span>F(t) ∈ [{bounds[0].toFixed(6)}, {bounds[1].toFixed(6)}]</span>
        <button type="button" className="underline text-deep" onClick={() => select({ kind: "jump", order: validOrder ? Number(orderText) : 1 })}>Inspect jump r = {validOrder ? orderText : "1"}</button>
      </div>}
      <div className="beatty-legend" aria-label="Chart layers">
        {LAYERS.map(layer => <button key={layer.key} type="button" aria-pressed={layers[layer.key]} onClick={() => setLayers(previous => ({ ...previous, [layer.key]: !previous[layer.key] }))}>
          <span className={`beatty-swatch beatty-swatch-${layer.swatch}`} aria-hidden="true" />{layer.label}
        </button>)}
      </div>
      <BeattyProfile selection={selection} focused={focused} range={range} layers={layers} onSelect={select} />
      {row && <p className="mt-2 text-sm text-muted">{core ? "The selected jump’s certified gap interior is highlighted on the value axis." : "This jump is too small to resolve a certified gap interior with the current tail bound."}</p>}
      <div className="beatty-notes text-xs text-muted">
        <span>5,047 jumps · omitted tail &lt; 0.020220</span>
        <span>Filled: left value · hollow: right trace</span>
        <span><span className="beatty-swatch beatty-swatch-unresolved" aria-hidden="true" /> Remaining strip: unresolved</span>
      </div>
      <details className="mt-5 border-t border-line pt-4" onToggle={event => setShowDistribution(event.currentTarget.open)}>
        <summary className="cursor-pointer text-sm font-medium">Compare empirical and limiting distributions</summary>
        {showDistribution && <BeattyDistribution range={range} />}
      </details>
      <details className="mt-4 border-t border-line pt-3 text-xs text-muted">
        <summary className="cursor-pointer">Data and numerical scope</summary>
        <p className="mt-2">Figure snapshot: {BEATTY.generatedUtc.slice(0, 10)} · exact counts to depth {BEATTY.depth.toLocaleString("en-US")} · {BEATTY.precisionBits}-bit Arb enclosures.</p>
        <p className="mt-2">{BEATTY.scope}</p>
        <p className="mt-2 break-all">Source: {BEATTY.source}<br />SHA-256: <code>{BEATTY.sourceSha256}</code></p>
      </details>
    </div>
  );
}
