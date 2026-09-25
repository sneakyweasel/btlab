import { useDeferredValue, useEffect, useMemo, useState, type ReactNode } from "react";
import { Link } from "react-router-dom";
import { Metric } from "../components/Metric";
import { Tex } from "../components/Tex";
import "../components/beatty.css";
import {
  EVIDENCE_LABEL, GAME_FAMILIES, SLOPES, lawDim, lowerDim, patternNu, starDim, twoScaleDim, upperDim,
  type Element, type Evidence, type Pattern,
} from "../juggler/beattyAtlas";
import { BEATTY } from "../juggler/beatty";
import { AtlasDimensionMap, type MapPoint } from "../visuals/AtlasDimensionMap";
import { AtlasGame } from "../visuals/AtlasGame";
import { AtlasGrowth } from "../visuals/AtlasGrowth";
import { AtlasTube } from "../visuals/AtlasTube";
import { AtlasTwoScale } from "../visuals/AtlasTwoScale";

const MAX_ELEMENTS = 8;

const samePattern = (a: Pattern, b: Pattern) => a.length === b.length && a.every((e, i) => e.kind === b[i].kind && e.t === b[i].t);

function Badge({ evidence, claim, source }: { evidence: Evidence; claim?: string; source?: string }) {
  return (
    <span className="atlas-evidence">
      <span className={`atlas-badge atlas-badge-${evidence.toLowerCase()}`}>{EVIDENCE_LABEL[evidence]}</span>
      {claim && <code className="atlas-claim">{claim}</code>}
      {source && <span className="atlas-claim">{source}</span>}
    </span>
  );
}

function Fact({ evidence, claim, source, children }: { evidence: Evidence; claim?: string; source?: string; children: ReactNode }) {
  return (
    <li className="atlas-fact">
      <span>{children}</span>
      <Badge evidence={evidence} claim={claim} source={source} />
    </li>
  );
}

function Panel({ eyebrow, title, children }: { eyebrow: string; title: string; children: ReactNode }) {
  return (
    <section className="space-y-4 rounded-xl border border-line bg-card p-4 sm:p-6">
      <header>
        <p className="text-xs uppercase tracking-[0.18em] text-muted">{eyebrow}</p>
        <h2 className="mt-1 text-2xl">{title}</h2>
      </header>
      {children}
    </section>
  );
}

function useNoIndex() {
  useEffect(() => {
    const meta = document.createElement("meta");
    meta.name = "robots";
    meta.content = "noindex, nofollow";
    document.head.appendChild(meta);
    const title = document.title;
    document.title = "Beatty atlas";
    return () => { meta.remove(); document.title = title; };
  }, []);
}

const clampT = (kind: Element["kind"], t: number) => Math.min(kind === "g" ? 50 : 1e9, Math.max(kind === "g" ? 1.01 : 1.01, t));

export default function BeattyAtlasPage() {
  useNoIndex();
  const [slopeKey, setSlopeKey] = useState("log23");
  const slope = SLOPES.find(s => s.key === slopeKey)!;
  const [pattern, setPattern] = useState<Pattern>(GAME_FAMILIES[4].pattern);
  const deferred = useDeferredValue(pattern);
  const result = useMemo(() => {
    const upper = upperDim(deferred);
    const { s: lower, gammas } = lowerDim(deferred, 12);
    return { upper, lower, gammas, nu: patternNu(deferred) };
  }, [deferred]);
  const twoScale = pattern.length === 2 && pattern[0].kind === "g" && pattern[1].kind === "d"
    ? { nu: pattern[0].t, rho: pattern[1].t } : null;
  const points: MapPoint[] = [
    { nu: result.nu, s: result.lower, label: "game value", tone: "model" },
    ...(slope.nu ? [{ nu: slope.nu[0], s: slope.dim[0], label: slope.name, tone: "slope" as const }] : []),
  ];
  const edit = (index: number, next: Partial<Element>) =>
    setPattern(pattern.map((e, i) => {
      if (i !== index) return e;
      const kind = next.kind ?? e.kind;
      return { kind, t: clampT(kind, next.t ?? e.t) };
    }));

  return (
    <div className="space-y-6">
      <header className="space-y-3">
        <p className="text-xs uppercase tracking-[0.18em] text-muted">Beatty first passage · working view</p>
        <h1 className="text-4xl">Dimension atlas</h1>
        <p className="prose-measure text-muted">
          For an irrational slope α &gt; 1 the binomial-normalized first-passage counts
          accumulate on a compact null set <Tex>{String.raw`K_\alpha`}</Tex> with singular
          limit law <Tex>{String.raw`\mu_\alpha`}</Tex>. Its Minkowski and packing
          dimensions are 2/3 for every slope, while its Hausdorff dimension depends on how
          fast the convergent denominators of α grow. This page tracks that dependence:
          what is proved, what is written, and what the exponent model predicts.
        </p>
        <ul className="flex flex-wrap gap-2 text-xs" aria-label="Evidence labels">
          {(["LEAN", "HUMAN", "OBSERVATION", "CONJECTURE"] as const).map(e =>
            <li key={e}><span className={`atlas-badge atlas-badge-${e.toLowerCase()}`}>{EVIDENCE_LABEL[e]}</span></li>)}
        </ul>
      </header>

      <Panel eyebrow="1 · Slope" title="Continued fraction and growth">
        <div className="flex flex-wrap gap-2" role="radiogroup" aria-label="Slope">
          {SLOPES.map(s => (
            <button key={s.key} type="button" role="radio" aria-checked={s.key === slopeKey} onClick={() => setSlopeKey(s.key)}
              className={`rounded-full px-3 py-1 text-sm ${s.key === slopeKey ? "bg-deep text-card" : "border border-line text-muted"}`}>
              {s.name}
            </button>
          ))}
        </div>
        <div className="flex flex-wrap items-baseline gap-x-4 gap-y-1">
          <span className="text-xl"><Tex>{`\\alpha=${slope.tex}`}</Tex></span>
          {slope.quotients.length > 0 && <code className="text-xs break-all text-muted">
            [{slope.quotients[0]}; {slope.quotients.slice(1, 28).join(", ")}{slope.quotients.length > 28 ? ", …" : ""}]
          </code>}
        </div>
        <p className="text-xs text-muted">Partial quotients: {slope.quotientsSource}.</p>
        <AtlasGrowth quotients={slope.quotients} />
        {slope.quotients.length > 0 && <p className="text-sm text-muted">
          Since <Tex>{String.raw`|Q_k\alpha-P_k|\asymp Q_{k+1}^{-1}`}</Tex>, the class ν is the limsup of these
          ratios. A finite prefix cannot determine it: the bars show where large partial quotients sit, not ν.
        </p>}
        <ul className="space-y-2">
          {slope.statements.map(s => <Fact key={s.text} evidence={s.evidence} claim={s.claim} source={s.source}>{s.text}</Fact>)}
        </ul>
      </Panel>

      <Panel eyebrow="2 · Map" title="Hausdorff dimension against the Diophantine class">
        <AtlasDimensionMap points={points} onPick={nu => setPattern([{ kind: "g", t: nu }])} />
        <ul className="space-y-2">
          <Fact evidence="LEAN" claim="J-beatty-slope-packing-dim">Packing dimension of <Tex>{String.raw`K_\alpha`}</Tex> is 2/3 for every irrational slope; the law has packing dimension 2/3 too (<code>J-beatty-slope-law-packing</code>).</Fact>
          <Fact evidence="LEAN" claim="J-beatty-slope-law-dimension">The limit law has Hausdorff dimension exactly 2/(2+ν), a function of the class alone.</Fact>
          <Fact evidence="LEAN" claim="J-beatty-slope-star-upper">For class ν &gt; 1, <Tex>{String.raw`2/(2+\nu)\le\dim_H K_\alpha\le s^*(\nu)=\tfrac{2(\sqrt{1+3\nu}-1)}{3\nu}`}</Tex>.</Fact>
          <Fact evidence="LEAN" claim="J-beatty-slope-regular-exact-dim">Regular growth <Tex>{String.raw`Q_{n+1}\asymp Q_n^\nu`}</Tex> attains the lower curve.</Fact>
          <Fact evidence="LEAN" claim="J-beatty-slope-isolated-exact">Sparse isolated good levels attain the upper curve, so dim_H K is not a function of the class.</Fact>
          <Fact evidence="LEAN" claim="J-beatty-slope-ae-hausdorff-dimension">Almost every slope sits at ν = 1, where both curves meet at 2/3.</Fact>
        </ul>
        {!slope.nu && <p className="text-sm text-muted">
          {slope.name} is not placed on the map: {slope.key === "liouville" ? "its class is infinite and dim_H K = 0." : `its class is unknown; the recorded range is ${slope.dim[0]} ≤ dim_H K ≤ 2/3.`}
        </p>}
      </Panel>

      <Panel eyebrow="3 · Phase 1" title="Two-scale slopes: a jump ν, then a dense stretch ρ">
        <p className="prose-measure text-sm text-muted">
          Between the two curves the answer depends on the whole growth sequence. For the two-scale family the
          dimension is <Tex>{String.raw`2/(2+\nu)`}</Tex> while <Tex>{String.raw`\rho\le1+3/\nu`}</Tex>, and otherwise
          the positive root of <Tex>{String.raw`3(R-1)s^2+4(\rho-1)s-4(\rho-1)=0`}</Tex> with <Tex>{String.raw`R=\rho\nu`}</Tex>;
          it tends to <Tex>{String.raw`s^*(\nu)`}</Tex> as ρ → ∞.
        </p>
        <AtlasTwoScale selected={twoScale} onPick={(nu, rho) => setPattern([{ kind: "g", t: nu }, { kind: "d", t: rho }])} />
        <ul className="space-y-2">
          <Fact evidence="HUMAN" source="note §33, not refereed">Written proof of both bounds for two-scale slopes.</Fact>
          <Fact evidence="OBSERVATION" source="beatty_dimension_game.py">The cover and window recursions reproduce the closed form to 1e−15.</Fact>
        </ul>
        <p className="text-sm text-muted">Next: the Lean lower bound, replacing the isolated-levels sparsity with a growth ratio.</p>
      </Panel>

      <Panel eyebrow="4 · Exponent model" title="The dimension game">
        <p className="prose-measure text-sm text-muted">
          A slope is modelled by its log-scales <Tex>{String.raw`\Lambda_k=\log Q_k`}</Tex>: a jump multiplies Λ by t, a dense
          stretch of bounded quotients by ρ. The cover recursion gives an upper threshold; the window measure, with an
          exponent <Tex>{String.raw`\gamma\in[1,t]`}</Tex> at each jump, a lower one. Constants are dropped: this locates
          where the two methods meet and proves nothing.
        </p>
        <div className="flex flex-wrap items-end gap-3">
          <label className="grid gap-1 text-sm">
            <span className="text-muted">Family</span>
            <select className="atlas-input" value={GAME_FAMILIES.find(f => samePattern(f.pattern, pattern))?.name ?? ""}
              onChange={event => { const f = GAME_FAMILIES.find(x => x.name === event.target.value); if (f) setPattern(f.pattern); }}>
              <option value="" disabled>custom pattern</option>
              {GAME_FAMILIES.map(f => <option key={f.name} value={f.name}>{f.name}</option>)}
            </select>
          </label>
          <button type="button" className="atlas-button" disabled={pattern.length >= MAX_ELEMENTS} onClick={() => setPattern([...pattern, { kind: "g", t: 2 }])}>Add jump</button>
          <button type="button" className="atlas-button" disabled={pattern.length >= MAX_ELEMENTS} onClick={() => setPattern([...pattern, { kind: "d", t: 5 }])}>Add dense stretch</button>
        </div>
        <ol className="flex flex-wrap gap-2" aria-label="Periodic pattern">
          {pattern.map((e, i) => (
            <li key={i} className="flex items-center gap-1 rounded-lg border border-line px-2 py-1 text-sm">
              <select aria-label={`Element ${i + 1} kind`} className="atlas-input" value={e.kind} onChange={event => edit(i, { kind: event.target.value as Element["kind"] })}>
                <option value="g">jump t</option>
                <option value="d">dense ρ</option>
              </select>
              <input aria-label={`Element ${i + 1} value`} className="atlas-input w-24" type="number" step={e.kind === "g" ? 0.1 : 1} min={1.01}
                value={e.t} onChange={event => { const t = Number(event.target.value); if (Number.isFinite(t) && t > 1) edit(i, { t }); }} />
              <button type="button" aria-label={`Remove element ${i + 1}`} className="px-1 text-muted" disabled={pattern.length <= 1}
                onClick={() => setPattern(pattern.filter((_, j) => j !== i))}>×</button>
            </li>
          ))}
        </ol>
        <div className="grid grid-cols-2 gap-3 md:grid-cols-4">
          <Metric label="Window measure (lower)" value={result.lower.toFixed(9)} />
          <Metric label="Cover recursion (upper)" value={result.upper.toFixed(9)} />
          <Metric label="Gap" value={(result.upper - result.lower).toExponential(1)} hint={result.upper - result.lower < 1e-6 ? "methods meet" : "marginal or separated"} />
          <Metric label="Class: largest jump" value={result.nu.toFixed(3)}
            hint={`law ${lawDim(result.nu).toFixed(4)} · s* ${starDim(result.nu).toFixed(4)}`} />
        </div>
        {twoScale && <p className="text-sm text-muted tabular-nums">Two-scale closed form: {twoScaleDim(twoScale.nu, twoScale.rho).s.toFixed(9)}.</p>}
        <AtlasGame pattern={deferred} upper={result.upper} lower={result.lower} gammas={result.gammas} nu={result.nu} />
        <ul className="space-y-2">
          <Fact evidence="OBSERVATION" source="dimension_game.json">Upper and lower agree on all 15 committed periodic families and 19 random patterns; residuals at marginal thresholds shrink with the iteration count.</Fact>
          <Fact evidence="CONJECTURE" source="dossier">For every irrational α &gt; 1, dim_H K_α equals the value of this game along its growth sequence.</Fact>
        </ul>
      </Panel>

      <Panel eyebrow="5 · Geometry" title="Neighbourhood volume at log₂3">
        <AtlasTube />
        <ul className="space-y-2">
          <Fact evidence="LEAN" claim="J-beatty-certificate-cantor-dimension">vol(K_ε) = 2ε + Σ_r min(w_r, 2ε), bounded above and below by constant multiples of ε^(1/3).</Fact>
          <Fact evidence="LEAN" claim="J-beatty-slope-minkowski-dimension">Minkowski dimension 2/3 for every irrational slope.</Fact>
        </ul>
        <p className="text-sm text-muted">
          The curve uses the display weights of the first 5,047 gaps; the dashed curve adds the certified omitted-mass
          bound {BEATTY.tailUpper}. It is a picture of the formula, not a certificate for any ε. The certified profile
          itself is in <Link to="/play/beatty-profile">Beatty profile</Link>.
        </p>
      </Panel>

      <p className="text-xs text-muted">
        Sources: the working note <code>docs/theory/juggler_beatty_first_passage_note.md</code>, the dossier
        <code> docs/problems/juggler_winkler_phase_collapse.md</code> and the claim ledger. Finite pictures do not
        establish orbit termination.
      </p>
    </div>
  );
}
