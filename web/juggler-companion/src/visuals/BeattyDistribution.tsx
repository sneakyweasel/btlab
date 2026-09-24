import { useEffect, useId, useMemo, useRef, useState } from "react";
import { BEATTY, BEATTY_LIMIT_CDF, beattyCDFAt, beattyEmpiricalCDF, beattyLimitCDFBounds, beattySamples, type BeattyCDFPoint, type BeattySamples } from "../juggler/beatty";

function clipTrace(points: readonly BeattyCDFPoint[], min: number, max: number): BeattyCDFPoint[] {
  return [
    { value: min, cumulative: beattyCDFAt(points, min) },
    ...points.filter(point => point.value > min && point.value < max),
    { value: max, cumulative: beattyCDFAt(points, max) },
  ];
}

export function BeattyDistribution({ range }: { range: BeattySamples }) {
  const container = useRef<HTMLDivElement>(null);
  const [width, setWidth] = useState(720);
  const [value, setValue] = useState(1.5);
  const titleId = useId(), descriptionId = useId(), clipId = useId();
  const empirical = useMemo(() => beattyEmpiricalCDF(range), [range]);
  const sampleCount = beattySamples(range).length;
  const [lower, upper] = beattyLimitCDFBounds(value);
  const actual = beattyCDFAt(empirical, value);
  const geometry = useMemo(() => {
    const height = 300, left = 58, right = width - 16, top = 16, bottom = height - 48;
    const min = Math.min(1, empirical[0].value) - 0.02;
    const max = Math.max(BEATTY.envelope, empirical[empirical.length - 1].value) + 0.02;
    const x = (v: number) => left + (v - min) / (max - min) * (right - left);
    const y = (p: number) => bottom - p * (bottom - top);
    const stepPath = (points: readonly BeattyCDFPoint[]) => points.map((point, index) => `${index ? "H" : "M"}${x(point.value)}${index ? "V" : ","}${y(point.cumulative)}`).join("");
    const lowerPoints = clipTrace(BEATTY_LIMIT_CDF.lower, min, max);
    const upperPoints = clipTrace(BEATTY_LIMIT_CDF.upper, min, max);
    let band = stepPath(upperPoints) + `L${x(max)},${y(lowerPoints[lowerPoints.length - 1].cumulative)}`;
    for (let index = lowerPoints.length - 2; index >= 0; index--) band += `V${y(lowerPoints[index].cumulative)}H${x(lowerPoints[index].value)}`;
    band += "Z";
    const tickCount = width < 480 ? 3 : 6;
    const ticks = Array.from({ length: tickCount + 1 }, (_, index) => min + index * (max - min) / tickCount);
    return { height, left, right, top, bottom, min, max, x, y, band, lowerPath: stepPath(lowerPoints), upperPath: stepPath(upperPoints), empiricalPath: stepPath(clipTrace(empirical, min, max)), ticks };
  }, [width, empirical]);
  useEffect(() => {
    if (!container.current) return;
    const observer = new ResizeObserver(([entry]) => setWidth(Math.max(230, entry.contentRect.width)));
    observer.observe(container.current);
    return () => observer.disconnect();
  }, []);
  const g = geometry;
  return (
    <section aria-label="Empirical and limiting distributions" className="mt-4 space-y-3">
      <p className="text-sm text-muted">
        {sampleCount.toLocaleString("en-US")} samples · {range === "late" ? "r = 4,048–5,047" : range === "early" ? "r = 1–1,000" : "r = 1–5,047"} · all phases.
        The sample range follows the selector above; profile zoom does not filter this view.
      </p>
      <div className="beatty-legend" aria-label="Distribution legend">
        <span><span className="beatty-swatch beatty-swatch-empirical" aria-hidden="true" />Empirical R⁺ CDF</span>
        <span><span className="beatty-swatch beatty-swatch-band" aria-hidden="true" />Limiting CDF enclosure</span>
      </div>
      <div ref={container}>
        <svg viewBox={`0 0 ${width} ${g.height}`} height={g.height} className="beatty-chart" role="img" aria-labelledby={`${titleId} ${descriptionId}`}>
          <title id={titleId}>Empirical distribution of normalized counts against the limiting law of F(U)</title>
          <desc id={descriptionId}>The orange step curve is the proportion of samples at or below each value. The green band encloses the limiting cumulative distribution using the existing omitted-tail bound. The finite-step bounds are not the exact continuous limiting CDF.</desc>
          <defs><clipPath id={clipId}><rect x={g.left} y={g.top} width={g.right - g.left} height={g.bottom - g.top} /></clipPath></defs>
          <rect x={g.left} y={g.top} width={g.right - g.left} height={g.bottom - g.top} fill="none" stroke="var(--color-line)" />
          {[0, .25, .5, .75, 1].map(tick => <g key={tick}>
            <line x1={g.left} x2={g.right} y1={g.y(tick)} y2={g.y(tick)} stroke="var(--color-line)" strokeWidth={.6} />
            <text x={g.left - 8} y={g.y(tick) + 4} textAnchor="end">{(tick * 100).toFixed(0)}%</text>
          </g>)}
          {g.ticks.map((tick, index) => <text key={tick} x={g.x(tick)} y={g.bottom + 20} textAnchor={index === 0 ? "start" : index === g.ticks.length - 1 ? "end" : "middle"}>{tick.toFixed(2)}</text>)}
          <text x={(g.left + g.right) / 2} y={g.height - 7} textAnchor="middle">Value y</text>
          <text transform={`translate(13,${(g.top + g.bottom) / 2}) rotate(-90)`} textAnchor="middle">Cumulative probability</text>
          <g clipPath={`url(#${clipId})`}>
            <path data-cdf="band" d={g.band} fill="var(--color-even)" opacity={.18} />
            <path d={g.lowerPath} fill="none" stroke="var(--color-even)" strokeWidth={.8} strokeDasharray="3 3" />
            <path d={g.upperPath} fill="none" stroke="var(--color-even)" strokeWidth={.8} strokeDasharray="3 3" />
            <path data-cdf="empirical" d={g.empiricalPath} fill="none" stroke="var(--color-odd)" strokeWidth={1.6} />
            <line x1={g.x(value)} x2={g.x(value)} y1={g.top} y2={g.bottom} stroke="var(--color-muted)" strokeWidth={.8} />
            <circle cx={g.x(value)} cy={g.y(actual)} r={3.5} fill="var(--color-odd)" />
          </g>
        </svg>
      </div>
      <label className="block text-sm">
        <span className="flex justify-between"><span>Inspect value y</span><output className="font-mono">{value.toFixed(3)}</output></span>
        <input type="range" aria-label="Inspect distribution value" min={g.min} max={g.max} step={.001} value={value} className="mt-2 w-full accent-even" onChange={event => setValue(Number(event.target.value))} />
      </label>
      <p className="text-sm tabular-nums" aria-live="polite">
        Samples ≤ y: {Math.round(actual * sampleCount).toLocaleString("en-US")} / {sampleCount.toLocaleString("en-US")} ({(actual * 100).toFixed(2)}%).
        {" "}P(F(U) ≤ y) ∈ [{(Math.floor(lower * 1e6) / 1e4).toFixed(4)}%, {(Math.ceil(upper * 1e6) / 1e4).toFixed(4)}%].
      </p>
      <p className="text-xs text-muted">
        Uniform phase weights each plateau by its phase-interval length. From Fₘ ≤ F ≤ Fₘ + T,
        the CDF bounds are Hₘ(y − T) ≤ P(F(U) ≤ y) ≤ Hₘ(y), with T &lt; 0.020220.
        The band includes padding for rounded display coordinates; it is not a finite-sample confidence band or a convergence-rate estimate.
      </p>
    </section>
  );
}
