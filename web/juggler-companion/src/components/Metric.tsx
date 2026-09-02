type MetricProps = {
  label: string;
  value: string;
  hint?: string;
};

export function Metric({ label, value, hint }: MetricProps) {
  return (
    <div className="min-w-0 rounded-lg border border-line bg-card px-3 py-3">
      <div className="text-xs uppercase tracking-wide text-muted">{label}</div>
      <div className="mt-1 font-mono text-lg break-all text-ink">{value}</div>
      {hint ? <div className="mt-1 text-xs text-muted">{hint}</div> : null}
    </div>
  );
}
