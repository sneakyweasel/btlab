import {
  CartesianGrid,
  Line,
  LineChart,
  ResponsiveContainer,
  Tooltip,
  XAxis,
  YAxis,
} from "recharts";
import { Metric } from "../../components/Metric";
import { StartControl } from "../../components/StartControl";
import { TrajectoryBeads } from "../../visuals/TrajectoryBeads";
import { usePlayState } from "../../context/PlayState";
import {
  NOTE_TRAJECTORY_3,
  NOTE_PEAK_37,
  TRAJECTORY_STEPS_MAX,
} from "../../juggler/constants";
import { formatInt, parsePositiveInt } from "../../juggler/format";
import { bitLength } from "../../juggler/map";
import { walkTrajectory } from "../../juggler/trajectory";

function chartY(state: bigint): number {
  if (state <= 0n) return 1;
  if (bitLength(state) <= 53) return Number(state);
  return 2 ** (bitLength(state) - 1);
}

export function TrajectoryTab() {
  const { nText, steps, setSteps } = usePlayState();
  const n = parsePositiveInt(nText);
  const view = n === null ? null : walkTrajectory(n, steps);
  const data =
    view?.rows.map((row) => ({
      step: row.step,
      value: chartY(row.state),
      letter: row.letter,
      shown: formatInt(row.state),
    })) ?? [];
  return (
    <div className="space-y-5">
      <p className="text-sm text-muted">
        Trajectory = the list of values. Word = the O/E parities of the prefix so
        far. Hitting 1 is one trajectory, not a theorem.
      </p>
      <StartControl />
      <label className="block text-sm text-muted">
        Step cap
        <input
          className="ml-2 align-middle"
          type="range"
          min={1}
          max={TRAJECTORY_STEPS_MAX}
          value={steps}
          onChange={(event) => setSteps(Number(event.target.value))}
        />
        <span className="ml-2 font-mono">{steps}</span>
      </label>
      {view ? (
        <>
          <div className="grid gap-3 sm:grid-cols-4">
            <Metric label="Word so far" value={view.word || "—"} />
            <Metric label="Steps" value={String(view.states.length - 1)} />
            <Metric
              label="Hit 1?"
              value={view.reachedOne ? "yes" : "no"}
              hint="one trajectory, not a theorem"
            />
            <Metric
              label="Last value"
              value={formatInt(view.states[view.states.length - 1])}
            />
          </div>
          {view.bitCapped || view.tooLarge ? (
            <p className="text-sm text-warn">
              A value exceeded the 256-bit display cap. The walk stopped.
            </p>
          ) : null}
          {n === 3n &&
          view.states.length >= NOTE_TRAJECTORY_3.length &&
          NOTE_TRAJECTORY_3.every((state, index) => view.states[index] === state) ? (
            <p className="text-sm text-ok">This is the note trajectory of 3.</p>
          ) : null}
          {n === 37n && view.states.includes(NOTE_PEAK_37) ? (
            <p className="text-sm text-ok">The recorded peak of 37 is on this walk.</p>
          ) : null}
          <div className="overflow-x-auto rounded-xl border border-line bg-card p-3">
            <TrajectoryBeads states={view.states.slice(0, 12)} />
          </div>
          <div className="h-72 rounded-xl border border-line bg-card p-3">
            <ResponsiveContainer width="100%" height="100%">
              <LineChart data={data}>
                <CartesianGrid stroke="#d4cbb8" strokeDasharray="3 3" />
                <XAxis dataKey="step" />
                <YAxis scale="log" domain={["auto", "auto"]} allowDataOverflow />
                <Tooltip
                  content={({ active, payload }) => {
                    if (!active || !payload?.[0]) return null;
                    const point = payload[0].payload as { shown: string };
                    return (
                      <div className="rounded border border-line bg-card px-2 py-1 font-mono text-sm">
                        {point.shown}
                      </div>
                    );
                  }}
                />
                <Line type="monotone" dataKey="value" stroke="#1f6f6a" dot />
              </LineChart>
            </ResponsiveContainer>
          </div>
          <details>
            <summary className="cursor-pointer text-sm text-muted">Step table</summary>
            <div className="mt-2 overflow-x-auto">
              <table className="w-full text-left text-sm">
                <thead>
                  <tr className="text-muted">
                    <th className="pr-3">step</th>
                    <th className="pr-3">state</th>
                    <th className="pr-3">letter</th>
                    <th>bits</th>
                  </tr>
                </thead>
                <tbody>
                  {view.rows.map((row) => (
                    <tr key={row.step}>
                      <td className="pr-3 font-mono">{row.step}</td>
                      <td className="pr-3 font-mono">{formatInt(row.state)}</td>
                      <td className="pr-3 font-mono">{row.letter || "—"}</td>
                      <td className="font-mono">{row.bits}</td>
                    </tr>
                  ))}
                </tbody>
              </table>
            </div>
          </details>
        </>
      ) : null}
    </div>
  );
}
