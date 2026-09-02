import { usePlayState } from "../context/PlayState";
import { N_PRESETS } from "../juggler/constants";
import { parsePositiveInt } from "../juggler/format";

export function StartControl() {
  const { nText, setNText } = usePlayState();
  const parsed = parsePositiveInt(nText);
  return (
    <div className="flex flex-wrap items-end gap-3">
      <label className="text-sm text-muted">
        Start n
        <input
          className="ml-2 rounded border border-line bg-card px-2 py-1 font-mono"
          value={nText}
          onChange={(event) => setNText(event.target.value)}
          inputMode="numeric"
        />
      </label>
      <select
        className="rounded border border-line bg-card px-2 py-1 text-sm"
        value=""
        onChange={(event) => {
          if (event.target.value) setNText(event.target.value);
        }}
      >
        <option value="">Presets</option>
        {N_PRESETS.map((preset) => (
          <option key={preset.value.toString()} value={preset.value.toString()}>
            {preset.label}
          </option>
        ))}
      </select>
      {parsed === null ? (
        <span className="text-sm text-warn">Enter a positive integer.</span>
      ) : null}
    </div>
  );
}
