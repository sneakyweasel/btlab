import { EMBER, SEA } from "../juggler/palette";

type ItineraryBeadsProps = {
  word: string;
  onSelect?: (index: number) => void;
};

export function ItineraryBeads({ word, onSelect }: ItineraryBeadsProps) {
  if (word.length === 0) {
    return (
      <p className="text-center text-sm text-muted">
        Play to write the itinerary. Each bead is the next letter.
      </p>
    );
  }

  return (
    <ol className="m-0 flex list-none flex-wrap items-center justify-center gap-y-2 p-0">
      {word.split("").map((letter, index) => {
        const odd = letter === "O";
        const last = index === word.length - 1;
        return (
          <li key={`${index}-${letter}`} className="flex items-center">
            {index > 0 ? (
              <span className="w-3 text-center text-xs text-line" aria-hidden>
                —
              </span>
            ) : null}
            <button
              type="button"
              aria-current={last ? "step" : undefined}
              aria-label={`Letter ${index + 1}, ${odd ? "odd" : "even"} ${letter}`}
              disabled={!onSelect}
              onClick={() => onSelect?.(index)}
              className={`flex h-9 w-9 items-center justify-center rounded-full font-mono text-sm text-white ${
                onSelect ? "cursor-pointer" : "cursor-default"
              } ${last ? "ring-2 ring-ink ring-offset-2 ring-offset-card" : ""}`}
              style={{ background: odd ? EMBER : SEA }}
            >
              {letter}
            </button>
          </li>
        );
      })}
    </ol>
  );
}
