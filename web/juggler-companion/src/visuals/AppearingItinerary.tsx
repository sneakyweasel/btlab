type AppearingItineraryProps = {
  itinerary: string;
  revealed: number;
  note?: string | null;
};

export function AppearingItinerary({ itinerary, revealed, note }: AppearingItineraryProps) {
  const shown = Math.max(0, Math.min(revealed, itinerary.length));
  const prefix = itinerary.slice(0, shown);
  const oddCount = [...prefix].filter((letter) => letter === "O").length;
  return (
    <div className="flex h-full flex-col rounded-2xl border border-line bg-paper/70 px-4 py-3">
      <p className="text-xs uppercase tracking-wide text-muted">Itinerary</p>
      <p className="mt-1 text-sm text-muted">
        The trajectory is the list of values. The itinerary is the parities: O or E.
      </p>
      {itinerary ? (
        <p className="mt-2 font-mono text-2xl leading-snug tracking-wide break-all">
          {itinerary.split("").map((letter, index) => {
            const visible = index < shown;
            const odd = letter === "O";
            return (
              <span
                key={`${index}-${letter}`}
                className={
                  visible ? (odd ? "text-odd" : "text-even") : "text-line"
                }
              >
                {letter}
              </span>
            );
          })}
        </p>
      ) : (
        <p className="mt-2 text-sm text-muted">No letters yet.</p>
      )}
      {shown > 0 ? (
        <p className="mt-2 font-mono text-sm text-ink">
          Ideal exponent of this prefix: 3<sup>{oddCount}</sup>/2
          <sup>{shown}</sup>
          <span className="ml-1 font-sans text-muted">
            ({oddCount} odd {oddCount === 1 ? "letter" : "letters"}, {shown}{" "}
            {shown === 1 ? "step" : "steps"}; floors are not in this ratio)
          </span>
        </p>
      ) : null}
      <p className="mt-auto pt-3 text-sm text-muted">
        {itinerary.length === 0
          ? "The browser did not write an itinerary for this start."
          : shown === 0
            ? "A letter appears only when this walk takes that step — that is a realized itinerary. Play or step to see it."
            : shown < itinerary.length
              ? `${shown} of ${itinerary.length} letters realized. O is odd, E is even.`
              : `${itinerary.length} letters realized. O is odd, E is even.`}
        {note ? ` ${note}` : ""}
      </p>
    </div>
  );
}
