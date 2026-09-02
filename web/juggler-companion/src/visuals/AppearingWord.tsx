type AppearingWordProps = {
  word: string;
  revealed: number;
  note?: string | null;
};

export function AppearingWord({ word, revealed, note }: AppearingWordProps) {
  const shown = Math.max(0, Math.min(revealed, word.length));
  return (
    <div className="flex h-full flex-col rounded-2xl border border-line bg-paper/70 px-4 py-3">
      <p className="text-xs uppercase tracking-wide text-muted">Word</p>
      {word ? (
        <p className="mt-2 font-mono text-2xl leading-snug tracking-wide break-all">
          {word.split("").map((letter, index) => {
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
      <p className="mt-auto pt-3 text-sm text-muted">
        {word.length === 0
          ? "The browser did not write a word for this start."
          : shown === 0
            ? "Each step writes O or E. Play or step to see the word appear."
            : shown < word.length
              ? `${shown} of ${word.length} letters. O is odd, E is even.`
              : `${word.length} letters. O is odd, E is even.`}
        {note ? ` ${note}` : ""}
      </p>
    </div>
  );
}
