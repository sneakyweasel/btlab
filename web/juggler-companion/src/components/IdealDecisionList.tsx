import { memo } from "react";
import {
  DECISION_KIND_LABEL,
  DECISION_PART_LABEL,
  DECISION_PARTS,
  DECISIONS_BY_PART,
  lookupDecision,
  type DecisionKind,
  type IdealDecision,
} from "../content/idealDecisions";

const KIND_CLASS: Record<DecisionKind, string> = {
  theorem: "bg-ok/15 text-ok",
  optional: "bg-warn/15 text-warn",
  leftover: "bg-even/15 text-even",
  "off-figure": "bg-line text-muted",
};

function KindChip({ kind }: { kind: DecisionKind }) {
  return (
    <span
      className={`rounded-full px-1.5 py-0.5 text-[10px] uppercase tracking-wide ${KIND_CLASS[kind]}`}
    >
      {DECISION_KIND_LABEL[kind]}
    </span>
  );
}

export const IdealDecisionCard = memo(function IdealDecisionCard({
  decision,
}: {
  decision: IdealDecision | null;
}) {
  if (!decision) {
    return (
      <div
        className="rounded-xl border border-line bg-paper/70 px-3 py-3"
        data-keep-focus
      >
        <p className="text-xs uppercase tracking-wide text-muted">
          Why this mark
        </p>
        <p className="mt-2 font-serif text-lg leading-tight">
          Click a bead or a row
        </p>
        <p className="mt-2 text-sm text-ink">
          Solid and grey keep their meaning. The wash is only a
          pointer. Click empty space to show the whole figure again.
        </p>
      </div>
    );
  }
  return (
    <div
      className="rounded-xl border border-line bg-paper/70 px-3 py-3"
      data-keep-focus
    >
      <p className="text-xs uppercase tracking-wide text-muted">
        Why this mark
      </p>
      <div className="mt-2 flex flex-wrap items-center gap-2">
        <KindChip kind={decision.kind} />
        <p className="font-serif text-lg leading-tight">{decision.title}</p>
      </div>
      <p className="mt-2 text-sm text-ink">{decision.why}</p>
      <p className="mt-2 font-mono text-xs text-muted">{decision.lemma}</p>
    </div>
  );
});

export const IdealDecisionList = memo(function IdealDecisionList({
  selectedId,
  onSelect,
}: {
  selectedId: string | null;
  onSelect: (id: string | null) => void;
}) {
  return (
    <div
      className="rounded-xl border border-line bg-paper/70 px-3 py-3"
      data-keep-focus
    >
      <p className="text-xs uppercase tracking-wide text-muted">
        Each decision, with its lemma
      </p>
      <p className="mt-1 text-sm text-muted">
        Theorem is forced. Optional stem is one legal first visit. Leftover
        is a named shape that still does not close. Off-figure was harvested
        and does not paint a bead.
      </p>
      <div className="mt-3 grid gap-4 lg:grid-cols-2">
        {DECISION_PARTS.map((part) => (
          <section key={part}>
            <h3 className="font-serif text-lg">{DECISION_PART_LABEL[part]}</h3>
            <ul className="mt-2 grid gap-1.5">
              {DECISIONS_BY_PART[part].map((decision) => {
                  const open = decision.id === selectedId;
                  return (
                    <li key={decision.id}>
                      <button
                        type="button"
                        aria-pressed={open}
                        className={`w-full rounded-lg border px-2.5 py-2 text-left ${
                          open
                            ? "border-ink bg-card"
                            : "border-line bg-card/60 hover:border-ink/40"
                        }`}
                        onClick={(event) => {
                          event.stopPropagation();
                          onSelect(open ? null : decision.id);
                        }}
                      >
                        <span className="flex flex-wrap items-center gap-2">
                          <KindChip kind={decision.kind} />
                          <span className="text-sm text-ink">{decision.title}</span>
                        </span>
                        {open ? (
                          <span className="mt-2 block text-sm text-muted">
                            {decision.why}
                            <span className="mt-1 block font-mono text-xs">
                              {decision.lemma}
                            </span>
                          </span>
                        ) : null}
                      </button>
                    </li>
                  );
                })}
            </ul>
          </section>
        ))}
      </div>
    </div>
  );
});

export function findDecision(id: string | null): IdealDecision | null {
  return lookupDecision(id);
}
