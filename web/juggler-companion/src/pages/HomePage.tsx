import { Link } from "react-router-dom";
import { Tex } from "../components/Tex";
import {
  LAB_WALK_PERIOD,
  PAPER_PERIOD,
  PRINTED_PERIOD,
} from "../juggler/constants";
import { resolveTrajectory } from "../juggler/monsters";
import { MapDoors } from "../visuals/MapDoors";

const HOME_WALK = resolveTrajectory(173n);

const REPO = "https://github.com/sneakyweasel/balanced_ternary/blob/main/juggler_review";
const PAPERS = [
  {
    letter: "A",
    href: `${REPO}/juggler_finite_dynamics_note.pdf`,
    title: "Cycles",
    hint: "Finance and walk charge. Period lower bounds, not a halt theorem.",
  },
  {
    letter: "B",
    href: `${REPO}/juggler_parity_discrepancy_note.pdf`,
    title: "Parity",
    hint: "Nested floor powers. Certified descent density 7/8.",
  },
  {
    letter: "C",
    href: `${REPO}/juggler_fate_almost_all_note.pdf`,
    title: "Fates",
    hint: "Contagion and the almost-all reduction. No fate excluded.",
  },
] as const;

export function HomePage() {
  return (
    <div className="space-y-10">
      <section className="space-y-6">
        <div>
          <p className="text-sm uppercase tracking-[0.2em] text-muted">
            After Pickover’s Mathematics of Oz
          </p>
          <h1 className="mt-2 max-w-2xl text-4xl sm:text-5xl">
            Two rules. Complex consequences.
          </h1>
          <p className="prose-measure mt-4 text-lg text-muted">
            Pickover’s yellow-brick juggler: even n takes a square root,
            odd n takes n√n, then throw the decimals away. Two cuts,
            million-bit flights, a loop still open. Paper A does not send
            every start home — it only bounds how long a hypothetical
            cycle would have to be, given a certified floor N₀.
          </p>
          <div className="mt-6 flex flex-wrap gap-3">
            <Link
              to="/tour/the-map"
              className="rounded-full bg-deep px-4 py-2 text-card no-underline"
            >
              Start the tour
            </Link>
            <Link
              to="/play/trajectory"
              className="rounded-full border border-line px-4 py-2 text-ink no-underline"
            >
              Open the playground
            </Link>
          </div>
          <div className="mt-6 grid gap-3 sm:grid-cols-3">
            {PAPERS.map((paper) => (
              <a
                key={paper.letter}
                href={paper.href}
                target="_blank"
                rel="noreferrer"
                className="rounded-xl border border-line bg-card p-4 no-underline"
              >
                <div className="text-xs uppercase tracking-wide text-muted">
                  Paper {paper.letter}
                </div>
                <div className="mt-2 font-serif text-2xl text-ink">{paper.title}</div>
                <p className="mt-1 text-sm text-muted">{paper.hint}</p>
              </a>
            ))}
          </div>
        </div>
        <div className="rounded-2xl border border-line bg-card p-4">
          <MapDoors
            states={HOME_WALK.states}
            sparseScale
            side={
              <div className="flex h-full items-center justify-center rounded-2xl border border-line bg-card px-3 py-4">
                <Tex display>
                  {String.raw`J(n)=\begin{cases}\lfloor\sqrt n\rfloor,&n\text{ even}\\\lfloor n\sqrt n\rfloor,&n\text{ odd.}\end{cases}`}
                </Tex>
              </div>
            }
          />
          <p className="mt-3 text-sm text-muted">
            Start 173: thirty-two steps, then 1. The peak is 272 bits — a
            larger digit than the atoms in the universe — and the evens
            still cut it down. Floor: the brackets ⌊ ⌋ throw the decimals
            away. One trajectory, not a theorem.
          </p>
        </div>
      </section>
      <section className="space-y-3">
        <p className="text-sm text-muted">
          Lemma 1.1: these are the only three possibilities. The paper does
          not pick one.
        </p>
        <div className="grid gap-3 sm:grid-cols-3">
          <FateCard
            title="Reach 1"
            body="Some iterate equals 1. The unique fixed point is J(1) = 1."
          />
          <FateCard
            title="Cycle"
            body="Some m ≥ 2 returns. A bounded infinite trajectory must do this."
          />
          <FateCard
            title="Unbounded"
            body="The values grow without bound."
          />
        </div>
      </section>
      <section className="grid gap-3 sm:grid-cols-3">
        <BoundCard title="Theorem 4.6" bound={PAPER_PERIOD} floor="1,000,000" />
        <BoundCard title="Theorem 5.9" bound={LAB_WALK_PERIOD} floor="26,254,995" />
        <BoundCard title="Corollary 5.10" bound={PRINTED_PERIOD} floor="162,849,448" />
      </section>
      <section className="prose-measure space-y-3 text-muted">
        <p>
          Use the tour if the itineraries are new. Use the playground to try the
          trajectory of 173, a cycle word, a CycleMin survivor, a short O/E
          itinerary, a one-step preimage, a necklace rotation,
          or a finance length from the shipped table.
        </p>
        <p>This site is a glossary, not the laboratory Streamlit app.</p>
      </section>
    </div>
  );
}

function FateCard({ title, body }: { title: string; body: string }) {
  return (
    <div className="rounded-xl border border-line bg-card p-4">
      <div className="text-xs uppercase tracking-wide text-muted">{title}</div>
      <p className="mt-2 text-sm text-muted">{body}</p>
    </div>
  );
}

function BoundCard({
  title,
  bound,
  floor,
}: {
  title: string;
  bound: number;
  floor: string;
}) {
  return (
    <div className="rounded-xl border border-line bg-card p-4">
      <div className="text-xs uppercase tracking-wide text-muted">{title}</div>
      <div className="mt-2 font-serif text-3xl">L ≥ {bound.toLocaleString("en-US")}</div>
      <div className="mt-1 text-sm text-muted">at N₀ = {floor}</div>
    </div>
  );
}
