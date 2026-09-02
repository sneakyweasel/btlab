import { Link } from "react-router-dom";
import { Tex } from "../components/Tex";
import {
  LAB_WALK_PERIOD,
  PAPER_PERIOD,
  PRINTED_PERIOD,
} from "../juggler/constants";
import { MapDoors } from "../visuals/MapDoors";

export function HomePage() {
  return (
    <div className="space-y-10">
      <section className="space-y-6">
        <div>
          <p className="text-sm uppercase tracking-[0.2em] text-muted">
            Paper A companion
          </p>
          <h1 className="mt-2 max-w-xl text-4xl sm:text-5xl">
            A picture dictionary for the Juggler cycle paper
          </h1>
          <p className="prose-measure mt-4 text-lg text-muted">
            Pickover introduced the map in 1991 as a Collatz variation.
            Even n goes to the square root and odd n to n to the
            three-halves — that is n√n, not the cube root — then floor:
            throw away the decimals and keep the integer part. That floor
            is applied after every step. Paper A does not prove that every
            start reaches 1. It proves period lower bounds for a
            hypothetical cycle, once a verified descent floor N₀ is given.
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
        </div>
        <div className="rounded-2xl border border-line bg-card p-4">
          <MapDoors />
          <div className="mt-3 text-center">
            <Tex display>{String.raw`J(n)=\begin{cases}\lfloor\sqrt n\rfloor,&n\text{ even}\\\lfloor n^{3/2}\rfloor,&n\text{ odd.}\end{cases}`}</Tex>
            <p className="mt-2 text-sm text-muted">
              Trajectory of 3: the values 3, 5, 11, 36, 6, 2, 1. Word: OOOEEE —
              the parities, not the values. Floor: the brackets ⌊ ⌋ throw
              away the decimals. Example: ⌊3√3⌋ = ⌊5.196…⌋ = 5. Hitting 1
              here is one trajectory, not a theorem.
            </p>
          </div>
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
          Use the tour if the words are new. Use the playground to try the
          trajectory of 3, a short O/E word, a preimage cell, a necklace rotation,
          or a finance length from the shipped table.
        </p>
        <p>
          Manuscript:{" "}
          <a href="https://github.com/sneakyweasel/balanced_ternary/blob/main/juggler_review/juggler_finite_dynamics_note.pdf">
            Paper A PDF
          </a>
          . This site is a glossary, not the laboratory Streamlit app.
        </p>
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
