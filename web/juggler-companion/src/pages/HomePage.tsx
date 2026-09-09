import { useState, type ReactNode } from "react";
import { Link } from "react-router-dom";
import { Tex } from "../components/Tex";
import { PAPERS, paperDoiHref, paperPdfHref } from "../content/papers";
import {
  LAB_WALK_PERIOD,
  MAIN_FLOOR,
  MAIN_PERIOD,
  PAPER_PERIOD,
  PRINTED_FLOOR,
  PRINTED_PERIOD,
} from "../juggler/constants";
import { formatInt } from "../juggler/format";
import { resolveTrajectory } from "../juggler/monsters";
import { MapDoors } from "../visuals/MapDoors";

const HOME_WALK = resolveTrajectory(173n);
const PAPER_ACTION =
  "rounded-full border border-line px-3 py-1 text-xs text-ink no-underline";

function StrokeIcon({
  children,
  className = "h-4 w-4",
}: {
  children: ReactNode;
  className?: string;
}) {
  return (
    <svg viewBox="0 0 24 24" className={className} aria-hidden="true">
      {children}
    </svg>
  );
}

function stroke() {
  return {
    fill: "none",
    stroke: "currentColor",
    strokeWidth: 2,
    strokeLinecap: "round" as const,
    strokeLinejoin: "round" as const,
  };
}

function HeroIcon({ d }: { d: string }) {
  return (
    <StrokeIcon>
      <path d={d} {...stroke()} />
    </StrokeIcon>
  );
}

function AtroposIcon() {
  return (
    <StrokeIcon>
      <circle cx="6" cy="6" r="2.5" {...stroke()} />
      <circle cx="6" cy="18" r="2.5" {...stroke()} />
      <path d="M20 4 8.5 15.5M14.5 14.5 20 20M8.5 8.5 12 12" {...stroke()} />
    </StrokeIcon>
  );
}

function LachesisIcon() {
  return (
    <StrokeIcon>
      <circle cx="12" cy="12" r="7" {...stroke()} />
      <path d="M12 8v4l3 2" {...stroke()} />
    </StrokeIcon>
  );
}

function ClothoIcon() {
  return (
    <StrokeIcon>
      <path
        d="M12 12c-2-2.7-4-4-6-4a4 4 0 1 0 0 8c2 0 4-1.3 6-4Zm0 0c2 2.7 4 4 6 4a4 4 0 0 0 0-8c-2 0-4 1.3-6 4Z"
        {...stroke()}
      />
    </StrokeIcon>
  );
}

export function HomePage() {
  const [step, setStep] = useState(0);
  const here = HOME_WALK.states[step] ?? HOME_WALK.states[0];
  return (
    <div className="space-y-10">
      <section className="space-y-6">
        <div>
          <p className="text-sm uppercase tracking-[0.2em] text-muted">
            Interactive pictures · Pickover’s juggler
          </p>
          <h1 className="mt-2 max-w-2xl text-4xl sm:text-5xl">
            Two rules. Three fates.
          </h1>
          <p className="prose-measure mt-4 text-lg text-muted">
            Pictures you can walk: a visual companion for three Juggler
            preprints. Even n takes a square root, odd n takes n√n. Then
            the orbit reaches 1, cycles, or runs away. Click the walk
            below, then take the tour or open the playground. The PDFs
            stay the proofs. The papers do not pick a fate.
          </p>
          <div className="mt-6 flex flex-wrap gap-3">
            <Link
              to="/tour/the-map"
              className="inline-flex items-center gap-2 rounded-full bg-deep px-4 py-2 text-card no-underline"
            >
              <HeroIcon d="M4 19a2 2 0 1 0 0-4 2 2 0 0 0 0 4Zm16-10a2 2 0 1 0 0-4 2 2 0 0 0 0 4ZM6 16l4.5-7L14 13l4-6" />
              Start the tour
            </Link>
            <Link
              to="/play/trajectory"
              className="inline-flex items-center gap-2 rounded-full border border-line px-4 py-2 text-ink no-underline"
            >
              <HeroIcon d="M4 4h7v7H4Zm9 0h7v7h-7ZM4 13h7v7H4Zm9 0h7v7h-7Z" />
              Playground
            </Link>
            <Link
              to="/claims"
              className="inline-flex items-center gap-2 rounded-full border border-line px-4 py-2 text-ink no-underline"
            >
              <HeroIcon d="M8 6h12M8 12h12M8 18h12M4 6h.01M4 12h.01M4 18h.01" />
              What the paper claims
            </Link>
          </div>
        </div>
        <div className="rounded-2xl border border-line bg-card p-4">
          <MapDoors
            states={HOME_WALK.states}
            sparseScale
            active={step}
            onSelect={setStep}
            side={
              <div className="flex h-full items-center justify-center rounded-2xl border border-line bg-card px-3 py-4">
                <Tex display>
                  {String.raw`J(n)=\begin{cases}\lfloor\sqrt n\rfloor,&n\text{ even}\\\lfloor n\sqrt n\rfloor,&n\text{ odd.}\end{cases}`}
                </Tex>
              </div>
            }
          />
          <p className="mt-3 text-sm text-muted">
            Click a point. Start 173, step {step} of {HOME_WALK.states.length - 1},
            now {formatInt(here)}. The peak is 272 bits — larger than the
            number of atoms in the universe — and the evens still cut it
            down. One trajectory, not a theorem.{" "}
            <Link to="/play/trajectory">Open this walk in the playground</Link>.
          </p>
        </div>
        <div className="grid gap-3 sm:grid-cols-3">
          {PAPERS.map((paper) => (
            <div
              key={paper.letter}
              className="rounded-xl border border-line bg-card p-4"
            >
              <div className="text-xs uppercase tracking-wide text-muted">
                Paper {paper.letter}
              </div>
              <div className="mt-2 font-serif text-2xl text-ink">{paper.title}</div>
              <p className="mt-1 text-sm text-muted">{paper.hint}</p>
              <div className="mt-3 flex flex-wrap items-center gap-2">
                <a
                  href={paperPdfHref(paper)}
                  target="_blank"
                  rel="noreferrer"
                  className={PAPER_ACTION}
                >
                  PDF
                </a>
                {paper.guide ? (
                  <Link to={paper.guide.to} className={PAPER_ACTION}>
                    {paper.guide.label}
                  </Link>
                ) : null}
                {paper.doi ? (
                  <a
                    href={paperDoiHref(paper.doi)}
                    target="_blank"
                    rel="noreferrer"
                    className={PAPER_ACTION}
                  >
                    DOI
                  </a>
                ) : null}
              </div>
            </div>
          ))}
        </div>
      </section>
      <section className="space-y-3">
        <h2 className="text-2xl">Three fates</h2>
        <p className="prose-measure text-sm text-muted">
          Lemma 1.1: these are the only three possibilities. The papers do
          not pick one. The Moirai names are a mnemonic: Atropos cuts,
          Lachesis measures, Clotho spins.
        </p>
        <div className="grid gap-3 sm:grid-cols-3">
          <FateCard
            title="Reach 1"
            moira="Atropos"
            icon={<AtroposIcon />}
            body="Cuts the thread: some iterate equals 1. The unique fixed point is J(1) = 1."
          />
          <FateCard
            title="Cycle"
            moira="Lachesis"
            icon={<LachesisIcon />}
            body="Measures an allotted length: some m ≥ 2 returns. A bounded infinite trajectory must do this."
          />
          <FateCard
            title="Unbounded"
            moira="Clotho"
            icon={<ClothoIcon />}
            body="Spins without end: the values grow without bound."
          />
        </div>
      </section>
      <section className="space-y-3">
        <h2 className="text-2xl">Period lower bounds</h2>
        <p className="prose-measure text-sm text-muted">
          Paper A: a hypothetical cycle is at least this long at a certified
          descent floor N₀. Raising N₀ is more computation, not a new
          theorem.
        </p>
        <div className="grid gap-3 sm:grid-cols-2 lg:grid-cols-4">
          <BoundCard title="Theorem 4.6" bound={PAPER_PERIOD} floor="1,000,000" />
          <BoundCard title="Theorem 5.9" bound={LAB_WALK_PERIOD} floor="26,254,995" />
          <BoundCard
            title="Corollary 5.10"
            bound={PRINTED_PERIOD}
            floor={PRINTED_FLOOR.toLocaleString("en-US")}
          />
          <BoundCard
            title="Corollary 5.11"
            bound={MAIN_PERIOD}
            floor={MAIN_FLOOR.toLocaleString("en-US")}
          />
        </div>
      </section>
      <section className="prose-measure space-y-2 text-muted">
        <p>
          Walk the pictures in the{" "}
          <Link to="/tour/the-map">tour</Link>. Try a start in the{" "}
          <Link to="/play/trajectory">playground</Link>. Checking a claim?{" "}
          <Link to="/claims">What the paper claims</Link>.
        </p>
      </section>
    </div>
  );
}

function FateCard({
  title,
  moira,
  icon,
  body,
}: {
  title: string;
  moira: string;
  icon: ReactNode;
  body: string;
}) {
  return (
    <div className="rounded-xl border border-line bg-card p-4">
      <div className="flex items-center gap-2 text-muted">
        {icon}
        <div>
          <div className="text-xs uppercase tracking-wide">{title}</div>
          <div className="font-serif text-lg text-ink">{moira}</div>
        </div>
      </div>
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
