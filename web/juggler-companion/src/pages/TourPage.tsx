import type { JSX } from "react";
import { useState } from "react";
import { Link, Navigate, useParams } from "react-router-dom";
import {
  PreimagesWidget,
  OeFiberWidget,
  CycleWidget,
  LeftoversWidget,
  EnvelopeWidget,
  ExpandingWidget,
  FinanceWidget,
  FloorWidget,
  GapTransferWidget,
  MapWidget,
  RunSuffixWidget,
  WalkChargeWidget,
  FanWidget,
} from "../components/TourWidgets";
import { Prose, ProseInline } from "../components/Prose";
import {
  TOUR_CHAPTERS,
  chapterBySlug,
  neighborChapters,
  type TourSlug,
} from "../content/glossary";

const SHORT_TERM: Record<TourSlug, string> = {
  "the-map": "Map",
  "cycle-itinerary": "Cycle",
  "cycle-survivors": "Survivors",
  expanding: "Expand",
  envelope: "Envelope",
  "run-suffix": "Suffix",
  preimages: "Preimages",
  "oe-fiber": "OE fiber",
  "descent-floor": "Floor",
  finance: "Finance",
  "gap-transfer": "Gap",
  "walk-charge": "Walk",
  fan: "Fan",
};

const WIDGETS: Record<TourSlug, () => JSX.Element> = {
  "the-map": MapWidget,
  "cycle-itinerary": CycleWidget,
  "cycle-survivors": LeftoversWidget,
  expanding: ExpandingWidget,
  envelope: EnvelopeWidget,
  "run-suffix": RunSuffixWidget,
  preimages: PreimagesWidget,
  "oe-fiber": OeFiberWidget,
  "descent-floor": FloorWidget,
  finance: FinanceWidget,
  "gap-transfer": GapTransferWidget,
  "walk-charge": WalkChargeWidget,
  fan: FanWidget,
};

export function TourIndexPage() {
  return <Navigate to="/tour/the-map" replace />;
}

export function TourPage() {
  const { slug } = useParams();
  const [menuOpen, setMenuOpen] = useState(false);
  if (
    slug === "orbit-word" ||
    slug === "trajectory-word" ||
    slug === "trajectory-itinerary"
  ) {
    return <Navigate to="/tour/the-map" replace />;
  }
  if (slug === "cells") {
    return <Navigate to="/tour/preimages" replace />;
  }
  if (slug === "cycle-leftovers") {
    return <Navigate to="/tour/cycle-survivors" replace />;
  }
  if (slug === "suffix") {
    return <Navigate to="/tour/run-suffix" replace />;
  }
  if (slug === "rhin") {
    return <Navigate to="/tour/gap-transfer" replace />;
  }
  const chapter = chapterBySlug(slug);
  if (!chapter) {
    return <Navigate to="/tour/the-map" replace />;
  }
  const { prev, next } = neighborChapters(chapter.slug);
  const Widget = WIDGETS[chapter.slug];
  return (
    <div
      className={`grid gap-6 ${
        menuOpen ? "lg:grid-cols-[10.5rem_1fr]" : "lg:grid-cols-[2.75rem_1fr]"
      }`}
    >
      <aside className="lg:sticky lg:top-4 lg:self-start">
        <div className="mb-2 flex items-center gap-2">
          {menuOpen ? (
            <p className="hidden text-xs uppercase tracking-[0.18em] text-muted lg:block">
              Tour
            </p>
          ) : null}
          <button
            type="button"
            className="hidden h-8 w-8 items-center justify-center rounded-full border border-line bg-card text-sm text-muted lg:inline-flex"
            aria-expanded={menuOpen}
            aria-label={menuOpen ? "Collapse chapter list" : "Expand chapter list"}
            onClick={() => setMenuOpen((open) => !open)}
          >
            {menuOpen ? "‹" : "›"}
          </button>
        </div>
        <ol
          className={`flex flex-wrap gap-1 ${menuOpen ? "lg:flex-col" : "lg:flex-col lg:items-stretch"}`}
        >
          {TOUR_CHAPTERS.map((item) => {
            const current = item.slug === chapter.slug;
            return (
              <li key={item.slug}>
                <Link
                  to={`/tour/${item.slug}`}
                  title={`${item.number}. ${item.term}`}
                  className={`flex items-center no-underline ${
                    menuOpen
                      ? "rounded-md px-2 py-1 text-sm"
                      : "h-8 w-8 justify-center rounded-full text-xs"
                  } ${
                    current
                      ? "bg-deep text-card"
                      : "bg-card text-muted hover:bg-paper lg:bg-transparent"
                  }`}
                >
                  {menuOpen ? (
                    <>
                      <span className="w-4 font-mono text-xs">{item.number}</span>
                      <span className="ml-1">{SHORT_TERM[item.slug]}</span>
                    </>
                  ) : (
                    item.number
                  )}
                </Link>
              </li>
            );
          })}
        </ol>
      </aside>
      <article className="min-w-0 space-y-6">
        <header>
          <p className="text-sm text-muted">
            Chapter {chapter.number} of {TOUR_CHAPTERS.length}
          </p>
          <h1 className="mt-1 text-4xl">{chapter.term}</h1>
          <p className="prose-measure mt-3 text-lg text-muted">
            <ProseInline text={chapter.blurb} />
          </p>
        </header>
        <div className="min-w-0 overflow-hidden rounded-2xl border border-line bg-card p-4 sm:p-6">
          <Widget />
        </div>
        <Prose text={chapter.body} />
        <p className="prose-measure text-sm text-muted">
          <span className="font-medium text-ink">In the paper. </span>
          <ProseInline text={chapter.paper} />
        </p>
        <div className="flex flex-wrap justify-between gap-3 border-t border-line pt-4">
          {prev ? (
            <Link to={`/tour/${prev.slug}`} className="text-sm">
              ← {prev.term}
            </Link>
          ) : (
            <span />
          )}
          {next ? (
            <Link to={`/tour/${next.slug}`} className="text-sm">
              {next.term} →
            </Link>
          ) : (
            <Link to="/play/fan" className="text-sm">
              Open the playground →
            </Link>
          )}
        </div>
      </article>
    </div>
  );
}
