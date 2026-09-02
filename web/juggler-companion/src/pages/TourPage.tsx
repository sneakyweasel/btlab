import type { JSX } from "react";
import { Link, Navigate, useParams } from "react-router-dom";
import {
  CellsWidget,
  CycleWidget,
  EnvelopeWidget,
  ExpandingWidget,
  FinanceWidget,
  FloorWidget,
  MapWidget,
  OrbitWidget,
  WalkChargeWidget,
} from "../components/TourWidgets";
import {
  TOUR_CHAPTERS,
  chapterBySlug,
  neighborChapters,
  type TourSlug,
} from "../content/glossary";

const WIDGETS: Record<TourSlug, () => JSX.Element> = {
  "the-map": MapWidget,
  "orbit-word": OrbitWidget,
  "cycle-word": CycleWidget,
  expanding: ExpandingWidget,
  envelope: EnvelopeWidget,
  cells: CellsWidget,
  "descent-floor": FloorWidget,
  finance: FinanceWidget,
  "walk-charge": WalkChargeWidget,
};

export function TourIndexPage() {
  return <Navigate to="/tour/the-map" replace />;
}

export function TourPage() {
  const { slug } = useParams();
  const chapter = chapterBySlug(slug);
  if (!chapter) {
    return <Navigate to="/tour/the-map" replace />;
  }
  const { prev, next } = neighborChapters(chapter.slug);
  const Widget = WIDGETS[chapter.slug];
  return (
    <div className="grid gap-8 lg:grid-cols-[16rem_1fr]">
      <aside>
        <p className="text-xs uppercase tracking-[0.18em] text-muted">Tour</p>
        <ol className="mt-3 space-y-1">
          {TOUR_CHAPTERS.map((item) => (
            <li key={item.slug}>
              <Link
                to={`/tour/${item.slug}`}
                className={`block rounded-md px-2 py-1 text-sm no-underline ${
                  item.slug === chapter.slug
                    ? "bg-deep text-card"
                    : "text-muted hover:bg-card"
                }`}
              >
                {item.number}. {item.term}
              </Link>
            </li>
          ))}
        </ol>
      </aside>
      <article className="space-y-6">
        <header>
          <p className="text-sm text-muted">Chapter {chapter.number} of 9</p>
          <h1 className="mt-1 text-4xl">{chapter.term}</h1>
          <p className="prose-measure mt-3 text-lg text-muted">{chapter.blurb}</p>
        </header>
        <div className="rounded-2xl border border-line bg-card p-4 sm:p-6">
          <Widget />
        </div>
        <p className="prose-measure">{chapter.body}</p>
        <p className="text-sm text-muted">
          <span className="font-medium text-ink">In the paper. </span>
          {chapter.paper}
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
            <Link to="/play/orbit" className="text-sm">
              Open the playground →
            </Link>
          )}
        </div>
      </article>
    </div>
  );
}
