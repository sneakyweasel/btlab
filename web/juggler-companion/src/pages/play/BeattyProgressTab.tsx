import { Link } from "react-router-dom";
import { BeattyProgress } from "../../components/BeattyProgress";

export default function BeattyProgressTab() {
  return (
    <section className="space-y-5" aria-labelledby="beatty-progress-heading">
      <header className="space-y-3">
        <p className="text-xs uppercase tracking-[0.18em] text-muted">Beatty first passage</p>
        <h2 id="beatty-progress-heading" className="text-3xl">What is established so far</h2>
        <p className="prose-measure text-muted">
          Every Beatty claim in the laboratory ledger, with its evidence label,
          its Lean module and the day it was first recorded. The results cover
          the binomial-normalized jump profile, its cluster set and limit law,
          their singular geometry, and the Gamma-normalized second law, first at
          the slope log₂ 3 and then for every irrational slope above one.
          See the <Link to="/play/beatty-profile">Beatty profile</Link> for the
          certified numerical picture.
        </p>
      </header>
      <BeattyProgress />
    </section>
  );
}
