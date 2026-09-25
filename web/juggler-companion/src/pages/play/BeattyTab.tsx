import { BeattyExplorer } from "../../components/BeattyExplorer";
import { Tex } from "../../components/Tex";

export default function BeattyTab() {
  return (
    <section className="space-y-5" aria-labelledby="beatty-heading">
      <header className="space-y-3">
        <p className="text-xs uppercase tracking-[0.18em] text-muted">Beatty first passage</p>
        <h2 id="beatty-heading" className="text-3xl">From phase to deleted gaps</h2>
        <p className="prose-measure text-muted">
          The normalized counts gather around an increasing profile. Each jump
          skips an interval of values. Select a jump or move through the phase to
          see how those gaps appear on the value axis.
        </p>
      </header>
      <BeattyExplorer />
      <details className="rounded-xl border border-line bg-card p-4 text-sm">
        <summary className="cursor-pointer font-medium">How to read the profile</summary>
        <div className="mt-4 space-y-3">
          <Tex display>{String.raw`\delta_r=\{r\log_2 3\},\qquad F(t)=1+\sum_{\delta_j<t}w_j,\qquad R_r^+=\frac{r c_r}{\binom{\lfloor r\log_2 3\rfloor-1}{r-1}}.`}</Tex>
          <p>
            The strict inequality makes the profile left-continuous. A filled dot
            marks the selected left value of the truncated profile; the hollow
            dot marks its right trace. The connecting vertical guide is not part
            of the graph. The accumulation set is the closure of the profile’s
            values, including their one-sided limits.
          </p>
          <p>
            The shaded band encloses the infinite profile using the omitted
            positive tail. It does not bound the error of a finite count sample.
            Only certified interiors of the true deleted gaps are colored on
            the value axis. The remaining regions are unresolved at this cutoff,
            and must not be read as the exact accumulation set.
          </p>
          <p>
            Samples come from exact integer counts; their displayed ratios,
            phases and plot coordinates are rounded. These finite pictures do
            not establish orbit termination.
          </p>
          <p>
            The selected-index panel shows the phase, jump size, profile enclosure,
            and residual R⁺ᵣ − F(δᵣ). The residual enclosure subtracts the full
            profile interval from the count ratio, reversing the interval endpoints.
            Containing zero means the residual’s sign is unresolved at this cutoff.
          </p>
          <p>
            The optional distribution view compares the empirical CDF with an
            enclosure of the limiting law of F(U), where U is uniform on [0, 1].
            The finite truncated profile has a step distribution; it is not the
            exact continuous limiting law. Changing the sample range updates this
            comparison without changing the limiting-law enclosure.
          </p>
        </div>
      </details>
    </section>
  );
}
