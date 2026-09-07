import { RunSuffixExplorer } from "../../components/RunSuffixExplorer";

export function RunSuffixTab() {
  return (
    <div className="space-y-5">
      <p className="prose-measure text-sm text-muted">
        Section 3.9 of the paper in three pictures. An odd run O<sup>a</sup>{" "}
        meets a suffix u; the two envelopes either cross or they do not. Type a
        suffix of length at most 8 that starts with E, pick a, and move the
        cycle minimum. The ten printed recoveries are chips. The site does not
        enumerate the 325,452 seven-even forms of Theorem 3.31.
      </p>
      <RunSuffixExplorer />
    </div>
  );
}
