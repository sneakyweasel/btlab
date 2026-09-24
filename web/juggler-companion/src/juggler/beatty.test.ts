import { describe, expect, it } from "vitest";
import { BEATTY, BEATTY_ROWS, beattyBounds, beattyLevel, beattyRow, beattySamples, beattySegments } from "./beatty";

describe("Beatty figure numerical conventions", () => {
  it("excludes the atom at its exact phase, then includes it immediately to the right", () => {
    for (const order of [1, 2, 7, 665, 5047]) {
      const row = beattyRow(order);
      expect(beattyLevel(row.phase)).toBe(row.left);
      expect(beattyLevel(row.phase + 1e-10)).toBeCloseTo(row.left + row.weight, 13);
    }
    expect(beattyRow(1).weight).toBeCloseTo(Math.log(2) / Math.log(3), 14);
  });

  it("preserves total mass, positive jumps and the certified tail ceiling", () => {
    expect(BEATTY_ROWS).toHaveLength(5047);
    expect(new Set(BEATTY_ROWS.map(row => row.order)).size).toBe(5047);
    expect(BEATTY_ROWS.every(row => row.weight > 0)).toBe(true);
    expect(beattyLevel(0)).toBe(1);
    expect(BEATTY.envelope - beattyLevel(1)).toBeGreaterThan(0);
    expect(BEATTY.envelope - beattyLevel(1)).toBeLessThan(BEATTY.tailUpper);
    expect(beattyBounds(0)).toEqual([1, 1]);
  });

  it("keeps gap drawings strictly inside the exact rational certificates", () => {
    // Compare an IEEE double exactly with a positive rational using binary decomposition.
    function compare(value: number, rational: string) {
      const buffer = new ArrayBuffer(8), view = new DataView(buffer);
      view.setFloat64(0, value);
      const bits = view.getBigUint64(0), exponent = Number((bits >> 52n) & 2047n) - 1023 - 52;
      let n = (bits & ((1n << 52n) - 1n)) + (1n << 52n), d = 1n;
      if (exponent >= 0) n <<= BigInt(exponent); else d <<= BigInt(-exponent);
      const [rn, rd] = rational.split("/").map(BigInt);
      return n * rd - rn * d;
    }
    expect(BEATTY.cores).toHaveLength(9);
    for (const core of BEATTY.cores) {
      expect(compare(core.lower, core.certificate.lower)).toBeGreaterThan(0n);
      expect(compare(core.upper, core.certificate.upper)).toBeLessThan(0n);
      expect(core.lower).toBeLessThan(core.upper);
    }
    expect(BEATTY.cores.some(core => core.order === 5047)).toBe(false);
  });

  it("does not claim that the profile tail bounds the finite-sample error", () => {
    const first = beattyRow(1), bounds = beattyBounds(first.phase);
    expect(first.ratio).toBe(1);
    expect(first.ratio).toBeLessThan(bounds[0]);
    expect(bounds[1] - bounds[0]).toBeGreaterThanOrEqual(BEATTY.tailUpper);
  });

  it("keeps the two sample windows and the full range distinct", () => {
    expect(beattySamples("late")).toHaveLength(1000);
    expect(beattySamples("late").every(row => row.order >= 4048)).toBe(true);
    expect(beattySamples("early")).toHaveLength(1000);
    expect(beattySamples("early").every(row => row.order <= 1000)).toBe(true);
    expect(beattySamples("all")).toHaveLength(5047);
  });

  it("clips horizontal segments to the zoom and rejects invalid selections", () => {
    const segments = beattySegments(0.15, 0.19);
    expect(segments[0][0]).toBe(0.15);
    expect(segments[segments.length - 1][1]).toBe(0.19);
    expect(segments.every(([a, b]) => a >= 0.15 && b <= 0.19 && a <= b)).toBe(true);
    for (const order of [0, 1.5, 5048, NaN]) expect(() => beattyRow(order)).toThrow(RangeError);
    for (const phase of [-0.1, 1.1, NaN]) expect(() => beattyLevel(phase)).toThrow(RangeError);
  });
});
