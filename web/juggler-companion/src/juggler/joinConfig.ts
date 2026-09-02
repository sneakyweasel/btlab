/**
 * Join card adapter. The Lean table lives in `lollipop.ts`
 * (`sureLetterJoinTable` / `JoinFigure`).
 */
export {
  JOIN_INTERVALS_NOT_STOPS,
  JOIN_VS_WORD_ROTATION,
  idealJoinConfig,
  stemBeadsForJoin,
  stemTerminalLetter,
  type JoinConfig,
} from "./lollipop";

import { paintStem, type PaintedBead } from "./lollipop";
import { joinFigure, siteAtIndex } from "./lollipop";

/** Optional-launch stem ending forced E (O-arrival). */
export const STEM_BEADS_E: readonly PaintedBead[] = paintStem(
  "optionalLaunch",
  joinFigure("launchO", 1),
);

/** Optional-launch stem ending unknown (E-arrival / fill). */
export const STEM_BEADS_E_OR_O: readonly PaintedBead[] = paintStem(
  "optionalLaunch",
  joinFigure("valley", 0),
);

export function stemBeadsOptional(joinIndex: number): readonly PaintedBead[] {
  return paintStem("optionalLaunch", joinFigure(siteAtIndex(joinIndex), joinIndex));
}
