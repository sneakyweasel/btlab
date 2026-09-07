import { createContext, useContext, useMemo, useState, type ReactNode } from "react";
import { MAIN_FLOOR, PAPER_PERIOD, NECKLACE_PRESETS } from "../juggler/constants";
import type { EnvelopeMode } from "../juggler/runSuffix";

type PlayState = {
  nText: string;
  setNText: (value: string) => void;
  itinerary: string;
  setItinerary: (value: string) => void;
  cycleItinerary: string;
  setCycleItinerary: (value: string) => void;
  cycleShift: number;
  setCycleShift: (value: number) => void;
  financeL: number;
  setFinanceL: (value: number) => void;
  suffix: string;
  setSuffix: (value: string) => void;
  runA: number;
  setRunA: (value: number) => void;
  runN: number;
  setRunN: (value: number) => void;
  envelopeMode: EnvelopeMode;
  setEnvelopeMode: (value: EnvelopeMode) => void;
  gapN: number;
  setGapN: (value: number) => void;
  gapL: number;
  setGapL: (value: number) => void;
  gapO: number | null;
  setGapO: (value: number | null) => void;
};

type NecklaceState = {
  necklaceNText: string;
  setNecklaceNText: (value: string) => void;
  necklaceWord: string;
  setNecklaceWord: (value: string) => void;
};

const PlayContext = createContext<PlayState | null>(null);
const NecklaceContext = createContext<NecklaceState | null>(null);

export function PlayStateProvider({ children }: { children: ReactNode }) {
  const [nText, setNText] = useState("3");
  const [itinerary, setItinerary] = useState("OOE");
  const [cycleItinerary, setCycleItinerary] = useState("OOOOOOOEEEE");
  const [cycleShift, setCycleShift] = useState(0);
  const [financeL, setFinanceL] = useState(25781);
  const [suffix, setSuffix] = useState("EE");
  const [runA, setRunA] = useState(4);
  const [runN, setRunN] = useState(300);
  const [envelopeMode, setEnvelopeMode] = useState<EnvelopeMode>("crude");
  const [gapN, setGapN] = useState(MAIN_FLOOR);
  const [gapL, setGapL] = useState(PAPER_PERIOD);
  const [gapO, setGapO] = useState<number | null>(null);
  const [necklaceNText, setNecklaceNText] = useState(NECKLACE_PRESETS[0].n.toString());
  const [necklaceWord, setNecklaceWord] = useState<string>(NECKLACE_PRESETS[0].word);
  const value = useMemo(
    () => ({
      nText,
      setNText,
      itinerary,
      setItinerary,
      cycleItinerary,
      setCycleItinerary,
      cycleShift,
      setCycleShift,
      financeL,
      setFinanceL,
      suffix,
      setSuffix,
      runA,
      setRunA,
      runN,
      setRunN,
      envelopeMode,
      setEnvelopeMode,
      gapN,
      setGapN,
      gapL,
      setGapL,
      gapO,
      setGapO,
    }),
    [
      nText,
      itinerary,
      cycleItinerary,
      cycleShift,
      financeL,
      suffix,
      runA,
      runN,
      envelopeMode,
      gapN,
      gapL,
      gapO,
    ],
  );
  const necklace = useMemo(
    () => ({
      necklaceNText,
      setNecklaceNText,
      necklaceWord,
      setNecklaceWord,
    }),
    [necklaceNText, necklaceWord],
  );
  return (
    <PlayContext.Provider value={value}>
      <NecklaceContext.Provider value={necklace}>{children}</NecklaceContext.Provider>
    </PlayContext.Provider>
  );
}

export function usePlayState(): PlayState {
  const state = useContext(PlayContext);
  if (!state) {
    throw new Error("usePlayState must be used inside PlayStateProvider");
  }
  return state;
}

export function useNecklaceState(): NecklaceState {
  const state = useContext(NecklaceContext);
  if (!state) {
    throw new Error("useNecklaceState must be used inside PlayStateProvider");
  }
  return state;
}
