import { createContext, useContext, useMemo, useState, type ReactNode } from "react";
import { NECKLACE_PRESETS } from "../juggler/constants";

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
    }),
    [nText, itinerary, cycleItinerary, cycleShift, financeL],
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
