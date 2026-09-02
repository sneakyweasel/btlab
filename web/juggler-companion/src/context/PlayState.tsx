import { createContext, useContext, useMemo, useState, type ReactNode } from "react";

type PlayState = {
  nText: string;
  setNText: (value: string) => void;
  itinerary: string;
  setItinerary: (value: string) => void;
  cycleItinerary: string;
  setCycleItinerary: (value: string) => void;
  cycleShift: number;
  setCycleShift: (value: number) => void;
  steps: number;
  setSteps: (value: number) => void;
  financeL: number;
  setFinanceL: (value: number) => void;
};

const PlayContext = createContext<PlayState | null>(null);

export function PlayStateProvider({ children }: { children: ReactNode }) {
  const [nText, setNText] = useState("3");
  const [itinerary, setItinerary] = useState("OOE");
  const [cycleItinerary, setCycleItinerary] = useState("OOOOOOOEEEE");
  const [cycleShift, setCycleShift] = useState(0);
  const [steps, setSteps] = useState(20);
  const [financeL, setFinanceL] = useState(25781);
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
      steps,
      setSteps,
      financeL,
      setFinanceL,
    }),
    [nText, itinerary, cycleItinerary, cycleShift, steps, financeL],
  );
  return <PlayContext.Provider value={value}>{children}</PlayContext.Provider>;
}

export function usePlayState(): PlayState {
  const state = useContext(PlayContext);
  if (!state) {
    throw new Error("usePlayState must be used inside PlayStateProvider");
  }
  return state;
}
