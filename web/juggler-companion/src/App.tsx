import { BrowserRouter, Navigate, Route, Routes } from "react-router-dom";
import { Layout } from "./components/Layout";
import { PlayStateProvider } from "./context/PlayState";
import { ClaimsPage } from "./pages/ClaimsPage";
import { HomePage } from "./pages/HomePage";
import { PlaygroundIndexPage, PlaygroundPage } from "./pages/PlaygroundPage";
import { TourIndexPage, TourPage } from "./pages/TourPage";
import { PreimagesTab } from "./pages/play/PreimagesTab";
import { CycleTab } from "./pages/play/CycleTab";
import { FinanceTab } from "./pages/play/FinanceTab";
import { TrajectoryTab } from "./pages/play/TrajectoryTab";
import { ItineraryTab } from "./pages/play/ItineraryTab";

const basename = import.meta.env.BASE_URL.replace(/\/$/, "");

export default function App() {
  return (
    <BrowserRouter basename={basename}>
      <PlayStateProvider>
        <Routes>
          <Route element={<Layout />}>
            <Route index element={<HomePage />} />
            <Route path="tour" element={<TourIndexPage />} />
            <Route path="tour/:slug" element={<TourPage />} />
            <Route path="play" element={<PlaygroundPage />}>
              <Route index element={<PlaygroundIndexPage />} />
              <Route path="trajectory" element={<TrajectoryTab />} />
              <Route path="orbit" element={<Navigate to="/play/trajectory" replace />} />
              <Route path="itinerary" element={<ItineraryTab />} />
              <Route path="word" element={<Navigate to="/play/itinerary" replace />} />
              <Route path="preimages" element={<PreimagesTab />} />
              <Route path="cells" element={<Navigate to="/play/preimages" replace />} />
              <Route path="cycle" element={<CycleTab />} />
              <Route path="finance" element={<FinanceTab />} />
            </Route>
            <Route path="claims" element={<ClaimsPage />} />
            <Route path="*" element={<Navigate to="/" replace />} />
          </Route>
        </Routes>
      </PlayStateProvider>
    </BrowserRouter>
  );
}
