import { BrowserRouter, Navigate, Route, Routes } from "react-router-dom";
import { Layout } from "./components/Layout";
import { PlayStateProvider } from "./context/PlayState";
import { ClaimsPage } from "./pages/ClaimsPage";
import { HomePage } from "./pages/HomePage";
import { PlaygroundIndexPage, PlaygroundPage } from "./pages/PlaygroundPage";
import { TourIndexPage, TourPage } from "./pages/TourPage";
import { CellsTab } from "./pages/play/CellsTab";
import { CycleTab } from "./pages/play/CycleTab";
import { FinanceTab } from "./pages/play/FinanceTab";
import { OrbitTab } from "./pages/play/OrbitTab";
import { WordTab } from "./pages/play/WordTab";

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
              <Route path="orbit" element={<OrbitTab />} />
              <Route path="word" element={<WordTab />} />
              <Route path="cells" element={<CellsTab />} />
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
