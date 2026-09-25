import tailwindcss from "@tailwindcss/vite";
import react from "@vitejs/plugin-react";
import { defineConfig } from "vitest/config";

function publicBase(): string {
  const raw = process.env.VITE_BASE ?? "/";
  return raw.endsWith("/") ? raw : `${raw}/`;
}

export default defineConfig({
  // Vercel and local preview serve from `/`; VITE_BASE overrides it for a sub-path.
  base: publicBase(),
  plugins: [react(), tailwindcss()],
  test: {
    environment: "node",
    include: ["src/**/*.test.ts"],
  },
});
