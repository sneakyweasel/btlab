import tailwindcss from "@tailwindcss/vite";
import react from "@vitejs/plugin-react";
import { defineConfig } from "vitest/config";

function publicBase(): string {
  const raw = process.env.VITE_BASE ?? "/";
  return raw.endsWith("/") ? raw : `${raw}/`;
}

export default defineConfig({
  // Vercel and local preview serve from `/`. GitHub project pages set
  // VITE_BASE=/balanced_ternary/ in the workflow.
  base: publicBase(),
  plugins: [react(), tailwindcss()],
  test: {
    environment: "node",
    include: ["src/**/*.test.ts"],
  },
});
