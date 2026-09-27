import { defineConfig } from "vite";
import react from "@vitejs/plugin-react";

// Output is served by apps/control/server.ts from apps/web/dist under a strict
// CSP (script-src 'self'): no inline scripts, no external assets.
export default defineConfig({
  base: "/",
  plugins: [react()],
  build: { outDir: "dist", emptyOutDir: true, modulePreload: { polyfill: false }, assetsInlineLimit: 0 },
});
