/**
 * Playwright config for the Sparkle JupyterLab tutorial image.
 *
 * Reproduces the same path a real user takes:
 *   1. `docker run -p 18888:8888 sparkle-tutorial:latest`
 *   2. Open http://localhost:18888/lab in a browser.
 *   3. Open a chapter notebook, run the import cell, observe the
 *      output (or the error).
 *
 * The container is started outside Playwright (see Makefile target
 * or `tests/e2e/run.sh`) and is expected to be reachable on
 * SPARKLE_E2E_PORT (default 18888) before `npx playwright test`
 * runs.  We don't manage the container lifecycle from inside
 * Playwright because rebuilding the 8 GB image on every test run
 * would be absurd.
 */
import { defineConfig, devices } from '@playwright/test';

const PORT = Number(process.env.SPARKLE_E2E_PORT ?? 18888);

export default defineConfig({
  testDir: __dirname,
  testMatch: /.*\.spec\.ts/,

  // First-cell-after-kernel-start does olean header processing —
  // 167K constants worth — and 26-cell chapters take several
  // minutes end-to-end on a cold kernel.  Give each test plenty
  // of headroom.
  timeout: 360_000,
  expect: { timeout: 30_000 },

  // The native xlean kernel is single-threaded and heavy; running
  // tests in parallel just thrashes memory.
  fullyParallel: false,
  workers: 1,

  reporter: [['list'], ['html', { outputFolder: 'playwright-report', open: 'never' }]],

  use: {
    baseURL: `http://localhost:${PORT}`,
    trace: 'retain-on-failure',
    screenshot: 'only-on-failure',
    video: 'off',
  },

  projects: [
    { name: 'chromium', use: { ...devices['Desktop Chrome'] } },
  ],
});
