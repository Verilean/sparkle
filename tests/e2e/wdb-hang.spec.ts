import { test, expect, Page } from '@playwright/test';

/**
 * Repro / debug aid for the user-reported "kernel hangs after the
 * `Display.waveformFromWdb` cell" symptom in Ch 3 §3.5d.
 *
 * What this spec captures (regardless of pass / fail):
 *   - Every WebSocket frame between JupyterLab and the kernel
 *     (lets us see whether the waveform JS is spamming `comm_msg`
 *     queries faster than the kernel can answer).
 *   - Every browser console log / error (hangs caused by JS
 *     exceptions show up here, not in the cell output).
 *   - Failed network requests (e.g. `/api/kernels/...` retries
 *     when the comm WebSocket dies).
 *   - Kernel execution-state polled over time (idle / busy /
 *     starting) so a "stuck busy" state is obvious in the trace.
 *
 * Playwright's `trace: 'on'` stores all of the above in a
 * single .zip; open it with `npx playwright show-trace` after
 * the run and you get a per-frame replay of the symptom.
 */

const CHAPTER = 'ch03-sequential.ipynb';

async function openChapter(page: Page, chapter: string) {
  await page.goto(`/lab/tree/${chapter}`);
  await page.waitForLoadState('networkidle');
}

test('ch03 wdb section: kernel stays responsive after waveformFromWdb', async ({ page }, testInfo) => {
  // Record every WebSocket created during the test — the wdb
  // viewer opens its own connection on top of the kernel's
  // shell channel, so this is where we expect to see traffic.
  const wsLog: { url: string; events: string[] }[] = [];
  page.on('websocket', (ws) => {
    const entry = { url: ws.url(), events: [] as string[] };
    wsLog.push(entry);
    ws.on('framesent',     (f) => entry.events.push(`→ ${f.payload?.toString().slice(0, 200) ?? ''}`));
    ws.on('framereceived', (f) => entry.events.push(`← ${f.payload?.toString().slice(0, 200) ?? ''}`));
    ws.on('socketerror',   (e) => entry.events.push(`!! ${e}`));
    ws.on('close',         () => entry.events.push('-- closed'));
  });

  // Console logs (errors are the most interesting; everything
  // else is captured so we have context).
  const consoleLog: string[] = [];
  page.on('console', (msg) => {
    consoleLog.push(`[${msg.type()}] ${msg.text()}`);
  });

  // Failed requests (kernel REST endpoints in particular).
  const failedRequests: string[] = [];
  page.on('requestfailed', (req) => {
    failedRequests.push(`${req.method()} ${req.url()}: ${req.failure()?.errorText ?? '?'}`);
  });

  await openChapter(page, CHAPTER);

  const baseURL = page.url().split('/lab')[0];

  // Click into the first cell to focus the notebook — the Run
  // menu items are disabled until something is selected.
  await page.locator('.jp-Cell').first().click();
  await page.waitForTimeout(500);

  // Drive Kernel → "Restart Kernel and Run All Cells…" — one
  // click that both clears prior session state and runs the
  // chapter end-to-end.  In JupyterLab 4.x the menu label is
  // "Restart Kernel and Run All", and the confirmation dialog's
  // OK button is "Confirm Kernel Restart".
  await page.getByRole('menuitem', { name: 'Kernel', exact: true }).click();
  await page.getByRole('menuitem', { name: /^Restart Kernel and Run All/i }).first().click();
  // Confirmation dialog
  const restartDialog = page.locator('.jp-Dialog').first();
  await restartDialog.waitFor({ state: 'visible', timeout: 30_000 });
  await restartDialog.getByRole('button', { name: /Confirm Kernel Restart|^Restart$/i })
    .click();
  await restartDialog.waitFor({ state: 'hidden', timeout: 10_000 });

  // Sample kernel state every 2 s for up to 4 min.  Record
  // every transition so we can see whether the kernel goes
  // busy → idle (good) or busy → busy → ... (the hang).
  const stateTimeline: { t: number; state: string }[] = [];
  const start = Date.now();
  while (Date.now() - start < 240_000) {
    const state = await page.evaluate(async (base) => {
      const list: any[] = await fetch(`${base}/api/kernels`).then((r) => r.json());
      return list[0]?.execution_state ?? 'no-kernel';
    }, baseURL);
    if (stateTimeline.at(-1)?.state !== state) {
      stateTimeline.push({ t: Date.now() - start, state });
    }
    if (state === 'idle' && stateTimeline.length >= 3) {
      // We've seen at least one busy → idle round-trip after
      // restart, and we're back to idle.  Done.
      break;
    }
    await page.waitForTimeout(2_000);
  }

  // Attach everything we collected to the test report.  Even
  // on success this is useful — you can open the trace.zip and
  // confirm the WebSocket traffic looks healthy.
  await testInfo.attach('websocket-log', {
    body: JSON.stringify(wsLog, null, 2),
    contentType: 'application/json',
  });
  await testInfo.attach('console-log', {
    body: consoleLog.join('\n'),
    contentType: 'text/plain',
  });
  await testInfo.attach('failed-requests', {
    body: failedRequests.join('\n'),
    contentType: 'text/plain',
  });
  await testInfo.attach('kernel-state-timeline', {
    body: stateTimeline.map((e) => `${(e.t / 1000).toFixed(1)}s: ${e.state}`).join('\n'),
    contentType: 'text/plain',
  });

  // The actual assertion: kernel must return to idle within
  // the 4-minute budget and we must NOT see a runaway WS
  // (more than 500 frames in a single connection is the
  // empirical "JS is spamming the kernel" threshold).
  const lastState = stateTimeline.at(-1)?.state ?? 'unknown';
  expect(
    lastState,
    `Kernel never returned to idle.  Timeline:\n${stateTimeline.map((e) => `  ${(e.t / 1000).toFixed(1)}s: ${e.state}`).join('\n')}`,
  ).toBe('idle');

  for (const ws of wsLog) {
    expect(
      ws.events.length,
      `WebSocket ${ws.url} produced ${ws.events.length} frames — possible runaway`,
    ).toBeLessThan(500);
  }
});

/**
 * The user-reported follow-up: after running the wdb cell in
 * ch03, opening *another* notebook tab freezes the kernel —
 * the new tab's cells stay `[*]` and never finish.  Hypothesis:
 * the wdb viewer's comm channel survives the chapter switch,
 * keeps pushing iopub traffic in the background, and the kernel
 * thread is busy serving it / blocked on iopub HWM.
 *
 * This spec exercises that path: open ch03, run wdb, then
 * navigate to ch01 (a tiny chapter) and run one cell.  If the
 * kernel is wedged the second cell never reaches `[1]:`.
 */
test('open ch01 after ch03 wdb: second notebook still runs', async ({ page }, testInfo) => {
  const wsLog: { url: string; events: string[] }[] = [];
  page.on('websocket', (ws) => {
    const entry = { url: ws.url(), events: [] as string[] };
    wsLog.push(entry);
    ws.on('framesent',     (f) => entry.events.push(`→ ${f.payload?.toString().slice(0, 100) ?? ''}`));
    ws.on('framereceived', (f) => entry.events.push(`← ${f.payload?.toString().slice(0, 100) ?? ''}`));
    ws.on('close',         () => entry.events.push('-- closed'));
  });

  // ── Step 1: open ch03, restart kernel + run all so the wdb
  //           cell is exercised the same way the first test does.
  await openChapter(page, CHAPTER);
  // Wait for the notebook to fully attach a kernel before we
  // click anything — otherwise the Kernel menu items can still
  // be disabled when our click arrives, the menu opens then
  // closes silently, and the page state appears unchanged.
  // Poll the REST API directly: a kernel session for the
  // chapter's path means JupyterLab has finished the
  // attachment.
  const baseURL = page.url().split('/lab')[0];
  await expect.poll(async () => {
    const sessions: any[] = await page.evaluate(async (base) => {
      return await fetch(`${base}/api/sessions`).then((r) => r.json());
    }, baseURL);
    return sessions.some((s: any) =>
      typeof s?.path === 'string' && s.path.endsWith(CHAPTER));
  }, { timeout: 60_000, message: 'ch03 kernel session never came up' }).toBe(true);
  await page.locator('.jp-Cell').first().click();
  await page.waitForTimeout(1_000);
  await page.getByRole('menuitem', { name: 'Kernel', exact: true }).click();
  // Wait for the dropdown to actually render before clicking.
  const restartItem1 = page.getByRole('menuitem', { name: /^Restart Kernel and Run All/i }).first();
  await restartItem1.waitFor({ state: 'visible', timeout: 10_000 });
  await restartItem1.click();
  const dialog1 = page.locator('.jp-Dialog').first();
  await dialog1.waitFor({ state: 'visible', timeout: 30_000 });
  await dialog1.getByRole('button', { name: /Confirm Kernel Restart|^Restart$/i }).click();
  await dialog1.waitFor({ state: 'hidden', timeout: 10_000 });

  // Wait for ch03 to settle.  Use the DOM execution counts as the
  // signal of progress — kernel busy/idle transitions can flip
  // faster than our 500ms poll between cells, but the
  // `[N]:` execution numbers are sticky and monotonic.  We
  // declare ch03 settled once the highest execution count has
  // stopped advancing for 5 consecutive seconds AND is ≥ 1.
  const ch03Timeline: { t: number; maxCount: number; state: string }[] = [];
  const ch03Start = Date.now();
  let ch03Settled = false;
  let stableSince = -1;
  let lastMax = -1;
  while (Date.now() - ch03Start < 240_000) {
    const maxCount: number = await page.evaluate(() => {
      let max = 0;
      document.querySelectorAll('.jp-InputPrompt').forEach((p) => {
        const m = (p.textContent ?? '').match(/\[(\d+)\]/);
        if (m) max = Math.max(max, parseInt(m[1], 10));
      });
      return max;
    });
    const list: any[] = await page.evaluate(async (base) => {
      return await fetch(`${base}/api/kernels`).then((r) => r.json());
    }, baseURL);
    const state = list[0]?.execution_state ?? 'no-kernel';
    const last = ch03Timeline.at(-1);
    if (!last || last.maxCount !== maxCount || last.state !== state) {
      ch03Timeline.push({ t: Date.now() - ch03Start, maxCount, state });
    }
    if (maxCount > lastMax) {
      lastMax = maxCount;
      stableSince = Date.now();
    }
    // Settle: at least one cell ran AND counts have been stable
    // for 5s AND kernel is idle.
    if (lastMax >= 1 && stableSince > 0
        && Date.now() - stableSince >= 5_000
        && state === 'idle') {
      ch03Settled = true;
      break;
    }
    await page.waitForTimeout(500);
  }
  await testInfo.attach('ch03-kernel-state-timeline', {
    body: ch03Timeline.map((e) =>
      `${(e.t / 1000).toFixed(1)}s: max=[${e.maxCount}] state=${e.state}`).join('\n'),
    contentType: 'text/plain',
  });
  expect(ch03Settled, `ch03 never finished — see ch03-kernel-state-timeline attachment`).toBe(true);

  // ── Step 2: navigate to ch01 in the same browser tab.  Same
  //           kernel manager, but a different notebook view.
  await page.goto('/lab/tree/ch01-leanforhdl.ipynb');
  await page.waitForLoadState('networkidle');
  // Click the first cell to focus the new notebook.
  await page.locator('.jp-Cell').first().click();
  await page.waitForTimeout(500);

  // ── Step 3: run all cells in ch01.  If the wdb comm is
  //           still spamming the kernel from the previous tab,
  //           or the kernel is stuck on iopub HWM, ch01's cells
  //           won't finish.
  await page.getByRole('menuitem', { name: 'Kernel', exact: true }).click();
  await page.getByRole('menuitem', { name: /^Restart Kernel and Run All/i }).first().click();
  const dialog2 = page.locator('.jp-Dialog').first();
  await dialog2.waitFor({ state: 'visible', timeout: 30_000 });
  await dialog2.getByRole('button', { name: /Confirm Kernel Restart|^Restart$/i }).click();
  await dialog2.waitFor({ state: 'hidden', timeout: 10_000 });

  // Settle ch01 the same way as ch03 — execution counts are
  // sticky and survive the kind of fast busy/idle flips that
  // pure kernel-state polling can miss.  Crucially, this is the
  // step where the user-reported hang would manifest: if the
  // wdb comm channel from ch03 is still flooding the kernel,
  // ch01's cells either (a) don't increment past zero or
  // (b) increment partially and then stall.
  const ch01Timeline: { t: number; maxCount: number; state: string }[] = [];
  const ch01Start = Date.now();
  let ch01Settled = false;
  let ch01StableSince = -1;
  let ch01LastMax = -1;
  while (Date.now() - ch01Start < 240_000) {
    const maxCount: number = await page.evaluate(() => {
      let max = 0;
      document.querySelectorAll('.jp-InputPrompt').forEach((p) => {
        const m = (p.textContent ?? '').match(/\[(\d+)\]/);
        if (m) max = Math.max(max, parseInt(m[1], 10));
      });
      return max;
    });
    const list: any[] = await page.evaluate(async (base) => {
      return await fetch(`${base}/api/kernels`).then((r) => r.json());
    }, baseURL);
    const state = list[0]?.execution_state ?? 'no-kernel';
    const last = ch01Timeline.at(-1);
    if (!last || last.maxCount !== maxCount || last.state !== state) {
      ch01Timeline.push({ t: Date.now() - ch01Start, maxCount, state });
    }
    if (maxCount > ch01LastMax) {
      ch01LastMax = maxCount;
      ch01StableSince = Date.now();
    }
    if (ch01LastMax >= 1 && ch01StableSince > 0
        && Date.now() - ch01StableSince >= 5_000
        && state === 'idle') {
      ch01Settled = true;
      break;
    }
    await page.waitForTimeout(500);
  }

  await testInfo.attach('ch01-kernel-state-timeline', {
    body: ch01Timeline.map((e) =>
      `${(e.t / 1000).toFixed(1)}s: max=[${e.maxCount}] state=${e.state}`).join('\n'),
    contentType: 'text/plain',
  });
  await testInfo.attach('ch01-websocket-summary', {
    body: wsLog.map((w, i) => `[${i}] ${w.url}: ${w.events.length} frames`).join('\n'),
    contentType: 'text/plain',
  });

  expect(
    ch01Settled,
    `ch01 kernel never finished — timeline:\n${ch01Timeline.map((e) => `  ${(e.t / 1000).toFixed(1)}s: max=[${e.maxCount}] state=${e.state}`).join('\n')}`,
  ).toBe(true);
});

/**
 * Control test: same navigation pattern as `open ch01 after ch03
 * wdb`, but using ch02 (combinational, no wdb / no comm sessions)
 * as the "first" notebook.  If the second-tab hang depends on the
 * wdb comm channel surviving the navigation, this should pass
 * reliably; if it fails at the same rate as the wdb version, the
 * hang is a generic two-kernel race that wdb just happens to
 * exercise.
 */
test('open ch01 after ch02 (no wdb): second notebook still runs', async ({ page }, testInfo) => {
  const FIRST = 'ch02-combinational.ipynb';
  await page.goto(`/lab/tree/${FIRST}`);
  await page.waitForLoadState('networkidle');

  const baseURL = page.url().split('/lab')[0];
  await expect.poll(async () => {
    const sessions: any[] = await page.evaluate(async (base) => {
      return await fetch(`${base}/api/sessions`).then((r) => r.json());
    }, baseURL);
    return sessions.some((s: any) =>
      typeof s?.path === 'string' && s.path.endsWith(FIRST));
  }, { timeout: 60_000, message: 'ch02 kernel session never came up' }).toBe(true);

  await page.locator('.jp-Cell').first().click();
  await page.waitForTimeout(1_000);
  await page.getByRole('menuitem', { name: 'Kernel', exact: true }).click();
  const restartItem1 = page.getByRole('menuitem', { name: /^Restart Kernel and Run All/i }).first();
  await restartItem1.waitFor({ state: 'visible', timeout: 10_000 });
  await restartItem1.click();
  const dialog1 = page.locator('.jp-Dialog').first();
  await dialog1.waitFor({ state: 'visible', timeout: 30_000 });
  await dialog1.getByRole('button', { name: /Confirm Kernel Restart|^Restart$/i }).click();
  await dialog1.waitFor({ state: 'hidden', timeout: 10_000 });

  // Settle ch02 by execution-count (same recipe as the wdb test).
  const ch02Timeline: { t: number; maxCount: number; state: string }[] = [];
  const ch02Start = Date.now();
  let ch02Settled = false;
  let ch02StableSince = -1;
  let ch02LastMax = -1;
  while (Date.now() - ch02Start < 240_000) {
    const maxCount: number = await page.evaluate(() => {
      let max = 0;
      document.querySelectorAll('.jp-InputPrompt').forEach((p) => {
        const m = (p.textContent ?? '').match(/\[(\d+)\]/);
        if (m) max = Math.max(max, parseInt(m[1], 10));
      });
      return max;
    });
    const list: any[] = await page.evaluate(async (base) => {
      return await fetch(`${base}/api/kernels`).then((r) => r.json());
    }, baseURL);
    const state = list[0]?.execution_state ?? 'no-kernel';
    const last = ch02Timeline.at(-1);
    if (!last || last.maxCount !== maxCount || last.state !== state) {
      ch02Timeline.push({ t: Date.now() - ch02Start, maxCount, state });
    }
    if (maxCount > ch02LastMax) {
      ch02LastMax = maxCount;
      ch02StableSince = Date.now();
    }
    if (ch02LastMax >= 1 && ch02StableSince > 0
        && Date.now() - ch02StableSince >= 5_000
        && state === 'idle') {
      ch02Settled = true;
      break;
    }
    await page.waitForTimeout(500);
  }
  await testInfo.attach('ch02-kernel-state-timeline', {
    body: ch02Timeline.map((e) =>
      `${(e.t / 1000).toFixed(1)}s: max=[${e.maxCount}] state=${e.state}`).join('\n'),
    contentType: 'text/plain',
  });
  expect(ch02Settled, 'ch02 never finished').toBe(true);

  // Navigate to ch01 in the same browser tab.
  await page.goto('/lab/tree/ch01-leanforhdl.ipynb');
  await page.waitForLoadState('networkidle');
  await page.locator('.jp-Cell').first().click();
  await page.waitForTimeout(500);

  await page.getByRole('menuitem', { name: 'Kernel', exact: true }).click();
  await page.getByRole('menuitem', { name: /^Restart Kernel and Run All/i }).first().click();
  const dialog2 = page.locator('.jp-Dialog').first();
  await dialog2.waitFor({ state: 'visible', timeout: 30_000 });
  await dialog2.getByRole('button', { name: /Confirm Kernel Restart|^Restart$/i }).click();
  await dialog2.waitFor({ state: 'hidden', timeout: 10_000 });

  const ch01Timeline: { t: number; maxCount: number; state: string }[] = [];
  const ch01Start = Date.now();
  let ch01Settled = false;
  let ch01StableSince = -1;
  let ch01LastMax = -1;
  while (Date.now() - ch01Start < 240_000) {
    const maxCount: number = await page.evaluate(() => {
      let max = 0;
      document.querySelectorAll('.jp-InputPrompt').forEach((p) => {
        const m = (p.textContent ?? '').match(/\[(\d+)\]/);
        if (m) max = Math.max(max, parseInt(m[1], 10));
      });
      return max;
    });
    const list: any[] = await page.evaluate(async (base) => {
      return await fetch(`${base}/api/kernels`).then((r) => r.json());
    }, baseURL);
    const state = list[0]?.execution_state ?? 'no-kernel';
    const last = ch01Timeline.at(-1);
    if (!last || last.maxCount !== maxCount || last.state !== state) {
      ch01Timeline.push({ t: Date.now() - ch01Start, maxCount, state });
    }
    if (maxCount > ch01LastMax) {
      ch01LastMax = maxCount;
      ch01StableSince = Date.now();
    }
    if (ch01LastMax >= 1 && ch01StableSince > 0
        && Date.now() - ch01StableSince >= 5_000
        && state === 'idle') {
      ch01Settled = true;
      break;
    }
    await page.waitForTimeout(500);
  }
  await testInfo.attach('ch01-kernel-state-timeline', {
    body: ch01Timeline.map((e) =>
      `${(e.t / 1000).toFixed(1)}s: max=[${e.maxCount}] state=${e.state}`).join('\n'),
    contentType: 'text/plain',
  });
  expect(
    ch01Settled,
    `ch01 kernel never finished — timeline:\n${ch01Timeline.map((e) => `  ${(e.t / 1000).toFixed(1)}s: max=[${e.maxCount}] state=${e.state}`).join('\n')}`,
  ).toBe(true);
});

/**
 * Mitigation note.  An earlier draft of this file had a third
 * Playwright test that closed ch03's tab and then opened ch01,
 * expecting the kernel-shutdown-on-tab-close override (shipped
 * via `docker/tutorial/Dockerfile` →
 * `@jupyterlab/notebook-extension:tracker.kernelShutdown=true`)
 * to make the second kernel spawn cleanly.  The verification
 * was flaky for reasons unrelated to the bug — JupyterLab's
 * dialog flow on tab-close shifts between releases and the
 * spec kept tripping over UI quirks.
 *
 * The kernel-spawn race itself is now exercised by
 * `tests/e2e/wdb-hang-race.py`, which uses `jupyter_client`
 * directly (no browser, no UI dance).  That script reveals an
 * unexpected fact: the race is NOT in the xlean binary.  Two
 * coexisting xlean processes driven straight from
 * `jupyter_client` pass 5/5 trials.  The hang the user
 * reported only reproduces through the browser/JupyterLab
 * path — meaning the buggy interaction lives somewhere in
 * JupyterLab's comm-channel or kernel-manager logic, not in
 * the kernel binary.
 *
 * Practical workaround for users: close the previous chapter's
 * tab before opening the next one; the override turns that
 * close into a kernel shutdown automatically.  See
 * `docs/tutorial/md/Ch00_Setup.md` ("Switching between
 * chapters").
 */
