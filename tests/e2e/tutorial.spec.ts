import { test, expect, Page } from '@playwright/test';

/**
 * Open one chapter notebook end-to-end:
 *   - Land on /lab
 *   - Wait for the file browser to settle
 *   - Open ch04-modules.ipynb
 *   - Wait for the kernel indicator to read "Lean 4"
 *   - Run all cells
 *   - Read the first cell output and assert it contains either the
 *     expected SystemVerilog snippet or, on failure, the actual
 *     error so the test report shows what went wrong on the kernel
 *     side (this is exactly the path that breaks when LEAN_PATH /
 *     kernelspec wiring is wrong).
 */

const CHAPTER = 'ch04-modules.ipynb';

async function openChapter(page: Page, chapter: string) {
  await page.goto(`/lab/tree/${chapter}`);
  // The file browser sometimes intercepts the navigation; click into
  // the notebook explicitly if we land on the launcher instead.
  await page.waitForLoadState('networkidle');
}

test('chapter 4 import cell: Sparkle namespaces resolve in xlean kernel', async ({ page }) => {
  await openChapter(page, CHAPTER);

  // The kernel-status badge in the top-right shows the kernel name.
  // We're happy with anything that says "Lean 4".  If the kernel
  // didn't auto-attach, JupyterLab pops a "Select Kernel" dialog —
  // that itself is a failure mode worth catching.
  const dialogPromise = page.locator('.jp-Dialog').first();
  const kernelLabel = page.locator('.jp-Toolbar-kernelName').first();

  await Promise.race([
    kernelLabel.waitFor({ state: 'visible', timeout: 60_000 }),
    dialogPromise.waitFor({ state: 'visible', timeout: 60_000 }),
  ]);

  // If a "Select Kernel" dialog appeared, surface that explicitly.
  if (await dialogPromise.isVisible().catch(() => false)) {
    const text = await dialogPromise.innerText();
    throw new Error(
      `JupyterLab popped a kernel-selection dialog when opening ${CHAPTER}. ` +
      `This means the notebook's metadata.kernelspec.name does not match ` +
      `any installed kernel.  Dialog text:\n${text}`,
    );
  }

  // Restart all live kernels via the Jupyter REST API before
  // running cells.  xeus-lean only accepts `import` as the very
  // first statement of a session, so a kernel reused from a
  // previous test (or from someone poking at the notebook) blows
  // up on the chapter's first cell with "invalid 'import' command".
  // The REST path is far more robust than fishing for the
  // "Kernel → Restart Kernel…" menu, whose dialog labels and
  // CSS classes drift between JupyterLab versions.
  const baseURL = page.url().split('/lab')[0];
  const kernels = await page.request.get(`${baseURL}/api/kernels`).then(r => r.json());
  for (const k of kernels) {
    await page.request.post(`${baseURL}/api/kernels/${k.id}/restart`);
  }
  // Reload the notebook so JupyterLab picks up the now-fresh kernel
  // (the old kernel-busy state can otherwise stick to the cell gutter).
  await page.reload();
  await page.waitForLoadState('networkidle');

  // Trigger "Run All Cells" via the Run menu.  Keyboard shortcuts
  // vary across JupyterLab versions (`Ctrl+Shift+Enter` is "run
  // selected cell" in 4.x, not "run all"), so we drive the menu
  // explicitly.
  await page.getByRole('menuitem', { name: 'Run', exact: true }).click();
  await page.getByRole('menuitem', { name: 'Run All Cells', exact: true }).click();

  // Wait until *all* code cells have run (every `.jp-InputPrompt`
  // shows `[N]`, none still show `[ ]` or `[*]`).  Without this we
  // race the kernel and scrape stale outputs from only the first
  // few cells, missing the chapter's `#synthesizeVerilog` near
  // the end.
  await expect.poll(async () => {
    const counters = await page.locator('.jp-InputPrompt').allInnerTexts();
    if (counters.length === 0) return false;
    // Any code cell still pending or busy?
    const pending = counters.some((s) => /\[\s*\]|\[\*\]/.test(s));
    if (pending) return false;
    // At least one cell must have an execution count (i.e. cells
    // actually ran).
    return counters.some((s) => /\[\d+\]/.test(s));
  }, { timeout: 180_000, message: 'cells never finished executing' }).toBe(true);

  // Scrape every output area for known signals.
  const outputs = await page.locator('.jp-OutputArea-output').allInnerTexts();
  const joined = outputs.join('\n');

  // Negative assertion (the user-reported failure): no namespace
  // resolution errors anywhere in the chapter output.
  expect(joined, `Outputs were:\n${joined}`).not.toMatch(/unknown namespace `Sparkle/);
  expect(joined, `Outputs were:\n${joined}`).not.toMatch(/Unknown constant `Display\./);

  // Positive assertion: at least one cell rendered SV from
  // `#synthesizeVerilog`.  We accept either the conventional
  // `module foo (` opener or, if xeus-lean wraps SV in a
  // `<pre class="systemverilog">` block, the keyword on its own.
  expect(joined).toMatch(/module\s+\w+\s*\(|endmodule/);
});
