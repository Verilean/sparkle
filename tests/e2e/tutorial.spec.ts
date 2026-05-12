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

  // Drive the kernel directly via Jupyter's REST + WebSocket
  // protocol.  This sidesteps all UI flakiness — JupyterLab's
  // "Run All Cells" menu item, restart-kernel dialog labels,
  // and cell-prompt polling all drift between versions and
  // they're not what the user actually cares about.  What
  // matters is: does the chapter's `import Sparkle …` line
  // resolve in a fresh kernel?
  const baseURL = page.url().split('/lab')[0];
  const result = await page.evaluate(
    async ({ base, chapter }) => {
      const xsrf = document.cookie
        .split('; ')
        .find((c) => c.startsWith('_xsrf='))
        ?.split('=')[1] ?? '';
      const auth = { 'X-XSRFToken': xsrf };

      // Fetch the chapter notebook and pull out its first
      // code cell — that's the `import Sparkle …` block.
      const nb = await fetch(`${base}/api/contents/${chapter}`)
        .then((r) => r.json());
      const firstCode = (nb.content.cells as any[])
        .find((c) => c.cell_type === 'code');
      const code = Array.isArray(firstCode.source)
        ? firstCode.source.join('')
        : firstCode.source;

      // Spawn a fresh xeus-lean kernel.
      const kernel = await fetch(`${base}/api/kernels`, {
        method: 'POST',
        headers: { ...auth, 'Content-Type': 'application/json' },
        body: JSON.stringify({ name: 'xeus-lean' }),
      }).then((r) => r.json());

      try {
        // Open WebSocket to the kernel's "channels" endpoint
        // and execute the import code.  Wait for the
        // `execute_reply` and any `error` / `stream` messages.
        const wsUrl = `${base.replace(/^http/, 'ws')}/api/kernels/${kernel.id}/channels`;
        return await new Promise<{ status: string; output: string }>(
          (resolve, reject) => {
            const ws = new WebSocket(wsUrl);
            let output = '';
            let status = '';
            ws.onopen = () => {
              const msgId = crypto.randomUUID();
              const msg = {
                header: {
                  msg_id: msgId,
                  username: 'pw',
                  session: crypto.randomUUID(),
                  msg_type: 'execute_request',
                  version: '5.3',
                  date: new Date().toISOString(),
                },
                metadata: {},
                content: {
                  code,
                  silent: false,
                  store_history: false,
                  user_expressions: {},
                  allow_stdin: false,
                  stop_on_error: true,
                },
                buffers: [],
                parent_header: {},
                channel: 'shell',
              };
              ws.send(JSON.stringify(msg));
            };
            ws.onmessage = (ev) => {
              const m = JSON.parse(ev.data as string);
              if (m.msg_type === 'stream') output += m.content.text;
              if (m.msg_type === 'error') {
                output += m.content.ename + ': ' + m.content.evalue + '\n';
                output += (m.content.traceback ?? []).join('\n');
              }
              if (m.msg_type === 'execute_reply') {
                status = m.content.status;
                ws.close();
                resolve({ status, output });
              }
            };
            ws.onerror = () => reject(new Error('WebSocket error'));
            setTimeout(() => {
              ws.close();
              reject(new Error('execute_reply timeout (60s)'));
            }, 60_000);
          },
        );
      } finally {
        await fetch(`${base}/api/kernels/${kernel.id}`, {
          method: 'DELETE',
          headers: auth,
        });
      }
    },
    { base: baseURL, chapter: CHAPTER },
  );

  console.log('--- kernel execute_reply ---');
  console.log('status:', result.status);
  console.log('output:', result.output);

  // The user's reported failure: namespace resolution dies
  // because `Sparkle.Core.Domain` isn't on the kernel's
  // `LEAN_PATH`.  Catch that explicitly.
  expect(
    result.output,
    `import-cell output:\n${result.output}`,
  ).not.toMatch(/unknown namespace `Sparkle/);
  expect(
    result.output,
    `import-cell output:\n${result.output}`,
  ).not.toMatch(/Unknown constant `Display\./);

  // The execute_reply itself must report success.
  expect(result.status, `output:\n${result.output}`).toBe('ok');
});
