import { expect, test } from '@playwright/test';

declare global {
  interface Window {
    mypaDebug?: {
      setText(text: string): void;
      markers(): { message: string }[];
    };
  }
}

test('proof state updates from default empty message', async ({ page }) => {
  page.on('console', (msg) => {
    console.log(`[browser:${msg.type()}] ${msg.text()}`);
  });
  page.on('pageerror', (err) => {
    console.log(`[pageerror] ${err.message}`);
  });

  await page.goto('/');

  const root = page.getByTestId('proof-state-root');
  await expect(root).toBeVisible();

  await page.waitForTimeout(5000);
  console.log('proof-state-root:', await root.textContent());

  await expect(root).not.toContainText('No proof state.', { timeout: 20000 });
});

test('publishes diagnostics as Monaco markers', async ({ page }) => {
  await page.goto('/');
  await expect(page.getByTestId('proof-state-root')).not.toContainText('No proof state.', { timeout: 20000 });

  await page.evaluate(() => {
    window.mypaDebug?.setText('this is not a theorem header');
  });

  await expect.poll(async () => {
    return page.evaluate(() => window.mypaDebug?.markers().map((m) => m.message) ?? []);
  }, { timeout: 20000 }).toContain('Expected theorem header `def/theorem ... := by`.');
});
