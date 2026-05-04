import { expect, test } from '@playwright/test';

declare global {
  interface Window {
    mypaDebug?: {
      setText(text: string): void;
      getText(): string;
      setPosition(lineNumber: number, column: number): void;
      getPosition(): { lineNumber: number; column: number } | null;
      markers(): { message: string }[];
      symbolCompletionLabels(prefix: string): string[];
      wordBasedSuggestions(): string;
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
  }, { timeout: 20000 }).toContain('Expected theorem header `theorem ... := by`.');
});

test('linear symbol shortcuts insert unicode completions', async ({ page }) => {
  await page.goto('/');
  await expect(page.getByTestId('proof-state-root')).not.toContainText('No proof state.', { timeout: 20000 });

  const cases = [
    { shortcut: '\\tensor', output: '⊗' },
    { shortcut: '\\par', output: '⅋' },
    { shortcut: '\\oplus', output: '⊕' },
    { shortcut: '\\with', output: '&' },
    { shortcut: '\\lolli', output: '⊸' },
    { shortcut: '\\^bot', output: '^bot' },
  ];

  for (const item of cases) {
    await page.evaluate(() => {
      window.mypaDebug?.setText('');
    });
    await page.locator('.monaco-editor').click();
    await page.keyboard.type(item.shortcut);
    await expect.poll(async () => {
      return page.evaluate(() => window.mypaDebug?.getText() ?? '');
    }, { timeout: 20000 }).toBe(item.output);
  }
});

test('symbol shortcut expansion preserves cursor at insertion point', async ({ page }) => {
  await page.goto('/');
  await expect(page.getByTestId('proof-state-root')).not.toContainText('No proof state.', { timeout: 20000 });

  const text = [
    'theorem cursor_demo using ILLp : A  := by',
    '  rlolli h',
    '  ax h',
  ].join('\n');
  const insertionColumn = text.split('\n')[0].indexOf('  := by') + 2;

  await page.evaluate(({ source, column }) => {
    window.mypaDebug?.setText(source);
    window.mypaDebug?.setPosition(1, column);
  }, { source: text, column: insertionColumn });
  await page.keyboard.type('\\lolli');

  await expect.poll(async () => {
    return page.evaluate(() => ({
      text: window.mypaDebug?.getText() ?? '',
      position: window.mypaDebug?.getPosition() ?? null,
    }));
  }, { timeout: 20000 }).toEqual({
    text: text.replace('A  := by', 'A ⊸ := by'),
    position: { lineNumber: 1, column: insertionColumn + 1 },
  });
});

test('backslash symbol suggestions exclude theorem names', async ({ page }) => {
  await page.goto('/');
  await expect(page.getByTestId('proof-state-root')).not.toContainText('No proof state.', { timeout: 20000 });

  await page.evaluate(() => {
    window.mypaDebug?.setText('');
  });
  await expect.poll(async () => {
    return page.evaluate(() => window.mypaDebug?.symbolCompletionLabels('\\ten') ?? []);
  }, { timeout: 20000 }).toEqual(['\\tensor']);
  await expect.poll(async () => {
    return page.evaluate(() => window.mypaDebug?.symbolCompletionLabels('\\^') ?? []);
  }, { timeout: 20000 }).toEqual(['\\^bot']);
  await expect.poll(async () => {
    return page.evaluate(() => window.mypaDebug?.symbolCompletionLabels('\\bot') ?? []);
  }, { timeout: 20000 }).toEqual([]);
  await expect.poll(async () => {
    return page.evaluate(() => window.mypaDebug?.wordBasedSuggestions() ?? '');
  }, { timeout: 20000 }).toBe('off');

  await page.locator('.monaco-editor').click();
  await page.keyboard.type('\\lol');
  await expect(page.locator('.suggest-widget')).toContainText('\\lolli', { timeout: 20000 });
  await expect(page.locator('.suggest-widget')).not.toContainText('ill_ex_01_tensor_comm');
});

test('help page documents exact theorem starters', async ({ page }) => {
  await page.goto('/');
  await page.getByRole('button', { name: 'Help' }).click();

  await expect(page.getByRole('heading', { name: 'Quick Start' })).toBeVisible();
  await expect(page.getByText('theorem <name> using CLLp : <formula> := by')).toBeVisible();
  await expect(page.getByText('theorem <name> using ILLp : <formula> := by')).toBeVisible();
  await expect(page.getByText('theorem <name> using <logic> : <formula> := by')).toBeVisible();
  await expect(page.getByText('A^bot', { exact: true })).toBeVisible();
  await expect(page.getByText('A\\^bot', { exact: true })).toBeVisible();
  await expect(page.getByText('Type a backslash prefix such as')).toBeVisible();
  await expect(page.getByText('\\lol', { exact: true })).toBeVisible();
  await expect(page.getByText('\\ten', { exact: true })).toBeVisible();
});

test('help toggle preserves editor text and cursor', async ({ page }) => {
  await page.goto('/');
  await expect(page.getByTestId('proof-state-root')).not.toContainText('No proof state.', { timeout: 20000 });

  const text = [
    'theorem preserve_demo using ILLp : A ⊸ A := by',
    '  rlolli h',
    '  ax h',
  ].join('\n');

  await page.evaluate((source) => {
    window.mypaDebug?.setText(source);
    window.mypaDebug?.setPosition(2, 5);
  }, text);

  await page.getByRole('button', { name: 'Help' }).click();
  await expect(page.getByRole('heading', { name: 'MyPA Help' })).toBeVisible();
  await page.getByRole('button', { name: 'Editor' }).click();

  await expect.poll(async () => {
    return page.evaluate(() => ({
      text: window.mypaDebug?.getText() ?? '',
      position: window.mypaDebug?.getPosition() ?? null,
    }));
  }, { timeout: 20000 }).toEqual({
    text,
    position: { lineNumber: 2, column: 5 },
  });
});

test('editor scrollbar gutter is opaque', async ({ page }) => {
  await page.goto('/');
  await expect(page.getByTestId('proof-state-root')).not.toContainText('No proof state.', { timeout: 20000 });

  await expect.poll(async () => {
    return page.locator('.mypa-editor-host .scrollbar.vertical').first().evaluate((node) => {
      return getComputedStyle(node).backgroundColor;
    });
  }, { timeout: 20000 }).toBe('rgb(255, 255, 255)');
});
