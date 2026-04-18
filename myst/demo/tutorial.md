# Linear Logic, Statically Cached
## A MyST-style tutorial that embeds verified MyPA programs and cached proof states.

This page uses the `:::{mypa}` directive form and turns each block into a read-only proof notebook. The MyPA source is evaluated ahead of time, every cursor position is cached, and the browser only looks up those precomputed states.

:::callout
Click inside a code block, move with the arrow keys, and watch the proof state update. The document never sends edits to Lean, and there is no live LSP session in the page.
:::

## Identity in the sequent calculus

The smallest linear proof already shows the main idea: in the body of a theorem, the visible state depends only on cursor position.

:::{mypa} Identity sequent
def id_linear using LL in GENTZEN with LL : a ⊸ a := by
rlolli h
ax h
:::

## Building tensors

The right tensor rule splits the proof into two subgoals. Cursoring across the proof lets the reader see that branching structure without changing the source.

:::{mypa} Tensor introduction
def tensor_intro using LL in GENTZEN with LL : a ⊸ b ⊸ (a ⊗ b) := by
rlolli ha
rlolli hb
rtensor ha
ax ha
ax hb
:::

## Distributing tensor over plus

This example is larger on purpose. Static caching matters most once the tutorial contains proofs with several tactics and multiple local branches.

:::{mypa} Tensor-plus distribution
def tensor_plus_distrib using LL in GENTZEN with LL : ((a ⊗ (b ⊕ c)) ⊸ ((a ⊗ b) ⊕ (a ⊗ c))) & (((a ⊗ b) ⊕ (a ⊗ c)) ⊸ (a ⊗ (b ⊕ c))) := by
rwith
rlolli h
ltensor at h as ha hbc
lplus at hbc as hb hc
rplusl
rtensor ha
ax ha
ax hb
rplusr
rtensor ha
ax ha
ax hc
rlolli h
lplus at h as hab hac
ltensor at hab as ha hb
rtensor ha
ax ha
rplusl
ax hb
ltensor at hac as ha hc
rtensor ha
ax ha
rplusr
ax hc
:::

## Exponentials

When the profile allows `!`, cached proof states still work the same way. The browser does not need any extra semantic machinery; it only renders the states produced offline.

:::{mypa} Bang and with
def bang_with_distrib using LL! in GENTZEN with LL! : (!(a & b) ⊸ (!a ⊗ !b)) & ((!a ⊗ !b) ⊸ !(a & b)) := by
rwith
rlolli h
lbang at h
rtensor
rbang
lleft at h as ha
ax ha
rbang
lright at h as hb
ax hb
rlolli h
ltensor at h as ha hb
lbang at ha
lbang at hb
rbang
rwith
ax ha
ax hb
:::

## Why this integration is stable

- The code examples are verified during the tutorial build, so broken proofs fail the build instead of failing in the reader's browser.
- The browser runtime is read-only and only performs `(line, character) -> cached state` lookup.
- The proof-state panel is rendered by the same extension asset used by the VS Code goals view.
