# Tutorial chapter sources (Markdown)

These are the **canonical chapter sources** for the Sparkle
tutorial.  Edit a chapter by editing the corresponding
`Ch??_*.md` here.

## Cell-format conventions

The Markdown is processed by xeus-lean's `xlean-convert` CLI:

| Fence tag                       | Becomes                                                  |
|---------------------------------|----------------------------------------------------------|
| ` ```lean ` (case-insensitive)  | a Jupyter **code** cell + a `-- %%` block in the `.lean` |
| ` ```text `, ` ```bash `, etc.  | stays inside the surrounding Markdown cell (illustrative) |
| no fence                        | accumulates into a Markdown cell                         |

So when you want to *show* Lean code that should not be executed
(for example, a code template, an "old style" example, or a
pseudocode sketch with `...`), use ` ```text `:

````markdown
```text
def halfAdder ... : Signal dom Bool × Signal dom Bool := ...
```
````

Use ` ```lean ` only for code that should run as part of the
chapter.

## Building

After editing, regenerate the `.lean` and `.ipynb` artefacts:

```bash
bash docs/tutorial/build-from-md.sh
```

Then typecheck every code cell:

```bash
lake build TutorialNotebooks
```

Both should succeed before you commit.  CI runs the same two
commands.

## Style rules

Two non-negotiable rules govern every ` ```lean ` cell:

1. **Synthesis-safe by default.**  Every ` ```lean ` block must
   compile via `#synthesizeVerilog`.  See
   `docs/reference/Troubleshooting_Synthesis.md` for the canonical
   list (no `if-then-else` over `Signal dom Bool`, no `unbundle2`
   destructuring, no `Signal.loopMemo`).
2. **Read-friendly.**  Operators (`+`, `-`, `*`, `<<<`, `&&&`,
   `===`) and `circuit do` first.  No `<$>` / `<*>` /
   `Signal.pure` in chapter prose; `Signal.loop` shown once for
   comparison only.
