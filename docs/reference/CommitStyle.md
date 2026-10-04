# Commit message style

Conventions for writing Sparkle commit messages.

## Language

Commit messages are in **English**, even when the underlying
discussion happened in another language. Paraphrase the technical
point rather than quoting the original.

## Don't include raw conversational records

Avoid lines like:

  - `User feedback: "..."` followed by a verbatim quote
  - `User pushback: ...`
  - `User question: ...`
  - `Per user feedback: ...`
  - `User said: ...`

These are conversational records, not changelog material. They
date the commit message to a specific exchange and embed
information that the commit itself can't justify on its own.

Instead, **state the technical motivation directly**:

| Bad                                    | Good                                  |
|----------------------------------------|---------------------------------------|
| `User feedback: "this is confusing"`   | `Improve readability of X by ...`     |
| `User asked: can we add Y?`            | `Add Y to support Z workflow`         |
| `Per user pushback, I rechecked …`     | `Re-examined the elab/codegen layer:` |

If the change addresses a real shortcoming or correction, name
the shortcoming itself, not the conversation that surfaced it.

## Structure

1. **Subject line**: 50-72 chars, imperative mood, no trailing
   period. Optionally a topic prefix (e.g., `MMU/PA:`, `Tutorial:`).
2. **Blank line.**
3. **Body**: wrap at 72 chars. Explain *what* and *why* (not
   *how* — the diff already shows that).
4. Optional sections: `Files`, `Verified`, `Open issues`.

## Examples

Good:

```
MMU/PA: pin Sv32 megapage PA fix with concrete-vector theorems

Adds 5 `decide`-closed theorems in MMU/PA.lean covering the
exact translation vectors that were broken pre-bf6d873:
  ...
```

Avoid:

```
MMU/PA: fix what the user reported

User feedback: "Linux didn't boot"
Per user request, I went and added some theorems for ...
```

## Co-author / acknowledgement

When a contribution comes from a discussion or a particular
user's idea, use the standard `Co-authored-by:` trailer at the
end of the commit message. Do not paraphrase the conversation in
the body — the trailer is enough to give credit.
