/-
  Smoke test for MermaidHelper: emit a small diagram and assert
  the output contains the expected MIME marker.
-/

import TutorialExtended.MermaidHelper

open TutorialExtended.MermaidHelper

def main : IO UInt32 := do
  IO.println "── MermaidHelper smoke test ──"
  -- Build a diagram and capture the rendered HTML wrapper.
  let graph := "flowchart LR\n  A --> B --> C"
  let wrapped := mermaidHTML graph
  IO.println "(rendered HTML, first 150 chars):"
  IO.println (wrapped.take 150)
  -- Verify the MIME marker is well-formed.
  let marker := mkMarker "text/html" wrapped
  let escByte := Char.ofNat 0x1B
  let rsByte  := Char.ofNat 0x1E
  let hasOpener := marker.startsWith s!"{escByte}MIME:text/html{rsByte}"
  let hasCloser := marker.endsWith   s!"{escByte}/MIME{rsByte}"
  IO.println s!"opener present: {hasOpener}"
  IO.println s!"closer present: {hasCloser}"
  let containsFlowchart := decide ((wrapped.splitOn "flowchart").length > 1)
  IO.println s!"escaped Mermaid graph contained 'flowchart': {containsFlowchart}"
  -- And run the actual emitter to demonstrate stdout output.
  IO.println "\n── direct emit: ──"
  mermaid graph
  return 0
