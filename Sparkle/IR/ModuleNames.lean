import Sparkle.IR.NameHints

/-! Lexical contract for emitted SystemVerilog module identifiers. Invalid
names are rejected by the synthesis entry, not renamed by a new encoding. -/
namespace Sparkle.IR.ModuleNames

set_option maxRecDepth 2048

/-- IEEE 1364 / 1800 keywords through 1800-2012, including configuration
keywords. Cross-checked against Icarus Verilog v12_0 lexor_keyword.gperf:
https://github.com/steveicarus/iverilog/blob/v12_0/lexor_keyword.gperf
This is separate from the deliberately partial in-tree parser keyword list. -/
def keywords : List String :=
  ["accept_on", "alias", "always", "always_comb", "always_ff", "always_latch", "and", "assert",
   "assign", "assume", "automatic", "before", "begin", "bind", "bins", "binsof",
   "bit", "break", "buf", "bufif0", "bufif1", "byte", "case", "casex",
   "casez", "cell", "chandle", "checker", "class", "clocking", "cmos", "config",
   "const", "constraint", "context", "continue", "cover", "covergroup", "coverpoint", "cross",
   "deassign", "default", "defparam", "design", "disable", "dist", "do", "edge",
   "else", "end", "endcase", "endchecker", "endconfig", "endclass", "endclocking", "endfunction",
   "endgenerate", "endgroup", "endinterface", "endmodule", "endpackage", "endprimitive", "endprogram", "endproperty",
   "endspecify", "endsequence", "endtable", "endtask", "enum", "event", "eventually", "expect",
   "export", "extends", "extern", "final", "first_match", "for", "foreach", "force",
   "forever", "fork", "forkjoin", "function", "generate", "genvar", "global", "highz0",
   "highz1", "if", "iff", "ifnone", "ignore_bins", "illegal_bins", "implies", "implements",
   "import", "incdir", "include", "initial", "inout", "input", "inside", "instance",
   "int", "integer", "interconnect", "interface", "intersect", "join", "join_any", "join_none",
   "large", "let", "liblist", "library", "local", "localparam", "logic", "longint",
   "macromodule", "matches", "medium", "modport", "module", "nand", "negedge", "nettype",
   "new", "nexttime", "nmos", "nor", "noshowcancelled", "not", "notif0", "notif1",
   "null", "or", "output", "package", "packed", "parameter", "pmos", "posedge",
   "primitive", "priority", "program", "property", "protected", "pull0", "pull1", "pulldown",
   "pullup", "pulsestyle_onevent", "pulsestyle_ondetect", "pure", "rand", "randc", "randcase", "randsequence",
   "rcmos", "real", "realtime", "ref", "reg", "reject_on", "release", "repeat",
   "restrict", "return", "rnmos", "rpmos", "rtran", "rtranif0", "rtranif1", "s_always",
   "s_eventually", "s_nexttime", "s_until", "s_until_with", "scalared", "sequence", "shortint", "shortreal",
   "showcancelled", "signed", "small", "soft", "solve", "specify", "specparam", "static",
   "string", "strong", "strong0", "strong1", "struct", "super", "supply0", "supply1",
   "sync_accept_on", "sync_reject_on", "table", "tagged", "task", "this", "throughout", "time",
   "timeprecision", "timeunit", "tran", "tranif0", "tranif1", "tri", "tri0", "tri1",
   "triand", "trior", "trireg", "type", "typedef", "union", "unique", "unique0",
   "unsigned", "until", "until_with", "untyped", "use", "uwire", "var", "vectored",
   "virtual", "void", "wait", "wait_order", "wand", "weak", "weak0", "weak1",
   "while", "wildcard", "wire", "with", "within", "wone", "wor", "xnor",
   "xor"]

def legal (s : String) : Bool :=
  (match s.toList with | [] => false | c :: _ => c.isAlpha || c == '_') &&
    s.all NameHints.charOk && !keywords.contains s

/-- This names only the lexical contract. Declaration identity and linkage
are checked after the existing Verilog normalization, in ModuleNameCheck. -/
theorem legal_spec {s : String} (h : legal s = true) :
    (∃ c cs, s.toList = c :: cs ∧ (c.isAlpha = true ∨ c = '_')) ∧
    NameHints.Clean s ∧ s ∉ keywords := by
  simp only [legal, Bool.and_eq_true] at h
  refine ⟨?_, ?_, ?_⟩
  · cases he : s.toList with
    | nil => simp [he] at h
    | cons c cs => exact ⟨c, cs, rfl, by simpa [he] using h.1.1⟩
  · simpa only [NameHints.Clean, String.all_bool_eq, List.all_eq_true] using h.1.2
  · simpa using h.2

end Sparkle.IR.ModuleNames
