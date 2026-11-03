import Tools.ShippingGen4KWalkEnv

-- shape probe (rt166): how `(← IO.getEnv ..)` in a MetaM do-block (Elab.lean:5602) elaborates
open Lean Meta Tools.ShippingGen4KWalkEnv

def probeGetEnv : MetaM Bool := do
  if (← IO.getEnv "SPARKLE_NO_REGDEDUP").isSome then return true
  return false

set_option pp.explicit true in
#print probeGetEnv

set_option pp.explicit true in
def asc (n : String) : MetaM (Option String) := (IO.getEnv n : MetaM (Option String))
set_option pp.explicit true in
#print asc

example : probeGetEnv =
    (bind (IO.getEnv "SPARKLE_NO_REGDEDUP" : MetaM (Option String))
      (fun x => if x.isSome = true then pure true else pure false) : MetaM Bool) := by
  unfold probeGetEnv; rfl
