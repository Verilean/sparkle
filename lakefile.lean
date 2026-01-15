import Lake
open Lake DSL

package «sparkle» where
  -- add package configuration options here

lean_lib «Sparkle» where
  -- add library configuration options here

@[default_target]
lean_exe «sparkle» where
  root := `Main
