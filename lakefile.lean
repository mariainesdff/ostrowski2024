import Lake
open Lake DSL

package «ostrowski2024» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «Ostrowski2024» {
  -- add any library configuration options here
}
