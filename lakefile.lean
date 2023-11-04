import Lake
open Lake DSL

package «random_graphs» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «RandomGraphs» {
  -- add any library configuration options here
}
