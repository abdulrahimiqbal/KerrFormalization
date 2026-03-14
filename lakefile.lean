import Lake
open Lake DSL

package «KerrFormalization» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "master"

@[default_target]
lean_lib «KerrFormalization» where
