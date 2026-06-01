import Lake
open Lake DSL

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

package Kopt where

@[default_target]
lean_lib Kopt where
