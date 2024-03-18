import Lake
open Lake DSL

package «functional-programming-in-lean» where
  -- add package configuration options here

lean_lib «FunctionalProgrammingInLean» where
  -- add library configuration options here
  require Http from git "https://github.com/axiomed/Http.lean.git"

@[default_target]
lean_exe «functional-programming-in-lean» where
  root := `Main
