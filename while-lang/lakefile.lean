import Lake
open Lake DSL

package "while-lang" where
  -- add package configuration options here

lean_lib «WhileLang» where
  -- add library configuration options here

@[default_target]
lean_exe "while-lang" where
  root := `Main
