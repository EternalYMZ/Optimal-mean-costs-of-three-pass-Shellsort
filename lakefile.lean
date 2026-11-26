import Lake
open Lake DSL

package «shellsort-three-pass»

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "fc4f59e577feb1a4956671bc04ac18aaaf8cd842"

@[default_target]
lean_lib Shellsort where
  roots := #[`Shellsort, `Shellsort.Stage8]

@[default_target]
lean_lib ReviewJK where
  roots := #[`ReviewJK.Review]
  globs := #[.submodules `ReviewJK]

@[default_target]
lean_lib JKSign where
  roots := #[`JKSign.Review]
  globs := #[.submodules `JKSign]
