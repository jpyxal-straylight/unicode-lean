import Lake
open Lake DSL

package unicode where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib Unicode where
  srcDir := "."
  roots := #[`Unicode]
  globs := #[.submodules `Unicode]
