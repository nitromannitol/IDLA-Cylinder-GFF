import Lake

open Lake DSL

package «idlaCyl» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "81a5d257c8e410db227a6665ed08f64fea08e997"

require «lattice-probability» from git
  "https://github.com/nitromannitol/Lattice-Probability" @ "fcfd4332bc9051cf5a6bbabe73e334df3bf28e76"

@[default_target]
lean_lib «IdlaCyl» where
  globs := #[.andSubmodules `IdlaCyl]
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`linter.unusedVariables, true⟩,
    ⟨`linter.unusedSectionVars, true⟩,
    ⟨`linter.unusedSimpArgs, true⟩,
    ⟨`linter.unnecessarySimpa, true⟩,
    ⟨`linter.deprecated, true⟩
  ]

/-- The comparator audit (`IdlaCylAudit/`): Mathlib-only challenges for the four main theorems,
their shared vocabulary, the bridge to the library and the solutions. Not a default target: it
builds on demand (`lake build IdlaCylAudit`). -/
lean_lib IdlaCylAudit where
  globs := #[.submodules `IdlaCylAudit]
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`linter.unusedVariables, true⟩,
    ⟨`linter.unusedSectionVars, true⟩,
    ⟨`linter.unusedSimpArgs, true⟩,
    ⟨`linter.unnecessarySimpa, true⟩,
    ⟨`linter.deprecated, true⟩
  ]
