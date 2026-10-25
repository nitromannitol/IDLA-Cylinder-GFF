import Lake

open Lake DSL

package «idlaCyl» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "065356127b1dc0016f66b7283ce0ce2c4055aa55"

require «lattice-probability» from git
  "https://github.com/nitromannitol/Lattice-Probability" @ "788c74c88494a93bcea3f71a0b85a6fa35706842"

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
