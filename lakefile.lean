import Lake
open Lake DSL

package FalconPrecision where
  description := "Kernel-checked security of fixed-point Falcon signing (ePrint 2026/1531) with explicit constants"
  license := "Apache-2.0"
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`weak.linter.mathlibStandardSet, true⟩,
    ⟨`weak.linter.style.longFile, .ofNat 1500⟩
  ]

require VCVio from git "https://github.com/Verified-zkEVM/VCV-io" @ "e7770ef7e042e91fecf94504fcf1d448f372109e"

@[default_target]
lean_lib FalconPrecision where
  globs := #[.andSubmodules `FalconPrecision]

lean_lib Axioms where
  srcDir := "test"
  roots := #[`Axioms, `EndToEnd, `S7Axioms]
