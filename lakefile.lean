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

require VCVio from git "https://github.com/Verified-zkEVM/VCV-io" @ "c2192f887572f92312e5312e992670f230f1d1d8"

@[default_target]
lean_lib FalconPrecision

lean_lib Axioms where
  srcDir := "test"
  roots := #[`Axioms, `EndToEnd]
