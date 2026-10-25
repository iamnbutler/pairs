import Lake
open Lake DSL

/-- Pairs on Cairn. The package name is the claim scope: Pairs's claims are `pairs^N`. -/
package pairs where
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩,
    -- `weak.`: Lake passes it to every module, and only those that use the claim commands know it.
    ⟨`weak.cairn.claims.scope, "pairs"⟩]

require cairn from git "https://github.com/iamnbutler/cairn.git" @ "1987f0639398aee13d6c68751e2e1d9e2ea7f0c9" / "lean"
require "iamnbutler" / "cairn_json" @ "^0.1.0"

/-- The app: its exports (`Pairs.Abi`) and everything they import from this package. -/
@[default_target]
lean_lib Pairs where
  roots := #[`Pairs.Abi, `Pairs]
  defaultFacets := #[LeanLib.staticFacet]

/-- The app with its proofs and checks (`Checks.lean`): what the ledger, the axiom audit and the
kernel replay read. Never linked into the app. -/
@[default_target]
lean_lib Checks

/-- `lake exe pairsfuzz [--seed S] [--iterations N] [--steps K] [--out DIR]`: the app's machine
against a random host (`Pairs/Fuzz.lean`). -/
lean_exe pairsfuzz where
  root := `PairsFuzz

/-- `lake exe fuzz` (`cairn fuzz`): Cairn's claim-driven fuzzer on the app's controls. -/
lean_exe fuzz where
  root := `FuzzMain
