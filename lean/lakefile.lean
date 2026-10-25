import Lake
open Lake DSL

/-- Pairs on Cairn. The package name is the claim scope: Pairs's claims are `pairs^N`. -/
package pairs where
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩,
    -- `weak.`: Lake passes it to every module, and only those that use the claim commands know it.
    ⟨`weak.cairn.claims.scope, "pairs"⟩]

require "iamnbutler" / "cairn" @ "^0.2.4"
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

/-- `lake exe fuzz` (`cairn fuzz`): Cairn's fuzzer on the app and a simulated host. -/
lean_exe fuzz where
  root := `FuzzMain
