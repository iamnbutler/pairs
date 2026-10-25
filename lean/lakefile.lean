import Lake
open Lake DSL

package pairs where
  leanOptions := #[⟨`weak.cairn.claims.scope, "pairs"⟩]

require "iamnbutler" / "cairn" @ "^0.2.1"
require "iamnbutler" / "cairn_json" @ "^0.1.0"

@[default_target]
lean_lib Pairs where
  roots := #[`Pairs.Abi, `Pairs]
  defaultFacets := #[LeanLib.staticFacet]
