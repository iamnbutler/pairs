import Checks
import Pairs.Fuzz
import Cairn.Fuzz.Collect
import Cairn.Fuzz.Main

/-! `lake exe fuzz` (`cairn fuzz`): Cairn's claim-driven fuzzer on Pairs's controls (Cairn's
docs/fuzz.md): clicks, keys and resizes, the invariants checked after each step. The host's side
(replies, timers, evictions) is `lake exe pairsfuzz`. -/

def targets : List Cairn.Fuzz.Target := fuzz_targets%

def main (args : List String) : IO UInt32 := Cairn.Fuzz.main targets args
