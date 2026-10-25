import Checks
import Pairs.Fuzz
import Cairn.Fuzz.Collect
import Cairn.Fuzz.Main

/-! `lake exe fuzz` (`cairn fuzz`): Cairn's claim-driven fuzzer on Pairs's controls (Cairn's
docs/fuzz.md): clicks, keys and resizes, the invariants checked after each step. It plays the
host too, with Pairs's replies and checks (`Pairs.fuzz`, Pairs/Fuzz.lean). -/

def targets : List Cairn.Fuzz.Target := fuzz_targets%

def main (args : List String) : IO UInt32 := Cairn.Fuzz.main targets args
