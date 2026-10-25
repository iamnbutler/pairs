import Pairs.Fuzz

/-! `lake exe pairsfuzz`: Pairs against a random host (`Pairs/Fuzz.lean`). -/

def main (args : List String) : IO UInt32 := Pairs.Fuzz.main args
