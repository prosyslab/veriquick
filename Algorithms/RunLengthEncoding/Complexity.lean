import VeriQuick.Complexity
import Algorithms.RunLengthEncoding.Correctness

open VeriQuick.TimeM
open VeriQuick.Complexity
open Algorithms.RunLengthEncoding.Correctness

namespace Algorithms.RunLengthEncoding.Complexity

/-!
`decode` is specification machinery. Its running time is proportional to the
sum of run counts (the expanded output length), not merely the number of runs,
so the list-length `Size` instance is intentionally used only for `encode`.
-/

/-- Linear cost bound with a nonzero value at input size zero. -/
def Bound (n : Nat) : Nat := n + 1

/-- Instrumented run-length encoding is O(n) in the input-list length. -/
def complexity (impl : List Nat → TimeM (List Run)) : Prop :=
  Asymptotic impl (.some Bound)

end Algorithms.RunLengthEncoding.Complexity
