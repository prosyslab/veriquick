import VeriQuick.Complexity

open VeriQuick.TimeM
open VeriQuick.Complexity

namespace Algorithms.BinarySearch.Complexity

def Bound (n : Nat) : Nat := Nat.log2 n + 1

def complexity (impl : Nat → Array Nat → TimeM Nat) : Prop :=
  ∀ key, Asymptotic (impl key) (.some Bound)

end Algorithms.BinarySearch.Complexity
