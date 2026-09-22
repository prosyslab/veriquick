import VeriQuick.Complexity

open VeriQuick.TimeM
open VeriQuick.Complexity

namespace Algorithms.LinearSearch.Complexity

def Bound (n : Nat) : Nat := n + 1

def complexity (impl : Nat → List Nat → TimeM Bool) : Prop :=
  ∀ x, Asymptotic (impl x) (.some Bound)

end Algorithms.LinearSearch.Complexity
