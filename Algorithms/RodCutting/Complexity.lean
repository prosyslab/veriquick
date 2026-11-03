import VeriQuick.Complexity

/-! # Rod cutting complexity specification -/

open VeriQuick.TimeM
open VeriQuick.Complexity

namespace Algorithms.RodCutting.Complexity

/-- Quadratic in the number of prices, which is also the rod length. -/
def Bound (n : Nat) : Nat := n ^ 2

/-- Quadratic cost in the number of listed prices. -/
def complexity (impl : List Nat → TimeM Nat) : Prop :=
  Asymptotic impl (.some Bound)

end Algorithms.RodCutting.Complexity
