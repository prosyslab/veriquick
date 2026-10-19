import VeriQuick.Complexity

open VeriQuick.TimeM
open VeriQuick.Complexity

namespace Algorithms.ModExp.Complexity

structure Input where
  base : Nat
  exponent : Nat
  modulus : Nat

instance : Size Input where
  size x := x.exponent

/-- Logarithmic bound in the exponent. -/
def Bound (n : Nat) : Nat := Nat.log2 n

/-- Instrumented modular exponentiation is `O(log exponent)`. -/
def complexity (impl : Nat → Nat → Nat → TimeM Nat) : Prop :=
  Asymptotic (fun (x : Input) => impl x.base x.exponent x.modulus) (.some Bound)

end Algorithms.ModExp.Complexity
