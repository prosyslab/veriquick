import VeriQuick.Complexity

/-! # Binary search complexity specification -/

open VeriQuick.TimeM VeriQuick.Complexity

namespace Algorithms.BinarySearch.Complexity

structure Input where
  values : Array Int
  target : Int

instance : Size Input where
  size input := input.values.size

/-- The additive one includes empty and singleton arrays. -/
def Bound (size : Nat) : Nat := Nat.log2 size + 1

/-- Logarithmic cost in the number of array elements. -/
def complexity (search : Array Int → Int → TimeM (Option Nat)) : Prop :=
  Asymptotic (fun input : Input => search input.values input.target) (.some Bound)

end Algorithms.BinarySearch.Complexity
