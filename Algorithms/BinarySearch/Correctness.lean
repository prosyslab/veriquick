import Mathlib.Init

/-! # Binary search specification -/

namespace Algorithms.BinarySearch.Correctness

/-- Elements at increasing indices are nondecreasing. -/
def Sorted (values : Array Int) : Prop :=
  ∀ i j, i ≤ j → j < values.size → values.getD i 0 ≤ values.getD j 0

/-- A result contains a valid matching index, or certifies that the target is absent. -/
def ResultCorrect (values : Array Int) (target : Int) (result : Option Nat) : Prop :=
  match result with
  | none => ∀ i, i < values.size → values.getD i 0 ≠ target
  | some i => i < values.size ∧ values.getD i 0 = target

/-- A search returns a correct result on every sorted input. -/
def Correct (search : Array Int → Int → Option Nat) : Prop :=
  ∀ values target, Sorted values → ResultCorrect values target (search values target)

end Algorithms.BinarySearch.Correctness
