namespace Algorithms.LinearSearch.Correctness

def Correct (impl : Nat → List Nat → Bool) : Prop :=
  ∀ x xs, impl x xs = true ↔ x ∈ xs

end Algorithms.LinearSearch.Correctness
