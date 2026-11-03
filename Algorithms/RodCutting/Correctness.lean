import Mathlib

/-!
The price at index `i` is the selling price of a piece of length `i + 1`.
Prices and revenues are natural numbers. The input lists prices for every
length from one to the length of the rod; the empty input describes a rod of
length zero.
-/

namespace Algorithms.RodCutting.Correctness

/-- Revenue obtainable by cutting a rod into positive-length pieces with
listed prices. Each `cut` chooses one piece and a plan for the remainder. -/
inductive Obtainable (prices : List Nat) : Nat → Nat → Prop where
  | empty : Obtainable prices 0 0
  | cut {i price len revenue : Nat} :
      prices[i]? = some price →
      Obtainable prices len revenue →
      Obtainable prices (i + 1 + len) (price + revenue)

/-- The revenue is achievable and bounds every achievable revenue. -/
def Optimal (prices : List Nat) (len revenue : Nat) : Prop :=
  Obtainable prices len revenue ∧
    ∀ other, Obtainable prices len other → other ≤ revenue

/-- Return the optimum for a rod whose length is the number of listed prices. -/
def Correct (impl : List Nat → Nat) : Prop :=
  ∀ prices, Optimal prices prices.length (impl prices)

end Algorithms.RodCutting.Correctness
