import Mathlib
import VeriQuick.Instrumentation
import Algorithms.BinarySearch.Correctness
import Algorithms.BinarySearch.Complexity

/-! # Array binary search -/

open VeriQuick.TimeM
open Algorithms.BinarySearch.Correctness

namespace Algorithms.BinarySearch.Impl

/-- Compare the target and midpoint value in one place. -/
def compareInt (left right : Int) : Ordering :=
  if left < right then .lt else if right < left then .gt else .eq
#instrument compareInt as compareInt_timed

/-- The midpoint of the half-open interval `[low, high)`. -/
def midpoint (low high : Nat) : Nat := low + (high - low) / 2
#instrument midpoint as midpoint_timed

/-- Keep the interval test Boolean so the instrumentation can reuse its value
certificate without comparing dependent termination conditions. -/
def intervalEmpty (low high : Nat) : Bool := Nat.ble high low
#instrument intervalEmpty as intervalEmpty_timed

/-- Search `[low, high)`, recursing only on strictly smaller intervals. -/
def search (values : Array Int) (target : Int) (low high : Nat) : Option Nat :=
  if intervalEmpty low high then none
  else
    let middle := midpoint low high
    match compareInt target (values.getD middle 0) with
    | .lt => search values target low middle
    | .eq => some middle
    | .gt => search values target (middle + 1) high
termination_by high - low
decreasing_by
  · simp_all [intervalEmpty, midpoint]
    omega
  · simp_all [intervalEmpty, midpoint]
    omega

#instrument search as search_timed

/-- Start with the full half-open interval `[0, values.size)`. -/
def binarySearch (values : Array Int) (target : Int) : Option Nat :=
  search values target 0 values.size

#instrument binarySearch as binarySearch_timed

/-- Every occurrence of the target remains inside the current interval. -/
private def Candidates (values : Array Int) (target : Int) (low high : Nat) : Prop :=
  ∀ index, index < values.size → values.getD index 0 = target → low ≤ index ∧ index < high

private theorem compareInt_spec (left right : Int) :
    match compareInt left right with
    | .lt => left < right
    | .eq => left = right
    | .gt => right < left := by
  unfold Algorithms.BinarySearch.Impl.compareInt
  by_cases leftLess : left < right
  · simp [leftLess]
  · by_cases rightLess : right < left
    · simp [leftLess, rightLess]
    · simp [leftLess, rightLess]
      omega

/-- A nonempty interval's midpoint is within the interval. -/
private theorem midpoint_valid {low high : Nat} {values : Array Int}
    (nonempty : low < high)
    (bound : high ≤ values.size) : midpoint low high < values.size := by
  unfold Algorithms.BinarySearch.Impl.midpoint
  omega

/-- A smaller target keeps every possible match to the left of `middle`. -/
private theorem candidates_left {values : Array Int} {target : Int}
    {low high middle : Nat} (sorted : Sorted values)
    (candidates : Candidates values target low high)
    (order : target < values.getD middle 0) : Candidates values target low middle := by
  intro index valid found
  have interval := candidates index valid found
  constructor
  · exact interval.1
  · by_cases before : index < middle
    · exact before
    · have after : middle ≤ index := by omega
      have monotone := sorted middle index after valid
      rw [found] at monotone
      omega

/-- A larger target keeps every possible match to the right of `middle`. -/
private theorem candidates_right {values : Array Int} {target : Int}
    {low high middle : Nat} (sorted : Sorted values)
    (candidates : Candidates values target low high) (middleValid : middle < values.size)
    (order : values.getD middle 0 < target) :
    Candidates values target (middle + 1) high := by
  intro index valid found
  have interval := candidates index valid found
  constructor
  · by_cases after : middle + 1 ≤ index
    · exact after
    · have before : index ≤ middle := by omega
      have monotone := sorted index middle before middleValid
      rw [found] at monotone
      omega
  · exact interval.2

/-- If all possible matches lie in an empty interval, the target is absent. -/
private theorem candidates_empty {values : Array Int} {target : Int} {low high : Nat}
    (candidates : Candidates values target low high) (empty : high ≤ low) :
    ∀ index, index < values.size → values.getD index 0 ≠ target := by
  intro index valid found
  have interval := candidates index valid found
  omega

/-- The interval contains every possible match and stays within the array. -/
private theorem search_correct (values : Array Int) (target : Int) (low high : Nat)
    (sorted : Sorted values) : high ≤ values.size → Candidates values target low high →
    ResultCorrect values target (search values target low high) := by
  fun_induction search values target low high with
  | case1 low high empty =>
      intro bound candidates
      have intervalEmpty : high ≤ low := by simpa [intervalEmpty] using empty
      exact candidates_empty candidates intervalEmpty
  | case2 low high notEmpty middle comparison ih =>
      intro bound candidates
      have nonempty : low < high := by simpa [intervalEmpty] using notEmpty
      have order := compareInt_spec target (values.getD (midpoint low high) 0)
      rw [comparison] at order
      have middleValid := Nat.le_of_lt (midpoint_valid nonempty bound)
      have nextCandidates := candidates_left sorted candidates order
      exact ih middleValid nextCandidates
  | case3 low high notEmpty middle comparison =>
      intro bound candidates
      have nonempty : low < high := by simpa [intervalEmpty] using notEmpty
      have order := compareInt_spec target (values.getD (midpoint low high) 0)
      rw [comparison] at order
      constructor
      · exact midpoint_valid nonempty bound
      · exact order.symm
  | case4 low high notEmpty middle comparison ih =>
      intro bound candidates
      have nonempty : low < high := by simpa [intervalEmpty] using notEmpty
      have order := compareInt_spec target (values.getD (midpoint low high) 0)
      rw [comparison] at order
      have middleValid := midpoint_valid nonempty bound
      have nextCandidates := candidates_right sorted candidates middleValid order
      exact ih bound nextCandidates

/-- Sorted arrays are searched completely, including duplicates and empty inputs. -/
theorem binarySearch_correct : Correct binarySearch := by
  intro values target sorted
  apply search_correct values target 0 values.size sorted
  · simp
  · intro index valid found
    constructor
    · omega
    · exact valid

/-- Computing the midpoint costs four ticks. -/
private theorem midpoint_timed_cost (low high : Nat) :
    (midpoint_timed low high).cost = 4 := by
  simp [midpoint_timed]

/-- Comparing two integers costs at most six ticks. -/
private theorem compareInt_timed_cost (left right : Int) :
    (compareInt_timed left right).cost ≤ 6 := by
  unfold compareInt_timed VeriQuick.Instrumentation.intLt
  by_cases leftLess : left < right
  · simp [leftLess]
  · by_cases rightLess : right < left
    · simp [leftLess, rightLess]
    · simp [leftLess, rightLess]

/-- An empty search costs at most five ticks. -/
private theorem search_empty (values : Array Int) (target : Int) (low high : Nat)
    (empty : high ≤ low) : (search_timed values target low high).cost ≤ 5 := by
  have emptyTest : Nat.ble high low = true := by simpa using empty
  rw [search_timed_eq_def]
  unfold VeriQuick.Instrumentation.WF.seqEq
  simp [intervalEmpty_timed, emptyTest]

/-- Expand one instrumented call and account for its constant work. -/
private theorem search_step_timed (values : Array Int) (target : Int) (low high bound : Nat)
    (leftCost : (search_timed values target low (midpoint_timed low high).value).cost ≤ bound)
    (rightCost :
      (search_timed values target ((midpoint_timed low high).value + 1) high).cost ≤ bound) :
    (search_timed values target low high).cost ≤ bound + 30 := by
  have emptyCost : (intervalEmpty_timed low high).cost = 2 := by
    simp [intervalEmpty_timed]
  have middleCost := midpoint_timed_cost low high
  have comparisonCost := compareInt_timed_cost target
    (values.getD (midpoint_timed low high).1 (Int.ofNat 0))
  unfold search_timed at leftCost rightCost
  simp only [TimeM.cost] at emptyCost middleCost comparisonCost
  simp only [TimeM.cost, TimeM.value] at leftCost rightCost
  simp at comparisonCost
  rw [search_timed_eq_def]
  unfold VeriQuick.Instrumentation.WF.seqEq TimeM.done
  simp only [TimeM.snd_step_prod, TimeM.fst_step_prod]
  cases condition : (intervalEmpty_timed low high).1
  · cases comparison :
      (compareInt_timed target (values.getD (midpoint_timed low high).1 (Int.ofNat 0))).1
    · simp
      omega
    · simp
      omega
    · simp
      omega
  · simp
    omega

/-- If each possible next interval costs at most `bound`, this call costs at most
`bound + 30`. The hypotheses use the ordinary midpoint. -/
private theorem search_step (values : Array Int) (target : Int) (low high bound : Nat)
    (leftCost : (search_timed values target low (midpoint low high)).cost ≤ bound)
    (rightCost : (search_timed values target (midpoint low high + 1) high).cost ≤ bound) :
    (search_timed values target low high).cost ≤ bound + 30 := by
  exact search_step_timed values target low high bound leftCost rightCost

/-- Both next intervals fit under the previous power-of-two width bound. -/
private theorem midpoint_halves_pow {low high levels : Nat}
    (width : high - low < 2 ^ (levels + 1)) :
    midpoint low high - low < 2 ^ levels ∧
      high - (midpoint low high + 1) < 2 ^ levels := by
  have half : (high - low) / 2 < 2 ^ levels := by
    have twoPositive : 0 < (2 : Nat) := by decide
    rw [Nat.div_lt_iff_lt_mul twoPositive]
    simpa [Nat.pow_succ, Nat.mul_comm] using width
  unfold Algorithms.BinarySearch.Impl.midpoint
  omega

/-- An interval shorter than `2^levels` takes at most `levels` comparisons.
`levels` is only a proof variable; it is not an argument to the algorithm. -/
private theorem search_cost_lt_pow (values : Array Int) (target : Int) (levels : Nat) :
    ∀ low high, high - low < 2 ^ levels →
      (search_timed values target low high).cost ≤ 30 * levels + 5 := by
  induction levels with
  | zero =>
      intro low high width
      simp at width
      have intervalEmpty : high ≤ low := by omega
      exact search_empty values target low high intervalEmpty
  | succ levels ih =>
      intro low high width
      have halves := midpoint_halves_pow width
      have leftCost := ih low (midpoint low high) halves.1
      have rightCost := ih (midpoint low high + 1) high halves.2
      have stepCost := search_step values target low high (30 * levels + 5)
        leftCost rightCost
      omega

/-- The outer entry point adds two ticks to the interval search. -/
private theorem binarySearch_timed_cost_eq (values : Array Int) (target : Int) :
    (binarySearch_timed values target).cost =
      (search_timed values target 0 values.size).cost + 2 := by
  unfold binarySearch_timed
  simp
  omega

/-- The full instrumented algorithm has logarithmic cost. -/
theorem binarySearch_timed_cost (values : Array Int) (target : Int) :
    (binarySearch_timed values target).cost ≤ 30 * (Nat.log2 values.size + 1) + 7 := by
  rw [binarySearch_timed_cost_eq]
  have width : values.size - 0 < 2 ^ (Nat.log2 values.size + 1) := by
    simp only [Nat.sub_zero]
    exact Nat.lt_log2_self
  have bound := search_cost_lt_pow values target (Nat.log2 values.size + 1)
    0 values.size width
  omega

theorem binarySearch_timed_isLogarithmic :
    Algorithms.BinarySearch.Complexity.complexity binarySearch_timed := by
  exists 37, 0
  constructor
  · decide
  · intro input size _
    have bound := binarySearch_timed_cost input.values input.target
    unfold Algorithms.BinarySearch.Complexity.Bound
    simp only [size, VeriQuick.Complexity.Size.size]
    omega

end Algorithms.BinarySearch.Impl
