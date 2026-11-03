import VeriQuick.Instrumentation
import Algorithms.RodCutting.Correctness
import Algorithms.RodCutting.Complexity

/-!
Bottom-up rod cutting: `prices[i]` is the price of a piece of length `i + 1`.
The table stores optimal revenues in reverse order: `[R(k), ..., R(0)]`.
-/

open VeriQuick.TimeM
open Algorithms.RodCutting.Correctness
open Algorithms.RodCutting.Complexity

namespace Algorithms.RodCutting.Impl

/-- Maximize the price of the first piece plus its saved remainder revenue. -/
def bestRevenue : List Nat → List Nat → Nat
  | price :: ps, revenue :: rs =>
      max (price + revenue) (bestRevenue ps rs)
  | _, _ => 0

#instrument bestRevenue as bestRevenue_timed

/-- Prepend `steps` optimal revenues to the existing table. -/
def buildTable (prices : List Nat) : Nat → List Nat → List Nat
  | 0, table => table
  | steps + 1, table =>
      buildTable prices steps ((bestRevenue prices table) :: table)

#instrument buildTable as buildTable_timed

/-- Count prices explicitly so instrumentation includes this pass. -/
def countPrices : List Nat → Nat
  | [] => 0
  | _ :: ps => countPrices ps + 1

#instrument countPrices as countPrices_timed

theorem countPrices_eq_length (prices : List Nat) :
    countPrices prices = prices.length := by
  induction prices with
  | nil => rfl
  | cons price prices ih => simp [countPrices, ih]

/-- Compute the optimum for a rod of length `prices.length`. -/
def rodCutting (prices : List Nat) : Nat :=
  match buildTable prices (countPrices prices) [0] with
  | [] => 0
  | revenue :: _ => revenue

#instrument rodCutting as rodCutting_timed

/-- Every paired candidate is bounded by the scan's maximum. -/
theorem le_bestRevenue (prices table : List Nat) (i price revenue : Nat)
    (priceAt : prices[i]? = some price)
    (revenueAt : table[i]? = some revenue) :
    price + revenue ≤ bestRevenue prices table := by
  induction prices generalizing table i with
  | nil => simp at priceAt
  | cons p ps ih =>
    cases table with
    | nil => simp at revenueAt
    | cons r rs =>
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at priceAt revenueAt
        subst price
        subst revenue
        exact Nat.le_max_left (p + r) (bestRevenue ps rs)
      | succ i =>
        simp only [List.getElem?_cons_succ] at priceAt revenueAt
        exact (ih rs i priceAt revenueAt).trans
          (Nat.le_max_right (p + r) (bestRevenue ps rs))

/-- For nonempty inputs, the maximum is attained by a paired candidate. -/
theorem bestRevenue_choice (prices table : List Nat)
    (hasPrices : prices ≠ []) (hasTable : table ≠ []) :
    ∃ i price revenue : Nat, prices[i]? = some price ∧
      table[i]? = some revenue ∧ bestRevenue prices table = price + revenue := by
  induction prices generalizing table with
  | nil => exact False.elim (hasPrices rfl)
  | cons p ps ih =>
    cases table with
    | nil => exact False.elim (hasTable rfl)
    | cons r rs =>
      by_cases headWins : bestRevenue ps rs ≤ p + r
      · exact ⟨0, p, r, rfl, rfl, Nat.max_eq_left headWins⟩
      · have psNe : ps ≠ [] := by
          intro h
          subst h
          simp [bestRevenue] at headWins
        have rsNe : rs ≠ [] := by
          intro h
          subst h
          simp [bestRevenue] at headWins
        obtain ⟨i, price, revenue, priceAt, revenueAt, choice⟩ := ih rs psNe rsNe
        refine ⟨i + 1, price, revenue, ?_, ?_, ?_⟩
        · simpa only [List.getElem?_cons_succ] using priceAt
        · simpa only [List.getElem?_cons_succ] using revenueAt
        · change max (p + r) (bestRevenue ps rs) = price + revenue
          rw [Nat.max_eq_right (Nat.le_of_lt (Nat.not_le.mp headWins)), choice]

/-- Each builder step adds one table entry. -/
theorem buildTable_length (prices : List Nat) (steps : Nat) (table : List Nat) :
    (buildTable prices steps table).length = steps + table.length := by
  induction steps generalizing table with
  | zero => simp [buildTable]
  | succ steps ih =>
    simp only [buildTable, ih, List.length_cons]
    omega

/-- Only zero revenue is obtainable from an empty rod. -/
private theorem empty_revenue (prices : List Nat) (revenue : Nat)
    (plan : Obtainable prices 0 revenue) : revenue = 0 := by
  generalize lenZero : 0 = len at plan
  cases plan with
  | empty => rfl
  | cut => omega

/-- A nonempty cutting plan consists of a first piece and a remainder plan. -/
private theorem plan_split (prices : List Nat) (len total : Nat)
    (plan : Obtainable prices len total) (nonempty : 0 < len) :
    ∃ i price restLen restRevenue : Nat,
      len = i + 1 + restLen ∧ total = price + restRevenue ∧
      prices[i]? = some price ∧ Obtainable prices restLen restRevenue := by
  cases plan with
  | empty => omega
  | @cut i price restLen restRevenue priceAt restPlan =>
    exact ⟨i, price, restLen, restRevenue, rfl, rfl, priceAt, restPlan⟩

/-- The table has `len + 1` entries, with index `i` optimal for length `len - i`.
Thus it stores the answers for lengths `len` down to zero. -/
def TableOptimal (prices : List Nat) (len : Nat) (table : List Nat) : Prop :=
  table.length = len + 1 ∧
    ∀ i revenue : Nat, table[i]? = some revenue → Optimal prices (len - i) revenue

/-- A scan of the optimal table computes the optimum for length `len + 1`. -/
theorem bestRevenue_optimal (prices table : List Nat) (len : Nat)
    (fits : len < prices.length) (invariant : TableOptimal prices len table) :
    Optimal prices (len + 1) (bestRevenue prices table) := by
  obtain ⟨size, optimal⟩ := invariant
  constructor
  · -- The chosen candidate is achievable.
    have hasPrices : prices ≠ [] := by
      intro empty
      simp [empty] at fits
    have hasTable : table ≠ [] := by
      intro empty
      simp [empty] at size
    obtain ⟨i, price, revenue, priceAt, revenueAt, choice⟩ :=
      bestRevenue_choice prices table hasPrices hasTable
    -- The lookup gives `i ≤ len`, so the piece and remainder fill `len + 1`.
    have valid : i < table.length := (List.getElem?_eq_some_iff.mp revenueAt).1
    have piecesFit : i + 1 + (len - i) = len + 1 := by omega
    rw [choice, ← piecesFit]
    exact Obtainable.cut priceAt (optimal i revenue revenueAt).1
  · -- Every cutting plan is bounded by a candidate in the scan.
    intro other otherPlan
    obtain ⟨i, price, restLen, restRevenue, lenSplit, sumEq, priceAt, restPlan⟩ :=
      plan_split prices (len + 1) other otherPlan (by omega)
    have valid : i < table.length := by omega
    have entry : table[i]? = some table[i] := by simp [valid]
    have restLenEq : restLen = len - i := by omega
    rw [restLenEq] at restPlan
    have restBound := (optimal i table[i] entry).2 restRevenue restPlan
    have choiceBound := le_bestRevenue prices table i price table[i] priceAt entry
    calc
      other = price + restRevenue := sumEq
      _ ≤ price + table[i] := Nat.add_le_add_left restBound price
      _ ≤ bestRevenue prices table := choiceBound

/-- Building `steps` entries preserves optimality and advances the solved length. -/
theorem buildTable_optimal (prices : List Nat) (steps : Nat) (table : List Nat) (len : Nat)
    (fits : len + steps ≤ prices.length) (invariant : TableOptimal prices len table) :
    TableOptimal prices (len + steps) (buildTable prices steps table) := by
  induction steps generalizing len table with
  | zero => simpa [buildTable] using invariant
  | succ steps ih =>
    have nextFits : len + 1 + steps ≤ prices.length := by omega
    have newOptimal :
        TableOptimal prices (len + 1) (bestRevenue prices table :: table) := by
      refine ⟨by simp [invariant.1], ?_⟩
      intro i revenue entry
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at entry
        subst revenue
        exact bestRevenue_optimal prices table len (by omega) invariant
      | succ i =>
        -- Shifting both the length and index preserves the remainder length.
        simp only [List.getElem?_cons_succ] at entry
        simpa only [Nat.succ_sub_succ_eq_sub] using invariant.2 i revenue entry
    have result := ih (bestRevenue prices table :: table) (len + 1) nextFits newOptimal
    simpa [buildTable, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using result

theorem rodCutting_correct : Correct rodCutting := by
  intro prices
  have base : TableOptimal prices 0 [0] := by
    refine ⟨rfl, ?_⟩
    intro i revenue entry
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at entry
      subst revenue
      exact ⟨Obtainable.empty, fun other otherPlan => by
        rw [empty_revenue prices other otherPlan]⟩
    | succ i => simp at entry
  have result := buildTable_optimal prices prices.length [0] 0 (by omega) base
  have size := result.1
  cases tableEq : buildTable prices prices.length [0] with
  | nil => simp [tableEq] at size
  | cons revenue rest =>
    have headEq : (buildTable prices prices.length [0])[0]? = some revenue := by
      rw [tableEq]
      rfl
    simpa [rodCutting, countPrices_eq_length, tableEq] using result.2 0 revenue headEq

/-- A scan costs at most four ticks per price plus two ticks to stop. -/
theorem bestRevenue_timed_linear (prices table : List Nat) :
    (bestRevenue_timed prices table).cost ≤ 4 * prices.length + 2 := by
  induction prices generalizing table with
  | nil => simp [bestRevenue_timed, TimeM.cost, TimeM.step, Bind.bind]
  | cons price prices ih =>
    cases table with
    | nil => simp [bestRevenue_timed, TimeM.cost, TimeM.step, Bind.bind]
    | cons revenue table =>
      have restCost := ih table
      simp [bestRevenue_timed, TimeM.cost, TimeM.step, TimeM.seq, Bind.bind]
        at restCost ⊢
      omega

/-- A builder step pays for a scan and three ticks of overhead. -/
theorem buildTable_timed_step (prices : List Nat) (steps : Nat) (table : List Nat) :
    (buildTable_timed prices (steps + 1) table).cost =
      (bestRevenue_timed prices table).cost +
      (buildTable_timed prices steps (bestRevenue prices table :: table)).cost + 3 := by
  simp [buildTable_timed, TimeM.cost, TimeM.step, TimeM.seq, Bind.bind,
    bestRevenue_timed_value]
  omega

/-- Each extension costs at most `4 * prices.length + 5`, with two ticks to stop. -/
theorem buildTable_timed_bound (prices : List Nat) (steps : Nat) (table : List Nat) :
    (buildTable_timed prices steps table).cost ≤
      steps * (4 * prices.length + 5) + 2 := by
  induction steps generalizing table with
  | zero => simp [buildTable_timed, TimeM.cost, TimeM.step, Bind.bind]
  | succ steps ih =>
    rw [buildTable_timed_step, Nat.succ_mul]
    have scanCost := bestRevenue_timed_linear prices table
    have restCost := ih (bestRevenue prices table :: table)
    omega

/-- Counting costs three ticks per price and two ticks to stop. -/
theorem countPrices_timed_cost (prices : List Nat) :
    (countPrices_timed prices).cost = 3 * prices.length + 2 := by
  induction prices with
  | nil => rfl
  | cons price prices ih =>
    simp [countPrices_timed, TimeM.cost, TimeM.step, TimeM.seq, Bind.bind] at ih ⊢
    omega

/-- Counting, initialization, and reading the head add `3 * prices.length + 6` ticks. -/
theorem rodCutting_timed_cost (prices : List Nat) :
    (rodCutting_timed prices).cost =
      (buildTable_timed prices prices.length [0]).cost + 3 * prices.length + 6 := by
  have countCost : (countPrices_timed prices).2 = 3 * prices.length + 2 :=
    countPrices_timed_cost prices
  simp [rodCutting_timed, TimeM.cost, TimeM.step, TimeM.seq, Bind.bind,
    countPrices_timed_value, countPrices_eq_length, buildTable_timed_value, countCost]
  cases buildTable prices prices.length [0] <;> simp <;> omega

/-- The `n` builder steps and wrapper cost at most `4n² + 8n + 8` ticks. -/
theorem rodCutting_timed_bound (prices : List Nat) :
    (rodCutting_timed prices).cost ≤ 4 * prices.length ^ 2 + 8 * prices.length + 8 := by
  rw [rodCutting_timed_cost]
  calc
    (buildTable_timed prices prices.length [0]).cost + 3 * prices.length + 6 ≤
        (prices.length * (4 * prices.length + 5) + 2) + 3 * prices.length + 6 := by
      apply Nat.add_le_add_right
      apply Nat.add_le_add_right
      exact buildTable_timed_bound prices prices.length [0]
    _ = 4 * prices.length ^ 2 + 8 * prices.length + 8 := by ring

/-- For `n ≥ 1`, the bounds `n ≤ n²` and `1 ≤ n²` absorb the lower-order terms. -/
theorem rodCutting_complexity : complexity rodCutting_timed := by
  refine ⟨20, 1, by decide, ?_⟩
  intro prices
  change 1 ≤ prices.length → (rodCutting_timed prices).cost ≤ 20 * prices.length ^ 2
  intro nonempty
  have costBound := rodCutting_timed_bound prices
  have leSquare : prices.length ≤ prices.length ^ 2 := by
    simpa only [pow_two, Nat.mul_one] using
      Nat.mul_le_mul_left prices.length nonempty
  omega

end Algorithms.RodCutting.Impl
