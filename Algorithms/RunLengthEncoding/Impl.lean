import VeriQuick.Instrumentation
import Algorithms.RunLengthEncoding.Correctness
import Algorithms.RunLengthEncoding.Complexity

open VeriQuick.TimeM
open VeriQuick.Instrumentation (natEq)
open VeriQuick.Complexity
open Algorithms.RunLengthEncoding.Correctness
open Algorithms.RunLengthEncoding.Complexity

namespace Algorithms.RunLengthEncoding.Impl

/-- Count and drop the leading elements equal to `x`. -/
def takeRun (x : Nat) : List Nat → Nat × List Nat
  | [] => (0, [])
  | y :: ys =>
    if x = y then
      let r := takeRun x ys
      (r.1 + 1, r.2)
    else (0, y :: ys)

/-- `takeRun` splits its input into `count` copies of `x` and the rest. -/
theorem takeRun_length (x : Nat) (xs : List Nat) :
    (takeRun x xs).1 + (takeRun x xs).2.length = xs.length := by
  induction xs with
  | nil => simp [takeRun]
  | cons y ys ih =>
    by_cases h : x = y
    · subst h
      simp only [takeRun, ↓reduceIte, List.length_cons]
      omega
    · simp [takeRun, h]

#instrument takeRun as takeRun_timed

/-- The consumed prefix is exactly `count` copies of `x`. -/
theorem takeRun_append (x : Nat) (xs : List Nat) :
    List.replicate (takeRun x xs).1 x ++ (takeRun x xs).2 = xs := by
  induction xs with
  | nil => simp [takeRun]
  | cons y ys ih =>
    by_cases h : x = y
    · subst h
      simp [takeRun, List.replicate_succ, ih]
    · simp [takeRun, h]

/-- The rest does not start with `x`. -/
theorem takeRun_head (x : Nat) (xs : List Nat) :
    (takeRun x xs).2.head? ≠ some x := by
  induction xs with
  | nil => simp [takeRun]
  | cons y ys ih =>
    by_cases h : x = y
    · subst h
      simpa [takeRun] using ih
    · simp [takeRun, h, Ne.symm h]

/-- Encode consecutive equal values as runs. -/
def encode : List Nat → List Run
  | [] => []
  | x :: xs =>
    match _h : takeRun x xs with
    | (count, rest) => ⟨count + 1, x, Nat.succ_pos count⟩ :: encode rest
termination_by xs => xs.length
decreasing_by
  have hlen := takeRun_length x xs
  rw [_h] at hlen
  simp only [List.length_cons] at hlen ⊢
  omega

#instrument encode as encode_timed

/-- The first run carries the first input value. -/
theorem encode_head (xs : List Nat) :
    (encode xs).head?.map Run.value = xs.head? := by
  cases xs with
  | nil => simp [encode]
  | cons x xs => simp [encode]

/-- The encoder is lossless and never repeats a value in neighboring runs. -/
theorem encode_correct : Correct encode := by
  intro xs
  fun_induction encode xs with
  | case1 => simp [decode, AdjacentDistinct]
  | case2 x xs count rest h ih =>
    rcases ih with ⟨hdecode, hadjacent⟩
    have happend := takeRun_append x xs
    have hhead := takeRun_head x xs
    have hfirst := encode_head rest
    rw [h] at happend hhead
    refine ⟨?_, ?_⟩
    · simp [decode, hdecode, List.replicate_succ, happend]
    · cases hrest : encode rest with
      | nil => trivial
      | cons next runs =>
        rw [hrest] at hadjacent hfirst
        refine ⟨?_, hadjacent⟩
        intro hx
        apply hhead
        simp [← hfirst, ← hx]

/-- Consuming a run of length `count` costs at most `8 * count + 6` ticks. -/
theorem takeRun_timed_linear (x : Nat) (xs : List Nat) :
    (takeRun_timed x xs).cost ≤ 8 * (takeRun x xs).1 + 6 := by
  induction xs with
  | nil =>
    change 4 ≤ 6
    omega
  | cons y ys ih =>
    by_cases h : x = y
    · subst h
      simp [takeRun_timed, takeRun, natEq, cond, TimeM.step, TimeM.seq, Bind.bind] at ih ⊢
      omega
    · simp [takeRun_timed, takeRun, h, natEq, cond, TimeM.step, TimeM.seq, Bind.bind]

/-- One encoding step costs the run scan, the recursive call, and six ticks. -/
theorem encode_timed_step (x : Nat) (xs : List Nat) :
    (encode_timed (x :: xs)).cost ≤
      (takeRun_timed x xs).cost + (encode_timed (takeRun x xs).2).cost + 6 := by
  rw [encode_timed_eq_def]
  have hcert (l : List Nat) : (encode_timed_certified l).1 = encode_timed l := rfl
  simp [VeriQuick.Instrumentation.WF.seqEq, TimeM.step, TimeM.done, TimeM.cost, bind,
    hcert, takeRun_timed_value]
  omega

/-- The instrumented encoder has a linear pointwise cost bound. -/
theorem encode_timed_linear (xs : List Nat) :
    (encode_timed xs).cost ≤ 12 * xs.length + 3 := by
  fun_induction encode xs with
  | case1 =>
    change 3 ≤ 3
    omega
  | case2 x xs count rest h ih =>
    have hstep := encode_timed_step x xs
    have hscan := takeRun_timed_linear x xs
    have hlen := takeRun_length x xs
    rw [h] at hstep hscan hlen
    dsimp only at hstep hscan hlen
    simp only [List.length_cons]
    omega

theorem encode_complexity : complexity encode_timed := by
  refine ⟨12, 0, by decide, ?_⟩
  intro xs
  dsimp [Size.size, Bound]
  intro _
  change (encode_timed xs).cost ≤ 12 * (xs.length + 1)
  have h := encode_timed_linear xs
  omega

end Algorithms.RunLengthEncoding.Impl
