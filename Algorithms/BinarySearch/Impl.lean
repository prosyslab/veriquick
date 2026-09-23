import Mathlib.Data.Nat.Log
import VeriQuick.Instrumentation
import Algorithms.BinarySearch.Correctness
import Algorithms.BinarySearch.Complexity

/-!
Lower-bound binary search over the half-open interval `[lo, hi)`, with its correctness
proof and an `O(log n)` tick bound.
-/

open VeriQuick.TimeM
open VeriQuick.Complexity
open Algorithms.BinarySearch.Correctness
open Algorithms.BinarySearch.Complexity

namespace Algorithms.BinarySearch.Impl

-- `midpoint`, `active` and `nextBounds` are separate so that `#instrument` succeeds.
-- Written in place, the value proof gets stuck on `Nat.div` vs `/` and on branch
-- conditions inside `loop`. `@[inline]` keeps the compiled code free of the extra calls.

@[inline] def midpoint (lo hi : Nat) : Nat := lo + (hi - lo) / 2

#instrument midpoint as midpoint_timed

@[inline] def active (lo hi : Nat) : Bool := Nat.ble (lo + 1) hi

#instrument active as active_timed

theorem active_eq_true (lo hi : Nat) : active lo hi = true ↔ lo < hi := by
  simp only [active, Nat.ble_eq]
  omega

-- Out of bounds, `getD` returns `key`, which is not `< key`.
@[inline] def nextBounds (a : Array Nat) (key lo hi : Nat) : Nat × Nat :=
  if a.getD (midpoint lo hi) key < key then (midpoint lo hi + 1, hi)
  else (lo, midpoint lo hi)

#instrument nextBounds as nextBounds_timed

theorem nextBounds_halves (a : Array Nat) (key lo hi : Nat) (hlt : lo < hi) :
    2 * ((nextBounds a key lo hi).2 - (nextBounds a key lo hi).1) ≤ hi - lo := by
  unfold nextBounds
  split <;> simp only [midpoint] <;> omega

def loop (a : Array Nat) (key lo hi : Nat) : Nat :=
  if _h : active lo hi then
    match _hb : nextBounds a key lo hi with
    | (lo', hi') => loop a key lo' hi'
  else lo
termination_by hi - lo
decreasing_by
  have hlt := (active_eq_true lo hi).1 _h
  have := nextBounds_halves a key lo hi hlt
  rw [_hb] at this
  omega

#instrument loop as loop_timed

def lowerBound (key : Nat) (a : Array Nat) : Nat :=
  loop a key 0 a.size

#instrument lowerBound as lowerBound_timed

-- Everything before `lo` is `< key`, everything from `hi` on is `≥ key`.
def Inv (a : Array Nat) (key lo hi : Nat) : Prop :=
  lo ≤ hi ∧ hi ≤ a.size ∧
    (∀ i (h : i < a.size), i < lo → a[i] < key) ∧
    (∀ i (h : i < a.size), hi ≤ i → key ≤ a[i])

theorem sorted_le {a : Array Nat} (hs : Sorted a) {i j : Nat} (hij : i ≤ j)
    (hj : j < a.size) : a[i] ≤ a[j] := by
  obtain h | rfl := Nat.lt_or_eq_of_le hij
  exacts [hs i j h hj, Nat.le_refl _]

theorem nextBounds_eq (a : Array Nat) (key lo hi : Nat) (h : midpoint lo hi < a.size) :
    nextBounds a key lo hi =
      if a[midpoint lo hi] < key then (midpoint lo hi + 1, hi)
      else (lo, midpoint lo hi) := by
  simp only [nextBounds, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h,
    Option.getD_some]

theorem nextBounds_inv {a : Array Nat} {key lo hi : Nat} (hs : Sorted a)
    (h : Inv a key lo hi) (hlt : lo < hi) :
    Inv a key (nextBounds a key lo hi).1 (nextBounds a key lo hi).2 := by
  obtain ⟨_, hhi, hbelow, habove⟩ := h
  have hm : midpoint lo hi < a.size := by unfold midpoint; omega
  rw [nextBounds_eq a key lo hi hm]
  split <;> dsimp only
  · refine ⟨by unfold midpoint; omega, hhi, fun i hi hlt' => ?_, habove⟩
    exact Nat.lt_of_le_of_lt (sorted_le hs (by omega) hm) ‹_›
  · refine ⟨by unfold midpoint; omega, by omega, hbelow, fun i hi hle => ?_⟩
    exact Nat.le_trans (by omega) (sorted_le hs hle hi)

theorem loop_inv (a : Array Nat) (key lo hi : Nat) (hs : Sorted a)
    (h : Inv a key lo hi) :
    Inv a key (loop a key lo hi) (loop a key lo hi) := by
  fun_induction loop a key lo hi with
  | case1 lo hi hact lo' hi' hb ih =>
    rw [active_eq_true] at hact
    have := nextBounds_inv hs h hact
    rw [hb] at this
    exact ih this
  | case2 lo hi hact =>
    rw [active_eq_true] at hact
    obtain rfl : hi = lo := by have := h.1; omega
    exact h

theorem lowerBound_correct : Correct lowerBound := by
  intro key a hs
  have hinit : Inv a key 0 a.size :=
    ⟨Nat.zero_le _, Nat.le_refl _, fun _ _ _ => by omega, fun _ _ _ => by omega⟩
  obtain ⟨_, hsize, hbelow, habove⟩ := loop_inv a key 0 a.size hs hinit
  refine ⟨hsize, fun i hi => ⟨hbelow i hi, fun hv => ?_⟩⟩
  exact Nat.lt_of_not_le fun hle => Nat.not_lt_of_le (habove i hi hle) hv

theorem midpoint_timed_cost (lo hi : Nat) : (midpoint_timed lo hi).2 = 4 := rfl

theorem active_timed_cost (lo hi : Nat) : (active_timed lo hi).2 = 3 := rfl

theorem nextBounds_cost (a : Array Nat) (key lo hi : Nat) :
    (nextBounds_timed a key lo hi).cost ≤ 16 := by
  simp only [nextBounds_timed, TimeM.cost, TimeM.snd_step, TimeM.snd_seq, TimeM.fst_seq,
    midpoint_timed_value, midpoint_timed_cost, TimeM.fst_step, TimeM.fst_done, TimeM.snd_done]
  cases VeriQuick.Instrumentation.natLt _ key <;>
    simp only [TimeM.snd_step, TimeM.snd_seq, TimeM.snd_done, Bool.cond_true, Bool.cond_false,
      midpoint_timed_cost] <;> omega

theorem loop_cost_stop (a : Array Nat) (key lo hi : Nat) (h : active lo hi = false) :
    (loop_timed a key lo hi).cost = 5 := by
  rw [loop_timed_eq_def]
  simp only [TimeM.cost, TimeM.snd_step, VeriQuick.Instrumentation.WF.snd_seqEq,
    active_timed_value, h, active_timed_cost, Bool.false_eq_true, dite_false, TimeM.snd_done]

theorem loop_cost_step (a : Array Nat) (key lo hi : Nat) (h : active lo hi = true) :
    (loop_timed a key lo hi).cost ≤
      22 + (loop_timed a key (nextBounds a key lo hi).1 (nextBounds a key lo hi).2).cost := by
  rw [loop_timed_eq_def]
  simp only [TimeM.cost, TimeM.snd_step, VeriQuick.Instrumentation.WF.snd_seqEq,
    active_timed_value, h, active_timed_cost, dite_true]
  have hnext := nextBounds_cost a key lo hi
  have hval := nextBounds_timed_value a key lo hi
  generalize nextBounds_timed a key lo hi = r at hnext hval ⊢
  obtain ⟨⟨lo', hi'⟩, c⟩ := r
  rw [← (hval : (lo', hi') = nextBounds a key lo hi)]
  change 3 + (c + ((loop_timed a key lo' hi').2 + 1) + 1) + 1 ≤ 22 + (loop_timed a key lo' hi').2
  simp only [TimeM.cost] at hnext
  omega

theorem loop_cost (a : Array Nat) (key k : Nat) :
    ∀ lo hi, hi - lo < 2 ^ k → (loop_timed a key lo hi).cost ≤ 22 * k + 5 := by
  induction k with
  | zero =>
    intro lo hi hlen
    have h : active lo hi = false := by
      rw [← Bool.not_eq_true, active_eq_true]
      omega
    rw [loop_cost_stop a key lo hi h]
  | succ k ih =>
    intro lo hi hlen
    cases h : active lo hi with
    | false =>
      rw [loop_cost_stop a key lo hi h]
      omega
    | true =>
      have hhalf := nextBounds_halves a key lo hi ((active_eq_true lo hi).1 h)
      have := ih (nextBounds a key lo hi).1 (nextBounds a key lo hi).2
        (by rw [Nat.pow_succ] at hlen; omega)
      have := loop_cost_step a key lo hi h
      omega

theorem lowerBound_cost (key : Nat) (a : Array Nat) :
    (lowerBound_timed key a).cost ≤ 22 * Bound a.size + 7 := by
  have h := loop_cost a key (Nat.log2 a.size + 1) 0 a.size
    (by simpa only [Nat.sub_zero] using Nat.lt_log2_self (n := a.size))
  simp only [lowerBound_timed, Bound, TimeM.cost, TimeM.snd_step, TimeM.snd_seq, TimeM.fst_step,
    TimeM.fst_done, TimeM.snd_done] at h ⊢
  omega

theorem lowerBound_complexity : complexity lowerBound_timed := by
  intro key
  refine ⟨29, 0, by omega, fun a _ => ?_⟩
  have h := lowerBound_cost key a
  have : 1 ≤ Bound a.size := Nat.le_add_left 1 _
  change (lowerBound_timed key a).cost ≤ 29 * Bound a.size
  omega

end Algorithms.BinarySearch.Impl
