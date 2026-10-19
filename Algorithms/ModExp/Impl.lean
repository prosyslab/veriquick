import VeriQuick.Instrumentation
import Algorithms.ModExp.Correctness
import Algorithms.ModExp.Complexity

open VeriQuick.TimeM
open VeriQuick.Complexity
open Algorithms.ModExp.Correctness
open Algorithms.ModExp.Complexity

namespace Algorithms.ModExp.Impl

/-- The lowest bit of `exponent`: `1` if `exponent` is odd, `0` otherwise. -/
def lowBit (exponent : Nat) : Nat := exponent % 2

#instrument lowBit as lowBit_timed

/-- Right-to-left square-and-multiply: consume `exponent` one bit at a time,
starting from the lowest, squaring `base` after each bit. -/
def loop (modulus acc base exponent : Nat) : Nat :=
  if _h : exponent = 0 then
    -- Base case: Do modulo because we are relying on Lean's `Nat.mod` arithmetic:
    -- modulus = 1, exponent = 0 => acc % 1 = 0
    acc % modulus
  else if lowBit exponent = 1 then
    -- Lowest bit set: multiply `acc` by `base`, square `base`, drop the bit.
    loop modulus (acc * base % modulus) (base * base % modulus) (exponent / 2)
  else
    -- Lowest bit clear: keep `acc`, square `base`, drop the bit.
    loop modulus acc (base * base % modulus) (exponent / 2)
termination_by exponent

#instrument loop as loop_timed

/-- Modular exponentiation `base ^ exponent % modulus` by the right-to-left
binary method. -/
def modExp (base exponent modulus : Nat) : Nat :=
  loop modulus 1 (base % modulus) exponent

#instrument modExp as modExp_timed

/-- The loop invariant: `loop` returns `acc * base ^ exponent` modulo `modulus`. -/
theorem loop_eq (modulus acc base exponent : Nat) :
    loop modulus acc base exponent = acc * base ^ exponent % modulus := by
  fun_induction loop modulus acc base exponent with
  | case1 acc base =>
    simp only [Nat.pow_zero, Nat.mul_one]
  | case2 acc base exponent h hodd ih =>
    unfold lowBit at hodd
    have hpow : base ^ exponent = base * (base * base) ^ (exponent / 2) := by
      rw [← Nat.pow_two, ← Nat.pow_mul, ← Nat.pow_succ']
      congr 1
      omega
    rw [ih, hpow, Nat.mul_mod, Nat.mod_mod, ← Nat.pow_mod, ← Nat.mul_mod,
      Nat.mul_assoc]
  | case3 acc base exponent h heven ih =>
    unfold lowBit at heven
    have hpow : base ^ exponent = (base * base) ^ (exponent / 2) := by
      rw [← Nat.pow_two, ← Nat.pow_mul]
      congr 1
      omega
    rw [ih, hpow, Nat.mul_mod, ← Nat.pow_mod, ← Nat.mul_mod]

theorem modExp_correct : Correct modExp := by
  intro base exponent modulus
  rw [modExp, loop_eq, Nat.one_mul, ← Nat.pow_mod]

/-- The loop exits in four ticks once the exponent reaches zero. -/
theorem loop_timed_zero (modulus acc base : Nat) :
    (loop_timed modulus acc base 0).cost = 4 := by
  rw [loop_timed_eq_def]
  rfl

/-- An iteration on an odd exponent costs twelve ticks. -/
theorem loop_timed_odd (modulus acc base exponent : Nat) (he : exponent ≠ 0)
    (hodd : lowBit exponent = 1) :
    (loop_timed modulus acc base exponent).cost =
      (loop_timed modulus (acc * base % modulus) (base * base % modulus) (exponent / 2)).cost +
        12 := by
  have hlow : lowBit_timed exponent = (lowBit exponent, 2) := rfl
  rw [loop_timed_eq_def]
  simp +arith only [TimeM.cost, TimeM.step, bind, TimeM.tick, VeriQuick.Instrumentation.WF.seqEq,
    TimeM.done, VeriQuick.Instrumentation.natEq, he, decide_false, Bool.false_eq_true, ↓reduceDIte,
    hlow, hodd, decide_true, Nat.mul_eq, VeriQuick.Instrumentation.WF.fst_certified]
  rfl

/-- An iteration on an even exponent costs ten ticks. -/
theorem loop_timed_even (modulus acc base exponent : Nat) (he : exponent ≠ 0)
    (heven : lowBit exponent ≠ 1) :
    (loop_timed modulus acc base exponent).cost =
      (loop_timed modulus acc (base * base % modulus) (exponent / 2)).cost + 10 := by
  have hlow : lowBit_timed exponent = (lowBit exponent, 2) := rfl
  rw [loop_timed_eq_def]
  simp +arith only [TimeM.cost, TimeM.step, bind, TimeM.tick, VeriQuick.Instrumentation.WF.seqEq,
    TimeM.done, VeriQuick.Instrumentation.natEq, he, decide_false, Bool.false_eq_true, ↓reduceDIte,
    hlow, heven, Nat.mul_eq, VeriQuick.Instrumentation.WF.fst_certified]
  rfl

/-- Each loop iteration costs at most 12 ticks and halves `exponent`, so the
loop runs `Nat.log2 exponent + 1` times for `exponent > 0`. -/
theorem loop_timed_bound (modulus acc base exponent : Nat) :
    (loop_timed modulus acc base exponent).cost ≤ 12 * (Nat.log2 exponent + 1) + 4 := by
  -- Halving either ends the loop or lowers `Nat.log2` by one.
  have hlog (exponent : Nat) :
      exponent / 2 = 0 ∨ Nat.log2 exponent = Nat.log2 (exponent / 2) + 1 := by
    by_cases h2 : 2 ≤ exponent
    · exact .inr (by rw [Nat.log2_def]; simp only [h2, ↓reduceIte])
    · exact .inl (by omega)
  fun_induction loop modulus acc base exponent with
  | case1 acc base =>
    rw [loop_timed_zero]
    omega
  | case2 acc base exponent h hodd ih =>
    rw [loop_timed_odd modulus acc base exponent h hodd]
    rcases hlog exponent with he | he
    · rw [he, loop_timed_zero]
      omega
    · omega
  | case3 acc base exponent h heven ih =>
    rw [loop_timed_even modulus acc base exponent h heven]
    rcases hlog exponent with he | he
    · rw [he, loop_timed_zero]
      omega
    · omega

/-- `modExp` adds two ticks on top of the loop: its own call and reducing the
base. -/
theorem modExp_timed_cost (base exponent modulus : Nat) :
    (modExp_timed base exponent modulus).cost =
      (loop_timed modulus 1 (base % modulus) exponent).cost + 2 := by
  simp only [modExp_timed, TimeM.cost, TimeM.snd_step, TimeM.snd_seq, TimeM.fst_step,
    TimeM.snd_done, TimeM.fst_done, show base.mod modulus = base % modulus from rfl]
  omega

/-- The explicit `O(log exponent)` bound for modular exponentiation. -/
theorem modExp_timed_bound (base exponent modulus : Nat) :
    (modExp_timed base exponent modulus).cost ≤ 12 * (Nat.log2 exponent + 1) + 6 := by
  have h := loop_timed_bound modulus 1 (base % modulus) exponent
  rw [modExp_timed_cost]
  omega

/-- For `exponent ≥ 2`, `Nat.log2 exponent ≥ 1` absorbs the additive constants. -/
theorem modExp_complexity : complexity modExp_timed := by
  refine ⟨30, 2, by decide, ?_⟩
  rintro ⟨base, exponent, modulus⟩
  dsimp only [Size.size, Bound]
  intro he
  have hlog : 1 ≤ Nat.log2 exponent :=
    (Nat.le_log2 (by omega)).2 (by simpa only [Nat.pow_one] using he)
  have h := modExp_timed_bound base exponent modulus
  omega

end Algorithms.ModExp.Impl
