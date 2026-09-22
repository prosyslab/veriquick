import VeriQuick.Instrumentation
import Algorithms.LinearSearch.Correctness
import Algorithms.LinearSearch.Complexity

open VeriQuick.TimeM
open VeriQuick.Complexity
open Algorithms.LinearSearch.Correctness
open Algorithms.LinearSearch.Complexity

namespace Algorithms.LinearSearch.Impl

def linearSearch (x : Nat) (xs : List Nat) : Bool :=
  match xs with
  | [] => false
  | hd :: tl =>
    if x = hd then true
    else linearSearch x tl

theorem linearSearch_correct : Correct linearSearch := by
  intro x xs
  induction xs with
  | nil => simp [linearSearch]
  | cons hd tl ih =>
    simp [linearSearch, ih]

#instrument linearSearch as linearSearch_timed

theorem linearSearch_timed_linear (x : Nat) (xs : List Nat) :
    (linearSearch_timed x xs).cost ≤ 4 * xs.length + 3 := by
  fun_induction linearSearch x xs with
  | case1 =>
    change 3 ≤ 3
    omega
  | case2 tl =>
    simp [linearSearch_timed, VeriQuick.Instrumentation.natEq, cond, TimeM.cost,
      TimeM.step, TimeM.tick, TimeM.done, TimeM.seq, Bind.bind]
    omega
  | case3 hd tl h ih =>
    cases htimed : linearSearch_timed x tl with
    | mk value cost =>
      simp [linearSearch_timed, VeriQuick.Instrumentation.natEq, cond, h, htimed,
        TimeM.cost, TimeM.step, TimeM.tick, TimeM.done, TimeM.seq, Bind.bind] at ih ⊢
      omega

theorem linearSearch_complexity : complexity linearSearch_timed := by
  intro x
  refine ⟨4, 0, by decide, ?_⟩
  intro xs
  dsimp [Size.size, Bound]
  intro _
  change (linearSearch_timed x xs).cost ≤ 4 * (xs.length + 1)
  have h := linearSearch_timed_linear x xs
  omega

end Algorithms.LinearSearch.Impl
