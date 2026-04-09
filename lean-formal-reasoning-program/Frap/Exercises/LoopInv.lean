-- loop invariant exercises

import Frap.LoopInv

namespace Imp
namespace Hoare
open AExp
open BExp
open Com
open CEval
open DCom
open Decorated
attribute [local simp]
  aeval beval aequiv bequiv cequiv update x y z

/-
exercise (3-star): minimum

Program
x = a, y = b, z = 0
while x != 0 && y != 0 do
  x := x - 1
  y := y - 1
  z := z + 1


Fill in decorations for the following program and prove them correct.
```
  { True } ->>
  { 0 + min a b = min a b}
    x := a;
                                { 0 + min x b = min a b }
    y := b;
                                { 0 + min x y = min a b }
    z := 0;
                                { z + min x y = min a b }
    while x != 0 && y != 0 do
                                { z + min x y = min a b ∧ (x ≠ 0 && y ≠ 0) } ->>
                                { (z + 1) + (min x-1 y-1) = min a b }
      x := x - 1
                                { (z + 1) + (min x y-1) = min a b }
      y := y - 1
                                { (z + 1) + min x y = min a b }
      z := z + 1
                                { z + min x y = min a b }
    end
  { z + min x y = min a b ∧ ¬(x ≠ 0 && y ≠ 0) } ->>
  { z = min a b }
```
-/


def minimum_dec (a b : Nat) : Decorated := decorated
  (fun _ => True) $
    dc_pre (fun st => 0 + min a b = min a b) $
    dc_seq (dc_asgn x (a_num a)
      (fun st => 0 + min (st x) b = min a b)) $
    dc_seq (dc_asgn y (a_num b)
      (fun st => 0 + min (st x) (st y) = min a b )) $
    dc_seq (dc_asgn z <{0}>
      (fun st => st z + min (st x) (st y) = min a b )) $
    dc_post (dc_while <{x != 0 && y != 0}>
        (fun st => (st z) + (min (st x) (st y)) = min a b ∧ (st x ≠ 0 && st y ≠ 0) )
        (dc_pre (fun st => (st z + 1) + (min (st x - 1) (st y - 1)) = min a b) $
      dc_seq (dc_asgn x <{x - 1}> (fun st => (st z + 1) + (min (st x) (st y - 1)) = min a b)) $
      dc_seq (dc_asgn y <{y - 1}> (fun st => (st z + 1) + (min (st x) (st y)) = min a b)) $
      dc_asgn z <{z + 1}> (fun st => (st z) + (min (st x) (st y)) = min a b)
      ) (fun st => st z + (min (st x) (st y)) = min a b ∧ ¬(st x ≠ 0 && st y ≠ 0)))
  (fun st => st z = min a b)

theorem minimum_correct a b : outer_triple_valid (minimum_dec a b) := by
  unfold minimum_dec
  verify

/-
exercise (2-star)
Show that the precondition in the rule `hoare_asgn` is in fact the weakest precondition.
-/

theorem hoare_asgn_weakest Q x a
    : is_wp (fun st => Q (st[x ↦ aeval st a])) <{x := <[a]>}> Q := by
  unfold is_wp; constructor
  . apply hoare_consequence_pre
    . apply hoare_asgn
    . verify_assertion
  . intro P' h st hP'
    unfold valid_hoare_triple at h
    apply h
    . assumption
    . constructor
      rfl
