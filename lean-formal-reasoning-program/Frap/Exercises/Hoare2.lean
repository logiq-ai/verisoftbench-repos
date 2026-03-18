-- Hoare logic 2 exercises

import Frap.Hoare2

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
exercise (2-star)
Prove the theorem below using `hoare_if`.
-/

theorem if_minus_plus :
    -- { True }
    {* fun _ => True *}
      <{if x <= y then z := y - x else y := x + z end}>
    -- { y = x + z }
    {* fun st => st y = st x + st z *} := by
  apply hoare_if
  . apply hoare_consequence_pre
    . apply hoare_asgn
    . simp
      intro st h
      omega
  . apply hoare_consequence_pre
    . apply hoare_asgn
    . simp
      intro st _
      constructor

/-
exercise (2-star)
Fill in valid decorations for the following program:

```
  { True }
    if x <= y then
                    { True ∧ x ≤ y } ->>
                    { y = x + (y - x) }
      z := y - x
                    { y = x + z }
    else
                    { True ∧ ¬(x ≤ y) } ->>
                    {(x + z) = x + z}
      y := x + z
                    { y = x + z }
    end
  { y = x + z }
```

Briefly justify each use of `->>`.

From hoare_if: {P} if b then c1 else c2 {Q} we can get 2 more information,
1.  Precondition for the if is {P ∧ b} or ({ True ∧ x ≤ y }) then we can perform c1 and the postcondition will be {Q} or {(y = x + z)}.
    After that we subsitute z by y - x in the postcondition. Thus, we will get { y = x + (y - x) } for the hoare assignment part.

2.  Likewise with the first one. Precondition is {P ∧ ¬b} or { True ∧ ¬(x ≤ y) } then we can perform c2 and the postcondition will also be {Q} or {(y = x + z)}.
    Subsequently, we substitute y by x + z in the postcondition. Thus, we will get {(x + z) = x + z} for hoare assignment part.*

-/

/-
exercise (2-star)
Here is a skeleton of the formal decorated version of the `if_minus_plus` program above.
Replace all occurrences of `FILL IN HERE` with appropriate assertions and fill in the proof (which should be just as straightforward as in the examples from lecture).
-/
def if_minus_plus_dec : Decorated := decorated
  (fun _ => True) $
    dc_if <{x <= y}>
      (fun st => True ∧ st x ≤ st y )
      (dc_pre (fun st => st y = st x + (st y - st x) ) $

    dc_asgn z <{y - x}>
      (fun st => st y = st x + st z))

      (fun st => True ∧ ¬(st x ≤ st y))
      (dc_pre (fun st => (st x + st z) =st  x + st z) $

    dc_asgn y <{x + z}>
      (fun st => st y = st x + st z))

  (fun st => st y = st x + st z)

theorem if_minus_plus_correct : outer_triple_valid if_minus_plus_dec := by
  verify

------------------------------------------------------------------------------------------------------------------------

/-
{True}
    if X ≤ 0
      then y := x + 1
      else y := x - 1
    end
{y ≠ x}.
-/

theorem if_add_simple :
    -- { True }
    {* fun _ => True *}
      <{if x <= 0 then y := x + 1 else y := x - 1 end}>
    -- { y ≠ x }
    {* fun st => st y ≠ st x *} := by
  apply hoare_if
  . apply hoare_consequence_pre
    . apply hoare_asgn
    . simp
      intro st h
      omega
  . apply hoare_consequence_pre
    . apply hoare_asgn
    . simp
      intro st h
      omega

/-
Fill in valid decorations for the following program:

```
  { True }
    if x ≤ 0 then
                    { True ∧ x ≤ 0 } ->>
                    { x + 1 ≠ x }
      y := x + 1
                    { y ≠ x }
    else
                    { True ∧ ¬(x ≤ 0) } ->>
                    { x - 1 ≠ x}
      y := x - 1
                    { y ≠ x}
    end
  { y ≠ x }
```
-/

def if_add_simple_dec : Decorated := decorated
  (fun _ => True) $
    dc_if <{x <= 0}>
      (fun st => True ∧ (st x ≤ 0))
      (dc_pre (fun st => st x + 1 ≠ st x) $

    dc_asgn y <{x + 1}>
      (fun st => st y ≠ st x))

      (fun st => True ∧ ¬(st x ≤ 0))
      (dc_pre (fun st => st x - 1 ≠ st x) $

    dc_asgn y <{x - 1}>
      (fun st => st y ≠ st x))
  (fun st => st y ≠ st x)

theorem if_add_simple_correct : outer_triple_valid if_add_simple_dec := by
verify

end Hoare
end Imp
