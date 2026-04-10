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
{True}
Program:
    if x ≤ 0
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


/-
```
  { True } ->>
  { 0 = n * (n + 1) / 2 - n * (n + 1) / 2 }
    z := 0;
                    { z = n * (n + 1) / 2 - n * (n + 1) / 2 }
    x := n;
                    { z = n * (n + 1) / 2 - x * (x + 1) / 2 }
    while x != 0 do
                    { z = n * (n + 1) / 2 - x * (x + 1) / 2 ∧ (x ≠ 0) } ->>
                    { z = n * (n + 1) / 2 - x * (x + 1) / 2 }
      y := x;
                    { z = n * (n + 1) / 2 - x * (x + 1) / 2 ∧ y = x}

      while y != 0 do
                    { z = n * (n + 1) / 2 - x * (x + 1) / 2 ∧ y = x ∧ (x ≠ 0) ∧ (y ≠ 0) } ->>
                    { z = (n * (n + 1) / 2) - ((x + 1) * x / 2) + (x - y) }
        z := z + 1;
                    { z = (n * (n + 1) / 2) - ((x - 1) * x / 2) + (x - y) + 1 }
        y := y - 1
                    { z = (n * (n + 1) / 2) - ((x - 1) * x / 2) + (x - ( y - 1))}
      end
                    { z = (n * (n + 1) / 2) - ((x - 1) * x / 2) + x ∧ ¬(y ≠ 0) } ->>
                    { z = n * (n + 1) / 2 - (x - 1) * x / 2 }

      x := x - 1
                    { z = n * (n + 1) / 2 - x * (x + 1) / 2 }
    end
  { z = n * (n + 1) / 2 - x * (x + 1) / 2 ∧ ¬(x ≠ 0) } ->>
  { z = n * (n + 1) / 2 }
```

def prog (n : Nat) : Decorated := decorated
  (fun _ => True) $
    dc_pre (fun _ => 0 = n * (n + 1) / 2 - n * (n + 1) / 2) $
    dc_seq (dc_asgn z <{0}>
      (fun st => st z = n * (n + 1) / 2 - n * (n + 1) / 2)) $
    dc_seq (dc_asgn x <{n}>
      (fun st => st z = n * (n + 1) / 2 - st x * (st x + 1) / 2)) $

    dc_post (dc_while <{x != 0}>
        (fun st => st z = n * (n + 1) / 2 - st x * (st x + 1) / 2 ∧ (st x ≠ 0)) (

      dc_pre (fun st => st z = n * (n + 1) / 2 - st x * (st x + 1) / 2) $ -- watch out
      dc_seq (dc_asgn y <{x}>
        (fun st => st z = n * (n + 1) / 2 - st x * (st x + 1) / 2 ∧ st y = st x)) $ -- watch out

      dc_seq (dc_while <{y != 0}> -- watch out inner loop
          (fun st => st z = n * (n + 1) / 2 - st x * (st x + 1) / 2 ∧ (st x ≠ 0) ∧ (st y ≠ 0)) ( -- precon inner loop
        dc_pre (fun st => st z = (n * (n + 1) / 2) - ((st x + 1) * st x / 2) + (st x - st y)) $
        dc_seq (dc_asgn z <{z + 1}>
          (fun st => st z = (n * (n + 1) / 2) - ((st x - 1) * st x / 2) + (st x - st y) + 1)) $
        dc_asgn y <{y - 1}>
          (fun st => st z = (n * (n + 1) / 2) - ((st x - 1) * st x / 2) + (st x - (st y - 1)))
      ) (fun st => st z = n * (n + 1) / 2 - (st x - 1) * st x / 2 ∧ ¬(st y ≠ 0))) $ -- postcon inner loop

      dc_asgn x <{x - 1}>
        (fun st => st z = n * (n + 1) / 2 - st x * (st x + 1) / 2)

    ) (fun st => st z = n * (n + 1) / 2 - st x * (st x + 1) / 2 ∧ ¬(st x ≠ 0)))
  (fun st => st z = n * (n + 1) / 2)

-/
