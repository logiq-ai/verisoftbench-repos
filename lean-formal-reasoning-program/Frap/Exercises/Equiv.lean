import Frap.Equiv

namespace Imp
open Com
open CEval
-- -- enable this if necessary
attribute [local simp]
  aeval beval update lookup_update_eq lookup_update_neq

/-
exercise (2-star)
Prove that adding a `skip` after a command results in an equivalent program.
-/

theorem skip_right c : cequiv <{ <[c]>; skip }> c := by
  intro st st'
  constructor
  . intro h
    cases h with
    | e_seq _ _ st₁' st₁'' st₁''' hc₁ hc₂ => cases hc₂; assumption
  . intro h
    constructor
    . assumption
    . constructor

/-
exercise (2-star)
Prove that if `b` is equivalent to `False`, then `if b then c₁ else c₂` is equivalent to `c₂`.
-/

theorem if_false b c₁ c₂
    : bequiv b <{false}> → cequiv <{if <[b]> then <[c₁]> else <[c₂]> end}> c₂ := by
  intros hb st st'
  unfold bequiv at hb; specialize hb st; simp at hb
  constructor
  . intro h
    cases h with
    | e_ifTrue _ _ _ _ _ hbt hc₁ => simp [*] at *
    | e_ifFalse _ _ _ _ _ hbf hc₂ => assumption
  . intro h
    apply CEval.e_ifFalse
    . assumption
    . assumption

/-
exercise (3-star)
Consider the following predicate.
This predicate yields `true` just on programs that have no while loops.
-/

def no_whiles (c : Com) : Bool :=
  match c with
  | c_skip => true
  | c_asgn _ _ => true
  | c_seq c₁ c₂ => and (no_whiles c₁) (no_whiles c₂)
  | c_if _ c₁ c₂ => and (no_whiles c₁) (no_whiles c₂)
  | c_while _ _ => false

/-
Using `inductive`, write a property `No_whilesR` such that `No_whilesR c` is provable exactly when `c` is a program with no while loops.
-/

inductive No_whilesR : Com → Prop :=
  /- **fill in here** -/
  | nw_skip  : No_whilesR Com.c_skip
  | nw_asgn  : ∀ (x : String) (e : AExp), No_whilesR (c_asgn x e)
  | nw_seq   : ∀ (c1 c2 : Com), No_whilesR c1 → No_whilesR c2 → No_whilesR (c_seq c1 c2)
  | nw_if    : ∀ (b : BExp) (c1 c2 : Com), No_whilesR c1 → No_whilesR c2 → No_whilesR (c_if b c1 c2)
  | nw_while : ∀ (b : BExp) (c : Com), false → No_whilesR (c_while b c)

/-
Then, prove its equivalence with `no_whiles`.
-/

theorem no_whiles_eqv c : no_whiles c = true ↔ No_whilesR c := by
  constructor
  . intro h
    induction c
    case c_skip => constructor
    case c_asgn => constructor
    case c_seq c₁ c₂ ih₁ ih₂ =>
      simp [no_whiles] at h
      simp [*] at *
      apply No_whilesR.nw_seq <;> assumption
    case c_if b c₁ c₂ ih₁ ih₂ =>
      simp [no_whiles] at h
      simp [*] at *
      apply No_whilesR.nw_if <;> assumption
    case c_while b c _ =>
      simp [no_whiles] at h
  . intro h
    induction h
    case nw_skip => simp [no_whiles]
    case nw_asgn => simp [no_whiles]
    case nw_seq c₁ c₂ c₁' c₂' ih₁ ih₂ =>
      simp [no_whiles] at *
      constructor <;> assumption
    case nw_if b c₁ c₂ c₁' c₂' ih₁ ih₂ =>
      simp [no_whiles] at *
      constructor <;> assumption
    case nw_while b c =>
      simp [no_whiles]
      contradiction
