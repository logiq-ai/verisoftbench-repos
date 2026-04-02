/-
# Small-step operational semantics

The evaluators we have seen so far (for `AExps`, `BExps`, commands, ...) have been formulated in a "big-step" style: they specify how a given expression can be evaluated to its final value (or a how command plus a store can be evaluated to a final store) "all in one big step."

This style is simple and natural for many purposes.
Indeed, Gilles Kahn, who popularized it, called it _natural semantics_.
But there are some things it does not do well.
In particular, it does not give us a convenient way of talking about _concurrent_ programming languages, where the semantics of a program—i.e., the essence of how it behaves—is not just which input states get mapped to which output states, but also includes the intermediate states that it passes through along the way; this is crucial, since these states can also be observed by concurrently executing code.

Another shortcoming of the big-step style is more technical but equally critical in many situations.

Suppose we want to define a variant of Imp where variables could hold _either_ numbers or lists of numbers.
In the syntax of this extended language, it will be possible to write strange expressions like `2 + nil`, and our semantics for arithmetic expressions will then need to say something about how such expressions behave.
One possibility is to maintain the convention that every arithmetic expression evaluates to some number by choosing some way of viewing a list as a number, e.g., by specifying that a list should be interpreted as `0` when it occurs in a context expecting a number. But this would be a bit of a hack.

A much more natural approach is simply to say that the behavior of the expression `2 + nil` is undefined, i.e., it doesn't evaluate to any result at all.
And we can easily do this: we just have to formulate `aeval` and `beval` as `inductive` propositions rather than `def`s, so that we can make them partial functions instead of total ones.

Now, however, we encounter a serious deficiency.
In this language, a command might fail to map a given starting state to any ending state for _two quite different reasons_: either because the execution gets into an infinite loop or because, at some point, the program tries to do an operation that makes no sense, such as adding a number to a list, so that none of the evaluation rules can be applied.

These two outcomes—nontermination vs. getting stuck in an erroneous configuration—should not be confused.
In particular, we want to _allow_ the first (because permitting the possibility of infinite loops is the price we pay for the convenience of programming with general looping constructs like `while`) but _prevent_ the second (which is just wrong), for example by adding some form of _typechecking_ to the language.
Indeed, this will be a major topic in the rest of the course.
As a first step, we need a way of presenting the semantics that allows us to distinguish nontermination from erroneous "stuck states."

So, for lots of reasons, we'd like to have a finer-grained way of defining and reasoning about program behaviors.
This is the topic of the present chapter.
Our goal is to replace the "big-step" `eval` relation with a "small-step" relation that specifies, for a given program, how its atomic steps of computation are performed.

## A toy language

To save space in the discussion, let's go back to an incredibly simple language containing just constants and addition.
(We use single letters—`c` and `p` (for constant and plus)—as constructor names, for brevity.)
Later on, we'll see how to apply the same techniques to the full Imp language.
-/

inductive Tm : Type :=
  | c : Nat → Tm      /- constant -/
  | p : Tm → Tm → Tm  /- plus -/

open Tm

/-
Here is a standard evaluator for this language, written in the big-step style that we've been using up to this point.
-/

def evalF (t : Tm) : Nat :=
  match t with
  | c n => n
  | p t1 t2 => evalF t1 + evalF t2

/-
Here is the same evaluator, written in exactly the same style, but formulated as an inductively defined relation.
We use the notation `t ==> n` for "t evaluates to n."
-/

inductive Eval : Tm → Nat → Prop :=
  | e_const n : Eval (c n) n
  | e_plus t₁ t₂ n₁ n₂ : Eval t₁ n₁ → Eval t₂ n₂ → Eval (p t₁ t₂) (n₁ + n₂)

open Eval

syntax term "==>" term : term
macro_rules
  | `(term|$t:term ==> $n:term) => `(Eval $t $n)

namespace SimpleArith1

/-
Now, here is the corresponding _small-step_ evaluation relation.
-/

inductive Step : Tm → Tm → Prop :=
  | st_plusConstConst n₁ n₂ : Step (p (c n₁) (c n₂)) (c (n₁ + n₂))
  | st_plus1 t₁ t₁' t₂ : Step t₁ t₁' → Step (p t₁ t₂) (p t₁' t₂)
  | st_plus2 n₁ t₂ t₂' : Step t₂ t₂' → Step (p (c n₁) t₂) (p (c n₁) t₂')

open Step

syntax term "~~>" term : term
macro_rules
  | `(term|$t₁:term ~~> $t₂:term) => `(Step $t₁ $t₂)

/-
Things to notice:
* We are defining a single reduction step, in which just one `p` node is replaced by its value.
* Each step finds the _leftmost_ `p` node that is ready to go (both of its operands are constants) and rewrites it in place.
  The first rule tells how to rewrite this `p` node itself; the other two rules tell how to find it.
* A term that is just a constant cannot take a step.

Let's pause and check a couple of examples of reasoning with the `Step` relation...

If `t₁` can take a step to `t₁'`, then `p t₁ t₂` steps to `p t₁' t₂`:
-/

example :
    p
      (p (c 1) (c 3))
      (p (c 2) (c 4))
    ~~>
    p
      (c 4)
      (p (c 2) (c 4)) := by
  apply st_plus1
  apply st_plusConstConst

/-
exercise (1-star)
Right-hand sides of sums can take a step only when the left-hand side is finished: if `t₂` can take a step to `t₂'`, then `p (c n) t₂` steps to `p (c n) t₂'`:
-/

example :
    p
      (c 0)
      (p
        (c 2)
        (p (c 1) (c 3)))
    ~~>
    p
      (c 0)
      (p
        (c 2)
        (c 4)) := by
  apply st_plus2
  apply st_plus2
  apply st_plusConstConst

end SimpleArith1

/-
### Determinism of evaluation

One simple property of the `~~>` relation is that, like the big-step evaluation relation for Imp, it is _deterministic_.
-/

def relation (X : Type) := X → X → Prop

def deterministic {X : Type} (R : relation X) :=
  ∀ x y₁ y₂, R x y₁ → R x y₂ → y₁ = y₂

/-
_Theorem_:
For each `t`, there is at most one `t'` such that `t` steps to `t'` (`t ~~> t'` is provable).

_Proof sketch_:
We show that if `x` steps to both `y₁` and `y₂`, then `y₁` and `y₂` are equal, by induction on a derivation of `Step x y₁`.
There are several cases to consider, depending on the last rule used in this derivation and the last rule in the given derivation of `Step x y₂`.
* If both are `st_plusConstConst`, the result is immediate.
* The cases when both derivations end with `st_plus1` or `st_plus2` follow by the induction hypothesis.
* It cannot happen that one is `st_plusConstConst` and the other is `st_plus1` or `st_plus2`, since this would imply that `x` has the form `p t₁ t₂` where both `t₁` and `t₂` are constants (by `st_plusConstConst`) and one of `t₁` or `t₂` has the form `p _`.
* Similarly, it cannot happen that one is `st_plus1` and the other is `st_plus2`, since this would imply that `x` has the form `p t₁ t₂` where `t₁` has both the form `p t₁₁ t₁₂` and the form `c n`.

Formally:
-/

namespace SimpleArith2
open SimpleArith1

theorem step_deterministic : deterministic Step := by
  unfold deterministic
  intro x y₁ y₂ hy₁ hy₂
  induction hy₁ generalizing y₂ with
  | st_plusConstConst n₁ n₂ =>
    cases hy₂ with
    | st_plusConstConst => rfl
    | st_plus1 => rename_i h; cases h
    | st_plus2 => rename_i h; cases h
  | st_plus1 t₁ t₁' t₂ h₁ ih =>
    cases hy₂ with
    | st_plusConstConst => cases h₁
    | st_plus1 => congr; apply ih; assumption
    | st_plus2 => cases h₁
  | st_plus2 n₁ t₂ t₂' h₂ ih =>
    cases hy₂ with
    | st_plusConstConst => cases h₂
    | st_plus1 => rename_i h; cases h
    | st_plus2 => congr; apply ih; assumption

end SimpleArith2

/-
### Values

Next, it will be useful to slightly reformulate the definition of single-step reduction by stating it in terms of "values."

It can be useful to think of the `~~>` relation as defining an _abstract machine_:
* At any moment, the state of the machine is a term.
* A step of the machine is an atomic unit of computation: here, a single "add" operation.
* The _halting states_ of the machine are ones where there is no more computation to be done.

We can then _execute_ a term `t` as follows:
* Take `t` as the starting state of the machine.
* Repeatedly use the `~~>` relation to find a sequence of machine states, starting with `t`, where each state steps to the next.
* When no more reduction is possible, "read out" the final state of the machine as the result of execution.

Intuitively, it is clear that the final states of the machine are always terms of the form `c n` for some `n`.
We call such terms _values_.
-/

inductive Value : Tm → Prop :=
  | v_const n : Value (c n)

open Value

/-
Having introduced the idea of values, we can use it in the definition of the `~~>` relation to write `st_plus2` rule in a slightly more elegant way:
-/

inductive Step : Tm → Tm → Prop :=
  | st_plusConstConst n₁ n₂ : Step (p (c n₁) (c n₂)) (c (n₁ + n₂))
  | st_plus1 t₁ t₁' t₂ : Step t₁ t₁' → Step (p t₁ t₂) (p t₁' t₂)
  | st_plus2 v₁ t₂ t₂' : Value v₁ → Step t₂ t₂' → Step (p v₁ t₂) (p v₁ t₂')

open Step

/-
exercise (3-star)
As a sanity check on this change, let's re-verify determinism.
Here's an informal proof:

_Proof sketch_:
We must show that if `x` steps to both `y₁` and `y₂`, then `y₁` and `y₂` are equal, by induction on a derivation of `Step x y₁`.
Consider the final rules used in the derivations of `Step x y₁` and `Step x y₂`.
* If both are `st_plusConstConst`, the result is immediate.
* The cases when both derivations end with `st_plus1` or `st_plus2` follow by the induction hypothesis.
* It cannot happen that one is `st_plusConstConst` and the other is `st_plus1` or `st_plus2`, since this would imply that `x` has the form `p t₁ t₂` where both `t₁` and `t₂` are constants (by `st_plusConstConst`) and one of `t₁` or `t₂` has the form `p _`.
* Similarly, it cannot happen that one is `st_plus1` and the other is `st_plus2`, since this would imply that `x` has the form `p t₁ t₂` where `t₁` has both the form `p t₁₁ t₁₂` and is a value (hence has the form `c n`).

Most of this proof is the same as the one above.
But to get maximum benefit from the exercise you should try to write your formal version from scratch and just use the earlier one if you get stuck.
-/

theorem step_deterministic : deterministic Step := by
  unfold deterministic
  intro x y₁ y₂ hy₁ hy₂
  induction hy₁ generalizing y₂ with
  | st_plusConstConst n₁ n₂ =>
    cases hy₂ with
    | st_plusConstConst => rfl
    | st_plus1 => rename_i h; cases h
    | st_plus2 => rename_i h; cases h
  | st_plus1 t₁ t₁' t₂ h₁ ih =>
    cases hy₂ with
    | st_plusConstConst => cases h₁
    | st_plus1 => congr; apply ih; assumption
    | st_plus2 => rename_i h;

                  sorry
  | st_plus2 v₁ t₂ t₂' h₂ ih =>
    cases hy₂ with
    | st_plusConstConst => sorry
    | st_plus1 => sorry
    | st_plus2 => sorry

/-
### Strong progress and normal forms

The definition of single-step reduction for our toy language is fairly simple, but for a larger language it would be easy to forget one of the rules and accidentally create a situation where some term cannot take a step even though it has not been completely reduced to a value.
The following theorem shows that we did not, in fact, make such a mistake here.

_Theorem (strong progress)_:
If `t` is a term, then either `t` is a value or else there exists a term `t'` such that `t ~~> t'`.

_Proof_:
By induction on `t`.
* Suppose `t = c n`.
  Then `t` is a value.
* Suppose `t = p t₁ t₂`, where (by the IH) `t₁` either is a value or can step to some `t₁'`, and where `t₂` is either a value or can step to some `t₂'`.
  We must show `p t₁ t₂` is either a value or steps to some `t'`.
  * If `t₁` and `t₂` are both values, then `t` can take a step, by `st_plusConstConst`.
  * If `t₁` is a value and `t₂` can take a step, then so can `t`, by `st_plus2`.
  * If `t₁` can take a step, then so can `t`, by `st_plus1`.

Or, formally:
-/

theorem strong_progress t : Value t ∨ ∃t', Step t t' := by
  induction t with
  | c n => left; apply v_const
  | p t₁ t₂ ih₁ ih₂ =>
    right
    cases ih₁ <;> rename_i h₁
    . cases h₁
      cases ih₂ <;> rename_i h₂
      . cases h₂
        rename_i n₁ n₂
        exists c (n₁ + n₂)
        apply st_plusConstConst
      . obtain ⟨t₂', hst⟩:= h₂
        rename_i n₁
        exists p (c n₁) t₂'
        apply st_plus2
        . apply v_const
        . exact hst
    . obtain ⟨t₁', hst⟩ := h₁
      exists (p t₁' t₂)
      apply st_plus1
      exact hst

/-
This important property is called _strong progress_, because every term either is a value or can "make progress" by stepping to some other term.
(The qualifier "strong" distinguishes it from a more refined version that we'll see in later on, called just _progress_.)

The idea of "making progress" can be extended to tell us something interesting about values: they are exactly the terms that _cannot_ make progress in this sense.

To state this observation formally, let's begin by giving a name to "terms that cannot make progress."
We'll call them _normal forms_.
-/

def normal_form {X : Type} (R : relation X) (t : X) : Prop := ¬∃t', R t t'

/-
Note that this definition specifies what it is to be a normal form for an _arbitrary_ relation `R` over an arbitrary set `X`, not just for the particular single-step reduction relation over terms that we are interested in at the moment.
We'll re-use the same terminology for talking about other relations later in the course.

We can use this terminology to generalize the observation we made in the strong progress theorem: in this language (though not necessarily, in general), normal forms and values are actually the same thing.
-/

theorem value_is_nf v : Value v → normal_form Step v := by
  unfold normal_form
  intro h; cases h
  intro contra; obtain ⟨_, hst⟩ := contra
  cases hst

theorem nf_is_value t : normal_form Step t → Value t := by
  unfold normal_form
  intro h
  have ht : Value t ∨ ∃t', (Step t t') := by apply strong_progress
  cases ht
  . assumption
  . simp [*] at *

theorem nf_same_as_value t : normal_form Step t ↔ Value t := by
  constructor
  . apply nf_is_value
  . apply value_is_nf

/-
Why is this interesting?

Because `Value` is a syntactic concept (it is defined by looking at the way a term is written), while `normal_form` is a semantic one (it is defined by looking at how the term steps).

It is not obvious that these concepts should characterize the same set of terms!

Indeed, we could easily have written the definitions (incorrectly) so that they would _not_ coincide.
-/

/-
### Multi-step reduction

We've been working so far with the _single-step reduction_ relation `~~>`, which formalizes the individual steps of an abstract machine for executing programs.

We can use the same machine to reduce programs to completion, to find out what final result they yield.
This can be formalized as follows:
* First, we define a _multi-step reduction_ relation `~~>*`, which relates terms `t` and `t'` if `t` can reach `t'` by any number (including zero) of single reduction steps.
* Then we define a "result" of a term `t` as a normal form that `t` can reach by multi-step reduction.

Since we'll want to reuse the idea of multi-step reduction many times with many different single-step relations, let's pause and define the concept generically.

Given a relation `R` (e.g., the step relation `~~>`), we define a new relation `Multi R`, called the _multi-step closure_ of `R` as follows.
-/

inductive Multi {X : Type} (R : relation X) : relation X :=
  | multi_refl x : Multi R x x
  | multi_step x y z : R x y → Multi R y z → Multi R x z

open Multi

/-
The effect of this definition is that `Multi R` relates two elements `x` and `y` if
* `x = y`, or
* `R x y`, or
* there is some nonempty sequence `z1`, `z2`, ..., `zn` such that
    `R x z1`
    `R z1 z2`
    ...
    `R zn y`.

Intuitively, if `R` describes a single-step of computation, then `z1` ... `zn` are the intermediate steps of computation that get us from `x` to `y`.

We write `~~>*` for the multi step relation on terms.
-/

syntax term "~~>*" term : term
macro_rules
  | `(term|$t₁:term ~~>* $t₂:term) => `(Multi Step $t₁ $t₂)

/-
The relation `Multi R` has several crucial properties.

First, it is obviously _reflexive_ (that is, `∀ x, Multi R x x`).
In the case of the `~~>*` (i.e., `Multi Step`) relation, the intuition is that a term can execute to itself by taking zero steps of reduction.

Second, it contains `R`; that is, single-step reductions are a particular case of multi-step executions.
  (It is this fact that justifies the word "closure" in the term "multi-step closure of `R`.")
-/

theorem multi_R (X : Type) (R : relation X) x y : R x y → Multi R x y := by
  intro hR
  apply multi_step
  . assumption
  . apply multi_refl

/-
Third, `Multi R` is _transitive_.
-/

theorem multi_trans (X : Type) (R : relation X) x y z
    : Multi R x y → Multi R y z → Multi R x z := by
  intro hxy hyz
  induction hxy generalizing z with
  | multi_refl => exact hyz
  | multi_step  =>
    rename_i xy _ ih
    apply multi_step
    . apply xy
    . apply ih; apply hyz

/-
In particular, for the multi step relation on terms, if `t₁ ~~>* t₂` and `t₂ ~~>* t₃`, then `t₁ ~~>* t₃`.
-/

/-
### Normal forms again

If `t` reduces to `t'` in zero or more steps and `t'` is a normal form, we say that "`t'` is a normal form of `t`."
-/

def step_normal_form := normal_form Step

def normal_form_of t t' := (t ~~>* t') ∧ step_normal_form t'

/-
We have already seen that, for our language, single-step reduction is deterministic, i.e., a given term can take a single step in at most one way.
It follows from this that, if `t` can reach a normal form, then this normal form is unique.

In other words, we can actually pronounce `normal_form t t'` as "`t'` is _the_ normal form of `t`."
-/

/-
exercise (3-star)
-/
theorem normal_forms_unique : deterministic normal_form_of := by
  unfold deterministic; unfold normal_form_of
  intro x y₁ y₂ P₁ P₂
  obtain ⟨P₁₁, P₁₂⟩ := P₁
  obtain ⟨P₂₁, P₂₂⟩ := P₂
  sorry

/-
Indeed, something stronger is true for this language (though not for all the languages we will see): the reduction of _any_ term `t` will eventually reach a normal form, i.e., `normal_form_of` is a _total_ function.
We say the `Step` relation is _normalizing_.
-/

def normalizing {X : Type} (R : relation X) :=
  ∀t, ∃t', (Multi R) t t' ∧ normal_form R t'

/-
To prove that `Step` is normalizing, we need a couple of lemmas.

First, we observe that, if `t` reduces to `t'` in many steps, then the same sequence of reduction steps within `t` is also possible when `t` appears as the first argument to `p`, and similarly when `t` appears as the second argument to `p` (and the first argument is a value).
-/

theorem multistep_congr_1 t₁ t₁' t₂
    : (t₁ ~~>* t₁') → (p t₁ t₂ ~~>* p t₁' t₂) := by
  intro h
  induction h with
  | multi_refl => apply multi_refl
  | multi_step t₁ t₁' t₁'' h1 _ ih =>
    apply multi_step
    . apply st_plus1; apply h1
    . apply ih

/-
exercise (2-star)
-/
theorem multistep_congr_2 v₁ t₂ t₂'
    : (t₂ ~~>* t₂') → (p v₁ t₂ ~~>* p v₁ t₂') := by
  sorry

/-
With these lemmas in hand, the main proof is a straightforward induction.

_Theorem_:
The `Step` function is normalizing, i.e., for every `t` there exists some `t'` such that `t` reduces to `t'` and `t'` is a normal form.

_Proof sketch_:
By induction on terms.
There are two cases to consider:
* `t = c n` for some `n`.
  Here, `t` doesn't take a step, and we have `t' = t`.
  We can derive the left-hand side by reflexivity and the right-hand side by observing (a) that values are normal forms (by `nf_same_as_value`) and (b) that `t` is a value (by `v_const`).
* `t = p t₁ t₂` for some `t₁` and `t₂`.
  By the IH, `t₁` and `t₂` reduce to normal forms `t₁'` and `t₂'`.
  Recall that normal forms are values (by `nf_same_as_value`); we therefore know that `t₁' = c n₁` and `t₂' = c n₂`, for some n₁ and n₂.
  We can combine the `~~>*` derivations for `t₁` and `t₂` using `multistep_congr_1` and `multistep_congr_2` to prove that `p t₁ t₂` reduces in many steps to `t' = c (n₁ + n₂)`.
  Finally, `c (n₁ + n₂)` is a value, which is in turn a normal form by `nf_same_as_value`.
-/

theorem multi_trans_bp {X : Type} (R : relation X) (x y z : X) : Multi R x y → Multi R y z → Multi R x z := by
  intro hxy hyz
  induction hxy generalizing z with
  | multi_refl =>
      exact hyz
  | multi_step =>
      rename_i xy _ ih
      apply multi_step
      · apply xy
      · apply ih
        apply hyz

theorem multistep_congr_1_bp (t₁ t₁' t₂ : Tm) : Multi Step t₁ t₁' → Multi Step (p t₁ t₂) (p t₁' t₂) := by
  exact multistep_congr_1 t₁ t₁' t₂

theorem multistep_congr_2_value (v₁ t₂ t₂' : Tm) : Value v₁ → Multi Step t₂ t₂' → Multi Step (p v₁ t₂) (p v₁ t₂') := by
  intro hv hm
  induction hm with
  | multi_refl =>
      exact Multi.multi_refl _
  | multi_step t₂ u t₂' hstep hm ih =>
      apply Multi.multi_step
      · exact Step.st_plus2 v₁ t₂ u hv hstep
      · exact ih

theorem step_normalizes_to_const (t : Tm) : ∃ n : Nat, Multi Step t (c n) := by
  induction t with
  | c n =>
      exact ⟨n, Multi.multi_refl _⟩
  | p t₁ t₂ ih₁ ih₂ =>
      rcases ih₁ with ⟨n₁, hm₁⟩
      rcases ih₂ with ⟨n₂, hm₂⟩
      refine ⟨n₁ + n₂, ?_⟩
      apply multi_trans_bp Step (p t₁ t₂) (p (c n₁) t₂) (c (n₁ + n₂))
      · exact multistep_congr_1_bp t₁ (c n₁) t₂ hm₁
      · apply multi_trans_bp Step (p (c n₁) t₂) (p (c n₁) (c n₂)) (c (n₁ + n₂))
        · exact multistep_congr_2_value (c n₁) t₂ (c n₂) (Value.v_const n₁) hm₂
        · exact Multi.multi_step _ _ _ (Step.st_plusConstConst n₁ n₂) (Multi.multi_refl _)

theorem value_is_nf_bp (v : Tm) : Value v → normal_form Step v := by
  intro hv
  cases hv with
  | v_const n =>
      unfold normal_form
      intro h
      rcases h with ⟨t', hs⟩
      cases hs

theorem step_normalizing : normalizing Step := by
  intro t
  rcases step_normalizes_to_const t with ⟨n, hmulti⟩
  refine ⟨c n, hmulti, ?_⟩
  apply value_is_nf_bp
  exact Value.v_const n


/-
### Equivalence of big-step and small-step

Having defined the operational semantics of our tiny programming language in two different ways (big-step and small-step), it makes sense to ask whether these definitions actually define the same thing!

They do, though it takes a little work to show it.
The details are left as an exercise.
We consider the two implications separately.
-/

/-
exercise (3-star)
-/
theorem eval__multistep t n : (t ==> n) → (t ~~>* c n) := by
/-
The key idea in the proof can be seen as follows:
```
  p t₁ t₂ ~~>          (by st_plus1)
  p t₁' t₂ ~~>         (by st_plus1)
  p t₁'' t₂ ~~>        (by st_plus1)
  ...
  p (c v₁) t₂ ~~>      (by st_plus2)
  p (c v₁) t₂' ~~>     (by st_plus2)
  p (c v₁) t₂'' ~~>    (by st_plus2)
  ...
  p (c v₁) (c v₂) ~~>  (by st_plusConstConst)
  c (v₁ + v₂)
```
That is, the multistep reduction of a term of the form `P t₁ t₂` proceeds in three phases:
* First, we use `st_plus1` some number of times to reduce `t₁` to a normal form, which must (by `nf_same_as_value`) be a term of the form `c v₁` for some `v₁`.
* Next, we use `st_plus2` some number of times to reduce `t₂` to a normal form, which must again by a term of the form `c v₂` for some `v₂`.
* Finally, we use `st_plusConstConst` once to reduce `p (c v₁) (c v₂)` to `c (v₁ + v₂)`.

To formalize this intuition, you'll need to use the congruence lemmas from above (you might want to review them now, so that you'll be able to recognize when they are useful), plus some basic properties of `~~>*`: that it is reflexive, transitive, and includes `~~>`.
-/
  sorry

/-
For the other direction, we need one lemma, which establishes a relation between single-step reduction and big-step evaluation.
-/

/-
exercise (3-star)
-/
theorem step__eval t t' n
    : Step t t' → (t' ==> n) → t ==> n := by
  intro Hs
  induction Hs generalizing n with (intro he; cases he)
  | _ => sorry

/-
The fact that small-step reduction implies big-step evaluation is now straightforward to prove.

The proof proceeds by induction on the multi-step reduction sequence that is buried in the hypothesis `normal_form_of t t'`.

Make sure you understand the statement before you start to work on the proof.
-/

/-
exercise (3-star)
-/
theorem multistep__eval t t' : normal_form_of t t' → ∃n, t' = c n ∧ t ==> n := by
  sorry

/-
### Additional exercises

We've considered arithmetic expressions.
This exercise explores how they interact with conditional expressions.
-/

namespace Combined

inductive Tm : Type :=
  | c : Nat → Tm
  | p : Tm → Tm → Tm
  | tru : Tm
  | fls : Tm
  | test : Tm → Tm → Tm → Tm

open Tm

inductive Value : Tm → Prop :=
  | v_const n : Value (c n)
  | v_tru : Value tru
  | v_fls : Value fls

open Value

inductive Step : Tm → Tm → Prop :=
  | st_plusConstConst n₁ n₂ : Step (p (c n₁) (c n₂)) (c (n₁ + n₂))
  | st_plus1 t₁ t₁' t₂ : Step t₁ t₁' → Step (p t₁ t₂) (p t₁' t₂)
  | st_plus2 n₁ t₂ t₂' : Step t₂ t₂' → Step (p (c n₁) t₂) (p (c n₁) t₂')
  | st_ifTrue t₁ t₂ : Step (test tru t₁ t₂) t₁
  | st_ifFalse t₁ t₂ : Step (test fls t₁ t₂) t₂
  | st_if t₀ t₀' t₁ t₂ : Step t₀ t₀' → Step (test t₀ t₁ t₂) (test t₀' t₁ t₂)

open Step

/-
Formally prove or disprove these two properties for the combined language.
-/

/-
exercise (3-star)
-/
theorem combined_step_deterministic
    : deterministic Step ∨ ¬ deterministic Step := by
  sorry

/-
exercise (3-star)
-/
theorem combined_strong_progress
    : (∀ t, Value t ∨ ∃ t', Step t t') ∨ ¬ (∀ t, Value t ∨ ∃ t', Step t t')
    := by
  sorry

end Combined

/-
## references
* [Software Foundations, Volume 2 Programming Language Foundations: Small-Step Operational Semantics](https://softwarefoundations.cis.upenn.edu/plf-current/Smallstep.html)
-/
