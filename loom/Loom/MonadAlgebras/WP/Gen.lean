import Mathlib.Logic.Function.Basic
import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Order.Lattice
import Mathlib.Order.Basic

import Loom.MonadAlgebras.WP.Basic
import Loom.MonadAlgebras.WP.Liberal
import Loom.MonadAlgebras.WP.DoNames'

open Lean Meta Elab Command Term

universe u v w

private def _root_.Lean.SimpleScopedEnvExtension.get [Inhabited σ] (ext : SimpleScopedEnvExtension α σ)
  [Monad m] [MonadEnv m] : m σ := do
  return ext.getState (<- getEnv)

private def _root_.Lean.SimpleScopedEnvExtension.modify
  (ext : SimpleScopedEnvExtension α σ) (s : σ -> σ)
  [Monad m] [MonadEnv m] : m Unit := do
  Lean.modifyEnv (ext.modifyState · s)

private def _root_.Lean.SimplePersistentEnvExtension.get [Inhabited σ] (ext : SimplePersistentEnvExtension α σ)
  [Monad m] [MonadEnv m] : m σ := do
  return ext.getState (<- getEnv)

private def _root_.Lean.SimplePersistentEnvExtension.modify
  (ext : SimplePersistentEnvExtension α σ) (s : σ -> σ)
  [Monad m] [MonadEnv m] : m Unit := do
  Lean.modifyEnv (ext.modifyState · s)

structure LoomAssertionsMap where
  maxId : Int
  syntaxStore : Std.HashMap Int Term
  nameStore : Std.HashMap Name Int
  nameCounter : Std.HashMap Name Int

  deriving Inhabited

def addAssertion (s : LoomAssertionsMap) (t : Term) (n : Name) (coreName: Name): LoomAssertionsMap :=
  let maxId := s.maxId + 1
  let maxIdLocal := s.nameCounter.get! coreName + 1
  { s with
    maxId := maxId
    syntaxStore := s.syntaxStore.insert maxId t
    nameStore := s.nameStore.insert n maxId
    nameCounter := s.nameCounter.insert coreName maxIdLocal }

initialize loomAssertionsMap :
  SimplePersistentEnvExtension (Term × Name × Name) LoomAssertionsMap <-
  registerSimplePersistentEnvExtension {
    addEntryFn := fun s ⟨t, n, coreName⟩ => addAssertion s t n coreName
    addImportedFn := fun as => Id.run do
      let mut res : LoomAssertionsMap := default
      for a in as do
        for (t, n, coreName) in a do
          res := addAssertion res t n coreName
      return res
  }

section
variable {m : Type u -> Type v} [Monad m] [LawfulMonad m] {α : Type u} {l : Type u} [CompleteLattice l]

set_option linter.unusedVariables false in
def invariantGadget [MAlgOrdered m l] (inv : List l): m PUnit := pure .unit

variable [MAlgOrdered m l]

@[simp]
abbrev invariantSeq (f : List l) := f.foldr (·⊓·) ⊤

-- macro "invariant" t:term : invariantClause => `(invariantGadget $t)


set_option linter.unusedVariables false in
def onDoneGadget {invType : Type u} (inv : invType) : m PUnit := pure .unit


set_option linter.unusedVariables false in
def assertGadget {l : Type u} (h : l) : m PUnit := pure .unit


set_option linter.unusedVariables false in
def decreasingGadget (measure : Option ℕ) : m PUnit := pure .unit

elab "with_name_prefix" lit:name inv:term : term => do
  let ⟨maxId, _, _, cntr⟩ <- loomAssertionsMap.get
  let newMaxId := maxId + 1
  let coreName := match (← Term.getDeclName?) with
    | some res => res
    | none => `nameless
  let localName := (Lean.Name.mkSimple (lit.getName.toString ++ "_" ++ coreName.toString))
  let cntrElem := match cntr.get? localName with
    | some resId => resId
    | none => 0
  let maxIdLocal := 1 + cntrElem
  let invName := lit.getName.toString ++ "_" ++ toString maxIdLocal.toNat |>.toName
  loomAssertionsMap.modify (fun res => {
      syntaxStore := res.syntaxStore.insert newMaxId inv
      nameStore := res.nameStore.insert invName newMaxId
      maxId := newMaxId
      nameCounter := res.nameCounter.insert localName maxIdLocal
      })
  Term.elabTerm (<- ``(WithName $inv $(Lean.quoteNameMk invName))) none

elab "type_with_name_prefix" lit:name inv:term : term => do
  let ⟨maxId, _, _, cntr⟩ <- loomAssertionsMap.get
  let newMaxId := maxId + 1
  let coreName := match (← Term.getDeclName?) with
    | some res => res
    | none => `nameless
  let localName := (Lean.Name.mkSimple (lit.getName.toString ++ "_" ++ coreName.toString))
  let cntrElem := match cntr.get? localName with
    | some resId => resId
    | none => 0
  let maxIdLocal := 1 + cntrElem
  let invName := lit.getName.toString ++ "_" ++ toString maxIdLocal.toNat |>.toName
  loomAssertionsMap.modify (fun res => {
      syntaxStore := res.syntaxStore.insert newMaxId inv
      nameStore := res.nameStore.insert invName newMaxId
      maxId := newMaxId
      nameCounter := res.nameCounter.insert localName maxIdLocal
      })
  Term.elabTerm (<- ``(typeWithName $inv $(Lean.quoteNameMk invName))) none


def termBeforeInvariant := Parser.withForbidden "invariant" Parser.termParser

attribute [run_builtin_parser_attribute_hooks] termBeforeInvariant

builtin_initialize
  register_parser_alias termBeforeInvariant

structure WPGen (x : m α) where
  get : Cont l α
  -- sideCond : l := ⊤
  prop : ∀ post, get post <= wp x post

omit [LawfulMonad m] in
lemma WPGen.intro (x : m α) (wpg : WPGen x) :
  pre <= wpg.get post ->
  -- pre <= wpg.sideCond ->
  triple pre x post := by
  intro h; apply le_trans'; apply wpg.prop; apply_assumption

def WPGen.default (x : m α) : WPGen x where
  get := wp x
  prop := by intro post; simp

def WPGen.pure (x : α) : WPGen (pure (f := m) x) where
  get := fun post => post x
  prop := by intro post; simp [wp_pure]

def WPGen.bind {x : m α} {f : α -> m β} (wpg : WPGen x) (wpgf : ∀ a, WPGen (f a)) :
  WPGen (x >>= f) where
  get := fun post => wpg.get (fun a => (wpgf a).get post)
  prop := by
    intro post; simp [wp_bind]; apply le_trans
    apply wpg.prop; apply wp_cons; intro a; apply (wpgf a).prop

def WPGen.map {x : m α} {f : α -> β} (wpg : WPGen x) : WPGen (f <$> x) where
  get := fun post => wpg.get (fun a => post (f a))
  prop := by
    rw [map_eq_pure_bind]; simp only [wp_bind, wp_pure]; intro
    apply le_trans; solve_by_elim [wpg.prop]; rfl

noncomputable
def WPGen.spec_triple (x : m α) (trp : triple pre x post) : WPGen x where
  get := spec pre post
  prop := by rw [<-triple_spec] at trp; solve_by_elim

-- noncomputable
-- def WPGen.spec_triple_invs (x : m α) (trp : invs -> triple pre x post) : WPGen x where
--   get := spec pre post
--   prop := by rw [<-triple_spec] at trp; solve_by_elim

def WPGen.spec_wp wp' (x : m α) (trp : wp x = wp') : WPGen x where
  get := wp'
  prop := by
    intro post
    subst trp
    simp

def triple_forIn_deacreasing_inv {β} (measure : β → ℕ) (init : β) (inv : β → l) : ℕ → β → l :=
  fun i b => if measure b ≤ measure init - i then inv b else ⊥

theorem triple_forIn_deacreasing_measure_bound (a b c i : ℕ) : a < b → b ≤ c - i → a ≤ c - (i + 1) := by
  intro hab hbc
  omega

theorem triple_forIn_deacreasing_step {β} {measure : β → ℕ}
  {init : β} {f : β → m (ForInStep β)}
  (inv : β → l)
  (hstep : ∀ b,
    measure b ≤ measure init →
    triple
      (inv b)
      (f b)
      (fun | .yield b' => inv b' ⊓ ⌜measure b' < measure b⌝ | .done b' => ⌜measure b' = 0⌝ ⊓ inv b')) :
  ∀ i b,
    triple
      (triple_forIn_deacreasing_inv measure init inv i b)
      (f b)
      (fun | .yield b' => triple_forIn_deacreasing_inv measure init inv (i + 1) b'
           | .done b' => triple_forIn_deacreasing_inv measure init inv (measure init) b') := by
  intro i b
  by_cases hb : measure b ≤ measure init - i
  · have hb_init : measure b ≤ measure init := by
      exact le_trans hb (Nat.sub_le _ _)
    refine triple_cons (x := f b) (pre := inv b)
      (post := fun
        | .yield b' => inv b' ⊓ ⌜measure b' < measure b⌝
        | .done b' => ⌜measure b' = 0⌝ ⊓ inv b')
      ?_ ?_ (hstep b hb_init)
    · simp [triple_forIn_deacreasing_inv, hb]
    · intro y
      cases y with
      | yield b' =>
          by_cases hb' : measure b' ≤ measure init - (i + 1)
          · simpa [triple_forIn_deacreasing_inv, hb'] using (inf_le_left : inv b' ⊓ ⌜measure b' < measure b⌝ ≤ inv b')
          · have hnotlt : ¬ measure b' < measure b := by
              intro hlt
              exact hb' (triple_forIn_deacreasing_measure_bound (a := measure b') (b := measure b)
                (c := measure init) (i := i) hlt hb)
            simp [triple_forIn_deacreasing_inv, hb', hnotlt]
      | done b' =>
          by_cases hb' : measure b' ≤ measure init - measure init
          · have hz : measure b' = 0 := by
              exact Nat.eq_zero_of_le_zero (by simpa using hb')
            simp [triple_forIn_deacreasing_inv, hb', hz]
          · have hne : measure b' ≠ 0 := by
              intro h0
              apply hb'
              simpa [h0]
            simp [triple_forIn_deacreasing_inv, hb', hne]
  · simp [triple, triple_forIn_deacreasing_inv, hb]

theorem triple_forIn_deacreasing {β} {measure : β -> ℕ}
  {init : β} {f : β → m (ForInStep β)}
  (inv : β → l)
  (hstep : ∀ b,
    measure b <= measure init ->
    triple
      (inv b)
      (f b)
      (fun | .yield b' => inv b' ⊓ ⌜measure b' < measure b⌝ | .done b' => ⌜ measure b' = 0 ⌝ ⊓ inv b')) :
  triple (inv init) (forIn [0:measure init] init (fun _ => f)) (fun b => inv b ⊓ ⌜measure b = 0⌝) := by
  let I : ℕ → β → l := triple_forIn_deacreasing_inv measure init inv
  have hloop :
      triple (I 0 init) (forIn [0:measure init] init (fun _ => f)) (I (measure init)) := by
    apply triple_forIn_range_step1 (m := m) (xs := [0:measure init]) (f := fun _ => f) (inv := I)
    · intro i b
      simpa [I, triple_forIn_deacreasing_inv] using
        (triple_forIn_deacreasing_step (measure := measure) (init := init) (f := f) inv hstep i b)
    · rfl
    · simp
  have hstart : I 0 init = inv init := by
    simp [I, triple_forIn_deacreasing_inv, Nat.sub_zero]
  have hfinal : I (measure init) = fun b => inv b ⊓ ⌜measure b = 0⌝ := by
    funext b
    by_cases h : measure b = 0
    · simp [I, triple_forIn_deacreasing_inv, Nat.sub_self, LE.pure, h]
    · simp [I, triple_forIn_deacreasing_inv, Nat.sub_self, LE.pure, h]
  rw [hstart] at hloop
  rw [hfinal] at hloop
  exact hloop


attribute [-simp] Std.Range.forIn_eq_forIn_range' in
noncomputable
def WPGen.forWithInvariant {xs : Std.Range} {init : β} {f : ℕ → β → m (ForInStep β)}
  (inv : ℕ → β → List l) (wpg : ∀ i b, WPGen (f i b)) (xs1 : xs.step = 1) (xs_le : xs.start <= xs.stop := by omega) :
    WPGen (forIn xs init (fun i b => do invariantGadget (inv i b); (f i b))) where
    get := ⌜∀ i b, invariantSeq (inv i b) <= (wpg i b).get fun
      | .yield b' => invariantSeq <| inv (i + 1) b'
      | .done b'  => invariantSeq <| inv xs.stop b'⌝
      ⊓ spec
      ((inv xs.start init).foldr (·⊓·) ⊤)
      (fun b => (inv xs.stop b).foldr (·⊓·) ⊤)
    prop := by
      intro post; simp only [LE.pure]; split_ifs with h <;> try simp
      apply (triple_spec ..).mpr
      simp [invariantGadget]
      apply triple_forIn_range_step1 (fun i b => (inv i b).foldr (·⊓·) ⊤)
      simp [invariantSeq, <-xs1] at h
      intro i b; apply (wpg i b).intro
      all_goals solve_by_elim

-- noncomputable
-- def WPGen.forWithInvariantDecreasing {β} {measure : β -> ℕ}
--   {init : β} {f : β → m (ForInStep β)}
--   (inv : β → List l) :
--     WPGen (forIn [0:mb] init (fun _ b => do decreasingGadget (measure b); invariantGadget (inv b); f b)) := by
--   apply spec_triple_invs (invs :=
--     mb = measure init ∧
--     (∀ b, measure b <= measure init -> triple (invariants (inv b)) (f b) (fun | .yield b' => invariants (inv b') ⊓ ⌜measure b' < measure b⌝ | .done b' => ⌜ measure b' = 0 ⌝ ⊓ invariants (inv b'))))
--   simp only [and_imp]; intros eq h; simp only [eq]
--   apply triple_forIn_deacreasing (fun b => invariants (inv b)); simp [invariantGadget, decreasingGadget]
--   solve_by_elim

end
variable {m : Type u -> Type v} [Monad m] [LawfulMonad m] {α : Type u} {l : Type u} [CompleteBooleanAlgebra l] [MAlgOrdered m l]


def WPGen.assert {l : Type u} {m : Type u -> Type v} [Monad m] [LawfulMonad m] [CompleteBooleanAlgebra l] [MAlgOrdered m l] (h : l) : WPGen (assertGadget (m := m) h) where
  get := fun post => h ⊓ (h ⇨ post .unit)
  prop := by simp [assertGadget, wp_pure]

noncomputable
def WPGen.if {l : Type u} {m : Type u -> Type v} [Monad m] [LawfulMonad m] [CompleteBooleanAlgebra l] [MAlgOrdered m l]
  {hd : Decidable h} {x y : m α}
  (wpgx : h → WPGen x) (wpgy : ¬h → WPGen y)
  : WPGen (if h then x else y) where
  get := fun post =>
    (⨅ hc : WithName h (Lean.Name.anonymous.mkStr "if_pos"), (wpgx hc).get post) ⊓
    (⨅ hc : WithName (¬h) (Lean.Name.anonymous.mkStr "if_neg"), (wpgy hc).get post)
  prop := by
    intro post
    split
    { refine inf_le_of_left_le ?_
      apply iInf_le_iff.mpr
      rename_i hc
      intro b hi
      apply le_trans (b := (wpgx hc).get post)
      exact hi hc
      apply (wpgx hc).prop }
    refine inf_le_of_right_le ?_
    apply iInf_le_iff.mpr
    rename_i hc
    intro b hi
    apply le_trans (b := (wpgy hc).get post)
    exact hi hc
    apply (wpgy hc).prop

noncomputable
def WPGen.let  {l : Type u} {m : Type u -> Type v} [Monad m] [LawfulMonad m] [CompleteBooleanAlgebra l] [MAlgOrdered m l]
  (y : β) {x : β -> m α} (wpgx : ∀ y, WPGen (x y)) : WPGen (let z := y; x z) where
  get := fun post => ⨅ z, ⌜z = y⌝ ⇨ (wpgx z).get post
  prop := by
     intro post; simp; refine iInf_le_of_le y ?_
     simp; apply (wpgx y).prop
