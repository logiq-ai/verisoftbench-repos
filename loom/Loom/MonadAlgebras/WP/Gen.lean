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

noncomputable abbrev triple_forIn_deacreasing_inv {β : Type u} (measure : β → ℕ) (init : β) (inv : β → l) : ℕ → β → l := fun i b => inv b ⊓ ⌜measure b + i ≤ measure init⌝

theorem triple_forIn_deacreasing_step: {β : Type u} → {measure : β → ℕ} → {init : β} → {f : β → m (ForInStep β)} →
    (inv : β → l) →
    (hstep : ∀ b,
      measure b ≤ measure init →
      triple
        (inv b)
        (f b)
        (fun
          | .yield b' => inv b' ⊓ ⌜measure b' < measure b⌝
          | .done b' => ⌜measure b' = 0⌝ ⊓ inv b')) →
    ∀ i b,
      triple
        (triple_forIn_deacreasing_inv measure init inv i b)
        (f b)
        (fun
          | .yield b' => triple_forIn_deacreasing_inv measure init inv (i + 1) b'
          | .done b' => triple_forIn_deacreasing_inv measure init inv (measure init) b') := by
  intro β measure init f inv hstep i b
  simp only [triple, triple_forIn_deacreasing_inv, LE.pure]
  split_ifs with hbound
  · have hb : measure b ≤ measure init := by
      exact le_trans (Nat.le_add_right _ _) hbound
    have hs :
        inv b ≤
          wp (f b) (fun x => match x with
            | .yield b' => inv b' ⊓ ⌜measure b' < measure b⌝
            | .done b' => ⌜measure b' = 0⌝ ⊓ inv b') := by
      simpa [triple] using hstep b hb
    refine le_trans ?_ (le_trans hs ?_)
    · simp
    · apply wp_cons
      intro s
      cases s with
      | yield b' =>
          simp only [LE.pure]
          by_cases hlt : measure b' < measure b
          · have h₁ : measure b' + (i + 1) ≤ measure b + i := by
              simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
                Nat.add_le_add_right (Nat.succ_le_of_lt hlt) i
            have h₂ : measure b' + (i + 1) ≤ measure init := by
              exact le_trans h₁ hbound
            simp [hlt, h₂]
          · simp [hlt]
      | done b' =>
          simp only [LE.pure]
          by_cases hzero : measure b' = 0
          · have h₂ : measure b' + measure init ≤ measure init := by
              simpa [hzero]
            simp [hzero, h₂, inf_comm, inf_left_comm, inf_assoc]
          · simp [hzero]
  · simp

theorem triple_forIn_deacreasing: {β : Type u} → {measure : β → ℕ} →
    {init : β} → {f : β → m (ForInStep β)} →
    (inv : β → l) →
    (hstep : ∀ b,
      measure b ≤ measure init →
      triple
        (inv b)
        (f b)
        (fun
          | .yield b' => inv b' ⊓ ⌜measure b' < measure b⌝
          | .done b' => ⌜measure b' = 0⌝ ⊓ inv b')) →
    triple
      (inv init)
      (forIn [0:measure init] init (fun _ => f))
      (fun b => inv b ⊓ ⌜measure b = 0⌝) := by
  intro β measure init f inv hstep
  let I := triple_forIn_deacreasing_inv measure init inv
  apply (triple_cons (x := forIn [0:measure init] init (fun _ => f))
    (pre := I 0 init) (post := fun b => I (measure init) b))
  · simpa [I, triple_forIn_deacreasing_inv]
  · intro b
    change inv b ⊓ ⌜measure b + measure init ≤ measure init⌝ ≤ inv b ⊓ ⌜measure b = 0⌝
    rw [pure_intro_l]
    intro h
    have hb : measure b = 0 := by omega
    simp [hb]
  · simpa [I, triple_forIn_deacreasing_inv] using
      (triple_forIn_range_step1 (xs := [0:measure init]) (init := init) (f := fun _ => f) (inv := I)
        (hstep := triple_forIn_deacreasing_step inv hstep) (by simp) (by simp))


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
