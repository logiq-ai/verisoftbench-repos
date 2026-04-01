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

noncomputable def triple_forIn_deacreasing_inv {β} (measure : β → ℕ) (inv : β → l) (init : β) (i : ℕ) (b : β) : l :=
  inv b ⊓ ⌜measure b + i ≤ measure init⌝

theorem triple_forIn_deacreasing_final {β} {measure : β → ℕ} {init : β} (inv : β → l) (b : β) :
  triple_forIn_deacreasing_inv measure inv init (measure init) b ≤ inv b ⊓ ⌜measure b = 0⌝ := by
  by_cases h : measure b + measure init ≤ measure init
  · have h0 : measure b + measure init ≤ 0 + measure init := by
      simpa [Nat.zero_add] using h
    have hb0 : measure b ≤ 0 := by
      exact (Nat.add_le_add_iff_right).mp h0
    have hb : measure b = 0 := Nat.eq_zero_of_le_zero hb0
    simp [triple_forIn_deacreasing_inv, h, hb]
  · simp [triple_forIn_deacreasing_inv, h]

theorem triple_forIn_deacreasing_step {β} {measure : β → ℕ}
  {init : β} {f : β → m (ForInStep β)}
  (inv : β → l)
  (hstep : ∀ b,
    measure b <= measure init ->
    triple
      (inv b)
      (f b)
      (fun | .yield b' => inv b' ⊓ ⌜measure b' < measure b⌝ | .done b' => ⌜ measure b' = 0 ⌝ ⊓ inv b'))
  (i : ℕ) (b : β) :
  triple
    (triple_forIn_deacreasing_inv measure inv init i b)
    (f b)
    (fun | .yield b' => triple_forIn_deacreasing_inv measure inv init (i + 1) b'
         | .done b' => triple_forIn_deacreasing_inv measure inv init (measure init) b') := by
  by_cases hbi : measure b + i ≤ measure init
  · have hb : measure b ≤ measure init := le_trans (Nat.le_add_right _ _) hbi
    apply triple_cons (x := f b) (pre := inv b)
      (post := fun
        | .yield b' => inv b' ⊓ ⌜measure b' < measure b⌝
        | .done b' => ⌜measure b' = 0⌝ ⊓ inv b')
    · simp [triple_forIn_deacreasing_inv, hbi]
    · intro y
      cases y with
      | yield b' =>
          have hpure : ⌜measure b' < measure b⌝ ≤ (⌜measure b' + (i + 1) ≤ measure init⌝ : l) :=
            LE.pure_imp _ _ (by
              intro hlt
              omega)
          simpa [triple_forIn_deacreasing_inv] using
            (inf_le_inf le_rfl hpure :
              inv b' ⊓ ⌜measure b' < measure b⌝ ≤ inv b' ⊓ ⌜measure b' + (i + 1) ≤ measure init⌝)
      | done b' =>
          have hpure : ⌜measure b' = 0⌝ ≤ (⌜measure b' + measure init ≤ measure init⌝ : l) :=
            LE.pure_imp _ _ (by
              intro h0
              omega)
          simpa [triple_forIn_deacreasing_inv, inf_comm] using
            (inf_le_inf le_rfl hpure :
              inv b' ⊓ ⌜measure b' = 0⌝ ≤ inv b' ⊓ ⌜measure b' + measure init ≤ measure init⌝)
    · exact hstep b hb
  · simp [triple, triple_forIn_deacreasing_inv, hbi]

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
  let I : ℕ → β → l := triple_forIn_deacreasing_inv measure inv init
  have hrange0 :
      triple (I 0 init) (forIn [0:measure init] init (fun _ => f)) (I (measure init)) := by
    refine triple_forIn_range_step1 (xs := [0:measure init]) (init := init) (f := fun _ => f) I ?_ rfl ?_
    · intro i b
      simpa [I] using
        (triple_forIn_deacreasing_step (measure := measure) (init := init) (f := f) inv hstep i b)
    · simp
  have hrange :
      triple (inv init) (forIn [0:measure init] init (fun _ => f)) (I (measure init)) := by
    simpa [I, triple_forIn_deacreasing_inv] using hrange0
  refine triple_cons (x := forIn [0:measure init] init (fun _ => f)) ?_ ?_ hrange
  · rfl
  · intro b
    exact triple_forIn_deacreasing_final (measure := measure) (init := init) inv b


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
