/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under LGPL 2.1 license as described in the file LICENSE.md.
Authors: Wojciech Różowski
-/

import LeroyCompilerVerificationCourse.Imp

/-
  2. The target language: a stack machine

  Our compiler will translate IMP to the language of a simple stack
  machine.  This machine is similar to the "Reverse Polish Notation"
  used by old HP pocket calculators: a stack holds intermediate
  results, and individual instructions pop arguments off the stack and
  push results back on the stack.
-/

/-
  2.1 Instruction set

  Here is the instruction set of the machine:
-/
@[grind] inductive instr : Type where
  | Iconst (n : Int)            /-r push the integer `n` -/
  | Ivar (x : ident)            /-r push the current value of variable `x` -/
  | Isetvar (x : ident)         /-r pop an integer and assign it to variable `x` -/
  | Iadd                        /-r pop two integers, push their sum -/
  | Iopp                        /-r pop one integer, push its opposite -/
  | Ibranch (d : Int)           /-r skip forward or backward `d` instructions -/
  | Ibeq (d1 : Int) (d0 : Int)  /-r pop two integers, skip `d1` instructions if equal, `d0` if not equal -/
  | Ible (d1 : Int) (d0 : Int)  /-r pop two integer, skip `d1` instructions if less or equal, `d0` if greater -/
  | Ihalt                       /-r stop execution -/
    deriving Repr

/-
  A piece of machine code is a list of instructions.
  The length (number of instructions) of a piece of code.
-/
@[grind] def codelen (c : List instr) : Int := c.length

/-
  2.2 Operational semantics

  The machine operates on a code `C` (a fixed list of instructions)
  and three variable components:
  - a program counter `pc`, denoting a position in `C`
  - an evaluation stack, containing integers
  - a store assigning integer values to variables.
-/

def stack : Type := List Int

def config : Type := Int × stack × store

/-
  `instr_at C pc = .some i` if `i` is the instruction at position `pc` in `C`.
-/
@[grind] def instr_at (C : List instr) (pc : Int) : Option instr :=
  match C with
  | [] => .none
  | i :: C' => if pc = 0 then .some i else instr_at C' (pc - 1)

/-
  The semantics of the machine is given in small-step style as a transition system:
  a relation between machine configurations "before" and "after" execution
  of the instruction at the current program point.
  The transition relation is parameterized by the code `C` for the whole program.
  There is one transition for each kind of instruction,
  except `.Ihalt`, which has no transition.
-/
@[grind] inductive transition (C : List instr) : config → config → Prop where
  | trans_const : ∀ pc stk s n,
      instr_at C pc = .some (.Iconst n) →
      transition C (pc    , stk     , s)
                   (pc + 1, n :: stk, s)
  | trans_var : ∀ pc stk s x,
      instr_at C pc = .some (.Ivar x) ->
      transition C (pc    , stk       , s)
                   (pc + 1, s x :: stk, s)
  | trans_setvar : ∀ pc stk s x n,
      instr_at C pc = .some (.Isetvar x) ->
      transition C (pc    , n :: stk, s)
                   (pc + 1, stk     , update x n s)
  | trans_add : ∀ pc stk s n1 n2,
      instr_at C pc = .some (.Iadd) ->
      transition C (pc    , n2 :: n1 :: stk , s)
                   (pc + 1, (n1 + n2) :: stk, s)
  | trans_opp : ∀ pc stk s n,
      instr_at C pc = .some (.Iopp) ->
      transition C (pc    , n :: stk    , s)
                   (pc + 1, (- n) :: stk, s)
  | trans_branch : ∀ pc stk s d pc',
      instr_at C pc = .some (.Ibranch d) ->
      pc' = pc + 1 + d ->
      transition C (pc , stk, s)
                   (pc', stk, s)
  | trans_beq : ∀ pc stk s d1 d0 n1 n2 pc',
      instr_at C pc = .some (.Ibeq d1 d0) ->
      pc' = pc + 1 + (if n1 = n2 then d1 else d0) ->
      transition C (pc , n2 :: n1 :: stk, s)
                   (pc', stk            , s)
  | trans_ble : ∀ pc stk s d1 d0 n1 n2 pc',
      instr_at C pc = .some (.Ible d1 d0) ->
      pc' = pc + 1 + (if n1 ≤ n2 then d1 else d0) ->
      transition C (pc , n2 :: n1 :: stk, s)
                   (pc', stk            , s)

/-
  As usual with small-step semantics, we form sequences of machine transitions
  to define the behavior of a code.  Zero, one or several transitions
  correspond to the reflexive transitive closure of relation `transition C`.
-/
@[grind] def transitions (C : List instr) : config → config → Prop :=
  star (transition C)

/-
  We always start with `pc = 0` and an empty evaluation stack.
  We stop successfully if `pc` points to an `.Ihalt` instruction
  and the evaluation stack is empty.
-/
def machine_terminates (C : List instr) (s_init : store) (s_final : store) : Prop :=
  ∃ pc, transitions C (0, [], s_init) (pc, [], s_final)
          ∧ instr_at C pc = .some .Ihalt

/-
  The machine can also run forever, making infinitely many transitions.
-/
def machine_diverges (C : List instr) (s_init : store) : Prop :=
  infseq (transition C) (0, [], s_init)

/-
  Yet another possibility is that the machine gets stuck after some transitions.
-/
def machine_goes_wrong (C : List instr) (s_init : store) : Prop :=
  ∃ pc stk s,
      transitions C (0, [], s_init) (pc, stk, s)
   ∧ irred (transition C) (pc, stk, s)
   ∧ (instr_at C pc ≠ .some .Ihalt ∨ stk ≠ [])

/-
  3. The compilation scheme

  We now define the compilation of IMP expressions and commands to
    sequence of machine instructions.
  The code for an arithmetic expression `a` executes in sequence (no
  branches), and deposits the value of `a` at the top of the stack.
  This is the familiar translation to "reverse Polish notation".

  The only twist here is that the machine has no "subtract" instruction.
  However, it can compute the difference `a - b` by adding `a` to the
  opposite of `b`.
-/
@[grind] def compile_aexp (a : aexp) : List instr :=
  match a with
  | .CONST n => .Iconst n :: []
  | .VAR x => .Ivar x :: []
  | .PLUS a1 a2  => (compile_aexp a1) ++ (compile_aexp a2) ++ (.Iadd :: [])
  | .MINUS a1 a2 => compile_aexp a1 ++ compile_aexp a2 ++ (.Iopp :: .Iadd :: [])

/-
  For Boolean expressions `b`, we could produce code that deposits `1` or `0`
  at the top of the stack, depending on whether `b` is true or false.
  The compiled code for `.IFTHENELSE` and `.WHILE` commands would, then,
  compare this 0/1 value against 0 and branch to the appropriate piece of code.

  However, it is simpler and more efficient to compile a Boolean expression `b`
  to a piece of code that directly jumps `d1` or `d0` instructions forward,
  depending on whether `b` is true or false.  The actual value of `b` is
  never computed as an integer, and the stack is unchanged.
-/
@[grind] def compile_bexp (b : bexp) (d1 : Int) (d0 : Int) : List instr :=
  match b with
  | .TRUE => if d1 = 0 then [] else .Ibranch d1 :: []
  | .FALSE => if d0 = 0 then [] else .Ibranch d0 :: []
  | .EQUAL a1 a2 => compile_aexp a1 ++ compile_aexp a2 ++ .Ibeq d1 d0 :: []
  | .LESSEQUAL a1 a2 => compile_aexp a1 ++ compile_aexp a2 ++ .Ible d1 d0 :: []
  | .NOT b1 => compile_bexp b1 d0 d1
  | .AND b1 b2 =>
      let code2 := compile_bexp b2 d1 d0
      let code1 := compile_bexp b1 0 (codelen code2 + d0)
      code1 ++ code2

/-
  The code for a command `c`:
  - updates the store (the values of variables) as prescribed by `c`
  - preserves the stack
  - finishes "at the end" of the generated code: the next instruction
    executed is the instruction that will follow the generated code.
-/
@[grind] def compile_com (c : com) : List instr :=
  match c with
  | .SKIP =>
      []
  | .ASSIGN x a =>
      compile_aexp a ++ .Isetvar x :: []
  | .SEQ c1 c2 =>
      compile_com c1 ++ compile_com c2
  | .IFTHENELSE b ifso ifnot =>
      let code_ifso := compile_com ifso
      let code_ifnot := compile_com ifnot
      compile_bexp b 0 (codelen code_ifso + 1)
      ++ code_ifso
      ++ .Ibranch (codelen code_ifnot)
      :: code_ifnot
  | .WHILE b body =>
      let code_body := compile_com body
      let code_test := compile_bexp b 0 (codelen code_body + 1)
      code_test
      ++ code_body
      ++ .Ibranch (- (codelen code_test + codelen code_body + 1)) :: []

/-
  The code for a program `p` (a command) is similar, but terminates
  cleanly on an `.Ihalt` instruction.
-/
def compile_program (p : com) : List instr :=
  compile_com p ++ .Ihalt :: []

/-- info: [instr.Ivar "x", instr.Iconst 1, instr.Iadd, instr.Isetvar "x", instr.Ihalt] -/
#guard_msgs in
#eval (compile_program (.ASSIGN "x" (.PLUS (.VAR "x") (.CONST 1))))

def smart_Ibranch (d : Int) : List instr :=
  if d = 0 then [] else .Ibranch d :: []

/-
  4. First compiler correctness proofs

  To reason about the execution of compiled code, we need to consider
  code sequences `C2` that are at position `pc` in a bigger code
  sequence `C = C1 ++ C2 ++ C3`.  The following predicate
  `code_at C pc C2` does just this.
-/
@[grind] inductive code_at : List instr → Int → List instr → Prop where
  | code_at_intro : ∀ C1 C2 C3 pc,
      pc = codelen C1 ->
      code_at (C1 ++ C2 ++ C3) pc C2

/-
  We show a number of simple lemmas about `instr_at` and `code_at`,
  and annotate them with `@[grind]`, so that `grind` can use them automatically.
-/
@[grind =] theorem codelen_cons :
  ∀ i c, codelen (i :: c) = codelen c + 1 := by grind

@[grind =] theorem codelen_singleton : codelen [i] = 1 := by
  dsimp [codelen]

@[grind =] theorem codelen_app :
  ∀ c1 c2, codelen (c1 ++ c2) = codelen c1 + codelen c2 := by
    intro c1 _
    induction c1 with grind

@[grind =>] theorem instr_a : ∀ i c2 c1 pc,
  pc = codelen c1 ->
  instr_at (c1 ++ (i :: c2) ) pc = .some i := by
    intro i c2 c1 pc
    induction c1 generalizing pc with grind

@[grind] theorem instr_at_app :
  ∀ i c2 c1 pc,
  pc = codelen c1 ->
  instr_at (c1 ++ (i :: c2)) pc = .some i := by
    intro i c2 c1 pc pc_eq
    induction c1 generalizing pc with grind

theorem code_at_head :
  ∀ C pc i C',
  code_at C pc (i :: C') ->
  instr_at C pc = .some i := by
    intro C pc i C'  H
    generalize heq1 : (i :: C') = x
    rw [heq1] at H
    induction H
    case code_at_intro c1 c2 c3 oc a =>
      induction c1 generalizing oc with grind

@[grind] theorem code_at_tail :
   ∀ C pc i C',
  code_at C pc (i :: C') →
  code_at C (pc + 1) C' := by
    intro C pc i C' h
    cases h
    case code_at_intro c1 c3 a =>
      have s : c1 ++ i :: C' ++ c3 = c1 ++ [i] ++ C' ++ c3 := by grind
      grind

@[grind] theorem code_at_app_left :
  ∀ C pc C1 C2,
  code_at C pc (C1 ++ C2) ->
  code_at C pc C1 := by
    intro c pc m1 m2 h
    cases h
    case code_at_intro c1 c3 a =>
      have := code_at.code_at_intro c1 m1 (m2 ++ c3) pc a
      grind

@[grind] theorem code_at_app_right :
  ∀ C pc C1 C2,
  code_at C pc (C1 ++ C2) ->
  code_at C (pc + codelen C1) C2 := by
    intro C pc c1 c2 h
    cases h
    case code_at_intro b e a =>
      have := code_at.code_at_intro (b ++ c1) c2 e (pc + codelen c1) (by grind)
      grind

@[grind] theorem code_at_app_right2 : ∀ C pc C1 C2 C3,
  code_at C pc (C1 ++ C2 ++ C3) →
  code_at C (pc + codelen C1) C2 := by
    intro C pc c1 c2 c3 h
    cases h
    case code_at_intro b e a =>
      have := code_at.code_at_intro (b ++ c1) c2 (c3 ++ e) (pc + codelen c1) (by grind)
      grind

@[grind] theorem code_at_nil : ∀ C pc C1,
  code_at C pc C1 -> code_at C pc [] := by
    intro C pc c1 h
    cases h
    case code_at_intro b e a =>
      have := code_at.code_at_intro b [] (c1 ++ e) pc a
      grind

@[grind] theorem instr_at_code_at_nil :
  ∀ C pc i, instr_at C pc = .some i -> code_at C pc [] := by
    intro C pc i h
    induction C generalizing pc i
    case nil => grind
    case cons f t t_ih =>
      have := code_at.code_at_intro [] [] (f :: t) pc
      grind

@[grind] theorem code_at_to_instr_at : code_at C pc (c1 ++ i :: c2) → instr_at C (pc + codelen c1) = .some i := by
  grind

/-
  4.1 Correctness of generated code for expressions.

  Remember the informal specification we gave for the code generated
  for an arithmetic expression `a`.  It should
  - execute in sequence (no branches)
  - deposit the value of `a` at the top of the stack
  - preserve the variable state.

  We now prove that the code `compile_aexp a` fulfills this contract.
  The proof is a nice induction on the structure of `a`.
-/

theorem compile_aexp_correct (C : List instr) (s : store) (a : aexp) (pc : Int) (stk : stack) :
  code_at C pc (compile_aexp a) →
  transitions C (pc, stk, s) (pc + codelen (compile_aexp a), aeval s a :: stk, s) := by
    induction a generalizing C pc stk
    next =>
      unfold transitions
      grind
    next =>
      intro a
      apply star_one
      grind
    next a1 a2 a1_ih a2_ih =>
      simp [aeval, compile_aexp]
      intro a
      apply star_trans
      · apply a1_ih
        grind
      · apply star_trans
        · apply a2_ih
          grind
        · apply star_one
          cases a
          next c1 c3 a =>
            have h1 := instr_a
            have h2 := @transition.trans_add
            grind
    next a1 a2 a1_ih a2_ih =>
      simp [aeval, compile_aexp]
      intro a
      apply star_trans
      · apply a1_ih
        grind
      · apply star_trans
        · apply a2_ih
          grind
        · apply star_trans
          · apply star_one
            · apply transition.trans_opp
              grind
          · apply star_one
            · have := @code_at_to_instr_at C pc (compile_aexp a1 ++ compile_aexp a2 ++ [instr.Iopp])
              have := @transition.trans_add
              grind

/-
  The proof for the compilation of Boolean expressions is similar.
  We recall the informal specification for the code generated by
  [compile_bexp b d1 d0]: it should
  - skip `d1` instructions if `b` evaluates to true,
       `d0` if `b` evaluates to false
  - leave the stack unchanged
  - leave the store unchanged.
-/
theorem compile_bexp_correct (C : List instr) (s : store) (b : bexp) (d1 d0 : Int) (pc : Int) (stk : stack) (h : code_at C pc (compile_bexp b d1 d0))  :
   transitions C
       (pc, stk, s)
       (pc + codelen (compile_bexp b d1 d0) + (if beval s b then d1 else d0), stk, s) := by sorry
/-
  4.2 Correctness of generated code for commands, terminating case.
-/
theorem compile_com_assign_correct_aux (s : store) (x : ident) (a : aexp) : ∀ C pc stk, code_at C pc (compile_com (.ASSIGN x a)) → transitions C (pc, stk, s) (pc + codelen (compile_com (.ASSIGN x a)), stk, update x (aeval s a) s) := by
  intro C pc stk hcode
  have hA : code_at C pc (compile_aexp a) := by
    simpa [compile_com] using
      (code_at_app_left (C := C) (pc := pc) (C1 := compile_aexp a) (C2 := [instr.Isetvar x]) hcode)
  have hRunA :
      transitions C (pc, stk, s)
        (pc + codelen (compile_aexp a), aeval s a :: stk, s) := by
    exact compile_aexp_correct C s a pc stk hA
  have hInstr :
      instr_at C (pc + codelen (compile_aexp a)) = .some (.Isetvar x) := by
    have hcode' : code_at C pc (compile_aexp a ++ instr.Isetvar x :: []) := by
      simpa [compile_com] using hcode
    simpa using
      (code_at_to_instr_at (C := C) (pc := pc) (c1 := compile_aexp a) (i := instr.Isetvar x) (c2 := []) hcode')
  have hSet :
      transitions C (pc + codelen (compile_aexp a), aeval s a :: stk, s)
        (pc + codelen (compile_aexp a) + 1, stk, update x (aeval s a) s) := by
    apply star_one
    exact transition.trans_setvar (pc := pc + codelen (compile_aexp a))
      (stk := stk) (s := s) (x := x) (n := aeval s a) hInstr
  have h := star_trans (transition C)
      (pc, stk, s)
      (pc + codelen (compile_aexp a), aeval s a :: stk, s)
      hRunA
      (pc + codelen (compile_aexp a) + 1, stk, update x (aeval s a) s)
      hSet
  simpa [compile_com, codelen_app, codelen_singleton, Int.add_assoc] using h

theorem compile_com_ifthenelse_correct_aux (s s' : store) (b : bexp) (c1 c2 : com) (ih : ∀ C pc stk, code_at C pc (compile_com (if beval s b then c1 else c2)) → transitions C (pc, stk, s) (pc + codelen (compile_com (if beval s b then c1 else c2)), stk, s')) : ∀ C pc stk, code_at C pc (compile_com (.IFTHENELSE b c1 c2)) → transitions C (pc, stk, s) (pc + codelen (compile_com (.IFTHENELSE b c1 c2)), stk, s') := by
  intro C pc stk hcode
  let code_ifso := compile_com c1
  let code_ifnot := compile_com c2
  let test := compile_bexp b 0 (codelen code_ifso + 1)
  have hcode' : code_at C pc (test ++ code_ifso ++ [instr.Ibranch (codelen code_ifnot)] ++ code_ifnot) := by
    simpa [compile_com, code_ifso, code_ifnot, test, List.append_assoc] using hcode
  have hcode_left : code_at C pc (test ++ (code_ifso ++ [instr.Ibranch (codelen code_ifnot)] ++ code_ifnot)) := by
    simpa [List.append_assoc] using hcode'
  have hcode_mid : code_at C pc (test ++ code_ifso ++ ([instr.Ibranch (codelen code_ifnot)] ++ code_ifnot)) := by
    simpa [List.append_assoc] using hcode'
  have hcode_branch : code_at C pc ((test ++ code_ifso) ++ instr.Ibranch (codelen code_ifnot) :: code_ifnot) := by
    simpa [List.append_assoc] using hcode'
  have hcode_right : code_at C pc ((test ++ code_ifso ++ [instr.Ibranch (codelen code_ifnot)]) ++ code_ifnot) := by
    simpa [List.append_assoc] using hcode'
  have hTest : code_at C pc test := by
    exact code_at_app_left (C := C) (pc := pc) (C1 := test)
      (C2 := code_ifso ++ [instr.Ibranch (codelen code_ifnot)] ++ code_ifnot) hcode_left
  have hrunTest := compile_bexp_correct C s b 0 (codelen code_ifso + 1) pc stk hTest
  by_cases hb : beval s b = true
  · have hIfso : code_at C (pc + codelen test) code_ifso := by
      exact code_at_app_right2 (C := C) (pc := pc) (C1 := test) (C2 := code_ifso)
        (C3 := [instr.Ibranch (codelen code_ifnot)] ++ code_ifnot) hcode_mid
    have hIfso' : code_at C (pc + codelen test) (compile_com (if beval s b then c1 else c2)) := by
      simpa [hb, code_ifso] using hIfso
    have hrunIfso :
        transitions C (pc + codelen test, stk, s)
          (pc + codelen test + codelen code_ifso, stk, s') := by
      simpa [hb, code_ifso, Int.add_assoc] using (ih C (pc + codelen test) stk hIfso')
    have hInstr0 : instr_at C (pc + codelen (test ++ code_ifso)) = .some (.Ibranch (codelen code_ifnot)) := by
      exact code_at_to_instr_at (C := C) (pc := pc) (c1 := test ++ code_ifso)
        (i := instr.Ibranch (codelen code_ifnot)) (c2 := code_ifnot) hcode_branch
    have hInstr : instr_at C (pc + codelen test + codelen code_ifso) = .some (.Ibranch (codelen code_ifnot)) := by
      simpa [codelen_app, Int.add_assoc] using hInstr0
    have hBranch : transitions C
        (pc + codelen test + codelen code_ifso, stk, s')
        ((pc + codelen test + codelen code_ifso) + 1 + codelen code_ifnot, stk, s') := by
      apply star_one
      exact transition.trans_branch (pc := pc + codelen test + codelen code_ifso)
        (stk := stk) (s := s') (d := codelen code_ifnot)
        (pc' := (pc + codelen test + codelen code_ifso) + 1 + codelen code_ifnot) hInstr rfl
    have htestTrue : transitions C (pc, stk, s) (pc + codelen test, stk, s) := by
      simpa [hb] using hrunTest
    have hfinal : transitions C (pc, stk, s)
        (((pc + codelen test + codelen code_ifso) + 1 + codelen code_ifnot), stk, s') := by
      apply star_trans
      · exact htestTrue
      · apply star_trans
        · exact hrunIfso
        · exact hBranch
    have hpc_true :
        ((pc + codelen test + codelen code_ifso) + 1 + codelen code_ifnot) =
          pc + codelen (compile_com (.IFTHENELSE b c1 c2)) := by
      simp [compile_com, code_ifso, code_ifnot, test, codelen_app, codelen_cons, Int.add_assoc]
      omega
    simpa [hpc_true] using hfinal
  · have hIfnot0 : code_at C (pc + codelen (test ++ code_ifso ++ [instr.Ibranch (codelen code_ifnot)])) code_ifnot := by
      exact code_at_app_right (C := C) (pc := pc)
        (C1 := test ++ code_ifso ++ [instr.Ibranch (codelen code_ifnot)]) (C2 := code_ifnot) hcode_right
    have hIfnot : code_at C (pc + codelen test + (codelen code_ifso + 1)) code_ifnot := by
      simpa [codelen_app, codelen_singleton, Int.add_assoc] using hIfnot0
    have hIfnot' :
        code_at C (pc + codelen test + (codelen code_ifso + 1))
          (compile_com (if beval s b then c1 else c2)) := by
      simpa [hb, code_ifnot] using hIfnot
    have hrunIfnot : transitions C
        (pc + codelen test + (codelen code_ifso + 1), stk, s)
        (pc + codelen test + (codelen code_ifso + 1) + codelen code_ifnot, stk, s') := by
      simpa [hb, code_ifnot, Int.add_assoc] using
        (ih C (pc + codelen test + (codelen code_ifso + 1)) stk hIfnot')
    have htestFalse : transitions C (pc, stk, s) (pc + codelen test + (codelen code_ifso + 1), stk, s) := by
      simpa [hb] using hrunTest
    have hfinal : transitions C (pc, stk, s)
        ((pc + codelen test + (codelen code_ifso + 1) + codelen code_ifnot), stk, s') := by
      apply star_trans
      · exact htestFalse
      · exact hrunIfnot
    have hpc_false :
        (pc + codelen test + (codelen code_ifso + 1) + codelen code_ifnot) =
          pc + codelen (compile_com (.IFTHENELSE b c1 c2)) := by
      simp [compile_com, code_ifso, code_ifnot, test, codelen_app, codelen_cons, Int.add_assoc]
      omega
    simpa [hpc_false] using hfinal

theorem compile_com_seq_correct_aux (s s' s'' : store) (c1 c2 : com) (ih1 : ∀ C pc stk, code_at C pc (compile_com c1) → transitions C (pc, stk, s) (pc + codelen (compile_com c1), stk, s')) (ih2 : ∀ C pc stk, code_at C pc (compile_com c2) → transitions C (pc, stk, s') (pc + codelen (compile_com c2), stk, s'')) : ∀ C pc stk, code_at C pc (compile_com (.SEQ c1 c2)) → transitions C (pc, stk, s) (pc + codelen (compile_com (.SEQ c1 c2)), stk, s'') := by
  intro C pc stk hcode
  have h1 : code_at C pc (compile_com c1) := by
    simpa [compile_com] using
      (code_at_app_left C pc (compile_com c1) (compile_com c2) (by simpa [compile_com] using hcode))
  have h2 : code_at C (pc + codelen (compile_com c1)) (compile_com c2) := by
    simpa [compile_com] using
      (code_at_app_right C pc (compile_com c1) (compile_com c2) (by simpa [compile_com] using hcode))
  have t1 : transitions C (pc, stk, s) (pc + codelen (compile_com c1), stk, s') :=
    ih1 C pc stk h1
  have t2 :
      transitions C (pc + codelen (compile_com c1), stk, s')
        (pc + codelen (compile_com c1) + codelen (compile_com c2), stk, s'') :=
    ih2 C (pc + codelen (compile_com c1)) stk h2
  simpa [transitions, compile_com, codelen_app, Int.add_assoc] using
    (star_trans (transition C) (pc, stk, s) (pc + codelen (compile_com c1), stk, s') t1
      (pc + codelen (compile_com c1) + codelen (compile_com c2), stk, s'') t2)

theorem compile_com_while_done_correct_aux (s : store) (b : bexp) (c : com) (hb : beval s b = false) : ∀ C pc stk, code_at C pc (compile_com (.WHILE b c)) → transitions C (pc, stk, s) (pc + codelen (compile_com (.WHILE b c)), stk, s) := by
  intro C pc stk hcode
  let code_body := compile_com c
  let test := compile_bexp b 0 (codelen code_body + 1)
  have hloop : code_at C pc (test ++ code_body ++ [instr.Ibranch (-(codelen test + codelen code_body + 1))]) := by
    simpa [compile_com, code_body, test, List.append_assoc] using hcode
  have hTest : code_at C pc test := by
    apply code_at_app_left C pc test (code_body ++ [instr.Ibranch (-(codelen test + codelen code_body + 1))])
    simpa [List.append_assoc] using hloop
  have htrans :
      transitions C (pc, stk, s)
        (pc + codelen test + (if beval s b then 0 else codelen code_body + 1), stk, s) :=
    compile_bexp_correct C s b 0 (codelen code_body + 1) pc stk hTest
  simpa [compile_com, code_body, test, codelen_app, codelen_singleton, Int.add_assoc, hb] using htrans

theorem compile_com_while_loop_correct_aux (s s' s'' : store) (b : bexp) (c : com) (hcond : beval s b = true) (ih_body : ∀ C pc stk, code_at C pc (compile_com c) → transitions C (pc, stk, s) (pc + codelen (compile_com c), stk, s')) (ih_while : ∀ C pc stk, code_at C pc (compile_com (.WHILE b c)) → transitions C (pc, stk, s') (pc + codelen (compile_com (.WHILE b c)), stk, s'')) : ∀ C pc stk, code_at C pc (compile_com (.WHILE b c)) → transitions C (pc, stk, s) (pc + codelen (compile_com (.WHILE b c)), stk, s'') := by
  intro C pc stk hcode
  let code_body := compile_com c
  let test := compile_bexp b 0 (codelen code_body + 1)
  let back : Int := -(codelen test + codelen code_body + 1)
  have hcode' : code_at C pc (test ++ code_body ++ [instr.Ibranch back]) := by
    simpa [compile_com, code_body, test, back, List.append_assoc] using hcode
  have hcode'' : code_at C pc (test ++ (code_body ++ [instr.Ibranch back])) := by
    simpa [List.append_assoc] using hcode'
  have hTest : code_at C pc test := by
    exact code_at_app_left C pc test (code_body ++ [instr.Ibranch back]) hcode''
  have hTestRun : transitions C (pc, stk, s) (pc + codelen test, stk, s) := by
    simpa [test, hcond] using
      (compile_bexp_correct C s b 0 (codelen code_body + 1) pc stk hTest)
  have hBody : code_at C (pc + codelen test) code_body := by
    exact code_at_app_right2 C pc test code_body [instr.Ibranch back] hcode'
  have hBodyRun : transitions C (pc + codelen test, stk, s)
      (pc + codelen test + codelen code_body, stk, s') := by
    simpa [code_body] using ih_body C (pc + codelen test) stk hBody
  have hBranchInstr' : instr_at C (pc + codelen (test ++ code_body)) = .some (instr.Ibranch back) := by
    apply code_at_to_instr_at
    simpa using hcode'
  have hBranchInstr : instr_at C (pc + codelen test + codelen code_body) = .some (instr.Ibranch back) := by
    simpa [codelen_app, Int.add_assoc] using hBranchInstr'
  have hBackRun : transitions C (pc + codelen test + codelen code_body, stk, s') (pc, stk, s') := by
    apply star_one
    apply transition.trans_branch
    · exact hBranchInstr
    · dsimp [back]
      omega
  apply star_trans
  · exact hTestRun
  · apply star_trans
    · exact hBodyRun
    · apply star_trans
      · exact hBackRun
      · exact ih_while C pc stk hcode

theorem compile_com_correct_terminating (s s' : store) (c : com) (h₁ : cexec s c s') :
 ∀ C pc stk, code_at C pc (compile_com c) →
  transitions C
      (pc, stk, s)
      (pc + codelen (compile_com c), stk, s') := by
  intro C pc stk hcode
  induction h₁ generalizing C pc stk with
  | cexec_skip =>
      rename_i s0
      unfold transitions
      simpa [compile_com, codelen] using (star.star_refl (R := transition C) (x := (pc, stk, s0)))
  | cexec_assign =>
      rename_i s0 x a
      exact compile_com_assign_correct_aux s0 x a C pc stk hcode
  | cexec_seq =>
      rename_i s0 c1 s1 c2 s2 h1 h2 ih1 ih2
      exact compile_com_seq_correct_aux s0 s1 s2 c1 c2 ih1 ih2 C pc stk hcode
  | cexec_ifthenelse =>
      rename_i s0 b c1 c2 s1 h ih
      exact compile_com_ifthenelse_correct_aux s0 s1 b c1 c2 ih C pc stk hcode
  | cexec_while_done =>
      rename_i s0 b c hfalse
      exact compile_com_while_done_correct_aux s0 b c hfalse C pc stk hcode
  | cexec_while_loop =>
      rename_i s0 b c s1 s2 htrue hbody hwhile ih1 ih2
      exact compile_com_while_loop_correct_aux s0 s1 s2 b c htrue ih1 ih2 C pc stk hcode


/-
  7.  Full proof of compiler correctness

  We would like to strengthen the correctness result above so that it
  is not restricted to terminating source programs, but also applies to
  source program that diverge.  To this end, we abandon the big-step
  semantics for commands and switch to the small-step semantics with
  continuations.  We then show a simulation theorem, establishing that
  every transition of the small-step semantics in the source program
  is simulated (in a sense to be made precise below) by zero, one or
  several transitions of the machine executing the compiled code for
  the source program.

  Our first task is to relate configurations `(c, k, s)` of the small-step
  semantics with configurations `(C, pc, stk, s)` of the machine.
  We already know how to relate a command `c` with the machine code,
  using the `codeseq_at` predicate.  What needs to be defined is a relation
  between the continuation `k` and the machine code.

  Intuitively, when the machine finishes executing the generated code for
  command `c`, that is, when it reaches the program point
  `pc + codelen(compile_com c)`, the machine should continue by executing
  instructions that perform the pending computations described by
  continuation `k`, then reach an `.Ihalt` instruction to stop cleanly.

  We formalize this intution by the following inductive predicate
  `compile_cont C k pc`, which states that, starting at program point `pc`,
  there are instructions that perform the computations described in `k`
  and reach an `.Ihalt` instruction.
-/
inductive compile_cont (C : List instr) : cont -> Int -> Prop where
  | ccont_stop : ∀ pc,
      instr_at C pc = .some .Ihalt ->
      compile_cont C .Kstop pc
  | ccont_seq : ∀ c k pc pc',
      code_at C pc (compile_com c) ->
      pc' = pc + codelen (compile_com c) ->
      compile_cont C k pc' ->
      compile_cont C (.Kseq c k) pc
  | ccont_while : ∀ b c k pc d pc' pc'',
      instr_at C pc = .some (.Ibranch d) ->
      pc' = pc + 1 + d ->
      code_at C pc' (compile_com (.WHILE b c)) ->
      pc'' = pc' + codelen (compile_com (.WHILE b c)) ->
      compile_cont C k pc'' ->
      compile_cont C (.Kwhile b c k) pc
  | ccont_branch : ∀ d k pc pc',
      instr_at C pc = .some (.Ibranch d) ->
      pc' = pc + 1 + d ->
      compile_cont C k pc' ->
      compile_cont C k pc
/-
  Then, a configuration `(c,k,s)` of the small-step semantics matches
  a configuration `(C, pc, stk, s')` of the machine if the following conditions hold:
  - The stores are identical: `s' = s`.
  - The machine stack is empty: `stk = []]`.
  - The machine code at point `pc` is the compiled code for `c`:
  `code_at C pc (compile_com c)`.
  - The machine code at point `pc + codelen (compile_com c)` matches continuation
  `k`, in the sense of `compile_cont` above.
-/
inductive match_config (C : List instr) : com × cont × store -> config -> Prop where
  | match_config_intro : ∀ c k st pc,
      code_at C pc (compile_com c) ->
      compile_cont C k (pc + codelen (compile_com c)) ->
      match_config C (c, k, st) (pc, [], st)

/-
  We are now ready to prove the expected simulation property.
  Since some transitions in the source command correspond to zero transitions
  in the compiled code, we need a simulation diagram of the "star" kind.
                      match_config
     c / k / st  ----------------------- machconfig
       |                                   |
       |                                   | + or ( * and |c',k'| < |c,k| )
       |                                   |
       v                                   v
    c' / k' / st' ----------------------- machconfig'
                      match_config

  Note the stronger conclusion on the right:
  - either the virtual machine does one or several transitions
  - or it does zero, one or several transitions, but the size of the `c,k`
  pair decreases strictly.

  It would be equivalent to state:
  - either the virtual machine does one or several transitions
  - or it does zero transitions, but the size of the `c,k` pair decreases strictly.

  However, the formulation above, with the "star" case, is often more convenient.

  Finding an appropriate "anti-stuttering" measure is a bit of a black art.
  After trial and error, we find that the following measure works.  It is
  the sum of the sizes of the command `c` under focus and all the commands
  appearing in the continuation `k`.
-/
def com_size (c : com) : Nat :=
  match c with
  | .SKIP => 1
  | .ASSIGN _ _ => 1
  | (c1 ;; c2) => (com_size c1 + com_size c2 + 1)
  | .IFTHENELSE _ c1 c2 => (com_size c1 + com_size c2 + 1)
  | .WHILE _ c1 => (com_size c1 + 1)

theorem com_size_nonzero : ∀ c, (com_size c > 0) := by
  intro c
  fun_induction com_size with grind

def cont_size (k : cont) : Nat :=
  match k with
  | .Kstop => 0
  | .Kseq c k' => (com_size c + cont_size k')
  | .Kwhile _ _ k' => cont_size k'

def measure' (impconf : com × cont × store) : Nat :=
  match impconf with
  | (c, k, _) => (com_size c + cont_size k)

/-
  A few technical lemmas to help with the simulation proof.
-/
theorem compile_cont_Kstop_inv (C : List instr) (pc : Int) (s : store) :
  compile_cont C .Kstop pc →
  ∃ pc',
  star (transition C) (pc, [], s) (pc', [], s)
  ∧ instr_at C pc' = .some .Ihalt := by
    intro H
    generalize h₁ : cont.Kstop = a₁
    generalize h₂ : pc = a₂
    rw [h₁, h₂] at H
    induction H generalizing pc with grind

theorem compile_cont_Kseq_inv (C : List instr) (c : com) (k :cont) (pc : Int) (s : store) (H : compile_cont C (.Kseq c k) pc) :
  ∃ pc',
  star (transition C) (pc, [], s) (pc', [], s)
  ∧ code_at C pc' (compile_com c)
  ∧ compile_cont C k (pc' + codelen (compile_com c)) := by
    generalize h₁ : (cont.Kseq c k) = a₁
    generalize h₂ : pc = a₂
    rw [h₁, h₂] at H
    induction H generalizing pc k with grind

theorem compile_cont_Kwhile_inv (C : List instr) (b : bexp) (c : com) (k : cont) (pc : Int) (s : store) (H : compile_cont C (.Kwhile b c k) pc) :
  ∃ pc',
  plus (transition C) (pc, [], s) (pc', [], s)
  ∧ code_at C pc' (compile_com (.WHILE b c))
  ∧ compile_cont C k (pc' + codelen (compile_com (.WHILE b c))) := by
    generalize h₁ : (cont.Kwhile b c k) = a₁
    generalize h₂ : pc = a₂
    rw [h₁, h₂] at H
    induction H generalizing pc k
    any_goals grind
    case ccont_branch d k' pc₂ pc₃ h₃ h₄ h₅ ih =>
      specialize ih k pc₃ h₁ rfl
      apply Exists.elim ih
      intro pc₄ ih
      exists pc₄
      apply And.intro
      · rw [h₄] at ih
        rw [←h₂]
        rw [←h₂] at ih
        apply plus.plus_left
        rotate_left
        · apply plus_star
          exact ih.1
        · apply transition.trans_branch
          rotate_left
          · exact rfl
          · grind
      · grind

theorem match_config_skip (C : List instr) (k : cont) (s : store) (pc : Int) (H : compile_cont C k pc) :
 match_config C (.SKIP, k, s) (pc, [], s) := by
  constructor
  · cases H <;> grind
  · grind

/-
  At last, we can state and prove the simulation diagram.
-/
theorem simulation_step :
  ∀ C impconf1 impconf2 machconf1,
  step impconf1 impconf2 ->
  match_config C impconf1 machconf1 ->
  ∃ machconf2,
      (plus (transition C) machconf1 machconf2
       \/ (star (transition C) machconf1 machconf2
           /\ (measure' impconf2 < measure' impconf1)))
   /\ match_config C impconf2 machconf2 := by sorry

/-
  The hard work is done!  Nice consequences will follow.

  First, we get an alternate proof of `compile_program_correct_terminating`,
  using the continuation semantics instead of the big-step semantics
  to characterize termination of the source program.
-/
theorem simulation_steps :
  ∀ C impconf1 impconf2, star step impconf1 impconf2 ->
  ∀ machconf1, match_config C impconf1 machconf1 ->
  ∃ machconf2,
     star (transition C) machconf1 machconf2
  /\ match_config C impconf2 machconf2 := by
      intro C impconf1 impconf2 STAR machconf1 MATCH
      induction STAR generalizing machconf1
      case star_refl x =>
        exists machconf1
        constructor
        · apply star.star_refl
        · exact MATCH
      case star_step x y z STEP STAR ih =>
        have ⟨ machconf2, steps2, match2 ⟩ := simulation_step C x y machconf1 STEP MATCH
        specialize ih machconf2 match2
        rcases ih with ⟨ machconf3, steps3, match3⟩
        exists machconf3
        have w : star (transition C) machconf1 machconf2 := by
          cases steps2
          case inl h =>
            apply plus_star
            exact h
          case inr h =>
            exact h.1
        constructor
        · apply star_trans
          · exact w
          · exact steps3
        · exact match3

theorem instr_at_len : instr_at (C ++ [i]) (codelen C) = .some i := by
  induction C with grind

theorem match_initial_configs :
  ∀ c s,
  match_config (compile_program c) (c, .Kstop, s) (0, [], s) := by
    intro c s
    generalize heq : compile_com c = C
    constructor
    · simp [compile_program]
      have := code_at.code_at_intro [] C [instr.Ihalt] 0 (by simp [codelen])
      grind
    · simp [compile_program, heq]
      constructor
      grind

theorem compile_program_correct_terminating_2 :
  ∀ c s s',
  star step (c, .Kstop, s) (.SKIP, .Kstop, s') ->
  machine_terminates (compile_program c) s s' := by
    intro c s s' STAR
    generalize heq : compile_program c = C
    have ⟨ ms, A, B ⟩ := simulation_steps C (c, cont.Kstop, s) (com.SKIP, cont.Kstop, s') STAR (0, [], s) (by grind [match_initial_configs])
    cases B
    case match_config_intro pc w1 w2 =>
      have ⟨pc', D, E ⟩ := compile_cont_Kstop_inv C (pc + codelen (compile_com com.SKIP)) s' w2
      exists pc'
      constructor
      · apply star_trans
        · exact A
        · simp [compile_com, codelen] at D
          exact D
      · exact E

/-
  Second, and more importantly, we get a proof of semantic preservation
  for diverging source programs: if the program makes infinitely many steps,
  the generated code makes infinitely many machine transitions.
-/
theorem simulation_infseq_inv :
  ∀ C n impconf1 machconf1,
  infseq step impconf1 -> match_config C impconf1 machconf1 ->
  (measure' impconf1 < n) ->
  ∃ impconf2 machconf2,
      infseq step impconf2
   /\ plus (transition C) machconf1 machconf2
   /\ match_config C impconf2 machconf2 := by
    intro C n impconf1 h1 h2 h3 h4
    induction n generalizing impconf1 h1
    case zero => contradiction
    case succ n' ih =>
      rw [infseq] at h2
      rcases h2 with ⟨impconf2 , STEP, INFSEQ⟩
      have ⟨ machconf2, h5 , h6 ⟩ := simulation_step C impconf1 impconf2 h1 STEP h3
      cases h5
      next PLUS =>
        exists impconf2
        exists machconf2
      next w =>
        rcases w with ⟨ STAR, MEASURE ⟩
        specialize ih impconf2 machconf2 INFSEQ h6 (by omega)
        rcases ih with ⟨ c1, m1, w⟩
        exists c1
        exists m1
        constructor
        · exact w.1
        · constructor
          · apply star_plus_trans
            · exact STAR
            · exact w.2.1
          · exact w.2.2

theorem compile_program_correct_diverging :
  ∀ c s,
  infseq step (c, .Kstop, s) ->
  machine_diverges (compile_program c) s := by
    intro c s H
    generalize heq : compile_program c = C
    unfold machine_diverges
    apply infseq_coinduction_principle_2 (fun machconf => ∃ impconf, infseq step impconf /\ match_config C impconf machconf)
    rotate_left
    · exists (c, .Kstop, s)
      constructor
      · exact H
      · have := match_initial_configs c s
        grind
    · intro machconf ⟨ impconf , ⟨INFSEQ, MATCH ⟩⟩
      have ⟨impconf2 , machconf2, INFSEQ2 , PLUS , MATCH2⟩  := simulation_infseq_inv C (measure' impconf +1) impconf machconf INFSEQ MATCH (by omega)
      exists machconf2
      constructor
      · exact PLUS
      · exists impconf2
