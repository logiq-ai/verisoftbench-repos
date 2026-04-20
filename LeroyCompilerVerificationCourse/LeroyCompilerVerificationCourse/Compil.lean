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
theorem compile_bexp_correct (C : List instr) (s : store) (b : bexp) (d1 d0 : Int) (pc : Int) (stk : stack) (h : code_at C pc (compile_bexp b d1 d0)) : transitions C (pc, stk, s) (pc + codelen (compile_bexp b d1 d0) + (if beval s b then d1 else d0), stk, s) := by
  -- Primary strategy: prove the theorem by structural induction on `b`, generalizing `C`, `pc`, and `stk`, exactly in the style of `compile_aexp_correct`.
  -- 
  -- Main lemmas/results to use:
  -- - `compile_aexp_correct`
  -- - `star_one`
  -- - `star_trans`
  -- - `code_at_app_left`, `code_at_app_right`, `code_at_app_right2`
  -- - `code_at_to_instr_at`
  -- - `codelen_app`, `codelen_singleton`
  -- - constructors `transition.trans_branch`, `transition.trans_beq`, `transition.trans_ble`
  -- 
  -- Suggested proof skeleton:
  -- 1. `induction b generalizing C pc stk`.
  -- 2. For each case, `simp [compile_bexp, beval]` (and `codelen_app` / `Int.add_assoc` when needed), then introduce the `code_at` hypothesis.
  -- 
  -- Case details:
  -- - `TRUE`:
  --   Do `by_cases hd1 : d1 = 0`.
  --   * If `hd1`, then `compile_bexp .TRUE d1 d0 = []`, so the goal is reflexive: `unfold transitions`; `grind`.
  --   * Otherwise the code is `[instr.Ibranch d1]`; use `star_one`, then `transition.trans_branch`. `grind` should recover `instr_at C pc = .some (.Ibranch d1)` from the `code_at` hypothesis (or use `code_at_head`/`cases h` if needed). The target pc is `pc + 1 + d1`.
  -- 
  -- - `FALSE`:
  --   Same argument, but split on `d0 = 0` and use `.Ibranch d0`.
  -- 
  -- - `EQUAL a1 a2`:
  --   The compiled code is `compile_aexp a1 ++ compile_aexp a2 ++ [instr.Ibeq d1 d0]`.
  --   Use `star_trans` three times:
  --   * first `compile_aexp_correct` for `a1` at `(pc, stk, s)`;
  --   * then `compile_aexp_correct` for `a2` at `(pc + codelen (compile_aexp a1), aeval s a1 :: stk, s)`;
  --   * finally one step with `transition.trans_beq`.
  --   For the last step, obtain the branch instruction with
  --   `have := @code_at_to_instr_at C pc (compile_aexp a1 ++ compile_aexp a2) (instr.Ibeq d1 d0) []`.
  --   Then `grind` / `simp [codelen_app, Int.add_assoc]` should close the arithmetic and boolean rewriting.
  -- 
  -- - `LESSEQUAL a1 a2`:
  --   Exactly the same pattern as `EQUAL`, ending with `transition.trans_ble`.
  -- 
  -- - `NOT b1`:
  --   `compile_bexp (.NOT b1) d1 d0 = compile_bexp b1 d0 d1`. Apply the IH with swapped jump distances and finish with
  --   `simpa [compile_bexp, beval]`.
  --   If the boolean simplification does not fire immediately, rewrite `if beval s b1 then d0 else d1` vs `if !(beval s b1) then d1 else d0` by cases on `beval s b1`.
  -- 
  -- - `AND b1 b2`:
  --   Let
  --   `code2 := compile_bexp b2 d1 d0`
  --   and
  --   `code1 := compile_bexp b1 0 (codelen code2 + d0)`.
  --   The whole code is `code1 ++ code2`.
  -- 
  --   First apply the IH for `b1` to `code1`, obtaining
  --   `transitions C (pc, stk, s)
  --       (pc + codelen code1 + (if beval s b1 then 0 else codelen code2 + d0), stk, s)`.
  -- 
  --   Now split on `hb1 : beval s b1 = true`.
  --   * If `hb1`, rewrite the first result to land at `(pc + codelen code1, stk, s)`. From the original `code_at` hypothesis for `code1 ++ code2`, get `code_at C (pc + codelen code1) code2` using `code_at_app_right`. Then apply the IH for `b2` starting from this new pc. Finish with
  --     `simpa [code1, code2, hb1, codelen_app, Int.add_assoc]`.
  --   * If `hb1 = false`, the first IH already jumps over `code2` by exactly `codelen code2 + d0`; finish with
  --     `simpa [code1, code2, hb1, codelen_app, Int.add_assoc]`.
  -- 
  -- Sanity check / disproof check:
  -- - The statement is consistent with the operational behavior of every constructor.
  -- - The only subtle point is `AND`: when `b1 = false`, the compiled code for `b1` must skip over all of `code2` and then apply the false offset `d0`; this is exactly why the false branch of `code1` is `codelen code2 + d0`. So no obvious counterexample.
  -- 
  -- Alternative tactics:
  -- - In `TRUE`/`FALSE`, instead of relying on `grind` to recover `instr_at`, you can `cases h` and use `instr_a` directly.
  -- - In `AND`, `cases hb1 : beval s b1` is equivalent to `by_cases hb1 : beval s b1 = true` if the boolean normalization behaves better that way.
  sorry

/-
  4.2 Correctness of generated code for commands, terminating case.
-/
theorem compile_com_correct_terminating (s s' : store) (c : com) (h₁ : cexec s c s') :
 ∀ C pc stk, code_at C pc (compile_com c) →
  transitions C
      (pc, stk, s)
      (pc + codelen (compile_com c), stk, s') := by sorry

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
