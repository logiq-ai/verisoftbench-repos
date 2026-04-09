-- algebraic data types exercises

/-
Define queue operations on lists.

Then, prove algebraic properties of queue operations.
If your proof gets stuck, your implementation of some operation might be incorrect.
-/

open List  -- use Lean 4's `List`

def empty {α : Type u} : List α :=
  []

def is_empty (q : List α) : Bool :=
  match q with
  | [] => true
  | _ :: _ => false

def enqueue (q : List α) (x : α) : List α :=
  match q with
  | [] => [x]
  | head :: tail => head :: enqueue tail x

def peek (default : α) (q : List α) : α :=
  match q with
  | [] => default
  | head :: _ => head

def dequeue (q : List α) : List α :=
  match q with
  | [] => []
  | _ :: tail => tail

theorem is_empty_empty : is_empty (@empty α) := by
  rfl

theorem is_empty_nonempty (q : List α) (x : α)
    : is_empty (enqueue q x) = false := by
  induction q with
  | nil => rfl
  | cons _ _ ih => simp [enqueue, is_empty, ih]

theorem peek_empty (d : α) : peek d empty = d := by
  rfl

theorem peek_nonempty (d x : α) (q : List α)  --Hard
    : peek d (enqueue q x) = peek x q := by
  induction q with
  | nil => rfl
  | cons head _ ih => simp [enqueue, peek, ih]

theorem dequeue_empty : dequeue (@empty α) = empty := by
  rfl

theorem dequeue_nonempty (x : α) (q : List α) --Hard
    : dequeue (enqueue q x) = if is_empty q then q else enqueue (dequeue q) x := by
  induction q with
  | nil => rfl
  | cons head _ ih => simp [enqueue, dequeue, is_empty, ih]
