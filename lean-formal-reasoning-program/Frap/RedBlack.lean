/-
## Red-black trees

Red-black trees are balanced binary search trees.
Each node is either red or black.
The empty node is assumed to be black.
-/

inductive Color where
  | red
  | black

inductive Tree (α : Type u) where
  | empty  : Tree α
  | tree (c: Color) (l : Tree α) (k : Nat) (v : α) (r : Tree α) : Tree α

namespace Tree
open Color

def ex_tree : Tree String :=
  tree black (tree red empty 2 "two" empty) 4 "four" (tree red empty 5 "five" empty)

def empty_tree {α : Type u} : Tree α := empty

/-
`contains` and `lookup` operations work like before.
-/

def contains {α : Type u} (x : Nat) (t : Tree α) : Bool :=
  match t with
  | empty => false
  | tree _ l k _ r =>
      if x < k then contains x l
      else if x > k then contains x r
      else true

def lookup {α : Type u} (d : α) (x : Nat) (t : Tree α) : α :=
  match t with
  | empty => d
  | tree _ l k v r =>
      if x < k then lookup d x l
      else if x > k then lookup d x r
      else v

/-
## Red-black tree properties

To maintain balance, red-black trees maintain two invariants:
1. No red node has a red parent, i.e., no two consecutive red nodes in a tree.
2. Every path from the root node to leaf contains the same number of black nodes.

These invariants ensure that the height of a red-black tree is logarithmic in the number of nodes, as the longest possible path from root (alternating colors) is no more than twice as long as the shortet path (black nodes only).

## Insertion

During an `insert` operation, these invariants may be invalidated.
Therefore, we need to keep the newly modified subtree balanced.
This is done by the `balance` function.
-/

def balance {α : Type u} (c : Color) (l : Tree α) (k : Nat) (vk : α) (r : Tree α) : Tree α :=
  match c with
  | red => tree red l k vk r
  | black =>
    match (l, k, vk, r) with
    | (tree red (tree red a x vx b) y vy c, z, vz, d)
    | (tree red a x vx (tree red b y vy c), z, vz, d)
    | (a, x, vx, tree red (tree red b y vy c) z vz d)
    | (a, x, vx, tree red b y vy (tree red c z vz d))
        => tree red (tree black a x vx b) y vy (tree black c z vz d)
    | _ => tree black l k vk r

/-
The main work is done in the `ins` function, which is like insertion on unbalanced binary search trees, but with two differences:
1. The new node is colored red.
2. We apply `balance` before returning the result.

By coloring the new node red, we maintain Invariant 2, but we might be violating Invariant 1.
The `balance` function above inspects whether there are a red child and a red grandchild on the same path from the black root node.
Four cases are possible.
In such cases, the tree is rebuilt accordingly, to maintain binary search tree property and reestablish red-black tree invariants.
-/

def ins {α : Type u} (x : Nat) (vx : α) (t : Tree α) : Tree α :=
  match t with
  | empty => tree red empty x vx empty
  | tree c l k vk r =>
      if x < k then balance c (ins x vx l) k vk r
      else if x > k then balance c l k vk (ins x vx r)
      else tree c l x vx r  -- update value

/-
Finally, when we are back at the root, it is possible that the root node itself is red, which might still violate Invariant 1.
To fix this, we simply recolor the root node to black.
Thus, the entire insertion operation entails calling `ins` function above, and then make the resulting root black.
-/

def make_black {α : Type u} (t : Tree α) : Tree α :=
  match t with
  | empty => empty
  | tree _ l k vk r => tree black l k vk r

def insert {α : Type u} (x : Nat) (vx : α) (t : Tree α) : Tree α :=
  make_black (ins x vx t)

attribute [local simp]
  contains lookup balance ins make_black insert

/-
Now we are ready to prove properties on red-black trees.
First, we prove that the result of insertion is not the empty tree.
-/

theorem ins_not_empty {α : Type u} (k : Nat) (vk : α) (t : Tree α)
    : ins k vk t ≠ empty := by
  cases t with simp
  | tree c l k' _ r =>
    split  -- k < k'
    . split  -- c
      . simp
      . split  -- (ins k vk l, k', v✝, r)
        . simp
        . simp
        . simp
        . simp
        . simp
    . split  -- k > k'
      . split  -- c
        . simp
        . split  -- (l, k', v✝, ins k vk r)
          . simp
          . simp
          . simp
          . simp
          . simp
      . simp

/-
We can see that the prove above is quite mundane: `split` until we can't, and then simplify.
We can shorten the proof by using the `repeat'` _tactic combinator_.
`repeat' t` applies tactic `t` repeatedly and recursively to each subgoal generated until it can't.
-/

example {α : Type u} (k : Nat) (vk : α) (t : Tree α)
    : ins k vk t ≠ empty := by
  cases t with simp
  | tree c l k' _ r =>
    (repeat' split) <;> simp

/-
Once again, we define an inductive predicate stating that a given predicate holds for a tree when the predicate holds for every node of the tree.
-/

inductive ForallTree {α : Type u} (p : Nat → α → Prop) : Tree α → Prop where
  | empty : ForallTree p empty
  | tree : ∀ c l k v r,
      p k v → ForallTree p l → ForallTree p r
      → ForallTree p (tree c l k v r)

/-
Now, we define the _binary search tree_ property.
-/

inductive BST {α : Type u} : Tree α → Prop where
  | empty : BST empty
  | tree : ∀ c l k v r,
      ForallTree (fun x _ => x < k) l
      → ForallTree (fun x _ => x > k) r
      → BST l
      → BST r
      → BST (tree c l k v r)

/-
We show that the example tree satisfies the BST property.
-/

example : BST ex_tree := by
  constructor <;> constructor <;> constructor <;> constructor

example : BST ex_tree := by
  repeat' constructor

/-
The empty tree satisfies the BST property trivially.
-/

theorem empty_tree_BST {α : Type u} : BST (@empty α) := by
  constructor

/-
Now, we would like to prove that the `balance` operation establishes the BST property.
We might start as follows.
-/

example {α : Type u} c (l : Tree α) k vk (r : Tree α)
    : ForallTree (fun x _ => x < k) l
      -> ForallTree (fun x _ => x > k) r
      -> BST l
      -> BST r
      -> BST (balance c l k vk r) := by
  intro hlk hkr hbl hbr; simp
  split
  . constructor <;> assumption
  . split
    . -- we are in the case where `x` is left child of `y`
      /-
      In the hypothesis, we see that `l` must be a tree such that its left-left nodes are both red.
      We perform case analysis on `l`, which takes care of the impossible case when `l` is empty.
      -/
      cases l <;> repeat simp [*] at *
      /-
      Here, we see that we need to further perform cases analysis on the left subtree of `l`.
      In other words, we need to destruct `l` recursively.
      The tactics we know so far don't quite accommodate this just yet.

      The `all_goals` tactic combinator applies the given tactic to all the remaining goals in context.
      Here, we simply abort the remaining proof.
      -/
      all_goals sorry
    all_goals sorry
  all_goals sorry

theorem forallTree_imp {α : Type u} (P Q : Nat → α → Prop) t
    : ForallTree P t → (∀ k v, P k v → Q k v) → ForallTree Q t := by
  intro hp ha
  induction t with
  | empty => constructor
  | tree =>
    cases hp
    constructor <;> simp [*]

theorem forallTree_lt {α : Type u} (t : Tree α) k k'
    : ForallTree (fun x _ => x < k) t → k < k'
      → ForallTree (fun x _ => x < k') t := by
  intro h hlt
  apply forallTree_imp <;> try assumption
  omega

theorem forallTree_gt {α : Type u} (t : Tree α) k k'
    : ForallTree (fun x _ => x > k) t → k > k'
      → ForallTree (fun x _ => x > k') t := by
  intro h hgt
  apply forallTree_imp <;> try assumption
  omega

/-
To recursively destruct an inductively defined object, we can use the `rcases` tactic.
We can give names to parameters in each case, so that we can refer to them later.
-/

theorem ForallTree_gt_mono {α : Type _} {t : Tree α} {x y : Nat} : x < y -> ForallTree (fun z _ => z > y) t -> ForallTree (fun z _ => z > x) t := by
  intro hxy h
  exact forallTree_gt t y x h hxy

theorem ForallTree_lt_mono {α : Type _} {t : Tree α} {x y : Nat} : x < y -> ForallTree (fun z _ => z < x) t -> ForallTree (fun z _ => z < y) t := by
  intro hxy h
  exact forallTree_lt t x y h hxy

theorem balance_black_left_left_BST {α : Type _} (a b c d : Tree α) (x y z : Nat) (vx vy vz : α) : ForallTree (fun t _ => t < z) (tree red (tree red a x vx b) y vy c) -> ForallTree (fun t _ => t > z) d -> BST (tree red (tree red a x vx b) y vy c) -> BST d -> BST (balance black (tree red (tree red a x vx b) y vy c) z vz d) := by
  intro hlt hgt hbstl hbstd
  simp only [balance]
  cases hlt with
  | tree _ _ _ _ _ hyz _ hcz =>
    cases hbstl with
    | tree _ _ _ _ _ hleft_lt_y hc_gt_y hbst_left hbst_c =>
      cases hleft_lt_y with
      | tree _ _ _ _ _ hxy hay hby =>
        cases hbst_left with
        | tree _ _ _ _ _ ha_lt_x hb_gt_x hbst_a hbst_b =>
          constructor
          · constructor
            · exact hxy
            · exact hay
            · exact hby
          · constructor
            · exact hyz
            · exact hc_gt_y
            · exact ForallTree_gt_mono hyz hgt
          · constructor
            · exact ha_lt_x
            · exact hb_gt_x
            · exact hbst_a
            · exact hbst_b
          · constructor
            · exact hcz
            · exact hgt
            · exact hbst_c
            · exact hbstd

theorem balance_black_left_right_BST {α : Type _} (a b c d : Tree α) (x y z : Nat) (vx vy vz : α) : ForallTree (fun t _ => t < z) (tree red a x vx (tree red b y vy c)) -> ForallTree (fun t _ => t > z) d -> BST (tree red a x vx (tree red b y vy c)) -> BST d -> BST (balance black (tree red a x vx (tree red b y vy c)) z vz d) := by
  intro hlz hdz hbstl hbstd
  cases a with
  | empty =>
      cases hbstl with
      | tree _ _ _ _ _ hax_lt_x hbc_gt_x hbsta hbstbc =>
          cases hbstbc with
          | tree _ _ _ _ _ hb_lt_y hc_gt_y hbstb hbstc =>
              cases hbc_gt_x with
              | tree _ _ _ _ _ hxy hb_gt_x hc_gt_x =>
                  cases hlz with
                  | tree _ _ _ _ _ hx_lt_z ha_lt_z hbc_lt_z =>
                      cases hbc_lt_z with
                      | tree _ _ _ _ _ hy_lt_z hb_lt_z hc_lt_z =>
                          simp only [balance]
                          constructor
                          · constructor
                            · exact hxy
                            · exact ForallTree_lt_mono hxy hax_lt_x
                            · exact hb_lt_y
                          · constructor
                            · exact hy_lt_z
                            · exact hc_gt_y
                            · exact ForallTree_gt_mono hy_lt_z hdz
                          · constructor
                            · exact hax_lt_x
                            · exact hb_gt_x
                            · exact hbsta
                            · exact hbstb
                          · constructor
                            · exact hc_lt_z
                            · exact hdz
                            · exact hbstc
                            · exact hbstd
  | tree ca a1 x1 va a2 =>
      cases ca with
      | red =>
          exact balance_black_left_left_BST
            (a := a1) (b := a2) (c := tree red b y vy c) (d := d)
            (x := x1) (y := x) (z := z) (vx := va) (vy := vx) (vz := vz)
            hlz hdz hbstl hbstd
      | black =>
          cases hbstl with
          | tree _ _ _ _ _ hax_lt_x hbc_gt_x hbsta hbstbc =>
              cases hbstbc with
              | tree _ _ _ _ _ hb_lt_y hc_gt_y hbstb hbstc =>
                  cases hbc_gt_x with
                  | tree _ _ _ _ _ hxy hb_gt_x hc_gt_x =>
                      cases hlz with
                      | tree _ _ _ _ _ hx_lt_z ha_lt_z hbc_lt_z =>
                          cases hbc_lt_z with
                          | tree _ _ _ _ _ hy_lt_z hb_lt_z hc_lt_z =>
                              simp only [balance]
                              constructor
                              · constructor
                                · exact hxy
                                · exact ForallTree_lt_mono hxy hax_lt_x
                                · exact hb_lt_y
                              · constructor
                                · exact hy_lt_z
                                · exact hc_gt_y
                                · exact ForallTree_gt_mono hy_lt_z hdz
                              · constructor
                                · exact hax_lt_x
                                · exact hb_gt_x
                                · exact hbsta
                                · exact hbstb
                              · constructor
                                · exact hc_lt_z
                                · exact hdz
                                · exact hbstc
                                · exact hbstd

theorem balance_black_right_left_BST {α : Type _} (a b c d : Tree α) (x y z : Nat) (vx vy vz : α) : ForallTree (fun t _ => t < x) a -> ForallTree (fun t _ => t > x) (tree red (tree red b y vy c) z vz d) -> BST a -> BST (tree red (tree red b y vy c) z vz d) -> BST (balance black a x vx (tree red (tree red b y vy c) z vz d)) := by
  intro hax hrgt haB hR
  cases a with
  | empty =>
    simp [balance] at *
    sorry
  | tree c0 l0 k0 v0 r0 =>
    cases c0 <;> simp [balance] at *
    · sorry
    · sorry

theorem balance_black_right_right_BST {α : Type _} (a b c d : Tree α) (x y z : Nat) (vx vy vz : α) : ForallTree (fun t _ => t < x) a -> ForallTree (fun t _ => t > x) (tree red b y vy (tree red c z vz d)) -> BST a -> BST (tree red b y vy (tree red c z vz d)) -> BST (balance black a x vx (tree red b y vy (tree red c z vz d))) := by
  intro hax hright hbstA hbstR
  cases b with
  | empty =>
    simp [balance] at *
    sorry
  | tree cb bb kb vb rb =>
    cases cb with
    | red =>
      simp [balance] at *
      sorry
    | black =>
      simp [balance] at *
      sorry

theorem balance_black_BST {α : Type _} (l : Tree α) k vk (r : Tree α) : ForallTree (fun x _ => x < k) l -> ForallTree (fun x _ => x > k) r -> BST l -> BST r -> BST (balance black l k vk r) := by
  intro hl hr hbl hbr
  unfold balance
  split
  · sorry
  · sorry

theorem balance_BST {α : Type u} c (l : Tree α) k vk (r : Tree α)
    : ForallTree (fun x _ => x < k) l
      -> ForallTree (fun x _ => x > k) r
      -> BST l
      -> BST r
      -> BST (balance c l k vk r) := by
  intro hl hr hbstl hbstr
  cases c with
  | red =>
      exact BST.tree red l k vk r hl hr hbstl hbstr
  | black =>
      exact balance_black_BST l k vk r hl hr hbstl hbstr


/-
exercise (2-star)
Prove that `balance` preserves `ForallTree P`.
-/
theorem balanceP {α : Type u} (P : Nat → α → Prop) c (l : Tree α) k vk (r : Tree α)
    : ForallTree P l → ForallTree P r → P k vk
      → ForallTree P (balance c l k vk r) := by
  intro hpl hpr hp; simp
  sorry
  -- split
  -- . constructor <;> assumption
  -- . split
  --   . cases l <;> repeat simp [*] at *



/-
exercise (2-star)
Prove that `ins` preserves `ForallTree P`.
Hint: proceed by induction on `t`.
Use `balanceP`.
-/
theorem insP {α : Type u} (P : Nat → α → Prop) (t : Tree α) k vk
    : ForallTree P t → P k vk
      → ForallTree P (ins k vk t) := by
  sorry

/-
exercise (3-star)
Prove that `ins` maintains `BST`.
Proceed by induction on `t`.
-/
theorem ins_BST {α : Type u} (t : Tree α) k vk : BST t → BST (ins k vk t) := by
  intro h₁
  unfold ins
  split
  sorry
  sorry

/-
## Verification

1. `lookup d k empty_tree = d`
2. `lookup d k (insert k vk t) = vk`
3. `lookup d k' (insert k vk t) = lookup d k' t       if k ≠ k'`
-/

theorem lookup_empty {α : Type u} (d : α) (k : Nat)
    : lookup d k empty_tree = d := by
  rfl

/-
exercise (4-star)
Prove that `balance` preserves the result of lookup on nonempty trees.
Use the same proof technique as in `balance_BST`.
-/
theorem balance_lookup {α : Type u} (d : α) c k k' (vk : α) l r
    : BST l → BST r
      → ForallTree (fun x _ => x < k) l → ForallTree (fun x _ => k < x) r
      → lookup d k' (balance c l k vk r) =
          if k' < k then lookup d k' l
          else if k' > k then lookup d k' r
          else vk := by
  sorry

/-
exercise (3-star)
Verify the second equation, though for `ins` rather than `insert`.
Proceed by induction on the evidence that `t` is a `BST`.
Note that precondition `BST t` will be essential in your proof, unlike the ordinary BST's we saw last time.
-/
theorem lookup_ins_eq {α : Type u} (d : α) t k vk
    : BST t → lookup d k (ins k vk t) = vk := by
  sorry

/-
exercise (3-star)
Verify the third equation, once again for `ins` instead of `insert`.
The same hints as for the second equation hold.
-/
theorem lookup_ins_neq {α : Type u} (d : α) t k vk
    : BST t → k ≠ k' → lookup d k' (ins k vk t) = lookup d k' t := by
  sorry

/-
## references
* [Chris Okasaki. Red-black trees in a functional setting. Journal of Functional Programming. 1999;9(4):471-477.](https://doi.org/10.1017/S0956796899003494)
* [Software Foundations, Volume 3 Verified Functional Algorithms: Red-Black Trees](https://softwarefoundations.cis.upenn.edu/vfa-current/Redblack.html)
* [Theorem Proving in Lean 4: Tactics](https://leanprover.github.io/theorem_proving_in_lean4/tactics.html)
-/
