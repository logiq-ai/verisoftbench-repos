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

theorem balance_BST_forallTree_imp: ∀ {α : Type _} {p q : Nat → α → Prop} {t : Tree α}, (∀ x v, p x v → q x v) -> ForallTree p t -> ForallTree q t := by
  intro α p q t hpq h
  induction h with
  | empty =>
      exact ForallTree.empty
  | tree c l k v r hroot hl hr ihl ihr =>
      exact ForallTree.tree c l k v r (hpq k v hroot) ihl ihr

theorem balance_BST_forallTree_recolor: ∀ {α : Type _} {p : Nat → α → Prop} {c₁ c₂ : Color} {l : Tree α} {k : Nat} {v : α} {r : Tree α}, ForallTree p (Tree.tree c₁ l k v r) -> ForallTree p (Tree.tree c₂ l k v r) := by
  intro α p c₁ c₂ l k v r h
  cases h
  constructor <;> assumption

theorem balance_BST_left_left: ∀ {α : Type _} (a b c d : Tree α) (x : Nat) (vx : α) (y : Nat) (vy : α) (z : Nat) (vz : α), ForallTree (fun t _ => t < z) (Tree.tree red (Tree.tree red a x vx b) y vy c) -> ForallTree (fun t _ => t > z) d -> BST (Tree.tree red (Tree.tree red a x vx b) y vy c) -> BST d -> BST (Tree.tree red (Tree.tree black a x vx b) y vy (Tree.tree black c z vz d)) := by
  intro α a b c d x vx y vy z vz hltz hdgtz hbstl hbstd
  cases hltz with
  | tree _ _ _ _ _ hy_lt_z hll_lt_z hc_lt_z =>
    cases hbstl with
    | tree _ _ _ _ _ hll_lt_y hc_gt_y hbst_ll hbst_c =>
      cases hbst_ll with
      | tree _ _ _ _ _ ha_lt_x hb_gt_x hbst_a hbst_b =>
        have hleft_bst : BST (Tree.tree black a x vx b) := by
          exact BST.tree black a x vx b ha_lt_x hb_gt_x hbst_a hbst_b
        have hleft_lt_y : ForallTree (fun t _ => t < y) (Tree.tree black a x vx b) := by
          exact balance_BST_forallTree_recolor hll_lt_y
        have hd_gt_y : ForallTree (fun t _ => t > y) d := by
          exact balance_BST_forallTree_imp (fun t _ h => Nat.lt_trans hy_lt_z h) hdgtz
        have hright_bst : BST (Tree.tree black c z vz d) := by
          exact BST.tree black c z vz d hc_lt_z hdgtz hbst_c hbstd
        have hright_gt_y : ForallTree (fun t _ => t > y) (Tree.tree black c z vz d) := by
          exact ForallTree.tree black c z vz d hy_lt_z hc_gt_y hd_gt_y
        exact BST.tree red (Tree.tree black a x vx b) y vy (Tree.tree black c z vz d) hleft_lt_y hright_gt_y hleft_bst hright_bst

theorem balance_BST_left_right: ∀ {α : Type _} (a b c d : Tree α) (x : Nat) (vx : α) (y : Nat) (vy : α) (z : Nat) (vz : α), ForallTree (fun t _ => t < z) (Tree.tree red a x vx (Tree.tree red b y vy c)) -> ForallTree (fun t _ => t > z) d -> BST (Tree.tree red a x vx (Tree.tree red b y vy c)) -> BST d -> BST (Tree.tree red (Tree.tree black a x vx b) y vy (Tree.tree black c z vz d)) := by
  intro α a b c d x vx y vy z vz hall hdz hbst hbst_d
  cases hall with
  | tree _ _ _ _ _ hx_lt_z ha_lt_z hr_lt_z =>
    cases hbst with
    | tree _ _ _ _ _ ha_lt_x hr_gt_x hbst_a hbst_r =>
      cases hbst_r with
      | tree _ _ _ _ _ hb_lt_y hc_gt_y hbst_b hbst_c =>
        cases hr_gt_x with
        | tree _ _ _ _ _ hx_lt_y hb_gt_x hc_gt_x =>
          cases hr_lt_z with
          | tree _ _ _ _ _ hy_lt_z hb_lt_z hc_lt_z =>
            have ha_lt_y : ForallTree (fun t _ => t < y) a := by
              apply balance_BST_forallTree_imp
              · intro t v ht
                exact Nat.lt_trans ht hx_lt_y
              · exact ha_lt_x
            have hd_gt_y : ForallTree (fun t _ => t > y) d := by
              apply balance_BST_forallTree_imp
              · intro t v ht
                exact Nat.lt_trans hy_lt_z ht
              · exact hdz
            constructor
            · constructor
              · exact hx_lt_y
              · exact ha_lt_y
              · exact hb_lt_y
            · constructor
              · exact hy_lt_z
              · exact hc_gt_y
              · exact hd_gt_y
            · constructor
              · exact ha_lt_x
              · exact hb_gt_x
              · exact hbst_a
              · exact hbst_b
            · constructor
              · exact hc_lt_z
              · exact hdz
              · exact hbst_c
              · exact hbst_d

theorem balance_BST_right_left: ∀ {α : Type _} (a b c d : Tree α) (x : Nat) (vx : α) (y : Nat) (vy : α) (z : Nat) (vz : α), ForallTree (fun t _ => t < x) a -> ForallTree (fun t _ => t > x) (Tree.tree red (Tree.tree red b y vy c) z vz d) -> BST a -> BST (Tree.tree red (Tree.tree red b y vy c) z vz d) -> BST (Tree.tree red (Tree.tree black a x vx b) y vy (Tree.tree black c z vz d)) := by
  intro α a b c d x vx y vy z vz ha_lt_x hright_gt_x hbst_a hbst_right
  cases hright_gt_x
  case tree hleft_gt_x hz_gt_x hd_gt_x =>
    cases hbst_right
    case tree hleft_lt_z hd_gt_z hbst_left hbst_d =>
      sorry

theorem balance_BST_right_right: ∀ {α : Type _} (a b c d : Tree α) (x : Nat) (vx : α) (y : Nat) (vy : α) (z : Nat) (vz : α), ForallTree (fun t _ => t < x) a -> ForallTree (fun t _ => t > x) (Tree.tree red b y vy (Tree.tree red c z vz d)) -> BST a -> BST (Tree.tree red b y vy (Tree.tree red c z vz d)) -> BST (Tree.tree red (Tree.tree black a x vx b) y vy (Tree.tree black c z vz d)) := by
  intro α a b c d x vx y vy z vz hax hright hbsta hbstRight
  cases hright with
  | tree _ _ _ _ _ hxy hb_gt_x hr_gt_x =>
    cases hbstRight with
    | tree _ _ _ _ _ hb_lt_y hr_gt_y hbst_b hbst_r =>
      cases hbst_r with
      | tree _ _ _ _ _ hc_lt_z hd_gt_z hbst_c hbst_d =>
        apply BST.tree
        · have haxy : ForallTree (fun t _ => t < y) a :=
            balance_BST_forallTree_imp (fun t v ht => by omega) hax
          exact ForallTree.tree black a x vx b hxy haxy hb_lt_y
        · exact balance_BST_forallTree_recolor hr_gt_y
        · exact BST.tree black a x vx b hax hb_gt_x hbsta hbst_b
        · exact BST.tree black c z vz d hc_lt_z hd_gt_z hbst_c hbst_d

theorem balance_BST: ∀ {α : Type _} (c : Color) (l : Tree α) (k : Nat) (vk : α) (r : Tree α), ForallTree (fun x _ => x < k) l -> ForallTree (fun x _ => x > k) r -> BST l -> BST r -> BST (balance c l k vk r) := by
  intro α c l k vk r hlk hkr hbl hbr
  cases c with
  | red =>
      exact BST.tree red l k vk r hlk hkr hbl hbr
  | black =>
      cases l <;> cases r <;> simp [balance] at *
      all_goals sorry


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
