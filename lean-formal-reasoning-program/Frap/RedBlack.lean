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

theorem BST_tree_inv {α : Type _} {c : Color} {l : Tree α} {k : Nat} {v : α} {r : Tree α} : BST (tree c l k v r) -> ForallTree (fun x _ => x < k) l ∧ ForallTree (fun x _ => x > k) r ∧ BST l ∧ BST r := by
  intro h
  cases h with
  | tree _ _ _ _ _ hl hr hbl hbr =>
      exact ⟨hl, hr, hbl, hbr⟩

theorem forallTree_tree_inv {α : Type _} {P : Nat → α → Prop} {c : Color} {l : Tree α} {k : Nat} {v : α} {r : Tree α} : ForallTree P (tree c l k v r) -> P k v ∧ ForallTree P l ∧ ForallTree P r := by
  intro h
  cases h with
  | tree _ _ _ _ _ hk hl hr =>
      exact ⟨hk, hl, hr⟩

theorem balance_BST_left_left {α : Type _} (ta tb tc td : Tree α) (x y z : Nat) (vx vy vz : α) : ForallTree (fun n _ => n < z) (tree red (tree red ta x vx tb) y vy tc) -> ForallTree (fun n _ => n > z) td -> BST (tree red (tree red ta x vx tb) y vy tc) -> BST td -> BST (tree red (tree black ta x vx tb) y vy (tree black tc z vz td)) := by
  intro hlz hzd hbstl hbstd
  rcases BST_tree_inv hbstl with ⟨hleft_lt_y, htc_gt_y, hbst_left, hbst_tc⟩
  rcases BST_tree_inv hbst_left with ⟨hta_lt_x, htb_gt_x, hbst_ta, hbst_tb⟩
  rcases forallTree_tree_inv hleft_lt_y with ⟨hxy, hta_lt_y, htb_lt_y⟩
  rcases forallTree_tree_inv hlz with ⟨hyz, hleft_lt_z, htc_lt_z⟩
  constructor
  · constructor
    · exact hxy
    · exact hta_lt_y
    · exact htb_lt_y
  · constructor
    · omega
    · exact htc_gt_y
    · exact forallTree_gt td z y hzd (by omega)
  · constructor
    · exact hta_lt_x
    · exact htb_gt_x
    · exact hbst_ta
    · exact hbst_tb
  · constructor
    · exact htc_lt_z
    · exact hzd
    · exact hbst_tc
    · exact hbstd

theorem balance_BST_left_right {α : Type _} (ta tb tc td : Tree α) (x y z : Nat) (vx vy vz : α) : ForallTree (fun n _ => n < z) (tree red ta x vx (tree red tb y vy tc)) -> ForallTree (fun n _ => n > z) td -> BST (tree red ta x vx (tree red tb y vy tc)) -> BST td -> BST (tree red (tree black ta x vx tb) y vy (tree black tc z vz td)) := by
  intro hlz hzd hbstl hbstd
  rcases BST_tree_inv hbstl with ⟨hta_lt_x, hright_gt_x, hbsta, hbst_right⟩
  rcases BST_tree_inv hbst_right with ⟨htb_lt_y, htc_gt_y, hbstb, hbstc⟩
  rcases forallTree_tree_inv hright_gt_x with ⟨hxy, htb_gt_x, htc_gt_x⟩
  rcases forallTree_tree_inv hlz with ⟨hxz, hta_lt_z, hright_lt_z⟩
  rcases forallTree_tree_inv hright_lt_z with ⟨hyz, htb_lt_z, htc_lt_z⟩
  have hta_lt_y : ForallTree (fun n _ => n < y) ta := forallTree_lt ta x y hta_lt_x hxy
  have htd_gt_y : ForallTree (fun n _ => n > y) td := forallTree_gt td z y hzd hyz
  constructor
  · constructor
    · exact hxy
    · exact hta_lt_y
    · exact htb_lt_y
  · constructor
    · exact hyz
    · exact htc_gt_y
    · exact htd_gt_y
  · constructor
    · exact hta_lt_x
    · exact htb_gt_x
    · exact hbsta
    · exact hbstb
  · constructor
    · exact htc_lt_z
    · exact hzd
    · exact hbstc
    · exact hbstd

theorem balance_BST_right_left {α : Type _} (ta tb tc td : Tree α) (x y z : Nat) (vx vy vz : α) : ForallTree (fun n _ => n < x) ta -> ForallTree (fun n _ => n > x) (tree red (tree red tb y vy tc) z vz td) -> BST ta -> BST (tree red (tree red tb y vy tc) z vz td) -> BST (tree red (tree black ta x vx tb) y vy (tree black tc z vz td)) := by
  intro hlx hrx hbsta hbstr
  have ⟨hleft_lt_z, htd_gt_z, hbst_left, hbst_td⟩ := BST_tree_inv hbstr
  have ⟨htb_lt_y, htc_gt_y, hbst_tb, hbst_tc⟩ := BST_tree_inv hbst_left
  have ⟨hz_gt_x, hrx_mid, htd_gt_x⟩ := forallTree_tree_inv hrx
  have ⟨hy_gt_x, htb_gt_x, htc_gt_x⟩ := forallTree_tree_inv hrx_mid
  have ⟨hy_lt_z, htb_lt_z, htc_lt_z⟩ := forallTree_tree_inv hleft_lt_z
  constructor
  · constructor
    · omega
    · exact forallTree_lt ta x y hlx (by omega)
    · exact htb_lt_y
  · constructor
    · omega
    · exact htc_gt_y
    · exact forallTree_gt td z y htd_gt_z (by omega)
  · constructor
    · exact hlx
    · exact htb_gt_x
    · exact hbsta
    · exact hbst_tb
  · constructor
    · exact htc_lt_z
    · exact htd_gt_z
    · exact hbst_tc
    · exact hbst_td

theorem balance_BST_right_right {α : Type _} (ta tb tc td : Tree α) (x y z : Nat) (vx vy vz : α) : ForallTree (fun n _ => n < x) ta -> ForallTree (fun n _ => n > x) (tree red tb y vy (tree red tc z vz td)) -> BST ta -> BST (tree red tb y vy (tree red tc z vz td)) -> BST (tree red (tree black ta x vx tb) y vy (tree black tc z vz td)) := by
  intro hlx hrx hbsta hbstr
  rcases BST_tree_inv hbstr with ⟨htb_lt_y, hright_gt_y, hbst_tb, hbst_right⟩
  rcases BST_tree_inv hbst_right with ⟨htc_lt_z, htd_gt_z, hbst_tc, hbst_td⟩
  rcases forallTree_tree_inv hrx with ⟨hy_gt_x, htb_gt_x, hright_gt_x⟩
  rcases forallTree_tree_inv hright_gt_y with ⟨hz_gt_y, htc_gt_y, htd_gt_y⟩
  have hxy : x < y := by omega
  have hta_lt_y : ForallTree (fun n _ => n < y) ta := forallTree_lt ta x y hlx hxy
  constructor
  · constructor
    · exact hxy
    · exact hta_lt_y
    · exact htb_lt_y
  · constructor
    · exact hz_gt_y
    · exact htc_gt_y
    · exact htd_gt_y
  · constructor
    · exact hlx
    · exact htb_gt_x
    · exact hbsta
    · exact hbst_tb
  · constructor
    · exact htc_lt_z
    · exact htd_gt_z
    · exact hbst_tc
    · exact hbst_td

theorem balance_BST {α : Type u} c (l : Tree α) k vk (r : Tree α)
    : ForallTree (fun x _ => x < k) l
      -> ForallTree (fun x _ => x > k) r
      -> BST l
      -> BST r
      -> BST (balance c l k vk r) := by
  intro hlk hkr hbl hbr
  cases c with
  | red =>
      simpa [balance] using (BST.tree red l k vk r hlk hkr hbl hbr)
  | black =>
      simp [balance]
      repeat' split
      · rename_i tup a x vx b y vy c z vz d hEq
        cases hEq
        simpa using balance_BST_left_left _ _ _ _ _ _ _ _ _ _ hlk hkr hbl hbr
      · rename_i tup a x vx b y vy c z vz d hne hEq
        cases hEq
        simpa using balance_BST_left_right _ _ _ _ _ _ _ _ _ _ hlk hkr hbl hbr
      · rename_i tup a x vx b y vy c z vz d hne1 hne2 hEq
        cases hEq
        simpa using balance_BST_right_left _ _ _ _ _ _ _ _ _ _ hlk hkr hbl hbr
      · rename_i tup a x vx b y vy c z vz d hne1 hne2 hne3 hEq
        cases hEq
        simpa using balance_BST_right_right _ _ _ _ _ _ _ _ _ _ hlk hkr hbl hbr
      · constructor <;> assumption


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
