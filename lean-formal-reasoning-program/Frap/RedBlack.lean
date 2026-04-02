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
The full proof appears below as `balance_BST`.
-/

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
  | tree _ _ _ _ _ hl hr hbstl hbstr =>
      exact ⟨hl, hr, hbstl, hbstr⟩

theorem ForallTree_mono {α : Type _} {p q : Nat → α → Prop} {t : Tree α} : (∀ x v, p x v → q x v) -> ForallTree p t -> ForallTree q t := by
  intro himp h
  induction h with
  | empty =>
      exact ForallTree.empty
  | tree c l k v r hkv hl hr ihl ihr =>
      exact ForallTree.tree _ _ _ _ _ (himp _ _ hkv) ihl ihr

theorem ForallTree_gt_of_lt {α : Type _} {t : Tree α} {x y : Nat} : x < y -> ForallTree (fun z _ => z > y) t -> ForallTree (fun z _ => z > x) t := by
  intro hxy hgt
  exact ForallTree_mono (fun z v hz => Nat.lt_trans hxy hz) hgt

theorem ForallTree_lt_of_lt {α : Type _} {t : Tree α} {x y : Nat} : x < y -> ForallTree (fun z _ => z < x) t -> ForallTree (fun z _ => z < y) t := by
  intro hxy hforall
  exact ForallTree_mono (fun z v hz => Nat.lt_trans hz hxy) hforall

theorem ForallTree_tree_inv {α : Type _} {p : Nat → α → Prop} {c : Color} {l : Tree α} {k : Nat} {v : α} {r : Tree α} : ForallTree p (tree c l k v r) -> p k v ∧ ForallTree p l ∧ ForallTree p r := by
  intro h
  cases h with
  | tree _ _ _ _ _ hk hl hr =>
      exact ⟨hk, hl, hr⟩

theorem balance_BST_black_default {α : Type _} (l : Tree α) (k : Nat) (vk : α) (r : Tree α) : ForallTree (fun x _ => x < k) l -> ForallTree (fun x _ => x > k) r -> BST l -> BST r -> BST (tree black l k vk r) := by
  intro hlt hgt hbstl hbstr
  exact BST.tree black l k vk r hlt hgt hbstl hbstr

theorem balance_BST_black_ll {α : Type _} (a b c d : Tree α) (x y z : Nat) (vx vy vz : α) : ForallTree (fun t _ => t < z) (tree red (tree red a x vx b) y vy c) -> ForallTree (fun t _ => t > z) d -> BST (tree red (tree red a x vx b) y vy c) -> BST d -> BST (tree red (tree black a x vx b) y vy (tree black c z vz d)) := by
  intro hlt hgt hbst hbst_d
  cases hlt with
  | tree _ _ _ _ _ hyz hll_lt_z hc_lt_z =>
    cases hbst with
    | tree _ _ _ _ _ hll_lt_y hc_gt_y hbst_ll hbst_c =>
      cases hll_lt_y with
      | tree _ _ _ _ _ hxy ha_lt_y hb_lt_y =>
        cases hbst_ll with
        | tree _ _ _ _ _ ha_lt_x hb_gt_x hbst_a hbst_b =>
          apply BST.tree
          · exact ForallTree.tree black a x vx b hxy ha_lt_y hb_lt_y
          · exact ForallTree.tree black c z vz d hyz hc_gt_y (ForallTree_gt_of_lt hyz hgt)
          · exact BST.tree black a x vx b ha_lt_x hb_gt_x hbst_a hbst_b
          · exact BST.tree black c z vz d hc_lt_z hgt hbst_c hbst_d

theorem balance_BST_black_lr {α : Type _} (a b c d : Tree α) (x y z : Nat) (vx vy vz : α) : ForallTree (fun t _ => t < z) (tree red a x vx (tree red b y vy c)) -> ForallTree (fun t _ => t > z) d -> BST (tree red a x vx (tree red b y vy c)) -> BST d -> BST (tree red (tree black a x vx b) y vy (tree black c z vz d)) := by
  intro hlt hgt hbst_l hbst_d
  cases hlt with
  | tree _ _ _ _ _ hxz ha_lt_z hr_lt_z =>
    cases hr_lt_z with
    | tree _ _ _ _ _ hyz hb_lt_z hc_lt_z =>
      cases hbst_l with
      | tree _ _ _ _ _ ha_lt_x hr_gt_x hbst_a hbst_r =>
        cases hr_gt_x with
        | tree _ _ _ _ _ hxy hb_gt_x hc_gt_x =>
          cases hbst_r with
          | tree _ _ _ _ _ hb_lt_y hc_gt_y hbst_b hbst_c =>
            apply BST.tree
            · exact ForallTree.tree black a x vx b hxy (ForallTree_lt_of_lt hxy ha_lt_x) hb_lt_y
            · exact ForallTree.tree black c z vz d hyz hc_gt_y (ForallTree_gt_of_lt hyz hgt)
            · exact BST.tree black a x vx b ha_lt_x hb_gt_x hbst_a hbst_b
            · exact BST.tree black c z vz d hc_lt_z hgt hbst_c hbst_d

theorem balance_BST_black_rl {α : Type _} (a b c d : Tree α) (x y z : Nat) (vx vy vz : α) : ForallTree (fun t _ => t < x) a -> ForallTree (fun t _ => t > x) (tree red (tree red b y vy c) z vz d) -> BST a -> BST (tree red (tree red b y vy c) z vz d) -> BST (tree red (tree black a x vx b) y vy (tree black c z vz d)) := by
  intro hax hright hbst_a hbst_right
  cases hright with
  | tree _ _ _ _ _ hxz hmid_gt_x hd_gt_x =>
      cases hmid_gt_x with
      | tree _ _ _ _ _ hxy hb_gt_x hc_gt_x =>
          cases hbst_right with
          | tree _ _ _ _ _ hmid_lt_z hd_gt_z hbst_mid hbst_d =>
              cases hmid_lt_z with
              | tree _ _ _ _ _ hyz hb_lt_z hc_lt_z =>
                  cases hbst_mid with
                  | tree _ _ _ _ _ hb_lt_y hc_gt_y hbst_b hbst_c =>
                      have hxy' : x < y := by omega
                      have hyz' : y < z := hyz
                      constructor
                      · constructor
                        · omega
                        · exact ForallTree_lt_of_lt hxy' hax
                        · exact hb_lt_y
                      · constructor
                        · omega
                        · exact hc_gt_y
                        · exact ForallTree_gt_of_lt hyz' hd_gt_z
                      · constructor
                        · exact hax
                        · exact hb_gt_x
                        · exact hbst_a
                        · exact hbst_b
                      · constructor
                        · exact hc_lt_z
                        · exact hd_gt_z
                        · exact hbst_c
                        · exact hbst_d

theorem balance_BST_black_rr {α : Type _} (a b c d : Tree α) (x y z : Nat) (vx vy vz : α) : ForallTree (fun t _ => t < x) a -> ForallTree (fun t _ => t > x) (tree red b y vy (tree red c z vz d)) -> BST a -> BST (tree red b y vy (tree red c z vz d)) -> BST (tree red (tree black a x vx b) y vy (tree black c z vz d)) := by
  intro hax hrx hbsta hbstR
  cases hrx with
  | tree _ _ _ _ _ hxy hb_gt_x hr_gt_x =>
    cases hbstR with
    | tree _ _ _ _ _ hb_lt_y hr_gt_y hbst_b hbst_r =>
      cases hr_gt_y with
      | tree _ _ _ _ _ hyz hc_gt_y hd_gt_y =>
        cases hbst_r with
        | tree _ _ _ _ _ hc_lt_z hd_gt_z hbst_c hbst_d =>
          constructor
          · constructor
            · exact hxy
            · exact ForallTree_lt_of_lt hxy hax
            · exact hb_lt_y
          · constructor
            · exact hyz
            · exact hc_gt_y
            · exact hd_gt_y
          · constructor
            · exact hax
            · exact hb_gt_x
            · exact hbsta
            · exact hbst_b
          · constructor
            · exact hc_lt_z
            · exact hd_gt_z
            · exact hbst_c
            · exact hbst_d

theorem balance_BST_red {α : Type _} (l : Tree α) (k : Nat) (vk : α) (r : Tree α) : ForallTree (fun x _ => x < k) l -> ForallTree (fun x _ => x > k) r -> BST l -> BST r -> BST (balance red l k vk r) := by
  intro hlt hgt hbstl hbstr
  simpa [balance] using (BST.tree red l k vk r hlt hgt hbstl hbstr)

theorem balance_black_BST {α : Type _} (l : Tree α) (k : Nat) (vk : α) (r : Tree α) : ForallTree (fun x _ => x < k) l -> ForallTree (fun x _ => x > k) r -> BST l -> BST r -> BST (balance black l k vk r) := by
  intro hlt hgt hbstl hbstr
  simp [balance]
  split <;> simp [*] at *
  · exact balance_BST_black_ll _ _ _ _ _ _ _ _ _ _
      (by simpa [*] using hlt)
      (by simpa [*] using hgt)
      (by simpa [*] using hbstl)
      (by simpa [*] using hbstr)
  · exact balance_BST_black_lr _ _ _ _ _ _ _ _ _ _
      (by simpa [*] using hlt)
      (by simpa [*] using hgt)
      (by simpa [*] using hbstl)
      (by simpa [*] using hbstr)
  · exact balance_BST_black_rl _ _ _ _ _ _ _ _ _ _
      (by simpa [*] using hlt)
      (by simpa [*] using hgt)
      (by simpa [*] using hbstl)
      (by simpa [*] using hbstr)
  · exact balance_BST_black_rr _ _ _ _ _ _ _ _ _ _
      (by simpa [*] using hlt)
      (by simpa [*] using hgt)
      (by simpa [*] using hbstl)
      (by simpa [*] using hbstr)
  · exact balance_BST_black_default _ _ _ _
      (by simpa [*] using hlt)
      (by simpa [*] using hgt)
      (by simpa [*] using hbstl)
      (by simpa [*] using hbstr)

theorem balance_BST {α : Type u} c (l : Tree α) k vk (r : Tree α)
    : ForallTree (fun x _ => x < k) l
      -> ForallTree (fun x _ => x > k) r
      -> BST l
      -> BST r
      -> BST (balance c l k vk r) := by
  intro hlt hgt hbstl hbstr
  cases c with
  | red =>
      exact balance_BST_red l k vk r hlt hgt hbstl hbstr
  | black =>
      exact balance_black_BST l k vk r hlt hgt hbstl hbstr


/-
exercise (2-star)
Prove that `balance` preserves `ForallTree P`.
-/
theorem balanceP_black_default {α : Type _} (P : Nat → α → Prop)
    (l : Tree α) (k : Nat) (vk : α) (r : Tree α) :
    ForallTree P l -> ForallTree P r -> P k vk ->
    ForallTree P (tree black l k vk r) := by
  intro hpl hpr hp
  exact ForallTree.tree black l k vk r hp hpl hpr

theorem balanceP_black_ll {α : Type _} (P : Nat → α → Prop)
    (a b c d : Tree α) (x y z : Nat) (vx vy vz : α) :
    ForallTree P (tree red (tree red a x vx b) y vy c) ->
    ForallTree P d ->
    P z vz ->
    ForallTree P (tree red (tree black a x vx b) y vy (tree black c z vz d)) := by
  intro hleft hd hpz
  cases hleft with
  | tree _ _ _ _ _ hpy hleftleft hc =>
      cases hleftleft with
      | tree _ _ _ _ _ hpx ha hb =>
          exact ForallTree.tree red _ _ _ _ hpy
            (ForallTree.tree black a x vx b hpx ha hb)
            (ForallTree.tree black c z vz d hpz hc hd)

theorem balanceP_black_lr {α : Type _} (P : Nat → α → Prop)
    (a b c d : Tree α) (x y z : Nat) (vx vy vz : α) :
    ForallTree P (tree red a x vx (tree red b y vy c)) ->
    ForallTree P d ->
    P z vz ->
    ForallTree P (tree red (tree black a x vx b) y vy (tree black c z vz d)) := by
  intro hleft hd hpz
  cases hleft with
  | tree _ _ _ _ _ hpx ha hleftright =>
      cases hleftright with
      | tree _ _ _ _ _ hpy hb hc =>
          exact ForallTree.tree red _ _ _ _ hpy
            (ForallTree.tree black a x vx b hpx ha hb)
            (ForallTree.tree black c z vz d hpz hc hd)

theorem balanceP_black_rl {α : Type _} (P : Nat → α → Prop)
    (a b c d : Tree α) (x y z : Nat) (vx vy vz : α) :
    ForallTree P a ->
    ForallTree P (tree red (tree red b y vy c) z vz d) ->
    P x vx ->
    ForallTree P (tree red (tree black a x vx b) y vy (tree black c z vz d)) := by
  intro ha hright hpx
  cases hright with
  | tree _ _ _ _ _ hpz hrightleft hd =>
      cases hrightleft with
      | tree _ _ _ _ _ hpy hb hc =>
          exact ForallTree.tree red _ _ _ _ hpy
            (ForallTree.tree black a x vx b hpx ha hb)
            (ForallTree.tree black c z vz d hpz hc hd)

theorem balanceP_black_rr {α : Type _} (P : Nat → α → Prop)
    (a b c d : Tree α) (x y z : Nat) (vx vy vz : α) :
    ForallTree P a ->
    ForallTree P (tree red b y vy (tree red c z vz d)) ->
    P x vx ->
    ForallTree P (tree red (tree black a x vx b) y vy (tree black c z vz d)) := by
  intro ha hright hpx
  cases hright with
  | tree _ _ _ _ _ hpy hb hrightright =>
      cases hrightright with
      | tree _ _ _ _ _ hpz hc hd =>
          exact ForallTree.tree red _ _ _ _ hpy
            (ForallTree.tree black a x vx b hpx ha hb)
            (ForallTree.tree black c z vz d hpz hc hd)

theorem balanceP {α : Type u} (P : Nat → α → Prop) c (l : Tree α) k vk (r : Tree α)
    : ForallTree P l → ForallTree P r → P k vk
      → ForallTree P (balance c l k vk r) := by
  intro hpl hpr hp
  cases c with
  | red =>
      exact ForallTree.tree red l k vk r hp hpl hpr
  | black =>
      simp [balance]
      split <;> simp [*] at *
      · exact balanceP_black_ll P _ _ _ _ _ _ _ _ _ _
          (by simpa [*] using hpl)
          (by simpa [*] using hpr)
          (by simpa [*] using hp)
      · exact balanceP_black_lr P _ _ _ _ _ _ _ _ _ _
          (by simpa [*] using hpl)
          (by simpa [*] using hpr)
          (by simpa [*] using hp)
      · exact balanceP_black_rl P _ _ _ _ _ _ _ _ _ _
          (by simpa [*] using hpl)
          (by simpa [*] using hpr)
          (by simpa [*] using hp)
      · exact balanceP_black_rr P _ _ _ _ _ _ _ _ _ _
          (by simpa [*] using hpl)
          (by simpa [*] using hpr)
          (by simpa [*] using hp)
      · exact balanceP_black_default P _ _ _ _
          (by simpa [*] using hpl)
          (by simpa [*] using hpr)
          hp



/-
exercise (2-star)
Prove that `ins` preserves `ForallTree P`.
Hint: proceed by induction on `t`.
Use `balanceP`.
-/
theorem insP {α : Type u} (P : Nat → α → Prop) (t : Tree α) k vk
    : ForallTree P t → P k vk
      → ForallTree P (ins k vk t) := by
  intro ht hp
  induction ht with
  | empty =>
      exact ForallTree.tree red empty k vk empty hp ForallTree.empty ForallTree.empty
  | tree c l k' v' r hk hl hr ihl ihr =>
      unfold ins
      by_cases hlt : k < k'
      · simp [hlt]
        exact balanceP P c (ins k vk l) k' v' r ihl hr hk
      · simp [hlt]
        by_cases hgt : k > k'
        · simp [hgt]
          exact balanceP P c l k' v' (ins k vk r) hl ihr hk
        · simp [hgt]
          exact ForallTree.tree c l k vk r hp hl hr

/-
exercise (3-star)
Prove that `ins` maintains `BST`.
Proceed by induction on `t`.
-/
theorem ins_BST {α : Type u} (t : Tree α) k vk : BST t → BST (ins k vk t) := by
  intro hbst
  induction hbst with
  | empty =>
      exact BST.tree red empty k vk empty ForallTree.empty ForallTree.empty BST.empty BST.empty
  | tree c l k' v' r hlt hgt hbstl hbstr ihl ihr =>
      unfold ins
      by_cases hlt' : k < k'
      · simp [hlt']
        exact balance_BST c (ins k vk l) k' v' r
          (insP (fun x _ => x < k') l k vk hlt hlt')
          hgt
          ihl
          hbstr
      · simp [hlt']
        by_cases hgt' : k > k'
        · simp [hgt']
          exact balance_BST c l k' v' (ins k vk r)
            hlt
            (insP (fun x _ => x > k') r k vk hgt hgt')
            hbstl
            ihr
        · simp [hgt']
          have heq : k = k' := by omega
          simpa [heq] using (BST.tree c l k' vk r hlt hgt hbstl hbstr)

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
theorem balance_lookup_black_ll {α : Type _} (dflt : α) (k' : Nat)
    (a b c d : Tree α) (x y z : Nat) (vx vy vz : α) :
    BST (tree red (tree red a x vx b) y vy c) ->
    BST d ->
    ForallTree (fun t _ => t < z) (tree red (tree red a x vx b) y vy c) ->
    ForallTree (fun t _ => t > z) d ->
    lookup dflt k' (tree red (tree black a x vx b) y vy (tree black c z vz d)) =
      if k' < z then lookup dflt k' (tree red (tree red a x vx b) y vy c)
      else if k' > z then lookup dflt k' d
      else vz := by
  intro hbst _ hlt _
  cases hlt with
  | tree _ _ _ _ _ hyz hll_lt_z hc_lt_z =>
      cases hbst with
      | tree _ _ _ _ _ hll_lt_y hc_gt_y hbst_ll hbst_c =>
          cases hll_lt_y with
          | tree _ _ _ _ _ hxy ha_lt_y hb_lt_y =>
              by_cases hk'_lt_y : k' < y
              · have hk'_lt_z : k' < z := by omega
                simp [lookup, hk'_lt_y, hk'_lt_z]
              · by_cases hk'_gt_y : k' > y
                · simp [lookup, hk'_lt_y, hk'_gt_y]
                · have hk'_eq_y : k' = y := by omega
                  have hk'_lt_z : k' < z := by omega
                  simp [lookup, hk'_lt_y, hk'_gt_y, hk'_eq_y, hk'_lt_z, hyz]

theorem balance_lookup_black_lr {α : Type _} (dflt : α) (k' : Nat)
    (a b c d : Tree α) (x y z : Nat) (vx vy vz : α) :
    BST (tree red a x vx (tree red b y vy c)) ->
    BST d ->
    ForallTree (fun t _ => t < z) (tree red a x vx (tree red b y vy c)) ->
    ForallTree (fun t _ => t > z) d ->
    lookup dflt k' (tree red (tree black a x vx b) y vy (tree black c z vz d)) =
      if k' < z then lookup dflt k' (tree red a x vx (tree red b y vy c))
      else if k' > z then lookup dflt k' d
      else vz := by
  intro hbst _ hlt _
  cases hlt with
  | tree _ _ _ _ _ hxz ha_lt_z hr_lt_z =>
      cases hr_lt_z with
      | tree _ _ _ _ _ hyz hb_lt_z hc_lt_z =>
          cases hbst with
          | tree _ _ _ _ _ ha_lt_x hr_gt_x hbst_a hbst_r =>
              cases hr_gt_x with
              | tree _ _ _ _ _ hxy hb_gt_x hc_gt_x =>
                  by_cases hk'_lt_y : k' < y
                  · have hk'_lt_z : k' < z := by omega
                    simp [lookup, hk'_lt_y, hk'_lt_z]
                  · by_cases hk'_gt_y : k' > y
                    · have hk'_gt_x : k' > x := by omega
                      have hk'_not_lt_x : ¬ k' < x := by omega
                      simp [lookup, hk'_lt_y, hk'_gt_y, hk'_gt_x, hk'_not_lt_x]
                    · have hk'_eq_y : k' = y := by omega
                      have hk'_gt_x : k' > x := by omega
                      have hk'_lt_z : k' < z := by omega
                      have hnot_y_lt_x : ¬ y < x := by omega
                      simp [lookup, hk'_lt_y, hk'_gt_y, hk'_eq_y, hk'_gt_x, hk'_lt_z, hxy, hyz, hnot_y_lt_x]

theorem balance_lookup_black_rl {α : Type _} (dflt : α) (k' : Nat)
    (a b c d : Tree α) (x y z : Nat) (vx vy vz : α) :
    BST a ->
    BST (tree red (tree red b y vy c) z vz d) ->
    ForallTree (fun t _ => t < x) a ->
    ForallTree (fun t _ => t > x) (tree red (tree red b y vy c) z vz d) ->
    lookup dflt k' (tree red (tree black a x vx b) y vy (tree black c z vz d)) =
      if k' < x then lookup dflt k' a
      else if k' > x then lookup dflt k' (tree red (tree red b y vy c) z vz d)
      else vx := by
  intro _ hbst _ hgt
  cases hgt with
  | tree _ _ _ _ _ hxz hmid_gt_x hd_gt_x =>
      cases hmid_gt_x with
      | tree _ _ _ _ _ hxy hb_gt_x hc_gt_x =>
          cases hbst with
          | tree _ _ _ _ _ hmid_lt_z hd_gt_z hbst_mid hbst_d =>
              cases hmid_lt_z with
              | tree _ _ _ _ _ hyz hb_lt_z hc_lt_z =>
                  by_cases hk'_lt_y : k' < y
                  · have hk'_lt_z : k' < z := by omega
                    simp [lookup, hk'_lt_y, hk'_lt_z]
                  · by_cases hk'_gt_y : k' > y
                    · have hk'_gt_x : k' > x := by omega
                      have hk'_not_lt_x : ¬ k' < x := by omega
                      simp [lookup, hk'_lt_y, hk'_gt_y, hk'_gt_x, hk'_not_lt_x]
                    · have hk'_eq_y : k' = y := by omega
                      have hk'_gt_x : k' > x := by omega
                      have hk'_lt_z : k' < z := by omega
                      have hnot_y_lt_x : ¬ y < x := by omega
                      simp [lookup, hk'_lt_y, hk'_gt_y, hk'_eq_y, hk'_gt_x, hk'_lt_z, hxy, hyz, hnot_y_lt_x]

theorem balance_lookup_black_rr {α : Type _} (dflt : α) (k' : Nat)
    (a b c d : Tree α) (x y z : Nat) (vx vy vz : α) :
    BST a ->
    BST (tree red b y vy (tree red c z vz d)) ->
    ForallTree (fun t _ => t < x) a ->
    ForallTree (fun t _ => t > x) (tree red b y vy (tree red c z vz d)) ->
    lookup dflt k' (tree red (tree black a x vx b) y vy (tree black c z vz d)) =
      if k' < x then lookup dflt k' a
      else if k' > x then lookup dflt k' (tree red b y vy (tree red c z vz d))
      else vx := by
  intro _ hbst _ hgt
  cases hgt with
  | tree _ _ _ _ _ hxy hb_gt_x hr_gt_x =>
      cases hbst with
      | tree _ _ _ _ _ hb_lt_y hr_gt_y hbst_b hbst_r =>
          cases hr_gt_y with
          | tree _ _ _ _ _ hyz hc_gt_y hd_gt_y =>
              cases hbst_r with
              | tree _ _ _ _ _ hc_lt_z hd_gt_z hbst_c hbst_d =>
                  by_cases hk'_lt_y : k' < y
                  · simp [lookup, hk'_lt_y]
                  · by_cases hk'_gt_y : k' > y
                    · have hk'_gt_x : k' > x := by omega
                      have hk'_not_lt_x : ¬ k' < x := by omega
                      simp [lookup, hk'_lt_y, hk'_gt_y, hk'_gt_x, hk'_not_lt_x]
                    · have hk'_eq_y : k' = y := by omega
                      have hk'_gt_x : k' > x := by omega
                      have hnot_y_lt_x : ¬ y < x := by omega
                      simp [lookup, hk'_lt_y, hk'_gt_y, hk'_eq_y, hk'_gt_x, hxy, hnot_y_lt_x]

theorem balance_lookup {α : Type u} (d : α) c k k' (vk : α) l r
    : BST l → BST r
      → ForallTree (fun x _ => x < k) l → ForallTree (fun x _ => k < x) r
      → lookup d k' (balance c l k vk r) =
          if k' < k then lookup d k' l
          else if k' > k then lookup d k' r
          else vk := by
  intro hbstl hbstr hlt hgt
  cases c with
  | red =>
      simp [balance, lookup]
  | black =>
      simp [balance]
      split <;> simp [*] at *
      · simpa [*] using balance_lookup_black_ll d k' _ _ _ _ _ _ _ _ _ _
          (by simpa [*] using hbstl)
          (by simpa [*] using hbstr)
          (by simpa [*] using hlt)
          (by simpa [*] using hgt)
      · simpa [*] using balance_lookup_black_lr d k' _ _ _ _ _ _ _ _ _ _
          (by simpa [*] using hbstl)
          (by simpa [*] using hbstr)
          (by simpa [*] using hlt)
          (by simpa [*] using hgt)
      · simpa [*] using balance_lookup_black_rl d k' _ _ _ _ _ _ _ _ _ _
          (by simpa [*] using hbstl)
          (by simpa [*] using hbstr)
          (by simpa [*] using hlt)
          (by simpa [*] using hgt)
      · simpa [*] using balance_lookup_black_rr d k' _ _ _ _ _ _ _ _ _ _
          (by simpa [*] using hbstl)
          (by simpa [*] using hbstr)
          (by simpa [*] using hlt)
          (by simpa [*] using hgt)

/-
exercise (3-star)
Verify the second equation, though for `ins` rather than `insert`.
Proceed by induction on the evidence that `t` is a `BST`.
Note that precondition `BST t` will be essential in your proof, unlike the ordinary BST's we saw last time.
-/
theorem lookup_ins_eq {α : Type u} (d : α) t k vk
    : BST t → lookup d k (ins k vk t) = vk := by
  intro hbst
  induction hbst with
  | empty =>
      simp [ins, lookup]
  | tree c l k' v' r hlt hgt hbstl hbstr ihl ihr =>
      unfold ins
      by_cases hlt' : k < k'
      · simp [hlt']
        have hleft : ForallTree (fun x _ => x < k') (ins k vk l) :=
          insP (fun x _ => x < k') l k vk hlt hlt'
        have hbal := balance_lookup d c k' k v' (ins k vk l) r (ins_BST l k vk hbstl) hbstr hleft hgt
        calc
          lookup d k (balance c (ins k vk l) k' v' r) = lookup d k (ins k vk l) := by
            simpa [hlt'] using hbal
          _ = vk := ihl
      · by_cases hgt' : k > k'
        · simp [hlt', hgt']
          have hright : ForallTree (fun x _ => x > k') (ins k vk r) :=
            insP (fun x _ => x > k') r k vk hgt hgt'
          have hbal := balance_lookup d c k' k v' l (ins k vk r) hbstl (ins_BST r k vk hbstr) hlt hright
          calc
            lookup d k (balance c l k' v' (ins k vk r)) = lookup d k (ins k vk r) := by
              simpa [hlt', hgt'] using hbal
            _ = vk := ihr
        · simpa [lookup, hlt', hgt'] using rfl

/-
exercise (3-star)
Verify the third equation, once again for `ins` instead of `insert`.
The same hints as for the second equation hold.
-/
theorem lookup_ins_neq {α : Type u} (d : α) t k vk
    : BST t → k ≠ k' → lookup d k' (ins k vk t) = lookup d k' t := by
  intro hbst hneq
  induction hbst with
  | empty =>
      by_cases hk'lt : k' < k
      · simp [ins, lookup, hk'lt]
      · have hk'gt : k' > k := by omega
        simp [ins, lookup, hk'lt, hk'gt]
  | tree c l x v' r hlt hgt hbstl hbstr ihl ihr =>
      unfold ins
      by_cases hlt' : k < x
      · simp [hlt']
        have hleft : ForallTree (fun y _ => y < x) (ins k vk l) :=
          insP (fun y _ => y < x) l k vk hlt hlt'
        have hbal := balance_lookup d c x k' v' (ins k vk l) r (ins_BST l k vk hbstl) hbstr hleft hgt
        calc
          lookup d k' (balance c (ins k vk l) x v' r)
              = if k' < x then lookup d k' (ins k vk l) else if k' > x then lookup d k' r else v' := hbal
          _ = if k' < x then lookup d k' l else if k' > x then lookup d k' r else v' := by
            by_cases hk'lt : k' < x
            · simp [hk'lt, ihl]
            · by_cases hk'gt : k' > x
              · simp [hk'lt, hk'gt]
              · simp [hk'lt, hk'gt]
          _ = lookup d k' (tree c l x v' r) := by rfl
      · by_cases hgt' : k > x
        · simp [hlt', hgt']
          have hright : ForallTree (fun y _ => y > x) (ins k vk r) :=
            insP (fun y _ => y > x) r k vk hgt hgt'
          have hbal := balance_lookup d c x k' v' l (ins k vk r) hbstl (ins_BST r k vk hbstr) hlt hright
          calc
            lookup d k' (balance c l x v' (ins k vk r))
                = if k' < x then lookup d k' l else if k' > x then lookup d k' (ins k vk r) else v' := hbal
            _ = if k' < x then lookup d k' l else if k' > x then lookup d k' r else v' := by
              by_cases hk'lt : k' < x
              · simp [hk'lt]
              · by_cases hk'gt : k' > x
                · simp [hk'lt, hk'gt, ihr]
                · simp [hk'lt, hk'gt]
            _ = lookup d k' (tree c l x v' r) := by rfl
        ·
          have heq : k = x := by omega
          subst x
          by_cases hk'lt : k' < k
          · simp [lookup, hlt', hgt', hk'lt]
          · have hk'gt : k' > k := by omega
            simp [lookup, hlt', hgt', hk'lt, hk'gt]

/-
## references
* [Chris Okasaki. Red-black trees in a functional setting. Journal of Functional Programming. 1999;9(4):471-477.](https://doi.org/10.1017/S0956796899003494)
* [Software Foundations, Volume 3 Verified Functional Algorithms: Red-Black Trees](https://softwarefoundations.cis.upenn.edu/vfa-current/Redblack.html)
* [Theorem Proving in Lean 4: Tactics](https://leanprover.github.io/theorem_proving_in_lean4/tactics.html)
-/
