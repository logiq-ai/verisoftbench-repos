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

theorem forallTree_gt_weaken {α : Type _} {t : Tree α} {a b : Nat} : a < b → ForallTree (fun x _ => x > b) t → ForallTree (fun x _ => x > a) t := by
  intro hab h
  exact forallTree_gt t b a h hab

theorem balance_black_left_left_BST {α : Type _} {a b c d : Tree α} {x y z : Nat} {vx vy vz : α} : ForallTree (fun t _ => t < z) (tree red (tree red a x vx b) y vy c) → ForallTree (fun t _ => t > z) d → BST (tree red (tree red a x vx b) y vy c) → BST d → BST (tree red (tree black a x vx b) y vy (tree black c z vz d)) := by
  intro hlt hgt hbstl hbstr
  cases hlt with
  | tree _ _ _ _ _ hy_lt_z hleft_lt_y hc_lt_z =>
    cases hbstl with
    | tree _ _ _ _ _ hleft_lt_y' hc_gt_y hbst_left hbst_c =>
      cases hleft_lt_y' with
      | tree _ _ _ _ _ hx_lt_y ha_lt_y hb_lt_y =>
        cases hbst_left with
        | tree _ _ _ _ _ ha_lt_x hb_gt_x hbst_a hbst_b =>
          constructor
          · constructor
            · exact hx_lt_y
            · exact ha_lt_y
            · exact hb_lt_y
          · constructor
            · exact hy_lt_z
            · exact hc_gt_y
            · exact forallTree_gt_weaken hy_lt_z hgt
          · constructor
            · exact ha_lt_x
            · exact hb_gt_x
            · exact hbst_a
            · exact hbst_b
          · constructor
            · exact hc_lt_z
            · exact hgt
            · exact hbst_c
            · exact hbstr

theorem forallTree_lt_weaken {α : Type _} {t : Tree α} {a b : Nat} : a < b → ForallTree (fun x _ => x < a) t → ForallTree (fun x _ => x < b) t := by
  intro hab h
  induction h with
  | empty =>
      exact ForallTree.empty
  | tree c l k v r hk hl hr ihl ihr =>
      exact ForallTree.tree c l k v r (Nat.lt_trans hk hab) ihl ihr

theorem balance_black_left_right_BST {α : Type _} {a b c d : Tree α} {x y z : Nat} {vx vy vz : α} : ForallTree (fun t _ => t < z) (tree red a x vx (tree red b y vy c)) → ForallTree (fun t _ => t > z) d → BST (tree red a x vx (tree red b y vy c)) → BST d → BST (tree red (tree black a x vx b) y vy (tree black c z vz d)) := by
  intro hlt hgt hbstl hbstr
  cases hbstl with
  | tree _ _ _ _ _ ha_lt_x hr_gt_x hbst_a hbst_right =>
    cases hr_gt_x with
    | tree _ _ _ _ _ hy_gt_x hb_gt_x hc_gt_x =>
      cases hbst_right with
      | tree _ _ _ _ _ hb_lt_y hc_gt_y hbst_b hbst_c =>
        cases hlt with
        | tree _ _ _ _ _ hx_lt_z ha_lt_z hr_lt_z =>
          cases hr_lt_z with
          | tree _ _ _ _ _ hy_lt_z hb_lt_z hc_lt_z =>
            constructor
            · constructor
              · exact hy_gt_x
              · exact forallTree_lt_weaken hy_gt_x ha_lt_x
              · exact hb_lt_y
            · constructor
              · exact hy_lt_z
              · exact hc_gt_y
              · exact forallTree_gt_weaken hy_lt_z hgt
            · constructor
              · exact ha_lt_x
              · exact hb_gt_x
              · exact hbst_a
              · exact hbst_b
            · constructor
              · exact hc_lt_z
              · exact hgt
              · exact hbst_c
              · exact hbstr

theorem balance_black_right_left_BST {α : Type _} {a b c d : Tree α} {x y z : Nat} {vx vy vz : α} : ForallTree (fun t _ => t < x) a → ForallTree (fun t _ => t > x) (tree red (tree red b y vy c) z vz d) → BST a → BST (tree red (tree red b y vy c) z vz d) → BST (tree red (tree black a x vx b) y vy (tree black c z vz d)) := by
  intro hlt hgt hbstl hbstr
  cases hgt with
  | tree _ _ _ _ _ hz_gt_x hleft_gt_x hd_gt_x =>
    cases hleft_gt_x with
    | tree _ _ _ _ _ hy_gt_x hb_gt_x hc_gt_x =>
      cases hbstr with
      | tree _ _ _ _ _ hleft_lt_z hd_gt_z hbst_left hbst_d =>
        cases hleft_lt_z with
        | tree _ _ _ _ _ hy_lt_z hb_lt_z hc_lt_z =>
          cases hbst_left with
          | tree _ _ _ _ _ hb_lt_y hc_gt_y hbst_b hbst_c =>
            apply BST.tree
            · apply ForallTree.tree
              · exact hy_gt_x
              · exact forallTree_lt_weaken hy_gt_x hlt
              · exact hb_lt_y
            · apply ForallTree.tree
              · exact hy_lt_z
              · exact hc_gt_y
              · exact forallTree_gt_weaken hy_lt_z hd_gt_z
            · apply BST.tree
              · exact hlt
              · exact hb_gt_x
              · exact hbstl
              · exact hbst_b
            · apply BST.tree
              · exact hc_lt_z
              · exact hd_gt_z
              · exact hbst_c
              · exact hbst_d

theorem balance_black_right_right_BST {α : Type _} {a b c d : Tree α} {x y z : Nat} {vx vy vz : α} : ForallTree (fun t _ => t < x) a → ForallTree (fun t _ => t > x) (tree red b y vy (tree red c z vz d)) → BST a → BST (tree red b y vy (tree red c z vz d)) → BST (tree red (tree black a x vx b) y vy (tree black c z vz d)) := by
  intro hlt hgt hbstl hbstr
  cases hgt with
  | tree _ _ _ _ _ hy_gt_x hb_gt_x hr_gt_x =>
      cases hbstr with
      | tree _ _ _ _ _ hb_lt_y hr_gt_y hbst_b hbst_right =>
          cases hr_gt_y with
          | tree _ _ _ _ _ hz_gt_y hc_gt_y hd_gt_y =>
              cases hbst_right with
              | tree _ _ _ _ _ hc_lt_z hd_gt_z hbst_c hbst_d =>
                  apply BST.tree
                  · apply ForallTree.tree
                    · exact hy_gt_x
                    · exact forallTree_lt_weaken hy_gt_x hlt
                    · exact hb_lt_y
                  · apply ForallTree.tree
                    · exact hz_gt_y
                    · exact hc_gt_y
                    · exact hd_gt_y
                  · apply BST.tree
                    · exact hlt
                    · exact hb_gt_x
                    · exact hbstl
                    · exact hbst_b
                  · apply BST.tree
                    · exact hc_lt_z
                    · exact hd_gt_z
                    · exact hbst_c
                    · exact hbst_d

theorem balance_BST {α : Type u} c (l : Tree α) k vk (r : Tree α)
    : ForallTree (fun x _ => x < k) l
      -> ForallTree (fun x _ => x > k) r
      -> BST l
      -> BST r
      -> BST (balance c l k vk r) := by
  intro hlt hgt hbstl hbstr
  cases c with
  | red =>
      simpa only [balance] using (BST.tree red l k vk r hlt hgt hbstl hbstr)
  | black =>
      simp only [balance]
      split <;> rename_i h
      · cases h
        exact balance_black_left_left_BST hlt hgt hbstl hbstr
      · cases h
        exact balance_black_left_right_BST hlt hgt hbstl hbstr
      · cases h
        exact balance_black_right_left_BST hlt hgt hbstl hbstr
      · cases h
        exact balance_black_right_right_BST hlt hgt hbstl hbstr
      · exact BST.tree black l k vk r hlt hgt hbstl hbstr

example {α : Type u} c (l : Tree α) k vk (r : Tree α)
    : ForallTree (fun x _ => x < k) l
      -> ForallTree (fun x _ => x > k) r
      -> BST l
      -> BST r
      -> BST (balance c l k vk r) := by
  exact balance_BST c l k vk r


/-
exercise (2-star)
Prove that `balance` preserves `ForallTree P`.
-/
theorem balanceP {α : Type u} (P : Nat → α → Prop) c (l : Tree α) k vk (r : Tree α)
    : ForallTree P l → ForallTree P r → P k vk
      → ForallTree P (balance c l k vk r) := by
  intro hpl hpr hp
  cases c with
  | red =>
    exact ForallTree.tree red l k vk r hp hpl hpr
  | black =>
    simp only [balance]
    split <;> rename_i h
    · cases h
      cases hpl with
      | tree _ _ _ _ _ hy hleft hc =>
        cases hleft with
        | tree _ _ _ _ _ hx ha hb =>
          constructor
          · exact hy
          · constructor <;> assumption
          · constructor <;> assumption
    · cases h
      cases hpl with
      | tree _ _ _ _ _ hx ha hright =>
        cases hright with
        | tree _ _ _ _ _ hy hb hc =>
          constructor
          · exact hy
          · constructor <;> assumption
          · constructor <;> assumption
    · cases h
      cases hpr with
      | tree _ _ _ _ _ hz hleft hd =>
        cases hleft with
        | tree _ _ _ _ _ hy hb hc =>
          constructor
          · exact hy
          · constructor <;> assumption
          · constructor <;> assumption
    · cases h
      cases hpr with
      | tree _ _ _ _ _ hy hb hright =>
        cases hright with
        | tree _ _ _ _ _ hz hc hd =>
          constructor
          · exact hy
          · constructor <;> assumption
          · constructor <;> assumption
    · exact ForallTree.tree black l k vk r hp hpl hpr



/-
exercise (2-star)
Prove that `ins` preserves `ForallTree P`.
Hint: proceed by induction on `t`.
Use `balanceP`.
-/
theorem insP {α : Type u} (P : Nat → α → Prop) (t : Tree α) k vk
    : ForallTree P t → P k vk
      → ForallTree P (ins k vk t) := by
  intro h
  induction h generalizing k vk with
  | empty =>
    intro hp
    exact ForallTree.tree red empty k vk empty hp ForallTree.empty ForallTree.empty
  | tree c l k' v' r hk hpl hpr ihl ihr =>
    intro hp
    simp only [ins]
    split
    · exact balanceP P c (ins k vk l) k' v' r (ihl k vk hp) hpr hk
    · split
      · exact balanceP P c l k' v' (ins k vk r) hpl (ihr k vk hp) hk
      · exact ForallTree.tree c l k vk r hp hpl hpr

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
    simp only [ins]
    split
    · exact balance_BST c (ins k vk l) k' v' r
        (insP (fun x _ => x < k') l k vk hlt ‹k < k'›) hgt ihl hbstr
    · split
      · exact balance_BST c l k' v' (ins k vk r)
          hlt (insP (fun x _ => x > k') r k vk hgt ‹k > k'›) hbstl ihr
      · have hk_eq : k = k' := by
          omega
        subst k
        exact BST.tree c l k' vk r hlt hgt hbstl hbstr

/-
## Verification

1. `lookup d k empty_tree = d`
2. `lookup d k (insert k vk t) = vk`
3. `lookup d k' (insert k vk t) = lookup d k' t       if k ≠ k'`
-/

theorem lookup_empty {α : Type u} (d : α) (k : Nat)
    : lookup d k empty_tree = d := by
  rfl

theorem balance_black_left_left_lookup {α : Type _} (dflt : α) {a b c d : Tree α} {x y z k' : Nat} {vx vy vz : α}
    : BST (tree red (tree red a x vx b) y vy c) → BST d
      → ForallTree (fun t _ => t < z) (tree red (tree red a x vx b) y vy c) → ForallTree (fun t _ => z < t) d
      → lookup dflt k' (tree red (tree black a x vx b) y vy (tree black c z vz d)) =
          if k' < z then lookup dflt k' (tree red (tree red a x vx b) y vy c)
          else if k' > z then lookup dflt k' d
          else vz := by
  intro _ _ hlt _
  cases hlt with
  | tree _ _ _ _ _ hy_lt_z _ _ =>
    by_cases hk_y : k' < y
    · have hk_z : k' < z := by
        omega
      have hk_not_gt_z : ¬ k' > z := by
        omega
      simp [lookup, hk_y, hk_z, hk_not_gt_z]
    · by_cases hk_gt_y : k' > y
      · by_cases hk_z : k' < z
        · have hk_not_gt_z : ¬ k' > z := by
            omega
          simp [lookup, hk_y, hk_gt_y, hk_z, hk_not_gt_z]
        · by_cases hk_gt_z : k' > z
          · simp [lookup, hk_y, hk_gt_y, hk_z, hk_gt_z]
          · have hk_eq_z : k' = z := by
              omega
            subst k'
            have hz_not_lt_y : ¬ z < y := by
              omega
            simp [lookup, hy_lt_z, hz_not_lt_y]
      · have hk_eq_y : k' = y := by
          omega
        subst k'
        simp [lookup, hy_lt_z]

theorem balance_black_left_right_lookup {α : Type _} (dflt : α) {a b c d : Tree α} {x y z k' : Nat} {vx vy vz : α}
    : BST (tree red a x vx (tree red b y vy c)) → BST d
      → ForallTree (fun t _ => t < z) (tree red a x vx (tree red b y vy c)) → ForallTree (fun t _ => z < t) d
      → lookup dflt k' (tree red (tree black a x vx b) y vy (tree black c z vz d)) =
          if k' < z then lookup dflt k' (tree red a x vx (tree red b y vy c))
          else if k' > z then lookup dflt k' d
          else vz := by
  intro hbstl _ hlt _
  cases hbstl with
  | tree _ _ _ _ _ _ hr_gt_x _ _ =>
    cases hr_gt_x with
    | tree _ _ _ _ _ hy_gt_x _ _ =>
      cases hlt with
      | tree _ _ _ _ _ _ _ hr_lt_z =>
        cases hr_lt_z with
        | tree _ _ _ _ _ hy_lt_z _ _ =>
          by_cases hk_y : k' < y
          · have hk_z : k' < z := by
              omega
            have hk_not_gt_z : ¬ k' > z := by
              omega
            simp [lookup, hk_y, hk_z, hk_not_gt_z]
          · by_cases hk_gt_y : k' > y
            · by_cases hk_z : k' < z
              · have hk_not_gt_z : ¬ k' > z := by
                  omega
                have hx_lt_k' : x < k' := by
                  omega
                have hk'_not_lt_x : ¬ k' < x := by
                  omega
                simp [lookup, hk_y, hk_gt_y, hk_z, hk_not_gt_z, hy_gt_x, hx_lt_k', hk'_not_lt_x]
              · by_cases hk_gt_z : k' > z
                · simp [lookup, hk_y, hk_gt_y, hk_z, hk_gt_z, hy_gt_x]
                · have hk_eq_z : k' = z := by
                    omega
                  subst k'
                  have hz_not_lt_y : ¬ z < y := by
                    omega
                  have hx_lt_z : x < z := by
                    omega
                  simp [lookup, hy_gt_x, hy_lt_z, hz_not_lt_y, hx_lt_z]
            · have hk_eq_y : k' = y := by
                omega
              subst k'
              have hy_not_lt_x : ¬ y < x := by
                omega
              simp [lookup, hy_gt_x, hy_lt_z, hy_not_lt_x]

theorem balance_black_right_left_lookup {α : Type _} (dflt : α) {a b c d : Tree α} {x y z k' : Nat} {vx vy vz : α}
    : BST a → BST (tree red (tree red b y vy c) z vz d)
      → ForallTree (fun t _ => t < x) a → ForallTree (fun t _ => t > x) (tree red (tree red b y vy c) z vz d)
      → lookup dflt k' (tree red (tree black a x vx b) y vy (tree black c z vz d)) =
          if k' < x then lookup dflt k' a
          else if k' > x then lookup dflt k' (tree red (tree red b y vy c) z vz d)
          else vx := by
  intro _ hbstr _ hgt
  cases hgt with
  | tree _ _ _ _ _ _ hleft_gt_x _ =>
    cases hleft_gt_x with
    | tree _ _ _ _ _ hy_gt_x _ _ =>
      cases hbstr with
      | tree _ _ _ _ _ hleft_lt_z _ _ _ =>
        cases hleft_lt_z with
        | tree _ _ _ _ _ hy_lt_z _ _ =>
          by_cases hk_y : k' < y
          · have hk_z : k' < z := by
              omega
            simp [lookup, hk_y, hk_z, hy_gt_x]
          · by_cases hk_gt_y : k' > y
            · by_cases hk_z : k' < z
              · have hk_not_gt_z : ¬ k' > z := by
                  omega
                have hx_lt_k' : x < k' := by
                  omega
                have hk'_not_lt_x : ¬ k' < x := by
                  omega
                simp [lookup, hk_y, hk_gt_y, hk_z, hk_not_gt_z, hy_gt_x, hx_lt_k', hk'_not_lt_x]
              · by_cases hk_gt_z : k' > z
                · have hx_lt_k' : x < k' := by
                    omega
                  have hk'_not_lt_x : ¬ k' < x := by
                    omega
                  simp [lookup, hk_y, hk_gt_y, hk_z, hk_gt_z, hy_gt_x, hx_lt_k', hk'_not_lt_x]
                · have hk_eq_z : k' = z := by
                    omega
                  subst k'
                  have hz_not_lt_y : ¬ z < y := by
                    omega
                  have hx_lt_z : x < z := by
                    omega
                  have hz_not_lt_x : ¬ z < x := by
                    omega
                  simp [lookup, hk_gt_y, hy_gt_x, hz_not_lt_y, hx_lt_z, hz_not_lt_x]
            · have hk_eq_y : k' = y := by
                omega
              subst k'
              have hy_not_lt_x : ¬ y < x := by
                omega
              simp [lookup, hy_gt_x, hy_lt_z, hy_not_lt_x]

theorem balance_black_right_right_lookup {α : Type _} (dflt : α) {a b c d : Tree α} {x y z k' : Nat} {vx vy vz : α}
    : BST a → BST (tree red b y vy (tree red c z vz d))
      → ForallTree (fun t _ => t < x) a → ForallTree (fun t _ => t > x) (tree red b y vy (tree red c z vz d))
      → lookup dflt k' (tree red (tree black a x vx b) y vy (tree black c z vz d)) =
          if k' < x then lookup dflt k' a
          else if k' > x then lookup dflt k' (tree red b y vy (tree red c z vz d))
          else vx := by
  intro _ hbstr _ hgt
  cases hgt with
  | tree _ _ _ _ _ hy_gt_x _ _ =>
    cases hbstr with
    | tree _ _ _ _ _ _ hr_gt_y _ _ =>
      cases hr_gt_y with
      | tree _ _ _ _ _ hz_gt_y _ _ =>
        by_cases hk_y : k' < y
        · simp [lookup, hk_y, hy_gt_x]
        · by_cases hk_gt_y : k' > y
          · by_cases hk_z : k' < z
            · have hk_not_gt_z : ¬ k' > z := by
                omega
              have hx_lt_k' : x < k' := by
                omega
              have hk'_not_lt_x : ¬ k' < x := by
                omega
              simp [lookup, hk_y, hk_gt_y, hk_z, hk_not_gt_z, hy_gt_x, hx_lt_k', hk'_not_lt_x]
            · by_cases hk_gt_z : k' > z
              · have hx_lt_k' : x < k' := by
                  omega
                have hk'_not_lt_x : ¬ k' < x := by
                  omega
                simp [lookup, hk_y, hk_gt_y, hk_z, hk_gt_z, hy_gt_x, hx_lt_k', hk'_not_lt_x]
              · have hk_eq_z : k' = z := by
                  omega
                subst k'
                have hz_not_lt_y : ¬ z < y := by
                  omega
                have hx_lt_z : x < z := by
                  omega
                have hz_not_lt_x : ¬ z < x := by
                  omega
                simp [lookup, hk_gt_y, hy_gt_x, hz_gt_y, hz_not_lt_y, hx_lt_z, hz_not_lt_x]
          · have hk_eq_y : k' = y := by
              omega
            subst k'
            have hy_not_lt_x : ¬ y < x := by
              omega
            simp [lookup, hy_gt_x, hy_not_lt_x]

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
  intro hbstl hbstr hlt hgt
  cases c with
  | red =>
    simp [balance, lookup]
  | black =>
    simp only [balance]
    split <;> rename_i h
    · cases h
      exact balance_black_left_left_lookup d hbstl hbstr hlt hgt
    · cases h
      exact balance_black_left_right_lookup d hbstl hbstr hlt hgt
    · cases h
      exact balance_black_right_left_lookup d hbstl hbstr hlt hgt
    · cases h
      exact balance_black_right_right_lookup d hbstl hbstr hlt hgt
    · simp [lookup]

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
    simp only [ins]
    split
    · simpa [‹k < k'›, ihl] using
        (balance_lookup d c k' k v' (ins k vk l) r
          (ins_BST l k vk hbstl) hbstr (insP (fun x _ => x < k') l k vk hlt ‹k < k'›) hgt)
    · split
      · have hk_not_lt : ¬ k < k' := by
          omega
        simpa [‹k > k'›, hk_not_lt, ihr] using
          (balance_lookup d c k' k v' l (ins k vk r)
            hbstl (ins_BST r k vk hbstr) hlt (insP (fun x _ => x > k') r k vk hgt ‹k > k'›))
      · have hk_eq : k = k' := by
          omega
        subst k
        simp [lookup]

/-
exercise (3-star)
Verify the third equation, once again for `ins` instead of `insert`.
The same hints as for the second equation hold.
-/
theorem lookup_ins_neq {α : Type u} (d : α) t k vk
    : BST t → k ≠ k' → lookup d k' (ins k vk t) = lookup d k' t := by
  intro hbst
  induction hbst generalizing k' with
  | empty =>
    intro hk_ne
    by_cases hk'lt : k' < k
    · simp [ins, lookup, hk'lt]
    · by_cases hk'gt : k' > k
      · simp [ins, lookup, hk'lt, hk'gt]
      · exfalso
        apply hk_ne
        omega
  | tree c l k0 v0 r hlt hgt hbstl hbstr ihl ihr =>
    intro hk_ne
    simp only [ins]
    split
    · have hleft : lookup d k' (ins k vk l) = lookup d k' l := by
        exact ihl hk_ne
      simpa [lookup, hleft] using
        (balance_lookup d c k0 k' v0 (ins k vk l) r
          (ins_BST l k vk hbstl) hbstr
          (insP (fun x _ => x < k0) l k vk hlt ‹k < k0›) hgt)
    · split
      · have hright : lookup d k' (ins k vk r) = lookup d k' r := by
          exact ihr hk_ne
        simpa [lookup, hright] using
          (balance_lookup d c k0 k' v0 l (ins k vk r)
            hbstl (ins_BST r k vk hbstr)
            hlt (insP (fun x _ => x > k0) r k vk hgt ‹k > k0›))
      · have hk_eq : k = k0 := by
          omega
        subst k
        by_cases hk'lt : k' < k0
        · simp [lookup, hk'lt]
        · by_cases hk'gt : k' > k0
          · simp [lookup, hk'lt, hk'gt]
          · exfalso
            apply hk_ne
            omega

/-
## references
* [Chris Okasaki. Red-black trees in a functional setting. Journal of Functional Programming. 1999;9(4):471-477.](https://doi.org/10.1017/S0956796899003494)
* [Software Foundations, Volume 3 Verified Functional Algorithms: Red-Black Trees](https://softwarefoundations.cis.upenn.edu/vfa-current/Redblack.html)
* [Theorem Proving in Lean 4: Tactics](https://leanprover.github.io/theorem_proving_in_lean4/tactics.html)
-/
