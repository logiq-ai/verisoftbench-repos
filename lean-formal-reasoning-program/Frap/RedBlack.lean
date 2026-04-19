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

theorem forallTree_mono {α : Type _} {p q : Nat → α → Prop} {t : Tree α} : (∀ x v, p x v → q x v) → ForallTree p t → ForallTree q t := by
  intro hmap h
  induction h with
  | empty =>
      exact ForallTree.empty
  | tree c l k v r hk hl hr ihl ihr =>
      exact ForallTree.tree c l k v r (hmap k v hk) ihl ihr

theorem balance_BST_black_left_left_clean {α : Type _} (a b c d : Tree α) (x y z : Nat) (vx vy vz : α) : ForallTree (fun t _ => t < z) (tree red (tree red a x vx b) y vy c) → ForallTree (fun t _ => t > z) d → BST (tree red (tree red a x vx b) y vy c) → BST d → BST (tree red (tree black a x vx b) y vy (tree black c z vz d)) := by
  intro hltz hgtz hbstL hbstd
  cases hltz with
  | tree _ _ _ _ _ hyz hltLL hltC =>
      cases hbstL with
      | tree _ _ _ _ _ hltY hgtY hBSTLL hBSTC =>
          cases hltY with
          | tree _ _ _ _ _ hxy hltA hltB =>
              cases hBSTLL with
              | tree _ _ _ _ _ hax hbx hBSTA hBSTB =>
                  have hdy : ForallTree (fun t _ => t > y) d :=
                    forallTree_mono (fun t v ht => Nat.lt_trans hyz ht) hgtz
                  refine BST.tree red (tree black a x vx b) y vy (tree black c z vz d) ?_ ?_ ?_ ?_
                  · exact ForallTree.tree black a x vx b hxy hltA hltB
                  · exact ForallTree.tree black c z vz d hyz hgtY hdy
                  · exact BST.tree black a x vx b hax hbx hBSTA hBSTB
                  · exact BST.tree black c z vz d hltC hgtz hBSTC hbstd

theorem balance_BST_black_left_right {α : Type _} (a b c d : Tree α) (x y z : Nat) (vx vy vz : α) : ForallTree (fun t _ => t < z) (tree red a x vx (tree red b y vy c)) → ForallTree (fun t _ => t > z) d → BST (tree red a x vx (tree red b y vy c)) → BST d → BST (tree red (tree black a x vx b) y vy (tree black c z vz d)) := by
  intro hltz hgtz hbst1 hbstd
  cases hbst1 with
  | tree _ _ _ _ _ hax hxR hbsta hbstR =>
    cases hxR with
    | tree _ _ _ _ _ hxy hxb hxc =>
      cases hbstR with
      | tree _ _ _ _ _ hby hyc hbstb hbstc =>
        cases hltz with
        | tree _ _ _ _ _ hxz haz hltzR =>
          cases hltzR with
          | tree _ _ _ _ _ hyz hbz hcz =>
            constructor
            · constructor
              · exact hxy
              · exact forallTree_mono (p := fun t _ => t < x) (q := fun t _ => t < y) (t := a) (fun t v ht => by omega) hax
              · exact hby
            · constructor
              · exact hyz
              · exact hyc
              · exact forallTree_mono (p := fun t _ => t > z) (q := fun t _ => t > y) (t := d) (fun t v ht => by omega) hgtz
            · constructor
              · exact hax
              · exact hxb
              · exact hbsta
              · exact hbstb
            · constructor
              · exact hcz
              · exact hgtz
              · exact hbstc
              · exact hbstd

theorem balance_BST_black_right_left_clean {α : Type _} (a b c d : Tree α) (x y z : Nat) (vx vy vz : α) : ForallTree (fun t _ => t < x) a → ForallTree (fun t _ => t > x) (tree red (tree red b y vy c) z vz d) → BST a → BST (tree red (tree red b y vy c) z vz d) → BST (tree red (tree black a x vx b) y vy (tree black c z vz d)) := by
  intro hax hrightx hbsta hbstR
  cases hrightx with
  | tree _ _ _ _ _ hxz hrightxL hdx =>
      cases hrightxL with
      | tree _ _ _ _ _ hxy hbx hcx =>
          cases hbstR with
          | tree _ _ _ _ _ hltz hgtz hbstBC hbstD =>
              cases hltz with
              | tree _ _ _ _ _ hyz hbz hcz =>
                  cases hbstBC with
                  | tree _ _ _ _ _ hby hcy hbstB hbstC =>
                      have hay : ForallTree (fun t _ => t < y) a :=
                        forallTree_mono (fun t v ht => Nat.lt_trans ht hxy) hax
                      have hdy : ForallTree (fun t _ => t > y) d :=
                        forallTree_mono (fun t v ht => Nat.lt_trans hyz ht) hgtz
                      refine BST.tree red (tree black a x vx b) y vy (tree black c z vz d) ?_ ?_ ?_ ?_
                      · exact ForallTree.tree black a x vx b hxy hay hby
                      · exact ForallTree.tree black c z vz d hyz hcy hdy
                      · exact BST.tree black a x vx b hax hbx hbsta hbstB
                      · exact BST.tree black c z vz d hcz hgtz hbstC hbstD

theorem balance_BST_black_right_right {α : Type _} (a b c d : Tree α) (x y z : Nat) (vx vy vz : α) : ForallTree (fun t _ => t < x) a → ForallTree (fun t _ => t > x) (tree red b y vy (tree red c z vz d)) → BST a → BST (tree red b y vy (tree red c z vz d)) → BST (tree red (tree black a x vx b) y vy (tree black c z vz d)) := by
  intro hax hrightx hba hbst_right
  cases hrightx with
  | tree _ _ _ _ _ hxy hbx hrightx' =>
    cases hbst_right with
    | tree _ _ _ _ _ hby hrighty hbb hbst_right' =>
      cases hrighty with
      | tree _ _ _ _ _ hyz hcy hdy =>
        cases hbst_right' with
        | tree _ _ _ _ _ hcz hdz hbc hbd =>
          have hay : ForallTree (fun t _ => t < y) a := by
            exact forallTree_lt a x y hax hxy
          constructor
          · constructor
            · exact hxy
            · exact hay
            · exact hby
          · constructor
            · exact hyz
            · exact hcy
            · exact hdy
          · constructor
            · exact hax
            · exact hbx
            · exact hba
            · exact hbb
          · constructor
            · exact hcz
            · exact hdz
            · exact hbc
            · exact hbd

theorem balance_BST {α : Type u} c (l : Tree α) k vk (r : Tree α)
    : ForallTree (fun x _ => x < k) l
      -> ForallTree (fun x _ => x > k) r
      -> BST l
      -> BST r
      -> BST (balance c l k vk r) := by
  intro hlt hgt hBSTl hBSTr
  cases c with
  | red =>
      simpa only [balance] using (BST.tree red l k vk r hlt hgt hBSTl hBSTr)
  | black =>
      simp [balance]
      repeat' split
      case h_1 htuple a x vx b y vy c z vz d heq =>
        cases heq
        exact balance_BST_black_left_left_clean a b c r x y k vx vy vk hlt hgt hBSTl hBSTr
      case h_2 htuple a x vx b y vy c z vz d hnot heq =>
        cases heq
        exact balance_BST_black_left_right a b c r x y k vx vy vk hlt hgt hBSTl hBSTr
      case h_3 htuple a x vx b y vy c z vz d hnot1 hnot2 heq =>
        cases heq
        exact balance_BST_black_right_left_clean l b c d k y z vk vy vz hlt hgt hBSTl hBSTr
      case h_4 htuple a x vx b y vy c z vz d hnot1 hnot2 hnot3 heq =>
        cases heq
        exact balance_BST_black_right_right l b c d k y z vk vy vz hlt hgt hBSTl hBSTr
      case h_5 =>
        exact BST.tree black l k vk r hlt hgt hBSTl hBSTr

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
      simpa [balance] using ForallTree.tree red l k vk r hp hpl hpr
  | black =>
      simp only [balance]
      split
      case h_1 htuple a x vx b y vy c z vz d heq =>
        cases heq
        cases hpl with
        | tree _ _ _ _ _ hy hll hc =>
            cases hll with
            | tree _ _ _ _ _ hx ha hb =>
                exact ForallTree.tree red (tree black a x vx b) y vy (tree black c k vk r) hy
                  (ForallTree.tree black a x vx b hx ha hb)
                  (ForallTree.tree black c k vk r hp hc hpr)
      case h_2 htuple a x vx b y vy c z vz d hnot heq =>
        cases heq
        cases hpl with
        | tree _ _ _ _ _ hx ha hright =>
            cases hright with
            | tree _ _ _ _ _ hy hb hc =>
                exact ForallTree.tree red (tree black a x vx b) y vy (tree black c k vk r) hy
                  (ForallTree.tree black a x vx b hx ha hb)
                  (ForallTree.tree black c k vk r hp hc hpr)
      case h_3 htuple a x vx b y vy c z vz d hnot1 hnot2 heq =>
        cases heq
        cases hpr with
        | tree _ _ _ _ _ hz hleft hd =>
            cases hleft with
            | tree _ _ _ _ _ hy hb hc =>
                exact ForallTree.tree red (tree black l k vk b) y vy (tree black c z vz d) hy
                  (ForallTree.tree black l k vk b hp hpl hb)
                  (ForallTree.tree black c z vz d hz hc hd)
      case h_4 htuple a x vx b y vy c z vz d hnot1 hnot2 hnot3 heq =>
        cases heq
        cases hpr with
        | tree _ _ _ _ _ hy hb hright =>
            cases hright with
            | tree _ _ _ _ _ hz hc hd =>
                exact ForallTree.tree red (tree black l k vk b) y vy (tree black c z vz d) hy
                  (ForallTree.tree black l k vk b hp hpl hb)
                  (ForallTree.tree black c z vz d hz hc hd)
      case h_5 =>
        exact ForallTree.tree black l k vk r hp hpl hpr



/-
exercise (2-star)
Prove that `ins` preserves `ForallTree P`.
Hint: proceed by induction on `t`.
Use `balanceP`.
-/
theorem insP {α : Type u} (P : Nat → α → Prop) (t : Tree α) k vk
    : ForallTree P t → P k vk
      → ForallTree P (ins k vk t) := by
  intro hP
  induction hP generalizing k vk with
  | empty =>
      intro hk
      simpa [ins] using ForallTree.tree red empty k vk empty hk ForallTree.empty ForallTree.empty
  | tree c l k' v r hroot hleft hright ihl ihr =>
      intro hk
      by_cases hlt : k < k'
      · simp [ins, hlt]
        exact balanceP P c (ins k vk l) k' v r (ihl (k := k) (vk := vk) hk) hright hroot
      · by_cases hgt : k > k'
        · simp [ins, hlt, hgt]
          exact balanceP P c l k' v (ins k vk r) hleft (ihr (k := k) (vk := vk) hk) hroot
        · simp [ins, hlt, hgt]
          exact ForallTree.tree c l k vk r hk hleft hright

/-
exercise (3-star)
Prove that `ins` maintains `BST`.
Proceed by induction on `t`.
-/
theorem ins_BST {α : Type u} (t : Tree α) k vk : BST t → BST (ins k vk t) := by
  intro hBST
  induction hBST with
  | empty =>
      simp [ins]
      constructor <;> constructor
  | tree c l k' v r hlt hgt hBSTl hBSTr ihl ihr =>
      by_cases hlt' : k < k'
      · simp [ins, hlt']
        exact balance_BST c (ins k vk l) k' v r
          (insP (fun x _ => x < k') l k vk hlt hlt')
          hgt
          ihl
          hBSTr
      · by_cases hgt' : k > k'
        · simp [ins, hlt', hgt']
          exact balance_BST c l k' v (ins k vk r)
            hlt
            (insP (fun x _ => x > k') r k vk hgt hgt')
            hBSTl
            ihr
        · simp [ins, hlt', hgt']
          have hk_eq : k' = k := by omega
          subst k'
          exact BST.tree c l k vk r hlt hgt hBSTl hBSTr

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
  intro hBSTl hBSTr hlt hgt
  cases c with
  | red =>
      simp [balance, lookup]
  | black =>
      simp only [balance]
      split
      case h_1 htuple a x vx b y vy c z vz d' heq =>
        cases heq
        cases hlt with
        | tree _ _ _ _ _ hyz hltLL hltC =>
            cases hBSTl with
            | tree _ _ _ _ _ hltY hgtY hBSTLL hBSTC =>
                cases hltY with
                | tree _ _ _ _ _ hxy hltA hltB =>
                    by_cases hky : k' < y
                    · have hkk : k' < k := by omega
                      by_cases hkx : k' < x
                      · simp [lookup, hky, hkk, hkx]
                      · by_cases hkx' : k' > x
                        · simp [lookup, hky, hkk, hkx, hkx']
                        · have hkxeq : k' = x := by omega
                          have hxk : x < k := by omega
                          simp [lookup, hky, hkk, hkx, hkx', hkxeq, hxy, hxk]
                    · by_cases hky' : k' > y
                      · by_cases hkk : k' < k
                        · simp [lookup, hky, hky', hkk]
                        · by_cases hkk' : k' > k
                          · simp [lookup, hky, hky', hkk, hkk']
                          · have hkkeq : k' = k := by omega
                            have hnyk : ¬ k < y := by omega
                            simp [lookup, hky, hky', hkk, hkk', hkkeq, hyz, hnyk]
                      · have hkyeq : k' = y := by omega
                        simp [lookup, hky, hky', hkyeq, hyz]
      case h_2 htuple a x vx b y vy c z vz d' hnot heq =>
        cases heq
        cases hBSTl with
        | tree _ _ _ _ _ hax hxR hbsta hbstR =>
            cases hxR with
            | tree _ _ _ _ _ hxy hxb hxc =>
                cases hlt with
                | tree _ _ _ _ _ hxz haz hltzR =>
                    cases hltzR with
                    | tree _ _ _ _ _ hyz hbz hcz =>
                        by_cases hky : k' < y
                        · have hkk : k' < k := by omega
                          by_cases hkx : k' < x
                          · simp [lookup, hky, hkk, hkx]
                          · by_cases hkx' : k' > x
                            · simp [lookup, hky, hkk, hkx, hkx']
                            · have hkxeq : k' = x := by omega
                              simp [lookup, hky, hkk, hkx, hkx', hkxeq, hxy, hxz]
                        · by_cases hky' : k' > y
                          · by_cases hkk : k' < k
                            · have hxk' : x < k' := by omega
                              have hnkx : ¬ k' < x := by omega
                              simp [lookup, hky, hky', hkk, hxk', hnkx]
                            · by_cases hkk' : k' > k
                              · simp [lookup, hky, hky', hkk, hkk']
                              · have hkkeq : k' = k := by omega
                                have hnyk : ¬ k < y := by omega
                                simp [lookup, hky, hky', hkk, hkk', hkkeq, hxy, hxz, hyz, hnyk]
                          · have hkyeq : k' = y := by omega
                            have hnyx : ¬ y < x := by omega
                            simp [lookup, hky, hky', hkyeq, hxy, hyz, hnyx]
      case h_3 htuple a x vx b y vy c z vz d' hnot1 hnot2 heq =>
        cases heq
        cases hgt with
        | tree _ _ _ _ _ hxz hrightxL hdx =>
            cases hrightxL with
            | tree _ _ _ _ _ hxy hbx hcx =>
                cases hBSTr with
                | tree _ _ _ _ _ hltz hgtz hbstBC hbstD =>
                    cases hltz with
                    | tree _ _ _ _ _ hyz hbz hcz =>
                        by_cases hky : k' < y
                        · by_cases hkk : k' < k
                          · simp [lookup, hky, hkk]
                          · by_cases hkk' : k' > k
                            · simp [lookup, hky, hkk, hkk']
                              have hkyz : k' < z := by omega
                              simp [lookup, hkyz]
                            · have hkkeq : k' = k := by omega
                              have hkz : k < z := by omega
                              simp [lookup, hky, hkk, hkk', hkkeq, hxy, hkz]
                        · by_cases hky' : k' > y
                          · by_cases hkz : k' < z
                            · have hkk'' : k < k' := by omega
                              have hnk : ¬ k' < k := by omega
                              simp [lookup, hky, hky', hkz, hkk'', hnk]
                            · by_cases hkz' : k' > z
                              · have hkk'' : k < k' := by omega
                                have hnk : ¬ k' < k := by omega
                                simp [lookup, hky, hky', hkz, hkz', hkk'', hnk]
                              · have hkzeq : k' = z := by omega
                                have hnzy : ¬ z < y := by omega
                                have hnzk : ¬ z < k := by omega
                                simp [lookup, hky, hky', hkz, hkz', hkzeq, hxy, hyz, hnzy, hnzk, hxz]
                          · have hkyeq : k' = y := by omega
                            have hnyk : ¬ y < k := by omega
                            simp [lookup, hky, hky', hkyeq, hxy, hyz, hnyk]
      case h_4 htuple a x vx b y vy c z vz d' hnot1 hnot2 hnot3 heq =>
        cases heq
        cases hgt with
        | tree _ _ _ _ _ hxy hbx hrightx' =>
            cases hBSTr with
            | tree _ _ _ _ _ hby hrighty hbb hbst_right' =>
                cases hrighty with
                | tree _ _ _ _ _ hyz hcy hdy =>
                    by_cases hky : k' < y
                    · by_cases hkk : k' < k
                      · simp [lookup, hky, hkk]
                      · by_cases hkk' : k' > k
                        · simp [lookup, hky, hkk, hkk']
                        · have hkkeq : k' = k := by omega
                          simp [lookup, hky, hkk, hkk', hkkeq, hxy]
                    · by_cases hky' : k' > y
                      · by_cases hkz : k' < z
                        · have hkk'' : k < k' := by omega
                          have hnk : ¬ k' < k := by omega
                          simp [lookup, hky, hky', hkz, hkk'', hnk]
                        · by_cases hkz' : k' > z
                          · have hkk'' : k < k' := by omega
                            have hnk : ¬ k' < k := by omega
                            simp [lookup, hky, hky', hkz, hkz', hkk'', hnk]
                          · have hkzeq : k' = z := by omega
                            have hnzy : ¬ z < y := by omega
                            have hnzk : ¬ z < k := by omega
                            have hkltz : k < z := by omega
                            simp [lookup, hky, hky', hkz, hkz', hkzeq, hxy, hyz, hnzy, hnzk, hkltz]
                      · have hkyeq : k' = y := by omega
                        have hnyk : ¬ y < k := by omega
                        simp [lookup, hky, hky', hkyeq, hxy, hnyk]
      case h_5 =>
        simp [lookup]

/-
exercise (3-star)
Verify the second equation, though for `ins` rather than `insert`.
Proceed by induction on the evidence that `t` is a `BST`.
Note that precondition `BST t` will be essential in your proof, unlike the ordinary BST's we saw last time.
-/
theorem lookup_ins_eq {α : Type u} (d : α) t k vk
    : BST t → lookup d k (ins k vk t) = vk := by
  intro hBST
  induction hBST with
  | empty =>
      simp [ins, lookup]
  | tree c l k' v r hlt hgt hBSTl hBSTr ihl ihr =>
      by_cases hlt' : k < k'
      · have hBSTins : BST (ins k vk l) := ins_BST l k vk hBSTl
        have hltins : ForallTree (fun x _ => x < k') (ins k vk l) :=
          insP (fun x _ => x < k') l k vk hlt hlt'
        simp only [ins, hlt']
        simp only [if_true, if_false]
        rw [balance_lookup (d := d) (c := c) (k := k') (k' := k) (vk := v) (l := ins k vk l) (r := r)
          hBSTins hBSTr hltins hgt]
        simp [hlt']
        exact ihl
      · by_cases hgt' : k > k'
        · have hBSTins : BST (ins k vk r) := ins_BST r k vk hBSTr
          have hgtins : ForallTree (fun x _ => x > k') (ins k vk r) :=
            insP (fun x _ => x > k') r k vk hgt hgt'
          simp only [ins, hlt', hgt']
          simp only [if_true, if_false]
          rw [balance_lookup (d := d) (c := c) (k := k') (k' := k) (vk := v) (l := l) (r := ins k vk r)
            hBSTl hBSTins hlt hgtins]
          simp [hlt', hgt']
          exact ihr
        · simp [ins, hlt', hgt', lookup]

/-
exercise (3-star)
Verify the third equation, once again for `ins` instead of `insert`.
The same hints as for the second equation hold.
-/
theorem lookup_ins_neq {α : Type u} (d : α) t k vk
    : BST t → k ≠ k' → lookup d k' (ins k vk t) = lookup d k' t := by
  intro hBST
  induction hBST generalizing k' with
  | empty =>
      intro hneq
      by_cases hk' : k' < k
      · simp [ins, lookup, hk']
      · by_cases hk'' : k' > k
        · simp [ins, lookup, hk', hk'']
        · have hEq : k' = k := by omega
          have : False := hneq hEq.symm
          contradiction
  | tree c l k0 v r hlt hgt hBSTl hBSTr ihl ihr =>
      intro hneq
      by_cases hlt' : k < k0
      · have hBSTins : BST (ins k vk l) := ins_BST l k vk hBSTl
        have hltins : ForallTree (fun x _ => x < k0) (ins k vk l) :=
          insP (fun x _ => x < k0) l k vk hlt hlt'
        simp only [ins, hlt']
        simp only [if_true, if_false]
        rw [balance_lookup (d := d) (c := c) (k := k0) (k' := k') (vk := v) (l := ins k vk l) (r := r)
          hBSTins hBSTr hltins hgt]
        by_cases hk' : k' < k0
        · simp [lookup, hk']
          exact ihl hneq
        · by_cases hk'' : k' > k0
          · simp [lookup, hk', hk'']
          · simp [lookup, hk', hk'']
      · by_cases hgt' : k > k0
        · have hBSTins : BST (ins k vk r) := ins_BST r k vk hBSTr
          have hgtins : ForallTree (fun x _ => x > k0) (ins k vk r) :=
            insP (fun x _ => x > k0) r k vk hgt hgt'
          simp only [ins, hlt', hgt']
          simp only [if_true, if_false]
          rw [balance_lookup (d := d) (c := c) (k := k0) (k' := k') (vk := v) (l := l) (r := ins k vk r)
            hBSTl hBSTins hlt hgtins]
          by_cases hk' : k' < k0
          · simp [lookup, hk']
          · by_cases hk'' : k' > k0
            · simp [lookup, hk', hk'']
              exact ihr hneq
            · simp [lookup, hk', hk'']
        · have hk0 : k0 = k := by omega
          subst k0
          by_cases hk' : k' < k
          · simp [ins, lookup, hlt', hgt', hk']
          · by_cases hk'' : k' > k
            · simp [ins, lookup, hlt', hgt', hk', hk'']
            · have hEq : k' = k := by omega
              have : False := hneq hEq.symm
              contradiction

/-
## references
* [Chris Okasaki. Red-black trees in a functional setting. Journal of Functional Programming. 1999;9(4):471-477.](https://doi.org/10.1017/S0956796899003494)
* [Software Foundations, Volume 3 Verified Functional Algorithms: Red-Black Trees](https://softwarefoundations.cis.upenn.edu/vfa-current/Redblack.html)
* [Theorem Proving in Lean 4: Tactics](https://leanprover.github.io/theorem_proving_in_lean4/tactics.html)
-/
