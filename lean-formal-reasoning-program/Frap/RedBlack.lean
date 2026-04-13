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

/- A complete proof appears below as `balance_BST`. -/

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

theorem balance_BST_black_ll {α : Type _} (a b c d : Tree α) (x y z : Nat) (vx vy vz : α) :
  ForallTree (fun t _ => t < z) (tree Color.red (tree Color.red a x vx b) y vy c) ->
  ForallTree (fun t _ => t > z) d ->
  BST (tree Color.red (tree Color.red a x vx b) y vy c) ->
  BST d ->
  BST (tree Color.red (tree Color.black a x vx b) y vy (tree Color.black c z vz d)) := by
  intro hltz hgtz hbst hbstd
  cases hltz with
  | tree _ _ _ _ _ hy_lt_z hleft_lt_z hc_lt_z =>
    cases hbst with
    | tree _ _ _ _ _ hleft_lt_y hc_gt_y hbst_left hbst_c =>
      cases hbst_left with
      | tree _ _ _ _ _ ha_lt_x hb_gt_x hbst_a hbst_b =>
        constructor
        · cases hleft_lt_y with
          | tree _ _ _ _ _ hx_lt_y ha_lt_y hb_lt_y =>
            constructor <;> assumption
        · constructor
          · exact hy_lt_z
          · exact hc_gt_y
          · exact forallTree_gt d z y hgtz hy_lt_z
        · constructor <;> assumption
        · constructor <;> assumption

theorem balance_BST_black_lr {α : Type _} (a b c d : Tree α) (x y z : Nat) (vx vy vz : α) :
  ForallTree (fun t _ => t < z) (tree Color.red a x vx (tree Color.red b y vy c)) ->
  ForallTree (fun t _ => t > z) d ->
  BST (tree Color.red a x vx (tree Color.red b y vy c)) ->
  BST d ->
  BST (tree Color.red (tree Color.black a x vx b) y vy (tree Color.black c z vz d)) := by
  intro hltz hdgtz hbst hbd
  cases hltz with
  | tree _ _ _ _ _ hxz haz hrightz =>
    cases hrightz with
    | tree _ _ _ _ _ hyz hbz hcz =>
      cases hbst with
      | tree _ _ _ _ _ hax hrightx hba hbst' =>
        cases hrightx with
        | tree _ _ _ _ _ hyx hbx hcx =>
          cases hbst' with
          | tree _ _ _ _ _ hby hcy hbb hbc =>
            constructor
            · constructor
              · exact hyx
              · exact forallTree_lt a x y hax hyx
              · exact hby
            · constructor
              · exact hyz
              · exact hcy
              · exact forallTree_gt d z y hdgtz hyz
            · constructor <;> assumption
            · constructor <;> assumption

theorem balance_BST_black_rl_branch {α : Type _} (l b c d : Tree α) (k y z : Nat) (vk vy vz : α) :
  ForallTree (fun t _ => t < k) l ->
  ForallTree (fun t _ => t > k) (tree Color.red (tree Color.red b y vy c) z vz d) ->
  BST l ->
  BST (tree Color.red (tree Color.red b y vy c) z vz d) ->
  BST (tree Color.red (tree Color.black l k vk b) y vy (tree Color.black c z vz d)) := by
  intro hlk hkr hbl hbr
  cases hkr with
  | tree _ _ _ _ _ _ hmid_gt_k hd_gt_k =>
      cases hmid_gt_k with
      | tree _ _ _ _ _ hy_gt_k hb_gt_k hc_gt_k =>
          cases hbr with
          | tree _ _ _ _ _ hmid_lt_z hd_gt_z hbst_mid hbd =>
              cases hmid_lt_z with
              | tree _ _ _ _ _ hy_lt_z hb_lt_z hc_lt_z =>
                  cases hbst_mid with
                  | tree _ _ _ _ _ hb_lt_y hc_gt_y hbb hbc =>
                      exact
                        BST.tree Color.red
                          (tree Color.black l k vk b) y vy (tree Color.black c z vz d)
                          (ForallTree.tree Color.black l k vk b hy_gt_k (forallTree_lt l k y hlk hy_gt_k) hb_lt_y)
                          (ForallTree.tree Color.black c z vz d hy_lt_z hc_gt_y (forallTree_gt d z y hd_gt_z hy_lt_z))
                          (BST.tree Color.black l k vk b hlk hb_gt_k hbl hbb)
                          (BST.tree Color.black c z vz d hc_lt_z hd_gt_z hbc hbd)

theorem balance_BST_black_rr {α : Type _} (a b c d : Tree α) (x y z : Nat) (vx vy vz : α) :
  ForallTree (fun t _ => t < x) a ->
  ForallTree (fun t _ => t > x) (tree Color.red b y vy (tree Color.red c z vz d)) ->
  BST a ->
  BST (tree Color.red b y vy (tree Color.red c z vz d)) ->
  BST (tree Color.red (tree Color.black a x vx b) y vy (tree Color.black c z vz d)) := by
  intro hax hgtx hba hbst
  cases hgtx with
  | tree _ _ _ _ _ hy_gt_x hb_gt_x hright_gt_x =>
      cases hright_gt_x with
      | tree _ _ _ _ _ hz_gt_x hc_gt_x hd_gt_x =>
          cases hbst with
          | tree _ _ _ _ _ hb_lt_y hright_gt_y hbb hbst_right =>
              cases hright_gt_y with
              | tree _ _ _ _ _ hz_gt_y hc_gt_y hd_gt_y =>
                  cases hbst_right with
                  | tree _ _ _ _ _ hc_lt_z hd_gt_z hbc hbd =>
                      exact
                        BST.tree Color.red
                          (tree Color.black a x vx b) y vy (tree Color.black c z vz d)
                          (ForallTree.tree Color.black a x vx b hy_gt_x (forallTree_lt a x y hax hy_gt_x) hb_lt_y)
                          (ForallTree.tree Color.black c z vz d hz_gt_y hc_gt_y hd_gt_y)
                          (BST.tree Color.black a x vx b hax hb_gt_x hba hbb)
                          (BST.tree Color.black c z vz d hc_lt_z hd_gt_z hbc hbd)

theorem balance_BST {α : Type u} c (l : Tree α) k vk (r : Tree α) :
  ForallTree (fun x _ => x < k) l ->
  ForallTree (fun x _ => x > k) r ->
  BST l ->
  BST r ->
  BST (balance c l k vk r) := by
  intro hlk hkr hbl hbr
  cases c with
  | red =>
      simpa only [balance] using (BST.tree Color.red l k vk r hlk hkr hbl hbr)
  | black =>
      simp only [balance]
      split
      · subst_eqs
        exact balance_BST_black_ll _ _ _ _ _ _ _ _ _ _ hlk hkr hbl hbr
      · subst_eqs
        exact balance_BST_black_lr _ _ _ _ _ _ _ _ _ _ hlk hkr hbl hbr
      · subst_eqs
        exact balance_BST_black_rl_branch _ _ _ _ _ _ _ _ _ _ hlk hkr hbl hbr
      · subst_eqs
        exact balance_BST_black_rr _ _ _ _ _ _ _ _ _ _ hlk hkr hbl hbr
      · exact BST.tree Color.black l k vk r hlk hkr hbl hbr


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
      exact ForallTree.tree Color.red l k vk r hp hpl hpr
  | black =>
      simp only [balance]
      repeat' split
      · subst_eqs
        cases hpl with
        | tree _ _ _ _ _ hy hll hlr =>
          cases hll with
          | tree _ _ _ _ _ hx ha hb =>
            exact
              ForallTree.tree Color.red _ _ _ _ hy
                (ForallTree.tree Color.black _ _ _ _ hx ha hb)
                (ForallTree.tree Color.black _ _ _ _ hp hlr hpr)
      · subst_eqs
        cases hpl with
        | tree _ _ _ _ _ hx hleft hright =>
          cases hright with
          | tree _ _ _ _ _ hy hb hc =>
            exact
              ForallTree.tree Color.red _ _ _ _ hy
                (ForallTree.tree Color.black _ _ _ _ hx hleft hb)
                (ForallTree.tree Color.black _ _ _ _ hp hc hpr)
      · subst_eqs
        cases hpr with
        | tree _ _ _ _ _ hz hleft hright =>
          cases hleft with
          | tree _ _ _ _ _ hy hb hc =>
            exact
              ForallTree.tree Color.red _ _ _ _ hy
                (ForallTree.tree Color.black _ _ _ _ hp hpl hb)
                (ForallTree.tree Color.black _ _ _ _ hz hc hright)
      · subst_eqs
        cases hpr with
        | tree _ _ _ _ _ hy hb hright =>
          cases hright with
          | tree _ _ _ _ _ hz hc hd =>
            exact
              ForallTree.tree Color.red _ _ _ _ hy
                (ForallTree.tree Color.black _ _ _ _ hp hpl hb)
                (ForallTree.tree Color.black _ _ _ _ hz hc hd)
      · exact ForallTree.tree Color.black l k vk r hp hpl hpr



/-
exercise (2-star)
Prove that `ins` preserves `ForallTree P`.
Hint: proceed by induction on `t`.
Use `balanceP`.
-/
theorem insP {α : Type u} (P : Nat → α → Prop) (t : Tree α) k vk
    : ForallTree P t → P k vk
      → ForallTree P (ins k vk t) := by
  intro hpt hpk
  induction hpt with
  | empty =>
      exact
        ForallTree.tree Color.red empty k vk empty hpk
          ForallTree.empty ForallTree.empty
  | tree c l k' v r hroot hl hr ihl ihr =>
      simp [ins]
      split
      · exact balanceP P c _ _ _ _ ihl hr hroot
      · split
        · exact balanceP P c _ _ _ _ hl ihr hroot
        · exact ForallTree.tree c l k vk r hpk hl hr

/-
exercise (3-star)
Prove that `ins` maintains `BST`.
Proceed by induction on `t`.
-/
theorem ins_BST {α : Type u} (t : Tree α) k vk : BST t → BST (ins k vk t) := by
  intro hbst
  induction hbst with
  | empty =>
      exact
        BST.tree Color.red empty k vk empty
          ForallTree.empty ForallTree.empty BST.empty BST.empty
  | tree c l k' v r hlt hgt hbl hbr ihl ihr =>
      simp [ins]
      split
      · exact
          balance_BST c _ _ _ _
            (insP (fun x _ => x < k') l k vk hlt ‹k < k'›)
            hgt ihl hbr
      · split
        · exact
            balance_BST c _ _ _ _
              hlt
              (insP (fun x _ => x > k') r k vk hgt ‹k > k'›)
              hbl ihr
        · have hk : k' = k := by omega
          subst k'
          exact BST.tree c l k vk r hlt hgt hbl hbr

/-
## Verification

1. `lookup d k empty_tree = d`
2. `lookup d k (insert k vk t) = vk`
3. `lookup d k' (insert k vk t) = lookup d k' t       if k ≠ k'`
-/

theorem lookup_empty {α : Type u} (d : α) (k : Nat)
    : lookup d k empty_tree = d := by
  rfl

theorem balance_lookup_black_ll {α : Type u} (d : α) k' (a b c d' : Tree α)
    (x y z : Nat) (vx vy vz : α) :
    BST d' ->
    ForallTree (fun t _ => t > z) d' ->
    BST (tree Color.red (tree Color.red a x vx b) y vy c) ->
    ForallTree (fun t _ => t < z) (tree Color.red (tree Color.red a x vx b) y vy c) ->
    lookup d k' (tree Color.red (tree Color.black a x vx b) y vy (tree Color.black c z vz d')) =
      if k' < z then lookup d k' (tree Color.red (tree Color.red a x vx b) y vy c)
      else if k' > z then lookup d k' d'
      else vz := by
  intro hbd hdgtz hbst hltz
  cases hltz with
  | tree _ _ _ _ _ hy_lt_z hleft_lt_z hc_lt_z =>
    cases hbst with
    | tree _ _ _ _ _ hleft_lt_y hc_gt_y hbst_left hbst_c =>
      cases hbst_left with
      | tree _ _ _ _ _ ha_lt_x hb_gt_x hbst_a hbst_b =>
        cases hleft_lt_y with
        | tree _ _ _ _ _ hx_lt_y ha_lt_y hb_lt_y =>
          simp [lookup]
          repeat' (first | split | simp [*] at * | omega)

theorem balance_lookup_black_lr {α : Type u} (d : α) k' (a b c d' : Tree α)
    (x y z : Nat) (vx vy vz : α) :
    BST d' ->
    ForallTree (fun t _ => t > z) d' ->
    BST (tree Color.red a x vx (tree Color.red b y vy c)) ->
    ForallTree (fun t _ => t < z) (tree Color.red a x vx (tree Color.red b y vy c)) ->
    lookup d k' (tree Color.red (tree Color.black a x vx b) y vy (tree Color.black c z vz d')) =
      if k' < z then lookup d k' (tree Color.red a x vx (tree Color.red b y vy c))
      else if k' > z then lookup d k' d'
      else vz := by
  intro hbd hdgtz hbst hltz
  cases hltz with
  | tree _ _ _ _ _ hx_lt_z ha_lt_z hright_lt_z =>
    cases hright_lt_z with
    | tree _ _ _ _ _ hy_lt_z hb_lt_z hc_lt_z =>
      cases hbst with
      | tree _ _ _ _ _ ha_lt_x hright_gt_x hbst_a hbst_right =>
        cases hright_gt_x with
        | tree _ _ _ _ _ hy_gt_x hb_gt_x hc_gt_x =>
          cases hbst_right with
          | tree _ _ _ _ _ hb_lt_y hc_gt_y hbst_b hbst_c =>
            simp [lookup]
            repeat' (first | split | simp [*] at * | omega)

theorem balance_lookup_black_rl {α : Type u} (d : α) k' (a b c d' : Tree α)
    (x y z : Nat) (vx vy vz : α) :
    BST a ->
    ForallTree (fun t _ => t < x) a ->
    BST (tree Color.red (tree Color.red b y vy c) z vz d') ->
    ForallTree (fun t _ => t > x) (tree Color.red (tree Color.red b y vy c) z vz d') ->
    lookup d k' (tree Color.red (tree Color.black a x vx b) y vy (tree Color.black c z vz d')) =
      if k' < x then lookup d k' a
      else if k' > x then lookup d k' (tree Color.red (tree Color.red b y vy c) z vz d')
      else vx := by
  intro hba hltx hbst hgtx
  cases hgtx with
  | tree _ _ _ _ _ hz_gt_x hmid_gt_x hd_gt_x =>
    cases hmid_gt_x with
    | tree _ _ _ _ _ hy_gt_x hb_gt_x hc_gt_x =>
      cases hbst with
      | tree _ _ _ _ _ hmid_lt_z hd_gt_z hbst_mid hbst_d =>
        cases hmid_lt_z with
        | tree _ _ _ _ _ hy_lt_z hb_lt_z hc_lt_z =>
          cases hbst_mid with
          | tree _ _ _ _ _ hb_lt_y hc_gt_y hbst_b hbst_c =>
            simp [lookup]
            repeat' (first | split | simp [*] at * | omega)

theorem balance_lookup_black_rr {α : Type u} (d : α) k' (a b c d' : Tree α)
    (x y z : Nat) (vx vy vz : α) :
    BST a ->
    ForallTree (fun t _ => t < x) a ->
    BST (tree Color.red b y vy (tree Color.red c z vz d')) ->
    ForallTree (fun t _ => t > x) (tree Color.red b y vy (tree Color.red c z vz d')) ->
    lookup d k' (tree Color.red (tree Color.black a x vx b) y vy (tree Color.black c z vz d')) =
      if k' < x then lookup d k' a
      else if k' > x then lookup d k' (tree Color.red b y vy (tree Color.red c z vz d'))
      else vx := by
  intro hba hltx hbst hgtx
  cases hgtx with
  | tree _ _ _ _ _ hy_gt_x hb_gt_x hright_gt_x =>
    cases hright_gt_x with
    | tree _ _ _ _ _ hz_gt_x hc_gt_x hd_gt_x =>
      cases hbst with
      | tree _ _ _ _ _ hb_lt_y hright_gt_y hbst_b hbst_right =>
        cases hright_gt_y with
        | tree _ _ _ _ _ hz_gt_y hc_gt_y hd_gt_y =>
          cases hbst_right with
          | tree _ _ _ _ _ hc_lt_z hd_gt_z hbst_c hbst_d =>
            simp [lookup]
            repeat' (first | split | simp [*] at * | omega)

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
  intro hbl hbr hlk hkr
  cases c with
  | red =>
      simp [balance, lookup]
  | black =>
      simp only [balance]
      split
      · subst_eqs
        simpa [lookup] using
          (balance_lookup_black_ll d k' _ _ _ _ _ _ _ _ _ _ hbr hkr hbl hlk)
      · subst_eqs
        simpa [lookup] using
          (balance_lookup_black_lr d k' _ _ _ _ _ _ _ _ _ _ hbr hkr hbl hlk)
      · subst_eqs
        simpa [lookup] using
          (balance_lookup_black_rl d k' _ _ _ _ _ _ _ _ _ _ hbl hlk hbr hkr)
      · subst_eqs
        simpa [lookup] using
          (balance_lookup_black_rr d k' _ _ _ _ _ _ _ _ _ _ hbl hlk hbr hkr)
      · simp [lookup]
        repeat' (first | split | simp [*] at * | omega)

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
  | tree c l k' v r hlt hgt hbl hbr ihl ihr =>
      simp [ins]
      split
      · simpa [*] using
          (balance_lookup d c k' k v (ins k vk l) r (ins_BST l k vk hbl) hbr
            (insP (fun x _ => x < k') l k vk hlt ‹k < k'›)
            hgt)
      · split
        · simpa [*] using
            (balance_lookup d c k' k v l (ins k vk r) hbl (ins_BST r k vk hbr)
              hlt
              (insP (fun x _ => x > k') r k vk hgt ‹k > k'›))
        · have hk : k = k' := by omega
          subst hk
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
      intro hneq
      simp [ins, lookup]
      omega
  | tree c l k0 v r hlt hgt hbl hbr ihl ihr =>
      intro hneq
      simp [ins]
      split
      · simpa [lookup, *, ihl (k' := k') hneq] using
          (balance_lookup d c k0 k' v (ins k vk l) r (ins_BST l k vk hbl) hbr
            (insP (fun x _ => x < k0) l k vk hlt ‹k < k0›)
            hgt)
      · split
        · simpa [lookup, *, ihr (k' := k') hneq] using
            (balance_lookup d c k0 k' v l (ins k vk r) hbl (ins_BST r k vk hbr)
              hlt
              (insP (fun x _ => x > k0) r k vk hgt ‹k > k0›))
        · have hk : k = k0 := by omega
          subst hk
          simp [lookup]
          repeat' (first | split | simp [*] at * | omega)

/-
## references
* [Chris Okasaki. Red-black trees in a functional setting. Journal of Functional Programming. 1999;9(4):471-477.](https://doi.org/10.1017/S0956796899003494)
* [Software Foundations, Volume 3 Verified Functional Algorithms: Red-Black Trees](https://softwarefoundations.cis.upenn.edu/vfa-current/Redblack.html)
* [Theorem Proving in Lean 4: Tactics](https://leanprover.github.io/theorem_proving_in_lean4/tactics.html)
-/
