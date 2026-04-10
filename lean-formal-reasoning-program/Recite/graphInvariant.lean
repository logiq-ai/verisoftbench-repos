import Mathlib.Combinatorics.SimpleGraph.Basic

-- Let's say we have a type V (could be ℕ or anything)
variable {V : Type} (G : SimpleGraph V)

/-
  If G is a simple graph and u ~ v (i.e., u is adjacent to v), then u ≠ v.
-/

example {u v : V} (h : G.Adj u v) : u ≠ v := by
  -- By definition of adjacency in a simple graph, u and v cannot be the same vertex.
  intro h_eq
  rw [h_eq] at h
  -- The adjacency relation cannot hold if u and v are equal.
  exact G.loopless v h
