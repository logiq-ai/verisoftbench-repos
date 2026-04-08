import Clean.Utils.Primes
import Clean.Circuit.Basic
import Clean.Utils.Field
import Clean.Types.U64

section
variable {p : ℕ} [Fact p.Prime] [p_large_enough: Fact (p > 512)]

namespace Gadgets.Not

def not64_bytewise (x : Var U64 (F p)) : Var U64 (F p) := U64.map x (fun x => 255 - x)

def not64_bytewise_value (x : U64 (F p)) : U64 (F p) := x.map (fun x => 255 - x)

omit p_large_enough in
lemma eval_not {env} {x_var : Var U64 (F p)} :
    eval env (not64_bytewise x_var) = not64_bytewise_value (eval env x_var) := by
  rw [not64_bytewise, not64_bytewise_value, U64.map, U64.map]
  simp only [circuit_norm, explicit_provable_type]
  ring_nf

theorem not_zify (n : ℕ) {x : ℕ} (hx : x < n) : ((n - 1 - x : ℕ) : ℤ) = ↑n - 1 - ↑x := by
  have n_ge_1 : 1 ≤ n := by linarith
  have x_le : x ≤ n - 1 := Nat.le_pred_of_lt hx
  rw [Nat.cast_sub x_le, Nat.cast_sub n_ge_1]
  rfl

theorem not_lt (n : ℕ) {x : ℕ} (hx : x < n) : n - 1 - (x : ℤ) < n := by
  rw [←not_zify n hx, Int.ofNat_lt]
  exact Nat.sub_one_sub_lt_of_lt hx

theorem not_bytewise_value_spec {x : U64 (F p)} (x_lt : x.Normalized) :
    (not64_bytewise_value x).value = not64 x.value
    ∧ (not64_bytewise_value x).Normalized := by sorry

def circuit : FormalCircuit (F p) U64 U64 where
  main x := pure (not64_bytewise x)
  Assumptions x := x.Normalized
  Spec x z := z.value = not64 x.value ∧ z.Normalized

  localLength _ := 0
  output x _ := not64_bytewise x

  soundness := by
    intro i env x_var x h_input x_norm h_holds
    simp_all only [circuit_norm, eval_not]
    exact not_bytewise_value_spec x_norm

  completeness _ := by
    -- there are no constraints to satisfy!
    intros
    exact trivial

end Gadgets.Not
