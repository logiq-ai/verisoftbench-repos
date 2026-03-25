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

theorem not_byte_val_int {x : F p} (hx : x.val < 256) : ((255 - x).val : ℤ) = 255 - ↑x.val := by
  have val_255 : (255 : F p).val = 255 := by
    exact FieldUtils.val_lt_p 255 (by linarith [p_large_enough.elim])
  have hx' : x.val ≤ (255 : F p).val := by
    rw [val_255]
    linarith
  rw [ZMod.val_sub hx', val_255]
  exact not_zify 256 hx

theorem not64_bytewise_value_normalized {x : U64 (F p)} (x_lt : x.Normalized) : (not64_bytewise_value x).Normalized := by
  rw [not64_bytewise_value, U64.map, U64.Normalized]
  rcases x_lt with ⟨hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7⟩
  have h (y : F p) (hy : y.val < 256) : (255 - y).val < 256 := by
    have h255 : ((255 : F p)).val = 255 := FieldUtils.val_lt_p 255 (by linarith [p_large_enough.elim])
    have hsub : (255 - y : F p).val = 255 - y.val := by
      rw [ZMod.val_sub]
      · rw [h255]
      · rw [h255]
        omega
    apply Int.ofNat_lt.mp
    rw [hsub, not_zify 256 hy]
    exact not_lt 256 hy
  exact ⟨h x.x0 hx0, h x.x1 hx1, h x.x2 hx2, h x.x3 hx3, h x.x4 hx4, h x.x5 hx5, h x.x6 hx6, h x.x7 hx7⟩

theorem not64_bytewise_value_value_eq_not64 {x : U64 (F p)} (x_lt : x.Normalized) : (not64_bytewise_value x).value = not64 x.value := by
  rw [not64_eq_sub (U64.value_lt_of_normalized x_lt)]
  rw [U64.value, not64_bytewise_value, U64.map]
  zify
  rw [not_zify (2^64) (U64.value_lt_of_normalized x_lt), U64.value]
  zify
  rcases x_lt with ⟨hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7⟩
  repeat rw [not_byte_val_int (by assumption)]
  ring

theorem not_bytewise_value_spec {x : U64 (F p)} (x_lt : x.Normalized) :
    (not64_bytewise_value x).value = not64 x.value
    ∧ (not64_bytewise_value x).Normalized := by
  exact ⟨not64_bytewise_value_value_eq_not64 x_lt, not64_bytewise_value_normalized x_lt⟩


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
