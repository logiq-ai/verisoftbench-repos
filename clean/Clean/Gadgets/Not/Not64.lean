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

theorem nat_byte_not_zify (x : ℕ) (hx : x < 256) : (((255 - x : ℕ) : ℤ)) = (256 : ℤ) - 1 - x := by
  simpa using (not_zify 256 (x := x) hx)

theorem not64_zify (x : ℕ) (hx : x < 2^64) : (((not64 x : ℕ) : ℤ)) = (2^64 : ℤ) - 1 - x := by
  rw [not64_eq_sub hx]
  simpa using (not_zify (2^64) (x := x) hx)

theorem not_byte_val (b : F p) (hb : b.val < 256) : (255 - b).val = 255 - b.val := by
  have h255 : ((255 : F p)).val = 255 := by
    exact FieldUtils.val_lt_p 255 (by linarith [p_large_enough.elim])
  have hb' : b.val ≤ ((255 : F p)).val := by
    rw [h255]
    exact Nat.le_pred_of_lt hb
  rw [ZMod.val_sub (a := (255 : F p)) (b := b) hb', h255]

theorem not_bytewise_value_arith (x0 x1 x2 x3 x4 x5 x6 x7 : ℕ) (hx0 : x0 < 256) (hx1 : x1 < 256) (hx2 : x2 < 256) (hx3 : x3 < 256) (hx4 : x4 < 256) (hx5 : x5 < 256) (hx6 : x6 < 256) (hx7 : x7 < 256) : (((255 - x0) + (255 - x1) * 256 + (255 - x2) * 256^2 + (255 - x3) * 256^3 + (255 - x4) * 256^4 + (255 - x5) * 256^5 + (255 - x6) * 256^6 + (255 - x7) * 256^7 : ℕ) : ℤ) = (2^64 : ℤ) - 1 - ((x0 + x1 * 256 + x2 * 256^2 + x3 * 256^3 + x4 * 256^4 + x5 * 256^5 + x6 * 256^6 + x7 * 256^7 : ℕ) : ℤ) := by
  have h0 : (((255 - x0 : ℕ) : ℤ)) = (256 : ℤ) - 1 - x0 := nat_byte_not_zify x0 hx0
  have h1 : (((255 - x1 : ℕ) : ℤ)) = (256 : ℤ) - 1 - x1 := nat_byte_not_zify x1 hx1
  have h2 : (((255 - x2 : ℕ) : ℤ)) = (256 : ℤ) - 1 - x2 := nat_byte_not_zify x2 hx2
  have h3 : (((255 - x3 : ℕ) : ℤ)) = (256 : ℤ) - 1 - x3 := nat_byte_not_zify x3 hx3
  have h4 : (((255 - x4 : ℕ) : ℤ)) = (256 : ℤ) - 1 - x4 := nat_byte_not_zify x4 hx4
  have h5 : (((255 - x5 : ℕ) : ℤ)) = (256 : ℤ) - 1 - x5 := nat_byte_not_zify x5 hx5
  have h6 : (((255 - x6 : ℕ) : ℤ)) = (256 : ℤ) - 1 - x6 := nat_byte_not_zify x6 hx6
  have h7 : (((255 - x7 : ℕ) : ℤ)) = (256 : ℤ) - 1 - x7 := nat_byte_not_zify x7 hx7
  push_cast
  rw [h0, h1, h2, h3, h4, h5, h6, h7]
  norm_num
  linarith [h0, h1, h2, h3, h4, h5, h6, h7]

theorem not_bytewise_value_spec {x : U64 (F p)} (x_lt : x.Normalized) :
    (not64_bytewise_value x).value = not64 x.value
    ∧ (not64_bytewise_value x).Normalized := by
  rcases x with ⟨x0, x1, x2, x3, x4, x5, x6, x7⟩
  rcases x_lt with ⟨hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7⟩
  let xu : U64 (F p) := U64.mk x0 x1 x2 x3 x4 x5 x6 x7
  have hxu : xu.Normalized := by
    exact ⟨hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7⟩
  have hxv : xu.value < 2^64 := U64.value_lt_of_normalized (x := xu) hxu
  have h0 : (255 - x0).val = 255 - x0.val := not_byte_val x0 hx0
  have h1 : (255 - x1).val = 255 - x1.val := not_byte_val x1 hx1
  have h2 : (255 - x2).val = 255 - x2.val := not_byte_val x2 hx2
  have h3 : (255 - x3).val = 255 - x3.val := not_byte_val x3 hx3
  have h4 : (255 - x4).val = 255 - x4.val := not_byte_val x4 hx4
  have h5 : (255 - x5).val = 255 - x5.val := not_byte_val x5 hx5
  have h6 : (255 - x6).val = 255 - x6.val := not_byte_val x6 hx6
  have h7 : (255 - x7).val = 255 - x7.val := not_byte_val x7 hx7
  constructor
  · have hleft : ((((not64_bytewise_value xu).value : ℕ) : ℤ)) = (2^64 : ℤ) - 1 - (xu.value : ℤ) := by
      simpa [xu, not64_bytewise_value, U64.map, U64.value, h0, h1, h2, h3, h4, h5, h6, h7] using
        not_bytewise_value_arith x0.val x1.val x2.val x3.val x4.val x5.val x6.val x7.val hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7
    have hright : (((not64 xu.value : ℕ) : ℤ)) = (2^64 : ℤ) - 1 - (xu.value : ℤ) := by
      exact not64_zify xu.value hxv
    exact Int.ofNat.inj (hleft.trans hright.symm)
  · simp only [xu, not64_bytewise_value, U64.map, U64.Normalized, h0, h1, h2, h3, h4, h5, h6, h7]
    exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩


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
