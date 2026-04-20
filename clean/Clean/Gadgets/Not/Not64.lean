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

theorem not_byte_val (a : F p) (ha : a.val < 256) : (255 - a).val = 255 - a.val := by
  have hp512 : p > 512 := p_large_enough.elim
  have h255ltp : 255 < p := lt_trans (by decide : 255 < 512) hp512
  have h255val : ((255 : F p)).val = 255 := by
    exact FieldUtils.val_lt_p 255 h255ltp
  have hle : a.val ≤ ((255 : F p)).val := by
    rw [h255val]
    exact Nat.le_pred_of_lt ha
  simpa [h255val] using (ZMod.val_sub hle)

theorem not64_bytewise_value_eq_sub {x : U64 (F p)} (x_lt : x.Normalized) : (not64_bytewise_value x).value = 2^64 - 1 - x.value := by
  rcases x_lt with ⟨hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7⟩
  simp only [not64_bytewise_value, U64.map, U64.value]
  rw [not_byte_val x.x0 hx0, not_byte_val x.x1 hx1, not_byte_val x.x2 hx2, not_byte_val x.x3 hx3,
    not_byte_val x.x4 hx4, not_byte_val x.x5 hx5, not_byte_val x.x6 hx6, not_byte_val x.x7 hx7]
  norm_num
  omega

theorem not_byte_lt (a : F p) (ha : a.val < 256) : (255 - a).val < 256 := by
  rw [not_byte_val a ha]
  omega

theorem not64_bytewise_value_normalized {x : U64 (F p)} (x_lt : x.Normalized) : (not64_bytewise_value x).Normalized := by
  rcases x with ⟨x0, x1, x2, x3, x4, x5, x6, x7⟩
  rcases x_lt with ⟨hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7⟩
  simp only [not64_bytewise_value, U64.map, U64.Normalized]
  exact ⟨not_byte_lt x0 hx0, not_byte_lt x1 hx1, not_byte_lt x2 hx2, not_byte_lt x3 hx3,
    not_byte_lt x4 hx4, not_byte_lt x5 hx5, not_byte_lt x6 hx6, not_byte_lt x7 hx7⟩

theorem not_bytewise_value_spec {x : U64 (F p)} (x_lt : x.Normalized) :
    (not64_bytewise_value x).value = not64 x.value
    ∧ (not64_bytewise_value x).Normalized := by
  constructor
  · have hx : x.value < 2^64 := U64.value_lt_of_normalized x_lt
    simpa [not64_eq_sub hx] using not64_bytewise_value_eq_sub x_lt
  · exact not64_bytewise_value_normalized x_lt


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
