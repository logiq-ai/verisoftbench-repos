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

theorem not_byte_val {a : F p} (ha : a.val < 256) : (255 - a).val = 255 - a.val := by
  have h255 : (255 : F p).val = 255 := by
    exact FieldUtils.val_lt_p 255 (by
      have hp' : p > 512 := p_large_enough.elim
      omega)
  have hle : a.val ≤ 255 := Nat.le_pred_of_lt ha
  have hle' : a.val ≤ (255 : F p).val := by
    simpa only [h255] using hle
  simpa only [h255] using (ZMod.val_sub (a := (255 : F p)) (b := a) hle')

theorem not_bytewise_value_spec {x : U64 (F p)} (x_lt : x.Normalized) :
    (not64_bytewise_value x).value = not64 x.value
    ∧ (not64_bytewise_value x).Normalized := by
  let ⟨hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7⟩ := x_lt
  have h0 : (255 - x.x0).val = 255 - x.x0.val := not_byte_val hx0
  have h1 : (255 - x.x1).val = 255 - x.x1.val := not_byte_val hx1
  have h2 : (255 - x.x2).val = 255 - x.x2.val := not_byte_val hx2
  have h3 : (255 - x.x3).val = 255 - x.x3.val := not_byte_val hx3
  have h4 : (255 - x.x4).val = 255 - x.x4.val := not_byte_val hx4
  have h5 : (255 - x.x5).val = 255 - x.x5.val := not_byte_val hx5
  have h6 : (255 - x.x6).val = 255 - x.x6.val := not_byte_val hx6
  have h7 : (255 - x.x7).val = 255 - x.x7.val := not_byte_val hx7
  refine ⟨?_, ?_⟩
  · have hxval : x.value < 2^64 := U64.value_lt_of_normalized x_lt
    rw [not64_eq_sub hxval]
    simp only [not64_bytewise_value, U64.map, U64.value, h0, h1, h2, h3, h4, h5, h6, h7]
    norm_num
    omega
  · simp only [not64_bytewise_value, U64.map, U64.Normalized, h0, h1, h2, h3, h4, h5, h6, h7]
    omega


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
