import Clean.Utils.Field
import Clean.Utils.Bitwise
import Clean.Types.U64
import Clean.Types.U32

namespace Gadgets.ByteDecomposition.Theorems
variable {p : ℕ} [Fact p.Prime] [p_large_enough: Fact (p > 2^16 + 2^8)]
instance : Fact (p > 512) := .mk (by linarith [p_large_enough.elim])

open FieldUtils (two_val two_pow_val)

theorem byteDecomposition_lift {low high two_power : F p}
  (h_low : low.val < 2^8) (h_high : high.val < 2^8) (h_two_power : two_power.val ≤ 2^8) :
    (low + high * two_power).val = low.val + high.val * two_power.val := by
  field_to_nat
  suffices high.val * two_power.val < 2^8 * 2^8 by linarith [p_large_enough.elim]
  apply Nat.mul_lt_mul_of_lt_of_le (by assumption) (by assumption)
  apply Nat.pow_pos
  trivial

-- version of the above which requires stronger assumptions and provides a tight bound
theorem byteDecomposition_lt (o : ℕ) (ho : o ≤ 8) {low high : F p} (h_low : low.val < 2^o) (h_high : high.val < 2^(8-o)) :
    (low + high * (2^o : ℕ)).val < 2^8
    ∧ (low + high * (2^o : ℕ)).val = low.val + high.val * 2^o
     := by
  have : 2^8 < p := by linarith [p_large_enough.elim]
  have : 2^o ≤ 2^8 := Nat.pow_le_pow_of_le (show 2 > 1 by norm_num) (by omega)
  have h_base : ((2^o : ℕ) : F p).val = 2^o := ZMod.val_cast_of_lt (by linarith)
  have : high.val * 2^o + 2^o ≤ 2^8 := by
    suffices high.val * 2^o + 1 * 2^o ≤ 2^(8 - o) * 2^o by
      rw [←pow_add, show 8 - o + o = 8 by omega] at this
      linarith
    rw [←add_mul]
    exact Nat.mul_le_mul_right _ h_high
  field_to_nat
  rw [h_base]
  use by linarith
  rw [h_base]; linarith

theorem soundness_val_eq (offset : Fin 8) (x low high : F p) (low_lt : low.val < 2^offset.val) (high_lt : high.val < 2^8) (h_eq : x = low + high * 2^offset.val) : x.val = low.val + high.val * 2^offset.val := by
  have hpow_le_nat : 2 ^ offset.val ≤ 2 ^ 8 := by
    apply Nat.pow_le_pow_of_le
    · norm_num
    · exact Nat.le_of_lt offset.isLt
  have low_lt_256 : low.val < 2 ^ 8 := lt_of_lt_of_le low_lt hpow_le_nat
  have hpow_val : ((2 ^ offset.val : F p)).val = 2 ^ offset.val := by
    exact two_pow_val offset.val (by omega)
  rw [h_eq]
  have h_two_power : ((2 ^ offset.val : F p)).val ≤ 2 ^ 8 := by
    rw [hpow_val]
    exact hpow_le_nat
  have h_lift := byteDecomposition_lift low_lt_256 high_lt h_two_power
  simpa only [hpow_val] using h_lift

theorem soundness (offset : Fin 8) (x low high : F p)
  (x_lt : x.val < 2^8) (low_lt : low.val < 2^offset.val) (high_lt : high.val < 2^8)
  (h_eq : x = low + high * 2^offset.val) :
    low.val = x.val % 2^offset.val ∧ high.val = x.val / 2^offset.val := by
  have hx_nat : x.val = low.val + high.val * 2 ^ offset.val :=
    soundness_val_eq offset x low high low_lt high_lt h_eq
  constructor
  · rw [hx_nat, Nat.mul_comm]
    rw [Nat.add_mul_mod_self_left]
    exact (Nat.mod_eq_of_lt low_lt).symm
  · rw [hx_nat, Nat.mul_comm]
    rw [Nat.add_mul_div_left _ _ (Nat.pow_pos (by norm_num))]
    rw [Nat.div_eq_of_lt low_lt]
    norm_num


end Gadgets.ByteDecomposition.Theorems
