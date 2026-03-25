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

theorem soundness_nat_eq (offset : Fin 8) (x low high : F p)
  (low_lt : low.val < 2^offset.val) (high_lt : high.val < 2^8)
  (h_eq : x = low + high * 2^offset.val) :
  x.val = low.val + high.val * 2^offset.val := by
  have hbase_le : 2 ^ offset.val ≤ 2 ^ 8 := by
    exact Nat.pow_le_pow_of_le (show 1 < 2 by norm_num) (Nat.le_of_lt offset.is_lt)
  have hlow8 : low.val < 2 ^ 8 := by
    exact lt_of_lt_of_le low_lt hbase_le
  have hbase_val : (((2 : F p) ^ offset.val)).val ≤ 2 ^ 8 := by
    rw [two_pow_val offset.val (Nat.le_of_lt offset.is_lt)]
    exact hbase_le
  calc
    x.val = (low + high * ((2 : F p) ^ offset.val)).val := by
      rw [h_eq]
    _ = low.val + high.val * (((2 : F p) ^ offset.val)).val := by
      exact byteDecomposition_lift (low := low) (high := high)
        (two_power := ((2 : F p) ^ offset.val)) hlow8 high_lt hbase_val
    _ = low.val + high.val * 2 ^ offset.val := by
      rw [two_pow_val offset.val (Nat.le_of_lt offset.is_lt)]

theorem soundness (offset : Fin 8) (x low high : F p)
  (x_lt : x.val < 2^8) (low_lt : low.val < 2^offset.val) (high_lt : high.val < 2^8)
  (h_eq : x = low + high * 2^offset.val) :
    low.val = x.val % 2^offset.val ∧ high.val = x.val / 2^offset.val := by
  have hnat : x.val = low.val + high.val * 2 ^ offset.val :=
    soundness_nat_eq offset x low high low_lt high_lt h_eq
  let base := 2 ^ offset.val
  have hbase_pos : 0 < base := by
    dsimp [base]
    exact Nat.pow_pos (by norm_num)
  constructor
  · rw [hnat, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt low_lt]
  · rw [hnat, Nat.add_mul_div_right _ _ hbase_pos, Nat.div_eq_of_lt low_lt, Nat.zero_add]


end Gadgets.ByteDecomposition.Theorems
