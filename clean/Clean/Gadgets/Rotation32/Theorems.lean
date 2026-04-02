import Clean.Utils.Field
import Clean.Utils.Bitwise
import Clean.Utils.Rotation
import Clean.Types.U32
import Clean.Gadgets.ByteDecomposition.ByteDecomposition

variable {p : ℕ} [Fact p.Prime]
variable [p_large_enough: Fact (p > 2^16 + 2^8)]

namespace Gadgets.Rotation32.Theorems
open Gadgets.ByteDecomposition.Theorems (byteDecomposition_lift)
open Utils.Rotation

/--
We define a bit rotation on byte vectors like U32 by splitting each byte
into low and high bits, and moving the lowest low bits to the top and concatenating
each resulting (high, low) pair again.

The ultimate goal is to prove that this is equivalent to `rotRight32`.
-/
def rotRight32_bytes (xs : Vector ℕ 4) (o : ℕ) : Vector ℕ 4 :=
  .ofFn fun ⟨ i, hi ⟩ => xs[i] / 2^o + (xs[(i + 1) % 4] % 2^o) * 2^(8-o)

-- unfold what rotRight32_bytes does on a U32
def rotRight32_u32 : U32 ℕ → ℕ → U32 ℕ
  | ⟨ x0, x1, x2, x3 ⟩, o => ⟨
    (x0 / 2^o) + (x1 % 2^o) * 2^(8-o),
    (x1 / 2^o) + (x2 % 2^o) * 2^(8-o),
    (x2 / 2^o) + (x3 % 2^o) * 2^(8-o),
    (x3 / 2^o) + (x0 % 2^o) * 2^(8-o),
  ⟩

-- these two are definitionally equal
lemma rotRight32_bytes_u32_eq (o : ℕ) (x : U32 ℕ) :
  rotRight32_bytes x.toLimbs o = (rotRight32_u32 x o).toLimbs := rfl

lemma h_mod32 {o : ℕ} (ho : o < 8) {x0 x1 x2 x3 : ℕ} :
    (x0 + x1 * 256 + x2 * 256^2 + x3 * 256^3) % 2^o = x0 % 2^o := by
  nth_rw 1 [←Nat.pow_one 256]
  repeat rw [Nat.add_mod, mul_mod256_off ho _ _ (by trivial), add_zero, Nat.mod_mod]

lemma h_div32 {o : ℕ} (ho : o < 8) {x0 x1 x2 x3: ℕ} :
    (x0 + x1 * 256 + x2 * 256^2 + x3 * 256^3) / 2^o
    = x0 / 2^o + x1 * 2^(8-o) + x2 * 256 * 2^(8-o) + x3 * 256^2 * 2^(8-o) := by
  rw [←Nat.pow_one 256]
  repeat rw [Nat.add_div_of_dvd_left (by apply divides_256_two_power ho; linarith)]

  rw [mul_div_256_off ho 1 (by simp only [gt_iff_lt, Nat.lt_one_iff, pos_of_gt])]
  rw [mul_div_256_off ho 2 (by simp only [gt_iff_lt, Nat.ofNat_pos])]
  rw [mul_div_256_off ho 3 (by simp only [gt_iff_lt, Nat.ofNat_pos])]
  simp only [tsub_self, pow_zero, mul_one, Nat.add_one_sub_one, pow_one, Nat.reducePow]

lemma h_x0_const32 {o : ℕ} (ho : o < 8) :
    2^(8-o) * 256^3 = 2^(32-o) := by
  rw [show 256 = 2^8 by rfl, ←Nat.pow_mul, ←Nat.pow_add, pow_right_inj₀ (by norm_num) (by norm_num)]
  omega

theorem rotation32_recombine_x1 (offset a z : ℕ) : a % 2 ^ offset * 2 ^ (8 - offset) + (2 ^ offset * (a / 2 ^ offset) * 2 ^ (8 - offset) + z) = a * 2 ^ (8 - offset) + z := by
  rw [← add_assoc]
  rw [soundness_simp']

theorem rotation32_recombine_x2 (offset a z : ℕ) : a % 2 ^ offset * 256 * 2 ^ (8 - offset) + (2 ^ offset * (a / 2 ^ offset) * 2 ^ (8 - offset) * 256 + z) = a * 256 * 2 ^ (8 - offset) + z := by
  calc
    a % 2 ^ offset * 256 * 2 ^ (8 - offset)
        + (2 ^ offset * (a / 2 ^ offset) * 2 ^ (8 - offset) * 256 + z)
        = a % 2 ^ offset * 2 ^ (8 - offset) * 256
            + (2 ^ offset * (a / 2 ^ offset) * 2 ^ (8 - offset) * 256 + z) := by
              ac_rfl
    _ = a * 256 * 2 ^ (8 - offset) + z := by
          rw [← add_assoc]
          rw [soundness_simp]

theorem rotation32_recombine_x3 (offset a z : ℕ) : a % 2 ^ offset * 2 ^ (8 - offset) * 256 ^ 2 + (2 ^ offset * (a / 2 ^ offset) * 2 ^ (8 - offset) * 256 ^ 2 + z) = a * 256 ^ 2 * 2 ^ (8 - offset) + z := by
  rw [← add_assoc]
  rw [soundness_simp]

theorem rotation32_bits_soundness {o : ℕ} (ho : o < 8) {x : U32 ℕ} :
    (rotRight32_u32 x o).valueNat = rotRight32 x.valueNat o := by
  simp only [rotRight32, rotRight32_u32, U32.valueNat]
  have offset_mod_32 : o % 32 = o := Nat.mod_eq_of_lt (by linarith)
  simp only [offset_mod_32]
  rw [h_mod32 ho, h_div32 ho]
  rw [shifted_decomposition_eq ho]
  rw [shifted_decomposition_eq'' ho (by simp only [gt_iff_lt, Nat.ofNat_pos])]
  rw [shifted_decomposition_eq'' ho (by simp only [gt_iff_lt, Nat.ofNat_pos])]
  simp only [Nat.add_one_sub_one, pow_one, add_mul, add_assoc]
  rw [rotation32_recombine_x1 (offset := o) (a := x.x1)]
  rw [rotation32_recombine_x2 (offset := o) (a := x.x2)]
  rw [rotation32_recombine_x3 (offset := o) (a := x.x3)]
  rw [← h_x0_const32 ho]
  ac_rfl

end Gadgets.Rotation32.Theorems
