/- ──────────────────────────────────────────────────────────────────────────────
   Proofs/FromBytesSpec.lean — phase 2, decompress step 2: the byte parser.

   `FieldElement51::from_bytes` loads five 64-bit little-endian windows at
   byte offsets 0/6/12/19/24, shifts by 0/3/6/1/12, and masks to 51 bits —
   the windows tile bits 0..254 exactly, so

       feVal (from_bytes b) = bytesVal b mod 2²⁵⁵            (from_bytes_spec)

   — the top bit is discarded, everything else is exact. This is the y-parse
   of decompression: for a canonical encoding (y-residue + sign bit), the
   parsed field element denotes exactly the y-residue.

   Port delta (risc0/betrusted v4 gen): from_bytes takes RangeFrom subslices
   (`bytes[k..]`) and feeds them to a local `load8` CLOSURE with literal
   indices 0..7, instead of dalek's named `load8_at s offset`. Same
   disjoint-OR loader math; the walk adds a subslice step per window.
   ────────────────────────────────────────────────────────────────────────────── -/
import Proofs.DecompressSpec
open Aeneas Aeneas.Std Result
open curve25519_dalek

set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option maxRecDepth 8000

namespace CurveFieldProofs

open Aeneas.Std.WP

/-- Disjoint low-bits OR is addition (product-order-robust form). -/
theorem or_add_low {a b : ℕ} (k : ℕ) (ha : a < 2^k) :
    a ||| b * 2^k = a + b * 2^k := by
  have hor := Nat.two_pow_add_eq_or_of_lt (b := a) (i := k) ha b
  calc a ||| b * 2^k = a ||| 2^k * b := by rw [Nat.mul_comm b]
    _ = 2^k * b ||| a := Nat.lor_comm _ _
    _ = 2^k * b + a := hor.symm
    _ = a + b * 2^k := by ring

/-- RangeFrom slice indexing yields the tail slice (the `step_simps` set
    already reduces the Array.index wrapper to this form). -/
theorem range_from_index_spec (s : Slice Std.U8)
    (r : core.ops.range.RangeFrom Std.Usize) (h : r.start.val ≤ s.length) :
    core.slice.index.SliceIndexRangeFromUsizeSlice.index r s ⦃ s' =>
      s'.val = s.val.drop r.start.val ⦄ := by
  simp only [core.slice.index.SliceIndexRangeFromUsizeSlice.index]
  split
  · simp [spec_ok, Slice.drop]
  · scalar_tac

/-- Generic 8-byte little-endian loader (closure form): given the eight bytes
    at positions 0..7 of the subslice, the loaded word is their LE value. -/
theorem closure_call_spec (c : backend.serial.u64.field.FieldElement51.from_bytes.closure)
    (s : Slice Std.U8)
    (c0 c1 c2 c3 c4 c5 c6 c7 : Std.U8)
    (hlen : 7 < s.length)
    (h0 : s.val[(0:ℕ)]! = c0) (h1 : s.val[(1:ℕ)]! = c1)
    (h2 : s.val[(2:ℕ)]! = c2) (h3 : s.val[(3:ℕ)]! = c3)
    (h4 : s.val[(4:ℕ)]! = c4) (h5 : s.val[(5:ℕ)]! = c5)
    (h6 : s.val[(6:ℕ)]! = c6) (h7 : s.val[(7:ℕ)]! = c7) :
    backend.serial.u64.field.FieldElement51.from_bytes.closure.Insts.CoreOpsFunctionFnTupleSharedSliceU8U64.call
      c s ⦃ w =>
      w.val = c0.val + c1.val * 2^8 + c2.val * 2^16 + c3.val * 2^24
        + c4.val * 2^32 + c5.val * 2^40 + c6.val * 2^48 + c7.val * 2^56 ⦄ := by
  unfold backend.serial.u64.field.FieldElement51.from_bytes.closure.Insts.CoreOpsFunctionFnTupleSharedSliceU8U64.call
  step as ⟨x0, hx0⟩
  rw [← getElem!_pos (↑s : List Std.U8) 0 (by scalar_tac)] at hx0
  rw [h0] at hx0
  step as ⟨w0, hw0⟩
  have hw0v : w0.val = c0.val := by
    rw [hw0, UScalar.cast_val_eq, hx0]
    norm_num [UScalarTy.numBits]
    scalar_tac
  step as ⟨x1, hx1⟩
  rw [← getElem!_pos (↑s : List Std.U8) 1 (by scalar_tac)] at hx1
  rw [h1] at hx1
  step as ⟨y1, hy1⟩
  have hy1v : y1.val = c1.val := by
    rw [hy1, UScalar.cast_val_eq, hx1]
    norm_num [UScalarTy.numBits]
    scalar_tac
  step as ⟨t1, ht1⟩
  have ht1v : t1.val = c1.val * 2^8 := by
    rw [ht1]
    simp only [Nat.shiftLeft_eq, hy1v]
    rw [Nat.mod_eq_of_lt (show c1.val * 2^8 < U64.size by scalar_tac)]
  step as ⟨w1, hw1⟩
  have hw1v : w1.val = c0.val + c1.val * 2^8 := by
    rw [hw1, UScalar.val_or, hw0v, ht1v]
    rw [or_add_low 8 (by scalar_tac)]
    try ring
  clear hx1 hy1 hy1v ht1 ht1v hw0 hw0v
  step as ⟨x2, hx2⟩
  rw [← getElem!_pos (↑s : List Std.U8) 2 (by scalar_tac)] at hx2
  rw [h2] at hx2
  step as ⟨y2, hy2⟩
  have hy2v : y2.val = c2.val := by
    rw [hy2, UScalar.cast_val_eq, hx2]
    norm_num [UScalarTy.numBits]
    scalar_tac
  step as ⟨t2, ht2⟩
  have ht2v : t2.val = c2.val * 2^16 := by
    rw [ht2]
    simp only [Nat.shiftLeft_eq, hy2v]
    rw [Nat.mod_eq_of_lt (show c2.val * 2^16 < U64.size by scalar_tac)]
  step as ⟨w2, hw2⟩
  have hw2v : w2.val = c0.val + c1.val * 2^8 + c2.val * 2^16 := by
    rw [hw2, UScalar.val_or, hw1v, ht2v]
    rw [or_add_low 16 (by scalar_tac)]
    try ring
  clear hx2 hy2 hy2v ht2 ht2v hw1 hw1v
  step as ⟨x3, hx3⟩
  rw [← getElem!_pos (↑s : List Std.U8) 3 (by scalar_tac)] at hx3
  rw [h3] at hx3
  step as ⟨y3, hy3⟩
  have hy3v : y3.val = c3.val := by
    rw [hy3, UScalar.cast_val_eq, hx3]
    norm_num [UScalarTy.numBits]
    scalar_tac
  step as ⟨t3, ht3⟩
  have ht3v : t3.val = c3.val * 2^24 := by
    rw [ht3]
    simp only [Nat.shiftLeft_eq, hy3v]
    rw [Nat.mod_eq_of_lt (show c3.val * 2^24 < U64.size by scalar_tac)]
  step as ⟨w3, hw3⟩
  have hw3v : w3.val = c0.val + c1.val * 2^8 + c2.val * 2^16 + c3.val * 2^24 := by
    rw [hw3, UScalar.val_or, hw2v, ht3v]
    rw [or_add_low 24 (by scalar_tac)]
    try ring
  clear hx3 hy3 hy3v ht3 ht3v hw2 hw2v
  step as ⟨x4, hx4⟩
  rw [← getElem!_pos (↑s : List Std.U8) 4 (by scalar_tac)] at hx4
  rw [h4] at hx4
  step as ⟨y4, hy4⟩
  have hy4v : y4.val = c4.val := by
    rw [hy4, UScalar.cast_val_eq, hx4]
    norm_num [UScalarTy.numBits]
    scalar_tac
  step as ⟨t4, ht4⟩
  have ht4v : t4.val = c4.val * 2^32 := by
    rw [ht4]
    simp only [Nat.shiftLeft_eq, hy4v]
    rw [Nat.mod_eq_of_lt (show c4.val * 2^32 < U64.size by scalar_tac)]
  step as ⟨w4, hw4⟩
  have hw4v : w4.val = c0.val + c1.val * 2^8 + c2.val * 2^16 + c3.val * 2^24 + c4.val * 2^32 := by
    rw [hw4, UScalar.val_or, hw3v, ht4v]
    rw [or_add_low 32 (by scalar_tac)]
    try ring
  clear hx4 hy4 hy4v ht4 ht4v hw3 hw3v
  step as ⟨x5, hx5⟩
  rw [← getElem!_pos (↑s : List Std.U8) 5 (by scalar_tac)] at hx5
  rw [h5] at hx5
  step as ⟨y5, hy5⟩
  have hy5v : y5.val = c5.val := by
    rw [hy5, UScalar.cast_val_eq, hx5]
    norm_num [UScalarTy.numBits]
    scalar_tac
  step as ⟨t5, ht5⟩
  have ht5v : t5.val = c5.val * 2^40 := by
    rw [ht5]
    simp only [Nat.shiftLeft_eq, hy5v]
    rw [Nat.mod_eq_of_lt (show c5.val * 2^40 < U64.size by scalar_tac)]
  step as ⟨w5, hw5⟩
  have hw5v : w5.val = c0.val + c1.val * 2^8 + c2.val * 2^16 + c3.val * 2^24 + c4.val * 2^32 + c5.val * 2^40 := by
    rw [hw5, UScalar.val_or, hw4v, ht5v]
    rw [or_add_low 40 (by scalar_tac)]
    try ring
  clear hx5 hy5 hy5v ht5 ht5v hw4 hw4v
  step as ⟨x6, hx6⟩
  rw [← getElem!_pos (↑s : List Std.U8) 6 (by scalar_tac)] at hx6
  rw [h6] at hx6
  step as ⟨y6, hy6⟩
  have hy6v : y6.val = c6.val := by
    rw [hy6, UScalar.cast_val_eq, hx6]
    norm_num [UScalarTy.numBits]
    scalar_tac
  step as ⟨t6, ht6⟩
  have ht6v : t6.val = c6.val * 2^48 := by
    rw [ht6]
    simp only [Nat.shiftLeft_eq, hy6v]
    rw [Nat.mod_eq_of_lt (show c6.val * 2^48 < U64.size by scalar_tac)]
  step as ⟨w6, hw6⟩
  have hw6v : w6.val = c0.val + c1.val * 2^8 + c2.val * 2^16 + c3.val * 2^24 + c4.val * 2^32 + c5.val * 2^40 + c6.val * 2^48 := by
    rw [hw6, UScalar.val_or, hw5v, ht6v]
    rw [or_add_low 48 (by scalar_tac)]
    try ring
  clear hx6 hy6 hy6v ht6 ht6v hw5 hw5v
  step as ⟨x7, hx7⟩
  rw [← getElem!_pos (↑s : List Std.U8) 7 (by scalar_tac)] at hx7
  rw [h7] at hx7
  step as ⟨y7, hy7⟩
  have hy7v : y7.val = c7.val := by
    rw [hy7, UScalar.cast_val_eq, hx7]
    norm_num [UScalarTy.numBits]
    scalar_tac
  step as ⟨t7, ht7⟩
  have ht7v : t7.val = c7.val * 2^56 := by
    rw [ht7]
    simp only [Nat.shiftLeft_eq, hy7v]
    rw [Nat.mod_eq_of_lt (show c7.val * 2^56 < U64.size by scalar_tac)]
  try simp only [spec_ok]
  rw [UScalar.val_or, hw6v, ht7v]
  rw [or_add_low 56 (by scalar_tac)]
  try ring


/-- Extract a 64-bit window: with the value decomposed as low + 2^m·window
    + 2^m·2^64·high (window < 2^64, low < 2^m), division and mod recover the
    window. -/
theorem window_extract (Lo M H : ℕ) (m : ℕ) (hL : Lo < 2^m) (hM : M < 2^64) :
    (Lo + 2^m * M + 2^m * 2^64 * H) / 2^m % 2^64 = M := by
  have h1 : (Lo + 2^m * M + 2^m * 2^64 * H) / 2^m = M + 2^64 * H := by
    rw [show Lo + 2^m * M + 2^m * 2^64 * H = Lo + 2^m * (M + 2^64 * H) by ring]
    rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos m), Nat.div_eq_of_lt hL]
    omega
  rw [h1]
  omega

/-- Shift inside a 64-bit window: for sh + 51 ≤ 64,
    ((B/2^(8o)) mod 2^64 / 2^sh) mod 2^51 = (B / 2^(8o+sh)) mod 2^51. -/
theorem window_shift (B o sh : ℕ) (hsh : sh + 51 ≤ 64) :
    (B / 2^(8*o) % 2^64 / 2^sh) % 2^51 = B / 2^(8*o + sh) % 2^51 := by
  have h1 : B / 2^(8*o) % 2^64 / 2^sh = B / 2^(8*o) / 2^sh % 2^(64 - sh) := by
    have hsplit : (2:ℕ)^64 = 2^sh * 2^(64 - sh) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hsplit, Nat.mod_mul_right_div_self]
  rw [h1, Nat.div_div_eq_div_mul, ← pow_add]
  have h2 : B / 2^(8*o + sh) % 2^(64 - sh) % 2^51 = B / 2^(8*o + sh) % 2^51 := by
    apply Nat.mod_mod_of_dvd
    exact pow_dvd_pow 2 (by omega)
  rw [h2]

/-- Base-2⁵¹ five-digit tiling: the masked digits reassemble the value
    mod 2²⁵⁵. -/
theorem digits_tile (B : ℕ) :
    B % 2^51
      + (B / 2^51 % 2^51) * 2^51
      + (B / 2^102 % 2^51) * 2^102
      + (B / 2^153 % 2^51) * 2^153
      + (B / 2^204 % 2^51) * 2^204 = B % 2^255 := by
  have e1 : B / 2^51 / 2^51 = B / 2^102 := by rw [Nat.div_div_eq_div_mul]; norm_num
  have e2 : B / 2^102 / 2^51 = B / 2^153 := by rw [Nat.div_div_eq_div_mul]; norm_num
  have e3 : B / 2^153 / 2^51 = B / 2^204 := by rw [Nat.div_div_eq_div_mul]; norm_num
  have e4 : B / 2^204 / 2^51 = B / 2^255 := by rw [Nat.div_div_eq_div_mul]; norm_num
  have d0 := Nat.div_add_mod B (2^51)
  have d1 := Nat.div_add_mod (B / 2^51) (2^51)
  have d2 := Nat.div_add_mod (B / 2^102) (2^51)
  have d3 := Nat.div_add_mod (B / 2^153) (2^51)
  have d4 := Nat.div_add_mod (B / 2^204) (2^51)
  have dT := Nat.div_add_mod B (2^255)
  omega

/-- **The byte parser is exact below bit 255**: for any 32 input bytes,
    `from_bytes` succeeds with 51-bit limbs denoting `bytesVal b mod 2²⁵⁵`
    (the sign bit is discarded, the rest is the little-endian value). -/
theorem from_bytes_spec (bytes : Std.Array Std.U8 32#usize)
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 : Std.U8)
    (hbl : (↑bytes : List Std.U8) = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31]) :
    backend.serial.u64.field.FieldElement51.from_bytes bytes ⦃ r =>
      Bnd r (2^51) ∧ feVal r = bytesVal bytes % 2^255 ⦄ := by
  unfold backend.serial.u64.field.FieldElement51.from_bytes
  step as ⟨msk0, hmsk0⟩
  step as ⟨mask, hmask⟩
  have hmaskv : mask.val = 2251799813685247 := by
    rw [hmask, hmsk0]
    simp [Nat.shiftLeft_eq]
    scalar_tac
  -- window 0: bytes 0..7, shift 0
  step with (range_from_index_spec bytes.to_slice { start := 0#usize } (by scalar_tac))
    as ⟨s0, hs0v⟩
  step with (closure_call_spec () s0 b0 b1 b2 b3 b4 b5 b6 b7
    (by rw [Slice.length]; simp [hs0v, hbl, Array.to_slice])
    (by simp [hs0v, hbl, Array.to_slice])
    (by simp [hs0v, hbl, Array.to_slice])
    (by simp [hs0v, hbl, Array.to_slice])
    (by simp [hs0v, hbl, Array.to_slice])
    (by simp [hs0v, hbl, Array.to_slice])
    (by simp [hs0v, hbl, Array.to_slice])
    (by simp [hs0v, hbl, Array.to_slice])
    (by simp [hs0v, hbl, Array.to_slice])
    ) as ⟨w0, hw0⟩
  step as ⟨l0, hl0⟩
  have hl0v : l0.val = w0.val % 2^51 := by
    rw [hl0, UScalar.val_and, hmaskv, nat_and_mask]
    norm_num
  -- window 1: bytes 6..13, shift 3
  step with (range_from_index_spec bytes.to_slice { start := 6#usize } (by scalar_tac))
    as ⟨s1, hs1v⟩
  step with (closure_call_spec () s1 b6 b7 b8 b9 b10 b11 b12 b13
    (by rw [Slice.length]; simp [hs1v, hbl, Array.to_slice])
    (by simp [hs1v, hbl, Array.to_slice])
    (by simp [hs1v, hbl, Array.to_slice])
    (by simp [hs1v, hbl, Array.to_slice])
    (by simp [hs1v, hbl, Array.to_slice])
    (by simp [hs1v, hbl, Array.to_slice])
    (by simp [hs1v, hbl, Array.to_slice])
    (by simp [hs1v, hbl, Array.to_slice])
    (by simp [hs1v, hbl, Array.to_slice])
    ) as ⟨w1, hw1⟩
  step as ⟨sh1, hsh1⟩
  step as ⟨l1, hl1⟩
  have hl1v : l1.val = (w1.val / 2^3) % 2^51 := by
    rw [hl1, UScalar.val_and, hmaskv, nat_and_mask, hsh1, nat_shr]
    norm_num
  -- window 2: bytes 12..19, shift 6
  step with (range_from_index_spec bytes.to_slice { start := 12#usize } (by scalar_tac))
    as ⟨s2, hs2v⟩
  step with (closure_call_spec () s2 b12 b13 b14 b15 b16 b17 b18 b19
    (by rw [Slice.length]; simp [hs2v, hbl, Array.to_slice])
    (by simp [hs2v, hbl, Array.to_slice])
    (by simp [hs2v, hbl, Array.to_slice])
    (by simp [hs2v, hbl, Array.to_slice])
    (by simp [hs2v, hbl, Array.to_slice])
    (by simp [hs2v, hbl, Array.to_slice])
    (by simp [hs2v, hbl, Array.to_slice])
    (by simp [hs2v, hbl, Array.to_slice])
    (by simp [hs2v, hbl, Array.to_slice])
    ) as ⟨w2, hw2⟩
  step as ⟨sh2, hsh2⟩
  step as ⟨l2, hl2⟩
  have hl2v : l2.val = (w2.val / 2^6) % 2^51 := by
    rw [hl2, UScalar.val_and, hmaskv, nat_and_mask, hsh2, nat_shr]
    norm_num
  -- window 3: bytes 19..26, shift 1
  step with (range_from_index_spec bytes.to_slice { start := 19#usize } (by scalar_tac))
    as ⟨s3, hs3v⟩
  step with (closure_call_spec () s3 b19 b20 b21 b22 b23 b24 b25 b26
    (by rw [Slice.length]; simp [hs3v, hbl, Array.to_slice])
    (by simp [hs3v, hbl, Array.to_slice])
    (by simp [hs3v, hbl, Array.to_slice])
    (by simp [hs3v, hbl, Array.to_slice])
    (by simp [hs3v, hbl, Array.to_slice])
    (by simp [hs3v, hbl, Array.to_slice])
    (by simp [hs3v, hbl, Array.to_slice])
    (by simp [hs3v, hbl, Array.to_slice])
    (by simp [hs3v, hbl, Array.to_slice])
    ) as ⟨w3, hw3⟩
  step as ⟨sh3, hsh3⟩
  step as ⟨l3, hl3⟩
  have hl3v : l3.val = (w3.val / 2^1) % 2^51 := by
    rw [hl3, UScalar.val_and, hmaskv, nat_and_mask, hsh3, nat_shr]
    norm_num
  -- window 4: bytes 24..31, shift 12
  step with (range_from_index_spec bytes.to_slice { start := 24#usize } (by scalar_tac))
    as ⟨s4, hs4v⟩
  step with (closure_call_spec () s4 b24 b25 b26 b27 b28 b29 b30 b31
    (by rw [Slice.length]; simp [hs4v, hbl, Array.to_slice])
    (by simp [hs4v, hbl, Array.to_slice])
    (by simp [hs4v, hbl, Array.to_slice])
    (by simp [hs4v, hbl, Array.to_slice])
    (by simp [hs4v, hbl, Array.to_slice])
    (by simp [hs4v, hbl, Array.to_slice])
    (by simp [hs4v, hbl, Array.to_slice])
    (by simp [hs4v, hbl, Array.to_slice])
    (by simp [hs4v, hbl, Array.to_slice])
    ) as ⟨w4, hw4⟩
  step as ⟨sh4, hsh4⟩
  step as ⟨l4, hl4⟩
  have hl4v : l4.val = (w4.val / 2^12) % 2^51 := by
    rw [hl4, UScalar.val_and, hmaskv, nat_and_mask, hsh4, nat_shr]
    norm_num
  try simp only [spec_ok]
  constructor
  · rw [Bnd_eq _ l0 l1 l2 l3 l4 _ rfl]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> · first
      | (rw [hl0v]; exact Nat.mod_lt _ (by norm_num))
      | (rw [hl1v]; exact Nat.mod_lt _ (by norm_num))
      | (rw [hl2v]; exact Nat.mod_lt _ (by norm_num))
      | (rw [hl3v]; exact Nat.mod_lt _ (by norm_num))
      | (rw [hl4v]; exact Nat.mod_lt _ (by norm_num))
  · rw [feVal_eq _ l0 l1 l2 l3 l4 rfl]
    unfold limbsVal
    have hB : bytesVal bytes = b0.val + b1.val * 2^8 + b2.val * 2^16 + b3.val * 2^24 + b4.val * 2^32 + b5.val * 2^40 + b6.val * 2^48 + b7.val * 2^56 + b8.val * 2^64 + b9.val * 2^72 + b10.val * 2^80 + b11.val * 2^88 + b12.val * 2^96 + b13.val * 2^104 + b14.val * 2^112 + b15.val * 2^120 + b16.val * 2^128 + b17.val * 2^136 + b18.val * 2^144 + b19.val * 2^152 + b20.val * 2^160 + b21.val * 2^168 + b22.val * 2^176 + b23.val * 2^184 + b24.val * 2^192 + b25.val * 2^200 + b26.val * 2^208 + b27.val * 2^216 + b28.val * 2^224 + b29.val * 2^232 + b30.val * 2^240 + b31.val * 2^248 := by
      simp only [bytesVal, hbl]
    have hwin0 : w0.val = bytesVal bytes / 2^0 % 2^64 := by
      have hdecomp : (b0.val + b1.val * 2^8 + b2.val * 2^16 + b3.val * 2^24 + b4.val * 2^32 + b5.val * 2^40 + b6.val * 2^48 + b7.val * 2^56 + b8.val * 2^64 + b9.val * 2^72 + b10.val * 2^80 + b11.val * 2^88 + b12.val * 2^96 + b13.val * 2^104 + b14.val * 2^112 + b15.val * 2^120 + b16.val * 2^128 + b17.val * 2^136 + b18.val * 2^144 + b19.val * 2^152 + b20.val * 2^160 + b21.val * 2^168 + b22.val * 2^176 + b23.val * 2^184 + b24.val * 2^192 + b25.val * 2^200 + b26.val * 2^208 + b27.val * 2^216 + b28.val * 2^224 + b29.val * 2^232 + b30.val * 2^240 + b31.val * 2^248)
          = (0) + 2^0 * (b0.val + b1.val * 2^8 + b2.val * 2^16 + b3.val * 2^24 + b4.val * 2^32 + b5.val * 2^40 + b6.val * 2^48 + b7.val * 2^56) + 2^0 * 2^64 * (b8.val + b9.val * 2^8 + b10.val * 2^16 + b11.val * 2^24 + b12.val * 2^32 + b13.val * 2^40 + b14.val * 2^48 + b15.val * 2^56 + b16.val * 2^64 + b17.val * 2^72 + b18.val * 2^80 + b19.val * 2^88 + b20.val * 2^96 + b21.val * 2^104 + b22.val * 2^112 + b23.val * 2^120 + b24.val * 2^128 + b25.val * 2^136 + b26.val * 2^144 + b27.val * 2^152 + b28.val * 2^160 + b29.val * 2^168 + b30.val * 2^176 + b31.val * 2^184) := by
        ring
      rw [hw0, hB, hdecomp]
      exact (window_extract (0) (b0.val + b1.val * 2^8 + b2.val * 2^16 + b3.val * 2^24 + b4.val * 2^32 + b5.val * 2^40 + b6.val * 2^48 + b7.val * 2^56) (b8.val + b9.val * 2^8 + b10.val * 2^16 + b11.val * 2^24 + b12.val * 2^32 + b13.val * 2^40 + b14.val * 2^48 + b15.val * 2^56 + b16.val * 2^64 + b17.val * 2^72 + b18.val * 2^80 + b19.val * 2^88 + b20.val * 2^96 + b21.val * 2^104 + b22.val * 2^112 + b23.val * 2^120 + b24.val * 2^128 + b25.val * 2^136 + b26.val * 2^144 + b27.val * 2^152 + b28.val * 2^160 + b29.val * 2^168 + b30.val * 2^176 + b31.val * 2^184) 0
        (by scalar_tac) (by scalar_tac)).symm
    have hlimb0 : l0.val = bytesVal bytes / 2^0 % 2^51 := by
      rw [hl0v, hwin0]
      exact Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 (by norm_num))
    have hwin1 : w1.val = bytesVal bytes / 2^48 % 2^64 := by
      have hdecomp : (b0.val + b1.val * 2^8 + b2.val * 2^16 + b3.val * 2^24 + b4.val * 2^32 + b5.val * 2^40 + b6.val * 2^48 + b7.val * 2^56 + b8.val * 2^64 + b9.val * 2^72 + b10.val * 2^80 + b11.val * 2^88 + b12.val * 2^96 + b13.val * 2^104 + b14.val * 2^112 + b15.val * 2^120 + b16.val * 2^128 + b17.val * 2^136 + b18.val * 2^144 + b19.val * 2^152 + b20.val * 2^160 + b21.val * 2^168 + b22.val * 2^176 + b23.val * 2^184 + b24.val * 2^192 + b25.val * 2^200 + b26.val * 2^208 + b27.val * 2^216 + b28.val * 2^224 + b29.val * 2^232 + b30.val * 2^240 + b31.val * 2^248)
          = (b0.val + b1.val * 2^8 + b2.val * 2^16 + b3.val * 2^24 + b4.val * 2^32 + b5.val * 2^40) + 2^48 * (b6.val + b7.val * 2^8 + b8.val * 2^16 + b9.val * 2^24 + b10.val * 2^32 + b11.val * 2^40 + b12.val * 2^48 + b13.val * 2^56) + 2^48 * 2^64 * (b14.val + b15.val * 2^8 + b16.val * 2^16 + b17.val * 2^24 + b18.val * 2^32 + b19.val * 2^40 + b20.val * 2^48 + b21.val * 2^56 + b22.val * 2^64 + b23.val * 2^72 + b24.val * 2^80 + b25.val * 2^88 + b26.val * 2^96 + b27.val * 2^104 + b28.val * 2^112 + b29.val * 2^120 + b30.val * 2^128 + b31.val * 2^136) := by
        ring
      rw [hw1, hB, hdecomp]
      exact (window_extract (b0.val + b1.val * 2^8 + b2.val * 2^16 + b3.val * 2^24 + b4.val * 2^32 + b5.val * 2^40) (b6.val + b7.val * 2^8 + b8.val * 2^16 + b9.val * 2^24 + b10.val * 2^32 + b11.val * 2^40 + b12.val * 2^48 + b13.val * 2^56) (b14.val + b15.val * 2^8 + b16.val * 2^16 + b17.val * 2^24 + b18.val * 2^32 + b19.val * 2^40 + b20.val * 2^48 + b21.val * 2^56 + b22.val * 2^64 + b23.val * 2^72 + b24.val * 2^80 + b25.val * 2^88 + b26.val * 2^96 + b27.val * 2^104 + b28.val * 2^112 + b29.val * 2^120 + b30.val * 2^128 + b31.val * 2^136) 48
        (by scalar_tac) (by scalar_tac)).symm
    have hlimb1 : l1.val = bytesVal bytes / 2^51 % 2^51 := by
      rw [hl1v, hwin1]
      have := window_shift (bytesVal bytes) 6 3 (by norm_num)
      norm_num at this ⊢
      rw [this]
    have hwin2 : w2.val = bytesVal bytes / 2^96 % 2^64 := by
      have hdecomp : (b0.val + b1.val * 2^8 + b2.val * 2^16 + b3.val * 2^24 + b4.val * 2^32 + b5.val * 2^40 + b6.val * 2^48 + b7.val * 2^56 + b8.val * 2^64 + b9.val * 2^72 + b10.val * 2^80 + b11.val * 2^88 + b12.val * 2^96 + b13.val * 2^104 + b14.val * 2^112 + b15.val * 2^120 + b16.val * 2^128 + b17.val * 2^136 + b18.val * 2^144 + b19.val * 2^152 + b20.val * 2^160 + b21.val * 2^168 + b22.val * 2^176 + b23.val * 2^184 + b24.val * 2^192 + b25.val * 2^200 + b26.val * 2^208 + b27.val * 2^216 + b28.val * 2^224 + b29.val * 2^232 + b30.val * 2^240 + b31.val * 2^248)
          = (b0.val + b1.val * 2^8 + b2.val * 2^16 + b3.val * 2^24 + b4.val * 2^32 + b5.val * 2^40 + b6.val * 2^48 + b7.val * 2^56 + b8.val * 2^64 + b9.val * 2^72 + b10.val * 2^80 + b11.val * 2^88) + 2^96 * (b12.val + b13.val * 2^8 + b14.val * 2^16 + b15.val * 2^24 + b16.val * 2^32 + b17.val * 2^40 + b18.val * 2^48 + b19.val * 2^56) + 2^96 * 2^64 * (b20.val + b21.val * 2^8 + b22.val * 2^16 + b23.val * 2^24 + b24.val * 2^32 + b25.val * 2^40 + b26.val * 2^48 + b27.val * 2^56 + b28.val * 2^64 + b29.val * 2^72 + b30.val * 2^80 + b31.val * 2^88) := by
        ring
      rw [hw2, hB, hdecomp]
      exact (window_extract (b0.val + b1.val * 2^8 + b2.val * 2^16 + b3.val * 2^24 + b4.val * 2^32 + b5.val * 2^40 + b6.val * 2^48 + b7.val * 2^56 + b8.val * 2^64 + b9.val * 2^72 + b10.val * 2^80 + b11.val * 2^88) (b12.val + b13.val * 2^8 + b14.val * 2^16 + b15.val * 2^24 + b16.val * 2^32 + b17.val * 2^40 + b18.val * 2^48 + b19.val * 2^56) (b20.val + b21.val * 2^8 + b22.val * 2^16 + b23.val * 2^24 + b24.val * 2^32 + b25.val * 2^40 + b26.val * 2^48 + b27.val * 2^56 + b28.val * 2^64 + b29.val * 2^72 + b30.val * 2^80 + b31.val * 2^88) 96
        (by scalar_tac) (by scalar_tac)).symm
    have hlimb2 : l2.val = bytesVal bytes / 2^102 % 2^51 := by
      rw [hl2v, hwin2]
      have := window_shift (bytesVal bytes) 12 6 (by norm_num)
      norm_num at this ⊢
      rw [this]
    have hwin3 : w3.val = bytesVal bytes / 2^152 % 2^64 := by
      have hdecomp : (b0.val + b1.val * 2^8 + b2.val * 2^16 + b3.val * 2^24 + b4.val * 2^32 + b5.val * 2^40 + b6.val * 2^48 + b7.val * 2^56 + b8.val * 2^64 + b9.val * 2^72 + b10.val * 2^80 + b11.val * 2^88 + b12.val * 2^96 + b13.val * 2^104 + b14.val * 2^112 + b15.val * 2^120 + b16.val * 2^128 + b17.val * 2^136 + b18.val * 2^144 + b19.val * 2^152 + b20.val * 2^160 + b21.val * 2^168 + b22.val * 2^176 + b23.val * 2^184 + b24.val * 2^192 + b25.val * 2^200 + b26.val * 2^208 + b27.val * 2^216 + b28.val * 2^224 + b29.val * 2^232 + b30.val * 2^240 + b31.val * 2^248)
          = (b0.val + b1.val * 2^8 + b2.val * 2^16 + b3.val * 2^24 + b4.val * 2^32 + b5.val * 2^40 + b6.val * 2^48 + b7.val * 2^56 + b8.val * 2^64 + b9.val * 2^72 + b10.val * 2^80 + b11.val * 2^88 + b12.val * 2^96 + b13.val * 2^104 + b14.val * 2^112 + b15.val * 2^120 + b16.val * 2^128 + b17.val * 2^136 + b18.val * 2^144) + 2^152 * (b19.val + b20.val * 2^8 + b21.val * 2^16 + b22.val * 2^24 + b23.val * 2^32 + b24.val * 2^40 + b25.val * 2^48 + b26.val * 2^56) + 2^152 * 2^64 * (b27.val + b28.val * 2^8 + b29.val * 2^16 + b30.val * 2^24 + b31.val * 2^32) := by
        ring
      rw [hw3, hB, hdecomp]
      exact (window_extract (b0.val + b1.val * 2^8 + b2.val * 2^16 + b3.val * 2^24 + b4.val * 2^32 + b5.val * 2^40 + b6.val * 2^48 + b7.val * 2^56 + b8.val * 2^64 + b9.val * 2^72 + b10.val * 2^80 + b11.val * 2^88 + b12.val * 2^96 + b13.val * 2^104 + b14.val * 2^112 + b15.val * 2^120 + b16.val * 2^128 + b17.val * 2^136 + b18.val * 2^144) (b19.val + b20.val * 2^8 + b21.val * 2^16 + b22.val * 2^24 + b23.val * 2^32 + b24.val * 2^40 + b25.val * 2^48 + b26.val * 2^56) (b27.val + b28.val * 2^8 + b29.val * 2^16 + b30.val * 2^24 + b31.val * 2^32) 152
        (by scalar_tac) (by scalar_tac)).symm
    have hlimb3 : l3.val = bytesVal bytes / 2^153 % 2^51 := by
      rw [hl3v, hwin3]
      have := window_shift (bytesVal bytes) 19 1 (by norm_num)
      norm_num at this ⊢
      rw [this]
    have hwin4 : w4.val = bytesVal bytes / 2^192 % 2^64 := by
      have hdecomp : (b0.val + b1.val * 2^8 + b2.val * 2^16 + b3.val * 2^24 + b4.val * 2^32 + b5.val * 2^40 + b6.val * 2^48 + b7.val * 2^56 + b8.val * 2^64 + b9.val * 2^72 + b10.val * 2^80 + b11.val * 2^88 + b12.val * 2^96 + b13.val * 2^104 + b14.val * 2^112 + b15.val * 2^120 + b16.val * 2^128 + b17.val * 2^136 + b18.val * 2^144 + b19.val * 2^152 + b20.val * 2^160 + b21.val * 2^168 + b22.val * 2^176 + b23.val * 2^184 + b24.val * 2^192 + b25.val * 2^200 + b26.val * 2^208 + b27.val * 2^216 + b28.val * 2^224 + b29.val * 2^232 + b30.val * 2^240 + b31.val * 2^248)
          = (b0.val + b1.val * 2^8 + b2.val * 2^16 + b3.val * 2^24 + b4.val * 2^32 + b5.val * 2^40 + b6.val * 2^48 + b7.val * 2^56 + b8.val * 2^64 + b9.val * 2^72 + b10.val * 2^80 + b11.val * 2^88 + b12.val * 2^96 + b13.val * 2^104 + b14.val * 2^112 + b15.val * 2^120 + b16.val * 2^128 + b17.val * 2^136 + b18.val * 2^144 + b19.val * 2^152 + b20.val * 2^160 + b21.val * 2^168 + b22.val * 2^176 + b23.val * 2^184) + 2^192 * (b24.val + b25.val * 2^8 + b26.val * 2^16 + b27.val * 2^24 + b28.val * 2^32 + b29.val * 2^40 + b30.val * 2^48 + b31.val * 2^56) + 2^192 * 2^64 * 0 := by
        ring
      rw [hw4, hB, hdecomp]
      exact (window_extract (b0.val + b1.val * 2^8 + b2.val * 2^16 + b3.val * 2^24 + b4.val * 2^32 + b5.val * 2^40 + b6.val * 2^48 + b7.val * 2^56 + b8.val * 2^64 + b9.val * 2^72 + b10.val * 2^80 + b11.val * 2^88 + b12.val * 2^96 + b13.val * 2^104 + b14.val * 2^112 + b15.val * 2^120 + b16.val * 2^128 + b17.val * 2^136 + b18.val * 2^144 + b19.val * 2^152 + b20.val * 2^160 + b21.val * 2^168 + b22.val * 2^176 + b23.val * 2^184) (b24.val + b25.val * 2^8 + b26.val * 2^16 + b27.val * 2^24 + b28.val * 2^32 + b29.val * 2^40 + b30.val * 2^48 + b31.val * 2^56) 0 192
        (by scalar_tac) (by scalar_tac)).symm
    have hlimb4 : l4.val = bytesVal bytes / 2^204 % 2^51 := by
      rw [hl4v, hwin4]
      have := window_shift (bytesVal bytes) 24 12 (by norm_num)
      norm_num at this ⊢
      rw [this]
    have ht := digits_tile (bytesVal bytes)
    norm_num at ht hlimb0 hlimb1 hlimb2 hlimb3 hlimb4 ⊢
    omega

end CurveFieldProofs
