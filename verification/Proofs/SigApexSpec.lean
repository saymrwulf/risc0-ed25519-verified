/- ──────────────────────────────────────────────────────────────────────────────
   Proofs/SigApexSpec.lean — the signature-layer apex, phase 1:
   the EdDSA verification equation, SHA-512 opaque.

   `verify_sha512 key msg sig` is the extracted RustCrypto verifier
   (gen/CurveSig): parse the signature, recompute
       R' = compress( [s]·B − [k]·A )              (k from the SHA-512 hash)
   and accept iff R' equals the signature's R, byte-for-byte.

   This file proves the verifier's control flow reduces EXACTLY to that
   recompute-and-compare — the literal EdDSA check — over the PROVEN curve
   model. SHA-512 stays an opaque oracle: the statement holds for whatever
   bytes the hash produces, so the theorem is the honest
       "accept  ↔  the recomputed compressed point equals R".

   Phase 2 (the point-level equation  [s]B − [k]A = decompress R,  which
   additionally needs `to_bytes` canonicity and `decompress`) is deliberately
   deferred and documented — mirroring the dsm layer's phase split.

   The load-bearing lemma is `verify_loop_eq`: the 32-byte comparison loop
   returns precisely the byte-equality of the two arrays.
   ────────────────────────────────────────────────────────────────────────────── -/
import Proofs.ScalarDenote
import Proofs.AddSpec
import CurveSig.Funs
open Aeneas Aeneas.Std Result ControlFlow
open curve25519_dalek

set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option maxRecDepth 8000

namespace CurveFieldProofs

open Aeneas.Std.WP

/-- Byte-equality of two 32-byte arrays over the tail `[n, 32)`. -/
def rangeEq (e r : Array Std.U8 32#usize) (n : ℕ) : Prop :=
  ∀ j, n ≤ j → j < 32 → e.val[j]! = r.val[j]!

instance (e r : Array Std.U8 32#usize) (n : ℕ) : Decidable (rangeEq e r n) := by
  have : rangeEq e r n ↔ ∀ j, j < 32 → n ≤ j → e.val[j]! = r.val[j]! := by
    unfold rangeEq; exact ⟨fun h j hj hn => h j hn hj, fun h j hn hj => h j hj hn⟩
  exact decidable_of_iff _ this.symm

/-- **The comparison loop returns byte-equality.** From accumulator `b` at
    index `i ≤ 32`, `verify_sha512_loop` returns `b ∧ (all bytes in [i,32)
    agree)`. Proven as a Hoare triple (the codebase's loop idiom); since the
    loop always returns `ok`, this pins its value exactly. -/
theorem verify_loop_spec (e r : Array Std.U8 32#usize) :
    ∀ (n : ℕ) (b : Bool) (i : Usize), i.val = 32 - n → n ≤ 32 →
    ed25519_dalek.verifying.verify_sha512_loop e r b i
      ⦃ res => res = (b && decide (rangeEq e r (32 - n))) ⦄ := by
  intro n
  induction n with
  | zero =>
    intro b i hi _
    unfold ed25519_dalek.verifying.verify_sha512_loop
    apply loop_step
    simp only [ed25519_dalek.verifying.verify_sha512_loop.body]
    have hge : ¬ (i < 32#usize) := by clear * - hi; scalar_tac
    rw [if_neg hge]
    try simp only [spec_ok]
    have hemp : decide (rangeEq e r (32 - 0)) = true := by
      simp only [decide_eq_true_eq]; intro j hj1 hj2; omega
    rw [hemp, Bool.and_true]
  | succ n ih =>
    intro b i hi hle
    unfold ed25519_dalek.verifying.verify_sha512_loop
    apply loop_step
    simp only [ed25519_dalek.verifying.verify_sha512_loop.body]
    have hlt : i < 32#usize := by clear * - hi hle; scalar_tac
    rw [if_pos hlt]
    have hiv : i.val = 32 - (n + 1) := hi
    have hb1 : i.val < (e.val).length := by clear * - hle hiv; scalar_tac
    have hb2 : i.val < (r.val).length := by clear * - hle hiv; scalar_tac
    -- e[i], r[i]
    step as ⟨x, hx⟩
    step as ⟨y, hy⟩
    -- the accumulator update: reduce the `if` to a plain `ok`
    have hite : (if (x != y) = true then (ok false : Result Bool) else ok b)
        = ok (if (x != y) = true then false else b) := by
      by_cases hc : (x != y) = true
      · rw [if_pos hc, if_pos hc]
      · rw [if_neg hc, if_neg hc]
    rw [hite]
    -- name the reduced accumulator, then reduce the trivial `ok` bind
    generalize heq1 : (if (x != y) = true then false else b) = eq1
    simp only [bind_tc_ok]
    -- i + 1
    step as ⟨i3, hi3⟩
    have hnext : i3.val = 32 - n := by clear * - hi3 hiv hle; scalar_tac
    try simp only [spec_ok]
    -- close with the IH at (eq1, i3); rewrite the range split
    apply spec_mono (ih eq1 i3 hnext (by omega))
    intro res hres
    rw [hres]
    -- eq1 = (b && e[i]=r[i]); the [i,32) range = byte i ∧ [i+1,32)
    have hxv : x = e.val[i.val]'hb1 := by rw [hx]
    have hyv : y = r.val[i.val]'hb2 := by rw [hy]
    have heq1v : eq1 = (b && decide (e.val[i.val]! = r.val[i.val]!)) := by
      rw [← heq1, hxv, hyv]
      rw [getElem!_pos e.val i.val hb1, getElem!_pos r.val i.val hb2]
      by_cases h : e.val[i.val]'hb1 = r.val[i.val]'hb2
      · have hb : ¬ ((e.val[i.val]'hb1 != r.val[i.val]'hb2) = true) := by
          simp [bne_iff_ne, h]
        rw [if_neg hb]; simp [h]
      · have hb : (e.val[i.val]'hb1 != r.val[i.val]'hb2) = true := by
          simp [bne_iff_ne, h]
        rw [if_pos hb]; simp [h]
    rw [heq1v, Bool.and_assoc]
    congr 1
    -- decide(byte i) && decide(tail [i+1,32)) = decide(rangeEq [i,32))
    have hiff : rangeEq e r (32 - (n + 1)) ↔
        (e.val[i.val]! = r.val[i.val]!) ∧ rangeEq e r (32 - n) := by
      have h32 : i.val < 32 := by clear * - hlt; scalar_tac
      constructor
      · intro h
        refine ⟨h i.val (by clear * - hiv; omega) h32, ?_⟩
        intro j hj1 hj2; exact h j (by omega) hj2
      · rintro ⟨hbyte, htail⟩ j hj1 hj2
        rcases Nat.lt_or_ge j (32 - n) with hj | hj
        · have hji : j = i.val := by clear * - hj1 hj hiv; omega
          rw [hji]; exact hbyte
        · exact htail j hj hj2
    have hda : (decide (e.val[i.val]! = r.val[i.val]!) && decide (rangeEq e r (32 - n)))
        = decide ((e.val[i.val]! = r.val[i.val]!) ∧ rangeEq e r (32 - n)) := by
      by_cases hp : (e.val[i.val]! = r.val[i.val]!) <;>
        by_cases hq : rangeEq e r (32 - n) <;> simp [hp, hq]
    rw [hda, decide_eq_decide]
    exact hiff.symm

/-- The comparison loop from the verifier's entry state (`b = true`,
    `i = 0`): the result equals the full 32-byte equality. -/
theorem verify_loop_full (e r : Array Std.U8 32#usize) :
    ed25519_dalek.verifying.verify_sha512_loop e r true 0#usize
      ⦃ res => res = decide (rangeEq e r 0) ⦄ := by
  have h := verify_loop_spec e r 32 true 0#usize (by scalar_tac) (le_refl _)
  apply spec_mono h
  intro res hres; rw [hres]; simp

/-! ### The apex: the EdDSA verification equation -/

open ed25519_dalek in
/-- **The EdDSA verification equation, SHA-512 opaque.** For a signature that
    parses (`try_from` succeeds with internal signature `val`), and with the
    recomputation and byte extractions total, the extracted RustCrypto
    verifier accepts **iff** the recomputed compressed point `expected_R`
    equals the signature's `R`, byte-for-byte:
        verify_sha512 key msg sig = ok (Ok ())   ↔   e = R  (all 32 bytes).

    `expected_R` (via `recompute_r_sha512`) is the PROVEN composition
    `compress( [s]·B − [k]·A )` over the certified curve model; `k` is the
    scalar the SHA-512 oracle produces — the hash stays opaque, so this is
    exactly the honest EdDSA acceptance criterion. -/
theorem verify_accepts_iff
    (key : verifying.VerifyingKey) (msg : Slice Std.U8) (sig : ed25519.Signature)
    (val : signature.InternalSignature)
    (er : curve25519_dalek.edwards.CompressedEdwardsY)
    (e r1 : Array Std.U8 32#usize)
    (hparse : signature.InternalSignature.Insts.CoreConvertTryFromShared0SignatureError.try_from sig
        = ok (core.result.Result.Ok val))
    (hrec : verifying.recompute_r_sha512 key val msg = ok er)
    (he : curve25519_dalek.edwards.CompressedEdwardsY.as_bytes er = ok e)
    (hr1 : curve25519_dalek.edwards.CompressedEdwardsY.as_bytes val.R = ok r1) :
    verifying.verify_sha512 key msg sig = ok (core.result.Result.Ok ())
      ↔ rangeEq e r1 0 := by
  unfold verifying.verify_sha512
  rw [hparse]
  simp only [core.result.Result.Insts.CoreOpsTry_traitTry.branch, bind_tc_ok]
  rw [hrec]
  simp only [bind_tc_ok]
  rw [he]
  simp only [bind_tc_ok]
  rw [hr1]
  simp only [bind_tc_ok]
  have hloop := verify_loop_full e r1
  obtain ⟨v, hv, hpost⟩ := spec_imp_exists hloop
  rw [hv]
  simp only [bind_tc_ok]
  rw [hpost]
  by_cases hb : rangeEq e r1 0
  · rw [decide_eq_true hb, if_pos rfl]
    simp only [hb, iff_true]
  · rw [decide_eq_false hb, if_neg (by simp)]
    constructor
    · intro hcontra
      exfalso
      -- the else-branch binds an opaque error value; whatever it is, binding
      -- with `Err` can only yield `fail`/`div`/`ok (Err _)` — never `ok (Ok ())`
      generalize hz : signature.error.Error.Insts.CoreConvertFromInternalError.from
        errors.InternalError.Verify = z at hcontra
      cases z <;> simp_all
    · intro hc; exact absurd hc hb

end CurveFieldProofs
