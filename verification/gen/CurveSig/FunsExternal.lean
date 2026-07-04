/- ──────────────────────────────────────────────────────────────────────────────
   gen/CurveSig/FunsExternal.lean — external functions for the verify glue.

   TIER A/B — REAL DEFINITIONS (no axioms): importing CurveField.Funs makes
   the curve calls (compress, vartime_double_scalar_mul_basepoint,
   as_bytes, neg, from_bytes_mod_order, from_bytes_mod_order_wide) resolve to
   the PROVEN model's definitions by their fully-qualified names. The Result
   Try/FromResidual plumbing and the compressed_from_bytes constructor are
   given real definitions below.

   TIER C — THE DELIBERATE OPAQUE BOUNDARY (the only axioms):
   · verifying.sha512_hash3 — SHA-512 over r ‖ a ‖ m, one call
   · ed25519.Signature.to_bytes — the wire accessor of an opaque type
   · signature.error.Error.new  — an opaque error value
   The apex certificate will carry EXACTLY these axioms beyond the standard
   three — the documented hash-oracle boundary.
   ────────────────────────────────────────────────────────────────────────────── -/
import Aeneas
import CurveSig.TypesExternal
import CurveField.Funs
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false

/-! ### Tier A/B: real definitions -/

/-- `Try::branch` for `core::result::Result` — the `?` operator's dispatch. -/
def core.result.Result.Insts.CoreOpsTry_traitTry.branch
    {T : Type} {E : Type} (r : core.result.Result T E) :
    Result (core.ops.control_flow.ControlFlow
      (core.result.Result core.convert.Infallible E) T) :=
  match r with
  | .Ok v => ok (.Continue v)
  | .Err e => ok (.Break (.Err e))

/-- `FromResidual` for `core::result::Result` — the `?` operator's error
    conversion. The `Ok Infallible` branch is uninhabited. -/
def core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual
    (T : Type) {E : Type} {F : Type} (convertFromInst : core.convert.From F E)
    (r : core.result.Result core.convert.Infallible E) :
    Result (core.result.Result T F) :=
  match r with
  | .Ok v => nomatch v
  | .Err e => do
      let f ← convertFromInst.from_ e
      ok (.Err f)

/-- The compressed-point constructor: `CompressedEdwardsY` is the 32-byte
    array synonym in the proven model. -/
def signature.compressed_from_bytes
    (bytes : Array Std.U8 32#usize) :
    Result curve25519_dalek.edwards.CompressedEdwardsY :=
  ok bytes

/-! ### Tier C: the deliberate opaque boundary -/

/-- SHA-512 over r ‖ a ‖ m, as one call (this fork's sha2-0.10 stack; the
    signature carries no foreign types). OPAQUE BY DESIGN — the hash oracle. -/
axiom verifying.sha512_hash3
  : Slice Std.U8 → Slice Std.U8 → Slice Std.U8 → Result (Array Std.U8 64#usize)

/-- The wire signature's 64 bytes (R ‖ s). Opaque accessor of an opaque
    type — the verify spec is stated relative to its result. -/
axiom ed25519.Signature.to_bytes
  : ed25519.Signature → Result (Array Std.U8 64#usize)

/-- An opaque error value; the spec only distinguishes ok from err. -/
axiom signature.error.Error.new : Result signature.error.Error
