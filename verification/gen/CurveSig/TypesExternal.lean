/- ──────────────────────────────────────────────────────────────────────────────
   gen/CurveSig/TypesExternal.lean — external types for the verify glue.

   The three curve types (CompressedEdwardsY, EdwardsPoint, Scalar) are NOT
   axiomatized: importing CurveField.Types makes every fully-qualified
   reference in CurveSig/Funs.lean resolve to the PROVEN model's types —
   the glue and the curve share one universe.

   Only the genuinely foreign types stay opaque — THE deliberate boundary:
   · ed25519.Signature      — the wire-format signature (only observed
                              through the opaque `to_bytes`)
   · signature.error.Error  — the RustCrypto error value (verify's spec only
                              distinguishes ok from err)
   ────────────────────────────────────────────────────────────────────────────── -/
import Aeneas
import CurveField.Types
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false

/-- [ed25519::Signature] — opaque: the 64-byte wire signature, observed only
    through `to_bytes`. -/
@[rust_type "ed25519::Signature"]
axiom ed25519.Signature : Type

/-- [signature::error::Error] — opaque: the error value carries no
    information the verification spec depends on. -/
@[rust_type "signature::error::Error"]
axiom signature.error.Error : Type
