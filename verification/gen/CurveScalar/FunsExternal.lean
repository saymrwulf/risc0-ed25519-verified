-- Hand-written external function models for the Scalar52 arithmetic extraction.
-- This fork (curve25519-dalek v4.1.3) implements Scalar52::sub's constant-time
-- conditional add directly with a local `black_box` optimization barrier rather
-- than routing through subtle::ConditionallySelectable (as the v5 dalek does).
-- The sole external item is that `black_box`.
import Aeneas
import CurveScalar.Types
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
open curve25519_dalek

/-- [curve25519_dalek::backend::serial::u64::scalar::{curve25519_dalek::backend::serial::u64::scalar::Scalar52}::sub::black_box]:
    Source: 'curve25519-dalek/src/backend/serial/u64/scalar.rs', lines 179:8-183:9

    MODEL (faithful): the Rust body is
      `unsafe { core::ptr::read_volatile(&value) }`
    — a volatile read of the `u64` `value` living on the stack. The `volatile`
    qualifier only forbids the compiler from eliding/reordering the read (an
    optimization barrier to keep the constant-time path branch-free); the VALUE
    read back is exactly the value written, so semantically this is the identity
    on `u64`. -/
def backend.serial.u64.scalar.Scalar52.sub.black_box
  (value : Std.U64) : Result Std.U64 :=
  ok value
