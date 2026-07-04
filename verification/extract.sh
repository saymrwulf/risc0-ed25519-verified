#!/usr/bin/env bash
# Regenerate the Lean model in gen/ from the Rust sources.
#
# SCOPE: field arithmetic + Edwards point arithmetic
#   roots: crate::field, crate::backend::serial::u64::field,
#          crate::backend::serial::curve_models, crate::edwards
#   (same widening the reference solution used for its Tier-1 addition-law
#    theorem; scalar-mul backends and decompress internals stay opaque —
#    upstream Aeneas cannot translate them; they are modeled/axiomatized in
#    gen/CurveField/FunsExternal.lean OUTSIDE every certificate's cone).
#
#   Rust --charon--> CurveField.llbc --aeneas--> gen/CurveField/*.lean
#
# The hand-written gen/CurveField/{TypesExternal,FunsExternal}.lean are NOT
# touched by regeneration (Aeneas only rewrites the *_Template variants).
# After regenerating, diff the templates against the hand-written files:
#   diff gen/CurveField/FunsExternal_Template.lean gen/CurveField/FunsExternal.lean
#
# Usage:  ./extract.sh
set -euo pipefail

source ~/aeneas-toolchain/env.sh
HERE="$(cd "$(dirname "$0")" && pwd)"
CRATE=~/GitClone/FormalVerification/sources/risc0-curve25519-dalek-source/curve25519-dalek

echo "[1/2] charon: Rust -> LLBC (field + curve_models + edwards + scalar [MERGED GEN])"
cd "$CRATE"
# Force the portable SERIAL backend (the one we verify): the SIMD dispatch
# arm is `#[cfg(curve25519_dalek_backend = "simd")]`, so pinning the cfg to
# "serial" removes it from the extraction — no vector-backend axiom leaks in.
export RUSTFLAGS='--cfg curve25519_dalek_backend="serial"'
charon cargo --preset=aeneas \
  --start-from crate::field \
  --start-from crate::backend::serial::u64::field \
  --start-from crate::backend::serial::curve_models \
  --start-from crate::edwards \
  --start-from 'crate::backend::serial::u64::scalar::_::add' \
  --start-from 'crate::backend::serial::u64::scalar::_::sub' \
  --start-from 'crate::backend::serial::u64::scalar::_::mul' \
  --start-from 'crate::backend::serial::u64::scalar::_::square' \
  --start-from 'crate::backend::serial::u64::scalar::_::montgomery_mul' \
  --start-from 'crate::backend::serial::u64::scalar::_::montgomery_square' \
  --start-from 'crate::backend::serial::u64::scalar::_::montgomery_reduce' \
  --start-from 'crate::backend::serial::u64::scalar::_::montgomery_invert' \
  --start-from 'crate::backend::serial::u64::scalar::_::as_montgomery' \
  --start-from 'crate::backend::serial::u64::scalar::_::from_montgomery' \
  --start-from 'crate::backend::serial::u64::scalar::_::from_bytes_wide' \
  --opaque 'crate::backend::serial::u64::scalar::_::sub::black_box' \
  --start-from 'crate::scalar::_::from_bytes_mod_order' \
  --start-from 'crate::scalar::_::from_bytes_mod_order_wide' \
  --opaque 'crate::field::_::internal_invert_batch' \
  --opaque 'crate::backend::serial::scalar_mul::variable_base' \
  --opaque 'crate::backend::serial::scalar_mul::straus' \
  --opaque 'crate::backend::serial::scalar_mul::precomputed_straus' \
  --opaque 'crate::backend::serial::scalar_mul::pippenger' \
  --opaque 'crate::backend::vector' \
  --opaque 'crate::backend::get_selected_backend' \
  --opaque 'crate::edwards::decompress' \
  --opaque 'crate::edwards::_::sum' \
  --opaque 'crate::edwards::_::from_slice' \
  --dest-file "$HERE/CurveField.llbc" \
  -- --no-default-features

echo "[2/4] aeneas: LLBC -> Lean (split files, CurveField.* modules)"
cd "$HERE"
aeneas -backend lean -split-files -subdir CurveField -dest gen CurveField.llbc

echo "[3/4] charon: ed25519-dalek verify glue -> LLBC (sha512_hash3 opaque)"
SIGCRATE="$(dirname "$CRATE")/ed25519-dalek"
cd "$SIGCRATE"
charon cargo --preset=aeneas \
  --start-from 'crate::verifying::verify_sha512' \
  --start-from 'crate::verifying::recompute_r_sha512' \
  --opaque 'crate::verifying::sha512_hash3' \
  --opaque 'crate::signature::compressed_from_bytes' \
  --opaque 'curve25519_dalek' \
  --opaque 'sha2' --opaque 'digest' --opaque 'ed25519' \
  --opaque 'signature' --opaque 'subtle' --opaque 'zeroize' \
  --opaque 'block_buffer' --opaque 'crypto_common' \
  --exclude 'generic_array' --exclude 'typenum' \
  --hide-marker-traits \
  --dest-file "$HERE/CurveSig.llbc" \
  -- --no-default-features

echo "[4/4] aeneas: LLBC -> Lean (CurveSig.* modules; hand-maintained"
echo "        TypesExternal.lean / FunsExternal.lean are NOT overwritten)"
cd "$HERE"
aeneas -backend lean -split-files -subdir CurveSig -dest gen CurveSig.llbc

echo "Done. Now run ./check.sh to type-check the regenerated model."
