# risc0-ed25519-verified

Formal verification of the ed25519 implementation in **risc0/curve25519-dalek (RISC Zero fork, v4.1.3)**, built as a
coherent proof pyramid in Lean 4 via the Charon/Aeneas transpilation pipeline:

```
        ┌──────────────────────────────┐
        │  Signature (EdDSA verify)    │   accepted ⇔ decompress(R) = [k](−A)+[s]B
        ├──────────────────────────────┤
        │  Scalar arithmetic mod ℓ     │   Scalar52 ops correct mod ℓ
        ├──────────────────────────────┤
        │  Group law (twisted Edwards) │   point ops = complete addition law
        ├──────────────────────────────┤
        │  Field 𝔽_p, p = 2²⁵⁵ − 19    │   FieldElement51 ops correct mod p
        └──────────────────────────────┘
```

Every layer states its theorems about the **actual Aeneas-transpiled Rust
code** (never about a hand-written re-model), and every claim in the status
table below is backed by a compiled proof plus an axiom audit of the named
certificate. Files that do not compile under `verification/check.sh` are not
in this repository.

## Layer status

| Layer | Certificate | Status | Axioms of certificate |
|-------|-------------|--------|-----------------------|
| Field 𝔽_p          | `fieldImplementation`    | ✅ proven | `[propext, Classical.choice, Quot.sound]` |
| Group law (Edwards) | `edwardsImplementation`  | ✅ proven | `[propext, Classical.choice, Quot.sound]` |
| Scalar mod ℓ        | `scalarImplementation` (add ✅ sub ✅ mul ✅) | ✅ proven | `[propext, Classical.choice, Quot.sound]` |
| Signature (EdDSA)   | `verify_accepts_iff` … `verify_accepts_iff_decompress` (4 tiers) | ✅ proven (phases 1+2) | standard three + the button-enforced SHA-512/wire-format boundary — see [The signature apex](#the-signature-apex-phases-1-and-2) |

Status legend: ✅ proven & axiom-audited · ⏳ in progress · ❌ not started.
This table is updated only when `verification/check.sh` passes for the layer.

## The signature apex (phases 1 and 2)

The apex certificate `CurveFieldProofs.verify_accepts_iff` is the literal EdDSA
acceptance criterion, proven about the extracted verifier:

> For a signature that parses, the verifier returns `Ok(())` **iff** the
> recomputed compressed point `compress([s]·B − [k]·A)` equals the signature's
> `R`, byte-for-byte — where `k` is whatever scalar the opaque SHA-512 oracle
> produces from `(R, A, msg)`.

The recomputation runs entirely through the **proven** model: the vendored `ed25519-dalek` verify glue is extracted as `gen/CurveSig`, whose
hand-maintained externals import `gen/CurveField` — every curve and scalar call
resolves by fully-qualified name to a **proven** definition. Only SHA-512 (a
single monomorphic `sha512_hash3(R, A, m)` oracle — this fork's sha2-0.10 stack
makes the incremental-hasher types untranslatable) and the wire-format types
stay opaque.

`check.sh` has a dedicated audit phase (Phase 3b) that fails the build unless
each apex-tier certificate's axiom cone is **exactly**

`[propext, Classical.choice, Quot.sound]` + `{ed25519.Signature, verifying.sha512_hash3, ed25519.Signature.to_bytes, signature.error.Error, signature.error.Error.new}`

— i.e. the three Lean foundations plus the documented SHA-512/wire-format
boundary. Zero curve, scalar, or backend axioms. The companion certificate
`verify_loop_full` (the 32-byte comparison loop computes array equality)
carries the standard three axioms only.

**Phase 2 (complete): the point-level lift.** Phase 3b enforces the SAME
axiom boundary on three further tiers that lift the byte equation to points:

| Tier | Certificate | Statement |
|------|-------------|-----------|
| half-lift | `verify_accepts_iff_point` | accepted ⇔ R = the **canonical encoding** of `[k]·(−A) + [s]·B` (compress semantics + `as_bytes` canonicity + hash-to-scalar, recompute chain inverted) |
| point equation | `verify_accepts_iff_point_eq` | for any valid on-curve `Q` canonically encoded by R: accepted ⇔ `Q = [k]·(−A) + [s]·B` **as points** (encoding-injectivity: d non-square + parity root-selection) |
| full lift | `verify_accepts_iff_decompress` | R **decompresses** to a valid on-curve `Pt`, and accepted ⇔ `Pt = [k]·(−A) + [s]·B` — the constructive capstone |

The full lift runs through the extracted `CompressedEdwardsY::decompress`
itself, proven end-to-end: `from_bytes` parses the y-residue exactly below
bit 255 (`from_bytes_spec`), `sqrt_ratio_i` returns the even square root of
`(y²−1)/(dy²+1)` (`sqrt_ratio_i_sq_spec`, Fermat-exponent square root), and
the sign bit selects the x-parity (`decompress_of_canonical`, standard three
axioms). Byte comparison ↔ encoding equality ↔ point equality ↔
decompressed-point equality: every link is machine-checked over the
extracted code, and `check.sh` fails the build if any of the four tiers'
cones deviates from the boundary above.


## Source

- **Upstream**: [risc0/curve25519-dalek](https://github.com/risc0/curve25519-dalek), commit `385adda`
- **Pinned/patched source**: [saymrwulf/risc0-curve25519-dalek-source](https://github.com/saymrwulf/risc0-curve25519-dalek-source), commit `d58065f` (adds the decompress step_2 negate-then-assign patch)
- **Patches**: minimal Aeneas-compatibility only (documented in the source repo)
- **Scope caveat**: this verifies the fork's pure-Rust `serial/u64` path. The RISC Zero zkVM accelerator/syscall path is different code and is NOT covered by these proofs.

## Toolchain (pinned)

| Component | Version |
|-----------|---------|
| Aeneas    | `bf13c42e` |
| Charon    | `9dd7f23c` |
| Lean      | `v4.30.0-rc2` |
| OCaml     | `5.3.0` |

## Reproducing

```bash
source ~/aeneas-toolchain/env.sh
cd verification
./extract.sh    # Rust → LLBC → Lean (regenerates gen/)
./check.sh      # compiles EVERY shipped file + axiom-audits EVERY certificate
```

The gen model is ONE merged universe (`gen/CurveField`: field + curve +
scalar + the verify path's reachable code), regenerated in full by
`extract.sh`. The scalar layer keeps its own check button:

```bash
./check-scalar.sh     # compiles the merged gen + all scalar proofs (add, sub,
                      # Montgomery mul, byte-parsing) and kernel-audits the
                      # scalar certificates, incl. the scalarImplementation
                      # aggregate
```


## Trusted base

See [TRUSTED-BASE.md](TRUSTED-BASE.md) for the complete list of assumptions
(Lean kernel, mathlib, Charon/Aeneas semantics, external-function models,
and — in the signature layer only — an opaque SHA-512 model).
