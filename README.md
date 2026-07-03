# risc0-ed25519-verified

Formal verification of the ed25519 implementation in **risc0/curve25519-dalek (RISC Zero fork, v4.1.3)**, built as a
coherent proof pyramid in Lean 4 via the Charon/Aeneas transpilation pipeline:

```
        ┌──────────────────────────────┐
        │  Signature (EdDSA verify)    │   accepted ⇒ [8][S]B = [8]R + [8][k]A
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
| Scalar mod ℓ        | `scalarImplementation` (planned; `L_val` proven)   | 🔨 foundation | denotation + L=ℓ proven; add/sub/mul in progress |
| Signature (EdDSA)   | `verifyEquation` (planned)          | ⏳ planned | — |

Status legend: ✅ proven & axiom-audited · ⏳ in progress · ❌ not started.
This table is updated only when `verification/check.sh` passes for the layer.

## Source

- **Upstream**: [risc0/curve25519-dalek](https://github.com/risc0/curve25519-dalek), commit `385adda`
- **Pinned/patched source**: [saymrwulf/risc0-curve25519-dalek-source](https://github.com/saymrwulf/risc0-curve25519-dalek-source), commit `2643444`
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

The scalar layer has its own pair of buttons:

```bash
./extract-scalar.sh   # regenerates gen/CurveScalar (Scalar52 limb arithmetic)
./check-scalar.sh     # compiles the scalar gen + the proven scalar foundation
```


## Trusted base

See [TRUSTED-BASE.md](TRUSTED-BASE.md) for the complete list of assumptions
(Lean kernel, mathlib, Charon/Aeneas semantics, external-function models,
and — in the signature layer only — an opaque SHA-512 model).
