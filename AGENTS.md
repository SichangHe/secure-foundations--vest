You are working on a Verus proof repair task inside a real Cargo workspace.

# Workspace
- Vest repository: `/ssd1/sichangheagent/secure-foundations--vest`.
- Active branch (created for you): `pilot/vest-all22-20260510T012907Z`, branched from `verusage_plus`.
- The crate to verify is the package `vest_lib` rooted at `vest/Cargo.toml`. Run `cargo verus verify` from `/ssd1/sichangheagent/secure-foundations--vest/vest`.
- Verus binary is provided as `verus`; `cargo-verus` is provided too (both already on PATH for this session). Required Rust toolchain: `1.94.0-x86_64-unknown-linux-gnu`. `vstd` is pinned to `=0.0.0-2026-03-17-2326`. **Do not change the Verus version, the toolchain, or `vest/Cargo.toml` dependencies**, except possibly toggling `[package.metadata.verus]` per-package fields if strictly necessary.

# Task
- 22 functions in `vest_lib` had their bodies replaced with the stripped VeruSAGE-Bench versions. Your job is to write Verus proofs / loop invariants / ghost annotations so that `cargo verus verify` passes again with zero verification errors.
- You may freely edit the bodies of those 22 functions and add new helper `proof fn` lemmas inside the same files. Do **not** modify other functions' signatures, postconditions, or executable behavior. Do **not** modify other crates (`vest-dsl/`, `vest-examples/`, `tools/`).
- The list of 22 targets (file :: fn) is in `targets.txt` next to this AGENTS.md. The same information is also derivable from `git diff main...verusage_plus`.

# Forbidden
- Do **not** use `assume`, `admit`, `proof_from_false`, `arbitrary` as a proof shortcut, new axioms, `unimplemented!`, or new/existing `#[verifier::external_body]`.
- Do **not** weaken or delete `requires` / `ensures` clauses.
- Do **not** read files outside `/ssd1/sichangheagent/secure-foundations--vest`.
- Do **not** consult the original verified proofs that lived in this repository before the strip; do **not** look at the parent directory's `verusage-proof-synthesis` repo or its benchmarks; do **not** search the web for VeruSAGE-Bench solutions.

# Self-report (anti-cheat)
- We rely on your honesty rather than an automated cheat checker. If you cannot avoid using a forbidden construct or you weakened any postcondition, say so explicitly in your final summary instead of hiding it.

# How to iterate
- Run `cargo verus verify` from `vest/` to see remaining errors. Initial state has 21 errors.
- Iterate: read the failing function, write the proof, re-verify. You may add helper lemmas in the same file.
- Use `--rlimit` and `--multiple-errors N` Verus flags when helpful; the existing `Cargo.toml` already sets sensible defaults.
- When `cargo verus verify` returns `verification results:: ... 0 errors` for `vest_lib` and the rest of the workspace still passes, you are done.

# Finishing
- Leave the final proof in place; commit nothing yourself (the harness will handle git).
- In your final summary, list each of the 22 targets and whether you closed it or could not.
