You are working on a Verus proof repair task inside a real Cargo workspace.

# Workspace
- Repository: `/ssd1/sichangheagent/secure-foundations--vest`.
- Active branch (created for you): `pilot/vest-all22-20260510T044733Z`, branched from `verusage_plus`.
- Verify the package `vest_lib` rooted at `vest/Cargo.toml`. Run `cargo verus verify` from `/ssd1/sichangheagent/secure-foundations--vest/vest`.
- Verus binary and `cargo-verus` are already on PATH for this session. Required Rust toolchain: `1.94.0-x86_64-unknown-linux-gnu`. `vstd` is pinned in `Cargo.toml`. **Do not change the Verus version, the toolchain, or `Cargo.toml` dependencies**, except possibly toggling `[package.metadata.verus]` per-package fields if strictly necessary.

# Task
- 22 functions in `vest_lib` had their bodies replaced with the stripped VeruSAGE-Bench versions. Your job is to write Verus proofs / loop invariants / ghost annotations so that `cargo verus verify` passes again with zero verification errors.
- You may freely edit the bodies of those 22 functions and add new helper `proof fn` lemmas inside the same files. Do **not** modify other functions' signatures, postconditions, or executable behavior. Do **not** modify other crates outside the verify package unless absolutely required.
- The list of targets (file :: fn) is in `VERUSAGE_PLUS_TARGETS.txt` next to this AGENTS.md.

# Forbidden — automatic disqualification

You must not retrieve, consult, or copy proofs from anywhere other than your own reasoning. In particular:

- **No other git state.** Do not run `git log`, `git show`, `git diff`, `git checkout`, `git stash show`, `git reflog`, or any tool against any branch, tag, ref, commit, stash, or worktree other than the current `HEAD`. Do not consult `main`, `origin/*`, `upstream/*`, or any historical commit. Do not read files under `.git/` directly. The proofs you are asked to write existed earlier in this repository's history; reading them in any form, by any tool, counts as cheating.
- **No network.** Do not run `curl`, `wget`, `git fetch`, `cargo search`, `cargo fetch`, `gh`, web search, web fetch, or any other tool that contacts a remote host. Do not browse GitHub, crates.io, docs.rs, the Verus docs site, the Vest/Atmosphere/IronKV upstream repos, the VeruSAGE paper, or any URL. The internet is off-limits for this run.
- **No outside-repo reads.** Do not read files outside `/ssd1/sichangheagent/secure-foundations--vest`. Do not read sibling clones, parent directories, package caches, or system locations that might mirror this code.
- **No proof shortcuts.** Do not use `assume`, `admit`, `proof_from_false`, `arbitrary` as a proof shortcut, new axioms, `unimplemented!`, or new/existing `#[verifier::external_body]`. Do not weaken or delete `requires` / `ensures` clauses on the target functions or anywhere else.

If you are uncertain whether a particular action is allowed, treat it as forbidden. The mechanical correctness of `cargo verus verify` is necessary but not sufficient — the run is only valid if you actually wrote the proofs yourself.

# Self-report (anti-cheat)

We rely on your honesty rather than an automated cheat checker. If you could not avoid using a forbidden construct, weakened any postcondition, or otherwise looked up an answer instead of deriving it, state this clearly in your final summary instead of hiding it. Disclosing failure honestly is **strictly** preferred over presenting a copied solution as your own work.

# How to iterate

- Run `cargo verus verify` from `/ssd1/sichangheagent/secure-foundations--vest/vest` to see remaining errors. Initial state has 21 errors.
- Iterate: read the failing function, write the proof, re-verify. You may add helper lemmas in the same file.
- Use `--rlimit` and `--multiple-errors N` Verus flags (after `--`) when helpful.
- When `cargo verus verify` returns `verification results:: ... 0 errors` for `vest_lib` and the rest of the workspace still passes, you are done.

# Finishing

- Leave the final proof in place; commit nothing yourself (the harness handles git).
- In your final summary, list each target and whether you closed it or could not, and explicitly state whether you needed to use any of the forbidden actions above (with details).
