# Changes from Upstream VeriSoftBench

Summary of all modifications made to reproduce the evaluation.

## Fixes to the Evaluation Process

Changes to the [official VeriSoftBench](https://github.com/utopia-group/VeriSoftBench) evaluation scripts, applied in the [`verisoftbench` branch](https://github.com/logiq-ai/verisoftbench-repos/tree/verisoftbench).

### Connector (new functionality)

Custom `ProverInterface` that reads `.patch` files from AlephProver and uses GPT-5.4 to extract proofs into the XML format the benchmark expects.

- [`core/patch_prover.py`](https://github.com/logiq-ai/verisoftbench-repos/blob/verisoftbench/core/patch_prover.py) — PatchProverInterface
- [`configs/aleph_patch.yaml`](https://github.com/logiq-ai/verisoftbench-repos/blob/verisoftbench/configs/aleph_patch.yaml) — evaluation config

Minor changes to wire it in:
- `core/evaluator.py` — import + route to PatchProverInterface when `model_name == "patch"`
- `evaluate.py` — pass through `patches_dir`, `results_json`, `extraction_model_id` from config

### Bug fix: `_clean_thm_stmt` truncates `let` bindings (task 163)

The benchmark's `_clean_thm_stmt` function incorrectly matches `:=` inside a `let` binding in the theorem's return type as the proof separator, destroying the statement. Affects `Circuit.FoldlM.forAll_iff_const` which has `let acc := ...` in its type.

- [Commit `09a4ba9`](https://github.com/logiq-ai/verisoftbench-repos/commit/09a4ba9) — skip body-stripping for this theorem

Full diff from upstream: [compare](https://github.com/logiq-ai/verisoftbench-repos/compare/ad1591d..verisoftbench)

## Fixes to Original Lean Repos

Changes to make `lake build` succeed on the 23 VeriSoftBench repos, applied in the [`main` branch](https://github.com/logiq-ai/verisoftbench-repos/tree/main).

### Build fixes

- Toolchain/dependency version bumps (Mathlib pinned to v4.10.0, lean-formal-reasoning-program and pcf-lean upgraded to v4.14.0, iris-lean Qq dependency updated to v4.26.0 tag)
- SAT solver timeouts increased for `bv_decide` in the clean project
- Sorry'd out broken proofs in clean that prevented compilation
- Stubbed out loom's `DoNames.lean` (Lean 3 `meta` keyword)
- Fixed veil build targets and smt dependency

Full diff of all build fixes: [compare](https://github.com/logiq-ai/verisoftbench-repos/compare/0f45d1a..88050d7)

### Proof stripping

Replaced all 100 ground truth proofs with `by sorry` so AlephProver doesn't see the original solutions when tasks are submitted. 53 files across 11 repos.

Full PR: [#124](https://github.com/logiq-ai/verisoftbench-repos/pull/124)

Iris-lean Qq dependency fix (after PR merge): [commit `20fe01d`](https://github.com/logiq-ai/verisoftbench-repos/commit/20fe01d)
