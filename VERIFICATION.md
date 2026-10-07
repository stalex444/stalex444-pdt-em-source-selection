# Verification status — 6 October 2026

**Local verification record, completed before publication.** Public-commit preflight results will be recorded
in the repository's Actions runs once the package is published; nothing below is a Palomar acceptance.

All 87 root modules and the 88 `GravityScreening` modules compile (every root library built as a target, 6–7 October 2026, exit 0; three smoke-test modules outside every proof closure were removed from the package rather than shipped) on Lean 4.35.0-rc2 against Mathlib revision
`065356127b1dc0016f66b7283ce0ce2c4055aa55`, with the nine transitive packages pinned in `lake-manifest.json`
(the same pin as the two registered packages this one builds on). `lake build Solution Challenge` exits 0.

The twelve selected declarations in `Solution.lean` each depend on exactly `propext`, `Classical.choice` and
`Quot.sound` (recorded by `#print axioms` on a direct recompile of `Solution.lean`, 6 October 2026). No module in the
package contains `sorry` outside the twelve `sorry` placeholders of `Challenge.lean`, and no module uses
`native_decide` or declares an axiom. `Challenge.lean` imports Mathlib alone. `comparator.json`, `Solution.lean` and
`Challenge.lean` name the same twelve declarations in the same order.

## Completed local checks

- Full compile of the research closure after the port (eleven build rounds, 6 October 2026). Port repairs, all
  recorded in `PROVENANCE.md`: `simp`/`dsimp` steps that no longer act wrapped in `try` or removed
  (`FinitePfaffian`, `SourceMaxwell`, `CrossSource`); tactics running after their goal is already closed guarded with
  `all_goals` (`SourceControls`, `ConservationControls`, `SmoothConsequences`); one declaration given an unbounded
  heartbeat budget (`UnrestrictedSourceKernel.probe_formulas`). No statement or proof logic changed.
- The statement bridge proves every Challenge object equal to the corresponding research object — the Lorentz
  generator and field-action tables by the research module's own formula theorems
  (`PDTQuadraticSource.lorentz_formula`, `PDTQuadraticSource.field_action_formula`), all other definitions by `rfl` —
  and derives each compared statement from the research theorem it corresponds to
  (`source_classification`, `source_uniqueness`, `finite_certificate`, `conserved_source_classification`,
  `conservation_forces_hodge_invariance`, `regular_source_polynomial` + `conserved_polynomial_classification`,
  `smooth_zero_field_selection`, `differentiable_sourceful_classification`,
  `differentiable_normalized_selection`, and the four control theorems).
- The original research batches (C2-059, C2-060, C2-062, C2-063) carry their own 30 September 2026 verification
  receipts on Lean 4.31.0 / Mathlib fabf563a, with 38, 42, 21 and 29 independent exact checks respectively; those
  receipts and sources are preserved unchanged.
- MSC2020 codes are `15A72` (vector and tensor algebra, invariant theory), `35Q61` (Maxwell equations) and `70S10`
  (symmetries and conservation laws in field theory). These describe the selected mathematics.

## Not yet done

- The official pinned preflight (`.github/workflows/palomar-preflight.yml`) on the exact public commit, in Palomar's
  Linux sandbox with the independent kernels. Local compilation used the pinned dependency cache and is not a
  substitute. Before submission the published package must pass that workflow with zero errors and zero warnings.
- An adversarial proof review of the package by a second agent. The literature pass is recorded in `PRIOR_WORK.md`.
- `local-checks.json` with source hashes, to be generated at publication.

No acceptance or public registry ID is claimed for this package. The two registered packages it builds on are unchanged.
