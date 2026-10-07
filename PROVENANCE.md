# Source provenance and extraction

The proofs were developed in Stephanie Alexander's PDT Canon 2 research and verified on 30 September 2026 (Lean 4.31.0,
Mathlib fabf563a, with per-batch verification receipts): C2-059 (`pdt-quadratic-source-uniqueness`: quadratic class,
209-equation certificate, coefficient recovery, Maxwell identification, controls; 38 exact checks), C2-060
(`pdt-conserved-source`: conservation-only selection and consequences; 42 checks), C2-061 (`pdt-polynomial-source`:
linear certificate, cross family and the polynomial classification that the C^3 route reduces to; 32 checks), C2-062
(`pdt-smooth-source`: the C^3 reduction and the zero-field selection; 21 checks), and C2-063 (`pdt-sourceful-selection`:
the exchange law and the differentiable-only route; 29 checks). Supporting definitions come from C2-006
(`pdt-stress-source`: field, stress, stress balance), C2-057 (`pdt-unrestricted-source-kernel`: embed, Hodge map), and
the Lorentz-generator modules shared with the two registered packages below.

Two registered packages supply ported infrastructure: `stalex444/pdt-hodge-lie-generation` at
`e2d8dde6f076b730b9a718c95ff1664c6aa88b51` (the `GravityScreening` library: register, orthogonal generators, local
Hodge data, and the three `ResponseClosure*` root modules) and `stalex444/pdt-metric-pfaffian-hodge-stabilizers` at
`0e436b9e3468e0393641d42fd37dfc9e3520ffbf` (the stabilizer modules defining `localIndex` and the cubic generator
action). Their selected theorems are not imported or resubmitted. One self-contained stub module of the second package
(`GeometryPrimitives`) duplicated definitions that the research modules define directly and was dropped in favour of the
research modules. Of the 88 `GravityScreening` modules in the first package, the eight outside every import closure of
this package (`AdjointResponseUniqueness`, `HodgeBulkScreen`, `HorizonEinsteinClosureCapstone`, `PdtOpticalRepair`,
`PdtStabilizer`, `QuantumGalileoPhase`, `StructuralGravityExponent`, `TwoSidedTraceFree`) were dropped rather than
shipped unbuilt; 80 remain, every one of them in the closure of a root module. Three smoke-test modules of the research
batches, outside every proof closure, were dropped on the same rule.

The 87 root modules are: 3 written for this package (`Challenge`, `Solution`, `StatementBridge`), 3 copied from the
first registered package (`ResponseClosureCertificate`, `ResponseClosureGeometry`, `ResponseClosureOrthogonalBasis`),
and 81 research modules whose originals sit in 21 Codex output folders (the five batches above, their supporting
batches, and the shared generator modules). Extraction kept the transitive import closure of the five research batches
and ported it to Lean 4.35.0-rc2 with the Mathlib revision pinned in the manifest.

## Port changes, by module

Every module gained the module-system header (`module`, `public import`, `@[expose] public section`) and the
elaboration option `set_option backward.isDefEq.respectTransparency false`. Beyond that, a line diff against the Codex
originals (ignoring those header lines) shows 19 of the 81 research modules changed, as follows.

- `dsimp` that no longer acts wrapped in `try`: `BoundaryConnection`, `ConservationJets`, `CrossSource`,
  `MaxwellResponse`, `MaxwellSymbol`, `PolynomialConsequences`, `PolynomialUniqueness`, `SourceMaxwell`,
  `SmoothConsequences`.
- Tactics that now run after their goal is already closed guarded with `all_goals`: `ConservationControls`,
  `DifferentiableSourceful`, `SmoothConsequences`, `SourceControls` (where one `ring` became `all_goals ring1`),
  `SourcefulSelection`.
- Tactic steps that no longer act removed outright: the trailing `<;> rfl` on every action lemma of `CubicInvariance`,
  twelve `rfl` lines in `StabilizerRecovery`, and `simp +decide only [ite_false]` before `ring!` in `FinitePfaffian`.
- One declaration given an unbounded heartbeat budget: `probe_formulas` in `UnrestrictedSourceKernel`.
- One visibility change: `metricIntegral` in `StabilizerControls` is no longer `private`.
- One module trimmed: `PfaffianBridge` now imports `ResponseBridge`, `HodgeConnection`, `StressTensor` and
  `GravityScreening.HodgeLieGeneration` instead of the dropped `CompanionCompatibility`, and the definition
  `pfaffianGenerated` with the theorems `generated_same`, `generated_sl`, `generated_dimension`,
  `hessian_reads_as_phase` and `companion_from_pfaffian` (the first registered package's selected theorems and their
  companions, with their `#print axioms`) were removed; `CubicInvariance` imports `PfaffianBridge` in place of
  `PfaffianEM` accordingly.

No compared statement, and no research theorem that `StatementBridge.lean` invokes, was changed. The removals in
`PfaffianBridge` are the registered theorems this package does not resubmit.

`Challenge.lean` restates every definition from Mathlib alone, with the six Lorentz generators and the field action as
explicit tables. `StatementBridge.lean` re-declares the same definitions beside the research modules and proves them
equal to the research objects (the generator and field-action tables by the research module's own formula theorems;
everything else definitionally), then proves each compared statement from the research theorems. `Solution.lean` states
the twelve declarations and delegates to the bridge.

The original research folders and their receipts are preserved unchanged. See `VERIFICATION.md` for the build record.
