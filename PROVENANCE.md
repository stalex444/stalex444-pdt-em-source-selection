# Source provenance and extraction

The proofs were developed in Stephanie Alexander's PDT Canon 2 research and verified on 30 September 2026 (Lean 4.31.0,
Mathlib fabf563a, with per-batch verification receipts): C2-059 (`pdt-quadratic-source-uniqueness`: quadratic class,
209-equation certificate, coefficient recovery, Maxwell identification, controls), C2-060 (`pdt-conserved-source`:
conservation-only selection and consequences), C2-061/C2-062 (`pdt-polynomial-source`, `pdt-smooth-source`: linear
certificate, polynomial and C^3 classifications), and C2-063 (`pdt-sourceful-selection`: the exchange law and the
differentiable-only route). Supporting definitions come from C2-006 (`pdt-stress-source`: field, stress, stress balance),
C2-057 (`pdt-unrestricted-source-kernel`: embed, Hodge map), and the Lorentz-generator modules shared with the two
registered packages below.

Two registered packages supply ported infrastructure: `stalex444/pdt-hodge-lie-generation` at
`e2d8dde6f076b730b9a718c95ff1664c6aa88b51` (the `GravityScreening` library: register, orthogonal generators, local
Hodge data, and the `ResponseClosure*` modules) and `stalex444/pdt-metric-pfaffian-hodge-stabilizers` at
`0e436b9e3468e0393641d42fd37dfc9e3520ffbf` (the stabilizer modules defining `localIndex` and the cubic generator
action). Their selected theorems are not imported or resubmitted. One self-contained stub module of the second package
(`GeometryPrimitives`) duplicated definitions that the research modules define directly and was dropped in favour of the
research modules.

Extraction kept the transitive closure of the four research batches (fourteen folders, 83 root modules) and ported it to
Lean 4.35.0-rc2 with the Mathlib revision pinned in the manifest. Port changes: module-system declarations (`module`,
`public import`, `@[expose] public section`, the transparency compatibility option); `simp`/`dsimp` steps that no longer
act after `norm_num` wrapped in `try` or removed; tactics that now run after their goal is already closed guarded with
`all_goals`; and one declaration (`probe_formulas` in `UnrestrictedSourceKernel`) given an unbounded heartbeat budget.
No statement, definition or proof logic was changed.

`Challenge.lean` restates every definition from Mathlib alone, with the six Lorentz generators and the field action as
explicit tables. `StatementBridge.lean` re-declares the same definitions beside the research modules and proves them
equal to the research objects (the generator and field-action tables by the research module's own formula theorems;
everything else definitionally), then proves each compared statement from the research theorems. `Solution.lean` states
the twelve declarations and delegates to the bridge.

The original research folders and their receipts are preserved unchanged. See `VERIFICATION.md` for the build record.
