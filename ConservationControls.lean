module
public import ConservationLaws

@[expose] public section
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
namespace PDTConservedSource
noncomputable section
open PDTStressTensor PDTUnrestrictedSourceKernel PDTQuadraticSource
open scoped Matrix

/-- Dropping homogeneity admits a constant metric contribution. -/
theorem constant_metric_conserved : Conserved (fun _ => metric) := by
  intro x D _
  funext ν
  simp [divergence]

theorem quadratic_at_zero (c : Coeff) : source c 0=0 := by
  ext i j
  simp [source,poly]

theorem constant_metric_not_quadratic : ¬ IsQuadraticSource (fun _ => metric) := by
  rintro ⟨c,h⟩
  have hh := congrArg (fun S : Local → Tensor => S 0 0 0) h
  rw [quadratic_at_zero] at hh
  norm_num [metric,Matrix.diagonal,eta] at hh

theorem constant_metric_not_trace_free : ¬ TraceFree (fun _ => metric) := by
  intro h
  have hh := h 0
  norm_num [metric,Matrix.diagonal,eta] at hh

/-- Selecting just one stress column preserves conservation but removes symmetry. -/
def columnSource (x : Local) : Tensor := fun μ ν =>
  if ν=0 then registerStress 1 (embed x) μ ν else 0

theorem column_conserved : Conserved columnSource := by
  intro x D hD
  funext ν
  by_cases hv : ν=0
  · simpa [divergence,columnSource,hv] using congrFun (original_conserved 1 x D hD) ν
  · simp [divergence,columnSource,hv]

theorem column_quadratic_entries (i j : Fin 4) :
    ∃ c : Fin 21 → ℝ, ∀ x, columnSource x i j=poly c x := by
  by_cases hj : j=0
  · refine ⟨maxwellCoefficients (tensorIndex i j),?_⟩
    intro x
    simp [columnSource,hj,← maxwell_original,source]
  · refine ⟨0,?_⟩
    intro x
    simp [columnSource,hj,poly]

theorem column_not_symmetric : ¬ ∀ x, (columnSource x).transpose=columnSource x := by
  intro h
  have hh := congrArg (fun T : Tensor => T 0 1) (h ![0,1,0,1,0,0])
  norm_num [columnSource,registerStress,stress,field,embed,metric,Matrix.diagonal,eta,
    invariant,PDTMaxwellSymbol.mink,Matrix.transpose_apply] at hh

#print axioms constant_metric_conserved
#print axioms quadratic_at_zero
#print axioms constant_metric_not_quadratic
#print axioms constant_metric_not_trace_free
#print axioms column_conserved
#print axioms column_quadratic_entries
#print axioms column_not_symmetric
end
end PDTConservedSource
