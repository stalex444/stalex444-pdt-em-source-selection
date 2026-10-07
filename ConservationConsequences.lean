module
public import ConservedSourceSelection
public import ConservationControls
public import SourceKernelConsequences

@[expose] public section
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
namespace PDTConservedSource
noncomputable section
open PDTStressTensor PDTUnrestrictedSourceKernel PDTQuadraticSource
open scoped Matrix

theorem metric_invariant_not_conserved : ¬ Conserved (source metricInvariantCoefficients) := by
  intro h
  exact metric_invariant_not_trace_free
    (conservation_forces_covariance_and_trace _ ⟨metricInvariantCoefficients,rfl⟩ h).2

/-- The original Hodge invariance follows from conservation within this source class. -/
theorem conservation_forces_hodge_invariance (S : Local → Tensor)
    (hq : IsQuadraticSource S) (hc : Conserved S) (x : Local) : S (J *ᵥ x)=S x := by
  obtain ⟨d,rfl⟩ := (conserved_source_classification S hq).mp hc
  change stress d (field (embed (J *ᵥ x)))=stress d (field (embed x))
  rw [local_hodge_field]
  exact actual_hodge_preserves_stress d (embed x)

/-- An explicit nonzero field and its actual Hodge image cannot be distinguished by such a source. -/
theorem conserved_source_not_injective (S : Local → Tensor)
    (hq : IsQuadraticSource S) (hc : Conserved S) : ¬ Function.Injective S := by
  intro hi
  have he := hi (conservation_forces_hodge_invariance S hq hc ![1,0,0,0,0,0])
  have hh := congrFun he 0
  norm_num [J,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] at hh

/-- Counterexamples to extending the conclusions past the stated source class. -/
theorem source_class_controls :
    (∃ S : Local → Tensor, Conserved S ∧ ¬ IsQuadraticSource S ∧ ¬ TraceFree S) ∧
    (∃ S : Local → Tensor, Conserved S ∧
      (∀ i j, ∃ c : Fin 21 → ℝ, ∀ x, S x i j=poly c x) ∧
      ¬ ∀ x, (S x).transpose=S x) :=
  ⟨⟨fun _ => metric,constant_metric_conserved,constant_metric_not_quadratic,
      constant_metric_not_trace_free⟩,
    ⟨columnSource,column_conserved,column_quadratic_entries,column_not_symmetric⟩⟩

#print axioms metric_invariant_not_conserved
#print axioms conservation_forces_hodge_invariance
#print axioms conserved_source_not_injective
#print axioms source_class_controls
end
end PDTConservedSource
