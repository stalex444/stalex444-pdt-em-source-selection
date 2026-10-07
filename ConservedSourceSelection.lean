module
public import ConservationBridge
public import ConservationRecovery

@[expose] public section
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
namespace PDTConservedSource
noncomputable section
open PDTStressTensor PDTUnrestrictedSourceKernel PDTQuadraticSource

/-- Within the complete symmetric homogeneous quadratic class, Maxwell conservation
alone forces the original source, with exactly one real coefficient. -/
theorem conserved_source_uniqueness (S : Local → Tensor) (hq : IsQuadraticSource S)
    (hc : Conserved S) : ∃! d : ℝ, S=fun x => registerStress d (embed x) := by
  obtain ⟨c,rfl⟩ := hq
  have hr := conservation_recovery c (constraints_from_conservation c hc)
  have hs : source c=fun x => registerStress (2*c 0 0) (embed x) := by
    conv_lhs => rw [hr]
    funext x
    exact scaled_maxwell_original (2*c 0 0) x
  refine ⟨2*c 0 0,hs,?_⟩
  intro d hd
  exact original_scale_unique d (2*c 0 0) (hd.symm.trans hs)

theorem conserved_source_classification (S : Local → Tensor) (hq : IsQuadraticSource S) :
    Conserved S ↔ ∃ d : ℝ, S=fun x => registerStress d (embed x) := by
  constructor
  · intro hc
    obtain ⟨d,hd,_⟩ := conserved_source_uniqueness S hq hc
    exact ⟨d,hd⟩
  · rintro ⟨d,rfl⟩
    exact original_conserved d

theorem conservation_forces_covariance_and_trace (S : Local → Tensor)
    (hq : IsQuadraticSource S) (hc : Conserved S) : Covariant S ∧ TraceFree S := by
  obtain ⟨d,rfl⟩ := (conserved_source_classification S hq).mp hc
  exact ⟨original_covariant d,original_trace_free d⟩

/-- Conservation and the previous geometric characterization select exactly the same class. -/
theorem conservation_iff_covariance_and_trace (S : Local → Tensor)
    (hq : IsQuadraticSource S) : Conserved S ↔ Covariant S ∧ TraceFree S := by
  rw [conserved_source_classification S hq,source_classification S hq]

theorem finite_conservation_certificate (c : Coeff) :
    conservationConstraints c=0 ↔ Conserved (source c) := by
  constructor
  · intro h
    have hr := conservation_recovery c h
    have hs : source c=fun x => registerStress (2*c 0 0) (embed x) := by
      conv_lhs => rw [hr]
      funext x
      exact scaled_maxwell_original (2*c 0 0) x
    rw [hs]
    exact original_conserved _
  · exact constraints_from_conservation c

theorem conserved_scale_free (d : ℝ) :
    IsQuadraticSource (fun x => registerStress d (embed x)) ∧
    Conserved (fun x => registerStress d (embed x)) :=
  ⟨original_is_quadratic d,original_conserved d⟩

#print axioms conserved_source_uniqueness
#print axioms conserved_source_classification
#print axioms conservation_forces_covariance_and_trace
#print axioms conservation_iff_covariance_and_trace
#print axioms finite_conservation_certificate
#print axioms conserved_scale_free
end
end PDTConservedSource
