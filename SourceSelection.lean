module
public import SourceCoefficientBridge
public import SourceCoefficientRecovery
public import SourceMaxwell

@[expose] public section
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
namespace PDTQuadraticSource
noncomputable section
open PDTStressTensor PDTUnrestrictedSourceKernel

/-- The geometric hypotheses force the original stress, with one uniquely determined scale. -/
theorem source_uniqueness (S : Local → Tensor) (hq : IsQuadraticSource S)
    (hc : Covariant S) (ht : TraceFree S) :
    ∃! d : ℝ, S=fun x => registerStress d (embed x) := by
  obtain ⟨c,rfl⟩ := hq
  have hr := coefficient_recovery c (constraints_from_laws c hc ht)
  have hs : source c=fun x => registerStress (2*c 0 0) (embed x) := by
    conv_lhs => rw [hr]
    funext x
    exact scaled_maxwell_original (2*c 0 0) x
  refine ⟨2*c 0 0,hs,?_⟩
  intro d hd
  exact original_scale_unique d (2*c 0 0) (hd.symm.trans hs)

/-- A classification of source functions, with both directions proved. -/
theorem source_classification (S : Local → Tensor) (hq : IsQuadraticSource S) :
    (Covariant S ∧ TraceFree S) ↔ ∃ d : ℝ, S=fun x => registerStress d (embed x) := by
  constructor
  · intro ⟨hc,ht⟩
    obtain ⟨d,hd,_⟩ := source_uniqueness S hq hc ht
    exact ⟨d,hd⟩
  · rintro ⟨d,rfl⟩
    exact ⟨original_covariant d,original_trace_free d⟩

/-- The finite certificate is equivalent to the all-field geometric conditions. -/
theorem finite_certificate (c : Coeff) :
    constraints c=0 ↔ Covariant (source c) ∧ TraceFree (source c) := by
  constructor
  · intro h
    have hr := coefficient_recovery c h
    have hs : source c=fun x => registerStress (2*c 0 0) (embed x) := by
      conv_lhs => rw [hr]
      funext x
      exact scaled_maxwell_original (2*c 0 0) x
    rw [hs]
    exact ⟨original_covariant _,original_trace_free _⟩
  · rintro ⟨hc,ht⟩
    exact constraints_from_laws c hc ht

/-- Covariance and zero trace leave the overall strength free. -/
theorem scale_is_free (d : ℝ) :
    IsQuadraticSource (fun x => registerStress d (embed x)) ∧
    Covariant (fun x => registerStress d (embed x)) ∧
    TraceFree (fun x => registerStress d (embed x)) :=
  ⟨original_is_quadratic d,original_covariant d,original_trace_free d⟩

theorem two_distinct_scales :
    (fun x => registerStress 1 (embed x)) ≠ (fun x => registerStress 2 (embed x)) := by
  intro h
  have hh := original_scale_unique 1 2 h
  norm_num at hh

#print axioms source_uniqueness
#print axioms source_classification
#print axioms finite_certificate
#print axioms scale_is_free
#print axioms two_distinct_scales
end
end PDTQuadraticSource
