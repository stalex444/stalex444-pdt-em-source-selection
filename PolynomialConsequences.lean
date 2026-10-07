module
public import PolynomialUniqueness

@[expose] public section
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
namespace PDTPolynomialSource
noncomputable section
open PDTStressTensor PDTUnrestrictedSourceKernel PDTQuadraticSource PDTConservedSource
open scoped Matrix

theorem covariant_as_conserved (c d : ℝ) :
    covariantFamily c d=conservedFamily (metricCoefficients c) 0 d := by
  funext x
  simp only [covariantFamily,conservedFamily,constant_metric_coefficients,cross_zero,
    linear_zero_coefficients,add_zero]

theorem covariant_family_trace (c d : ℝ) (x : Local) :
    covariantFamily c d x 0 0+covariantFamily c d x 1 1+
      covariantFamily c d x 2 2-covariantFamily c d x 3 3=4*c := by
  have h := original_trace_free d x
  simp only [covariantFamily,Matrix.add_apply]
  norm_num [metric,eta,Matrix.diagonal_apply]
  try dsimp
  norm_num
  linarith only [h]

theorem trace_free_iff_no_constant (c d : ℝ) : TraceFree (covariantFamily c d) ↔ c=0 := by
  constructor
  · intro h
    have hh := h 0
    rw [covariant_family_trace] at hh
    linarith only [hh]
  · intro h x
    rw [covariant_family_trace,h,mul_zero]

theorem zero_field_iff_no_constant (c d : ℝ) : covariantFamily c d 0=0 ↔ c=0 := by
  rw [covariant_family_at_zero]
  constructor
  · intro h
    have hh := congrFun (congrFun h 0) 0
    simpa [metric,eta,Matrix.diagonal_apply] using hh
  · intro h
    rw [h,zero_smul]

/-- Either a zero-field condition or zero metric trace removes the sole constant freedom. -/
theorem zero_field_and_trace_equivalent (S : Local → Tensor) (hp : IsPolynomialSource S)
    (hc : Conserved S) (hv : Covariant S) :
    (S 0=0 ↔ TraceFree S) ∧
    (S 0=0 ↔ ∃ d : ℝ, S=fun x => registerStress d (embed x)) := by
  obtain ⟨c,d,rfl⟩ := (covariant_conserved_polynomial_classification S hp).mp ⟨hc,hv⟩
  refine ⟨(zero_field_iff_no_constant c d).trans (trace_free_iff_no_constant c d).symm,?_⟩
  constructor
  · intro h
    have hh := (zero_field_iff_no_constant c d).mp h
    refine ⟨d,?_⟩
    funext x
    simp only [covariantFamily,hh,zero_smul,zero_add]
  · rintro ⟨e,he⟩
    rw [he]
    exact original_stress_zero e

theorem polynomial_hodge_invariance (S : Local → Tensor) (hp : IsPolynomialSource S)
    (hc : Conserved S) (hv : Covariant S) (x : Local) : S (J *ᵥ x)=S x := by
  obtain ⟨c,d,rfl⟩ := (covariant_conserved_polynomial_classification S hp).mp ⟨hc,hv⟩
  unfold covariantFamily
  congr 1
  change stress d (field (embed (J *ᵥ x)))=stress d (field (embed x))
  rw [local_hodge_field]
  exact actual_hodge_preserves_stress d (embed x)

theorem polynomial_source_not_injective (S : Local → Tensor) (hp : IsPolynomialSource S)
    (hc : Conserved S) (hv : Covariant S) : ¬ Function.Injective S := by
  intro hi
  have he := hi (polynomial_hodge_invariance S hp hc hv ![1,0,0,0,0,0])
  have hh := congrFun he 0
  norm_num [J,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] at hh

/-- Enlarging the class really allows a nonzero constant, so trace zero no longer follows. -/
theorem constant_trace_control : IsPolynomialSource (covariantFamily 1 0) ∧
    Conserved (covariantFamily 1 0) ∧ Covariant (covariantFamily 1 0) ∧
    ¬ TraceFree (covariantFamily 1 0) := by
  obtain ⟨hp,hc,hv⟩ := covariant_family_converse 1 0
  refine ⟨hp,hc,hv,?_⟩
  rw [trace_free_iff_no_constant]
  norm_num

/-- A fixed nonzero background cross term witnesses why covariance is needed. -/
theorem background_covariance_control :
    IsPolynomialSource (conservedFamily 0 ![1,0,0,0,0,0] 0) ∧
    Conserved (conservedFamily 0 ![1,0,0,0,0,0] 0) ∧
    ¬ Covariant (conservedFamily 0 ![1,0,0,0,0,0] 0) := by
  obtain ⟨hp,hc⟩ := conserved_family_converse 0 ![1,0,0,0,0,0] 0
  refine ⟨hp,hc,?_⟩
  intro hv
  obtain ⟨c,d,he⟩ := (covariant_conserved_polynomial_classification _ hp).mp ⟨hc,hv⟩
  rw [covariant_as_conserved] at he
  have hh := (conserved_parameters_unique _ _ _ _ _ _ he).2.1
  have hz := congrFun hh 0
  norm_num at hz

/-- A direction-dependent constant is a separate conserved, noncovariant control. -/
theorem constant_covariance_control :
    IsPolynomialSource (conservedFamily ![1,0,0,0,0,0,0,0,0,0] 0 0) ∧
    Conserved (conservedFamily ![1,0,0,0,0,0,0,0,0,0] 0 0) ∧
    ¬ Covariant (conservedFamily ![1,0,0,0,0,0,0,0,0,0] 0 0) := by
  obtain ⟨hp,hc⟩ := conserved_family_converse ![1,0,0,0,0,0,0,0,0,0] 0 0
  refine ⟨hp,hc,?_⟩
  intro hv
  obtain ⟨c,d,he⟩ := (covariant_conserved_polynomial_classification _ hp).mp ⟨hc,hv⟩
  rw [covariant_as_conserved] at he
  have hh := (conserved_parameters_unique _ _ _ _ _ _ he).1
  have h0 := congrFun hh 0
  have h4 := congrFun hh 4
  change (1 : ℝ)=c at h0
  change (0 : ℝ)=c at h4
  linarith only [h0,h4]

#print axioms covariant_as_conserved
#print axioms covariant_family_trace
#print axioms trace_free_iff_no_constant
#print axioms zero_field_iff_no_constant
#print axioms zero_field_and_trace_equivalent
#print axioms polynomial_hodge_invariance
#print axioms polynomial_source_not_injective
#print axioms constant_trace_control
#print axioms background_covariance_control
#print axioms constant_covariance_control
end
end PDTPolynomialSource
