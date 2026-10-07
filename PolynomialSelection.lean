module
public import LinearSourceBridge
public import LinearSourceRecovery
public import LowerCovariance

@[expose] public section
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
namespace PDTPolynomialSource
noncomputable section
open PDTStressTensor PDTUnrestrictedSourceKernel PDTQuadraticSource PDTConservedSource
open scoped Matrix

def conservedFamily (A : ConstantCoeff) (b : Local) (d : ℝ) (x : Local) : Tensor :=
  constant A+linear (crossCoefficients b) x+registerStress d (embed x)

def covariantFamily (c d : ℝ) (x : Local) : Tensor := c • metric+registerStress d (embed x)

def metricCoefficients (c : ℝ) : ConstantCoeff := ![c,0,0,0,c,0,0,c,0,-c]

theorem constant_metric_coefficients (c : ℝ) : constant (metricCoefficients c)=c • metric := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [constant,metricCoefficients,tensorIndex,metric,eta]

theorem linear_zero_coefficients (x : Local) : linear 0 x=0 := by
  ext i j
  simp [linear]

theorem conserved_family_polynomial (A : ConstantCoeff) (b : Local) (d : ℝ) :
    conservedFamily A b d=polynomial A (crossCoefficients b) (d • maxwellCoefficients) := by
  funext x
  simp only [conservedFamily,polynomial,scaled_maxwell_original]

theorem covariant_family_polynomial (c d : ℝ) :
    covariantFamily c d=polynomial (metricCoefficients c) 0 (d • maxwellCoefficients) := by
  funext x
  simp only [covariantFamily,polynomial,scaled_maxwell_original,constant_metric_coefficients,
    linear_zero_coefficients,add_zero]

theorem conserved_family_converse (A : ConstantCoeff) (b : Local) (d : ℝ) :
    IsPolynomialSource (conservedFamily A b d) ∧ Conserved (conservedFamily A b d) := by
  rw [conserved_family_polynomial]
  refine ⟨⟨A,crossCoefficients b,d • maxwellCoefficients,rfl⟩,?_⟩
  apply (conservation_split _ _ _).mpr
  refine ⟨cross_conserved b,?_⟩
  have hs : source (d • maxwellCoefficients)=(fun x => registerStress d (embed x)) := by
    funext x
    exact scaled_maxwell_original d x
  rw [hs]
  exact original_conserved d

/-- All conserved symmetric sources of degree at most two: ten constant,
six fixed-background cross, and one quadratic-scale parameter. -/
theorem conserved_polynomial_classification (S : Local → Tensor) (hp : IsPolynomialSource S) :
    Conserved S ↔ ∃ A b d, S=conservedFamily A b d := by
  constructor
  · intro hc
    obtain ⟨A,l,q,rfl⟩ := hp
    obtain ⟨hl,hq⟩ := (conservation_split A l q).mp hc
    have hr := linear_recovery l (linear_constraints_from_law l hl)
    obtain ⟨d,hd⟩ := (conserved_source_classification (source q) ⟨q,rfl⟩).mp hq
    refine ⟨A,background l,d,?_⟩
    funext x
    unfold polynomial conservedFamily
    rw [hd]
    exact congrArg (fun z => constant A+linear z x+registerStress d (embed x)) hr
  · rintro ⟨A,b,d,rfl⟩
    exact (conserved_family_converse A b d).2

theorem covariant_family_converse (c d : ℝ) :
    IsPolynomialSource (covariantFamily c d) ∧
    Conserved (covariantFamily c d) ∧ Covariant (covariantFamily c d) := by
  have he : covariantFamily c d=conservedFamily (metricCoefficients c) 0 d := by
    funext x
    simp only [covariantFamily,conservedFamily,constant_metric_coefficients,cross_zero,
      linear_zero_coefficients,add_zero]
  refine ⟨he ▸ (conserved_family_converse (metricCoefficients c) 0 d).1,
    he ▸ (conserved_family_converse (metricCoefficients c) 0 d).2,?_⟩
  rw [covariant_family_polynomial]
  apply (polynomial_covariance_iff _ _ _).mpr
  intro k x
  have hs : source (d • maxwellCoefficients)=(fun z => registerStress d (embed z)) := by
    funext z
    exact scaled_maxwell_original d z
  have hq : Covariant (source (d • maxwellCoefficients)) := hs ▸ original_covariant d
  rw [linear_zero_coefficients,zero_add,(PDTQuadraticSource.covariance_iff _).mp hq k x]
  simp only [polynomial,linear_zero_coefficients,add_zero,constant_metric_coefficients,
    tensor_action_add,metric_tensor_action,zero_add]

/-- The original conservation and covariance laws leave precisely the EM stress
plus a constant multiple of the original metric. -/
theorem covariant_conserved_polynomial_classification (S : Local → Tensor)
    (hp : IsPolynomialSource S) :
    Conserved S ∧ Covariant S ↔ ∃ c d : ℝ, S=covariantFamily c d := by
  constructor
  · rintro ⟨hc,hv⟩
    obtain ⟨A,l,q,rfl⟩ := hp
    obtain ⟨hl,hq⟩ := (conservation_split A l q).mp hc
    obtain ⟨hA,hL⟩ := covariance_lower_parts A l q hv
      (conservation_forces_covariance_and_trace _ ⟨q,rfl⟩ hq).1
    have hr := linear_recovery l (linear_constraints_from_law l hl)
    have hb : background l=0 := covariant_background_zero _ (hr ▸ hL)
    have hl0 : l=0 := hr.trans (by rw [hb,cross_zero])
    obtain ⟨d,hd⟩ := (conserved_source_classification (source q) ⟨q,rfl⟩).mp hq
    refine ⟨A 0,d,?_⟩
    funext x
    simp only [polynomial,covariantFamily,constant_is_metric A hA,hl0,
      linear_zero_coefficients,add_zero,hd]
  · rintro ⟨c,d,rfl⟩
    exact (covariant_family_converse c d).2

#print axioms constant_metric_coefficients
#print axioms linear_zero_coefficients
#print axioms conserved_family_polynomial
#print axioms covariant_family_polynomial
#print axioms conserved_family_converse
#print axioms conserved_polynomial_classification
#print axioms covariant_family_converse
#print axioms covariant_conserved_polynomial_classification
end
end PDTPolynomialSource
