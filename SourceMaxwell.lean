module
public import SourceCoefficientData

@[expose] public section
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
namespace PDTQuadraticSource
noncomputable section
open PDTStressTensor PDTUnrestrictedSourceKernel
open scoped Matrix

theorem source_smul (a : ℝ) (c : Coeff) (x : Local) :
    source (a • c) x=a • source c x := by
  ext i j
  simp [source,poly,Finset.mul_sum,mul_assoc]

/-- The coefficient line is the original stress, including its original signs and factor 1/2. -/
theorem maxwell_original (x : Local) :
    source maxwellCoefficients x=registerStress 1 (embed x) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [source,poly,monomialPair,tensorIndex,maxwellCoefficients,Fin.sum_univ_succ,
      registerStress,stress,field,embed,metric,eta,Matrix.diagonal,invariant,PDTMaxwellSymbol.mink] <;>
    ring
theorem scaled_maxwell_original (d : ℝ) (x : Local) :
    source (d • maxwellCoefficients) x=registerStress d (embed x) := by
  rw [source_smul,maxwell_original]
  exact (stress_coefficient d (field (embed x))).symm

theorem original_is_quadratic (d : ℝ) :
    IsQuadraticSource (fun x => registerStress d (embed x)) := by
  refine ⟨d • maxwellCoefficients,?_⟩
  funext x
  exact (scaled_maxwell_original d x).symm

theorem original_trace_free (d : ℝ) :
    TraceFree (fun x => registerStress d (embed x)) := by
  intro x
  exact stress_traceless d (field (embed x))

/-- Full polynomial covariance on every field, for all six actual generators. -/
theorem maxwell_covariance (d : ℝ) : Covariant (source (d • maxwellCoefficients)) := by
  apply (covariance_iff _).mpr
  intro k x
  ext i j
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    norm_num [variation,dpoly,source,poly,maxwellCoefficients,monomialPair,tensorIndex,
      field_action_formula,tensorAction,lorentz_formula,lorentzTable,Matrix.mul_apply,
      Matrix.transpose_apply,Fin.sum_univ_succ] <;> ring

theorem original_covariant (d : ℝ) : Covariant (fun x => registerStress d (embed x)) := by
  have h : (fun x => registerStress d (embed x))=source (d • maxwellCoefficients) := by
    funext x
    exact (scaled_maxwell_original d x).symm
  rw [h]
  exact maxwell_covariance d

theorem original_scale_unique (a b : ℝ)
    (h : (fun x => registerStress a (embed x))=(fun x => registerStress b (embed x))) : a=b := by
  have he := congrArg (fun S : Local → Tensor => S (Pi.single 0 1) 3 3) h
  simp [register_energy,embed] at he
  linarith

#print axioms source_smul
#print axioms maxwell_original
#print axioms scaled_maxwell_original
#print axioms original_is_quadratic
#print axioms original_trace_free
#print axioms maxwell_covariance
#print axioms original_covariant
#print axioms original_scale_unique
end
end PDTQuadraticSource
