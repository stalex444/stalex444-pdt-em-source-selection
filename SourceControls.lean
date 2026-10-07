module
public import SourceMaxwell

@[expose] public section
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
namespace PDTQuadraticSource
noncomputable section
open PDTStressTensor PDTUnrestrictedSourceKernel
open scoped Matrix

/-- Metric times the electromagnetic scalar invariant, a competing quadratic covariant source. -/
def metricInvariantCoefficients : Coeff :=
  ![![2,0,0,0,0,0,2,0,0,0,0,-2,0,0,0,2,0,0,-2,0,-2],
    ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![2,0,0,0,0,0,2,0,0,0,0,-2,0,0,0,2,0,0,-2,0,-2],
    ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![2,0,0,0,0,0,2,0,0,0,0,-2,0,0,0,2,0,0,-2,0,-2],
    ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![-2,0,0,0,0,0,-2,0,0,0,0,2,0,0,0,-2,0,0,2,0,2]]

/-- A trace-free but frame-dependent quadratic source. -/
def anisotropicCoefficients : Coeff :=
  ![![1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]

theorem metric_invariant_formula (x : Local) :
    source metricInvariantCoefficients x=
    (2*(x 0^2+x 1^2-x 2^2+x 3^2-x 4^2-x 5^2)) • metric := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [source,poly,metricInvariantCoefficients,monomialPair,tensorIndex,
      metric,Matrix.diagonal,eta,Fin.sum_univ_succ] <;> (try dsimp) <;> ring

theorem metric_invariant_covariant : Covariant (source metricInvariantCoefficients) := by
  apply (covariance_iff _).mpr
  intro k x
  ext i j
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    norm_num [variation,dpoly,source,poly,metricInvariantCoefficients,monomialPair,tensorIndex,
      field_action_formula,tensorAction,lorentz_formula,lorentzTable,Matrix.mul_apply,
      Matrix.transpose_apply,Fin.sum_univ_succ] <;> (try dsimp) <;> ring

theorem metric_invariant_not_trace_free : ¬ TraceFree (source metricInvariantCoefficients) := by
  intro h
  have hh := h ![1,0,0,0,0,0]
  rw [metric_invariant_formula] at hh
  norm_num [metric,Matrix.diagonal,eta] at hh
  all_goals dsimp at hh
  all_goals norm_num at hh

theorem anisotropic_trace_free : TraceFree (source anisotropicCoefficients) := by
  intro x
  norm_num [source,poly,anisotropicCoefficients,monomialPair,tensorIndex,
    Fin.sum_univ_succ]
  try dsimp
  all_goals ring1

theorem anisotropic_not_covariant : ¬ Covariant (source anisotropicCoefficients) := by
  intro h
  have hh := congrArg (fun T : Tensor => T 0 1)
    ((covariance_iff _).mp h 0 ![1,0,0,0,0,0])
  norm_num [variation,dpoly,source,poly,anisotropicCoefficients,monomialPair,tensorIndex,
    field_action_formula,tensorAction,lorentz_formula,lorentzTable,Matrix.mul_apply,
    Matrix.transpose_apply,Fin.sum_univ_succ] at hh
  all_goals dsimp at hh
  all_goals norm_num at hh

/-- Each of the two geometric requirements excludes an explicit alternative. -/
theorem both_conditions_necessary :
    (∃ S : Local → Tensor, IsQuadraticSource S ∧ Covariant S ∧ ¬ TraceFree S) ∧
    (∃ S : Local → Tensor, IsQuadraticSource S ∧ TraceFree S ∧ ¬ Covariant S) :=
  ⟨⟨source metricInvariantCoefficients,⟨metricInvariantCoefficients,rfl⟩,
      metric_invariant_covariant,metric_invariant_not_trace_free⟩,
    ⟨source anisotropicCoefficients,⟨anisotropicCoefficients,rfl⟩,
      anisotropic_trace_free,anisotropic_not_covariant⟩⟩

#print axioms metric_invariant_formula
#print axioms metric_invariant_covariant
#print axioms metric_invariant_not_trace_free
#print axioms anisotropic_trace_free
#print axioms anisotropic_not_covariant
#print axioms both_conditions_necessary
end
end PDTQuadraticSource
