module
public import SmoothCalculus

@[expose] public section
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
namespace PDTSmoothSource
noncomputable section
open PDTStressTensor PDTUnrestrictedSourceKernel PDTQuadraticSource PDTConservedSource PDTPolynomialSource
open scoped Matrix ContDiff

abbrev Components := Fin 10 → Local → ℝ
def assembled (f : Components) (x : Local) : Tensor := constant (fun t => f t x)
def gradient (f : Components) (x : Local) : LinearCoeff := fun t a => pd a (f t) x
def bg (f : Components) (a : Fin 6) (x : Local) : ℝ := background (gradient f x) a

theorem assembled_symmetric (f : Components) (x : Local) :
    (assembled f x).transpose=assembled f x := constant_symmetric _

theorem assembled_divergence (f : Components) (hf : ∀ t, Differentiable ℝ (f t))
    (x : Local) (D : Jet) : divergence (assembled f) x D=linearDivergence (gradient f x) D := by
  funext ν
  unfold divergence linearDivergence
  apply Finset.sum_congr rfl
  intro μ _
  exact directional_deriv (f (tensorIndex μ ν)) (hf _) x (D μ)

/-- Conservation of a general differentiable source constrains its actual gradient. -/
theorem conserved_gradient (f : Components) (hf : ∀ t, Differentiable ℝ (f t))
    (hc : Conserved (assembled f)) (x : Local) :
    gradient f x=crossCoefficients (fun a => bg f a x) := by
  apply linear_recovery
  apply linear_constraints_from_law
  intro D hD
  rw [← assembled_divergence f hf]
  exact hc x D hD

theorem background_contDiff (f : Components) (hf : ∀ t, ContDiff ℝ 3 (f t))
    (a : Fin 6) : ContDiff ℝ 2 (bg f a) := by
  have hh (j : Fin 6) : ContDiff ℝ 2 (pd j (f 0)) := partial_contDiff (hf 0) (by norm_num) j
  fin_cases a
  · exact hh 0
  · exact hh 1
  · exact (hh 2).neg
  · exact (hh 3).neg
  · exact hh 4
  · exact hh 5

#print axioms assembled_symmetric
#print axioms assembled_divergence
#print axioms conserved_gradient
#print axioms background_contDiff
end
end PDTSmoothSource
