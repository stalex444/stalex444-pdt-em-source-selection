module
public import SmoothGradient
public import IntegrabilityCertificate

@[expose] public section
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
namespace PDTSmoothSource
noncomputable section
open PDTStressTensor PDTUnrestrictedSourceKernel PDTQuadraticSource PDTConservedSource PDTPolynomialSource
open scoped Matrix

def crossMap (b : Fin 6 → Local → ℝ) : Fin 10 → Fin 6 → Local → ℝ :=
  ![![b 0,b 1,-(b 2),-(b 3),b 4,b 5],![0,b 3,-(b 4),b 1,-(b 2),0],![-(b 3),0,-(b 5),-(b 0),0,-(b 2)],![-(b 4),-(b 5),0,0,-(b 0),-(b 1)],![b 0,-(b 1),b 2,b 3,-(b 4),b 5],![b 1,b 0,0,0,-(b 5),-(b 4)],![b 2,0,b 0,-(b 5),0,-(b 3)],![-(b 0),b 1,b 2,b 3,b 4,-(b 5)],![0,b 2,b 1,b 4,b 3,0],![b 0,b 1,b 2,b 3,b 4,b 5]]

theorem cross_map_value (b : Fin 6 → Local → ℝ) (t : Fin 10) (a : Fin 6) (x : Local) :
    crossMap b t a x=crossCoefficients (fun j => b j x) t a := by
  fin_cases t <;> fin_cases a <;> simp [crossMap,crossCoefficients]

theorem cross_map_partial (b : Fin 6 → Local → ℝ) (t : Fin 10) (a k : Fin 6) (x : Local) :
    pd k (crossMap b t a) x=crossCoefficients (fun j => pd k (b j) x) t a := by
  fin_cases t <;> fin_cases a
  · change pd k (b 0) x=(1)*pd k (b 0) x
    simp [partial_neg]
  · change pd k (b 1) x=(1)*pd k (b 1) x
    simp [partial_neg]
  · change pd k (-(b 2)) x=(-1)*pd k (b 2) x
    simp [partial_neg]
  · change pd k (-(b 3)) x=(-1)*pd k (b 3) x
    simp [partial_neg]
  · change pd k (b 4) x=(1)*pd k (b 4) x
    simp [partial_neg]
  · change pd k (b 5) x=(1)*pd k (b 5) x
    simp [partial_neg]
  · change pd k (0 : Local → ℝ) x=0
    rw [partial_zero]
    rfl
  · change pd k (b 3) x=(1)*pd k (b 3) x
    simp [partial_neg]
  · change pd k (-(b 4)) x=(-1)*pd k (b 4) x
    simp [partial_neg]
  · change pd k (b 1) x=(1)*pd k (b 1) x
    simp [partial_neg]
  · change pd k (-(b 2)) x=(-1)*pd k (b 2) x
    simp [partial_neg]
  · change pd k (0 : Local → ℝ) x=0
    rw [partial_zero]
    rfl
  · change pd k (-(b 3)) x=(-1)*pd k (b 3) x
    simp [partial_neg]
  · change pd k (0 : Local → ℝ) x=0
    rw [partial_zero]
    rfl
  · change pd k (-(b 5)) x=(-1)*pd k (b 5) x
    simp [partial_neg]
  · change pd k (-(b 0)) x=(-1)*pd k (b 0) x
    simp [partial_neg]
  · change pd k (0 : Local → ℝ) x=0
    rw [partial_zero]
    rfl
  · change pd k (-(b 2)) x=(-1)*pd k (b 2) x
    simp [partial_neg]
  · change pd k (-(b 4)) x=(-1)*pd k (b 4) x
    simp [partial_neg]
  · change pd k (-(b 5)) x=(-1)*pd k (b 5) x
    simp [partial_neg]
  · change pd k (0 : Local → ℝ) x=0
    rw [partial_zero]
    rfl
  · change pd k (0 : Local → ℝ) x=0
    rw [partial_zero]
    rfl
  · change pd k (-(b 0)) x=(-1)*pd k (b 0) x
    simp [partial_neg]
  · change pd k (-(b 1)) x=(-1)*pd k (b 1) x
    simp [partial_neg]
  · change pd k (b 0) x=(1)*pd k (b 0) x
    simp [partial_neg]
  · change pd k (-(b 1)) x=(-1)*pd k (b 1) x
    simp [partial_neg]
  · change pd k (b 2) x=(1)*pd k (b 2) x
    simp [partial_neg]
  · change pd k (b 3) x=(1)*pd k (b 3) x
    simp [partial_neg]
  · change pd k (-(b 4)) x=(-1)*pd k (b 4) x
    simp [partial_neg]
  · change pd k (b 5) x=(1)*pd k (b 5) x
    simp [partial_neg]
  · change pd k (b 1) x=(1)*pd k (b 1) x
    simp [partial_neg]
  · change pd k (b 0) x=(1)*pd k (b 0) x
    simp [partial_neg]
  · change pd k (0 : Local → ℝ) x=0
    rw [partial_zero]
    rfl
  · change pd k (0 : Local → ℝ) x=0
    rw [partial_zero]
    rfl
  · change pd k (-(b 5)) x=(-1)*pd k (b 5) x
    simp [partial_neg]
  · change pd k (-(b 4)) x=(-1)*pd k (b 4) x
    simp [partial_neg]
  · change pd k (b 2) x=(1)*pd k (b 2) x
    simp [partial_neg]
  · change pd k (0 : Local → ℝ) x=0
    rw [partial_zero]
    rfl
  · change pd k (b 0) x=(1)*pd k (b 0) x
    simp [partial_neg]
  · change pd k (-(b 5)) x=(-1)*pd k (b 5) x
    simp [partial_neg]
  · change pd k (0 : Local → ℝ) x=0
    rw [partial_zero]
    rfl
  · change pd k (-(b 3)) x=(-1)*pd k (b 3) x
    simp [partial_neg]
  · change pd k (-(b 0)) x=(-1)*pd k (b 0) x
    simp [partial_neg]
  · change pd k (b 1) x=(1)*pd k (b 1) x
    simp [partial_neg]
  · change pd k (b 2) x=(1)*pd k (b 2) x
    simp [partial_neg]
  · change pd k (b 3) x=(1)*pd k (b 3) x
    simp [partial_neg]
  · change pd k (b 4) x=(1)*pd k (b 4) x
    simp [partial_neg]
  · change pd k (-(b 5)) x=(-1)*pd k (b 5) x
    simp [partial_neg]
  · change pd k (0 : Local → ℝ) x=0
    rw [partial_zero]
    rfl
  · change pd k (b 2) x=(1)*pd k (b 2) x
    simp [partial_neg]
  · change pd k (b 1) x=(1)*pd k (b 1) x
    simp [partial_neg]
  · change pd k (b 4) x=(1)*pd k (b 4) x
    simp [partial_neg]
  · change pd k (b 3) x=(1)*pd k (b 3) x
    simp [partial_neg]
  · change pd k (0 : Local → ℝ) x=0
    rw [partial_zero]
    rfl
  · change pd k (b 0) x=(1)*pd k (b 0) x
    simp [partial_neg]
  · change pd k (b 1) x=(1)*pd k (b 1) x
    simp [partial_neg]
  · change pd k (b 2) x=(1)*pd k (b 2) x
    simp [partial_neg]
  · change pd k (b 3) x=(1)*pd k (b 3) x
    simp [partial_neg]
  · change pd k (b 4) x=(1)*pd k (b 4) x
    simp [partial_neg]
  · change pd k (b 5) x=(1)*pd k (b 5) x
    simp [partial_neg]

theorem gradient_cross_map (f : Components) (hf : ∀ t, Differentiable ℝ (f t))
    (hc : Conserved (assembled f)) (t : Fin 10) (a : Fin 6) :
    pd a (f t)=crossMap (bg f) t a := by
  funext x
  rw [cross_map_value]
  exact congrFun (congrFun (conserved_gradient f hf hc x) t) a

/-- Actual second derivatives of the source satisfy the finite compatibility system. -/
theorem background_derivative_scalar (f : Components) (hf : ∀ t, ContDiff ℝ 3 (f t))
    (hc : Conserved (assembled f)) (x : Local) (j k : Fin 6) :
    pd k (bg f j) x=if j=k then pd 0 (bg f 0) x else 0 := by
  apply compatible_scalar (fun j k => pd k (bg f j) x)
  intro t a b
  rw [← cross_map_partial,← cross_map_partial,
    ← gradient_cross_map f (fun t => (hf t).differentiable (by norm_num)) hc,
    ← gradient_cross_map f (fun t => (hf t).differentiable (by norm_num)) hc]
  exact congrFun (partial_mixed (f t) ((hf t).of_le (by norm_num)) b a) x

#print axioms cross_map_value
#print axioms cross_map_partial
#print axioms gradient_cross_map
#print axioms background_derivative_scalar
end
end PDTSmoothSource
