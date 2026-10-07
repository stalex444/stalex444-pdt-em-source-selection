module
public import SmoothIntegrability

@[expose] public section
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
namespace PDTSmoothSource
noncomputable section
open PDTStressTensor PDTUnrestrictedSourceKernel PDTQuadraticSource PDTConservedSource PDTPolynomialSource
open scoped Matrix ContDiff

/-- In dimension six a C2 map with scalar Jacobian has constant scalar factor. -/
theorem scalar_jacobian_constant (b : Fin 6 → Local → ℝ)
    (hb : ∀ j, ContDiff ℝ 2 (b j))
    (h : ∀ x j k, pd k (b j) x=if j=k then pd 0 (b 0) x else 0) :
    ∀ x, pd 0 (b 0) x=pd 0 (b 0) 0 := by
  have hd (j : Fin 6) : pd j (b j)=pd 0 (b 0) := by
    funext x
    simpa using h x j j
  have hz (j k : Fin 6) (hne : j≠k) : pd k (b j)=0 := by
    funext x
    simpa only [hne,ite_false,Pi.zero_apply] using h x j k
  apply partials_zero_constant (pd 0 (b 0))
    ((partial_contDiff (hb 0) (m := 1) (by norm_num) 0).differentiable_one)
  intro k
  by_cases hk : k=0
  · subst k
    rw [← hd 1,partial_mixed (b 1) (hb 1),hz 1 0 (by decide),partial_zero]
  · rw [← hd 0,partial_mixed (b 0) (hb 0),hz 0 k (Ne.symm hk),partial_zero]

/-- The six derivative-background functions must be one common affine dilation. -/
theorem scalar_jacobian_affine (b : Fin 6 → Local → ℝ)
    (hb : ∀ j, ContDiff ℝ 2 (b j))
    (h : ∀ x j k, pd k (b j) x=if j=k then pd 0 (b 0) x else 0) :
    ∀ j x, b j x=pd 0 (b 0) 0*x j+b j 0 := by
  let d := pd 0 (b 0) 0
  have hd := scalar_jacobian_constant b hb h
  intro j x
  let g : Local → ℝ := fun z => d*z j+b j 0
  have hg : Differentiable ℝ g := by unfold g; fun_prop
  have hz : ∀ k, pd k ((b j)-g)=0 := by
    intro k
    funext z
    unfold pd
    rw [fderiv_sub ((hb j).differentiable (by norm_num) z) (hg z)]
    change pd k (b j) z - fderiv ℝ g z (unit k)=0
    rw [h,hd]
    have hg' : HasFDerivAt g (d • (ContinuousLinearMap.proj j : Local →L[ℝ] ℝ)) z := by
      convert! ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 6 => ℝ) j).hasFDerivAt.const_mul d).add_const (b j 0) using 1
    rw [hg'.fderiv]
    simp [unit,Pi.single_apply,d]
  have hh := partials_zero_constant ((b j)-g) ((hb j).differentiable (by norm_num) |>.sub hg) hz x
  change b j x-(d*x j+b j 0)=b j 0-(d*(0 : Local) j+b j 0) at hh
  simp only [Pi.zero_apply,mul_zero,zero_add,sub_self] at hh
  exact sub_eq_zero.mp hh

#print axioms scalar_jacobian_constant
#print axioms scalar_jacobian_affine
end
end PDTSmoothSource
