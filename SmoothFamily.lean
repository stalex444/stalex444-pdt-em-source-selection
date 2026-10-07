module
public import SmoothCalculus

@[expose] public section
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
namespace PDTSmoothSource
noncomputable section
open PDTStressTensor PDTUnrestrictedSourceKernel PDTQuadraticSource PDTConservedSource PDTPolynomialSource
open scoped Matrix ContDiff

theorem family_contDiff (A : ConstantCoeff) (b : Local) (d : ℝ) (i j : Fin 4) :
    ContDiff ℝ 3 (fun x => conservedFamily A b d x i j) := by
  simp only [conserved_family_polynomial,polynomial,Matrix.add_apply,constant,linear,source,poly]
  fun_prop

theorem maxwell_variation (d : ℝ) (x y : Local) :
    variation (d • maxwellCoefficients) x y=
      PDTStressBalance.firstVariation d (embed x) (embed y) := by
  ext i j
  have h := source_hasDerivAt (d • maxwellCoefficients) x y i j
  have he : (fun t : ℝ => source (d • maxwellCoefficients) (x+t • y) i j)=
      (fun t => registerStress d (embed x+t • embed y) i j) := by
    funext t
    rw [scaled_maxwell_original,embed_affine]
  rw [he] at h
  exact h.unique (PDTStressBalance.firstVariation_hasDerivAt d (embed x) (embed y) i j)

set_option linter.unusedTactic false in
theorem cross_coefficients_affine (b x : Local) (d : ℝ) :
    crossCoefficients (b+d • x)=crossCoefficients b+d • crossCoefficients x := by
  ext t a
  fin_cases t <;> fin_cases a <;> norm_num [crossCoefficients] <;> (try dsimp) <;> ring

theorem linear_coefficients_add (l m : LinearCoeff) (y : Local) :
    linear (l+m) y=linear l y+linear m y := by
  ext i j
  simp [linear,add_mul,Finset.sum_add_distrib]

theorem linear_coefficients_smul (d : ℝ) (l : LinearCoeff) (y : Local) :
    linear (d • l) y=d • linear l y := by
  ext i j
  simp [linear,Finset.mul_sum,mul_assoc]

theorem linear_unit (l : LinearCoeff) (a : Fin 6) (i j : Fin 4) :
    linear l (unit a) i j=l (tensorIndex i j) a := by
  simp [linear,unit,Pi.single_apply]

theorem family_variation (b x y : Local) (d : ℝ) :
    linear (crossCoefficients b) y+variation (d • maxwellCoefficients) x y=
      linear (crossCoefficients (b+d • x)) y := by
  rw [cross_coefficients_affine,linear_coefficients_add,linear_coefficients_smul,maxwell_variation]
  congr 1
  rw [cross_original_variation]
  ext i j
  simp [PDTStressBalance.firstVariation]

theorem family_partial (A : ConstantCoeff) (b : Local) (d : ℝ)
    (x : Local) (a : Fin 6) (i j : Fin 4) :
    pd a (fun z => conservedFamily A b d z i j) x=
      crossCoefficients (b+d • x) (tensorIndex i j) a := by
  have hd := directional_deriv (fun z => conservedFamily A b d z i j)
    ((family_contDiff A b d i j).differentiable (by norm_num)) x (unit a)
  have he : (fun t : ℝ => conservedFamily A b d (x+t • unit a) i j)=
      (fun t => polynomial A (crossCoefficients b) (d • maxwellCoefficients) (x+t • unit a) i j) := by
    rw [conserved_family_polynomial]
  rw [he,(polynomial_hasDerivAt A (crossCoefficients b) (d • maxwellCoefficients) x (unit a) i j).deriv] at hd
  have hv := congrFun (congrFun (family_variation b x (unit a) d) i) j
  rw [linear_unit] at hv
  have hh : (∑ k, pd k (fun z => conservedFamily A b d z i j) x*unit a k)=
      pd a (fun z => conservedFamily A b d z i j) x := by simp [unit,Pi.single_apply]
  rw [hh] at hd
  exact hd.symm.trans hv

#print axioms family_contDiff
#print axioms maxwell_variation
#print axioms cross_coefficients_affine
#print axioms linear_coefficients_add
#print axioms linear_coefficients_smul
#print axioms linear_unit
#print axioms family_variation
#print axioms family_partial
end
end PDTSmoothSource
