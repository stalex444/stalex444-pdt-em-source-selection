module
public import PolynomialConsequences
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
namespace PDTSmoothSource
noncomputable section
open PDTStressTensor PDTUnrestrictedSourceKernel PDTQuadraticSource PDTConservedSource PDTPolynomialSource
open scoped Matrix ContDiff

def unit (a : Fin 6) : Local := Pi.single a 1
def pd (a : Fin 6) (f : Local → ℝ) (x : Local) : ℝ := fderiv ℝ f x (unit a)

theorem vector_expansion (x : Local) : x=∑ a, x a • unit a := by
  ext j
  simp [unit,Finset.sum_apply,Pi.single_apply]

theorem derivative_expansion (f : Local → ℝ) (x y : Local) :
    fderiv ℝ f x y=∑ a, pd a f x*y a := by
  conv_lhs => rw [vector_expansion y]
  simp [pd,map_sum,map_smul,mul_comm]

theorem partial_contDiff {n m : ℕ∞ω} {f : Local → ℝ}
    (h : ContDiff ℝ n f) (hm : m+1≤n) (a : Fin 6) : ContDiff ℝ m (pd a f) :=
  (h.fderiv_right hm).clm_apply contDiff_const

theorem partial_add (a : Fin 6) {f g : Local → ℝ} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) : pd a (f+g)=pd a f+pd a g := by
  funext x
  simp [pd,fderiv_add (hf x) (hg x)]

theorem partial_neg (a : Fin 6) (f : Local → ℝ) : pd a (-f)= -pd a f := by
  funext x
  have hh := congrArg (fun L : Local →L[ℝ] ℝ => L (unit a))
    (fderiv_neg (𝕜 := ℝ) (f := f) (x := x))
  exact hh

theorem partial_zero (a : Fin 6) : pd a (0 : Local → ℝ)=0 := by
  funext x
  simp [pd]

theorem partial_const (a : Fin 6) (c : ℝ) : pd a (fun _ : Local => c)=0 := by
  funext x
  simp [pd]

theorem partial_coordinate (a j : Fin 6) : pd a (fun x : Local => x j)=
    fun _ => if j=a then 1 else 0 := by
  funext x
  have hh : HasFDerivAt (fun y : Local => y j) (ContinuousLinearMap.proj j) x :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 6 => ℝ) j).hasFDerivAt
  unfold pd
  rw [hh.fderiv]
  simp [unit,Pi.single_apply]

theorem partial_mixed (f : Local → ℝ) (hf : ContDiff ℝ 2 f) (a b : Fin 6) :
    pd a (pd b f)=pd b (pd a f) := by
  funext x
  have hd : Differentiable ℝ (fderiv ℝ f) := (hf.fderiv_right (m := 1) (by norm_num)).differentiable_one
  have hh := (hf.contDiffAt (x := x)).isSymmSndFDerivAt (by simp) (unit a) (unit b)
  change (fderiv ℝ (fun y => fderiv ℝ f y (unit b)) x) (unit a)=
    (fderiv ℝ (fun y => fderiv ℝ f y (unit a)) x) (unit b)
  rw [fderiv_clm_apply (hd x) (differentiableAt_const (unit b)),
    fderiv_clm_apply (hd x) (differentiableAt_const (unit a))]
  simpa using hh

theorem partials_zero_constant (f : Local → ℝ) (hf : Differentiable ℝ f)
    (hz : ∀ a, pd a f=0) (x : Local) : f x=f 0 := by
  apply is_const_of_fderiv_eq_zero hf _ x 0
  intro y
  ext v
  rw [derivative_expansion]
  simp [hz]

theorem affine_path_hasDerivAt (x y : Local) :
    HasDerivAt (fun t : ℝ => x+t • y) y 0 := by
  convert! (hasDerivAt_const (0 : ℝ) x).add ((hasDerivAt_id (0 : ℝ)).smul_const y) using 1
  simp

theorem directional_deriv (f : Local → ℝ) (hf : Differentiable ℝ f) (x y : Local) :
    deriv (fun t : ℝ => f (x+t • y)) 0=∑ a,pd a f x*y a := by
  have hh : HasFDerivAt f (fderiv ℝ f x) (x+(0 : ℝ) • y) := by
    simpa only [zero_smul,add_zero] using (hf x).hasFDerivAt
  rw [← derivative_expansion]
  exact (hh.comp_hasDerivAt 0 (affine_path_hasDerivAt x y)).deriv

#print axioms vector_expansion
#print axioms derivative_expansion
#print axioms partial_contDiff
#print axioms partial_add
#print axioms partial_neg
#print axioms partial_zero
#print axioms partial_const
#print axioms partial_coordinate
#print axioms partial_mixed
#print axioms partials_zero_constant
#print axioms affine_path_hasDerivAt
#print axioms directional_deriv
end
end PDTSmoothSource
