module
public import BackgroundRigidity
public import SmoothFamily

@[expose] public section
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
namespace PDTSmoothSource
noncomputable section
open PDTStressTensor PDTUnrestrictedSourceKernel PDTQuadraticSource PDTConservedSource PDTPolynomialSource
open scoped Matrix ContDiff

theorem tensor_pair_index (t : Fin 10) : tensorIndex (tensorPair t).1 (tensorPair t).2=t := by
  fin_cases t <;> rfl

theorem tensor_entry_recovery (T : Tensor) (h : T.transpose=T) (i j : Fin 4) :
    T (tensorPair (tensorIndex i j)).1 (tensorPair (tensorIndex i j)).2=T i j := by
  have hh (a b : Fin 4) : T b a=T a b := congrFun (congrFun h a) b
  fin_cases i <;> fin_cases j <;> first | rfl | exact hh _ _

/-- Conservation forces the arbitrary C3 source into the banked polynomial family. -/
theorem smooth_assembled_family (f : Components) (hf : ∀ t, ContDiff ℝ 3 (f t))
    (hc : Conserved (assembled f)) : ∃ A b d, assembled f=conservedFamily A b d := by
  let A : ConstantCoeff := fun t => f t 0
  let b : Local := fun j => bg f j 0
  let d : ℝ := pd 0 (bg f 0) 0
  have hbg := scalar_jacobian_affine (bg f) (background_contDiff f hf)
    (background_derivative_scalar f hf hc)
  have hgrad (x : Local) (t : Fin 10) (a : Fin 6) :
      pd a (f t) x=crossCoefficients (b+d • x) t a := by
    have hh := congrFun (congrFun (conserved_gradient f
      (fun t => (hf t).differentiable (by norm_num)) hc x) t) a
    have he : (fun j => bg f j x)=b+d • x := by
      funext j
      change bg f j x=bg f j 0+pd 0 (bg f 0) 0*x j
      rw [hbg]
      exact add_comm _ _
    exact hh.trans (congrArg (fun v => crossCoefficients v t a) he)
  have hentry (t : Fin 10) (x : Local) :
      f t x=conservedFamily A b d x (tensorPair t).1 (tensorPair t).2 := by
    let g : Local → ℝ := fun z => conservedFamily A b d z (tensorPair t).1 (tensorPair t).2
    have hg : Differentiable ℝ g := (family_contDiff A b d _ _).differentiable (by norm_num)
    have hz : ∀ a, pd a ((f t)-g)=0 := by
      intro a
      funext z
      unfold pd
      rw [fderiv_sub ((hf t).differentiable (by norm_num) z) (hg z)]
      change pd a (f t) z-pd a g z=0
      rw [hgrad,family_partial,tensor_pair_index,sub_self]
    have hh := partials_zero_constant ((f t)-g) ((hf t).differentiable (by norm_num) |>.sub hg) hz x
    change f t x-g x=f t 0-g 0 at hh
    have hg0 : g 0=f t 0 := by
      simp only [g,conserved_family_at_zero,constant,tensor_pair_index,A]
    rw [hg0,sub_self] at hh
    exact sub_eq_zero.mp hh
  refine ⟨A,b,d,?_⟩
  funext x
  ext i j
  change f (tensorIndex i j) x=conservedFamily A b d x i j
  rw [hentry]
  apply tensor_entry_recovery
  rw [conserved_family_polynomial]
  exact polynomial_symmetric _ _ _ _

/-- Symmetry and three continuous derivatives, with no degree or polynomial assumption. -/
def RegularSource (S : Local → Tensor) : Prop :=
  (∀ x, (S x).transpose=S x) ∧ ∀ i j, ContDiff ℝ 3 (fun x => S x i j)

theorem regular_source_polynomial (S : Local → Tensor) (hr : RegularSource S)
    (hc : Conserved S) : IsPolynomialSource S := by
  let f : Components := fun t x => S x (tensorPair t).1 (tensorPair t).2
  have he : assembled f=S := by
    funext x
    ext i j
    exact tensor_entry_recovery (S x) (hr.1 x) i j
  have hf : ∀ t, ContDiff ℝ 3 (f t) := fun t => hr.2 _ _
  obtain ⟨A,b,d,hs⟩ := smooth_assembled_family f hf (he ▸ hc)
  rw [← he,hs]
  exact (conserved_family_converse A b d).1

theorem regular_family (A : ConstantCoeff) (b : Local) (d : ℝ) :
    RegularSource (conservedFamily A b d) := by
  refine ⟨?_,family_contDiff A b d⟩
  intro x
  rw [conserved_family_polynomial]
  exact polynomial_symmetric _ _ _ _

theorem smooth_conserved_classification (S : Local → Tensor) (hr : RegularSource S) :
    Conserved S ↔ ∃ A b d, S=conservedFamily A b d := by
  constructor
  · intro hc
    exact (conserved_polynomial_classification S (regular_source_polynomial S hr hc)).mp hc
  · rintro ⟨A,b,d,rfl⟩
    exact (conserved_family_converse A b d).2

theorem smooth_conserved_uniqueness (S : Local → Tensor) (hr : RegularSource S)
    (hc : Conserved S) : ∃! p : ConstantCoeff × Local × ℝ,
      S=conservedFamily p.1 p.2.1 p.2.2 :=
  conserved_polynomial_uniqueness S (regular_source_polynomial S hr hc) hc

theorem smooth_covariant_classification (S : Local → Tensor) (hr : RegularSource S) :
    Conserved S ∧ Covariant S ↔ ∃ c d : ℝ, S=covariantFamily c d := by
  constructor
  · intro h
    exact (covariant_conserved_polynomial_classification S
      (regular_source_polynomial S hr h.1)).mp h
  · rintro ⟨c,d,rfl⟩
    exact (covariant_family_converse c d).2

theorem smooth_covariant_uniqueness (S : Local → Tensor) (hr : RegularSource S)
    (hc : Conserved S) (hv : Covariant S) : ∃! p : ℝ × ℝ, S=covariantFamily p.1 p.2 :=
  covariant_polynomial_uniqueness S (regular_source_polynomial S hr hc) hc hv

#print axioms tensor_pair_index
#print axioms tensor_entry_recovery
#print axioms smooth_assembled_family
#print axioms regular_source_polynomial
#print axioms regular_family
#print axioms smooth_conserved_classification
#print axioms smooth_conserved_uniqueness
#print axioms smooth_covariant_classification
#print axioms smooth_covariant_uniqueness
end
end PDTSmoothSource
