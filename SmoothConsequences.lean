module
public import SmoothSelection

@[expose] public section
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
namespace PDTSmoothSource
noncomputable section
open PDTStressTensor PDTUnrestrictedSourceKernel PDTQuadraticSource PDTConservedSource PDTPolynomialSource
open scoped Matrix ContDiff

theorem smooth_zero_field_selection (S : Local → Tensor) (hr : RegularSource S)
    (hc : Conserved S) (hv : Covariant S) :
    (S 0=0 ↔ TraceFree S) ∧
    (S 0=0 ↔ ∃ d : ℝ, S=fun x => registerStress d (embed x)) :=
  zero_field_and_trace_equivalent S (regular_source_polynomial S hr hc) hc hv

theorem smooth_hodge_invariance (S : Local → Tensor) (hr : RegularSource S)
    (hc : Conserved S) (hv : Covariant S) (x : Local) : S (J *ᵥ x)=S x :=
  polynomial_hodge_invariance S (regular_source_polynomial S hr hc) hc hv x

theorem smooth_source_not_injective (S : Local → Tensor) (hr : RegularSource S)
    (hc : Conserved S) (hv : Covariant S) : ¬ Function.Injective S :=
  polynomial_source_not_injective S (regular_source_polynomial S hr hc) hc hv

theorem full_smooth_conserved_family (A : ConstantCoeff) (b : Local) (d : ℝ) :
    RegularSource (conservedFamily A b d) ∧ Conserved (conservedFamily A b d) :=
  ⟨regular_family A b d,(conserved_family_converse A b d).2⟩

theorem full_smooth_covariant_family (c d : ℝ) : RegularSource (covariantFamily c d) ∧
    Conserved (covariantFamily c d) ∧ Covariant (covariantFamily c d) := by
  refine ⟨?_,(covariant_family_converse c d).2⟩
  rw [covariant_as_conserved]
  exact regular_family _ _ _

/-- A source allowed by C3 regularity and symmetry, tested against actual conservation. -/
def exponentialSource (x : Local) : Tensor := fun i j =>
  if i=0 ∧ j=0 then Real.exp (x 3) else 0

theorem exponential_source_regular : RegularSource exponentialSource := by
  constructor
  · intro x
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  · intro i j
    by_cases h : i=0 ∧ j=0
    · simpa [exponentialSource,h] using
        (show ContDiff ℝ 3 (fun x : Local => Real.exp (x 3)) by fun_prop)
    · simp only [exponentialSource,h,ite_false]
      exact contDiff_const

theorem exponential_source_not_conserved : ¬ Conserved exponentialSource := by
  intro h
  have hh := congrFun (h 0 (testJet 0) (testJet_vacuum 0)) 0
  norm_num [divergence,exponentialSource,testJet,Fin.sum_univ_succ] at hh
  try dsimp at hh
  all_goals norm_num at hh

/-- Covariance still has an independent role even after regularity replaces the degree bound. -/
theorem smooth_covariance_control :
    RegularSource (conservedFamily 0 ![1,0,0,0,0,0] 0) ∧
    Conserved (conservedFamily 0 ![1,0,0,0,0,0] 0) ∧
    ¬ Covariant (conservedFamily 0 ![1,0,0,0,0,0] 0) :=
  ⟨regular_family _ _ _,background_covariance_control.2⟩

theorem smooth_trace_control : RegularSource (covariantFamily 1 0) ∧
    Conserved (covariantFamily 1 0) ∧ Covariant (covariantFamily 1 0) ∧
    ¬ TraceFree (covariantFamily 1 0) :=
  ⟨(full_smooth_covariant_family 1 0).1,constant_trace_control.2⟩

#print axioms smooth_zero_field_selection
#print axioms smooth_hodge_invariance
#print axioms smooth_source_not_injective
#print axioms full_smooth_conserved_family
#print axioms full_smooth_covariant_family
#print axioms exponential_source_regular
#print axioms exponential_source_not_conserved
#print axioms smooth_covariance_control
#print axioms smooth_trace_control
end
end PDTSmoothSource
