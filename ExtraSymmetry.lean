module
public import ExteriorKernel

@[expose] public section
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
namespace PDTExtraSymmetry
noncomputable section
open PDTExteriorAction PDTExteriorKernel PDTExteriorMetric PDTFiniteHodge
open PDTPfaffianCubic PDTPfaffianBridge PDTStabilizerTests PDTGeometricTransport
open PDTCubicPolarization PDTFinitePfaffian
open scoped Matrix

def reflection : M6 := Matrix.diagonal (fun i => if i=0 then -1 else 1)
def extra : M15 := -lift reflection

theorem reflection_square : reflection*reflection=1 := by
  ext i j
  simp only [reflection,Matrix.diagonal_mul,Matrix.diagonal_apply,Matrix.one_apply]
  split_ifs <;> norm_num

theorem reflection_metric : reflection.transpose*ambientMetric*reflection=ambientMetric := by
  ext i j
  simp only [reflection,ambientMetric,Matrix.diagonal_transpose,
    Matrix.mul_diagonal,Matrix.diagonal_apply]
  split_ifs <;> simp_all

theorem reflection_det : reflection.det= -1 := by
  norm_num [reflection,Matrix.det_diagonal,Fin.prod_univ_succ]

theorem cubic_neg (x : I → ℝ) : cubic (-x)= -cubic x := by
  simp only [cubic,pfaffian_eval,Pi.neg_apply]
  ring

theorem extra_involution : extra*extra=1 := by
  simp only [extra,neg_mul_neg,← lift_mul,reflection_square,lift_one]

theorem extra_metric : extra.transpose*bivectorMetric*extra=bivectorMetric := by
  simpa only [extra,Matrix.transpose_neg,Matrix.neg_mul,neg_mul_neg] using
    induced_metric reflection reflection_metric

theorem extra_cubic (x : I → ℝ) : cubic (extra *ᵥ x)=cubic x := by
  rw [extra,Matrix.neg_mulVec,cubic_neg]
  change -value (lift reflection *ᵥ x)=value x
  rw [pfaffian_transform,reflection_det]
  ring

/-- The counterexample has no exterior-square realization by any real matrix. -/
theorem extra_no_lift : ¬ ∃ M : M6, lift M=extra := by
  rintro ⟨M,h⟩
  apply no_negative_identity (M*reflection)
  rw [lift_mul,h,extra,Matrix.neg_mul,← lift_mul,reflection_square,lift_one]

/-- This is an explicit negation of the previously proposed finite converse. -/
theorem finite_converse_false : ¬ (∀ T : M15,
    T.transpose*bivectorMetric*T=bivectorMetric →
    (∀ x : I → ℝ, cubic (T *ᵥ x)=cubic x) →
    ∃ M : M6, M.transpose*ambientMetric*M=ambientMetric ∧ M.det=1 ∧ lift M=T) := by
  intro h
  obtain ⟨M,_,_,hM⟩ := h extra extra_metric extra_cubic
  exact extra_no_lift ⟨M,hM⟩

theorem extra_hodge (x : I → ℝ) :
    movingHodge (extra *ᵥ x)=extra*movingHodge x*extra := by
  have hi : reverse extra=extra := by
    exact Matrix.left_inv_eq_left_inv (reverse_left extra extra_metric) extra_involution
  have hc := finite_covariance extra extra_metric extra_cubic x
  simp only [movingHodge,hc,hi,Matrix.mul_neg,Matrix.neg_mul]

#print axioms reflection_square
#print axioms reflection_metric
#print axioms reflection_det
#print axioms cubic_neg
#print axioms extra_involution
#print axioms extra_metric
#print axioms extra_cubic
#print axioms extra_no_lift
#print axioms finite_converse_false
#print axioms extra_hodge
end
end PDTExtraSymmetry
