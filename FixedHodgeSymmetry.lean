module
public import HodgeReference

@[expose] public section
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
namespace PDTFixedHodgeSymmetry
noncomputable section
open PDTExteriorAction PDTExteriorMetric PDTSignedTransport PDTFiniteHodge
open PDTHodgeReference PDTPfaffianCubic PDTStabilizerTests
open scoped Matrix

/-- Reflection of coordinate 4, in the original complementary 45 plane. -/
def complementReflection : M6 := Matrix.diagonal (fun i => if i=4 then -1 else 1)
def action : M15 := signedLift complementReflection

theorem complement_det : complementReflection.det= -1 := by
  norm_num [complementReflection,Matrix.det_diagonal,Fin.prod_univ_succ]

theorem complement_square : complementReflection*complementReflection=1 := by
  ext i j
  simp only [complementReflection,Matrix.diagonal_mul,Matrix.diagonal_apply,Matrix.one_apply]
  split_ifs <;> norm_num

theorem complement_metric :
    complementReflection.transpose*ambientMetric*complementReflection=ambientMetric := by
  ext i j
  simp only [complementReflection,ambientMetric,Matrix.diagonal_transpose,
    Matrix.mul_diagonal,Matrix.diagonal_apply]
  split_ifs <;> simp_all

theorem action_involution : action*action=1 := by
  rw [action,← signed_mul,complement_square,signed_one]

theorem action_metric : action.transpose*bivectorMetric*action=bivectorMetric :=
  signed_metric complementReflection complement_metric

theorem action_cubic (x : I → ℝ) :
    PDTCubicPolarization.cubic (action *ᵥ x)=PDTCubicPolarization.cubic x :=
  signed_cubic complementReflection complement_metric x

theorem action_reference : action *ᵥ reference=reference := by
  rw [action,signedLift,complement_det,neg_one_smul,Matrix.neg_mulVec]
  unfold reference
  rw [lift_column]
  ext p
  fin_cases p <;>
    norm_num [wedge,complementReflection,ia,ib,Matrix.diagonal_apply,Pi.single_apply] <;>
    simp +decide

theorem action_commutes_hodge : action*PDTHodgeConnection.H=PDTHodgeConnection.H*action :=
  (commutes_iff action action_metric action_cubic).mpr action_reference

theorem action_fixes_hodge : action*PDTHodgeConnection.H*action=PDTHodgeConnection.H := by
  rw [action_commutes_hodge,Matrix.mul_assoc,action_involution,Matrix.mul_one]

theorem action_no_lift : ¬ ∃ M : M6, lift M=action :=
  negative_branch_no_lift complementReflection complement_det

/-- Fixed Hodge still does not force an ordinary exterior lift of a joint symmetry. -/
theorem fixed_hodge_converse_false : ¬ (∀ T : M15,
    T.transpose*bivectorMetric*T=bivectorMetric →
    (∀ x : I → ℝ, PDTCubicPolarization.cubic (T *ᵥ x)=PDTCubicPolarization.cubic x) →
    T*PDTHodgeConnection.H=PDTHodgeConnection.H*T → ∃ M : M6, lift M=T) := by
  intro h
  exact action_no_lift (h action action_metric action_cubic action_commutes_hodge)

#print axioms complement_det
#print axioms complement_square
#print axioms complement_metric
#print axioms action_involution
#print axioms action_metric
#print axioms action_cubic
#print axioms action_reference
#print axioms action_commutes_hodge
#print axioms action_fixes_hodge
#print axioms action_no_lift
#print axioms fixed_hodge_converse_false
end
end PDTFixedHodgeSymmetry
