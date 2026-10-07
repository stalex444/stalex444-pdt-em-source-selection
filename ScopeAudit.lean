module
public import SignedTransport

@[expose] public section
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
namespace PDTFiniteScopeAudit
noncomputable section
open PDTExteriorAction PDTExtraSymmetry PDTGeometricTransport
open PDTPfaffianCubic
open scoped Matrix

/-- The explicit extra candidate reverses the supplied complementary reference. -/
theorem extra_reference : extra *ᵥ Pi.single 14 1= -(Pi.single 14 1 : I → ℝ) := by
  rw [extra,Matrix.neg_mulVec,lift_column]
  congr 1
  ext p
  fin_cases p <;>
    norm_num [wedge,reflection,ia,ib,Matrix.diagonal_apply,Pi.single_apply] <;> simp +decide

theorem extra_not_reference_preserving :
    extra *ᵥ Pi.single 14 1 ≠ (Pi.single 14 1 : I → ℝ) := by
  rw [extra_reference]
  intro h
  have h14 := congrFun h 14
  norm_num at h14

/-- Covariance here sends the fixed Hodge to its negative; it does not fix it. -/
theorem extra_reverses_hodge :
    extra*PDTHodgeConnection.H*extra= -PDTHodgeConnection.H := by
  have h := extra_hodge (Pi.single 14 1)
  rw [extra_reference,reverse_reference,initial_hodge] at h
  exact h.symm

#print axioms extra_reference
#print axioms extra_not_reference_preserving
#print axioms extra_reverses_hodge
end
end PDTFiniteScopeAudit
