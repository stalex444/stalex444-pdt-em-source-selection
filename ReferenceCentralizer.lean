module
public import FixedHodgeSource

@[expose] public section
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
namespace PDTReferenceCentralizer
noncomputable section
open PDTPfaffianCubic PDTPfaffianBridge PDTHessianCovariance PDTCubicInvariance
open PDTStabilizerTests PDTJointStabilizer PDTHodgeReference PDTGeometricTransport
open GravityScreening.ResponseClosureGeometry
open scoped Matrix

theorem raised_zero : raisedHessian ℝ (0 : I → ℝ)=0 := by
  rw [← jordanMap_eq,map_zero]

/-- Infinitesimal fixed Hodge is exactly annihilation of the supplied reference. -/
theorem commutes_iff_annihilates (A : Mat) (hm : MetricSkew A) (hc : CubicInvariant A) :
    A*PDTHodgeConnection.H=PDTHodgeConnection.H*A ↔ A *ᵥ reference=0 := by
  have hcov := joint_hessian_covariance A hm hc reference
  have hH : PDTHodgeConnection.H= -raisedHessian ℝ reference := initial_hodge.symm
  rw [hH,Matrix.mul_neg,Matrix.neg_mul,neg_inj]
  rw [← sub_eq_zero, hcov,← raised_zero]
  exact raised_injective.eq_iff

def NoMixing (w : I → ℝ) : Prop :=
  w 3=0 ∧ w 4=0 ∧ w 7=0 ∧ w 8=0 ∧ w 10=0 ∧ w 11=0 ∧ w 12=0 ∧ w 13=0

private def lastColumn (i p : I) : ℤ :=
  if (i=3 ∧ p=4) ∨ (i=4 ∧ p=3) ∨ (i=7 ∧ p=8) ∨ (i=8 ∧ p=7) ∨
    (i=10 ∧ p=11) ∨ (i=11 ∧ p=10) ∨ (i=12 ∧ p=13) ∨ (i=13 ∧ p=12)
  then 1 else 0

private theorem column_certificate : ∀ i p : I, geometricAdjoint p i 14=lastColumn i p := by
  decide +kernel

theorem reference_action (w : I → ℝ) : connection ℝ w *ᵥ reference=
    ![0,0,0,w 4,w 3,0,0,w 8,w 7,0,w 11,w 10,w 13,w 12,0] := by
  rw [reference,Matrix.mulVec_single_one]
  have he (i p : I) : generator ℝ p i 14=(lastColumn i p : ℝ) := by
    change (geometricAdjoint p i 14 : ℝ)=(lastColumn i p : ℝ)
    rw [column_certificate]
  ext i
  simp only [Matrix.col_apply,connection,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,he]
  fin_cases i <;> norm_num [lastColumn,Fin.sum_univ_succ]

theorem annihilates_iff_no_mixing (w : I → ℝ) :
    connection ℝ w *ᵥ reference=0 ↔ NoMixing w := by
  rw [reference_action]
  constructor
  · intro h
    have h3 := congrFun h 3
    have h4 := congrFun h 4
    have h7 := congrFun h 7
    have h8 := congrFun h 8
    have h10 := congrFun h 10
    have h11 := congrFun h 11
    have h12 := congrFun h 12
    have h13 := congrFun h 13
    exact ⟨h4,h3,h8,h7,h11,h10,h13,h12⟩
  · rintro ⟨h3,h4,h7,h8,h10,h11,h12,h13⟩
    ext i
    fin_cases i <;> simp [h3,h4,h7,h8,h10,h11,h12,h13]

theorem connection_commutes_iff (w : I → ℝ) :
    connection ℝ w*PDTHodgeConnection.H=PDTHodgeConnection.H*connection ℝ w ↔ NoMixing w := by
  rw [commutes_iff_annihilates _ (connection_metric w) (connection_invariance ℝ w),
    annihilates_iff_no_mixing]

/-- The previous ninety cubic checks remain sufficient with this added reference condition. -/
theorem finite_certificate (A : Mat) (hm : MetricSkew A) (hf : FiniteTests A) :
    A*PDTHodgeConnection.H=PDTHodgeConnection.H*A ↔
      NoMixing (PDTStabilizerRecovery.decode A) := by
  conv_lhs => rw [finite_reconstruction A hm hf]
  exact connection_commutes_iff _

#print axioms raised_zero
#print axioms commutes_iff_annihilates
#print axioms reference_action
#print axioms annihilates_iff_no_mixing
#print axioms connection_commutes_iff
#print axioms finite_certificate
end
end PDTReferenceCentralizer
