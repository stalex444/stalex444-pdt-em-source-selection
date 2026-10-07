module
public import FinitePfaffian
public import ExteriorMetric
public import CubicPolarization

@[expose] public section
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
namespace PDTFiniteHodge
noncomputable section
open PDTExteriorAction PDTExteriorMetric PDTCubicPolarization
open PDTPfaffianCubic PDTPfaffianBridge PDTStabilizerTests PDTGeometricTransport
open scoped Matrix

theorem polarization_transport (T : M15) (hc : ∀ x, cubic (T *ᵥ x)=cubic x)
    (x u v : I → ℝ) : polar (T *ᵥ x) (T *ᵥ u) (T *ᵥ v)=polar x u v := by
  simp only [polar,← Matrix.mulVec_add,hc]

theorem hessian_congruence (T : M15) (hc : ∀ x, cubic (T *ᵥ x)=cubic x)
    (x : I → ℝ) : T.transpose*hessian ℝ (T *ᵥ x)*T=hessian ℝ x := by
  have hb (u v : I → ℝ) :
      dotProduct u ((T.transpose*hessian ℝ (T *ᵥ x)*T) *ᵥ v)=
      dotProduct u (hessian ℝ x *ᵥ v) := by
    rw [← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,
      Matrix.dotProduct_mulVec,Matrix.vecMul_transpose]
    rw [hessian_polarization,hessian_polarization,polarization_transport T hc]
  ext r c
  simpa using hb (Pi.single r 1) (Pi.single c 1)

theorem raised_eq (x : I → ℝ) : raisedHessian ℝ x=bivectorMetric*hessian ℝ x := by
  ext r c
  simp [raisedHessian,bivectorMetric,Matrix.diagonal_mul]

def reverse (T : M15) : M15 := bivectorMetric*T.transpose*bivectorMetric

theorem reverse_left (T : M15) (hm : T.transpose*bivectorMetric*T=bivectorMetric) :
    reverse T*T=1 := by
  calc
    _ = bivectorMetric*(T.transpose*bivectorMetric*T) := by simp only [reverse,Matrix.mul_assoc]
    _ = 1 := by rw [hm,metric_square]

theorem reverse_right (T : M15) (hm : T.transpose*bivectorMetric*T=bivectorMetric) :
    T*reverse T=1 := by
  exact mul_eq_one_comm.mp (reverse_left T hm)

theorem reverse_eq_inverse (T : M15) (hm : T.transpose*bivectorMetric*T=bivectorMetric) :
    reverse T=T⁻¹ := (Matrix.inv_eq_left_inv (reverse_left T hm)).symm

/-- Finite covariance of the actual raised Hessian, with an explicit inverse. -/
theorem finite_covariance (T : M15) (hm : T.transpose*bivectorMetric*T=bivectorMetric)
    (hc : ∀ x, cubic (T *ᵥ x)=cubic x) (x : I → ℝ) :
    raisedHessian ℝ (T *ᵥ x)=T*raisedHessian ℝ x*reverse T := by
  have hh := hessian_congruence T hc x
  have hr : reverse T*raisedHessian ℝ (T *ᵥ x)*T=raisedHessian ℝ x := by
    simp only [raised_eq,reverse,Matrix.mul_assoc]
    calc
      _ = bivectorMetric*(T.transpose*(bivectorMetric*bivectorMetric)*hessian ℝ (T *ᵥ x)*T) := by
        simp only [Matrix.mul_assoc]
      _ = bivectorMetric*hessian ℝ x := by rw [metric_square,Matrix.mul_one,hh]
  calc
    _ = T*(reverse T*raisedHessian ℝ (T *ᵥ x)*T)*reverse T := by
      simp only [← Matrix.mul_assoc,reverse_right T hm,Matrix.one_mul]
      rw [Matrix.mul_assoc,reverse_right T hm,Matrix.mul_one]
    _ = _ := by rw [hr]

/-- All hypotheses here concern the ambient transformation, not assumed register invariance. -/
theorem ambient_covariance (M : M6)
    (hm : M.transpose*ambientMetric*M=ambientMetric) (hd : M.det=1) (x : I → ℝ) :
    raisedHessian ℝ (lift M *ᵥ x)=lift M*raisedHessian ℝ x*reverse (lift M) := by
  apply finite_covariance (lift M) (induced_metric M hm)
  intro y
  exact PDTFinitePfaffian.oriented_value M hd y

theorem ambient_hodge (M : M6)
    (hm : M.transpose*ambientMetric*M=ambientMetric) (hd : M.det=1) (x : I → ℝ) :
    movingHodge (lift M *ᵥ x)=lift M*movingHodge x*reverse (lift M) := by
  simp only [movingHodge,ambient_covariance M hm hd,Matrix.mul_neg,Matrix.neg_mul]

theorem original_hodge_transport (M : M6)
    (hm : M.transpose*ambientMetric*M=ambientMetric) (hd : M.det=1) :
    movingHodge (lift M *ᵥ Pi.single 14 1)=
      lift M*PDTHodgeConnection.H*reverse (lift M) := by
  rw [ambient_hodge M hm hd,initial_hodge]

#print axioms polarization_transport
#print axioms hessian_congruence
#print axioms raised_eq
#print axioms reverse_left
#print axioms reverse_eq_inverse
#print axioms reverse_right
#print axioms finite_covariance
#print axioms ambient_covariance
#print axioms ambient_hodge
#print axioms original_hodge_transport
end
end PDTFiniteHodge
