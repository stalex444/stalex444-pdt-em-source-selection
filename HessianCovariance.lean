module
public import CubicInvariance
public import CovarianceCertificate

@[expose] public section
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
namespace PDTHessianCovariance
noncomputable section
open PDTPfaffianCubic PDTPfaffianBridge PDTCubicInvariance PDTCovarianceCertificate
open GravityScreening.ResponseClosureCertificate GravityScreening.ResponseClosureGeometry
open scoped Matrix
variable (R : Type*) [CommRing R]

def jordanMap : (I → R) →ₗ[R] Matrix I I R where
  toFun x := ∑ p : I, x p • cast R (jordan p)
  map_add' x y := by simp [add_smul,Finset.sum_add_distrib]
  map_smul' a x := by simp [smul_smul,Finset.smul_sum]

theorem jordanMap_eq (x : I → R) : jordanMap R x=raisedHessian R x := by
  rw [raisedHessian_expansion]
  change (∑ p : I, x p • cast R (jordan p))= _
  apply Finset.sum_congr rfl
  intro p _
  rw [actual_jordan]
  rfl

theorem covariance_basis (p j : I) :
    generator R p * cast R (jordan j)-cast R (jordan j)*generator R p=
      jordanMap R (generator R p *ᵥ Pi.single j 1) := by
  simp only [generator,← certificate_adjoint]
  rw [← map_mul,← map_mul,← map_sub]
  change cast R (comm (adj p) (jordan j))= _
  rw [integral_covariance]
  ext r c
  change (((∑ k : I, adj p k j • jordan k) r c : ℤ) : R)= _
  simp only [Matrix.sum_apply,Matrix.smul_apply]
  simp [PDTCubicInvariance.cast,jordanMap,Matrix.sum_apply,
    Matrix.smul_apply]

theorem jordan_covariance (p : I) (x : I → R) :
    generator R p*jordanMap R x-jordanMap R x*generator R p=
      jordanMap R (generator R p *ᵥ x) := by
  have hx : x=∑ j : I, x j • (Pi.single j 1 : I → R) := by
    ext i
    simp [Pi.single_apply]
  have hg : generator R p *ᵥ x=
      ∑ j : I, x j • (generator R p *ᵥ Pi.single j 1) := by
    conv_lhs => rw [hx]
    simp [Matrix.mulVec_sum,Matrix.mulVec_smul]
  rw [hg,map_sum]
  simp only [map_smul]
  change generator R p*(∑ j : I, x j • cast R (jordan j))-
    (∑ j : I, x j • cast R (jordan j))*generator R p= _
  rw [Matrix.mul_sum,Matrix.sum_mul,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [Matrix.mul_smul,Matrix.smul_mul,← smul_sub,covariance_basis]

theorem hessian_covariance (p : I) (x : I → R) :
    generator R p*raisedHessian R x-raisedHessian R x*generator R p=
      raisedHessian R (generator R p *ᵥ x) := by
  simp only [← jordanMap_eq]
  exact jordan_covariance R p x

def connection (w : I → R) : Matrix I I R := ∑ p : I, w p • generator R p

theorem connection_action (w x : I → R) :
    connection R w *ᵥ x=∑ p : I, w p • (generator R p *ᵥ x) := by
  simp [connection,Matrix.sum_mulVec,Matrix.smul_mulVec]

theorem connection_invariance (w x : I → R) :
    directional R x (connection R w *ᵥ x)=0 := by
  rw [connection_action]
  change directionalMap R x (∑ p : I, w p • (generator R p *ᵥ x))=0
  rw [map_sum]
  simp only [map_smul]
  change (∑ p : I, w p • directional R x (generator R p *ᵥ x))=0
  simp only [generator_invariance,smul_zero,Finset.sum_const_zero]

theorem connection_covariance (w x : I → R) :
    connection R w*raisedHessian R x-raisedHessian R x*connection R w=
      raisedHessian R (connection R w *ᵥ x) := by
  simp only [← jordanMap_eq,connection_action,map_sum,map_smul]
  change (∑ p : I, w p • generator R p)*jordanMap R x-
    jordanMap R x*(∑ p : I, w p • generator R p)= _
  rw [Matrix.sum_mul,Matrix.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p _
  rw [Matrix.smul_mul,Matrix.mul_smul,← smul_sub,jordan_covariance]

#print axioms jordanMap_eq
#print axioms covariance_basis
#print axioms jordan_covariance
#print axioms hessian_covariance
#print axioms connection_action
#print axioms connection_invariance
#print axioms connection_covariance
end
end PDTHessianCovariance
