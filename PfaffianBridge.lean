module
public import PfaffianCubic
public import ResponseBridge
public import HodgeConnection
public import StressTensor
public import GravityScreening.HodgeLieGeneration
@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
namespace PDTPfaffianBridge
open PDTPfaffianCubic GravityScreening
open GravityScreening.ResponseClosureCertificate
open GravityScreening.ResponseClosureGeometry
open scoped Matrix

/-- All 3375 entries are checked against the independent product-rule formula. -/
theorem integral_jordan : ∀ p r c : Fin 15,
    q r * computedHessian ℤ (Pi.single p 1) r c=jordan p r c := by
  decide +kernel

noncomputable section
variable (R : Type*) [CommRing R]

/-- Raise the first Hessian index with the actual self-inverse bivector metric. -/
def raisedHessian (x : I → R) : Matrix I I R := fun r c =>
  (q r : R)*hessian R x r c

/-- Identity over every commutative ring, without division by two or six. -/
theorem actual_jordan (p : I) : raisedHessian R (Pi.single p 1)=
    fun r c => (jordan p r c : R) := by
  ext r c
  simp only [raisedHessian,hessian_formula]
  have hc := computedHessian_cast R (Pi.single p 1) r c
  have hs : (fun i => ((Pi.single p 1 : I → ℤ) i : R))=(Pi.single p 1 : I → R) := by
    ext i
    simp [Pi.single_apply]
  rw [hs] at hc
  rw [hc,← Int.cast_mul,integral_jordan]

theorem actual_hodge : -raisedHessian R (Pi.single 14 1)=
    fun r c => (hodgeComplement r c : R) := by
  rw [actual_jordan]
  ext r c
  rw [← certificate_hodge]
  simp only [hodge_eq_neg_jordan14,Matrix.neg_apply,Int.cast_neg]

theorem raisedHessian_expansion (x : I → R) :
    raisedHessian R x=∑ p : I, x p • raisedHessian R (Pi.single p 1) := by
  ext r c
  change (q r : R)*hessian R x r c= _
  rw [hessian_basis_expansion R x]
  simp only [raisedHessian,Matrix.sum_apply,
    Matrix.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  ring

section Field
variable (K : Type*) [Field K]
attribute [local instance] LieRing.ofAssociativeRing

theorem jordan_cast (p : I) :
    raisedHessian K (Pi.single p 1)=HodgeLieGeneration.castMatrix K (jordan p) :=
  actual_jordan K p

theorem hodge_cast : -raisedHessian K (Pi.single 14 1)=
    HodgeLieGeneration.castMatrix K hodgeComplement := actual_hodge K

end Field
end
end PDTPfaffianBridge
