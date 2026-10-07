module
public import ScopeAudit

@[expose] public section
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
namespace PDTHodgeReference
noncomputable section
open PDTPfaffianCubic PDTPfaffianBridge PDTGeometricTransport
open PDTExteriorAction PDTExteriorMetric PDTFiniteHodge PDTStabilizerTests
open GravityScreening.ResponseClosureGeometry GravityScreening.ResponseClosureCertificate
open scoped Matrix

def sampleRow : I → I := ![9,6,5,5,5,2,1,1,1,0,0,0,0,0,0]
def sampleCol : I → I := ![14,14,14,13,12,14,14,13,12,14,13,12,11,10,9]
def sampleSign : I → ℤ := ![-1,1,1,-1,1,-1,-1,1,-1,1,-1,1,1,-1,1]

private theorem integral_samples : ∀ i j : I,
    sampleSign i*jordan j (sampleRow i) (sampleCol i) = if i=j then 1 else 0 := by
  decide +kernel

/-- Read fifteen selected entries of the actual raised Hessian. -/
def decode (A : M15) (i : I) : ℝ :=
  (sampleSign i : ℝ)*A (sampleRow i) (sampleCol i)

theorem decode_raised (x : I → ℝ) : decode (raisedHessian ℝ x)=x := by
  rw [raisedHessian_expansion]
  ext i
  simp only [decode,Matrix.sum_apply,Matrix.smul_apply,
    smul_eq_mul,actual_jordan]
  rw [Finset.mul_sum]
  have hi (j : I) : (sampleSign i : ℝ)*(jordan j (sampleRow i) (sampleCol i) : ℝ)=
      if i=j then 1 else 0 := by
    exact_mod_cast integral_samples i j
  calc
    _ = ∑ j : I, x j*(if i=j then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [← hi j]
      ring
    _ = x i := by simp

theorem raised_injective : Function.Injective (raisedHessian ℝ) :=
  Function.LeftInverse.injective decode_raised

theorem moving_injective : Function.Injective movingHodge := by
  intro x y h
  apply raised_injective
  exact neg_injective h

def reference : I → ℝ := Pi.single 14 1

/-- Among actual metric/cubic symmetries, fixing Hodge is exactly fixing its reference. -/
theorem fixed_iff (T : M15)
    (hm : T.transpose*bivectorMetric*T=bivectorMetric)
    (hc : ∀ x, PDTCubicPolarization.cubic (T *ᵥ x)=PDTCubicPolarization.cubic x) :
    T*PDTHodgeConnection.H*reverse T=PDTHodgeConnection.H ↔
      T *ᵥ reference=reference := by
  have ht : movingHodge (T *ᵥ reference)=T*PDTHodgeConnection.H*reverse T := by
    rw [← initial_hodge]
    change -raisedHessian ℝ (T *ᵥ reference)=T*(-raisedHessian ℝ reference)*reverse T
    rw [finite_covariance T hm hc,Matrix.mul_neg,Matrix.neg_mul]
  have hr : movingHodge reference=PDTHodgeConnection.H := initial_hodge
  rw [← ht,← hr]
  exact moving_injective.eq_iff

theorem commutes_iff (T : M15)
    (hm : T.transpose*bivectorMetric*T=bivectorMetric)
    (hc : ∀ x, PDTCubicPolarization.cubic (T *ᵥ x)=PDTCubicPolarization.cubic x) :
    T*PDTHodgeConnection.H=PDTHodgeConnection.H*T ↔ T *ᵥ reference=reference := by
  rw [← fixed_iff T hm hc]
  constructor
  · intro h
    rw [h,Matrix.mul_assoc,reverse_right T hm,Matrix.mul_one]
  · intro h
    have hh := congrArg (fun A : M15 => A*T) h
    simpa only [Matrix.mul_assoc,reverse_left T hm,Matrix.mul_one] using hh

#print axioms decode_raised
#print axioms raised_injective
#print axioms moving_injective
#print axioms fixed_iff
#print axioms commutes_iff
end
end PDTHodgeReference
