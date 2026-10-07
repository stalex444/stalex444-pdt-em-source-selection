module
public import MovingConnection

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! Connection compatibility of the actual geometric local Hodge.
Only the six local Lorentz generators are used for this connection.
The generated sl15 response algebra is a different object. -/
namespace PDTHodgeConnection
noncomputable section
open GravityScreening GravityScreening.HodgeResponseCovariance PDTResponseBridge
open scoped Matrix

def H : Mat := (hodgeGenerator ℝ : Mat)
def localConnection (w : Fin 15 → ℝ) : Mat :=
  ∑ p ∈ Finset.univ.filter ResponseClosureGeometry.LocalPair,
    w p • (adjointGenerator ℝ p : Mat)

def asContinuous (M : Mat) : V →L[ℝ] V :=
  LinearMap.toContinuousLinearMap (Matrix.mulVecLin M)

/-- Induced action on e_c wedge e_d, calculated directly from the actual
six-dimensional vector generator. This is the product rule on two vectors. -/
def exteriorGenerator (p : Fin 15) : ResponseClosureCertificate.IMat := fun output input =>
  let ab := ResponseClosureGeometry.basisPairs output
  let cd := ResponseClosureGeometry.basisPairs input
  let A := ResponseClosureGeometry.orthogonalGenerator p
  A ab.1 cd.1 * (if ab.2 = cd.2 then 1 else 0) -
    A ab.1 cd.2 * (if ab.2 = cd.1 then 1 else 0) +
    (if ab.1 = cd.1 then 1 else 0) * A ab.2 cd.2 -
    (if ab.1 = cd.2 then 1 else 0) * A ab.2 cd.1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The frozen adjoint representation is exactly the induced bivector action
of its vector generators, on all 3375 integral entries. -/
theorem geometric_is_exterior :
    ∀ p, ResponseClosureGeometry.geometricAdjoint p = exteriorGenerator p := by
  decide +kernel

/-- Therefore the connection used below is the actual induced bivector
connection, not an independently assigned 15-dimensional operator. -/
theorem localConnection_is_induced (w : Fin 15 → ℝ) :
    localConnection w =
      ∑ p ∈ Finset.univ.filter ResponseClosureGeometry.LocalPair,
        w p • HodgeLieGeneration.castMatrix ℝ (exteriorGenerator p) := by
  unfold localConnection
  apply Finset.sum_congr rfl
  intro p _
  change w p • HodgeLieGeneration.castMatrix ℝ
      (ResponseClosureGeometry.geometricAdjoint p) = _
  rw [geometric_is_exterior p]

theorem local_generator_commutes (p : Fin 15)
    (hp : ResponseClosureGeometry.LocalPair p) :
    (adjointGenerator ℝ p : Mat)*H = H*(adjointGenerator ℝ p : Mat) := by
  have hi := ResponseClosureGeometry.hodge_local_equivariance p hp
  have hc := congrArg (HodgeLieGeneration.castMatrix ℝ) hi
  change HodgeLieGeneration.castMatrix ℝ
    (ResponseClosureGeometry.geometricAdjoint p *
        ResponseClosureGeometry.hodgeComplement -
      ResponseClosureGeometry.hodgeComplement *
        ResponseClosureGeometry.geometricAdjoint p) = _ at hc
  rw [map_sub, map_mul, map_mul, map_zero] at hc
  exact sub_eq_zero.mp hc

/-- Any supplied local Lorentz connection commutes with the same Hodge. -/
theorem connection_commutes (w : Fin 15 → ℝ) :
    localConnection w*H = H*localConnection w := by
  classical
  unfold localConnection
  simp only [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Matrix.smul_mul, Matrix.mul_smul,
    local_generator_commutes p (Finset.mem_filter.mp hp).2]

/-- The fixed geometric Hodge acts on an actual differentiable field curve. -/
theorem hodge_hasDerivAt (f : ℝ → V) (t : ℝ) (df : V)
    (hf : HasDerivAt f df t) :
    HasDerivAt (fun s => H *ᵥ f s) (H *ᵥ df) t := by
  have hc := (hasDerivAt_const t (asContinuous H)).clm_apply hf
  simpa [asContinuous] using hc

/-- Hodge duality is parallel for the supplied local Lorentz connection. -/
theorem actual_hodge_parallel (w : Fin 15 → ℝ) (f : ℝ → V)
    (t : ℝ) (df : V) (hf : HasDerivAt f df t) :
    deriv (fun s => H *ᵥ f s) t + localConnection w *ᵥ (H *ᵥ f t) =
      H *ᵥ (df + localConnection w *ᵥ f t) := by
  rw [(hodge_hasDerivAt f t df hf).deriv, Matrix.mulVec_add,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, connection_commutes]

/-- Curvature components for supplied connection and derivative coefficients.
The derivative coefficients may be those of a smooth connection; no spacetime
metric, torsion condition, or Einstein equation is selected by this definition. -/
def curvature (wμ wν dμwν dνwμ : Fin 15 → ℝ) : Mat :=
  localConnection dμwν - localConnection dνwμ +
    localConnection wμ*localConnection wν -
      localConnection wν*localConnection wμ

theorem curvature_commutes (wμ wν dμwν dνwμ : Fin 15 → ℝ) :
    curvature wμ wν dμwν dνwμ*H = H*curvature wμ wν dμwν dνwμ := by
  have hc (w : Fin 15 → ℝ) : Commute (localConnection w) H := connection_commutes w
  exact (((hc dμwν).sub_left (hc dνwμ)).add_left
    ((hc wμ).mul_left (hc wν))).sub_left ((hc wν).mul_left (hc wμ))

variable (R : G →ₗ[ℝ] G)
variable (ha : ∀ p x, R ⁅adjointGenerator ℝ p, x⁆ = ⁅adjointGenerator ℝ p, R x⁆)
variable (hh : ∀ x, R ⁅hodgeGenerator ℝ, x⁆ = ⁅hodgeGenerator ℝ, R x⁆)
variable (rho q : ℝ)
variable (hmode : HodgeModeCalibration.complexifyMatrix (R (hodgeGenerator ℝ) : Mat) =
  HodgeModeCalibration.divide (rho : ℂ) (q : ℂ) * HodgeModeCalibration.hodgeMatrix *
  HodgeModeCalibration.flip (rho : ℂ) (q : ℂ))
variable {v : V} (hv : v ≠ 0)
variable (S : V →ₗ[ℝ] V) (hS : (ev v).comp R = S.comp (ev v))
include ha hh hmode hv hS

/-- The actual calibrated quotient response is parallel for this connection.
The original constant r=rho*Q is carried through the derivative. -/
theorem actual_response_parallel (w : Fin 15 → ℝ) (f : ℝ → V)
    (t : ℝ) (df : V) (hf : HasDerivAt f df t) :
    deriv (fun s => S (f s)) t + localConnection w *ᵥ S (f t) =
      S (df + localConnection w *ᵥ f t) := by
  have hR := (HodgeModeCalibration.real_geometric_hodge_calibrated_determinant
    R ha hh rho q hmode).1
  have hs := descended_response_unique hv R (rho*q) hR S hS
  rw [hs]
  change deriv (fun s => (rho*q) • f s) t +
    asContinuous (localConnection w) ((rho*q) • f t) =
      (rho*q) • (df + asContinuous (localConnection w) (f t))
  exact PDTMovingConnection.constant_response_parallel
    (rho*q) (asContinuous (localConnection w)) f t df hf

#print axioms local_generator_commutes
#print axioms geometric_is_exterior
#print axioms localConnection_is_induced
#print axioms connection_commutes
#print axioms hodge_hasDerivAt
#print axioms actual_hodge_parallel
#print axioms curvature_commutes
#print axioms actual_response_parallel
end
end PDTHodgeConnection
