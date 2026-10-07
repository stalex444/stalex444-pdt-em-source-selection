module
public import DifferentiableSourceful

@[expose] public section
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
namespace PDTSourcefulSelection
noncomputable section
open PDTStressTensor PDTUnrestrictedSourceKernel PDTQuadraticSource PDTConservedSource PDTPolynomialSource PDTSmoothSource PDTStressBalance
open PDTEinsteinStressSource PDTResponseBridge
open GravityScreening GravityScreening.HodgeResponseCovariance
open scoped Matrix

/-- Lower both tensor indices and place time first, as in the banked local
Einstein theorem. This is a convention change, not another response choice. -/
def toGravity (S : Local → Tensor) (x : Local) : Tensor := fun i j =>
  eta (timeFirstIndex i)*eta (timeFirstIndex j)*S x (timeFirstIndex i) (timeFirstIndex j)

theorem selected_gravitational_source (k : ℝ) (S : Local → Tensor)
    (hs : DifferentiableSource S) (he : ExchangeLaw k S) (h0 : S 0=0) (x : Local) :
    toGravity S x=gravitationalStress k (embed x) := by
  rw [differentiable_normalized_selection k S hs he h0]
  rfl

variable (R : G →ₗ[ℝ] G)
variable (ha : ∀ p x, R ⁅adjointGenerator ℝ p, x⁆ = ⁅adjointGenerator ℝ p, R x⁆)
variable (hh : ∀ x, R ⁅hodgeGenerator ℝ, x⁆ = ⁅hodgeGenerator ℝ, R x⁆)
variable (rho q : ℝ)
variable (hmode : HodgeModeCalibration.complexifyMatrix (R (hodgeGenerator ℝ) : Mat) =
  HodgeModeCalibration.divide (rho : ℂ) (q : ℂ) * HodgeModeCalibration.hodgeMatrix *
  HodgeModeCalibration.flip (rho : ℂ) (q : ℂ))
variable {anchor : V} (hv : anchor ≠ 0)
variable (Qlin : V →ₗ[ℝ] V) (hQ : (ev anchor).comp R = Qlin.comp (ev anchor))
include ha hh hmode hv hQ

/-- The now-selected smooth source enters the already calibrated gravitational
response with the same banked exponent 209. Stiffness calibration is an input;
exchange fixes the source coefficient to that calibration. -/
theorem selected_actual_einstein_source (hr : 0 < rho*q) (screening m : ℝ)
    (S : Local → Tensor) (hs : DifferentiableSource S)
    (he : ExchangeLaw (PDTEinsteinMaxwellInterface.maxwellStiffness
      (LinearMap.det Qlin) projectiveBoundaryVolume) S)
    (h0 : S 0=0) (x : Local) :
    (8*Real.pi*PDTEinsteinMaxwellInterface.newtonCoefficient
      (LinearMap.det R) projectiveBoundaryVolume screening m) • toGravity S x =
      (2*Real.pi^2/(screening*(rho*q)^209*m^2)) • gravitationalStress 1 (embed x) := by
  rw [selected_gravitational_source _ S hs he h0 x]
  exact actual_einstein_source R ha hh rho q hmode hv Qlin hQ hr screening m (embed x)

/-- The banked local null-Clausius closure applies to the selected smooth
source. Ricci symmetry and the null-Clausius premise remain explicit. -/
theorem selected_local_einstein_closure (hr : 0 < rho*q) (screening m : ℝ)
    (S : Local → Tensor) (hs : DifferentiableSource S)
    (he : ExchangeLaw (PDTEinsteinMaxwellInterface.maxwellStiffness
      (LinearMap.det Qlin) projectiveBoundaryVolume) S)
    (h0 : S 0=0) (x : Local) (ricci : Tensor) (hRicci : ricci.transpose=ricci)
    (hnull : ∀ u : Fin 4 → ℝ, localMinkowskiSq u=0 →
      localQuadraticContraction (ricci -
        (8*Real.pi*PDTEinsteinMaxwellInterface.newtonCoefficient
          (LinearMap.det R) projectiveBoundaryVolume screening m) • toGravity S x) u=0) :
    ∃ cosmological : ℝ,
      ricci - (localMinkowskiTrace ricci/2) • localMinkowskiMetric +
        cosmological • localMinkowskiMetric =
          (2*Real.pi^2/(screening*(rho*q)^209*m^2)) • gravitationalStress 1 (embed x) := by
  rw [selected_gravitational_source _ S hs he h0 x] at hnull
  exact actual_null_clausius_einstein_source R ha hh rho q hmode hv Qlin hQ hr
    screening m (embed x) ricci hRicci hnull

#print axioms selected_gravitational_source
#print axioms selected_actual_einstein_source
#print axioms selected_local_einstein_closure
end
end PDTSourcefulSelection
