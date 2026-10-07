module
public import ResponseBridge
public import BoundaryAction

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! Compose actual gravity-response descent, the existing observer integral,
and the new positive-mode action. Physical inclusive/source assignments remain
visible: none is inferred from generator covariance. -/
namespace PDTBoundaryConnection
noncomputable section
open GravityScreening GravityScreening.HodgeResponseCovariance
open PDTResponseBridge MeasureTheory

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

/-- The determinant used in the original alpha rule now belongs to the
descended response of the calibrated real gravity operator. -/
theorem actual_quotient_determinant : LinearMap.det S = (rho*q)^15 := by
  have hR := (HodgeModeCalibration.real_geometric_hodge_calibrated_determinant
    R ha hh rho q hmode).1
  have hs := descended_response_unique hv R (rho*q) hR S hS
  simp [hs, LinearMap.det_smul, V]

variable [MeasurableSpace ObserverRotationGroup]
variable (μ : Measure ObserverRotationGroup) [IsFiniteMeasure μ] [μ.IsMulLeftInvariant]
variable (hB : μ.real Set.univ = projectiveBoundaryVolume)
include hB

/-- Existing inclusive integration, now with the determinant of the actual
induced response rather than an independently defined scalar vertex. -/
theorem actual_response_observer_integral :
    (∫ _ : ObserverRotationGroup, 1 / LinearMap.det S ∂μ) =
      electromagneticCoupling rho q := by
  rw [actual_quotient_determinant R ha hh rho q hmode hv S hS,
    integral_rotationScalar_eq_mass_mul, hB, projectiveBoundaryVolume_eq_pi_sq]
  simp [electromagneticCoupling, electromagneticExponent, div_eq_mul_inv]

omit [IsFiniteMeasure μ] [μ.IsMulLeftInvariant] in
/-- The effective quadratic stiffness of the inclusive positive-mode action. -/
theorem actual_response_effective_stiffness :
    (LinearMap.det S / (4*Real.pi)) / PDTBoundaryAction.mass μ =
      (rho*q)^15/(4*Real.pi^3) := by
  rw [actual_quotient_determinant R ha hh rho q hmode hv S hS]
  change ((rho*q)^15/(4*Real.pi))/μ.real Set.univ = _
  rw [hB]
  exact PDTBoundaryAction.pdt_stiffness (rho*q)

omit [μ.IsMulLeftInvariant] in
/-- With a fixed source j, the minimizing inclusive amplitude carries
e^2 = 4*pi*alpha_L1. This is a scalar positive-mode result. -/
theorem actual_response_sourced_minimum (hr : 0 < rho*q) (j : ℝ)
    (f : ObserverRotationGroup → ℝ) (hf : Integrable f μ)
    (hf2 : Integrable (fun x => (f x)^2) μ) :
    let d := LinearMap.det S/(4*Real.pi);
    -(PDTBoundaryAction.mass μ)*j^2/(2*d) ≤ PDTBoundaryAction.sourcedEnergy μ d j f ∧
    PDTBoundaryAction.total μ (fun _ => j/d) =
      (4*Real.pi*electromagneticCoupling rho q)*j := by
  try dsimp
  have hdS := actual_quotient_determinant R ha hh rho q hmode hv S hS
  have hd : 0 < LinearMap.det S/(4*Real.pi) := by
    rw [hdS]
    positivity
  constructor
  · exact (PDTBoundaryAction.sourced_minimizer μ
      (LinearMap.det S/(4*Real.pi)) j hd f hf hf2).1
  · rw [PDTBoundaryAction.total_const, hdS]
    change μ.real Set.univ * (j / ((rho*q)^15/(4*Real.pi))) = _
    rw [hB, projectiveBoundaryVolume_eq_pi_sq]
    unfold electromagneticCoupling electromagneticExponent
    field_simp [ne_of_gt hr]

#print axioms actual_quotient_determinant
#print axioms actual_response_observer_integral
#print axioms actual_response_effective_stiffness
#print axioms actual_response_sourced_minimum
end
end PDTBoundaryConnection
