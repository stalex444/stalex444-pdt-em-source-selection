module
public import MaxwellHodge

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! The gauge/source symbol and the physical polarization field are composed
with the same calibrated response used in the earlier gravity/EM bridge.
The determinant-to-kinetic-coefficient and inclusive measure assignments remain
explicit; gauge invariance alone does not choose their normalization. -/
namespace PDTMaxwellResponse
noncomputable section
open PDTMaxwellSymbol PDTMaxwellHodge MeasureTheory
open GravityScreening GravityScreening.HodgeResponseCovariance PDTResponseBridge

section Integral
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)

def inclusive (a : Ω → Four) : Four := fun i => ∫ ω, a ω i ∂μ

/-- Integrating a gauge shift produces a gauge shift of the integrated field.
The proof works for every supplied measure, so does not select its mass. -/
theorem inclusive_gauge (k : Four) (a : Ω → Four)
    (ha : ∀ i, Integrable (fun ω => a ω i) μ)
    (c : Ω → ℝ) (hc : Integrable c μ) :
    inclusive μ (fun ω => gauge k (a ω) (c ω)) =
      gauge k (inclusive μ a) (∫ ω, c ω ∂μ) := by
  ext i
  simp only [inclusive, PDTMaxwellSymbol.gauge, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [integral_add (ha i) (hc.mul_const (k i)), integral_mul_const]

/-- The conserved source remains gauge invariant under the inclusive readout. -/
theorem inclusive_source_gauge (k j : Four) (hj : conserved k j)
    (a : Ω → Four) (ha : ∀ i, Integrable (fun ω => a ω i) μ)
    (c : Ω → ℝ) (hc : Integrable c μ) :
    mink j (inclusive μ (fun ω => gauge k (a ω) (c ω))) =
      mink j (inclusive μ a) := by
  rw [inclusive_gauge μ k a ha c hc]
  exact (source_gauge_iff k j (inclusive μ a)).mpr hj _
end Integral

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

/-- The physical wave field lives in the same V and inherits the same scalar.
This does not replace the 15-dimensional coupling determinant by a 2D one. -/
theorem actual_wave_response (x y : ℝ) :
    S (fieldCoordinates waveVector (transverse x y)) =
      (rho*q) • fieldCoordinates waveVector (transverse x y) := by
  have hR := (HodgeModeCalibration.real_geometric_hodge_calibrated_determinant
    R ha hh rho q hmode).1
  have hs := descended_response_unique hv R (rho*q) hR S hS
  simp [hs]

/-- The supplied kinetic coefficient of the actual quotient is reciprocal
to e² = 4*pi*alpha_L1. No observed coupling is used. -/
theorem actual_stiffness_times_e2 (hr : 0 < rho*q) :
    PDTEinsteinMaxwellInterface.maxwellStiffness
        (LinearMap.det S) projectiveBoundaryVolume *
      (4*Real.pi*electromagneticCoupling rho q) = 1 := by
  rw [PDTBoundaryConnection.actual_quotient_determinant
    R ha hh rho q hmode hv S hS]
  unfold PDTEinsteinMaxwellInterface.maxwellStiffness
    electromagneticCoupling electromagneticExponent
  rw [projectiveBoundaryVolume_eq_pi_sq]
  field_simp [ne_of_gt hr, Real.pi_ne_zero]
  exact div_self (ne_of_gt hr)

/-- The non-null conserved-current mode solves the sourced Euler equation
with the actual calibrated quotient's supplied kinetic coefficient. -/
theorem actual_conserved_source_equation (hr : 0 < rho*q)
    (k j : Four) (hj : conserved k j) (hk : mink k k ≠ 0) :
    let a := ((4*Real.pi*electromagneticCoupling rho q)/mink k k) • j
    conserved k a ∧
      PDTEinsteinMaxwellInterface.maxwellStiffness
        (LinearMap.det S) projectiveBoundaryVolume • symbol k a = j := by
  try dsimp
  have hs := conserved_source_solution k j hj hk
    (4*Real.pi*electromagneticCoupling rho q)
  refine ⟨hs.1, ?_⟩
  rw [hs.2, smul_smul,
    actual_stiffness_times_e2 R ha hh rho q hmode hv S hS hr, one_smul]

#print axioms inclusive_gauge
#print axioms inclusive_source_gauge
#print axioms actual_wave_response
#print axioms actual_stiffness_times_e2
#print axioms actual_conserved_source_equation
end
end PDTMaxwellResponse
