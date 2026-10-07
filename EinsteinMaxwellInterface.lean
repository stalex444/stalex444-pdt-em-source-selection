module
public import BoundaryConnection
public import CurrentFrame

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! Coefficient identities on one calibrated response and its actual quotient.
Einstein-Maxwell dynamics and the unit-charge field convention are physical
inputs to the interpretation; these theorems do not construct those equations. -/
namespace PDTEinsteinMaxwellInterface
noncomputable section
open GravityScreening GravityScreening.HodgeResponseCovariance
open PDTResponseBridge

/-- Newton's constant in natural units, with m the electron reference mass. -/
def newtonCoefficient (Dg B screening m : ℝ) : ℝ :=
  B^2/(screening * Dg * m^2)

/-- Maxwell stiffness 1/e^2 in the convention where A couples to unit charge. -/
def maxwellStiffness (Dv B : ℝ) : ℝ := Dv/(4*Real.pi*B)

/-- The quotient determinant cancels from the Einstein source coefficient
when G and e^2 are built from the same factorized response. -/
theorem source_coefficient_cancellation (Dg Dh Dv B screening m : ℝ)
    (hfactor : Dg = Dh*Dv) (hDv : Dv ≠ 0) (hB : B ≠ 0) :
    8*Real.pi*newtonCoefficient Dg B screening m * maxwellStiffness Dv B =
      2*B/(screening * Dh * m^2) := by
  rw [hfactor]
  unfold newtonCoefficient maxwellStiffness
  by_cases hs : screening = 0
  · simp [hs]
  by_cases hh : Dh = 0
  · simp [hh]
  by_cases hm : m = 0
  · simp [hm]
  field_simp
  ring

/-- The common ruler can be eliminated entirely, giving a consistency
identity for the two leading couplings without substituting measured alpha. -/
theorem shared_ruler_consistency (r B screening : ℝ) (hs : screening ≠ 0) :
    (B^2/(screening*r^224))^15 * screening^15 * B^194 =
      (B/r^15)^224 := by
  by_cases hr : r = 0
  · subst r
    simp
  · field_simp

/-- The same determinant cancellation in the dimensionless coupling ratio. -/
theorem coupling_ratio_cancellation (Dg Dh Dv B screening : ℝ)
    (hfactor : Dg = Dh*Dv) (hDv : Dv ≠ 0) (hB : B ≠ 0) :
    (B^2/(screening*Dg))/(B/Dv) = B/(screening*Dh) := by
  rw [hfactor]
  by_cases hs : screening = 0
  · simp [hs]
  by_cases hh : Dh = 0
  · simp [hh]
  field_simp

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

/-- Transported spatial currents reproduce the coupling of the actual
quotient response with the supplied geometric measure. -/
theorem actual_current_readout {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) (hB : μ.real Set.univ = projectiveBoundaryVolume)
    (O : Ω → PDTCurrentFrame.Rotation)
    (hO : ∀ ω, O ω * (O ω).transpose = 1) (j : PDTCurrentFrame.Spatial) :
    PDTCurrentFrame.readout μ O
        (PDTCurrentFrame.localMinimum O (LinearMap.det S/(4*Real.pi)) j) =
      (4*Real.pi*electromagneticCoupling rho q) • j := by
  rw [PDTCurrentFrame.minimum_readout μ O hO]
  have hDS := PDTBoundaryConnection.actual_quotient_determinant
    R ha hh rho q hmode hv S hS
  have hc : PDTBoundaryAction.mass μ / (LinearMap.det S/(4*Real.pi)) =
      4*Real.pi*electromagneticCoupling rho q := by
    rw [hDS]
    change μ.real Set.univ / ((rho*q)^15/(4*Real.pi)) = _
    rw [hB, projectiveBoundaryVolume_eq_pi_sq]
    unfold electromagneticCoupling electromagneticExponent
    field_simp
  rw [hc]

/-- The already banked alpha-link, expressed on this calibrated R and
its actual descended S. The complementary count is forced by the restriction. -/
theorem actual_coupling_ratio (hr : 0 < rho*q) (B screening : ℝ)
    (hB : B ≠ 0) :
    (B^2/(screening*LinearMap.det R))/(B/LinearMap.det S) =
      B/(screening*(rho*q)^209) := by
  have hR := (HodgeModeCalibration.real_geometric_hodge_calibrated_determinant
    R ha hh rho q hmode).1
  have hD := determinant_factorization hv R (rho*q) hR
  have hDS := PDTBoundaryConnection.actual_quotient_determinant
    R ha hh rho q hmode hv S hS
  have hf : LinearMap.det R = (rho*q)^209 * LinearMap.det S := by
    rw [hDS, hD.1, ← pow_add]
  exact coupling_ratio_cancellation _ _ _ _ _ hf
    (by rw [hDS]; exact pow_ne_zero _ (ne_of_gt hr)) hB

/-- The remaining 209 power is the determinant of the anchored restriction
of this R; it is not an independently inserted complementary factor. -/
theorem actual_source_coefficient (hr : 0 < rho*q) (B screening m : ℝ)
    (hB : B ≠ 0) :
    8*Real.pi*newtonCoefficient (LinearMap.det R) B screening m *
        maxwellStiffness (LinearMap.det S) B =
      2*B/(screening * (rho*q)^209 * m^2) := by
  have hR := (HodgeModeCalibration.real_geometric_hodge_calibrated_determinant
    R ha hh rho q hmode).1
  have hD := determinant_factorization hv R (rho*q) hR
  have hDS := PDTBoundaryConnection.actual_quotient_determinant
    R ha hh rho q hmode hv S hS
  have hf : LinearMap.det R = (rho*q)^209 * LinearMap.det S := by
    rw [hDS, hD.1, ← pow_add]
  exact source_coefficient_cancellation _ _ _ _ _ _ hf
    (by rw [hDS]; exact pow_ne_zero _ (ne_of_gt hr)) hB

theorem pdt_source_coefficient (hr : 0 < rho*q) (screening m : ℝ) :
    8*Real.pi*newtonCoefficient (LinearMap.det R) projectiveBoundaryVolume screening m *
        maxwellStiffness (LinearMap.det S) projectiveBoundaryVolume =
      2*Real.pi^2/(screening * (rho*q)^209 * m^2) := by
  have h := actual_source_coefficient R ha hh rho q hmode hv S hS hr
    projectiveBoundaryVolume screening m
    (by rw [projectiveBoundaryVolume_eq_pi_sq]; positivity)
  simpa [projectiveBoundaryVolume_eq_pi_sq] using h

#print axioms source_coefficient_cancellation
#print axioms shared_ruler_consistency
#print axioms coupling_ratio_cancellation
#print axioms actual_current_readout
#print axioms actual_coupling_ratio
#print axioms actual_source_coefficient
#print axioms pdt_source_coefficient
end
end PDTEinsteinMaxwellInterface
