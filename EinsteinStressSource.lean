module
public import StressBalance

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! Insert the actual electromagnetic stress into the frozen local Einstein
closure, retaining its null-Clausius premise and the calibrated PDT response.
The old Einstein module has time index 0; the actual field has time index 3.
Both lowering tensor indices and permuting the coordinates are explicit. -/
namespace PDTEinsteinStressSource
noncomputable section
open PDTStressTensor PDTResponseBridge
open GravityScreening GravityScreening.HodgeResponseCovariance
open scoped Matrix

def timeFirstIndex : Fin 4 → Fin 4 := ![3,0,1,2]
def gravitationalStress (d : ℝ) (v : V) : Tensor := fun i j =>
  eta (timeFirstIndex i)*eta (timeFirstIndex j)*
    registerStress d v (timeFirstIndex i) (timeFirstIndex j)

theorem gravitationalStress_symmetric (d : ℝ) (v : V) :
    (gravitationalStress d v).transpose = gravitationalStress d v := by
  ext i j
  have h : registerStress d v (timeFirstIndex j) (timeFirstIndex i) =
      registerStress d v (timeFirstIndex i) (timeFirstIndex j) :=
    congrArg (fun T : Tensor => T (timeFirstIndex i) (timeFirstIndex j))
      (stress_symmetric d (field v))
  change eta (timeFirstIndex j)*eta (timeFirstIndex i)*_ =
    eta (timeFirstIndex i)*eta (timeFirstIndex j)*_
  rw [h]
  ring

theorem gravitationalStress_coefficient (d : ℝ) (v : V) :
    gravitationalStress d v = d • gravitationalStress 1 v := by
  ext i j
  simp [gravitationalStress, registerStress, stress]
  ring

theorem gravitationalStress_hodge_invariant (d : ℝ) (v : V) :
    gravitationalStress d (PDTHodgeConnection.H *ᵥ v) = gravitationalStress d v := by
  unfold gravitationalStress
  rw [actual_hodge_preserves_stress]

theorem gravitationalStress_traceless (d : ℝ) (v : V) :
    localMinkowskiTrace (gravitationalStress d v) = 0 := by
  have h := stress_traceless d (field v)
  simp [localMinkowskiTrace, gravitationalStress, timeFirstIndex, eta,
    registerStress]
  linarith

variable (R : G →ₗ[ℝ] G)
variable (ha : ∀ p x, R ⁅adjointGenerator ℝ p, x⁆ = ⁅adjointGenerator ℝ p, R x⁆)
variable (hh : ∀ x, R ⁅hodgeGenerator ℝ, x⁆ = ⁅hodgeGenerator ℝ, R x⁆)
variable (rho q : ℝ)
variable (hmode : HodgeModeCalibration.complexifyMatrix (R (hodgeGenerator ℝ) : Mat) =
  HodgeModeCalibration.divide (rho : ℂ) (q : ℂ) * HodgeModeCalibration.hodgeMatrix *
  HodgeModeCalibration.flip (rho : ℂ) (q : ℂ))
variable {anchor : V} (hv : anchor ≠ 0)
variable (S : V →ₗ[ℝ] V) (hS : (ev anchor).comp R = S.comp (ev anchor))
include ha hh hmode hv hS

/-- The existing actual determinant cancellation now multiplies the actual
field stress tensor, in the coordinate convention of the Einstein theorem. -/
theorem actual_einstein_source (hr : 0 < rho*q) (screening m : ℝ) (v : V) :
    (8*Real.pi*PDTEinsteinMaxwellInterface.newtonCoefficient
      (LinearMap.det R) projectiveBoundaryVolume screening m) •
        gravitationalStress (PDTEinsteinMaxwellInterface.maxwellStiffness
          (LinearMap.det S) projectiveBoundaryVolume) v =
      (2*Real.pi^2/(screening*(rho*q)^209*m^2)) • gravitationalStress 1 v := by
  rw [gravitationalStress_coefficient, smul_smul]
  rw [PDTEinsteinMaxwellInterface.pdt_source_coefficient
    R ha hh rho q hmode hv S hS hr screening m]

/-- The frozen local Einstein shape theorem, instantiated on these fields.
Ricci symmetry and the same null-Clausius relation remain hypotheses. -/
theorem actual_null_clausius_einstein_source
    (hr : 0 < rho*q) (screening m : ℝ) (v : V) (ricci : Tensor)
    (hRicci : ricci.transpose = ricci)
    (hnull : ∀ u : Fin 4 → ℝ, localMinkowskiSq u = 0 →
      localQuadraticContraction
        (ricci -
          (8*Real.pi*PDTEinsteinMaxwellInterface.newtonCoefficient
            (LinearMap.det R) projectiveBoundaryVolume screening m) •
              gravitationalStress (PDTEinsteinMaxwellInterface.maxwellStiffness
                (LinearMap.det S) projectiveBoundaryVolume) v) u = 0) :
    ∃ cosmological : ℝ,
      ricci - (localMinkowskiTrace ricci/2) • localMinkowskiMetric +
        cosmological • localMinkowskiMetric =
          (2*Real.pi^2/(screening*(rho*q)^209*m^2)) • gravitationalStress 1 v := by
  obtain ⟨c,hc⟩ := nullClausius_forces_localEinsteinShape ricci
    (gravitationalStress (PDTEinsteinMaxwellInterface.maxwellStiffness
      (LinearMap.det S) projectiveBoundaryVolume) v)
    (8*Real.pi*PDTEinsteinMaxwellInterface.newtonCoefficient
      (LinearMap.det R) projectiveBoundaryVolume screening m)
    hRicci (gravitationalStress_symmetric _ v) hnull
  refine ⟨c, ?_⟩
  rw [hc]
  exact actual_einstein_source R ha hh rho q hmode hv S hS hr screening m v

#print axioms gravitationalStress_symmetric
#print axioms gravitationalStress_coefficient
#print axioms gravitationalStress_hodge_invariant
#print axioms gravitationalStress_traceless
#print axioms actual_einstein_source
#print axioms actual_null_clausius_einstein_source
end
end PDTEinsteinStressSource
