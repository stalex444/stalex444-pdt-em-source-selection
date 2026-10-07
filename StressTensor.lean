module
public import HodgeConnection
public import GravityScreening.LocalEinsteinClosure

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! Maxwell stress on the original local bivectors, with time index 3.
The Hilbert stress convention and Maxwell kinetic assignment are explicit.
The independent metric-variation calculation is in check_stress.py. -/
namespace PDTStressTensor
noncomputable section
open PDTMaxwellSymbol PDTMaxwellHodge PDTResponseBridge
open scoped Matrix

abbrev Tensor := Matrix (Fin 4) (Fin 4) ℝ
def eta : Four := ![1,1,1,-1]
def metric : Tensor := Matrix.diagonal eta

/-- Contravariant field components extracted from the actual register. -/
def field (v : V) : Tensor :=
  !![0, v 0, v 1, v 2;
     -v 0, 0, v 5, v 6;
     -v 1, -v 5, 0, v 9;
     -v 2, -v 6, -v 9, 0]

def invariant (F : Tensor) : ℝ :=
  mink (F 0) (F 0)+mink (F 1) (F 1)+mink (F 2) (F 2)-mink (F 3) (F 3)
def stress (d : ℝ) (F : Tensor) : Tensor := fun μ ν =>
  d*(mink (F μ) (F ν)-metric μ ν*invariant F/4)
def registerStress (d : ℝ) (v : V) : Tensor := stress d (field v)

theorem field_from_existing_wave (k a : Four) :
    field (fieldCoordinates k a) = fieldTensor k a := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [field, fieldCoordinates, extend, GravityScreening.ResponseClosureGeometry.basisPairs,
      fieldTensor]

theorem stress_symmetric (d : ℝ) (F : Tensor) :
    (stress d F).transpose = stress d F := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [stress, metric, eta, Matrix.diagonal, mink, Matrix.transpose_apply, mul_comm]

theorem stress_traceless (d : ℝ) (F : Tensor) :
    stress d F 0 0+stress d F 1 1+stress d F 2 2-stress d F 3 3 = 0 := by
  simp [stress, metric, eta, Matrix.diagonal, invariant]
  ring

theorem stress_coefficient (d : ℝ) (F : Tensor) :
    stress d F = d • stress 1 F := by
  ext i j
  simp [stress]

theorem register_energy (d : ℝ) (v : V) :
    registerStress d v 3 3 =
      d/2*((v 0)^2+(v 1)^2+(v 2)^2+(v 5)^2+(v 6)^2+(v 9)^2) := by
  simp [registerStress, stress, field, metric, eta, Matrix.diagonal, invariant, mink]
  ring

theorem register_energy_nonnegative (d : ℝ) (hd : 0 ≤ d) (v : V) :
    0 ≤ registerStress d v 3 3 := by
  rw [register_energy]
  positivity

/-- A local dual field, with signs inherited from the actual oriented Hodge. -/
def dualField (v : V) : Tensor :=
  !![0, -v 9, v 6, v 5;
     v 9, 0, -v 2, -v 1;
     -v 6, v 2, 0, v 0;
     -v 5, v 1, -v 0, 0]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem field_actual_hodge (v : V) :
    field (PDTHodgeConnection.H *ᵥ v) = dualField v := by
  change field (GravityScreening.HodgeLieGeneration.castMatrix ℝ
    GravityScreening.ResponseClosureGeometry.hodgeComplement *ᵥ v) = _
  rw [← GravityScreening.ResponseClosureGeometry.certificate_hodge]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [field, dualField, Matrix.mulVec, dotProduct,
      GravityScreening.HodgeLieGeneration.castMatrix, RingHom.mapMatrix, Matrix.map,
      GravityScreening.ResponseClosureCertificate.hodge, Matrix.single]

theorem actual_hodge_preserves_stress (d : ℝ) (v : V) :
    registerStress d (PDTHodgeConnection.H *ᵥ v) = registerStress d v := by
  unfold registerStress
  rw [field_actual_hodge]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [stress, field, dualField, metric, eta, Matrix.diagonal, invariant, mink] <;>
      ring_nf <;> simp

/-- Physical wave stress: a positive coefficient times a null outer product. -/
theorem wave_stress (d x y : ℝ) :
    registerStress d (fieldCoordinates waveVector (transverse x y)) =
      fun μ ν => (d*(x^2+y^2))*waveVector μ*waveVector ν := by
  unfold registerStress
  rw [field_from_existing_wave]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [stress, fieldTensor, waveVector, transverse, metric, eta,
      Matrix.diagonal, invariant, mink] <;> ring_nf <;> simp

/-- Bilinear stress for a simple field k wedge a, on vector probes u,w. -/
def waveStressForm (d : ℝ) (k a u w : Four) : ℝ :=
  d*(mink k u*mink k w*mink a a -
    (mink k u*mink a w+mink a u*mink k w)*mink k a +
    mink a u*mink a w*mink k k -
    mink u w*(mink k k*mink a a-(mink k a)^2)/2)

theorem wave_stress_lorentz_invariant (L : Four ≃ₗ[ℝ] Four)
    (hL : PDTLorentzFrame.IsLorentz L) (d : ℝ) (k a u w : Four) :
    waveStressForm d (L k) (L a) (L u) (L w) = waveStressForm d k a u w := by
  simp only [waveStressForm, hL k u, hL k w, hL a a, hL a w,
    hL a u, hL k a, hL k k, hL u w]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
/-- This invariant form is the contraction of the same component stress. -/
theorem wave_stress_form_is_contraction (d : ℝ) (k a u w : Four) :
    waveStressForm d k a u w =
      ∑ μ, ∑ ν, eta μ*u μ*stress d (fieldTensor k a) μ ν*eta ν*w ν := by
  simp [waveStressForm, Fin.sum_univ_succ, eta, stress, metric,
    Matrix.diagonal, invariant, fieldTensor, mink]
  ring

#print axioms field_from_existing_wave
#print axioms stress_symmetric
#print axioms stress_traceless
#print axioms stress_coefficient
#print axioms register_energy
#print axioms register_energy_nonnegative
#print axioms field_actual_hodge
#print axioms actual_hodge_preserves_stress
#print axioms wave_stress
#print axioms wave_stress_lorentz_invariant
#print axioms wave_stress_form_is_contraction
end
end PDTStressTensor
