module
public import MaxwellSymbol

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! Two physical polarization amplitudes at one fixed nonzero null wave-vector,
embedded in the actual local bivectors of the frozen geometric construction. -/
namespace PDTMaxwellHodge
noncomputable section
open PDTMaxwellSymbol GravityScreening
open scoped Matrix

def waveVector : Four := ![0,0,1,1]
def transverse (x y : ℝ) : Four := ![x,y,0,0]
def extend (a : Four) : Fin 6 → ℝ := ![a 0,a 1,a 2,a 3,0,0]
def fieldCoordinates (k a : Four) : Fin 15 → ℝ := fun p =>
  let pair := ResponseClosureGeometry.basisPairs p
  extend k pair.1 * extend a pair.2 - extend k pair.2 * extend a pair.1

theorem waveVector_null : mink waveVector waveVector = 0 := by
  change (0 : ℝ)*0+0*0+1*1-1*1 = 0
  norm_num

theorem free_wave_iff (a : Four) :
    symbol waveVector a = 0 ↔ a 2 = a 3 := by
  constructor
  · intro h
    have hi := congrFun h 2
    have he : a 3 = a 2 := by
      simpa [symbol, mink, waveVector, sub_eq_zero] using hi
    exact he.symm
  · intro h
    ext i
    fin_cases i <;> simp [symbol, mink, waveVector, h]

/-- Every free amplitude is uniquely a transverse pair plus one gauge direction. -/
theorem two_polarizations (a : Four) (ha : symbol waveVector a = 0) :
    ∃! u : ℝ × ℝ × ℝ,
      a = gauge waveVector (transverse u.1 u.2.1) u.2.2 := by
  have h := (free_wave_iff a).mp ha
  refine ⟨(a 0,a 1,a 2), ?_, ?_⟩
  · ext i
    fin_cases i <;> simp [PDTMaxwellSymbol.gauge, transverse, waveVector, h]
  · intro u hu
    have h0 := congrFun hu 0
    have h1 := congrFun hu 1
    have h2 := congrFun hu 2
    simp [PDTMaxwellSymbol.gauge, transverse, waveVector] at h0 h1 h2
    exact Prod.ext h0.symm (Prod.ext h1.symm h2.symm)

theorem transverse_is_free (x y : ℝ) :
    symbol waveVector (transverse x y) = 0 := by
  apply (free_wave_iff _).mpr
  simp [transverse]

/-- The field coordinate map, rather than the potential, removes gauge freedom. -/
theorem fieldCoordinates_gauge (k a : Four) (c : ℝ) :
    fieldCoordinates k (gauge k a c) = fieldCoordinates k a := by
  ext p
  fin_cases p <;>
    simp [fieldCoordinates, extend, ResponseClosureGeometry.basisPairs,
      PDTMaxwellSymbol.gauge, smul_eq_mul] <;> ring

theorem physical_field_injective :
    Function.Injective (fun u : ℝ × ℝ =>
      fieldCoordinates waveVector (transverse u.1 u.2)) := by
  intro u v h
  have h1 := congrFun h 1
  have h5 := congrFun h 5
  simp [fieldCoordinates, extend, ResponseClosureGeometry.basisPairs,
    waveVector, transverse] at h1 h5
  exact Prod.ext h1 h5

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
/-- The actual geometric local Hodge rotates the two transverse polarizations.
The 15-by-15 Hodge is imported, not replaced by an independently chosen 2-by-2 model. -/
theorem actual_hodge_on_wave (x y : ℝ) :
    (HodgeResponseCovariance.hodgeGenerator ℝ : Matrix (Fin 15) (Fin 15) ℝ) *ᵥ
        fieldCoordinates waveVector (transverse x y) =
      fieldCoordinates waveVector (transverse y (-x)) := by
  change HodgeLieGeneration.castMatrix ℝ ResponseClosureGeometry.hodgeComplement *ᵥ
    fieldCoordinates waveVector (transverse x y) = _
  rw [← ResponseClosureGeometry.certificate_hodge]
  ext i
  fin_cases i <;>
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero] <;>
    dsimp [HodgeLieGeneration.castMatrix, RingHom.mapMatrix, Matrix.map,
      ResponseClosureCertificate.hodge, Matrix.single,
      fieldCoordinates, extend, ResponseClosureGeometry.basisPairs,
      waveVector, transverse] <;> norm_num

#print axioms free_wave_iff
#print axioms two_polarizations
#print axioms fieldCoordinates_gauge
#print axioms physical_field_injective
#print axioms actual_hodge_on_wave
end
end PDTMaxwellHodge
