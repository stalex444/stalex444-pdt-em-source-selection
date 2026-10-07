module
public import GravityScreening.HodgeModeCalibration
public import GravityScreening.ConformalResponseAlgebra

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! Private continuation, independent of the frozen submission. Evaluation and
restriction of its actual calibrated response; no Maxwell identification is
assumed or concluded. -/
namespace PDTResponseBridge
noncomputable section
open GravityScreening GravityScreening.HodgeResponseCovariance
open scoped Matrix

abbrev V := Fin 15 → ℝ
abbrev G := ResponseAlgebra ℝ
abbrev Mat := Matrix (Fin 15) (Fin 15) ℝ

def ev (v : V) : G →ₗ[ℝ] V where
  toFun T := (T : Mat) *ᵥ v
  map_add' T U := Matrix.add_mulVec (T : Mat) (U : Mat) v
  map_smul' c T := Matrix.smul_mulVec c (T : Mat) v

theorem ev_surjective {v : V} (hv : v ≠ 0) : Function.Surjective (ev v) := by
  exact TraceFreeMatrixSolver.action_surjective (by norm_num) hv

def stabilizer (v : V) : Submodule ℝ G := LinearMap.ker (ev v)

theorem dim_G : Module.finrank ℝ G = 224 := by
  change Module.finrank ℝ (LieAlgebra.SpecialLinear.sl (Fin 15) ℝ) = 224
  have h := SignedLieGeneration.finrank_sl_add_one (K := ℝ) (0 : Fin 15)
  norm_num at h
  omega

theorem dim_stabilizer {v : V} (hv : v ≠ 0) :
    Module.finrank ℝ (stabilizer v) = 209 := by
  have h := LinearMap.finrank_range_add_finrank_ker (ev v)
  rw [LinearMap.range_eq_top.mpr (ev_surjective hv), finrank_top, dim_G] at h
  have hd : Module.finrank ℝ V = 15 := by simp [V]
  rw [hd] at h
  change Module.finrank ℝ (LinearMap.ker (ev v)) = 209
  omega

/-- The target response is uniquely forced by the commuting evaluation square. -/
theorem descended_response_unique {v : V} (hv : v ≠ 0)
    (R : G →ₗ[ℝ] G) (r : ℝ) (hR : R = r • LinearMap.id)
    (S : V →ₗ[ℝ] V) (hS : (ev v).comp R = S.comp (ev v)) :
    S = r • LinearMap.id := by
  apply LinearMap.ext
  intro w
  obtain ⟨T, rfl⟩ := ev_surjective hv w
  have h := LinearMap.congr_fun hS T
  simpa [hR] using h.symm

theorem descent_square (v : V) (r : ℝ) :
    (ev v).comp (r • LinearMap.id) = (r • LinearMap.id).comp (ev v) := by
  apply LinearMap.ext
  intro T
  simp

def restrictedResponse (v : V) (R : G →ₗ[ℝ] G)
    (h : ∀ T, T ∈ stabilizer v → R T ∈ stabilizer v) :
    stabilizer v →ₗ[ℝ] stabilizer v where
  toFun T := ⟨R T, h T T.property⟩
  map_add' T U := Subtype.ext (R.map_add T U)
  map_smul' c T := Subtype.ext (R.map_smul c T)

theorem preserves_stabilizer (v : V) (R : G →ₗ[ℝ] G)
    (r : ℝ) (hR : R = r • LinearMap.id) :
    ∀ T, T ∈ stabilizer v → R T ∈ stabilizer v := by
  intro T hT
  simpa [hR] using (stabilizer v).smul_mem r hT

theorem restriction_scalar (v : V) (R : G →ₗ[ℝ] G)
    (r : ℝ) (hR : R = r • LinearMap.id) :
    restrictedResponse v R (preserves_stabilizer v R r hR) =
      r • LinearMap.id := by
  apply LinearMap.ext
  intro T
  apply Subtype.ext
  simp [restrictedResponse, hR]

/-- Determinants of the restriction and the uniquely induced response, on the
same 224-dimensional response that appears in the generation theorem. -/
theorem determinant_factorization {v : V} (hv : v ≠ 0)
    (R : G →ₗ[ℝ] G) (r : ℝ) (hR : R = r • LinearMap.id) :
    LinearMap.det R = r ^ 224 ∧
    LinearMap.det (restrictedResponse v R (preserves_stabilizer v R r hR)) = r ^ 209 ∧
    LinearMap.det (r • (LinearMap.id : V →ₗ[ℝ] V)) = r ^ 15 ∧
    LinearMap.det R =
      LinearMap.det (restrictedResponse v R (preserves_stabilizer v R r hR)) *
      LinearMap.det (r • (LinearMap.id : V →ₗ[ℝ] V)) := by
  rw [restriction_scalar v R r hR, hR]
  simp only [LinearMap.det_smul, LinearMap.det_id, mul_one,
    dim_G, dim_stabilizer hv]
  have hd : Module.finrank ℝ V = 15 := by simp [V]
  rw [hd]
  simp only [and_self, ← pow_add]

/-- Infinitesimal covariance is restored when the anchor varies by A v. -/
theorem moving_anchor_covariance (A T : G) (v : V) :
    ev v ⁅A,T⁆ + ev ((A : Mat) *ᵥ v) T = (A : Mat) *ᵥ ev v T := by
  change ((A : Mat) * (T : Mat) - (T : Mat) * (A : Mat)) *ᵥ v +
    (T : Mat) *ᵥ ((A : Mat) *ᵥ v) = (A : Mat) *ᵥ ((T : Mat) *ᵥ v)
  rw [Matrix.sub_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  exact sub_add_cancel _ _

/-- For a fixed anchor, covariance under A holds exactly when A fixes v. -/
theorem fixed_anchor_covariance_iff (A : G) (v : V) :
    (∀ T : G, ev v ⁅A,T⁆ = (A : Mat) *ᵥ ev v T) ↔ (A : Mat) *ᵥ v = 0 := by
  constructor
  · intro h
    by_contra hn
    obtain ⟨T, hT⟩ := ev_surjective hn (fun _ => 1)
    have he := moving_anchor_covariance A T v
    rw [h T, hT] at he
    have hz : (fun _ : Fin 15 => (1 : ℝ)) = 0 := add_left_cancel (he.trans (add_zero _).symm)
    have := congr_fun hz 0
    norm_num at this
  · intro h T
    have he := moving_anchor_covariance A T v
    simpa [h, ev] using he

/-- No nonzero choice of fixed anchor makes evaluation a full g-module map.
This excludes this candidate construction, not other EM/gravity interfaces. -/
theorem no_fixed_anchor_full_covariance {v : V} (hv : v ≠ 0) :
    ¬ (∀ A T : G, ev v ⁅A,T⁆ = (A : Mat) *ᵥ ev v T) := by
  intro h
  obtain ⟨A, hA⟩ := ev_surjective hv (fun _ => 1)
  have hz := (fixed_anchor_covariance_iff A v).mp (h A)
  change ev v A = 0 at hz
  rw [hA] at hz
  have := congr_fun hz 0
  norm_num at this

/-- Finite counterpart of moving-anchor covariance; all matrices here act
on V, and U is the supplied left inverse of S. -/
theorem finite_moving_anchor (S U T : Mat) (hUS : U * S = 1) (v : V) :
    (S * T * U) *ᵥ (S *ᵥ v) = S *ᵥ (T *ᵥ v) := by
  simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc, hUS, mul_one]

/-- The full real Hodge calibration theorem now feeds the evaluation descent. -/
theorem calibrated_response_descends
    (R : G →ₗ[ℝ] G)
    (ha : ∀ p x, R ⁅adjointGenerator ℝ p, x⁆ = ⁅adjointGenerator ℝ p, R x⁆)
    (hh : ∀ x, R ⁅hodgeGenerator ℝ, x⁆ = ⁅hodgeGenerator ℝ, R x⁆)
    (rho q : ℝ)
    (hmode : HodgeModeCalibration.complexifyMatrix (R (hodgeGenerator ℝ) : Mat) =
      HodgeModeCalibration.divide (rho : ℂ) (q : ℂ) * HodgeModeCalibration.hodgeMatrix *
        HodgeModeCalibration.flip (rho : ℂ) (q : ℂ))
    {v : V} (hv : v ≠ 0) :
    ∃! S : V →ₗ[ℝ] V, (ev v).comp R = S.comp (ev v) := by
  have hR := (HodgeModeCalibration.real_geometric_hodge_calibrated_determinant
    R ha hh rho q hmode).1
  refine ⟨(rho * q) • LinearMap.id, ?_, ?_⟩
  · rw [hR]
    exact descent_square v (rho * q)
  · intro S hS
    exact descended_response_unique hv R (rho * q) hR S hS

#print axioms determinant_factorization
#print axioms moving_anchor_covariance
#print axioms fixed_anchor_covariance_iff
#print axioms no_fixed_anchor_full_covariance
#print axioms finite_moving_anchor
#print axioms calibrated_response_descends
end
end PDTResponseBridge
