module
public import BoundaryAction
public import Mathlib.LinearAlgebra.Matrix.DotProduct

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! Transport of one spatial current between orthogonal observer frames.
The measure and the inclusive source/readout assignment are supplied.
This is a positive spatial-mode model, not a Lorentzian Maxwell construction. -/
namespace PDTCurrentFrame
noncomputable section
open MeasureTheory
open scoped Matrix

abbrev Spatial := Fin 3 → ℝ
abbrev Rotation := Matrix (Fin 3) (Fin 3) ℝ

/-- Rotating both field and source preserves the source pairing. -/
theorem source_pairing (O : Rotation) (j a : Spatial) :
    j ⬝ᵥ (O *ᵥ a) = (O.transpose *ᵥ j) ⬝ᵥ a := by
  rw [Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]

theorem transported_norm (O : Rotation) (hO : O * O.transpose = 1)
    (j : Spatial) :
    (O.transpose *ᵥ j) ⬝ᵥ (O.transpose *ᵥ j) = j ⬝ᵥ j := by
  rw [Matrix.dotProduct_transpose_mulVec, Matrix.mulVec_mulVec, hO,
    Matrix.one_mulVec]

/-- Completing the square in the local frame keeps the laboratory current's norm. -/
theorem local_action_split (O : Rotation) (hO : O * O.transpose = 1)
    (d : ℝ) (hd : d ≠ 0) (j a : Spatial) :
    (d/2)*(a ⬝ᵥ a) - j ⬝ᵥ (O *ᵥ a) =
      (d/2)*((a - d⁻¹ • (O.transpose *ᵥ j)) ⬝ᵥ
        (a - d⁻¹ • (O.transpose *ᵥ j))) - (j ⬝ᵥ j)/(2*d) := by
  rw [source_pairing, ← transported_norm O hO j]
  generalize O.transpose *ᵥ j = k
  simp only [dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  field_simp [hd]
  ring

theorem local_action_minimum (O : Rotation) (hO : O * O.transpose = 1)
    (d : ℝ) (hd : 0 < d) (j a : Spatial) :
    -(j ⬝ᵥ j)/(2*d) ≤ (d/2)*(a ⬝ᵥ a) - j ⬝ᵥ (O *ᵥ a) := by
  rw [local_action_split O hO d (ne_of_gt hd)]
  have hn : 0 ≤ (a - d⁻¹ • (O.transpose *ᵥ j)) ⬝ᵥ
      (a - d⁻¹ • (O.transpose *ᵥ j)) := by
    exact Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
  have hm := mul_nonneg (show 0 ≤ d/2 by positivity) hn
  rw [neg_div]
  linarith only [hm]

variable {Ω : Type*} [MeasurableSpace Ω]

def localMinimum (O : Ω → Rotation) (d : ℝ) (j : Spatial) :
    Ω → Spatial := fun ω => d⁻¹ • ((O ω).transpose *ᵥ j)

def readout (μ : Measure Ω) (O : Ω → Rotation) (a : Ω → Spatial) :
    Spatial := fun i => ∫ ω, (O ω *ᵥ a ω) i ∂μ

omit [MeasurableSpace Ω] in
/-- The same laboratory current is recovered in every local frame. -/
theorem localMinimum_transports (O : Ω → Rotation)
    (hO : ∀ ω, O ω * (O ω).transpose = 1) (d : ℝ) (j : Spatial) (ω : Ω) :
    O ω *ᵥ localMinimum O d j ω = d⁻¹ • j := by
  simp [localMinimum, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hO]

/-- Integrating the transported current supplies B/d, with no factor of three. -/
theorem minimum_readout (μ : Measure Ω) (O : Ω → Rotation)
    (hO : ∀ ω, O ω * (O ω).transpose = 1) (d : ℝ) (j : Spatial) :
    readout μ O (localMinimum O d j) = (PDTBoundaryAction.mass μ / d) • j := by
  ext i
  simp only [readout, localMinimum_transports O hO, Pi.smul_apply, smul_eq_mul]
  rw [integral_const]
  simp [PDTBoundaryAction.mass, smul_eq_mul, div_eq_mul_inv, mul_assoc]

omit [MeasurableSpace Ω] in
/-- The minimizing family attains the local square-completion bound. -/
theorem localMinimum_attains (O : Ω → Rotation)
    (hO : ∀ ω, O ω * (O ω).transpose = 1)
    (d : ℝ) (hd : d ≠ 0) (j : Spatial) (ω : Ω) :
    (d/2)*(localMinimum O d j ω ⬝ᵥ localMinimum O d j ω) -
      j ⬝ᵥ (O ω *ᵥ localMinimum O d j ω) = -(j ⬝ᵥ j)/(2*d) := by
  rw [local_action_split (O ω) (hO ω) d hd]
  simp [localMinimum, neg_div]

#print axioms source_pairing
#print axioms local_action_split
#print axioms local_action_minimum
#print axioms minimum_readout
#print axioms localMinimum_attains
end
end PDTCurrentFrame
