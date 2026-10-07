module
public import GravityScreening.ObserverGaugeIntegration

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! A variational realization of inclusive response integration.
The physical interpretation of the orientation-indexed amplitudes is explicit:
this is an auxiliary-channel action, not a derivation of new photon species.
All analytic theorems concern a positive scalar quadratic mode. -/
namespace PDTBoundaryAction
noncomputable section
open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]
variable (μ : Measure Ω) [IsFiniteMeasure μ]

def mass : ℝ := μ.real Set.univ
def total (f : Ω → ℝ) : ℝ := ∫ x, f x ∂μ
def energy (d : ℝ) (f : Ω → ℝ) : ℝ := (d / 2) * ∫ x, (f x)^2 ∂μ
def sourcedEnergy (d j : ℝ) (f : Ω → ℝ) : ℝ :=
  energy μ d f - j * total μ f

omit [IsFiniteMeasure μ] in
theorem total_const (a : ℝ) : total μ (fun _ => a) = mass μ * a := by
  simp [total, mass, integral_const, smul_eq_mul]

theorem integrable_shift_sq (f : Ω → ℝ) (hf : Integrable f μ)
    (hf2 : Integrable (fun x => (f x)^2) μ) (c : ℝ) :
    Integrable (fun x => (f x - c)^2) μ := by
  have h := (hf2.sub (hf.const_mul (2*c))).add (integrable_const (c^2))
  have hp : (fun x => (f x-c)^2) =
      ((fun x => (f x)^2) - (fun x => (2*c)*f x) + (fun _ => c^2)) := by
    funext x
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  rw [hp]
  exact h

theorem integral_shift_sq (f : Ω → ℝ) (hf : Integrable f μ)
    (hf2 : Integrable (fun x => (f x)^2) μ) (c : ℝ) :
    (∫ x, (f x - c)^2 ∂μ) =
      (∫ x, (f x)^2 ∂μ) - 2*c*total μ f + mass μ*c^2 := by
  have hp : (fun x => (f x-c)^2) =
      (fun x => (f x)^2 - (2*c)*f x + c^2) := by
    funext x
    ring
  rw [hp]
  have hs : Integrable (fun x => (f x)^2 - (2*c)*f x) μ :=
    hf2.sub (hf.const_mul (2*c))
  rw [integral_add hs (integrable_const _),
    integral_sub hf2 (hf.const_mul (2*c)), integral_const_mul, integral_const]
  simp [total, mass, smul_eq_mul]

/-- Exact action decomposition for a fixed inclusive amplitude A. -/
theorem fixed_total_energy_split (d A : ℝ) (hB : mass μ ≠ 0)
    (f : Ω → ℝ) (hf : Integrable f μ)
    (hf2 : Integrable (fun x => (f x)^2) μ) (hA : total μ f = A) :
    energy μ d f = d/(2*mass μ)*A^2 +
      (d/2)*(∫ x, (f x - A/mass μ)^2 ∂μ) := by
  rw [integral_shift_sq μ f hf hf2, hA]
  unfold energy
  field_simp [hB]
  ring

/-- The inclusive field has effective stiffness d/B, with an attained minimum. -/
theorem fixed_total_minimum (d A : ℝ) (hd : 0 ≤ d) (hB : 0 < mass μ)
    (f : Ω → ℝ) (hf : Integrable f μ)
    (hf2 : Integrable (fun x => (f x)^2) μ) (hA : total μ f = A) :
    d/(2*mass μ)*A^2 ≤ energy μ d f ∧
    total μ (fun _ => A/mass μ) = A ∧
    energy μ d (fun _ => A/mass μ) = d/(2*mass μ)*A^2 := by
  have hBn : mass μ ≠ 0 := ne_of_gt hB
  refine ⟨?_, ?_, ?_⟩
  · rw [fixed_total_energy_split μ d A hBn f hf hf2 hA]
    have hi : 0 ≤ ∫ x, (f x - A/mass μ)^2 ∂μ :=
      integral_nonneg (fun _ => sq_nonneg _)
    exact le_add_of_nonneg_right (mul_nonneg (by positivity) hi)
  · rw [total_const]
    field_simp [hBn]
  · simp only [energy, integral_const, smul_eq_mul]
    change d/2 * (mass μ * (A/mass μ)^2) = _
    field_simp [hBn]

/-- The source couples to the inclusive amplitude, with no change of j.
The minimum is -B*j^2/(2d), so its susceptibility is B/d. -/
theorem sourced_energy_split (d j : ℝ) (hd : d ≠ 0)
    (f : Ω → ℝ) (hf : Integrable f μ)
    (hf2 : Integrable (fun x => (f x)^2) μ) :
    sourcedEnergy μ d j f =
      (d/2)*(∫ x, (f x-j/d)^2 ∂μ) - mass μ*j^2/(2*d) := by
  rw [integral_shift_sq μ f hf hf2]
  unfold sourcedEnergy energy
  field_simp [hd]
  ring

theorem sourced_minimizer (d j : ℝ) (hd : 0 < d)
    (f : Ω → ℝ) (hf : Integrable f μ)
    (hf2 : Integrable (fun x => (f x)^2) μ) :
    -mass μ*j^2/(2*d) ≤ sourcedEnergy μ d j f ∧
    sourcedEnergy μ d j (fun _ => j/d) = -mass μ*j^2/(2*d) ∧
    total μ (fun _ => j/d) = mass μ*j/d := by
  have hdn : d ≠ 0 := ne_of_gt hd
  refine ⟨?_, ?_, ?_⟩
  · rw [sourced_energy_split μ d j hdn f hf hf2]
    have hi : 0 ≤ ∫ x, (f x-j/d)^2 ∂μ :=
      integral_nonneg (fun _ => sq_nonneg _)
    have := mul_nonneg (show 0 ≤ d/2 by positivity) hi
    simpa only [zero_add, add_zero, add_comm, sub_eq_add_neg, neg_mul, neg_div] using
      add_le_add_right this (-(mass μ*j^2/(2*d)))
  · rw [sourced_energy_split μ d j hdn _ (integrable_const _) (integrable_const _)]
    simp
    ring
  · rw [total_const]
    ring

/-- With positive stiffness the minimizing channel amplitude is unique a.e. -/
theorem sourced_minimum_iff (d j : ℝ) (hd : 0 < d)
    (f : Ω → ℝ) (hf : Integrable f μ)
    (hf2 : Integrable (fun x => (f x)^2) μ) :
    sourcedEnergy μ d j f = -mass μ*j^2/(2*d) ↔
      f =ᵐ[μ] (fun _ => j/d) := by
  rw [sourced_energy_split μ d j (ne_of_gt hd) f hf hf2]
  have hz : ((d/2)*(∫ x, (f x-j/d)^2 ∂μ) - mass μ*j^2/(2*d) =
      -mass μ*j^2/(2*d)) ↔ (∫ x, (f x-j/d)^2 ∂μ) = 0 := by
    constructor <;> intro h
    · have hp : 0 < d/2 := by positivity
      have hm : (d/2)*(∫ x, (f x-j/d)^2 ∂μ) = 0 := by
        linear_combination h
      exact (mul_eq_zero.mp hm).resolve_left (ne_of_gt hp)
    · rw [h]
      ring
  rw [hz, integral_eq_zero_iff_of_nonneg (fun _ => sq_nonneg _)
    (integrable_shift_sq μ f hf hf2 (j/d))]
  constructor
  · intro h
    filter_upwards [h] with x hx
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hx)
  · intro h
    filter_upwards [h] with x hx
    simp [hx]

omit [IsFiniteMeasure μ] in
/-- The same-channel/common-field convention instead gives stiffness B*d. -/
theorem common_field_energy (d a : ℝ) :
    energy μ d (fun _ => a) = (mass μ*d)/2*a^2 := by
  simp [energy, integral_const, smul_eq_mul, mass]
  ring

/-- Exact source-normalized scalar equation for the effective inclusive field. -/
theorem inclusive_stationary_iff (B d j A : ℝ) (hB : B ≠ 0) (hd : d ≠ 0) :
    (d/B)*A = j ↔ A = B*j/d := by
  constructor <;> intro h <;> field_simp [hB, hd] at h ⊢ <;> nlinarith [h]

/-- One action coefficient is fixed after the inclusive rule and boundary
mass are supplied. This does not derive that rule from observer gauge freedom. -/
theorem pdt_stiffness (r : ℝ) :
    (r^15/(4*Real.pi))/GravityScreening.projectiveBoundaryVolume =
      r^15/(4*Real.pi^3) := by
  rw [GravityScreening.projectiveBoundaryVolume_eq_pi_sq]
  field_simp

omit [IsFiniteMeasure μ] in
/-- Relabeling observer orientations preserves both the action and its
inclusive source term for a left-invariant measure. -/
theorem observer_relabeling_invariant [Group Ω] [MeasurableMul Ω]
    [μ.IsMulLeftInvariant] (g : Ω) (d j : ℝ) (f : Ω → ℝ) :
    sourcedEnergy μ d j (fun x => f (g*x)) = sourcedEnergy μ d j f := by
  unfold sourcedEnergy energy total
  rw [integral_mul_left_eq_self (fun x => (f x)^2) g,
    integral_mul_left_eq_self f g]

#print axioms fixed_total_minimum
#print axioms sourced_minimizer
#print axioms sourced_minimum_iff
#print axioms common_field_energy
#print axioms inclusive_stationary_iff
#print axioms pdt_stiffness
#print axioms observer_relabeling_invariant
end
end PDTBoundaryAction
