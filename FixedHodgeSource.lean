module
public import FixedHodgeSymmetry
public import EinsteinStressSource

@[expose] public section
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
namespace PDTFixedHodgeSource
noncomputable section
open PDTExteriorAction PDTPfaffianCubic PDTHodgeReference PDTFixedHodgeSymmetry
open PDTSignedTransport PDTStressTensor PDTResponseBridge PDTEinsteinStressSource
open scoped Matrix

/-- Exact action on all fifteen original register coordinates. -/
theorem action_diagonal : action=Matrix.diagonal
    (fun p : I => if p=3 ∨ p=7 ∨ p=10 ∨ p=12 ∨ p=14 then (1 : ℝ) else -1) := by
  rw [action,signedLift,complement_det,neg_one_smul]
  ext r c
  fin_cases r <;> fin_cases c <;>
    norm_num [lift,complementReflection,ia,ib,Matrix.diagonal_apply] <;> simp +decide

/-- The actual six electromagnetic components all change sign. -/
theorem field_action (v : V) : field (action *ᵥ v)= -field v := by
  rw [action_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [field,Matrix.mulVec_diagonal] <;> simp +decide

theorem stress_neg (d : ℝ) (F : Tensor) : stress d (-F)=stress d F := by
  ext i j
  simp only [stress,invariant,PDTMaxwellSymbol.mink,Matrix.neg_apply]
  ring

theorem register_stress_action (d : ℝ) (v : V) :
    registerStress d (action *ᵥ v)=registerStress d v := by
  unfold registerStress
  rw [field_action,stress_neg]

/-- The tensor used in the existing Einstein source is unchanged for every register. -/
theorem gravitational_stress_action (d : ℝ) (v : V) :
    gravitationalStress d (action *ᵥ v)=gravitationalStress d v := by
  unfold gravitationalStress
  rw [register_stress_action]

theorem field_action_nontrivial :
    field (action *ᵥ (Pi.single 0 1 : V)) ≠ field (Pi.single 0 1 : V) := by
  rw [field_action]
  intro h
  have he := congrArg (fun F : Tensor => F 0 1) h
  norm_num [field] at he

/-- Even with this fixed geometric structure, the source tensor alone cannot recover field sign. -/
theorem no_field_decoder (d : ℝ) : ¬ ∃ decode : Tensor → Tensor,
    ∀ v : V, decode (gravitationalStress d v)=field v := by
  rintro ⟨decode,hd⟩
  have h := congrArg decode (gravitational_stress_action d (Pi.single 0 1))
  rw [hd,hd] at h
  exact field_action_nontrivial h

#print axioms action_diagonal
#print axioms field_action
#print axioms stress_neg
#print axioms register_stress_action
#print axioms gravitational_stress_action
#print axioms field_action_nontrivial
#print axioms no_field_decoder
end
end PDTFixedHodgeSource
