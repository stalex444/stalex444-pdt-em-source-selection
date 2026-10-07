module
public import CentralizerSplit

@[expose] public section
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
namespace PDTEMActionKernel
noncomputable section
open PDTPfaffianCubic PDTHessianCovariance PDTCentralizerDimension PDTCentralizerSplit
open PDTStabilizerTests
open PDTStressTensor
open scoped Matrix

abbrev V := PDTResponseBridge.V
abbrev Action := V → Tensor
def action (A : Mat) : Action := fun v => field (A *ᵥ v)

theorem field_add (v w : V) : field (v+w)=field v+field w := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [field,add_comm]

theorem field_smul (a : ℝ) (v : V) : field (a • v)=a • field v := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [field,mul_neg]

theorem field_zero : field (0 : V)=0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [field]

theorem action_add (A B : Mat) : action (A+B)=action A+action B := by
  funext v
  exact (congrArg field (Matrix.add_mulVec A B v)).trans (field_add _ _)

theorem action_smul (a : ℝ) (A : Mat) : action (a • A)=a • action A := by
  funext v
  simp only [action,Matrix.smul_mulVec,field_smul,Pi.smul_apply]

theorem action_complement : action complement=0 := by
  funext v
  exact complement_field_zero v

theorem action_split (u : Fin 6 → ℝ) (a : ℝ) :
    action (physical u+a • complement)=action (physical u) := by
  rw [action_add,action_smul,action_complement,smul_zero,add_zero]

/-- Six scalar readings of the response to four specified local basis inputs. -/
def probes (f : Action) : Fin 6 → ℝ :=
  ![f (Pi.single 5 1) 0 2, -f (Pi.single 5 1) 0 1,
    f (Pi.single 6 1) 0 1, f (Pi.single 1 1) 0 1,
    -f (Pi.single 2 1) 0 1, -f (Pi.single 2 1) 0 2]

theorem probes_zero : probes (0 : Action)=0 := by
  ext i
  fin_cases i <;> simp [probes]

theorem probes_decode (A : Mat) (i : Fin 6) :
    probes (action A) i=PDTStabilizerRecovery.decode A (localIndex i) := by
  fin_cases i <;>
    simp [probes,action,field,
      PDTStabilizerRecovery.decode,localIndex]

theorem recover_split (u : Fin 6 → ℝ) (a : ℝ) :
    probes (action (physical u+a • complement))=u := by
  ext i
  rw [probes_decode,← joined_split]
  change PDTStabilizerRecovery.decode (connection ℝ (extend (join u a))) (localIndex i)=u i
  rw [PDTStabilizerRecovery.decode_connection]
  fin_cases i <;> rfl

theorem recover_physical (u : Fin 6 → ℝ) : probes (action (physical u))=u := by
  simpa only [zero_smul,add_zero] using recover_split u 0

theorem physical_action_injective : Function.Injective (fun u => action (physical u)) :=
  Function.LeftInverse.injective recover_physical

theorem physical_zero : physical (0 : Fin 6 → ℝ)=0 := by
  simp [physical]

theorem action_zero : action (0 : Mat)=0 := by
  funext v
  simp [action,field_zero]

/-- Within the full fixed-Hodge stabilizer, this is exactly the all-field kernel. -/
theorem invisible_iff (A : Mat) (hA : Qualifies A) :
    action A=0 ↔ ∃ a : ℝ, A=a • complement := by
  constructor
  · intro hz
    obtain ⟨⟨u,a⟩,ha,_⟩ := unique_split A hA
    have hu : u=0 := by
      have hp := congrArg probes hz
      rw [ha,recover_split,probes_zero] at hp
      exact hp
    exact ⟨a,by simpa only [hu,physical_zero,zero_add] using ha⟩
  · rintro ⟨a,rfl⟩
    rw [action_smul,action_complement,smul_zero]

theorem all_fields_iff (A : Mat) (hA : Qualifies A) :
    (∀ v : V, field (A *ᵥ v)=0) ↔ ∃ a : ℝ, A=a • complement := by
  rw [← invisible_iff A hA]
  exact ⟨fun h => funext h,fun h v => congrFun h v⟩

/-- The six scalar probes suffice under the preservation hypotheses. -/
theorem finite_probe_iff (A : Mat) (hA : Qualifies A) :
    probes (action A)=0 ↔ action A=0 := by
  obtain ⟨⟨u,a⟩,rfl,_⟩ := unique_split A hA
  rw [recover_split,action_split]
  constructor
  · rintro rfl
    rw [physical_zero,action_zero]
  · intro h
    have hp := congrArg probes h
    simpa only [recover_physical,probes_zero] using hp

def physicalActionMap : (Fin 6 → ℝ) →ₗ[ℝ] Action where
  toFun u := action (physical u)
  map_add' u v := by
    change action (physicalMap (u+v))=action (physicalMap u)+action (physicalMap v)
    rw [map_add,action_add]
  map_smul' a u := by
    change action (physicalMap (a • u))=a • action (physicalMap u)
    rw [map_smul,action_smul]

theorem visible_action_finrank :
    Module.finrank ℝ (LinearMap.range physicalActionMap)=6 := by
  rw [LinearMap.finrank_range_of_inj (f := physicalActionMap) physical_action_injective]
  simp

theorem same_action_iff (u v : Fin 6 → ℝ) (a b : ℝ) :
    action (physical u+a • complement)=action (physical v+b • complement) ↔ u=v := by
  rw [action_split,action_split]
  exact physical_action_injective.eq_iff

theorem reconstruct_action (A : Mat) (hA : Qualifies A) :
    action A=action (physical (probes (action A))) := by
  obtain ⟨⟨u,a⟩,rfl,_⟩ := unique_split A hA
  rw [recover_split,action_split]

theorem physical_qualifies (u : Fin 6 → ℝ) : Qualifies (physical u) := by
  simpa only [joined_split,zero_smul,add_zero] using parameter_qualifies (join u 0)

theorem physical_single (i : Fin 6) :
    physical (Pi.single i 1)=PDTCubicInvariance.generator ℝ (localIndex i) := by
  simp [physical]

/-- A nonzero field can be fixed by a transformation which is visible on other fields. -/
theorem fixed_field_control : ∃ A : Mat, ∃ v : V,
    Qualifies A ∧ field v ≠ 0 ∧ field (A *ᵥ v)=0 ∧ action A ≠ 0 := by
  refine ⟨physical (Pi.single 0 1),Pi.single 0 1,physical_qualifies _,?_,?_,?_⟩
  · intro h
    have he := congrArg (fun F : Tensor => F 0 1) h
    change (1 : ℝ)=0 at he
    norm_num at he
  · have hc : ∀ i : I,
        GravityScreening.ResponseClosureGeometry.geometricAdjoint 0 i 0=0 := by
      decide +kernel
    rw [physical_single]
    have hv : PDTCubicInvariance.generator ℝ (localIndex 0) *ᵥ
        (Pi.single 0 1 : V)=0 := by
      rw [Matrix.mulVec_single_one]
      ext i
      change (GravityScreening.ResponseClosureGeometry.geometricAdjoint 0 i 0 : ℝ)=0
      rw [hc,Int.cast_zero]
    rw [hv,field_zero]
  · intro h
    have hp := congrArg probes h
    rw [recover_physical,probes_zero] at hp
    have he := congrFun hp 0
    change (1 : ℝ)=0 at he
    norm_num at he

#print axioms field_add
#print axioms field_smul
#print axioms field_zero
#print axioms action_add
#print axioms action_smul
#print axioms action_complement
#print axioms action_split
#print axioms probes_zero
#print axioms probes_decode
#print axioms recover_split
#print axioms recover_physical
#print axioms physical_action_injective
#print axioms physical_zero
#print axioms action_zero
#print axioms invisible_iff
#print axioms all_fields_iff
#print axioms finite_probe_iff
#print axioms visible_action_finrank
#print axioms same_action_iff
#print axioms reconstruct_action
#print axioms physical_qualifies
#print axioms physical_single
#print axioms fixed_field_control
end
end PDTEMActionKernel
