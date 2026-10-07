module
public import UnrestrictedSourceKernel

@[expose] public section
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
namespace PDTUnrestrictedSourceKernel
noncomputable section
open PDTStressTensor PDTStressBalance
open scoped Matrix

theorem extract_embed (x : Local) : extract (embed x)=x := by
  ext i
  fin_cases i <;> simp [extract,embed]

theorem local_hodge_field (x : Local) :
    field (embed (J *ᵥ x))=field (PDTHodgeConnection.H *ᵥ embed x) := by
  rw [field_actual_hodge]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [field,embed,J,dualField,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]

theorem local_hodge_actual (x : Local) :
    extract (PDTHodgeConnection.H *ᵥ embed x)=J *ᵥ x := by
  have h := local_hodge_field x
  have h0 := congrArg (fun F : Tensor => F 0 1) h
  have h1 := congrArg (fun F : Tensor => F 0 2) h
  have h2 := congrArg (fun F : Tensor => F 0 3) h
  have h3 := congrArg (fun F : Tensor => F 1 2) h
  have h4 := congrArg (fun F : Tensor => F 1 3) h
  have h5 := congrArg (fun F : Tensor => F 2 3) h
  ext i
  fin_cases i <;> simp_all [extract,embed,field]

theorem local_hodge_square : J*J= -(1 : End) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [J,Matrix.mul_apply,Fin.sum_univ_succ,Matrix.one_apply]

theorem local_hodge_nonzero : J≠0 := by
  intro h
  have hh := congrArg (fun A : End => A 0 5) h
  change (-1 : ℝ)=0 at hh
  norm_num at hh

theorem response_hasDerivAt (d : ℝ) (D : End) (x : Local) (i j : Fin 4) :
    HasDerivAt (fun t : ℝ => registerStress d (embed x+t • embed (D *ᵥ x)) i j)
      (response d D x i j) 0 := firstVariation_hasDerivAt _ _ _ _ _

theorem response_scale (d : ℝ) (D : End) (x : Local) :
    response d D x=d • response 1 D x := by
  ext i j
  simp [response,firstVariation]

theorem response_add (d : ℝ) (A B : End) (x : Local) :
    response d (A+B) x=response d A x+response d B x := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [response,firstVariation,crossInvariant,embed,field,Matrix.add_mulVec,
      metric,eta,Matrix.diagonal,PDTMaxwellSymbol.mink] <;> ring

theorem response_smul (d a : ℝ) (D : End) (x : Local) :
    response d (a • D) x=a • response d D x := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [response,firstVariation,crossInvariant,embed,field,Matrix.smul_mulVec,
      metric,eta,Matrix.diagonal,PDTMaxwellSymbol.mink] <;> ring

theorem nonzero_scale_kernel (d : ℝ) (hd : d≠0) (D : End) :
    Invisible d D ↔ Invisible 1 D := by
  unfold Invisible
  apply forall_congr'
  intro x
  rw [response_scale d D x,smul_eq_zero]
  simp [hd]

theorem hodge_invisible (d : ℝ) : Invisible d J := by
  intro x
  have h := congrFun (PDTSourceActionKernel.hodge_source_zero d) (embed x)
  change firstVariation d (embed x) (PDTHodgeConnection.H *ᵥ embed x)=0 at h
  change firstVariation d (embed x) (embed (J *ᵥ x))=0
  have he : firstVariation d (embed x) (embed (J *ᵥ x))=
      firstVariation d (embed x) (PDTHodgeConnection.H *ᵥ embed x) := by
    unfold firstVariation crossInvariant
    rw [local_hodge_field]
  exact he.trans h

theorem scalar_hodge_invisible (d a : ℝ) : Invisible d (a • J) := by
  intro x
  rw [response_smul,hodge_invisible d x,smul_zero]

theorem invisible_probes (D : End) (h : Invisible 1 D) : probes D=0 := by
  unfold Invisible at h
  ext k
  fin_cases k <;> simp [probes,h]

theorem finite_certificate (D : End) : probes D=0 ↔ Invisible 1 D := by
  constructor
  · intro h
    rw [finite_reconstruction D h]
    exact scalar_hodge_invisible _ _
  · exact invisible_probes D

/-- Every real matrix on the six original components is covered: no geometric qualification. -/
theorem universal_kernel (d : ℝ) (hd : d≠0) (D : End) :
    Invisible d D ↔ ∃ a : ℝ, D=a • J := by
  rw [nonzero_scale_kernel d hd]
  constructor
  · intro h
    exact ⟨-D 0 5,finite_reconstruction D (invisible_probes D h)⟩
  · rintro ⟨a,rfl⟩
    exact scalar_hodge_invisible _ _

def phaseMap : ℝ →ₗ[ℝ] End where
  toFun a := a • J
  map_add' a b := add_smul a b J
  map_smul' a b := by simp [smul_smul]

theorem phase_injective : Function.Injective phaseMap := by
  intro a b h
  have hh := congrArg (fun D : End => D 0 5) h
  change a * (-1)=b * (-1) at hh
  linarith

theorem unique_phase (d : ℝ) (hd : d≠0) (D : End) (h : Invisible d D) :
    ∃! a : ℝ, D=a • J := by
  obtain ⟨a,ha⟩ := (universal_kernel d hd D).mp h
  refine ⟨a,ha,?_⟩
  intro b hb
  exact phase_injective (hb.symm.trans ha)

def responseMap : End →ₗ[ℝ] (Local → Tensor) where
  toFun D := response 1 D
  map_add' A B := by funext x; exact response_add _ _ _ _
  map_smul' a D := by funext x; exact response_smul _ _ _ _

theorem kernel_eq_phase_range : LinearMap.ker responseMap=LinearMap.range phaseMap := by
  ext D
  change (response 1 D=0) ↔ ∃ a : ℝ, a • J=D
  rw [funext_iff]
  change Invisible 1 D ↔ ∃ a : ℝ, a • J=D
  rw [universal_kernel 1 one_ne_zero]
  exact exists_congr (fun _ => eq_comm)

theorem kernel_finrank : Module.finrank ℝ (LinearMap.ker responseMap)=1 := by
  rw [kernel_eq_phase_range,LinearMap.finrank_range_of_inj phase_injective]
  simp

/-- One fixed field does not constrain an arbitrary linear map on other fields. -/
def fixedFieldMap : End := Matrix.single 0 1 1

theorem fixed_field_control : response 1 fixedFieldMap (Pi.single 0 1)=0 ∧
    ¬Invisible 1 fixedFieldMap := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [response,fixedFieldMap,Matrix.mulVec,dotProduct,
      Matrix.single,embed,field,firstVariation,crossInvariant,PDTMaxwellSymbol.mink]
  · intro h
    obtain ⟨a,ha⟩ := (universal_kernel 1 one_ne_zero fixedFieldMap).mp h
    have hh := congrArg (fun D : End => D 0 1) ha
    norm_num [fixedFieldMap,Matrix.single,J] at hh

theorem zero_coupling_control (D : End) : Invisible 0 D := by
  intro x
  rw [response_scale,zero_smul]

theorem magnitude_change_control : ¬Invisible 1 (1 : End) := by
  intro h
  obtain ⟨a,ha⟩ := (universal_kernel 1 one_ne_zero (1 : End)).mp h
  have hh := congrArg (fun D : End => D 0 0) ha
  change (1 : ℝ)=a*0 at hh
  norm_num at hh


#print axioms extract_embed
#print axioms local_hodge_field
#print axioms local_hodge_actual
#print axioms local_hodge_square
#print axioms local_hodge_nonzero
#print axioms response_hasDerivAt
#print axioms response_scale
#print axioms response_add
#print axioms response_smul
#print axioms nonzero_scale_kernel
#print axioms hodge_invisible
#print axioms scalar_hodge_invisible
#print axioms invisible_probes
#print axioms finite_certificate
#print axioms universal_kernel
#print axioms phase_injective
#print axioms unique_phase
#print axioms kernel_eq_phase_range
#print axioms kernel_finrank
#print axioms fixed_field_control
#print axioms zero_coupling_control
#print axioms magnitude_change_control
end
end PDTUnrestrictedSourceKernel
