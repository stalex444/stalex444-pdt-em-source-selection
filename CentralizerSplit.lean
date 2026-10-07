module
public import CentralizerDimension

@[expose] public section
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
namespace PDTCentralizerSplit
noncomputable section
open PDTPfaffianCubic PDTCubicInvariance PDTHessianCovariance PDTStabilizerTests
open PDTCentralizerDimension GravityScreening.ResponseClosureCertificate
open GravityScreening.ResponseClosureGeometry
open scoped Matrix

def localIndex : Fin 6 → I := ![0,1,2,5,6,9]
def join (u : Fin 6 → ℝ) (a : ℝ) : Params := ![u 0,u 1,u 2,u 3,u 4,u 5,a]
def physical (u : Fin 6 → ℝ) : Mat := ∑ i : Fin 6, u i • generator ℝ (localIndex i)
def complement : Mat := generator ℝ 14

theorem local_indices : ∀ p : I, LocalPair p ↔ ∃ i : Fin 6, localIndex i=p := by
  decide +kernel

theorem complementary_ambient : orthogonalGenerator 14=
    -(Matrix.single 4 5 (1 : ℤ))-Matrix.single 5 4 1 := by
  decide +kernel

theorem joined_split (u : Fin 6 → ℝ) (a : ℝ) :
    parameterMap (join u a)=physical u+a • complement := by
  change connection ℝ (extend (join u a))= _
  norm_num [connection,extend,join,physical,complement,localIndex,Fin.sum_univ_succ,Fin.succ]
  change u 0 • generator ℝ 0 + (u 1 • generator ℝ 1 +
    (u 2 • generator ℝ 2 + (u 3 • generator ℝ 5 +
    (u 4 • generator ℝ 6 + (u 5 • generator ℝ 9 + a • generator ℝ 14))))) =
    (u 0 • generator ℝ 0 + (u 1 • generator ℝ 1 +
    (u 2 • generator ℝ 2 + (u 3 • generator ℝ 5 +
    (u 4 • generator ℝ 6 + u 5 • generator ℝ 9))))) + a • generator ℝ 14
  abel

theorem unique_split (A : Mat) (hA : Qualifies A) :
    ∃! ua : (Fin 6 → ℝ) × ℝ, A=physical ua.1+ua.2 • complement := by
  obtain ⟨c,hc,_⟩ := unique_parameters A hA
  let u : Fin 6 → ℝ := fun i => c i.castSucc
  have hj : join u (c 6)=c := by ext i; fin_cases i <;> rfl
  refine ⟨(u,c 6),?_,?_⟩
  · change A=physical u+c 6 • complement
    rw [← joined_split,hj]
    exact hc
  · rintro ⟨v,b⟩ hv
    rw [← joined_split] at hv
    have he := parameter_injective (hv.symm.trans hc)
    apply Prod.ext
    · ext i
      have hi := congrFun he i.castSucc
      fin_cases i <;> simpa [join,u] using hi
    · have hi := congrFun he 6
      simpa [join] using hi

theorem physical_injective : Function.Injective physical := by
  intro u v h
  have he : parameterMap (join u 0)=parameterMap (join v 0) := by
    simpa only [joined_split,zero_smul,add_zero] using h
  have hc := parameter_injective he
  ext i
  have hi := congrFun hc i.castSucc
  fin_cases i <;> simpa [join] using hi

def physicalMap : (Fin 6 → ℝ) →ₗ[ℝ] Mat where
  toFun := physical
  map_add' u v := by simp [physical,add_smul,Finset.sum_add_distrib]
  map_smul' a u := by simp [physical,smul_smul,Finset.smul_sum]

theorem physical_finrank : Module.finrank ℝ (LinearMap.range physicalMap)=6 := by
  rw [LinearMap.finrank_range_of_inj (f := physicalMap) physical_injective]
  simp

private theorem integral_commutes : ∀ i : Fin 6,
    adj 14*adj (localIndex i)=adj (localIndex i)*adj 14 := by decide +kernel

theorem complement_commutes_generator (i : Fin 6) :
    complement*generator ℝ (localIndex i)=generator ℝ (localIndex i)*complement := by
  unfold complement generator
  rw [← certificate_adjoint,← certificate_adjoint,← map_mul,← map_mul,integral_commutes]

theorem complement_commutes (u : Fin 6 → ℝ) :
    complement*physical u=physical u*complement := by
  simp only [physical,Matrix.mul_sum,Matrix.sum_mul,Matrix.mul_smul,Matrix.smul_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [complement_commutes_generator]

private theorem integral_local_bracket : ∀ i j : Fin 6,
    adj (localIndex i)*adj (localIndex j)-adj (localIndex j)*adj (localIndex i)=
      ∑ k : Fin 6, adj (localIndex i) (localIndex k) (localIndex j) • adj (localIndex k) := by
  decide +kernel

/-- The six actual local generators close under the matrix commutator. -/
theorem physical_bracket_basis (i j : Fin 6) :
    generator ℝ (localIndex i)*generator ℝ (localIndex j)-
      generator ℝ (localIndex j)*generator ℝ (localIndex i)=
        physical (fun k => (adj (localIndex i) (localIndex k) (localIndex j) : ℝ)) := by
  simp only [physical,generator]
  simp_rw [← certificate_adjoint]
  rw [← map_mul,← map_mul,← map_sub,integral_local_bracket,map_sum]
  apply Finset.sum_congr rfl
  intro k _
  ext r c
  change (((adj (localIndex i) (localIndex k) (localIndex j) •
    adj (localIndex k)) r c : ℤ) : ℝ) =
      (adj (localIndex i) (localIndex k) (localIndex j) : ℝ) *
        (adj (localIndex k) r c : ℝ)
  rw [Matrix.smul_apply,smul_eq_mul,Int.cast_mul]

theorem complement_nonzero : complement ≠ 0 := by
  intro h
  have he := congrArg (fun A : Mat => A 3 4) h
  change (geometricAdjoint 14 3 4 : ℝ)=0 at he
  rw [← certificate_adjoint] at he
  have hi : adj 14 3 4= -1 := by decide +kernel
  rw [hi] at he
  norm_num at he

theorem complement_field_zero (v : PDTResponseBridge.V) :
    PDTStressTensor.field (complement *ᵥ v)=0 := by
  have hr : ∀ i : I, LocalPair i → ∀ j : I, geometricAdjoint 14 i j=0 := by
    decide +kernel
  have hv (i : I) (hi : LocalPair i) : (complement *ᵥ v) i=0 := by
    unfold Matrix.mulVec dotProduct
    apply Finset.sum_eq_zero
    intro j _
    change (geometricAdjoint 14 i j : ℝ)*v j=0
    rw [hr i hi,Int.cast_zero,zero_mul]
  have h0 := hv 0 (by decide +kernel)
  have h1 := hv 1 (by decide +kernel)
  have h2 := hv 2 (by decide +kernel)
  have h5 := hv 5 (by decide +kernel)
  have h6 := hv 6 (by decide +kernel)
  have h9 := hv 9 (by decide +kernel)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [PDTStressTensor.field,h0,h1,h2,h5,h6,h9]

theorem complement_ne_hodge : complement ≠ PDTHodgeConnection.H := by
  intro h
  have hf := complement_field_zero (Pi.single 0 1)
  rw [h,PDTStressTensor.field_actual_hodge] at hf
  have he := congrArg (fun F : PDTStressTensor.Tensor => F 2 3) hf
  change (1 : ℝ)=0 at he
  norm_num at he

#print axioms local_indices
#print axioms complementary_ambient
#print axioms joined_split
#print axioms unique_split
#print axioms physical_injective
#print axioms physical_finrank
#print axioms complement_commutes_generator
#print axioms complement_commutes
#print axioms physical_bracket_basis
#print axioms complement_nonzero
#print axioms complement_field_zero
#print axioms complement_ne_hodge
end
end PDTCentralizerSplit
