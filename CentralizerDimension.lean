module
public import ReferenceCentralizer

@[expose] public section
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
namespace PDTCentralizerDimension
noncomputable section
open PDTPfaffianCubic PDTHessianCovariance PDTStabilizerTests PDTJointStabilizer
open PDTReferenceCentralizer
open scoped Matrix

abbrev Params := Fin 7 → ℝ
def extend (c : Params) : I → ℝ := ![c 0,c 1,c 2,0,0,c 3,c 4,0,0,c 5,0,0,0,0,c 6]
def restrict (w : I → ℝ) : Params := ![w 0,w 1,w 2,w 5,w 6,w 9,w 14]

theorem restrict_extend (c : Params) : restrict (extend c)=c := by
  ext i
  fin_cases i <;> simp [restrict,extend]

theorem extend_injective : Function.Injective extend :=
  Function.LeftInverse.injective restrict_extend

theorem extend_no_mixing (c : Params) : NoMixing (extend c) := by
  simp [NoMixing,extend]

theorem extend_restrict (w : I → ℝ) (hw : NoMixing w) : extend (restrict w)=w := by
  rcases hw with ⟨h3,h4,h7,h8,h10,h11,h12,h13⟩
  ext i
  fin_cases i <;> simp [extend,restrict,h3,h4,h7,h8,h10,h11,h12,h13]

def extendMap : Params →ₗ[ℝ] (I → ℝ) where
  toFun := extend
  map_add' c d := by ext i; fin_cases i <;> simp [extend]
  map_smul' a c := by ext i; fin_cases i <;> simp [extend]

def parameterMap : Params →ₗ[ℝ] Mat := geometricMap.comp extendMap

theorem parameter_injective : Function.Injective parameterMap :=
  PDTStabilizerRecovery.connection_injective.comp extend_injective

def Qualifies (A : Mat) : Prop :=
  MetricSkew A ∧ CubicInvariant A ∧ A*PDTHodgeConnection.H=PDTHodgeConnection.H*A

theorem parameter_qualifies (c : Params) : Qualifies (parameterMap c) := by
  refine ⟨connection_metric _,connection_invariance ℝ _,?_⟩
  exact (connection_commutes_iff _).mpr (extend_no_mixing c)

theorem classification (A : Mat) : Qualifies A ↔ ∃ c : Params, A=parameterMap c := by
  constructor
  · rintro ⟨hm,hc,hh⟩
    have ha := joint_reconstruction A hm hc
    have hn : NoMixing (PDTStabilizerRecovery.decode A) := by
      apply (connection_commutes_iff _).mp
      simpa only [← ha] using hh
    refine ⟨restrict (PDTStabilizerRecovery.decode A),?_⟩
    change A=connection ℝ (extend (restrict (PDTStabilizerRecovery.decode A)))
    rw [extend_restrict _ hn]
    exact ha
  · rintro ⟨c,rfl⟩
    exact parameter_qualifies c

theorem unique_parameters (A : Mat) (hA : Qualifies A) : ∃! c : Params, A=parameterMap c := by
  obtain ⟨c,hc⟩ := (classification A).mp hA
  refine ⟨c,hc,?_⟩
  intro d hd
  exact parameter_injective (hd.symm.trans hc)

def hodgeCommutator : Mat →ₗ[ℝ] Mat where
  toFun A := A*PDTHodgeConnection.H-PDTHodgeConnection.H*A
  map_add' A B := by
    simp only [Matrix.add_mul,Matrix.mul_add]
    abel
  map_smul' c A := by
    simp only [Matrix.smul_mul,Matrix.mul_smul,smul_sub]
    rfl

def fixedSpace : Submodule ℝ Mat := jointStabilizer ⊓ LinearMap.ker hodgeCommutator

theorem mem_fixedSpace (A : Mat) : A ∈ fixedSpace ↔ Qualifies A := by
  change (MetricSkew A ∧ CubicInvariant A) ∧
    A*PDTHodgeConnection.H-PDTHodgeConnection.H*A=0 ↔ Qualifies A
  simp only [Qualifies,sub_eq_zero,and_assoc]

theorem fixedSpace_eq_range : fixedSpace=LinearMap.range parameterMap := by
  ext A
  rw [mem_fixedSpace,classification]
  simp only [LinearMap.mem_range]
  exact exists_congr (fun _ => eq_comm)

theorem fixedSpace_finrank : Module.finrank ℝ fixedSpace=7 := by
  rw [fixedSpace_eq_range,LinearMap.finrank_range_of_inj parameter_injective]
  simp [Params]

#print axioms restrict_extend
#print axioms extend_injective
#print axioms extend_no_mixing
#print axioms extend_restrict
#print axioms parameter_injective
#print axioms parameter_qualifies
#print axioms classification
#print axioms unique_parameters
#print axioms mem_fixedSpace
#print axioms fixedSpace_eq_range
#print axioms fixedSpace_finrank
end
end PDTCentralizerDimension
