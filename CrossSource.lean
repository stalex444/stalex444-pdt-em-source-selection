module
public import LinearSourceData

@[expose] public section
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
namespace PDTPolynomialSource
noncomputable section
open PDTStressTensor PDTUnrestrictedSourceKernel PDTQuadraticSource PDTConservedSource
open scoped Matrix

/-- The allowed linear source is the bilinear stress cross term with a fixed field. -/
theorem cross_original_variation (b x : Local) :
    linear (crossCoefficients b) x=PDTStressBalance.firstVariation 1 (embed b) (embed x) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [linear,crossCoefficients,tensorIndex,Fin.sum_univ_succ,
      PDTStressBalance.firstVariation,PDTStressBalance.crossInvariant,field,embed,
      PDTMaxwellSymbol.mink,metric,eta,Matrix.diagonal_apply] <;> (try dsimp) <;> norm_num <;> ring

theorem cross_stress_increment (b x : Local) :
    registerStress 1 (embed (b+x))=registerStress 1 (embed b)+
      linear (crossCoefficients b) x+registerStress 1 (embed x) := by
  have h := PDTStressBalance.exact_stress_increment 1 (embed b) (embed x) 1
  have he : embed (b+x)=embed b+embed x := by
    simpa only [one_smul] using embed_affine b x 1
  simpa only [he,one_smul,one_pow,← cross_original_variation] using h

theorem cross_conserved (b : Local) : LinearConserved (crossCoefficients b) := by
  intro D hD
  have hh := original_conserved 1 b D hD
  rw [original_divergence] at hh
  convert hh using 1
  funext ν
  unfold linearDivergence PDTStressBalance.stressDivergence
  apply Finset.sum_congr rfl
  intro μ _
  exact congrFun (congrFun (cross_original_variation b (D μ)) μ) ν

theorem cross_zero : crossCoefficients 0=0 := by
  ext t a
  fin_cases t <;> fin_cases a <;> norm_num [crossCoefficients]

theorem background_cross (b : Local) : background (crossCoefficients b)=b := by
  ext a
  fin_cases a <;> simp [background,crossCoefficients]

#print axioms cross_original_variation
#print axioms cross_stress_increment
#print axioms cross_conserved
#print axioms cross_zero
#print axioms background_cross
end
end PDTPolynomialSource
