module
public import SmoothConsequences
public import EinsteinStressSource

@[expose] public section
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
namespace PDTSourcefulSelection
noncomputable section
open PDTStressTensor PDTUnrestrictedSourceKernel PDTQuadraticSource PDTConservedSource PDTPolynomialSource PDTSmoothSource PDTStressBalance
open scoped Matrix

/-- The original exchange law with a supplied Maxwell stiffness k and arbitrary
Bianchi-compatible first jets, including nonzero currents. -/
def ExchangeLaw (k : ℝ) (S : Local → Tensor) : Prop := ∀ x D,
  bianchiJet (registerJet D) → divergence S x D=exchange (embed x) (sourcedCurrent k (registerJet D))

def currentJet : Fin 4 → Jet :=
  ![!![0,0,0,0,0,0;-1,0,0,0,0,0;0,0,0,0,0,0;0,0,0,0,0,0],
    !![1,0,0,0,0,0;0,0,0,0,0,0;0,0,0,0,0,0;0,0,0,0,0,0],
    !![0,1,0,0,0,0;0,0,0,0,0,0;0,0,0,0,0,0;0,0,0,0,0,0],
    !![0,0,1,0,0,0;0,0,0,0,0,0;0,0,0,0,0,0;0,0,0,0,0,0]]

set_option linter.unusedTactic false in
theorem current_jet_bianchi (a : Fin 4) : bianchiJet (registerJet (currentJet a)) := by
  fin_cases a <;> norm_num [bianchiJet,registerJet,currentJet,embed] <;> (try dsimp) <;> norm_num

set_option linter.unusedTactic false in
theorem current_jet_current (a : Fin 4) (k : ℝ) :
    sourcedCurrent k (registerJet (currentJet a))=k • Pi.single a 1 := by
  ext ν
  fin_cases a <;> fin_cases ν <;>
    norm_num [sourcedCurrent,registerJet,currentJet,embed,field,Fin.sum_univ_succ,Pi.single_apply] <;> (try dsimp) <;> norm_num

theorem current_coefficient (k : ℝ) (D : Jet) :
    sourcedCurrent k (registerJet D)=k • sourcedCurrent 1 (registerJet D) := by
  ext ν
  simp [sourcedCurrent]

theorem exchange_zero_current (x : Local) : exchange (embed x) 0=0 := by
  ext ν
  simp [exchange,PDTMaxwellSymbol.mink]

theorem exchange_zero_field (j : PDTMaxwellSymbol.Four) : exchange (embed 0) j=0 := by
  ext ν
  fin_cases ν <;> simp [exchange,embed,field,PDTMaxwellSymbol.mink]

theorem exchange_implies_conservation (k : ℝ) (S : Local → Tensor)
    (h : ExchangeLaw k S) : Conserved S := by
  intro x D hD
  rw [h x D hD.1,current_coefficient,hD.2,smul_zero,exchange_zero_current]

theorem family_divergence (A : ConstantCoeff) (b : Local) (d : ℝ) (x : Local) (D : Jet) :
    divergence (conservedFamily A b d) x D=
      stressDivergence 1 (embed b) (registerJet D)+stressDivergence d (embed x) (registerJet D) := by
  rw [conserved_family_polynomial,polynomial_divergence]
  funext ν
  change (∑ μ, linear (crossCoefficients b) (D μ) μ ν) +
    (∑ μ, variation (d • maxwellCoefficients) x (D μ) μ ν) = _
  simp only [cross_original_variation,maxwell_variation]
  rfl

theorem family_exchange (A : ConstantCoeff) (b : Local) (d : ℝ) (x : Local)
    (D : Jet) (hD : bianchiJet (registerJet D)) :
    divergence (conservedFamily A b d) x D=
      exchange (embed b) (sourcedCurrent 1 (registerJet D))+
        exchange (embed x) (sourcedCurrent d (registerJet D)) := by
  rw [family_divergence,stress_balance 1 (embed b) _ hD,stress_balance d (embed x) _ hD]

theorem fixed_scale_converse (A : ConstantCoeff) (k : ℝ) :
    ExchangeLaw k (conservedFamily A 0 k) := by
  intro x D hD
  rw [family_exchange A 0 k x D hD,exchange_zero_field,zero_add]

#print axioms current_jet_bianchi
#print axioms current_jet_current
#print axioms current_coefficient
#print axioms exchange_zero_current
#print axioms exchange_zero_field
#print axioms exchange_implies_conservation
#print axioms family_divergence
#print axioms family_exchange
#print axioms fixed_scale_converse
end
end PDTSourcefulSelection
