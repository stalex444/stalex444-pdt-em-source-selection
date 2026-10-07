module
public import SourceSelection
public import SourceControls
public import StressBalance

@[expose] public section
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
namespace PDTConservedSource
noncomputable section
open PDTStressTensor PDTUnrestrictedSourceKernel PDTQuadraticSource
open scoped Matrix

abbrev Jet := Fin 4 → Local

def registerJet (D : Jet) : Fin 4 → PDTResponseBridge.V := fun μ => embed (D μ)

/-- The original source-free Maxwell and raised Bianchi equations. -/
def VacuumJet (D : Jet) : Prop :=
  PDTStressBalance.bianchiJet (registerJet D) ∧
  PDTStressBalance.sourcedCurrent 1 (registerJet D)=0

/-- Actual directional derivatives of the source, contracted in its first index. -/
def divergence (S : Local → Tensor) (x : Local) (D : Jet) : Fin 4 → ℝ :=
  fun ν => ∑ μ, deriv (fun t : ℝ => S (x+t • D μ) μ ν) 0

def Conserved (S : Local → Tensor) : Prop :=
  ∀ x D, VacuumJet D → divergence S x D=0

def quadraticDivergence (c : Coeff) (x : Local) (D : Jet) : Fin 4 → ℝ :=
  fun ν => ∑ μ, variation c x (D μ) μ ν

theorem divergence_quadratic (c : Coeff) (x : Local) (D : Jet) :
    divergence (source c) x D=quadraticDivergence c x D := by
  funext ν
  unfold divergence quadraticDivergence
  apply Finset.sum_congr rfl
  intro μ _
  exact (source_hasDerivAt c x (D μ) μ ν).deriv

theorem conservation_iff (c : Coeff) : Conserved (source c) ↔
    ∀ x D, VacuumJet D → quadraticDivergence c x D=0 := by
  simp only [Conserved,divergence_quadratic]

theorem conservation_reading (c : Coeff) (h : Conserved (source c))
    (x : Local) (D : Jet) (hD : VacuumJet D) (ν : Fin 4) :
    quadraticDivergence c x D ν=0 := congrFun ((conservation_iff c).mp h x D hD) ν

theorem embed_affine (x y : Local) (t : ℝ) :
    embed (x+t • y)=embed x+t • embed y := by
  ext i
  fin_cases i <;> simp [embed]

theorem original_divergence (d : ℝ) (x : Local) (D : Jet) :
    divergence (fun z => registerStress d (embed z)) x D=
      PDTStressBalance.stressDivergence d (embed x) (registerJet D) := by
  funext ν
  unfold divergence PDTStressBalance.stressDivergence
  apply Finset.sum_congr rfl
  intro μ _
  simp only [embed_affine]
  exact (PDTStressBalance.firstVariation_hasDerivAt d (embed x) (embed (D μ)) μ ν).deriv

theorem original_conserved (d : ℝ) : Conserved (fun x => registerStress d (embed x)) := by
  intro x D hD
  rw [original_divergence]
  apply PDTStressBalance.source_free_stress_conserved d (embed x) (registerJet D) hD.1
  funext ν
  have h := congrFun hD.2 ν
  simp only [PDTStressBalance.sourcedCurrent,one_mul,Pi.zero_apply] at h
  simp [PDTStressBalance.sourcedCurrent,h]

#print axioms divergence_quadratic
#print axioms conservation_iff
#print axioms conservation_reading
#print axioms embed_affine
#print axioms original_divergence
#print axioms original_conserved
end
end PDTConservedSource
