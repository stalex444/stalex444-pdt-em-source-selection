module
public import StressTensor

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! The local first-jet Maxwell stress balance.
D mu is a supplied coordinate derivative of the bivector register.
The algebra applies in flat coordinates or a normal frame at a point.
No global PDE solution or matter equation is asserted. -/
namespace PDTStressBalance
noncomputable section
open PDTStressTensor PDTMaxwellSymbol PDTResponseBridge

def crossInvariant (F A : Tensor) : ℝ :=
  mink (F 0) (A 0)+mink (F 1) (A 1)+mink (F 2) (A 2)-mink (F 3) (A 3)
def firstVariation (d : ℝ) (v w : V) : Tensor := fun μ ν =>
  d*(mink (field v μ) (field w ν)+mink (field w μ) (field v ν) -
    metric μ ν*crossInvariant (field v) (field w)/2)

theorem exact_stress_increment (d : ℝ) (v w : V) (t : ℝ) :
    registerStress d (v+t • w) =
      registerStress d v+t • firstVariation d v w+t^2 • registerStress d w := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [registerStress, stress, field, firstVariation, crossInvariant,
      metric, eta, Matrix.diagonal, invariant, mink] <;> ring

/-- The polynomial increment gives an actual derivative in every field direction. -/
theorem firstVariation_hasDerivAt (d : ℝ) (v w : V) (μ ν : Fin 4) :
    HasDerivAt (fun t : ℝ => registerStress d (v+t • w) μ ν)
      (firstVariation d v w μ ν) 0 := by
  have he : (fun t : ℝ => registerStress d (v+t • w) μ ν) =
      (fun t => registerStress d v μ ν+t*firstVariation d v w μ ν+
        t^2*registerStress d w μ ν) := by
    funext t
    rw [exact_stress_increment]
    rfl
  rw [he]
  have h := ((hasDerivAt_const (0 : ℝ) (registerStress d v μ ν)).add
    ((hasDerivAt_id (0 : ℝ)).mul_const (firstVariation d v w μ ν))).add
    (((hasDerivAt_id (0 : ℝ)).pow 2).mul_const (registerStress d w μ ν))
  convert! h using 1
  simp

/-- Four independent components of the raised Bianchi identity. -/
def bianchiJet (D : Fin 4 → V) : Prop :=
  D 0 5-D 1 1+D 2 0 = 0 ∧
  D 0 6-D 1 2-D 3 0 = 0 ∧
  D 0 9-D 2 2-D 3 1 = 0 ∧
  D 1 9-D 2 6-D 3 5 = 0

/-- Convention: j^nu=d partial_mu F^{mu nu}. -/
def sourcedCurrent (d : ℝ) (D : Fin 4 → V) : Four := fun ν =>
  d * ∑ μ, field (D μ) μ ν
def stressDivergence (d : ℝ) (v : V) (D : Fin 4 → V) : Four := fun ν =>
  ∑ μ, firstVariation d v (D μ) μ ν
def exchange (v : V) (j : Four) : Four := fun ν => mink (field v ν) j

/-- The field stress exchanges energy-momentum with the supplied Maxwell source.
The sign follows exactly the displayed definition of sourcedCurrent. -/
theorem stress_balance (d : ℝ) (v : V) (D : Fin 4 → V) (hB : bianchiJet D) :
    stressDivergence d v D = exchange v (sourcedCurrent d D) := by
  rcases hB with ⟨h0,h1,h2,h3⟩
  have r0 : D 0 5 = D 1 1-D 2 0 := by linarith
  have r1 : D 0 6 = D 1 2+D 3 0 := by linarith
  have r2 : D 0 9 = D 2 2+D 3 1 := by linarith
  have r3 : D 1 9 = D 2 6+D 3 5 := by linarith
  ext ν
  fin_cases ν <;>
    simp [stressDivergence, firstVariation, crossInvariant, sourcedCurrent,
      exchange, field, metric, eta, Matrix.diagonal, mink, Fin.sum_univ_succ,
      r0, r1, r2, r3] <;> ring

theorem source_free_stress_conserved (d : ℝ) (v : V) (D : Fin 4 → V)
    (hB : bianchiJet D) (hj : sourcedCurrent d D = 0) :
    stressDivergence d v D = 0 := by
  rw [stress_balance d v D hB, hj]
  ext ν
  simp [exchange, mink]

/-- Conservation of total stress additionally needs the opposite matter exchange. -/
theorem total_stress_conserved (d : ℝ) (v : V) (D : Fin 4 → V)
    (hB : bianchiJet D) (matterDivergence : Four)
    (hm : matterDivergence = -exchange v (sourcedCurrent d D)) :
    stressDivergence d v D+matterDivergence = 0 := by
  rw [stress_balance d v D hB, hm, add_neg_cancel]

#print axioms exact_stress_increment
#print axioms firstVariation_hasDerivAt
#print axioms stress_balance
#print axioms source_free_stress_conserved
#print axioms total_stress_conserved
end
end PDTStressBalance
