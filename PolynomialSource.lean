module
public import ConservationConsequences

@[expose] public section
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
namespace PDTPolynomialSource
noncomputable section
open PDTStressTensor PDTUnrestrictedSourceKernel PDTQuadraticSource PDTConservedSource
open scoped Matrix

abbrev ConstantCoeff := Fin 10 → ℝ
abbrev LinearCoeff := Fin 10 → Fin 6 → ℝ

def constant (A : ConstantCoeff) : Tensor := fun i j => A (tensorIndex i j)
def linear (l : LinearCoeff) (x : Local) : Tensor := fun i j => ∑ a, l (tensorIndex i j) a*x a

def polynomial (A : ConstantCoeff) (l : LinearCoeff) (q : Coeff) (x : Local) : Tensor :=
  constant A+linear l x+source q x

/-- All 280 real coefficients, with no dependence on coordinates or field derivatives. -/
def IsPolynomialSource (S : Local → Tensor) : Prop :=
  ∃ A l q, S=polynomial A l q

def linearDivergence (l : LinearCoeff) (D : Jet) : Fin 4 → ℝ :=
  fun ν => ∑ μ, linear l (D μ) μ ν

def LinearConserved (l : LinearCoeff) : Prop := ∀ D, VacuumJet D → linearDivergence l D=0

def ConstantInvariant (A : ConstantCoeff) : Prop := ∀ k, tensorAction k (constant A)=0

def LinearCovariant (l : LinearCoeff) : Prop :=
  ∀ k x, linear l (fieldAction k x)=tensorAction k (linear l x)

theorem constant_symmetric (A : ConstantCoeff) : (constant A).transpose=constant A := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem polynomial_symmetric (A : ConstantCoeff) (l : LinearCoeff) (q : Coeff) (x : Local) :
    (polynomial A l q x).transpose=polynomial A l q x := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem linear_at_zero (l : LinearCoeff) : linear l 0=0 := by
  ext i j
  simp [linear]

theorem polynomial_at_zero (A : ConstantCoeff) (l : LinearCoeff) (q : Coeff) :
    polynomial A l q 0=constant A := by
  simp [polynomial,linear_at_zero,quadratic_at_zero]

theorem linear_hasDerivAt (l : LinearCoeff) (x y : Local) (i j : Fin 4) :
    HasDerivAt (fun t : ℝ => linear l (x+t • y) i j) (linear l y i j) 0 := by
  unfold linear
  have h (a : Fin 6) : HasDerivAt
      (fun t : ℝ => l (tensorIndex i j) a*(x a+t*y a)) (l (tensorIndex i j) a*y a) 0 := by
    convert! (((hasDerivAt_const (0 : ℝ) (x a)).add
      ((hasDerivAt_id (0 : ℝ)).mul_const (y a))).const_mul (l (tensorIndex i j) a)) using 1
    simp
  convert! HasDerivAt.sum (fun a (_ : a ∈ Finset.univ) => h a) using 1

theorem polynomial_hasDerivAt (A : ConstantCoeff) (l : LinearCoeff) (q : Coeff)
    (x y : Local) (i j : Fin 4) :
    HasDerivAt (fun t : ℝ => polynomial A l q (x+t • y) i j)
      (linear l y i j+variation q x y i j) 0 := by
  convert! (((hasDerivAt_const (0 : ℝ) (constant A i j)).add
    (linear_hasDerivAt l x y i j)).add (source_hasDerivAt q x y i j)) using 1
  simp

theorem polynomial_divergence (A : ConstantCoeff) (l : LinearCoeff) (q : Coeff)
    (x : Local) (D : Jet) : divergence (polynomial A l q) x D=
      linearDivergence l D+quadraticDivergence q x D := by
  funext ν
  simp only [divergence,linearDivergence,quadraticDivergence,Pi.add_apply,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro μ _
  exact (polynomial_hasDerivAt A l q x (D μ) μ ν).deriv

theorem quadratic_divergence_zero (q : Coeff) (D : Jet) : quadraticDivergence q 0 D=0 := by
  funext ν
  simp [quadraticDivergence,variation,dpoly]

theorem conservation_split (A : ConstantCoeff) (l : LinearCoeff) (q : Coeff) :
    Conserved (polynomial A l q) ↔ LinearConserved l ∧ Conserved (source q) := by
  constructor
  · intro h
    have hl : LinearConserved l := by
      intro D hD
      have hh := h 0 D hD
      simpa only [polynomial_divergence,quadratic_divergence_zero,add_zero] using hh
    refine ⟨hl,(PDTConservedSource.conservation_iff q).mpr ?_⟩
    intro x D hD
    have hh := h x D hD
    simpa only [polynomial_divergence,hl D hD,zero_add] using hh
  · rintro ⟨hl,hq⟩ x D hD
    rw [polynomial_divergence,hl D hD,(PDTConservedSource.conservation_iff q).mp hq x D hD,add_zero]

theorem polynomial_covariance_iff (A : ConstantCoeff) (l : LinearCoeff) (q : Coeff) :
    Covariant (polynomial A l q) ↔ ∀ k x,
      linear l (fieldAction k x)+variation q x (fieldAction k x)=
        tensorAction k (polynomial A l q x) := by
  constructor
  · intro h k x
    ext i j
    exact (polynomial_hasDerivAt A l q x (fieldAction k x) i j).unique (h k x i j)
  · intro h k x i j
    have hh := polynomial_hasDerivAt A l q x (fieldAction k x) i j
    rw [← h k x]
    exact hh

theorem field_action_zero (k : Fin 6) : fieldAction k 0=0 := by
  ext i
  fin_cases k <;> fin_cases i <;> norm_num [field_action_formula]

theorem tensor_action_add (k : Fin 6) (T U : Tensor) :
    tensorAction k (T+U)=tensorAction k T+tensorAction k U := by
  simp [tensorAction,mul_add,add_mul,add_assoc,add_left_comm]

theorem variation_at_zero (q : Coeff) : variation q 0 0=0 := by
  ext i j
  simp [variation,dpoly]

theorem covariance_lower_parts (A : ConstantCoeff) (l : LinearCoeff) (q : Coeff)
    (hc : Covariant (polynomial A l q)) (hq : Covariant (source q)) :
    ConstantInvariant A ∧ LinearCovariant l := by
  have h := (polynomial_covariance_iff A l q).mp hc
  have ha : ConstantInvariant A := by
    intro k
    have hh := h k 0
    simpa only [field_action_zero,polynomial_at_zero,linear_at_zero,variation_at_zero,
      zero_add] using hh.symm
  refine ⟨ha,?_⟩
  intro k x
  have hh := h k x
  rw [polynomial,tensor_action_add,tensor_action_add,ha k,zero_add,
    (PDTQuadraticSource.covariance_iff q).mp hq k x] at hh
  exact add_right_cancel hh

#print axioms constant_symmetric
#print axioms polynomial_symmetric
#print axioms linear_at_zero
#print axioms polynomial_at_zero
#print axioms linear_hasDerivAt
#print axioms polynomial_hasDerivAt
#print axioms polynomial_divergence
#print axioms quadratic_divergence_zero
#print axioms conservation_split
#print axioms polynomial_covariance_iff
#print axioms field_action_zero
#print axioms tensor_action_add
#print axioms variation_at_zero
#print axioms covariance_lower_parts
end
end PDTPolynomialSource
