module
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import ResponseClosureGeometry

@[expose] public section
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
namespace PDTPfaffianCubic
open GravityScreening GravityScreening.ResponseClosureGeometry
open MvPolynomial
abbrev I := Fin 15

/-- Canonical increasing perfect matchings of six ordered indices. -/
def matching : Fin 15 → Fin 3 → I :=
  ![![0,9,14],
    ![0,10,13],
    ![0,11,12],
    ![1,6,14],
    ![1,7,13],
    ![1,8,12],
    ![2,5,14],
    ![2,7,11],
    ![2,8,10],
    ![3,5,13],
    ![3,6,11],
    ![3,8,9],
    ![4,5,12],
    ![4,6,10],
    ![4,7,9]]

def endpoints (a b c : I) : Fin 6 → Fin 6 :=
  ![(basisPairs a).1,(basisPairs a).2,(basisPairs b).1,(basisPairs b).2,
    (basisPairs c).1,(basisPairs c).2]

def matchingSign (t : Fin 15) : ℤ :=
  (-1) ^ (∑ i : Fin 6, ∑ j : Fin 6,
    if i < j ∧ endpoints (matching t 0) (matching t 1) (matching t 2) i >
      endpoints (matching t 0) (matching t 1) (matching t 2) j then 1 else 0)

theorem matching_complete : ∀ a b c : I,
    (a < b ∧ b < c ∧ (Finset.univ.image (endpoints a b c)).card=6) ↔
      ∃ t, matching t = ![a,b,c] := by
  decide +kernel

theorem matching_injective : Function.Injective matching := by decide +kernel

theorem matching_signs : matchingSign =
    ![1,-1,1,-1,1,-1,1,-1,1,-1,1,-1,1,-1,1] := by
  decide +kernel

noncomputable section
variable (R : Type*) [CommRing R]

/-- Integral signed matching expansion; no factorial denominator is used. -/
def pfaffian : MvPolynomial I R :=
  ∑ t : Fin 15, C (matchingSign t : R) *
    (X (matching t 0) * X (matching t 1) * X (matching t 2))

/-- Actual iterated formal partial derivative, evaluated at x. -/
def hessian (x : I → R) : Matrix I I R := fun r c =>
  eval x (pderiv r (pderiv c (pfaffian R)))

def delta (i j : I) : R := if i=j then 1 else 0

/-- Explicit product-rule formula, independent of the frozen operator tables. -/
def tripleHessian (x : I → R) (r c a b d : I) : R :=
  delta R c a * delta R r b * x d + delta R c a * x b * delta R r d +
  delta R r a * delta R c b * x d + x a * delta R c b * delta R r d +
  delta R r a * x b * delta R c d + x a * delta R r b * delta R c d

def computedHessian (x : I → R) : Matrix I I R := fun r c =>
  ∑ t : Fin 15, (matchingSign t : R) *
    tripleHessian R x r c (matching t 0) (matching t 1) (matching t 2)

private theorem derivative_X (i j : I) :
    pderiv i (X j : MvPolynomial I R)=C (delta R i j) := by
  classical
  by_cases h : i=j
  · subst j; simp [delta]
  · simp [pderiv_X,delta,h,Ne.symm h]

private theorem derivative_const_mul (a : R) (f : MvPolynomial I R) (r : I) :
    pderiv r (C a*f)=C a*pderiv r f := by
  simp only [pderiv_mul,pderiv_C,zero_mul,zero_add]

private theorem triple_derivative (x : I → R) (r c a b d : I) :
    eval x (pderiv r (pderiv c (X a * X b * X d : MvPolynomial I R)))=
      tripleHessian R x r c a b d := by
  classical
  simp only [pderiv_mul,map_add,derivative_X,pderiv_C,zero_mul,mul_zero,
    zero_add,add_zero,map_mul,eval_C,eval_X,tripleHessian]
  ring

theorem hessian_formula (x : I → R) : hessian R x=computedHessian R x := by
  ext r c
  simp only [hessian,pfaffian,map_sum,derivative_const_mul,
    map_mul,eval_C,computedHessian]
  apply Finset.sum_congr rfl
  intro t _
  rw [triple_derivative]


/-- The formal Hessian is linear in its evaluation point because this polynomial is cubic. -/
def hessianMap : (I → R) →ₗ[R] Matrix I I R where
  toFun := computedHessian R
  map_add' x y := by
    ext r c
    simp [computedHessian,tripleHessian,mul_add,add_mul,Finset.sum_add_distrib]
    ring
  map_smul' a x := by
    ext r c
    change computedHessian R (a • x) r c=a*computedHessian R x r c
    simp only [computedHessian,tripleHessian,Pi.smul_apply,smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    ring

theorem hessian_basis_expansion (x : I → R) :
    hessian R x=∑ p : I, x p • hessian R (Pi.single p 1) := by
  simp_rw [hessian_formula]
  change hessianMap R x=∑ p : I, x p • hessianMap R (Pi.single p 1)
  have hx : x=∑ p : I, x p • (Pi.single p 1 : I → R) := by
    ext i
    simp [Pi.single_apply]
  conv_lhs => rw [hx,map_sum]
  simp only [map_smul]

theorem computedHessian_cast (x : I → ℤ) (r c : I) :
    computedHessian R (fun p => (x p : R)) r c=(computedHessian ℤ x r c : R) := by
  simp only [computedHessian,tripleHessian,delta,Int.cast_sum,Int.cast_add,Int.cast_mul]
  simp only [Int.cast_ite,Int.cast_one,Int.cast_zero,Int.cast_id]


theorem pfaffian_eval (x : I → R) :
    eval x (pfaffian R)=x 0*x 9*x 14 - x 0*x 10*x 13 + x 0*x 11*x 12 - x 1*x 6*x 14 + x 1*x 7*x 13 - x 1*x 8*x 12 + x 2*x 5*x 14 - x 2*x 7*x 11 + x 2*x 8*x 10 - x 3*x 5*x 13 + x 3*x 6*x 11 - x 3*x 8*x 9 + x 4*x 5*x 12 - x 4*x 6*x 10 + x 4*x 7*x 9 := by
  simp [pfaffian,matching_signs,matching,Fin.sum_univ_succ]
  ring

#print axioms matching_complete
#print axioms matching_injective
#print axioms matching_signs
#print axioms hessian_formula
#print axioms hessian_basis_expansion
#print axioms computedHessian_cast
#print axioms pfaffian_eval
end
end PDTPfaffianCubic
