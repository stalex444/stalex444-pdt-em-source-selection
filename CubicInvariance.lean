module
public import PfaffianBridge

@[expose] public section
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
namespace PDTCubicInvariance
noncomputable section
open PDTPfaffianCubic GravityScreening
open GravityScreening.ResponseClosureCertificate GravityScreening.ResponseClosureGeometry
open MvPolynomial
open scoped Matrix
variable (R : Type*) [CommRing R]

def cast : IMat →+* Matrix I I R := (Int.castRingHom R).mapMatrix
def generator (p : I) : Matrix I I R := cast R (geometricAdjoint p)

/-- Evaluation-friendly presentation, checked against the original tables. -/
def coefficients (p r c : I) : ℤ :=
  if p.val=0 then (if r.val=1 then (if c.val=5 then 1 else 0) else if r.val=2 then (if c.val=6 then 1 else 0) else if r.val=3 then (if c.val=7 then 1 else 0) else if r.val=4 then (if c.val=8 then 1 else 0) else if r.val=5 then (if c.val=1 then -1 else 0) else if r.val=6 then (if c.val=2 then -1 else 0) else if r.val=7 then (if c.val=3 then -1 else 0) else if r.val=8 then (if c.val=4 then -1 else 0) else 0) else
  if p.val=1 then (if r.val=0 then (if c.val=5 then -1 else 0) else if r.val=2 then (if c.val=9 then 1 else 0) else if r.val=3 then (if c.val=10 then 1 else 0) else if r.val=4 then (if c.val=11 then 1 else 0) else if r.val=5 then (if c.val=0 then 1 else 0) else if r.val=9 then (if c.val=2 then -1 else 0) else if r.val=10 then (if c.val=3 then -1 else 0) else if r.val=11 then (if c.val=4 then -1 else 0) else 0) else
  if p.val=2 then (if r.val=0 then (if c.val=6 then 1 else 0) else if r.val=1 then (if c.val=9 then 1 else 0) else if r.val=3 then (if c.val=12 then -1 else 0) else if r.val=4 then (if c.val=13 then -1 else 0) else if r.val=6 then (if c.val=0 then 1 else 0) else if r.val=9 then (if c.val=1 then 1 else 0) else if r.val=12 then (if c.val=3 then -1 else 0) else if r.val=13 then (if c.val=4 then -1 else 0) else 0) else
  if p.val=3 then (if r.val=0 then (if c.val=7 then -1 else 0) else if r.val=1 then (if c.val=10 then -1 else 0) else if r.val=2 then (if c.val=12 then -1 else 0) else if r.val=4 then (if c.val=14 then 1 else 0) else if r.val=7 then (if c.val=0 then 1 else 0) else if r.val=10 then (if c.val=1 then 1 else 0) else if r.val=12 then (if c.val=2 then 1 else 0) else if r.val=14 then (if c.val=4 then -1 else 0) else 0) else
  if p.val=4 then (if r.val=0 then (if c.val=8 then 1 else 0) else if r.val=1 then (if c.val=11 then 1 else 0) else if r.val=2 then (if c.val=13 then 1 else 0) else if r.val=3 then (if c.val=14 then 1 else 0) else if r.val=8 then (if c.val=0 then 1 else 0) else if r.val=11 then (if c.val=1 then 1 else 0) else if r.val=13 then (if c.val=2 then 1 else 0) else if r.val=14 then (if c.val=3 then 1 else 0) else 0) else
  if p.val=5 then (if r.val=0 then (if c.val=1 then 1 else 0) else if r.val=1 then (if c.val=0 then -1 else 0) else if r.val=6 then (if c.val=9 then 1 else 0) else if r.val=7 then (if c.val=10 then 1 else 0) else if r.val=8 then (if c.val=11 then 1 else 0) else if r.val=9 then (if c.val=6 then -1 else 0) else if r.val=10 then (if c.val=7 then -1 else 0) else if r.val=11 then (if c.val=8 then -1 else 0) else 0) else
  if p.val=6 then (if r.val=0 then (if c.val=2 then -1 else 0) else if r.val=2 then (if c.val=0 then -1 else 0) else if r.val=5 then (if c.val=9 then 1 else 0) else if r.val=7 then (if c.val=12 then -1 else 0) else if r.val=8 then (if c.val=13 then -1 else 0) else if r.val=9 then (if c.val=5 then 1 else 0) else if r.val=12 then (if c.val=7 then -1 else 0) else if r.val=13 then (if c.val=8 then -1 else 0) else 0) else
  if p.val=7 then (if r.val=0 then (if c.val=3 then 1 else 0) else if r.val=3 then (if c.val=0 then -1 else 0) else if r.val=5 then (if c.val=10 then -1 else 0) else if r.val=6 then (if c.val=12 then -1 else 0) else if r.val=8 then (if c.val=14 then 1 else 0) else if r.val=10 then (if c.val=5 then 1 else 0) else if r.val=12 then (if c.val=6 then 1 else 0) else if r.val=14 then (if c.val=8 then -1 else 0) else 0) else
  if p.val=8 then (if r.val=0 then (if c.val=4 then -1 else 0) else if r.val=4 then (if c.val=0 then -1 else 0) else if r.val=5 then (if c.val=11 then 1 else 0) else if r.val=6 then (if c.val=13 then 1 else 0) else if r.val=7 then (if c.val=14 then 1 else 0) else if r.val=11 then (if c.val=5 then 1 else 0) else if r.val=13 then (if c.val=6 then 1 else 0) else if r.val=14 then (if c.val=7 then 1 else 0) else 0) else
  if p.val=9 then (if r.val=1 then (if c.val=2 then -1 else 0) else if r.val=2 then (if c.val=1 then -1 else 0) else if r.val=5 then (if c.val=6 then -1 else 0) else if r.val=6 then (if c.val=5 then -1 else 0) else if r.val=10 then (if c.val=12 then -1 else 0) else if r.val=11 then (if c.val=13 then -1 else 0) else if r.val=12 then (if c.val=10 then -1 else 0) else if r.val=13 then (if c.val=11 then -1 else 0) else 0) else
  if p.val=10 then (if r.val=1 then (if c.val=3 then 1 else 0) else if r.val=3 then (if c.val=1 then -1 else 0) else if r.val=5 then (if c.val=7 then 1 else 0) else if r.val=7 then (if c.val=5 then -1 else 0) else if r.val=9 then (if c.val=12 then -1 else 0) else if r.val=11 then (if c.val=14 then 1 else 0) else if r.val=12 then (if c.val=9 then 1 else 0) else if r.val=14 then (if c.val=11 then -1 else 0) else 0) else
  if p.val=11 then (if r.val=1 then (if c.val=4 then -1 else 0) else if r.val=4 then (if c.val=1 then -1 else 0) else if r.val=5 then (if c.val=8 then -1 else 0) else if r.val=8 then (if c.val=5 then -1 else 0) else if r.val=9 then (if c.val=13 then 1 else 0) else if r.val=10 then (if c.val=14 then 1 else 0) else if r.val=13 then (if c.val=9 then 1 else 0) else if r.val=14 then (if c.val=10 then 1 else 0) else 0) else
  if p.val=12 then (if r.val=2 then (if c.val=3 then 1 else 0) else if r.val=3 then (if c.val=2 then 1 else 0) else if r.val=6 then (if c.val=7 then 1 else 0) else if r.val=7 then (if c.val=6 then 1 else 0) else if r.val=9 then (if c.val=10 then 1 else 0) else if r.val=10 then (if c.val=9 then 1 else 0) else if r.val=13 then (if c.val=14 then 1 else 0) else if r.val=14 then (if c.val=13 then 1 else 0) else 0) else
  if p.val=13 then (if r.val=2 then (if c.val=4 then -1 else 0) else if r.val=4 then (if c.val=2 then 1 else 0) else if r.val=6 then (if c.val=8 then -1 else 0) else if r.val=8 then (if c.val=6 then 1 else 0) else if r.val=9 then (if c.val=11 then -1 else 0) else if r.val=11 then (if c.val=9 then 1 else 0) else if r.val=12 then (if c.val=14 then 1 else 0) else if r.val=14 then (if c.val=12 then -1 else 0) else 0) else
  if p.val=14 then (if r.val=3 then (if c.val=4 then -1 else 0) else if r.val=4 then (if c.val=3 then -1 else 0) else if r.val=7 then (if c.val=8 then -1 else 0) else if r.val=8 then (if c.val=7 then -1 else 0) else if r.val=10 then (if c.val=11 then -1 else 0) else if r.val=11 then (if c.val=10 then -1 else 0) else if r.val=12 then (if c.val=13 then -1 else 0) else if r.val=13 then (if c.val=12 then -1 else 0) else 0) else 0

private theorem coefficients_correct : ∀ p r c : I, adj p r c=coefficients p r c := by
  decide +kernel

def directional (x y : I → R) : R :=
  ∑ t : Fin 15, (matchingSign t : R)*
    (y (matching t 0)*x (matching t 1)*x (matching t 2)+
      x (matching t 0)*y (matching t 1)*x (matching t 2)+
      x (matching t 0)*x (matching t 1)*y (matching t 2))

theorem directional_eval (x y : I → R) : directional R x y=(y 0*x 9*x 14+x 0*y 9*x 14+x 0*x 9*y 14) -(y 0*x 10*x 13+x 0*y 10*x 13+x 0*x 10*y 13) +(y 0*x 11*x 12+x 0*y 11*x 12+x 0*x 11*y 12) -(y 1*x 6*x 14+x 1*y 6*x 14+x 1*x 6*y 14) +(y 1*x 7*x 13+x 1*y 7*x 13+x 1*x 7*y 13) -(y 1*x 8*x 12+x 1*y 8*x 12+x 1*x 8*y 12) +(y 2*x 5*x 14+x 2*y 5*x 14+x 2*x 5*y 14) -(y 2*x 7*x 11+x 2*y 7*x 11+x 2*x 7*y 11) +(y 2*x 8*x 10+x 2*y 8*x 10+x 2*x 8*y 10) -(y 3*x 5*x 13+x 3*y 5*x 13+x 3*x 5*y 13) +(y 3*x 6*x 11+x 3*y 6*x 11+x 3*x 6*y 11) -(y 3*x 8*x 9+x 3*y 8*x 9+x 3*x 8*y 9) +(y 4*x 5*x 12+x 4*y 5*x 12+x 4*x 5*y 12) -(y 4*x 6*x 10+x 4*y 6*x 10+x 4*x 6*y 10) +(y 4*x 7*x 9+x 4*y 7*x 9+x 4*x 7*y 9) := by
  simp [directional,matching_signs,matching,Fin.sum_univ_succ]
  ring

def directionalMap (x : I → R) : (I → R) →ₗ[R] R where
  toFun := directional R x
  map_add' y z := by
    simp [directional,mul_add,add_mul,Finset.sum_add_distrib]
    ring
  map_smul' a y := by
    change directional R x (a • y)=a*directional R x y
    simp only [directional,Pi.smul_apply,smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    ring

private theorem generator_coeff (p r c : I) :
    generator R p r c=(coefficients p r c : R) := by
  change (geometricAdjoint p r c : R)=(coefficients p r c : R)
  rw [← certificate_adjoint,coefficients_correct]

private def action00 (x : I → R) : I → R := fun i => if i.val=1 then x 5 else if i.val=2 then x 6 else if i.val=3 then x 7 else if i.val=4 then x 8 else if i.val=5 then -x 1 else if i.val=6 then -x 2 else if i.val=7 then -x 3 else if i.val=8 then -x 4 else 0

private theorem action00_eq (x : I → R) :
    generator R 0 *ᵥ x=action00 R x := by
  ext i
  simp only [Matrix.mulVec,dotProduct,generator_coeff]
  fin_cases i <;> norm_num [coefficients,action00,Fin.sum_univ_succ]

private theorem invariant00 (x : I → R) :
    directional R x (generator R 0 *ᵥ x)=0 := by
  rw [action00_eq,directional_eval]
  norm_num [action00]
  ring

private def action01 (x : I → R) : I → R := fun i => if i.val=0 then -x 5 else if i.val=2 then x 9 else if i.val=3 then x 10 else if i.val=4 then x 11 else if i.val=5 then x 0 else if i.val=9 then -x 2 else if i.val=10 then -x 3 else if i.val=11 then -x 4 else 0

private theorem action01_eq (x : I → R) :
    generator R 1 *ᵥ x=action01 R x := by
  ext i
  simp only [Matrix.mulVec,dotProduct,generator_coeff]
  fin_cases i <;> norm_num [coefficients,action01,Fin.sum_univ_succ]

private theorem invariant01 (x : I → R) :
    directional R x (generator R 1 *ᵥ x)=0 := by
  rw [action01_eq,directional_eval]
  norm_num [action01]
  ring

private def action02 (x : I → R) : I → R := fun i => if i.val=0 then x 6 else if i.val=1 then x 9 else if i.val=3 then -x 12 else if i.val=4 then -x 13 else if i.val=6 then x 0 else if i.val=9 then x 1 else if i.val=12 then -x 3 else if i.val=13 then -x 4 else 0

private theorem action02_eq (x : I → R) :
    generator R 2 *ᵥ x=action02 R x := by
  ext i
  simp only [Matrix.mulVec,dotProduct,generator_coeff]
  fin_cases i <;> norm_num [coefficients,action02,Fin.sum_univ_succ]

private theorem invariant02 (x : I → R) :
    directional R x (generator R 2 *ᵥ x)=0 := by
  rw [action02_eq,directional_eval]
  norm_num [action02]
  ring

private def action03 (x : I → R) : I → R := fun i => if i.val=0 then -x 7 else if i.val=1 then -x 10 else if i.val=2 then -x 12 else if i.val=4 then x 14 else if i.val=7 then x 0 else if i.val=10 then x 1 else if i.val=12 then x 2 else if i.val=14 then -x 4 else 0

private theorem action03_eq (x : I → R) :
    generator R 3 *ᵥ x=action03 R x := by
  ext i
  simp only [Matrix.mulVec,dotProduct,generator_coeff]
  fin_cases i <;> norm_num [coefficients,action03,Fin.sum_univ_succ]

private theorem invariant03 (x : I → R) :
    directional R x (generator R 3 *ᵥ x)=0 := by
  rw [action03_eq,directional_eval]
  norm_num [action03]
  ring

private def action04 (x : I → R) : I → R := fun i => if i.val=0 then x 8 else if i.val=1 then x 11 else if i.val=2 then x 13 else if i.val=3 then x 14 else if i.val=8 then x 0 else if i.val=11 then x 1 else if i.val=13 then x 2 else if i.val=14 then x 3 else 0

private theorem action04_eq (x : I → R) :
    generator R 4 *ᵥ x=action04 R x := by
  ext i
  simp only [Matrix.mulVec,dotProduct,generator_coeff]
  fin_cases i <;> norm_num [coefficients,action04,Fin.sum_univ_succ]

private theorem invariant04 (x : I → R) :
    directional R x (generator R 4 *ᵥ x)=0 := by
  rw [action04_eq,directional_eval]
  norm_num [action04]
  ring

private def action05 (x : I → R) : I → R := fun i => if i.val=0 then x 1 else if i.val=1 then -x 0 else if i.val=6 then x 9 else if i.val=7 then x 10 else if i.val=8 then x 11 else if i.val=9 then -x 6 else if i.val=10 then -x 7 else if i.val=11 then -x 8 else 0

private theorem action05_eq (x : I → R) :
    generator R 5 *ᵥ x=action05 R x := by
  ext i
  simp only [Matrix.mulVec,dotProduct,generator_coeff]
  fin_cases i <;> norm_num [coefficients,action05,Fin.sum_univ_succ]

private theorem invariant05 (x : I → R) :
    directional R x (generator R 5 *ᵥ x)=0 := by
  rw [action05_eq,directional_eval]
  norm_num [action05]
  ring

private def action06 (x : I → R) : I → R := fun i => if i.val=0 then -x 2 else if i.val=2 then -x 0 else if i.val=5 then x 9 else if i.val=7 then -x 12 else if i.val=8 then -x 13 else if i.val=9 then x 5 else if i.val=12 then -x 7 else if i.val=13 then -x 8 else 0

private theorem action06_eq (x : I → R) :
    generator R 6 *ᵥ x=action06 R x := by
  ext i
  simp only [Matrix.mulVec,dotProduct,generator_coeff]
  fin_cases i <;> norm_num [coefficients,action06,Fin.sum_univ_succ]

private theorem invariant06 (x : I → R) :
    directional R x (generator R 6 *ᵥ x)=0 := by
  rw [action06_eq,directional_eval]
  norm_num [action06]
  ring

private def action07 (x : I → R) : I → R := fun i => if i.val=0 then x 3 else if i.val=3 then -x 0 else if i.val=5 then -x 10 else if i.val=6 then -x 12 else if i.val=8 then x 14 else if i.val=10 then x 5 else if i.val=12 then x 6 else if i.val=14 then -x 8 else 0

private theorem action07_eq (x : I → R) :
    generator R 7 *ᵥ x=action07 R x := by
  ext i
  simp only [Matrix.mulVec,dotProduct,generator_coeff]
  fin_cases i <;> norm_num [coefficients,action07,Fin.sum_univ_succ]

private theorem invariant07 (x : I → R) :
    directional R x (generator R 7 *ᵥ x)=0 := by
  rw [action07_eq,directional_eval]
  norm_num [action07]
  ring

private def action08 (x : I → R) : I → R := fun i => if i.val=0 then -x 4 else if i.val=4 then -x 0 else if i.val=5 then x 11 else if i.val=6 then x 13 else if i.val=7 then x 14 else if i.val=11 then x 5 else if i.val=13 then x 6 else if i.val=14 then x 7 else 0

private theorem action08_eq (x : I → R) :
    generator R 8 *ᵥ x=action08 R x := by
  ext i
  simp only [Matrix.mulVec,dotProduct,generator_coeff]
  fin_cases i <;> norm_num [coefficients,action08,Fin.sum_univ_succ]

private theorem invariant08 (x : I → R) :
    directional R x (generator R 8 *ᵥ x)=0 := by
  rw [action08_eq,directional_eval]
  norm_num [action08]
  ring

private def action09 (x : I → R) : I → R := fun i => if i.val=1 then -x 2 else if i.val=2 then -x 1 else if i.val=5 then -x 6 else if i.val=6 then -x 5 else if i.val=10 then -x 12 else if i.val=11 then -x 13 else if i.val=12 then -x 10 else if i.val=13 then -x 11 else 0

private theorem action09_eq (x : I → R) :
    generator R 9 *ᵥ x=action09 R x := by
  ext i
  simp only [Matrix.mulVec,dotProduct,generator_coeff]
  fin_cases i <;> norm_num [coefficients,action09,Fin.sum_univ_succ]

private theorem invariant09 (x : I → R) :
    directional R x (generator R 9 *ᵥ x)=0 := by
  rw [action09_eq,directional_eval]
  norm_num [action09]
  ring

private def action10 (x : I → R) : I → R := fun i => if i.val=1 then x 3 else if i.val=3 then -x 1 else if i.val=5 then x 7 else if i.val=7 then -x 5 else if i.val=9 then -x 12 else if i.val=11 then x 14 else if i.val=12 then x 9 else if i.val=14 then -x 11 else 0

private theorem action10_eq (x : I → R) :
    generator R 10 *ᵥ x=action10 R x := by
  ext i
  simp only [Matrix.mulVec,dotProduct,generator_coeff]
  fin_cases i <;> norm_num [coefficients,action10,Fin.sum_univ_succ]

private theorem invariant10 (x : I → R) :
    directional R x (generator R 10 *ᵥ x)=0 := by
  rw [action10_eq,directional_eval]
  norm_num [action10]
  ring

private def action11 (x : I → R) : I → R := fun i => if i.val=1 then -x 4 else if i.val=4 then -x 1 else if i.val=5 then -x 8 else if i.val=8 then -x 5 else if i.val=9 then x 13 else if i.val=10 then x 14 else if i.val=13 then x 9 else if i.val=14 then x 10 else 0

private theorem action11_eq (x : I → R) :
    generator R 11 *ᵥ x=action11 R x := by
  ext i
  simp only [Matrix.mulVec,dotProduct,generator_coeff]
  fin_cases i <;> norm_num [coefficients,action11,Fin.sum_univ_succ]

private theorem invariant11 (x : I → R) :
    directional R x (generator R 11 *ᵥ x)=0 := by
  rw [action11_eq,directional_eval]
  norm_num [action11]
  ring

private def action12 (x : I → R) : I → R := fun i => if i.val=2 then x 3 else if i.val=3 then x 2 else if i.val=6 then x 7 else if i.val=7 then x 6 else if i.val=9 then x 10 else if i.val=10 then x 9 else if i.val=13 then x 14 else if i.val=14 then x 13 else 0

private theorem action12_eq (x : I → R) :
    generator R 12 *ᵥ x=action12 R x := by
  ext i
  simp only [Matrix.mulVec,dotProduct,generator_coeff]
  fin_cases i <;> norm_num [coefficients,action12,Fin.sum_univ_succ]

private theorem invariant12 (x : I → R) :
    directional R x (generator R 12 *ᵥ x)=0 := by
  rw [action12_eq,directional_eval]
  norm_num [action12]
  ring

private def action13 (x : I → R) : I → R := fun i => if i.val=2 then -x 4 else if i.val=4 then x 2 else if i.val=6 then -x 8 else if i.val=8 then x 6 else if i.val=9 then -x 11 else if i.val=11 then x 9 else if i.val=12 then x 14 else if i.val=14 then -x 12 else 0

private theorem action13_eq (x : I → R) :
    generator R 13 *ᵥ x=action13 R x := by
  ext i
  simp only [Matrix.mulVec,dotProduct,generator_coeff]
  fin_cases i <;> norm_num [coefficients,action13,Fin.sum_univ_succ]

private theorem invariant13 (x : I → R) :
    directional R x (generator R 13 *ᵥ x)=0 := by
  rw [action13_eq,directional_eval]
  norm_num [action13]
  ring

private def action14 (x : I → R) : I → R := fun i => if i.val=3 then -x 4 else if i.val=4 then -x 3 else if i.val=7 then -x 8 else if i.val=8 then -x 7 else if i.val=10 then -x 11 else if i.val=11 then -x 10 else if i.val=12 then -x 13 else if i.val=13 then -x 12 else 0

private theorem action14_eq (x : I → R) :
    generator R 14 *ᵥ x=action14 R x := by
  ext i
  simp only [Matrix.mulVec,dotProduct,generator_coeff]
  fin_cases i <;> norm_num [coefficients,action14,Fin.sum_univ_succ]

private theorem invariant14 (x : I → R) :
    directional R x (generator R 14 *ᵥ x)=0 := by
  rw [action14_eq,directional_eval]
  norm_num [action14]
  ring

theorem generator_invariance (p : I) (x : I → R) :
    directional R x (generator R p *ᵥ x)=0 := by
  fin_cases p
  · exact invariant00 R x
  · exact invariant01 R x
  · exact invariant02 R x
  · exact invariant03 R x
  · exact invariant04 R x
  · exact invariant05 R x
  · exact invariant06 R x
  · exact invariant07 R x
  · exact invariant08 R x
  · exact invariant09 R x
  · exact invariant10 R x
  · exact invariant11 R x
  · exact invariant12 R x
  · exact invariant13 R x
  · exact invariant14 R x

#print axioms directional_eval
#print axioms generator_invariance
end
end PDTCubicInvariance
