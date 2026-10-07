module
public import ExteriorAction
public import Mathlib.LinearAlgebra.Matrix.Transvection

@[expose] public section
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
namespace PDTFinitePfaffian
noncomputable section
open PDTExteriorAction PDTPfaffianCubic MvPolynomial
open scoped Matrix

def value (x : I → ℝ) : ℝ := eval x (pfaffian ℝ)

private theorem diagonal_action (d : Fin 6 → ℝ) (x : I → ℝ) :
    lift (Matrix.diagonal d) *ᵥ x=fun p => d (ia p)*d (ib p)*x p := by
  ext p
  fin_cases p <;> simp only [Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> norm_num [lift,Matrix.diagonal_apply,Matrix.mulVec,dotProduct,
    ia,ib,Fin.sum_univ_succ] <;> ring!

theorem diagonal_value (d : Fin 6 → ℝ) (x : I → ℝ) :
    value (lift (Matrix.diagonal d) *ᵥ x)=(Matrix.diagonal d).det*value x := by
  rw [diagonal_action]
  simp only [value,pfaffian_eval,Matrix.det_diagonal]
  norm_num [ia,ib,Fin.prod_univ_succ]
  ring!

private def action01 (a : ℝ) (x : I → ℝ) : I → ℝ := fun p =>
  if p.val=1 then x 1 +a*x 5 else if p.val=2 then x 2 +a*x 6 else if p.val=3 then x 3 +a*x 7 else if p.val=4 then x 4 +a*x 8 else x p

private theorem action01_eq (a : ℝ) (x : I → ℝ) :
    lift (Matrix.transvection 0 1 a) *ᵥ x=action01 a x := by
  ext p
  fin_cases p <;> simp only [Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> norm_num [lift,Matrix.transvection,Matrix.single_apply,Matrix.one_apply,
    Matrix.mulVec,dotProduct,ia,ib,Fin.sum_univ_succ,action01] <;> ring!

private theorem value01 (a : ℝ) (x : I → ℝ) :
    value (lift (Matrix.transvection 0 1 a) *ᵥ x)=value x := by
  rw [action01_eq]
  simp only [value,pfaffian_eval]
  norm_num [action01]
  ring!

private def action02 (a : ℝ) (x : I → ℝ) : I → ℝ := fun p =>
  if p.val=0 then x 0 -a*x 5 else if p.val=2 then x 2 +a*x 9 else if p.val=3 then x 3 +a*x 10 else if p.val=4 then x 4 +a*x 11 else x p

private theorem action02_eq (a : ℝ) (x : I → ℝ) :
    lift (Matrix.transvection 0 2 a) *ᵥ x=action02 a x := by
  ext p
  fin_cases p <;> simp only [Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> norm_num [lift,Matrix.transvection,Matrix.single_apply,Matrix.one_apply,
    Matrix.mulVec,dotProduct,ia,ib,Fin.sum_univ_succ,action02] <;> ring!

private theorem value02 (a : ℝ) (x : I → ℝ) :
    value (lift (Matrix.transvection 0 2 a) *ᵥ x)=value x := by
  rw [action02_eq]
  simp only [value,pfaffian_eval]
  norm_num [action02]
  ring!

private def action03 (a : ℝ) (x : I → ℝ) : I → ℝ := fun p =>
  if p.val=0 then x 0 -a*x 6 else if p.val=1 then x 1 -a*x 9 else if p.val=3 then x 3 +a*x 12 else if p.val=4 then x 4 +a*x 13 else x p

private theorem action03_eq (a : ℝ) (x : I → ℝ) :
    lift (Matrix.transvection 0 3 a) *ᵥ x=action03 a x := by
  ext p
  fin_cases p <;> simp only [Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> norm_num [lift,Matrix.transvection,Matrix.single_apply,Matrix.one_apply,
    Matrix.mulVec,dotProduct,ia,ib,Fin.sum_univ_succ,action03] <;> ring!

private theorem value03 (a : ℝ) (x : I → ℝ) :
    value (lift (Matrix.transvection 0 3 a) *ᵥ x)=value x := by
  rw [action03_eq]
  simp only [value,pfaffian_eval]
  norm_num [action03]
  ring!

private def action04 (a : ℝ) (x : I → ℝ) : I → ℝ := fun p =>
  if p.val=0 then x 0 -a*x 7 else if p.val=1 then x 1 -a*x 10 else if p.val=2 then x 2 -a*x 12 else if p.val=4 then x 4 +a*x 14 else x p

private theorem action04_eq (a : ℝ) (x : I → ℝ) :
    lift (Matrix.transvection 0 4 a) *ᵥ x=action04 a x := by
  ext p
  fin_cases p <;> simp only [Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> norm_num [lift,Matrix.transvection,Matrix.single_apply,Matrix.one_apply,
    Matrix.mulVec,dotProduct,ia,ib,Fin.sum_univ_succ,action04] <;> ring!

private theorem value04 (a : ℝ) (x : I → ℝ) :
    value (lift (Matrix.transvection 0 4 a) *ᵥ x)=value x := by
  rw [action04_eq]
  simp only [value,pfaffian_eval]
  norm_num [action04]
  ring!

private def action05 (a : ℝ) (x : I → ℝ) : I → ℝ := fun p =>
  if p.val=0 then x 0 -a*x 8 else if p.val=1 then x 1 -a*x 11 else if p.val=2 then x 2 -a*x 13 else if p.val=3 then x 3 -a*x 14 else x p

private theorem action05_eq (a : ℝ) (x : I → ℝ) :
    lift (Matrix.transvection 0 5 a) *ᵥ x=action05 a x := by
  ext p
  fin_cases p <;> simp only [Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> norm_num [lift,Matrix.transvection,Matrix.single_apply,Matrix.one_apply,
    Matrix.mulVec,dotProduct,ia,ib,Fin.sum_univ_succ,action05] <;> ring!

private theorem value05 (a : ℝ) (x : I → ℝ) :
    value (lift (Matrix.transvection 0 5 a) *ᵥ x)=value x := by
  rw [action05_eq]
  simp only [value,pfaffian_eval]
  norm_num [action05]
  ring!

private def action10 (a : ℝ) (x : I → ℝ) : I → ℝ := fun p =>
  if p.val=5 then x 5 +a*x 1 else if p.val=6 then x 6 +a*x 2 else if p.val=7 then x 7 +a*x 3 else if p.val=8 then x 8 +a*x 4 else x p

private theorem action10_eq (a : ℝ) (x : I → ℝ) :
    lift (Matrix.transvection 1 0 a) *ᵥ x=action10 a x := by
  ext p
  fin_cases p <;> simp only [Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> norm_num [lift,Matrix.transvection,Matrix.single_apply,Matrix.one_apply,
    Matrix.mulVec,dotProduct,ia,ib,Fin.sum_univ_succ,action10] <;> ring!

private theorem value10 (a : ℝ) (x : I → ℝ) :
    value (lift (Matrix.transvection 1 0 a) *ᵥ x)=value x := by
  rw [action10_eq]
  simp only [value,pfaffian_eval]
  norm_num [action10]
  ring!

private def action12 (a : ℝ) (x : I → ℝ) : I → ℝ := fun p =>
  if p.val=0 then x 0 +a*x 1 else if p.val=6 then x 6 +a*x 9 else if p.val=7 then x 7 +a*x 10 else if p.val=8 then x 8 +a*x 11 else x p

private theorem action12_eq (a : ℝ) (x : I → ℝ) :
    lift (Matrix.transvection 1 2 a) *ᵥ x=action12 a x := by
  ext p
  fin_cases p <;> simp only [Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> norm_num [lift,Matrix.transvection,Matrix.single_apply,Matrix.one_apply,
    Matrix.mulVec,dotProduct,ia,ib,Fin.sum_univ_succ,action12] <;> ring!

private theorem value12 (a : ℝ) (x : I → ℝ) :
    value (lift (Matrix.transvection 1 2 a) *ᵥ x)=value x := by
  rw [action12_eq]
  simp only [value,pfaffian_eval]
  norm_num [action12]
  ring!

private def action13 (a : ℝ) (x : I → ℝ) : I → ℝ := fun p =>
  if p.val=0 then x 0 +a*x 2 else if p.val=5 then x 5 -a*x 9 else if p.val=7 then x 7 +a*x 12 else if p.val=8 then x 8 +a*x 13 else x p

private theorem action13_eq (a : ℝ) (x : I → ℝ) :
    lift (Matrix.transvection 1 3 a) *ᵥ x=action13 a x := by
  ext p
  fin_cases p <;> simp only [Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> norm_num [lift,Matrix.transvection,Matrix.single_apply,Matrix.one_apply,
    Matrix.mulVec,dotProduct,ia,ib,Fin.sum_univ_succ,action13] <;> ring!

private theorem value13 (a : ℝ) (x : I → ℝ) :
    value (lift (Matrix.transvection 1 3 a) *ᵥ x)=value x := by
  rw [action13_eq]
  simp only [value,pfaffian_eval]
  norm_num [action13]
  ring!

private def action14 (a : ℝ) (x : I → ℝ) : I → ℝ := fun p =>
  if p.val=0 then x 0 +a*x 3 else if p.val=5 then x 5 -a*x 10 else if p.val=6 then x 6 -a*x 12 else if p.val=8 then x 8 +a*x 14 else x p

private theorem action14_eq (a : ℝ) (x : I → ℝ) :
    lift (Matrix.transvection 1 4 a) *ᵥ x=action14 a x := by
  ext p
  fin_cases p <;> simp only [Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> norm_num [lift,Matrix.transvection,Matrix.single_apply,Matrix.one_apply,
    Matrix.mulVec,dotProduct,ia,ib,Fin.sum_univ_succ,action14] <;> ring!

private theorem value14 (a : ℝ) (x : I → ℝ) :
    value (lift (Matrix.transvection 1 4 a) *ᵥ x)=value x := by
  rw [action14_eq]
  simp only [value,pfaffian_eval]
  norm_num [action14]
  ring!

private def action15 (a : ℝ) (x : I → ℝ) : I → ℝ := fun p =>
  if p.val=0 then x 0 +a*x 4 else if p.val=5 then x 5 -a*x 11 else if p.val=6 then x 6 -a*x 13 else if p.val=7 then x 7 -a*x 14 else x p

private theorem action15_eq (a : ℝ) (x : I → ℝ) :
    lift (Matrix.transvection 1 5 a) *ᵥ x=action15 a x := by
  ext p
  fin_cases p <;> simp only [Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> norm_num [lift,Matrix.transvection,Matrix.single_apply,Matrix.one_apply,
    Matrix.mulVec,dotProduct,ia,ib,Fin.sum_univ_succ,action15] <;> ring!

private theorem value15 (a : ℝ) (x : I → ℝ) :
    value (lift (Matrix.transvection 1 5 a) *ᵥ x)=value x := by
  rw [action15_eq]
  simp only [value,pfaffian_eval]
  norm_num [action15]
  ring!

private def action20 (a : ℝ) (x : I → ℝ) : I → ℝ := fun p =>
  if p.val=5 then x 5 -a*x 0 else if p.val=9 then x 9 +a*x 2 else if p.val=10 then x 10 +a*x 3 else if p.val=11 then x 11 +a*x 4 else x p

private theorem action20_eq (a : ℝ) (x : I → ℝ) :
    lift (Matrix.transvection 2 0 a) *ᵥ x=action20 a x := by
  ext p
  fin_cases p <;> simp only [Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> norm_num [lift,Matrix.transvection,Matrix.single_apply,Matrix.one_apply,
    Matrix.mulVec,dotProduct,ia,ib,Fin.sum_univ_succ,action20] <;> ring!

private theorem value20 (a : ℝ) (x : I → ℝ) :
    value (lift (Matrix.transvection 2 0 a) *ᵥ x)=value x := by
  rw [action20_eq]
  simp only [value,pfaffian_eval]
  norm_num [action20]
  ring!

private def action21 (a : ℝ) (x : I → ℝ) : I → ℝ := fun p =>
  if p.val=1 then x 1 +a*x 0 else if p.val=9 then x 9 +a*x 6 else if p.val=10 then x 10 +a*x 7 else if p.val=11 then x 11 +a*x 8 else x p

private theorem action21_eq (a : ℝ) (x : I → ℝ) :
    lift (Matrix.transvection 2 1 a) *ᵥ x=action21 a x := by
  ext p
  fin_cases p <;> simp only [Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> norm_num [lift,Matrix.transvection,Matrix.single_apply,Matrix.one_apply,
    Matrix.mulVec,dotProduct,ia,ib,Fin.sum_univ_succ,action21] <;> ring!

private theorem value21 (a : ℝ) (x : I → ℝ) :
    value (lift (Matrix.transvection 2 1 a) *ᵥ x)=value x := by
  rw [action21_eq]
  simp only [value,pfaffian_eval]
  norm_num [action21]
  ring!

private def action23 (a : ℝ) (x : I → ℝ) : I → ℝ := fun p =>
  if p.val=1 then x 1 +a*x 2 else if p.val=5 then x 5 +a*x 6 else if p.val=10 then x 10 +a*x 12 else if p.val=11 then x 11 +a*x 13 else x p

private theorem action23_eq (a : ℝ) (x : I → ℝ) :
    lift (Matrix.transvection 2 3 a) *ᵥ x=action23 a x := by
  ext p
  fin_cases p <;> simp only [Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> norm_num [lift,Matrix.transvection,Matrix.single_apply,Matrix.one_apply,
    Matrix.mulVec,dotProduct,ia,ib,Fin.sum_univ_succ,action23] <;> ring!

private theorem value23 (a : ℝ) (x : I → ℝ) :
    value (lift (Matrix.transvection 2 3 a) *ᵥ x)=value x := by
  rw [action23_eq]
  simp only [value,pfaffian_eval]
  norm_num [action23]
  ring!

private def action24 (a : ℝ) (x : I → ℝ) : I → ℝ := fun p =>
  if p.val=1 then x 1 +a*x 3 else if p.val=5 then x 5 +a*x 7 else if p.val=9 then x 9 -a*x 12 else if p.val=11 then x 11 +a*x 14 else x p

private theorem action24_eq (a : ℝ) (x : I → ℝ) :
    lift (Matrix.transvection 2 4 a) *ᵥ x=action24 a x := by
  ext p
  fin_cases p <;> simp only [Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> norm_num [lift,Matrix.transvection,Matrix.single_apply,Matrix.one_apply,
    Matrix.mulVec,dotProduct,ia,ib,Fin.sum_univ_succ,action24] <;> ring!

private theorem value24 (a : ℝ) (x : I → ℝ) :
    value (lift (Matrix.transvection 2 4 a) *ᵥ x)=value x := by
  rw [action24_eq]
  simp only [value,pfaffian_eval]
  norm_num [action24]
  ring!

private def action25 (a : ℝ) (x : I → ℝ) : I → ℝ := fun p =>
  if p.val=1 then x 1 +a*x 4 else if p.val=5 then x 5 +a*x 8 else if p.val=9 then x 9 -a*x 13 else if p.val=10 then x 10 -a*x 14 else x p

private theorem action25_eq (a : ℝ) (x : I → ℝ) :
    lift (Matrix.transvection 2 5 a) *ᵥ x=action25 a x := by
  ext p
  fin_cases p <;> simp only [Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> norm_num [lift,Matrix.transvection,Matrix.single_apply,Matrix.one_apply,
    Matrix.mulVec,dotProduct,ia,ib,Fin.sum_univ_succ,action25] <;> ring!

private theorem value25 (a : ℝ) (x : I → ℝ) :
    value (lift (Matrix.transvection 2 5 a) *ᵥ x)=value x := by
  rw [action25_eq]
  simp only [value,pfaffian_eval]
  norm_num [action25]
  ring!

private def action30 (a : ℝ) (x : I → ℝ) : I → ℝ := fun p =>
  if p.val=6 then x 6 -a*x 0 else if p.val=9 then x 9 -a*x 1 else if p.val=12 then x 12 +a*x 3 else if p.val=13 then x 13 +a*x 4 else x p

private theorem action30_eq (a : ℝ) (x : I → ℝ) :
    lift (Matrix.transvection 3 0 a) *ᵥ x=action30 a x := by
  ext p
  fin_cases p <;> simp only [Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> norm_num [lift,Matrix.transvection,Matrix.single_apply,Matrix.one_apply,
    Matrix.mulVec,dotProduct,ia,ib,Fin.sum_univ_succ,action30] <;> ring!

private theorem value30 (a : ℝ) (x : I → ℝ) :
    value (lift (Matrix.transvection 3 0 a) *ᵥ x)=value x := by
  rw [action30_eq]
  simp only [value,pfaffian_eval]
  norm_num [action30]
  ring!

private def action31 (a : ℝ) (x : I → ℝ) : I → ℝ := fun p =>
  if p.val=2 then x 2 +a*x 0 else if p.val=9 then x 9 -a*x 5 else if p.val=12 then x 12 +a*x 7 else if p.val=13 then x 13 +a*x 8 else x p

private theorem action31_eq (a : ℝ) (x : I → ℝ) :
    lift (Matrix.transvection 3 1 a) *ᵥ x=action31 a x := by
  ext p
  fin_cases p <;> simp only [Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> norm_num [lift,Matrix.transvection,Matrix.single_apply,Matrix.one_apply,
    Matrix.mulVec,dotProduct,ia,ib,Fin.sum_univ_succ,action31] <;> ring!

private theorem value31 (a : ℝ) (x : I → ℝ) :
    value (lift (Matrix.transvection 3 1 a) *ᵥ x)=value x := by
  rw [action31_eq]
  simp only [value,pfaffian_eval]
  norm_num [action31]
  ring!

private def action32 (a : ℝ) (x : I → ℝ) : I → ℝ := fun p =>
  if p.val=2 then x 2 +a*x 1 else if p.val=6 then x 6 +a*x 5 else if p.val=12 then x 12 +a*x 10 else if p.val=13 then x 13 +a*x 11 else x p

private theorem action32_eq (a : ℝ) (x : I → ℝ) :
    lift (Matrix.transvection 3 2 a) *ᵥ x=action32 a x := by
  ext p
  fin_cases p <;> simp only [Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> norm_num [lift,Matrix.transvection,Matrix.single_apply,Matrix.one_apply,
    Matrix.mulVec,dotProduct,ia,ib,Fin.sum_univ_succ,action32] <;> ring!

private theorem value32 (a : ℝ) (x : I → ℝ) :
    value (lift (Matrix.transvection 3 2 a) *ᵥ x)=value x := by
  rw [action32_eq]
  simp only [value,pfaffian_eval]
  norm_num [action32]
  ring!

private def action34 (a : ℝ) (x : I → ℝ) : I → ℝ := fun p =>
  if p.val=2 then x 2 +a*x 3 else if p.val=6 then x 6 +a*x 7 else if p.val=9 then x 9 +a*x 10 else if p.val=13 then x 13 +a*x 14 else x p

private theorem action34_eq (a : ℝ) (x : I → ℝ) :
    lift (Matrix.transvection 3 4 a) *ᵥ x=action34 a x := by
  ext p
  fin_cases p <;> simp only [Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> norm_num [lift,Matrix.transvection,Matrix.single_apply,Matrix.one_apply,
    Matrix.mulVec,dotProduct,ia,ib,Fin.sum_univ_succ,action34] <;> ring!

private theorem value34 (a : ℝ) (x : I → ℝ) :
    value (lift (Matrix.transvection 3 4 a) *ᵥ x)=value x := by
  rw [action34_eq]
  simp only [value,pfaffian_eval]
  norm_num [action34]
  ring!

private def action35 (a : ℝ) (x : I → ℝ) : I → ℝ := fun p =>
  if p.val=2 then x 2 +a*x 4 else if p.val=6 then x 6 +a*x 8 else if p.val=9 then x 9 +a*x 11 else if p.val=12 then x 12 -a*x 14 else x p

private theorem action35_eq (a : ℝ) (x : I → ℝ) :
    lift (Matrix.transvection 3 5 a) *ᵥ x=action35 a x := by
  ext p
  fin_cases p <;> simp only [Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> norm_num [lift,Matrix.transvection,Matrix.single_apply,Matrix.one_apply,
    Matrix.mulVec,dotProduct,ia,ib,Fin.sum_univ_succ,action35] <;> ring!

private theorem value35 (a : ℝ) (x : I → ℝ) :
    value (lift (Matrix.transvection 3 5 a) *ᵥ x)=value x := by
  rw [action35_eq]
  simp only [value,pfaffian_eval]
  norm_num [action35]
  ring!

private def action40 (a : ℝ) (x : I → ℝ) : I → ℝ := fun p =>
  if p.val=7 then x 7 -a*x 0 else if p.val=10 then x 10 -a*x 1 else if p.val=12 then x 12 -a*x 2 else if p.val=14 then x 14 +a*x 4 else x p

private theorem action40_eq (a : ℝ) (x : I → ℝ) :
    lift (Matrix.transvection 4 0 a) *ᵥ x=action40 a x := by
  ext p
  fin_cases p <;> simp only [Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> norm_num [lift,Matrix.transvection,Matrix.single_apply,Matrix.one_apply,
    Matrix.mulVec,dotProduct,ia,ib,Fin.sum_univ_succ,action40] <;> ring!

private theorem value40 (a : ℝ) (x : I → ℝ) :
    value (lift (Matrix.transvection 4 0 a) *ᵥ x)=value x := by
  rw [action40_eq]
  simp only [value,pfaffian_eval]
  norm_num [action40]
  ring!

private def action41 (a : ℝ) (x : I → ℝ) : I → ℝ := fun p =>
  if p.val=3 then x 3 +a*x 0 else if p.val=10 then x 10 -a*x 5 else if p.val=12 then x 12 -a*x 6 else if p.val=14 then x 14 +a*x 8 else x p

private theorem action41_eq (a : ℝ) (x : I → ℝ) :
    lift (Matrix.transvection 4 1 a) *ᵥ x=action41 a x := by
  ext p
  fin_cases p <;> simp only [Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> norm_num [lift,Matrix.transvection,Matrix.single_apply,Matrix.one_apply,
    Matrix.mulVec,dotProduct,ia,ib,Fin.sum_univ_succ,action41] <;> ring!

private theorem value41 (a : ℝ) (x : I → ℝ) :
    value (lift (Matrix.transvection 4 1 a) *ᵥ x)=value x := by
  rw [action41_eq]
  simp only [value,pfaffian_eval]
  norm_num [action41]
  ring!

private def action42 (a : ℝ) (x : I → ℝ) : I → ℝ := fun p =>
  if p.val=3 then x 3 +a*x 1 else if p.val=7 then x 7 +a*x 5 else if p.val=12 then x 12 -a*x 9 else if p.val=14 then x 14 +a*x 11 else x p

private theorem action42_eq (a : ℝ) (x : I → ℝ) :
    lift (Matrix.transvection 4 2 a) *ᵥ x=action42 a x := by
  ext p
  fin_cases p <;> simp only [Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> norm_num [lift,Matrix.transvection,Matrix.single_apply,Matrix.one_apply,
    Matrix.mulVec,dotProduct,ia,ib,Fin.sum_univ_succ,action42] <;> ring!

private theorem value42 (a : ℝ) (x : I → ℝ) :
    value (lift (Matrix.transvection 4 2 a) *ᵥ x)=value x := by
  rw [action42_eq]
  simp only [value,pfaffian_eval]
  norm_num [action42]
  ring!

private def action43 (a : ℝ) (x : I → ℝ) : I → ℝ := fun p =>
  if p.val=3 then x 3 +a*x 2 else if p.val=7 then x 7 +a*x 6 else if p.val=10 then x 10 +a*x 9 else if p.val=14 then x 14 +a*x 13 else x p

private theorem action43_eq (a : ℝ) (x : I → ℝ) :
    lift (Matrix.transvection 4 3 a) *ᵥ x=action43 a x := by
  ext p
  fin_cases p <;> simp only [Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> norm_num [lift,Matrix.transvection,Matrix.single_apply,Matrix.one_apply,
    Matrix.mulVec,dotProduct,ia,ib,Fin.sum_univ_succ,action43] <;> ring!

private theorem value43 (a : ℝ) (x : I → ℝ) :
    value (lift (Matrix.transvection 4 3 a) *ᵥ x)=value x := by
  rw [action43_eq]
  simp only [value,pfaffian_eval]
  norm_num [action43]
  ring!

private def action45 (a : ℝ) (x : I → ℝ) : I → ℝ := fun p =>
  if p.val=3 then x 3 +a*x 4 else if p.val=7 then x 7 +a*x 8 else if p.val=10 then x 10 +a*x 11 else if p.val=12 then x 12 +a*x 13 else x p

private theorem action45_eq (a : ℝ) (x : I → ℝ) :
    lift (Matrix.transvection 4 5 a) *ᵥ x=action45 a x := by
  ext p
  fin_cases p <;> simp only [Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> norm_num [lift,Matrix.transvection,Matrix.single_apply,Matrix.one_apply,
    Matrix.mulVec,dotProduct,ia,ib,Fin.sum_univ_succ,action45] <;> ring!

private theorem value45 (a : ℝ) (x : I → ℝ) :
    value (lift (Matrix.transvection 4 5 a) *ᵥ x)=value x := by
  rw [action45_eq]
  simp only [value,pfaffian_eval]
  norm_num [action45]
  ring!

private def action50 (a : ℝ) (x : I → ℝ) : I → ℝ := fun p =>
  if p.val=8 then x 8 -a*x 0 else if p.val=11 then x 11 -a*x 1 else if p.val=13 then x 13 -a*x 2 else if p.val=14 then x 14 -a*x 3 else x p

private theorem action50_eq (a : ℝ) (x : I → ℝ) :
    lift (Matrix.transvection 5 0 a) *ᵥ x=action50 a x := by
  ext p
  fin_cases p <;> simp only [Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> norm_num [lift,Matrix.transvection,Matrix.single_apply,Matrix.one_apply,
    Matrix.mulVec,dotProduct,ia,ib,Fin.sum_univ_succ,action50] <;> ring!

private theorem value50 (a : ℝ) (x : I → ℝ) :
    value (lift (Matrix.transvection 5 0 a) *ᵥ x)=value x := by
  rw [action50_eq]
  simp only [value,pfaffian_eval]
  norm_num [action50]
  ring!

private def action51 (a : ℝ) (x : I → ℝ) : I → ℝ := fun p =>
  if p.val=4 then x 4 +a*x 0 else if p.val=11 then x 11 -a*x 5 else if p.val=13 then x 13 -a*x 6 else if p.val=14 then x 14 -a*x 7 else x p

private theorem action51_eq (a : ℝ) (x : I → ℝ) :
    lift (Matrix.transvection 5 1 a) *ᵥ x=action51 a x := by
  ext p
  fin_cases p <;> simp only [Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> norm_num [lift,Matrix.transvection,Matrix.single_apply,Matrix.one_apply,
    Matrix.mulVec,dotProduct,ia,ib,Fin.sum_univ_succ,action51] <;> ring!

private theorem value51 (a : ℝ) (x : I → ℝ) :
    value (lift (Matrix.transvection 5 1 a) *ᵥ x)=value x := by
  rw [action51_eq]
  simp only [value,pfaffian_eval]
  norm_num [action51]
  ring!

private def action52 (a : ℝ) (x : I → ℝ) : I → ℝ := fun p =>
  if p.val=4 then x 4 +a*x 1 else if p.val=8 then x 8 +a*x 5 else if p.val=13 then x 13 -a*x 9 else if p.val=14 then x 14 -a*x 10 else x p

private theorem action52_eq (a : ℝ) (x : I → ℝ) :
    lift (Matrix.transvection 5 2 a) *ᵥ x=action52 a x := by
  ext p
  fin_cases p <;> simp only [Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> norm_num [lift,Matrix.transvection,Matrix.single_apply,Matrix.one_apply,
    Matrix.mulVec,dotProduct,ia,ib,Fin.sum_univ_succ,action52] <;> ring!

private theorem value52 (a : ℝ) (x : I → ℝ) :
    value (lift (Matrix.transvection 5 2 a) *ᵥ x)=value x := by
  rw [action52_eq]
  simp only [value,pfaffian_eval]
  norm_num [action52]
  ring!

private def action53 (a : ℝ) (x : I → ℝ) : I → ℝ := fun p =>
  if p.val=4 then x 4 +a*x 2 else if p.val=8 then x 8 +a*x 6 else if p.val=11 then x 11 +a*x 9 else if p.val=14 then x 14 -a*x 12 else x p

private theorem action53_eq (a : ℝ) (x : I → ℝ) :
    lift (Matrix.transvection 5 3 a) *ᵥ x=action53 a x := by
  ext p
  fin_cases p <;> simp only [Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> norm_num [lift,Matrix.transvection,Matrix.single_apply,Matrix.one_apply,
    Matrix.mulVec,dotProduct,ia,ib,Fin.sum_univ_succ,action53] <;> ring!

private theorem value53 (a : ℝ) (x : I → ℝ) :
    value (lift (Matrix.transvection 5 3 a) *ᵥ x)=value x := by
  rw [action53_eq]
  simp only [value,pfaffian_eval]
  norm_num [action53]
  ring!

private def action54 (a : ℝ) (x : I → ℝ) : I → ℝ := fun p =>
  if p.val=4 then x 4 +a*x 3 else if p.val=8 then x 8 +a*x 7 else if p.val=11 then x 11 +a*x 10 else if p.val=13 then x 13 +a*x 12 else x p

private theorem action54_eq (a : ℝ) (x : I → ℝ) :
    lift (Matrix.transvection 5 4 a) *ᵥ x=action54 a x := by
  ext p
  fin_cases p <;> simp only [Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> norm_num [lift,Matrix.transvection,Matrix.single_apply,Matrix.one_apply,
    Matrix.mulVec,dotProduct,ia,ib,Fin.sum_univ_succ,action54] <;> ring!

private theorem value54 (a : ℝ) (x : I → ℝ) :
    value (lift (Matrix.transvection 5 4 a) *ᵥ x)=value x := by
  rw [action54_eq]
  simp only [value,pfaffian_eval]
  norm_num [action54]
  ring!

theorem shear_value (i j : Fin 6) (hij : i ≠ j) (a : ℝ) (x : I → ℝ) :
    value (lift (Matrix.transvection i j a) *ᵥ x)=value x := by
  fin_cases i <;> fin_cases j
  · exact False.elim (hij rfl)
  · exact value01 a x
  · exact value02 a x
  · exact value03 a x
  · exact value04 a x
  · exact value05 a x
  · exact value10 a x
  · exact False.elim (hij rfl)
  · exact value12 a x
  · exact value13 a x
  · exact value14 a x
  · exact value15 a x
  · exact value20 a x
  · exact value21 a x
  · exact False.elim (hij rfl)
  · exact value23 a x
  · exact value24 a x
  · exact value25 a x
  · exact value30 a x
  · exact value31 a x
  · exact value32 a x
  · exact False.elim (hij rfl)
  · exact value34 a x
  · exact value35 a x
  · exact value40 a x
  · exact value41 a x
  · exact value42 a x
  · exact value43 a x
  · exact False.elim (hij rfl)
  · exact value45 a x
  · exact value50 a x
  · exact value51 a x
  · exact value52 a x
  · exact value53 a x
  · exact value54 a x
  · exact False.elim (hij rfl)

/-- The actual integral cubic has its determinant transformation law for every real matrix. -/
theorem pfaffian_transform (M : M6) (x : I → ℝ) :
    value (lift M *ᵥ x)=M.det*value x := by
  have hp : ∀ N : M6, ∀ y : I → ℝ, value (lift N *ᵥ y)=N.det*value y := by
    intro N
    apply Matrix.diagonal_transvection_induction
      (fun T : M6 => ∀ y : I → ℝ, value (lift T *ᵥ y)=T.det*value y) N
    · intro d _ y
      exact diagonal_value d y
    · intro t y
      simpa only [Matrix.TransvectionStruct.toMatrix,Matrix.det_transvection_of_ne _ _ t.hij,
        one_mul] using shear_value t.i t.j t.hij t.c y
    · intro A B hA hB y
      rw [lift_mul,← Matrix.mulVec_mulVec,hA,hB,Matrix.det_mul,mul_assoc]
  exact hp M x

theorem oriented_value (M : M6) (hdet : M.det=1) (x : I → ℝ) :
    value (lift M *ᵥ x)=value x := by
  rw [pfaffian_transform,hdet,one_mul]

#print axioms diagonal_value
#print axioms shear_value
#print axioms pfaffian_transform
#print axioms oriented_value
end
end PDTFinitePfaffian
