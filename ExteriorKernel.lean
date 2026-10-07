module
public import FiniteHodge

@[expose] public section
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
namespace PDTExteriorKernel
noncomputable section
open PDTExteriorAction PDTPfaffianCubic
open scoped Matrix

theorem lift_neg (M : M6) : lift (-M)=lift M := by
  ext r c
  simp only [lift,Matrix.neg_apply]
  ring

private theorem scalar_off_diagonal (M : M6) (s : ℝ) (hs : s ≠ 0)
    (h : lift M=s • (1 : M15)) (i a : Fin 6) (hia : i ≠ a) : M i a=0 := by
  fin_cases i <;> fin_cases a
  · exact False.elim (hia rfl)
  · have h0 := congrArg (fun A : M15 => A 5 5) h
    have h1 := congrArg (fun A : M15 => A 1 5) h
    have h2 := congrArg (fun A : M15 => A 0 5) h
    norm_num [lift,ia,ib,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,Fin.ext_iff] at h0 h1 h2
    have hz : s * M 0 1=0 := by
      linear_combination -M 0 1 * h0 + (1) * M 1 1 * h1 - (1) * M 2 1 * h2
    exact (mul_eq_zero.mp hz).resolve_left hs
  · have h0 := congrArg (fun A : M15 => A 5 5) h
    have h1 := congrArg (fun A : M15 => A 0 5) h
    have h2 := congrArg (fun A : M15 => A 1 5) h
    norm_num [lift,ia,ib,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,Fin.ext_iff] at h0 h1 h2
    have hz : s * M 0 2=0 := by
      linear_combination -M 0 2 * h0 + (-1) * M 2 2 * h1 - (-1) * M 1 2 * h2
    exact (mul_eq_zero.mp hz).resolve_left hs
  · have h0 := congrArg (fun A : M15 => A 6 6) h
    have h1 := congrArg (fun A : M15 => A 0 6) h
    have h2 := congrArg (fun A : M15 => A 2 6) h
    norm_num [lift,ia,ib,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,Fin.ext_iff] at h0 h1 h2
    have hz : s * M 0 3=0 := by
      linear_combination -M 0 3 * h0 + (-1) * M 3 3 * h1 - (-1) * M 1 3 * h2
    exact (mul_eq_zero.mp hz).resolve_left hs
  · have h0 := congrArg (fun A : M15 => A 7 7) h
    have h1 := congrArg (fun A : M15 => A 0 7) h
    have h2 := congrArg (fun A : M15 => A 3 7) h
    norm_num [lift,ia,ib,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,Fin.ext_iff] at h0 h1 h2
    have hz : s * M 0 4=0 := by
      linear_combination -M 0 4 * h0 + (-1) * M 4 4 * h1 - (-1) * M 1 4 * h2
    exact (mul_eq_zero.mp hz).resolve_left hs
  · have h0 := congrArg (fun A : M15 => A 8 8) h
    have h1 := congrArg (fun A : M15 => A 0 8) h
    have h2 := congrArg (fun A : M15 => A 4 8) h
    norm_num [lift,ia,ib,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,Fin.ext_iff] at h0 h1 h2
    have hz : s * M 0 5=0 := by
      linear_combination -M 0 5 * h0 + (-1) * M 5 5 * h1 - (-1) * M 1 5 * h2
    exact (mul_eq_zero.mp hz).resolve_left hs
  · have h0 := congrArg (fun A : M15 => A 1 1) h
    have h1 := congrArg (fun A : M15 => A 5 1) h
    have h2 := congrArg (fun A : M15 => A 0 1) h
    norm_num [lift,ia,ib,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,Fin.ext_iff] at h0 h1 h2
    have hz : s * M 1 0=0 := by
      linear_combination -M 1 0 * h0 + (1) * M 0 0 * h1 - (-1) * M 2 0 * h2
    exact (mul_eq_zero.mp hz).resolve_left hs
  · exact False.elim (hia rfl)
  · have h0 := congrArg (fun A : M15 => A 1 1) h
    have h1 := congrArg (fun A : M15 => A 0 1) h
    have h2 := congrArg (fun A : M15 => A 5 1) h
    norm_num [lift,ia,ib,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,Fin.ext_iff] at h0 h1 h2
    have hz : s * M 1 2=0 := by
      linear_combination -M 1 2 * h0 + (1) * M 2 2 * h1 - (-1) * M 0 2 * h2
    exact (mul_eq_zero.mp hz).resolve_left hs
  · have h0 := congrArg (fun A : M15 => A 2 2) h
    have h1 := congrArg (fun A : M15 => A 0 2) h
    have h2 := congrArg (fun A : M15 => A 6 2) h
    norm_num [lift,ia,ib,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,Fin.ext_iff] at h0 h1 h2
    have hz : s * M 1 3=0 := by
      linear_combination -M 1 3 * h0 + (1) * M 3 3 * h1 - (-1) * M 0 3 * h2
    exact (mul_eq_zero.mp hz).resolve_left hs
  · have h0 := congrArg (fun A : M15 => A 3 3) h
    have h1 := congrArg (fun A : M15 => A 0 3) h
    have h2 := congrArg (fun A : M15 => A 7 3) h
    norm_num [lift,ia,ib,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,Fin.ext_iff] at h0 h1 h2
    have hz : s * M 1 4=0 := by
      linear_combination -M 1 4 * h0 + (1) * M 4 4 * h1 - (-1) * M 0 4 * h2
    exact (mul_eq_zero.mp hz).resolve_left hs
  · have h0 := congrArg (fun A : M15 => A 4 4) h
    have h1 := congrArg (fun A : M15 => A 0 4) h
    have h2 := congrArg (fun A : M15 => A 8 4) h
    norm_num [lift,ia,ib,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,Fin.ext_iff] at h0 h1 h2
    have hz : s * M 1 5=0 := by
      linear_combination -M 1 5 * h0 + (1) * M 5 5 * h1 - (-1) * M 0 5 * h2
    exact (mul_eq_zero.mp hz).resolve_left hs
  · have h0 := congrArg (fun A : M15 => A 0 0) h
    have h1 := congrArg (fun A : M15 => A 5 0) h
    have h2 := congrArg (fun A : M15 => A 1 0) h
    norm_num [lift,ia,ib,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,Fin.ext_iff] at h0 h1 h2
    have hz : s * M 2 0=0 := by
      linear_combination -M 2 0 * h0 + (-1) * M 0 0 * h1 - (-1) * M 1 0 * h2
    exact (mul_eq_zero.mp hz).resolve_left hs
  · have h0 := congrArg (fun A : M15 => A 0 0) h
    have h1 := congrArg (fun A : M15 => A 1 0) h
    have h2 := congrArg (fun A : M15 => A 5 0) h
    norm_num [lift,ia,ib,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,Fin.ext_iff] at h0 h1 h2
    have hz : s * M 2 1=0 := by
      linear_combination -M 2 1 * h0 + (1) * M 1 1 * h1 - (1) * M 0 1 * h2
    exact (mul_eq_zero.mp hz).resolve_left hs
  · exact False.elim (hia rfl)
  · have h0 := congrArg (fun A : M15 => A 2 2) h
    have h1 := congrArg (fun A : M15 => A 1 2) h
    have h2 := congrArg (fun A : M15 => A 9 2) h
    norm_num [lift,ia,ib,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,Fin.ext_iff] at h0 h1 h2
    have hz : s * M 2 3=0 := by
      linear_combination -M 2 3 * h0 + (1) * M 3 3 * h1 - (-1) * M 0 3 * h2
    exact (mul_eq_zero.mp hz).resolve_left hs
  · have h0 := congrArg (fun A : M15 => A 3 3) h
    have h1 := congrArg (fun A : M15 => A 1 3) h
    have h2 := congrArg (fun A : M15 => A 10 3) h
    norm_num [lift,ia,ib,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,Fin.ext_iff] at h0 h1 h2
    have hz : s * M 2 4=0 := by
      linear_combination -M 2 4 * h0 + (1) * M 4 4 * h1 - (-1) * M 0 4 * h2
    exact (mul_eq_zero.mp hz).resolve_left hs
  · have h0 := congrArg (fun A : M15 => A 4 4) h
    have h1 := congrArg (fun A : M15 => A 1 4) h
    have h2 := congrArg (fun A : M15 => A 11 4) h
    norm_num [lift,ia,ib,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,Fin.ext_iff] at h0 h1 h2
    have hz : s * M 2 5=0 := by
      linear_combination -M 2 5 * h0 + (1) * M 5 5 * h1 - (-1) * M 0 5 * h2
    exact (mul_eq_zero.mp hz).resolve_left hs
  · have h0 := congrArg (fun A : M15 => A 0 0) h
    have h1 := congrArg (fun A : M15 => A 6 0) h
    have h2 := congrArg (fun A : M15 => A 2 0) h
    norm_num [lift,ia,ib,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,Fin.ext_iff] at h0 h1 h2
    have hz : s * M 3 0=0 := by
      linear_combination -M 3 0 * h0 + (-1) * M 0 0 * h1 - (-1) * M 1 0 * h2
    exact (mul_eq_zero.mp hz).resolve_left hs
  · have h0 := congrArg (fun A : M15 => A 0 0) h
    have h1 := congrArg (fun A : M15 => A 2 0) h
    have h2 := congrArg (fun A : M15 => A 6 0) h
    norm_num [lift,ia,ib,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,Fin.ext_iff] at h0 h1 h2
    have hz : s * M 3 1=0 := by
      linear_combination -M 3 1 * h0 + (1) * M 1 1 * h1 - (1) * M 0 1 * h2
    exact (mul_eq_zero.mp hz).resolve_left hs
  · have h0 := congrArg (fun A : M15 => A 1 1) h
    have h1 := congrArg (fun A : M15 => A 2 1) h
    have h2 := congrArg (fun A : M15 => A 9 1) h
    norm_num [lift,ia,ib,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,Fin.ext_iff] at h0 h1 h2
    have hz : s * M 3 2=0 := by
      linear_combination -M 3 2 * h0 + (1) * M 2 2 * h1 - (1) * M 0 2 * h2
    exact (mul_eq_zero.mp hz).resolve_left hs
  · exact False.elim (hia rfl)
  · have h0 := congrArg (fun A : M15 => A 3 3) h
    have h1 := congrArg (fun A : M15 => A 2 3) h
    have h2 := congrArg (fun A : M15 => A 12 3) h
    norm_num [lift,ia,ib,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,Fin.ext_iff] at h0 h1 h2
    have hz : s * M 3 4=0 := by
      linear_combination -M 3 4 * h0 + (1) * M 4 4 * h1 - (-1) * M 0 4 * h2
    exact (mul_eq_zero.mp hz).resolve_left hs
  · have h0 := congrArg (fun A : M15 => A 4 4) h
    have h1 := congrArg (fun A : M15 => A 2 4) h
    have h2 := congrArg (fun A : M15 => A 13 4) h
    norm_num [lift,ia,ib,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,Fin.ext_iff] at h0 h1 h2
    have hz : s * M 3 5=0 := by
      linear_combination -M 3 5 * h0 + (1) * M 5 5 * h1 - (-1) * M 0 5 * h2
    exact (mul_eq_zero.mp hz).resolve_left hs
  · have h0 := congrArg (fun A : M15 => A 0 0) h
    have h1 := congrArg (fun A : M15 => A 7 0) h
    have h2 := congrArg (fun A : M15 => A 3 0) h
    norm_num [lift,ia,ib,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,Fin.ext_iff] at h0 h1 h2
    have hz : s * M 4 0=0 := by
      linear_combination -M 4 0 * h0 + (-1) * M 0 0 * h1 - (-1) * M 1 0 * h2
    exact (mul_eq_zero.mp hz).resolve_left hs
  · have h0 := congrArg (fun A : M15 => A 0 0) h
    have h1 := congrArg (fun A : M15 => A 3 0) h
    have h2 := congrArg (fun A : M15 => A 7 0) h
    norm_num [lift,ia,ib,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,Fin.ext_iff] at h0 h1 h2
    have hz : s * M 4 1=0 := by
      linear_combination -M 4 1 * h0 + (1) * M 1 1 * h1 - (1) * M 0 1 * h2
    exact (mul_eq_zero.mp hz).resolve_left hs
  · have h0 := congrArg (fun A : M15 => A 1 1) h
    have h1 := congrArg (fun A : M15 => A 3 1) h
    have h2 := congrArg (fun A : M15 => A 10 1) h
    norm_num [lift,ia,ib,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,Fin.ext_iff] at h0 h1 h2
    have hz : s * M 4 2=0 := by
      linear_combination -M 4 2 * h0 + (1) * M 2 2 * h1 - (1) * M 0 2 * h2
    exact (mul_eq_zero.mp hz).resolve_left hs
  · have h0 := congrArg (fun A : M15 => A 2 2) h
    have h1 := congrArg (fun A : M15 => A 3 2) h
    have h2 := congrArg (fun A : M15 => A 12 2) h
    norm_num [lift,ia,ib,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,Fin.ext_iff] at h0 h1 h2
    have hz : s * M 4 3=0 := by
      linear_combination -M 4 3 * h0 + (1) * M 3 3 * h1 - (1) * M 0 3 * h2
    exact (mul_eq_zero.mp hz).resolve_left hs
  · exact False.elim (hia rfl)
  · have h0 := congrArg (fun A : M15 => A 4 4) h
    have h1 := congrArg (fun A : M15 => A 3 4) h
    have h2 := congrArg (fun A : M15 => A 14 4) h
    norm_num [lift,ia,ib,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,Fin.ext_iff] at h0 h1 h2
    have hz : s * M 4 5=0 := by
      linear_combination -M 4 5 * h0 + (1) * M 5 5 * h1 - (-1) * M 0 5 * h2
    exact (mul_eq_zero.mp hz).resolve_left hs
  · have h0 := congrArg (fun A : M15 => A 0 0) h
    have h1 := congrArg (fun A : M15 => A 8 0) h
    have h2 := congrArg (fun A : M15 => A 4 0) h
    norm_num [lift,ia,ib,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,Fin.ext_iff] at h0 h1 h2
    have hz : s * M 5 0=0 := by
      linear_combination -M 5 0 * h0 + (-1) * M 0 0 * h1 - (-1) * M 1 0 * h2
    exact (mul_eq_zero.mp hz).resolve_left hs
  · have h0 := congrArg (fun A : M15 => A 0 0) h
    have h1 := congrArg (fun A : M15 => A 4 0) h
    have h2 := congrArg (fun A : M15 => A 8 0) h
    norm_num [lift,ia,ib,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,Fin.ext_iff] at h0 h1 h2
    have hz : s * M 5 1=0 := by
      linear_combination -M 5 1 * h0 + (1) * M 1 1 * h1 - (1) * M 0 1 * h2
    exact (mul_eq_zero.mp hz).resolve_left hs
  · have h0 := congrArg (fun A : M15 => A 1 1) h
    have h1 := congrArg (fun A : M15 => A 4 1) h
    have h2 := congrArg (fun A : M15 => A 11 1) h
    norm_num [lift,ia,ib,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,Fin.ext_iff] at h0 h1 h2
    have hz : s * M 5 2=0 := by
      linear_combination -M 5 2 * h0 + (1) * M 2 2 * h1 - (1) * M 0 2 * h2
    exact (mul_eq_zero.mp hz).resolve_left hs
  · have h0 := congrArg (fun A : M15 => A 2 2) h
    have h1 := congrArg (fun A : M15 => A 4 2) h
    have h2 := congrArg (fun A : M15 => A 13 2) h
    norm_num [lift,ia,ib,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,Fin.ext_iff] at h0 h1 h2
    have hz : s * M 5 3=0 := by
      linear_combination -M 5 3 * h0 + (1) * M 3 3 * h1 - (1) * M 0 3 * h2
    exact (mul_eq_zero.mp hz).resolve_left hs
  · have h0 := congrArg (fun A : M15 => A 3 3) h
    have h1 := congrArg (fun A : M15 => A 4 3) h
    have h2 := congrArg (fun A : M15 => A 14 3) h
    norm_num [lift,ia,ib,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,Fin.ext_iff] at h0 h1 h2
    have hz : s * M 5 4=0 := by
      linear_combination -M 5 4 * h0 + (1) * M 4 4 * h1 - (1) * M 0 4 * h2
    exact (mul_eq_zero.mp hz).resolve_left hs
  · exact False.elim (hia rfl)

theorem scalar_diagonal (M : M6) (s : ℝ) (hs : s ≠ 0)
    (h : lift M=s • (1 : M15)) : M=Matrix.diagonal (fun i => M i i) := by
  ext i j
  by_cases hij : i=j
  · subst j; simp
  · simp [hij,scalar_off_diagonal M s hs h i j hij]

theorem scalar_pair (M : M6) (s : ℝ) (hs : s ≠ 0)
    (h : lift M=s • (1 : M15)) (a b : Fin 6) (hab : a ≠ b) : M a a*M b b=s := by
  have hd := scalar_diagonal M s hs h
  fin_cases a <;> fin_cases b
  · exact False.elim (hab rfl)
  · have hk := congrArg (fun A : M15 => A 0 0) h
    conv_lhs at hk => rw [hd]
    norm_num [lift,ia,ib,Matrix.diagonal_apply,Matrix.smul_apply,smul_eq_mul,
      Matrix.one_apply,Fin.ext_iff] at hk
    convert hk using 1; ring!
  · have hk := congrArg (fun A : M15 => A 1 1) h
    conv_lhs at hk => rw [hd]
    norm_num [lift,ia,ib,Matrix.diagonal_apply,Matrix.smul_apply,smul_eq_mul,
      Matrix.one_apply,Fin.ext_iff] at hk
    convert hk using 1; ring!
  · have hk := congrArg (fun A : M15 => A 2 2) h
    conv_lhs at hk => rw [hd]
    norm_num [lift,ia,ib,Matrix.diagonal_apply,Matrix.smul_apply,smul_eq_mul,
      Matrix.one_apply,Fin.ext_iff] at hk
    convert hk using 1; ring!
  · have hk := congrArg (fun A : M15 => A 3 3) h
    conv_lhs at hk => rw [hd]
    norm_num [lift,ia,ib,Matrix.diagonal_apply,Matrix.smul_apply,smul_eq_mul,
      Matrix.one_apply,Fin.ext_iff] at hk
    convert hk using 1; ring!
  · have hk := congrArg (fun A : M15 => A 4 4) h
    conv_lhs at hk => rw [hd]
    norm_num [lift,ia,ib,Matrix.diagonal_apply,Matrix.smul_apply,smul_eq_mul,
      Matrix.one_apply,Fin.ext_iff] at hk
    convert hk using 1; ring!
  · have hk := congrArg (fun A : M15 => A 0 0) h
    conv_lhs at hk => rw [hd]
    norm_num [lift,ia,ib,Matrix.diagonal_apply,Matrix.smul_apply,smul_eq_mul,
      Matrix.one_apply,Fin.ext_iff] at hk
    convert hk using 1; ring!
  · exact False.elim (hab rfl)
  · have hk := congrArg (fun A : M15 => A 5 5) h
    conv_lhs at hk => rw [hd]
    norm_num [lift,ia,ib,Matrix.diagonal_apply,Matrix.smul_apply,smul_eq_mul,
      Matrix.one_apply,Fin.ext_iff] at hk
    convert hk using 1; ring!
  · have hk := congrArg (fun A : M15 => A 6 6) h
    conv_lhs at hk => rw [hd]
    norm_num [lift,ia,ib,Matrix.diagonal_apply,Matrix.smul_apply,smul_eq_mul,
      Matrix.one_apply,Fin.ext_iff] at hk
    convert hk using 1; ring!
  · have hk := congrArg (fun A : M15 => A 7 7) h
    conv_lhs at hk => rw [hd]
    norm_num [lift,ia,ib,Matrix.diagonal_apply,Matrix.smul_apply,smul_eq_mul,
      Matrix.one_apply,Fin.ext_iff] at hk
    convert hk using 1; ring!
  · have hk := congrArg (fun A : M15 => A 8 8) h
    conv_lhs at hk => rw [hd]
    norm_num [lift,ia,ib,Matrix.diagonal_apply,Matrix.smul_apply,smul_eq_mul,
      Matrix.one_apply,Fin.ext_iff] at hk
    convert hk using 1; ring!
  · have hk := congrArg (fun A : M15 => A 1 1) h
    conv_lhs at hk => rw [hd]
    norm_num [lift,ia,ib,Matrix.diagonal_apply,Matrix.smul_apply,smul_eq_mul,
      Matrix.one_apply,Fin.ext_iff] at hk
    convert hk using 1; ring!
  · have hk := congrArg (fun A : M15 => A 5 5) h
    conv_lhs at hk => rw [hd]
    norm_num [lift,ia,ib,Matrix.diagonal_apply,Matrix.smul_apply,smul_eq_mul,
      Matrix.one_apply,Fin.ext_iff] at hk
    convert hk using 1; ring!
  · exact False.elim (hab rfl)
  · have hk := congrArg (fun A : M15 => A 9 9) h
    conv_lhs at hk => rw [hd]
    norm_num [lift,ia,ib,Matrix.diagonal_apply,Matrix.smul_apply,smul_eq_mul,
      Matrix.one_apply,Fin.ext_iff] at hk
    convert hk using 1; ring!
  · have hk := congrArg (fun A : M15 => A 10 10) h
    conv_lhs at hk => rw [hd]
    norm_num [lift,ia,ib,Matrix.diagonal_apply,Matrix.smul_apply,smul_eq_mul,
      Matrix.one_apply,Fin.ext_iff] at hk
    convert hk using 1; ring!
  · have hk := congrArg (fun A : M15 => A 11 11) h
    conv_lhs at hk => rw [hd]
    norm_num [lift,ia,ib,Matrix.diagonal_apply,Matrix.smul_apply,smul_eq_mul,
      Matrix.one_apply,Fin.ext_iff] at hk
    convert hk using 1; ring!
  · have hk := congrArg (fun A : M15 => A 2 2) h
    conv_lhs at hk => rw [hd]
    norm_num [lift,ia,ib,Matrix.diagonal_apply,Matrix.smul_apply,smul_eq_mul,
      Matrix.one_apply,Fin.ext_iff] at hk
    convert hk using 1; ring!
  · have hk := congrArg (fun A : M15 => A 6 6) h
    conv_lhs at hk => rw [hd]
    norm_num [lift,ia,ib,Matrix.diagonal_apply,Matrix.smul_apply,smul_eq_mul,
      Matrix.one_apply,Fin.ext_iff] at hk
    convert hk using 1; ring!
  · have hk := congrArg (fun A : M15 => A 9 9) h
    conv_lhs at hk => rw [hd]
    norm_num [lift,ia,ib,Matrix.diagonal_apply,Matrix.smul_apply,smul_eq_mul,
      Matrix.one_apply,Fin.ext_iff] at hk
    convert hk using 1; ring!
  · exact False.elim (hab rfl)
  · have hk := congrArg (fun A : M15 => A 12 12) h
    conv_lhs at hk => rw [hd]
    norm_num [lift,ia,ib,Matrix.diagonal_apply,Matrix.smul_apply,smul_eq_mul,
      Matrix.one_apply,Fin.ext_iff] at hk
    convert hk using 1; ring!
  · have hk := congrArg (fun A : M15 => A 13 13) h
    conv_lhs at hk => rw [hd]
    norm_num [lift,ia,ib,Matrix.diagonal_apply,Matrix.smul_apply,smul_eq_mul,
      Matrix.one_apply,Fin.ext_iff] at hk
    convert hk using 1; ring!
  · have hk := congrArg (fun A : M15 => A 3 3) h
    conv_lhs at hk => rw [hd]
    norm_num [lift,ia,ib,Matrix.diagonal_apply,Matrix.smul_apply,smul_eq_mul,
      Matrix.one_apply,Fin.ext_iff] at hk
    convert hk using 1; ring!
  · have hk := congrArg (fun A : M15 => A 7 7) h
    conv_lhs at hk => rw [hd]
    norm_num [lift,ia,ib,Matrix.diagonal_apply,Matrix.smul_apply,smul_eq_mul,
      Matrix.one_apply,Fin.ext_iff] at hk
    convert hk using 1; ring!
  · have hk := congrArg (fun A : M15 => A 10 10) h
    conv_lhs at hk => rw [hd]
    norm_num [lift,ia,ib,Matrix.diagonal_apply,Matrix.smul_apply,smul_eq_mul,
      Matrix.one_apply,Fin.ext_iff] at hk
    convert hk using 1; ring!
  · have hk := congrArg (fun A : M15 => A 12 12) h
    conv_lhs at hk => rw [hd]
    norm_num [lift,ia,ib,Matrix.diagonal_apply,Matrix.smul_apply,smul_eq_mul,
      Matrix.one_apply,Fin.ext_iff] at hk
    convert hk using 1; ring!
  · exact False.elim (hab rfl)
  · have hk := congrArg (fun A : M15 => A 14 14) h
    conv_lhs at hk => rw [hd]
    norm_num [lift,ia,ib,Matrix.diagonal_apply,Matrix.smul_apply,smul_eq_mul,
      Matrix.one_apply,Fin.ext_iff] at hk
    convert hk using 1; ring!
  · have hk := congrArg (fun A : M15 => A 4 4) h
    conv_lhs at hk => rw [hd]
    norm_num [lift,ia,ib,Matrix.diagonal_apply,Matrix.smul_apply,smul_eq_mul,
      Matrix.one_apply,Fin.ext_iff] at hk
    convert hk using 1; ring!
  · have hk := congrArg (fun A : M15 => A 8 8) h
    conv_lhs at hk => rw [hd]
    norm_num [lift,ia,ib,Matrix.diagonal_apply,Matrix.smul_apply,smul_eq_mul,
      Matrix.one_apply,Fin.ext_iff] at hk
    convert hk using 1; ring!
  · have hk := congrArg (fun A : M15 => A 11 11) h
    conv_lhs at hk => rw [hd]
    norm_num [lift,ia,ib,Matrix.diagonal_apply,Matrix.smul_apply,smul_eq_mul,
      Matrix.one_apply,Fin.ext_iff] at hk
    convert hk using 1; ring!
  · have hk := congrArg (fun A : M15 => A 13 13) h
    conv_lhs at hk => rw [hd]
    norm_num [lift,ia,ib,Matrix.diagonal_apply,Matrix.smul_apply,smul_eq_mul,
      Matrix.one_apply,Fin.ext_iff] at hk
    convert hk using 1; ring!
  · have hk := congrArg (fun A : M15 => A 14 14) h
    conv_lhs at hk => rw [hd]
    norm_num [lift,ia,ib,Matrix.diagonal_apply,Matrix.smul_apply,smul_eq_mul,
      Matrix.one_apply,Fin.ext_iff] at hk
    convert hk using 1; ring!
  · exact False.elim (hab rfl)

#print axioms lift_neg
#print axioms scalar_diagonal
#print axioms scalar_pair
/-- A nonzero scalar exterior action forces a scalar real ambient matrix. -/
theorem scalar_matrix (M : M6) (s : ℝ) (hs : s ≠ 0)
    (h : lift M=s • (1 : M15)) : ∃ a : ℝ, M=a • (1 : M6) ∧ a^2=s := by
  have hp := scalar_pair M s hs h
  have hn1 : M 1 1 ≠ 0 := by
    intro hz
    have hh := hp 0 1 (by decide)
    rw [hz,mul_zero] at hh
    exact hs hh.symm
  have hn2 : M 2 2 ≠ 0 := by
    intro hz
    have hh := hp 0 2 (by decide)
    rw [hz,mul_zero] at hh
    exact hs hh.symm
  have he (i : Fin 6) : M i i=M 0 0 := by
    by_cases hi : i=1
    · subst i
      apply mul_right_cancel₀ hn2
      rw [hp 1 2 (by decide),hp 0 2 (by decide)]
    · apply mul_right_cancel₀ hn1
      rw [hp i 1 hi,hp 0 1 (by decide)]
  refine ⟨M 0 0,?_,?_⟩
  · rw [scalar_diagonal M s hs h]
    ext i j
    simp [Matrix.diagonal_apply,Matrix.smul_apply,Matrix.one_apply,he]
  · have hh := hp 0 1 (by decide)
    rw [he 1] at hh
    nlinarith

theorem kernel_iff (M : M6) : lift M=1 ↔ M=1 ∨ M= -1 := by
  constructor
  · intro h
    obtain ⟨a,ha,hs⟩ := scalar_matrix M 1 (by norm_num) (by simpa using h)
    have hz : (a-1)*(a+1)=0 := by nlinarith
    rcases mul_eq_zero.mp hz with hp | hn
    · left
      have : a=1 := by linarith
      simpa [this] using ha
    · right
      have : a= -1 := by linarith
      simpa [this] using ha
  · rintro (rfl | rfl)
    · exact lift_one
    · rw [lift_neg,lift_one]

/-- The negative identity on the real bivector register has no real exterior lift. -/
theorem no_negative_identity (M : M6) : lift M ≠ -(1 : M15) := by
  intro h
  obtain ⟨a,_,hs⟩ := scalar_matrix M (-1) (by norm_num) (by simpa using h)
  nlinarith [sq_nonneg a]

/-- Any invertible ambient lift is unique up to its overall sign. -/
theorem lift_fiber (M N : M6) (hn : N.det ≠ 0) :
    lift M=lift N ↔ M=N ∨ M= -N := by
  have hnu : IsUnit N.det := isUnit_iff_ne_zero.mpr hn
  have hi := Matrix.mul_nonsing_inv N hnu
  have hj := Matrix.nonsing_inv_mul N hnu
  constructor
  · intro h
    have hk : lift (M*N⁻¹)=1 := by
      rw [lift_mul,h,← lift_mul,hi,lift_one]
    rcases (kernel_iff _).mp hk with hp | hm
    · left
      have hh := congrArg (fun A : M6 => A*N) hp
      simpa only [Matrix.mul_assoc,hj,Matrix.mul_one,Matrix.one_mul] using hh
    · right
      have hh := congrArg (fun A : M6 => A*N) hm
      simpa only [Matrix.mul_assoc,hj,Matrix.mul_one,Matrix.neg_mul,Matrix.one_mul] using hh
  · rintro (rfl | rfl)
    · rfl
    · exact lift_neg N

#print axioms scalar_matrix
#print axioms kernel_iff
#print axioms no_negative_identity
#print axioms lift_fiber

end
end PDTExteriorKernel
