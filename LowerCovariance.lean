module
public import CrossSource

@[expose] public section
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
-- Uniform finite certificates share the same normalization steps.
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
namespace PDTPolynomialSource
noncomputable section
open PDTStressTensor PDTUnrestrictedSourceKernel PDTQuadraticSource PDTConservedSource
open scoped Matrix

private theorem constant_row_0 (A : ConstantCoeff) (h : ConstantInvariant A) : (2)*A 1=0 := by
  have hh := congrFun (congrFun (h 0) 0) 0
  norm_num [tensorAction,lorentz_formula,lorentzTable,constant,tensorIndex,
    Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ] at hh
  try dsimp at hh
  norm_num at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]
private theorem constant_row_1 (A : ConstantCoeff) (h : ConstantInvariant A) : (-1)*A 0 + (1)*A 4=0 := by
  have hh := congrFun (congrFun (h 0) 0) 1
  norm_num [tensorAction,lorentz_formula,lorentzTable,constant,tensorIndex,
    Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ] at hh
  try dsimp at hh
  norm_num at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]
private theorem constant_row_2 (A : ConstantCoeff) (h : ConstantInvariant A) : (1)*A 5=0 := by
  have hh := congrFun (congrFun (h 0) 0) 2
  norm_num [tensorAction,lorentz_formula,lorentzTable,constant,tensorIndex,
    Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ] at hh
  try dsimp at hh
  norm_num at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]
private theorem constant_row_3 (A : ConstantCoeff) (h : ConstantInvariant A) : (1)*A 6=0 := by
  have hh := congrFun (congrFun (h 0) 0) 3
  norm_num [tensorAction,lorentz_formula,lorentzTable,constant,tensorIndex,
    Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ] at hh
  try dsimp at hh
  norm_num at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]
private theorem constant_row_4 (A : ConstantCoeff) (h : ConstantInvariant A) : (-1)*A 2=0 := by
  have hh := congrFun (congrFun (h 0) 1) 2
  norm_num [tensorAction,lorentz_formula,lorentzTable,constant,tensorIndex,
    Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ] at hh
  try dsimp at hh
  norm_num at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]
private theorem constant_row_5 (A : ConstantCoeff) (h : ConstantInvariant A) : (-1)*A 3=0 := by
  have hh := congrFun (congrFun (h 0) 1) 3
  norm_num [tensorAction,lorentz_formula,lorentzTable,constant,tensorIndex,
    Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ] at hh
  try dsimp at hh
  norm_num at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]
private theorem constant_row_6 (A : ConstantCoeff) (h : ConstantInvariant A) : (-1)*A 0 + (1)*A 7=0 := by
  have hh := congrFun (congrFun (h 1) 0) 2
  norm_num [tensorAction,lorentz_formula,lorentzTable,constant,tensorIndex,
    Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ] at hh
  try dsimp at hh
  norm_num at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]
private theorem constant_row_7 (A : ConstantCoeff) (h : ConstantInvariant A) : (1)*A 8=0 := by
  have hh := congrFun (congrFun (h 1) 0) 3
  norm_num [tensorAction,lorentz_formula,lorentzTable,constant,tensorIndex,
    Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ] at hh
  try dsimp at hh
  norm_num at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]
private theorem constant_row_8 (A : ConstantCoeff) (h : ConstantInvariant A) : (-1)*A 0 + (-1)*A 9=0 := by
  have hh := congrFun (congrFun (h 2) 0) 3
  norm_num [tensorAction,lorentz_formula,lorentzTable,constant,tensorIndex,
    Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ] at hh
  try dsimp at hh
  norm_num at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]
theorem constant_recovery (A : ConstantCoeff) (h : ConstantInvariant A) :
    A=![A 0,0,0,0,A 0,0,0,A 0,0,-A 0] := by
  have h0 : (2)*A 1=0 := constant_row_0 A h
  have h1 : (-1)*A 0 + (1)*A 4=0 := constant_row_1 A h
  have h2 : (1)*A 5=0 := constant_row_2 A h
  have h3 : (1)*A 6=0 := constant_row_3 A h
  have h4 : (-1)*A 2=0 := constant_row_4 A h
  have h5 : (-1)*A 3=0 := constant_row_5 A h
  have h6 : (-1)*A 0 + (1)*A 7=0 := constant_row_6 A h
  have h7 : (1)*A 8=0 := constant_row_7 A h
  have h8 : (-1)*A 0 + (-1)*A 9=0 := constant_row_8 A h
  ext t
  fin_cases t
  · change A 0 = A 0
    ring
  · change A 1 = 0
    linear_combination (1/2 : ℝ)*h0
  · change A 2 = 0
    linear_combination (-1 : ℝ)*h4
  · change A 3 = 0
    linear_combination (-1 : ℝ)*h5
  · change A 4 = A 0
    linear_combination (1 : ℝ)*h1
  · change A 5 = 0
    linear_combination (1 : ℝ)*h2
  · change A 6 = 0
    linear_combination (1 : ℝ)*h3
  · change A 7 = A 0
    linear_combination (1 : ℝ)*h6
  · change A 8 = 0
    linear_combination (1 : ℝ)*h7
  · change A 9 = -A 0
    linear_combination (-1 : ℝ)*h8
theorem constant_is_metric (A : ConstantCoeff) (h : ConstantInvariant A) :
    constant A=(A 0) • metric := by
  have hr := constant_recovery A h
  conv_lhs => rw [hr]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [constant,tensorIndex,metric,eta,Matrix.diagonal_apply]

private theorem background_row_0 (b : Local) (h : LinearCovariant (crossCoefficients b)) : (-1)*b 3=0 := by
  have hh := congrFun (congrFun (h 0 ![0,1,0,0,0,0]) 0) 0
  norm_num [linear,crossCoefficients,tensorIndex,field_action_formula,tensorAction,
    lorentz_formula,lorentzTable,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ] at hh
  try dsimp at hh
  norm_num at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]
private theorem background_row_1 (b : Local) (h : LinearCovariant (crossCoefficients b)) : (1)*b 4=0 := by
  have hh := congrFun (congrFun (h 0 ![0,0,1,0,0,0]) 0) 0
  norm_num [linear,crossCoefficients,tensorIndex,field_action_formula,tensorAction,
    lorentz_formula,lorentzTable,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ] at hh
  try dsimp at hh
  norm_num at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]
private theorem background_row_2 (b : Local) (h : LinearCovariant (crossCoefficients b)) : (-1)*b 1=0 := by
  have hh := congrFun (congrFun (h 0 ![0,0,0,1,0,0]) 0) 0
  norm_num [linear,crossCoefficients,tensorIndex,field_action_formula,tensorAction,
    lorentz_formula,lorentzTable,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ] at hh
  try dsimp at hh
  norm_num at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]
private theorem background_row_3 (b : Local) (h : LinearCovariant (crossCoefficients b)) : (1)*b 2=0 := by
  have hh := congrFun (congrFun (h 0 ![0,0,0,0,1,0]) 0) 0
  norm_num [linear,crossCoefficients,tensorIndex,field_action_formula,tensorAction,
    lorentz_formula,lorentzTable,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ] at hh
  try dsimp at hh
  norm_num at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]
private theorem background_row_4 (b : Local) (h : LinearCovariant (crossCoefficients b)) : (1)*b 5=0 := by
  have hh := congrFun (congrFun (h 1 ![0,0,1,0,0,0]) 0) 0
  norm_num [linear,crossCoefficients,tensorIndex,field_action_formula,tensorAction,
    lorentz_formula,lorentzTable,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ] at hh
  try dsimp at hh
  norm_num at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]
private theorem background_row_5 (b : Local) (h : LinearCovariant (crossCoefficients b)) : (1)*b 0=0 := by
  have hh := congrFun (congrFun (h 1 ![0,0,0,1,0,0]) 0) 0
  norm_num [linear,crossCoefficients,tensorIndex,field_action_formula,tensorAction,
    lorentz_formula,lorentzTable,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ] at hh
  try dsimp at hh
  norm_num at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]
theorem covariant_background_zero (b : Local) (h : LinearCovariant (crossCoefficients b)) : b=0 := by
  have h0 := background_row_0 b h
  have h1 := background_row_1 b h
  have h2 := background_row_2 b h
  have h3 := background_row_3 b h
  have h4 := background_row_4 b h
  have h5 := background_row_5 b h
  ext a
  fin_cases a
  · change b 0=0
    linear_combination (1 : ℝ)*h5
  · change b 1=0
    linear_combination (-1 : ℝ)*h2
  · change b 2=0
    linear_combination (1 : ℝ)*h3
  · change b 3=0
    linear_combination (-1 : ℝ)*h0
  · change b 4=0
    linear_combination (1 : ℝ)*h1
  · change b 5=0
    linear_combination (1 : ℝ)*h4
theorem metric_tensor_action (k : Fin 6) (c : ℝ) : tensorAction k (c • metric)=0 := by
  ext i j
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    norm_num [tensorAction,lorentz_formula,lorentzTable,metric,eta,
      Matrix.diagonal_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ]

#print axioms constant_recovery
#print axioms constant_is_metric
#print axioms covariant_background_zero
#print axioms metric_tensor_action
end
end PDTPolynomialSource
