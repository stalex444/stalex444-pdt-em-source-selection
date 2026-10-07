module
public import SourceCoefficientData

@[expose] public section
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
namespace PDTQuadraticSource
noncomputable section
open PDTStressTensor PDTUnrestrictedSourceKernel
open scoped Matrix

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

private theorem constraint_000 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : (-2) * c 1 0=0 := by
  have h := defect_zero c hc 0 (![1,0,0,0,0,0]) 0 0
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_001 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : (-1) * c 0 3 + (-2) * c 1 1=0 := by
  have h := defect_zero c hc 0 (![1,0,0,0,0,0]+![0,1,0,0,0,0]) 0 0
  have ha := defect_zero c hc 0 (![1,0,0,0,0,0]) 0 0
  have hb := defect_zero c hc 0 (![0,1,0,0,0,0]) 0 0
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_002 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : (-1) * c 0 4 + (-2) * c 1 2=0 := by
  have h := defect_zero c hc 0 (![1,0,0,0,0,0]+![0,0,1,0,0,0]) 0 0
  have ha := defect_zero c hc 0 (![1,0,0,0,0,0]) 0 0
  have hb := defect_zero c hc 0 (![0,0,1,0,0,0]) 0 0
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_003 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 1 * c 0 1 + (-2) * c 1 3=0 := by
  have h := defect_zero c hc 0 (![1,0,0,0,0,0]+![0,0,0,1,0,0]) 0 0
  have ha := defect_zero c hc 0 (![1,0,0,0,0,0]) 0 0
  have hb := defect_zero c hc 0 (![0,0,0,1,0,0]) 0 0
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_004 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 1 * c 0 2 + (-2) * c 1 4=0 := by
  have h := defect_zero c hc 0 (![1,0,0,0,0,0]+![0,0,0,0,1,0]) 0 0
  have ha := defect_zero c hc 0 (![1,0,0,0,0,0]) 0 0
  have hb := defect_zero c hc 0 (![0,0,0,0,1,0]) 0 0
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_005 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : (-2) * c 1 5=0 := by
  have h := defect_zero c hc 0 (![1,0,0,0,0,0]+![0,0,0,0,0,1]) 0 0
  have ha := defect_zero c hc 0 (![1,0,0,0,0,0]) 0 0
  have hb := defect_zero c hc 0 (![0,0,0,0,0,1]) 0 0
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_006 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : (-1) * c 0 8 + (-2) * c 1 6=0 := by
  have h := defect_zero c hc 0 (![0,1,0,0,0,0]) 0 0
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_007 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : (-1) * c 0 9 + (-1) * c 0 12 + (-2) * c 1 7=0 := by
  have h := defect_zero c hc 0 (![0,1,0,0,0,0]+![0,0,1,0,0,0]) 0 0
  have ha := defect_zero c hc 0 (![0,1,0,0,0,0]) 0 0
  have hb := defect_zero c hc 0 (![0,0,1,0,0,0]) 0 0
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_008 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 2 * c 0 6 + (-2) * c 0 15 + (-2) * c 1 8=0 := by
  have h := defect_zero c hc 0 (![0,1,0,0,0,0]+![0,0,0,1,0,0]) 0 0
  have ha := defect_zero c hc 0 (![0,1,0,0,0,0]) 0 0
  have hb := defect_zero c hc 0 (![0,0,0,1,0,0]) 0 0
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_009 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 1 * c 0 7 + (-1) * c 0 16 + (-2) * c 1 9=0 := by
  have h := defect_zero c hc 0 (![0,1,0,0,0,0]+![0,0,0,0,1,0]) 0 0
  have ha := defect_zero c hc 0 (![0,1,0,0,0,0]) 0 0
  have hb := defect_zero c hc 0 (![0,0,0,0,1,0]) 0 0
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_010 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : (-1) * c 0 17 + (-2) * c 1 10=0 := by
  have h := defect_zero c hc 0 (![0,1,0,0,0,0]+![0,0,0,0,0,1]) 0 0
  have ha := defect_zero c hc 0 (![0,1,0,0,0,0]) 0 0
  have hb := defect_zero c hc 0 (![0,0,0,0,0,1]) 0 0
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_011 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : (-1) * c 0 13 + (-2) * c 1 11=0 := by
  have h := defect_zero c hc 0 (![0,0,1,0,0,0]) 0 0
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_012 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 1 * c 0 7 + (-1) * c 0 16 + (-2) * c 1 12=0 := by
  have h := defect_zero c hc 0 (![0,0,1,0,0,0]+![0,0,0,1,0,0]) 0 0
  have ha := defect_zero c hc 0 (![0,0,1,0,0,0]) 0 0
  have hb := defect_zero c hc 0 (![0,0,0,1,0,0]) 0 0
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_013 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 2 * c 0 11 + (-2) * c 0 18 + (-2) * c 1 13=0 := by
  have h := defect_zero c hc 0 (![0,0,1,0,0,0]+![0,0,0,0,1,0]) 0 0
  have ha := defect_zero c hc 0 (![0,0,1,0,0,0]) 0 0
  have hb := defect_zero c hc 0 (![0,0,0,0,1,0]) 0 0
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_014 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : (-1) * c 0 19 + (-2) * c 1 14=0 := by
  have h := defect_zero c hc 0 (![0,0,1,0,0,0]+![0,0,0,0,0,1]) 0 0
  have ha := defect_zero c hc 0 (![0,0,1,0,0,0]) 0 0
  have hb := defect_zero c hc 0 (![0,0,0,0,0,1]) 0 0
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_015 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 1 * c 0 8 + (-2) * c 1 15=0 := by
  have h := defect_zero c hc 0 (![0,0,0,1,0,0]) 0 0
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_016 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 1 * c 0 9 + 1 * c 0 12 + (-2) * c 1 16=0 := by
  have h := defect_zero c hc 0 (![0,0,0,1,0,0]+![0,0,0,0,1,0]) 0 0
  have ha := defect_zero c hc 0 (![0,0,0,1,0,0]) 0 0
  have hb := defect_zero c hc 0 (![0,0,0,0,1,0]) 0 0
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_017 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 1 * c 0 10 + (-2) * c 1 17=0 := by
  have h := defect_zero c hc 0 (![0,0,0,1,0,0]+![0,0,0,0,0,1]) 0 0
  have ha := defect_zero c hc 0 (![0,0,0,1,0,0]) 0 0
  have hb := defect_zero c hc 0 (![0,0,0,0,0,1]) 0 0
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_018 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 1 * c 0 13 + (-2) * c 1 18=0 := by
  have h := defect_zero c hc 0 (![0,0,0,0,1,0]) 0 0
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_019 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 1 * c 0 14 + (-2) * c 1 19=0 := by
  have h := defect_zero c hc 0 (![0,0,0,0,1,0]+![0,0,0,0,0,1]) 0 0
  have ha := defect_zero c hc 0 (![0,0,0,0,1,0]) 0 0
  have hb := defect_zero c hc 0 (![0,0,0,0,0,1]) 0 0
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_020 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : (-2) * c 1 20=0 := by
  have h := defect_zero c hc 0 (![0,0,0,0,0,1]) 0 0
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_021 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 1 * c 0 0 + (-1) * c 4 0=0 := by
  have h := defect_zero c hc 0 (![1,0,0,0,0,0]) 0 1
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_022 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : (-1) * c 1 3 + 1 * c 0 1 + (-1) * c 4 1=0 := by
  have h := defect_zero c hc 0 (![1,0,0,0,0,0]+![0,1,0,0,0,0]) 0 1
  have ha := defect_zero c hc 0 (![1,0,0,0,0,0]) 0 1
  have hb := defect_zero c hc 0 (![0,1,0,0,0,0]) 0 1
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_023 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : (-1) * c 1 4 + 1 * c 0 2 + (-1) * c 4 2=0 := by
  have h := defect_zero c hc 0 (![1,0,0,0,0,0]+![0,0,1,0,0,0]) 0 1
  have ha := defect_zero c hc 0 (![1,0,0,0,0,0]) 0 1
  have hb := defect_zero c hc 0 (![0,0,1,0,0,0]) 0 1
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_024 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 1 * c 1 1 + 1 * c 0 3 + (-1) * c 4 3=0 := by
  have h := defect_zero c hc 0 (![1,0,0,0,0,0]+![0,0,0,1,0,0]) 0 1
  have ha := defect_zero c hc 0 (![1,0,0,0,0,0]) 0 1
  have hb := defect_zero c hc 0 (![0,0,0,1,0,0]) 0 1
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_025 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 1 * c 1 2 + 1 * c 0 4 + (-1) * c 4 4=0 := by
  have h := defect_zero c hc 0 (![1,0,0,0,0,0]+![0,0,0,0,1,0]) 0 1
  have ha := defect_zero c hc 0 (![1,0,0,0,0,0]) 0 1
  have hb := defect_zero c hc 0 (![0,0,0,0,1,0]) 0 1
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_026 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 1 * c 0 5 + (-1) * c 4 5=0 := by
  have h := defect_zero c hc 0 (![1,0,0,0,0,0]+![0,0,0,0,0,1]) 0 1
  have ha := defect_zero c hc 0 (![1,0,0,0,0,0]) 0 1
  have hb := defect_zero c hc 0 (![0,0,0,0,0,1]) 0 1
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_027 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : (-1) * c 1 8 + 1 * c 0 6 + (-1) * c 4 6=0 := by
  have h := defect_zero c hc 0 (![0,1,0,0,0,0]) 0 1
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_028 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : (-1) * c 1 9 + (-1) * c 1 12 + 1 * c 0 7 + (-1) * c 4 7=0 := by
  have h := defect_zero c hc 0 (![0,1,0,0,0,0]+![0,0,1,0,0,0]) 0 1
  have ha := defect_zero c hc 0 (![0,1,0,0,0,0]) 0 1
  have hb := defect_zero c hc 0 (![0,0,1,0,0,0]) 0 1
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_029 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 2 * c 1 6 + (-2) * c 1 15 + 1 * c 0 8 + (-1) * c 4 8=0 := by
  have h := defect_zero c hc 0 (![0,1,0,0,0,0]+![0,0,0,1,0,0]) 0 1
  have ha := defect_zero c hc 0 (![0,1,0,0,0,0]) 0 1
  have hb := defect_zero c hc 0 (![0,0,0,1,0,0]) 0 1
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_030 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 1 * c 1 7 + (-1) * c 1 16 + 1 * c 0 9 + (-1) * c 4 9=0 := by
  have h := defect_zero c hc 0 (![0,1,0,0,0,0]+![0,0,0,0,1,0]) 0 1
  have ha := defect_zero c hc 0 (![0,1,0,0,0,0]) 0 1
  have hb := defect_zero c hc 0 (![0,0,0,0,1,0]) 0 1
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_031 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : (-1) * c 1 17 + 1 * c 0 10 + (-1) * c 4 10=0 := by
  have h := defect_zero c hc 0 (![0,1,0,0,0,0]+![0,0,0,0,0,1]) 0 1
  have ha := defect_zero c hc 0 (![0,1,0,0,0,0]) 0 1
  have hb := defect_zero c hc 0 (![0,0,0,0,0,1]) 0 1
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_032 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : (-1) * c 1 13 + 1 * c 0 11 + (-1) * c 4 11=0 := by
  have h := defect_zero c hc 0 (![0,0,1,0,0,0]) 0 1
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_033 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 1 * c 1 7 + (-1) * c 1 16 + 1 * c 0 12 + (-1) * c 4 12=0 := by
  have h := defect_zero c hc 0 (![0,0,1,0,0,0]+![0,0,0,1,0,0]) 0 1
  have ha := defect_zero c hc 0 (![0,0,1,0,0,0]) 0 1
  have hb := defect_zero c hc 0 (![0,0,0,1,0,0]) 0 1
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_034 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 2 * c 1 11 + (-2) * c 1 18 + 1 * c 0 13 + (-1) * c 4 13=0 := by
  have h := defect_zero c hc 0 (![0,0,1,0,0,0]+![0,0,0,0,1,0]) 0 1
  have ha := defect_zero c hc 0 (![0,0,1,0,0,0]) 0 1
  have hb := defect_zero c hc 0 (![0,0,0,0,1,0]) 0 1
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_035 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : (-1) * c 1 19 + 1 * c 0 14 + (-1) * c 4 14=0 := by
  have h := defect_zero c hc 0 (![0,0,1,0,0,0]+![0,0,0,0,0,1]) 0 1
  have ha := defect_zero c hc 0 (![0,0,1,0,0,0]) 0 1
  have hb := defect_zero c hc 0 (![0,0,0,0,0,1]) 0 1
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_036 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 1 * c 1 8 + 1 * c 0 15 + (-1) * c 4 15=0 := by
  have h := defect_zero c hc 0 (![0,0,0,1,0,0]) 0 1
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_037 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 1 * c 1 9 + 1 * c 1 12 + 1 * c 0 16 + (-1) * c 4 16=0 := by
  have h := defect_zero c hc 0 (![0,0,0,1,0,0]+![0,0,0,0,1,0]) 0 1
  have ha := defect_zero c hc 0 (![0,0,0,1,0,0]) 0 1
  have hb := defect_zero c hc 0 (![0,0,0,0,1,0]) 0 1
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_038 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 1 * c 1 10 + 1 * c 0 17 + (-1) * c 4 17=0 := by
  have h := defect_zero c hc 0 (![0,0,0,1,0,0]+![0,0,0,0,0,1]) 0 1
  have ha := defect_zero c hc 0 (![0,0,0,1,0,0]) 0 1
  have hb := defect_zero c hc 0 (![0,0,0,0,0,1]) 0 1
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_039 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 1 * c 1 13 + 1 * c 0 18 + (-1) * c 4 18=0 := by
  have h := defect_zero c hc 0 (![0,0,0,0,1,0]) 0 1
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_040 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 1 * c 1 14 + 1 * c 0 19 + (-1) * c 4 19=0 := by
  have h := defect_zero c hc 0 (![0,0,0,0,1,0]+![0,0,0,0,0,1]) 0 1
  have ha := defect_zero c hc 0 (![0,0,0,0,1,0]) 0 1
  have hb := defect_zero c hc 0 (![0,0,0,0,0,1]) 0 1
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_041 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 1 * c 0 20 + (-1) * c 4 20=0 := by
  have h := defect_zero c hc 0 (![0,0,0,0,0,1]) 0 1
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_042 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : (-1) * c 5 0=0 := by
  have h := defect_zero c hc 0 (![1,0,0,0,0,0]) 0 2
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_043 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : (-1) * c 2 3 + (-1) * c 5 1=0 := by
  have h := defect_zero c hc 0 (![1,0,0,0,0,0]+![0,1,0,0,0,0]) 0 2
  have ha := defect_zero c hc 0 (![1,0,0,0,0,0]) 0 2
  have hb := defect_zero c hc 0 (![0,1,0,0,0,0]) 0 2
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_044 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : (-1) * c 2 4 + (-1) * c 5 2=0 := by
  have h := defect_zero c hc 0 (![1,0,0,0,0,0]+![0,0,1,0,0,0]) 0 2
  have ha := defect_zero c hc 0 (![1,0,0,0,0,0]) 0 2
  have hb := defect_zero c hc 0 (![0,0,1,0,0,0]) 0 2
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_045 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 1 * c 2 1 + (-1) * c 5 3=0 := by
  have h := defect_zero c hc 0 (![1,0,0,0,0,0]+![0,0,0,1,0,0]) 0 2
  have ha := defect_zero c hc 0 (![1,0,0,0,0,0]) 0 2
  have hb := defect_zero c hc 0 (![0,0,0,1,0,0]) 0 2
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_046 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 1 * c 2 2 + (-1) * c 5 4=0 := by
  have h := defect_zero c hc 0 (![1,0,0,0,0,0]+![0,0,0,0,1,0]) 0 2
  have ha := defect_zero c hc 0 (![1,0,0,0,0,0]) 0 2
  have hb := defect_zero c hc 0 (![0,0,0,0,1,0]) 0 2
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_047 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : (-1) * c 5 5=0 := by
  have h := defect_zero c hc 0 (![1,0,0,0,0,0]+![0,0,0,0,0,1]) 0 2
  have ha := defect_zero c hc 0 (![1,0,0,0,0,0]) 0 2
  have hb := defect_zero c hc 0 (![0,0,0,0,0,1]) 0 2
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_048 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : (-1) * c 2 8 + (-1) * c 5 6=0 := by
  have h := defect_zero c hc 0 (![0,1,0,0,0,0]) 0 2
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_049 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : (-1) * c 2 9 + (-1) * c 2 12 + (-1) * c 5 7=0 := by
  have h := defect_zero c hc 0 (![0,1,0,0,0,0]+![0,0,1,0,0,0]) 0 2
  have ha := defect_zero c hc 0 (![0,1,0,0,0,0]) 0 2
  have hb := defect_zero c hc 0 (![0,0,1,0,0,0]) 0 2
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_050 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 2 * c 2 6 + (-2) * c 2 15 + (-1) * c 5 8=0 := by
  have h := defect_zero c hc 0 (![0,1,0,0,0,0]+![0,0,0,1,0,0]) 0 2
  have ha := defect_zero c hc 0 (![0,1,0,0,0,0]) 0 2
  have hb := defect_zero c hc 0 (![0,0,0,1,0,0]) 0 2
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_051 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 1 * c 2 7 + (-1) * c 2 16 + (-1) * c 5 9=0 := by
  have h := defect_zero c hc 0 (![0,1,0,0,0,0]+![0,0,0,0,1,0]) 0 2
  have ha := defect_zero c hc 0 (![0,1,0,0,0,0]) 0 2
  have hb := defect_zero c hc 0 (![0,0,0,0,1,0]) 0 2
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_052 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : (-1) * c 2 17 + (-1) * c 5 10=0 := by
  have h := defect_zero c hc 0 (![0,1,0,0,0,0]+![0,0,0,0,0,1]) 0 2
  have ha := defect_zero c hc 0 (![0,1,0,0,0,0]) 0 2
  have hb := defect_zero c hc 0 (![0,0,0,0,0,1]) 0 2
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_053 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : (-1) * c 2 13 + (-1) * c 5 11=0 := by
  have h := defect_zero c hc 0 (![0,0,1,0,0,0]) 0 2
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_054 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 1 * c 2 7 + (-1) * c 2 16 + (-1) * c 5 12=0 := by
  have h := defect_zero c hc 0 (![0,0,1,0,0,0]+![0,0,0,1,0,0]) 0 2
  have ha := defect_zero c hc 0 (![0,0,1,0,0,0]) 0 2
  have hb := defect_zero c hc 0 (![0,0,0,1,0,0]) 0 2
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_055 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 2 * c 2 11 + (-2) * c 2 18 + (-1) * c 5 13=0 := by
  have h := defect_zero c hc 0 (![0,0,1,0,0,0]+![0,0,0,0,1,0]) 0 2
  have ha := defect_zero c hc 0 (![0,0,1,0,0,0]) 0 2
  have hb := defect_zero c hc 0 (![0,0,0,0,1,0]) 0 2
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_056 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : (-1) * c 2 19 + (-1) * c 5 14=0 := by
  have h := defect_zero c hc 0 (![0,0,1,0,0,0]+![0,0,0,0,0,1]) 0 2
  have ha := defect_zero c hc 0 (![0,0,1,0,0,0]) 0 2
  have hb := defect_zero c hc 0 (![0,0,0,0,0,1]) 0 2
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_057 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 1 * c 2 8 + (-1) * c 5 15=0 := by
  have h := defect_zero c hc 0 (![0,0,0,1,0,0]) 0 2
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_058 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 1 * c 2 9 + 1 * c 2 12 + (-1) * c 5 16=0 := by
  have h := defect_zero c hc 0 (![0,0,0,1,0,0]+![0,0,0,0,1,0]) 0 2
  have ha := defect_zero c hc 0 (![0,0,0,1,0,0]) 0 2
  have hb := defect_zero c hc 0 (![0,0,0,0,1,0]) 0 2
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_059 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 1 * c 2 10 + (-1) * c 5 17=0 := by
  have h := defect_zero c hc 0 (![0,0,0,1,0,0]+![0,0,0,0,0,1]) 0 2
  have ha := defect_zero c hc 0 (![0,0,0,1,0,0]) 0 2
  have hb := defect_zero c hc 0 (![0,0,0,0,0,1]) 0 2
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_060 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 1 * c 2 13 + (-1) * c 5 18=0 := by
  have h := defect_zero c hc 0 (![0,0,0,0,1,0]) 0 2
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_061 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 1 * c 2 14 + (-1) * c 5 19=0 := by
  have h := defect_zero c hc 0 (![0,0,0,0,1,0]+![0,0,0,0,0,1]) 0 2
  have ha := defect_zero c hc 0 (![0,0,0,0,1,0]) 0 2
  have hb := defect_zero c hc 0 (![0,0,0,0,0,1]) 0 2
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_062 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : (-1) * c 5 20=0 := by
  have h := defect_zero c hc 0 (![0,0,0,0,0,1]) 0 2
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_063 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : (-1) * c 6 0=0 := by
  have h := defect_zero c hc 0 (![1,0,0,0,0,0]) 0 3
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_064 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : (-1) * c 3 3 + (-1) * c 6 1=0 := by
  have h := defect_zero c hc 0 (![1,0,0,0,0,0]+![0,1,0,0,0,0]) 0 3
  have ha := defect_zero c hc 0 (![1,0,0,0,0,0]) 0 3
  have hb := defect_zero c hc 0 (![0,1,0,0,0,0]) 0 3
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_065 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : (-1) * c 3 4 + (-1) * c 6 2=0 := by
  have h := defect_zero c hc 0 (![1,0,0,0,0,0]+![0,0,1,0,0,0]) 0 3
  have ha := defect_zero c hc 0 (![1,0,0,0,0,0]) 0 3
  have hb := defect_zero c hc 0 (![0,0,1,0,0,0]) 0 3
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_066 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 1 * c 3 1 + (-1) * c 6 3=0 := by
  have h := defect_zero c hc 0 (![1,0,0,0,0,0]+![0,0,0,1,0,0]) 0 3
  have ha := defect_zero c hc 0 (![1,0,0,0,0,0]) 0 3
  have hb := defect_zero c hc 0 (![0,0,0,1,0,0]) 0 3
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_067 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 1 * c 3 2 + (-1) * c 6 4=0 := by
  have h := defect_zero c hc 0 (![1,0,0,0,0,0]+![0,0,0,0,1,0]) 0 3
  have ha := defect_zero c hc 0 (![1,0,0,0,0,0]) 0 3
  have hb := defect_zero c hc 0 (![0,0,0,0,1,0]) 0 3
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_068 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : (-1) * c 6 5=0 := by
  have h := defect_zero c hc 0 (![1,0,0,0,0,0]+![0,0,0,0,0,1]) 0 3
  have ha := defect_zero c hc 0 (![1,0,0,0,0,0]) 0 3
  have hb := defect_zero c hc 0 (![0,0,0,0,0,1]) 0 3
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_069 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : (-1) * c 3 8 + (-1) * c 6 6=0 := by
  have h := defect_zero c hc 0 (![0,1,0,0,0,0]) 0 3
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_070 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : (-1) * c 3 9 + (-1) * c 3 12 + (-1) * c 6 7=0 := by
  have h := defect_zero c hc 0 (![0,1,0,0,0,0]+![0,0,1,0,0,0]) 0 3
  have ha := defect_zero c hc 0 (![0,1,0,0,0,0]) 0 3
  have hb := defect_zero c hc 0 (![0,0,1,0,0,0]) 0 3
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_071 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 2 * c 3 6 + (-2) * c 3 15 + (-1) * c 6 8=0 := by
  have h := defect_zero c hc 0 (![0,1,0,0,0,0]+![0,0,0,1,0,0]) 0 3
  have ha := defect_zero c hc 0 (![0,1,0,0,0,0]) 0 3
  have hb := defect_zero c hc 0 (![0,0,0,1,0,0]) 0 3
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_072 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 1 * c 3 7 + (-1) * c 3 16 + (-1) * c 6 9=0 := by
  have h := defect_zero c hc 0 (![0,1,0,0,0,0]+![0,0,0,0,1,0]) 0 3
  have ha := defect_zero c hc 0 (![0,1,0,0,0,0]) 0 3
  have hb := defect_zero c hc 0 (![0,0,0,0,1,0]) 0 3
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_073 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : (-1) * c 3 17 + (-1) * c 6 10=0 := by
  have h := defect_zero c hc 0 (![0,1,0,0,0,0]+![0,0,0,0,0,1]) 0 3
  have ha := defect_zero c hc 0 (![0,1,0,0,0,0]) 0 3
  have hb := defect_zero c hc 0 (![0,0,0,0,0,1]) 0 3
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_074 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : (-1) * c 3 13 + (-1) * c 6 11=0 := by
  have h := defect_zero c hc 0 (![0,0,1,0,0,0]) 0 3
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_075 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 1 * c 3 7 + (-1) * c 3 16 + (-1) * c 6 12=0 := by
  have h := defect_zero c hc 0 (![0,0,1,0,0,0]+![0,0,0,1,0,0]) 0 3
  have ha := defect_zero c hc 0 (![0,0,1,0,0,0]) 0 3
  have hb := defect_zero c hc 0 (![0,0,0,1,0,0]) 0 3
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_076 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 2 * c 3 11 + (-2) * c 3 18 + (-1) * c 6 13=0 := by
  have h := defect_zero c hc 0 (![0,0,1,0,0,0]+![0,0,0,0,1,0]) 0 3
  have ha := defect_zero c hc 0 (![0,0,1,0,0,0]) 0 3
  have hb := defect_zero c hc 0 (![0,0,0,0,1,0]) 0 3
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_077 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : (-1) * c 3 19 + (-1) * c 6 14=0 := by
  have h := defect_zero c hc 0 (![0,0,1,0,0,0]+![0,0,0,0,0,1]) 0 3
  have ha := defect_zero c hc 0 (![0,0,1,0,0,0]) 0 3
  have hb := defect_zero c hc 0 (![0,0,0,0,0,1]) 0 3
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_078 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 1 * c 3 8 + (-1) * c 6 15=0 := by
  have h := defect_zero c hc 0 (![0,0,0,1,0,0]) 0 3
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_079 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 1 * c 3 9 + 1 * c 3 12 + (-1) * c 6 16=0 := by
  have h := defect_zero c hc 0 (![0,0,0,1,0,0]+![0,0,0,0,1,0]) 0 3
  have ha := defect_zero c hc 0 (![0,0,0,1,0,0]) 0 3
  have hb := defect_zero c hc 0 (![0,0,0,0,1,0]) 0 3
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_080 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 1 * c 3 10 + (-1) * c 6 17=0 := by
  have h := defect_zero c hc 0 (![0,0,0,1,0,0]+![0,0,0,0,0,1]) 0 3
  have ha := defect_zero c hc 0 (![0,0,0,1,0,0]) 0 3
  have hb := defect_zero c hc 0 (![0,0,0,0,0,1]) 0 3
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_081 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 1 * c 3 13 + (-1) * c 6 18=0 := by
  have h := defect_zero c hc 0 (![0,0,0,0,1,0]) 0 3
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_082 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 1 * c 3 14 + (-1) * c 6 19=0 := by
  have h := defect_zero c hc 0 (![0,0,0,0,1,0]+![0,0,0,0,0,1]) 0 3
  have ha := defect_zero c hc 0 (![0,0,0,0,1,0]) 0 3
  have hb := defect_zero c hc 0 (![0,0,0,0,0,1]) 0 3
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_083 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : (-1) * c 6 20=0 := by
  have h := defect_zero c hc 0 (![0,0,0,0,0,1]) 0 3
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_084 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : (-1) * c 4 3 + 2 * c 1 1=0 := by
  have h := defect_zero c hc 0 (![1,0,0,0,0,0]+![0,1,0,0,0,0]) 1 1
  have ha := defect_zero c hc 0 (![1,0,0,0,0,0]) 1 1
  have hb := defect_zero c hc 0 (![0,1,0,0,0,0]) 1 1
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_085 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : (-1) * c 4 4 + 2 * c 1 2=0 := by
  have h := defect_zero c hc 0 (![1,0,0,0,0,0]+![0,0,1,0,0,0]) 1 1
  have ha := defect_zero c hc 0 (![1,0,0,0,0,0]) 1 1
  have hb := defect_zero c hc 0 (![0,0,1,0,0,0]) 1 1
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_086 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 1 * c 4 1 + 2 * c 1 3=0 := by
  have h := defect_zero c hc 0 (![1,0,0,0,0,0]+![0,0,0,1,0,0]) 1 1
  have ha := defect_zero c hc 0 (![1,0,0,0,0,0]) 1 1
  have hb := defect_zero c hc 0 (![0,0,0,1,0,0]) 1 1
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_087 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 1 * c 4 2 + 2 * c 1 4=0 := by
  have h := defect_zero c hc 0 (![1,0,0,0,0,0]+![0,0,0,0,1,0]) 1 1
  have ha := defect_zero c hc 0 (![1,0,0,0,0,0]) 1 1
  have hb := defect_zero c hc 0 (![0,0,0,0,1,0]) 1 1
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_088 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : (-1) * c 4 17 + 2 * c 1 10=0 := by
  have h := defect_zero c hc 0 (![0,1,0,0,0,0]+![0,0,0,0,0,1]) 1 1
  have ha := defect_zero c hc 0 (![0,1,0,0,0,0]) 1 1
  have hb := defect_zero c hc 0 (![0,0,0,0,0,1]) 1 1
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_089 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : (-1) * c 4 19 + 2 * c 1 14=0 := by
  have h := defect_zero c hc 0 (![0,0,1,0,0,0]+![0,0,0,0,0,1]) 1 1
  have ha := defect_zero c hc 0 (![0,0,1,0,0,0]) 1 1
  have hb := defect_zero c hc 0 (![0,0,0,0,0,1]) 1 1
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_090 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 1 * c 4 10 + 2 * c 1 17=0 := by
  have h := defect_zero c hc 0 (![0,0,0,1,0,0]+![0,0,0,0,0,1]) 1 1
  have ha := defect_zero c hc 0 (![0,0,0,1,0,0]) 1 1
  have hb := defect_zero c hc 0 (![0,0,0,0,0,1]) 1 1
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_091 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 1 * c 4 14 + 2 * c 1 19=0 := by
  have h := defect_zero c hc 0 (![0,0,0,0,1,0]+![0,0,0,0,0,1]) 1 1
  have ha := defect_zero c hc 0 (![0,0,0,0,1,0]) 1 1
  have hb := defect_zero c hc 0 (![0,0,0,0,0,1]) 1 1
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_092 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 1 * c 2 0=0 := by
  have h := defect_zero c hc 0 (![1,0,0,0,0,0]) 1 2
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_093 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 1 * c 2 5=0 := by
  have h := defect_zero c hc 0 (![1,0,0,0,0,0]+![0,0,0,0,0,1]) 1 2
  have ha := defect_zero c hc 0 (![1,0,0,0,0,0]) 1 2
  have hb := defect_zero c hc 0 (![0,0,0,0,0,1]) 1 2
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_094 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : (-1) * c 5 8 + 1 * c 2 6=0 := by
  have h := defect_zero c hc 0 (![0,1,0,0,0,0]) 1 2
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_095 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : (-1) * c 5 9 + (-1) * c 5 12 + 1 * c 2 7=0 := by
  have h := defect_zero c hc 0 (![0,1,0,0,0,0]+![0,0,1,0,0,0]) 1 2
  have ha := defect_zero c hc 0 (![0,1,0,0,0,0]) 1 2
  have hb := defect_zero c hc 0 (![0,0,1,0,0,0]) 1 2
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_096 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 2 * c 5 6 + (-2) * c 5 15 + 1 * c 2 8=0 := by
  have h := defect_zero c hc 0 (![0,1,0,0,0,0]+![0,0,0,1,0,0]) 1 2
  have ha := defect_zero c hc 0 (![0,1,0,0,0,0]) 1 2
  have hb := defect_zero c hc 0 (![0,0,0,1,0,0]) 1 2
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_097 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 1 * c 5 7 + (-1) * c 5 16 + 1 * c 2 9=0 := by
  have h := defect_zero c hc 0 (![0,1,0,0,0,0]+![0,0,0,0,1,0]) 1 2
  have ha := defect_zero c hc 0 (![0,1,0,0,0,0]) 1 2
  have hb := defect_zero c hc 0 (![0,0,0,0,1,0]) 1 2
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_098 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : (-1) * c 5 13 + 1 * c 2 11=0 := by
  have h := defect_zero c hc 0 (![0,0,1,0,0,0]) 1 2
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_099 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 1 * c 5 7 + (-1) * c 5 16 + 1 * c 2 12=0 := by
  have h := defect_zero c hc 0 (![0,0,1,0,0,0]+![0,0,0,1,0,0]) 1 2
  have ha := defect_zero c hc 0 (![0,0,1,0,0,0]) 1 2
  have hb := defect_zero c hc 0 (![0,0,0,1,0,0]) 1 2
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_100 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 2 * c 5 11 + (-2) * c 5 18 + 1 * c 2 13=0 := by
  have h := defect_zero c hc 0 (![0,0,1,0,0,0]+![0,0,0,0,1,0]) 1 2
  have ha := defect_zero c hc 0 (![0,0,1,0,0,0]) 1 2
  have hb := defect_zero c hc 0 (![0,0,0,0,1,0]) 1 2
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_101 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 1 * c 5 8 + 1 * c 2 15=0 := by
  have h := defect_zero c hc 0 (![0,0,0,1,0,0]) 1 2
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_102 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 1 * c 5 9 + 1 * c 5 12 + 1 * c 2 16=0 := by
  have h := defect_zero c hc 0 (![0,0,0,1,0,0]+![0,0,0,0,1,0]) 1 2
  have ha := defect_zero c hc 0 (![0,0,0,1,0,0]) 1 2
  have hb := defect_zero c hc 0 (![0,0,0,0,1,0]) 1 2
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_103 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 1 * c 5 13 + 1 * c 2 18=0 := by
  have h := defect_zero c hc 0 (![0,0,0,0,1,0]) 1 2
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_104 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 1 * c 2 20=0 := by
  have h := defect_zero c hc 0 (![0,0,0,0,0,1]) 1 2
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_105 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 1 * c 3 0=0 := by
  have h := defect_zero c hc 0 (![1,0,0,0,0,0]) 1 3
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_106 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 1 * c 3 5=0 := by
  have h := defect_zero c hc 0 (![1,0,0,0,0,0]+![0,0,0,0,0,1]) 1 3
  have ha := defect_zero c hc 0 (![1,0,0,0,0,0]) 1 3
  have hb := defect_zero c hc 0 (![0,0,0,0,0,1]) 1 3
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_107 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : (-1) * c 6 8 + 1 * c 3 6=0 := by
  have h := defect_zero c hc 0 (![0,1,0,0,0,0]) 1 3
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_108 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : (-1) * c 6 9 + (-1) * c 6 12 + 1 * c 3 7=0 := by
  have h := defect_zero c hc 0 (![0,1,0,0,0,0]+![0,0,1,0,0,0]) 1 3
  have ha := defect_zero c hc 0 (![0,1,0,0,0,0]) 1 3
  have hb := defect_zero c hc 0 (![0,0,1,0,0,0]) 1 3
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_109 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 2 * c 6 6 + (-2) * c 6 15 + 1 * c 3 8=0 := by
  have h := defect_zero c hc 0 (![0,1,0,0,0,0]+![0,0,0,1,0,0]) 1 3
  have ha := defect_zero c hc 0 (![0,1,0,0,0,0]) 1 3
  have hb := defect_zero c hc 0 (![0,0,0,1,0,0]) 1 3
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_110 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 1 * c 6 7 + (-1) * c 6 16 + 1 * c 3 9=0 := by
  have h := defect_zero c hc 0 (![0,1,0,0,0,0]+![0,0,0,0,1,0]) 1 3
  have ha := defect_zero c hc 0 (![0,1,0,0,0,0]) 1 3
  have hb := defect_zero c hc 0 (![0,0,0,0,1,0]) 1 3
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_111 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : (-1) * c 6 13 + 1 * c 3 11=0 := by
  have h := defect_zero c hc 0 (![0,0,1,0,0,0]) 1 3
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_112 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 1 * c 6 7 + (-1) * c 6 16 + 1 * c 3 12=0 := by
  have h := defect_zero c hc 0 (![0,0,1,0,0,0]+![0,0,0,1,0,0]) 1 3
  have ha := defect_zero c hc 0 (![0,0,1,0,0,0]) 1 3
  have hb := defect_zero c hc 0 (![0,0,0,1,0,0]) 1 3
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_113 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 2 * c 6 11 + (-2) * c 6 18 + 1 * c 3 13=0 := by
  have h := defect_zero c hc 0 (![0,0,1,0,0,0]+![0,0,0,0,1,0]) 1 3
  have ha := defect_zero c hc 0 (![0,0,1,0,0,0]) 1 3
  have hb := defect_zero c hc 0 (![0,0,0,0,1,0]) 1 3
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_114 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 1 * c 6 8 + 1 * c 3 15=0 := by
  have h := defect_zero c hc 0 (![0,0,0,1,0,0]) 1 3
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_115 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 1 * c 6 9 + 1 * c 6 12 + 1 * c 3 16=0 := by
  have h := defect_zero c hc 0 (![0,0,0,1,0,0]+![0,0,0,0,1,0]) 1 3
  have ha := defect_zero c hc 0 (![0,0,0,1,0,0]) 1 3
  have hb := defect_zero c hc 0 (![0,0,0,0,1,0]) 1 3
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_116 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 1 * c 6 13 + 1 * c 3 18=0 := by
  have h := defect_zero c hc 0 (![0,0,0,0,1,0]) 1 3
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_117 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 1 * c 3 20=0 := by
  have h := defect_zero c hc 0 (![0,0,0,0,0,1]) 1 3
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_118 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : (-1) * c 7 3=0 := by
  have h := defect_zero c hc 0 (![1,0,0,0,0,0]+![0,1,0,0,0,0]) 2 2
  have ha := defect_zero c hc 0 (![1,0,0,0,0,0]) 2 2
  have hb := defect_zero c hc 0 (![0,1,0,0,0,0]) 2 2
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_119 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : (-1) * c 7 4=0 := by
  have h := defect_zero c hc 0 (![1,0,0,0,0,0]+![0,0,1,0,0,0]) 2 2
  have ha := defect_zero c hc 0 (![1,0,0,0,0,0]) 2 2
  have hb := defect_zero c hc 0 (![0,0,1,0,0,0]) 2 2
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_120 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 1 * c 7 1=0 := by
  have h := defect_zero c hc 0 (![1,0,0,0,0,0]+![0,0,0,1,0,0]) 2 2
  have ha := defect_zero c hc 0 (![1,0,0,0,0,0]) 2 2
  have hb := defect_zero c hc 0 (![0,0,0,1,0,0]) 2 2
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_121 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 1 * c 7 2=0 := by
  have h := defect_zero c hc 0 (![1,0,0,0,0,0]+![0,0,0,0,1,0]) 2 2
  have ha := defect_zero c hc 0 (![1,0,0,0,0,0]) 2 2
  have hb := defect_zero c hc 0 (![0,0,0,0,1,0]) 2 2
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_122 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : (-1) * c 7 8=0 := by
  have h := defect_zero c hc 0 (![0,1,0,0,0,0]) 2 2
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_123 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : (-1) * c 7 9 + (-1) * c 7 12=0 := by
  have h := defect_zero c hc 0 (![0,1,0,0,0,0]+![0,0,1,0,0,0]) 2 2
  have ha := defect_zero c hc 0 (![0,1,0,0,0,0]) 2 2
  have hb := defect_zero c hc 0 (![0,0,1,0,0,0]) 2 2
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_124 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 2 * c 7 6 + (-2) * c 7 15=0 := by
  have h := defect_zero c hc 0 (![0,1,0,0,0,0]+![0,0,0,1,0,0]) 2 2
  have ha := defect_zero c hc 0 (![0,1,0,0,0,0]) 2 2
  have hb := defect_zero c hc 0 (![0,0,0,1,0,0]) 2 2
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_125 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 1 * c 7 7 + (-1) * c 7 16=0 := by
  have h := defect_zero c hc 0 (![0,1,0,0,0,0]+![0,0,0,0,1,0]) 2 2
  have ha := defect_zero c hc 0 (![0,1,0,0,0,0]) 2 2
  have hb := defect_zero c hc 0 (![0,0,0,0,1,0]) 2 2
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_126 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : (-1) * c 7 17=0 := by
  have h := defect_zero c hc 0 (![0,1,0,0,0,0]+![0,0,0,0,0,1]) 2 2
  have ha := defect_zero c hc 0 (![0,1,0,0,0,0]) 2 2
  have hb := defect_zero c hc 0 (![0,0,0,0,0,1]) 2 2
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_127 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : (-1) * c 7 13=0 := by
  have h := defect_zero c hc 0 (![0,0,1,0,0,0]) 2 2
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_128 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 2 * c 7 11 + (-2) * c 7 18=0 := by
  have h := defect_zero c hc 0 (![0,0,1,0,0,0]+![0,0,0,0,1,0]) 2 2
  have ha := defect_zero c hc 0 (![0,0,1,0,0,0]) 2 2
  have hb := defect_zero c hc 0 (![0,0,0,0,1,0]) 2 2
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_129 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : (-1) * c 7 19=0 := by
  have h := defect_zero c hc 0 (![0,0,1,0,0,0]+![0,0,0,0,0,1]) 2 2
  have ha := defect_zero c hc 0 (![0,0,1,0,0,0]) 2 2
  have hb := defect_zero c hc 0 (![0,0,0,0,0,1]) 2 2
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_130 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 1 * c 7 10=0 := by
  have h := defect_zero c hc 0 (![0,0,0,1,0,0]+![0,0,0,0,0,1]) 2 2
  have ha := defect_zero c hc 0 (![0,0,0,1,0,0]) 2 2
  have hb := defect_zero c hc 0 (![0,0,0,0,0,1]) 2 2
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_131 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 1 * c 7 14=0 := by
  have h := defect_zero c hc 0 (![0,0,0,0,1,0]+![0,0,0,0,0,1]) 2 2
  have ha := defect_zero c hc 0 (![0,0,0,0,1,0]) 2 2
  have hb := defect_zero c hc 0 (![0,0,0,0,0,1]) 2 2
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_132 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : (-1) * c 8 3=0 := by
  have h := defect_zero c hc 0 (![1,0,0,0,0,0]+![0,1,0,0,0,0]) 2 3
  have ha := defect_zero c hc 0 (![1,0,0,0,0,0]) 2 3
  have hb := defect_zero c hc 0 (![0,1,0,0,0,0]) 2 3
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_133 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : (-1) * c 8 4=0 := by
  have h := defect_zero c hc 0 (![1,0,0,0,0,0]+![0,0,1,0,0,0]) 2 3
  have ha := defect_zero c hc 0 (![1,0,0,0,0,0]) 2 3
  have hb := defect_zero c hc 0 (![0,0,1,0,0,0]) 2 3
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_134 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 1 * c 8 1=0 := by
  have h := defect_zero c hc 0 (![1,0,0,0,0,0]+![0,0,0,1,0,0]) 2 3
  have ha := defect_zero c hc 0 (![1,0,0,0,0,0]) 2 3
  have hb := defect_zero c hc 0 (![0,0,0,1,0,0]) 2 3
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_135 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 1 * c 8 2=0 := by
  have h := defect_zero c hc 0 (![1,0,0,0,0,0]+![0,0,0,0,1,0]) 2 3
  have ha := defect_zero c hc 0 (![1,0,0,0,0,0]) 2 3
  have hb := defect_zero c hc 0 (![0,0,0,0,1,0]) 2 3
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_136 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : (-1) * c 8 8=0 := by
  have h := defect_zero c hc 0 (![0,1,0,0,0,0]) 2 3
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_137 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : (-1) * c 8 9 + (-1) * c 8 12=0 := by
  have h := defect_zero c hc 0 (![0,1,0,0,0,0]+![0,0,1,0,0,0]) 2 3
  have ha := defect_zero c hc 0 (![0,1,0,0,0,0]) 2 3
  have hb := defect_zero c hc 0 (![0,0,1,0,0,0]) 2 3
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_138 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 2 * c 8 6 + (-2) * c 8 15=0 := by
  have h := defect_zero c hc 0 (![0,1,0,0,0,0]+![0,0,0,1,0,0]) 2 3
  have ha := defect_zero c hc 0 (![0,1,0,0,0,0]) 2 3
  have hb := defect_zero c hc 0 (![0,0,0,1,0,0]) 2 3
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_139 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 1 * c 8 7 + (-1) * c 8 16=0 := by
  have h := defect_zero c hc 0 (![0,1,0,0,0,0]+![0,0,0,0,1,0]) 2 3
  have ha := defect_zero c hc 0 (![0,1,0,0,0,0]) 2 3
  have hb := defect_zero c hc 0 (![0,0,0,0,1,0]) 2 3
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_140 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : (-1) * c 8 17=0 := by
  have h := defect_zero c hc 0 (![0,1,0,0,0,0]+![0,0,0,0,0,1]) 2 3
  have ha := defect_zero c hc 0 (![0,1,0,0,0,0]) 2 3
  have hb := defect_zero c hc 0 (![0,0,0,0,0,1]) 2 3
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_141 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : (-1) * c 8 13=0 := by
  have h := defect_zero c hc 0 (![0,0,1,0,0,0]) 2 3
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_142 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 2 * c 8 11 + (-2) * c 8 18=0 := by
  have h := defect_zero c hc 0 (![0,0,1,0,0,0]+![0,0,0,0,1,0]) 2 3
  have ha := defect_zero c hc 0 (![0,0,1,0,0,0]) 2 3
  have hb := defect_zero c hc 0 (![0,0,0,0,1,0]) 2 3
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_143 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : (-1) * c 8 19=0 := by
  have h := defect_zero c hc 0 (![0,0,1,0,0,0]+![0,0,0,0,0,1]) 2 3
  have ha := defect_zero c hc 0 (![0,0,1,0,0,0]) 2 3
  have hb := defect_zero c hc 0 (![0,0,0,0,0,1]) 2 3
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_144 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 1 * c 8 10=0 := by
  have h := defect_zero c hc 0 (![0,0,0,1,0,0]+![0,0,0,0,0,1]) 2 3
  have ha := defect_zero c hc 0 (![0,0,0,1,0,0]) 2 3
  have hb := defect_zero c hc 0 (![0,0,0,0,0,1]) 2 3
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_145 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 1 * c 8 14=0 := by
  have h := defect_zero c hc 0 (![0,0,0,0,1,0]+![0,0,0,0,0,1]) 2 3
  have ha := defect_zero c hc 0 (![0,0,0,0,1,0]) 2 3
  have hb := defect_zero c hc 0 (![0,0,0,0,0,1]) 2 3
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_146 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : (-1) * c 9 3=0 := by
  have h := defect_zero c hc 0 (![1,0,0,0,0,0]+![0,1,0,0,0,0]) 3 3
  have ha := defect_zero c hc 0 (![1,0,0,0,0,0]) 3 3
  have hb := defect_zero c hc 0 (![0,1,0,0,0,0]) 3 3
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_147 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : (-1) * c 9 4=0 := by
  have h := defect_zero c hc 0 (![1,0,0,0,0,0]+![0,0,1,0,0,0]) 3 3
  have ha := defect_zero c hc 0 (![1,0,0,0,0,0]) 3 3
  have hb := defect_zero c hc 0 (![0,0,1,0,0,0]) 3 3
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_148 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 1 * c 9 1=0 := by
  have h := defect_zero c hc 0 (![1,0,0,0,0,0]+![0,0,0,1,0,0]) 3 3
  have ha := defect_zero c hc 0 (![1,0,0,0,0,0]) 3 3
  have hb := defect_zero c hc 0 (![0,0,0,1,0,0]) 3 3
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_149 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 1 * c 9 2=0 := by
  have h := defect_zero c hc 0 (![1,0,0,0,0,0]+![0,0,0,0,1,0]) 3 3
  have ha := defect_zero c hc 0 (![1,0,0,0,0,0]) 3 3
  have hb := defect_zero c hc 0 (![0,0,0,0,1,0]) 3 3
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_150 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : (-1) * c 9 8=0 := by
  have h := defect_zero c hc 0 (![0,1,0,0,0,0]) 3 3
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_151 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : (-1) * c 9 9 + (-1) * c 9 12=0 := by
  have h := defect_zero c hc 0 (![0,1,0,0,0,0]+![0,0,1,0,0,0]) 3 3
  have ha := defect_zero c hc 0 (![0,1,0,0,0,0]) 3 3
  have hb := defect_zero c hc 0 (![0,0,1,0,0,0]) 3 3
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_152 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 2 * c 9 6 + (-2) * c 9 15=0 := by
  have h := defect_zero c hc 0 (![0,1,0,0,0,0]+![0,0,0,1,0,0]) 3 3
  have ha := defect_zero c hc 0 (![0,1,0,0,0,0]) 3 3
  have hb := defect_zero c hc 0 (![0,0,0,1,0,0]) 3 3
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_153 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 1 * c 9 7 + (-1) * c 9 16=0 := by
  have h := defect_zero c hc 0 (![0,1,0,0,0,0]+![0,0,0,0,1,0]) 3 3
  have ha := defect_zero c hc 0 (![0,1,0,0,0,0]) 3 3
  have hb := defect_zero c hc 0 (![0,0,0,0,1,0]) 3 3
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_154 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : (-1) * c 9 17=0 := by
  have h := defect_zero c hc 0 (![0,1,0,0,0,0]+![0,0,0,0,0,1]) 3 3
  have ha := defect_zero c hc 0 (![0,1,0,0,0,0]) 3 3
  have hb := defect_zero c hc 0 (![0,0,0,0,0,1]) 3 3
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_155 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : (-1) * c 9 13=0 := by
  have h := defect_zero c hc 0 (![0,0,1,0,0,0]) 3 3
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_156 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 2 * c 9 11 + (-2) * c 9 18=0 := by
  have h := defect_zero c hc 0 (![0,0,1,0,0,0]+![0,0,0,0,1,0]) 3 3
  have ha := defect_zero c hc 0 (![0,0,1,0,0,0]) 3 3
  have hb := defect_zero c hc 0 (![0,0,0,0,1,0]) 3 3
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_157 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : (-1) * c 9 19=0 := by
  have h := defect_zero c hc 0 (![0,0,1,0,0,0]+![0,0,0,0,0,1]) 3 3
  have ha := defect_zero c hc 0 (![0,0,1,0,0,0]) 3 3
  have hb := defect_zero c hc 0 (![0,0,0,0,0,1]) 3 3
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_158 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 1 * c 9 10=0 := by
  have h := defect_zero c hc 0 (![0,0,0,1,0,0]+![0,0,0,0,0,1]) 3 3
  have ha := defect_zero c hc 0 (![0,0,0,1,0,0]) 3 3
  have hb := defect_zero c hc 0 (![0,0,0,0,0,1]) 3 3
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_159 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 1 * c 9 14=0 := by
  have h := defect_zero c hc 0 (![0,0,0,0,1,0]+![0,0,0,0,0,1]) 3 3
  have ha := defect_zero c hc 0 (![0,0,0,0,1,0]) 3 3
  have hb := defect_zero c hc 0 (![0,0,0,0,0,1]) 3 3
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_160 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 1 * c 0 8 + (-2) * c 2 1=0 := by
  have h := defect_zero c hc 1 (![1,0,0,0,0,0]+![0,1,0,0,0,0]) 0 0
  have ha := defect_zero c hc 1 (![1,0,0,0,0,0]) 0 0
  have hb := defect_zero c hc 1 (![0,1,0,0,0,0]) 0 0
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_161 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : (-1) * c 0 5 + 1 * c 0 12 + (-2) * c 2 2=0 := by
  have h := defect_zero c hc 1 (![1,0,0,0,0,0]+![0,0,1,0,0,0]) 0 0
  have ha := defect_zero c hc 1 (![1,0,0,0,0,0]) 0 0
  have hb := defect_zero c hc 1 (![0,0,1,0,0,0]) 0 0
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_162 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : (-2) * c 0 0 + 2 * c 0 15 + (-2) * c 2 3=0 := by
  have h := defect_zero c hc 1 (![1,0,0,0,0,0]+![0,0,0,1,0,0]) 0 0
  have ha := defect_zero c hc 1 (![1,0,0,0,0,0]) 0 0
  have hb := defect_zero c hc 1 (![0,0,0,1,0,0]) 0 0
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_163 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 1 * c 0 16 + (-2) * c 2 4=0 := by
  have h := defect_zero c hc 1 (![1,0,0,0,0,0]+![0,0,0,0,1,0]) 0 0
  have ha := defect_zero c hc 1 (![1,0,0,0,0,0]) 0 0
  have hb := defect_zero c hc 1 (![0,0,0,0,1,0]) 0 0
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_164 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 1 * c 0 7 + (-2) * c 2 10=0 := by
  have h := defect_zero c hc 1 (![0,1,0,0,0,0]+![0,0,0,0,0,1]) 0 0
  have ha := defect_zero c hc 1 (![0,1,0,0,0,0]) 0 0
  have hb := defect_zero c hc 1 (![0,0,0,0,0,1]) 0 0
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_165 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 2 * c 0 11 + (-2) * c 0 20 + (-2) * c 2 14=0 := by
  have h := defect_zero c hc 1 (![0,0,1,0,0,0]+![0,0,0,0,0,1]) 0 0
  have ha := defect_zero c hc 1 (![0,0,1,0,0,0]) 0 0
  have hb := defect_zero c hc 1 (![0,0,0,0,0,1]) 0 0
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_166 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : (-1) * c 0 5 + 1 * c 0 12 + (-2) * c 2 17=0 := by
  have h := defect_zero c hc 1 (![0,0,0,1,0,0]+![0,0,0,0,0,1]) 0 0
  have ha := defect_zero c hc 1 (![0,0,0,1,0,0]) 0 0
  have hb := defect_zero c hc 1 (![0,0,0,0,0,1]) 0 0
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_167 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 1 * c 0 13 + (-2) * c 2 19=0 := by
  have h := defect_zero c hc 1 (![0,0,0,0,1,0]+![0,0,0,0,0,1]) 0 0
  have ha := defect_zero c hc 1 (![0,0,0,0,1,0]) 0 0
  have hb := defect_zero c hc 1 (![0,0,0,0,0,1]) 0 0
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_168 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 1 * c 1 8 + (-1) * c 5 1=0 := by
  have h := defect_zero c hc 1 (![1,0,0,0,0,0]+![0,1,0,0,0,0]) 0 1
  have ha := defect_zero c hc 1 (![1,0,0,0,0,0]) 0 1
  have hb := defect_zero c hc 1 (![0,1,0,0,0,0]) 0 1
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_169 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : (-1) * c 1 5 + 1 * c 1 12 + (-1) * c 5 2=0 := by
  have h := defect_zero c hc 1 (![1,0,0,0,0,0]+![0,0,1,0,0,0]) 0 1
  have ha := defect_zero c hc 1 (![1,0,0,0,0,0]) 0 1
  have hb := defect_zero c hc 1 (![0,0,1,0,0,0]) 0 1
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_170 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : (-2) * c 1 0 + 2 * c 1 15 + (-1) * c 5 3=0 := by
  have h := defect_zero c hc 1 (![1,0,0,0,0,0]+![0,0,0,1,0,0]) 0 1
  have ha := defect_zero c hc 1 (![1,0,0,0,0,0]) 0 1
  have hb := defect_zero c hc 1 (![0,0,0,1,0,0]) 0 1
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_171 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 1 * c 1 16 + (-1) * c 5 4=0 := by
  have h := defect_zero c hc 1 (![1,0,0,0,0,0]+![0,0,0,0,1,0]) 0 1
  have ha := defect_zero c hc 1 (![1,0,0,0,0,0]) 0 1
  have hb := defect_zero c hc 1 (![0,0,0,0,1,0]) 0 1
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_172 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 2 * c 1 11 + (-2) * c 1 20 + (-1) * c 5 14=0 := by
  have h := defect_zero c hc 1 (![0,0,1,0,0,0]+![0,0,0,0,0,1]) 0 1
  have ha := defect_zero c hc 1 (![0,0,1,0,0,0]) 0 1
  have hb := defect_zero c hc 1 (![0,0,0,0,0,1]) 0 1
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_173 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : (-1) * c 1 5 + 1 * c 1 12 + (-1) * c 5 17=0 := by
  have h := defect_zero c hc 1 (![0,0,0,1,0,0]+![0,0,0,0,0,1]) 0 1
  have ha := defect_zero c hc 1 (![0,0,0,1,0,0]) 0 1
  have hb := defect_zero c hc 1 (![0,0,0,0,0,1]) 0 1
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_174 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 1 * c 1 13 + (-1) * c 5 19=0 := by
  have h := defect_zero c hc 1 (![0,0,0,0,1,0]+![0,0,0,0,0,1]) 0 1
  have ha := defect_zero c hc 1 (![0,0,0,0,1,0]) 0 1
  have hb := defect_zero c hc 1 (![0,0,0,0,0,1]) 0 1
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_175 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 1 * c 2 3 + 1 * c 0 0 + (-1) * c 7 0=0 := by
  have h := defect_zero c hc 1 (![1,0,0,0,0,0]) 0 2
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_176 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 1 * c 2 2 + 1 * c 2 17 + 1 * c 0 5 + (-1) * c 7 5=0 := by
  have h := defect_zero c hc 1 (![1,0,0,0,0,0]+![0,0,0,0,0,1]) 0 2
  have ha := defect_zero c hc 1 (![1,0,0,0,0,0]) 0 2
  have hb := defect_zero c hc 1 (![0,0,0,0,0,1]) 0 2
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_177 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 1 * c 0 6 + (-1) * c 7 6=0 := by
  have h := defect_zero c hc 1 (![0,1,0,0,0,0]) 0 2
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_178 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : (-1) * c 2 10 + 1 * c 0 7 + (-1) * c 7 7=0 := by
  have h := defect_zero c hc 1 (![0,1,0,0,0,0]+![0,0,1,0,0,0]) 0 2
  have ha := defect_zero c hc 1 (![0,1,0,0,0,0]) 0 2
  have hb := defect_zero c hc 1 (![0,0,1,0,0,0]) 0 2
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_179 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 1 * c 0 9 + (-1) * c 7 9=0 := by
  have h := defect_zero c hc 1 (![0,1,0,0,0,0]+![0,0,0,0,1,0]) 0 2
  have ha := defect_zero c hc 1 (![0,1,0,0,0,0]) 0 2
  have hb := defect_zero c hc 1 (![0,0,0,0,1,0]) 0 2
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_180 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : (-1) * c 2 14 + 1 * c 0 11 + (-1) * c 7 11=0 := by
  have h := defect_zero c hc 1 (![0,0,1,0,0,0]) 0 2
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_181 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 1 * c 2 14 + 1 * c 0 20 + (-1) * c 7 20=0 := by
  have h := defect_zero c hc 1 (![0,0,0,0,0,1]) 0 2
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_182 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 1 * c 3 3 + (-1) * c 8 0=0 := by
  have h := defect_zero c hc 1 (![1,0,0,0,0,0]) 0 3
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_183 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 1 * c 3 2 + 1 * c 3 17 + (-1) * c 8 5=0 := by
  have h := defect_zero c hc 1 (![1,0,0,0,0,0]+![0,0,0,0,0,1]) 0 3
  have ha := defect_zero c hc 1 (![1,0,0,0,0,0]) 0 3
  have hb := defect_zero c hc 1 (![0,0,0,0,0,1]) 0 3
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_184 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : (-1) * c 8 6=0 := by
  have h := defect_zero c hc 1 (![0,1,0,0,0,0]) 0 3
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_185 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : (-1) * c 3 10 + (-1) * c 8 7=0 := by
  have h := defect_zero c hc 1 (![0,1,0,0,0,0]+![0,0,1,0,0,0]) 0 3
  have ha := defect_zero c hc 1 (![0,1,0,0,0,0]) 0 3
  have hb := defect_zero c hc 1 (![0,0,1,0,0,0]) 0 3
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_186 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : (-1) * c 3 1 + (-1) * c 8 8=0 := by
  have h := defect_zero c hc 1 (![0,1,0,0,0,0]+![0,0,0,1,0,0]) 0 3
  have ha := defect_zero c hc 1 (![0,1,0,0,0,0]) 0 3
  have hb := defect_zero c hc 1 (![0,0,0,1,0,0]) 0 3
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_187 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : (-1) * c 8 9=0 := by
  have h := defect_zero c hc 1 (![0,1,0,0,0,0]+![0,0,0,0,1,0]) 0 3
  have ha := defect_zero c hc 1 (![0,1,0,0,0,0]) 0 3
  have hb := defect_zero c hc 1 (![0,0,0,0,1,0]) 0 3
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_188 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : (-1) * c 3 14 + (-1) * c 8 11=0 := by
  have h := defect_zero c hc 1 (![0,0,1,0,0,0]) 0 3
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_189 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : (-1) * c 3 2 + (-1) * c 3 17 + (-1) * c 8 12=0 := by
  have h := defect_zero c hc 1 (![0,0,1,0,0,0]+![0,0,0,1,0,0]) 0 3
  have ha := defect_zero c hc 1 (![0,0,1,0,0,0]) 0 3
  have hb := defect_zero c hc 1 (![0,0,0,1,0,0]) 0 3
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_190 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : (-1) * c 3 19 + (-1) * c 8 13=0 := by
  have h := defect_zero c hc 1 (![0,0,1,0,0,0]+![0,0,0,0,1,0]) 0 3
  have ha := defect_zero c hc 1 (![0,0,1,0,0,0]) 0 3
  have hb := defect_zero c hc 1 (![0,0,0,0,1,0]) 0 3
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_191 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : (-1) * c 3 3 + (-1) * c 8 15=0 := by
  have h := defect_zero c hc 1 (![0,0,0,1,0,0]) 0 3
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_192 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : (-1) * c 3 4 + (-1) * c 8 16=0 := by
  have h := defect_zero c hc 1 (![0,0,0,1,0,0]+![0,0,0,0,1,0]) 0 3
  have ha := defect_zero c hc 1 (![0,0,0,1,0,0]) 0 3
  have hb := defect_zero c hc 1 (![0,0,0,0,1,0]) 0 3
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_193 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : (-1) * c 8 18=0 := by
  have h := defect_zero c hc 1 (![0,0,0,0,1,0]) 0 3
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_194 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 1 * c 3 14 + (-1) * c 8 20=0 := by
  have h := defect_zero c hc 1 (![0,0,0,0,0,1]) 0 3
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_195 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : (-1) * c 6 10=0 := by
  have h := defect_zero c hc 1 (![0,1,0,0,0,0]+![0,0,1,0,0,0]) 1 3
  have ha := defect_zero c hc 1 (![0,1,0,0,0,0]) 1 3
  have hb := defect_zero c hc 1 (![0,0,1,0,0,0]) 1 3
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_196 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : (-1) * c 9 5 + 1 * c 9 12=0 := by
  have h := defect_zero c hc 1 (![1,0,0,0,0,0]+![0,0,1,0,0,0]) 3 3
  have ha := defect_zero c hc 1 (![1,0,0,0,0,0]) 3 3
  have hb := defect_zero c hc 1 (![0,0,1,0,0,0]) 3 3
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_197 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : (-2) * c 9 0 + 2 * c 9 15=0 := by
  have h := defect_zero c hc 1 (![1,0,0,0,0,0]+![0,0,0,1,0,0]) 3 3
  have ha := defect_zero c hc 1 (![1,0,0,0,0,0]) 3 3
  have hb := defect_zero c hc 1 (![0,0,0,1,0,0]) 3 3
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_198 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 1 * c 9 16=0 := by
  have h := defect_zero c hc 1 (![1,0,0,0,0,0]+![0,0,0,0,1,0]) 3 3
  have ha := defect_zero c hc 1 (![1,0,0,0,0,0]) 3 3
  have hb := defect_zero c hc 1 (![0,0,0,0,1,0]) 3 3
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_199 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 2 * c 9 11 + (-2) * c 9 20=0 := by
  have h := defect_zero c hc 1 (![0,0,1,0,0,0]+![0,0,0,0,0,1]) 3 3
  have ha := defect_zero c hc 1 (![0,0,1,0,0,0]) 3 3
  have hb := defect_zero c hc 1 (![0,0,0,0,0,1]) 3 3
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_200 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 2 * c 0 0 + 2 * c 0 18 + 2 * c 3 4=0 := by
  have h := defect_zero c hc 2 (![1,0,0,0,0,0]+![0,0,0,0,1,0]) 0 0
  have ha := defect_zero c hc 2 (![1,0,0,0,0,0]) 0 0
  have hb := defect_zero c hc 2 (![0,0,0,0,1,0]) 0 0
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_201 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 1 * c 1 13 + 1 * c 6 2=0 := by
  have h := defect_zero c hc 2 (![1,0,0,0,0,0]+![0,0,1,0,0,0]) 0 1
  have ha := defect_zero c hc 2 (![1,0,0,0,0,0]) 0 1
  have hb := defect_zero c hc 2 (![0,0,1,0,0,0]) 0 1
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_202 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 1 * c 1 16 + 1 * c 6 3=0 := by
  have h := defect_zero c hc 2 (![1,0,0,0,0,0]+![0,0,0,1,0,0]) 0 1
  have ha := defect_zero c hc 2 (![1,0,0,0,0,0]) 0 1
  have hb := defect_zero c hc 2 (![0,0,0,1,0,0]) 0 1
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_203 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 1 * c 1 8 + 1 * c 6 17=0 := by
  have h := defect_zero c hc 2 (![0,0,0,1,0,0]+![0,0,0,0,0,1]) 0 1
  have ha := defect_zero c hc 2 (![0,0,0,1,0,0]) 0 1
  have hb := defect_zero c hc 2 (![0,0,0,0,0,1]) 0 1
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_204 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 1 * c 3 4 + 1 * c 0 0 + 1 * c 9 0=0 := by
  have h := defect_zero c hc 2 (![1,0,0,0,0,0]) 0 3
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  try dsimp at h
  norm_num at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_205 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 1 * c 3 1 + 1 * c 3 19 + 1 * c 0 5 + 1 * c 9 5=0 := by
  have h := defect_zero c hc 2 (![1,0,0,0,0,0]+![0,0,0,0,0,1]) 0 3
  have ha := defect_zero c hc 2 (![1,0,0,0,0,0]) 0 3
  have hb := defect_zero c hc 2 (![0,0,0,0,0,1]) 0 3
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

private theorem constraint_206 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 1 * c 0 11 + 1 * c 9 11=0 := by
  have h := defect_zero c hc 2 (![0,0,1,0,0,0]) 0 3
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  try dsimp at h
  norm_num at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_207 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 1 * c 0 0 + 1 * c 4 0 + 1 * c 7 0 + (-1) * c 9 0=0 := by
  have h := ht (![1,0,0,0,0,0])
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_208 (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : 1 * c 0 5 + 1 * c 4 5 + 1 * c 7 5 + (-1) * c 9 5=0 := by
  have h := ht (![1,0,0,0,0,0]+![0,0,0,0,0,1])
  have ha := ht (![1,0,0,0,0,0])
  have hb := ht (![0,0,0,0,0,1])
  simp only [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  norm_num [defect,variation,dpoly,source,poly,field_action_formula,tensorAction,lorentz_formula,lorentzTable,
      Matrix.add_apply,Pi.add_apply,Pi.smul_apply,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ,Fin.succ,monomialPair,tensorIndex,Pi.single_apply] at h ha hb
  try dsimp at h ha hb
  norm_num at h ha hb
  linarith only [h,ha,hb]

theorem constraints_from_laws (c : Coeff) (hc : Covariant (source c))
    (ht : TraceFree (source c)) : constraints c=0 := by
  funext n
  fin_cases n
  · exact constraint_000 c hc ht
  · exact constraint_001 c hc ht
  · exact constraint_002 c hc ht
  · exact constraint_003 c hc ht
  · exact constraint_004 c hc ht
  · exact constraint_005 c hc ht
  · exact constraint_006 c hc ht
  · exact constraint_007 c hc ht
  · exact constraint_008 c hc ht
  · exact constraint_009 c hc ht
  · exact constraint_010 c hc ht
  · exact constraint_011 c hc ht
  · exact constraint_012 c hc ht
  · exact constraint_013 c hc ht
  · exact constraint_014 c hc ht
  · exact constraint_015 c hc ht
  · exact constraint_016 c hc ht
  · exact constraint_017 c hc ht
  · exact constraint_018 c hc ht
  · exact constraint_019 c hc ht
  · exact constraint_020 c hc ht
  · exact constraint_021 c hc ht
  · exact constraint_022 c hc ht
  · exact constraint_023 c hc ht
  · exact constraint_024 c hc ht
  · exact constraint_025 c hc ht
  · exact constraint_026 c hc ht
  · exact constraint_027 c hc ht
  · exact constraint_028 c hc ht
  · exact constraint_029 c hc ht
  · exact constraint_030 c hc ht
  · exact constraint_031 c hc ht
  · exact constraint_032 c hc ht
  · exact constraint_033 c hc ht
  · exact constraint_034 c hc ht
  · exact constraint_035 c hc ht
  · exact constraint_036 c hc ht
  · exact constraint_037 c hc ht
  · exact constraint_038 c hc ht
  · exact constraint_039 c hc ht
  · exact constraint_040 c hc ht
  · exact constraint_041 c hc ht
  · exact constraint_042 c hc ht
  · exact constraint_043 c hc ht
  · exact constraint_044 c hc ht
  · exact constraint_045 c hc ht
  · exact constraint_046 c hc ht
  · exact constraint_047 c hc ht
  · exact constraint_048 c hc ht
  · exact constraint_049 c hc ht
  · exact constraint_050 c hc ht
  · exact constraint_051 c hc ht
  · exact constraint_052 c hc ht
  · exact constraint_053 c hc ht
  · exact constraint_054 c hc ht
  · exact constraint_055 c hc ht
  · exact constraint_056 c hc ht
  · exact constraint_057 c hc ht
  · exact constraint_058 c hc ht
  · exact constraint_059 c hc ht
  · exact constraint_060 c hc ht
  · exact constraint_061 c hc ht
  · exact constraint_062 c hc ht
  · exact constraint_063 c hc ht
  · exact constraint_064 c hc ht
  · exact constraint_065 c hc ht
  · exact constraint_066 c hc ht
  · exact constraint_067 c hc ht
  · exact constraint_068 c hc ht
  · exact constraint_069 c hc ht
  · exact constraint_070 c hc ht
  · exact constraint_071 c hc ht
  · exact constraint_072 c hc ht
  · exact constraint_073 c hc ht
  · exact constraint_074 c hc ht
  · exact constraint_075 c hc ht
  · exact constraint_076 c hc ht
  · exact constraint_077 c hc ht
  · exact constraint_078 c hc ht
  · exact constraint_079 c hc ht
  · exact constraint_080 c hc ht
  · exact constraint_081 c hc ht
  · exact constraint_082 c hc ht
  · exact constraint_083 c hc ht
  · exact constraint_084 c hc ht
  · exact constraint_085 c hc ht
  · exact constraint_086 c hc ht
  · exact constraint_087 c hc ht
  · exact constraint_088 c hc ht
  · exact constraint_089 c hc ht
  · exact constraint_090 c hc ht
  · exact constraint_091 c hc ht
  · exact constraint_092 c hc ht
  · exact constraint_093 c hc ht
  · exact constraint_094 c hc ht
  · exact constraint_095 c hc ht
  · exact constraint_096 c hc ht
  · exact constraint_097 c hc ht
  · exact constraint_098 c hc ht
  · exact constraint_099 c hc ht
  · exact constraint_100 c hc ht
  · exact constraint_101 c hc ht
  · exact constraint_102 c hc ht
  · exact constraint_103 c hc ht
  · exact constraint_104 c hc ht
  · exact constraint_105 c hc ht
  · exact constraint_106 c hc ht
  · exact constraint_107 c hc ht
  · exact constraint_108 c hc ht
  · exact constraint_109 c hc ht
  · exact constraint_110 c hc ht
  · exact constraint_111 c hc ht
  · exact constraint_112 c hc ht
  · exact constraint_113 c hc ht
  · exact constraint_114 c hc ht
  · exact constraint_115 c hc ht
  · exact constraint_116 c hc ht
  · exact constraint_117 c hc ht
  · exact constraint_118 c hc ht
  · exact constraint_119 c hc ht
  · exact constraint_120 c hc ht
  · exact constraint_121 c hc ht
  · exact constraint_122 c hc ht
  · exact constraint_123 c hc ht
  · exact constraint_124 c hc ht
  · exact constraint_125 c hc ht
  · exact constraint_126 c hc ht
  · exact constraint_127 c hc ht
  · exact constraint_128 c hc ht
  · exact constraint_129 c hc ht
  · exact constraint_130 c hc ht
  · exact constraint_131 c hc ht
  · exact constraint_132 c hc ht
  · exact constraint_133 c hc ht
  · exact constraint_134 c hc ht
  · exact constraint_135 c hc ht
  · exact constraint_136 c hc ht
  · exact constraint_137 c hc ht
  · exact constraint_138 c hc ht
  · exact constraint_139 c hc ht
  · exact constraint_140 c hc ht
  · exact constraint_141 c hc ht
  · exact constraint_142 c hc ht
  · exact constraint_143 c hc ht
  · exact constraint_144 c hc ht
  · exact constraint_145 c hc ht
  · exact constraint_146 c hc ht
  · exact constraint_147 c hc ht
  · exact constraint_148 c hc ht
  · exact constraint_149 c hc ht
  · exact constraint_150 c hc ht
  · exact constraint_151 c hc ht
  · exact constraint_152 c hc ht
  · exact constraint_153 c hc ht
  · exact constraint_154 c hc ht
  · exact constraint_155 c hc ht
  · exact constraint_156 c hc ht
  · exact constraint_157 c hc ht
  · exact constraint_158 c hc ht
  · exact constraint_159 c hc ht
  · exact constraint_160 c hc ht
  · exact constraint_161 c hc ht
  · exact constraint_162 c hc ht
  · exact constraint_163 c hc ht
  · exact constraint_164 c hc ht
  · exact constraint_165 c hc ht
  · exact constraint_166 c hc ht
  · exact constraint_167 c hc ht
  · exact constraint_168 c hc ht
  · exact constraint_169 c hc ht
  · exact constraint_170 c hc ht
  · exact constraint_171 c hc ht
  · exact constraint_172 c hc ht
  · exact constraint_173 c hc ht
  · exact constraint_174 c hc ht
  · exact constraint_175 c hc ht
  · exact constraint_176 c hc ht
  · exact constraint_177 c hc ht
  · exact constraint_178 c hc ht
  · exact constraint_179 c hc ht
  · exact constraint_180 c hc ht
  · exact constraint_181 c hc ht
  · exact constraint_182 c hc ht
  · exact constraint_183 c hc ht
  · exact constraint_184 c hc ht
  · exact constraint_185 c hc ht
  · exact constraint_186 c hc ht
  · exact constraint_187 c hc ht
  · exact constraint_188 c hc ht
  · exact constraint_189 c hc ht
  · exact constraint_190 c hc ht
  · exact constraint_191 c hc ht
  · exact constraint_192 c hc ht
  · exact constraint_193 c hc ht
  · exact constraint_194 c hc ht
  · exact constraint_195 c hc ht
  · exact constraint_196 c hc ht
  · exact constraint_197 c hc ht
  · exact constraint_198 c hc ht
  · exact constraint_199 c hc ht
  · exact constraint_200 c hc ht
  · exact constraint_201 c hc ht
  · exact constraint_202 c hc ht
  · exact constraint_203 c hc ht
  · exact constraint_204 c hc ht
  · exact constraint_205 c hc ht
  · exact constraint_206 c hc ht
  · exact constraint_207 c hc ht
  · exact constraint_208 c hc ht

#print axioms constraints_from_laws
end
end PDTQuadraticSource
