module
public import LinearSourceData

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

private theorem row_0 (l : LinearCoeff) (h : LinearConserved l) : (1)*l 0 3 + (1)*l 1 1=0 := by
  have hh := congrFun (h (testJet 0) (testJet_vacuum 0)) 0
  norm_num [linearDivergence,linear,testJet,tensorIndex,Fin.sum_univ_succ] at hh
  try dsimp at hh
  norm_num at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]
private theorem row_1 (l : LinearCoeff) (h : LinearConserved l) : (1)*l 1 3 + (1)*l 4 1=0 := by
  have hh := congrFun (h (testJet 0) (testJet_vacuum 0)) 1
  norm_num [linearDivergence,linear,testJet,tensorIndex,Fin.sum_univ_succ] at hh
  try dsimp at hh
  norm_num at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]
private theorem row_2 (l : LinearCoeff) (h : LinearConserved l) : (1)*l 2 3 + (1)*l 5 1=0 := by
  have hh := congrFun (h (testJet 0) (testJet_vacuum 0)) 2
  norm_num [linearDivergence,linear,testJet,tensorIndex,Fin.sum_univ_succ] at hh
  try dsimp at hh
  norm_num at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]
private theorem row_3 (l : LinearCoeff) (h : LinearConserved l) : (1)*l 3 3 + (1)*l 6 1=0 := by
  have hh := congrFun (h (testJet 0) (testJet_vacuum 0)) 3
  norm_num [linearDivergence,linear,testJet,tensorIndex,Fin.sum_univ_succ] at hh
  try dsimp at hh
  norm_num at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]
private theorem row_4 (l : LinearCoeff) (h : LinearConserved l) : (1)*l 0 4 + (1)*l 1 2=0 := by
  have hh := congrFun (h (testJet 1) (testJet_vacuum 1)) 0
  norm_num [linearDivergence,linear,testJet,tensorIndex,Fin.sum_univ_succ] at hh
  try dsimp at hh
  norm_num at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]
private theorem row_5 (l : LinearCoeff) (h : LinearConserved l) : (1)*l 1 4 + (1)*l 4 2=0 := by
  have hh := congrFun (h (testJet 1) (testJet_vacuum 1)) 1
  norm_num [linearDivergence,linear,testJet,tensorIndex,Fin.sum_univ_succ] at hh
  try dsimp at hh
  norm_num at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]
private theorem row_6 (l : LinearCoeff) (h : LinearConserved l) : (1)*l 2 4 + (1)*l 5 2=0 := by
  have hh := congrFun (h (testJet 1) (testJet_vacuum 1)) 2
  norm_num [linearDivergence,linear,testJet,tensorIndex,Fin.sum_univ_succ] at hh
  try dsimp at hh
  norm_num at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]
private theorem row_7 (l : LinearCoeff) (h : LinearConserved l) : (1)*l 3 4 + (1)*l 6 2=0 := by
  have hh := congrFun (h (testJet 1) (testJet_vacuum 1)) 3
  norm_num [linearDivergence,linear,testJet,tensorIndex,Fin.sum_univ_succ] at hh
  try dsimp at hh
  norm_num at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]
private theorem row_8 (l : LinearCoeff) (h : LinearConserved l) : (-1)*l 0 1 + (1)*l 1 3=0 := by
  have hh := congrFun (h (testJet 2) (testJet_vacuum 2)) 0
  norm_num [linearDivergence,linear,testJet,tensorIndex,Fin.sum_univ_succ] at hh
  try dsimp at hh
  norm_num at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]
private theorem row_9 (l : LinearCoeff) (h : LinearConserved l) : (-1)*l 1 1 + (1)*l 4 3=0 := by
  have hh := congrFun (h (testJet 2) (testJet_vacuum 2)) 1
  norm_num [linearDivergence,linear,testJet,tensorIndex,Fin.sum_univ_succ] at hh
  try dsimp at hh
  norm_num at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]
private theorem row_10 (l : LinearCoeff) (h : LinearConserved l) : (-1)*l 2 1 + (1)*l 5 3=0 := by
  have hh := congrFun (h (testJet 2) (testJet_vacuum 2)) 2
  norm_num [linearDivergence,linear,testJet,tensorIndex,Fin.sum_univ_succ] at hh
  try dsimp at hh
  norm_num at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]
private theorem row_11 (l : LinearCoeff) (h : LinearConserved l) : (-1)*l 3 1 + (1)*l 6 3=0 := by
  have hh := congrFun (h (testJet 2) (testJet_vacuum 2)) 3
  norm_num [linearDivergence,linear,testJet,tensorIndex,Fin.sum_univ_succ] at hh
  try dsimp at hh
  norm_num at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]
private theorem row_12 (l : LinearCoeff) (h : LinearConserved l) : (-1)*l 0 2 + (1)*l 1 4=0 := by
  have hh := congrFun (h (testJet 3) (testJet_vacuum 3)) 0
  norm_num [linearDivergence,linear,testJet,tensorIndex,Fin.sum_univ_succ] at hh
  try dsimp at hh
  norm_num at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]
private theorem row_13 (l : LinearCoeff) (h : LinearConserved l) : (-1)*l 1 2 + (1)*l 4 4=0 := by
  have hh := congrFun (h (testJet 3) (testJet_vacuum 3)) 1
  norm_num [linearDivergence,linear,testJet,tensorIndex,Fin.sum_univ_succ] at hh
  try dsimp at hh
  norm_num at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]
private theorem row_14 (l : LinearCoeff) (h : LinearConserved l) : (-1)*l 2 2 + (1)*l 5 4=0 := by
  have hh := congrFun (h (testJet 3) (testJet_vacuum 3)) 2
  norm_num [linearDivergence,linear,testJet,tensorIndex,Fin.sum_univ_succ] at hh
  try dsimp at hh
  norm_num at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]
private theorem row_15 (l : LinearCoeff) (h : LinearConserved l) : (-1)*l 3 2 + (1)*l 6 4=0 := by
  have hh := congrFun (h (testJet 3) (testJet_vacuum 3)) 3
  norm_num [linearDivergence,linear,testJet,tensorIndex,Fin.sum_univ_succ] at hh
  try dsimp at hh
  norm_num at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]
private theorem row_16 (l : LinearCoeff) (h : LinearConserved l) : (-1)*l 0 3 + (1)*l 2 0=0 := by
  have hh := congrFun (h (testJet 4) (testJet_vacuum 4)) 0
  norm_num [linearDivergence,linear,testJet,tensorIndex,Fin.sum_univ_succ] at hh
  try dsimp at hh
  norm_num at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]
private theorem row_17 (l : LinearCoeff) (h : LinearConserved l) : (-1)*l 1 3 + (1)*l 5 0=0 := by
  have hh := congrFun (h (testJet 4) (testJet_vacuum 4)) 1
  norm_num [linearDivergence,linear,testJet,tensorIndex,Fin.sum_univ_succ] at hh
  try dsimp at hh
  norm_num at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]
private theorem row_18 (l : LinearCoeff) (h : LinearConserved l) : (-1)*l 2 3 + (1)*l 7 0=0 := by
  have hh := congrFun (h (testJet 4) (testJet_vacuum 4)) 2
  norm_num [linearDivergence,linear,testJet,tensorIndex,Fin.sum_univ_succ] at hh
  try dsimp at hh
  norm_num at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]
private theorem row_19 (l : LinearCoeff) (h : LinearConserved l) : (-1)*l 3 3 + (1)*l 8 0=0 := by
  have hh := congrFun (h (testJet 4) (testJet_vacuum 4)) 3
  norm_num [linearDivergence,linear,testJet,tensorIndex,Fin.sum_univ_succ] at hh
  try dsimp at hh
  norm_num at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]
private theorem row_20 (l : LinearCoeff) (h : LinearConserved l) : (-1)*l 1 0 + (1)*l 2 1=0 := by
  have hh := congrFun (h (testJet 5) (testJet_vacuum 5)) 0
  norm_num [linearDivergence,linear,testJet,tensorIndex,Fin.sum_univ_succ] at hh
  try dsimp at hh
  norm_num at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]
private theorem row_21 (l : LinearCoeff) (h : LinearConserved l) : (-1)*l 4 0 + (1)*l 5 1=0 := by
  have hh := congrFun (h (testJet 5) (testJet_vacuum 5)) 1
  norm_num [linearDivergence,linear,testJet,tensorIndex,Fin.sum_univ_succ] at hh
  try dsimp at hh
  norm_num at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]
private theorem row_22 (l : LinearCoeff) (h : LinearConserved l) : (-1)*l 5 0 + (1)*l 7 1=0 := by
  have hh := congrFun (h (testJet 5) (testJet_vacuum 5)) 2
  norm_num [linearDivergence,linear,testJet,tensorIndex,Fin.sum_univ_succ] at hh
  try dsimp at hh
  norm_num at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]
private theorem row_23 (l : LinearCoeff) (h : LinearConserved l) : (-1)*l 6 0 + (1)*l 8 1=0 := by
  have hh := congrFun (h (testJet 5) (testJet_vacuum 5)) 3
  norm_num [linearDivergence,linear,testJet,tensorIndex,Fin.sum_univ_succ] at hh
  try dsimp at hh
  norm_num at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]
private theorem row_24 (l : LinearCoeff) (h : LinearConserved l) : (1)*l 0 5 + (1)*l 2 2=0 := by
  have hh := congrFun (h (testJet 6) (testJet_vacuum 6)) 0
  norm_num [linearDivergence,linear,testJet,tensorIndex,Fin.sum_univ_succ] at hh
  try dsimp at hh
  norm_num at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]
private theorem row_25 (l : LinearCoeff) (h : LinearConserved l) : (1)*l 1 5 + (1)*l 5 2=0 := by
  have hh := congrFun (h (testJet 6) (testJet_vacuum 6)) 1
  norm_num [linearDivergence,linear,testJet,tensorIndex,Fin.sum_univ_succ] at hh
  try dsimp at hh
  norm_num at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]
private theorem row_26 (l : LinearCoeff) (h : LinearConserved l) : (1)*l 2 5 + (1)*l 7 2=0 := by
  have hh := congrFun (h (testJet 6) (testJet_vacuum 6)) 2
  norm_num [linearDivergence,linear,testJet,tensorIndex,Fin.sum_univ_succ] at hh
  try dsimp at hh
  norm_num at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]
private theorem row_27 (l : LinearCoeff) (h : LinearConserved l) : (1)*l 3 5 + (1)*l 8 2=0 := by
  have hh := congrFun (h (testJet 6) (testJet_vacuum 6)) 3
  norm_num [linearDivergence,linear,testJet,tensorIndex,Fin.sum_univ_succ] at hh
  try dsimp at hh
  norm_num at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]
private theorem row_28 (l : LinearCoeff) (h : LinearConserved l) : (1)*l 0 0 + (1)*l 2 3=0 := by
  have hh := congrFun (h (testJet 7) (testJet_vacuum 7)) 0
  norm_num [linearDivergence,linear,testJet,tensorIndex,Fin.sum_univ_succ] at hh
  try dsimp at hh
  norm_num at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]
private theorem row_29 (l : LinearCoeff) (h : LinearConserved l) : (1)*l 1 0 + (1)*l 5 3=0 := by
  have hh := congrFun (h (testJet 7) (testJet_vacuum 7)) 1
  norm_num [linearDivergence,linear,testJet,tensorIndex,Fin.sum_univ_succ] at hh
  try dsimp at hh
  norm_num at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]
private theorem row_30 (l : LinearCoeff) (h : LinearConserved l) : (1)*l 2 0 + (1)*l 7 3=0 := by
  have hh := congrFun (h (testJet 7) (testJet_vacuum 7)) 2
  norm_num [linearDivergence,linear,testJet,tensorIndex,Fin.sum_univ_succ] at hh
  try dsimp at hh
  norm_num at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]
private theorem row_31 (l : LinearCoeff) (h : LinearConserved l) : (1)*l 3 0 + (1)*l 8 3=0 := by
  have hh := congrFun (h (testJet 7) (testJet_vacuum 7)) 3
  norm_num [linearDivergence,linear,testJet,tensorIndex,Fin.sum_univ_succ] at hh
  try dsimp at hh
  norm_num at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]
private theorem row_32 (l : LinearCoeff) (h : LinearConserved l) : (1)*l 1 5 + (1)*l 2 4=0 := by
  have hh := congrFun (h (testJet 8) (testJet_vacuum 8)) 0
  norm_num [linearDivergence,linear,testJet,tensorIndex,Fin.sum_univ_succ] at hh
  try dsimp at hh
  norm_num at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]
private theorem row_33 (l : LinearCoeff) (h : LinearConserved l) : (1)*l 4 5 + (1)*l 5 4=0 := by
  have hh := congrFun (h (testJet 8) (testJet_vacuum 8)) 1
  norm_num [linearDivergence,linear,testJet,tensorIndex,Fin.sum_univ_succ] at hh
  try dsimp at hh
  norm_num at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]
private theorem row_34 (l : LinearCoeff) (h : LinearConserved l) : (1)*l 5 5 + (1)*l 7 4=0 := by
  have hh := congrFun (h (testJet 8) (testJet_vacuum 8)) 2
  norm_num [linearDivergence,linear,testJet,tensorIndex,Fin.sum_univ_succ] at hh
  try dsimp at hh
  norm_num at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]
private theorem row_35 (l : LinearCoeff) (h : LinearConserved l) : (1)*l 6 5 + (1)*l 8 4=0 := by
  have hh := congrFun (h (testJet 8) (testJet_vacuum 8)) 3
  norm_num [linearDivergence,linear,testJet,tensorIndex,Fin.sum_univ_succ] at hh
  try dsimp at hh
  norm_num at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]
private theorem row_36 (l : LinearCoeff) (h : LinearConserved l) : (-1)*l 0 2 + (1)*l 2 5=0 := by
  have hh := congrFun (h (testJet 9) (testJet_vacuum 9)) 0
  norm_num [linearDivergence,linear,testJet,tensorIndex,Fin.sum_univ_succ] at hh
  try dsimp at hh
  norm_num at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]
private theorem row_37 (l : LinearCoeff) (h : LinearConserved l) : (-1)*l 1 2 + (1)*l 5 5=0 := by
  have hh := congrFun (h (testJet 9) (testJet_vacuum 9)) 1
  norm_num [linearDivergence,linear,testJet,tensorIndex,Fin.sum_univ_succ] at hh
  try dsimp at hh
  norm_num at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]
private theorem row_38 (l : LinearCoeff) (h : LinearConserved l) : (-1)*l 2 2 + (1)*l 7 5=0 := by
  have hh := congrFun (h (testJet 9) (testJet_vacuum 9)) 2
  norm_num [linearDivergence,linear,testJet,tensorIndex,Fin.sum_univ_succ] at hh
  try dsimp at hh
  norm_num at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]
private theorem row_39 (l : LinearCoeff) (h : LinearConserved l) : (-1)*l 3 2 + (1)*l 8 5=0 := by
  have hh := congrFun (h (testJet 9) (testJet_vacuum 9)) 3
  norm_num [linearDivergence,linear,testJet,tensorIndex,Fin.sum_univ_succ] at hh
  try dsimp at hh
  norm_num at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]
private theorem row_40 (l : LinearCoeff) (h : LinearConserved l) : (1)*l 0 4 + (1)*l 3 0=0 := by
  have hh := congrFun (h (testJet 10) (testJet_vacuum 10)) 0
  norm_num [linearDivergence,linear,testJet,tensorIndex,Fin.sum_univ_succ] at hh
  try dsimp at hh
  norm_num at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]
private theorem row_41 (l : LinearCoeff) (h : LinearConserved l) : (1)*l 1 4 + (1)*l 6 0=0 := by
  have hh := congrFun (h (testJet 10) (testJet_vacuum 10)) 1
  norm_num [linearDivergence,linear,testJet,tensorIndex,Fin.sum_univ_succ] at hh
  try dsimp at hh
  norm_num at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]
private theorem row_42 (l : LinearCoeff) (h : LinearConserved l) : (1)*l 2 4 + (1)*l 8 0=0 := by
  have hh := congrFun (h (testJet 10) (testJet_vacuum 10)) 2
  norm_num [linearDivergence,linear,testJet,tensorIndex,Fin.sum_univ_succ] at hh
  try dsimp at hh
  norm_num at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]
private theorem row_43 (l : LinearCoeff) (h : LinearConserved l) : (1)*l 3 4 + (1)*l 9 0=0 := by
  have hh := congrFun (h (testJet 10) (testJet_vacuum 10)) 3
  norm_num [linearDivergence,linear,testJet,tensorIndex,Fin.sum_univ_succ] at hh
  try dsimp at hh
  norm_num at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]
private theorem row_44 (l : LinearCoeff) (h : LinearConserved l) : (1)*l 0 5 + (1)*l 3 1=0 := by
  have hh := congrFun (h (testJet 11) (testJet_vacuum 11)) 0
  norm_num [linearDivergence,linear,testJet,tensorIndex,Fin.sum_univ_succ] at hh
  try dsimp at hh
  norm_num at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]
private theorem row_45 (l : LinearCoeff) (h : LinearConserved l) : (1)*l 3 5 + (1)*l 9 1=0 := by
  have hh := congrFun (h (testJet 11) (testJet_vacuum 11)) 3
  norm_num [linearDivergence,linear,testJet,tensorIndex,Fin.sum_univ_succ] at hh
  try dsimp at hh
  norm_num at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]
private theorem row_46 (l : LinearCoeff) (h : LinearConserved l) : (-1)*l 1 0 + (1)*l 3 2=0 := by
  have hh := congrFun (h (testJet 12) (testJet_vacuum 12)) 0
  norm_num [linearDivergence,linear,testJet,tensorIndex,Fin.sum_univ_succ] at hh
  try dsimp at hh
  norm_num at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]
private theorem row_47 (l : LinearCoeff) (h : LinearConserved l) : (-1)*l 4 0 + (1)*l 6 2=0 := by
  have hh := congrFun (h (testJet 12) (testJet_vacuum 12)) 1
  norm_num [linearDivergence,linear,testJet,tensorIndex,Fin.sum_univ_succ] at hh
  try dsimp at hh
  norm_num at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]
private theorem row_48 (l : LinearCoeff) (h : LinearConserved l) : (-1)*l 5 0 + (1)*l 8 2=0 := by
  have hh := congrFun (h (testJet 12) (testJet_vacuum 12)) 2
  norm_num [linearDivergence,linear,testJet,tensorIndex,Fin.sum_univ_succ] at hh
  try dsimp at hh
  norm_num at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]
private theorem row_49 (l : LinearCoeff) (h : LinearConserved l) : (-1)*l 6 0 + (1)*l 9 2=0 := by
  have hh := congrFun (h (testJet 12) (testJet_vacuum 12)) 3
  norm_num [linearDivergence,linear,testJet,tensorIndex,Fin.sum_univ_succ] at hh
  try dsimp at hh
  norm_num at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]
private theorem row_50 (l : LinearCoeff) (h : LinearConserved l) : (1)*l 6 5 + (1)*l 9 3=0 := by
  have hh := congrFun (h (testJet 13) (testJet_vacuum 13)) 3
  norm_num [linearDivergence,linear,testJet,tensorIndex,Fin.sum_univ_succ] at hh
  try dsimp at hh
  norm_num at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]
private theorem row_51 (l : LinearCoeff) (h : LinearConserved l) : (1)*l 2 0 + (1)*l 8 4=0 := by
  have hh := congrFun (h (testJet 14) (testJet_vacuum 14)) 2
  norm_num [linearDivergence,linear,testJet,tensorIndex,Fin.sum_univ_succ] at hh
  try dsimp at hh
  norm_num at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]
private theorem row_52 (l : LinearCoeff) (h : LinearConserved l) : (1)*l 3 0 + (1)*l 9 4=0 := by
  have hh := congrFun (h (testJet 14) (testJet_vacuum 14)) 3
  norm_num [linearDivergence,linear,testJet,tensorIndex,Fin.sum_univ_succ] at hh
  try dsimp at hh
  norm_num at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]
private theorem row_53 (l : LinearCoeff) (h : LinearConserved l) : (1)*l 3 1 + (1)*l 9 5=0 := by
  have hh := congrFun (h (testJet 15) (testJet_vacuum 15)) 3
  norm_num [linearDivergence,linear,testJet,tensorIndex,Fin.sum_univ_succ] at hh
  try dsimp at hh
  norm_num at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]
theorem linear_constraints_from_law (l : LinearCoeff) (h : LinearConserved l) :
    linearConstraints l=0 := by
  ext i
  fin_cases i
  · exact row_0 l h
  · exact row_1 l h
  · exact row_2 l h
  · exact row_3 l h
  · exact row_4 l h
  · exact row_5 l h
  · exact row_6 l h
  · exact row_7 l h
  · exact row_8 l h
  · exact row_9 l h
  · exact row_10 l h
  · exact row_11 l h
  · exact row_12 l h
  · exact row_13 l h
  · exact row_14 l h
  · exact row_15 l h
  · exact row_16 l h
  · exact row_17 l h
  · exact row_18 l h
  · exact row_19 l h
  · exact row_20 l h
  · exact row_21 l h
  · exact row_22 l h
  · exact row_23 l h
  · exact row_24 l h
  · exact row_25 l h
  · exact row_26 l h
  · exact row_27 l h
  · exact row_28 l h
  · exact row_29 l h
  · exact row_30 l h
  · exact row_31 l h
  · exact row_32 l h
  · exact row_33 l h
  · exact row_34 l h
  · exact row_35 l h
  · exact row_36 l h
  · exact row_37 l h
  · exact row_38 l h
  · exact row_39 l h
  · exact row_40 l h
  · exact row_41 l h
  · exact row_42 l h
  · exact row_43 l h
  · exact row_44 l h
  · exact row_45 l h
  · exact row_46 l h
  · exact row_47 l h
  · exact row_48 l h
  · exact row_49 l h
  · exact row_50 l h
  · exact row_51 l h
  · exact row_52 l h
  · exact row_53 l h
#print axioms linear_constraints_from_law
end
end PDTPolynomialSource
