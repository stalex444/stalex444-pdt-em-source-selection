module
public import ConservationData

@[expose] public section
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
namespace PDTConservedSource
noncomputable section
open PDTStressTensor PDTUnrestrictedSourceKernel PDTQuadraticSource
open scoped Matrix

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

private theorem constraint_000 (c : Coeff) (hc : Conserved (source c)) :
    1 * c 0 3 + 1 * c 1 1=0 := by
  have h := conservation_reading c hc ![1,0,0,0,0,0] (testJet 0) (testJet_vacuum 0) 0
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_001 (c : Coeff) (hc : Conserved (source c)) :
    1 * c 1 3 + 1 * c 4 1=0 := by
  have h := conservation_reading c hc ![1,0,0,0,0,0] (testJet 0) (testJet_vacuum 0) 1
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_002 (c : Coeff) (hc : Conserved (source c)) :
    1 * c 2 3 + 1 * c 5 1=0 := by
  have h := conservation_reading c hc ![1,0,0,0,0,0] (testJet 0) (testJet_vacuum 0) 2
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_003 (c : Coeff) (hc : Conserved (source c)) :
    1 * c 3 3 + 1 * c 6 1=0 := by
  have h := conservation_reading c hc ![1,0,0,0,0,0] (testJet 0) (testJet_vacuum 0) 3
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_004 (c : Coeff) (hc : Conserved (source c)) :
    1 * c 0 8 + 2 * c 1 6=0 := by
  have h := conservation_reading c hc ![0,1,0,0,0,0] (testJet 0) (testJet_vacuum 0) 0
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_005 (c : Coeff) (hc : Conserved (source c)) :
    1 * c 1 8 + 2 * c 4 6=0 := by
  have h := conservation_reading c hc ![0,1,0,0,0,0] (testJet 0) (testJet_vacuum 0) 1
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_006 (c : Coeff) (hc : Conserved (source c)) :
    1 * c 2 8 + 2 * c 5 6=0 := by
  have h := conservation_reading c hc ![0,1,0,0,0,0] (testJet 0) (testJet_vacuum 0) 2
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_007 (c : Coeff) (hc : Conserved (source c)) :
    1 * c 3 8 + 2 * c 6 6=0 := by
  have h := conservation_reading c hc ![0,1,0,0,0,0] (testJet 0) (testJet_vacuum 0) 3
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_008 (c : Coeff) (hc : Conserved (source c)) :
    1 * c 0 12 + 1 * c 1 7=0 := by
  have h := conservation_reading c hc ![0,0,1,0,0,0] (testJet 0) (testJet_vacuum 0) 0
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_009 (c : Coeff) (hc : Conserved (source c)) :
    1 * c 1 12 + 1 * c 4 7=0 := by
  have h := conservation_reading c hc ![0,0,1,0,0,0] (testJet 0) (testJet_vacuum 0) 1
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_010 (c : Coeff) (hc : Conserved (source c)) :
    1 * c 2 12 + 1 * c 5 7=0 := by
  have h := conservation_reading c hc ![0,0,1,0,0,0] (testJet 0) (testJet_vacuum 0) 2
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_011 (c : Coeff) (hc : Conserved (source c)) :
    1 * c 3 12 + 1 * c 6 7=0 := by
  have h := conservation_reading c hc ![0,0,1,0,0,0] (testJet 0) (testJet_vacuum 0) 3
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_012 (c : Coeff) (hc : Conserved (source c)) :
    2 * c 0 15 + 1 * c 1 8=0 := by
  have h := conservation_reading c hc ![0,0,0,1,0,0] (testJet 0) (testJet_vacuum 0) 0
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_013 (c : Coeff) (hc : Conserved (source c)) :
    2 * c 1 15 + 1 * c 4 8=0 := by
  have h := conservation_reading c hc ![0,0,0,1,0,0] (testJet 0) (testJet_vacuum 0) 1
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_014 (c : Coeff) (hc : Conserved (source c)) :
    2 * c 2 15 + 1 * c 5 8=0 := by
  have h := conservation_reading c hc ![0,0,0,1,0,0] (testJet 0) (testJet_vacuum 0) 2
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_015 (c : Coeff) (hc : Conserved (source c)) :
    2 * c 3 15 + 1 * c 6 8=0 := by
  have h := conservation_reading c hc ![0,0,0,1,0,0] (testJet 0) (testJet_vacuum 0) 3
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_016 (c : Coeff) (hc : Conserved (source c)) :
    1 * c 0 16 + 1 * c 1 9=0 := by
  have h := conservation_reading c hc ![0,0,0,0,1,0] (testJet 0) (testJet_vacuum 0) 0
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_017 (c : Coeff) (hc : Conserved (source c)) :
    1 * c 1 16 + 1 * c 4 9=0 := by
  have h := conservation_reading c hc ![0,0,0,0,1,0] (testJet 0) (testJet_vacuum 0) 1
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_018 (c : Coeff) (hc : Conserved (source c)) :
    1 * c 2 16 + 1 * c 5 9=0 := by
  have h := conservation_reading c hc ![0,0,0,0,1,0] (testJet 0) (testJet_vacuum 0) 2
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_019 (c : Coeff) (hc : Conserved (source c)) :
    1 * c 3 16 + 1 * c 6 9=0 := by
  have h := conservation_reading c hc ![0,0,0,0,1,0] (testJet 0) (testJet_vacuum 0) 3
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_020 (c : Coeff) (hc : Conserved (source c)) :
    1 * c 0 17 + 1 * c 1 10=0 := by
  have h := conservation_reading c hc ![0,0,0,0,0,1] (testJet 0) (testJet_vacuum 0) 0
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_021 (c : Coeff) (hc : Conserved (source c)) :
    1 * c 1 17 + 1 * c 4 10=0 := by
  have h := conservation_reading c hc ![0,0,0,0,0,1] (testJet 0) (testJet_vacuum 0) 1
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_022 (c : Coeff) (hc : Conserved (source c)) :
    1 * c 2 17 + 1 * c 5 10=0 := by
  have h := conservation_reading c hc ![0,0,0,0,0,1] (testJet 0) (testJet_vacuum 0) 2
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_023 (c : Coeff) (hc : Conserved (source c)) :
    1 * c 3 17 + 1 * c 6 10=0 := by
  have h := conservation_reading c hc ![0,0,0,0,0,1] (testJet 0) (testJet_vacuum 0) 3
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_024 (c : Coeff) (hc : Conserved (source c)) :
    1 * c 0 4 + 1 * c 1 2=0 := by
  have h := conservation_reading c hc ![1,0,0,0,0,0] (testJet 1) (testJet_vacuum 1) 0
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_025 (c : Coeff) (hc : Conserved (source c)) :
    1 * c 1 4 + 1 * c 4 2=0 := by
  have h := conservation_reading c hc ![1,0,0,0,0,0] (testJet 1) (testJet_vacuum 1) 1
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_026 (c : Coeff) (hc : Conserved (source c)) :
    1 * c 2 4 + 1 * c 5 2=0 := by
  have h := conservation_reading c hc ![1,0,0,0,0,0] (testJet 1) (testJet_vacuum 1) 2
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_027 (c : Coeff) (hc : Conserved (source c)) :
    1 * c 3 4 + 1 * c 6 2=0 := by
  have h := conservation_reading c hc ![1,0,0,0,0,0] (testJet 1) (testJet_vacuum 1) 3
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_028 (c : Coeff) (hc : Conserved (source c)) :
    1 * c 0 9 + 1 * c 1 7=0 := by
  have h := conservation_reading c hc ![0,1,0,0,0,0] (testJet 1) (testJet_vacuum 1) 0
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_029 (c : Coeff) (hc : Conserved (source c)) :
    1 * c 1 9 + 1 * c 4 7=0 := by
  have h := conservation_reading c hc ![0,1,0,0,0,0] (testJet 1) (testJet_vacuum 1) 1
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_030 (c : Coeff) (hc : Conserved (source c)) :
    1 * c 2 9 + 1 * c 5 7=0 := by
  have h := conservation_reading c hc ![0,1,0,0,0,0] (testJet 1) (testJet_vacuum 1) 2
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_031 (c : Coeff) (hc : Conserved (source c)) :
    1 * c 3 9 + 1 * c 6 7=0 := by
  have h := conservation_reading c hc ![0,1,0,0,0,0] (testJet 1) (testJet_vacuum 1) 3
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_032 (c : Coeff) (hc : Conserved (source c)) :
    1 * c 0 13 + 2 * c 1 11=0 := by
  have h := conservation_reading c hc ![0,0,1,0,0,0] (testJet 1) (testJet_vacuum 1) 0
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_033 (c : Coeff) (hc : Conserved (source c)) :
    1 * c 1 13 + 2 * c 4 11=0 := by
  have h := conservation_reading c hc ![0,0,1,0,0,0] (testJet 1) (testJet_vacuum 1) 1
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_034 (c : Coeff) (hc : Conserved (source c)) :
    1 * c 2 13 + 2 * c 5 11=0 := by
  have h := conservation_reading c hc ![0,0,1,0,0,0] (testJet 1) (testJet_vacuum 1) 2
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_035 (c : Coeff) (hc : Conserved (source c)) :
    1 * c 3 13 + 2 * c 6 11=0 := by
  have h := conservation_reading c hc ![0,0,1,0,0,0] (testJet 1) (testJet_vacuum 1) 3
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_036 (c : Coeff) (hc : Conserved (source c)) :
    1 * c 1 16 + 1 * c 4 12=0 := by
  have h := conservation_reading c hc ![0,0,0,1,0,0] (testJet 1) (testJet_vacuum 1) 1
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_037 (c : Coeff) (hc : Conserved (source c)) :
    1 * c 2 16 + 1 * c 5 12=0 := by
  have h := conservation_reading c hc ![0,0,0,1,0,0] (testJet 1) (testJet_vacuum 1) 2
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_038 (c : Coeff) (hc : Conserved (source c)) :
    1 * c 3 16 + 1 * c 6 12=0 := by
  have h := conservation_reading c hc ![0,0,0,1,0,0] (testJet 1) (testJet_vacuum 1) 3
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_039 (c : Coeff) (hc : Conserved (source c)) :
    2 * c 0 18 + 1 * c 1 13=0 := by
  have h := conservation_reading c hc ![0,0,0,0,1,0] (testJet 1) (testJet_vacuum 1) 0
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_040 (c : Coeff) (hc : Conserved (source c)) :
    2 * c 1 18 + 1 * c 4 13=0 := by
  have h := conservation_reading c hc ![0,0,0,0,1,0] (testJet 1) (testJet_vacuum 1) 1
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_041 (c : Coeff) (hc : Conserved (source c)) :
    2 * c 2 18 + 1 * c 5 13=0 := by
  have h := conservation_reading c hc ![0,0,0,0,1,0] (testJet 1) (testJet_vacuum 1) 2
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_042 (c : Coeff) (hc : Conserved (source c)) :
    2 * c 3 18 + 1 * c 6 13=0 := by
  have h := conservation_reading c hc ![0,0,0,0,1,0] (testJet 1) (testJet_vacuum 1) 3
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_043 (c : Coeff) (hc : Conserved (source c)) :
    1 * c 0 19 + 1 * c 1 14=0 := by
  have h := conservation_reading c hc ![0,0,0,0,0,1] (testJet 1) (testJet_vacuum 1) 0
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_044 (c : Coeff) (hc : Conserved (source c)) :
    1 * c 1 19 + 1 * c 4 14=0 := by
  have h := conservation_reading c hc ![0,0,0,0,0,1] (testJet 1) (testJet_vacuum 1) 1
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_045 (c : Coeff) (hc : Conserved (source c)) :
    1 * c 2 19 + 1 * c 5 14=0 := by
  have h := conservation_reading c hc ![0,0,0,0,0,1] (testJet 1) (testJet_vacuum 1) 2
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_046 (c : Coeff) (hc : Conserved (source c)) :
    1 * c 3 19 + 1 * c 6 14=0 := by
  have h := conservation_reading c hc ![0,0,0,0,0,1] (testJet 1) (testJet_vacuum 1) 3
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_047 (c : Coeff) (hc : Conserved (source c)) :
    (-1) * c 0 1 + 1 * c 1 3=0 := by
  have h := conservation_reading c hc ![1,0,0,0,0,0] (testJet 2) (testJet_vacuum 2) 0
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_048 (c : Coeff) (hc : Conserved (source c)) :
    (-1) * c 1 1 + 1 * c 4 3=0 := by
  have h := conservation_reading c hc ![1,0,0,0,0,0] (testJet 2) (testJet_vacuum 2) 1
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_049 (c : Coeff) (hc : Conserved (source c)) :
    (-1) * c 2 1 + 1 * c 5 3=0 := by
  have h := conservation_reading c hc ![1,0,0,0,0,0] (testJet 2) (testJet_vacuum 2) 2
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_050 (c : Coeff) (hc : Conserved (source c)) :
    (-1) * c 3 1 + 1 * c 6 3=0 := by
  have h := conservation_reading c hc ![1,0,0,0,0,0] (testJet 2) (testJet_vacuum 2) 3
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_051 (c : Coeff) (hc : Conserved (source c)) :
    (-2) * c 0 6 + 1 * c 1 8=0 := by
  have h := conservation_reading c hc ![0,1,0,0,0,0] (testJet 2) (testJet_vacuum 2) 0
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_052 (c : Coeff) (hc : Conserved (source c)) :
    (-2) * c 1 6 + 1 * c 4 8=0 := by
  have h := conservation_reading c hc ![0,1,0,0,0,0] (testJet 2) (testJet_vacuum 2) 1
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_053 (c : Coeff) (hc : Conserved (source c)) :
    (-2) * c 2 6 + 1 * c 5 8=0 := by
  have h := conservation_reading c hc ![0,1,0,0,0,0] (testJet 2) (testJet_vacuum 2) 2
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_054 (c : Coeff) (hc : Conserved (source c)) :
    (-2) * c 3 6 + 1 * c 6 8=0 := by
  have h := conservation_reading c hc ![0,1,0,0,0,0] (testJet 2) (testJet_vacuum 2) 3
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_055 (c : Coeff) (hc : Conserved (source c)) :
    (-1) * c 0 7 + 1 * c 1 12=0 := by
  have h := conservation_reading c hc ![0,0,1,0,0,0] (testJet 2) (testJet_vacuum 2) 0
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_056 (c : Coeff) (hc : Conserved (source c)) :
    (-1) * c 1 7 + 1 * c 4 12=0 := by
  have h := conservation_reading c hc ![0,0,1,0,0,0] (testJet 2) (testJet_vacuum 2) 1
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_057 (c : Coeff) (hc : Conserved (source c)) :
    (-1) * c 2 7 + 1 * c 5 12=0 := by
  have h := conservation_reading c hc ![0,0,1,0,0,0] (testJet 2) (testJet_vacuum 2) 2
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_058 (c : Coeff) (hc : Conserved (source c)) :
    (-1) * c 3 7 + 1 * c 6 12=0 := by
  have h := conservation_reading c hc ![0,0,1,0,0,0] (testJet 2) (testJet_vacuum 2) 3
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_059 (c : Coeff) (hc : Conserved (source c)) :
    (-1) * c 1 8 + 2 * c 4 15=0 := by
  have h := conservation_reading c hc ![0,0,0,1,0,0] (testJet 2) (testJet_vacuum 2) 1
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_060 (c : Coeff) (hc : Conserved (source c)) :
    (-1) * c 2 8 + 2 * c 5 15=0 := by
  have h := conservation_reading c hc ![0,0,0,1,0,0] (testJet 2) (testJet_vacuum 2) 2
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_061 (c : Coeff) (hc : Conserved (source c)) :
    (-1) * c 3 8 + 2 * c 6 15=0 := by
  have h := conservation_reading c hc ![0,0,0,1,0,0] (testJet 2) (testJet_vacuum 2) 3
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_062 (c : Coeff) (hc : Conserved (source c)) :
    (-1) * c 1 9 + 1 * c 4 16=0 := by
  have h := conservation_reading c hc ![0,0,0,0,1,0] (testJet 2) (testJet_vacuum 2) 1
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_063 (c : Coeff) (hc : Conserved (source c)) :
    (-1) * c 2 9 + 1 * c 5 16=0 := by
  have h := conservation_reading c hc ![0,0,0,0,1,0] (testJet 2) (testJet_vacuum 2) 2
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_064 (c : Coeff) (hc : Conserved (source c)) :
    (-1) * c 3 9 + 1 * c 6 16=0 := by
  have h := conservation_reading c hc ![0,0,0,0,1,0] (testJet 2) (testJet_vacuum 2) 3
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_065 (c : Coeff) (hc : Conserved (source c)) :
    (-1) * c 0 10 + 1 * c 1 17=0 := by
  have h := conservation_reading c hc ![0,0,0,0,0,1] (testJet 2) (testJet_vacuum 2) 0
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_066 (c : Coeff) (hc : Conserved (source c)) :
    (-1) * c 1 10 + 1 * c 4 17=0 := by
  have h := conservation_reading c hc ![0,0,0,0,0,1] (testJet 2) (testJet_vacuum 2) 1
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_067 (c : Coeff) (hc : Conserved (source c)) :
    (-1) * c 2 10 + 1 * c 5 17=0 := by
  have h := conservation_reading c hc ![0,0,0,0,0,1] (testJet 2) (testJet_vacuum 2) 2
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_068 (c : Coeff) (hc : Conserved (source c)) :
    (-1) * c 3 10 + 1 * c 6 17=0 := by
  have h := conservation_reading c hc ![0,0,0,0,0,1] (testJet 2) (testJet_vacuum 2) 3
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_069 (c : Coeff) (hc : Conserved (source c)) :
    (-1) * c 0 2 + 1 * c 1 4=0 := by
  have h := conservation_reading c hc ![1,0,0,0,0,0] (testJet 3) (testJet_vacuum 3) 0
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_070 (c : Coeff) (hc : Conserved (source c)) :
    (-1) * c 1 2 + 1 * c 4 4=0 := by
  have h := conservation_reading c hc ![1,0,0,0,0,0] (testJet 3) (testJet_vacuum 3) 1
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_071 (c : Coeff) (hc : Conserved (source c)) :
    (-1) * c 2 2 + 1 * c 5 4=0 := by
  have h := conservation_reading c hc ![1,0,0,0,0,0] (testJet 3) (testJet_vacuum 3) 2
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_072 (c : Coeff) (hc : Conserved (source c)) :
    (-1) * c 3 2 + 1 * c 6 4=0 := by
  have h := conservation_reading c hc ![1,0,0,0,0,0] (testJet 3) (testJet_vacuum 3) 3
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_073 (c : Coeff) (hc : Conserved (source c)) :
    (-2) * c 0 11 + 1 * c 1 13=0 := by
  have h := conservation_reading c hc ![0,0,1,0,0,0] (testJet 3) (testJet_vacuum 3) 0
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_074 (c : Coeff) (hc : Conserved (source c)) :
    (-2) * c 1 11 + 1 * c 4 13=0 := by
  have h := conservation_reading c hc ![0,0,1,0,0,0] (testJet 3) (testJet_vacuum 3) 1
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_075 (c : Coeff) (hc : Conserved (source c)) :
    (-2) * c 2 11 + 1 * c 5 13=0 := by
  have h := conservation_reading c hc ![0,0,1,0,0,0] (testJet 3) (testJet_vacuum 3) 2
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_076 (c : Coeff) (hc : Conserved (source c)) :
    (-2) * c 3 11 + 1 * c 6 13=0 := by
  have h := conservation_reading c hc ![0,0,1,0,0,0] (testJet 3) (testJet_vacuum 3) 3
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_077 (c : Coeff) (hc : Conserved (source c)) :
    (-1) * c 1 13 + 2 * c 4 18=0 := by
  have h := conservation_reading c hc ![0,0,0,0,1,0] (testJet 3) (testJet_vacuum 3) 1
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_078 (c : Coeff) (hc : Conserved (source c)) :
    (-1) * c 2 13 + 2 * c 5 18=0 := by
  have h := conservation_reading c hc ![0,0,0,0,1,0] (testJet 3) (testJet_vacuum 3) 2
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_079 (c : Coeff) (hc : Conserved (source c)) :
    (-1) * c 3 13 + 2 * c 6 18=0 := by
  have h := conservation_reading c hc ![0,0,0,0,1,0] (testJet 3) (testJet_vacuum 3) 3
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_080 (c : Coeff) (hc : Conserved (source c)) :
    (-1) * c 0 14 + 1 * c 1 19=0 := by
  have h := conservation_reading c hc ![0,0,0,0,0,1] (testJet 3) (testJet_vacuum 3) 0
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_081 (c : Coeff) (hc : Conserved (source c)) :
    (-1) * c 1 14 + 1 * c 4 19=0 := by
  have h := conservation_reading c hc ![0,0,0,0,0,1] (testJet 3) (testJet_vacuum 3) 1
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_082 (c : Coeff) (hc : Conserved (source c)) :
    (-1) * c 2 14 + 1 * c 5 19=0 := by
  have h := conservation_reading c hc ![0,0,0,0,0,1] (testJet 3) (testJet_vacuum 3) 2
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_083 (c : Coeff) (hc : Conserved (source c)) :
    (-1) * c 3 14 + 1 * c 6 19=0 := by
  have h := conservation_reading c hc ![0,0,0,0,0,1] (testJet 3) (testJet_vacuum 3) 3
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_084 (c : Coeff) (hc : Conserved (source c)) :
    (-1) * c 0 3 + 2 * c 2 0=0 := by
  have h := conservation_reading c hc ![1,0,0,0,0,0] (testJet 4) (testJet_vacuum 4) 0
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_085 (c : Coeff) (hc : Conserved (source c)) :
    (-1) * c 1 3 + 2 * c 5 0=0 := by
  have h := conservation_reading c hc ![1,0,0,0,0,0] (testJet 4) (testJet_vacuum 4) 1
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_086 (c : Coeff) (hc : Conserved (source c)) :
    (-1) * c 2 3 + 2 * c 7 0=0 := by
  have h := conservation_reading c hc ![1,0,0,0,0,0] (testJet 4) (testJet_vacuum 4) 2
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_087 (c : Coeff) (hc : Conserved (source c)) :
    (-1) * c 3 3 + 2 * c 8 0=0 := by
  have h := conservation_reading c hc ![1,0,0,0,0,0] (testJet 4) (testJet_vacuum 4) 3
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_088 (c : Coeff) (hc : Conserved (source c)) :
    (-1) * c 0 8 + 1 * c 2 1=0 := by
  have h := conservation_reading c hc ![0,1,0,0,0,0] (testJet 4) (testJet_vacuum 4) 0
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_089 (c : Coeff) (hc : Conserved (source c)) :
    (-1) * c 1 8 + 1 * c 5 1=0 := by
  have h := conservation_reading c hc ![0,1,0,0,0,0] (testJet 4) (testJet_vacuum 4) 1
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_090 (c : Coeff) (hc : Conserved (source c)) :
    (-1) * c 2 8 + 1 * c 7 1=0 := by
  have h := conservation_reading c hc ![0,1,0,0,0,0] (testJet 4) (testJet_vacuum 4) 2
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_091 (c : Coeff) (hc : Conserved (source c)) :
    (-1) * c 3 8 + 1 * c 8 1=0 := by
  have h := conservation_reading c hc ![0,1,0,0,0,0] (testJet 4) (testJet_vacuum 4) 3
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_092 (c : Coeff) (hc : Conserved (source c)) :
    (-1) * c 0 12 + 1 * c 2 2=0 := by
  have h := conservation_reading c hc ![0,0,1,0,0,0] (testJet 4) (testJet_vacuum 4) 0
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_093 (c : Coeff) (hc : Conserved (source c)) :
    (-1) * c 1 12 + 1 * c 5 2=0 := by
  have h := conservation_reading c hc ![0,0,1,0,0,0] (testJet 4) (testJet_vacuum 4) 1
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_094 (c : Coeff) (hc : Conserved (source c)) :
    (-1) * c 2 12 + 1 * c 7 2=0 := by
  have h := conservation_reading c hc ![0,0,1,0,0,0] (testJet 4) (testJet_vacuum 4) 2
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_095 (c : Coeff) (hc : Conserved (source c)) :
    (-1) * c 3 12 + 1 * c 8 2=0 := by
  have h := conservation_reading c hc ![0,0,1,0,0,0] (testJet 4) (testJet_vacuum 4) 3
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_096 (c : Coeff) (hc : Conserved (source c)) :
    (-2) * c 2 15 + 1 * c 7 3=0 := by
  have h := conservation_reading c hc ![0,0,0,1,0,0] (testJet 4) (testJet_vacuum 4) 2
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_097 (c : Coeff) (hc : Conserved (source c)) :
    (-2) * c 3 15 + 1 * c 8 3=0 := by
  have h := conservation_reading c hc ![0,0,0,1,0,0] (testJet 4) (testJet_vacuum 4) 3
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_098 (c : Coeff) (hc : Conserved (source c)) :
    (-1) * c 2 16 + 1 * c 7 4=0 := by
  have h := conservation_reading c hc ![0,0,0,0,1,0] (testJet 4) (testJet_vacuum 4) 2
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_099 (c : Coeff) (hc : Conserved (source c)) :
    (-1) * c 3 16 + 1 * c 8 4=0 := by
  have h := conservation_reading c hc ![0,0,0,0,1,0] (testJet 4) (testJet_vacuum 4) 3
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_100 (c : Coeff) (hc : Conserved (source c)) :
    (-1) * c 0 17 + 1 * c 2 5=0 := by
  have h := conservation_reading c hc ![0,0,0,0,0,1] (testJet 4) (testJet_vacuum 4) 0
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_101 (c : Coeff) (hc : Conserved (source c)) :
    (-1) * c 1 17 + 1 * c 5 5=0 := by
  have h := conservation_reading c hc ![0,0,0,0,0,1] (testJet 4) (testJet_vacuum 4) 1
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_102 (c : Coeff) (hc : Conserved (source c)) :
    (-1) * c 2 17 + 1 * c 7 5=0 := by
  have h := conservation_reading c hc ![0,0,0,0,0,1] (testJet 4) (testJet_vacuum 4) 2
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_103 (c : Coeff) (hc : Conserved (source c)) :
    (-1) * c 3 17 + 1 * c 8 5=0 := by
  have h := conservation_reading c hc ![0,0,0,0,0,1] (testJet 4) (testJet_vacuum 4) 3
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_104 (c : Coeff) (hc : Conserved (source c)) :
    (-2) * c 1 0 + 1 * c 2 1=0 := by
  have h := conservation_reading c hc ![1,0,0,0,0,0] (testJet 5) (testJet_vacuum 5) 0
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_105 (c : Coeff) (hc : Conserved (source c)) :
    (-2) * c 4 0 + 1 * c 5 1=0 := by
  have h := conservation_reading c hc ![1,0,0,0,0,0] (testJet 5) (testJet_vacuum 5) 1
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_106 (c : Coeff) (hc : Conserved (source c)) :
    (-2) * c 5 0 + 1 * c 7 1=0 := by
  have h := conservation_reading c hc ![1,0,0,0,0,0] (testJet 5) (testJet_vacuum 5) 2
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_107 (c : Coeff) (hc : Conserved (source c)) :
    (-2) * c 6 0 + 1 * c 8 1=0 := by
  have h := conservation_reading c hc ![1,0,0,0,0,0] (testJet 5) (testJet_vacuum 5) 3
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_108 (c : Coeff) (hc : Conserved (source c)) :
    (-1) * c 1 1 + 2 * c 2 6=0 := by
  have h := conservation_reading c hc ![0,1,0,0,0,0] (testJet 5) (testJet_vacuum 5) 0
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_109 (c : Coeff) (hc : Conserved (source c)) :
    (-1) * c 5 1 + 2 * c 7 6=0 := by
  have h := conservation_reading c hc ![0,1,0,0,0,0] (testJet 5) (testJet_vacuum 5) 2
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_110 (c : Coeff) (hc : Conserved (source c)) :
    (-1) * c 6 1 + 2 * c 8 6=0 := by
  have h := conservation_reading c hc ![0,1,0,0,0,0] (testJet 5) (testJet_vacuum 5) 3
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_111 (c : Coeff) (hc : Conserved (source c)) :
    (-1) * c 1 2 + 1 * c 2 7=0 := by
  have h := conservation_reading c hc ![0,0,1,0,0,0] (testJet 5) (testJet_vacuum 5) 0
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_112 (c : Coeff) (hc : Conserved (source c)) :
    (-1) * c 4 2 + 1 * c 5 7=0 := by
  have h := conservation_reading c hc ![0,0,1,0,0,0] (testJet 5) (testJet_vacuum 5) 1
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_113 (c : Coeff) (hc : Conserved (source c)) :
    (-1) * c 5 2 + 1 * c 7 7=0 := by
  have h := conservation_reading c hc ![0,0,1,0,0,0] (testJet 5) (testJet_vacuum 5) 2
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_114 (c : Coeff) (hc : Conserved (source c)) :
    (-1) * c 6 2 + 1 * c 8 7=0 := by
  have h := conservation_reading c hc ![0,0,1,0,0,0] (testJet 5) (testJet_vacuum 5) 3
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_115 (c : Coeff) (hc : Conserved (source c)) :
    (-1) * c 5 3 + 1 * c 7 8=0 := by
  have h := conservation_reading c hc ![0,0,0,1,0,0] (testJet 5) (testJet_vacuum 5) 2
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_116 (c : Coeff) (hc : Conserved (source c)) :
    (-1) * c 6 3 + 1 * c 8 8=0 := by
  have h := conservation_reading c hc ![0,0,0,1,0,0] (testJet 5) (testJet_vacuum 5) 3
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_117 (c : Coeff) (hc : Conserved (source c)) :
    (-1) * c 5 4 + 1 * c 7 9=0 := by
  have h := conservation_reading c hc ![0,0,0,0,1,0] (testJet 5) (testJet_vacuum 5) 2
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_118 (c : Coeff) (hc : Conserved (source c)) :
    (-1) * c 6 4 + 1 * c 8 9=0 := by
  have h := conservation_reading c hc ![0,0,0,0,1,0] (testJet 5) (testJet_vacuum 5) 3
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_119 (c : Coeff) (hc : Conserved (source c)) :
    (-1) * c 1 5 + 1 * c 2 10=0 := by
  have h := conservation_reading c hc ![0,0,0,0,0,1] (testJet 5) (testJet_vacuum 5) 0
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_120 (c : Coeff) (hc : Conserved (source c)) :
    (-1) * c 4 5 + 1 * c 5 10=0 := by
  have h := conservation_reading c hc ![0,0,0,0,0,1] (testJet 5) (testJet_vacuum 5) 1
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_121 (c : Coeff) (hc : Conserved (source c)) :
    (-1) * c 5 5 + 1 * c 7 10=0 := by
  have h := conservation_reading c hc ![0,0,0,0,0,1] (testJet 5) (testJet_vacuum 5) 2
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_122 (c : Coeff) (hc : Conserved (source c)) :
    (-1) * c 6 5 + 1 * c 8 10=0 := by
  have h := conservation_reading c hc ![0,0,0,0,0,1] (testJet 5) (testJet_vacuum 5) 3
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_123 (c : Coeff) (hc : Conserved (source c)) :
    1 * c 0 5 + 1 * c 2 2=0 := by
  have h := conservation_reading c hc ![1,0,0,0,0,0] (testJet 6) (testJet_vacuum 6) 0
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_124 (c : Coeff) (hc : Conserved (source c)) :
    1 * c 1 5 + 1 * c 5 2=0 := by
  have h := conservation_reading c hc ![1,0,0,0,0,0] (testJet 6) (testJet_vacuum 6) 1
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_125 (c : Coeff) (hc : Conserved (source c)) :
    1 * c 2 5 + 1 * c 7 2=0 := by
  have h := conservation_reading c hc ![1,0,0,0,0,0] (testJet 6) (testJet_vacuum 6) 2
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_126 (c : Coeff) (hc : Conserved (source c)) :
    1 * c 3 5 + 1 * c 8 2=0 := by
  have h := conservation_reading c hc ![1,0,0,0,0,0] (testJet 6) (testJet_vacuum 6) 3
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_127 (c : Coeff) (hc : Conserved (source c)) :
    1 * c 0 10 + 1 * c 2 7=0 := by
  have h := conservation_reading c hc ![0,1,0,0,0,0] (testJet 6) (testJet_vacuum 6) 0
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_128 (c : Coeff) (hc : Conserved (source c)) :
    1 * c 3 10 + 1 * c 8 7=0 := by
  have h := conservation_reading c hc ![0,1,0,0,0,0] (testJet 6) (testJet_vacuum 6) 3
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_129 (c : Coeff) (hc : Conserved (source c)) :
    1 * c 0 14 + 2 * c 2 11=0 := by
  have h := conservation_reading c hc ![0,0,1,0,0,0] (testJet 6) (testJet_vacuum 6) 0
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_130 (c : Coeff) (hc : Conserved (source c)) :
    1 * c 1 14 + 2 * c 5 11=0 := by
  have h := conservation_reading c hc ![0,0,1,0,0,0] (testJet 6) (testJet_vacuum 6) 1
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_131 (c : Coeff) (hc : Conserved (source c)) :
    1 * c 2 14 + 2 * c 7 11=0 := by
  have h := conservation_reading c hc ![0,0,1,0,0,0] (testJet 6) (testJet_vacuum 6) 2
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_132 (c : Coeff) (hc : Conserved (source c)) :
    1 * c 3 14 + 2 * c 8 11=0 := by
  have h := conservation_reading c hc ![0,0,1,0,0,0] (testJet 6) (testJet_vacuum 6) 3
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_133 (c : Coeff) (hc : Conserved (source c)) :
    1 * c 2 17 + 1 * c 7 12=0 := by
  have h := conservation_reading c hc ![0,0,0,1,0,0] (testJet 6) (testJet_vacuum 6) 2
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_134 (c : Coeff) (hc : Conserved (source c)) :
    1 * c 3 17 + 1 * c 8 12=0 := by
  have h := conservation_reading c hc ![0,0,0,1,0,0] (testJet 6) (testJet_vacuum 6) 3
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_135 (c : Coeff) (hc : Conserved (source c)) :
    1 * c 2 19 + 1 * c 7 13=0 := by
  have h := conservation_reading c hc ![0,0,0,0,1,0] (testJet 6) (testJet_vacuum 6) 2
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_136 (c : Coeff) (hc : Conserved (source c)) :
    1 * c 3 19 + 1 * c 8 13=0 := by
  have h := conservation_reading c hc ![0,0,0,0,1,0] (testJet 6) (testJet_vacuum 6) 3
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_137 (c : Coeff) (hc : Conserved (source c)) :
    2 * c 0 20 + 1 * c 2 14=0 := by
  have h := conservation_reading c hc ![0,0,0,0,0,1] (testJet 6) (testJet_vacuum 6) 0
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_138 (c : Coeff) (hc : Conserved (source c)) :
    2 * c 1 20 + 1 * c 5 14=0 := by
  have h := conservation_reading c hc ![0,0,0,0,0,1] (testJet 6) (testJet_vacuum 6) 1
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_139 (c : Coeff) (hc : Conserved (source c)) :
    2 * c 2 20 + 1 * c 7 14=0 := by
  have h := conservation_reading c hc ![0,0,0,0,0,1] (testJet 6) (testJet_vacuum 6) 2
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_140 (c : Coeff) (hc : Conserved (source c)) :
    2 * c 3 20 + 1 * c 8 14=0 := by
  have h := conservation_reading c hc ![0,0,0,0,0,1] (testJet 6) (testJet_vacuum 6) 3
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_141 (c : Coeff) (hc : Conserved (source c)) :
    2 * c 0 0 + 1 * c 2 3=0 := by
  have h := conservation_reading c hc ![1,0,0,0,0,0] (testJet 7) (testJet_vacuum 7) 0
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_142 (c : Coeff) (hc : Conserved (source c)) :
    2 * c 1 0 + 1 * c 5 3=0 := by
  have h := conservation_reading c hc ![1,0,0,0,0,0] (testJet 7) (testJet_vacuum 7) 1
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_143 (c : Coeff) (hc : Conserved (source c)) :
    2 * c 2 0 + 1 * c 7 3=0 := by
  have h := conservation_reading c hc ![1,0,0,0,0,0] (testJet 7) (testJet_vacuum 7) 2
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_144 (c : Coeff) (hc : Conserved (source c)) :
    2 * c 3 0 + 1 * c 8 3=0 := by
  have h := conservation_reading c hc ![1,0,0,0,0,0] (testJet 7) (testJet_vacuum 7) 3
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_145 (c : Coeff) (hc : Conserved (source c)) :
    1 * c 0 1 + 1 * c 2 8=0 := by
  have h := conservation_reading c hc ![0,1,0,0,0,0] (testJet 7) (testJet_vacuum 7) 0
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_146 (c : Coeff) (hc : Conserved (source c)) :
    1 * c 3 1 + 1 * c 8 8=0 := by
  have h := conservation_reading c hc ![0,1,0,0,0,0] (testJet 7) (testJet_vacuum 7) 3
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_147 (c : Coeff) (hc : Conserved (source c)) :
    1 * c 0 2 + 1 * c 2 12=0 := by
  have h := conservation_reading c hc ![0,0,1,0,0,0] (testJet 7) (testJet_vacuum 7) 0
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_148 (c : Coeff) (hc : Conserved (source c)) :
    1 * c 1 2 + 1 * c 5 12=0 := by
  have h := conservation_reading c hc ![0,0,1,0,0,0] (testJet 7) (testJet_vacuum 7) 1
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_149 (c : Coeff) (hc : Conserved (source c)) :
    1 * c 2 2 + 1 * c 7 12=0 := by
  have h := conservation_reading c hc ![0,0,1,0,0,0] (testJet 7) (testJet_vacuum 7) 2
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_150 (c : Coeff) (hc : Conserved (source c)) :
    1 * c 3 2 + 1 * c 8 12=0 := by
  have h := conservation_reading c hc ![0,0,1,0,0,0] (testJet 7) (testJet_vacuum 7) 3
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_151 (c : Coeff) (hc : Conserved (source c)) :
    1 * c 2 3 + 2 * c 7 15=0 := by
  have h := conservation_reading c hc ![0,0,0,1,0,0] (testJet 7) (testJet_vacuum 7) 2
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_152 (c : Coeff) (hc : Conserved (source c)) :
    1 * c 3 3 + 2 * c 8 15=0 := by
  have h := conservation_reading c hc ![0,0,0,1,0,0] (testJet 7) (testJet_vacuum 7) 3
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_153 (c : Coeff) (hc : Conserved (source c)) :
    1 * c 2 4 + 1 * c 7 16=0 := by
  have h := conservation_reading c hc ![0,0,0,0,1,0] (testJet 7) (testJet_vacuum 7) 2
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_154 (c : Coeff) (hc : Conserved (source c)) :
    1 * c 3 4 + 1 * c 8 16=0 := by
  have h := conservation_reading c hc ![0,0,0,0,1,0] (testJet 7) (testJet_vacuum 7) 3
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_155 (c : Coeff) (hc : Conserved (source c)) :
    1 * c 1 5 + 1 * c 5 17=0 := by
  have h := conservation_reading c hc ![0,0,0,0,0,1] (testJet 7) (testJet_vacuum 7) 1
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_156 (c : Coeff) (hc : Conserved (source c)) :
    1 * c 2 5 + 1 * c 7 17=0 := by
  have h := conservation_reading c hc ![0,0,0,0,0,1] (testJet 7) (testJet_vacuum 7) 2
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_157 (c : Coeff) (hc : Conserved (source c)) :
    1 * c 3 5 + 1 * c 8 17=0 := by
  have h := conservation_reading c hc ![0,0,0,0,0,1] (testJet 7) (testJet_vacuum 7) 3
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_158 (c : Coeff) (hc : Conserved (source c)) :
    1 * c 6 5 + 1 * c 8 4=0 := by
  have h := conservation_reading c hc ![1,0,0,0,0,0] (testJet 8) (testJet_vacuum 8) 3
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_159 (c : Coeff) (hc : Conserved (source c)) :
    1 * c 1 14 + 1 * c 2 13=0 := by
  have h := conservation_reading c hc ![0,0,1,0,0,0] (testJet 8) (testJet_vacuum 8) 0
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_160 (c : Coeff) (hc : Conserved (source c)) :
    1 * c 4 14 + 1 * c 5 13=0 := by
  have h := conservation_reading c hc ![0,0,1,0,0,0] (testJet 8) (testJet_vacuum 8) 1
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_161 (c : Coeff) (hc : Conserved (source c)) :
    1 * c 5 14 + 1 * c 7 13=0 := by
  have h := conservation_reading c hc ![0,0,1,0,0,0] (testJet 8) (testJet_vacuum 8) 2
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_162 (c : Coeff) (hc : Conserved (source c)) :
    1 * c 6 14 + 1 * c 8 13=0 := by
  have h := conservation_reading c hc ![0,0,1,0,0,0] (testJet 8) (testJet_vacuum 8) 3
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_163 (c : Coeff) (hc : Conserved (source c)) :
    1 * c 5 19 + 2 * c 7 18=0 := by
  have h := conservation_reading c hc ![0,0,0,0,1,0] (testJet 8) (testJet_vacuum 8) 2
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_164 (c : Coeff) (hc : Conserved (source c)) :
    1 * c 6 19 + 2 * c 8 18=0 := by
  have h := conservation_reading c hc ![0,0,0,0,1,0] (testJet 8) (testJet_vacuum 8) 3
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_165 (c : Coeff) (hc : Conserved (source c)) :
    2 * c 4 20 + 1 * c 5 19=0 := by
  have h := conservation_reading c hc ![0,0,0,0,0,1] (testJet 8) (testJet_vacuum 8) 1
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_166 (c : Coeff) (hc : Conserved (source c)) :
    2 * c 5 20 + 1 * c 7 19=0 := by
  have h := conservation_reading c hc ![0,0,0,0,0,1] (testJet 8) (testJet_vacuum 8) 2
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_167 (c : Coeff) (hc : Conserved (source c)) :
    2 * c 6 20 + 1 * c 8 19=0 := by
  have h := conservation_reading c hc ![0,0,0,0,0,1] (testJet 8) (testJet_vacuum 8) 3
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_168 (c : Coeff) (hc : Conserved (source c)) :
    (-2) * c 0 11 + 1 * c 2 14=0 := by
  have h := conservation_reading c hc ![0,0,1,0,0,0] (testJet 9) (testJet_vacuum 9) 0
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_169 (c : Coeff) (hc : Conserved (source c)) :
    (-2) * c 1 11 + 1 * c 5 14=0 := by
  have h := conservation_reading c hc ![0,0,1,0,0,0] (testJet 9) (testJet_vacuum 9) 1
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_170 (c : Coeff) (hc : Conserved (source c)) :
    (-2) * c 2 11 + 1 * c 7 14=0 := by
  have h := conservation_reading c hc ![0,0,1,0,0,0] (testJet 9) (testJet_vacuum 9) 2
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_171 (c : Coeff) (hc : Conserved (source c)) :
    (-2) * c 3 11 + 1 * c 8 14=0 := by
  have h := conservation_reading c hc ![0,0,1,0,0,0] (testJet 9) (testJet_vacuum 9) 3
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_172 (c : Coeff) (hc : Conserved (source c)) :
    (-1) * c 2 13 + 1 * c 7 19=0 := by
  have h := conservation_reading c hc ![0,0,0,0,1,0] (testJet 9) (testJet_vacuum 9) 2
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_173 (c : Coeff) (hc : Conserved (source c)) :
    (-1) * c 3 13 + 1 * c 8 19=0 := by
  have h := conservation_reading c hc ![0,0,0,0,1,0] (testJet 9) (testJet_vacuum 9) 3
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_174 (c : Coeff) (hc : Conserved (source c)) :
    (-1) * c 2 14 + 2 * c 7 20=0 := by
  have h := conservation_reading c hc ![0,0,0,0,0,1] (testJet 9) (testJet_vacuum 9) 2
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_175 (c : Coeff) (hc : Conserved (source c)) :
    (-1) * c 3 14 + 2 * c 8 20=0 := by
  have h := conservation_reading c hc ![0,0,0,0,0,1] (testJet 9) (testJet_vacuum 9) 3
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_176 (c : Coeff) (hc : Conserved (source c)) :
    1 * c 0 4 + 2 * c 3 0=0 := by
  have h := conservation_reading c hc ![1,0,0,0,0,0] (testJet 10) (testJet_vacuum 10) 0
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_177 (c : Coeff) (hc : Conserved (source c)) :
    1 * c 1 4 + 2 * c 6 0=0 := by
  have h := conservation_reading c hc ![1,0,0,0,0,0] (testJet 10) (testJet_vacuum 10) 1
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_178 (c : Coeff) (hc : Conserved (source c)) :
    1 * c 2 4 + 2 * c 8 0=0 := by
  have h := conservation_reading c hc ![1,0,0,0,0,0] (testJet 10) (testJet_vacuum 10) 2
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_179 (c : Coeff) (hc : Conserved (source c)) :
    1 * c 3 4 + 2 * c 9 0=0 := by
  have h := conservation_reading c hc ![1,0,0,0,0,0] (testJet 10) (testJet_vacuum 10) 3
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_180 (c : Coeff) (hc : Conserved (source c)) :
    1 * c 0 9 + 1 * c 3 1=0 := by
  have h := conservation_reading c hc ![0,1,0,0,0,0] (testJet 10) (testJet_vacuum 10) 0
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_181 (c : Coeff) (hc : Conserved (source c)) :
    1 * c 3 9 + 1 * c 9 1=0 := by
  have h := conservation_reading c hc ![0,1,0,0,0,0] (testJet 10) (testJet_vacuum 10) 3
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_182 (c : Coeff) (hc : Conserved (source c)) :
    1 * c 0 13 + 1 * c 3 2=0 := by
  have h := conservation_reading c hc ![0,0,1,0,0,0] (testJet 10) (testJet_vacuum 10) 0
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_183 (c : Coeff) (hc : Conserved (source c)) :
    1 * c 1 13 + 1 * c 6 2=0 := by
  have h := conservation_reading c hc ![0,0,1,0,0,0] (testJet 10) (testJet_vacuum 10) 1
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_184 (c : Coeff) (hc : Conserved (source c)) :
    1 * c 2 13 + 1 * c 8 2=0 := by
  have h := conservation_reading c hc ![0,0,1,0,0,0] (testJet 10) (testJet_vacuum 10) 2
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_185 (c : Coeff) (hc : Conserved (source c)) :
    1 * c 3 13 + 1 * c 9 2=0 := by
  have h := conservation_reading c hc ![0,0,1,0,0,0] (testJet 10) (testJet_vacuum 10) 3
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_186 (c : Coeff) (hc : Conserved (source c)) :
    1 * c 3 16 + 1 * c 9 3=0 := by
  have h := conservation_reading c hc ![0,0,0,1,0,0] (testJet 10) (testJet_vacuum 10) 3
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_187 (c : Coeff) (hc : Conserved (source c)) :
    2 * c 2 18 + 1 * c 8 4=0 := by
  have h := conservation_reading c hc ![0,0,0,0,1,0] (testJet 10) (testJet_vacuum 10) 2
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_188 (c : Coeff) (hc : Conserved (source c)) :
    2 * c 3 18 + 1 * c 9 4=0 := by
  have h := conservation_reading c hc ![0,0,0,0,1,0] (testJet 10) (testJet_vacuum 10) 3
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_189 (c : Coeff) (hc : Conserved (source c)) :
    1 * c 3 19 + 1 * c 9 5=0 := by
  have h := conservation_reading c hc ![0,0,0,0,0,1] (testJet 10) (testJet_vacuum 10) 3
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_190 (c : Coeff) (hc : Conserved (source c)) :
    1 * c 3 10 + 2 * c 9 6=0 := by
  have h := conservation_reading c hc ![0,1,0,0,0,0] (testJet 11) (testJet_vacuum 11) 3
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_191 (c : Coeff) (hc : Conserved (source c)) :
    1 * c 3 14 + 1 * c 9 7=0 := by
  have h := conservation_reading c hc ![0,0,1,0,0,0] (testJet 11) (testJet_vacuum 11) 3
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_192 (c : Coeff) (hc : Conserved (source c)) :
    1 * c 3 17 + 1 * c 9 8=0 := by
  have h := conservation_reading c hc ![0,0,0,1,0,0] (testJet 11) (testJet_vacuum 11) 3
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_193 (c : Coeff) (hc : Conserved (source c)) :
    1 * c 3 19 + 1 * c 9 9=0 := by
  have h := conservation_reading c hc ![0,0,0,0,1,0] (testJet 11) (testJet_vacuum 11) 3
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_194 (c : Coeff) (hc : Conserved (source c)) :
    2 * c 3 20 + 1 * c 9 10=0 := by
  have h := conservation_reading c hc ![0,0,0,0,0,1] (testJet 11) (testJet_vacuum 11) 3
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_195 (c : Coeff) (hc : Conserved (source c)) :
    (-2) * c 4 0 + 1 * c 6 2=0 := by
  have h := conservation_reading c hc ![1,0,0,0,0,0] (testJet 12) (testJet_vacuum 12) 1
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_196 (c : Coeff) (hc : Conserved (source c)) :
    (-2) * c 6 0 + 1 * c 9 2=0 := by
  have h := conservation_reading c hc ![1,0,0,0,0,0] (testJet 12) (testJet_vacuum 12) 3
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_197 (c : Coeff) (hc : Conserved (source c)) :
    (-1) * c 6 1 + 1 * c 9 7=0 := by
  have h := conservation_reading c hc ![0,1,0,0,0,0] (testJet 12) (testJet_vacuum 12) 3
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_198 (c : Coeff) (hc : Conserved (source c)) :
    (-1) * c 1 2 + 2 * c 3 11=0 := by
  have h := conservation_reading c hc ![0,0,1,0,0,0] (testJet 12) (testJet_vacuum 12) 0
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_199 (c : Coeff) (hc : Conserved (source c)) :
    (-1) * c 6 2 + 2 * c 9 11=0 := by
  have h := conservation_reading c hc ![0,0,1,0,0,0] (testJet 12) (testJet_vacuum 12) 3
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_200 (c : Coeff) (hc : Conserved (source c)) :
    (-1) * c 6 3 + 1 * c 9 12=0 := by
  have h := conservation_reading c hc ![0,0,0,1,0,0] (testJet 12) (testJet_vacuum 12) 3
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_201 (c : Coeff) (hc : Conserved (source c)) :
    (-1) * c 6 4 + 1 * c 9 13=0 := by
  have h := conservation_reading c hc ![0,0,0,0,1,0] (testJet 12) (testJet_vacuum 12) 3
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_202 (c : Coeff) (hc : Conserved (source c)) :
    (-1) * c 6 5 + 1 * c 9 14=0 := by
  have h := conservation_reading c hc ![0,0,0,0,0,1] (testJet 12) (testJet_vacuum 12) 3
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_203 (c : Coeff) (hc : Conserved (source c)) :
    1 * c 6 17 + 2 * c 9 15=0 := by
  have h := conservation_reading c hc ![0,0,0,1,0,0] (testJet 13) (testJet_vacuum 13) 3
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_204 (c : Coeff) (hc : Conserved (source c)) :
    1 * c 6 19 + 1 * c 9 16=0 := by
  have h := conservation_reading c hc ![0,0,0,0,1,0] (testJet 13) (testJet_vacuum 13) 3
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_205 (c : Coeff) (hc : Conserved (source c)) :
    2 * c 6 20 + 1 * c 9 17=0 := by
  have h := conservation_reading c hc ![0,0,0,0,0,1] (testJet 13) (testJet_vacuum 13) 3
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_206 (c : Coeff) (hc : Conserved (source c)) :
    1 * c 3 4 + 2 * c 9 18=0 := by
  have h := conservation_reading c hc ![0,0,0,0,1,0] (testJet 14) (testJet_vacuum 14) 3
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_207 (c : Coeff) (hc : Conserved (source c)) :
    1 * c 3 5 + 1 * c 9 19=0 := by
  have h := conservation_reading c hc ![0,0,0,0,0,1] (testJet 14) (testJet_vacuum 14) 3
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

private theorem constraint_208 (c : Coeff) (hc : Conserved (source c)) :
    1 * c 3 10 + 2 * c 9 20=0 := by
  have h := conservation_reading c hc ![0,0,0,0,0,1] (testJet 15) (testJet_vacuum 15) 3
  norm_num [quadraticDivergence,variation,dpoly,testJet,tensorIndex,monomialPair,
    Fin.sum_univ_succ] at h
  try dsimp at h
  norm_num at h
  linarith only [h]

theorem constraints_from_conservation (c : Coeff) (hc : Conserved (source c)) :
    conservationConstraints c=0 := by
  funext n
  fin_cases n
  · exact constraint_000 c hc
  · exact constraint_001 c hc
  · exact constraint_002 c hc
  · exact constraint_003 c hc
  · exact constraint_004 c hc
  · exact constraint_005 c hc
  · exact constraint_006 c hc
  · exact constraint_007 c hc
  · exact constraint_008 c hc
  · exact constraint_009 c hc
  · exact constraint_010 c hc
  · exact constraint_011 c hc
  · exact constraint_012 c hc
  · exact constraint_013 c hc
  · exact constraint_014 c hc
  · exact constraint_015 c hc
  · exact constraint_016 c hc
  · exact constraint_017 c hc
  · exact constraint_018 c hc
  · exact constraint_019 c hc
  · exact constraint_020 c hc
  · exact constraint_021 c hc
  · exact constraint_022 c hc
  · exact constraint_023 c hc
  · exact constraint_024 c hc
  · exact constraint_025 c hc
  · exact constraint_026 c hc
  · exact constraint_027 c hc
  · exact constraint_028 c hc
  · exact constraint_029 c hc
  · exact constraint_030 c hc
  · exact constraint_031 c hc
  · exact constraint_032 c hc
  · exact constraint_033 c hc
  · exact constraint_034 c hc
  · exact constraint_035 c hc
  · exact constraint_036 c hc
  · exact constraint_037 c hc
  · exact constraint_038 c hc
  · exact constraint_039 c hc
  · exact constraint_040 c hc
  · exact constraint_041 c hc
  · exact constraint_042 c hc
  · exact constraint_043 c hc
  · exact constraint_044 c hc
  · exact constraint_045 c hc
  · exact constraint_046 c hc
  · exact constraint_047 c hc
  · exact constraint_048 c hc
  · exact constraint_049 c hc
  · exact constraint_050 c hc
  · exact constraint_051 c hc
  · exact constraint_052 c hc
  · exact constraint_053 c hc
  · exact constraint_054 c hc
  · exact constraint_055 c hc
  · exact constraint_056 c hc
  · exact constraint_057 c hc
  · exact constraint_058 c hc
  · exact constraint_059 c hc
  · exact constraint_060 c hc
  · exact constraint_061 c hc
  · exact constraint_062 c hc
  · exact constraint_063 c hc
  · exact constraint_064 c hc
  · exact constraint_065 c hc
  · exact constraint_066 c hc
  · exact constraint_067 c hc
  · exact constraint_068 c hc
  · exact constraint_069 c hc
  · exact constraint_070 c hc
  · exact constraint_071 c hc
  · exact constraint_072 c hc
  · exact constraint_073 c hc
  · exact constraint_074 c hc
  · exact constraint_075 c hc
  · exact constraint_076 c hc
  · exact constraint_077 c hc
  · exact constraint_078 c hc
  · exact constraint_079 c hc
  · exact constraint_080 c hc
  · exact constraint_081 c hc
  · exact constraint_082 c hc
  · exact constraint_083 c hc
  · exact constraint_084 c hc
  · exact constraint_085 c hc
  · exact constraint_086 c hc
  · exact constraint_087 c hc
  · exact constraint_088 c hc
  · exact constraint_089 c hc
  · exact constraint_090 c hc
  · exact constraint_091 c hc
  · exact constraint_092 c hc
  · exact constraint_093 c hc
  · exact constraint_094 c hc
  · exact constraint_095 c hc
  · exact constraint_096 c hc
  · exact constraint_097 c hc
  · exact constraint_098 c hc
  · exact constraint_099 c hc
  · exact constraint_100 c hc
  · exact constraint_101 c hc
  · exact constraint_102 c hc
  · exact constraint_103 c hc
  · exact constraint_104 c hc
  · exact constraint_105 c hc
  · exact constraint_106 c hc
  · exact constraint_107 c hc
  · exact constraint_108 c hc
  · exact constraint_109 c hc
  · exact constraint_110 c hc
  · exact constraint_111 c hc
  · exact constraint_112 c hc
  · exact constraint_113 c hc
  · exact constraint_114 c hc
  · exact constraint_115 c hc
  · exact constraint_116 c hc
  · exact constraint_117 c hc
  · exact constraint_118 c hc
  · exact constraint_119 c hc
  · exact constraint_120 c hc
  · exact constraint_121 c hc
  · exact constraint_122 c hc
  · exact constraint_123 c hc
  · exact constraint_124 c hc
  · exact constraint_125 c hc
  · exact constraint_126 c hc
  · exact constraint_127 c hc
  · exact constraint_128 c hc
  · exact constraint_129 c hc
  · exact constraint_130 c hc
  · exact constraint_131 c hc
  · exact constraint_132 c hc
  · exact constraint_133 c hc
  · exact constraint_134 c hc
  · exact constraint_135 c hc
  · exact constraint_136 c hc
  · exact constraint_137 c hc
  · exact constraint_138 c hc
  · exact constraint_139 c hc
  · exact constraint_140 c hc
  · exact constraint_141 c hc
  · exact constraint_142 c hc
  · exact constraint_143 c hc
  · exact constraint_144 c hc
  · exact constraint_145 c hc
  · exact constraint_146 c hc
  · exact constraint_147 c hc
  · exact constraint_148 c hc
  · exact constraint_149 c hc
  · exact constraint_150 c hc
  · exact constraint_151 c hc
  · exact constraint_152 c hc
  · exact constraint_153 c hc
  · exact constraint_154 c hc
  · exact constraint_155 c hc
  · exact constraint_156 c hc
  · exact constraint_157 c hc
  · exact constraint_158 c hc
  · exact constraint_159 c hc
  · exact constraint_160 c hc
  · exact constraint_161 c hc
  · exact constraint_162 c hc
  · exact constraint_163 c hc
  · exact constraint_164 c hc
  · exact constraint_165 c hc
  · exact constraint_166 c hc
  · exact constraint_167 c hc
  · exact constraint_168 c hc
  · exact constraint_169 c hc
  · exact constraint_170 c hc
  · exact constraint_171 c hc
  · exact constraint_172 c hc
  · exact constraint_173 c hc
  · exact constraint_174 c hc
  · exact constraint_175 c hc
  · exact constraint_176 c hc
  · exact constraint_177 c hc
  · exact constraint_178 c hc
  · exact constraint_179 c hc
  · exact constraint_180 c hc
  · exact constraint_181 c hc
  · exact constraint_182 c hc
  · exact constraint_183 c hc
  · exact constraint_184 c hc
  · exact constraint_185 c hc
  · exact constraint_186 c hc
  · exact constraint_187 c hc
  · exact constraint_188 c hc
  · exact constraint_189 c hc
  · exact constraint_190 c hc
  · exact constraint_191 c hc
  · exact constraint_192 c hc
  · exact constraint_193 c hc
  · exact constraint_194 c hc
  · exact constraint_195 c hc
  · exact constraint_196 c hc
  · exact constraint_197 c hc
  · exact constraint_198 c hc
  · exact constraint_199 c hc
  · exact constraint_200 c hc
  · exact constraint_201 c hc
  · exact constraint_202 c hc
  · exact constraint_203 c hc
  · exact constraint_204 c hc
  · exact constraint_205 c hc
  · exact constraint_206 c hc
  · exact constraint_207 c hc
  · exact constraint_208 c hc

#print axioms constraints_from_conservation
end
end PDTConservedSource
