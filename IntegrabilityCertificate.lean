module
public import LinearSourceData

@[expose] public section
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
namespace PDTSmoothSource
noncomputable section
open PDTStressTensor PDTUnrestrictedSourceKernel PDTQuadraticSource PDTConservedSource PDTPolynomialSource
open scoped Matrix

def Compatible (M : Matrix (Fin 6) (Fin 6) ℝ) : Prop := ∀ t a b,
  crossCoefficients (fun j => M j b) t a=crossCoefficients (fun j => M j a) t b

private theorem row_0 (M : Matrix (Fin 6) (Fin 6) ℝ) (h : Compatible M) : (1)*M 0 1 + (-1)*M 1 0=0 := by
  have hh := h 0 0 1
  norm_num [crossCoefficients] at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]

private theorem row_1 (M : Matrix (Fin 6) (Fin 6) ℝ) (h : Compatible M) : (1)*M 0 2 + (1)*M 2 0=0 := by
  have hh := h 0 0 2
  norm_num [crossCoefficients] at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]

private theorem row_2 (M : Matrix (Fin 6) (Fin 6) ℝ) (h : Compatible M) : (1)*M 0 3 + (1)*M 3 0=0 := by
  have hh := h 0 0 3
  norm_num [crossCoefficients] at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]

private theorem row_3 (M : Matrix (Fin 6) (Fin 6) ℝ) (h : Compatible M) : (1)*M 0 4 + (-1)*M 4 0=0 := by
  have hh := h 0 0 4
  norm_num [crossCoefficients] at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]

private theorem row_4 (M : Matrix (Fin 6) (Fin 6) ℝ) (h : Compatible M) : (1)*M 0 5 + (-1)*M 5 0=0 := by
  have hh := h 0 0 5
  norm_num [crossCoefficients] at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]

private theorem row_5 (M : Matrix (Fin 6) (Fin 6) ℝ) (h : Compatible M) : (1)*M 1 2 + (1)*M 2 1=0 := by
  have hh := h 0 1 2
  norm_num [crossCoefficients] at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]

private theorem row_6 (M : Matrix (Fin 6) (Fin 6) ℝ) (h : Compatible M) : (1)*M 1 3 + (1)*M 3 1=0 := by
  have hh := h 0 1 3
  norm_num [crossCoefficients] at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]

private theorem row_7 (M : Matrix (Fin 6) (Fin 6) ℝ) (h : Compatible M) : (1)*M 1 4 + (-1)*M 4 1=0 := by
  have hh := h 0 1 4
  norm_num [crossCoefficients] at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]

private theorem row_8 (M : Matrix (Fin 6) (Fin 6) ℝ) (h : Compatible M) : (1)*M 1 5 + (-1)*M 5 1=0 := by
  have hh := h 0 1 5
  norm_num [crossCoefficients] at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]

private theorem row_9 (M : Matrix (Fin 6) (Fin 6) ℝ) (h : Compatible M) : (-1)*M 2 3 + (1)*M 3 2=0 := by
  have hh := h 0 2 3
  norm_num [crossCoefficients] at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]

private theorem row_10 (M : Matrix (Fin 6) (Fin 6) ℝ) (h : Compatible M) : (-1)*M 2 4 + (-1)*M 4 2=0 := by
  have hh := h 0 2 4
  norm_num [crossCoefficients] at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]

private theorem row_11 (M : Matrix (Fin 6) (Fin 6) ℝ) (h : Compatible M) : (-1)*M 2 5 + (-1)*M 5 2=0 := by
  have hh := h 0 2 5
  norm_num [crossCoefficients] at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]

private theorem row_12 (M : Matrix (Fin 6) (Fin 6) ℝ) (h : Compatible M) : (-1)*M 3 4 + (-1)*M 4 3=0 := by
  have hh := h 0 3 4
  norm_num [crossCoefficients] at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]

private theorem row_13 (M : Matrix (Fin 6) (Fin 6) ℝ) (h : Compatible M) : (-1)*M 3 5 + (-1)*M 5 3=0 := by
  have hh := h 0 3 5
  norm_num [crossCoefficients] at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]

private theorem row_14 (M : Matrix (Fin 6) (Fin 6) ℝ) (h : Compatible M) : (1)*M 4 5 + (-1)*M 5 4=0 := by
  have hh := h 0 4 5
  norm_num [crossCoefficients] at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]

private theorem row_15 (M : Matrix (Fin 6) (Fin 6) ℝ) (h : Compatible M) : (-1)*M 3 0=0 := by
  have hh := h 1 0 1
  norm_num [crossCoefficients] at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]

private theorem row_16 (M : Matrix (Fin 6) (Fin 6) ℝ) (h : Compatible M) : (1)*M 4 0=0 := by
  have hh := h 1 0 2
  norm_num [crossCoefficients] at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]

private theorem row_17 (M : Matrix (Fin 6) (Fin 6) ℝ) (h : Compatible M) : (-1)*M 1 0=0 := by
  have hh := h 1 0 3
  norm_num [crossCoefficients] at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]

private theorem row_18 (M : Matrix (Fin 6) (Fin 6) ℝ) (h : Compatible M) : (1)*M 2 0=0 := by
  have hh := h 1 0 4
  norm_num [crossCoefficients] at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]

private theorem row_19 (M : Matrix (Fin 6) (Fin 6) ℝ) (h : Compatible M) : (1)*M 3 2 + (1)*M 4 1=0 := by
  have hh := h 1 1 2
  norm_num [crossCoefficients] at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]

private theorem row_20 (M : Matrix (Fin 6) (Fin 6) ℝ) (h : Compatible M) : (-1)*M 1 1 + (1)*M 3 3=0 := by
  have hh := h 1 1 3
  norm_num [crossCoefficients] at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]

private theorem row_21 (M : Matrix (Fin 6) (Fin 6) ℝ) (h : Compatible M) : (1)*M 2 1 + (1)*M 3 4=0 := by
  have hh := h 1 1 4
  norm_num [crossCoefficients] at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]

private theorem row_22 (M : Matrix (Fin 6) (Fin 6) ℝ) (h : Compatible M) : (1)*M 3 5=0 := by
  have hh := h 1 1 5
  norm_num [crossCoefficients] at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]

private theorem row_23 (M : Matrix (Fin 6) (Fin 6) ℝ) (h : Compatible M) : (1)*M 2 2 + (-1)*M 4 4=0 := by
  have hh := h 1 2 4
  norm_num [crossCoefficients] at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]

private theorem row_24 (M : Matrix (Fin 6) (Fin 6) ℝ) (h : Compatible M) : (-1)*M 4 5=0 := by
  have hh := h 1 2 5
  norm_num [crossCoefficients] at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]

private theorem row_25 (M : Matrix (Fin 6) (Fin 6) ℝ) (h : Compatible M) : (1)*M 1 5=0 := by
  have hh := h 1 3 5
  norm_num [crossCoefficients] at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]

private theorem row_26 (M : Matrix (Fin 6) (Fin 6) ℝ) (h : Compatible M) : (-1)*M 2 5=0 := by
  have hh := h 1 4 5
  norm_num [crossCoefficients] at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]

private theorem row_27 (M : Matrix (Fin 6) (Fin 6) ℝ) (h : Compatible M) : (-1)*M 3 1=0 := by
  have hh := h 2 0 1
  norm_num [crossCoefficients] at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]

private theorem row_28 (M : Matrix (Fin 6) (Fin 6) ℝ) (h : Compatible M) : (-1)*M 3 2 + (1)*M 5 0=0 := by
  have hh := h 2 0 2
  norm_num [crossCoefficients] at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]

private theorem row_29 (M : Matrix (Fin 6) (Fin 6) ℝ) (h : Compatible M) : (1)*M 0 0 + (-1)*M 3 3=0 := by
  have hh := h 2 0 3
  norm_num [crossCoefficients] at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]

private theorem row_30 (M : Matrix (Fin 6) (Fin 6) ℝ) (h : Compatible M) : (-1)*M 3 4=0 := by
  have hh := h 2 0 4
  norm_num [crossCoefficients] at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]

private theorem row_31 (M : Matrix (Fin 6) (Fin 6) ℝ) (h : Compatible M) : (1)*M 2 2 + (-1)*M 5 5=0 := by
  have hh := h 2 2 5
  norm_num [crossCoefficients] at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]

private theorem row_32 (M : Matrix (Fin 6) (Fin 6) ℝ) (h : Compatible M) : (1)*M 2 4=0 := by
  have hh := h 2 4 5
  norm_num [crossCoefficients] at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]

private theorem row_33 (M : Matrix (Fin 6) (Fin 6) ℝ) (h : Compatible M) : (-1)*M 4 1 + (1)*M 5 0=0 := by
  have hh := h 3 0 1
  norm_num [crossCoefficients] at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]

private theorem row_34 (M : Matrix (Fin 6) (Fin 6) ℝ) (h : Compatible M) : (1)*M 0 0 + (-1)*M 4 4=0 := by
  have hh := h 3 0 4
  norm_num [crossCoefficients] at hh
  try dsimp at hh
  norm_num at hh
  linarith only [hh]

/-- Mixed-partial compatibility forces exactly a scalar derivative matrix. -/
theorem compatible_scalar (M : Matrix (Fin 6) (Fin 6) ℝ) (h : Compatible M) :
    ∀ j k, M j k=if j=k then M 0 0 else 0 := by
  have h0 := row_0 M h
  have h1 := row_1 M h
  have h2 := row_2 M h
  have h3 := row_3 M h
  have h4 := row_4 M h
  have h5 := row_5 M h
  have h6 := row_6 M h
  have h7 := row_7 M h
  have h8 := row_8 M h
  have h9 := row_9 M h
  have h10 := row_10 M h
  have h11 := row_11 M h
  have h12 := row_12 M h
  have h13 := row_13 M h
  have h14 := row_14 M h
  have h15 := row_15 M h
  have h16 := row_16 M h
  have h17 := row_17 M h
  have h18 := row_18 M h
  have h19 := row_19 M h
  have h20 := row_20 M h
  have h21 := row_21 M h
  have h22 := row_22 M h
  have h23 := row_23 M h
  have h24 := row_24 M h
  have h25 := row_25 M h
  have h26 := row_26 M h
  have h27 := row_27 M h
  have h28 := row_28 M h
  have h29 := row_29 M h
  have h30 := row_30 M h
  have h31 := row_31 M h
  have h32 := row_32 M h
  have h33 := row_33 M h
  have h34 := row_34 M h
  intro j k
  fin_cases j <;> fin_cases k
  · change M 0 0=M 0 0
    rfl
  · change M 0 1=0
    linear_combination (1 : ℝ)*h0 + (-1 : ℝ)*h17
  · change M 0 2=0
    linear_combination (1 : ℝ)*h1 + (-1 : ℝ)*h18
  · change M 0 3=0
    linear_combination (1 : ℝ)*h2 + (1 : ℝ)*h15
  · change M 0 4=0
    linear_combination (1 : ℝ)*h3 + (1 : ℝ)*h16
  · change M 0 5=0
    linear_combination (1 : ℝ)*h4 + (1/2 : ℝ)*h19 + (1/2 : ℝ)*h28 + (1/2 : ℝ)*h33
  · change M 1 0=0
    linear_combination (-1 : ℝ)*h17
  · change M 1 1=M 0 0
    linear_combination (-1 : ℝ)*h20 + (-1 : ℝ)*h29
  · change M 1 2=0
    linear_combination (1 : ℝ)*h5 + (-1 : ℝ)*h21 + (-1 : ℝ)*h30
  · change M 1 3=0
    linear_combination (1 : ℝ)*h6 + (1 : ℝ)*h27
  · change M 1 4=0
    linear_combination (1 : ℝ)*h7 + (1/2 : ℝ)*h19 + (1/2 : ℝ)*h28 + (-1/2 : ℝ)*h33
  · change M 1 5=0
    linear_combination (1 : ℝ)*h25
  · change M 2 0=0
    linear_combination (1 : ℝ)*h18
  · change M 2 1=0
    linear_combination (1 : ℝ)*h21 + (1 : ℝ)*h30
  · change M 2 2=M 0 0
    linear_combination (1 : ℝ)*h23 + (-1 : ℝ)*h34
  · change M 2 3=0
    linear_combination (-1 : ℝ)*h9 + (1/2 : ℝ)*h19 + (-1/2 : ℝ)*h28 + (1/2 : ℝ)*h33
  · change M 2 4=0
    linear_combination (1 : ℝ)*h32
  · change M 2 5=0
    linear_combination (-1 : ℝ)*h26
  · change M 3 0=0
    linear_combination (-1 : ℝ)*h15
  · change M 3 1=0
    linear_combination (-1 : ℝ)*h27
  · change M 3 2=0
    linear_combination (1/2 : ℝ)*h19 + (-1/2 : ℝ)*h28 + (1/2 : ℝ)*h33
  · change M 3 3=M 0 0
    linear_combination (-1 : ℝ)*h29
  · change M 3 4=0
    linear_combination (-1 : ℝ)*h30
  · change M 3 5=0
    linear_combination (1 : ℝ)*h22
  · change M 4 0=0
    linear_combination (1 : ℝ)*h16
  · change M 4 1=0
    linear_combination (1/2 : ℝ)*h19 + (1/2 : ℝ)*h28 + (-1/2 : ℝ)*h33
  · change M 4 2=0
    linear_combination (-1 : ℝ)*h10 + (-1 : ℝ)*h32
  · change M 4 3=0
    linear_combination (-1 : ℝ)*h12 + (1 : ℝ)*h30
  · change M 4 4=M 0 0
    linear_combination (-1 : ℝ)*h34
  · change M 4 5=0
    linear_combination (-1 : ℝ)*h24
  · change M 5 0=0
    linear_combination (1/2 : ℝ)*h19 + (1/2 : ℝ)*h28 + (1/2 : ℝ)*h33
  · change M 5 1=0
    linear_combination (-1 : ℝ)*h8 + (1 : ℝ)*h25
  · change M 5 2=0
    linear_combination (-1 : ℝ)*h11 + (1 : ℝ)*h26
  · change M 5 3=0
    linear_combination (-1 : ℝ)*h13 + (-1 : ℝ)*h22
  · change M 5 4=0
    linear_combination (-1 : ℝ)*h14 + (-1 : ℝ)*h24
  · change M 5 5=M 0 0
    linear_combination (1 : ℝ)*h23 + (-1 : ℝ)*h31 + (-1 : ℝ)*h34

#print axioms compatible_scalar
end
end PDTSmoothSource
