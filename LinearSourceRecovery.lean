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

theorem linear_recovery (l : LinearCoeff) (h : linearConstraints l=0) :
    l=crossCoefficients (background l) := by
  have h0 : (1)*l 0 3 + (1)*l 1 1=0 := congrFun h 0
  have h1 : (1)*l 1 3 + (1)*l 4 1=0 := congrFun h 1
  have h2 : (1)*l 2 3 + (1)*l 5 1=0 := congrFun h 2
  have h3 : (1)*l 3 3 + (1)*l 6 1=0 := congrFun h 3
  have h4 : (1)*l 0 4 + (1)*l 1 2=0 := congrFun h 4
  have h5 : (1)*l 1 4 + (1)*l 4 2=0 := congrFun h 5
  have h6 : (1)*l 2 4 + (1)*l 5 2=0 := congrFun h 6
  have h7 : (1)*l 3 4 + (1)*l 6 2=0 := congrFun h 7
  have h8 : (-1)*l 0 1 + (1)*l 1 3=0 := congrFun h 8
  have h9 : (-1)*l 1 1 + (1)*l 4 3=0 := congrFun h 9
  have h10 : (-1)*l 2 1 + (1)*l 5 3=0 := congrFun h 10
  have h11 : (-1)*l 3 1 + (1)*l 6 3=0 := congrFun h 11
  have h12 : (-1)*l 0 2 + (1)*l 1 4=0 := congrFun h 12
  have h13 : (-1)*l 1 2 + (1)*l 4 4=0 := congrFun h 13
  have h14 : (-1)*l 2 2 + (1)*l 5 4=0 := congrFun h 14
  have h15 : (-1)*l 3 2 + (1)*l 6 4=0 := congrFun h 15
  have h16 : (-1)*l 0 3 + (1)*l 2 0=0 := congrFun h 16
  have h17 : (-1)*l 1 3 + (1)*l 5 0=0 := congrFun h 17
  have h18 : (-1)*l 2 3 + (1)*l 7 0=0 := congrFun h 18
  have h19 : (-1)*l 3 3 + (1)*l 8 0=0 := congrFun h 19
  have h20 : (-1)*l 1 0 + (1)*l 2 1=0 := congrFun h 20
  have h21 : (-1)*l 4 0 + (1)*l 5 1=0 := congrFun h 21
  have h22 : (-1)*l 5 0 + (1)*l 7 1=0 := congrFun h 22
  have h23 : (-1)*l 6 0 + (1)*l 8 1=0 := congrFun h 23
  have h24 : (1)*l 0 5 + (1)*l 2 2=0 := congrFun h 24
  have h25 : (1)*l 1 5 + (1)*l 5 2=0 := congrFun h 25
  have h26 : (1)*l 2 5 + (1)*l 7 2=0 := congrFun h 26
  have h27 : (1)*l 3 5 + (1)*l 8 2=0 := congrFun h 27
  have h28 : (1)*l 0 0 + (1)*l 2 3=0 := congrFun h 28
  have h29 : (1)*l 1 0 + (1)*l 5 3=0 := congrFun h 29
  have h30 : (1)*l 2 0 + (1)*l 7 3=0 := congrFun h 30
  have h31 : (1)*l 3 0 + (1)*l 8 3=0 := congrFun h 31
  have h32 : (1)*l 1 5 + (1)*l 2 4=0 := congrFun h 32
  have h33 : (1)*l 4 5 + (1)*l 5 4=0 := congrFun h 33
  have h34 : (1)*l 5 5 + (1)*l 7 4=0 := congrFun h 34
  have h35 : (1)*l 6 5 + (1)*l 8 4=0 := congrFun h 35
  have h36 : (-1)*l 0 2 + (1)*l 2 5=0 := congrFun h 36
  have h37 : (-1)*l 1 2 + (1)*l 5 5=0 := congrFun h 37
  have h38 : (-1)*l 2 2 + (1)*l 7 5=0 := congrFun h 38
  have h39 : (-1)*l 3 2 + (1)*l 8 5=0 := congrFun h 39
  have h40 : (1)*l 0 4 + (1)*l 3 0=0 := congrFun h 40
  have h41 : (1)*l 1 4 + (1)*l 6 0=0 := congrFun h 41
  have h42 : (1)*l 2 4 + (1)*l 8 0=0 := congrFun h 42
  have h43 : (1)*l 3 4 + (1)*l 9 0=0 := congrFun h 43
  have h44 : (1)*l 0 5 + (1)*l 3 1=0 := congrFun h 44
  have h45 : (1)*l 3 5 + (1)*l 9 1=0 := congrFun h 45
  have h46 : (-1)*l 1 0 + (1)*l 3 2=0 := congrFun h 46
  have h47 : (-1)*l 4 0 + (1)*l 6 2=0 := congrFun h 47
  have h48 : (-1)*l 5 0 + (1)*l 8 2=0 := congrFun h 48
  have h49 : (-1)*l 6 0 + (1)*l 9 2=0 := congrFun h 49
  have h50 : (1)*l 6 5 + (1)*l 9 3=0 := congrFun h 50
  have h51 : (1)*l 2 0 + (1)*l 8 4=0 := congrFun h 51
  have h52 : (1)*l 3 0 + (1)*l 9 4=0 := congrFun h 52
  have h53 : (1)*l 3 1 + (1)*l 9 5=0 := congrFun h 53
  ext t a
  fin_cases t <;> fin_cases a
  · change l 0 0 = (1)*(l 0 0)
    ring
  · change l 0 1 = (1)*(l 0 1)
    ring
  · change l 0 2 = (-1)*(-l 0 2)
    ring
  · change l 0 3 = (-1)*(-l 0 3)
    ring
  · change l 0 4 = (1)*(l 0 4)
    ring
  · change l 0 5 = (1)*(l 0 5)
    ring
  · change l 1 0 = 0
    linear_combination (-1/2 : ℝ)*h10 + (-1/2 : ℝ)*h20 + (1/2 : ℝ)*h29
  · change l 1 1 = (1)*(-l 0 3)
    linear_combination (1 : ℝ)*h0
  · change l 1 2 = (-1)*(l 0 4)
    linear_combination (1 : ℝ)*h4
  · change l 1 3 = (1)*(l 0 1)
    linear_combination (1 : ℝ)*h8
  · change l 1 4 = (-1)*(-l 0 2)
    linear_combination (1 : ℝ)*h12
  · change l 1 5 = 0
    linear_combination (-1/2 : ℝ)*h6 + (1/2 : ℝ)*h25 + (1/2 : ℝ)*h32
  · change l 2 0 = (-1)*(-l 0 3)
    linear_combination (1 : ℝ)*h16
  · change l 2 1 = 0
    linear_combination (-1/2 : ℝ)*h10 + (1/2 : ℝ)*h20 + (1/2 : ℝ)*h29
  · change l 2 2 = (-1)*(l 0 5)
    linear_combination (1 : ℝ)*h24
  · change l 2 3 = (-1)*(l 0 0)
    linear_combination (1 : ℝ)*h28
  · change l 2 4 = 0
    linear_combination (1/2 : ℝ)*h6 + (-1/2 : ℝ)*h25 + (1/2 : ℝ)*h32
  · change l 2 5 = (-1)*(-l 0 2)
    linear_combination (1 : ℝ)*h36
  · change l 3 0 = (-1)*(l 0 4)
    linear_combination (1 : ℝ)*h40
  · change l 3 1 = (-1)*(l 0 5)
    linear_combination (1 : ℝ)*h44
  · change l 3 2 = 0
    linear_combination (-1/2 : ℝ)*h10 + (-1/2 : ℝ)*h20 + (1/2 : ℝ)*h29 + (1 : ℝ)*h46
  · change l 3 3 = 0
    linear_combination (-1/2 : ℝ)*h6 + (-1 : ℝ)*h19 + (1/2 : ℝ)*h25 + (-1/2 : ℝ)*h32 + (1 : ℝ)*h42
  · change l 3 4 = (-1)*(l 0 0)
    linear_combination (-1 : ℝ)*h2 + (1 : ℝ)*h7 + (1 : ℝ)*h21 + (1 : ℝ)*h28 + (-1 : ℝ)*h47
  · change l 3 5 = (-1)*(l 0 1)
    linear_combination (-1 : ℝ)*h8 + (-1 : ℝ)*h17 + (1 : ℝ)*h27 + (-1 : ℝ)*h48
  · change l 4 0 = (1)*(l 0 0)
    linear_combination (1 : ℝ)*h2 + (-1 : ℝ)*h21 + (-1 : ℝ)*h28
  · change l 4 1 = (-1)*(l 0 1)
    linear_combination (1 : ℝ)*h1 + (-1 : ℝ)*h8
  · change l 4 2 = (1)*(-l 0 2)
    linear_combination (1 : ℝ)*h5 + (-1 : ℝ)*h12
  · change l 4 3 = (1)*(-l 0 3)
    linear_combination (1 : ℝ)*h0 + (1 : ℝ)*h9
  · change l 4 4 = (-1)*(l 0 4)
    linear_combination (1 : ℝ)*h4 + (1 : ℝ)*h13
  · change l 4 5 = (1)*(l 0 5)
    linear_combination (-1 : ℝ)*h14 + (-1 : ℝ)*h24 + (1 : ℝ)*h33
  · change l 5 0 = (1)*(l 0 1)
    linear_combination (1 : ℝ)*h8 + (1 : ℝ)*h17
  · change l 5 1 = (1)*(l 0 0)
    linear_combination (1 : ℝ)*h2 + (-1 : ℝ)*h28
  · change l 5 2 = 0
    linear_combination (1/2 : ℝ)*h6 + (1/2 : ℝ)*h25 + (-1/2 : ℝ)*h32
  · change l 5 3 = 0
    linear_combination (1/2 : ℝ)*h10 + (1/2 : ℝ)*h20 + (1/2 : ℝ)*h29
  · change l 5 4 = (-1)*(l 0 5)
    linear_combination (1 : ℝ)*h14 + (1 : ℝ)*h24
  · change l 5 5 = (-1)*(l 0 4)
    linear_combination (1 : ℝ)*h4 + (1 : ℝ)*h37
  · change l 6 0 = (1)*(-l 0 2)
    linear_combination (-1 : ℝ)*h12 + (1 : ℝ)*h41
  · change l 6 1 = 0
    linear_combination (1 : ℝ)*h3 + (1/2 : ℝ)*h6 + (1 : ℝ)*h19 + (-1/2 : ℝ)*h25 + (1/2 : ℝ)*h32 + (-1 : ℝ)*h42
  · change l 6 2 = (1)*(l 0 0)
    linear_combination (1 : ℝ)*h2 + (-1 : ℝ)*h21 + (-1 : ℝ)*h28 + (1 : ℝ)*h47
  · change l 6 3 = (-1)*(l 0 5)
    linear_combination (1 : ℝ)*h11 + (1 : ℝ)*h44
  · change l 6 4 = 0
    linear_combination (-1/2 : ℝ)*h10 + (1 : ℝ)*h15 + (-1/2 : ℝ)*h20 + (1/2 : ℝ)*h29 + (1 : ℝ)*h46
  · change l 6 5 = (-1)*(-l 0 3)
    linear_combination (1 : ℝ)*h16 + (1 : ℝ)*h35 + (-1 : ℝ)*h51
  · change l 7 0 = (-1)*(l 0 0)
    linear_combination (1 : ℝ)*h18 + (1 : ℝ)*h28
  · change l 7 1 = (1)*(l 0 1)
    linear_combination (1 : ℝ)*h8 + (1 : ℝ)*h17 + (1 : ℝ)*h22
  · change l 7 2 = (1)*(-l 0 2)
    linear_combination (1 : ℝ)*h26 + (-1 : ℝ)*h36
  · change l 7 3 = (1)*(-l 0 3)
    linear_combination (-1 : ℝ)*h16 + (1 : ℝ)*h30
  · change l 7 4 = (1)*(l 0 4)
    linear_combination (-1 : ℝ)*h4 + (1 : ℝ)*h34 + (-1 : ℝ)*h37
  · change l 7 5 = (-1)*(l 0 5)
    linear_combination (1 : ℝ)*h24 + (1 : ℝ)*h38
  · change l 8 0 = 0
    linear_combination (-1/2 : ℝ)*h6 + (1/2 : ℝ)*h25 + (-1/2 : ℝ)*h32 + (1 : ℝ)*h42
  · change l 8 1 = (1)*(-l 0 2)
    linear_combination (-1 : ℝ)*h12 + (1 : ℝ)*h23 + (1 : ℝ)*h41
  · change l 8 2 = (1)*(l 0 1)
    linear_combination (1 : ℝ)*h8 + (1 : ℝ)*h17 + (1 : ℝ)*h48
  · change l 8 3 = (1)*(l 0 4)
    linear_combination (1 : ℝ)*h31 + (-1 : ℝ)*h40
  · change l 8 4 = (1)*(-l 0 3)
    linear_combination (-1 : ℝ)*h16 + (1 : ℝ)*h51
  · change l 8 5 = 0
    linear_combination (-1/2 : ℝ)*h10 + (-1/2 : ℝ)*h20 + (1/2 : ℝ)*h29 + (1 : ℝ)*h39 + (1 : ℝ)*h46
  · change l 9 0 = (1)*(l 0 0)
    linear_combination (1 : ℝ)*h2 + (-1 : ℝ)*h7 + (-1 : ℝ)*h21 + (-1 : ℝ)*h28 + (1 : ℝ)*h43 + (1 : ℝ)*h47
  · change l 9 1 = (1)*(l 0 1)
    linear_combination (1 : ℝ)*h8 + (1 : ℝ)*h17 + (-1 : ℝ)*h27 + (1 : ℝ)*h45 + (1 : ℝ)*h48
  · change l 9 2 = (1)*(-l 0 2)
    linear_combination (-1 : ℝ)*h12 + (1 : ℝ)*h41 + (1 : ℝ)*h49
  · change l 9 3 = (1)*(-l 0 3)
    linear_combination (-1 : ℝ)*h16 + (-1 : ℝ)*h35 + (1 : ℝ)*h50 + (1 : ℝ)*h51
  · change l 9 4 = (1)*(l 0 4)
    linear_combination (-1 : ℝ)*h40 + (1 : ℝ)*h52
  · change l 9 5 = (1)*(l 0 5)
    linear_combination (-1 : ℝ)*h44 + (1 : ℝ)*h53
#print axioms linear_recovery
end
end PDTPolynomialSource
