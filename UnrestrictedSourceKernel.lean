module
public import SourceActionKernel

@[expose] public section
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
namespace PDTUnrestrictedSourceKernel
noncomputable section
open PDTStressTensor PDTStressBalance
open scoped Matrix
abbrev Local := Fin 6 → ℝ
abbrev End := Matrix (Fin 6) (Fin 6) ℝ

def embed (x : Local) : PDTResponseBridge.V :=
  ![x 0,x 1,x 2,0,0,x 3,x 4,0,0,x 5,0,0,0,0,0]
def extract (v : PDTResponseBridge.V) : Local := ![v 0,v 1,v 2,v 5,v 6,v 9]
def J : End := !![0,0,0,0,0,-1;0,0,0,0,1,0;0,0,0,1,0,0;
  0,0,-1,0,0,0;0,-1,0,0,0,0;1,0,0,0,0,0]
def response (d : ℝ) (D : End) (x : Local) : Tensor :=
  firstVariation d (embed x) (embed (D *ᵥ x))
def Invisible (d : ℝ) (D : End) : Prop := ∀ x, response d D x=0

def testField (k : Fin 11) : Local :=
  ![Pi.single 0 1,Pi.single 1 1,Pi.single 2 1,Pi.single 3 1,Pi.single 4 1,
    Pi.single 5 1,Pi.single 0 1+Pi.single 1 1,Pi.single 0 1+Pi.single 2 1,
    Pi.single 0 1+Pi.single 3 1,Pi.single 0 1+Pi.single 4 1,Pi.single 0 1+Pi.single 5 1] k

def probes (D : End) : Fin 35 → ℝ :=
  ![response 1 D (testField 0) 0 0,
    response 1 D (testField 0) 0 2,
    response 1 D (testField 0) 0 3,
    response 1 D (testField 0) 1 2,
    response 1 D (testField 0) 1 3,
    response 1 D (testField 1) 0 0,
    response 1 D (testField 1) 0 1,
    response 1 D (testField 1) 0 3,
    response 1 D (testField 1) 1 2,
    response 1 D (testField 1) 2 3,
    response 1 D (testField 2) 0 0,
    response 1 D (testField 2) 0 1,
    response 1 D (testField 2) 0 2,
    response 1 D (testField 2) 1 3,
    response 1 D (testField 2) 2 3,
    response 1 D (testField 3) 0 0,
    response 1 D (testField 3) 0 1,
    response 1 D (testField 3) 0 2,
    response 1 D (testField 3) 1 3,
    response 1 D (testField 3) 2 3,
    response 1 D (testField 4) 0 0,
    response 1 D (testField 4) 0 1,
    response 1 D (testField 4) 0 3,
    response 1 D (testField 4) 1 2,
    response 1 D (testField 4) 2 3,
    response 1 D (testField 5) 0 0,
    response 1 D (testField 5) 0 2,
    response 1 D (testField 5) 0 3,
    response 1 D (testField 5) 1 2,
    response 1 D (testField 5) 1 3,
    response 1 D (testField 6) 0 3,
    response 1 D (testField 7) 0 2,
    response 1 D (testField 8) 1 3,
    response 1 D (testField 9) 1 2,
    response 1 D (testField 10) 0 0]

set_option maxHeartbeats 0 in
private theorem probe_formulas (D : End) : probes D =
  ![D 0 0,
    -D 3 0,
    -D 4 0,
    D 1 0,
    D 2 0,
    D 1 1,
    D 3 1,
    -D 5 1,
    D 0 1,
    D 2 1,
    -D 2 2,
    -D 4 2,
    -D 5 2,
    D 0 2,
    D 1 2,
    -D 3 3,
    D 1 3,
    -D 0 3,
    -D 5 3,
    D 4 3,
    D 4 4,
    -D 2 4,
    -D 0 4,
    -D 5 4,
    D 3 4,
    D 5 5,
    -D 2 5,
    -D 1 5,
    -D 4 5,
    -D 3 5,
    -D 4 0 + -D 4 1 + -D 5 0 + -D 5 1,
    -D 3 0 + -D 3 2 + -D 5 0 + -D 5 2,
    D 2 0 + D 2 3 + -D 5 0 + -D 5 3,
    D 1 0 + D 1 4 + -D 5 0 + -D 5 4,
    D 0 0 + D 0 5 + D 5 0 + D 5 5] := by
  ext k
  fin_cases k <;>
    simp [probes,response,testField,firstVariation,crossInvariant,embed,field,
      metric,eta,Matrix.diagonal,PDTMaxwellSymbol.mink,Matrix.mulVec,
      dotProduct,Fin.sum_univ_succ] <;> ring

theorem finite_reconstruction (D : End) (h : probes D=0) : D=(-D 0 5) • J := by
  rw [probe_formulas] at h
  have h0 : D 0 0=0 := congrFun h 0
  have h1 : -D 3 0=0 := congrFun h 1
  have h2 : -D 4 0=0 := congrFun h 2
  have h3 : D 1 0=0 := congrFun h 3
  have h4 : D 2 0=0 := congrFun h 4
  have h5 : D 1 1=0 := congrFun h 5
  have h6 : D 3 1=0 := congrFun h 6
  have h7 : -D 5 1=0 := congrFun h 7
  have h8 : D 0 1=0 := congrFun h 8
  have h9 : D 2 1=0 := congrFun h 9
  have h10 : -D 2 2=0 := congrFun h 10
  have h11 : -D 4 2=0 := congrFun h 11
  have h12 : -D 5 2=0 := congrFun h 12
  have h13 : D 0 2=0 := congrFun h 13
  have h14 : D 1 2=0 := congrFun h 14
  have h15 : -D 3 3=0 := congrFun h 15
  have h16 : D 1 3=0 := congrFun h 16
  have h17 : -D 0 3=0 := congrFun h 17
  have h18 : -D 5 3=0 := congrFun h 18
  have h19 : D 4 3=0 := congrFun h 19
  have h20 : D 4 4=0 := congrFun h 20
  have h21 : -D 2 4=0 := congrFun h 21
  have h22 : -D 0 4=0 := congrFun h 22
  have h23 : -D 5 4=0 := congrFun h 23
  have h24 : D 3 4=0 := congrFun h 24
  have h25 : D 5 5=0 := congrFun h 25
  have h26 : -D 2 5=0 := congrFun h 26
  have h27 : -D 1 5=0 := congrFun h 27
  have h28 : -D 4 5=0 := congrFun h 28
  have h29 : -D 3 5=0 := congrFun h 29
  have h30 : -D 4 0 + -D 4 1 + -D 5 0 + -D 5 1=0 := congrFun h 30
  have h31 : -D 3 0 + -D 3 2 + -D 5 0 + -D 5 2=0 := congrFun h 31
  have h32 : D 2 0 + D 2 3 + -D 5 0 + -D 5 3=0 := congrFun h 32
  have h33 : D 1 0 + D 1 4 + -D 5 0 + -D 5 4=0 := congrFun h 33
  have h34 : D 0 0 + D 0 5 + D 5 0 + D 5 5=0 := congrFun h 34
  ext i j
  fin_cases i <;> fin_cases j
  · change D 0 0=(-D 0 5)*(0)
    linear_combination (1) * h0
  · change D 0 1=(-D 0 5)*(0)
    linear_combination (1) * h8
  · change D 0 2=(-D 0 5)*(0)
    linear_combination (1) * h13
  · change D 0 3=(-D 0 5)*(0)
    linear_combination (-1) * h17
  · change D 0 4=(-D 0 5)*(0)
    linear_combination (-1) * h22
  · change D 0 5=(-D 0 5)*(-1)
    ring
  · change D 1 0=(-D 0 5)*(0)
    linear_combination (1) * h3
  · change D 1 1=(-D 0 5)*(0)
    linear_combination (1) * h5
  · change D 1 2=(-D 0 5)*(0)
    linear_combination (1) * h14
  · change D 1 3=(-D 0 5)*(0)
    linear_combination (1) * h16
  · change D 1 4=(-D 0 5)*(1)
    linear_combination (-1) * h0 + (-1) * h3 + (-1) * h23 + (-1) * h25 + (1) * h33 + (1) * h34
  · change D 1 5=(-D 0 5)*(0)
    linear_combination (-1) * h27
  · change D 2 0=(-D 0 5)*(0)
    linear_combination (1) * h4
  · change D 2 1=(-D 0 5)*(0)
    linear_combination (1) * h9
  · change D 2 2=(-D 0 5)*(0)
    linear_combination (-1) * h10
  · change D 2 3=(-D 0 5)*(1)
    linear_combination (-1) * h0 + (-1) * h4 + (-1) * h18 + (-1) * h25 + (1) * h32 + (1) * h34
  · change D 2 4=(-D 0 5)*(0)
    linear_combination (-1) * h21
  · change D 2 5=(-D 0 5)*(0)
    linear_combination (-1) * h26
  · change D 3 0=(-D 0 5)*(0)
    linear_combination (-1) * h1
  · change D 3 1=(-D 0 5)*(0)
    linear_combination (1) * h6
  · change D 3 2=(-D 0 5)*(-1)
    linear_combination (1) * h0 + (1) * h1 + (1) * h12 + (1) * h25 + (-1) * h31 + (-1) * h34
  · change D 3 3=(-D 0 5)*(0)
    linear_combination (-1) * h15
  · change D 3 4=(-D 0 5)*(0)
    linear_combination (1) * h24
  · change D 3 5=(-D 0 5)*(0)
    linear_combination (-1) * h29
  · change D 4 0=(-D 0 5)*(0)
    linear_combination (-1) * h2
  · change D 4 1=(-D 0 5)*(-1)
    linear_combination (1) * h0 + (1) * h2 + (1) * h7 + (1) * h25 + (-1) * h30 + (-1) * h34
  · change D 4 2=(-D 0 5)*(0)
    linear_combination (-1) * h11
  · change D 4 3=(-D 0 5)*(0)
    linear_combination (1) * h19
  · change D 4 4=(-D 0 5)*(0)
    linear_combination (1) * h20
  · change D 4 5=(-D 0 5)*(0)
    linear_combination (-1) * h28
  · change D 5 0=(-D 0 5)*(1)
    linear_combination (-1) * h0 + (-1) * h25 + (1) * h34
  · change D 5 1=(-D 0 5)*(0)
    linear_combination (-1) * h7
  · change D 5 2=(-D 0 5)*(0)
    linear_combination (-1) * h12
  · change D 5 3=(-D 0 5)*(0)
    linear_combination (-1) * h18
  · change D 5 4=(-D 0 5)*(0)
    linear_combination (-1) * h23
  · change D 5 5=(-D 0 5)*(0)
    linear_combination (1) * h25

#print axioms finite_reconstruction
end
end PDTUnrestrictedSourceKernel
