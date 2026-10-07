module
public import GeometricTransport

@[expose] public section
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
namespace PDTStabilizerTests
noncomputable section
open PDTPfaffianCubic PDTCubicInvariance PDTHessianCovariance
open GravityScreening.ResponseClosureCertificate GravityScreening.ResponseClosureGeometry
open scoped Matrix
abbrev Mat := Matrix I I ℝ

def bivectorMetric : Mat := Matrix.diagonal (fun i => (q i : ℝ))
def MetricSkew (A : Mat) : Prop := A.transpose*bivectorMetric+bivectorMetric*A=0
def CubicInvariant (A : Mat) : Prop := ∀ x : I → ℝ, directional ℝ x (A *ᵥ x)=0

def pair (a b : I) : I → ℝ := Pi.single a 1+Pi.single b 1
def triple (a b c : I) : I → ℝ := pair a b+Pi.single c 1

private theorem pair_action (A : Mat) (a b : I) :
    A *ᵥ pair a b=fun i => A i a+A i b := by
  simp [pair,Matrix.mulVec_add]
  rfl

private theorem triple_action (A : Mat) (a b c : I) :
    A *ᵥ triple a b c=fun i => A i a+A i b+A i c := by
  simp [triple,Matrix.mulVec_add,pair_action]
  rfl

def probe (k : Fin 90) : I → ℝ :=
  if k.val=0 then pair 0 9 else
  if k.val=1 then pair 0 10 else
  if k.val=2 then pair 0 11 else
  if k.val=3 then pair 0 12 else
  if k.val=4 then pair 0 13 else
  if k.val=5 then pair 0 14 else
  if k.val=6 then pair 1 6 else
  if k.val=7 then pair 1 7 else
  if k.val=8 then pair 1 8 else
  if k.val=9 then pair 1 12 else
  if k.val=10 then pair 1 13 else
  if k.val=11 then pair 1 14 else
  if k.val=12 then pair 2 5 else
  if k.val=13 then pair 2 7 else
  if k.val=14 then pair 2 8 else
  if k.val=15 then pair 2 10 else
  if k.val=16 then pair 2 11 else
  if k.val=17 then pair 2 14 else
  if k.val=18 then pair 3 5 else
  if k.val=19 then pair 3 6 else
  if k.val=20 then pair 3 8 else
  if k.val=21 then pair 3 9 else
  if k.val=22 then pair 3 11 else
  if k.val=23 then pair 3 13 else
  if k.val=24 then pair 4 5 else
  if k.val=25 then pair 4 6 else
  if k.val=26 then pair 4 7 else
  if k.val=27 then pair 4 9 else
  if k.val=28 then pair 4 10 else
  if k.val=29 then pair 4 12 else
  if k.val=30 then triple 0 1 6 else
  if k.val=31 then triple 0 1 7 else
  if k.val=32 then triple 0 1 8 else
  if k.val=33 then triple 0 1 9 else
  if k.val=34 then triple 0 1 10 else
  if k.val=35 then triple 0 1 11 else
  if k.val=36 then triple 0 1 12 else
  if k.val=37 then triple 0 1 13 else
  if k.val=38 then triple 0 1 14 else
  if k.val=39 then triple 0 2 9 else
  if k.val=40 then triple 0 2 10 else
  if k.val=41 then triple 0 2 11 else
  if k.val=42 then triple 0 2 12 else
  if k.val=43 then triple 0 2 13 else
  if k.val=44 then triple 0 2 14 else
  if k.val=45 then triple 0 3 9 else
  if k.val=46 then triple 0 3 10 else
  if k.val=47 then triple 0 3 11 else
  if k.val=48 then triple 0 3 12 else
  if k.val=49 then triple 0 3 13 else
  if k.val=50 then triple 0 3 14 else
  if k.val=51 then triple 0 4 9 else
  if k.val=52 then triple 0 4 10 else
  if k.val=53 then triple 0 4 11 else
  if k.val=54 then triple 0 4 12 else
  if k.val=55 then triple 0 4 13 else
  if k.val=56 then triple 0 4 14 else
  if k.val=57 then triple 0 5 12 else
  if k.val=58 then triple 0 5 13 else
  if k.val=59 then triple 0 5 14 else
  if k.val=60 then triple 0 6 10 else
  if k.val=61 then triple 0 6 11 else
  if k.val=62 then triple 0 6 14 else
  if k.val=63 then triple 0 7 9 else
  if k.val=64 then triple 0 7 11 else
  if k.val=65 then triple 0 7 13 else
  if k.val=66 then triple 0 8 9 else
  if k.val=67 then triple 0 8 10 else
  if k.val=68 then triple 0 8 12 else
  if k.val=69 then triple 0 9 10 else
  if k.val=70 then triple 0 9 11 else
  if k.val=71 then triple 0 9 12 else
  if k.val=72 then triple 0 9 13 else
  if k.val=73 then triple 0 10 11 else
  if k.val=74 then triple 0 10 12 else
  if k.val=75 then triple 1 2 14 else
  if k.val=76 then triple 1 3 13 else
  if k.val=77 then triple 1 4 12 else
  if k.val=78 then triple 1 5 12 else
  if k.val=79 then triple 1 5 13 else
  if k.val=80 then triple 1 5 14 else
  if k.val=81 then triple 1 6 10 else
  if k.val=82 then triple 1 6 11 else
  if k.val=83 then triple 1 6 12 else
  if k.val=84 then triple 1 6 13 else
  if k.val=85 then triple 1 7 11 else
  if k.val=86 then triple 1 7 12 else
  if k.val=87 then triple 2 5 12 else
  if k.val=88 then triple 2 5 13 else
  if k.val=89 then triple 3 5 12 else 0

def FiniteTests (A : Mat) : Prop := ∀ k : Fin 90, directional ℝ (probe k) (A *ᵥ probe k)=0

def equation (k : Fin 210) (A : Mat) : ℝ :=
  if k.val=0 then (2*A 0 0) else
  if k.val=1 then (A 0 1 + A 1 0) else
  if k.val=2 then (A 0 2 + -A 2 0) else
  if k.val=3 then (A 0 3 + A 3 0) else
  if k.val=4 then (A 0 4 + -A 4 0) else
  if k.val=5 then (A 0 5 + A 5 0) else
  if k.val=6 then (A 0 6 + -A 6 0) else
  if k.val=7 then (A 0 7 + A 7 0) else
  if k.val=8 then (A 0 8 + -A 8 0) else
  if k.val=9 then (A 0 9 + -A 9 0) else
  if k.val=10 then (A 0 10 + A 10 0) else
  if k.val=11 then (A 0 11 + -A 11 0) else
  if k.val=12 then (A 0 12 + -A 12 0) else
  if k.val=13 then (A 0 13 + A 13 0) else
  if k.val=14 then (A 0 14 + -A 14 0) else
  if k.val=15 then (2*A 1 1) else
  if k.val=16 then (A 1 2 + -A 2 1) else
  if k.val=17 then (A 1 3 + A 3 1) else
  if k.val=18 then (A 1 4 + -A 4 1) else
  if k.val=19 then (A 1 5 + A 5 1) else
  if k.val=20 then (A 1 6 + -A 6 1) else
  if k.val=21 then (A 1 7 + A 7 1) else
  if k.val=22 then (A 1 8 + -A 8 1) else
  if k.val=23 then (A 1 9 + -A 9 1) else
  if k.val=24 then (A 1 10 + A 10 1) else
  if k.val=25 then (A 1 11 + -A 11 1) else
  if k.val=26 then (A 1 12 + -A 12 1) else
  if k.val=27 then (A 1 13 + A 13 1) else
  if k.val=28 then (A 1 14 + -A 14 1) else
  if k.val=29 then (-2*A 2 2) else
  if k.val=30 then (-A 2 3 + A 3 2) else
  if k.val=31 then (-A 2 4 + -A 4 2) else
  if k.val=32 then (-A 2 5 + A 5 2) else
  if k.val=33 then (-A 2 6 + -A 6 2) else
  if k.val=34 then (-A 2 7 + A 7 2) else
  if k.val=35 then (-A 2 8 + -A 8 2) else
  if k.val=36 then (-A 2 9 + -A 9 2) else
  if k.val=37 then (-A 2 10 + A 10 2) else
  if k.val=38 then (-A 2 11 + -A 11 2) else
  if k.val=39 then (-A 2 12 + -A 12 2) else
  if k.val=40 then (-A 2 13 + A 13 2) else
  if k.val=41 then (-A 2 14 + -A 14 2) else
  if k.val=42 then (2*A 3 3) else
  if k.val=43 then (A 3 4 + -A 4 3) else
  if k.val=44 then (A 3 5 + A 5 3) else
  if k.val=45 then (A 3 6 + -A 6 3) else
  if k.val=46 then (A 3 7 + A 7 3) else
  if k.val=47 then (A 3 8 + -A 8 3) else
  if k.val=48 then (A 3 9 + -A 9 3) else
  if k.val=49 then (A 3 10 + A 10 3) else
  if k.val=50 then (A 3 11 + -A 11 3) else
  if k.val=51 then (A 3 12 + -A 12 3) else
  if k.val=52 then (A 3 13 + A 13 3) else
  if k.val=53 then (A 3 14 + -A 14 3) else
  if k.val=54 then (-2*A 4 4) else
  if k.val=55 then (-A 4 5 + A 5 4) else
  if k.val=56 then (-A 4 6 + -A 6 4) else
  if k.val=57 then (-A 4 7 + A 7 4) else
  if k.val=58 then (-A 4 8 + -A 8 4) else
  if k.val=59 then (-A 4 9 + -A 9 4) else
  if k.val=60 then (-A 4 10 + A 10 4) else
  if k.val=61 then (-A 4 11 + -A 11 4) else
  if k.val=62 then (-A 4 12 + -A 12 4) else
  if k.val=63 then (-A 4 13 + A 13 4) else
  if k.val=64 then (-A 4 14 + -A 14 4) else
  if k.val=65 then (2*A 5 5) else
  if k.val=66 then (A 5 6 + -A 6 5) else
  if k.val=67 then (A 5 7 + A 7 5) else
  if k.val=68 then (A 5 8 + -A 8 5) else
  if k.val=69 then (A 5 9 + -A 9 5) else
  if k.val=70 then (A 5 10 + A 10 5) else
  if k.val=71 then (A 5 11 + -A 11 5) else
  if k.val=72 then (A 5 12 + -A 12 5) else
  if k.val=73 then (A 5 13 + A 13 5) else
  if k.val=74 then (A 5 14 + -A 14 5) else
  if k.val=75 then (-2*A 6 6) else
  if k.val=76 then (-A 6 7 + A 7 6) else
  if k.val=77 then (-A 6 8 + -A 8 6) else
  if k.val=78 then (-A 6 9 + -A 9 6) else
  if k.val=79 then (-A 6 10 + A 10 6) else
  if k.val=80 then (-A 6 11 + -A 11 6) else
  if k.val=81 then (-A 6 12 + -A 12 6) else
  if k.val=82 then (-A 6 13 + A 13 6) else
  if k.val=83 then (-A 6 14 + -A 14 6) else
  if k.val=84 then (2*A 7 7) else
  if k.val=85 then (A 7 8 + -A 8 7) else
  if k.val=86 then (A 7 9 + -A 9 7) else
  if k.val=87 then (A 7 10 + A 10 7) else
  if k.val=88 then (A 7 11 + -A 11 7) else
  if k.val=89 then (A 7 12 + -A 12 7) else
  if k.val=90 then (A 7 13 + A 13 7) else
  if k.val=91 then (A 7 14 + -A 14 7) else
  if k.val=92 then (-2*A 8 8) else
  if k.val=93 then (-A 8 9 + -A 9 8) else
  if k.val=94 then (-A 8 10 + A 10 8) else
  if k.val=95 then (-A 8 11 + -A 11 8) else
  if k.val=96 then (-A 8 12 + -A 12 8) else
  if k.val=97 then (-A 8 13 + A 13 8) else
  if k.val=98 then (-A 8 14 + -A 14 8) else
  if k.val=99 then (-2*A 9 9) else
  if k.val=100 then (-A 9 10 + A 10 9) else
  if k.val=101 then (-A 9 11 + -A 11 9) else
  if k.val=102 then (-A 9 12 + -A 12 9) else
  if k.val=103 then (-A 9 13 + A 13 9) else
  if k.val=104 then (-A 9 14 + -A 14 9) else
  if k.val=105 then (2*A 10 10) else
  if k.val=106 then (A 10 11 + -A 11 10) else
  if k.val=107 then (A 10 12 + -A 12 10) else
  if k.val=108 then (A 10 13 + A 13 10) else
  if k.val=109 then (A 10 14 + -A 14 10) else
  if k.val=110 then (-2*A 11 11) else
  if k.val=111 then (-A 11 12 + -A 12 11) else
  if k.val=112 then (-A 11 13 + A 13 11) else
  if k.val=113 then (-A 11 14 + -A 14 11) else
  if k.val=114 then (-2*A 12 12) else
  if k.val=115 then (-A 12 13 + A 13 12) else
  if k.val=116 then (-A 12 14 + -A 14 12) else
  if k.val=117 then (2*A 13 13) else
  if k.val=118 then (A 13 14 + -A 14 13) else
  if k.val=119 then (-2*A 14 14) else
  if k.val=120 then (A 14 0 + A 14 9) else
  if k.val=121 then (-A 13 0 + -A 13 10) else
  if k.val=122 then (A 12 0 + A 12 11) else
  if k.val=123 then (A 11 0 + A 11 12) else
  if k.val=124 then (-A 10 0 + -A 10 13) else
  if k.val=125 then (A 9 0 + A 9 14) else
  if k.val=126 then (-A 14 1 + -A 14 6) else
  if k.val=127 then (A 13 1 + A 13 7) else
  if k.val=128 then (-A 12 1 + -A 12 8) else
  if k.val=129 then (-A 8 1 + -A 8 12) else
  if k.val=130 then (A 7 1 + A 7 13) else
  if k.val=131 then (-A 6 1 + -A 6 14) else
  if k.val=132 then (A 14 2 + A 14 5) else
  if k.val=133 then (-A 11 2 + -A 11 7) else
  if k.val=134 then (A 10 2 + A 10 8) else
  if k.val=135 then (A 8 2 + A 8 10) else
  if k.val=136 then (-A 7 2 + -A 7 11) else
  if k.val=137 then (A 5 2 + A 5 14) else
  if k.val=138 then (-A 13 3 + -A 13 5) else
  if k.val=139 then (A 11 3 + A 11 6) else
  if k.val=140 then (-A 9 3 + -A 9 8) else
  if k.val=141 then (-A 8 3 + -A 8 9) else
  if k.val=142 then (A 6 3 + A 6 11) else
  if k.val=143 then (-A 5 3 + -A 5 13) else
  if k.val=144 then (A 12 4 + A 12 5) else
  if k.val=145 then (-A 10 4 + -A 10 6) else
  if k.val=146 then (A 9 4 + A 9 7) else
  if k.val=147 then (A 7 4 + A 7 9) else
  if k.val=148 then (-A 6 4 + -A 6 10) else
  if k.val=149 then (A 5 4 + A 5 12) else
  if k.val=150 then (-A 14 0 + -A 14 1 + -A 14 6) else
  if k.val=151 then (A 13 0 + A 13 1 + A 13 7) else
  if k.val=152 then (-A 12 0 + -A 12 1 + -A 12 8) else
  if k.val=153 then (A 14 0 + A 14 1 + A 14 9) else
  if k.val=154 then (-A 13 0 + -A 13 1 + -A 13 10) else
  if k.val=155 then (A 12 0 + A 12 1 + A 12 11) else
  if k.val=156 then (-A 8 0 + -A 8 1 + -A 8 12 + A 11 0 + A 11 1 + A 11 12) else
  if k.val=157 then (A 7 0 + A 7 1 + A 7 13 + -A 10 0 + -A 10 1 + -A 10 13) else
  if k.val=158 then (-A 6 0 + -A 6 1 + -A 6 14 + A 9 0 + A 9 1 + A 9 14) else
  if k.val=159 then (A 14 0 + A 14 2 + A 14 9) else
  if k.val=160 then (A 8 0 + A 8 2 + A 8 10 + -A 13 0 + -A 13 2 + -A 13 10) else
  if k.val=161 then (-A 7 0 + -A 7 2 + -A 7 11 + A 12 0 + A 12 2 + A 12 11) else
  if k.val=162 then (A 11 0 + A 11 2 + A 11 12) else
  if k.val=163 then (-A 10 0 + -A 10 2 + -A 10 13) else
  if k.val=164 then (A 5 0 + A 5 2 + A 5 14 + A 9 0 + A 9 2 + A 9 14) else
  if k.val=165 then (-A 8 0 + -A 8 3 + -A 8 9 + A 14 0 + A 14 3 + A 14 9) else
  if k.val=166 then (-A 13 0 + -A 13 3 + -A 13 10) else
  if k.val=167 then (A 6 0 + A 6 3 + A 6 11 + A 12 0 + A 12 3 + A 12 11) else
  if k.val=168 then (A 11 0 + A 11 3 + A 11 12) else
  if k.val=169 then (-A 5 0 + -A 5 3 + -A 5 13 + -A 10 0 + -A 10 3 + -A 10 13) else
  if k.val=170 then (A 9 0 + A 9 3 + A 9 14) else
  if k.val=171 then (A 7 0 + A 7 4 + A 7 9 + A 14 0 + A 14 4 + A 14 9) else
  if k.val=172 then (-A 6 0 + -A 6 4 + -A 6 10 + -A 13 0 + -A 13 4 + -A 13 10) else
  if k.val=173 then (A 12 0 + A 12 4 + A 12 11) else
  if k.val=174 then (A 5 0 + A 5 4 + A 5 12 + A 11 0 + A 11 4 + A 11 12) else
  if k.val=175 then (-A 10 0 + -A 10 4 + -A 10 13) else
  if k.val=176 then (A 9 0 + A 9 4 + A 9 14) else
  if k.val=177 then (A 4 0 + A 4 5 + A 4 12 + A 11 0 + A 11 5 + A 11 12) else
  if k.val=178 then (-A 3 0 + -A 3 5 + -A 3 13 + -A 10 0 + -A 10 5 + -A 10 13) else
  if k.val=179 then (A 2 0 + A 2 5 + A 2 14 + A 9 0 + A 9 5 + A 9 14) else
  if k.val=180 then (-A 4 0 + -A 4 6 + -A 4 10 + -A 13 0 + -A 13 6 + -A 13 10) else
  if k.val=181 then (A 3 0 + A 3 6 + A 3 11 + A 12 0 + A 12 6 + A 12 11) else
  if k.val=182 then (-A 1 0 + -A 1 6 + -A 1 14 + A 9 0 + A 9 6 + A 9 14) else
  if k.val=183 then (A 4 0 + A 4 7 + A 4 9 + A 14 0 + A 14 7 + A 14 9) else
  if k.val=184 then (-A 2 0 + -A 2 7 + -A 2 11 + A 12 0 + A 12 7 + A 12 11) else
  if k.val=185 then (A 1 0 + A 1 7 + A 1 13 + -A 10 0 + -A 10 7 + -A 10 13) else
  if k.val=186 then (-A 3 0 + -A 3 8 + -A 3 9 + A 14 0 + A 14 8 + A 14 9) else
  if k.val=187 then (A 2 0 + A 2 8 + A 2 10 + -A 13 0 + -A 13 8 + -A 13 10) else
  if k.val=188 then (-A 1 0 + -A 1 8 + -A 1 12 + A 11 0 + A 11 8 + A 11 12) else
  if k.val=189 then (-A 13 0 + -A 13 9 + -A 13 10 + A 14 0 + A 14 9 + A 14 10) else
  if k.val=190 then (A 12 0 + A 12 9 + A 12 11 + A 14 0 + A 14 9 + A 14 11) else
  if k.val=191 then (A 11 0 + A 11 9 + A 11 12 + A 14 0 + A 14 9 + A 14 12) else
  if k.val=192 then (-A 10 0 + -A 10 9 + -A 10 13 + A 14 0 + A 14 9 + A 14 13) else
  if k.val=193 then (A 12 0 + A 12 10 + A 12 11 + -A 13 0 + -A 13 10 + -A 13 11) else
  if k.val=194 then (A 11 0 + A 11 10 + A 11 12 + -A 13 0 + -A 13 10 + -A 13 12) else
  if k.val=195 then (A 5 1 + A 5 2 + A 5 14 + -A 6 1 + -A 6 2 + -A 6 14) else
  if k.val=196 then (-A 5 1 + -A 5 3 + -A 5 13 + A 7 1 + A 7 3 + A 7 13) else
  if k.val=197 then (A 5 1 + A 5 4 + A 5 12 + -A 8 1 + -A 8 4 + -A 8 12) else
  if k.val=198 then (A 4 1 + A 4 5 + A 4 12 + -A 8 1 + -A 8 5 + -A 8 12) else
  if k.val=199 then (-A 3 1 + -A 3 5 + -A 3 13 + A 7 1 + A 7 5 + A 7 13) else
  if k.val=200 then (A 2 1 + A 2 5 + A 2 14 + -A 6 1 + -A 6 5 + -A 6 14) else
  if k.val=201 then (-A 4 1 + -A 4 6 + -A 4 10 + -A 14 1 + -A 14 6 + -A 14 10) else
  if k.val=202 then (A 3 1 + A 3 6 + A 3 11 + -A 14 1 + -A 14 6 + -A 14 11) else
  if k.val=203 then (-A 8 1 + -A 8 6 + -A 8 12 + -A 14 1 + -A 14 6 + -A 14 12) else
  if k.val=204 then (A 7 1 + A 7 6 + A 7 13 + -A 14 1 + -A 14 6 + -A 14 13) else
  if k.val=205 then (-A 2 1 + -A 2 7 + -A 2 11 + A 13 1 + A 13 7 + A 13 11) else
  if k.val=206 then (-A 8 1 + -A 8 7 + -A 8 12 + A 13 1 + A 13 7 + A 13 12) else
  if k.val=207 then (A 4 2 + A 4 5 + A 4 12 + A 14 2 + A 14 5 + A 14 12) else
  if k.val=208 then (-A 3 2 + -A 3 5 + -A 3 13 + A 14 2 + A 14 5 + A 14 13) else
  if k.val=209 then (A 4 3 + A 4 5 + A 4 12 + -A 13 3 + -A 13 5 + -A 13 12) else 0

def Certificate (A : Mat) : Prop := ∀ k : Fin 210, equation k A=0

theorem metric_entry (A : Mat) (hm : MetricSkew A) (r c : I) :
    (q r : ℝ)*A r c+(q c : ℝ)*A c r=0 := by
  have h := congrArg (fun M : Mat => M r c) hm
  simpa [bivectorMetric,Matrix.mul_diagonal,Matrix.diagonal_mul,mul_comm,add_comm] using h

private theorem probe_00 (A : Mat) :
    directional ℝ (pair 0 9) (A *ᵥ pair 0 9)=A 14 0 + A 14 9 := by
  rw [pair_action,directional_eval]
  norm_num [triple,pair,Pi.single_apply,Fin.ext_iff]

private theorem probe_01 (A : Mat) :
    directional ℝ (pair 0 10) (A *ᵥ pair 0 10)=-A 13 0 + -A 13 10 := by
  rw [pair_action,directional_eval]
  norm_num [triple,pair,Pi.single_apply,Fin.ext_iff]
  ring

private theorem probe_02 (A : Mat) :
    directional ℝ (pair 0 11) (A *ᵥ pair 0 11)=A 12 0 + A 12 11 := by
  rw [pair_action,directional_eval]
  norm_num [triple,pair,Pi.single_apply,Fin.ext_iff]

private theorem probe_03 (A : Mat) :
    directional ℝ (pair 0 12) (A *ᵥ pair 0 12)=A 11 0 + A 11 12 := by
  rw [pair_action,directional_eval]
  norm_num [triple,pair,Pi.single_apply,Fin.ext_iff]

private theorem probe_04 (A : Mat) :
    directional ℝ (pair 0 13) (A *ᵥ pair 0 13)=-A 10 0 + -A 10 13 := by
  rw [pair_action,directional_eval]
  norm_num [triple,pair,Pi.single_apply,Fin.ext_iff]
  ring

private theorem probe_05 (A : Mat) :
    directional ℝ (pair 0 14) (A *ᵥ pair 0 14)=A 9 0 + A 9 14 := by
  rw [pair_action,directional_eval]
  norm_num [triple,pair,Pi.single_apply,Fin.ext_iff]

private theorem probe_06 (A : Mat) :
    directional ℝ (pair 1 6) (A *ᵥ pair 1 6)=-A 14 1 + -A 14 6 := by
  rw [pair_action,directional_eval]
  norm_num [triple,pair,Pi.single_apply,Fin.ext_iff]
  ring

private theorem probe_07 (A : Mat) :
    directional ℝ (pair 1 7) (A *ᵥ pair 1 7)=A 13 1 + A 13 7 := by
  rw [pair_action,directional_eval]
  norm_num [triple,pair,Pi.single_apply,Fin.ext_iff]

private theorem probe_08 (A : Mat) :
    directional ℝ (pair 1 8) (A *ᵥ pair 1 8)=-A 12 1 + -A 12 8 := by
  rw [pair_action,directional_eval]
  norm_num [triple,pair,Pi.single_apply,Fin.ext_iff]
  ring

private theorem probe_09 (A : Mat) :
    directional ℝ (pair 1 12) (A *ᵥ pair 1 12)=-A 8 1 + -A 8 12 := by
  rw [pair_action,directional_eval]
  norm_num [triple,pair,Pi.single_apply,Fin.ext_iff]
  ring

private theorem probe_10 (A : Mat) :
    directional ℝ (pair 1 13) (A *ᵥ pair 1 13)=A 7 1 + A 7 13 := by
  rw [pair_action,directional_eval]
  norm_num [triple,pair,Pi.single_apply,Fin.ext_iff]

private theorem probe_11 (A : Mat) :
    directional ℝ (pair 1 14) (A *ᵥ pair 1 14)=-A 6 1 + -A 6 14 := by
  rw [pair_action,directional_eval]
  norm_num [triple,pair,Pi.single_apply,Fin.ext_iff]
  ring

private theorem probe_12 (A : Mat) :
    directional ℝ (pair 2 5) (A *ᵥ pair 2 5)=A 14 2 + A 14 5 := by
  rw [pair_action,directional_eval]
  norm_num [triple,pair,Pi.single_apply,Fin.ext_iff]

private theorem probe_13 (A : Mat) :
    directional ℝ (pair 2 7) (A *ᵥ pair 2 7)=-A 11 2 + -A 11 7 := by
  rw [pair_action,directional_eval]
  norm_num [triple,pair,Pi.single_apply,Fin.ext_iff]
  ring

private theorem probe_14 (A : Mat) :
    directional ℝ (pair 2 8) (A *ᵥ pair 2 8)=A 10 2 + A 10 8 := by
  rw [pair_action,directional_eval]
  norm_num [triple,pair,Pi.single_apply,Fin.ext_iff]

private theorem probe_15 (A : Mat) :
    directional ℝ (pair 2 10) (A *ᵥ pair 2 10)=A 8 2 + A 8 10 := by
  rw [pair_action,directional_eval]
  norm_num [triple,pair,Pi.single_apply,Fin.ext_iff]

private theorem probe_16 (A : Mat) :
    directional ℝ (pair 2 11) (A *ᵥ pair 2 11)=-A 7 2 + -A 7 11 := by
  rw [pair_action,directional_eval]
  norm_num [triple,pair,Pi.single_apply,Fin.ext_iff]
  ring

private theorem probe_17 (A : Mat) :
    directional ℝ (pair 2 14) (A *ᵥ pair 2 14)=A 5 2 + A 5 14 := by
  rw [pair_action,directional_eval]
  norm_num [triple,pair,Pi.single_apply,Fin.ext_iff]

private theorem probe_18 (A : Mat) :
    directional ℝ (pair 3 5) (A *ᵥ pair 3 5)=-A 13 3 + -A 13 5 := by
  rw [pair_action,directional_eval]
  norm_num [triple,pair,Pi.single_apply,Fin.ext_iff]
  ring

private theorem probe_19 (A : Mat) :
    directional ℝ (pair 3 6) (A *ᵥ pair 3 6)=A 11 3 + A 11 6 := by
  rw [pair_action,directional_eval]
  norm_num [triple,pair,Pi.single_apply,Fin.ext_iff]

private theorem probe_20 (A : Mat) :
    directional ℝ (pair 3 8) (A *ᵥ pair 3 8)=-A 9 3 + -A 9 8 := by
  rw [pair_action,directional_eval]
  norm_num [triple,pair,Pi.single_apply,Fin.ext_iff]
  ring

private theorem probe_21 (A : Mat) :
    directional ℝ (pair 3 9) (A *ᵥ pair 3 9)=-A 8 3 + -A 8 9 := by
  rw [pair_action,directional_eval]
  norm_num [triple,pair,Pi.single_apply,Fin.ext_iff]
  ring

private theorem probe_22 (A : Mat) :
    directional ℝ (pair 3 11) (A *ᵥ pair 3 11)=A 6 3 + A 6 11 := by
  rw [pair_action,directional_eval]
  norm_num [triple,pair,Pi.single_apply,Fin.ext_iff]

private theorem probe_23 (A : Mat) :
    directional ℝ (pair 3 13) (A *ᵥ pair 3 13)=-A 5 3 + -A 5 13 := by
  rw [pair_action,directional_eval]
  norm_num [triple,pair,Pi.single_apply,Fin.ext_iff]
  ring

private theorem probe_24 (A : Mat) :
    directional ℝ (pair 4 5) (A *ᵥ pair 4 5)=A 12 4 + A 12 5 := by
  rw [pair_action,directional_eval]
  norm_num [triple,pair,Pi.single_apply,Fin.ext_iff]

private theorem probe_25 (A : Mat) :
    directional ℝ (pair 4 6) (A *ᵥ pair 4 6)=-A 10 4 + -A 10 6 := by
  rw [pair_action,directional_eval]
  norm_num [triple,pair,Pi.single_apply,Fin.ext_iff]
  ring

private theorem probe_26 (A : Mat) :
    directional ℝ (pair 4 7) (A *ᵥ pair 4 7)=A 9 4 + A 9 7 := by
  rw [pair_action,directional_eval]
  norm_num [triple,pair,Pi.single_apply,Fin.ext_iff]

private theorem probe_27 (A : Mat) :
    directional ℝ (pair 4 9) (A *ᵥ pair 4 9)=A 7 4 + A 7 9 := by
  rw [pair_action,directional_eval]
  norm_num [triple,pair,Pi.single_apply,Fin.ext_iff]

private theorem probe_28 (A : Mat) :
    directional ℝ (pair 4 10) (A *ᵥ pair 4 10)=-A 6 4 + -A 6 10 := by
  rw [pair_action,directional_eval]
  norm_num [triple,pair,Pi.single_apply,Fin.ext_iff]
  ring

private theorem probe_29 (A : Mat) :
    directional ℝ (pair 4 12) (A *ᵥ pair 4 12)=A 5 4 + A 5 12 := by
  rw [pair_action,directional_eval]
  norm_num [triple,pair,Pi.single_apply,Fin.ext_iff]

private theorem probe_30 (A : Mat) :
    directional ℝ (triple 0 1 6) (A *ᵥ triple 0 1 6)=-A 14 0 + -A 14 1 + -A 14 6 := by
  rw [triple_action,directional_eval]
  norm_num [triple,pair,Pi.single_apply,Fin.ext_iff]
  ring

private theorem probe_31 (A : Mat) :
    directional ℝ (triple 0 1 7) (A *ᵥ triple 0 1 7)=A 13 0 + A 13 1 + A 13 7 := by
  rw [triple_action,directional_eval]
  norm_num [triple,pair,Pi.single_apply,Fin.ext_iff]

private theorem probe_32 (A : Mat) :
    directional ℝ (triple 0 1 8) (A *ᵥ triple 0 1 8)=-A 12 0 + -A 12 1 + -A 12 8 := by
  rw [triple_action,directional_eval]
  norm_num [triple,pair,Pi.single_apply,Fin.ext_iff]
  ring

private theorem probe_33 (A : Mat) :
    directional ℝ (triple 0 1 9) (A *ᵥ triple 0 1 9)=A 14 0 + A 14 1 + A 14 9 := by
  rw [triple_action,directional_eval]
  norm_num [triple,pair,Pi.single_apply,Fin.ext_iff]

private theorem probe_34 (A : Mat) :
    directional ℝ (triple 0 1 10) (A *ᵥ triple 0 1 10)=-A 13 0 + -A 13 1 + -A 13 10 := by
  rw [triple_action,directional_eval]
  norm_num [triple,pair,Pi.single_apply,Fin.ext_iff]
  ring

private theorem probe_35 (A : Mat) :
    directional ℝ (triple 0 1 11) (A *ᵥ triple 0 1 11)=A 12 0 + A 12 1 + A 12 11 := by
  rw [triple_action,directional_eval]
  norm_num [triple,pair,Pi.single_apply,Fin.ext_iff]

private theorem probe_36 (A : Mat) :
    directional ℝ (triple 0 1 12) (A *ᵥ triple 0 1 12)=-A 8 0 + -A 8 1 + -A 8 12 + A 11 0 + A 11 1 + A 11 12 := by
  rw [triple_action,directional_eval]
  norm_num [triple,pair,Pi.single_apply,Fin.ext_iff]
  ring

private theorem probe_37 (A : Mat) :
    directional ℝ (triple 0 1 13) (A *ᵥ triple 0 1 13)=A 7 0 + A 7 1 + A 7 13 + -A 10 0 + -A 10 1 + -A 10 13 := by
  rw [triple_action,directional_eval]
  norm_num [triple,pair,Pi.single_apply,Fin.ext_iff]
  ring

private theorem probe_38 (A : Mat) :
    directional ℝ (triple 0 1 14) (A *ᵥ triple 0 1 14)=-A 6 0 + -A 6 1 + -A 6 14 + A 9 0 + A 9 1 + A 9 14 := by
  rw [triple_action,directional_eval]
  norm_num [triple,pair,Pi.single_apply,Fin.ext_iff]
  ring

private theorem probe_39 (A : Mat) :
    directional ℝ (triple 0 2 9) (A *ᵥ triple 0 2 9)=A 14 0 + A 14 2 + A 14 9 := by
  rw [triple_action,directional_eval]
  norm_num [triple,pair,Pi.single_apply,Fin.ext_iff]

private theorem probe_40 (A : Mat) :
    directional ℝ (triple 0 2 10) (A *ᵥ triple 0 2 10)=A 8 0 + A 8 2 + A 8 10 + -A 13 0 + -A 13 2 + -A 13 10 := by
  rw [triple_action,directional_eval]
  norm_num [triple,pair,Pi.single_apply,Fin.ext_iff]
  ring

private theorem probe_41 (A : Mat) :
    directional ℝ (triple 0 2 11) (A *ᵥ triple 0 2 11)=-A 7 0 + -A 7 2 + -A 7 11 + A 12 0 + A 12 2 + A 12 11 := by
  rw [triple_action,directional_eval]
  norm_num [triple,pair,Pi.single_apply,Fin.ext_iff]
  ring

private theorem probe_42 (A : Mat) :
    directional ℝ (triple 0 2 12) (A *ᵥ triple 0 2 12)=A 11 0 + A 11 2 + A 11 12 := by
  rw [triple_action,directional_eval]
  norm_num [triple,pair,Pi.single_apply,Fin.ext_iff]

private theorem probe_43 (A : Mat) :
    directional ℝ (triple 0 2 13) (A *ᵥ triple 0 2 13)=-A 10 0 + -A 10 2 + -A 10 13 := by
  rw [triple_action,directional_eval]
  norm_num [triple,pair,Pi.single_apply,Fin.ext_iff]
  ring

private theorem probe_44 (A : Mat) :
    directional ℝ (triple 0 2 14) (A *ᵥ triple 0 2 14)=A 5 0 + A 5 2 + A 5 14 + A 9 0 + A 9 2 + A 9 14 := by
  rw [triple_action,directional_eval]
  norm_num [triple,pair,Pi.single_apply,Fin.ext_iff]
  ring

private theorem probe_45 (A : Mat) :
    directional ℝ (triple 0 3 9) (A *ᵥ triple 0 3 9)=-A 8 0 + -A 8 3 + -A 8 9 + A 14 0 + A 14 3 + A 14 9 := by
  rw [triple_action,directional_eval]
  norm_num [triple,pair,Pi.single_apply,Fin.ext_iff]
  ring

private theorem probe_46 (A : Mat) :
    directional ℝ (triple 0 3 10) (A *ᵥ triple 0 3 10)=-A 13 0 + -A 13 3 + -A 13 10 := by
  rw [triple_action,directional_eval]
  norm_num [triple,pair,Pi.single_apply,Fin.ext_iff]
  ring

private theorem probe_47 (A : Mat) :
    directional ℝ (triple 0 3 11) (A *ᵥ triple 0 3 11)=A 6 0 + A 6 3 + A 6 11 + A 12 0 + A 12 3 + A 12 11 := by
  rw [triple_action,directional_eval]
  norm_num [triple,pair,Pi.single_apply,Fin.ext_iff]
  ring

private theorem probe_48 (A : Mat) :
    directional ℝ (triple 0 3 12) (A *ᵥ triple 0 3 12)=A 11 0 + A 11 3 + A 11 12 := by
  rw [triple_action,directional_eval]
  norm_num [triple,pair,Pi.single_apply,Fin.ext_iff]

private theorem probe_49 (A : Mat) :
    directional ℝ (triple 0 3 13) (A *ᵥ triple 0 3 13)=-A 5 0 + -A 5 3 + -A 5 13 + -A 10 0 + -A 10 3 + -A 10 13 := by
  rw [triple_action,directional_eval]
  norm_num [triple,pair,Pi.single_apply,Fin.ext_iff]
  ring

private theorem probe_50 (A : Mat) :
    directional ℝ (triple 0 3 14) (A *ᵥ triple 0 3 14)=A 9 0 + A 9 3 + A 9 14 := by
  rw [triple_action,directional_eval]
  norm_num [triple,pair,Pi.single_apply,Fin.ext_iff]

private theorem probe_51 (A : Mat) :
    directional ℝ (triple 0 4 9) (A *ᵥ triple 0 4 9)=A 7 0 + A 7 4 + A 7 9 + A 14 0 + A 14 4 + A 14 9 := by
  rw [triple_action,directional_eval]
  norm_num [triple,pair,Pi.single_apply,Fin.ext_iff]
  ring

private theorem probe_52 (A : Mat) :
    directional ℝ (triple 0 4 10) (A *ᵥ triple 0 4 10)=-A 6 0 + -A 6 4 + -A 6 10 + -A 13 0 + -A 13 4 + -A 13 10 := by
  rw [triple_action,directional_eval]
  norm_num [triple,pair,Pi.single_apply,Fin.ext_iff]
  ring

private theorem probe_53 (A : Mat) :
    directional ℝ (triple 0 4 11) (A *ᵥ triple 0 4 11)=A 12 0 + A 12 4 + A 12 11 := by
  rw [triple_action,directional_eval]
  norm_num [triple,pair,Pi.single_apply,Fin.ext_iff]

private theorem probe_54 (A : Mat) :
    directional ℝ (triple 0 4 12) (A *ᵥ triple 0 4 12)=A 5 0 + A 5 4 + A 5 12 + A 11 0 + A 11 4 + A 11 12 := by
  rw [triple_action,directional_eval]
  norm_num [triple,pair,Pi.single_apply,Fin.ext_iff]
  ring

private theorem probe_55 (A : Mat) :
    directional ℝ (triple 0 4 13) (A *ᵥ triple 0 4 13)=-A 10 0 + -A 10 4 + -A 10 13 := by
  rw [triple_action,directional_eval]
  norm_num [triple,pair,Pi.single_apply,Fin.ext_iff]
  ring

private theorem probe_56 (A : Mat) :
    directional ℝ (triple 0 4 14) (A *ᵥ triple 0 4 14)=A 9 0 + A 9 4 + A 9 14 := by
  rw [triple_action,directional_eval]
  norm_num [triple,pair,Pi.single_apply,Fin.ext_iff]

private theorem probe_57 (A : Mat) :
    directional ℝ (triple 0 5 12) (A *ᵥ triple 0 5 12)=A 4 0 + A 4 5 + A 4 12 + A 11 0 + A 11 5 + A 11 12 := by
  rw [triple_action,directional_eval]
  norm_num [triple,pair,Pi.single_apply,Fin.ext_iff]
  ring

private theorem probe_58 (A : Mat) :
    directional ℝ (triple 0 5 13) (A *ᵥ triple 0 5 13)=-A 3 0 + -A 3 5 + -A 3 13 + -A 10 0 + -A 10 5 + -A 10 13 := by
  rw [triple_action,directional_eval]
  norm_num [triple,pair,Pi.single_apply,Fin.ext_iff]
  ring

private theorem probe_59 (A : Mat) :
    directional ℝ (triple 0 5 14) (A *ᵥ triple 0 5 14)=A 2 0 + A 2 5 + A 2 14 + A 9 0 + A 9 5 + A 9 14 := by
  rw [triple_action,directional_eval]
  norm_num [triple,pair,Pi.single_apply,Fin.ext_iff]
  ring

private theorem probe_60 (A : Mat) :
    directional ℝ (triple 0 6 10) (A *ᵥ triple 0 6 10)=-A 4 0 + -A 4 6 + -A 4 10 + -A 13 0 + -A 13 6 + -A 13 10 := by
  rw [triple_action,directional_eval]
  norm_num [triple,pair,Pi.single_apply,Fin.ext_iff]
  ring

private theorem probe_61 (A : Mat) :
    directional ℝ (triple 0 6 11) (A *ᵥ triple 0 6 11)=A 3 0 + A 3 6 + A 3 11 + A 12 0 + A 12 6 + A 12 11 := by
  rw [triple_action,directional_eval]
  norm_num [triple,pair,Pi.single_apply,Fin.ext_iff]
  ring

private theorem probe_62 (A : Mat) :
    directional ℝ (triple 0 6 14) (A *ᵥ triple 0 6 14)=-A 1 0 + -A 1 6 + -A 1 14 + A 9 0 + A 9 6 + A 9 14 := by
  rw [triple_action,directional_eval]
  norm_num [triple,pair,Pi.single_apply,Fin.ext_iff]
  ring

private theorem probe_63 (A : Mat) :
    directional ℝ (triple 0 7 9) (A *ᵥ triple 0 7 9)=A 4 0 + A 4 7 + A 4 9 + A 14 0 + A 14 7 + A 14 9 := by
  rw [triple_action,directional_eval]
  norm_num [triple,pair,Pi.single_apply,Fin.ext_iff]
  ring

private theorem probe_64 (A : Mat) :
    directional ℝ (triple 0 7 11) (A *ᵥ triple 0 7 11)=-A 2 0 + -A 2 7 + -A 2 11 + A 12 0 + A 12 7 + A 12 11 := by
  rw [triple_action,directional_eval]
  norm_num [triple,pair,Pi.single_apply,Fin.ext_iff]
  ring

private theorem probe_65 (A : Mat) :
    directional ℝ (triple 0 7 13) (A *ᵥ triple 0 7 13)=A 1 0 + A 1 7 + A 1 13 + -A 10 0 + -A 10 7 + -A 10 13 := by
  rw [triple_action,directional_eval]
  norm_num [triple,pair,Pi.single_apply,Fin.ext_iff]
  ring

private theorem probe_66 (A : Mat) :
    directional ℝ (triple 0 8 9) (A *ᵥ triple 0 8 9)=-A 3 0 + -A 3 8 + -A 3 9 + A 14 0 + A 14 8 + A 14 9 := by
  rw [triple_action,directional_eval]
  norm_num [triple,pair,Pi.single_apply,Fin.ext_iff]
  ring

private theorem probe_67 (A : Mat) :
    directional ℝ (triple 0 8 10) (A *ᵥ triple 0 8 10)=A 2 0 + A 2 8 + A 2 10 + -A 13 0 + -A 13 8 + -A 13 10 := by
  rw [triple_action,directional_eval]
  norm_num [triple,pair,Pi.single_apply,Fin.ext_iff]
  ring

private theorem probe_68 (A : Mat) :
    directional ℝ (triple 0 8 12) (A *ᵥ triple 0 8 12)=-A 1 0 + -A 1 8 + -A 1 12 + A 11 0 + A 11 8 + A 11 12 := by
  rw [triple_action,directional_eval]
  norm_num [triple,pair,Pi.single_apply,Fin.ext_iff]
  ring

private theorem probe_69 (A : Mat) :
    directional ℝ (triple 0 9 10) (A *ᵥ triple 0 9 10)=-A 13 0 + -A 13 9 + -A 13 10 + A 14 0 + A 14 9 + A 14 10 := by
  rw [triple_action,directional_eval]
  norm_num [triple,pair,Pi.single_apply,Fin.ext_iff]
  ring

private theorem probe_70 (A : Mat) :
    directional ℝ (triple 0 9 11) (A *ᵥ triple 0 9 11)=A 12 0 + A 12 9 + A 12 11 + A 14 0 + A 14 9 + A 14 11 := by
  rw [triple_action,directional_eval]
  norm_num [triple,pair,Pi.single_apply,Fin.ext_iff]
  ring

private theorem probe_71 (A : Mat) :
    directional ℝ (triple 0 9 12) (A *ᵥ triple 0 9 12)=A 11 0 + A 11 9 + A 11 12 + A 14 0 + A 14 9 + A 14 12 := by
  rw [triple_action,directional_eval]
  norm_num [triple,pair,Pi.single_apply,Fin.ext_iff]
  ring

private theorem probe_72 (A : Mat) :
    directional ℝ (triple 0 9 13) (A *ᵥ triple 0 9 13)=-A 10 0 + -A 10 9 + -A 10 13 + A 14 0 + A 14 9 + A 14 13 := by
  rw [triple_action,directional_eval]
  norm_num [triple,pair,Pi.single_apply,Fin.ext_iff]
  ring

private theorem probe_73 (A : Mat) :
    directional ℝ (triple 0 10 11) (A *ᵥ triple 0 10 11)=A 12 0 + A 12 10 + A 12 11 + -A 13 0 + -A 13 10 + -A 13 11 := by
  rw [triple_action,directional_eval]
  norm_num [triple,pair,Pi.single_apply,Fin.ext_iff]
  ring

private theorem probe_74 (A : Mat) :
    directional ℝ (triple 0 10 12) (A *ᵥ triple 0 10 12)=A 11 0 + A 11 10 + A 11 12 + -A 13 0 + -A 13 10 + -A 13 12 := by
  rw [triple_action,directional_eval]
  norm_num [triple,pair,Pi.single_apply,Fin.ext_iff]
  ring

private theorem probe_75 (A : Mat) :
    directional ℝ (triple 1 2 14) (A *ᵥ triple 1 2 14)=A 5 1 + A 5 2 + A 5 14 + -A 6 1 + -A 6 2 + -A 6 14 := by
  rw [triple_action,directional_eval]
  norm_num [triple,pair,Pi.single_apply,Fin.ext_iff]
  ring

private theorem probe_76 (A : Mat) :
    directional ℝ (triple 1 3 13) (A *ᵥ triple 1 3 13)=-A 5 1 + -A 5 3 + -A 5 13 + A 7 1 + A 7 3 + A 7 13 := by
  rw [triple_action,directional_eval]
  norm_num [triple,pair,Pi.single_apply,Fin.ext_iff]
  ring

private theorem probe_77 (A : Mat) :
    directional ℝ (triple 1 4 12) (A *ᵥ triple 1 4 12)=A 5 1 + A 5 4 + A 5 12 + -A 8 1 + -A 8 4 + -A 8 12 := by
  rw [triple_action,directional_eval]
  norm_num [triple,pair,Pi.single_apply,Fin.ext_iff]
  ring

private theorem probe_78 (A : Mat) :
    directional ℝ (triple 1 5 12) (A *ᵥ triple 1 5 12)=A 4 1 + A 4 5 + A 4 12 + -A 8 1 + -A 8 5 + -A 8 12 := by
  rw [triple_action,directional_eval]
  norm_num [triple,pair,Pi.single_apply,Fin.ext_iff]
  ring

private theorem probe_79 (A : Mat) :
    directional ℝ (triple 1 5 13) (A *ᵥ triple 1 5 13)=-A 3 1 + -A 3 5 + -A 3 13 + A 7 1 + A 7 5 + A 7 13 := by
  rw [triple_action,directional_eval]
  norm_num [triple,pair,Pi.single_apply,Fin.ext_iff]
  ring

private theorem probe_80 (A : Mat) :
    directional ℝ (triple 1 5 14) (A *ᵥ triple 1 5 14)=A 2 1 + A 2 5 + A 2 14 + -A 6 1 + -A 6 5 + -A 6 14 := by
  rw [triple_action,directional_eval]
  norm_num [triple,pair,Pi.single_apply,Fin.ext_iff]
  ring

private theorem probe_81 (A : Mat) :
    directional ℝ (triple 1 6 10) (A *ᵥ triple 1 6 10)=-A 4 1 + -A 4 6 + -A 4 10 + -A 14 1 + -A 14 6 + -A 14 10 := by
  rw [triple_action,directional_eval]
  norm_num [triple,pair,Pi.single_apply,Fin.ext_iff]
  ring

private theorem probe_82 (A : Mat) :
    directional ℝ (triple 1 6 11) (A *ᵥ triple 1 6 11)=A 3 1 + A 3 6 + A 3 11 + -A 14 1 + -A 14 6 + -A 14 11 := by
  rw [triple_action,directional_eval]
  norm_num [triple,pair,Pi.single_apply,Fin.ext_iff]
  ring

private theorem probe_83 (A : Mat) :
    directional ℝ (triple 1 6 12) (A *ᵥ triple 1 6 12)=-A 8 1 + -A 8 6 + -A 8 12 + -A 14 1 + -A 14 6 + -A 14 12 := by
  rw [triple_action,directional_eval]
  norm_num [triple,pair,Pi.single_apply,Fin.ext_iff]
  ring

private theorem probe_84 (A : Mat) :
    directional ℝ (triple 1 6 13) (A *ᵥ triple 1 6 13)=A 7 1 + A 7 6 + A 7 13 + -A 14 1 + -A 14 6 + -A 14 13 := by
  rw [triple_action,directional_eval]
  norm_num [triple,pair,Pi.single_apply,Fin.ext_iff]
  ring

private theorem probe_85 (A : Mat) :
    directional ℝ (triple 1 7 11) (A *ᵥ triple 1 7 11)=-A 2 1 + -A 2 7 + -A 2 11 + A 13 1 + A 13 7 + A 13 11 := by
  rw [triple_action,directional_eval]
  norm_num [triple,pair,Pi.single_apply,Fin.ext_iff]
  ring

private theorem probe_86 (A : Mat) :
    directional ℝ (triple 1 7 12) (A *ᵥ triple 1 7 12)=-A 8 1 + -A 8 7 + -A 8 12 + A 13 1 + A 13 7 + A 13 12 := by
  rw [triple_action,directional_eval]
  norm_num [triple,pair,Pi.single_apply,Fin.ext_iff]
  ring

private theorem probe_87 (A : Mat) :
    directional ℝ (triple 2 5 12) (A *ᵥ triple 2 5 12)=A 4 2 + A 4 5 + A 4 12 + A 14 2 + A 14 5 + A 14 12 := by
  rw [triple_action,directional_eval]
  norm_num [triple,pair,Pi.single_apply,Fin.ext_iff]
  ring

private theorem probe_88 (A : Mat) :
    directional ℝ (triple 2 5 13) (A *ᵥ triple 2 5 13)=-A 3 2 + -A 3 5 + -A 3 13 + A 14 2 + A 14 5 + A 14 13 := by
  rw [triple_action,directional_eval]
  norm_num [triple,pair,Pi.single_apply,Fin.ext_iff]
  ring

private theorem probe_89 (A : Mat) :
    directional ℝ (triple 3 5 12) (A *ᵥ triple 3 5 12)=A 4 3 + A 4 5 + A 4 12 + -A 13 3 + -A 13 5 + -A 13 12 := by
  rw [triple_action,directional_eval]
  norm_num [triple,pair,Pi.single_apply,Fin.ext_iff]
  ring

theorem all_points_imply_finite (A : Mat) (hc : CubicInvariant A) : FiniteTests A :=
  fun k => hc (probe k)

theorem certificate_of_finite (A : Mat) (hm : MetricSkew A) (hf : FiniteTests A) :
    Certificate A := by
  intro k
  fin_cases k
  · have h := metric_entry A hm 0 0
    change ((1 : ℤ) : ℝ)*A 0 0+((1 : ℤ) : ℝ)*A 0 0=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change 2*A 0 0=0
    linear_combination h
  · have h := metric_entry A hm 0 1
    change ((1 : ℤ) : ℝ)*A 0 1+((1 : ℤ) : ℝ)*A 1 0=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change A 0 1 + A 1 0=0
    linear_combination h
  · have h := metric_entry A hm 0 2
    change ((1 : ℤ) : ℝ)*A 0 2+((-1 : ℤ) : ℝ)*A 2 0=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change A 0 2 + -A 2 0=0
    linear_combination h
  · have h := metric_entry A hm 0 3
    change ((1 : ℤ) : ℝ)*A 0 3+((1 : ℤ) : ℝ)*A 3 0=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change A 0 3 + A 3 0=0
    linear_combination h
  · have h := metric_entry A hm 0 4
    change ((1 : ℤ) : ℝ)*A 0 4+((-1 : ℤ) : ℝ)*A 4 0=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change A 0 4 + -A 4 0=0
    linear_combination h
  · have h := metric_entry A hm 0 5
    change ((1 : ℤ) : ℝ)*A 0 5+((1 : ℤ) : ℝ)*A 5 0=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change A 0 5 + A 5 0=0
    linear_combination h
  · have h := metric_entry A hm 0 6
    change ((1 : ℤ) : ℝ)*A 0 6+((-1 : ℤ) : ℝ)*A 6 0=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change A 0 6 + -A 6 0=0
    linear_combination h
  · have h := metric_entry A hm 0 7
    change ((1 : ℤ) : ℝ)*A 0 7+((1 : ℤ) : ℝ)*A 7 0=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change A 0 7 + A 7 0=0
    linear_combination h
  · have h := metric_entry A hm 0 8
    change ((1 : ℤ) : ℝ)*A 0 8+((-1 : ℤ) : ℝ)*A 8 0=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change A 0 8 + -A 8 0=0
    linear_combination h
  · have h := metric_entry A hm 0 9
    change ((1 : ℤ) : ℝ)*A 0 9+((-1 : ℤ) : ℝ)*A 9 0=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change A 0 9 + -A 9 0=0
    linear_combination h
  · have h := metric_entry A hm 0 10
    change ((1 : ℤ) : ℝ)*A 0 10+((1 : ℤ) : ℝ)*A 10 0=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change A 0 10 + A 10 0=0
    linear_combination h
  · have h := metric_entry A hm 0 11
    change ((1 : ℤ) : ℝ)*A 0 11+((-1 : ℤ) : ℝ)*A 11 0=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change A 0 11 + -A 11 0=0
    linear_combination h
  · have h := metric_entry A hm 0 12
    change ((1 : ℤ) : ℝ)*A 0 12+((-1 : ℤ) : ℝ)*A 12 0=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change A 0 12 + -A 12 0=0
    linear_combination h
  · have h := metric_entry A hm 0 13
    change ((1 : ℤ) : ℝ)*A 0 13+((1 : ℤ) : ℝ)*A 13 0=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change A 0 13 + A 13 0=0
    linear_combination h
  · have h := metric_entry A hm 0 14
    change ((1 : ℤ) : ℝ)*A 0 14+((-1 : ℤ) : ℝ)*A 14 0=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change A 0 14 + -A 14 0=0
    linear_combination h
  · have h := metric_entry A hm 1 1
    change ((1 : ℤ) : ℝ)*A 1 1+((1 : ℤ) : ℝ)*A 1 1=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change 2*A 1 1=0
    linear_combination h
  · have h := metric_entry A hm 1 2
    change ((1 : ℤ) : ℝ)*A 1 2+((-1 : ℤ) : ℝ)*A 2 1=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change A 1 2 + -A 2 1=0
    linear_combination h
  · have h := metric_entry A hm 1 3
    change ((1 : ℤ) : ℝ)*A 1 3+((1 : ℤ) : ℝ)*A 3 1=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change A 1 3 + A 3 1=0
    linear_combination h
  · have h := metric_entry A hm 1 4
    change ((1 : ℤ) : ℝ)*A 1 4+((-1 : ℤ) : ℝ)*A 4 1=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change A 1 4 + -A 4 1=0
    linear_combination h
  · have h := metric_entry A hm 1 5
    change ((1 : ℤ) : ℝ)*A 1 5+((1 : ℤ) : ℝ)*A 5 1=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change A 1 5 + A 5 1=0
    linear_combination h
  · have h := metric_entry A hm 1 6
    change ((1 : ℤ) : ℝ)*A 1 6+((-1 : ℤ) : ℝ)*A 6 1=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change A 1 6 + -A 6 1=0
    linear_combination h
  · have h := metric_entry A hm 1 7
    change ((1 : ℤ) : ℝ)*A 1 7+((1 : ℤ) : ℝ)*A 7 1=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change A 1 7 + A 7 1=0
    linear_combination h
  · have h := metric_entry A hm 1 8
    change ((1 : ℤ) : ℝ)*A 1 8+((-1 : ℤ) : ℝ)*A 8 1=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change A 1 8 + -A 8 1=0
    linear_combination h
  · have h := metric_entry A hm 1 9
    change ((1 : ℤ) : ℝ)*A 1 9+((-1 : ℤ) : ℝ)*A 9 1=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change A 1 9 + -A 9 1=0
    linear_combination h
  · have h := metric_entry A hm 1 10
    change ((1 : ℤ) : ℝ)*A 1 10+((1 : ℤ) : ℝ)*A 10 1=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change A 1 10 + A 10 1=0
    linear_combination h
  · have h := metric_entry A hm 1 11
    change ((1 : ℤ) : ℝ)*A 1 11+((-1 : ℤ) : ℝ)*A 11 1=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change A 1 11 + -A 11 1=0
    linear_combination h
  · have h := metric_entry A hm 1 12
    change ((1 : ℤ) : ℝ)*A 1 12+((-1 : ℤ) : ℝ)*A 12 1=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change A 1 12 + -A 12 1=0
    linear_combination h
  · have h := metric_entry A hm 1 13
    change ((1 : ℤ) : ℝ)*A 1 13+((1 : ℤ) : ℝ)*A 13 1=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change A 1 13 + A 13 1=0
    linear_combination h
  · have h := metric_entry A hm 1 14
    change ((1 : ℤ) : ℝ)*A 1 14+((-1 : ℤ) : ℝ)*A 14 1=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change A 1 14 + -A 14 1=0
    linear_combination h
  · have h := metric_entry A hm 2 2
    change ((-1 : ℤ) : ℝ)*A 2 2+((-1 : ℤ) : ℝ)*A 2 2=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change -2*A 2 2=0
    linear_combination h
  · have h := metric_entry A hm 2 3
    change ((-1 : ℤ) : ℝ)*A 2 3+((1 : ℤ) : ℝ)*A 3 2=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change -A 2 3 + A 3 2=0
    linear_combination h
  · have h := metric_entry A hm 2 4
    change ((-1 : ℤ) : ℝ)*A 2 4+((-1 : ℤ) : ℝ)*A 4 2=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change -A 2 4 + -A 4 2=0
    linear_combination h
  · have h := metric_entry A hm 2 5
    change ((-1 : ℤ) : ℝ)*A 2 5+((1 : ℤ) : ℝ)*A 5 2=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change -A 2 5 + A 5 2=0
    linear_combination h
  · have h := metric_entry A hm 2 6
    change ((-1 : ℤ) : ℝ)*A 2 6+((-1 : ℤ) : ℝ)*A 6 2=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change -A 2 6 + -A 6 2=0
    linear_combination h
  · have h := metric_entry A hm 2 7
    change ((-1 : ℤ) : ℝ)*A 2 7+((1 : ℤ) : ℝ)*A 7 2=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change -A 2 7 + A 7 2=0
    linear_combination h
  · have h := metric_entry A hm 2 8
    change ((-1 : ℤ) : ℝ)*A 2 8+((-1 : ℤ) : ℝ)*A 8 2=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change -A 2 8 + -A 8 2=0
    linear_combination h
  · have h := metric_entry A hm 2 9
    change ((-1 : ℤ) : ℝ)*A 2 9+((-1 : ℤ) : ℝ)*A 9 2=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change -A 2 9 + -A 9 2=0
    linear_combination h
  · have h := metric_entry A hm 2 10
    change ((-1 : ℤ) : ℝ)*A 2 10+((1 : ℤ) : ℝ)*A 10 2=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change -A 2 10 + A 10 2=0
    linear_combination h
  · have h := metric_entry A hm 2 11
    change ((-1 : ℤ) : ℝ)*A 2 11+((-1 : ℤ) : ℝ)*A 11 2=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change -A 2 11 + -A 11 2=0
    linear_combination h
  · have h := metric_entry A hm 2 12
    change ((-1 : ℤ) : ℝ)*A 2 12+((-1 : ℤ) : ℝ)*A 12 2=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change -A 2 12 + -A 12 2=0
    linear_combination h
  · have h := metric_entry A hm 2 13
    change ((-1 : ℤ) : ℝ)*A 2 13+((1 : ℤ) : ℝ)*A 13 2=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change -A 2 13 + A 13 2=0
    linear_combination h
  · have h := metric_entry A hm 2 14
    change ((-1 : ℤ) : ℝ)*A 2 14+((-1 : ℤ) : ℝ)*A 14 2=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change -A 2 14 + -A 14 2=0
    linear_combination h
  · have h := metric_entry A hm 3 3
    change ((1 : ℤ) : ℝ)*A 3 3+((1 : ℤ) : ℝ)*A 3 3=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change 2*A 3 3=0
    linear_combination h
  · have h := metric_entry A hm 3 4
    change ((1 : ℤ) : ℝ)*A 3 4+((-1 : ℤ) : ℝ)*A 4 3=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change A 3 4 + -A 4 3=0
    linear_combination h
  · have h := metric_entry A hm 3 5
    change ((1 : ℤ) : ℝ)*A 3 5+((1 : ℤ) : ℝ)*A 5 3=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change A 3 5 + A 5 3=0
    linear_combination h
  · have h := metric_entry A hm 3 6
    change ((1 : ℤ) : ℝ)*A 3 6+((-1 : ℤ) : ℝ)*A 6 3=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change A 3 6 + -A 6 3=0
    linear_combination h
  · have h := metric_entry A hm 3 7
    change ((1 : ℤ) : ℝ)*A 3 7+((1 : ℤ) : ℝ)*A 7 3=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change A 3 7 + A 7 3=0
    linear_combination h
  · have h := metric_entry A hm 3 8
    change ((1 : ℤ) : ℝ)*A 3 8+((-1 : ℤ) : ℝ)*A 8 3=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change A 3 8 + -A 8 3=0
    linear_combination h
  · have h := metric_entry A hm 3 9
    change ((1 : ℤ) : ℝ)*A 3 9+((-1 : ℤ) : ℝ)*A 9 3=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change A 3 9 + -A 9 3=0
    linear_combination h
  · have h := metric_entry A hm 3 10
    change ((1 : ℤ) : ℝ)*A 3 10+((1 : ℤ) : ℝ)*A 10 3=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change A 3 10 + A 10 3=0
    linear_combination h
  · have h := metric_entry A hm 3 11
    change ((1 : ℤ) : ℝ)*A 3 11+((-1 : ℤ) : ℝ)*A 11 3=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change A 3 11 + -A 11 3=0
    linear_combination h
  · have h := metric_entry A hm 3 12
    change ((1 : ℤ) : ℝ)*A 3 12+((-1 : ℤ) : ℝ)*A 12 3=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change A 3 12 + -A 12 3=0
    linear_combination h
  · have h := metric_entry A hm 3 13
    change ((1 : ℤ) : ℝ)*A 3 13+((1 : ℤ) : ℝ)*A 13 3=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change A 3 13 + A 13 3=0
    linear_combination h
  · have h := metric_entry A hm 3 14
    change ((1 : ℤ) : ℝ)*A 3 14+((-1 : ℤ) : ℝ)*A 14 3=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change A 3 14 + -A 14 3=0
    linear_combination h
  · have h := metric_entry A hm 4 4
    change ((-1 : ℤ) : ℝ)*A 4 4+((-1 : ℤ) : ℝ)*A 4 4=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change -2*A 4 4=0
    linear_combination h
  · have h := metric_entry A hm 4 5
    change ((-1 : ℤ) : ℝ)*A 4 5+((1 : ℤ) : ℝ)*A 5 4=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change -A 4 5 + A 5 4=0
    linear_combination h
  · have h := metric_entry A hm 4 6
    change ((-1 : ℤ) : ℝ)*A 4 6+((-1 : ℤ) : ℝ)*A 6 4=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change -A 4 6 + -A 6 4=0
    linear_combination h
  · have h := metric_entry A hm 4 7
    change ((-1 : ℤ) : ℝ)*A 4 7+((1 : ℤ) : ℝ)*A 7 4=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change -A 4 7 + A 7 4=0
    linear_combination h
  · have h := metric_entry A hm 4 8
    change ((-1 : ℤ) : ℝ)*A 4 8+((-1 : ℤ) : ℝ)*A 8 4=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change -A 4 8 + -A 8 4=0
    linear_combination h
  · have h := metric_entry A hm 4 9
    change ((-1 : ℤ) : ℝ)*A 4 9+((-1 : ℤ) : ℝ)*A 9 4=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change -A 4 9 + -A 9 4=0
    linear_combination h
  · have h := metric_entry A hm 4 10
    change ((-1 : ℤ) : ℝ)*A 4 10+((1 : ℤ) : ℝ)*A 10 4=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change -A 4 10 + A 10 4=0
    linear_combination h
  · have h := metric_entry A hm 4 11
    change ((-1 : ℤ) : ℝ)*A 4 11+((-1 : ℤ) : ℝ)*A 11 4=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change -A 4 11 + -A 11 4=0
    linear_combination h
  · have h := metric_entry A hm 4 12
    change ((-1 : ℤ) : ℝ)*A 4 12+((-1 : ℤ) : ℝ)*A 12 4=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change -A 4 12 + -A 12 4=0
    linear_combination h
  · have h := metric_entry A hm 4 13
    change ((-1 : ℤ) : ℝ)*A 4 13+((1 : ℤ) : ℝ)*A 13 4=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change -A 4 13 + A 13 4=0
    linear_combination h
  · have h := metric_entry A hm 4 14
    change ((-1 : ℤ) : ℝ)*A 4 14+((-1 : ℤ) : ℝ)*A 14 4=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change -A 4 14 + -A 14 4=0
    linear_combination h
  · have h := metric_entry A hm 5 5
    change ((1 : ℤ) : ℝ)*A 5 5+((1 : ℤ) : ℝ)*A 5 5=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change 2*A 5 5=0
    linear_combination h
  · have h := metric_entry A hm 5 6
    change ((1 : ℤ) : ℝ)*A 5 6+((-1 : ℤ) : ℝ)*A 6 5=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change A 5 6 + -A 6 5=0
    linear_combination h
  · have h := metric_entry A hm 5 7
    change ((1 : ℤ) : ℝ)*A 5 7+((1 : ℤ) : ℝ)*A 7 5=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change A 5 7 + A 7 5=0
    linear_combination h
  · have h := metric_entry A hm 5 8
    change ((1 : ℤ) : ℝ)*A 5 8+((-1 : ℤ) : ℝ)*A 8 5=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change A 5 8 + -A 8 5=0
    linear_combination h
  · have h := metric_entry A hm 5 9
    change ((1 : ℤ) : ℝ)*A 5 9+((-1 : ℤ) : ℝ)*A 9 5=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change A 5 9 + -A 9 5=0
    linear_combination h
  · have h := metric_entry A hm 5 10
    change ((1 : ℤ) : ℝ)*A 5 10+((1 : ℤ) : ℝ)*A 10 5=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change A 5 10 + A 10 5=0
    linear_combination h
  · have h := metric_entry A hm 5 11
    change ((1 : ℤ) : ℝ)*A 5 11+((-1 : ℤ) : ℝ)*A 11 5=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change A 5 11 + -A 11 5=0
    linear_combination h
  · have h := metric_entry A hm 5 12
    change ((1 : ℤ) : ℝ)*A 5 12+((-1 : ℤ) : ℝ)*A 12 5=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change A 5 12 + -A 12 5=0
    linear_combination h
  · have h := metric_entry A hm 5 13
    change ((1 : ℤ) : ℝ)*A 5 13+((1 : ℤ) : ℝ)*A 13 5=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change A 5 13 + A 13 5=0
    linear_combination h
  · have h := metric_entry A hm 5 14
    change ((1 : ℤ) : ℝ)*A 5 14+((-1 : ℤ) : ℝ)*A 14 5=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change A 5 14 + -A 14 5=0
    linear_combination h
  · have h := metric_entry A hm 6 6
    change ((-1 : ℤ) : ℝ)*A 6 6+((-1 : ℤ) : ℝ)*A 6 6=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change -2*A 6 6=0
    linear_combination h
  · have h := metric_entry A hm 6 7
    change ((-1 : ℤ) : ℝ)*A 6 7+((1 : ℤ) : ℝ)*A 7 6=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change -A 6 7 + A 7 6=0
    linear_combination h
  · have h := metric_entry A hm 6 8
    change ((-1 : ℤ) : ℝ)*A 6 8+((-1 : ℤ) : ℝ)*A 8 6=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change -A 6 8 + -A 8 6=0
    linear_combination h
  · have h := metric_entry A hm 6 9
    change ((-1 : ℤ) : ℝ)*A 6 9+((-1 : ℤ) : ℝ)*A 9 6=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change -A 6 9 + -A 9 6=0
    linear_combination h
  · have h := metric_entry A hm 6 10
    change ((-1 : ℤ) : ℝ)*A 6 10+((1 : ℤ) : ℝ)*A 10 6=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change -A 6 10 + A 10 6=0
    linear_combination h
  · have h := metric_entry A hm 6 11
    change ((-1 : ℤ) : ℝ)*A 6 11+((-1 : ℤ) : ℝ)*A 11 6=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change -A 6 11 + -A 11 6=0
    linear_combination h
  · have h := metric_entry A hm 6 12
    change ((-1 : ℤ) : ℝ)*A 6 12+((-1 : ℤ) : ℝ)*A 12 6=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change -A 6 12 + -A 12 6=0
    linear_combination h
  · have h := metric_entry A hm 6 13
    change ((-1 : ℤ) : ℝ)*A 6 13+((1 : ℤ) : ℝ)*A 13 6=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change -A 6 13 + A 13 6=0
    linear_combination h
  · have h := metric_entry A hm 6 14
    change ((-1 : ℤ) : ℝ)*A 6 14+((-1 : ℤ) : ℝ)*A 14 6=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change -A 6 14 + -A 14 6=0
    linear_combination h
  · have h := metric_entry A hm 7 7
    change ((1 : ℤ) : ℝ)*A 7 7+((1 : ℤ) : ℝ)*A 7 7=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change 2*A 7 7=0
    linear_combination h
  · have h := metric_entry A hm 7 8
    change ((1 : ℤ) : ℝ)*A 7 8+((-1 : ℤ) : ℝ)*A 8 7=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change A 7 8 + -A 8 7=0
    linear_combination h
  · have h := metric_entry A hm 7 9
    change ((1 : ℤ) : ℝ)*A 7 9+((-1 : ℤ) : ℝ)*A 9 7=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change A 7 9 + -A 9 7=0
    linear_combination h
  · have h := metric_entry A hm 7 10
    change ((1 : ℤ) : ℝ)*A 7 10+((1 : ℤ) : ℝ)*A 10 7=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change A 7 10 + A 10 7=0
    linear_combination h
  · have h := metric_entry A hm 7 11
    change ((1 : ℤ) : ℝ)*A 7 11+((-1 : ℤ) : ℝ)*A 11 7=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change A 7 11 + -A 11 7=0
    linear_combination h
  · have h := metric_entry A hm 7 12
    change ((1 : ℤ) : ℝ)*A 7 12+((-1 : ℤ) : ℝ)*A 12 7=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change A 7 12 + -A 12 7=0
    linear_combination h
  · have h := metric_entry A hm 7 13
    change ((1 : ℤ) : ℝ)*A 7 13+((1 : ℤ) : ℝ)*A 13 7=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change A 7 13 + A 13 7=0
    linear_combination h
  · have h := metric_entry A hm 7 14
    change ((1 : ℤ) : ℝ)*A 7 14+((-1 : ℤ) : ℝ)*A 14 7=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change A 7 14 + -A 14 7=0
    linear_combination h
  · have h := metric_entry A hm 8 8
    change ((-1 : ℤ) : ℝ)*A 8 8+((-1 : ℤ) : ℝ)*A 8 8=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change -2*A 8 8=0
    linear_combination h
  · have h := metric_entry A hm 8 9
    change ((-1 : ℤ) : ℝ)*A 8 9+((-1 : ℤ) : ℝ)*A 9 8=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change -A 8 9 + -A 9 8=0
    linear_combination h
  · have h := metric_entry A hm 8 10
    change ((-1 : ℤ) : ℝ)*A 8 10+((1 : ℤ) : ℝ)*A 10 8=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change -A 8 10 + A 10 8=0
    linear_combination h
  · have h := metric_entry A hm 8 11
    change ((-1 : ℤ) : ℝ)*A 8 11+((-1 : ℤ) : ℝ)*A 11 8=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change -A 8 11 + -A 11 8=0
    linear_combination h
  · have h := metric_entry A hm 8 12
    change ((-1 : ℤ) : ℝ)*A 8 12+((-1 : ℤ) : ℝ)*A 12 8=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change -A 8 12 + -A 12 8=0
    linear_combination h
  · have h := metric_entry A hm 8 13
    change ((-1 : ℤ) : ℝ)*A 8 13+((1 : ℤ) : ℝ)*A 13 8=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change -A 8 13 + A 13 8=0
    linear_combination h
  · have h := metric_entry A hm 8 14
    change ((-1 : ℤ) : ℝ)*A 8 14+((-1 : ℤ) : ℝ)*A 14 8=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change -A 8 14 + -A 14 8=0
    linear_combination h
  · have h := metric_entry A hm 9 9
    change ((-1 : ℤ) : ℝ)*A 9 9+((-1 : ℤ) : ℝ)*A 9 9=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change -2*A 9 9=0
    linear_combination h
  · have h := metric_entry A hm 9 10
    change ((-1 : ℤ) : ℝ)*A 9 10+((1 : ℤ) : ℝ)*A 10 9=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change -A 9 10 + A 10 9=0
    linear_combination h
  · have h := metric_entry A hm 9 11
    change ((-1 : ℤ) : ℝ)*A 9 11+((-1 : ℤ) : ℝ)*A 11 9=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change -A 9 11 + -A 11 9=0
    linear_combination h
  · have h := metric_entry A hm 9 12
    change ((-1 : ℤ) : ℝ)*A 9 12+((-1 : ℤ) : ℝ)*A 12 9=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change -A 9 12 + -A 12 9=0
    linear_combination h
  · have h := metric_entry A hm 9 13
    change ((-1 : ℤ) : ℝ)*A 9 13+((1 : ℤ) : ℝ)*A 13 9=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change -A 9 13 + A 13 9=0
    linear_combination h
  · have h := metric_entry A hm 9 14
    change ((-1 : ℤ) : ℝ)*A 9 14+((-1 : ℤ) : ℝ)*A 14 9=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change -A 9 14 + -A 14 9=0
    linear_combination h
  · have h := metric_entry A hm 10 10
    change ((1 : ℤ) : ℝ)*A 10 10+((1 : ℤ) : ℝ)*A 10 10=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change 2*A 10 10=0
    linear_combination h
  · have h := metric_entry A hm 10 11
    change ((1 : ℤ) : ℝ)*A 10 11+((-1 : ℤ) : ℝ)*A 11 10=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change A 10 11 + -A 11 10=0
    linear_combination h
  · have h := metric_entry A hm 10 12
    change ((1 : ℤ) : ℝ)*A 10 12+((-1 : ℤ) : ℝ)*A 12 10=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change A 10 12 + -A 12 10=0
    linear_combination h
  · have h := metric_entry A hm 10 13
    change ((1 : ℤ) : ℝ)*A 10 13+((1 : ℤ) : ℝ)*A 13 10=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change A 10 13 + A 13 10=0
    linear_combination h
  · have h := metric_entry A hm 10 14
    change ((1 : ℤ) : ℝ)*A 10 14+((-1 : ℤ) : ℝ)*A 14 10=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change A 10 14 + -A 14 10=0
    linear_combination h
  · have h := metric_entry A hm 11 11
    change ((-1 : ℤ) : ℝ)*A 11 11+((-1 : ℤ) : ℝ)*A 11 11=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change -2*A 11 11=0
    linear_combination h
  · have h := metric_entry A hm 11 12
    change ((-1 : ℤ) : ℝ)*A 11 12+((-1 : ℤ) : ℝ)*A 12 11=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change -A 11 12 + -A 12 11=0
    linear_combination h
  · have h := metric_entry A hm 11 13
    change ((-1 : ℤ) : ℝ)*A 11 13+((1 : ℤ) : ℝ)*A 13 11=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change -A 11 13 + A 13 11=0
    linear_combination h
  · have h := metric_entry A hm 11 14
    change ((-1 : ℤ) : ℝ)*A 11 14+((-1 : ℤ) : ℝ)*A 14 11=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change -A 11 14 + -A 14 11=0
    linear_combination h
  · have h := metric_entry A hm 12 12
    change ((-1 : ℤ) : ℝ)*A 12 12+((-1 : ℤ) : ℝ)*A 12 12=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change -2*A 12 12=0
    linear_combination h
  · have h := metric_entry A hm 12 13
    change ((-1 : ℤ) : ℝ)*A 12 13+((1 : ℤ) : ℝ)*A 13 12=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change -A 12 13 + A 13 12=0
    linear_combination h
  · have h := metric_entry A hm 12 14
    change ((-1 : ℤ) : ℝ)*A 12 14+((-1 : ℤ) : ℝ)*A 14 12=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change -A 12 14 + -A 14 12=0
    linear_combination h
  · have h := metric_entry A hm 13 13
    change ((1 : ℤ) : ℝ)*A 13 13+((1 : ℤ) : ℝ)*A 13 13=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change 2*A 13 13=0
    linear_combination h
  · have h := metric_entry A hm 13 14
    change ((1 : ℤ) : ℝ)*A 13 14+((-1 : ℤ) : ℝ)*A 14 13=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change A 13 14 + -A 14 13=0
    linear_combination h
  · have h := metric_entry A hm 14 14
    change ((-1 : ℤ) : ℝ)*A 14 14+((-1 : ℤ) : ℝ)*A 14 14=0 at h
    norm_num only [Int.cast_neg,Int.cast_one] at h
    change -2*A 14 14=0
    linear_combination h
  · have h := hf 0
    change directional ℝ (pair 0 9)
      (A *ᵥ pair 0 9)=0 at h
    rw [probe_00] at h
    exact h
  · have h := hf 1
    change directional ℝ (pair 0 10)
      (A *ᵥ pair 0 10)=0 at h
    rw [probe_01] at h
    exact h
  · have h := hf 2
    change directional ℝ (pair 0 11)
      (A *ᵥ pair 0 11)=0 at h
    rw [probe_02] at h
    exact h
  · have h := hf 3
    change directional ℝ (pair 0 12)
      (A *ᵥ pair 0 12)=0 at h
    rw [probe_03] at h
    exact h
  · have h := hf 4
    change directional ℝ (pair 0 13)
      (A *ᵥ pair 0 13)=0 at h
    rw [probe_04] at h
    exact h
  · have h := hf 5
    change directional ℝ (pair 0 14)
      (A *ᵥ pair 0 14)=0 at h
    rw [probe_05] at h
    exact h
  · have h := hf 6
    change directional ℝ (pair 1 6)
      (A *ᵥ pair 1 6)=0 at h
    rw [probe_06] at h
    exact h
  · have h := hf 7
    change directional ℝ (pair 1 7)
      (A *ᵥ pair 1 7)=0 at h
    rw [probe_07] at h
    exact h
  · have h := hf 8
    change directional ℝ (pair 1 8)
      (A *ᵥ pair 1 8)=0 at h
    rw [probe_08] at h
    exact h
  · have h := hf 9
    change directional ℝ (pair 1 12)
      (A *ᵥ pair 1 12)=0 at h
    rw [probe_09] at h
    exact h
  · have h := hf 10
    change directional ℝ (pair 1 13)
      (A *ᵥ pair 1 13)=0 at h
    rw [probe_10] at h
    exact h
  · have h := hf 11
    change directional ℝ (pair 1 14)
      (A *ᵥ pair 1 14)=0 at h
    rw [probe_11] at h
    exact h
  · have h := hf 12
    change directional ℝ (pair 2 5)
      (A *ᵥ pair 2 5)=0 at h
    rw [probe_12] at h
    exact h
  · have h := hf 13
    change directional ℝ (pair 2 7)
      (A *ᵥ pair 2 7)=0 at h
    rw [probe_13] at h
    exact h
  · have h := hf 14
    change directional ℝ (pair 2 8)
      (A *ᵥ pair 2 8)=0 at h
    rw [probe_14] at h
    exact h
  · have h := hf 15
    change directional ℝ (pair 2 10)
      (A *ᵥ pair 2 10)=0 at h
    rw [probe_15] at h
    exact h
  · have h := hf 16
    change directional ℝ (pair 2 11)
      (A *ᵥ pair 2 11)=0 at h
    rw [probe_16] at h
    exact h
  · have h := hf 17
    change directional ℝ (pair 2 14)
      (A *ᵥ pair 2 14)=0 at h
    rw [probe_17] at h
    exact h
  · have h := hf 18
    change directional ℝ (pair 3 5)
      (A *ᵥ pair 3 5)=0 at h
    rw [probe_18] at h
    exact h
  · have h := hf 19
    change directional ℝ (pair 3 6)
      (A *ᵥ pair 3 6)=0 at h
    rw [probe_19] at h
    exact h
  · have h := hf 20
    change directional ℝ (pair 3 8)
      (A *ᵥ pair 3 8)=0 at h
    rw [probe_20] at h
    exact h
  · have h := hf 21
    change directional ℝ (pair 3 9)
      (A *ᵥ pair 3 9)=0 at h
    rw [probe_21] at h
    exact h
  · have h := hf 22
    change directional ℝ (pair 3 11)
      (A *ᵥ pair 3 11)=0 at h
    rw [probe_22] at h
    exact h
  · have h := hf 23
    change directional ℝ (pair 3 13)
      (A *ᵥ pair 3 13)=0 at h
    rw [probe_23] at h
    exact h
  · have h := hf 24
    change directional ℝ (pair 4 5)
      (A *ᵥ pair 4 5)=0 at h
    rw [probe_24] at h
    exact h
  · have h := hf 25
    change directional ℝ (pair 4 6)
      (A *ᵥ pair 4 6)=0 at h
    rw [probe_25] at h
    exact h
  · have h := hf 26
    change directional ℝ (pair 4 7)
      (A *ᵥ pair 4 7)=0 at h
    rw [probe_26] at h
    exact h
  · have h := hf 27
    change directional ℝ (pair 4 9)
      (A *ᵥ pair 4 9)=0 at h
    rw [probe_27] at h
    exact h
  · have h := hf 28
    change directional ℝ (pair 4 10)
      (A *ᵥ pair 4 10)=0 at h
    rw [probe_28] at h
    exact h
  · have h := hf 29
    change directional ℝ (pair 4 12)
      (A *ᵥ pair 4 12)=0 at h
    rw [probe_29] at h
    exact h
  · have h := hf 30
    change directional ℝ (triple 0 1 6)
      (A *ᵥ triple 0 1 6)=0 at h
    rw [probe_30] at h
    exact h
  · have h := hf 31
    change directional ℝ (triple 0 1 7)
      (A *ᵥ triple 0 1 7)=0 at h
    rw [probe_31] at h
    exact h
  · have h := hf 32
    change directional ℝ (triple 0 1 8)
      (A *ᵥ triple 0 1 8)=0 at h
    rw [probe_32] at h
    exact h
  · have h := hf 33
    change directional ℝ (triple 0 1 9)
      (A *ᵥ triple 0 1 9)=0 at h
    rw [probe_33] at h
    exact h
  · have h := hf 34
    change directional ℝ (triple 0 1 10)
      (A *ᵥ triple 0 1 10)=0 at h
    rw [probe_34] at h
    exact h
  · have h := hf 35
    change directional ℝ (triple 0 1 11)
      (A *ᵥ triple 0 1 11)=0 at h
    rw [probe_35] at h
    exact h
  · have h := hf 36
    change directional ℝ (triple 0 1 12)
      (A *ᵥ triple 0 1 12)=0 at h
    rw [probe_36] at h
    exact h
  · have h := hf 37
    change directional ℝ (triple 0 1 13)
      (A *ᵥ triple 0 1 13)=0 at h
    rw [probe_37] at h
    exact h
  · have h := hf 38
    change directional ℝ (triple 0 1 14)
      (A *ᵥ triple 0 1 14)=0 at h
    rw [probe_38] at h
    exact h
  · have h := hf 39
    change directional ℝ (triple 0 2 9)
      (A *ᵥ triple 0 2 9)=0 at h
    rw [probe_39] at h
    exact h
  · have h := hf 40
    change directional ℝ (triple 0 2 10)
      (A *ᵥ triple 0 2 10)=0 at h
    rw [probe_40] at h
    exact h
  · have h := hf 41
    change directional ℝ (triple 0 2 11)
      (A *ᵥ triple 0 2 11)=0 at h
    rw [probe_41] at h
    exact h
  · have h := hf 42
    change directional ℝ (triple 0 2 12)
      (A *ᵥ triple 0 2 12)=0 at h
    rw [probe_42] at h
    exact h
  · have h := hf 43
    change directional ℝ (triple 0 2 13)
      (A *ᵥ triple 0 2 13)=0 at h
    rw [probe_43] at h
    exact h
  · have h := hf 44
    change directional ℝ (triple 0 2 14)
      (A *ᵥ triple 0 2 14)=0 at h
    rw [probe_44] at h
    exact h
  · have h := hf 45
    change directional ℝ (triple 0 3 9)
      (A *ᵥ triple 0 3 9)=0 at h
    rw [probe_45] at h
    exact h
  · have h := hf 46
    change directional ℝ (triple 0 3 10)
      (A *ᵥ triple 0 3 10)=0 at h
    rw [probe_46] at h
    exact h
  · have h := hf 47
    change directional ℝ (triple 0 3 11)
      (A *ᵥ triple 0 3 11)=0 at h
    rw [probe_47] at h
    exact h
  · have h := hf 48
    change directional ℝ (triple 0 3 12)
      (A *ᵥ triple 0 3 12)=0 at h
    rw [probe_48] at h
    exact h
  · have h := hf 49
    change directional ℝ (triple 0 3 13)
      (A *ᵥ triple 0 3 13)=0 at h
    rw [probe_49] at h
    exact h
  · have h := hf 50
    change directional ℝ (triple 0 3 14)
      (A *ᵥ triple 0 3 14)=0 at h
    rw [probe_50] at h
    exact h
  · have h := hf 51
    change directional ℝ (triple 0 4 9)
      (A *ᵥ triple 0 4 9)=0 at h
    rw [probe_51] at h
    exact h
  · have h := hf 52
    change directional ℝ (triple 0 4 10)
      (A *ᵥ triple 0 4 10)=0 at h
    rw [probe_52] at h
    exact h
  · have h := hf 53
    change directional ℝ (triple 0 4 11)
      (A *ᵥ triple 0 4 11)=0 at h
    rw [probe_53] at h
    exact h
  · have h := hf 54
    change directional ℝ (triple 0 4 12)
      (A *ᵥ triple 0 4 12)=0 at h
    rw [probe_54] at h
    exact h
  · have h := hf 55
    change directional ℝ (triple 0 4 13)
      (A *ᵥ triple 0 4 13)=0 at h
    rw [probe_55] at h
    exact h
  · have h := hf 56
    change directional ℝ (triple 0 4 14)
      (A *ᵥ triple 0 4 14)=0 at h
    rw [probe_56] at h
    exact h
  · have h := hf 57
    change directional ℝ (triple 0 5 12)
      (A *ᵥ triple 0 5 12)=0 at h
    rw [probe_57] at h
    exact h
  · have h := hf 58
    change directional ℝ (triple 0 5 13)
      (A *ᵥ triple 0 5 13)=0 at h
    rw [probe_58] at h
    exact h
  · have h := hf 59
    change directional ℝ (triple 0 5 14)
      (A *ᵥ triple 0 5 14)=0 at h
    rw [probe_59] at h
    exact h
  · have h := hf 60
    change directional ℝ (triple 0 6 10)
      (A *ᵥ triple 0 6 10)=0 at h
    rw [probe_60] at h
    exact h
  · have h := hf 61
    change directional ℝ (triple 0 6 11)
      (A *ᵥ triple 0 6 11)=0 at h
    rw [probe_61] at h
    exact h
  · have h := hf 62
    change directional ℝ (triple 0 6 14)
      (A *ᵥ triple 0 6 14)=0 at h
    rw [probe_62] at h
    exact h
  · have h := hf 63
    change directional ℝ (triple 0 7 9)
      (A *ᵥ triple 0 7 9)=0 at h
    rw [probe_63] at h
    exact h
  · have h := hf 64
    change directional ℝ (triple 0 7 11)
      (A *ᵥ triple 0 7 11)=0 at h
    rw [probe_64] at h
    exact h
  · have h := hf 65
    change directional ℝ (triple 0 7 13)
      (A *ᵥ triple 0 7 13)=0 at h
    rw [probe_65] at h
    exact h
  · have h := hf 66
    change directional ℝ (triple 0 8 9)
      (A *ᵥ triple 0 8 9)=0 at h
    rw [probe_66] at h
    exact h
  · have h := hf 67
    change directional ℝ (triple 0 8 10)
      (A *ᵥ triple 0 8 10)=0 at h
    rw [probe_67] at h
    exact h
  · have h := hf 68
    change directional ℝ (triple 0 8 12)
      (A *ᵥ triple 0 8 12)=0 at h
    rw [probe_68] at h
    exact h
  · have h := hf 69
    change directional ℝ (triple 0 9 10)
      (A *ᵥ triple 0 9 10)=0 at h
    rw [probe_69] at h
    exact h
  · have h := hf 70
    change directional ℝ (triple 0 9 11)
      (A *ᵥ triple 0 9 11)=0 at h
    rw [probe_70] at h
    exact h
  · have h := hf 71
    change directional ℝ (triple 0 9 12)
      (A *ᵥ triple 0 9 12)=0 at h
    rw [probe_71] at h
    exact h
  · have h := hf 72
    change directional ℝ (triple 0 9 13)
      (A *ᵥ triple 0 9 13)=0 at h
    rw [probe_72] at h
    exact h
  · have h := hf 73
    change directional ℝ (triple 0 10 11)
      (A *ᵥ triple 0 10 11)=0 at h
    rw [probe_73] at h
    exact h
  · have h := hf 74
    change directional ℝ (triple 0 10 12)
      (A *ᵥ triple 0 10 12)=0 at h
    rw [probe_74] at h
    exact h
  · have h := hf 75
    change directional ℝ (triple 1 2 14)
      (A *ᵥ triple 1 2 14)=0 at h
    rw [probe_75] at h
    exact h
  · have h := hf 76
    change directional ℝ (triple 1 3 13)
      (A *ᵥ triple 1 3 13)=0 at h
    rw [probe_76] at h
    exact h
  · have h := hf 77
    change directional ℝ (triple 1 4 12)
      (A *ᵥ triple 1 4 12)=0 at h
    rw [probe_77] at h
    exact h
  · have h := hf 78
    change directional ℝ (triple 1 5 12)
      (A *ᵥ triple 1 5 12)=0 at h
    rw [probe_78] at h
    exact h
  · have h := hf 79
    change directional ℝ (triple 1 5 13)
      (A *ᵥ triple 1 5 13)=0 at h
    rw [probe_79] at h
    exact h
  · have h := hf 80
    change directional ℝ (triple 1 5 14)
      (A *ᵥ triple 1 5 14)=0 at h
    rw [probe_80] at h
    exact h
  · have h := hf 81
    change directional ℝ (triple 1 6 10)
      (A *ᵥ triple 1 6 10)=0 at h
    rw [probe_81] at h
    exact h
  · have h := hf 82
    change directional ℝ (triple 1 6 11)
      (A *ᵥ triple 1 6 11)=0 at h
    rw [probe_82] at h
    exact h
  · have h := hf 83
    change directional ℝ (triple 1 6 12)
      (A *ᵥ triple 1 6 12)=0 at h
    rw [probe_83] at h
    exact h
  · have h := hf 84
    change directional ℝ (triple 1 6 13)
      (A *ᵥ triple 1 6 13)=0 at h
    rw [probe_84] at h
    exact h
  · have h := hf 85
    change directional ℝ (triple 1 7 11)
      (A *ᵥ triple 1 7 11)=0 at h
    rw [probe_85] at h
    exact h
  · have h := hf 86
    change directional ℝ (triple 1 7 12)
      (A *ᵥ triple 1 7 12)=0 at h
    rw [probe_86] at h
    exact h
  · have h := hf 87
    change directional ℝ (triple 2 5 12)
      (A *ᵥ triple 2 5 12)=0 at h
    rw [probe_87] at h
    exact h
  · have h := hf 88
    change directional ℝ (triple 2 5 13)
      (A *ᵥ triple 2 5 13)=0 at h
    rw [probe_88] at h
    exact h
  · have h := hf 89
    change directional ℝ (triple 3 5 12)
      (A *ᵥ triple 3 5 12)=0 at h
    rw [probe_89] at h
    exact h

private theorem coefficients_match : ∀ p r c : I,
    adj p r c=PDTCubicInvariance.coefficients p r c := by
  decide +kernel

theorem generator_entry (p r c : I) : generator ℝ p r c=
    (PDTCubicInvariance.coefficients p r c : ℝ) := by
  change (geometricAdjoint p r c : ℝ)= _
  rw [← certificate_adjoint,coefficients_match]

#print axioms metric_entry
#print axioms all_points_imply_finite
#print axioms certificate_of_finite
#print axioms generator_entry
end
end PDTStabilizerTests
