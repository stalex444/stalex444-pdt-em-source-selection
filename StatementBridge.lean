module
public import SourceSelection
public import SourceControls
public import ConservationConsequences
public import SmoothConsequences
public import DifferentiableSourceful

@[expose] public section
set_option backward.isDefEq.respectTransparency false
/-! Statement bridge: the Challenge definitions, restated verbatim, and the proofs that each
compared statement follows from the research modules. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 30000
namespace PDTSourceSelection
noncomputable section
open scoped Matrix

abbrev Local := Fin 6 → ℝ
abbrev Four := Fin 4 → ℝ
abbrev Tensor := Matrix (Fin 4) (Fin 4) ℝ
abbrev Register := Fin 15 → ℝ

/-- Minkowski pairing of two 4-vectors, signature (+,+,+,−). -/
def mink (a b : Four) : ℝ :=
  a 0*b 0 + a 1*b 1 + a 2*b 2 - a 3*b 3
def eta : Four := ![1,1,1,-1]
def metric : Tensor := Matrix.diagonal eta
/-- The six field components placed in the bivector register (slots 01,02,03,12,13,23). -/
def embed (x : Local) : Register :=
  ![x 0,x 1,x 2,0,0,x 3,x 4,0,0,x 5,0,0,0,0,0]
/-- The antisymmetric field tensor read from the register. -/
def field (v : Register) : Tensor :=
  !![0, v 0, v 1, v 2;
     -v 0, 0, v 5, v 6;
     -v 1, -v 5, 0, v 9;
     -v 2, -v 6, -v 9, 0]
def invariant (F : Tensor) : ℝ :=
  mink (F 0) (F 0)+mink (F 1) (F 1)+mink (F 2) (F 2)-mink (F 3) (F 3)
/-- The Maxwell stress of scale d. -/
def stress (d : ℝ) (F : Tensor) : Tensor := fun μ ν =>
  d*(mink (F μ) (F ν)-metric μ ν*invariant F/4)
def registerStress (d : ℝ) (v : Register) : Tensor := stress d (field v)

/-! ## Quadratic sources: all 210 coefficients -/
abbrev Coeff := Fin 10 → Fin 21 → ℝ
def monomialPair : Fin 21 → Fin 6 × Fin 6 :=
  ![(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),
    (1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,3),(2,4),(2,5),
    (3,3),(3,4),(3,5),(4,4),(4,5),(5,5)]
def tensorIndex : Fin 4 → Fin 4 → Fin 10 :=
  !![0,1,2,3;1,4,5,6;2,5,7,8;3,6,8,9]
def poly (c : Fin 21 → ℝ) (x : Local) : ℝ :=
  ∑ m, c m * x (monomialPair m).1 * x (monomialPair m).2
def source (c : Coeff) (x : Local) : Tensor := fun i j => poly (c (tensorIndex i j)) x
def IsQuadraticSource (S : Local → Tensor) : Prop := ∃ c : Coeff, S=source c

/-! ## The six Lorentz generators and the two laws -/
def lorentzTable : Fin 6 → Matrix (Fin 4) (Fin 4) ℤ :=
  ![!![0,1,0,0;-1,0,0,0;0,0,0,0;0,0,0,0],
    !![0,0,1,0;0,0,0,0;-1,0,0,0;0,0,0,0],
    !![0,0,0,-1;0,0,0,0;0,0,0,0;-1,0,0,0],
    !![0,0,0,0;0,0,1,0;0,-1,0,0;0,0,0,0],
    !![0,0,0,0;0,0,0,-1;0,0,0,0;0,-1,0,0],
    !![0,0,0,0;0,0,0,0;0,0,0,-1;0,0,-1,0]]
def lorentzGenerator (k : Fin 6) : Tensor := fun i j => (lorentzTable k i j : ℝ)
/-- Infinitesimal action of generator k on the six field components. -/
def fieldAction (k : Fin 6) (x : Local) : Local :=
  ![![0,1 * x 3,1 * x 4,(-1) * x 1,(-1) * x 2,0],
    ![(-1) * x 3,0,1 * x 5,1 * x 0,0,(-1) * x 2],
    ![1 * x 4,1 * x 5,0,0,1 * x 0,1 * x 1],
    ![1 * x 1,(-1) * x 0,0,0,1 * x 5,(-1) * x 4],
    ![(-1) * x 2,0,(-1) * x 0,1 * x 5,0,1 * x 3],
    ![0,(-1) * x 2,(-1) * x 1,(-1) * x 4,(-1) * x 3,0]] k
def tensorAction (k : Fin 6) (T : Tensor) : Tensor :=
  lorentzGenerator k * T + T * (lorentzGenerator k).transpose
/-- Directional covariance: the derivative of S along the generator flow is the tensor action. -/
def Covariant (S : Local → Tensor) : Prop := ∀ k x i j,
  HasDerivAt (fun t : ℝ => S (x+t • fieldAction k x) i j)
    (tensorAction k (S x) i j) 0
def TraceFree (S : Local → Tensor) : Prop := ∀ x,
  S x 0 0 + S x 1 1 + S x 2 2 - S x 3 3 = 0
/-- The 209 selected coefficient equations. -/
def constraints (c : Coeff) : Fin 209 → ℝ :=
  ![(-2) * c 1 0,
    (-1) * c 0 3 + (-2) * c 1 1,
    (-1) * c 0 4 + (-2) * c 1 2,
    1 * c 0 1 + (-2) * c 1 3,
    1 * c 0 2 + (-2) * c 1 4,
    (-2) * c 1 5,
    (-1) * c 0 8 + (-2) * c 1 6,
    (-1) * c 0 9 + (-1) * c 0 12 + (-2) * c 1 7,
    2 * c 0 6 + (-2) * c 0 15 + (-2) * c 1 8,
    1 * c 0 7 + (-1) * c 0 16 + (-2) * c 1 9,
    (-1) * c 0 17 + (-2) * c 1 10,
    (-1) * c 0 13 + (-2) * c 1 11,
    1 * c 0 7 + (-1) * c 0 16 + (-2) * c 1 12,
    2 * c 0 11 + (-2) * c 0 18 + (-2) * c 1 13,
    (-1) * c 0 19 + (-2) * c 1 14,
    1 * c 0 8 + (-2) * c 1 15,
    1 * c 0 9 + 1 * c 0 12 + (-2) * c 1 16,
    1 * c 0 10 + (-2) * c 1 17,
    1 * c 0 13 + (-2) * c 1 18,
    1 * c 0 14 + (-2) * c 1 19,
    (-2) * c 1 20,
    1 * c 0 0 + (-1) * c 4 0,
    (-1) * c 1 3 + 1 * c 0 1 + (-1) * c 4 1,
    (-1) * c 1 4 + 1 * c 0 2 + (-1) * c 4 2,
    1 * c 1 1 + 1 * c 0 3 + (-1) * c 4 3,
    1 * c 1 2 + 1 * c 0 4 + (-1) * c 4 4,
    1 * c 0 5 + (-1) * c 4 5,
    (-1) * c 1 8 + 1 * c 0 6 + (-1) * c 4 6,
    (-1) * c 1 9 + (-1) * c 1 12 + 1 * c 0 7 + (-1) * c 4 7,
    2 * c 1 6 + (-2) * c 1 15 + 1 * c 0 8 + (-1) * c 4 8,
    1 * c 1 7 + (-1) * c 1 16 + 1 * c 0 9 + (-1) * c 4 9,
    (-1) * c 1 17 + 1 * c 0 10 + (-1) * c 4 10,
    (-1) * c 1 13 + 1 * c 0 11 + (-1) * c 4 11,
    1 * c 1 7 + (-1) * c 1 16 + 1 * c 0 12 + (-1) * c 4 12,
    2 * c 1 11 + (-2) * c 1 18 + 1 * c 0 13 + (-1) * c 4 13,
    (-1) * c 1 19 + 1 * c 0 14 + (-1) * c 4 14,
    1 * c 1 8 + 1 * c 0 15 + (-1) * c 4 15,
    1 * c 1 9 + 1 * c 1 12 + 1 * c 0 16 + (-1) * c 4 16,
    1 * c 1 10 + 1 * c 0 17 + (-1) * c 4 17,
    1 * c 1 13 + 1 * c 0 18 + (-1) * c 4 18,
    1 * c 1 14 + 1 * c 0 19 + (-1) * c 4 19,
    1 * c 0 20 + (-1) * c 4 20,
    (-1) * c 5 0,
    (-1) * c 2 3 + (-1) * c 5 1,
    (-1) * c 2 4 + (-1) * c 5 2,
    1 * c 2 1 + (-1) * c 5 3,
    1 * c 2 2 + (-1) * c 5 4,
    (-1) * c 5 5,
    (-1) * c 2 8 + (-1) * c 5 6,
    (-1) * c 2 9 + (-1) * c 2 12 + (-1) * c 5 7,
    2 * c 2 6 + (-2) * c 2 15 + (-1) * c 5 8,
    1 * c 2 7 + (-1) * c 2 16 + (-1) * c 5 9,
    (-1) * c 2 17 + (-1) * c 5 10,
    (-1) * c 2 13 + (-1) * c 5 11,
    1 * c 2 7 + (-1) * c 2 16 + (-1) * c 5 12,
    2 * c 2 11 + (-2) * c 2 18 + (-1) * c 5 13,
    (-1) * c 2 19 + (-1) * c 5 14,
    1 * c 2 8 + (-1) * c 5 15,
    1 * c 2 9 + 1 * c 2 12 + (-1) * c 5 16,
    1 * c 2 10 + (-1) * c 5 17,
    1 * c 2 13 + (-1) * c 5 18,
    1 * c 2 14 + (-1) * c 5 19,
    (-1) * c 5 20,
    (-1) * c 6 0,
    (-1) * c 3 3 + (-1) * c 6 1,
    (-1) * c 3 4 + (-1) * c 6 2,
    1 * c 3 1 + (-1) * c 6 3,
    1 * c 3 2 + (-1) * c 6 4,
    (-1) * c 6 5,
    (-1) * c 3 8 + (-1) * c 6 6,
    (-1) * c 3 9 + (-1) * c 3 12 + (-1) * c 6 7,
    2 * c 3 6 + (-2) * c 3 15 + (-1) * c 6 8,
    1 * c 3 7 + (-1) * c 3 16 + (-1) * c 6 9,
    (-1) * c 3 17 + (-1) * c 6 10,
    (-1) * c 3 13 + (-1) * c 6 11,
    1 * c 3 7 + (-1) * c 3 16 + (-1) * c 6 12,
    2 * c 3 11 + (-2) * c 3 18 + (-1) * c 6 13,
    (-1) * c 3 19 + (-1) * c 6 14,
    1 * c 3 8 + (-1) * c 6 15,
    1 * c 3 9 + 1 * c 3 12 + (-1) * c 6 16,
    1 * c 3 10 + (-1) * c 6 17,
    1 * c 3 13 + (-1) * c 6 18,
    1 * c 3 14 + (-1) * c 6 19,
    (-1) * c 6 20,
    (-1) * c 4 3 + 2 * c 1 1,
    (-1) * c 4 4 + 2 * c 1 2,
    1 * c 4 1 + 2 * c 1 3,
    1 * c 4 2 + 2 * c 1 4,
    (-1) * c 4 17 + 2 * c 1 10,
    (-1) * c 4 19 + 2 * c 1 14,
    1 * c 4 10 + 2 * c 1 17,
    1 * c 4 14 + 2 * c 1 19,
    1 * c 2 0,
    1 * c 2 5,
    (-1) * c 5 8 + 1 * c 2 6,
    (-1) * c 5 9 + (-1) * c 5 12 + 1 * c 2 7,
    2 * c 5 6 + (-2) * c 5 15 + 1 * c 2 8,
    1 * c 5 7 + (-1) * c 5 16 + 1 * c 2 9,
    (-1) * c 5 13 + 1 * c 2 11,
    1 * c 5 7 + (-1) * c 5 16 + 1 * c 2 12,
    2 * c 5 11 + (-2) * c 5 18 + 1 * c 2 13,
    1 * c 5 8 + 1 * c 2 15,
    1 * c 5 9 + 1 * c 5 12 + 1 * c 2 16,
    1 * c 5 13 + 1 * c 2 18,
    1 * c 2 20,
    1 * c 3 0,
    1 * c 3 5,
    (-1) * c 6 8 + 1 * c 3 6,
    (-1) * c 6 9 + (-1) * c 6 12 + 1 * c 3 7,
    2 * c 6 6 + (-2) * c 6 15 + 1 * c 3 8,
    1 * c 6 7 + (-1) * c 6 16 + 1 * c 3 9,
    (-1) * c 6 13 + 1 * c 3 11,
    1 * c 6 7 + (-1) * c 6 16 + 1 * c 3 12,
    2 * c 6 11 + (-2) * c 6 18 + 1 * c 3 13,
    1 * c 6 8 + 1 * c 3 15,
    1 * c 6 9 + 1 * c 6 12 + 1 * c 3 16,
    1 * c 6 13 + 1 * c 3 18,
    1 * c 3 20,
    (-1) * c 7 3,
    (-1) * c 7 4,
    1 * c 7 1,
    1 * c 7 2,
    (-1) * c 7 8,
    (-1) * c 7 9 + (-1) * c 7 12,
    2 * c 7 6 + (-2) * c 7 15,
    1 * c 7 7 + (-1) * c 7 16,
    (-1) * c 7 17,
    (-1) * c 7 13,
    2 * c 7 11 + (-2) * c 7 18,
    (-1) * c 7 19,
    1 * c 7 10,
    1 * c 7 14,
    (-1) * c 8 3,
    (-1) * c 8 4,
    1 * c 8 1,
    1 * c 8 2,
    (-1) * c 8 8,
    (-1) * c 8 9 + (-1) * c 8 12,
    2 * c 8 6 + (-2) * c 8 15,
    1 * c 8 7 + (-1) * c 8 16,
    (-1) * c 8 17,
    (-1) * c 8 13,
    2 * c 8 11 + (-2) * c 8 18,
    (-1) * c 8 19,
    1 * c 8 10,
    1 * c 8 14,
    (-1) * c 9 3,
    (-1) * c 9 4,
    1 * c 9 1,
    1 * c 9 2,
    (-1) * c 9 8,
    (-1) * c 9 9 + (-1) * c 9 12,
    2 * c 9 6 + (-2) * c 9 15,
    1 * c 9 7 + (-1) * c 9 16,
    (-1) * c 9 17,
    (-1) * c 9 13,
    2 * c 9 11 + (-2) * c 9 18,
    (-1) * c 9 19,
    1 * c 9 10,
    1 * c 9 14,
    1 * c 0 8 + (-2) * c 2 1,
    (-1) * c 0 5 + 1 * c 0 12 + (-2) * c 2 2,
    (-2) * c 0 0 + 2 * c 0 15 + (-2) * c 2 3,
    1 * c 0 16 + (-2) * c 2 4,
    1 * c 0 7 + (-2) * c 2 10,
    2 * c 0 11 + (-2) * c 0 20 + (-2) * c 2 14,
    (-1) * c 0 5 + 1 * c 0 12 + (-2) * c 2 17,
    1 * c 0 13 + (-2) * c 2 19,
    1 * c 1 8 + (-1) * c 5 1,
    (-1) * c 1 5 + 1 * c 1 12 + (-1) * c 5 2,
    (-2) * c 1 0 + 2 * c 1 15 + (-1) * c 5 3,
    1 * c 1 16 + (-1) * c 5 4,
    2 * c 1 11 + (-2) * c 1 20 + (-1) * c 5 14,
    (-1) * c 1 5 + 1 * c 1 12 + (-1) * c 5 17,
    1 * c 1 13 + (-1) * c 5 19,
    1 * c 2 3 + 1 * c 0 0 + (-1) * c 7 0,
    1 * c 2 2 + 1 * c 2 17 + 1 * c 0 5 + (-1) * c 7 5,
    1 * c 0 6 + (-1) * c 7 6,
    (-1) * c 2 10 + 1 * c 0 7 + (-1) * c 7 7,
    1 * c 0 9 + (-1) * c 7 9,
    (-1) * c 2 14 + 1 * c 0 11 + (-1) * c 7 11,
    1 * c 2 14 + 1 * c 0 20 + (-1) * c 7 20,
    1 * c 3 3 + (-1) * c 8 0,
    1 * c 3 2 + 1 * c 3 17 + (-1) * c 8 5,
    (-1) * c 8 6,
    (-1) * c 3 10 + (-1) * c 8 7,
    (-1) * c 3 1 + (-1) * c 8 8,
    (-1) * c 8 9,
    (-1) * c 3 14 + (-1) * c 8 11,
    (-1) * c 3 2 + (-1) * c 3 17 + (-1) * c 8 12,
    (-1) * c 3 19 + (-1) * c 8 13,
    (-1) * c 3 3 + (-1) * c 8 15,
    (-1) * c 3 4 + (-1) * c 8 16,
    (-1) * c 8 18,
    1 * c 3 14 + (-1) * c 8 20,
    (-1) * c 6 10,
    (-1) * c 9 5 + 1 * c 9 12,
    (-2) * c 9 0 + 2 * c 9 15,
    1 * c 9 16,
    2 * c 9 11 + (-2) * c 9 20,
    2 * c 0 0 + 2 * c 0 18 + 2 * c 3 4,
    1 * c 1 13 + 1 * c 6 2,
    1 * c 1 16 + 1 * c 6 3,
    1 * c 1 8 + 1 * c 6 17,
    1 * c 3 4 + 1 * c 0 0 + 1 * c 9 0,
    1 * c 3 1 + 1 * c 3 19 + 1 * c 0 5 + 1 * c 9 5,
    1 * c 0 11 + 1 * c 9 11,
    1 * c 0 0 + 1 * c 4 0 + 1 * c 7 0 + (-1) * c 9 0,
    1 * c 0 5 + 1 * c 4 5 + 1 * c 7 5 + (-1) * c 9 5]

/-! ## Conservation on Maxwell/Bianchi first jets -/
abbrev Jet := Fin 4 → Local
def registerJet (D : Jet) : Fin 4 → Register := fun μ => embed (D μ)
def divergence (S : Local → Tensor) (x : Local) (D : Jet) : Fin 4 → ℝ :=
  fun ν => ∑ μ, deriv (fun t : ℝ => S (x+t • D μ) μ ν) 0
def bianchiJet (D : Fin 4 → Register) : Prop :=
  D 0 5-D 1 1+D 2 0 = 0 ∧
  D 0 6-D 1 2-D 3 0 = 0 ∧
  D 0 9-D 2 2-D 3 1 = 0 ∧
  D 1 9-D 2 6-D 3 5 = 0
def sourcedCurrent (d : ℝ) (D : Fin 4 → Register) : Four := fun ν =>
  d * ∑ μ, field (D μ) μ ν
def VacuumJet (D : Jet) : Prop :=
  bianchiJet (registerJet D) ∧ sourcedCurrent 1 (registerJet D)=0
def Conserved (S : Local → Tensor) : Prop :=
  ∀ x D, VacuumJet D → divergence S x D=0
def exchange (v : Register) (j : Four) : Four := fun ν => mink (field v ν) j
/-- The sourceful exchange law at current stiffness k. -/
def ExchangeLaw (k : ℝ) (S : Local → Tensor) : Prop := ∀ x D,
  bianchiJet (registerJet D) → divergence S x D=exchange (embed x) (sourcedCurrent k (registerJet D))
/-- The Hodge map on the six components. -/
def J : Matrix (Fin 6) (Fin 6) ℝ := !![0,0,0,0,0,-1;0,0,0,0,1,0;0,0,0,1,0,0;
  0,0,-1,0,0,0;0,-1,0,0,0,0;1,0,0,0,0,0]

/-! ## The polynomial family and regularity classes -/
abbrev ConstantCoeff := Fin 10 → ℝ
abbrev LinearCoeff := Fin 10 → Fin 6 → ℝ
def constant (A : ConstantCoeff) : Tensor := fun i j => A (tensorIndex i j)
def linear (l : LinearCoeff) (x : Local) : Tensor := fun i j => ∑ a, l (tensorIndex i j) a*x a
def crossCoefficients (b : Local) : LinearCoeff := ![![(1)*b 0,(1)*b 1,(-1)*b 2,(-1)*b 3,(1)*b 4,(1)*b 5],![0,(1)*b 3,(-1)*b 4,(1)*b 1,(-1)*b 2,0],![(-1)*b 3,0,(-1)*b 5,(-1)*b 0,0,(-1)*b 2],![(-1)*b 4,(-1)*b 5,0,0,(-1)*b 0,(-1)*b 1],![(1)*b 0,(-1)*b 1,(1)*b 2,(1)*b 3,(-1)*b 4,(1)*b 5],![(1)*b 1,(1)*b 0,0,0,(-1)*b 5,(-1)*b 4],![(1)*b 2,0,(1)*b 0,(-1)*b 5,0,(-1)*b 3],![(-1)*b 0,(1)*b 1,(1)*b 2,(1)*b 3,(1)*b 4,(-1)*b 5],![0,(1)*b 2,(1)*b 1,(1)*b 4,(1)*b 3,0],![(1)*b 0,(1)*b 1,(1)*b 2,(1)*b 3,(1)*b 4,(1)*b 5]]
def conservedFamily (A : ConstantCoeff) (b : Local) (d : ℝ) (x : Local) : Tensor :=
  constant A+linear (crossCoefficients b) x+registerStress d (embed x)
def covariantFamily (c d : ℝ) (x : Local) : Tensor := c • metric+registerStress d (embed x)
def RegularSource (S : Local → Tensor) : Prop :=
  (∀ x, (S x).transpose=S x) ∧ ∀ i j, ContDiff ℝ 3 (fun x => S x i j)
def DifferentiableSource (S : Local → Tensor) : Prop :=
  (∀ x, (S x).transpose=S x) ∧ ∀ i j, Differentiable ℝ (fun x => S x i j)

/-! ## Control coefficient tables -/
def metricInvariantCoefficients : Coeff :=
  ![![2,0,0,0,0,0,2,0,0,0,0,-2,0,0,0,2,0,0,-2,0,-2],
    ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![2,0,0,0,0,0,2,0,0,0,0,-2,0,0,0,2,0,0,-2,0,-2],
    ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![2,0,0,0,0,0,2,0,0,0,0,-2,0,0,0,2,0,0,-2,0,-2],
    ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![-2,0,0,0,0,0,-2,0,0,0,0,2,0,0,0,-2,0,0,2,0,2]]
def anisotropicCoefficients : Coeff :=
  ![![1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]


/-! ## Bridging lemmas: the restated objects are the research objects -/

theorem embed_eq (x : Local) : embed x = PDTUnrestrictedSourceKernel.embed x := rfl
theorem registerStress_eq (d : ℝ) (v : Register) :
    registerStress d v = PDTStressTensor.registerStress d v := rfl
theorem source_eq (c : Coeff) : source c = PDTQuadraticSource.source c := rfl
theorem isQuadratic_iff (S : Local → Tensor) :
    IsQuadraticSource S ↔ PDTQuadraticSource.IsQuadraticSource S := Iff.rfl
theorem lorentzGenerator_eq (k : Fin 6) :
    lorentzGenerator k = PDTQuadraticSource.lorentzGenerator k :=
  (PDTQuadraticSource.lorentz_formula k).symm
theorem fieldAction_eq (k : Fin 6) (x : Local) :
    fieldAction k x = PDTQuadraticSource.fieldAction k x :=
  (PDTQuadraticSource.field_action_formula k x).symm
theorem tensorAction_eq (k : Fin 6) (T : Tensor) :
    tensorAction k T = PDTQuadraticSource.tensorAction k T := by
  unfold tensorAction PDTQuadraticSource.tensorAction
  rw [lorentzGenerator_eq]
theorem covariant_iff (S : Local → Tensor) :
    Covariant S ↔ PDTQuadraticSource.Covariant S := by
  unfold Covariant PDTQuadraticSource.Covariant
  simp only [fieldAction_eq, tensorAction_eq]
theorem traceFree_iff (S : Local → Tensor) :
    TraceFree S ↔ PDTQuadraticSource.TraceFree S := Iff.rfl
theorem constraints_eq (c : Coeff) :
    constraints c = PDTQuadraticSource.constraints c := rfl
theorem conserved_iff (S : Local → Tensor) :
    Conserved S ↔ PDTConservedSource.Conserved S := Iff.rfl
theorem exchangeLaw_iff (k : ℝ) (S : Local → Tensor) :
    ExchangeLaw k S ↔ PDTSourcefulSelection.ExchangeLaw k S := Iff.rfl
theorem conservedFamily_eq (A : ConstantCoeff) (b : Local) (d : ℝ) :
    conservedFamily A b d = PDTPolynomialSource.conservedFamily A b d := rfl
theorem covariantFamily_eq (c d : ℝ) :
    covariantFamily c d = PDTPolynomialSource.covariantFamily c d := rfl
theorem regular_iff (S : Local → Tensor) :
    RegularSource S ↔ PDTSmoothSource.RegularSource S := Iff.rfl
theorem differentiable_iff (S : Local → Tensor) :
    DifferentiableSource S ↔ PDTSourcefulSelection.DifferentiableSource S := Iff.rfl
theorem J_eq : J = PDTUnrestrictedSourceKernel.J := rfl
theorem metricInvariant_eq :
    metricInvariantCoefficients = PDTQuadraticSource.metricInvariantCoefficients := rfl
theorem anisotropic_eq :
    anisotropicCoefficients = PDTQuadraticSource.anisotropicCoefficients := rfl

/-! ## Proofs of the compared statements -/

theorem quadraticSelection_proof (S : Local → Tensor) (hq : IsQuadraticSource S) :
    (Covariant S ∧ TraceFree S) ↔ ∃ d : ℝ, S=fun x => registerStress d (embed x) := by
  rw [covariant_iff, traceFree_iff]
  exact PDTQuadraticSource.source_classification S hq

theorem quadraticUniqueness_proof (S : Local → Tensor) (hq : IsQuadraticSource S)
    (hc : Covariant S) (ht : TraceFree S) :
    ∃! d : ℝ, S=fun x => registerStress d (embed x) :=
  PDTQuadraticSource.source_uniqueness S hq ((covariant_iff S).mp hc) ((traceFree_iff S).mp ht)

theorem finiteCertificate_proof (c : Coeff) :
    constraints c=0 ↔ Covariant (source c) ∧ TraceFree (source c) := by
  rw [constraints_eq, covariant_iff, traceFree_iff, source_eq]
  exact PDTQuadraticSource.finite_certificate c

theorem conservationSelection_proof (S : Local → Tensor) (hq : IsQuadraticSource S) :
    Conserved S ↔ ∃ d : ℝ, S=fun x => registerStress d (embed x) :=
  PDTConservedSource.conserved_source_classification S hq

theorem conservationHodgeInvariance_proof (S : Local → Tensor) (hq : IsQuadraticSource S)
    (hc : Conserved S) (x : Local) : S (J *ᵥ x)=S x :=
  PDTConservedSource.conservation_forces_hodge_invariance S hq hc x

theorem smoothClassification_proof (S : Local → Tensor) (hr : RegularSource S) (hc : Conserved S) :
    ∃ A : ConstantCoeff, ∃ b : Local, ∃ d : ℝ, S=conservedFamily A b d :=
  (PDTPolynomialSource.conserved_polynomial_classification S
    (PDTSmoothSource.regular_source_polynomial S hr hc)).mp hc

theorem smoothZeroFieldSelection_proof (S : Local → Tensor) (hr : RegularSource S)
    (hc : Conserved S) (hv : Covariant S) :
    (S 0=0 ↔ TraceFree S) ∧
    (S 0=0 ↔ ∃ d : ℝ, S=fun x => registerStress d (embed x)) := by
  rw [traceFree_iff]
  exact PDTSmoothSource.smooth_zero_field_selection S hr hc ((covariant_iff S).mp hv)

theorem differentiableSourcefulClassification_proof (k : ℝ) (S : Local → Tensor)
    (hd : DifferentiableSource S) : ExchangeLaw k S ↔ ∃ A, S=conservedFamily A 0 k :=
  PDTSourcefulSelection.differentiable_sourceful_classification k S hd

theorem differentiableNormalizedSelection_proof (k : ℝ) (S : Local → Tensor)
    (hd : DifferentiableSource S) (he : ExchangeLaw k S) (h0 : S 0=0) :
    S=fun x => registerStress k (embed x) :=
  PDTSourcefulSelection.differentiable_normalized_selection k S hd he h0

theorem traceNecessity_proof :
    Covariant (source metricInvariantCoefficients) ∧
    ¬ TraceFree (source metricInvariantCoefficients) := by
  rw [covariant_iff, traceFree_iff, source_eq, metricInvariant_eq]
  exact ⟨PDTQuadraticSource.metric_invariant_covariant,
    PDTQuadraticSource.metric_invariant_not_trace_free⟩

theorem covarianceNecessity_proof :
    TraceFree (source anisotropicCoefficients) ∧
    ¬ Covariant (source anisotropicCoefficients) := by
  rw [covariant_iff, traceFree_iff, source_eq, anisotropic_eq]
  exact ⟨PDTQuadraticSource.anisotropic_trace_free, PDTQuadraticSource.anisotropic_not_covariant⟩

theorem smoothNecessity_proof :
    (RegularSource (conservedFamily 0 ![1,0,0,0,0,0] 0) ∧
      Conserved (conservedFamily 0 ![1,0,0,0,0,0] 0) ∧
      ¬ Covariant (conservedFamily 0 ![1,0,0,0,0,0] 0)) ∧
    (RegularSource (covariantFamily 1 0) ∧ Conserved (covariantFamily 1 0) ∧
      Covariant (covariantFamily 1 0) ∧ ¬ TraceFree (covariantFamily 1 0)) := by
  rw [covariant_iff, covariant_iff, traceFree_iff, conservedFamily_eq, covariantFamily_eq]
  exact ⟨PDTSmoothSource.smooth_covariance_control, PDTSmoothSource.smooth_trace_control⟩

end
end PDTSourceSelection
