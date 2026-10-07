module
public import UnrestrictedSourceKernel

@[expose] public section
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
namespace PDTQuadraticSource
noncomputable section
open PDTStressTensor PDTUnrestrictedSourceKernel
open scoped Matrix

abbrev Coeff := Fin 10 → Fin 21 → ℝ

/-- Every unordered pair, including squares: all degree-two monomials in six variables. -/
def monomialPair : Fin 21 → Fin 6 × Fin 6 :=
  ![(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),
    (1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,3),(2,4),(2,5),
    (3,3),(3,4),(3,5),(4,4),(4,5),(5,5)]

def tensorPair : Fin 10 → Fin 4 × Fin 4 :=
  ![(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,2),(2,3),(3,3)]

def tensorIndex : Fin 4 → Fin 4 → Fin 10 :=
  !![0,1,2,3;1,4,5,6;2,5,7,8;3,6,8,9]

def poly (c : Fin 21 → ℝ) (x : Local) : ℝ :=
  ∑ m, c m * x (monomialPair m).1 * x (monomialPair m).2

def dpoly (c : Fin 21 → ℝ) (x y : Local) : ℝ :=
  ∑ m, c m * (y (monomialPair m).1 * x (monomialPair m).2 +
    x (monomialPair m).1 * y (monomialPair m).2)

def source (c : Coeff) (x : Local) : Tensor := fun i j => poly (c (tensorIndex i j)) x
def variation (c : Coeff) (x y : Local) : Tensor :=
  fun i j => dpoly (c (tensorIndex i j)) x y

/-- An arbitrary homogeneous quadratic symmetric tensor, with no contraction ansatz. -/
def IsQuadraticSource (S : Local → Tensor) : Prop := ∃ c : Coeff, S=source c

/-- The existing geometric generator, restricted to the original four-plane. -/
def lorentzGenerator (k : Fin 6) : Tensor := fun i j =>
  (GravityScreening.ResponseClosureGeometry.orthogonalGenerator
    (PDTCentralizerSplit.localIndex k) (Fin.castAdd 2 i) (Fin.castAdd 2 j) : ℝ)

/-- The original fifteen-dimensional adjoint action on the six active coordinates. -/
def fieldAction (k : Fin 6) (x : Local) : Local := extract
  (PDTCubicInvariance.generator ℝ (PDTCentralizerSplit.localIndex k) *ᵥ embed x)

def tensorAction (k : Fin 6) (T : Tensor) : Tensor :=
  lorentzGenerator k * T + T * (lorentzGenerator k).transpose

/-- True directional derivatives of the candidate source, using the original geometry. -/
def Covariant (S : Local → Tensor) : Prop := ∀ k x i j,
  HasDerivAt (fun t : ℝ => S (x+t • fieldAction k x) i j)
    (tensorAction k (S x) i j) 0

def TraceFree (S : Local → Tensor) : Prop := ∀ x,
  S x 0 0 + S x 1 1 + S x 2 2 - S x 3 3 = 0

theorem source_symmetric (c : Coeff) (x : Local) :
    (source c x).transpose=source c x := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem poly_hasDerivAt (c : Fin 21 → ℝ) (x y : Local) :
    HasDerivAt (fun t : ℝ => poly c (x+t • y)) (dpoly c x y) 0 := by
  unfold poly dpoly
  have h (m : Fin 21) : HasDerivAt
      (fun t : ℝ => c m * (x (monomialPair m).1+t*y (monomialPair m).1) *
        (x (monomialPair m).2+t*y (monomialPair m).2))
      (c m * (y (monomialPair m).1*x (monomialPair m).2+
        x (monomialPair m).1*y (monomialPair m).2)) 0 := by
    have ha := (hasDerivAt_const (0 : ℝ) (x (monomialPair m).1)).add
      ((hasDerivAt_id (0 : ℝ)).mul_const (y (monomialPair m).1))
    have hb := (hasDerivAt_const (0 : ℝ) (x (monomialPair m).2)).add
      ((hasDerivAt_id (0 : ℝ)).mul_const (y (monomialPair m).2))
    convert! ((ha.const_mul (c m)).mul hb) using 1
    simp
    ring
  convert! HasDerivAt.sum (fun m (_ : m ∈ Finset.univ) => h m) using 1

theorem source_hasDerivAt (c : Coeff) (x y : Local) (i j : Fin 4) :
    HasDerivAt (fun t : ℝ => source c (x+t • y) i j) (variation c x y i j) 0 :=
  poly_hasDerivAt (c (tensorIndex i j)) x y

theorem covariance_iff (c : Coeff) : Covariant (source c) ↔
    ∀ k x, variation c x (fieldAction k x)=tensorAction k (source c x) := by
  constructor
  · intro h k x
    ext i j
    exact (source_hasDerivAt c x (fieldAction k x) i j).unique (h k x i j)
  · intro h k x i j
    rw [← h k x]
    exact source_hasDerivAt c x (fieldAction k x) i j

def defect (c : Coeff) (k : Fin 6) (x : Local) (i j : Fin 4) : ℝ :=
  variation c x (fieldAction k x) i j - tensorAction k (source c x) i j

theorem defect_zero (c : Coeff) (h : Covariant (source c))
    (k : Fin 6) (x : Local) (i j : Fin 4) : defect c k x i j=0 := by
  unfold defect
  rw [(covariance_iff c).mp h k x,sub_self]

/-- Recover a quadratic coefficient from exact unit and pair-sum evaluations. -/
def reading (f : Local → ℝ) (m : Fin 21) : ℝ :=
  let ab := monomialPair m
  if ab.1=ab.2 then f (Pi.single ab.1 1)
  else f (Pi.single ab.1 1+Pi.single ab.2 1)-f (Pi.single ab.1 1)-f (Pi.single ab.2 1)

theorem reading_zero (f : Local → ℝ) (h : ∀ x, f x=0) (m : Fin 21) : reading f m=0 := by
  simp [reading,h]

#print axioms source_symmetric
#print axioms poly_hasDerivAt
#print axioms source_hasDerivAt
#print axioms covariance_iff
#print axioms defect_zero
#print axioms reading_zero
end
end PDTQuadraticSource
