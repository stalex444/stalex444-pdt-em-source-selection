module
public import QuadraticSource

@[expose] public section
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
namespace PDTQuadraticSource
noncomputable section
open PDTStressTensor PDTUnrestrictedSourceKernel
open GravityScreening.ResponseClosureCertificate GravityScreening.ResponseClosureGeometry
open scoped Matrix

def lorentzTable : Fin 6 → Matrix (Fin 4) (Fin 4) ℤ :=
  ![!![0,1,0,0;-1,0,0,0;0,0,0,0;0,0,0,0],
    !![0,0,1,0;0,0,0,0;-1,0,0,0;0,0,0,0],
    !![0,0,0,-1;0,0,0,0;0,0,0,0;-1,0,0,0],
    !![0,0,0,0;0,0,1,0;0,-1,0,0;0,0,0,0],
    !![0,0,0,0;0,0,0,-1;0,0,0,0;0,-1,0,0],
    !![0,0,0,0;0,0,0,0;0,0,0,-1;0,0,-1,0]]

private theorem lorentz_integral : ∀ k : Fin 6, ∀ i j : Fin 4,
    orthogonalGenerator (PDTCentralizerSplit.localIndex k) (Fin.castAdd 2 i) (Fin.castAdd 2 j)=lorentzTable k i j := by
  decide +kernel

theorem lorentz_formula (k : Fin 6) : lorentzGenerator k=
    fun i j => (lorentzTable k i j : ℝ) := by
  ext i j
  exact congrArg (fun z : ℤ => (z : ℝ)) (lorentz_integral k i j)

theorem field_action_formula (k : Fin 6) (x : Local) : fieldAction k x=
  ![![0,1 * x 3,1 * x 4,(-1) * x 1,(-1) * x 2,0],
    ![(-1) * x 3,0,1 * x 5,1 * x 0,0,(-1) * x 2],
    ![1 * x 4,1 * x 5,0,0,1 * x 0,1 * x 1],
    ![1 * x 1,(-1) * x 0,0,0,1 * x 5,(-1) * x 4],
    ![(-1) * x 2,0,(-1) * x 0,1 * x 5,0,1 * x 3],
    ![0,(-1) * x 2,(-1) * x 1,(-1) * x 4,(-1) * x 3,0]] k := by
  unfold fieldAction PDTCubicInvariance.generator
  simp only [← certificate_adjoint]
  ext i
  fin_cases k <;> fin_cases i <;>
    simp [PDTCubicInvariance.cast,RingHom.mapMatrix,Matrix.map,extract,embed,
      PDTCentralizerSplit.localIndex,adj,adj00,adj01,adj02,adj05,adj06,adj09,
      Matrix.mulVec,dotProduct,Matrix.single]

#print axioms lorentz_formula
#print axioms field_action_formula
end
end PDTQuadraticSource
