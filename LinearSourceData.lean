module
public import PolynomialSource

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


def crossCoefficients (b : Local) : LinearCoeff := ![![(1)*b 0,(1)*b 1,(-1)*b 2,(-1)*b 3,(1)*b 4,(1)*b 5],![0,(1)*b 3,(-1)*b 4,(1)*b 1,(-1)*b 2,0],![(-1)*b 3,0,(-1)*b 5,(-1)*b 0,0,(-1)*b 2],![(-1)*b 4,(-1)*b 5,0,0,(-1)*b 0,(-1)*b 1],![(1)*b 0,(-1)*b 1,(1)*b 2,(1)*b 3,(-1)*b 4,(1)*b 5],![(1)*b 1,(1)*b 0,0,0,(-1)*b 5,(-1)*b 4],![(1)*b 2,0,(1)*b 0,(-1)*b 5,0,(-1)*b 3],![(-1)*b 0,(1)*b 1,(1)*b 2,(1)*b 3,(1)*b 4,(-1)*b 5],![0,(1)*b 2,(1)*b 1,(1)*b 4,(1)*b 3,0],![(1)*b 0,(1)*b 1,(1)*b 2,(1)*b 3,(1)*b 4,(1)*b 5]]

def background (l : LinearCoeff) : Local := ![l 0 0,l 0 1,-l 0 2,-l 0 3,l 0 4,l 0 5]

def linearConstraints (l : LinearCoeff) : Fin 54 → ℝ := ![(1)*l 0 3 + (1)*l 1 1,(1)*l 1 3 + (1)*l 4 1,(1)*l 2 3 + (1)*l 5 1,(1)*l 3 3 + (1)*l 6 1,(1)*l 0 4 + (1)*l 1 2,(1)*l 1 4 + (1)*l 4 2,(1)*l 2 4 + (1)*l 5 2,(1)*l 3 4 + (1)*l 6 2,(-1)*l 0 1 + (1)*l 1 3,(-1)*l 1 1 + (1)*l 4 3,(-1)*l 2 1 + (1)*l 5 3,(-1)*l 3 1 + (1)*l 6 3,(-1)*l 0 2 + (1)*l 1 4,(-1)*l 1 2 + (1)*l 4 4,(-1)*l 2 2 + (1)*l 5 4,(-1)*l 3 2 + (1)*l 6 4,(-1)*l 0 3 + (1)*l 2 0,(-1)*l 1 3 + (1)*l 5 0,(-1)*l 2 3 + (1)*l 7 0,(-1)*l 3 3 + (1)*l 8 0,(-1)*l 1 0 + (1)*l 2 1,(-1)*l 4 0 + (1)*l 5 1,(-1)*l 5 0 + (1)*l 7 1,(-1)*l 6 0 + (1)*l 8 1,(1)*l 0 5 + (1)*l 2 2,(1)*l 1 5 + (1)*l 5 2,(1)*l 2 5 + (1)*l 7 2,(1)*l 3 5 + (1)*l 8 2,(1)*l 0 0 + (1)*l 2 3,(1)*l 1 0 + (1)*l 5 3,(1)*l 2 0 + (1)*l 7 3,(1)*l 3 0 + (1)*l 8 3,(1)*l 1 5 + (1)*l 2 4,(1)*l 4 5 + (1)*l 5 4,(1)*l 5 5 + (1)*l 7 4,(1)*l 6 5 + (1)*l 8 4,(-1)*l 0 2 + (1)*l 2 5,(-1)*l 1 2 + (1)*l 5 5,(-1)*l 2 2 + (1)*l 7 5,(-1)*l 3 2 + (1)*l 8 5,(1)*l 0 4 + (1)*l 3 0,(1)*l 1 4 + (1)*l 6 0,(1)*l 2 4 + (1)*l 8 0,(1)*l 3 4 + (1)*l 9 0,(1)*l 0 5 + (1)*l 3 1,(1)*l 3 5 + (1)*l 9 1,(-1)*l 1 0 + (1)*l 3 2,(-1)*l 4 0 + (1)*l 6 2,(-1)*l 5 0 + (1)*l 8 2,(-1)*l 6 0 + (1)*l 9 2,(1)*l 6 5 + (1)*l 9 3,(1)*l 2 0 + (1)*l 8 4,(1)*l 3 0 + (1)*l 9 4,(1)*l 3 1 + (1)*l 9 5]

end
end PDTPolynomialSource
