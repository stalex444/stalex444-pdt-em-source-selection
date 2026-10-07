module
public import ConservationLaws

@[expose] public section
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
namespace PDTConservedSource
noncomputable section
open PDTStressTensor PDTUnrestrictedSourceKernel PDTQuadraticSource
open scoped Matrix

def testJet : Fin 16 → Jet :=
  ![!![0,0,0,1,0,0;0,1,0,0,0,0;0,0,0,0,0,0;0,0,0,0,0,0],
    !![0,0,0,0,1,0;0,0,1,0,0,0;0,0,0,0,0,0;0,0,0,0,0,0],
    !![0,-1,0,0,0,0;0,0,0,1,0,0;0,0,0,0,0,0;0,0,0,0,0,0],
    !![0,0,-1,0,0,0;0,0,0,0,1,0;0,0,0,0,0,0;0,0,0,0,0,0],
    !![0,0,0,-1,0,0;0,0,0,0,0,0;1,0,0,0,0,0;0,0,0,0,0,0],
    !![0,0,0,0,0,0;-1,0,0,0,0,0;0,1,0,0,0,0;0,0,0,0,0,0],
    !![0,0,0,0,0,1;0,0,0,0,0,0;0,0,1,0,0,0;0,0,0,0,0,0],
    !![1,0,0,0,0,0;0,0,0,0,0,0;0,0,0,1,0,0;0,0,0,0,0,0],
    !![0,0,0,0,0,0;0,0,0,0,0,1;0,0,0,0,1,0;0,0,0,0,0,0],
    !![0,0,-1,0,0,0;0,0,0,0,0,0;0,0,0,0,0,1;0,0,0,0,0,0],
    !![0,0,0,0,1,0;0,0,0,0,0,0;0,0,0,0,0,0;1,0,0,0,0,0],
    !![0,0,0,0,0,1;0,0,0,0,0,0;0,0,0,0,0,0;0,1,0,0,0,0],
    !![0,0,0,0,0,0;-1,0,0,0,0,0;0,0,0,0,0,0;0,0,1,0,0,0],
    !![0,0,0,0,0,0;0,0,0,0,0,1;0,0,0,0,0,0;0,0,0,1,0,0],
    !![1,0,0,0,0,0;0,0,0,0,0,0;0,0,0,0,0,0;0,0,0,0,1,0],
    !![0,1,0,0,0,0;0,0,0,0,0,0;0,0,0,0,0,0;0,0,0,0,0,1]]

theorem testJet_vacuum (k : Fin 16) : VacuumJet (testJet k) := by
  constructor
  · fin_cases k <;>
      norm_num [VacuumJet,PDTStressBalance.bianchiJet,registerJet,testJet,embed] <;>
      dsimp <;> norm_num
  · ext ν
    fin_cases k <;> fin_cases ν <;>
      norm_num [PDTStressBalance.sourcedCurrent,registerJet,testJet,embed,field,
        Fin.sum_univ_succ] <;> (try dsimp) <;> norm_num

#print axioms testJet_vacuum
end
end PDTConservedSource
