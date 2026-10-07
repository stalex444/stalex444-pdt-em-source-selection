module
public import ExteriorAction

@[expose] public section
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
namespace PDTExteriorMetric
noncomputable section
open PDTExteriorAction PDTPfaffianCubic PDTStabilizerTests
open GravityScreening.ResponseClosureCertificate GravityScreening.ResponseClosureGeometry
open scoped Matrix

def ambientMetric : M6 := Matrix.diagonal (fun i => (eta i : ℝ))

theorem lift_transpose (M : M6) : lift M.transpose=(lift M).transpose := by
  ext r c
  simp only [lift,Matrix.transpose_apply]
  ring

theorem lift_metric : lift ambientMetric=bivectorMetric := by
  have hi : ∀ r c : I,
      (Matrix.diagonal eta (ia r) (ia c)*Matrix.diagonal eta (ib r) (ib c)-
       Matrix.diagonal eta (ia r) (ib c)*Matrix.diagonal eta (ib r) (ia c))=
       Matrix.diagonal q r c := by decide +kernel
  ext r c
  have h := hi r c
  unfold lift ambientMetric bivectorMetric
  simp only [Matrix.diagonal_apply] at h ⊢
  exact_mod_cast h

theorem metric_square : bivectorMetric*bivectorMetric=(1 : M15) := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    norm_num [bivectorMetric,Matrix.diagonal_mul,Matrix.diagonal_apply,Matrix.one_apply,q,Fin.ext_iff]

/-- The original metric is preserved by the actual exterior action of every ambient isometry. -/
theorem induced_metric (M : M6) (hm : M.transpose*ambientMetric*M=ambientMetric) :
    (lift M).transpose*bivectorMetric*lift M=bivectorMetric := by
  rw [← lift_metric,← lift_transpose,← lift_mul,← lift_mul,hm]

#print axioms lift_transpose
#print axioms lift_metric
#print axioms metric_square
#print axioms induced_metric
end
end PDTExteriorMetric
