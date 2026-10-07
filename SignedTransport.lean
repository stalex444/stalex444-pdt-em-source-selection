module
public import ExtraSymmetry

@[expose] public section
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
namespace PDTSignedTransport
noncomputable section
open PDTExteriorAction PDTExteriorKernel PDTExteriorMetric PDTFiniteHodge
open PDTExtraSymmetry PDTPfaffianCubic PDTPfaffianBridge PDTStabilizerTests
open PDTGeometricTransport PDTCubicPolarization PDTFinitePfaffian
open GravityScreening.ResponseClosureGeometry
open scoped Matrix

/-- Determinant-signed exterior action, defined for every real ambient matrix. -/
def signedLift (M : M6) : M15 := M.det • lift M

theorem signed_mul (M N : M6) : signedLift (M*N)=signedLift M*signedLift N := by
  simp only [signedLift,Matrix.det_mul,lift_mul,Matrix.smul_mul,Matrix.mul_smul,smul_smul]
  rw [mul_comm M.det N.det]

theorem signed_one : signedLift (1 : M6)=1 := by
  simp [signedLift,lift_one]

theorem signed_reflection : signedLift reflection=extra := by
  simp [signedLift,reflection_det,extra]

theorem ambient_metric_det : ambientMetric.det=1 := by
  norm_num [ambientMetric,eta,Matrix.det_diagonal,Fin.prod_univ_succ]

theorem isometry_det_square (M : M6)
    (hm : M.transpose*ambientMetric*M=ambientMetric) : M.det^2=1 := by
  have hd := congrArg Matrix.det hm
  rw [Matrix.det_mul,Matrix.det_mul,Matrix.det_transpose,ambient_metric_det] at hd
  nlinarith

theorem isometry_det_cases (M : M6)
    (hm : M.transpose*ambientMetric*M=ambientMetric) : M.det=1 ∨ M.det= -1 := by
  have hh := isometry_det_square M hm
  have hz : (M.det-1)*(M.det+1)=0 := by nlinarith
  rcases mul_eq_zero.mp hz with h | h
  · left; linarith
  · right; linarith

theorem signed_metric (M : M6)
    (hm : M.transpose*ambientMetric*M=ambientMetric) :
    (signedLift M).transpose*bivectorMetric*signedLift M=bivectorMetric := by
  rcases isometry_det_cases M hm with hp | hn
  · simpa only [signedLift,hp,one_smul] using induced_metric M hm
  · simpa only [signedLift,hn,neg_one_smul,Matrix.transpose_neg,
      Matrix.neg_mul,neg_mul_neg] using induced_metric M hm

theorem signed_cubic (M : M6)
    (hm : M.transpose*ambientMetric*M=ambientMetric) (x : I → ℝ) :
    cubic (signedLift M *ᵥ x)=cubic x := by
  rcases isometry_det_cases M hm with hp | hn
  · simpa only [signedLift,hp,one_smul,cubic,value] using oriented_value M hp x
  · rw [signedLift,hn,neg_one_smul,Matrix.neg_mulVec,cubic_neg]
    change -value (lift M *ᵥ x)=value x
    rw [pfaffian_transform,hn]
    ring

theorem signed_hodge (M : M6)
    (hm : M.transpose*ambientMetric*M=ambientMetric) (x : I → ℝ) :
    movingHodge (signedLift M *ᵥ x)=
      signedLift M*movingHodge x*(signedLift M)⁻¹ := by
  have hc := finite_covariance (signedLift M) (signed_metric M hm) (signed_cubic M hm) x
  rw [reverse_eq_inverse _ (signed_metric M hm)] at hc
  simp only [movingHodge,hc,Matrix.mul_neg,Matrix.neg_mul]

/-- The new orientation-reversing branch has no real unsigned exterior lift. -/
theorem negative_branch_no_lift (N : M6) (hn : N.det= -1) :
    ¬ ∃ M : M6, lift M=signedLift N := by
  rintro ⟨M,h⟩
  have hnu : IsUnit N.det := isUnit_iff_ne_zero.mpr (by rw [hn]; norm_num)
  apply no_negative_identity (M*N⁻¹)
  rw [lift_mul,h,signedLift,hn,neg_one_smul,Matrix.neg_mul,← lift_mul,
    Matrix.mul_nonsing_inv N hnu,lift_one]

theorem signed_neg (M : M6) : signedLift (-M)=signedLift M := by
  norm_num [signedLift,Matrix.det_neg,lift_neg]

/-- The determinant-signed action on ambient isometries is faithful up to overall sign. -/
theorem signed_fiber (M N : M6)
    (hm : M.transpose*ambientMetric*M=ambientMetric)
    (hn : N.transpose*ambientMetric*N=ambientMetric) :
    signedLift M=signedLift N ↔ M=N ∨ M= -N := by
  have hn0 : N.det ≠ 0 := by
    have h := isometry_det_square N hn
    intro hz
    rw [hz] at h
    norm_num at h
  constructor
  · intro h
    rcases isometry_det_cases M hm with hp | hm'
    · rcases isometry_det_cases N hn with hq | hn'
      · apply (lift_fiber M N hn0).mp
        simpa only [signedLift,hp,hq,one_smul] using h
      · have he : signedLift M=lift M := by simp [signedLift,hp]
        rw [he] at h
        exact False.elim (negative_branch_no_lift N hn' ⟨M,h⟩)
    · rcases isometry_det_cases N hn with hq | hn'
      · have he : signedLift N=lift N := by simp [signedLift,hq]
        rw [he] at h
        exact False.elim (negative_branch_no_lift M hm' ⟨N,h.symm⟩)
      · apply (lift_fiber M N hn0).mp
        simpa only [signedLift,hm',hn',neg_one_smul,neg_inj] using h
  · rintro (rfl | rfl)
    · rfl
    · exact signed_neg N

theorem signed_kernel (M : M6)
    (hm : M.transpose*ambientMetric*M=ambientMetric) :
    signedLift M=1 ↔ M=1 ∨ M= -1 := by
  have hi : (1 : M6).transpose*ambientMetric*1=ambientMetric := by simp
  simpa only [signed_one] using signed_fiber M 1 hm hi

#print axioms signed_neg
#print axioms signed_fiber
#print axioms signed_kernel

#print axioms signed_mul
#print axioms signed_one
#print axioms signed_reflection
#print axioms ambient_metric_det
#print axioms isometry_det_square
#print axioms isometry_det_cases
#print axioms signed_metric
#print axioms signed_cubic
#print axioms signed_hodge
#print axioms negative_branch_no_lift
end
end PDTSignedTransport
