module
public import StabilizerRecovery

@[expose] public section
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
namespace PDTJointStabilizer
noncomputable section
open PDTPfaffianCubic PDTCubicInvariance PDTHessianCovariance
open PDTStabilizerTests PDTStabilizerRecovery
open GravityScreening.ResponseClosureCertificate GravityScreening.ResponseClosureGeometry
open scoped Matrix

theorem metric_iff_entries (A : Mat) : MetricSkew A ↔
    ∀ r c : I, (q r : ℝ)*A r c+(q c : ℝ)*A c r=0 := by
  constructor
  · exact metric_entry A
  · intro h
    unfold MetricSkew
    ext r c
    simpa [bivectorMetric,Matrix.mul_diagonal,Matrix.diagonal_mul,mul_comm,add_comm] using h r c

theorem generator_metric (p : I) : MetricSkew (generator ℝ p) := by
  apply (metric_iff_entries _).mpr
  intro r c
  have hi := congrArg (fun M : IMat => M r c) (PDTCovarianceCertificate.metric_invariance p)
  simp only [Matrix.add_apply,Matrix.mul_diagonal,Matrix.diagonal_mul,
    Matrix.transpose_apply,Matrix.zero_apply] at hi
  change (q r : ℝ)*(geometricAdjoint p r c : ℝ)+
    (q c : ℝ)*(geometricAdjoint p c r : ℝ)=0
  rw [← certificate_adjoint]
  have hz : q r*adj p r c+q c*adj p c r=0 := by linear_combination hi
  exact_mod_cast hz

def geometricMap : (I → ℝ) →ₗ[ℝ] Mat where
  toFun := connection ℝ
  map_add' u v := by simp [connection,add_smul,Finset.sum_add_distrib]
  map_smul' a w := by simp [connection,smul_smul,Finset.smul_sum]

theorem connection_metric (w : I → ℝ) : MetricSkew (connection ℝ w) := by
  apply (metric_iff_entries _).mpr
  intro r c
  simp only [connection,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,Finset.mul_sum,
    ← Finset.sum_add_distrib]
  have hz (p : I) := (metric_iff_entries _).mp (generator_metric p) r c
  calc
    _ = ∑ p : I, w p*((q r : ℝ)*generator ℝ p r c+(q c : ℝ)*generator ℝ p c r) := by
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ = 0 := by simp only [hz,mul_zero,Finset.sum_const_zero]

/-- The finite tests already determine the complete geometric combination. -/
theorem finite_reconstruction (A : Mat) (hm : MetricSkew A) (hf : FiniteTests A) :
    A=connection ℝ (decode A) := recover A (certificate_of_finite A hm hf)

/-- All-point preservation of both tensors forces the original geometric span. -/
theorem joint_reconstruction (A : Mat) (hm : MetricSkew A) (hc : CubicInvariant A) :
    A=connection ℝ (decode A) :=
  finite_reconstruction A hm (all_points_imply_finite A hc)

theorem joint_iff_geometric (A : Mat) :
    MetricSkew A ∧ CubicInvariant A ↔ ∃ w : I → ℝ, A=connection ℝ w := by
  constructor
  · rintro ⟨hm,hc⟩
    exact ⟨decode A,joint_reconstruction A hm hc⟩
  · rintro ⟨w,rfl⟩
    exact ⟨connection_metric w,connection_invariance ℝ w⟩

theorem joint_unique (A : Mat) (hm : MetricSkew A) (hc : CubicInvariant A) :
    ∃! w : I → ℝ, A=connection ℝ w := by
  refine ⟨decode A,joint_reconstruction A hm hc,?_⟩
  intro w hw
  apply connection_injective
  exact hw.symm.trans (joint_reconstruction A hm hc)

/-- Within metric-skew maps, the ninety explicit probes certify every point. -/
theorem finite_iff_all (A : Mat) (hm : MetricSkew A) :
    FiniteTests A ↔ CubicInvariant A := by
  constructor
  · intro hf
    rw [finite_reconstruction A hm hf]
    exact connection_invariance ℝ _
  · exact all_points_imply_finite A

def jointStabilizer : Submodule ℝ Mat where
  carrier := {A | MetricSkew A ∧ CubicInvariant A}
  zero_mem' := by
    change MetricSkew 0 ∧ CubicInvariant 0
    rw [joint_iff_geometric]
    exact ⟨0,by simp [connection]⟩
  add_mem' := by
    intro A B ha hb
    obtain ⟨u,rfl⟩ := (joint_iff_geometric A).mp ha
    obtain ⟨v,rfl⟩ := (joint_iff_geometric B).mp hb
    apply (joint_iff_geometric _).mpr
    exact ⟨u+v,(geometricMap.map_add u v).symm⟩
  smul_mem' := by
    intro a A ha
    obtain ⟨w,rfl⟩ := (joint_iff_geometric A).mp ha
    apply (joint_iff_geometric _).mpr
    exact ⟨a • w,(geometricMap.map_smul a w).symm⟩

theorem joint_eq_range : jointStabilizer=LinearMap.range geometricMap := by
  ext A
  change (MetricSkew A ∧ CubicInvariant A) ↔ _
  rw [joint_iff_geometric]
  simp only [LinearMap.mem_range,geometricMap,LinearMap.coe_mk,AddHom.coe_mk]
  exact exists_congr (fun _ => eq_comm)

theorem joint_finrank : Module.finrank ℝ jointStabilizer=15 := by
  rw [joint_eq_range,LinearMap.finrank_range_of_inj (f := geometricMap) connection_injective]
  simp [I]

/-- The recovered transformations carry the actual metric-raised Hessian. -/
theorem joint_hessian_covariance (A : Mat) (hm : MetricSkew A) (hc : CubicInvariant A)
    (x : I → ℝ) :
    A*PDTPfaffianBridge.raisedHessian ℝ x-PDTPfaffianBridge.raisedHessian ℝ x*A=
      PDTPfaffianBridge.raisedHessian ℝ (A *ᵥ x) := by
  rw [joint_reconstruction A hm hc]
  exact connection_covariance ℝ _ x

#print axioms metric_iff_entries
#print axioms generator_metric
#print axioms connection_metric
#print axioms finite_reconstruction
#print axioms joint_reconstruction
#print axioms joint_iff_geometric
#print axioms joint_unique
#print axioms finite_iff_all
#print axioms joint_eq_range
#print axioms joint_finrank
#print axioms joint_hessian_covariance
end
end PDTJointStabilizer
