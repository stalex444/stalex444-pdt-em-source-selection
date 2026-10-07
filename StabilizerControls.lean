module
public import JointStabilizer

@[expose] public section
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000
namespace PDTStabilizerControls
noncomputable section
open PDTPfaffianCubic PDTCubicInvariance PDTStabilizerTests PDTJointStabilizer
open GravityScreening.ResponseClosureCertificate
open PDTGeometricTransport
open scoped Matrix

/-- The induced diagonal weights of the ambient trace-free matrix diag(1,-1,0,0,0,0). -/
def cubicWeights (i : I) : ℝ :=
  if 1 ≤ i.val ∧ i.val ≤ 4 then 1 else if 5 ≤ i.val ∧ i.val ≤ 8 then -1 else 0

def cubicOnly : Mat := Matrix.diagonal cubicWeights

theorem cubic_only_preserves : CubicInvariant cubicOnly := by
  intro x
  rw [directional_eval]
  norm_num [cubicOnly,Matrix.mulVec_diagonal,cubicWeights]

theorem cubic_only_not_metric : ¬ MetricSkew cubicOnly := by
  intro hm
  have h := metric_entry cubicOnly hm 1 1
  norm_num [cubicOnly,cubicWeights,q] at h

def metricIntegral : IMat := Matrix.single 0 9 1+Matrix.single 9 0 1
private theorem metric_integral_entries : ∀ r c : I,
    q r*metricIntegral r c+q c*metricIntegral c r=0 := by
  decide +kernel

def metricOnly : Mat := PDTCubicInvariance.cast ℝ metricIntegral

theorem metric_only_preserves : MetricSkew metricOnly := by
  apply (metric_iff_entries _).mpr
  intro r c
  change (q r : ℝ)*(metricIntegral r c : ℝ)+(q c : ℝ)*(metricIntegral c r : ℝ)=0
  exact_mod_cast metric_integral_entries r c

private theorem metric_witness_action : metricOnly *ᵥ hodgeWitness=Pi.single 9 1 := by
  have hc : ∀ i : I, metricIntegral i 0+metricIntegral i 14=(Pi.single 9 1 : I → ℤ) i := by
    decide +kernel
  rw [hodgeWitness,Matrix.mulVec_add,Matrix.mulVec_single_one,Matrix.mulVec_single_one]
  ext i
  change (metricIntegral i 0 : ℝ)+(metricIntegral i 14 : ℝ)=(Pi.single 9 1 : I → ℝ) i
  rw [← Int.cast_add,hc]
  simp [Pi.single_apply]

theorem metric_only_not_cubic : ¬ CubicInvariant metricOnly := by
  intro hc
  have h := hc hodgeWitness
  rw [metric_witness_action,directional_eval] at h
  norm_num [hodgeWitness,Pi.single_apply,Fin.ext_iff] at h

#print axioms cubic_only_preserves
#print axioms cubic_only_not_metric
#print axioms metric_only_preserves
#print axioms metric_only_not_cubic
end
end PDTStabilizerControls
