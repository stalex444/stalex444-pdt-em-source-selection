module
public import EMActionKernel

@[expose] public section
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
namespace PDTSourceActionKernel
noncomputable section
open PDTPfaffianCubic PDTStabilizerTests PDTCentralizerDimension PDTCentralizerSplit
open PDTStressTensor PDTStressBalance PDTEMActionKernel
open scoped Matrix

def sourceAction (d : ℝ) (A : Mat) : Action := fun v => firstVariation d v (A *ᵥ v)

/-- This response is the already established actual derivative of the same stress tensor. -/
theorem source_hasDerivAt (d : ℝ) (A : Mat) (v : V) (i j : Fin 4) :
    HasDerivAt (fun t : ℝ => registerStress d (v+t • (A *ᵥ v)) i j)
      (sourceAction d A v i j) 0 := firstVariation_hasDerivAt d v (A *ᵥ v) i j

theorem variation_field_zero (d : ℝ) (v w : V) (hw : field w=0) :
    firstVariation d v w=0 := by
  ext i j
  simp [firstVariation,crossInvariant,hw,PDTMaxwellSymbol.mink]

theorem field_invisible_implies_source (d : ℝ) (A : Mat) (hA : action A=0) :
    sourceAction d A=0 := by
  funext v
  exact variation_field_zero d v (A *ᵥ v) (congrFun hA v)

theorem source_scale (d : ℝ) (A : Mat) : sourceAction d A=d • sourceAction 1 A := by
  funext v
  ext i j
  simp [sourceAction,firstVariation]

theorem scale_preserves_kernel (d : ℝ) (hd : d≠0) (A : Mat) :
    sourceAction d A=0 ↔ sourceAction 1 A=0 := by
  rw [source_scale,smul_eq_zero]
  simp [hd]

/-- Six scalar stress derivatives, evaluated at only two local basis fields. -/
def sourceProbes (f : Action) : Fin 6 → ℝ :=
  ![-f (Pi.single 1 1) 0 1,-f (Pi.single 0 1) 0 2,
    -f (Pi.single 0 1) 0 3,-f (Pi.single 0 1) 1 2,
    -f (Pi.single 0 1) 1 3,-f (Pi.single 1 1) 2 3]

theorem sourceProbes_zero : sourceProbes (0 : Action)=0 := by
  ext i
  fin_cases i <;> simp [sourceProbes]

/-- Metric preservation converts the source readings to the existing field decoder. -/
theorem sourceProbes_eq_fieldProbes (A : Mat) (hm : MetricSkew A) :
    sourceProbes (sourceAction 1 A)=probes (action A) := by
  have h0 := metric_entry A hm 1 5
  have h1 := metric_entry A hm 0 5
  have h2 := metric_entry A hm 0 6
  have h3 := metric_entry A hm 0 1
  have h4 := metric_entry A hm 0 2
  have h5 := metric_entry A hm 1 2
  have q0 : GravityScreening.ResponseClosureCertificate.q 0=1 := by decide +kernel
  have q1 : GravityScreening.ResponseClosureCertificate.q 1=1 := by decide +kernel
  have q2 : GravityScreening.ResponseClosureCertificate.q 2= -1 := by decide +kernel
  have q5 : GravityScreening.ResponseClosureCertificate.q 5=1 := by decide +kernel
  have q6 : GravityScreening.ResponseClosureCertificate.q 6= -1 := by decide +kernel
  norm_num [q0,q1,q2,q5,q6] at h0 h1 h2 h3 h4 h5
  ext i
  fin_cases i <;>
    simp [sourceProbes,sourceAction,firstVariation,crossInvariant,probes,action,
      field,metric,eta,Matrix.diagonal,PDTMaxwellSymbol.mink] <;> linarith

theorem recover_source (u : Fin 6 → ℝ) (a : ℝ) :
    sourceProbes (sourceAction 1 (physical u+a • complement))=u := by
  have h := parameter_qualifies (join u a)
  rw [joined_split] at h
  rw [sourceProbes_eq_fieldProbes _ h.1,recover_split]

theorem source_physical_injective :
    Function.Injective (fun u => sourceAction 1 (physical u)) := by
  have hleft : Function.LeftInverse sourceProbes (fun u => sourceAction 1 (physical u)) := by
    intro u
    simpa only [zero_smul,add_zero] using recover_source u 0
  exact hleft.injective

theorem source_invisible_iff_field (A : Mat) (hA : Qualifies A) :
    sourceAction 1 A=0 ↔ action A=0 := by
  constructor
  · intro hs
    apply (finite_probe_iff A hA).mp
    rw [← sourceProbes_eq_fieldProbes A hA.1,hs,sourceProbes_zero]
  · exact field_invisible_implies_source 1 A

theorem source_kernel (d : ℝ) (hd : d≠0) (A : Mat) (hA : Qualifies A) :
    sourceAction d A=0 ↔ ∃ a : ℝ, A=a • complement := by
  rw [scale_preserves_kernel d hd,source_invisible_iff_field A hA,invisible_iff A hA]

theorem source_finite_certificate (A : Mat) (hA : Qualifies A) :
    sourceProbes (sourceAction 1 A)=0 ↔ sourceAction 1 A=0 := by
  rw [sourceProbes_eq_fieldProbes _ hA.1,finite_probe_iff A hA,
    source_invisible_iff_field A hA]

/-- The separate duality direction is invisible to stress even when it moves the field. -/
theorem hodge_source_zero (d : ℝ) : sourceAction d PDTHodgeConnection.H=0 := by
  funext v
  change firstVariation d v (PDTHodgeConnection.H *ᵥ v)=0
  unfold firstVariation crossInvariant
  rw [field_actual_hodge]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dualField,field,metric,eta,Matrix.diagonal,PDTMaxwellSymbol.mink] <;> ring_nf <;> simp

theorem hodge_field_nonzero : action PDTHodgeConnection.H≠0 := by
  intro h
  have he := congrArg (fun f : Action => f (Pi.single 0 1) 2 3) h
  simp only [action,field_actual_hodge] at he
  change (1 : ℝ)=0 at he
  norm_num at he

theorem hodge_not_qualifies : ¬Qualifies PDTHodgeConnection.H := by
  intro h
  exact hodge_field_nonzero ((source_invisible_iff_field _ h).mp (hodge_source_zero 1))

theorem zero_coupling_control (A : Mat) : sourceAction 0 A=0 := by
  rw [source_scale,zero_smul]

#print axioms source_hasDerivAt
#print axioms variation_field_zero
#print axioms field_invisible_implies_source
#print axioms source_scale
#print axioms scale_preserves_kernel
#print axioms sourceProbes_zero
#print axioms sourceProbes_eq_fieldProbes
#print axioms recover_source
#print axioms source_physical_injective
#print axioms source_invisible_iff_field
#print axioms source_kernel
#print axioms source_finite_certificate
#print axioms hodge_source_zero
#print axioms hodge_field_nonzero
#print axioms hodge_not_qualifies
#print axioms zero_coupling_control
end
end PDTSourceActionKernel
