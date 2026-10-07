module
public import SourcefulSelection

@[expose] public section
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
namespace PDTSourcefulSelection
noncomputable section
open PDTStressTensor PDTUnrestrictedSourceKernel PDTQuadraticSource PDTConservedSource PDTPolynomialSource PDTSmoothSource PDTStressBalance
open scoped Matrix

theorem zero_constant_family (k : ℝ) :
    conservedFamily 0 0 k=(fun x => registerStress k (embed x)) := by
  funext x
  simp only [conservedFamily,cross_zero,linear_zero_coefficients,add_zero]
  have hz : constant (0 : ConstantCoeff)=0 := by ext i j; rfl
  rw [hz,zero_add]

theorem original_full_exchange (k : ℝ) :
    RegularSource (fun x => registerStress k (embed x)) ∧
    ExchangeLaw k (fun x => registerStress k (embed x)) ∧
    registerStress k (embed 0)=0 := by
  rw [← zero_constant_family]
  exact ⟨regular_family 0 0 k,fixed_scale_converse 0 k,original_stress_zero k⟩

theorem normalized_source_iff (k : ℝ) (S : Local → Tensor) (hr : RegularSource S) :
    (ExchangeLaw k S ∧ S 0=0) ↔ S=fun x => registerStress k (embed x) := by
  constructor
  · rintro ⟨he,h0⟩
    exact normalized_source_selection k S hr he h0
  · rintro rfl
    exact (original_full_exchange k).2

/-- Fixing the current law forbids a different stress coefficient even though
that coefficient would still pass every vacuum conservation test. -/
theorem wrong_scale_control (d k : ℝ) (hne : d≠k) :
    Conserved (fun x => registerStress d (embed x)) ∧
    ¬ ExchangeLaw k (fun x => registerStress d (embed x)) := by
  refine ⟨original_conserved d,?_⟩
  intro he
  rw [← zero_constant_family] at he
  exact hne (exchange_scale_fixed 0 d k he)

theorem fixed_background_control (k : ℝ) :
    Conserved (conservedFamily 0 ![1,0,0,0,0,0] k) ∧
    ¬ ExchangeLaw k (conservedFamily 0 ![1,0,0,0,0,0] k) := by
  refine ⟨(conserved_family_converse _ _ _).2,?_⟩
  intro he
  have h := congrFun (exchange_background_zero _ _ _ _ he) 0
  norm_num at h

/-- Exchange fixes the field-dependent source, leaving genuine constant freedom. -/
theorem constant_offset_control (k : ℝ) :
    ExchangeLaw k (covariantFamily 1 k) ∧ Covariant (covariantFamily 1 k) ∧
    covariantFamily 1 k 0≠0 ∧ ¬ TraceFree (covariantFamily 1 k) := by
  refine ⟨?_,(covariant_family_converse 1 k).2.2,?_,?_⟩
  · rw [covariant_as_conserved]
    exact fixed_scale_converse _ _
  · intro hz
    have hh := (zero_field_iff_no_constant 1 k).mp hz
    norm_num at hh
  · rw [trace_free_iff_no_constant]
    norm_num

theorem zero_stiffness_selection (S : Local → Tensor) (hr : RegularSource S)
    (he : ExchangeLaw 0 S) (h0 : S 0=0) : S=0 := by
  rw [normalized_source_selection 0 S hr he h0]
  funext x
  ext i j
  simp [registerStress,stress]

/-- The same regular source cannot obey two distinct current normalizations. -/
theorem current_stiffness_unique (S : Local → Tensor) (hr : RegularSource S)
    (k l : ℝ) (hk : ExchangeLaw k S) (hl : ExchangeLaw l S) : k=l := by
  obtain ⟨A,rfl⟩ := (sourceful_classification k S hr).mp hk
  exact exchange_scale_fixed A k l hl

/-- Trace zero removes the metric constant after covariance is supplied. -/
theorem covariant_trace_selection (k : ℝ) (S : Local → Tensor) (hr : RegularSource S)
    (he : ExchangeLaw k S) (hv : Covariant S) (ht : TraceFree S) :
    S=fun x => registerStress k (embed x) := by
  obtain ⟨c,rfl⟩ := (sourceful_covariant_classification k S hr).mp ⟨he,hv⟩
  have hc := (trace_free_iff_no_constant c k).mp ht
  subst c
  funext x
  simp only [covariantFamily,zero_smul,zero_add]

#print axioms zero_constant_family
#print axioms original_full_exchange
#print axioms normalized_source_iff
#print axioms wrong_scale_control
#print axioms fixed_background_control
#print axioms constant_offset_control
#print axioms zero_stiffness_selection
#print axioms current_stiffness_unique
#print axioms covariant_trace_selection
end
end PDTSourcefulSelection
