module
public import SourcefulLaw

@[expose] public section
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
namespace PDTSourcefulSelection
noncomputable section
open PDTStressTensor PDTUnrestrictedSourceKernel PDTQuadraticSource PDTConservedSource PDTPolynomialSource PDTSmoothSource PDTStressBalance
open scoped Matrix

theorem exchange_background_readings (A : ConstantCoeff) (b : Local) (d k : ℝ)
    (h : ExchangeLaw k (conservedFamily A b d)) (a : Fin 4) :
    exchange (embed b) (Pi.single a 1)=0 := by
  have hh := h 0 (currentJet a) (current_jet_bianchi a)
  simpa only [family_exchange _ _ _ _ _ (current_jet_bianchi a),exchange_zero_field,
    add_zero,current_jet_current,one_smul] using hh

set_option linter.unusedTactic false in
theorem exchange_background_zero (A : ConstantCoeff) (b : Local) (d k : ℝ)
    (h : ExchangeLaw k (conservedFamily A b d)) : b=0 := by
  have hz := exchange_background_readings A b d k h
  ext j
  fin_cases j
  · change b 0=0
    have hh := congrFun (hz 1) 0
    norm_num [exchange,embed,field,PDTMaxwellSymbol.mink,Pi.single_apply] at hh
    try dsimp at hh
    all_goals norm_num at hh
    all_goals linarith only [hh]
  · change b 1=0
    have hh := congrFun (hz 2) 0
    norm_num [exchange,embed,field,PDTMaxwellSymbol.mink,Pi.single_apply] at hh
    try dsimp at hh
    all_goals norm_num at hh
    all_goals linarith only [hh]
  · change b 2=0
    have hh := congrFun (hz 3) 0
    norm_num [exchange,embed,field,PDTMaxwellSymbol.mink,Pi.single_apply] at hh
    try dsimp at hh
    all_goals norm_num at hh
    all_goals linarith only [hh]
  · change b 3=0
    have hh := congrFun (hz 2) 1
    norm_num [exchange,embed,field,PDTMaxwellSymbol.mink,Pi.single_apply] at hh
    try dsimp at hh
    all_goals norm_num at hh
    all_goals linarith only [hh]
  · change b 4=0
    have hh := congrFun (hz 3) 1
    norm_num [exchange,embed,field,PDTMaxwellSymbol.mink,Pi.single_apply] at hh
    try dsimp at hh
    all_goals norm_num at hh
    all_goals linarith only [hh]
  · change b 5=0
    have hh := congrFun (hz 3) 2
    norm_num [exchange,embed,field,PDTMaxwellSymbol.mink,Pi.single_apply] at hh
    try dsimp at hh
    all_goals norm_num at hh
    all_goals linarith only [hh]

theorem exchange_scale_fixed (A : ConstantCoeff) (d k : ℝ)
    (h : ExchangeLaw k (conservedFamily A 0 d)) : d=k := by
  have hh := congrFun (h ![1,0,0,0,0,0] (currentJet 1) (current_jet_bianchi 1)) 0
  rw [family_exchange _ _ _ _ _ (current_jet_bianchi 1),exchange_zero_field,zero_add,
    current_jet_current,current_jet_current] at hh
  simpa [exchange,embed,field,PDTMaxwellSymbol.mink,Pi.single_apply] using hh

/-- Nonzero-current probes remove the background and fix the stress scale,
including when the supplied stiffness is zero. -/
theorem exchange_family_parameters (A : ConstantCoeff) (b : Local) (d k : ℝ)
    (h : ExchangeLaw k (conservedFamily A b d)) : b=0 ∧ d=k := by
  have hb := exchange_background_zero A b d k h
  subst b
  exact ⟨rfl,exchange_scale_fixed A d k h⟩

theorem sourceful_classification (k : ℝ) (S : Local → Tensor) (hr : RegularSource S) :
    ExchangeLaw k S ↔ ∃ A, S=conservedFamily A 0 k := by
  constructor
  · intro h
    obtain ⟨A,b,d,rfl⟩ := (smooth_conserved_classification S hr).mp (exchange_implies_conservation k S h)
    obtain ⟨hb,hd⟩ := exchange_family_parameters A b d k h
    subst b
    subst d
    exact ⟨A,rfl⟩
  · rintro ⟨A,rfl⟩
    exact fixed_scale_converse A k

theorem sourceful_constant_unique (k : ℝ) (S : Local → Tensor) (hr : RegularSource S)
    (h : ExchangeLaw k S) : ∃! A, S=conservedFamily A 0 k := by
  obtain ⟨A,hA⟩ := (sourceful_classification k S hr).mp h
  refine ⟨A,hA,?_⟩
  intro B hB
  exact (conserved_parameters_unique B A 0 0 k k (hB.symm.trans hA)).1

/-- Subtracting the zero-field source gives the original stress with the same
coefficient that appears in the prescribed current law. -/
theorem sourceful_field_difference (k : ℝ) (S : Local → Tensor) (hr : RegularSource S)
    (h : ExchangeLaw k S) (x : Local) : S x=S 0+registerStress k (embed x) := by
  obtain ⟨A,rfl⟩ := (sourceful_classification k S hr).mp h
  simp only [conservedFamily,cross_zero,linear_zero_coefficients,original_stress_zero,add_zero]

theorem normalized_source_selection (k : ℝ) (S : Local → Tensor) (hr : RegularSource S)
    (h : ExchangeLaw k S) (h0 : S 0=0) : S=fun x => registerStress k (embed x) := by
  funext x
  rw [sourceful_field_difference k S hr h x,h0,zero_add]

theorem sourceful_covariant_classification (k : ℝ) (S : Local → Tensor) (hr : RegularSource S) :
    ExchangeLaw k S ∧ Covariant S ↔ ∃ c, S=covariantFamily c k := by
  constructor
  · rintro ⟨he,hv⟩
    obtain ⟨c,d,hs⟩ := (smooth_covariant_classification S hr).mp
      ⟨exchange_implies_conservation k S he,hv⟩
    rw [hs,covariant_as_conserved] at he
    have hd := exchange_scale_fixed _ d k he
    exact ⟨c,hd ▸ hs⟩
  · rintro ⟨c,rfl⟩
    refine ⟨?_,(covariant_family_converse c k).2.2⟩
    rw [covariant_as_conserved]
    exact fixed_scale_converse _ _

theorem normalized_geometric_consequences (k : ℝ) (S : Local → Tensor) (hr : RegularSource S)
    (h : ExchangeLaw k S) (h0 : S 0=0) :
    Covariant S ∧ TraceFree S ∧ (∀ x, S (J *ᵥ x)=S x) := by
  rw [normalized_source_selection k S hr h h0]
  refine ⟨original_covariant k,original_trace_free k,?_⟩
  exact conservation_forces_hodge_invariance _ (original_is_quadratic k) (original_conserved k)

#print axioms exchange_background_readings
#print axioms exchange_background_zero
#print axioms exchange_scale_fixed
#print axioms exchange_family_parameters
#print axioms sourceful_classification
#print axioms sourceful_constant_unique
#print axioms sourceful_field_difference
#print axioms normalized_source_selection
#print axioms sourceful_covariant_classification
#print axioms normalized_geometric_consequences
end
end PDTSourcefulSelection
