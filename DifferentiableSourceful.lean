module
public import SourcefulControls

@[expose] public section
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
namespace PDTSourcefulSelection
noncomputable section
open PDTStressTensor PDTUnrestrictedSourceKernel PDTQuadraticSource PDTConservedSource PDTPolynomialSource PDTSmoothSource PDTStressBalance
open scoped Matrix

/-- Only ordinary everywhere Frechet differentiability is supplied. Continuity
of the derivative, C3 smoothness and a polynomial ansatz are not required. -/
def DifferentiableSource (S : Local → Tensor) : Prop :=
  (∀ x, (S x).transpose=S x) ∧ ∀ i j, Differentiable ℝ (fun x => S x i j)

set_option linter.unusedTactic false in
theorem exchange_probe_injective (b c : Local)
    (h : ∀ a : Fin 4, exchange (embed b) (Pi.single a 1)=exchange (embed c) (Pi.single a 1)) : b=c := by
  ext j
  fin_cases j
  · have hh := congrFun (h 1) 0
    norm_num [exchange,embed,field,PDTMaxwellSymbol.mink,Pi.single_apply] at hh
    try dsimp at hh
    all_goals norm_num at hh
    all_goals exact hh
  · have hh := congrFun (h 2) 0
    norm_num [exchange,embed,field,PDTMaxwellSymbol.mink,Pi.single_apply] at hh
    try dsimp at hh
    all_goals norm_num at hh
    all_goals exact hh
  · have hh := congrFun (h 3) 0
    norm_num [exchange,embed,field,PDTMaxwellSymbol.mink,Pi.single_apply] at hh
    try dsimp at hh
    all_goals norm_num at hh
    all_goals exact hh
  · have hh := congrFun (h 2) 1
    norm_num [exchange,embed,field,PDTMaxwellSymbol.mink,Pi.single_apply] at hh
    try dsimp at hh
    all_goals norm_num at hh
    all_goals exact hh
  · have hh := congrFun (h 3) 1
    norm_num [exchange,embed,field,PDTMaxwellSymbol.mink,Pi.single_apply] at hh
    try dsimp at hh
    all_goals norm_num at hh
    all_goals exact hh
  · have hh := congrFun (h 3) 2
    norm_num [exchange,embed,field,PDTMaxwellSymbol.mink,Pi.single_apply] at hh
    try dsimp at hh
    all_goals norm_num at hh
    all_goals exact hh

theorem exchange_field_scale (k : ℝ) (x : Local) (j : PDTMaxwellSymbol.Four) :
    exchange (embed (k • x)) j=exchange (embed x) (k • j) := by
  ext ν
  fin_cases ν <;> simp [exchange,embed,field,PDTMaxwellSymbol.mink] <;> ring

theorem linear_divergence_cross (b : Local) (D : Jet) :
    linearDivergence (crossCoefficients b) D=stressDivergence 1 (embed b) (registerJet D) := by
  funext ν
  unfold linearDivergence
  simp only [cross_original_variation]
  rfl

/-- At every field value the actual first derivative is forced directly by
vacuum jets together with the four nonzero-current probes. -/
theorem exchange_differentiable_gradient (k : ℝ) (f : Components)
    (hf : ∀ t, Differentiable ℝ (f t)) (he : ExchangeLaw k (assembled f)) (x : Local) :
    gradient f x=crossCoefficients (k • x) := by
  have hgrad := conserved_gradient f hf (exchange_implies_conservation k _ he) x
  have hb : (fun a => bg f a x)=k • x := by
    apply exchange_probe_injective
    intro a
    have hh := he x (currentJet a) (current_jet_bianchi a)
    rw [assembled_divergence f hf,hgrad,linear_divergence_cross,
      stress_balance 1 _ _ (current_jet_bianchi a),current_jet_current,
      one_smul,current_jet_current] at hh
    exact hh.trans (exchange_field_scale k x (Pi.single a 1)).symm
  rw [hb] at hgrad
  exact hgrad

theorem differentiable_assembled_selection (k : ℝ) (f : Components)
    (hf : ∀ t, Differentiable ℝ (f t)) (he : ExchangeLaw k (assembled f)) :
    ∃ A, assembled f=conservedFamily A 0 k := by
  let A : ConstantCoeff := fun t => f t 0
  have hentry (t : Fin 10) (x : Local) :
      f t x=conservedFamily A 0 k x (tensorPair t).1 (tensorPair t).2 := by
    let g : Local → ℝ := fun z => conservedFamily A 0 k z (tensorPair t).1 (tensorPair t).2
    have hg : Differentiable ℝ g := (family_contDiff A 0 k _ _).differentiable (by norm_num)
    have hz : ∀ a, pd a ((f t)-g)=0 := by
      intro a
      funext z
      unfold pd
      rw [fderiv_sub (hf t z) (hg z)]
      change pd a (f t) z-pd a g z=0
      have hh := congrFun (congrFun (exchange_differentiable_gradient k f hf he z) t) a
      change pd a (f t) z=crossCoefficients (k • z) t a at hh
      rw [hh,family_partial,tensor_pair_index,zero_add,sub_self]
    have hh := partials_zero_constant ((f t)-g) ((hf t).sub hg) hz x
    change f t x-g x=f t 0-g 0 at hh
    have hg0 : g 0=f t 0 := by
      simp only [g,conserved_family_at_zero,constant,tensor_pair_index,A]
    rw [hg0,sub_self] at hh
    exact sub_eq_zero.mp hh
  refine ⟨A,?_⟩
  funext x
  ext i j
  change f (tensorIndex i j) x=conservedFamily A 0 k x i j
  rw [hentry]
  exact tensor_entry_recovery _ ((regular_family A 0 k).1 x) i j

/-- The sourceful classification requires only differentiability, not C3. -/
theorem differentiable_sourceful_classification (k : ℝ) (S : Local → Tensor)
    (hd : DifferentiableSource S) : ExchangeLaw k S ↔ ∃ A, S=conservedFamily A 0 k := by
  constructor
  · intro he
    let f : Components := fun t x => S x (tensorPair t).1 (tensorPair t).2
    have hs : assembled f=S := by
      funext x
      ext i j
      exact tensor_entry_recovery (S x) (hd.1 x) i j
    obtain ⟨A,hA⟩ := differentiable_assembled_selection k f (fun t => hd.2 _ _) (hs ▸ he)
    exact ⟨A,hs.symm.trans hA⟩
  · rintro ⟨A,rfl⟩
    exact fixed_scale_converse A k

/-- Polynomial form and hence the earlier C3 regularity are now conclusions. -/
theorem sourceful_forces_regular (k : ℝ) (S : Local → Tensor)
    (hd : DifferentiableSource S) (he : ExchangeLaw k S) : RegularSource S := by
  obtain ⟨A,rfl⟩ := (differentiable_sourceful_classification k S hd).mp he
  exact regular_family A 0 k

theorem differentiable_sourceful_unique (k : ℝ) (S : Local → Tensor)
    (hd : DifferentiableSource S) (he : ExchangeLaw k S) : ∃! A, S=conservedFamily A 0 k :=
  sourceful_constant_unique k S (sourceful_forces_regular k S hd he) he

theorem differentiable_normalized_selection (k : ℝ) (S : Local → Tensor)
    (hd : DifferentiableSource S) (he : ExchangeLaw k S) (h0 : S 0=0) :
    S=fun x => registerStress k (embed x) :=
  normalized_source_selection k S (sourceful_forces_regular k S hd he) he h0

theorem differentiable_geometric_consequences (k : ℝ) (S : Local → Tensor)
    (hd : DifferentiableSource S) (he : ExchangeLaw k S) (h0 : S 0=0) :
    Covariant S ∧ TraceFree S ∧ (∀ x, S (J *ᵥ x)=S x) :=
  normalized_geometric_consequences k S (sourceful_forces_regular k S hd he) he h0

#print axioms exchange_probe_injective
#print axioms exchange_field_scale
#print axioms linear_divergence_cross
#print axioms exchange_differentiable_gradient
#print axioms differentiable_assembled_selection
#print axioms differentiable_sourceful_classification
#print axioms sourceful_forces_regular
#print axioms differentiable_sourceful_unique
#print axioms differentiable_normalized_selection
#print axioms differentiable_geometric_consequences
end
end PDTSourcefulSelection
