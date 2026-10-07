module
public import StatementBridge

@[expose] public section
namespace PDTSourceSelection
noncomputable section
open scoped Matrix

/-- Covariance and zero trace select the Maxwell stress line among all quadratic sources. -/
theorem quadraticSelection (S : Local → Tensor) (hq : IsQuadraticSource S) :
    (Covariant S ∧ TraceFree S) ↔ ∃ d : ℝ, S=fun x => registerStress d (embed x) :=
  quadraticSelection_proof S hq

/-- The selected scale is unique. -/
theorem quadraticUniqueness (S : Local → Tensor) (hq : IsQuadraticSource S)
    (hc : Covariant S) (ht : TraceFree S) :
    ∃! d : ℝ, S=fun x => registerStress d (embed x) :=
  quadraticUniqueness_proof S hq hc ht

/-- The 209 coefficient equations are equivalent to both laws on the quadratic class. -/
theorem finiteCertificate (c : Coeff) :
    constraints c=0 ↔ Covariant (source c) ∧ TraceFree (source c) :=
  finiteCertificate_proof c

/-- Conservation on all source-free jets selects the same line; no covariance or trace premise. -/
theorem conservationSelection (S : Local → Tensor) (hq : IsQuadraticSource S) :
    Conserved S ↔ ∃ d : ℝ, S=fun x => registerStress d (embed x) :=
  conservationSelection_proof S hq

/-- A conserved quadratic source is Hodge invariant. -/
theorem conservationHodgeInvariance (S : Local → Tensor) (hq : IsQuadraticSource S)
    (hc : Conserved S) (x : Local) : S (J *ᵥ x)=S x :=
  conservationHodgeInvariance_proof S hq hc x

/-- Every globally C³ symmetric conserved source lies in the seventeen-parameter family. -/
theorem smoothClassification (S : Local → Tensor) (hr : RegularSource S) (hc : Conserved S) :
    ∃ A : ConstantCoeff, ∃ b : Local, ∃ d : ℝ, S=conservedFamily A b d :=
  smoothClassification_proof S hr hc

/-- For C³ conserved covariant sources, zero field value ⇔ zero trace ⇔ the Maxwell line. -/
theorem smoothZeroFieldSelection (S : Local → Tensor) (hr : RegularSource S)
    (hc : Conserved S) (hv : Covariant S) :
    (S 0=0 ↔ TraceFree S) ∧
    (S 0=0 ↔ ∃ d : ℝ, S=fun x => registerStress d (embed x)) :=
  smoothZeroFieldSelection_proof S hr hc hv

/-- The sourceful exchange law at stiffness k classifies differentiable sources: a constant plus
the Maxwell stress of scale exactly k. -/
theorem differentiableSourcefulClassification (k : ℝ) (S : Local → Tensor)
    (hd : DifferentiableSource S) : ExchangeLaw k S ↔ ∃ A, S=conservedFamily A 0 k :=
  differentiableSourcefulClassification_proof k S hd

/-- Zero field value then selects the Maxwell stress with the current's stiffness. -/
theorem differentiableNormalizedSelection (k : ℝ) (S : Local → Tensor)
    (hd : DifferentiableSource S) (he : ExchangeLaw k S) (h0 : S 0=0) :
    S=fun x => registerStress k (embed x) :=
  differentiableNormalizedSelection_proof k S hd he h0

/-- Zero trace is necessary: η times the scalar invariant is covariant but not trace-free. -/
theorem traceNecessity :
    Covariant (source metricInvariantCoefficients) ∧
    ¬ TraceFree (source metricInvariantCoefficients) :=
  traceNecessity_proof

/-- Covariance is necessary: an anisotropic quadratic is trace-free but not covariant. -/
theorem covarianceNecessity :
    TraceFree (source anisotropicCoefficients) ∧
    ¬ Covariant (source anisotropicCoefficients) :=
  covarianceNecessity_proof

/-- In the smooth setting both laws remain necessary: a conserved cross term is not covariant,
and a conserved covariant source can carry nonzero trace. -/
theorem smoothNecessity :
    (RegularSource (conservedFamily 0 ![1,0,0,0,0,0] 0) ∧
      Conserved (conservedFamily 0 ![1,0,0,0,0,0] 0) ∧
      ¬ Covariant (conservedFamily 0 ![1,0,0,0,0,0] 0)) ∧
    (RegularSource (covariantFamily 1 0) ∧ Conserved (covariantFamily 1 0) ∧
      Covariant (covariantFamily 1 0) ∧ ¬ TraceFree (covariantFamily 1 0)) :=
  smoothNecessity_proof

end
end PDTSourceSelection

#print axioms PDTSourceSelection.quadraticSelection
#print axioms PDTSourceSelection.quadraticUniqueness
#print axioms PDTSourceSelection.finiteCertificate
#print axioms PDTSourceSelection.conservationSelection
#print axioms PDTSourceSelection.conservationHodgeInvariance
#print axioms PDTSourceSelection.smoothClassification
#print axioms PDTSourceSelection.smoothZeroFieldSelection
#print axioms PDTSourceSelection.differentiableSourcefulClassification
#print axioms PDTSourceSelection.differentiableNormalizedSelection
#print axioms PDTSourceSelection.traceNecessity
#print axioms PDTSourceSelection.covarianceNecessity
#print axioms PDTSourceSelection.smoothNecessity
