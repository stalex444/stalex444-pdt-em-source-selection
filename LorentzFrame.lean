module
public import MaxwellResponse

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! Finite Lorentz-frame transport of the existing Maxwell principal symbol.
Metric preservation is supplied; it is not inferred from the PDT ruler. -/
namespace PDTLorentzFrame
noncomputable section
open PDTMaxwellSymbol

def IsLorentz (L : Four ≃ₗ[ℝ] Four) : Prop :=
  ∀ a b, mink (L a) (L b) = mink a b

variable (L : Four ≃ₗ[ℝ] Four) (hL : IsLorentz L)
include hL

theorem symbol_covariant (k a : Four) :
    symbol (L k) (L a) = L (symbol k a) := by
  simp only [symbol, hL k k, hL k a, map_sub, map_smul]

theorem conserved_covariant (k j : Four) :
    conserved (L k) (L j) ↔ conserved k j := by
  simp only [conserved, hL k j]

theorem sourced_action_invariant (d : ℝ) (k j a : Four) :
    sourcedQuadratic d (L k) (L j) (L a) = sourcedQuadratic d k j a := by
  simp only [sourcedQuadratic, quadratic, hL k k, hL a a, hL k a, hL j a]

theorem sourced_equation_covariant (d : ℝ) (k j a : Four)
    (h : d • symbol k a = j) :
    d • symbol (L k) (L a) = L j := by
  rw [symbol_covariant L hL, ← map_smul, h]

theorem free_equation_iff (k a : Four) :
    symbol (L k) (L a) = 0 ↔ symbol k a = 0 := by
  rw [symbol_covariant L hL]
  exact L.map_eq_zero_iff

omit hL in
theorem gauge_covariant (k a : Four) (c : ℝ) :
    PDTMaxwellSymbol.gauge (L k) (L a) c = L (PDTMaxwellSymbol.gauge k a c) := by
  simp [PDTMaxwellSymbol.gauge]

theorem transported_wave_is_null :
    mink (L PDTMaxwellHodge.waveVector) (L PDTMaxwellHodge.waveVector) = 0 := by
  rw [hL, PDTMaxwellHodge.waveVector_null]

/-- The complete free-potential solution, including its single gauge parameter,
transports to every wave-vector reached by the supplied Lorentz frame. -/
theorem transported_two_polarizations (a : Four)
    (ha : symbol (L PDTMaxwellHodge.waveVector) a = 0) :
    ∃! u : ℝ × ℝ × ℝ,
      a = L (PDTMaxwellSymbol.gauge PDTMaxwellHodge.waveVector
        (PDTMaxwellHodge.transverse u.1 u.2.1) u.2.2) := by
  have hpre : symbol PDTMaxwellHodge.waveVector (L.symm a) = 0 := by
    apply (free_equation_iff L hL _ _).mp
    simpa using ha
  obtain ⟨u, hu, huniq⟩ := PDTMaxwellHodge.two_polarizations (L.symm a) hpre
  refine ⟨u, ?_, ?_⟩
  · simpa using congrArg L hu
  · intro w hw
    apply huniq w
    simpa using congrArg L.symm hw

#print axioms symbol_covariant
#print axioms conserved_covariant
#print axioms sourced_action_invariant
#print axioms sourced_equation_covariant
#print axioms gauge_covariant
#print axioms transported_two_polarizations
end
end PDTLorentzFrame
