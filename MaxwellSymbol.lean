module
public import EinsteinMaxwellInterface

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! The flat-space Maxwell principal symbol on the actual local +++- plane.
Time is coordinate 3. Wave-vector factors of i and the overall Fourier sign
are suppressed consistently: symbol = k² I - k ⊗ k_flat.
No full spacetime PDE or quantum dynamics is constructed here. -/
namespace PDTMaxwellSymbol
noncomputable section
open scoped Matrix

abbrev Four := Fin 4 → ℝ
def mink (a b : Four) : ℝ :=
  a 0*b 0 + a 1*b 1 + a 2*b 2 - a 3*b 3

def fieldTensor (k a : Four) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun μ ν => k μ*a ν-k ν*a μ

def symbol (k a : Four) : Four := mink k k • a - mink k a • k
def gauge (k a : Four) (c : ℝ) : Four := a+c • k
def conserved (k j : Four) : Prop := mink k j = 0
def quadratic (d : ℝ) (k a : Four) : ℝ :=
  (d/2)*(mink k k*mink a a-(mink k a)^2)
def sourcedQuadratic (d : ℝ) (k j a : Four) : ℝ :=
  quadratic d k a-mink j a

theorem field_gauge_invariant (k a : Four) (c : ℝ) :
    fieldTensor k (gauge k a c) = fieldTensor k a := by
  ext μ ν
  simp only [fieldTensor, gauge, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem bianchi (k a : Four) (μ ν σ : Fin 4) :
    k μ*fieldTensor k a ν σ + k ν*fieldTensor k a σ μ +
      k σ*fieldTensor k a μ ν = 0 := by
  unfold fieldTensor
  ring

/-- Contracting k_flat with the contravariant field strength gives the symbol. -/
theorem field_contraction (k a : Four) (ν : Fin 4) :
    k 0*fieldTensor k a 0 ν + k 1*fieldTensor k a 1 ν +
      k 2*fieldTensor k a 2 ν - k 3*fieldTensor k a 3 ν = symbol k a ν := by
  simp [fieldTensor, symbol, mink, smul_eq_mul]
  ring

theorem symbol_gauge_invariant (k a : Four) (c : ℝ) :
    symbol k (gauge k a c) = symbol k a := by
  ext ν
  simp [symbol, gauge, mink, smul_eq_mul]
  ring

theorem symbol_conserved (k a : Four) : conserved k (symbol k a) := by
  simp [conserved, symbol, mink, smul_eq_mul]
  ring

/-- Source gauge invariance is exactly the conserved-current condition. -/
theorem source_gauge_iff (k j a : Four) :
    (∀ c : ℝ, mink j (gauge k a c) = mink j a) ↔ conserved k j := by
  constructor
  · intro h
    have hc := h 1
    dsimp [gauge, mink, conserved] at *
    simp only [one_mul] at hc
    nlinarith only [hc]
  · intro h c
    have hc : mink j (gauge k a c) = mink j a+c*mink k j := by
      dsimp [gauge, mink]
      ring
    change mink k j = 0 at h
    rw [hc, h, mul_zero, add_zero]

theorem quadratic_gauge_invariant (d : ℝ) (k a : Four) (c : ℝ) :
    quadratic d k (gauge k a c) = quadratic d k a := by
  dsimp [quadratic, gauge, mink]
  ring

theorem sourced_gauge_invariant (d : ℝ) (k j a : Four)
    (hj : conserved k j) (c : ℝ) :
    sourcedQuadratic d k j (gauge k a c) = sourcedQuadratic d k j a := by
  rw [sourcedQuadratic, quadratic_gauge_invariant,
    (source_gauge_iff k j a).mpr hj c]
  rfl

/-- Exact directional expansion; its linear term is the Maxwell source equation. -/
theorem first_variation (d t : ℝ) (k j a b : Four) :
    sourcedQuadratic d k j (a+t • b) =
      sourcedQuadratic d k j a + t*mink (d • symbol k a-j) b +
        t^2*quadratic d k b := by
  simp [sourcedQuadratic, quadratic, symbol, mink, smul_eq_mul]
  ring

theorem stationary_iff (d : ℝ) (k j a : Four) :
    (∀ b : Four, mink (d • symbol k a-j) b = 0) ↔ d • symbol k a = j := by
  constructor
  · intro h
    have h0 := h ![1,0,0,0]
    have h1 := h ![0,1,0,0]
    have h2 := h ![0,0,1,0]
    have h3 := h ![0,0,0,1]
    simp [mink] at h0 h1 h2 h3
    ext i
    fin_cases i <;> simp_all <;> linarith
  · intro h b
    simp [h, mink]

/-- Away from k²=0, a conserved source has a transverse representative with
coefficient e²/k². This is a mode inverse, without a causal pole prescription. -/
theorem conserved_source_solution (k j : Four) (hj : conserved k j)
    (hk : mink k k ≠ 0) (e2 : ℝ) :
    let a := (e2 / mink k k) • j
    conserved k a ∧ symbol k a = e2 • j := by
  try dsimp
  have hm : mink k ((e2/mink k k) • j) = (e2/mink k k)*mink k j := by
    simp [mink, smul_eq_mul]
    ring
  have hz : mink k ((e2/mink k k) • j) = 0 := by
    rw [hm, hj, mul_zero]
  constructor
  · exact hz
  · unfold symbol
    rw [hz]
    ext i
    simp [smul_eq_mul]
    field_simp

/-- Gauge freedom remains an exact degeneracy of the source solution. -/
theorem sourced_solution_gauge (k j a : Four) (e2 c : ℝ)
    (h : symbol k a = e2 • j) :
    symbol k (gauge k a c) = e2 • j := by
  rw [symbol_gauge_invariant, h]

#print axioms field_gauge_invariant
#print axioms bianchi
#print axioms field_contraction
#print axioms symbol_conserved
#print axioms source_gauge_iff
#print axioms sourced_gauge_invariant
#print axioms first_variation
#print axioms stationary_iff
#print axioms conserved_source_solution
end
end PDTMaxwellSymbol
