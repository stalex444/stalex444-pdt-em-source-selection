module
public import PolynomialSelection

@[expose] public section
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
namespace PDTPolynomialSource
noncomputable section
open PDTStressTensor PDTUnrestrictedSourceKernel PDTQuadraticSource PDTConservedSource
open scoped Matrix

theorem original_stress_zero (d : ℝ) : registerStress d (embed 0)=0 := by
  rw [← scaled_maxwell_original,quadratic_at_zero]

theorem conserved_family_at_zero (A : ConstantCoeff) (b : Local) (d : ℝ) :
    conservedFamily A b d 0=constant A := by
  simp only [conservedFamily,linear_at_zero,original_stress_zero,add_zero]

theorem covariant_family_at_zero (c d : ℝ) : covariantFamily c d 0=c • metric := by
  simp only [covariantFamily,original_stress_zero,add_zero]

theorem constant_injective : Function.Injective constant := by
  intro A B h
  ext t
  have hh := congrFun (congrFun h (tensorPair t).1) (tensorPair t).2
  fin_cases t <;> exact hh

theorem covariant_parameters_unique (c d c' d' : ℝ)
    (h : covariantFamily c d=covariantFamily c' d') : c=c' ∧ d=d' := by
  have h0 := congrFun (congrFun (congrFun h 0) 0) 0
  simp only [covariant_family_at_zero] at h0
  have hc : c=c' := by simpa [metric,eta,Matrix.diagonal_apply] using h0
  subst c'
  refine ⟨rfl,original_scale_unique d d' ?_⟩
  funext x
  have hh := congrFun h x
  exact add_left_cancel hh

/-- Both parameters are determined by the source function itself. -/
theorem covariant_polynomial_uniqueness (S : Local → Tensor) (hp : IsPolynomialSource S)
    (hc : Conserved S) (hv : Covariant S) :
    ∃! p : ℝ × ℝ, S=covariantFamily p.1 p.2 := by
  obtain ⟨c,d,hs⟩ := (covariant_conserved_polynomial_classification S hp).mp ⟨hc,hv⟩
  refine ⟨(c,d),hs,?_⟩
  rintro ⟨a,b⟩ hh
  obtain ⟨ha,hb⟩ := covariant_parameters_unique a b c d (hh.symm.trans hs)
  exact Prod.ext ha hb

/-- A concrete reading that distinguishes the constant, odd and even source parts. -/
theorem conserved_family_00 (A : ConstantCoeff) (b : Local) (d : ℝ) (x : Local) :
    conservedFamily A b d x 0 0=A 0+
      (b 0*x 0+b 1*x 1-b 2*x 2-b 3*x 3+b 4*x 4+b 5*x 5)+
      d/2*(x 0^2+x 1^2-x 2^2-x 3^2+x 4^2+x 5^2) := by
  norm_num [conservedFamily,constant,linear,crossCoefficients,tensorIndex,Fin.sum_univ_succ,
    registerStress,stress,field,embed,PDTMaxwellSymbol.mink,metric,eta,Matrix.diagonal_apply,invariant]
  try dsimp
  ring

set_option linter.unusedTactic false in
theorem conserved_parameters_unique (A A' : ConstantCoeff) (b b' : Local) (d d' : ℝ)
    (h : conservedFamily A b d=conservedFamily A' b' d') : A=A' ∧ b=b' ∧ d=d' := by
  have hA : A=A' := constant_injective (by
    simpa only [conserved_family_at_zero] using congrFun h 0)
  subst A'
  have hb : b=b' := by
    ext a
    fin_cases a
    · change b 0=b' 0
      have hp := congrFun (congrFun (congrFun h ![1,0,0,0,0,0]) 0) 0
      have hn := congrFun (congrFun (congrFun h ![-1,0,0,0,0,0]) 0) 0
      simp only [conserved_family_00] at hp hn
      norm_num at hp hn
      try dsimp at hp hn
      norm_num at hp hn
      linarith only [hp,hn]
    · change b 1=b' 1
      have hp := congrFun (congrFun (congrFun h ![0,1,0,0,0,0]) 0) 0
      have hn := congrFun (congrFun (congrFun h ![0,-1,0,0,0,0]) 0) 0
      simp only [conserved_family_00] at hp hn
      norm_num at hp hn
      try dsimp at hp hn
      norm_num at hp hn
      linarith only [hp,hn]
    · change b 2=b' 2
      have hp := congrFun (congrFun (congrFun h ![0,0,1,0,0,0]) 0) 0
      have hn := congrFun (congrFun (congrFun h ![0,0,-1,0,0,0]) 0) 0
      simp only [conserved_family_00] at hp hn
      norm_num at hp hn
      try dsimp at hp hn
      norm_num at hp hn
      linarith only [hp,hn]
    · change b 3=b' 3
      have hp := congrFun (congrFun (congrFun h ![0,0,0,1,0,0]) 0) 0
      have hn := congrFun (congrFun (congrFun h ![0,0,0,-1,0,0]) 0) 0
      simp only [conserved_family_00] at hp hn
      norm_num at hp hn
      try dsimp at hp hn
      norm_num at hp hn
      linarith only [hp,hn]
    · change b 4=b' 4
      have hp := congrFun (congrFun (congrFun h ![0,0,0,0,1,0]) 0) 0
      have hn := congrFun (congrFun (congrFun h ![0,0,0,0,-1,0]) 0) 0
      simp only [conserved_family_00] at hp hn
      norm_num at hp hn
      try dsimp at hp hn
      norm_num at hp hn
      linarith only [hp,hn]
    · change b 5=b' 5
      have hp := congrFun (congrFun (congrFun h ![0,0,0,0,0,1]) 0) 0
      have hn := congrFun (congrFun (congrFun h ![0,0,0,0,0,-1]) 0) 0
      simp only [conserved_family_00] at hp hn
      norm_num at hp hn
      try dsimp at hp hn
      norm_num at hp hn
      linarith only [hp,hn]
  subst b'
  refine ⟨rfl,rfl,original_scale_unique d d' ?_⟩
  funext x
  exact add_left_cancel (congrFun h x)

theorem conserved_polynomial_uniqueness (S : Local → Tensor) (hp : IsPolynomialSource S)
    (hc : Conserved S) :
    ∃! p : ConstantCoeff × Local × ℝ, S=conservedFamily p.1 p.2.1 p.2.2 := by
  obtain ⟨A,b,d,hs⟩ := (conserved_polynomial_classification S hp).mp hc
  refine ⟨(A,b,d),hs,?_⟩
  rintro ⟨B,e,f⟩ hh
  obtain ⟨hA,hb,hd⟩ := conserved_parameters_unique B A e b f d (hh.symm.trans hs)
  exact Prod.ext hA (Prod.ext hb hd)
#print axioms original_stress_zero
#print axioms conserved_family_at_zero
#print axioms covariant_family_at_zero
#print axioms constant_injective
#print axioms covariant_parameters_unique
#print axioms covariant_polynomial_uniqueness
#print axioms conserved_family_00
#print axioms conserved_parameters_unique
#print axioms conserved_polynomial_uniqueness
end
end PDTPolynomialSource
