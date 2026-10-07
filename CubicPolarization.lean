module
public import ExteriorAction

@[expose] public section
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
namespace PDTCubicPolarization
noncomputable section
open PDTExteriorAction PDTPfaffianCubic MvPolynomial
open scoped Matrix

def cubic (x : I → ℝ) : ℝ := eval x (pfaffian ℝ)
def polar (x u v : I → ℝ) : ℝ :=
  cubic (x+u+v)-cubic (x+u)-cubic (x+v)-cubic (u+v)+cubic x+cubic u+cubic v

private theorem triple_contract (x u v : I → ℝ) (a b d : I) :
    (∑ r : I, ∑ c : I, u r * tripleHessian ℝ x r c a b d * v c)=
    u b*v a*x d + u d*v a*x b + u a*v b*x d + u d*v b*x a +
    u a*v d*x b + u b*v d*x a := by
  simp [tripleHessian,delta,mul_add,add_mul,Finset.sum_add_distrib]
  ring

theorem hessian_polarization (x u v : I → ℝ) :
    dotProduct u (hessian ℝ x *ᵥ v)=polar x u v := by
  rw [hessian_formula]
  simp only [dotProduct,Matrix.mulVec,computedHessian,Finset.mul_sum,Finset.sum_mul]
  conv_lhs =>
    arg 2
    ext r
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  have hs (t : Fin 15) :
      (∑ r : I, ∑ c : I, u r * ((matchingSign t : ℝ) *
        tripleHessian ℝ x r c (matching t 0) (matching t 1) (matching t 2) * v c))=
      (matchingSign t : ℝ) * (u (matching t 1)*v (matching t 0)*x (matching t 2) +
        u (matching t 2)*v (matching t 0)*x (matching t 1) +
        u (matching t 0)*v (matching t 1)*x (matching t 2) +
        u (matching t 2)*v (matching t 1)*x (matching t 0) +
        u (matching t 0)*v (matching t 2)*x (matching t 1) +
        u (matching t 1)*v (matching t 2)*x (matching t 0)) := by
    rw [← triple_contract]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro c _
    ring
  simp_rw [hs]
  norm_num [polar,cubic,pfaffian_eval,matching_signs,matching,Fin.sum_univ_succ]
  ring!

#print axioms hessian_polarization
end
end PDTCubicPolarization
