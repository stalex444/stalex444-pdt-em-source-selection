module
public import HessianCovariance

@[expose] public section
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
namespace PDTGeometricTransport
noncomputable section
open PDTPfaffianCubic PDTPfaffianBridge PDTCubicInvariance PDTHessianCovariance
open GravityScreening GravityScreening.ResponseClosureGeometry
open MvPolynomial
open scoped Matrix Matrix.Norms.Elementwise

/-- Actual derivative along any supplied differentiable real field-register curve. -/
theorem pfaffian_hasDerivAt (f : ℝ → I → ℝ) (df : I → ℝ) (t : ℝ)
    (hf : HasDerivAt f df t) :
    HasDerivAt (fun s => eval (f s) (pfaffian ℝ)) (directional ℝ (f t) df) t := by
  have hc (i : I) : HasDerivAt (fun s => f s i) (df i) t :=
    hasDerivAt_pi.mp hf i
  simp only [pfaffian,map_sum,map_mul,eval_C,eval_X,directional]
  apply HasDerivAt.fun_sum
  intro i _
  have hd := (((hc (matching i 0)).const_mul (matchingSign i : ℝ)).mul
    (hc (matching i 1))).mul (hc (matching i 2))
  change HasDerivAt (fun s => (matchingSign i : ℝ)*f s (matching i 0)*
    f s (matching i 1)*f s (matching i 2)) _ t at hd
  simpa only [Pi.mul_apply,mul_add,add_mul,mul_assoc,add_assoc] using hd

theorem geometric_derivative_zero (w : I → ℝ) (f : ℝ → I → ℝ) (t : ℝ)
    (hf : HasDerivAt f (connection ℝ w *ᵥ f t) t) :
    HasDerivAt (fun s => eval (f s) (pfaffian ℝ)) 0 t := by
  simpa only [connection_invariance] using pfaffian_hasDerivAt f _ t hf

/-- Any supplied globally differentiable geometric flow conserves the cubic. -/
theorem geometric_flow_preserves (w : ℝ → I → ℝ) (f : ℝ → I → ℝ)
    (hf : ∀ t, HasDerivAt f (connection ℝ (w t) *ᵥ f t) t) (a b : ℝ) :
    eval (f a) (pfaffian ℝ)=eval (f b) (pfaffian ℝ) := by
  have hd (t : ℝ) := geometric_derivative_zero (w t) f t (hf t)
  exact is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt)
    (fun t => (hd t).deriv) a b

def continuousHessian : (I → ℝ) →L[ℝ] Matrix I I ℝ :=
  LinearMap.toContinuousLinearMap (jordanMap ℝ)

theorem hessian_hasDerivAt (f : ℝ → I → ℝ) (df : I → ℝ) (t : ℝ)
    (hf : HasDerivAt f df t) :
    HasDerivAt (fun s => raisedHessian ℝ (f s)) (raisedHessian ℝ df) t := by
  have hd := continuousHessian.hasFDerivAt.comp_hasDerivAt t hf
  change HasDerivAt (fun s => jordanMap ℝ (f s)) (jordanMap ℝ df) t at hd
  simpa only [jordanMap_eq] using hd

def movingHodge (x : I → ℝ) : Matrix I I ℝ := -raisedHessian ℝ x

/-- The transported complementary reference gives the commutator evolution of Hodge. -/
theorem moving_hodge_transport (w : I → ℝ) (f : ℝ → I → ℝ) (t : ℝ)
    (hf : HasDerivAt f (connection ℝ w *ᵥ f t) t) :
    HasDerivAt (fun s => movingHodge (f s))
      (connection ℝ w*movingHodge (f t)-movingHodge (f t)*connection ℝ w) t := by
  have hd := (-continuousHessian).hasFDerivAt.comp_hasDerivAt t hf
  change HasDerivAt (fun s => -jordanMap ℝ (f s))
    (-jordanMap ℝ (connection ℝ w *ᵥ f t)) t at hd
  simp only [jordanMap_eq] at hd
  rw [← connection_covariance] at hd
  simpa only [movingHodge,Matrix.mul_neg,Matrix.neg_mul,neg_sub,neg_sub_neg] using hd

theorem initial_hodge : movingHodge (Pi.single 14 1)=PDTHodgeConnection.H := by
  exact hodge_cast ℝ

/-- Reversing the supplied complementary reference reverses the Hodge sign. -/
theorem reverse_reference (x : I → ℝ) : movingHodge (-x)= -movingHodge x := by
  simp only [movingHodge,← jordanMap_eq,map_neg,neg_neg]

def hodgeWitness : I → ℝ := Pi.single 0 1 + Pi.single 14 1

private theorem hodge_witness_action :
    PDTHodgeConnection.H *ᵥ hodgeWitness=Pi.single 9 1 := by
  have hc : ∀ i : I, ResponseClosureCertificate.hodge i 0+
      ResponseClosureCertificate.hodge i 14=(Pi.single 9 1 : I → ℤ) i := by
    decide +kernel
  rw [hodgeWitness,Matrix.mulVec_add,Matrix.mulVec_single_one,Matrix.mulVec_single_one]
  ext i
  change (hodgeComplement i 0 : ℝ)+(hodgeComplement i 14 : ℝ)=(Pi.single 9 1 : I → ℝ) i
  rw [← certificate_hodge,← Int.cast_add,hc]
  simp [Pi.single_apply]

/-- A concrete obstruction to treating the original Hodge as a cubic symmetry. -/
theorem hodge_changes_cubic :
    directional ℝ hodgeWitness (PDTHodgeConnection.H *ᵥ hodgeWitness)=1 := by
  rw [hodge_witness_action,directional_eval]
  norm_num [hodgeWitness,Pi.single_apply,Fin.ext_iff]

theorem hodge_not_cubic_invariant :
    ¬ ∀ x : I → ℝ, directional ℝ x (PDTHodgeConnection.H *ᵥ x)=0 := by
  intro h
  have hx := h hodgeWitness
  rw [hodge_changes_cubic] at hx
  norm_num at hx

#print axioms hodge_changes_cubic
#print axioms hodge_not_cubic_invariant

#print axioms pfaffian_hasDerivAt
#print axioms geometric_derivative_zero
#print axioms geometric_flow_preserves
#print axioms hessian_hasDerivAt
#print axioms moving_hodge_transport
#print axioms initial_hodge
#print axioms reverse_reference
end
end PDTGeometricTransport
