module
public import LorentzFrame

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! Actual directional derivatives and the connection transformation law.
The derivative variable may parameterize a curve or one coordinate direction.
This constructs neither a spacetime metric nor a curvature field. -/
namespace PDTMovingConnection
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

abbrev End (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] := E →L[ℝ] E

def transformedConnection (L U dL Ω : End E) : End E :=
  (L.comp Ω).comp U - dL.comp U

/-- The derivative-of-frame term cancels the inhomogeneous connection term. -/
theorem connection_cancellation (L U dL Ω : End E)
    (hUL : U.comp L = ContinuousLinearMap.id ℝ E) (a da : E) :
    dL a + L da + transformedConnection L U dL Ω (L a) =
      L (da + Ω a) := by
  have hi : U (L a) = a := by
    exact congrArg (fun T : End E => T a) hUL
  simp [transformedConnection, hi]
  abel

/-- Product differentiation, rather than a supplied formal derivative symbol,
gives covariance along a differentiable varying frame. -/
theorem covariant_derivative_transforms
    (L : ℝ → End E) (a : ℝ → E) (t : ℝ) (dL Ω U : End E) (da : E)
    (hL : HasDerivAt L dL t) (ha : HasDerivAt a da t)
    (hUL : U.comp (L t) = ContinuousLinearMap.id ℝ E) :
    deriv (fun s => L s (a s)) t +
      transformedConnection (L t) U dL Ω (L t (a t)) =
      L t (da + Ω (a t)) := by
  rw [(hL.clm_apply ha).deriv]
  exact connection_cancellation (L t) U dL Ω hUL _ _

/-- Requiring covariance for every field value uniquely fixes the connection
at this point, once frame, inverse, derivative and old connection are supplied. -/
theorem transformed_connection_unique (L U dL Ω C : End E)
    (hUL : U.comp L = ContinuousLinearMap.id ℝ E)
    (hLU : L.comp U = ContinuousLinearMap.id ℝ E)
    (hC : ∀ a da, dL a + L da + C (L a) = L (da+Ω a)) :
    C = transformedConnection L U dL Ω := by
  ext b
  have hi : L (U b) = b := by
    exact congrArg (fun T : End E => T b) hLU
  have hc := hC (U b) 0
  have ht := connection_cancellation L U dL Ω hUL (U b) 0
  rw [hi] at hc ht
  exact add_left_cancel (hc.trans ht.symm)

/-- A constant scalar response commutes with the covariant derivative.
This applies to r=rho*Q without altering the supplied connection. -/
theorem constant_response_parallel (r : ℝ) (Ω : End E)
    (a : ℝ → E) (t : ℝ) (da : E) (ha : HasDerivAt a da t) :
    deriv (fun s => r • a s) t + Ω (r • a t) =
      r • (da + Ω (a t)) := by
  have hd : HasDerivAt (fun s => r • a s) (r • da) t := by
    have hc := (hasDerivAt_const t (r • ContinuousLinearMap.id ℝ E)).clm_apply ha
    simpa only [zero_apply, zero_add,
      smul_apply, ContinuousLinearMap.id_apply] using hc
  rw [hd.deriv]
  simp [smul_add]

#print axioms connection_cancellation
#print axioms covariant_derivative_transforms
#print axioms transformed_connection_unique
#print axioms constant_response_parallel
end
end PDTMovingConnection
