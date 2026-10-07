# Selection of the electromagnetic source tensor

**Stephanie Alexander** · Lean 4.35.0-rc2 · MIT

Which symmetric tensor-valued functions of an electromagnetic field can serve as its source? On a fixed flat Lorentz
frame, this formalization answers that question four times over, with increasingly weak hypotheses, and each time the
answer is the Maxwell stress tensor.

1. Among all symmetric quadratic sources (210 free coefficients), the six infinitesimal Lorentz covariance equations and
   zero trace select the Maxwell stress up to a unique real scale, and 209 displayed linear equations certify both laws.
2. Conservation alone - vanishing divergence on every source-free Maxwell/Bianchi first jet - selects the same line;
   covariance, trace zero and Hodge invariance follow.
3. Every globally C^3 symmetric conserved source lies in an explicit seventeen-parameter family; with covariance, zero
   field value is equivalent to zero trace and to the stress line.
4. Under the sourceful exchange law at current stiffness k, every everywhere-differentiable symmetric source is a
   constant plus the Maxwell stress of scale exactly k; zero field value selects the stress.

Explicit counterexamples show that each hypothesis is necessary.

The principal statement is [Challenge.lean](Challenge.lean); [Solution.lean](Solution.lean) proves its twelve declarations
through [StatementBridge.lean](StatementBridge.lean). All definitions in the Challenge import Mathlib alone.
[MATHEMATICS.md](MATHEMATICS.md) gives the precise statements and claim map, [PRIOR_WORK.md](PRIOR_WORK.md) situates them
against the classical uniqueness theorems, and [VERIFICATION.md](VERIFICATION.md) records what was checked.

## Scope

Uniqueness of the Maxwell stress tensor is classical: Fock (1964, Appendix B), Kerrighan (1982), Navarro-Sancho (2012),
and the classification of Maxwell conservation laws by Anco and Pohjanpelto (2001). This package does not claim that
result as new. Its contribution is the constructive, kernel-checked development on the explicit six-component register:
finite certificates, exact coefficient recovery, the conservation-only and differentiable-only routes, and the necessity
counterexamples as theorems.

Sources are functions of the six field components only, on one flat frame; no curved geometry or global solution is
constructed. Pisot Dimensional Theory motivates the frame and the operators. Selecting a physical coupling is outside
these claims.
