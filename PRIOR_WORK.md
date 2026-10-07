# Prior work and the contribution of this package

The uniqueness of the electromagnetic energy-momentum tensor is classical. This formalization does not claim to originate
it. It was checked against the literature by statement on 6 October 2026.

**V. Fock**, *The Theory of Space, Time and Gravitation*, 2nd rev. ed. (Pergamon, 1964), section 31* and Appendix B.
For a symmetric tensor whose components are functions of the six field components only, the six infinitesimal Lorentz
covariance equations together with vanishing divergence on source-free Maxwell solutions give alpha times the Maxwell
stress plus lambda times the metric, and the condition T(0) = 0 removes lambda. This contains the covariance corollary of
`smoothClassification` and the normalization step in `smoothZeroFieldSelection`. It does not contain the quadratic
certificate, the conservation-only selection, or the sourceful statement.

**B. Kerrighan**, "An electromagnetic energy-momentum tensor uniqueness theorem", *J. Math. Phys.* 23 (1982), 1979-1980.
In the general-covariant concomitant framework, the metric and the Maxwell stress are the only symmetric rank-two
concomitants of a bivector and the metric whose divergence vanishes on source-free Maxwell solutions. This overlaps
`conservationSelection` (flat frame, quadratic class, explicit certificate); neither contains the other.

**S. C. Anco and J. Pohjanpelto**, "Classification of local conservation laws of Maxwell's equations", *Acta Appl. Math.*
69 (2001), 285-327. The complete classification of local conservation laws of Maxwell's equations. Its order-zero,
position-independent sector yields the conservation selection and the shape of the seventeen-parameter family
(constants, elementary linear currents, the stress) as an unstated corollary. The symmetric-tensor form and the explicit
cross family are not stated there; whether the cross family coincides exactly with the symmetric assembly of their
elementary linear currents has not been checked against the Lean statement and is not asserted.

**J. Navarro and J. B. Sancho**, "Energy and electromagnetism of a differential k-form", *J. Math. Phys.* 53 (2012),
102501, Theorem 3.5. Naturality, scale independence and a sourceful divergence identity give the Maxwell stress with its
coefficient fixed by the current. `differentiableNormalizedSelection` reaches the same conclusion on a fixed flat frame
under different and weaker hypotheses (everywhere differentiable; no naturality or scale axiom).

**Rainich, Misner-Wheeler, Bergqvist-Hoglund** (algebraic Rainich theory) run in the opposite direction, from the stress
to the field, and are not uniqueness-of-form results. Derivations that assume a Lagrangian (Gotay-Marsden, and the
Belinfante-Rosenfeld tradition) are likewise a different question. D. Lovelock's 1974 concomitant theorems are relevant
by title; the paper was not retrieved and no specific hypothesis set is attributed to it here.

**Formalizations.** A search on 6 October 2026 of Mathlib, physlib (formerly PhysLean), the Archive of Formal Proofs,
Lean4PHYS, Lean Zulip and the Palomar registry found the field strength and Lorentz equivariance (physlib) but no
formalized stress tensor, conservation statement or uniqueness statement. That is a dated search result, not a priority
claim.

## The contribution

A kernel-checked, constructive development on the explicit six-component register in one flat frame: the 209-equation
certificate equivalent to the two laws on the 210-coefficient quadratic class, with exact coefficient recovery; the
conservation-only selection with covariance, trace zero and Hodge invariance derived; the C^3 classification into an
explicit seventeen-parameter family without polynomiality, naturality or symmetry-of-origin assumptions; the
differentiable-only sourceful statement in which the current fixes the coefficient; and the necessity counterexamples
as theorems. These certificates and the exact register formulas are usable independently of any physical reading.
