# Prior work and the contribution of this package

The uniqueness of the electromagnetic energy-momentum tensor is classical. This formalization does not claim to originate
it. It was checked against the literature by statement on 6 October 2026 and again on 7 October 2026
(`reviews/LITSCOUT_second_pass_2026-10-07.md`).

**V. Fock**, *The Theory of Space, Time and Gravitation*, 2nd rev. ed. (Pergamon, 1964), section 31* (pp. 98-100) and
Appendix B (pp. 411-416). For a symmetric tensor whose components are functions of the six field components only, the
six infinitesimal Lorentz covariance equations together with vanishing divergence on source-free Maxwell solutions give
alpha times the Maxwell stress plus lambda times the metric, and the condition T(0) = 0 removes lambda. This contains
the covariance corollary of `smoothClassification` and the normalization step in `smoothZeroFieldSelection`, for the
regularity Fock assumes (second partials are taken freely; the exact assumption was not checked against the text). It
does not contain the quadratic certificate, the conservation-only selection, or the sourceful statement.
**C. D. Collinson**, "Proof of the uniqueness of the electromagnetic energy momentum tensor", *Math. Proc. Cambridge
Philos. Soc.* 66 (1969), 437-438, doi:10.1017/S0305004100045175, gives Fock's theorem in four-dimensional covariant form
(abstract read; text not retrieved).

**D. Lovelock**, "The electromagnetic energy momentum tensor and its uniqueness", *Int. J. Theor. Phys.* 10 (1974),
59-65, doi:10.1007/BF01808316. Hypotheses, from pp. 59-60: a symmetric tensor concomitant of the metric, a field and its
first derivatives, general covariance, and a divergence identity of the form "divergence of B equals a free coefficient
tensor times the Maxwell current"; the conclusion is reported as essentially unique (pp. 61-65 not retrieved, so the
theorem statement and the fate of the metric term are not attributed here). Its divergence hypothesis is the closest
classical analogue of the exchange-law shape in `differentiableSourcefulClassification`, which fixes the coefficient to
the current stiffness and assumes neither covariance nor smoothness; the two overlap and neither contains the other.

**D. B. Kerrighan**, "On the uniqueness of the energy-momentum tensor for electromagnetism", *J. Math. Phys.* 23 (1982),
1979-1980, doi:10.1063/1.525217.
In the general-covariant concomitant framework, the metric and the Maxwell stress are the only symmetric rank-two
concomitants of a bivector and the metric whose divergence vanishes on source-free Maxwell solutions. This overlaps
`conservationSelection` (flat frame, quadratic class, explicit certificate); neither contains the other.

**S. C. Anco and J. Pohjanpelto**, "Classification of local conservation laws of Maxwell's equations", *Acta Appl. Math.*
69 (2001), 285-327, doi:10.1023/A:1014263903283. The complete classification of local conservation laws of Maxwell's
equations. Its order-zero, position-independent sector yields the conservation selection and the shape of the
seventeen-parameter family (constants, elementary linear currents, the stress) as an unstated corollary. The
symmetric-tensor form and the explicit cross family are not stated there. The six-parameter cross family coincides with
the symmetric assembly of their elementary linear currents F a + *F b with a a constant bivector and b its Hodge dual
(32 parameters reduce to 6 by symmetry alone), and equals the polarization T(F + a) - T(F) - T(a) of the Maxwell
stress; this identification was verified on 7 October 2026 by exact computation against the Lean definitions
(`reviews/litscout_second_pass_2026-10-07_scripts`), and the polarization identity is kernel-proved in the research
module `CrossSource`, but neither is among the compared statements. The C^3 regularity is not in Anco-Pohjanpelto,
who work with smooth jet functions.

**J. Navarro and J. B. Sancho**, "Energy and electromagnetism of a differential k-form", *J. Math. Phys.* 53 (2012),
102501, Theorem 3.5. For natural operators on a Lorentzian manifold, scale independence, vanishing at zero field, and a
sourceful divergence identity on closed forms give the Maxwell stress with its coefficient fixed by the current.
`differentiableNormalizedSelection` reaches the same conclusion under different and incomparable hypotheses: symmetric,
field-only sources on one fixed flat frame, everywhere differentiable, with the same zero-field normalization but no
naturality or scale axiom.

**Rainich, Misner-Wheeler, Bergqvist-Hoglund** (algebraic Rainich theory) run in the opposite direction, from the stress
to the field, and are not uniqueness-of-form results. Derivations that assume a Lagrangian (Gotay-Marsden, and the
Belinfante-Rosenfeld tradition) are likewise a different question. The textbook treatments (Landau-Lifshitz, *The
Classical Theory of Fields*, 4th rev. ed., sections 32-33, pp. 82-89; Jackson, *Classical Electrodynamics*, 3rd ed.,
section 12.10, pp. 605-612) derive the tensor and note that its definition is not unique without symmetry; they state
no uniqueness theorem.

**Formalizations.** A search on 6 October 2026 of Mathlib (by library structure), physlib (formerly PhysLean), the
Archive of Formal Proofs, Lean4PHYS, Lean Zulip and the Palomar registry (public feed from 2 September 2026 only) found
the field strength, Lorentz equivariance and charge conservation (physlib) but no electromagnetic energy-momentum
tensor, and no conservation or uniqueness statement for one. That is a dated search result with the stated coverage,
not a priority claim.

## The contribution

A kernel-checked, constructive development on the explicit six-component register in one flat frame: the 209-equation
certificate equivalent to the two laws on the 210-coefficient quadratic class, with exact coefficient recovery; the
conservation-only selection with covariance, trace zero and Hodge invariance derived; the C^3 classification (an
equivalence) into an explicit seventeen-parameter family without polynomiality, naturality or symmetry-of-origin
assumptions; the differentiable-only sourceful statement in which the current fixes the coefficient; and the necessity
counterexamples as theorems. The statements hold at finite regularity (globally C^3, and everywhere differentiable for
the sourceful route), where the classical arguments work with smooth jet functions or take second partials freely.
These certificates and the exact register formulas are usable independently of any physical reading.
