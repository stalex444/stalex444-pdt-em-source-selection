# The mathematics

## Objects

Fix the flat metric eta = diag(1,1,1,-1) on R^4. The six real components x : Fin 6 -> R of an antisymmetric 4x4 field
are placed in a fifteen-slot register by `embed` (slots 01, 02, 03, 12, 13, 23) and read back as the field tensor
`field (embed x)`. The Minkowski pairing `mink`, the invariant `F.F`, and the Maxwell stress of scale d,

    stress d F = d * ( mink (F mu) (F nu) - eta_{mu nu} * invariant F / 4 ),

are defined exactly as displayed in `Challenge.lean`. Here "Maxwell stress" names the 4x4 electromagnetic
energy-momentum tensor F_{mu alpha} F_nu^alpha - (1/4) eta_{mu nu} F.F in signature (+,+,+,-), not its 3x3 spatial
block; sign and scale are carried by d. A *source* is a function S : Local -> Tensor.

Six Lorentz generators are displayed as integer 4x4 tables (`lorentzTable`), with the induced action on the six
components (`fieldAction`) and on tensors (`tensorAction k T = L_k T + T L_k^T`). The six tables are a basis of
so(3,1), so *covariance* is proper infinitesimal Lorentz covariance (parity and time reversal are not imposed), the
derivative law

    d/dt S(x + t fieldAction k x)|_{t=0} = tensorAction k (S x)      for all k, x, entries,

and *trace-free* is S x 00 + S x 11 + S x 22 - S x 33 = 0. The *homogeneous quadratic* class `source c` is
parameterized by all 210 coefficients (`Coeff`, ten tensor entries times twenty-one degree-two monomials; symmetry is
built in by `tensorIndex`, and no constant or linear term is admitted); `constraints` is the displayed list of 209
linear coefficient equations. "Quadratic" below always means this homogeneous class.

Index convention, which the definitions fix but do not name: the six slots hold the contravariant components F^{mu nu}
with index 3 the time direction, `tensorAction` is the induced action on a contravariant rank-two tensor, and a first
jet D : Fin 4 -> Local assigns to each coordinate mu the partial derivative d_mu of the six components. Under that
reading `bianchiJet` is the complete Bianchi set, `sourcedCurrent 1` is d_mu F^{mu nu}, and `stress 1` is the textbook
energy-momentum tensor with T^{33} = (E^2 + B^2)/2. The *divergence* of S at x along D is `sum_mu d/dt S(x + t D mu) mu nu`
(`deriv`, which is zero on a non-differentiable function; every compared statement assumes a polynomial, C^3 or
differentiable source, so nothing is vacuous). `bianchiJet` and `sourcedCurrent` express the Bianchi identity and the
current of a jet; a *vacuum jet* satisfies Bianchi with zero current (nonzero vacuum jets exist: the static field
E = (y, x, 0) gives one, and the research module `ConservationJets` carries a basis of sixteen). *Conserved* means zero
divergence on every vacuum jet; the *exchange law* at stiffness k requires, on every Bianchi-compatible jet,
divergence S x D = exchange (embed x) (sourcedCurrent k D). The polynomial family `conservedFamily A b d = constant A +
linear (crossCoefficients b) x + registerStress d (embed x)` is explicit (ten constants, six cross parameters, one
scale). The cross term is the polarization of the stress at a constant bivector: registerStress 1 (b + x) =
registerStress 1 b + linear (crossCoefficients b) x + registerStress 1 x (research module `CrossSource`,
`cross_stress_increment`; not among the compared statements).

## The twelve statements

| declaration | statement |
|---|---|
| `quadraticSelection` | For quadratic S: Covariant S and TraceFree S iff S = registerStress d (embed .) for some d. |
| `quadraticUniqueness` | The scale d is unique. |
| `finiteCertificate` | constraints c = 0 iff Covariant (source c) and TraceFree (source c). |
| `conservationSelection` | For quadratic S: Conserved S iff S is the Maxwell stress of some scale. |
| `conservationHodgeInvariance` | A conserved quadratic source satisfies S (J x) = S x for the displayed Hodge map J. |
| `smoothClassification` | RegularSource S (symmetric, globally C^3) and Conserved S iff S = conservedFamily A b d for some A, b, d. |
| `smoothZeroFieldSelection` | For C^3 conserved covariant S: S 0 = 0 iff TraceFree S iff S is the Maxwell line. |
| `differentiableSourcefulClassification` | For differentiable symmetric S: ExchangeLaw k S iff S = conservedFamily A 0 k. |
| `differentiableNormalizedSelection` | ... and S 0 = 0 then gives S = registerStress k (embed .). |
| `traceNecessity` | eta times the invariant is covariant and not trace-free. |
| `covarianceNecessity` | diag(x0^2, -x0^2, 0, 0) is trace-free and not covariant. |
| `smoothNecessity` | A conserved C^3 cross term is not covariant (covariance is necessary); the constant eta is conserved, covariant and not trace-free (the zero-field normalization is necessary). |

## How the proofs go

The quadratic selection evaluates the two laws on unit fields and pair sums, which yields the 209 coefficient
equations directly inside Lean; an exact rational certificate recovers every coefficient from those equations and one
anchor, and the recovered line is identified with the displayed stress at scale d = 1, entry by entry (including the
signs and the 1/2 entries of the coefficient vector). The
conservation-only route uses sixteen admissible vacuum jets to reach the same 209 readings, so covariance and trace
zero are consequences. The C^3 route shows the actual derivative of a conserved source satisfies a linear certificate
at every field, forces the background Jacobian to be scalar, and integrates by the mean-value theorem; the
differentiable-only sourceful route constrains the first derivative directly, with four current probes fixing the
background to k F, and integrates. The necessity statements are explicit evaluations.

## What is not claimed

The sources are field-only functions on one flat frame. No spacetime dependence, curved geometry, global solution, or
physical coupling value is asserted. The necessity statements cover the two laws and the zero-field normalization only;
the research modules also exhibit conserved sources that are not homogeneous (a constant metric), not symmetric, and
C^3 but not conserved, but those controls are not among the compared statements. Nine of the fifteen register slots are
inert in every compared statement (the register is inherited from the ported infrastructure). The correspondence
between the six-parameter cross family and the elementary linear conservation laws of Maxwell's equations was verified
by exact computation in review (PRIOR_WORK.md) and is not a formalized claim.
