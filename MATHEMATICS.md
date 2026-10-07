# The mathematics

## Objects

Fix the flat metric eta = diag(1,1,1,-1) on R^4. The six real components x : Fin 6 -> R of an antisymmetric 4x4 field
are placed in a fifteen-slot register by `embed` (slots 01, 02, 03, 12, 13, 23) and read back as the field tensor
`field (embed x)`. The Minkowski pairing `mink`, the invariant `F.F`, and the Maxwell stress of scale d,

    stress d F = d * ( mink (F mu) (F nu) - eta_{mu nu} * invariant F / 4 ),

are defined exactly as displayed in `Challenge.lean`. A *source* is a function S : Local -> Tensor.

Six Lorentz generators are displayed as integer 4x4 tables (`lorentzTable`), with the induced action on the six
components (`fieldAction`) and on tensors (`tensorAction k T = L_k T + T L_k^T`). *Covariance* is the derivative law

    d/dt S(x + t fieldAction k x)|_{t=0} = tensorAction k (S x)      for all k, x, entries,

and *trace-free* is S x 00 + S x 11 + S x 22 - S x 33 = 0. The quadratic class is parameterized by all 210
coefficients (`Coeff`, ten tensor entries times twenty-one monomials); `constraints` is the displayed list of 209
linear coefficient equations.

A first jet D : Fin 4 -> Local assigns to each coordinate direction a field increment. The *divergence* of S at x along
D is `sum_mu d/dt S(x + t D mu) mu nu`. `bianchiJet` and `sourcedCurrent` express the Bianchi identity and the current
of a jet; a *vacuum jet* satisfies Bianchi with zero current. *Conserved* means zero divergence on every vacuum jet; the
*exchange law* at stiffness k requires, on every Bianchi-compatible jet, divergence S x D = exchange (embed x)
(sourcedCurrent k D). The polynomial family `conservedFamily A b d = constant A + linear (crossCoefficients b) x +
registerStress d (embed x)` is explicit (ten constants, six cross parameters, one scale).

## The twelve statements

| declaration | statement |
|---|---|
| `quadraticSelection` | For quadratic S: Covariant S and TraceFree S iff S = registerStress d (embed .) for some d. |
| `quadraticUniqueness` | The scale d is unique. |
| `finiteCertificate` | constraints c = 0 iff Covariant (source c) and TraceFree (source c). |
| `conservationSelection` | For quadratic S: Conserved S iff S is the Maxwell stress of some scale. |
| `conservationHodgeInvariance` | A conserved quadratic source satisfies S (J x) = S x for the displayed Hodge map J. |
| `smoothClassification` | RegularSource S (symmetric, globally C^3) and Conserved S imply S = conservedFamily A b d. |
| `smoothZeroFieldSelection` | For C^3 conserved covariant S: S 0 = 0 iff TraceFree S iff S is the Maxwell line. |
| `differentiableSourcefulClassification` | For differentiable symmetric S: ExchangeLaw k S iff S = conservedFamily A 0 k. |
| `differentiableNormalizedSelection` | ... and S 0 = 0 then gives S = registerStress k (embed .). |
| `traceNecessity` | eta times the invariant is covariant and not trace-free. |
| `covarianceNecessity` | diag(x0^2, -x0^2, 0, 0) is trace-free and not covariant. |
| `smoothNecessity` | A conserved cross term is not covariant; a conserved covariant source can have nonzero trace. |

## How the proofs go

The quadratic selection evaluates the two laws on unit fields and pair sums, which yields the 209 coefficient
equations directly inside Lean; an exact rational certificate recovers every coefficient from those equations and one
anchor, and the recovered line is identified with the displayed stress including its signs and the factor 1/2. The
conservation-only route uses sixteen admissible vacuum jets to reach the same 209 readings, so covariance and trace
zero are consequences. The C^3 route shows the actual derivative of a conserved source satisfies a linear certificate
at every field, forces the background Jacobian to be scalar, and integrates by the mean-value theorem; the
differentiable-only sourceful route constrains the first derivative directly, with four current probes fixing the
background to k F, and integrates. The necessity statements are explicit evaluations.

## What is not claimed

The sources are field-only functions on one flat frame. No spacetime dependence, curved geometry, global solution, or
physical coupling value is asserted. The correspondence between the six-parameter cross family and the elementary linear
conservation laws of Maxwell's equations is a remark, not a formalized claim.
