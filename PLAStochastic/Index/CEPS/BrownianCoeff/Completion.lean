import PLAStochastic.Index.CEPS.BrownianCoeff.Main
import PLAStochastic.Index.CEPS.BrownianCoeff.DriftIntegral

/-!
# Brownian zero-scale coefficients with the full drift integral

The kernel envelope holds for every real drift and every imaginary frequency,
including zero frequency, uniformly on the closed variance disc of radius
`v₀ / 16`. The full drift integral is genuinely integrable and holomorphic on
the corresponding open disc. The closed disc of radius `v₀ / 32` is therefore
an explicit common admissible disc with actual open holomorphy neighborhoods.

The half-line terms are estimated by their cancellation. Neither the actual
PLA coefficient identification nor positive-scale Taylor budgets are asserted here.
-/
