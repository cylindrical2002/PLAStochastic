import PLAStochastic.Index.CEPS.BrownianCoeff.LowerDrift
import PLAStochastic.Index.CEPS.BrownianCoeff.Removable
import PLAStochastic.Index.CEPS.BrownianCoeff.Endpoint

/-!
# Brownian coefficient functions for P-CEPS at zero scale

The variance disc has the explicit radius `v₀ / 16`. This entry collects the
principal-root estimates, nonvanishing strip denominator, analytically extended
entrance and bridge, agreement with the Brownian formulas, variance holomorphy,
joint removability at zero, and the endpoint exponential envelope.

`cepsBrownianKernel_lower_decay` establishes the kernel envelope for `lam < 1`,
including the whole negative-drift tail. The envelope for `lam ≥ 1` must use the
cancellation with the half-line term. That estimate and holomorphy of the
integral over all drifts remain open; this entry does not assert full C-13.
-/
