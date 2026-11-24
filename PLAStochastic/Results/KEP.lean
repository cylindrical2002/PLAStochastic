import PLAStochastic.Index.KEP.FirstOrderHeight
import PLAStochastic.Index.KEP.Additive.ConstantDensity
import PLAStochastic.Index.KEP.Additive.Reductions
import PLAStochastic.Index.KEP.Additive.LawForm

/-!
# P-KEP: unconditional endpoint height for every Model K density

The original sorted iid sample and actual endpoint hierarchy satisfy the
additive height bound with the exact universal denominator `gepC eps`.
For every fixed DensityK density, one constant covers all sufficiently large
epsilon and every sample size at least two. The proof uses only the density,
iid and law hypotheses. The imported actual reference and Poisson proofs
pay all count, tail, regularity, stopping and window-law inputs.

## Main theorems

* `PGM.H_K_EP`
* `PGM.H_K_EP_const_additive`
* `PGM.H_K_EP_additive`
* `PGM.H_K_EP_additive_law`: law form; `ε₀, K` depend only on the density and serve every
  probability space and iid sample with marginal `densityLaw f A B`
-/
