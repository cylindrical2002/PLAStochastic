import PLAStochastic.Index.KRE.Uniform.Main
import PLAStochastic.Index.KRE.Exact.Integral

/-!
# P-KRE: uniform two-phase RE height in model K

The uniform two-phase height formula over the density class, and the exact
integer formula for a fixed nonconstant density outside both jump windows.
The latter includes the natural good event, the sorted-iid probability law,
and an explicit expectation error of at most `200 log N / N²`.

## Main theorems

* `PGM.K_RE_uniform`
* `PGM.K_RE_uniform_integral`
* `PGM.K_RE_fixed_density`
* `PGM.K_RE_exact`
* `PGM.K_RE_exact_probability`
* `PGM.K_RE_exact_integral`
-/
