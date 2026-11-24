import PLAStochastic.Index.GEP.Additive.UnconditionalHeight
import PLAStochastic.Index.GEP.Additive.LawForm

/-!
# P-GEP: additive endpoint (EP) height with the exact compression denominator in model G

Unconditional bound `|E H - log n / log C_ε| ≤ K` for `n ≥ 2` and `ε ≥ ε₀`.

## Main theorems

* `PGM.H_G_EP_additive`
* `PGM.H_G_EP_additive_law`: law form; `ε₀, K` depend only on the gap law `ν₀` and serve
  every probability space, iid sample with marginal `ν₀` and offset
* `PGM.tendsto_log_lawC_expPM_orbit`: the limit defining `gepLogC` exists for large `ε`

The all-order expansion of `C_ε` is the separate entry `PLAStochastic.Results.CEPS`.
-/
