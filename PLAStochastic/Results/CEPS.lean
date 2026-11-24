import PLAStochastic.Index.CEPS.Final.Unconditional
import PLAStochastic.Index.CEPS.Work

/-!
# P-CEPS: all-order expansion of the exact compression constant

`gepC ε / ε²` has a unique all-order expansion in powers of `ε⁻¹`: for every `M` the error of the
order-`M` truncation is `O(ε^{-M-1})` as `ε → ∞`, and the leading coefficient is
`optimalMeanConstant / optimalDispersionConstant`.

## Main theorems

* `PGM.gepC_asymptoticExpansion`
* `PGM.cepsTransformInterfaces_holds`: the analytic interfaces of the one-layer family expansion
* `PGM.cepsKernelJetRepresentation_holds`: the finite kernel-jet representation of the normal
  coefficients

`PLAStochastic.Index.CEPS.Work` imports the remaining P-CEPS support modules.
-/
