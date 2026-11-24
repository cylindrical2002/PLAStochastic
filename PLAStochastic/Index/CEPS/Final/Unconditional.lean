import PLAStochastic.Index.CEPS.Final.KernelJetFinal
import PLAStochastic.Index.CEPS.Strip.FinalInputs
import PLAStochastic.Index.CEPS.Central.Interface

/-!
# P-CEPS: the unconditional all-order expansion

The outer strip budgets (`Strip/`) and the central exact-root kernel (`Central/`) discharge
`CepsKernelPackages`; hence the kernel-jet representation holds and `gepC ε / ε²` has a unique
all-order expansion in powers of `ε⁻¹` with leading coefficient
`optimalMeanConstant / optimalDispersionConstant`.
-/

namespace PGM

/-- The kernel packages hold. -/
theorem cepsKernelPackages_holds : CepsKernelPackages where
  pair := cepsStripPairBudget_holds
  endpoint := cepsStripEndpointBudget_holds
  discount := cepsDiscountBudget_holds
  bridge := cepsStripBridgeAnalytic_holds
  central := cepsCentralPairKernel_holds

/-- The remaining kernel-jet premise of P-CEPS holds. -/
theorem cepsKernelJetRepresentation_holds : CepsKernelJetRepresentation :=
  cepsKernelJetRepresentation_of_packages cepsKernelPackages_holds

/-- The analytic interfaces of the one-layer family expansion hold. -/
theorem cepsTransformInterfaces_holds : CepsTransformInterfaces :=
  cepsTransformInterfaces_of_kernelJets cepsKernelJetRepresentation_holds

/-- **P-CEPS.** `gepC ε / ε²` has a unique all-order expansion in powers of `ε⁻¹`, with leading
coefficient `optimalMeanConstant / optimalDispersionConstant`. -/
theorem gepC_asymptoticExpansion :
    ∃! a : ℕ → ℝ, (∀ M : ℕ, ∃ K eps0 : ℝ, ∀ eps : ℝ, eps0 ≤ eps →
      |gepC eps / eps ^ 2 - ∑ j ∈ Finset.range (M + 1), a j * eps ^ (-(j : ℤ))| ≤
        K * eps ^ (-((M : ℤ) + 1))) ∧
      a 0 = BrownianAffine.optimalMeanConstant / BrownianAffine.optimalDispersionConstant :=
  gepC_asymptoticExpansion_of_kernelJets cepsKernelJetRepresentation_holds

end PGM
