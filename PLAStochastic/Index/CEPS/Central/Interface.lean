import PLAStochastic.Index.CEPS.Central.PairKernel
import PLAStochastic.Index.CEPS.Final.GlueConstruct

/-! # The central exact-root kernel in the form consumed by the final assembly -/

namespace PGM

/-- Package M: the central kernel hypothesis of the gluing construction holds for every
real reference vector with positive variance. -/
theorem cepsCentralPairKernel_holds (d N : ℕ) (p₀ : Fin d → ℝ)
    (hV : 0 < (cepsComplexJetPad d (fun i => (p₀ i : ℂ)) (cepsJetCode (.inl 0))).re) :
    CepsCentralPairKernel d N p₀ :=
  cepsCentralPairKernel_exists d N p₀ hV

end PGM
