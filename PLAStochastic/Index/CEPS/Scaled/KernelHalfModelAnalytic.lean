import PLAStochastic.Index.CEPS.Scaled.KernelHalfFactors
import PLAStochastic.Index.CEPS.Scaled.PositiveMarkerGap

/-! # Actual cumulant inputs pay the finite half-line model's analytic denominators -/

noncomputable section
open Complex Set Metric MeasureTheory Filter Topology
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW f : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsCumulantJet_variance_ne_zero (hfW : ∀ y, fW y = f (1 - y)) :
    cepsJet f (cepsJetCode (.inl 0)) ≠ 0 := by
  have hκ := cepsJet_cumulant_eq hW hθ hD hfW 0
  simp only [zero_add, iteratedDeriv_succ, iteratedDeriv_zero, deriv_deriv_cepsCgf_zero hW hθ hD] at hκ
  have he : cepsJet f (cepsJetCode (.inl 0)) = cepsStepVar ρW := by exact_mod_cast hκ.symm
  rw [he]
  exact (cepsStepVar_pos hW hθ hD).ne'

include dom hW hθ hD in
theorem cepsKernelHalfEntranceJetModel_cepsJet_analyticAt (hfW : ∀ y, fW y = f (1 - y))
    (N : ℕ) (lam : ℝ) (hlam : 1 ≤ lam) {z : ℂ} (hz : 0 ≤ z.re) :
    AnalyticAt ℂ (cepsKernelHalfEntranceJetModel (cepsJet f) N lam z) 0 := by
  have hR : 0 < dom.pairPolynomialScaleBase N 0 / (1 + |lam| + Real.sqrt ‖z‖) := by
    positivity [pairPolynomialScaleBase_pos dom hW hθ hD N 0]
  have hGap := cepsScaledPositiveMarkerGap_norm_lower dom hW hθ hD N 0 lam hlam hz (mem_ball_self hR)
  have hroot : cepsScaledSignedRoot D θ ρW lam z (-1) 0 ≠ 0 := by
    have he := norm_pos_iff.mp ((positiveMarkerGapLower_pos dom hW hθ hD).trans_le hGap)
    simpa only [zero_mul, zero_sub, neg_ne_zero] using he
  have hmodel : cepsCumulantRootModel (cepsJet f) N lam z (-1) N 0 ≠ 0 := by
    rw [cepsCumulantRootModel_cepsJet_zero dom hW hθ hD hfW N lam hz (by norm_num) N]
    exact hroot
  exact cepsKernelHalfEntranceJetModel_analyticAt (cepsJet f) N lam z
    (cepsCumulantJet_variance_ne_zero hW hθ hD hfW) hmodel

end PGM
