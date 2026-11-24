import PLAStochastic.Index.CEPS.Scaled.KernelPairModel
import PLAStochastic.Index.CEPS.Scaled.KernelHalfFrequencyJets
import PLAStochastic.Index.CEPS.Scaled.PositivePairError
import PLAStochastic.Index.CEPS.Scaled.SurrogateHalfEntranceHolomorphy
import PLAStochastic.ForMathlib.Analysis.Complex.TaylorJetTimeOperator

/-! # Exact complete positive-side half-line pair jets in the finite model -/

noncomputable section
open Complex Set Metric MeasureTheory Filter Topology PowerSeries
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} (dom : CepsCanonDomain D θ v) (hθ : 0 < θ) (hD : 0 < D)

set_option maxHeartbeats 600000 in
include hθ hD in
theorem cepsScaledSurrogateHalfPair_taylorJets_eq_finite_model :
    ∃ r : ℝ, 0 < r ∧ ∀ {ρW : Measure ℝ} {fW f : ℝ → ℝ} {m : ℕ} {η : ℝ},
      IsStepLaw ρW fW D θ v → (∀ y, fW y = f (1 - y)) → (∀ x, x < 0 → f x = 0) →
      0 < η → CepsSobolevClass m η f → CepsSobolevClass m η fW → 2 * dom.c₀ ≤ η →
      ∫ x, |f x - cepsLambdaDensity x| ≤ r →
      ∀ N : ℕ, N + 2 ≤ m → ∀ (lam : ℝ), 1 ≤ lam → ∀ {z : ℂ}, 0 ≤ z.re → ∀ j ≤ N,
        coeff j (complexTaylorSeries (cepsScaledSurrogateHalfPair dom ρW N lam z) 0) =
        coeff j (complexTaylorSeries (cepsKernelHalfPairJetModel (cepsJet f) N lam z) 0) := by
  obtain ⟨rJ, hrJ, heJ⟩ := cepsScaledSurrogateHalfFactors_taylorJets_eq_finite_model dom hθ hD
  obtain ⟨rV, hrV, heV⟩ := cepsScaledSurrogateHalfBridge_frequency_taylorJets_eq_finite_model dom hθ hD
  refine ⟨min rJ rV, lt_min hrJ hrV, ?_⟩
  intro ρW fW f m η hW hfW hneg hη hf hfS hηc hclose N hN lam hlam z hz
  have heU := heJ hW hfW hneg hη hf hfS hηc (hclose.trans (min_le_left _ _)) N hN lam hz
  have heD := heV hW hfW hneg hη hf hfS hηc (hclose.trans (min_le_right _ _)) N hN lam hlam hz
  obtain ⟨BF, hBF, hFB, hFE⟩ := cepsKernelHalfFactors_cepsJet_frequency_neighborhood dom hW hθ hD hfW N lam hlam hz
  have hRA : 0 < min (dom.jointRootScaleRadius lam z)
      (dom.entranceScaleRadius N (cepsSobolev m η fW) lam z) :=
    lt_min (jointRootScaleRadius_pos dom hW hθ hD lam z)
      (entranceScale_constants dom hW hθ hD N (cepsSobolev m η fW) lam z).1
  obtain ⟨BA, hBA, hAB, hAD⟩ := cepsScaledSurrogateHalfBridge_holomorphic_near_joint
    dom hW hθ hD hfS hηc N (by omega) lam hz (Or.inl (by linarith)) (mem_ball_self hRA)
  have hEA : 0 < dom.pairPolynomialScaleBase N (cepsSobolev m η fW) / (1 + |lam| + Real.sqrt ‖z‖) := by
    positivity [pairPolynomialScaleBase_pos dom hW hθ hD N (cepsSobolev m η fW)]
  have hAE := (cepsScaledSurrogateHalfEntrance_differentiableOn dom hW hθ hD hfS hηc
    (M := cepsSobolev m η fW) N (by omega) lam hlam hz).analyticAt (ball_mem_nhds _ hEA)
  have hFD := differentiableOn_deriv_snd (isOpen_ball.prod isOpen_ball) hFB
  exact complexTaylorSeries_coeff_eq_completePair hAE (analyticAt_slice_fst_on_polydisc hBF hFE)
    (analyticAt_slice_fst_on_polydisc hBA hAB) (analyticAt_slice_fst_on_polydisc hBF hFB)
    (analyticAt_slice_fst_on_polydisc hBA hAD) (analyticAt_slice_fst_on_polydisc hBF hFD)
    N lam z (heU.2 hlam) heU.1 heD

end PGM
