import PLAStochastic.Index.CEPS.Scaled.KernelPairModel
import PLAStochastic.Index.CEPS.Scaled.KernelBridgeFrequencyJets
import PLAStochastic.Index.CEPS.Scaled.KernelEntranceJets
import PLAStochastic.Index.CEPS.Scaled.TruePairScaling
import PLAStochastic.ForMathlib.Analysis.Complex.TaylorJetTimeOperator

/-! # Exact complete time-operator pair jets from the genuine finite model -/

noncomputable section
open Complex Set Metric MeasureTheory Filter Topology PowerSeries
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} (dom : CepsCanonDomain D θ v) (hθ : 0 < θ) (hD : 0 < D)

set_option maxHeartbeats 600000 in
include hθ hD in
theorem cepsScaledSurrogatePair_taylorJets_eq_finite_model :
    ∃ r : ℝ, 0 < r ∧ ∀ {ρW : Measure ℝ} {fW f : ℝ → ℝ} {m : ℕ} {η : ℝ},
      IsStepLaw ρW fW D θ v → (∀ y, fW y = f (1 - y)) → (∀ x, x < 0 → f x = 0) →
      0 < η → CepsSobolevClass m η f → CepsSobolevClass m η fW → 2 * dom.c₀ ≤ η →
      ∫ x, |f x - cepsLambdaDensity x| ≤ r →
      ∀ N : ℕ, N + 2 ≤ m → ∀ (lam : ℝ) {z : ℂ}, 0 ≤ z.re → (lam ≠ 0 ∨ z ≠ 0) → ∀ j ≤ N,
        coeff j (complexTaylorSeries (cepsScaledSurrogatePair dom ρW N lam z) 0) =
        coeff j (complexTaylorSeries (cepsKernelPairJetModel (cepsJet f) N lam z) 0) := by
  obtain ⟨rE, hrE, heE⟩ := cepsScaledSurrogateEntrance_taylorJets_eq_finite_model dom hθ hD
  obtain ⟨rU, hrU, heU⟩ := cepsScaledSurrogateBridge_taylorJets_eq_finite_model dom hθ hD
  obtain ⟨rV, hrV, heV⟩ := cepsScaledSurrogateBridge_frequency_taylorJets_eq_finite_model dom hθ hD
  obtain ⟨rF, hrF, heF⟩ := cepsKernelFiniteFactors_cepsJet_frequency_neighborhood hθ hD dom
  refine ⟨min rE (min rU (min rV rF)), lt_min hrE (lt_min hrU (lt_min hrV hrF)), ?_⟩
  intro ρW fW f m η hW hfW hneg hη hf hfS hηc hclose N hN lam z hz hne
  have hcloseE := hclose.trans (min_le_left _ _)
  have hcloseU := (hclose.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hcloseV := ((hclose.trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hcloseF := ((hclose.trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_right _ _)
  have heA := heE hW hfW hneg hη hf hfS hηc hcloseE N hN lam hz
  have heB := heU hW hfW hneg hη hf hfS hηc hcloseU N hN lam hz
  have heD := heV hW hfW hneg hη hf hfS hηc hcloseV N hN lam hz hne
  obtain ⟨BF, hBF, hFB, hFE⟩ := heF hW hfW hneg hη hf hfS hηc hcloseF N hN lam hz hne
  have hRA : 0 < min (dom.jointRootScaleRadius lam z)
      (dom.entranceScaleRadius N (cepsSobolev m η fW) lam z) :=
    lt_min (jointRootScaleRadius_pos dom hW hθ hD lam z)
      (entranceScale_constants dom hW hθ hD N (cepsSobolev m η fW) lam z).1
  obtain ⟨BA, hBA, hAB, hAD⟩ := cepsScaledSurrogateBridge_holomorphic_near_joint
    dom hW hθ hD hfS hηc le_rfl N (by omega) lam hz hne (mem_ball_self hRA)
  have hAE := (cepsScaledSurrogateEntrance_differentiableOn dom hW hθ hD hfS hηc le_rfl N (by omega) lam hz).analyticAt
    (ball_mem_nhds _ (entranceScale_constants dom hW hθ hD N (cepsSobolev m η fW) lam z).1)
  have hFD := differentiableOn_deriv_snd (isOpen_ball.prod isOpen_ball) hFB
  exact complexTaylorSeries_coeff_eq_completePair hAE (analyticAt_slice_fst_on_polydisc hBF hFE)
    (analyticAt_slice_fst_on_polydisc hBA hAB) (analyticAt_slice_fst_on_polydisc hBF hFB)
    (analyticAt_slice_fst_on_polydisc hBA hAD) (analyticAt_slice_fst_on_polydisc hBF hFD)
    N lam z heA heB heD

end PGM
