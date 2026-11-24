import PLAStochastic.Index.CEPS.Scaled.CentralPairBudget

/-! # Uniform central complete-pair scale jets and Taylor remainders -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledSurrogatePair_central_scale_jet_le {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m) (lam : ℝ)
    (hlam : |lam| ≤ dom.centralFrequencyDriftRadius N M) {z : ℂ} (hz : 0 ≤ z.re)
    (hznorm : ‖z‖ < dom.centralFrequencyRadius N M) (n : ℕ) :
    ‖iteratedDeriv n (cepsScaledSurrogatePair dom ρW N lam z) 0‖ ≤
      (n.factorial : ℝ) * dom.centralPairBound N M / (dom.centralPairScaleRadius N M / 2) ^ n :=
  norm_iteratedDeriv_le_of_ball n (centralPairScaleRadius_pos dom hW hθ hD N M)
    (cepsScaledSurrogatePair_central_differentiableOn dom hW hθ hD hf hη hM N hN lam hlam hz hznorm)
    (fun _b hb => cepsScaledSurrogatePair_central_bound dom hW hθ hD hf hη hM N hN lam hlam hz hznorm hb)

include hW hθ hD in
theorem cepsScaledSurrogatePair_central_taylor_le {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m) (lam : ℝ)
    (hlam : |lam| ≤ dom.centralFrequencyDriftRadius N M) {z : ℂ} (hz : 0 ≤ z.re)
    (hznorm : ‖z‖ < dom.centralFrequencyRadius N M) (n : ℕ) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.centralPairScaleRadius N M / 2)) :
    ‖cepsScaledSurrogatePair dom ρW N lam z b - complexTaylorSum (cepsScaledSurrogatePair dom ρW N lam z) n 0 b‖ ≤
      ((n.factorial : ℝ) * dom.centralPairBound N M / (dom.centralPairScaleRadius N M / 4) ^ n) * ‖b‖ ^ n := by
  simpa only [sub_zero] using norm_sub_complexTaylorSum_le_of_ball n
    (centralPairScaleRadius_pos dom hW hθ hD N M)
    (cepsScaledSurrogatePair_central_differentiableOn dom hW hθ hD hf hη hM N hN lam hlam hz hznorm)
    (fun _b hb => cepsScaledSurrogatePair_central_bound dom hW hθ hD hf hη hM N hN lam hlam hz hznorm hb) hb

end PGM
