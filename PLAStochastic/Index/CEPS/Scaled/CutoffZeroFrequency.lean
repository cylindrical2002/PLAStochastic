import PLAStochastic.Index.CEPS.Scaled.TruePairZeroFrequency
import PLAStochastic.Index.CEPS.Scaled.TrueCutoffIntegrability

/-! # A genuine frequency difference bound for the actual fixed-cutoff integral -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def CepsCanonDomain.trueCutoffZeroFrequencyConstant {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (δ : ℝ) : ℝ :=
  8 * δ * (1 + δ) * dom.trueSubtractedPairZeroFrequencyConstant / dom.trueHalfZeroFrequencyBase

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledTrueSubtractedPair_zero_frequency_sub_le (M lam : ℝ) {b : ℝ}
    (hb : 0 < b) (hb1 : b ≤ 1)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueFrequencyScaleRadius M lam 0)) {z : ℂ}
    (hz : z ∈ ball 0 (dom.trueHalfZeroFrequencyBase * b / 2)) :
    ‖cepsScaledTrueSubtractedPair dom ρW lam z b - cepsScaledTrueSubtractedPair dom ρW lam 0 b‖ ≤
      4 * dom.trueSubtractedPairZeroFrequencyConstant / (dom.trueHalfZeroFrequencyBase * b ^ 3) *
        (1 + |lam|) * ‖z‖ := by
  have hr := mul_pos (trueHalfZeroFrequencyBase_pos dom hW hθ hD) hb
  obtain ⟨hd, hbound⟩ := cepsScaledTrueSubtractedPair_zero_frequency_budget dom hW hθ hD M lam hb hb1 hbs
  have ht := norm_sub_le_of_ball_half hr hd hbound hz (mem_ball_self (half_pos hr))
  simpa only [sub_zero] using ht.trans_eq (by ring)

include hW hθ hD in
theorem cepsScaledTrueCutoffPair_zero_frequency_integral_sub_le {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (hm : 2 ≤ m) {b δ : ℝ}
    (hb : 0 < b) (hb1 : b ≤ 1) (hδ0 : 0 ≤ δ) (hδ : δ ≤ dom.trueDecayScaleBase M / 4)
    {z : ℂ} (hz : z.re = 0)
    (hbz : b * (1 + Real.sqrt ‖z‖) < dom.trueDecayScaleBase M / 4)
    (hsmall : z ∈ ball 0 (dom.trueHalfZeroFrequencyBase * b / 2)) :
    ‖(∫ lam : ℝ, cepsScaledTrueCutoffPair dom ρW b δ z lam) -
      (∫ lam : ℝ, cepsScaledTrueCutoffPair dom ρW b δ 0 lam)‖ ≤
      dom.trueCutoffZeroFrequencyConstant δ / b ^ 5 * ‖z‖ := by
  classical
  let R := dom.trueHalfZeroFrequencyBase
  let K := dom.trueSubtractedPairZeroFrequencyConstant
  let S := closedBall (0 : ℝ) (δ / b)
  let C := 4 * K / (R * b ^ 3) * ((1 + δ) / b) * ‖z‖
  have hR : 0 < R := trueHalfZeroFrequencyBase_pos dom hW hθ hD
  have hK : 0 ≤ K := trueSubtractedPairZeroFrequencyConstant_nonneg dom hW hθ hD
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hS : MeasurableSet S := measurableSet_closedBall
  have hi : Integrable (S.indicator (fun _ : ℝ => C)) :=
    (integrableOn_const (isCompact_closedBall (0 : ℝ) (δ / b)).measure_ne_top).integrable_indicator hS
  have hb0 : b * (1 + Real.sqrt ‖(0 : ℂ)‖) < dom.trueDecayScaleBase M / 4 := by
    simp only [norm_zero, Real.sqrt_zero, add_zero, mul_one]
    nlinarith [Real.sqrt_nonneg ‖z‖]
  have hA := cepsScaledTrueCutoffPair_integrable dom hW hθ hD hf hη hM hm hb hδ hz hbz
  have hB := cepsScaledTrueCutoffPair_integrable dom hW hθ hD hf hη hM hm hb hδ (by simp) hb0
  rw [← integral_sub hA hB]
  have ht := norm_integral_le_of_norm_le
    (f := fun lam : ℝ => cepsScaledTrueCutoffPair dom ρW b δ z lam - cepsScaledTrueCutoffPair dom ρW b δ 0 lam)
    hi (ae_of_all _ fun lam => ?_)
  · rw [integral_indicator_const C hS] at ht
    have hvolume : volume.real S = 2 * δ / b := by
      change (volume S).toReal = _
      rw [Real.volume_closedBall, ENNReal.toReal_ofReal (by positivity)]
      ring
    rw [smul_eq_mul, hvolume] at ht
    exact ht.trans_eq (by
      unfold C CepsCanonDomain.trueCutoffZeroFrequencyConstant
      dsimp [K, R]
      ring)
  · have hmem : lam ∈ S ↔ |lam| ≤ δ / b := by
      simp only [S, mem_closedBall_zero_iff, Real.norm_eq_abs]
    by_cases hlam : |lam| ≤ δ / b
    · rw [indicator_of_mem (hmem.mpr hlam)]
      simp only [cepsScaledTrueCutoffPair, if_pos hlam]
      have hbs := ball_subset_ball (trueDecayScaleRadius_le_frequency dom M lam 0)
        (cepsScaledTrueDecay_mem_of_cutoff dom hW hθ hD ((cepsSobolev_nonneg m η fW).trans hM)
          hb hδ hb0 hlam)
      apply (cepsScaledTrueSubtractedPair_zero_frequency_sub_le dom hW hθ hD M lam hb hb1 hbs hsmall).trans
      have hX : 1 + |lam| ≤ (1 + δ) / b := by
        apply (le_div_iff₀ hb).mpr
        have hh := (le_div_iff₀ hb).mp hlam
        nlinarith
      dsimp [C, K, R]
      gcongr
    · rw [indicator_of_notMem (fun hm => hlam (hmem.mp hm))]
      simp only [cepsScaledTrueCutoffPair, if_neg hlam, sub_self, norm_zero, le_refl]

end PGM
