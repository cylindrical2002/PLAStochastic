import PLAStochastic.Index.CEPS.Scaled.TrueDriftRoots
import PLAStochastic.Index.CEPS.Scaled.TrueDriftSlopes

/-! # Actual open real-drift charts on the fixed true frequency disc -/

noncomputable section
open Complex Set Metric MeasureTheory Filter Topology
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledTrue_drift_chart (M lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {b : ℝ} (hb : 0 < b)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueFrequencyScaleRadius M lam z)) :
    ∃ ε > 0,
      ‖(b : ℂ)‖ * dom.entranceSpatialScaleRadius lam z < dom.c₀ / 2 ∧
      (b : ℂ) * z ∈ ball (0 : ℂ) (dom.entranceSpatialScaleRadius lam z) ∧
      ContinuousOn (fun a : ℝ => cepsScaledSignedRoot D θ ρW a z 1 b) (ball lam ε) ∧
      ContinuousOn (fun a : ℝ => cepsScaledSignedRoot D θ ρW a z (-1) b) (ball lam ε) ∧
      ∀ a ∈ ball lam ε,
        (b : ℂ) ∈ ball (0 : ℂ) (dom.trueDenominatorScaleRadius M a z) ∧
        |b * a| < dom.μ₀ / 4 ∧ ‖cepsComplexScaledDiscount a z b‖ < dom.q₀ / 2 ∧
        0 ≤ (cepsComplexScaledDiscount a z b).re ∧
        cepsScaledSignedRoot D θ ρW a z 1 b ∈ ball 0 (dom.entranceSpatialScaleRadius lam z) ∧
        cepsScaledSignedRoot D θ ρW a z (-1) b ∈ ball 0 (dom.entranceSpatialScaleRadius lam z) := by
  have hbP := ball_subset_ball (trueFrequencyScaleRadius_le dom M lam z) hbs
  have hbD := ball_subset_ball (truePairScaleRadius_le dom M lam z) hbP
  have hbE := ball_subset_ball (trueDenominatorScaleRadius_le dom hW hθ hD M lam z) hbD
  have hbC := ball_subset_ball ((min_le_right _ _).trans
    (div_le_self (canonScaleRadius_pos dom hW hθ hD lam z).le (by norm_num))) hbE
  obtain ⟨hμc, hqc, _⟩ := canonScaleCurve_bounds dom hW hθ hD lam hz (sign := 1) (by norm_num) hbC
  have hμ : |b * lam| < dom.μ₀ / 4 := by
    have hh : ‖((b * lam : ℝ) : ℂ)‖ < dom.μ₀ / 8 := by simpa only [ofReal_mul] using hμc
    rw [norm_real, Real.norm_eq_abs] at hh
    linarith [dom.μ₀_pos]
  obtain ⟨_, _, hre, _, hw, _, _⟩ := cepsScaledTrueFrequency_curve_bounds dom hW hθ hD M lam hz hb hbs
  obtain ⟨hp, ha⟩ := cepsScaledSignedRootPlusMinus_continuousAt_drift dom hW hθ hD hb
    (hμ.le.trans (by linarith [dom.μ₀_pos])) (hqc.le.trans (half_le_self dom.q₀_pos.le)) hre
  have hpmem := entranceScaleCurve_roots_mem dom hW hθ hD 0 M lam hz
    (by norm_num : ‖(1 : ℂ)‖ ≤ 1) hbE
  have hamem := entranceScaleCurve_roots_mem dom hW hθ hD 0 M lam hz
    (by norm_num : ‖(-1 : ℂ)‖ ≤ 1) hbE
  have ht := entranceScaleCurve_mark_mem dom hD 0 M lam hbE
  have hS : ‖(b : ℂ)‖ * dom.entranceSpatialScaleRadius lam z < dom.c₀ / 2 := by
    have hh := entranceScaleCurve_product_bound dom hD 0 M lam hbE
    have hbase : dom.canonScaleBase ≤ dom.c₀ / 4 :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
    unfold CepsCanonDomain.entranceSpatialScaleRadius
    nlinarith [dom.c₀_pos]
  have hcR : Continuous (fun a : ℝ => dom.trueDenominatorScaleRadius M a z) := by
    unfold CepsCanonDomain.trueDenominatorScaleRadius
    apply continuous_const.div (by fun_prop)
    intro a
    have hh : 0 < 1 + |a| + Real.sqrt ‖z‖ := by positivity
    exact hh.ne'
  have h1 := hcR.tendsto lam (isOpen_Ioi.mem_nhds (mem_ball_zero_iff.mp hbD))
  have h2 : ∀ᶠ a : ℝ in 𝓝 lam, |b * a| < dom.μ₀ / 4 :=
    (continuous_const.mul continuous_id).abs.tendsto lam (isOpen_Iio.mem_nhds hμ)
  have hcq : Continuous (fun a : ℝ => cepsComplexScaledDiscount a z b) := by
    unfold cepsComplexScaledDiscount
    fun_prop
  have h3 := hcq.norm.tendsto lam (isOpen_Iio.mem_nhds hqc)
  have h4 : ∀ᶠ a : ℝ in 𝓝 lam, 0 < 1 + b * a :=
    (continuous_const.add (continuous_const.mul continuous_id)).tendsto lam
      (isOpen_Ioi.mem_nhds (by linarith : 0 < 1 + b * lam))
  have h5 := hp.eventually (isOpen_ball.mem_nhds hpmem)
  have h6 := ha.eventually (isOpen_ball.mem_nhds hamem)
  have hev : ∀ᶠ a : ℝ in 𝓝 lam,
      (b : ℂ) ∈ ball (0 : ℂ) (dom.trueDenominatorScaleRadius M a z) ∧
      |b * a| < dom.μ₀ / 4 ∧ ‖cepsComplexScaledDiscount a z b‖ < dom.q₀ / 2 ∧
      0 ≤ (cepsComplexScaledDiscount a z b).re ∧
      cepsScaledSignedRoot D θ ρW a z 1 b ∈ ball 0 (dom.entranceSpatialScaleRadius lam z) ∧
      cepsScaledSignedRoot D θ ρW a z (-1) b ∈ ball 0 (dom.entranceSpatialScaleRadius lam z) := by
    filter_upwards [h1, h2, h3, h4, h5, h6] with a ha1 ha2 ha3 ha4 ha5 ha6
    refine ⟨mem_ball_zero_iff.mpr ha1, ha2, ha3, ?_, ha5, ha6⟩
    have he : (cepsComplexScaledDiscount a z b).re = b ^ 2 * z.re * (1 + b * a) := by
      simp [cepsComplexScaledDiscount, mul_re, mul_im, pow_two]
    rw [he]
    exact mul_nonneg (mul_nonneg (sq_nonneg _) hz) ha4.le
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
  have hbounds : ∀ a ∈ ball lam ε,
      (b : ℂ) ∈ ball (0 : ℂ) (dom.trueDenominatorScaleRadius M a z) ∧
      |b * a| < dom.μ₀ / 4 ∧ ‖cepsComplexScaledDiscount a z b‖ < dom.q₀ / 2 ∧
      0 ≤ (cepsComplexScaledDiscount a z b).re ∧
      cepsScaledSignedRoot D θ ρW a z 1 b ∈ ball 0 (dom.entranceSpatialScaleRadius lam z) ∧
      cepsScaledSignedRoot D θ ρW a z (-1) b ∈ ball 0 (dom.entranceSpatialScaleRadius lam z) :=
    fun a ha => hball (mem_ball.mp ha)
  refine ⟨ε, hε, hS, ht, ?_, ?_, hbounds⟩
  · intro a ha
    exact (cepsScaledSignedRootPlusMinus_continuousAt_drift dom hW hθ hD hb
      ((hbounds a ha).2.1.le.trans (by linarith [dom.μ₀_pos]))
      ((hbounds a ha).2.2.1.le.trans (half_le_self dom.q₀_pos.le)) (hbounds a ha).2.2.2.1).1.continuousWithinAt
  · intro a ha
    exact (cepsScaledSignedRootPlusMinus_continuousAt_drift dom hW hθ hD hb
      ((hbounds a ha).2.1.le.trans (by linarith [dom.μ₀_pos]))
      ((hbounds a ha).2.2.1.le.trans (half_le_self dom.q₀_pos.le)) (hbounds a ha).2.2.2.1).2.continuousWithinAt

end PGM
