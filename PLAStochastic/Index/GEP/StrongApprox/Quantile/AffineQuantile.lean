import PLAStochastic.Index.GEP.StrongApprox.Quantile.DensitySandwich

/-! # WP5: density-to-quantile comparison with an arbitrary center and scale -/

namespace PGM

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory ProbabilityTheory Set Filter Topology

theorem SACDF.affine {F : ℝ → ℝ} (hF : SACDF F) (c : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    SACDF (fun x => F (c + σ * x)) := by
  refine ⟨hF.continuous.comp (continuous_const.add (continuous_const.mul continuous_id)),
    ?_, ?_, ?_⟩
  · intro x y hxy
    apply hF.strictMono
    linarith [mul_lt_mul_of_pos_left hxy hσ]
  · apply hF.atBot.comp
    rw [tendsto_atBot_atBot]
    intro b
    refine ⟨(b - c) / σ, fun x hx => ?_⟩
    have ht := (le_div_iff₀ hσ).mp hx
    linarith
  · apply hF.atTop.comp
    rw [tendsto_atTop_atTop]
    intro b
    refine ⟨(b - c) / σ, fun x hx => ?_⟩
    have ht := (div_le_iff₀ hσ).mp hx
    linarith

theorem SACDF.quantile_affine {F : ℝ → ℝ} (hF : SACDF F) (c : ℝ) {σ u : ℝ}
    (hσ : 0 < σ) (hu : u ∈ Ioo 0 1) :
    c + σ * saQuantile (fun x => F (c + σ * x)) u = saQuantile F u := by
  apply hF.strictMono.injective
  exact ((hF.affine c hσ).apply_quantile hu).trans (hF.apply_quantile hu).symm

/-- The interval comparison only requires the actual CDF derivative, so it is
stable under rescaling without constructing an auxiliary probability measure. -/
theorem saTail_sandwich_of_deriv {F q : ℝ → ℝ} (hq : Continuous q)
    (hd : ∀ x, HasDerivAt F (q x) x) {x Y ε b : ℝ} (hxY : x ≤ Y) (hε : 0 ≤ ε)
    (hFY : F Y ≤ 1)
    (hlocal : ∀ y ∈ Icc x Y,
      Real.exp (-ε) * gaussianPDFReal 0 1 y ≤ q y ∧ q y ≤ Real.exp ε * gaussianPDFReal 0 1 y)
    (hpY : saGaussianTail Y ≤ b) (hqY : 1 - F Y ≤ b) :
    Real.exp (-ε) * saGaussianTail x - b ≤ 1 - F x ∧
      1 - F x ≤ Real.exp ε * saGaussianTail x + b := by
  have hqI : (∫ y in x..Y, q y) = F Y - F x :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hd y) (hq.intervalIntegrable _ _)
  have hpI := saDensity_standardGaussian.tail_split x Y
  rw [sa_standardGaussian_law] at hpI
  have hlo : Real.exp (-ε) * (∫ y in x..Y, gaussianPDFReal 0 1 y) ≤ F Y - F x := by
    rw [← hqI, ← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_mono_on hxY
      (saDensity_standardGaussian.integrable.const_mul _).intervalIntegrable
      (hq.intervalIntegrable _ _) (fun y hy => (hlocal y hy).1)
  have hhi : F Y - F x ≤ Real.exp ε * ∫ y in x..Y, gaussianPDFReal 0 1 y := by
    rw [← hqI, ← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_mono_on hxY (hq.intervalIntegrable _ _)
      (saDensity_standardGaussian.integrable.const_mul _).intervalIntegrable
      (fun y hy => (hlocal y hy).2)
  have hp0 := (saGaussianTail_pos Y).le
  have hL : Real.exp (-ε) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hLp : Real.exp (-ε) * saGaussianTail Y ≤ b :=
    (mul_le_of_le_one_left hp0 hL).trans hpY
  have hUp : 0 ≤ Real.exp ε * saGaussianTail Y := mul_nonneg (Real.exp_nonneg _) hp0
  change saGaussianTail x = _ + saGaussianTail Y at hpI
  have heLo := congrArg (fun r => Real.exp (-ε) * r) hpI
  have heHi := congrArg (fun r => Real.exp ε * r) hpI
  constructor <;> nlinarith

theorem saQuantile_error_of_derivative {F q : ℝ → ℝ} (hF : SACDF F) (hq : Continuous q)
    (hd : ∀ x, HasDerivAt F (q x) x) {ε R Y z : ℝ}
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1 / 32) (hR : 0 ≤ R) (hY : R + 1 ≤ Y) (hz : |z| ≤ R)
    (hlocal : ∀ x, |x| ≤ Y →
      Real.exp (-ε) * gaussianPDFReal 0 1 x ≤ q x ∧ q x ≤ Real.exp ε * gaussianPDFReal 0 1 x)
    (hright : 1 - F Y ≤ ε * saGaussianTail R)
    (hleft : F (-Y) ≤ ε * saGaussianTail R)
    (hgauss : saGaussianTail Y ≤ ε * saGaussianTail R) :
    |saQuantile F (cdf (gaussianReal 0 1) z) - z| ≤ 32 * ε := by
  apply saQuantile_gaussian_error hF hε hε1 hz
  · intro x hx
    exact saTail_sandwich_of_deriv hq hd (by linarith [hx.2]) hε (hF.mem_Ioo Y).2.le
      (fun y hy => hlocal y (abs_le.mpr ⟨by linarith [hx.1, hy.1], hy.2⟩)) hgauss hright
  · intro x hx
    have hd' (y : ℝ) : HasDerivAt (fun y => 1 - F (-y)) (q (-y)) y := by
      have ht := ((hd (-y)).comp y (hasDerivAt_neg y)).const_sub 1
      convert! ht using 1
      simp only [mul_neg, mul_one, neg_neg]
    have hl : ∀ y ∈ Icc x Y, Real.exp (-ε) * gaussianPDFReal 0 1 y ≤ q (-y) ∧
        q (-y) ≤ Real.exp ε * gaussianPDFReal 0 1 y := by
      intro y hy
      have ha : |-y| ≤ Y := by rw [abs_neg]; exact abs_le.mpr ⟨by linarith [hx.1, hy.1], hy.2⟩
      have hh := hlocal (-y) ha
      have hg : gaussianPDFReal 0 1 (-y) = gaussianPDFReal 0 1 y := by
        simp only [gaussianPDFReal, sub_zero, neg_sq]
      rwa [hg] at hh
    have hfY : 1 - F (-Y) ≤ 1 := by have hh := (hF.mem_Ioo (-Y)).1; linarith
    have hb := saTail_sandwich_of_deriv (hq.comp continuous_neg) hd' (show x ≤ Y by linarith [hx.2])
      hε hfY hl hgauss (show 1 - (1 - F (-Y)) ≤ ε * saGaussianTail R by linarith)
    simpa only [sub_sub_cancel] using hb

/-- The affine form of the quantile lemma used at the root and at every split. -/
theorem saQuantile_error_of_affine_density {q : ℝ → ℝ} (hq : SADensity q)
    {c σ ε R Y z : ℝ} (hσ : 0 < σ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1 / 32)
    (hR : 0 ≤ R) (hY : R + 1 ≤ Y) (hz : |z| ≤ R)
    (hlocal : ∀ x, |x| ≤ Y →
      Real.exp (-ε) * gaussianPDFReal 0 1 x ≤ σ * q (c + σ * x) ∧
      σ * q (c + σ * x) ≤ Real.exp ε * gaussianPDFReal 0 1 x)
    (hright : 1 - cdf (hq.law : Measure ℝ) (c + σ * Y) ≤ ε * saGaussianTail R)
    (hleft : cdf (hq.law : Measure ℝ) (c - σ * Y) ≤ ε * saGaussianTail R)
    (hgauss : saGaussianTail Y ≤ ε * saGaussianTail R) :
    |saQuantile (cdf (hq.law : Measure ℝ)) (cdf (gaussianReal 0 1) z) - c - σ * z| ≤
      32 * σ * ε := by
  let F : ℝ → ℝ := fun x => cdf (hq.law : Measure ℝ) (c + σ * x)
  have hF : SACDF F := hq.regularCDF.affine c hσ
  have hd (x : ℝ) : HasDerivAt F (σ * q (c + σ * x)) x := by
    have ht := (hq.hasDerivAt_cdf (c + σ * x)).comp x
      (((hasDerivAt_id x).const_mul σ).const_add c)
    convert! ht using 1
    simp only [mul_one, mul_comm]
  have hq' : Continuous (fun x => σ * q (c + σ * x)) :=
    continuous_const.mul (hq.continuous.comp (continuous_const.add (continuous_const.mul continuous_id)))
  have hl : F (-Y) ≤ ε * saGaussianTail R := by simpa only [F, mul_neg, ← sub_eq_add_neg] using hleft
  have hb := saQuantile_error_of_derivative hF hq' hd hε hε1 hR hY hz hlocal hright hl hgauss
  have he := hq.regularCDF.quantile_affine c hσ
    ((saCDF_gaussianReal 0 (v := 1) one_ne_zero).mem_Ioo z)
  rw [← he]
  have ha : c + σ * saQuantile F (cdf (gaussianReal 0 1) z) - c - σ * z =
      σ * (saQuantile F (cdf (gaussianReal 0 1) z) - z) := by ring
  change |c + σ * saQuantile F (cdf (gaussianReal 0 1) z) - c - σ * z| ≤ _
  rw [ha, abs_mul, abs_of_pos hσ]
  nlinarith [mul_le_mul_of_nonneg_left hb hσ.le]

end

end PGM
