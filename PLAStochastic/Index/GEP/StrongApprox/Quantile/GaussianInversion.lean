import PLAStochastic.Index.GEP.StrongApprox.Quantile.GaussianTail

/-! # WP5: quantitative inversion of relative Gaussian tail bounds -/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set

theorem sa_exp_neg_three_add_le_one {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1 / 32) :
    Real.exp (-(3 * ε)) + ε ≤ 1 := by
  have hd : 0 < 1 + 3 * ε := by positivity
  have he : 1 + 3 * ε ≤ Real.exp (3 * ε) := by simpa [add_comm] using Real.add_one_le_exp (3 * ε)
  have hi := one_div_le_one_div_of_le hd he
  rw [one_div, ← Real.exp_neg] at hi
  have hq : 1 / (1 + 3 * ε) ≤ 1 - ε := by
    apply (div_le_iff₀ hd).2
    nlinarith [mul_nonneg hε (show 0 ≤ 2 - 3 * ε by linarith)]
  linarith

/-- Right-tail comparison gives a CDF sandwich at every nonnegative Gaussian argument. -/
theorem saGaussianCDF_sandwich {F : ℝ → ℝ} {ε R z : ℝ}
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1 / 32) (hz : 0 ≤ z) (hzR : z ≤ R)
    (htail : ∀ x ∈ Icc (-1) (R + 1),
      Real.exp (-ε) * saGaussianTail x - ε * saGaussianTail R ≤ 1 - F x ∧
      1 - F x ≤ Real.exp ε * saGaussianTail x + ε * saGaussianTail R) :
    F (z - 32 * ε) ≤ cdf (gaussianReal 0 1) z ∧
      cdf (gaussianReal 0 1) z ≤ F (z + 32 * ε) := by
  have hδ : 0 ≤ 32 * ε := by positivity
  have hδ1 : 32 * ε ≤ 1 := by linarith
  have hm := htail (z - 32 * ε) ⟨by linarith, by linarith⟩
  have hp := htail (z + 32 * ε) ⟨by linarith, by linarith⟩
  have hT : 0 ≤ saGaussianTail z := (saGaussianTail_pos z).le
  have hR : saGaussianTail R ≤ saGaussianTail z := by
    have hc := monotone_cdf (gaussianReal 0 1) hzR
    dsimp [saGaussianTail]
    linarith
  have hscale : 32 * ε / 8 = 4 * ε := by ring
  have hup := saGaussianTail_shift_le (x := z) (by linarith) hδ
  rw [hscale] at hup
  have hdown := saGaussianTail_shift_le (x := z - 32 * ε) (by linarith) hδ
  rw [sub_add_cancel, hscale] at hdown
  have hmul : Real.exp (4 * ε) * Real.exp (-(4 * ε)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hlo : Real.exp (4 * ε) * saGaussianTail z ≤ saGaussianTail (z - 32 * ε) := by
    have hh := mul_le_mul_of_nonneg_left hdown (Real.exp_nonneg (4 * ε))
    simpa only [← mul_assoc, hmul, one_mul] using hh
  have heUp : Real.exp ε * Real.exp (-(4 * ε)) = Real.exp (-(3 * ε)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have heLo : Real.exp (-ε) * Real.exp (4 * ε) = Real.exp (3 * ε) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hupper : 1 - F (z + 32 * ε) ≤ saGaussianTail z := by
    calc
      _ ≤ Real.exp ε * saGaussianTail (z + 32 * ε) + ε * saGaussianTail R := hp.2
      _ ≤ Real.exp ε * (Real.exp (-(4 * ε)) * saGaussianTail z) + ε * saGaussianTail z :=
        add_le_add (mul_le_mul_of_nonneg_left hup (Real.exp_nonneg _))
          (mul_le_mul_of_nonneg_left hR hε)
      _ = (Real.exp (-(3 * ε)) + ε) * saGaussianTail z := by rw [← mul_assoc, heUp]; ring
      _ ≤ 1 * saGaussianTail z := mul_le_mul_of_nonneg_right (sa_exp_neg_three_add_le_one hε hε1) hT
      _ = _ := one_mul _
  have hlower : saGaussianTail z ≤ 1 - F (z - 32 * ε) := by
    have he : 1 ≤ Real.exp (3 * ε) - ε := by
      have hh := Real.add_one_le_exp (3 * ε)
      linarith
    calc
      _ = 1 * saGaussianTail z := (one_mul _).symm
      _ ≤ (Real.exp (3 * ε) - ε) * saGaussianTail z := mul_le_mul_of_nonneg_right he hT
      _ = Real.exp (-ε) * (Real.exp (4 * ε) * saGaussianTail z) - ε * saGaussianTail z := by
        rw [← mul_assoc, heLo]
        ring
      _ ≤ Real.exp (-ε) * saGaussianTail (z - 32 * ε) - ε * saGaussianTail R :=
        sub_le_sub (mul_le_mul_of_nonneg_left hlo (Real.exp_nonneg _))
          (mul_le_mul_of_nonneg_left hR hε)
      _ ≤ _ := hm.1
  dsimp [saGaussianTail] at hlower hupper
  constructor <;> linarith

theorem saQuantile_gaussian_error_nonneg {F : ℝ → ℝ} (hF : SACDF F) {ε R z : ℝ}
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1 / 32) (hz : 0 ≤ z) (hzR : z ≤ R)
    (htail : ∀ x ∈ Icc (-1) (R + 1),
      Real.exp (-ε) * saGaussianTail x - ε * saGaussianTail R ≤ 1 - F x ∧
      1 - F x ≤ Real.exp ε * saGaussianTail x + ε * saGaussianTail R) :
    |saQuantile F (cdf (gaussianReal 0 1) z) - z| ≤ 32 * ε := by
  have hb := saGaussianCDF_sandwich hε hε1 hz hzR htail
  exact hF.quantile_error_le ((saCDF_gaussianReal 0 (v := 1) one_ne_zero).mem_Ioo z) hb.1 hb.2

/-- Two relative tail comparisons give a uniform central quantile error. -/
theorem saQuantile_gaussian_error {F : ℝ → ℝ} (hF : SACDF F) {ε R z : ℝ}
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1 / 32) (hz : |z| ≤ R)
    (hright : ∀ x ∈ Icc (-1) (R + 1),
      Real.exp (-ε) * saGaussianTail x - ε * saGaussianTail R ≤ 1 - F x ∧
      1 - F x ≤ Real.exp ε * saGaussianTail x + ε * saGaussianTail R)
    (hleft : ∀ x ∈ Icc (-1) (R + 1),
      Real.exp (-ε) * saGaussianTail x - ε * saGaussianTail R ≤ F (-x) ∧
      F (-x) ≤ Real.exp ε * saGaussianTail x + ε * saGaussianTail R) :
    |saQuantile F (cdf (gaussianReal 0 1) z) - z| ≤ 32 * ε := by
  by_cases hz0 : 0 ≤ z
  · exact saQuantile_gaussian_error_nonneg hF hε hε1 hz0 ((le_abs_self z).trans hz) hright
  · have ht : ∀ x ∈ Icc (-1) (R + 1),
        Real.exp (-ε) * saGaussianTail x - ε * saGaussianTail R ≤
          1 - (1 - F (-x)) ∧
        1 - (1 - F (-x)) ≤ Real.exp ε * saGaussianTail x + ε * saGaussianTail R := by
      intro x hx
      simpa only [sub_sub_cancel] using hleft x hx
    have hb := saGaussianCDF_sandwich (F := fun x => 1 - F (-x)) hε hε1
      (show 0 ≤ -z by linarith) ((neg_le_abs z).trans hz) ht
    have hm : -(-z - 32 * ε) = z + 32 * ε := by ring
    have hp : -(-z + 32 * ε) = z - 32 * ε := by ring
    rw [hm, hp, saGaussianCDF_neg] at hb
    dsimp [saGaussianTail] at hb
    apply hF.quantile_error_le ((saCDF_gaussianReal 0 (v := 1) one_ne_zero).mem_Ioo z)
    · linarith [hb.2]
    · linarith [hb.1]

end

end PGM
