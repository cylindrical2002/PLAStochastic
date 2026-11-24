import PLAStochastic.Index.CEPS.BrownianCoeff.Root

/-!
# Sector and combined-exponent bounds for the normalized Brownian root

The stronger bound pays for products containing an entrance squared and a bridge.
It also places the normalized root in the fixed sector `‖s‖ ≤ 3 re s`.
-/

noncomputable section

open Complex

namespace PGM

theorem cepsBrownian_variance_tight {v₀ : ℝ} {v : ℂ} (hv₀ : 0 < v₀)
    (hv : ‖v - (v₀ : ℂ)‖ ≤ cepsBrownianRadius v₀) : 15 * v₀ / 16 ≤ ‖v‖ := by
  have ht := norm_add_le ((v₀ : ℂ) - v) v
  rw [sub_add_cancel, norm_sub_rev, norm_real, Real.norm_eq_abs, abs_of_pos hv₀] at ht
  have hdist : ‖v - (v₀ : ℂ)‖ ≤ v₀ / 16 := hv
  linarith

private theorem real_root_re_strong {v₀ lam : ℝ} {z : ℂ} (hz : z.re = 0) :
    2 * ‖cepsBrownianR (v₀ : ℂ) lam z‖ / 3 ≤ (cepsBrownianR (v₀ : ℂ) lam z).re := by
  set R := cepsBrownianR (v₀ : ℂ) lam z
  have hs : R.re ^ 2 - R.im ^ 2 = lam ^ 2 := by
    simpa [pow_two, add_re, mul_re, hz] using
      congrArg Complex.re (cepsBrownianR_sq (v₀ : ℂ) lam z)
  have hn : ‖R‖ ^ 2 = R.re ^ 2 + R.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  have hp := cepsBrownianR_re_nonneg (v₀ : ℂ) lam z
  change 0 ≤ R.re at hp
  nlinarith [sq_nonneg lam, sq_nonneg (2 * ‖R‖ - 3 * R.re), norm_nonneg R]

theorem cepsBrownian_quotient_re_strong {v₀ : ℝ} {v : ℂ} {lam : ℝ} {z : ℂ}
    (hv₀ : 0 < v₀) (hv : ‖v - (v₀ : ℂ)‖ ≤ cepsBrownianRadius v₀) (hz : z.re = 0) :
    7 * ‖cepsBrownianR (v₀ : ℂ) lam z‖ / (15 * v₀) ≤ (cepsBrownianR v lam z / v).re := by
  set R := cepsBrownianR v lam z
  set S := cepsBrownianR (v₀ : ℂ) lam z
  have hvnorm := cepsBrownian_variance_tight hv₀ hv
  have hvne := (cepsBrownian_variance_bounds hv₀ hv).2.2.2
  have hv₀ne : (v₀ : ℂ) ≠ 0 := by exact_mod_cast hv₀.ne'
  have heq : R / v - S / (v₀ : ℂ) = (R - S) / v +
      S * ((v₀ : ℂ) - v) / (v * (v₀ : ℂ)) := by field_simp; ring
  have hd := cepsBrownianR_perturbation (lam := lam) hv₀ hv hz
  have hdist : ‖(v₀ : ℂ) - v‖ ≤ v₀ / 16 := by rw [norm_sub_rev]; exact hv
  have hnorm : ‖R / v - S / (v₀ : ℂ)‖ ≤ ‖S‖ / (5 * v₀) := by
    rw [heq]
    calc
      ‖(R - S) / v + S * ((v₀ : ℂ) - v) / (v * (v₀ : ℂ))‖ ≤
          ‖R - S‖ / ‖v‖ + ‖S‖ * ‖(v₀ : ℂ) - v‖ / (‖v‖ * v₀) := by
        simpa [norm_div, norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos hv₀] using
          norm_add_le ((R - S) / v) (S * ((v₀ : ℂ) - v) / (v * (v₀ : ℂ)))
      _ ≤ (‖S‖ / 8) / (15 * v₀ / 16) + (‖S‖ * (v₀ / 16)) / ((15 * v₀ / 16) * v₀) := by
        gcongr
      _ = ‖S‖ / (5 * v₀) := by field_simp; ring
  have hre := (abs_le.mp ((Complex.abs_re_le_norm (R / v - S / (v₀ : ℂ))).trans hnorm)).1
  have hs := real_root_re_strong (v₀ := v₀) (lam := lam) hz
  have hSre : (S / (v₀ : ℂ)).re = S.re / v₀ := by simp [Complex.div_re]; field_simp
  rw [sub_re, hSre] at hre
  have hsdiv : 2 * ‖S‖ / (3 * v₀) ≤ S.re / v₀ := by
    simpa [div_div] using div_le_div_of_nonneg_right hs hv₀.le
  have hrat : 2 * ‖S‖ / (3 * v₀) - ‖S‖ / (5 * v₀) = 7 * ‖S‖ / (15 * v₀) := by
    field_simp
    ring
  change 7 * ‖S‖ / (15 * v₀) ≤ (R / v).re
  linarith

theorem cepsBrownian_quotient_sector {v₀ : ℝ} {v : ℂ} {lam : ℝ} {z : ℂ}
    (hv₀ : 0 < v₀) (hv : ‖v - (v₀ : ℂ)‖ ≤ cepsBrownianRadius v₀) (hz : z.re = 0) :
    ‖cepsBrownianR v lam z / v‖ ≤ 3 * (cepsBrownianR v lam z / v).re := by
  set S := ‖cepsBrownianR (v₀ : ℂ) lam z‖
  have ht := norm_add_le (cepsBrownianR v lam z - cepsBrownianR (v₀ : ℂ) lam z)
    (cepsBrownianR (v₀ : ℂ) lam z)
  rw [sub_add_cancel] at ht
  have hd := cepsBrownianR_perturbation (lam := lam) hv₀ hv hz
  have hroot : ‖cepsBrownianR v lam z‖ ≤ 9 * S / 8 := by linarith
  have hvnorm := cepsBrownian_variance_tight hv₀ hv
  have hn : ‖cepsBrownianR v lam z / v‖ ≤ 6 * S / (5 * v₀) := by
    rw [norm_div]
    calc
      ‖cepsBrownianR v lam z‖ / ‖v‖ ≤ (9 * S / 8) / (15 * v₀ / 16) := by gcongr
      _ = 6 * S / (5 * v₀) := by field_simp; ring
  have hr := cepsBrownian_quotient_re_strong (lam := lam) hv₀ hv hz
  have hrat : 6 * S / (5 * v₀) ≤ 3 * (7 * S / (15 * v₀)) := by
    have hS : 0 ≤ S := norm_nonneg _
    field_simp
    nlinarith
  exact hn.trans (hrat.trans (mul_le_mul_of_nonneg_left hr (by norm_num)))

theorem cepsBrownian_real_norm_abs {v₀ lam : ℝ} {z : ℂ} (hz : z.re = 0) :
    |lam| ≤ ‖cepsBrownianR (v₀ : ℂ) lam z‖ := by
  set R := cepsBrownianR (v₀ : ℂ) lam z
  have hs : R.re ^ 2 - R.im ^ 2 = lam ^ 2 := by
    simpa [pow_two, add_re, mul_re, hz] using
      congrArg Complex.re (cepsBrownianR_sq (v₀ : ℂ) lam z)
  have hn : ‖R‖ ^ 2 = R.re ^ 2 + R.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  nlinarith [sq_abs lam, abs_nonneg lam, norm_nonneg R, sq_nonneg R.im]

/-- The exponent left after multiplying an entrance squared by a bridge still decays. -/
theorem cepsBrownian_combined_exponent {v₀ : ℝ} {v : ℂ} {lam : ℝ} {z : ℂ}
    (hv₀ : 0 < v₀) (hv : ‖v - (v₀ : ℂ)‖ ≤ cepsBrownianRadius v₀) (hz : z.re = 0) :
    cepsBrownianDecay v₀ / 3 * (|lam| + Real.sqrt ‖z‖) ≤
      3 * (cepsBrownianR v lam z / v).re - |((lam : ℂ) / v).re| := by
  set S := ‖cepsBrownianR (v₀ : ℂ) lam z‖
  have hvnorm := cepsBrownian_variance_tight hv₀ hv
  have hlam := cepsBrownian_real_norm_abs (v₀ := v₀) (lam := lam) hz
  have ha : |((lam : ℂ) / v).re| ≤ 16 * S / (15 * v₀) := by
    calc
      |((lam : ℂ) / v).re| ≤ ‖(lam : ℂ) / v‖ := Complex.abs_re_le_norm _
      _ = |lam| / ‖v‖ := by rw [norm_div, norm_real, Real.norm_eq_abs]
      _ ≤ S / (15 * v₀ / 16) := by gcongr
      _ = 16 * S / (15 * v₀) := by field_simp
  have hr := cepsBrownian_quotient_re_strong (lam := lam) hv₀ hv hz
  have hrat : 3 * (7 * S / (15 * v₀)) - 16 * S / (15 * v₀) = S / (3 * v₀) := by
    field_simp
    ring
  have hmain : S / (3 * v₀) ≤ 3 * (cepsBrownianR v lam z / v).re - |((lam : ℂ) / v).re| := by
    linarith
  have hcentre : ‖(v₀ : ℂ) - (v₀ : ℂ)‖ ≤ cepsBrownianRadius v₀ := by
    simp only [sub_self, norm_zero, cepsBrownianRadius]
    positivity
  have hb := cepsBrownian_quotient_re (lam := lam) hv₀ hcentre hz
  have hnorm : (cepsBrownianR (v₀ : ℂ) lam z / (v₀ : ℂ)).re ≤ S / v₀ := by
    calc
      (cepsBrownianR (v₀ : ℂ) lam z / (v₀ : ℂ)).re ≤
          ‖cepsBrownianR (v₀ : ℂ) lam z / (v₀ : ℂ)‖ := Complex.re_le_norm _
      _ = S / v₀ := by simp [S, norm_real, Real.norm_eq_abs, abs_of_pos hv₀]
  have hdiv := div_le_div_of_nonneg_right (hb.trans hnorm) (by norm_num : (0 : ℝ) ≤ 3)
  have hbound : cepsBrownianDecay v₀ / 3 * (|lam| + Real.sqrt ‖z‖) ≤ S / (3 * v₀) := by
    simpa [div_div, div_mul_eq_mul_div, mul_comm] using hdiv
  exact hbound.trans hmain

end PGM
