import PLAStochastic.Index.CEPS.Normal.MergedNonzero

/-! # Bridge bounds that retain the root-merging cancellation

The off-diagonal estimate uses the Delta lower bound. At a merged root
the genuine derivative denominator gives the same inverse-width gain.
-/

noncomputable section
open Complex
namespace PGM

theorem cepsNormal_rootGain_le {r l : ℝ} (hr : 0 ≤ r) (hl : 0 < l) :
    r ≤ min 1 (r * l) * (r + 1 / l) := by
  by_cases h : r * l ≤ 1
  · rw [min_eq_right h]
    have he : r * l * (r + 1 / l) = r * l * r + r := by
      field_simp
    rw [he]
    exact le_add_of_nonneg_left (by positivity)
  · rw [min_eq_left (le_of_not_ge h), one_mul]
    exact le_add_of_nonneg_right (by positivity)

namespace CepsNormalData

variable (a : CepsNormalData) (L : ℂ → ℂ → ℂ → ℂ) (μ q l : ℂ)

theorem regularBridge_mul_delta (hQm : a.Q a.βm ≠ 0)
    (hS : dslope (a.normalG L μ q l) a.βm a.βp ≠ 0) :
    a.regularBridge L μ q l * a.delta L μ q l =
      a.eta * a.normalG L μ q l a.βp := by
  have hD := a.delta_mul_normalG L μ q l hQm
  have hgm := a.normalG_ne L μ q l hQm
  unfold regularBridge
  field_simp
  linear_combination -a.normalG L μ q l a.βp * hD

omit l in
theorem norm_regularBridge_le_of_delta {l r c K G : ℝ}
    (hl : 0 < l) (hr : 0 < r) (hc : 0 < c) (hK : 0 ≤ K) (hG : 0 ≤ G)
    (hQm : a.Q a.βm ≠ 0)
    (hS : dslope (a.normalG L μ q l) a.βm a.βp ≠ 0)
    (hdelta : c * min 1 (r * l) ≤ ‖a.delta L μ q l‖)
    (heta : ‖a.eta‖ ≤ K * r)
    (hweight : ‖a.normalG L μ q l a.βp‖ ≤ G) :
    ‖a.regularBridge L μ q l‖ ≤ K * G / c * (r + 1 / l) := by
  have hm : 0 < min 1 (r * l) := lt_min (by norm_num) (mul_pos hr hl)
  have he := congrArg norm (a.regularBridge_mul_delta L μ q l hQm hS)
  simp only [norm_mul] at he
  have hgain := cepsNormal_rootGain_le hr.le hl
  have hmul : ‖a.regularBridge L μ q l‖ * (c * min 1 (r * l)) ≤
      (K * G * (r + 1 / l)) * min 1 (r * l) := by
    calc
      _ ≤ ‖a.regularBridge L μ q l‖ * ‖a.delta L μ q l‖ :=
        mul_le_mul_of_nonneg_left hdelta (norm_nonneg _)
      _ = ‖a.eta‖ * ‖a.normalG L μ q l a.βp‖ := he
      _ ≤ (K * r) * G := mul_le_mul heta hweight (norm_nonneg _) (mul_nonneg hK hr.le)
      _ = K * G * r := by ring
      _ ≤ K * G * (min 1 (r * l) * (r + 1 / l)) :=
        mul_le_mul_of_nonneg_left hgain (mul_nonneg hK hG)
      _ = _ := by ring
  rw [← mul_assoc] at hmul
  have hcancel := le_of_mul_le_mul_right hmul hm
  calc
    _ ≤ (K * G * (r + 1 / l)) / c := (le_div_iff₀ hc).mpr hcancel
    _ = _ := by ring

omit l in
theorem norm_regularBridge_merged_le {l M G : ℝ} {Q' L' : ℂ}
    (hl : 0 < l) (hwidth : 2 * M ≤ l)
    (hroots : a.βp = a.βm)
    (hQ : HasDerivAt a.Q Q' a.βm) (hL : HasDerivAt (L μ q) L' a.βm)
    (hQm : a.Q a.βm ≠ 0) (hbudget : ‖Q' / a.Q a.βm - 2 * L'‖ ≤ M)
    (hweight : ‖a.normalG L μ q l a.βm‖ ≤ G) :
    ‖a.regularBridge L μ q l‖ ≤ 2 * G / l := by
  have hMl : M < l := by linarith
  have hd := a.normalG_deriv_lower L μ q hQ hL hQm hbudget hMl
  have hd0 := a.normalG_deriv_ne L μ q hQ hL hQm hbudget hMl
  have hg0 : 0 < ‖a.normalG L μ q l a.βm‖ :=
    norm_pos_iff.mpr (a.normalG_ne L μ q l hQm)
  have he : ‖a.regularBridge L μ q l‖ * ‖deriv (a.normalG L μ q l) a.βm‖ =
      ‖a.normalG L μ q l a.βm‖ ^ 2 := by
    rw [a.regularBridge_merged L μ q l hroots, norm_div, norm_neg, norm_pow,
      div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hd0)]
  have hmul : (‖a.regularBridge L μ q l‖ * (l / 2)) *
      ‖a.normalG L μ q l a.βm‖ ≤ G * ‖a.normalG L μ q l a.βm‖ := by
    calc
      _ = ‖a.regularBridge L μ q l‖ * (l / 2 * ‖a.normalG L μ q l a.βm‖) := by ring
      _ ≤ ‖a.regularBridge L μ q l‖ * ((l - M) * ‖a.normalG L μ q l a.βm‖) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (by linarith) hg0.le) (norm_nonneg _)
      _ ≤ ‖a.regularBridge L μ q l‖ * ‖deriv (a.normalG L μ q l) a.βm‖ :=
        mul_le_mul_of_nonneg_left hd (norm_nonneg _)
      _ = _ := he
      _ ≤ _ := by simpa only [pow_two] using mul_le_mul_of_nonneg_right hweight hg0.le
  have hc := le_of_mul_le_mul_right hmul hg0
  exact (le_div_iff₀ hl).mpr (by linarith)

end CepsNormalData
end PGM
