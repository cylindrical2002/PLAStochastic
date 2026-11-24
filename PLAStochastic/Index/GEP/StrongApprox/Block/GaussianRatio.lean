import PLAStochastic.Index.GEP.StrongApprox.Block.Envelope

/-! # WP5: local Gaussian ratios on a fixed square-root block window -/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory

theorem sa_log_ratio_sandwich {p g e : ℝ} (hp : 0 < p) (hg : 0 < g)
    (he : |Real.log (p / g)| ≤ e) : Real.exp (-e) * g ≤ p ∧ p ≤ Real.exp e * g := by
  have hr : 0 < p / g := div_pos hp hg
  have hb := abs_le.mp he
  have hlo := Real.exp_le_exp.mpr hb.1
  have hhi := Real.exp_le_exp.mpr hb.2
  rw [Real.exp_log hr] at hlo hhi
  exact ⟨(le_div_iff₀ hg).mp hlo, (div_le_iff₀ hg).mp hhi⟩

theorem sa_gaussianPDFReal_scale {σ : ℝ} (hσ : 0 < σ) (x : ℝ) :
    σ * gaussianPDFReal 0 (Real.toNNReal (σ ^ 2)) (σ * x) = gaussianPDFReal 0 1 x := by
  simp only [gaussianPDFReal, Real.coe_toNNReal _ (sq_nonneg σ), sub_zero,
    NNReal.coe_one, mul_one]
  rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hσ.le, mul_inv_rev]
  have he : -(σ * x) ^ 2 / (2 * σ ^ 2) = -x ^ 2 / 2 := by field_simp
  rw [he]
  field_simp

/-- The local conditional ratio has a polynomial error in a square-root block
window; all constants precede the law and no probability hypothesis is hidden. -/
theorem exists_uniform_saSplitDensity_block_ratio
    (vlo vhi κ₃ B θ D c : ℝ) (hvlo : 0 < vlo) (hvhi : 0 < vhi)
    (hB : 0 < B) (hθ : 0 < θ) (hD : 0 < D) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧
      ∀ ν : ProbabilityMeasure ℝ, UnivClass vlo vhi κ₃ B θ ν → SmoothPart D c ν →
      ∀ s : ℝ, 0 < s → s ≤ 1 → ∀ l : ℕ, 2 ≤ l →
      1 / s ≤ (l : ℝ) ^ 8 → 2 * C ≤ Real.sqrt l →
      ∀ A Y : ℝ, 0 ≤ A → 0 ≤ Y → A + Y ≤ saMeanRadius vlo B θ * Real.sqrt l →
      ∀ u : ℝ, |u| * Real.sqrt l ≤ A → ∀ z : ℝ, |z| ≤ Y →
        |Real.log (saSplitDensity (saCenteredSumDensity ν s l) (2 * l * u)
            ((l : ℝ) * u + Real.sqrt l * z) /
          gaussianPDFReal 0 (Real.toNNReal ((l : ℝ) * (lawVar ν + s ^ 2) / 2)) (Real.sqrt l * z))| ≤
          (6 * C + saLogVarianceConstant vlo B θ / 2 * (3 * A + 2 * Y) +
            saRateThird vlo B θ * (A * Y ^ 2 + Y ^ 3 / 3)) / Real.sqrt l := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_saConditionalDensity_gaussian_ratio
    vlo vhi κ₃ B θ D c hvlo hvhi hB hθ hD hc
  refine ⟨C, hC, ?_⟩
  intro ν hν hsm s hs hs1 l hl hscale hlarge A Y hA hY hwindow u hu z hz
  have hl0 : 0 < l := by omega
  have hlr : 0 < (l : ℝ) := by exact_mod_cast hl0
  have hr : 0 < Real.sqrt (l : ℝ) := Real.sqrt_pos.mpr hlr
  have hL := (saLogVarianceConstant_pos (B := B) hvlo hθ).le
  have hT := (saRateThird_pos (B := B) hvlo hθ).le
  have hu' : |u| ≤ A / Real.sqrt l := (le_div_iff₀ hr).mpr hu
  have ht : |z / Real.sqrt l| ≤ Y / Real.sqrt l := by
    rw [abs_div, abs_of_pos hr]
    exact div_le_div_of_nonneg_right hz hr.le
  have hut : |u| + |z / Real.sqrt l| ≤ saMeanRadius vlo B θ := by
    have hs' : |u| + |z / Real.sqrt l| ≤ (A + Y) / Real.sqrt l := by
      rw [add_div]
      exact add_le_add hu' ht
    exact hs'.trans ((div_le_iff₀ hr).mpr hwindow)
  have he := hb ν hν hsm s hs hs1 l hl hscale hlarge u (z / Real.sqrt l) hut
  rw [← saSplitDensity_centeredSum ν hs hl0, mul_add, sa_block_scale_mul hl0] at he
  apply he.trans
  have hlin : saLogVarianceConstant vlo B θ / 2 * (3 * |u| + 2 * |z / Real.sqrt l|) ≤
      saLogVarianceConstant vlo B θ / 2 * (3 * (A / Real.sqrt l) + 2 * (Y / Real.sqrt l)) := by
    gcongr
  have hpol : (l : ℝ) * saRateThird vlo B θ *
      (|u| * (z / Real.sqrt l) ^ 2 + |z / Real.sqrt l| ^ 3 / 3) ≤
      (l : ℝ) * saRateThird vlo B θ *
      ((A / Real.sqrt l) * (Y / Real.sqrt l) ^ 2 + (Y / Real.sqrt l) ^ 3 / 3) := by
    rw [← sq_abs (z / Real.sqrt l)]
    gcongr
  apply (add_le_add (add_le_add le_rfl hlin) hpol).trans_eq
  have hsq : (l : ℝ) = Real.sqrt (l : ℝ) ^ 2 := (Real.sq_sqrt hlr.le).symm
  calc
    _ = 6 * C / Real.sqrt l + saLogVarianceConstant vlo B θ / 2 *
        (3 * (A / Real.sqrt l) + 2 * (Y / Real.sqrt l)) +
        (Real.sqrt (l : ℝ) ^ 2) * saRateThird vlo B θ *
        ((A / Real.sqrt l) * (Y / Real.sqrt l) ^ 2 + (Y / Real.sqrt l) ^ 3 / 3) := by rw [← hsq]
    _ = _ := by field_simp

/-- Root-sum version of the polynomial window error. -/
theorem exists_uniform_saCenteredSumDensity_block_ratio
    (vlo vhi κ₃ B θ D c : ℝ) (hvlo : 0 < vlo) (hvhi : 0 < vhi)
    (hB : 0 < B) (hθ : 0 < θ) (hD : 0 < D) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧
      ∀ ν : ProbabilityMeasure ℝ, UnivClass vlo vhi κ₃ B θ ν → SmoothPart D c ν →
      ∀ s : ℝ, 0 < s → s ≤ 1 → ∀ l : ℕ, 2 ≤ l →
      1 / s ≤ (l : ℝ) ^ 8 → 2 * C ≤ Real.sqrt l →
      ∀ Y : ℝ, 0 ≤ Y → Y ≤ saMeanRadius vlo B θ * Real.sqrt l →
      ∀ z : ℝ, |z| ≤ Y →
        |Real.log (saCenteredSumDensity ν s l (Real.sqrt l * z) /
          gaussianPDFReal 0 (Real.toNNReal ((l : ℝ) * (lawVar ν + s ^ 2))) (Real.sqrt l * z))| ≤
          (2 * C + saLogVarianceConstant vlo B θ / 2 * Y +
            saRateThird vlo B θ * Y ^ 3 / 6) / Real.sqrt l := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_saCenteredSumDensity_gaussian_ratio
    vlo vhi κ₃ B θ D c hvlo hvhi hB hθ hD hc
  refine ⟨C, hC, ?_⟩
  intro ν hν hsm s hs hs1 l hl hscale hlarge Y hY hwindow z hz
  have hl0 : 0 < l := by omega
  have hlr : 0 < (l : ℝ) := by exact_mod_cast hl0
  have hr : 0 < Real.sqrt (l : ℝ) := Real.sqrt_pos.mpr hlr
  have hL := (saLogVarianceConstant_pos (B := B) hvlo hθ).le
  have hT := (saRateThird_pos (B := B) hvlo hθ).le
  have ht : |z / Real.sqrt l| ≤ Y / Real.sqrt l := by
    rw [abs_div, abs_of_pos hr]
    exact div_le_div_of_nonneg_right hz hr.le
  have hw : |z / Real.sqrt l| ≤ saMeanRadius vlo B θ :=
    ht.trans ((div_le_iff₀ hr).mpr hwindow)
  have he := hb ν hν hsm s hs hs1 l hl hscale hlarge (z / Real.sqrt l) hw
  rw [sa_block_scale_mul hl0] at he
  apply he.trans
  have hlin : saLogVarianceConstant vlo B θ / 2 * |z / Real.sqrt l| ≤
      saLogVarianceConstant vlo B θ / 2 * (Y / Real.sqrt l) := by gcongr
  have hpol : (l : ℝ) * saRateThird vlo B θ * |z / Real.sqrt l| ^ 3 / 6 ≤
      (l : ℝ) * saRateThird vlo B θ * (Y / Real.sqrt l) ^ 3 / 6 := by gcongr
  apply (add_le_add (add_le_add le_rfl hlin) hpol).trans_eq
  have hsq : (l : ℝ) = Real.sqrt (l : ℝ) ^ 2 := (Real.sq_sqrt hlr.le).symm
  calc
    _ = 2 * C / Real.sqrt l + saLogVarianceConstant vlo B θ / 2 * (Y / Real.sqrt l) +
        Real.sqrt (l : ℝ) ^ 2 * saRateThird vlo B θ * (Y / Real.sqrt l) ^ 3 / 6 := by rw [← hsq]
    _ = _ := by field_simp

end

end PGM
