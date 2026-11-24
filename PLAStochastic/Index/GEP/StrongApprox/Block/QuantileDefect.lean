import PLAStochastic.Index.GEP.StrongApprox.Block.GaussianRatio

/-! # WP5: actual block quantile defects from the proved density estimates -/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory

/-- Convert a log-ratio window on a block scale to the standard Gaussian scale
used by the quantitative inverse-CDF theorem. -/
theorem saQuantile_error_of_block_density {q : ℝ → ℝ} (hq : SADensity q)
    {m d σ ε R Y z : ℝ} (hd : 0 < d) (hσ : 0 < σ)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1 / 32) (hR : 0 ≤ R) (_hY : 0 ≤ Y)
    (hwindow : σ * (R + 1) ≤ d * Y) (hz : |z| ≤ R)
    (hlocal : ∀ x, |x| ≤ Y →
      |Real.log (q (m + d * x) / gaussianPDFReal 0 (Real.toNNReal (σ ^ 2)) (d * x))| ≤ ε)
    (hright : 1 - cdf (hq.law : Measure ℝ) (m + d * Y) ≤ ε * saGaussianTail R)
    (hleft : cdf (hq.law : Measure ℝ) (m - d * Y) ≤ ε * saGaussianTail R)
    (hgauss : saGaussianTail (d * Y / σ) ≤ ε * saGaussianTail R) :
    |saQuantile (cdf (hq.law : Measure ℝ)) (cdf (gaussianReal 0 1) z) - m - σ * z| ≤
      32 * σ * ε := by
  apply saQuantile_error_of_affine_density hq hσ hε hε1 hR
    ((le_div_iff₀ hσ).mpr (by nlinarith)) hz (Y := d * Y / σ)
  · intro x hx
    have ht : |σ / d * x| ≤ Y := by
      rw [abs_mul, abs_of_pos (div_pos hσ hd)]
      calc
        _ ≤ (σ / d) * (d * Y / σ) := mul_le_mul_of_nonneg_left hx (by positivity)
        _ = Y := by field_simp
    have he := hlocal (σ / d * x) ht
    have hid : d * (σ / d * x) = σ * x := by field_simp
    rw [hid] at he
    have hg : 0 < gaussianPDFReal 0 (Real.toNNReal (σ ^ 2)) (σ * x) := by
      apply gaussianPDFReal_pos
      simp [Real.toNNReal_eq_zero, (sq_pos_of_pos hσ).not_ge]
    have hs := sa_log_ratio_sandwich (hq.pos _) hg he
    have hnorm := sa_gaussianPDFReal_scale hσ x
    constructor
    · have hb := mul_le_mul_of_nonneg_left hs.1 hσ.le
      calc
        _ = σ * (Real.exp (-ε) * gaussianPDFReal 0 (Real.toNNReal (σ ^ 2)) (σ * x)) := by
          rw [← hnorm]
          ring
        _ ≤ _ := hb
    · have hb := mul_le_mul_of_nonneg_left hs.2 hσ.le
      calc
        _ ≤ σ * (Real.exp ε * gaussianPDFReal 0 (Real.toNNReal (σ ^ 2)) (σ * x)) := hb
        _ = _ := by rw [← hnorm]; ring
  · convert hright using 2
    congr 1
    field_simp
  · convert hleft using 2
    congr 1
    field_simp
  · exact hgauss

/-- Conditional quantile defect for the actual dyadic split. The remaining
conditions are explicit scalar window and tail inequalities, suitable for one
class-uniform eventual choice of the horizon threshold. -/
theorem exists_uniform_saSplitQuantile_block_error
    (vlo vhi κ₃ B θ D c : ℝ) (hvlo : 0 < vlo) (hvhi : 0 < vhi)
    (hB : 0 < B) (hθ : 0 < θ) (hD : 0 < D) (hc : 0 < c) :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
      ∀ ν : ProbabilityMeasure ℝ, UnivClass vlo vhi κ₃ B θ ν → SmoothPart D c ν →
      ∀ s : ℝ, ∀ hs : 0 < s, s ≤ 1 → ∀ l : ℕ, ∀ hl : 2 ≤ l,
      1 / s ≤ (l : ℝ) ^ 8 → 2 * C ≤ Real.sqrt l →
      ∀ A Y : ℝ, 0 ≤ A → 0 < Y → A + Y ≤ saMeanRadius vlo B θ * Real.sqrt l →
      Y ≤ saMeanRadius vlo B θ / 2 * Real.sqrt l →
      ∀ u : ℝ, |u| * Real.sqrt l ≤ A → |u| ≤ saMeanRadius vlo B θ / 2 →
      ∀ ε R z : ℝ, 0 ≤ ε → ε ≤ 1 / 32 → 0 ≤ R → |z| ≤ R →
      (6 * C + saLogVarianceConstant vlo B θ / 2 * (3 * A + 2 * Y) +
        saRateThird vlo B θ * (A * Y ^ 2 + Y ^ 3 / 3)) / Real.sqrt l ≤ ε →
      let σ := Real.sqrt ((l : ℝ) * (lawVar ν + s ^ 2) / 2)
      let b := 4 / (5 * (vhi + 1))
      σ * (R + 1) ≤ Real.sqrt l * Y →
      K * Real.exp (-b * Y ^ 2) / (b * Y) ≤ ε * saGaussianTail R →
      saGaussianTail (Real.sqrt l * Y / σ) ≤ ε * saGaussianTail R →
      |saSplitQuantile (saDensity_centeredSum ν hs (show 0 < l by omega))
          (2 * l * u) (cdf (gaussianReal 0 1) z) - (l : ℝ) * u - σ * z| ≤ 32 * σ * ε := by
  obtain ⟨C₁, hC₁, hratio⟩ := exists_uniform_saSplitDensity_block_ratio
    vlo vhi κ₃ B θ D c hvlo hvhi hB hθ hD hc
  obtain ⟨C₂, K, hC₂, hK, htail⟩ := exists_uniform_saSplitDensity_block_tails
    vlo vhi κ₃ B θ D c hvlo hvhi hB hθ hD hc
  refine ⟨max C₁ C₂, K, lt_of_lt_of_le hC₁ (le_max_left _ _), hK, ?_⟩
  intro ν hν hsm s hs hs1 l hl hscale hlarge A Y hA hY hwindow hYscale u hu huR
    ε R z hε hε1 hR hz herr
  dsimp only
  intro hYstd htailNum hgauss
  have hl0 : 0 < l := by omega
  have hr : 0 < Real.sqrt (l : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hl0)
  have hV : 0 < lawVar ν + s ^ 2 := by nlinarith [hν.var_ge, sq_nonneg s]
  have hσ : 0 < Real.sqrt ((l : ℝ) * (lawVar ν + s ^ 2) / 2) := by positivity
  have hlarge₁ : 2 * C₁ ≤ Real.sqrt l := by nlinarith [le_max_left C₁ C₂]
  have hlarge₂ : 2 * C₂ ≤ Real.sqrt l := by nlinarith [le_max_right C₁ C₂]
  have ht := htail ν hν hsm s hs hs1 l hl hscale hlarge₂ u huR Y hY hYscale
  apply saQuantile_error_of_block_density
    ((saDensity_centeredSum ν hs hl0).splitDensity (2 * l * u)) hr hσ hε hε1 hR hY.le
    hYstd hz
  · intro x hx
    have he := hratio ν hν hsm s hs hs1 l hl hscale hlarge₁ A Y hA hY.le hwindow u hu x hx
    rw [Real.sq_sqrt (show 0 ≤ (l : ℝ) * (lawVar ν + s ^ 2) / 2 by positivity)]
    apply he.trans
    apply le_trans _ herr
    gcongr
    exact le_max_left _ _
  · exact ht.2.trans htailNum
  · exact ht.1.trans htailNum
  · exact hgauss

/-- Root quantile defect under the same explicit numerical window conditions. -/
theorem exists_uniform_saCenteredSumQuantile_block_error
    (vlo vhi κ₃ B θ D c : ℝ) (hvlo : 0 < vlo) (hvhi : 0 < vhi)
    (hB : 0 < B) (hθ : 0 < θ) (hD : 0 < D) (hc : 0 < c) :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
      ∀ ν : ProbabilityMeasure ℝ, UnivClass vlo vhi κ₃ B θ ν → SmoothPart D c ν →
      ∀ s : ℝ, ∀ hs : 0 < s, s ≤ 1 → ∀ l : ℕ, ∀ hl : 2 ≤ l,
      1 / s ≤ (l : ℝ) ^ 8 → 2 * C ≤ Real.sqrt l →
      ∀ Y : ℝ, 0 < Y → Y ≤ saMeanRadius vlo B θ * Real.sqrt l →
      ∀ ε R z : ℝ, 0 ≤ ε → ε ≤ 1 / 32 → 0 ≤ R → |z| ≤ R →
      (2 * C + saLogVarianceConstant vlo B θ / 2 * Y +
        saRateThird vlo B θ * Y ^ 3 / 6) / Real.sqrt l ≤ ε →
      let σ := Real.sqrt ((l : ℝ) * (lawVar ν + s ^ 2))
      let b := 2 / (5 * (vhi + 1))
      σ * (R + 1) ≤ Real.sqrt l * Y →
      K * Real.exp (-b * Y ^ 2) / (b * Y) ≤ ε * saGaussianTail R →
      saGaussianTail (Real.sqrt l * Y / σ) ≤ ε * saGaussianTail R →
      |saQuantile (cdf ((saDensity_centeredSum ν hs (show 0 < l by omega)).law : Measure ℝ))
          (cdf (gaussianReal 0 1) z) - σ * z| ≤ 32 * σ * ε := by
  obtain ⟨C, hC, hratio⟩ := exists_uniform_saCenteredSumDensity_block_ratio
    vlo vhi κ₃ B θ D c hvlo hvhi hB hθ hD hc
  obtain ⟨K, hK, htail⟩ := exists_uniform_saCenteredSumDensity_block_tails
    vlo vhi κ₃ B θ D c hvlo hvhi hB hθ hD hc
  refine ⟨C, K, hC, hK, ?_⟩
  intro ν hν hsm s hs hs1 l hl hscale hlarge Y hY hwindow ε R z hε hε1 hR hz herr
  dsimp only
  intro hYstd htailNum hgauss
  have hl0 : 0 < l := by omega
  have hr : 0 < Real.sqrt (l : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hl0)
  have hV : 0 < lawVar ν + s ^ 2 := by nlinarith [hν.var_ge, sq_nonneg s]
  have hσ : 0 < Real.sqrt ((l : ℝ) * (lawVar ν + s ^ 2)) := by positivity
  have ht := htail ν hν hsm s hs hs1 l hl hscale Y hY hwindow
  have hlocal (x : ℝ) (hx : |x| ≤ Y) :
      |Real.log (saCenteredSumDensity ν s l (0 + Real.sqrt l * x) /
        gaussianPDFReal 0 (Real.toNNReal (Real.sqrt ((l : ℝ) * (lawVar ν + s ^ 2)) ^ 2))
          (Real.sqrt l * x))| ≤ ε := by
    rw [zero_add, Real.sq_sqrt (show 0 ≤ (l : ℝ) * (lawVar ν + s ^ 2) by positivity)]
    exact (hratio ν hν hsm s hs hs1 l hl hscale hlarge Y hY.le hwindow x hx).trans herr
  have he := saQuantile_error_of_block_density (saDensity_centeredSum ν hs hl0) hr hσ
    hε hε1 hR hY.le hYstd hz hlocal
    (by simpa only [zero_add] using ht.2.trans htailNum)
    (by simpa only [zero_sub, neg_mul] using ht.1.trans htailNum) hgauss
  simpa only [sub_zero] using he

end

end PGM
