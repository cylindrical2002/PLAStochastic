import PLAStochastic.Index.GEP.StrongApprox.Saddle.ExactFormula
import PLAStochastic.Index.GEP.StrongApprox.Tilt.CentralDensity

/-! # WP5: quantitative saddle bounds for the actual sum density -/

namespace PGM

noncomputable section

open MeasureTheory Measure ProbabilityTheory Set
open scoped Real ENNReal NNReal

theorem saCenteredSumDensity_pos (ν : ProbabilityMeasure ℝ) {s : ℝ} (hs : 0 < s)
    {l : ℕ} (hl : 0 < l) (x : ℝ) : 0 < saCenteredSumDensity ν s l x := by
  let : IsProbabilityMeasure ((ν : Measure ℝ).map (fun y => y - 1)) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  apply saGaussianDensity_pos
  exact mul_ne_zero (by exact_mod_cast hl.ne')
    (by simp [Real.toNNReal_eq_zero, (sq_pos_of_pos hs).not_ge])

variable {vlo vhi κ₃ B θ : ℝ} {ν : ProbabilityMeasure ℝ}

/-- A maximum on the fixed tilt interval realizes the truncated Legendre transform. -/
theorem UnivClass.exists_saGlobalRate_saddle (h : UnivClass vlo vhi κ₃ B θ ν)
    (hvlo : 0 < vlo) (hθ : 0 < θ) (s w : ℝ) :
    ∃ lam : ℝ, |lam| ≤ saTiltRadius vlo B θ ∧
      saGlobalRate vlo B θ ν s w = lam * w - saSmoothCGF ν s lam := by
  have hr := (saTiltRadius_pos (B := B) hvlo hθ).le
  obtain ⟨lam, hlam, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc (-saTiltRadius vlo B θ) (saTiltRadius vlo B θ)).Nonempty from
      ⟨0, by constructor <;> linarith⟩)
    ((continuousOn_id.mul continuousOn_const).sub (h.continuousOn_saSmoothCGF hθ s))
  refine ⟨lam, abs_le.mpr hlam, le_antisymm ?_ (h.le_saGlobalRate hθ s w (abs_le.mpr hlam))⟩
  apply csSup_le (saGlobalRate_image_nonempty hvlo hθ ν s w)
  rintro z ⟨t, ht, rfl⟩
  exact hmax ht

/-- A global density bound using the actual smoothing width. There is no local
CLT assumption here, and the tilt is chosen over the fixed compact interval. -/
theorem UnivClass.saCenteredSumDensity_global_upper (h : UnivClass vlo vhi κ₃ B θ ν)
    (hvlo : 0 < vlo) (hθ : 0 < θ) {s : ℝ} (hs : 0 < s) {l : ℕ} (hl : 0 < l)
    (w : ℝ) :
    saCenteredSumDensity ν s l (l * w) ≤
      (Real.sqrt (2 * π * ((l : ℝ) * s ^ 2)))⁻¹ *
        Real.exp (-(l : ℝ) * saGlobalRate vlo B θ ν s w) := by
  obtain ⟨lam, hlam, heq⟩ := h.exists_saGlobalRate_saddle hvlo hθ s w
  have hlθ : |lam| ≤ θ := (hlam.trans (saTiltRadius_le_half vlo B hθ)).trans (by linarith)
  let μ := (ν : Measure ℝ).map (fun y => y - 1)
  let : IsProbabilityMeasure μ := Measure.isProbabilityMeasure_map (by fun_prop)
  have hM : Integrable (fun y : ℝ => Real.exp (lam * y)) μ := by
    rw [integrable_map_measure (by fun_prop) (by fun_prop)]
    exact h.integrable_exp_centered hlθ
  have hMl := sa_integrable_exp_convPow hM l
  let := isProbabilityMeasure_tilted hMl
  have hv : (l : ℝ≥0) * Real.toNNReal (s ^ 2) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast hl.ne')
      (by simp [Real.toNNReal_eq_zero, (sq_pos_of_pos hs).not_ge])
  have ht := saGaussianDensity_tilt (convPow μ l) hv hMl ((l : ℝ) * w)
  rw [sa_cgf_convPow, sa_cgf_centered_map, NNReal.coe_mul, NNReal.coe_natCast,
    Real.coe_toNNReal _ (sq_nonneg s)] at ht
  have he : (l : ℝ) * cgf (fun y : ℝ => y - 1) (ν : Measure ℝ) lam +
      ((l : ℝ) * s ^ 2) * lam ^ 2 / 2 - lam * ((l : ℝ) * w) =
      -(l : ℝ) * saGlobalRate vlo B θ ν s w := by
    rw [heq]
    unfold saSmoothCGF
    ring
  rw [he] at ht
  change saGaussianDensity (convPow μ l) _ _ ≤ _
  rw [ht]
  have hb := saGaussianDensity_le ((convPow μ l).tilted (fun y => lam * y))
    ((l : ℝ≥0) * Real.toNNReal (s ^ 2)) ((l : ℝ) * w - ((l : ℝ) * s ^ 2) * lam)
  rw [NNReal.coe_mul, NNReal.coe_natCast, Real.coe_toNNReal _ (sq_nonneg s)] at hb
  calc
    _ ≤ Real.exp (-(l : ℝ) * saGlobalRate vlo B θ ν s w) *
        (Real.sqrt (2 * π * ((l : ℝ) * s ^ 2)))⁻¹ :=
      mul_le_mul_of_nonneg_left hb (Real.exp_nonneg _)
    _ = _ := mul_comm _ _

/-- The remaining logarithmic density error is the genuine local CLT center
error plus the controlled change of tilted variance. -/
theorem UnivClass.saCenteredSumDensity_log_correction (h : UnivClass vlo vhi κ₃ B θ ν)
    (hvlo : 0 < vlo) (hθ : 0 < θ) {s : ℝ} (hs : 0 < s) {l : ℕ} (hl : 0 < l)
    {w : ℝ} (hw : |w| ≤ saMeanRadius vlo B θ) :
    |Real.log (saCenteredSumDensity ν s l (l * w)) +
        (l : ℝ) * saRate vlo B θ ν s w + Real.log (Real.sqrt l) +
        Real.log (Real.sqrt (2 * π * (lawVar ν + s ^ 2)))| ≤
      |Real.log (saTiltCentralFactor ν (saSaddle vlo B θ ν s w) s l)| +
        saLogVarianceConstant vlo B θ / 2 * |w| := by
  let lam := saSaddle vlo B θ ν s w
  let V := iteratedDeriv 2 (saSmoothCGF ν s) lam
  have hlam := abs_le.mpr (h.saSaddle_spec hvlo hθ s
    (hw.trans (saMeanRadius_lt_full hvlo hθ).le)).1
  have hlt : |lam| < θ :=
    (hlam.trans (saTiltRadius_le_half vlo B hθ)).trans_lt (by linarith)
  have hV : 0 < V := by
    have hb := (h.saSmoothCGF_variance_bracket hvlo hθ hlam s).1
    have := h.var_ge
    dsimp [V]
    nlinarith [sq_nonneg s]
  have hV0 : 0 < lawVar ν + s ^ 2 := by nlinarith [h.var_ge, sq_nonneg s]
  have hroot : 0 < Real.sqrt (l : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hl)
  have hbase : 0 < Real.sqrt (2 * π) := Real.sqrt_pos.mpr (by positivity)
  have hq : 0 < saTiltedCenterDensity ν s l lam := by
    let := h.isProbabilityMeasure_saRecenteredTilt hlt.le
    let : IsProbabilityMeasure ((convPow (saRecenteredTilt ν lam) l).map ((Real.sqrt l)⁻¹ * ·)) :=
      Measure.isProbabilityMeasure_map (by fun_prop)
    apply saGaussianDensity_pos
    simp [Real.toNNReal_eq_zero, (sq_pos_of_pos hs).not_ge]
  have hfac : saTiltCentralFactor ν lam s l =
      Real.sqrt (2 * π * V) * saTiltedCenterDensity ν s l lam := by
    dsimp [saTiltCentralFactor, V, saTiltedCenterDensity]
    rw [h.iteratedDeriv_two_saSmoothCGF hlt s]
  have hlogfac : Real.log (saTiltCentralFactor ν lam s l) =
      Real.log (Real.sqrt (2 * π)) + Real.log (Real.sqrt V) +
        Real.log (saTiltedCenterDensity ν s l lam) := by
    rw [hfac, Real.sqrt_mul (by positivity),
      Real.log_mul (mul_pos hbase (Real.sqrt_pos.mpr hV)).ne' hq.ne',
      Real.log_mul hbase.ne' (Real.sqrt_pos.mpr hV).ne']
  have hlogp : Real.log (saCenteredSumDensity ν s l (l * w)) =
      -(l : ℝ) * saRate vlo B θ ν s w - Real.log (Real.sqrt l) +
        Real.log (saTiltedCenterDensity ν s l lam) := by
    rw [h.saCenteredSumDensity_saddle hvlo hθ hs hl hw,
      Real.log_mul (div_ne_zero (Real.exp_ne_zero _) hroot.ne') hq.ne',
      Real.log_div (Real.exp_ne_zero _) hroot.ne', Real.log_exp]
  have hnorm : Real.log (Real.sqrt (2 * π * (lawVar ν + s ^ 2))) =
      Real.log (Real.sqrt (2 * π)) + Real.log (Real.sqrt (lawVar ν + s ^ 2)) := by
    rw [Real.sqrt_mul (by positivity), Real.log_mul hbase.ne' (Real.sqrt_pos.mpr hV0).ne']
  have heq : Real.log (saCenteredSumDensity ν s l (l * w)) +
      (l : ℝ) * saRate vlo B θ ν s w + Real.log (Real.sqrt l) +
      Real.log (Real.sqrt (2 * π * (lawVar ν + s ^ 2))) =
      Real.log (saTiltCentralFactor ν lam s l) -
        (Real.log (Real.sqrt V) - Real.log (Real.sqrt (lawVar ν + s ^ 2))) := by
    rw [hlogp, hnorm, hlogfac]
    ring
  rw [heq]
  exact (abs_sub _ _).trans (add_le_add le_rfl
    (h.log_saSaddle_sqrt_variance_sub_zero hvlo hθ s hw))

/-- The genuine central CLT makes the saddle-density estimate uniform in the
input law, the smoothing width, the block length, and the target mean. -/
theorem exists_uniform_saCenteredSumDensity_log_correction
    (vlo vhi κ₃ B θ D c : ℝ) (hvlo : 0 < vlo) (hvhi : 0 < vhi)
    (hB : 0 < B) (hθ : 0 < θ) (hD : 0 < D) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧
      ∀ ν : ProbabilityMeasure ℝ, UnivClass vlo vhi κ₃ B θ ν → SmoothPart D c ν →
      ∀ s : ℝ, 0 < s → s ≤ 1 → ∀ l : ℕ, 2 ≤ l →
      1 / s ≤ (l : ℝ) ^ 8 → 2 * C ≤ Real.sqrt l →
      ∀ w : ℝ, |w| ≤ saMeanRadius vlo B θ →
        |Real.log (saCenteredSumDensity ν s l (l * w)) +
            (l : ℝ) * saRate vlo B θ ν s w + Real.log (Real.sqrt l) +
            Real.log (Real.sqrt (2 * π * (lawVar ν + s ^ 2)))| ≤
          (2 * C) / Real.sqrt l + saLogVarianceConstant vlo B θ / 2 * |w| := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_saTiltCentralLog vlo vhi κ₃ B θ D c
    hvlo hvhi hB hθ hD hc
  refine ⟨C, hC, ?_⟩
  intro ν hν hsm s hs hs1 l hl hscale hlarge w hw
  have hmem := (hν.saSaddle_spec hvlo hθ s (hw.trans (saMeanRadius_lt_full hvlo hθ).le)).1
  apply (hν.saCenteredSumDensity_log_correction hvlo hθ hs (by omega) hw).trans
  exact add_le_add
    (hb ν hν hsm _ (abs_le.mpr hmem) s hs hs1 l hl hscale hlarge).2 le_rfl

end

end PGM
