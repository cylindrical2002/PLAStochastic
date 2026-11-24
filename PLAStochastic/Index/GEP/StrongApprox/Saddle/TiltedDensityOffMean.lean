import PLAStochastic.Index.GEP.StrongApprox.Saddle.ExactTilting

/-! # WP5: exact tilted density formula away from the tilted mean -/

namespace PGM

noncomputable section

open MeasureTheory Measure ProbabilityTheory
open scoped Real ENNReal NNReal

/-- Exact tilting, recentering and normalization at an arbitrary observation. -/
theorem saGaussianDensity_convPow_tilt_at (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {lam : ℝ} (hM : Integrable (fun y : ℝ => Real.exp (lam * y)) μ)
    {v : ℝ≥0} (hv : v ≠ 0) {l : ℕ} (hl : 0 < l) (m w : ℝ) :
    saGaussianDensity (convPow μ l) ((l : ℝ≥0) * v) (l * w) =
      Real.exp ((l : ℝ) * (cgf id μ lam + v * lam ^ 2 / 2 - lam * w)) /
        Real.sqrt l *
        saGaussianDensity ((convPow ((μ.tilted (fun y => lam * y)).map (fun y => y - m)) l).map
          ((Real.sqrt l)⁻¹ * ·)) v (Real.sqrt l * (w - m - v * lam)) := by
  let ρ := μ.tilted (fun y => lam * y)
  let : IsProbabilityMeasure ρ := isProbabilityMeasure_tilted hM
  have hlr : 0 < (l : ℝ) := by exact_mod_cast hl
  have hls : 0 < Real.sqrt l := Real.sqrt_pos.mpr hlr
  have hlsq : Real.sqrt (l : ℝ) ^ 2 = (l : ℝ) := Real.sq_sqrt hlr.le
  have hlv : (l : ℝ≥0) * v ≠ 0 := mul_ne_zero (by exact_mod_cast hl.ne') hv
  have ht := saGaussianDensity_tilt (convPow μ l) hlv (sa_integrable_exp_convPow hM l)
    ((l : ℝ) * w)
  rw [sa_cgf_convPow, sa_tilted_convPow] at ht
  have hx : (l : ℝ) * w - ↑((l : ℝ≥0) * v) * lam = l * (w - v * lam) := by
    push_cast
    ring
  have he : (l : ℝ) * cgf id μ lam + ↑((l : ℝ≥0) * v) * lam ^ 2 / 2 - lam * ((l : ℝ) * w) =
      (l : ℝ) * (cgf id μ lam + v * lam ^ 2 / 2 - lam * w) := by
    push_cast
    ring
  rw [hx, he] at ht
  have hscale := saGaussianDensity_map_inv_mul
    (convPow (ρ.map (fun y => y - m)) l) hls (Real.sqrt l * (w - m - v * lam)) v
  have hsq : (⟨Real.sqrt l ^ 2, sq_nonneg (Real.sqrt l)⟩ : ℝ≥0) = (l : ℝ≥0) := by
    ext
    exact hlsq
  rw [hsq] at hscale
  conv_rhs at hscale => rw [sa_convPow_map_sub, saGaussianDensity_map_sub]
  have hz : Real.sqrt (l : ℝ) * (Real.sqrt l * (w - m - v * lam)) + (l : ℝ) * m =
      (l : ℝ) * (w - v * lam) := by
    rw [← mul_assoc, ← sq, hlsq]
    ring
  rw [hz] at hscale
  rw [ht]
  change _ = _ * saGaussianDensity ((convPow (ρ.map (fun y => y - m)) l).map _) v _
  rw [hscale]
  field_simp
  rfl

end

end PGM
