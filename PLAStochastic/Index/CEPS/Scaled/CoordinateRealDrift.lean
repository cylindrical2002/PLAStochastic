import PLAStochastic.Index.CEPS.Scaled.ComplexRootSector

/-! # The real part of the root coordinate dominates the Brownian drift scale -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledRootCoordinate_real_drift_lower (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.radicandScaleRadius lam / 2)) :
    3 * |lam| / (4 * cepsStepVar ρW) ≤
      (cepsScaledRootCoordinate D θ ρW lam z b).re / Real.sqrt (cepsStepVar ρW / 2) := by
  let V := cepsStepVar ρW
  let s := Real.sqrt (V / 2)
  let u := cepsScaledMorseRadicand D θ ρW lam z 0
  let w := cepsScaledMorseRadicand D θ ρW lam z b
  let r := cepsScaledRootCoordinate D θ ρW lam z b
  have hV : 0 < V := cepsStepVar_pos hW hθ hD
  have hs : 0 < s := Real.sqrt_pos.mpr (by positivity)
  have hs2 : s ^ 2 = V / 2 := Real.sq_sqrt (by positivity)
  have hr : 0 ≤ r.re := by
    dsimp [r, cepsScaledRootCoordinate]
    rw [Complex.sqrt, cpow_inv_two_re]
    exact Real.sqrt_nonneg _
  have hu : lam ^ 2 / (2 * V) ≤ u.re := by
    dsimp [u]
    rw [cepsScaledMorseRadicand_zero hW hθ hD]
    have he : (((lam : ℂ) ^ 2 / (2 * (cepsStepVar ρW : ℂ)))).re = lam ^ 2 / (2 * V) := by
      dsimp only [V]
      norm_cast
    rw [add_re, he]
    linarith
  have hdiff : ‖w - u‖ ≤ ‖u‖ / 4 := cepsScaledMorseRadicand_relative_quarter dom hW hθ hD lam hz hb
  have hneg := (neg_le_abs (w - u).re).trans ((abs_re_le_norm _).trans hdiff)
  simp only [sub_re] at hneg
  have hn := norm_sub_norm_le u w
  rw [norm_sub_rev] at hn
  have huN := re_le_norm u
  have hsq : r.re ^ 2 - r.im ^ 2 = w.re := by
    have he : r ^ 2 = w := sqrt_sq_eq w
    simpa [pow_two, mul_re] using congrArg Complex.re he
  have hnr := Complex.sq_norm_sub_sq_re r
  have hnorm : ‖r‖ ^ 2 = ‖w‖ := norm_complex_sqrt_sq w
  have hreal : lam ^ 2 / (2 * V) * 3 ≤ 4 * r.re ^ 2 := by
    nlinarith
  have hbase : 3 * lam ^ 2 ≤ 8 * V * r.re ^ 2 := by
    have h := (div_le_iff₀ (by positivity : 0 < 2 * V)).mp
      (show 3 * lam ^ 2 / (2 * V) ≤ 4 * r.re ^ 2 from
        (by simpa only [show 3 * lam ^ 2 / (2 * V) = lam ^ 2 / (2 * V) * 3 by ring] using hreal))
    nlinarith
  have hmul : 3 * |lam| * s ≤ 4 * V * r.re := by
    apply (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num : 2 ≠ 0)).mp
    have hscaled := mul_le_mul_of_nonneg_left hbase hV.le
    rw [mul_pow, mul_pow, sq_abs, hs2]
    nlinarith [mul_nonneg hV.le (sq_nonneg lam)]
  exact (div_le_div_iff₀ (by positivity : 0 < 4 * V) hs).mpr (by nlinarith [hmul])

end PGM
