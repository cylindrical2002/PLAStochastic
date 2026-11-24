import PLAStochastic.Index.CEPS.Normal.ActualRootSector

/-! # Actual root separation and sectors under a small negative real discount -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}
variable (hW : IsStepLaw ρW fW D θ v) (hθ : 0 < θ) (hD : 0 < D)
variable (dom : CepsCanonDomain D θ v)

include hW hθ hD in
theorem cepsRoots_difference_linear_error {μ q : ℂ} (hμ : ‖μ‖ ≤ dom.μ₀)
    (hq : ‖q‖ ≤ dom.q₀) :
    ‖cepsRootPlus D θ ρW μ q - cepsRootMinus D θ ρW μ q -
      2 * cepsRootR D θ ρW μ q / (Real.sqrt (cepsStepVar ρW / 2) : ℂ)‖ ≤
        ‖cepsRootR D θ ρW μ q‖ / (4 * Real.sqrt (cepsStepVar ρW / 2)) := by
  have hr := dom.norm_cepsRootR_lt hW hθ hD hμ hq
  let r := cepsRootR D θ ρW μ q
  let s := Real.sqrt (cepsStepVar ρW / 2)
  have hp := cepsMorseRoot_linear_error hW hθ hD (dom.μ_lt_chart hμ) hr
  have hm := cepsMorseRoot_linear_error hW hθ hD (dom.μ_lt_chart hμ)
    (r := -r) (by simpa using hr)
  have he : cepsRootPlus D θ ρW μ q - cepsRootMinus D θ ρW μ q - 2 * r / (s : ℂ) =
      (cepsMorseRoot D θ ρW μ r - cepsMorseCenter D θ ρW μ - r / (s : ℂ)) -
        (cepsMorseRoot D θ ρW μ (-r) - cepsMorseCenter D θ ρW μ - (-r) / (s : ℂ)) := by
    dsimp [cepsRootPlus, cepsRootMinus, r]; ring
  rw [he]
  rw [norm_neg] at hm
  exact (norm_sub_le _ _).trans (by
    calc
      _ ≤ ‖r‖ / (8 * s) + ‖r‖ / (8 * s) := add_le_add hp hm
      _ = _ := by ring)

include hW hθ hD in
theorem cepsRoots_difference_norm_ge {μ q : ℂ} (hμ : ‖μ‖ ≤ dom.μ₀)
    (hq : ‖q‖ ≤ dom.q₀) :
    ‖cepsRootR D θ ρW μ q‖ / Real.sqrt v ≤
      ‖cepsRootPlus D θ ρW μ q - cepsRootMinus D θ ρW μ q‖ := by
  let s := Real.sqrt (cepsStepVar ρW / 2)
  have hs : 0 < s := Real.sqrt_pos.mpr (by linarith [cepsStepVar_pos hW hθ hD])
  have hsv : s ≤ Real.sqrt v := Real.sqrt_le_sqrt (by
    linarith [cepsStepVar_le hW, cepsStepVar_pos hW hθ hD])
  have hv : 0 < Real.sqrt v := Real.sqrt_pos.mpr (CepsCanonDomain.v_pos hW hθ hD)
  have he := cepsRoots_difference_linear_error hW hθ hD dom hμ hq
  have hh := norm_sub_norm_le
    (2 * cepsRootR D θ ρW μ q / (s : ℂ))
    (cepsRootPlus D θ ρW μ q - cepsRootMinus D θ ρW μ q)
  rw [norm_sub_rev (2 * cepsRootR D θ ρW μ q / (s : ℂ))
    (cepsRootPlus D θ ρW μ q - cepsRootMinus D θ ρW μ q)] at hh
  rw [norm_div, norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos hs] at hh
  norm_num at hh
  have hlow : ‖cepsRootR D θ ρW μ q‖ / s ≤
      ‖cepsRootPlus D θ ρW μ q - cepsRootMinus D θ ρW μ q‖ := by
    change ‖cepsRootPlus D θ ρW μ q - cepsRootMinus D θ ρW μ q -
      2 * cepsRootR D θ ρW μ q / (s : ℂ)‖ ≤ ‖cepsRootR D θ ρW μ q‖ / (4 * s) at he
    ring_nf at he hh ⊢
    have hnon : 0 ≤ ‖cepsRootR D θ ρW μ q‖ * s⁻¹ :=
      mul_nonneg (norm_nonneg _) (inv_nonneg.mpr hs.le)
    linarith
  exact (div_le_div_of_nonneg_left (norm_nonneg _) hs hsv).trans hlow

theorem sqrt_re_ge_half_norm_of_re_ge {z : ℂ} (hz : -‖z‖ / 2 ≤ z.re) :
    ‖Complex.sqrt z‖ / 2 ≤ (Complex.sqrt z).re := by
  have hre : 0 ≤ (Complex.sqrt z).re := by
    rw [Complex.sqrt, cpow_inv_two_re]; exact Real.sqrt_nonneg _
  have hs : (Complex.sqrt z).re ^ 2 - (Complex.sqrt z).im ^ 2 = z.re := by
    have hsq : (Complex.sqrt z) ^ 2 = z := sqrt_sq_eq z
    have := congrArg Complex.re hsq
    simpa [pow_two, mul_re] using this
  have hn := Complex.sq_norm_sub_sq_re (Complex.sqrt z)
  have hsq : ‖Complex.sqrt z‖ ^ 2 = ‖z‖ := by
    rw [← norm_pow, sqrt_sq_eq]
  nlinarith [norm_nonneg (Complex.sqrt z)]

include hW hθ hD in
theorem cepsRoots_difference_re_ge_of_rootR_sector {μ q : ℂ} (hμ : ‖μ‖ ≤ dom.μ₀)
    (hq : ‖q‖ ≤ dom.q₀)
    (hsector : ‖cepsRootR D θ ρW μ q‖ / 2 ≤ (cepsRootR D θ ρW μ q).re) :
    ‖cepsRootR D θ ρW μ q‖ / (2 * Real.sqrt v) ≤
      (cepsRootPlus D θ ρW μ q - cepsRootMinus D θ ρW μ q).re := by
  let r := cepsRootR D θ ρW μ q
  let s := Real.sqrt (cepsStepVar ρW / 2)
  let a := cepsRootPlus D θ ρW μ q - cepsRootMinus D θ ρW μ q
  have hs : 0 < s := Real.sqrt_pos.mpr (by linarith [cepsStepVar_pos hW hθ hD])
  have hv : 0 < Real.sqrt v := Real.sqrt_pos.mpr (CepsCanonDomain.v_pos hW hθ hD)
  have hsv : s ≤ Real.sqrt v := Real.sqrt_le_sqrt (by
    linarith [cepsStepVar_le hW, cepsStepVar_pos hW hθ hD])
  have herr := cepsRoots_difference_linear_error hW hθ hD dom hμ hq
  change ‖a - 2 * r / (s : ℂ)‖ ≤ ‖r‖ / (4 * s) at herr
  change ‖r‖ / 2 ≤ r.re at hsector
  have hreal : (a - 2 * r / (s : ℂ)).re = a.re - 2 * r.re / s := by
    simp [Complex.div_ofReal_re, mul_re]
  have hneg := (neg_le_abs (a - 2 * r / (s : ℂ)).re).trans
    ((abs_re_le_norm _).trans herr)
  rw [hreal] at hneg
  have hlow : ‖r‖ / (2 * s) ≤ a.re := by
    have hr := div_le_div_of_nonneg_right hsector hs.le
    ring_nf at hneg hr ⊢
    have hnon := mul_nonneg (inv_nonneg.mpr hs.le) (norm_nonneg r)
    linarith
  exact (div_le_div_of_nonneg_left (norm_nonneg r) (by positivity) (by linarith)).trans hlow

end PGM
