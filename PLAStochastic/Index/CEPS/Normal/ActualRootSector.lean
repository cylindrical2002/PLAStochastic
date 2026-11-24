import PLAStochastic.Index.CEPS.Normal.ActualMorseData
import PLAStochastic.Index.CEPS.Ident.Reality

/-! # A quantitative sector bound for the actual root difference

The inverse Morse chart is compared to its class-centred linear model.
The square-root sector is used only for nonnegative real discount.
-/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}
variable (hW : IsStepLaw ρW fW D θ v) (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
/-- The signed inverse chart differs from its linear model by at most one eighth. -/
theorem cepsMorseRoot_linear_error {μ r : ℂ} (hμ : ‖μ‖ < cepsChartMu D θ)
    (hr : ‖r‖ < cepsChartRho D θ) :
    ‖cepsMorseRoot D θ ρW μ r - cepsMorseCenter D θ ρW μ -
        r / (Real.sqrt (cepsStepVar ρW / 2) : ℂ)‖ ≤
      ‖r‖ / (8 * Real.sqrt (cepsStepVar ρW / 2)) := by
  let s := Real.sqrt (cepsStepVar ρW / 2)
  let u := cepsMorseRoot D θ ρW μ r - cepsMorseCenter D θ ρW μ
  let k := cepsMorseK ρW (cepsMorseCenter D θ ρW μ) u
  have hs : 0 < s := Real.sqrt_pos.mpr (by linarith [cepsStepVar_pos hW hθ hD])
  have hs2 : s ^ 2 = cepsStepVar ρW / 2 := cepsChartSlope_sq hW hθ hD
  obtain ⟨humem, hg⟩ := cepsMorseRoot_sub_center hW hθ hD hμ hr
  have hu : ‖u‖ < cepsChartRadius D θ := mem_ball_zero_iff.mp humem
  have hb := norm_cepsMorseCenter_lt hW hθ hD hμ
  have hnear := cepsMorseK_near hW hθ hD hb (show ‖u‖ < 2 * cepsChartRadius D θ by
    linarith [cepsChartRadius_pos hD hθ])
  have hsqrt := norm_sqrt_sub_sqrt_le (z := k) (c := cepsStepVar ρW / 2)
    (by linarith [cepsStepVar_pos hW hθ hD])
  have hreal : ((cepsStepVar ρW / 2 : ℝ) : ℂ) = (cepsStepVar ρW : ℂ) / 2 := by
    push_cast; rfl
  rw [hreal] at hsqrt
  have hk : ‖Complex.sqrt k - (s : ℂ)‖ ≤ 3 * cepsVarLo D / 128 / s :=
    hsqrt.trans (div_le_div_of_nonneg_right hnear hs.le)
  have hlin : ‖u‖ ≤ 2 / s * ‖r‖ := by
    have h := norm_cepsMorseRoot_sub_le hW hθ hD hμ hr
      (r₂ := 0) (by simpa using cepsChartRho_pos hD hθ)
    rwa [cepsMorseRoot_zero hW hθ hD hμ, sub_zero, norm_cepsChartSlope] at h
  have he : (u - r / (s : ℂ)) * (s : ℂ) = u * ((s : ℂ) - Complex.sqrt k) := by
    have hg' : u * Complex.sqrt k = r := by simpa only [cepsMorseG] using hg
    rw [← hg']
    have hsc : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
    field_simp
  have hn : ‖u - r / (s : ℂ)‖ = ‖u‖ * ‖Complex.sqrt k - (s : ℂ)‖ / s := by
    have h := congrArg norm he
    rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos hs, norm_mul] at h
    rw [norm_sub_rev (s : ℂ)] at h
    exact (eq_div_iff hs.ne').mpr h
  have hcoeff : (3 * cepsVarLo D / 128 / s) / s ≤ 3 / 64 := by
    rw [div_div, div_le_iff₀ (mul_pos hs hs)]
    nlinarith [cepsVarLo_le hW hθ hD]
  change ‖u - r / (s : ℂ)‖ ≤ ‖r‖ / (8 * s)
  calc
    _ = ‖u‖ * (‖Complex.sqrt k - (s : ℂ)‖ / s) := by rw [hn]; ring
    _ ≤ ‖u‖ * (3 / 64) := mul_le_mul_of_nonneg_left
      ((div_le_div_of_nonneg_right hk hs.le).trans hcoeff) (norm_nonneg _)
    _ ≤ (2 / s * ‖r‖) * (3 / 64) := mul_le_mul_of_nonneg_right hlin (by norm_num)
    _ = (3 / 32) * (‖r‖ / s) := by ring
    _ ≤ ‖r‖ / (8 * s) := by
      calc
        _ ≤ (1 / 8) * (‖r‖ / s) := mul_le_mul_of_nonneg_right (by norm_num)
          (div_nonneg (norm_nonneg r) hs.le)
        _ = _ := by ring

private theorem sqrt_re_ge_half_norm {z : ℂ} (hz : 0 ≤ z.re) :
    ‖Complex.sqrt z‖ / 2 ≤ (Complex.sqrt z).re := by
  have hre : 0 ≤ (Complex.sqrt z).re := by
    rw [Complex.sqrt, cpow_inv_two_re]; exact Real.sqrt_nonneg _
  have hs : (Complex.sqrt z).re ^ 2 - (Complex.sqrt z).im ^ 2 = z.re := by
    have hsq : (Complex.sqrt z) ^ 2 = z := by
      rw [Complex.sqrt]; exact cpow_ofNat_inv_pow z 2
    have := congrArg Complex.re hsq
    simpa [pow_two, mul_re] using this
  have hn := Complex.sq_norm_sub_sq_re (Complex.sqrt z)
  nlinarith [norm_nonneg (Complex.sqrt z), sq_nonneg (Complex.sqrt z).re]

variable (dom : CepsCanonDomain D θ v)

include hW hθ hD in
/-- The class-centred sector estimate includes both zero discount and root merging. -/
theorem cepsRoots_difference_re_ge {μ : ℝ} (hμ : |μ| ≤ dom.μ₀)
    {q : ℂ} (hq : ‖q‖ ≤ dom.q₀) (hre : 0 ≤ q.re) :
    ‖cepsRootR D θ ρW μ q‖ / (2 * Real.sqrt v) ≤
      (cepsRootPlus D θ ρW μ q - cepsRootMinus D θ ρW μ q).re := by
  have hμ' : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  have hμc := dom.μ_lt_chart hμ'
  have hr := dom.norm_cepsRootR_lt hW hθ hD hμ' hq
  let r := cepsRootR D θ ρW μ q
  let s := Real.sqrt (cepsStepVar ρW / 2)
  let η := cepsRootPlus D θ ρW μ q - cepsRootMinus D θ ρW μ q
  have hs : 0 < s := Real.sqrt_pos.mpr (by linarith [cepsStepVar_pos hW hθ hD])
  have hsp : 0 < Real.sqrt v := Real.sqrt_pos.mpr (CepsCanonDomain.v_pos hW hθ hD)
  have hsv : s ≤ Real.sqrt v := by
    apply Real.sqrt_le_sqrt
    linarith [cepsStepVar_le hW, cepsStepVar_pos hW hθ hD]
  have hrre : ‖r‖ / 2 ≤ r.re := sqrt_re_ge_half_norm
    (show 0 ≤ (q - cepsMorseMin D θ ρW μ).re by
      rw [sub_re]; linarith [re_cepsMorseMin_nonpos hW hθ hD hμc])
  have hp := cepsMorseRoot_linear_error hW hθ hD hμc hr
  have hm := cepsMorseRoot_linear_error hW hθ hD hμc
    (r := -r) (by simpa using hr)
  have herr : ‖η - 2 * r / (s : ℂ)‖ ≤ ‖r‖ / (4 * s) := by
    have he : η - 2 * r / (s : ℂ) =
        (cepsMorseRoot D θ ρW μ r - cepsMorseCenter D θ ρW μ - r / (s : ℂ)) -
        (cepsMorseRoot D θ ρW μ (-r) - cepsMorseCenter D θ ρW μ - (-r) / (s : ℂ)) := by
      dsimp [η, cepsRootPlus, cepsRootMinus, r]; ring
    rw [he]
    have ht := norm_sub_le
      (cepsMorseRoot D θ ρW μ r - cepsMorseCenter D θ ρW μ - r / (s : ℂ))
      (cepsMorseRoot D θ ρW μ (-r) - cepsMorseCenter D θ ρW μ - (-r) / (s : ℂ))
    rw [norm_neg] at hm
    calc
      _ ≤ _ := ht
      _ ≤ ‖r‖ / (8 * s) + ‖r‖ / (8 * s) := add_le_add hp hm
      _ = _ := by ring
  have hreal : (η - 2 * r / (s : ℂ)).re = η.re - 2 * r.re / s := by
    simp [Complex.div_ofReal_re, mul_re]
  have hneg := (neg_le_abs (η - 2 * r / (s : ℂ)).re).trans
    ((abs_re_le_norm _).trans herr)
  rw [hreal] at hneg
  have hsector : ‖r‖ / (2 * s) ≤ η.re := by
    have hrr := div_le_div_of_nonneg_right hrre hs.le
    ring_nf at hneg hrr ⊢
    have hnon := mul_nonneg (inv_nonneg.mpr hs.le) (norm_nonneg r)
    linarith
  exact (div_le_div_of_nonneg_left (norm_nonneg r) (by positivity) (by linarith)).trans hsector


include hW hθ hD in
/-- A class upper bound for the root difference with its vanishing factor retained. -/
theorem cepsRoots_difference_norm_le {μ q : ℂ} (hμ : ‖μ‖ ≤ dom.μ₀)
    (hq : ‖q‖ ≤ dom.q₀) :
    ‖cepsRootPlus D θ ρW μ q - cepsRootMinus D θ ρW μ q‖ ≤
      2 * cepsChartK D * ‖cepsRootR D θ ρW μ q‖ := by
  have hr := dom.norm_cepsRootR_lt hW hθ hD hμ hq
  have hp := norm_rootPlus_sub_center_le hW hθ hD (dom.μ_lt_chart hμ) hr
  have hm := norm_rootMinus_sub_center_le hW hθ hD (dom.μ_lt_chart hμ) hr
  calc
    _ = ‖(cepsRootPlus D θ ρW μ q - cepsMorseCenter D θ ρW μ) -
        (cepsRootMinus D θ ρW μ q - cepsMorseCenter D θ ρW μ)‖ := by ring_nf
    _ ≤ _ := norm_sub_le _ _
    _ ≤ cepsChartK D * ‖cepsRootR D θ ρW μ q‖ +
        cepsChartK D * ‖cepsRootR D θ ρW μ q‖ := add_le_add hp hm
    _ = _ := by ring

end PGM
