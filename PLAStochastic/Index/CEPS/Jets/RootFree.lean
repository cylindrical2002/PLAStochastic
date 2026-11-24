import PLAStochastic.Index.CEPS.Jets.Basic

/-!
# X8: the canonical factor without the removed quadratic

On the line `Re s = c₀` both near-zero roots `β±` lie in `|ζ| ≤ c₀/4`, so
`w(s) = D₀(s)/s² = (1 - β₊/s)(1 - β₋/s)` is holomorphic, close to `1` and `O(1/|s|)`-close on the
half-plane `Re s ≥ c₀`. Its Cauchy integral vanishes for `Re ζ < c₀` (shift the line to the right,
`integral_vline_eq_zero_of_right`). With `F̃ = F w = d (s² - 1)/s²` (`cepsJetF`), principal
logarithms add (`log F̃ = log F + log w`, both factors in the right half-plane), hence

  `L(ζ; t, q) = (2π)⁻¹ ∫ log F̃(c₀ + i y; t, q)/(c₀ + i y - ζ) dy - log(1 - ζ)`

(`CepsCanonDomain.canonL_eq_cepsRootFreeL`), for real `|t| ≤ μ₀`, `‖q‖ ≤ q₀`, `Re ζ < c₀`.
The roots no longer appear.
-/

noncomputable section

open MeasureTheory Set Complex Filter Topology
open PGM.WienerHopf

namespace PGM

/-- The root-free canonical factor on the line `Re s = c` for a transform `T`:
`(2π)⁻¹ ∫ log F̃(s; t, q)/(s - ζ) dy - log(1 - ζ)`, `F̃(s; t, q) = (1 - e^{ts - q} T(s))(s² - 1)/s²`. -/
def cepsRootFreeL (c : ℝ) (T : ℂ → ℂ) (t : ℝ) (q ζ : ℂ) : ℂ :=
  (2 * Real.pi : ℂ)⁻¹ * (∫ y : ℝ, Complex.log (cepsJetF (c + y * I)
      (cexp (t * (c + y * I) - q) * T (c + y * I))) / (c + y * I - ζ)) - Complex.log (1 - ζ)

theorem continuous_vline_of_differentiableAt {f : ℂ → ℂ} {c : ℝ}
    (hd : ∀ y : ℝ, DifferentiableAt ℂ f (c + y * I)) : Continuous fun y : ℝ => f (c + y * I) :=
  continuous_iff_continuousAt.mpr fun y => by
    have h1 : ContinuousAt (fun y : ℝ => (c : ℂ) + y * I) y := by fun_prop
    exact ContinuousAt.comp (g := f) (f := fun y : ℝ => (c : ℂ) + y * I) (hd y).continuousAt h1

theorem vline_re (c y : ℝ) : ((c : ℂ) + y * I).re = c := by simp

theorem integrable_vline_of_right {f : ℂ → ℂ} {c K : ℝ} {ζ : ℂ} (hc : 0 < c)
    (hζ : ζ.re < c) (hd : ∀ z : ℂ, c ≤ z.re → DifferentiableAt ℂ f z)
    (hb : ∀ z : ℂ, c ≤ z.re → ‖f z‖ ≤ K * ‖(z * (z - ζ))⁻¹‖) {c' : ℝ} (hcc : c ≤ c') :
    Integrable fun y : ℝ => f (c' + y * I) :=
  ((integrable_inv_mul_line (by linarith) (by linarith : ζ.re < c')).norm.const_mul K).mono'
    (continuous_vline_of_differentiableAt fun y => hd _ (by rw [vline_re]; exact hcc)).aestronglyMeasurable
    (Eventually.of_forall fun y => hb _ (by rw [vline_re]; exact hcc))

/-- **Right Cauchy integrals vanish.** If `f` is holomorphic on `Re z ≥ c > Re ζ`, `c > 0`, and
`‖f z‖ ≤ K ‖(z (z - ζ))⁻¹‖` there, then `∫ f(c + i y) dy = 0`. -/
theorem integral_vline_eq_zero_of_right {f : ℂ → ℂ} {c K : ℝ} {ζ : ℂ} (hc : 0 < c)
    (hζ : ζ.re < c) (hK : 0 ≤ K) (hd : ∀ z : ℂ, c ≤ z.re → DifferentiableAt ℂ f z)
    (hb : ∀ z : ℂ, c ≤ z.re → ‖f z‖ ≤ K * ‖(z * (z - ζ))⁻¹‖) :
    ∫ y : ℝ, f (c + y * I) = 0 := by
  have hshift : ∀ c' : ℝ, c ≤ c' →
      ∫ y : ℝ, f (c + y * I) = ∫ y : ℝ, f (c' + y * I) := by
    intro c' hcc
    have hedge : ∀ T : ℝ, ‖ζ‖ + 1 ≤ |T| →
        ‖∫ σ in c..c', f (σ + T * I)‖ ≤ K * (1 / (|T| * (|T| - ‖ζ‖))) * |c' - c| := by
      intro T hT
      refine intervalIntegral.norm_integral_le_of_norm_le_const fun σ hσ => ?_
      rw [uIoc_of_le hcc] at hσ
      have hT0 : 0 < |T| := by linarith [norm_nonneg ζ]
      have h1 : |T| ≤ ‖(σ : ℂ) + T * I‖ := by
        have := abs_im_le_norm ((σ : ℂ) + T * I); simpa using this
      have h2 : |T| - ‖ζ‖ ≤ ‖(σ : ℂ) + T * I - ζ‖ := by
        have := abs_im_le_norm ((σ : ℂ) + T * I - ζ)
        simp only [sub_im, add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im, mul_zero,
          mul_one, zero_add, add_zero] at this
        have h3 := abs_sub_abs_le_abs_sub T ζ.im
        have h4 := abs_im_le_norm ζ
        linarith
      have hσre : c ≤ ((σ : ℂ) + T * I).re := by simp; linarith [hσ.1]
      refine (hb _ hσre).trans (mul_le_mul_of_nonneg_left ?_ hK)
      rw [norm_inv, norm_mul]
      exact inv_anti₀ (by have : 0 < |T| - ‖ζ‖ := by linarith
                          positivity) (mul_le_mul h1 h2 (by linarith) (norm_nonneg _))
        |>.trans_eq (by rw [one_div])
    have hlim : ∀ (sgn : ℝ), sgn = 1 ∨ sgn = -1 →
        Tendsto (fun k : ℕ => ∫ σ in c..c', f (σ + ((sgn * ((k : ℝ) + ‖ζ‖ + 1) : ℝ) : ℂ) * I))
          atTop (𝓝 0) := by
      intro sgn hsgn
      have habs : ∀ k : ℕ, |sgn * ((k : ℝ) + ‖ζ‖ + 1)| = (k : ℝ) + ‖ζ‖ + 1 := by
        intro k
        have hp : (0 : ℝ) < k + ‖ζ‖ + 1 := by positivity
        rcases hsgn with h | h
        · rw [h, one_mul, abs_of_pos hp]
        · rw [h, neg_one_mul, abs_neg, abs_of_pos hp]
      refine squeeze_zero_norm (a := fun k : ℕ => K * (1 / ((k : ℝ) + 1)) * |c' - c|)
        (fun k => ?_) ?_
      · have h := hedge (sgn * ((k : ℝ) + ‖ζ‖ + 1)) (by
          rw [habs k]; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
        rw [habs k] at h
        refine h.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hK)
          (abs_nonneg _))
        apply one_div_le_one_div_of_le (by positivity)
        have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        nlinarith [norm_nonneg ζ]
      · have h1 := ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul K).mul_const
          |c' - c|
        simpa using h1
    have hT : Tendsto (fun k : ℕ => ((k : ℝ) + ‖ζ‖ + 1)) atTop atTop :=
      tendsto_atTop_add_const_right _ _ (tendsto_atTop_add_const_right _ _
        tendsto_natCast_atTop_atTop)
    refine integral_vertical_eq_of_tendsto (f := f) hcc ?_ ?_ ?_ ?_ hT hT ?_ ?_
    · exact fun z hz => (hd z hz.1).continuousAt.continuousWithinAt
    · exact fun z hz => hd z hz.1.le
    · exact integrable_vline_of_right hc hζ hd hb le_rfl
    · exact integrable_vline_of_right hc hζ hd hb hcc
    · have h := hlim 1 (Or.inl rfl)
      simp only [one_mul] at h
      exact h
    · have h := hlim (-1) (Or.inr rfl)
      simp only [neg_one_mul, ofReal_neg] at h
      refine h.congr fun k => ?_
      push_cast
      ring_nf
  have hbound : ∀ c' : ℝ, c ≤ c' →
      ‖∫ y : ℝ, f (c + y * I)‖ ≤ K * (Real.pi / c' + Real.pi / (c' - ζ.re)) := by
    intro c' hcc
    rw [hshift c' hcc]
    have hc' : 0 < c' := by linarith
    have hζ' : ζ.re < c' := by linarith
    obtain ⟨h1, e1⟩ := integral_inv_sq_add_sq (d := c') hc' 0
    obtain ⟨h2, e2⟩ := integral_inv_sq_add_sq (d := c' - ζ.re) (by linarith) ζ.im
    refine (norm_integral_le_of_norm_le ((h1.add h2).const_mul K)
      (Eventually.of_forall fun y => ?_)).trans (le_of_eq ?_)
    · refine (hb _ (by rw [vline_re]; exact hcc)).trans ?_
      exact mul_le_mul_of_nonneg_left (norm_inv_mul_line_le hc' hζ' y) hK
    · rw [integral_const_mul]
      simp only [Pi.add_apply]
      rw [integral_add h1 h2, e1, e2]
  have hlim0 : Tendsto (fun n : ℕ => K * (Real.pi / (c + n) + Real.pi / (c + n - ζ.re)))
      atTop (𝓝 0) := by
    have t1 : Tendsto (fun n : ℕ => c + (n : ℝ)) atTop atTop :=
      tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop
    have t2 : Tendsto (fun n : ℕ => c + (n : ℝ) - ζ.re) atTop atTop :=
      tendsto_atTop_add_const_right _ _ t1
    have := ((t1.const_div_atTop Real.pi).add (t2.const_div_atTop Real.pi)).const_mul K
    simpa using this
  have hle : ∀ n : ℕ, ‖∫ y : ℝ, f (c + y * I)‖ ≤
      K * (Real.pi / (c + n) + Real.pi / (c + n - ζ.re)) := fun n =>
    hbound (c + n) (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  have h0 : ‖∫ y : ℝ, f (c + y * I)‖ ≤ 0 := ge_of_tendsto' hlim0 hle
  exact norm_le_zero_iff.mp h0

/-! ### The quotient `w = D₀/s²` -/

/-- `‖(s - a)(s - b)/s² - 1‖ ≤ (9c/16)/‖s‖` for `‖a‖, ‖b‖ ≤ c/4 ≤ ‖s‖/4`. -/
theorem norm_quad_div_sq_sub_one_le {a b s : ℂ} {c : ℝ} (hc : 0 < c) (ha : ‖a‖ ≤ c / 4)
    (hb : ‖b‖ ≤ c / 4) (hs : c ≤ ‖s‖) :
    ‖(s - a) * (s - b) / s ^ 2 - 1‖ ≤ 9 * c / 16 / ‖s‖ := by
  have hs0 : s ≠ 0 := by intro h; rw [h, norm_zero] at hs; linarith
  have hsn : 0 < ‖s‖ := norm_pos_iff.mpr hs0
  have e : (s - a) * (s - b) / s ^ 2 - 1 = -(a + b) / s + a * b / s ^ 2 := by
    field_simp; ring
  rw [e]
  calc ‖-(a + b) / s + a * b / s ^ 2‖ ≤ ‖-(a + b) / s‖ + ‖a * b / s ^ 2‖ := norm_add_le _ _
    _ ≤ (c / 2) / ‖s‖ + (c / 4 * (c / 4)) / ‖s‖ ^ 2 := by
        gcongr
        · rw [norm_div, norm_neg]
          gcongr
          exact (norm_add_le a b).trans (by linarith)
        · rw [norm_div, norm_mul, norm_pow]
          gcongr
    _ ≤ (c / 2) / ‖s‖ + (c / 16) / ‖s‖ := by
        have h2 : c / 4 * (c / 4) / ‖s‖ ^ 2 ≤ c / 16 / ‖s‖ := by
          rw [div_le_div_iff₀ (by positivity) hsn]
          nlinarith [mul_nonneg (mul_nonneg hc.le hsn.le) (sub_nonneg.mpr hs)]
        linarith
    _ = 9 * c / 16 / ‖s‖ := by ring

/-- With `‖w - 1‖ ≤ 9/16`: `w` is in the right half-plane and `‖log w‖ ≤ 2 ‖w - 1‖`. -/
theorem quad_quot_facts {w : ℂ} (hw : ‖w - 1‖ ≤ 9 / 16) :
    0 < w.re ∧ ‖Complex.log w‖ ≤ 2 * ‖w - 1‖ := by
  constructor
  · have := neg_abs_le (w - 1).re
    have h2 := abs_re_le_norm (w - 1)
    simp only [sub_re, one_re] at this h2
    linarith
  · have h := Complex.norm_log_one_add_le (z := w - 1) (by linarith)
    rw [add_sub_cancel] at h
    refine h.trans ?_
    have hn := norm_nonneg (w - 1)
    have hinv : (1 - ‖w - 1‖)⁻¹ ≤ 16 / 7 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    have : ‖w - 1‖ ^ 2 * (1 - ‖w - 1‖)⁻¹ / 2 ≤ ‖w - 1‖ := by
      calc ‖w - 1‖ ^ 2 * (1 - ‖w - 1‖)⁻¹ / 2 ≤ ‖w - 1‖ ^ 2 * (16 / 7) / 2 := by gcongr
        _ ≤ ‖w - 1‖ := by nlinarith
    linarith

/-- Principal logarithms add for two factors in the right half-plane, and the product stays in
the slit plane. -/
theorem log_mul_of_re_pos {x y : ℂ} (hx : 0 < x.re) (hy : 0 < y.re) :
    Complex.log (x * y) = Complex.log x + Complex.log y ∧ x * y ∈ slitPlane := by
  have hx0 : x ≠ 0 := by intro h; rw [h, zero_re] at hx; exact lt_irrefl _ hx
  have hy0 : y ≠ 0 := by intro h; rw [h, zero_re] at hy; exact lt_irrefl _ hy
  have ax := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hx)
  have ay := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hy)
  have hmem : arg x + arg y ∈ Ioc (-Real.pi) Real.pi := by
    rw [abs_lt] at ax ay
    constructor <;> linarith
  refine ⟨Complex.log_mul hx0 hy0 hmem, ?_⟩
  rw [mem_slitPlane_iff_arg]
  refine ⟨?_, mul_ne_zero hx0 hy0⟩
  rw [(Complex.arg_mul_eq_add_arg_iff hx0 hy0).mpr hmem]
  rw [abs_lt] at ax ay
  intro h
  linarith

/-! ### Removing the roots on the line `Re s = c₀` -/

namespace CepsCanonDomain

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v) (hθ : 0 < θ) (hD : 0 < D)

theorem cexp_mul_sub (t : ℝ) (q s : ℂ) : cexp (t * s - q) = cexp (-q) * cexp (t * s) := by
  rw [← Complex.exp_add]; ring_nf

include hW hθ hD in
/-- On the half-plane `Re s ≥ c₀`: `w = D₀/s²` is close to `1`. -/
theorem norm_quadQuot_sub_one_le {t : ℝ} (ht : |t| ≤ dom.μ₀) {q : ℂ} (hq : ‖q‖ ≤ dom.q₀)
    {s : ℂ} (hs : dom.c₀ ≤ s.re) :
    ‖cepsQuad D θ ρW t q s / s ^ 2 - 1‖ ≤ 9 * dom.c₀ / 16 / ‖s‖ := by
  have ht' : ‖(t : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  exact norm_quad_div_sq_sub_one_le dom.c₀_pos (dom.norm_rootPlus_le hW hθ hD ht' hq)
    (dom.norm_rootMinus_le hW hθ hD ht' hq) (hs.trans (re_le_norm s))

include hW hθ hD in
theorem quadQuot_facts {t : ℝ} (ht : |t| ≤ dom.μ₀) {q : ℂ} (hq : ‖q‖ ≤ dom.q₀)
    {s : ℂ} (hs : dom.c₀ ≤ s.re) :
    0 < (cepsQuad D θ ρW t q s / s ^ 2).re ∧
      ‖Complex.log (cepsQuad D θ ρW t q s / s ^ 2)‖ ≤ 9 * dom.c₀ / 8 / ‖s‖ := by
  have h1 := dom.norm_quadQuot_sub_one_le hW hθ hD ht hq hs
  have hsn : dom.c₀ ≤ ‖s‖ := hs.trans (re_le_norm s)
  have hc := dom.c₀_pos
  have h916 : 9 * dom.c₀ / 16 / ‖s‖ ≤ 9 / 16 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  obtain ⟨hre, hlog⟩ := quad_quot_facts (h1.trans h916)
  refine ⟨hre, hlog.trans ?_⟩
  have : 2 * (9 * dom.c₀ / 16 / ‖s‖) = 9 * dom.c₀ / 8 / ‖s‖ := by ring
  linarith

include hW hθ hD in
theorem differentiableAt_log_quadQuot {t : ℝ} (ht : |t| ≤ dom.μ₀) {q : ℂ} (hq : ‖q‖ ≤ dom.q₀)
    {s : ℂ} (hs : dom.c₀ ≤ s.re) :
    DifferentiableAt ℂ (fun z => Complex.log (cepsQuad D θ ρW t q z / z ^ 2)) s := by
  have hs0 : s ≠ 0 := by
    intro h; rw [h, zero_re] at hs; linarith [dom.c₀_pos]
  have hre := (dom.quadQuot_facts hW hθ hD ht hq hs).1
  refine DifferentiableAt.clog ?_ (Or.inl hre)
  unfold cepsQuad
  exact ((differentiableAt_id.sub_const _).mul (differentiableAt_id.sub_const _)).div
    (differentiableAt_id.pow 2) (pow_ne_zero 2 hs0)

include hW hθ hD in
/-- The Cauchy integral of `log(D₀/s²)` vanishes left of the line. -/
theorem integral_log_quadQuot_eq_zero {t : ℝ} (ht : |t| ≤ dom.μ₀) {q : ℂ} (hq : ‖q‖ ≤ dom.q₀)
    {ζ : ℂ} (hζ : ζ.re < dom.c₀) :
    ∫ y : ℝ, Complex.log (cepsQuad D θ ρW t q (dom.c₀ + y * I) / (dom.c₀ + y * I) ^ 2) /
      (dom.c₀ + y * I - ζ) = 0 := by
  have hc := dom.c₀_pos
  refine integral_vline_eq_zero_of_right (f := fun z =>
      Complex.log (cepsQuad D θ ρW t q z / z ^ 2) / (z - ζ)) (K := 9 * dom.c₀ / 8) hc hζ
    (by positivity) (fun z hz => ?_) (fun z hz => ?_)
  · have hzζ : z - ζ ≠ 0 := by
      intro h; have := congrArg re h; simp at this; linarith
    exact (dom.differentiableAt_log_quadQuot hW hθ hD ht hq hz).div
      (differentiableAt_id.sub_const ζ) hzζ
  · have hz0 : 0 < ‖z‖ := lt_of_lt_of_le hc (hz.trans (re_le_norm z))
    have hzζ : 0 < ‖z - ζ‖ := by
      have := re_le_norm (z - ζ); simp at this; linarith
    have hlog := (dom.quadQuot_facts hW hθ hD ht hq hz).2
    rw [norm_div, norm_inv, norm_mul]
    calc ‖Complex.log (cepsQuad D θ ρW t q z / z ^ 2)‖ / ‖z - ζ‖
        ≤ 9 * dom.c₀ / 8 / ‖z‖ / ‖z - ζ‖ := by gcongr
      _ = 9 * dom.c₀ / 8 * (‖z‖ * ‖z - ζ‖)⁻¹ := by field_simp

include hW hθ hD in
theorem integrable_log_quadQuot {t : ℝ} (ht : |t| ≤ dom.μ₀) {q : ℂ} (hq : ‖q‖ ≤ dom.q₀)
    {ζ : ℂ} (hζ : ζ.re < dom.c₀) :
    Integrable fun y : ℝ => Complex.log (cepsQuad D θ ρW t q (dom.c₀ + y * I) /
      (dom.c₀ + y * I) ^ 2) / (dom.c₀ + y * I - ζ) := by
  have hc := dom.c₀_pos
  refine integrable_vline_of_right (f := fun z =>
      Complex.log (cepsQuad D θ ρW t q z / z ^ 2) / (z - ζ)) (K := 9 * dom.c₀ / 8) hc hζ
    (fun z hz => ?_) (fun z hz => ?_) le_rfl
  · have hzζ : z - ζ ≠ 0 := by
      intro h; have := congrArg re h; simp at this; linarith
    exact (dom.differentiableAt_log_quadQuot hW hθ hD ht hq hz).div
      (differentiableAt_id.sub_const ζ) hzζ
  · have hz0 : 0 < ‖z‖ := lt_of_lt_of_le hc (hz.trans (re_le_norm z))
    have hzζ : 0 < ‖z - ζ‖ := by
      have := re_le_norm (z - ζ); simp at this; linarith
    have hlog := (dom.quadQuot_facts hW hθ hD ht hq hz).2
    rw [norm_div, norm_inv, norm_mul]
    calc ‖Complex.log (cepsQuad D θ ρW t q z / z ^ 2)‖ / ‖z - ζ‖
        ≤ 9 * dom.c₀ / 8 / ‖z‖ / ‖z - ζ‖ := by gcongr
      _ = 9 * dom.c₀ / 8 * (‖z‖ * ‖z - ζ‖)⁻¹ := by field_simp

include hW hθ hD in
/-- On the line: `F̃ = F · (D₀/s²)` and the principal logarithms add. -/
theorem log_cepsJetF_eq {t : ℝ} (ht : |t| ≤ dom.μ₀) {q : ℂ} (hq : ‖q‖ ≤ dom.q₀) (y : ℝ) :
    Complex.log (cepsJetF (dom.c₀ + y * I) (cexp (t * (dom.c₀ + y * I) - q) *
        stepTransform ρW (dom.c₀ + y * I))) =
      Complex.log (cepsF D θ ρW ((1 : ℝ) : ℂ) t q (dom.c₀ + y * I)) +
        Complex.log (cepsQuad D θ ρW t q (dom.c₀ + y * I) / (dom.c₀ + y * I) ^ 2) ∧
    cepsJetF (dom.c₀ + y * I) (cexp (t * (dom.c₀ + y * I) - q) *
        stepTransform ρW (dom.c₀ + y * I)) ∈ slitPlane := by
  set s : ℂ := dom.c₀ + y * I with hs
  have hc := dom.c₀_pos
  have hsre : s.re = dom.c₀ := by rw [hs]; simp
  have hs0 : s ≠ 0 := by intro h; rw [h, zero_re] at hsre; linarith
  have ht' : ‖(t : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  have hsn : dom.c₀ / 2 ≤ ‖s‖ := by linarith [re_le_norm s]
  have hQ0 := dom.cepsQuad_ne_zero hW hθ hD ht' hq hsn
  obtain ⟨hF, -⟩ := dom.re_cepsF_ge hW hθ hD (γ := 1) (by norm_num) le_rfl ht'
    (by simp [dom.η_pos.le]) hq (by rw [hsre, abs_of_pos hc]) (by rw [hsre, abs_of_pos hc]; linarith)
  have hFre : 0 < (cepsF D θ ρW ((1 : ℝ) : ℂ) t q s).re :=
    lt_of_lt_of_le (dom.d₀_pos hD) hF
  have hwre := (dom.quadQuot_facts hW hθ hD ht hq hsre.ge).1
  have hprod : cepsJetF s (cexp (t * s - q) * stepTransform ρW s) =
      cepsF D θ ρW ((1 : ℝ) : ℂ) t q s * (cepsQuad D θ ρW t q s / s ^ 2) := by
    rw [cepsJetF, cepsF, cepsD, cexp_mul_sub]
    field_simp
    push_cast
    ring
  rw [hprod]
  exact log_mul_of_re_pos hFre hwre

include hW hθ hD in
/-- **Root removal.** The canonical factor equals the root-free factor on its own line. -/
theorem canonL_eq_cepsRootFreeL {t : ℝ} (ht : |t| ≤ dom.μ₀) {q : ℂ} (hq : ‖q‖ ≤ dom.q₀)
    {ζ : ℂ} (hζ : ζ.re < dom.c₀) :
    dom.canonL ρW t q ζ = cepsRootFreeL dom.c₀ (stepTransform ρW) t q ζ := by
  have ht' : ‖(t : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  have hc := dom.c₀_pos
  have hI1 := dom.integrable_cepsCanonL_integrand hW hθ hD (γ := 1) (by norm_num) le_rfl
    le_rfl (by linarith) ht' (by simp) hq hζ
  have hI2 := dom.integrable_log_quadQuot hW hθ hD ht hq hζ
  have hsplit : (fun y : ℝ => Complex.log (cepsJetF (dom.c₀ + y * I)
      (cexp (t * (dom.c₀ + y * I) - q) * stepTransform ρW (dom.c₀ + y * I))) /
        (dom.c₀ + y * I - ζ)) = fun y : ℝ => cepsLineIntegrand D θ ρW 1 dom.c₀ t q ζ y +
      Complex.log (cepsQuad D θ ρW t q (dom.c₀ + y * I) / (dom.c₀ + y * I) ^ 2) /
        (dom.c₀ + y * I - ζ) := by
    funext y
    rw [(dom.log_cepsJetF_eq hW hθ hD ht hq y).1, cepsLineIntegrand, add_div]
  rw [canonL, cepsCanonL_eq, cepsRootFreeL, hsplit, integral_add hI1 hI2,
    dom.integral_log_quadQuot_eq_zero hW hθ hD ht hq hζ, add_zero, ofReal_one]

end CepsCanonDomain

end PGM
