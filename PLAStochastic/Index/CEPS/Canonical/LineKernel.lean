import PLAStochastic.ForMathlib.Probability.RandomWalk.WienerHopf.LineShift
import PLAStochastic.ForMathlib.Probability.RandomWalk.WienerHopf.LineInversion

/-!
# CEPS WP3: a vanishing line integral

For `c > 0` and `Re ζ < c`, `∫_ℝ ((c + i y)(c + i y - ζ))⁻¹ dy = 0`
(`integral_inv_mul_line_eq_zero`): both poles lie left of the line, the integrand is `O(|s|⁻²)`;
shifting the line to `Re s = c'` (horizontal edges vanish) and letting `c' → ∞` gives `0`.
This is the identity `∫ ds/(s (s - ζ)) = 0` used for the transport identity C-4.
-/

noncomputable section

open MeasureTheory Set Complex Filter Topology
open PGM.WienerHopf

namespace PGM

theorem norm_line_sub_sq' (c y : ℝ) (ζ : ℂ) :
    ‖(c : ℂ) + y * I - ζ‖ ^ 2 = (y - ζ.im) ^ 2 + (c - ζ.re) ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [sub_re, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, sub_im, add_im, mul_im]
  ring

theorem norm_line_sq' (c y : ℝ) : ‖(c : ℂ) + y * I‖ ^ 2 = (y - 0) ^ 2 + c ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, add_im, mul_im]
  ring

/-- Pointwise bound `‖(s (s - ζ))⁻¹‖ ≤ |s|⁻² + |s - ζ|⁻²` on the line. -/
theorem norm_inv_mul_line_le {c : ℝ} {ζ : ℂ} (hc : 0 < c) (hζ : ζ.re < c) (y : ℝ) :
    ‖(((c : ℂ) + y * I) * ((c : ℂ) + y * I - ζ))⁻¹‖ ≤
      ((y - 0) ^ 2 + c ^ 2)⁻¹ + ((y - ζ.im) ^ 2 + (c - ζ.re) ^ 2)⁻¹ := by
  have h1 := norm_line_sq' c y
  have h2 := norm_line_sub_sq' c y ζ
  have ha : 0 < ‖(c : ℂ) + y * I‖ := by
    have := re_le_norm ((c : ℂ) + y * I); simp at this; linarith
  have hb : 0 < ‖(c : ℂ) + y * I - ζ‖ := by
    have := re_le_norm ((c : ℂ) + y * I - ζ); simp at this; linarith
  rw [norm_inv, norm_mul, ← h1, ← h2]
  set a := ‖(c : ℂ) + y * I‖
  set b := ‖(c : ℂ) + y * I - ζ‖
  rw [inv_le_iff_one_le_mul₀' (by positivity)]
  have : (a ^ 2)⁻¹ + (b ^ 2)⁻¹ = (a ^ 2 + b ^ 2) / (a ^ 2 * b ^ 2) := by field_simp; ring
  rw [this, show a * b * ((a ^ 2 + b ^ 2) / (a ^ 2 * b ^ 2)) = (a ^ 2 + b ^ 2) / (a * b) by
    field_simp]
  rw [le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (a - b)]

theorem integrable_inv_mul_line {c : ℝ} {ζ : ℂ} (hc : 0 < c) (hζ : ζ.re < c) :
    Integrable fun y : ℝ => (((c : ℂ) + y * I) * ((c : ℂ) + y * I - ζ))⁻¹ := by
  obtain ⟨h1, -⟩ := integral_inv_sq_add_sq (d := c) hc 0
  obtain ⟨h2, -⟩ := integral_inv_sq_add_sq (d := c - ζ.re) (by linarith) ζ.im
  refine (h1.add h2).mono' ?_ (Eventually.of_forall fun y => ?_)
  · exact Continuous.aestronglyMeasurable (by
      refine Continuous.inv₀ (by fun_prop) fun y h0 => ?_
      rcases mul_eq_zero.mp h0 with h | h
      · have := congrArg re h; simp at this; linarith
      · have := congrArg re h; simp at this; linarith)
  · exact norm_inv_mul_line_le hc hζ y

theorem norm_integral_inv_mul_line_le {c : ℝ} {ζ : ℂ} (hc : 0 < c) (hζ : ζ.re < c) :
    ‖∫ y : ℝ, (((c : ℂ) + y * I) * ((c : ℂ) + y * I - ζ))⁻¹‖ ≤
      Real.pi / c + Real.pi / (c - ζ.re) := by
  obtain ⟨h1, e1⟩ := integral_inv_sq_add_sq (d := c) hc 0
  obtain ⟨h2, e2⟩ := integral_inv_sq_add_sq (d := c - ζ.re) (by linarith) ζ.im
  refine (norm_integral_le_of_norm_le (h1.add h2)
    (Eventually.of_forall fun y => norm_inv_mul_line_le hc hζ y)).trans (le_of_eq ?_)
  have := integral_add (f := fun t : ℝ => ((t - 0) ^ 2 + c ^ 2)⁻¹)
    (g := fun t : ℝ => ((t - ζ.im) ^ 2 + (c - ζ.re) ^ 2)⁻¹) h1 h2
  rw [e1, e2] at this
  exact this

/-- **`∫ ds/(s(s - ζ)) = 0`** along `Re s = c > Re ζ`, `c > 0`. -/
theorem integral_inv_mul_line_eq_zero {c : ℝ} {ζ : ℂ} (hc : 0 < c) (hζ : ζ.re < c) :
    ∫ y : ℝ, (((c : ℂ) + y * I) * ((c : ℂ) + y * I - ζ))⁻¹ = 0 := by
  set f : ℂ → ℂ := fun z => (z * (z - ζ))⁻¹ with hf
  -- the integral does not depend on the abscissa `c' ≥ c`
  have hshift : ∀ c' : ℝ, c ≤ c' →
      ∫ y : ℝ, f (c + y * I) = ∫ y : ℝ, f (c' + y * I) := by
    intro c' hcc
    have hne : ∀ z : ℂ, z.re ∈ Icc c c' → z * (z - ζ) ≠ 0 := by
      intro z hz h0
      rcases mul_eq_zero.mp h0 with h | h
      · have := congrArg re h; simp at this; linarith [hz.1]
      · have := congrArg re h; simp at this; linarith [hz.1]
    have hdiff : ∀ z : ℂ, z.re ∈ Icc c c' → DifferentiableAt ℂ f z := fun z hz =>
      (differentiableAt_id.mul (differentiableAt_id.sub_const ζ)).inv (hne z hz)
    -- horizontal edges
    have hedge : ∀ T : ℝ, ‖ζ‖ + 1 ≤ |T| →
        ‖∫ σ in c..c', f (σ + T * I)‖ ≤ 1 / (|T| * (|T| - ‖ζ‖)) * |c' - c| := by
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
      rw [hf, norm_inv, norm_mul]
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
      refine squeeze_zero_norm (a := fun k : ℕ => 1 / ((k : ℝ) + 1) * |c' - c|) (fun k => ?_) ?_
      · have h := hedge (sgn * ((k : ℝ) + ‖ζ‖ + 1)) (by
          rw [habs k]; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
        rw [habs k] at h
        refine h.trans (mul_le_mul_of_nonneg_right ?_ (abs_nonneg _))
        apply one_div_le_one_div_of_le (by positivity)
        have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        nlinarith [norm_nonneg ζ]
      · have h1 := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const |c' - c|
        simpa using h1
    have hT : Tendsto (fun k : ℕ => ((k : ℝ) + ‖ζ‖ + 1)) atTop atTop :=
      tendsto_atTop_add_const_right _ _ (tendsto_atTop_add_const_right _ _
        tendsto_natCast_atTop_atTop)
    refine integral_vertical_eq_of_tendsto (f := f) hcc ?_ ?_ ?_ ?_ hT hT ?_ ?_
    · exact fun z hz => (hdiff z hz).continuousAt.continuousWithinAt
    · exact fun z hz => hdiff z ⟨hz.1.le, hz.2.le⟩
    · exact integrable_inv_mul_line hc hζ
    · exact integrable_inv_mul_line (by linarith) (by linarith)
    · have h := hlim 1 (Or.inl rfl)
      simp only [one_mul] at h
      exact h
    · have h := hlim (-1) (Or.inr rfl)
      simp only [neg_one_mul, ofReal_neg] at h
      refine h.congr fun k => ?_
      push_cast
      ring_nf
  -- let the abscissa tend to infinity
  have hbound : ∀ c' : ℝ, c ≤ c' →
      ‖∫ y : ℝ, f (c + y * I)‖ ≤ Real.pi / c' + Real.pi / (c' - ζ.re) := by
    intro c' hcc
    rw [hshift c' hcc]
    exact norm_integral_inv_mul_line_le (by linarith) (by linarith)
  have hlim0 : Tendsto (fun n : ℕ => Real.pi / (c + n) + Real.pi / (c + n - ζ.re))
      atTop (𝓝 0) := by
    have t1 : Tendsto (fun n : ℕ => c + (n : ℝ)) atTop atTop :=
      tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop
    have t2 : Tendsto (fun n : ℕ => c + (n : ℝ) - ζ.re) atTop atTop :=
      tendsto_atTop_add_const_right _ _ t1
    have := (t1.const_div_atTop Real.pi).add (t2.const_div_atTop Real.pi)
    simpa using this
  have hle : ∀ n : ℕ, ‖∫ y : ℝ, f (c + y * I)‖ ≤
      Real.pi / (c + n) + Real.pi / (c + n - ζ.re) := fun n =>
    hbound (c + n) (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  have h0 : ‖∫ y : ℝ, f (c + y * I)‖ ≤ 0 := ge_of_tendsto' hlim0 hle
  exact norm_le_zero_iff.mp h0

end PGM
