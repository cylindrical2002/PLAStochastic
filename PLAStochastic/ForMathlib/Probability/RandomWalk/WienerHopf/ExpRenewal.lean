import PLAStochastic.ForMathlib.Probability.RandomWalk.WienerHopf.LineInversion
import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# The complex renewal theorem with an exponential remainder (blueprint W-5)

Let `g` be a complex density on `(0, ∞)` with `|g(x)| ≤ D e^{-θ x}`, `0 < c₀ < θ`,
`∫ e^{-c₀ x}|g| < 1`, and suppose its Laplace transform `A` factors on the strip `|Re ζ| ≤ c₀` as
`1 - A(ζ) = (β - ζ) e^{Λ(ζ)}` with `|β| ≤ c₀/4` and
`Re Λ(ζ) ≥ -K - log(1 + |ζ|)`. This normalized bound permits the logarithmic decay of the
actual ladder factor at large imaginary part. Then the renewal density
`u = ∑_{n ≥ 1} g^{*n}` satisfies

  `|u(x) - A'(β)⁻¹ e^{-β x}| ≤ K' e^{-c₀ x / 2}`  for `x > 0`  (`norm_renewalDensity_sub_le`),

with an explicit `K'` depending only on `(D, θ, c₀, K)`.

Proof: the tail `u - g` has transform `A²/(1 - A)` on `Re ζ = -c₀`. Subtracting the pole term
`R (e^{-β x} - e^{-2 c₀ x})` (`R = A'(β)⁻¹`) leaves the transform
`F = -dslope (A²/Q) β + R/(2c₀ - ζ)`, `Q = dslope A β`, holomorphic across `β`. Laplace inversion
on `Re ζ = -c₀` and the line shift to `Re ζ = c₀/2` (horizontal edges by the Plancherel bound
`∫∫ |A|² < ∞`) give the remainder bound.
-/

noncomputable section

open MeasureTheory Complex Filter Topology Set
open scoped ENNReal Real

namespace PGM.WienerHopf

/-- The hypotheses of the exponential renewal theorem. -/
structure ExpRenewalData (g : ℝ → ℂ) (D θ c₀ : ℝ) (β : ℂ) (Λ : ℂ → ℂ) (K : ℝ) : Prop where
  density : IsExpDensity g D θ
  c₀_pos : 0 < c₀
  c₀_lt : c₀ < θ
  mass_lt : ∫⁻ x, ENNReal.ofReal (Real.exp (-c₀ * x) * ‖g x‖) < 1
  root_le : ‖β‖ ≤ c₀ / 4
  factor : ∀ ζ : ℂ, |ζ.re| ≤ c₀ → 1 - laplaceC g ζ = (β - ζ) * cexp (Λ ζ)
  log_le : ∀ ζ : ℂ, |ζ.re| ≤ c₀ → -K - Real.log (1 + ‖ζ‖) ≤ (Λ ζ).re

/-- A uniform constant controlling the residue and the normalized factor on distant lines. -/
def renewalFactorBound (c₀ K : ℝ) : ℝ :=
  (1 + c₀) * (2 + 8 / c₀) * Real.exp K

/-- A bounded normalized logarithm implies the weaker real-part budget required by W-5. -/
theorem renewal_log_lower_of_norm_add_log {Λ : ℂ → ℂ} {K : ℝ} {ζ : ℂ}
    (hz : 1 - ζ ≠ 0) (hbound : ‖Λ ζ + Complex.log (1 - ζ)‖ ≤ K) :
    -K - Real.log (1 + ‖ζ‖) ≤ (Λ ζ).re := by
  have hlow : -K ≤ (Λ ζ + Complex.log (1 - ζ)).re := by
    have ha := (Complex.abs_re_le_norm (Λ ζ + Complex.log (1 - ζ))).trans hbound
    linarith [neg_abs_le (Λ ζ + Complex.log (1 - ζ)).re]
  have hn : ‖1 - ζ‖ ≤ 1 + ‖ζ‖ := by simpa using norm_sub_le (1 : ℂ) ζ
  have hlog := Real.log_le_log (norm_pos_iff.mpr hz) hn
  simp only [Complex.add_re, Complex.log_re] at hlow
  linarith

theorem isOpen_halfPlane {θ : ℝ} : IsOpen {z : ℂ | z.re < θ} :=
  isOpen_lt Complex.continuous_re continuous_const

/-! ### The pole-subtracted transform -/

/-- `P = A²/Q` with `Q = dslope A β`. -/
def renewalP (g : ℝ → ℂ) (β : ℂ) (ζ : ℂ) : ℂ := laplaceC g ζ ^ 2 / dslope (laplaceC g) β ζ

/-- The residue `R = Q(β)⁻¹ = A'(β)⁻¹`. -/
def renewalRes (g : ℝ → ℂ) (β : ℂ) : ℂ := (dslope (laplaceC g) β β)⁻¹

/-- `F = -dslope P β + R/(2c₀ - ζ)`, the transform of the remainder. -/
def renewalF (g : ℝ → ℂ) (β : ℂ) (c₀ : ℝ) (ζ : ℂ) : ℂ :=
  -dslope (renewalP g β) β ζ + renewalRes g β / (((2 * c₀ : ℝ) : ℂ) - ζ)

theorem renewalRes_eq (g : ℝ → ℂ) (β : ℂ) : renewalRes g β = (deriv (laplaceC g) β)⁻¹ := by
  rw [renewalRes, dslope_same]

theorem isOpen_strip (c₀ : ℝ) : IsOpen {z : ℂ | |z.re| < c₀} :=
  isOpen_lt (continuous_abs.comp Complex.continuous_re) continuous_const

/-- The pole term `R (e^{-β x} - e^{-2c₀ x})` for `x > 0` (and `0` for `x ≤ 0`). -/
def renewalPole (g : ℝ → ℂ) (β : ℂ) (c₀ : ℝ) (x : ℝ) : ℂ :=
  renewalRes g β * (cexp (-β * (max x 0 : ℝ)) - cexp (-((2 * c₀ : ℝ) : ℂ) * (max x 0 : ℝ)))

/-- The remainder `u - g - pole`. -/
def renewalRem (g : ℝ → ℂ) (β : ℂ) (c₀ : ℝ) (x : ℝ) : ℂ :=
  renewalTail g x - renewalPole g β c₀ x

theorem continuous_renewalPole (g : ℝ → ℂ) (β : ℂ) (c₀ : ℝ) :
    Continuous (renewalPole g β c₀) := by
  unfold renewalPole; fun_prop

theorem renewalPole_of_pos (g : ℝ → ℂ) (β : ℂ) (c₀ : ℝ) {x : ℝ} (hx : 0 < x) :
    renewalPole g β c₀ x =
      renewalRes g β * (cexp (-β * x) - cexp (-((2 * c₀ : ℝ) : ℂ) * x)) := by
  rw [renewalPole, max_eq_left hx.le]

theorem renewalPole_of_nonpos (g : ℝ → ℂ) (β : ℂ) (c₀ : ℝ) {x : ℝ} (hx : x ≤ 0) :
    renewalPole g β c₀ x = 0 := by
  rw [renewalPole, max_eq_right hx]; simp

namespace ExpRenewalData

variable {g : ℝ → ℂ} {D θ c₀ : ℝ} {β : ℂ} {Λ : ℂ → ℂ} {K : ℝ}
  (h : ExpRenewalData g D θ c₀ β Λ K)
include h

theorem θ_pos : 0 < θ := h.c₀_pos.trans h.c₀_lt

theorem abs_re_root_le : |β.re| ≤ c₀ / 4 := (Complex.abs_re_le_norm β).trans h.root_le

theorem abs_im_root_le : |β.im| ≤ c₀ / 4 := (Complex.abs_im_le_norm β).trans h.root_le

theorem root_mem : |β.re| ≤ c₀ := h.abs_re_root_le.trans (by linarith [h.c₀_pos])

theorem laplace_root : laplaceC g β = 1 := by
  have := h.factor β h.root_mem
  rw [sub_self, zero_mul, sub_eq_zero] at this
  exact this.symm

theorem differentiableOn_laplace : DifferentiableOn ℂ (laplaceC g) {z | z.re < θ} :=
  differentiableOn_laplaceC h.density


theorem mem_halfPlane_of_abs_le {z : ℂ} (hz : |z.re| ≤ c₀) : z ∈ {z : ℂ | z.re < θ} :=
  lt_of_le_of_lt (le_of_abs_le hz) h.c₀_lt

theorem differentiableAt_laplace {z : ℂ} (hz : |z.re| ≤ c₀) :
    DifferentiableAt ℂ (laplaceC g) z :=
  h.differentiableOn_laplace.differentiableAt ((isOpen_halfPlane (θ := θ)).mem_nhds (h.mem_halfPlane_of_abs_le hz))

/-- `1 - A(ζ) = (β - ζ) Q(ζ)` with `Q = dslope A β`. -/
theorem one_sub_laplace_eq (ζ : ℂ) :
    1 - laplaceC g ζ = (β - ζ) * dslope (laplaceC g) β ζ := by
  have h1 := sub_smul_dslope (laplaceC g) β ζ
  rw [smul_eq_mul, h.laplace_root] at h1
  linear_combination h1

theorem dslope_eq_exp {ζ : ℂ} (hζ : |ζ.re| ≤ c₀) (hne : ζ ≠ β) :
    dslope (laplaceC g) β ζ = cexp (Λ ζ) := by
  have h1 := h.one_sub_laplace_eq ζ
  rw [h.factor ζ hζ] at h1
  have hb : β - ζ ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  exact (mul_left_cancel₀ hb h1).symm

theorem continuousAt_dslope {ζ : ℂ} (hζ : |ζ.re| ≤ c₀) :
    ContinuousAt (dslope (laplaceC g) β) ζ := by
  rcases eq_or_ne ζ β with rfl | hne
  · exact continuousAt_dslope_same.mpr (h.differentiableAt_laplace hζ)
  · exact (continuousAt_dslope_of_ne hne).mpr (h.differentiableAt_laplace hζ).continuousAt

theorem factorBound_pos : 0 < renewalFactorBound c₀ K := by
  unfold renewalFactorBound
  have hc := h.c₀_pos
  exact mul_pos (mul_pos (by linarith [h.c₀_pos]) (by positivity)) (Real.exp_pos K)

theorem exp_neg_le_norm_dslope {ζ : ℂ} (hζ : |ζ.re| ≤ c₀) :
    Real.exp (-K) ≤ (1 + ‖ζ‖) * ‖dslope (laplaceC g) β ζ‖ := by
  have hoff : ∀ z : ℂ, |z.re| ≤ c₀ → z ≠ β →
      Real.exp (-K) ≤ (1 + ‖z‖) * ‖dslope (laplaceC g) β z‖ := by
    intro z hz hne
    rw [h.dslope_eq_exp hz hne, Complex.norm_exp]
    calc
      Real.exp (-K) = (1 + ‖z‖) * Real.exp (-K - Real.log (1 + ‖z‖)) := by
        rw [Real.exp_sub, Real.exp_log (by positivity)]
        field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (h.log_le z hz)) (by positivity)
  rcases eq_or_ne ζ β with rfl | hne
  · set z : ℕ → ℂ := fun n => ζ + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * (c₀ / 2 : ℝ)
    have hz : Tendsto z atTop (𝓝 ζ) := by
      have h0 : Tendsto (fun n : ℕ => ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * ((c₀ / 2 : ℝ) : ℂ)) atTop
          (𝓝 0) := by
        have := (Complex.continuous_ofReal.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
        simpa using this.mul_const ((c₀ / 2 : ℝ) : ℂ)
      simpa [z] using (tendsto_const_nhds (x := ζ)).add h0
    have hzre : ∀ n, |(z n).re| ≤ c₀ := by
      intro n
      have hpos : 0 < 1 / ((n : ℝ) + 1) := by positivity
      have hle : 1 / ((n : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
      simp only [z, add_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
      have h1 := h.abs_re_root_le
      have hc := h.c₀_pos
      rw [abs_le] at h1 ⊢
      constructor <;> nlinarith
    have hzne : ∀ n, z n ≠ ζ := by
      intro n hn
      have : ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * ((c₀ / 2 : ℝ) : ℂ) = 0 := by simpa [z] using hn
      rw [← Complex.ofReal_mul, Complex.ofReal_eq_zero] at this
      have hpos : 0 < 1 / ((n : ℝ) + 1) * (c₀ / 2) := mul_pos (by positivity) (by linarith [h.c₀_pos])
      linarith
    have hlim := ((tendsto_const_nhds (x := (1 : ℝ))).add hz.norm).mul
      ((h.continuousAt_dslope hζ).tendsto.comp hz).norm
    exact ge_of_tendsto hlim (Filter.Eventually.of_forall fun n => hoff (z n) (hzre n) (hzne n))
  · exact hoff ζ hζ hne

theorem dslope_ne_zero {ζ : ℂ} (hζ : |ζ.re| ≤ c₀) : dslope (laplaceC g) β ζ ≠ 0 := by
  intro h0
  have := h.exp_neg_le_norm_dslope hζ
  rw [h0, norm_zero, mul_zero] at this
  exact (Real.exp_pos _).not_ge this

/-- The normalized polynomial weight is harmless away from the root. -/
theorem weight_le_sub_root {ζ : ℂ} (hd : c₀ / 4 ≤ ‖β - ζ‖) :
    (1 + ‖ζ‖) * Real.exp K ≤ (2 + 8 / c₀) * Real.exp K * ‖β - ζ‖ := by
  have hc := h.c₀_pos
  have hb : ‖β‖ ≤ ‖β - ζ‖ := h.root_le.trans hd
  have hz : ‖ζ‖ ≤ ‖β - ζ‖ + ‖β‖ := by
    calc ‖ζ‖ = ‖β - (β - ζ)‖ := by congr 1; ring
      _ ≤ ‖β‖ + ‖β - ζ‖ := norm_sub_le _ _
      _ = _ := by ring
  have h1 : 1 ≤ 4 / c₀ * ‖β - ζ‖ := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hc]
    linarith
  have h2 : 4 / c₀ ≤ 8 / c₀ := by gcongr; norm_num
  have hw : 1 + ‖ζ‖ ≤ (2 + 8 / c₀) * ‖β - ζ‖ := by
    nlinarith [mul_le_mul_of_nonneg_right h2 (norm_nonneg (β - ζ))]
  nlinarith [mul_le_mul_of_nonneg_right hw (Real.exp_pos K).le]

theorem factorBound_ge : (2 + 8 / c₀) * Real.exp K ≤ renewalFactorBound c₀ K := by
  unfold renewalFactorBound
  have hc := h.c₀_pos
  have he : 0 < (2 + 8 / c₀) * Real.exp K := by positivity
  nlinarith

theorem factorBound_scaled_ge :
    (2 + 8 / c₀) * Real.exp K ≤ 4 * renewalFactorBound c₀ K / c₀ := by
  have hc := h.c₀_pos
  rw [le_div_iff₀ hc]
  unfold renewalFactorBound
  have he : 0 < (2 + 8 / c₀) * Real.exp K := by positivity
  nlinarith

theorem differentiableOn_dslope : DifferentiableOn ℂ (dslope (laplaceC g) β) {z | z.re < θ} :=
  (Complex.differentiableOn_dslope ((isOpen_halfPlane (θ := θ)).mem_nhds
    (h.mem_halfPlane_of_abs_le h.root_mem))).mpr h.differentiableOn_laplace

theorem norm_renewalRes_le : ‖renewalRes g β‖ ≤ renewalFactorBound c₀ K := by
  have hQ := h.dslope_ne_zero h.root_mem
  have hl := h.exp_neg_le_norm_dslope h.root_mem
  have hl' : 1 ≤ (1 + ‖β‖) * ‖dslope (laplaceC g) β β‖ * Real.exp K := by
    have := mul_le_mul_of_nonneg_right hl (Real.exp_pos K).le
    rwa [← Real.exp_add, neg_add_cancel, Real.exp_zero] at this
  rw [renewalRes, norm_inv, inv_le_iff_one_le_mul₀ (norm_pos_iff.mpr hQ)]
  have hC : (1 + ‖β‖) * Real.exp K ≤ renewalFactorBound c₀ K := by
    unfold renewalFactorBound
    have hc := h.c₀_pos
    have he := Real.exp_pos K
    have h8 : 0 ≤ 8 / c₀ := by positivity
    nlinarith [h.root_le, mul_nonneg hc.le h8, norm_nonneg β]
  nlinarith [mul_le_mul_of_nonneg_right hC (norm_nonneg (dslope (laplaceC g) β β))]

theorem renewalP_root : renewalP g β β = renewalRes g β := by
  rw [renewalP, renewalRes, h.laplace_root, one_pow, one_div]

theorem differentiableOn_renewalP : DifferentiableOn ℂ (renewalP g β) {z | |z.re| < c₀} := by
  have hsub : {z : ℂ | |z.re| < c₀} ⊆ {z | z.re < θ} := fun z hz =>
    h.mem_halfPlane_of_abs_le (le_of_lt hz)
  exact ((h.differentiableOn_laplace.mono hsub).pow 2).div (h.differentiableOn_dslope.mono hsub)
    fun z hz => h.dslope_ne_zero (le_of_lt hz)

theorem root_mem_strip : β ∈ {z : ℂ | |z.re| < c₀} :=
  lt_of_le_of_lt h.abs_re_root_le (by linarith [h.c₀_pos])

theorem differentiableOn_renewalF : DifferentiableOn ℂ (renewalF g β c₀) {z | |z.re| < c₀} := by
  have h1 : DifferentiableOn ℂ (dslope (renewalP g β) β) {z | |z.re| < c₀} :=
    (Complex.differentiableOn_dslope ((isOpen_strip c₀).mem_nhds h.root_mem_strip)).mpr
      h.differentiableOn_renewalP
  refine h1.neg.add (DifferentiableOn.div (differentiableOn_const _)
    ((differentiableOn_const _).sub differentiableOn_id) fun z hz => ?_)
  intro h0
  have : z.re = 2 * c₀ := by
    have := congrArg Complex.re (sub_eq_zero.mp h0)
    simpa using this.symm
  have hz' : |z.re| < c₀ := hz
  rw [this, abs_of_pos (by linarith [h.c₀_pos])] at hz'
  linarith [h.c₀_pos]

theorem continuousAt_renewalP {z : ℂ} (hz : |z.re| ≤ c₀) : ContinuousAt (renewalP g β) z :=
  ((h.differentiableAt_laplace hz).continuousAt.pow 2).div (h.continuousAt_dslope hz)
    (h.dslope_ne_zero hz)

theorem continuousAt_renewalF {z : ℂ} (hz : |z.re| ≤ c₀) (hz2 : z.re < 2 * c₀) :
    ContinuousAt (renewalF g β c₀) z := by
  have h1 : ContinuousAt (dslope (renewalP g β) β) z := by
    rcases eq_or_ne z β with rfl | hne
    · exact continuousAt_dslope_same.mpr (h.differentiableOn_renewalP.differentiableAt
        ((isOpen_strip c₀).mem_nhds h.root_mem_strip))
    · exact (continuousAt_dslope_of_ne hne).mpr (h.continuousAt_renewalP hz)
  refine h1.neg.add (continuousAt_const.div (continuousAt_const.sub continuousAt_id) ?_)
  intro h0
  have := congrArg Complex.re (sub_eq_zero.mp h0)
  simp only [ofReal_re] at this
  linarith

/-- Off the root, `F = A²/(1 - A) - R/(β - ζ) + R/(2c₀ - ζ)`. -/
theorem renewalF_eq {ζ : ℂ} (hζ : |ζ.re| ≤ c₀) (hne : ζ ≠ β) :
    renewalF g β c₀ ζ = laplaceC g ζ ^ 2 / (1 - laplaceC g ζ) - renewalRes g β / (β - ζ) +
      renewalRes g β / (((2 * c₀ : ℝ) : ℂ) - ζ) := by
  have hb : β - ζ ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have hzb : ζ - β ≠ 0 := sub_ne_zero.mpr hne
  have hQ := h.dslope_ne_zero hζ
  rw [renewalF, dslope_of_ne _ hne, slope_def_field, h.renewalP_root, h.one_sub_laplace_eq ζ,
    renewalP]
  field_simp
  ring

theorem norm_renewalF_le {ζ : ℂ} (hζ : |ζ.re| ≤ c₀) (hne : ζ ≠ β) :
    ‖renewalF g β c₀ ζ‖ ≤ ‖laplaceC g ζ‖ ^ 2 * (1 + ‖ζ‖) * Real.exp K / ‖β - ζ‖ +
      renewalFactorBound c₀ K * ‖((2 * c₀ : ℝ) : ℂ) - β‖ / (‖β - ζ‖ * ‖((2 * c₀ : ℝ) : ℂ) - ζ‖) := by
  have hBpos := h.factorBound_pos
  have hb : β - ζ ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have h2 : ((2 * c₀ : ℝ) : ℂ) - ζ ≠ 0 := by
    intro h0
    have := congrArg Complex.re (sub_eq_zero.mp h0)
    simp only [ofReal_re] at this
    have hc := h.c₀_pos
    rw [abs_le] at hζ
    linarith [hζ.2]
  have hQ := h.dslope_ne_zero hζ
  have hQn := h.exp_neg_le_norm_dslope hζ
  have hform : renewalF g β c₀ ζ = laplaceC g ζ ^ 2 / ((β - ζ) * dslope (laplaceC g) β ζ) -
      renewalRes g β * ((((2 * c₀ : ℝ) : ℂ) - β) / ((β - ζ) * (((2 * c₀ : ℝ) : ℂ) - ζ))) := by
    rw [h.renewalF_eq hζ hne, h.one_sub_laplace_eq ζ]
    field_simp
    ring
  rw [hform]
  refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_div, norm_mul, norm_pow, div_le_div_iff₀ (by positivity) (norm_pos_iff.mpr hb)]
    have hb0 : 0 < ‖β - ζ‖ := norm_pos_iff.mpr hb
    have hQe : 1 ≤ (1 + ‖ζ‖) * ‖dslope (laplaceC g) β ζ‖ * Real.exp K := by
      have := mul_le_mul_of_nonneg_right hQn (Real.exp_pos K).le
      rwa [← Real.exp_add, neg_add_cancel, Real.exp_zero] at this
    nlinarith [sq_nonneg ‖laplaceC g ζ‖, mul_nonneg (sq_nonneg ‖laplaceC g ζ‖) hb0.le]
  · rw [norm_mul, norm_div, norm_mul]
    calc ‖renewalRes g β‖ * (‖((2 * c₀ : ℝ) : ℂ) - β‖ / (‖β - ζ‖ * ‖((2 * c₀ : ℝ) : ℂ) - ζ‖))
        ≤ renewalFactorBound c₀ K * (‖((2 * c₀ : ℝ) : ℂ) - β‖ / (‖β - ζ‖ * ‖((2 * c₀ : ℝ) : ℂ) - ζ‖)) :=
          mul_le_mul_of_nonneg_right h.norm_renewalRes_le (by positivity)
      _ = _ := by ring

/-! ### The remainder on the left line -/

theorem integrable_weight_pole :
    Integrable fun x : ℝ => cexp ((-c₀ : ℂ) * x) * renewalPole g β c₀ x := by
  have hc := h.c₀_pos
  have hb := h.abs_re_root_le
  set M := ‖renewalRes g β‖
  have hI : IntegrableOn (fun x : ℝ => 2 * M * Real.exp (-(3 * c₀ / 4) * x)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (by linarith) 0).const_mul _
  refine (hI.integrable_indicator measurableSet_Ioi).mono'
    ((by fun_prop : Continuous fun x : ℝ => cexp ((-c₀ : ℂ) * x)).mul
      (continuous_renewalPole g β c₀)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ Ioi (0 : ℝ)
  · rw [indicator_of_mem hx, renewalPole_of_pos g β c₀ hx, norm_mul, norm_mul]
    have hx0 : 0 < x := hx
    rw [norm_cexp_mul_ofReal']
    have h1 : ‖cexp (-β * x)‖ ≤ Real.exp (c₀ / 4 * x) := by
      rw [norm_cexp_mul_ofReal', Real.exp_le_exp]
      rw [abs_le] at hb
      simp only [neg_re]; nlinarith
    have h2 : ‖cexp (-((2 * c₀ : ℝ) : ℂ) * x)‖ ≤ Real.exp (c₀ / 4 * x) := by
      rw [norm_cexp_mul_ofReal', Real.exp_le_exp]
      simp only [neg_re, ofReal_re]; nlinarith
    calc Real.exp (-(-(-c₀ : ℂ)).re * x) * (M * ‖cexp (-β * x) - cexp (-((2 * c₀ : ℝ) : ℂ) * x)‖)
        ≤ Real.exp (-c₀ * x) * (M * (Real.exp (c₀ / 4 * x) + Real.exp (c₀ / 4 * x))) := by
          have : (-(-(-c₀ : ℂ)).re) = -c₀ := by simp
          rw [this]
          gcongr
          exact (norm_sub_le _ _).trans (add_le_add h1 h2)
      _ = 2 * M * Real.exp (-(3 * c₀ / 4) * x) := by
          rw [show Real.exp (c₀ / 4 * x) + Real.exp (c₀ / 4 * x) = 2 * Real.exp (c₀ / 4 * x) by ring]
          rw [show Real.exp (-c₀ * x) * (M * (2 * Real.exp (c₀ / 4 * x))) =
            2 * M * (Real.exp (-c₀ * x) * Real.exp (c₀ / 4 * x)) by ring, ← Real.exp_add]
          congr 2; ring
  · rw [indicator_of_notMem hx, renewalPole_of_nonpos g β c₀ (not_lt.mp hx), mul_zero, norm_zero]

omit h in
theorem laplaceC_pole {ζ : ℂ} (hζ : ζ.re < β.re) (hζ2 : ζ.re < 2 * c₀) :
    laplaceC (renewalPole g β c₀) ζ =
      renewalRes g β / (β - ζ) - renewalRes g β / (((2 * c₀ : ℝ) : ℂ) - ζ) := by
  have hne1 : ζ - β ≠ 0 := by
    intro h0; have := congrArg Complex.re h0; simp at this; linarith
  have hne2 : ζ - ((2 * c₀ : ℝ) : ℂ) ≠ 0 := by
    intro h0; have := congrArg Complex.re h0; simp at this; linarith
  have hi1 := integrableOn_exp_mul_complex_Ioi (a := ζ - β) (by simp; linarith) 0
  have hi2 := integrableOn_exp_mul_complex_Ioi (a := ζ - ((2 * c₀ : ℝ) : ℂ)) (by simp; linarith) 0
  have hsupp : laplaceC (renewalPole g β c₀) ζ =
      ∫ x in Ioi (0 : ℝ), renewalRes g β * (cexp ((ζ - β) * x) -
        cexp ((ζ - ((2 * c₀ : ℝ) : ℂ)) * x)) := by
    unfold laplaceC
    rw [← integral_indicator measurableSet_Ioi]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show cexp (ζ * x) * renewalPole g β c₀ x = _
    by_cases hx : x ∈ Ioi (0 : ℝ)
    · rw [indicator_of_mem hx, renewalPole_of_pos g β c₀ hx,
        show (ζ - β) * (x : ℂ) = ζ * x + -β * x by ring,
        show (ζ - ((2 * c₀ : ℝ) : ℂ)) * (x : ℂ) = ζ * x + -((2 * c₀ : ℝ) : ℂ) * x by ring,
        Complex.exp_add, Complex.exp_add]
      ring
    · rw [indicator_of_notMem hx, renewalPole_of_nonpos g β c₀ (not_lt.mp hx), mul_zero]
  rw [hsupp, integral_const_mul, integral_sub hi1 hi2, integral_exp_mul_complex_Ioi (by simp; linarith),
    integral_exp_mul_complex_Ioi (by simp; linarith)]
  simp only [ofReal_zero, mul_zero, Complex.exp_zero]
  have hne1' : β - ζ ≠ 0 := by intro h0; exact hne1 (by linear_combination -h0)
  have hne2' : ((2 * c₀ : ℝ) : ℂ) - ζ ≠ 0 := by intro h0; exact hne2 (by linear_combination -h0)
  field_simp
  ring

theorem mass_lt_left : ∫⁻ x, ENNReal.ofReal (Real.exp (-(-((-c₀ : ℂ)).re) * x) * ‖g x‖) < 1 := by
  have : -(-((-c₀ : ℂ)).re) = -c₀ := by simp
  rw [this]; exact h.mass_lt

theorem integrable_weight_rem :
    Integrable fun x : ℝ => (Real.exp (-c₀ * x) : ℂ) * renewalRem g β c₀ x := by
  have h1 := integrable_laplace_renewalTail h.density h.mass_lt_left
  have h2 := h.integrable_weight_pole
  refine (h1.sub h2).congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [renewalRem, Pi.sub_apply]
  rw [Complex.ofReal_exp, mul_sub]
  push_cast
  ring_nf

/-- On the left line the remainder has transform `F`. -/
theorem laplaceC_rem_left (t : ℝ) :
    laplaceC (renewalRem g β c₀) ((-c₀ : ℝ) + t * I) = renewalF g β c₀ ((-c₀ : ℝ) + t * I) := by
  set ζ : ℂ := (-c₀ : ℝ) + t * I
  have hζre : ζ.re = -c₀ := by simp [ζ]
  have hb := h.abs_re_root_le
  have hc := h.c₀_pos
  rw [abs_le] at hb
  have hne : ζ ≠ β := by
    intro h0; have := congrArg Complex.re h0; rw [hζre] at this; linarith
  have hζ : |ζ.re| ≤ c₀ := by rw [hζre, abs_neg, abs_of_pos hc]
  have hmass : ∫⁻ x, ENNReal.ofReal (Real.exp (-(-ζ.re) * x) * ‖g x‖) < 1 := by
    rw [hζre]; simpa using h.mass_lt
  have h1 := integrable_laplace_renewalTail h.density hmass
  have h2 : Integrable fun x : ℝ => cexp (ζ * x) * renewalPole g β c₀ x := by
    refine h.integrable_weight_pole.norm.mono' ((by fun_prop : Continuous fun x : ℝ =>
      cexp (ζ * x)).mul (continuous_renewalPole g β c₀)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => le_of_eq ?_)
    simp only [norm_mul, norm_cexp_mul_ofReal', hζre]
    simp
  have hsplit : laplaceC (renewalRem g β c₀) ζ =
      laplaceC (renewalTail g) ζ - laplaceC (renewalPole g β c₀) ζ := by
    unfold laplaceC renewalRem
    rw [← integral_sub h1 h2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    ring
  rw [hsplit, laplaceC_renewalTail h.density hmass,
    laplaceC_pole (g := g) (by rw [hζre]; linarith) (by rw [hζre]; linarith), h.renewalF_eq hζ hne]
  ring

/-! ### Integrability on vertical lines -/

theorem continuous_laplace_line {σ : ℝ} (hσ : σ < θ) :
    Continuous fun t : ℝ => laplaceC g (σ + t * I) :=
  h.differentiableOn_laplace.continuousOn.comp_continuous (by fun_prop)
    (fun t => by simp only [mem_ofPred_eq, add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im];
                 simpa using hσ)

theorem integrable_sq_laplace_line {σ : ℝ} (hσ : σ < θ) :
    Integrable (fun t : ℝ => ‖laplaceC g (σ + t * I)‖ ^ 2) ∧
      ∫ t : ℝ, ‖laplaceC g (σ + t * I)‖ ^ 2 ≤ π * D ^ 2 / (θ - σ) := by
  have hP := lintegral_norm_sq_laplaceC_le h.density hσ
  have hfin : ∫⁻ t : ℝ, ENNReal.ofReal (‖laplaceC g (σ + t * I)‖ ^ 2) < ⊤ :=
    lt_of_le_of_lt hP (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
  have hm : AEStronglyMeasurable (fun t : ℝ => ‖laplaceC g (σ + t * I)‖ ^ 2) volume :=
    ((h.continuous_laplace_line hσ).norm.pow 2).aestronglyMeasurable
  have hint : Integrable (fun t : ℝ => ‖laplaceC g (σ + t * I)‖ ^ 2) := by
    refine ⟨hm, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun _ => by positivity)]
    exact hfin
  refine ⟨hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun _ => by positivity) hm]
  have hθσ : 0 < θ - σ := by linarith
  calc (∫⁻ t : ℝ, ENNReal.ofReal (‖laplaceC g (σ + t * I)‖ ^ 2)).toReal
      ≤ (ENNReal.ofReal (2 * π) * ENNReal.ofReal (D ^ 2 / (2 * (θ - σ)))).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) hP
    _ = π * D ^ 2 / (θ - σ) := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
          ENNReal.toReal_ofReal (by positivity)]
        field_simp

omit h in
theorem norm_sub_root_ge {σ t : ℝ} : |β.re - σ| ≤ ‖β - ((σ : ℂ) + t * I)‖ := by
  have := Complex.abs_re_le_norm (β - ((σ : ℂ) + t * I))
  simpa using this

omit h in
theorem sq_norm_sub_eq (b : ℂ) (σ t : ℝ) :
    ‖b - ((σ : ℂ) + t * I)‖ ^ 2 = (t - b.im) ^ 2 + (b.re - σ) ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp; ring

/-- `F` is integrable on a vertical line at distance at least `c₀/4` from the root. -/
theorem integrable_renewalF_line {σ : ℝ} (hσ : |σ| ≤ c₀) (hd : c₀ / 4 ≤ |β.re - σ|) :
    Integrable (fun t : ℝ => renewalF g β c₀ (σ + t * I)) ∧
      ∫ t : ℝ, ‖renewalF g β c₀ (σ + t * I)‖ ≤
        4 * π * renewalFactorBound c₀ K * D ^ 2 / (c₀ * (θ - σ)) + 12 * π * renewalFactorBound c₀ K := by
  have hBpos := h.factorBound_pos
  have hc := h.c₀_pos
  have hσθ : σ < θ := lt_of_le_of_lt (le_of_abs_le hσ) h.c₀_lt
  have hσ2 : σ < 2 * c₀ := by linarith [le_of_abs_le hσ]
  have hd1 : 0 < |β.re - σ| := by linarith
  have hd2 : 0 < 2 * c₀ - σ := by linarith
  obtain ⟨hA2i, hA2⟩ := h.integrable_sq_laplace_line hσθ
  obtain ⟨hr1i, hr1⟩ := integral_inv_sq_add_sq hd1 β.im
  obtain ⟨hr2i, hr2⟩ := integral_inv_sq_add_sq hd2 0
  set B : ℝ → ℝ := fun t => 4 * renewalFactorBound c₀ K / c₀ * ‖laplaceC g (σ + t * I)‖ ^ 2 +
    3 * c₀ * renewalFactorBound c₀ K / 2 * (((t - β.im) ^ 2 + |β.re - σ| ^ 2)⁻¹ +
      ((t - 0) ^ 2 + (2 * c₀ - σ) ^ 2)⁻¹)
  have hr12 : Integrable fun t : ℝ => ((t - β.im) ^ 2 + |β.re - σ| ^ 2)⁻¹ +
      ((t - 0) ^ 2 + (2 * c₀ - σ) ^ 2)⁻¹ := hr1i.add hr2i
  have hBa : Integrable fun t : ℝ => 4 * renewalFactorBound c₀ K / c₀ * ‖laplaceC g (σ + t * I)‖ ^ 2 :=
    hA2i.const_mul _
  have hBb : Integrable fun t : ℝ => 3 * c₀ * renewalFactorBound c₀ K / 2 *
      (((t - β.im) ^ 2 + |β.re - σ| ^ 2)⁻¹ + ((t - 0) ^ 2 + (2 * c₀ - σ) ^ 2)⁻¹) :=
    hr12.const_mul _
  have hBi : Integrable B := hBa.add hBb
  have hcont : Continuous fun t : ℝ => renewalF g β c₀ (σ + t * I) := by
    refine continuous_iff_continuousAt.mpr fun t => ?_
    have hz : |((σ : ℂ) + t * I).re| ≤ c₀ := by simpa using hσ
    have hz2 : ((σ : ℂ) + t * I).re < 2 * c₀ := by simpa using hσ2
    exact ContinuousAt.comp (f := fun t : ℝ => (σ : ℂ) + t * I) (h.continuousAt_renewalF hz hz2)
      (by fun_prop)
  have hpt : ∀ t : ℝ, ‖renewalF g β c₀ (σ + t * I)‖ ≤ B t := by
    intro t
    set ζ : ℂ := (σ : ℂ) + t * I
    have hζ : |ζ.re| ≤ c₀ := by simpa [ζ] using hσ
    have hb1 : c₀ / 4 ≤ ‖β - ζ‖ := hd.trans norm_sub_root_ge
    have hb1' : 0 < ‖β - ζ‖ := by linarith
    have hne : ζ ≠ β := by
      intro h0; rw [h0, sub_self, norm_zero] at hb1'; exact lt_irrefl 0 hb1'
    have hb2 : 0 < ‖((2 * c₀ : ℝ) : ℂ) - ζ‖ := by
      have := norm_sub_root_ge (β := ((2 * c₀ : ℝ) : ℂ)) (σ := σ) (t := t)
      simp only [ofReal_re] at this
      rw [abs_of_pos hd2] at this; linarith
    have h2β : ‖((2 * c₀ : ℝ) : ℂ) - β‖ ≤ 3 * c₀ := by
      calc ‖((2 * c₀ : ℝ) : ℂ) - β‖ ≤ ‖((2 * c₀ : ℝ) : ℂ)‖ + ‖β‖ := norm_sub_le _ _
        _ ≤ 2 * c₀ + c₀ / 4 := by
            rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
            linarith [h.root_le]
        _ ≤ 3 * c₀ := by linarith
    have e1 : ‖β - ζ‖ ^ 2 = (t - β.im) ^ 2 + |β.re - σ| ^ 2 := by
      rw [sq_abs]; exact sq_norm_sub_eq β σ t
    have e2 : ‖((2 * c₀ : ℝ) : ℂ) - ζ‖ ^ 2 = (t - 0) ^ 2 + (2 * c₀ - σ) ^ 2 := by
      have := sq_norm_sub_eq ((2 * c₀ : ℝ) : ℂ) σ t
      simp only [ofReal_re, ofReal_im] at this
      rw [this]
    refine (h.norm_renewalF_le hζ hne).trans (add_le_add ?_ ?_)
    · rw [div_le_iff₀ hb1']
      have hw := h.weight_le_sub_root hb1
      have hb := mul_le_mul_of_nonneg_right h.factorBound_scaled_ge (norm_nonneg (β - ζ))
      calc ‖laplaceC g ζ‖ ^ 2 * (1 + ‖ζ‖) * Real.exp K
          = ‖laplaceC g ζ‖ ^ 2 * ((1 + ‖ζ‖) * Real.exp K) := by ring
        _ ≤ ‖laplaceC g ζ‖ ^ 2 * ((4 * renewalFactorBound c₀ K / c₀) * ‖β - ζ‖) :=
          mul_le_mul_of_nonneg_left (hw.trans hb) (sq_nonneg _)
        _ = _ := by ring
    · have hamgm : 1 / (‖β - ζ‖ * ‖((2 * c₀ : ℝ) : ℂ) - ζ‖) ≤
          (1 / ‖β - ζ‖ ^ 2 + 1 / ‖((2 * c₀ : ℝ) : ℂ) - ζ‖ ^ 2) / 2 := by
        rw [div_add_div _ _ (by positivity) (by positivity), div_div, div_le_div_iff₀
          (by positivity) (by positivity)]
        nlinarith [sq_nonneg (‖β - ζ‖ - ‖((2 * c₀ : ℝ) : ℂ) - ζ‖), hb1', hb2,
          mul_pos hb1' hb2]
      calc renewalFactorBound c₀ K * ‖((2 * c₀ : ℝ) : ℂ) - β‖ / (‖β - ζ‖ * ‖((2 * c₀ : ℝ) : ℂ) - ζ‖)
          = renewalFactorBound c₀ K * ‖((2 * c₀ : ℝ) : ℂ) - β‖ *
              (1 / (‖β - ζ‖ * ‖((2 * c₀ : ℝ) : ℂ) - ζ‖)) := by ring
        _ ≤ renewalFactorBound c₀ K * (3 * c₀) * ((1 / ‖β - ζ‖ ^ 2 + 1 / ‖((2 * c₀ : ℝ) : ℂ) - ζ‖ ^ 2) / 2) :=
            mul_le_mul (mul_le_mul_of_nonneg_left h2β h.factorBound_pos.le) hamgm
              (by positivity) (by positivity)
        _ = 3 * c₀ * renewalFactorBound c₀ K / 2 * (((t - β.im) ^ 2 + |β.re - σ| ^ 2)⁻¹ +
              ((t - 0) ^ 2 + (2 * c₀ - σ) ^ 2)⁻¹) := by
            rw [e1, e2]; ring
  have hFi : Integrable fun t : ℝ => renewalF g β c₀ (σ + t * I) :=
    hBi.mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall hpt)
  refine ⟨hFi, ?_⟩
  calc ∫ t : ℝ, ‖renewalF g β c₀ (σ + t * I)‖ ≤ ∫ t, B t := integral_mono hFi.norm hBi hpt
    _ = 4 * renewalFactorBound c₀ K / c₀ * (∫ t : ℝ, ‖laplaceC g (σ + t * I)‖ ^ 2) +
          3 * c₀ * renewalFactorBound c₀ K / 2 * (π / |β.re - σ| + π / (2 * c₀ - σ)) := by
        simp only [B]
        rw [integral_add hBa hBb, integral_const_mul, integral_const_mul, integral_add hr1i hr2i,
          hr1, hr2]
    _ ≤ 4 * renewalFactorBound c₀ K / c₀ * (π * D ^ 2 / (θ - σ)) +
          3 * c₀ * renewalFactorBound c₀ K / 2 * (4 * π / c₀ + 4 * π / c₀) := by
        have h1' : π / |β.re - σ| ≤ 4 * π / c₀ := by
          rw [div_le_div_iff₀ hd1 hc]; nlinarith [Real.pi_pos]
        have h2' : π / (2 * c₀ - σ) ≤ 4 * π / c₀ := by
          rw [div_le_div_iff₀ hd2 hc]; nlinarith [Real.pi_pos, le_of_abs_le hσ]
        exact add_le_add (mul_le_mul_of_nonneg_left hA2 (by positivity))
          (mul_le_mul_of_nonneg_left (add_le_add h1' h2') (by positivity))
    _ = 4 * π * renewalFactorBound c₀ K * D ^ 2 / (c₀ * (θ - σ)) + 12 * π * renewalFactorBound c₀ K := by
        field_simp; ring

/-! ### Horizontal edges -/

theorem continuous_laplace_clamp :
    Continuous fun p : ℝ × ℝ => laplaceC g ((max (-c₀) (min p.2 (c₀ / 2)) : ℝ) + p.1 * I) := by
  have hc := h.c₀_pos
  refine h.differentiableOn_laplace.continuousOn.comp_continuous (by fun_prop) fun p => ?_
  simp only [mem_ofPred_eq, add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, mul_zero,
    mul_one, sub_zero, add_zero]
  have : max (-c₀) (min p.2 (c₀ / 2)) ≤ c₀ / 2 := max_le (by linarith) (min_le_right _ _)
  linarith [h.c₀_lt]

theorem lintegral_edge_ne_top :
    ∫⁻ t : ℝ, ∫⁻ σ in Ioc (-c₀) (c₀ / 2), ENNReal.ofReal (‖laplaceC g (σ + t * I)‖ ^ 2) ≠ ⊤ := by
  have hc := h.c₀_pos
  set Φ : ℝ × ℝ → ℝ≥0∞ := fun p => {q : ℝ × ℝ | q.2 ∈ Ioc (-c₀) (c₀ / 2)}.indicator
    (fun q => ENNReal.ofReal (‖laplaceC g ((max (-c₀) (min q.2 (c₀ / 2)) : ℝ) + q.1 * I)‖ ^ 2)) p
  have hΦm : Measurable Φ :=
    (ENNReal.measurable_ofReal.comp ((h.continuous_laplace_clamp.norm.pow 2).measurable)).indicator
      (measurableSet_Ioc.preimage measurable_snd)
  have hclamp : ∀ σ ∈ Ioc (-c₀) (c₀ / 2), max (-c₀) (min σ (c₀ / 2)) = σ := fun σ hσ => by
    rw [min_eq_left hσ.2, max_eq_right hσ.1.le]
  have heq : ∀ t : ℝ, ∫⁻ σ in Ioc (-c₀) (c₀ / 2), ENNReal.ofReal (‖laplaceC g (σ + t * I)‖ ^ 2) =
      ∫⁻ σ, Φ (t, σ) := by
    intro t
    rw [← lintegral_indicator measurableSet_Ioc]
    refine lintegral_congr fun σ => ?_
    simp only [Φ, indicator_apply, mem_ofPred_eq]
    split_ifs with hσ
    · rw [hclamp σ hσ]
    · rfl
  simp_rw [heq]
  rw [lintegral_lintegral_swap (f := fun t σ => Φ (t, σ)) hΦm.aemeasurable]
  have hσbound : ∀ σ : ℝ, ∫⁻ t : ℝ, Φ (t, σ) ≤ (Ioc (-c₀) (c₀ / 2)).indicator
      (fun _ => ENNReal.ofReal (2 * π) * ENNReal.ofReal (D ^ 2 / (2 * (θ - c₀ / 2)))) σ := by
    intro σ
    by_cases hσ : σ ∈ Ioc (-c₀) (c₀ / 2)
    · rw [indicator_of_mem hσ]
      have hΦ : ∀ t, Φ (t, σ) = ENNReal.ofReal (‖laplaceC g (σ + t * I)‖ ^ 2) := by
        intro t; simp only [Φ, indicator_apply, mem_ofPred_eq, if_pos hσ, hclamp σ hσ]
      simp_rw [hΦ]
      have hσθ : σ < θ := lt_of_le_of_lt hσ.2 (by linarith [h.c₀_lt])
      refine (lintegral_norm_sq_laplaceC_le h.density hσθ).trans ?_
      gcongr
      · linarith [h.c₀_lt]
      · exact hσ.2
    · rw [indicator_of_notMem hσ]
      have : ∀ t, Φ (t, σ) = 0 := by
        intro t; simp only [Φ, indicator_apply, mem_ofPred_eq, if_neg hσ]
      simp [this]
  refine ne_top_of_le_ne_top ?_ (lintegral_mono hσbound)
  rw [lintegral_indicator measurableSet_Ioc, setLIntegral_const, Real.volume_Ioc]
  exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
    ENNReal.ofReal_ne_top

theorem norm_renewalF_edge_le {σ T : ℝ} (hσ : |σ| ≤ c₀) (hT : c₀ + 1 ≤ |T|) :
    ‖renewalF g β c₀ (σ + T * I)‖ ≤ renewalFactorBound c₀ K * ‖laplaceC g (σ + T * I)‖ ^ 2 +
      3 * c₀ * renewalFactorBound c₀ K / ((|T| - c₀ / 4) * |T|) := by
  have hBpos := h.factorBound_pos
  have hc := h.c₀_pos
  set ζ : ℂ := (σ : ℂ) + T * I
  have hζ : |ζ.re| ≤ c₀ := by simpa [ζ] using hσ
  have him := h.abs_im_root_le
  have hb1 : |T| - c₀ / 4 ≤ ‖β - ζ‖ := by
    have := Complex.abs_im_le_norm (β - ζ)
    have him' : (β - ζ).im = β.im - T := by simp [ζ]
    rw [him'] at this
    have h2 : |T| - |β.im| ≤ |β.im - T| := by
      have := abs_sub_abs_le_abs_sub T β.im; rw [abs_sub_comm] at this; exact this
    linarith
  have hb1' : 1 ≤ ‖β - ζ‖ := by linarith
  have hne : ζ ≠ β := by intro h0; rw [h0, sub_self, norm_zero] at hb1'; linarith
  have hb2 : |T| ≤ ‖((2 * c₀ : ℝ) : ℂ) - ζ‖ := by
    have := Complex.abs_im_le_norm (((2 * c₀ : ℝ) : ℂ) - ζ)
    simpa [ζ] using this
  have h2β : ‖((2 * c₀ : ℝ) : ℂ) - β‖ ≤ 3 * c₀ := by
    calc ‖((2 * c₀ : ℝ) : ℂ) - β‖ ≤ ‖((2 * c₀ : ℝ) : ℂ)‖ + ‖β‖ := norm_sub_le _ _
      _ ≤ 2 * c₀ + c₀ / 4 := by
          rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
          linarith [h.root_le]
      _ ≤ 3 * c₀ := by linarith
  have hTpos : 0 < |T| - c₀ / 4 := by linarith
  have hT0 : 0 < |T| := by linarith
  refine (h.norm_renewalF_le hζ hne).trans (add_le_add ?_ ?_)
  · rw [div_le_iff₀ (by linarith)]
    have hw := h.weight_le_sub_root (by linarith : c₀ / 4 ≤ ‖β - ζ‖)
    have hb := mul_le_mul_of_nonneg_right h.factorBound_ge (norm_nonneg (β - ζ))
    calc ‖laplaceC g ζ‖ ^ 2 * (1 + ‖ζ‖) * Real.exp K
        = ‖laplaceC g ζ‖ ^ 2 * ((1 + ‖ζ‖) * Real.exp K) := by ring
      _ ≤ ‖laplaceC g ζ‖ ^ 2 * (renewalFactorBound c₀ K * ‖β - ζ‖) :=
        mul_le_mul_of_nonneg_left (hw.trans hb) (sq_nonneg _)
      _ = _ := by ring
  · exact div_le_div₀ (by positivity) (by nlinarith [h.factorBound_pos]) (mul_pos hTpos hT0)
      (mul_le_mul hb1 hb2 hT0.le (by linarith))


/-! ### Assembly: inversion, line shift and the remainder bound -/

omit h in
theorem norm_cexp_line (σ t x : ℝ) : ‖cexp (-((σ : ℂ) + t * I) * x)‖ = Real.exp (-σ * x) := by
  rw [Complex.norm_exp]; congr 1; simp

omit h in
theorem integrable_line_mul {σ : ℝ} (hF : Integrable fun t : ℝ => renewalF g β c₀ (σ + t * I))
    (x : ℝ) : Integrable fun t : ℝ => cexp (-((σ : ℂ) + t * I) * x) * renewalF g β c₀ (σ + t * I) := by
  refine (hF.norm.const_mul (Real.exp (-σ * x))).mono'
    ((by fun_prop : Continuous fun t : ℝ => cexp (-((σ : ℂ) + t * I) * x)).aestronglyMeasurable.mul
      hF.aestronglyMeasurable) (Filter.Eventually.of_forall fun t => ?_)
  rw [norm_mul, norm_cexp_line]

omit h in
theorem norm_integral_line_le {σ : ℝ} (x : ℝ) :
    ‖∫ t : ℝ, cexp (-((σ : ℂ) + t * I) * x) * renewalF g β c₀ (σ + t * I)‖ ≤
      Real.exp (-σ * x) * ∫ t : ℝ, ‖renewalF g β c₀ (σ + t * I)‖ := by
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [norm_mul, norm_cexp_line]

/-- The horizontal edge integrals vanish along heights where the strip mass of `|A|²` does. -/
theorem tendsto_edge {x : ℝ} (hx : 0 ≤ x) {T : ℕ → ℝ} (hT : Tendsto (fun k => |T k|) atTop atTop)
    (hH : Tendsto (fun k => ∫⁻ σ in Ioc (-c₀) (c₀ / 2),
      ENNReal.ofReal (‖laplaceC g (σ + T k * I)‖ ^ 2)) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ σ in (-c₀)..(c₀ / 2),
      cexp (-((σ : ℂ) + T k * I) * x) * renewalF g β c₀ (σ + T k * I)) atTop (𝓝 0) := by
  have hBpos := h.factorBound_pos
  have hc := h.c₀_pos
  set H := fun k => ∫⁻ σ in Ioc (-c₀) (c₀ / 2), ENNReal.ofReal (‖laplaceC g (σ + T k * I)‖ ^ 2)
    with hHdef
  set C : ℕ → ℝ := fun k => 3 * c₀ * renewalFactorBound c₀ K / ((|T k| - c₀ / 4) * |T k|) with hCdef
  have hC : Tendsto C atTop (𝓝 0) := by
    have h1 : Tendsto (fun k => |T k| - c₀ / 4) atTop atTop := by
      simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-(c₀ / 4)) hT
    exact tendsto_const_nhds.div_atTop (h1.atTop_mul_atTop₀ hT)
  set E : ℕ → ℝ≥0∞ := fun k => ENNReal.ofReal (Real.exp (c₀ * x)) *
    (ENNReal.ofReal (renewalFactorBound c₀ K) * H k + ENNReal.ofReal (C k) * ENNReal.ofReal (c₀ / 2 - -c₀))
    with hEdef
  have hE : Tendsto E atTop (𝓝 0) := by
    have h1 : Tendsto (fun k => ENNReal.ofReal (renewalFactorBound c₀ K) * H k + ENNReal.ofReal (C k) *
        ENNReal.ofReal (c₀ / 2 - -c₀)) atTop (𝓝 (ENNReal.ofReal (renewalFactorBound c₀ K) * 0 +
        ENNReal.ofReal 0 * ENNReal.ofReal (c₀ / 2 - -c₀))) :=
      (ENNReal.Tendsto.const_mul hH (Or.inr ENNReal.ofReal_ne_top)).add
        (ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal hC) (Or.inr ENNReal.ofReal_ne_top))
    have h2 := ENNReal.Tendsto.const_mul h1
      (Or.inr (ENNReal.ofReal_ne_top (r := Real.exp (c₀ * x))))
    simp only [mul_zero, zero_mul, add_zero, ENNReal.ofReal_zero] at h2
    exact h2
  have hEr : Tendsto (fun k => (E k).toReal) atTop (𝓝 0) := by
    have h1 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hE
    rw [ENNReal.toReal_zero] at h1
    exact h1
  refine squeeze_zero_norm' ?_ hEr
  filter_upwards [hT.eventually_ge_atTop (c₀ + 1),
    hE.eventually (gt_mem_nhds (by simp : (0 : ℝ≥0∞) < ⊤))] with k hk hEk
  have hCk : 0 ≤ C k := div_nonneg (by positivity) (mul_nonneg (by linarith) (abs_nonneg _))
  rw [intervalIntegral.integral_of_le (by linarith)]
  refine (norm_integral_le_lintegral_norm _).trans (ENNReal.toReal_mono hEk.ne ?_)
  calc ∫⁻ σ in Ioc (-c₀) (c₀ / 2), ENNReal.ofReal ‖cexp (-((σ : ℂ) + T k * I) * x) *
        renewalF g β c₀ (σ + T k * I)‖
      ≤ ∫⁻ σ in Ioc (-c₀) (c₀ / 2), ENNReal.ofReal (Real.exp (c₀ * x)) *
        (ENNReal.ofReal (renewalFactorBound c₀ K) * ENNReal.ofReal (‖laplaceC g (σ + T k * I)‖ ^ 2) +
          ENNReal.ofReal (C k)) := by
        refine setLIntegral_mono' measurableSet_Ioc fun σ hσ => ?_
        have hσ' : |σ| ≤ c₀ := abs_le.mpr ⟨hσ.1.le, by linarith [hσ.2]⟩
        rw [← ENNReal.ofReal_mul h.factorBound_pos.le,
          ← ENNReal.ofReal_add (by positivity :
            (0 : ℝ) ≤ renewalFactorBound c₀ K * ‖laplaceC g (σ + T k * I)‖ ^ 2) hCk,
          ← ENNReal.ofReal_mul (Real.exp_pos (c₀ * x)).le]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [norm_mul, norm_cexp_line]
        have he : Real.exp (-σ * x) ≤ Real.exp (c₀ * x) :=
          Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by linarith [hσ.1]) hx)
        exact mul_le_mul he (h.norm_renewalF_edge_le hσ' hk) (norm_nonneg _) (Real.exp_pos _).le
    _ = E k := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_add_right _ measurable_const, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          setLIntegral_const, Real.volume_Ioc]

/-- The remainder is the inverse transform of `F` on the line `Re ζ = c₀/2`. -/
theorem renewalRem_eq_line {x : ℝ} (hx : 0 ≤ x) :
    renewalRem g β c₀ x = (1 / (2 * π) : ℂ) *
      ∫ t : ℝ, cexp (-(((c₀ / 2 : ℝ) : ℂ) + t * I) * x) *
        renewalF g β c₀ ((c₀ / 2 : ℝ) + t * I) := by
  have hc := h.c₀_pos
  have hb := h.abs_re_root_le
  rw [abs_le] at hb
  have hσL : |(-c₀)| ≤ c₀ := by rw [abs_neg, abs_of_pos hc]
  have hdL : c₀ / 4 ≤ |β.re - -c₀| := by rw [abs_of_pos (by linarith)]; linarith
  have hσR : |c₀ / 2| ≤ c₀ := by rw [abs_of_pos (by linarith)]; linarith
  have hdR : c₀ / 4 ≤ |β.re - c₀ / 2| := by rw [abs_of_neg (by linarith)]; linarith
  have hFL := (h.integrable_renewalF_line hσL hdL).1
  have hFR := (h.integrable_renewalF_line hσR hdR).1
  have hcont : Continuous (renewalRem g β c₀) :=
    (continuous_renewalTail h.density h.θ_pos).sub (continuous_renewalPole g β c₀)
  rw [laplace_inversion_line hcont h.integrable_weight_rem h.laplaceC_rem_left hFL x]
  congr 1
  obtain ⟨T, hT, hTH⟩ := exists_seq_tendsto_atTop_of_lintegral_ne_top h.lintegral_edge_ne_top
  have hneg : ∫⁻ t : ℝ, (∫⁻ σ in Ioc (-c₀) (c₀ / 2),
      ENNReal.ofReal (‖laplaceC g (σ + ((-t : ℝ) : ℂ) * I)‖ ^ 2)) ≠ ⊤ := by
    have := (Measure.measurePreserving_neg (volume : Measure ℝ)).lintegral_comp_emb
      (MeasurableEquiv.neg ℝ).measurableEmbedding
      (fun t : ℝ => ∫⁻ σ in Ioc (-c₀) (c₀ / 2), ENNReal.ofReal (‖laplaceC g (σ + t * I)‖ ^ 2))
    rw [this]
    exact h.lintegral_edge_ne_top
  obtain ⟨S, hS, hSH⟩ := exists_seq_tendsto_atTop_of_lintegral_ne_top hneg
  refine integral_vertical_eq_of_tendsto (f := fun z => cexp (-z * x) * renewalF g β c₀ z)
    (a := -c₀) (b := c₀ / 2) (by linarith) ?_ ?_ (integrable_line_mul hFL x)
    (integrable_line_mul hFR x) hT hS (h.tendsto_edge hx (tendsto_abs_atTop_atTop.comp hT) hTH)
    (h.tendsto_edge (T := fun k => -S k) hx
      (tendsto_abs_atBot_atTop.comp (tendsto_neg_atTop_atBot.comp hS)) hSH)
  · intro z hz
    have hz1 : -c₀ ≤ z.re := hz.1
    have hz2 : z.re ≤ c₀ / 2 := hz.2
    have hz' : |z.re| ≤ c₀ := abs_le.mpr ⟨hz1, by linarith⟩
    exact ((by fun_prop : Continuous fun z : ℂ => cexp (-z * x)).continuousAt.mul
      (h.continuousAt_renewalF hz' (by linarith))).continuousWithinAt
  · intro z hz
    have hz' : |z.re| < c₀ := abs_lt.mpr ⟨hz.1, by linarith [hz.2]⟩
    exact ((by fun_prop : Differentiable ℂ fun z : ℂ => cexp (-z * x)) z).mul
      (h.differentiableOn_renewalF.differentiableAt ((isOpen_strip c₀).mem_nhds hz'))

/-- The exponential bound on the remainder. -/
theorem norm_renewalRem_le {x : ℝ} (hx : 0 ≤ x) :
    ‖renewalRem g β c₀ x‖ ≤
      (2 * renewalFactorBound c₀ K * D ^ 2 / (c₀ * (θ - c₀ / 2)) + 6 * renewalFactorBound c₀ K) *
        Real.exp (-(c₀ / 2) * x) := by
  have hc := h.c₀_pos
  have hθ := h.c₀_lt
  have hb := h.abs_re_root_le
  rw [abs_le] at hb
  have hσR : |c₀ / 2| ≤ c₀ := by rw [abs_of_pos (by linarith)]; linarith
  have hdR : c₀ / 4 ≤ |β.re - c₀ / 2| := by rw [abs_of_neg (by linarith)]; linarith
  have hFRb := (h.integrable_renewalF_line hσR hdR).2
  rw [h.renewalRem_eq_line hx, norm_mul,
    show (1 / (2 * π) : ℂ) = ((1 / (2 * π) : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
    Real.norm_of_nonneg (by positivity)]
  calc 1 / (2 * π) * ‖∫ t : ℝ, cexp (-(((c₀ / 2 : ℝ) : ℂ) + t * I) * x) *
        renewalF g β c₀ ((c₀ / 2 : ℝ) + t * I)‖
      ≤ 1 / (2 * π) * (Real.exp (-(c₀ / 2) * x) *
        (4 * π * renewalFactorBound c₀ K * D ^ 2 / (c₀ * (θ - c₀ / 2)) + 12 * π * renewalFactorBound c₀ K)) := by
        gcongr
        exact (norm_integral_line_le x).trans
          (mul_le_mul_of_nonneg_left hFRb (Real.exp_pos _).le)
    _ = (2 * renewalFactorBound c₀ K * D ^ 2 / (c₀ * (θ - c₀ / 2)) + 6 * renewalFactorBound c₀ K) *
        Real.exp (-(c₀ / 2) * x) := by
        have : θ - c₀ / 2 ≠ 0 := by linarith
        field_simp
        ring

/-- **The complex renewal theorem with an exponential remainder (W-5).** For `x > 0`,
`|u(x) - A'(β)⁻¹ e^{-β x}| ≤ (D + 2 B D²/(c₀(θ - c₀/2)) + 7 B) e^{-c₀ x/2}`, where
`B = renewalFactorBound c₀ K`; here
`renewalRes g β = (deriv (laplaceC g) β)⁻¹` (`renewalRes_eq`). -/
theorem norm_renewalDensity_sub_le {x : ℝ} (hx : 0 < x) :
    ‖renewalDensity g x - renewalRes g β * cexp (-β * x)‖ ≤
      (D + 2 * renewalFactorBound c₀ K * D ^ 2 / (c₀ * (θ - c₀ / 2)) + 7 * renewalFactorBound c₀ K) *
        Real.exp (-(c₀ / 2) * x) := by
  have hBpos := h.factorBound_pos
  have hc := h.c₀_pos
  have hθ := h.c₀_lt
  have hD := h.density.nonneg_D
  have hdecomp : renewalDensity g x - renewalRes g β * cexp (-β * x) =
      g x + renewalRem g β c₀ x - renewalRes g β * cexp (-((2 * c₀ : ℝ) : ℂ) * x) := by
    rw [renewalDensity_eq_add_tail h.density, renewalRem, renewalPole_of_pos g β c₀ hx]; ring
  rw [hdecomp]
  have hg : ‖g x‖ ≤ D * Real.exp (-(c₀ / 2) * x) :=
    (h.density.norm_le x).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) hD)
  have hR : ‖renewalRes g β * cexp (-((2 * c₀ : ℝ) : ℂ) * x)‖ ≤
      renewalFactorBound c₀ K * Real.exp (-(c₀ / 2) * x) := by
    rw [norm_mul]
    refine mul_le_mul h.norm_renewalRes_le ?_ (norm_nonneg _) h.factorBound_pos.le
    rw [Complex.norm_exp]
    refine Real.exp_le_exp.mpr ?_
    simp only [neg_mul, neg_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
    nlinarith
  have hrem := h.norm_renewalRem_le hx.le
  calc ‖g x + renewalRem g β c₀ x - renewalRes g β * cexp (-((2 * c₀ : ℝ) : ℂ) * x)‖
      ≤ ‖g x‖ + ‖renewalRem g β c₀ x‖ +
          ‖renewalRes g β * cexp (-((2 * c₀ : ℝ) : ℂ) * x)‖ :=
        (norm_sub_le _ _).trans (by gcongr; exact norm_add_le _ _)
    _ ≤ (D + 2 * renewalFactorBound c₀ K * D ^ 2 / (c₀ * (θ - c₀ / 2)) + 7 * renewalFactorBound c₀ K) *
        Real.exp (-(c₀ / 2) * x) := by linarith

/-- If `Λ` is continuous at the root, the residue is `e^{-Λ(β)}`. -/
theorem renewalRes_eq_exp (hΛ : ContinuousAt Λ β) : renewalRes g β = cexp (-Λ β) := by
  have hQ : dslope (laplaceC g) β β = cexp (Λ β) := by
    have hev : dslope (laplaceC g) β =ᶠ[𝓝[≠] β] fun ζ => cexp (Λ ζ) := by
      have hmem : {z : ℂ | |z.re| < c₀} ∈ 𝓝 β := (isOpen_strip c₀).mem_nhds h.root_mem_strip
      filter_upwards [nhdsWithin_le_nhds hmem, self_mem_nhdsWithin] with ζ hζ hne
      exact h.dslope_eq_exp (le_of_lt hζ) hne
    have h1 : Tendsto (dslope (laplaceC g) β) (𝓝[≠] β) (𝓝 (dslope (laplaceC g) β β)) :=
      (h.continuousAt_dslope h.root_mem).tendsto.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto (fun ζ => cexp (Λ ζ)) (𝓝[≠] β) (𝓝 (cexp (Λ β))) :=
      ((Complex.continuous_exp.continuousAt).comp hΛ).tendsto.mono_left nhdsWithin_le_nhds
    exact tendsto_nhds_unique (h1.congr' hev) h2
  rw [renewalRes, hQ, ← Complex.exp_neg]

end ExpRenewalData


end PGM.WienerHopf
