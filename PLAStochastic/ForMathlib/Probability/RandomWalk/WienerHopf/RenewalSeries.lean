import PLAStochastic.ForMathlib.Probability.RandomWalk.WienerHopf.ConvPow
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-!
# The renewal series of a complex exponential density

For `IsExpDensity g D θ` (`θ > 0`) let `renewalTail g = ∑_{n ≥ 2} g^{*n} = u - g`.

* `measurable_renewalTail`, `continuous_renewalTail`: the tail is measurable and continuous
  (`g ⋆ g` is continuous by approximating `g` in `L¹` by compactly supported continuous
  functions; later powers are convolutions with bounded continuous functions).
* `integrable_laplace_renewalTail`, `laplaceC_renewalTail`: on a line `Re ζ = -c` where
  `a = ∫ e^{-c x}|g| < 1`, the weighted tail is integrable and its transform is `A²/(1 - A)`.
* `renewalDensity_eq_add_tail`: `u = g + renewalTail g`.
-/

noncomputable section

open MeasureTheory Complex Filter Topology Set
open scoped ENNReal Nat

namespace PGM.WienerHopf

variable {g : ℝ → ℂ} {D θ : ℝ}

/-- `∑_{n ≥ 2} g^{*n}`. -/
def renewalTail (g : ℝ → ℂ) (x : ℝ) : ℂ := ∑' n, convPow g (n + 1) x

theorem summable_convPow (hg : IsExpDensity g D θ) (x : ℝ) : Summable fun n => convPow g n x :=
  (summable_norm_convPow hg x).of_norm

theorem renewalDensity_eq_add_tail (hg : IsExpDensity g D θ) (x : ℝ) :
    renewalDensity g x = g x + renewalTail g x := by
  unfold renewalDensity renewalTail
  rw [(summable_convPow hg x).tsum_eq_zero_add]
  rfl

theorem measurable_renewalTail (hg : IsExpDensity g D θ) : Measurable (renewalTail g) := by
  refine measurable_of_tendsto_metrizable (f := fun N x => ∑ n ∈ Finset.range N, convPow g (n + 1) x)
    (fun N => Finset.measurable_sum _ fun n _ => measurable_convPow hg (n + 1)) ?_
  refine tendsto_pi_nhds.mpr fun x => ?_
  exact ((summable_nat_add_iff 1).mpr (summable_convPow hg x)).hasSum.tendsto_sum_nat

/-! ### Transform of the tail -/

theorem lintegral_weight_tail_term_le (hg : IsExpDensity g D θ) (c : ℝ) (n : ℕ) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (-c * x) * ‖convPow g (n + 1) x‖) ≤
      (∫⁻ x, ENNReal.ofReal (Real.exp (-c * x) * ‖g x‖)) ^ (n + 2) :=
  lintegral_weight_convPow_le hg c (n + 1)

/-- The weighted tail is integrable on a line where `∫ e^{-c x}|g| < 1`. -/
theorem integrable_laplace_renewalTail (hg : IsExpDensity g D θ) {ζ : ℂ}
    (ha : ∫⁻ x, ENNReal.ofReal (Real.exp (-(-ζ.re) * x) * ‖g x‖) < 1) :
    Integrable fun x : ℝ => cexp (ζ * x) * renewalTail g x := by
  set a := ∫⁻ x, ENNReal.ofReal (Real.exp (-(-ζ.re) * x) * ‖g x‖)
  refine ⟨((by fun_prop : Measurable fun x : ℝ => cexp (ζ * x)).mul
    (measurable_renewalTail hg)).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  calc ∫⁻ x : ℝ, ENNReal.ofReal ‖cexp (ζ * x) * renewalTail g x‖
      ≤ ∫⁻ x, ∑' n, ENNReal.ofReal (Real.exp (-(-ζ.re) * x) * ‖convPow g (n + 1) x‖) := by
        refine lintegral_mono fun x => ?_
        rw [norm_mul, norm_cexp_mul_ofReal', renewalTail]
        have hs := (summable_nat_add_iff 1).mpr (summable_norm_convPow hg x)
        calc ENNReal.ofReal (Real.exp (-(-ζ.re) * x) * ‖∑' n, convPow g (n + 1) x‖)
            ≤ ENNReal.ofReal (Real.exp (-(-ζ.re) * x) * ∑' n, ‖convPow g (n + 1) x‖) :=
              ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hs)
                (Real.exp_pos _).le)
          _ = ENNReal.ofReal (∑' n, Real.exp (-(-ζ.re) * x) * ‖convPow g (n + 1) x‖) := by
              rw [tsum_mul_left]
          _ = ∑' n, ENNReal.ofReal (Real.exp (-(-ζ.re) * x) * ‖convPow g (n + 1) x‖) :=
              ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) (hs.mul_left _)
    _ = ∑' n, ∫⁻ x, ENNReal.ofReal (Real.exp (-(-ζ.re) * x) * ‖convPow g (n + 1) x‖) :=
        lintegral_tsum fun n => (ENNReal.measurable_ofReal.comp
          ((by fun_prop : Measurable fun x : ℝ => Real.exp (-(-ζ.re) * x)).mul
            (measurable_convPow hg (n + 1)).norm)).aemeasurable
    _ ≤ ∑' n : ℕ, a ^ (n + 2) := ENNReal.tsum_le_tsum fun n => lintegral_weight_tail_term_le hg _ n
    _ = a ^ 2 * (1 - a)⁻¹ := by
        simp_rw [pow_add, mul_comm _ (a ^ 2)]
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
    _ < ⊤ := ENNReal.mul_lt_top (ENNReal.pow_lt_top (ha.trans ENNReal.one_lt_top))
        (ENNReal.inv_lt_top.mpr (tsub_pos_of_lt ha))

/-- On a line where `∫ e^{-c x}|g| < 1`, `∫ e^{ζ x} (u - g)(x) dx = A²/(1 - A)`. -/
theorem laplaceC_renewalTail (hg : IsExpDensity g D θ) {ζ : ℂ}
    (ha : ∫⁻ x, ENNReal.ofReal (Real.exp (-(-ζ.re) * x) * ‖g x‖) < 1) :
    laplaceC (renewalTail g) ζ = laplaceC g ζ ^ 2 / (1 - laplaceC g ζ) := by
  set a := ∫⁻ x, ENNReal.ofReal (Real.exp (-(-ζ.re) * x) * ‖g x‖)
  have ha' : a ≠ ⊤ := (ha.trans ENNReal.one_lt_top).ne
  have hA : ‖laplaceC g ζ‖ < 1 := by
    refine (norm_laplaceC_le ζ).trans_lt ?_
    rw [← ENNReal.toReal_one]
    exact ENNReal.toReal_strict_mono ENNReal.one_ne_top ha
  set F : ℕ → ℝ → ℂ := fun n x => cexp (ζ * x) * convPow g (n + 1) x
  have hFlin : ∀ n, ∫⁻ x, ENNReal.ofReal ‖F n x‖ ≤ a ^ (n + 2) := by
    intro n
    refine le_of_eq_of_le (lintegral_congr fun x => ?_) (lintegral_weight_tail_term_le hg _ n)
    rw [norm_mul, norm_cexp_mul_ofReal']
  have hFi : ∀ n, Integrable (F n) := by
    intro n
    refine ⟨((by fun_prop : Measurable fun x : ℝ => cexp (ζ * x)).mul
      (measurable_convPow hg (n + 1))).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_norm]
    exact (hFlin n).trans_lt (ENNReal.pow_lt_top (ha.trans ENNReal.one_lt_top))
  have hFs : Summable fun n => ∫ x, ‖F n x‖ := by
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun _ => norm_nonneg _)
      (fun n => ?_) (summable_geometric_of_lt_one ENNReal.toReal_nonneg
        (by rw [← ENNReal.toReal_one]; exact ENNReal.toReal_strict_mono ENNReal.one_ne_top ha)
        |>.mul_left (a.toReal ^ 2))
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun _ => norm_nonneg _)
      (hFi n).norm.aestronglyMeasurable]
    calc (∫⁻ x, ENNReal.ofReal ‖F n x‖).toReal ≤ (a ^ (n + 2)).toReal :=
          ENNReal.toReal_mono (ENNReal.pow_ne_top ha') (hFlin n)
      _ = a.toReal ^ 2 * a.toReal ^ n := by rw [ENNReal.toReal_pow, pow_add, mul_comm]
  have hsum := integral_tsum_of_summable_integral_norm hFi hFs
  calc laplaceC (renewalTail g) ζ = ∫ x, ∑' n, F n x := by
        unfold laplaceC renewalTail
        exact integral_congr_ae (Filter.Eventually.of_forall fun x => tsum_mul_left.symm)
    _ = ∑' n, ∫ x, F n x := hsum.symm
    _ = ∑' n : ℕ, laplaceC g ζ ^ 2 * laplaceC g ζ ^ n := by
        refine tsum_congr fun n => ?_
        rw [show ∫ x, F n x = laplaceC (convPow g (n + 1)) ζ from rfl,
          laplaceC_convPow hg ha' (n + 1), ← pow_add]
        ring_nf
    _ = laplaceC g ζ ^ 2 / (1 - laplaceC g ζ) := by
        rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hA, div_eq_mul_inv]

/-! ### Continuity of the tail -/

theorem IsExpDensity.norm_le_D (hg : IsExpDensity g D θ) (hθ : 0 ≤ θ) (x : ℝ) : ‖g x‖ ≤ D := by
  rcases le_or_gt x 0 with hx | hx
  · rw [hg.eq_zero_of_nonpos x hx, norm_zero]; exact hg.nonneg_D
  · exact (hg.norm_le x).trans (mul_le_of_le_one_right hg.nonneg_D
      (Real.exp_le_one_iff.mpr (by nlinarith)))

theorem IsExpDensity.integrable (hg : IsExpDensity g D θ) (hθ : 0 < θ) : Integrable g := by
  refine ⟨hg.measurable.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  calc ∫⁻ x, ENNReal.ofReal ‖g x‖ ≤ ∫⁻ x in Ioi 0, ENNReal.ofReal (D * Real.exp (-θ * x)) := by
        rw [← lintegral_indicator measurableSet_Ioi]
        refine lintegral_mono fun x => ?_
        by_cases hx : x ∈ Ioi (0 : ℝ)
        · rw [indicator_of_mem hx]; exact ENNReal.ofReal_le_ofReal (hg.norm_le x)
        · rw [indicator_of_notMem hx, hg.eq_zero_of_nonpos x (not_lt.mp hx), norm_zero,
            ENNReal.ofReal_zero]
    _ = ENNReal.ofReal (∫ x in Ioi 0, D * Real.exp (-θ * x)) :=
        (ofReal_integral_eq_lintegral_ofReal ((integrableOn_exp_mul_Ioi (by linarith) 0).const_mul _)
          ((ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun x _ => by
            have := hg.nonneg_D; positivity))).symm
    _ < ⊤ := ENNReal.ofReal_lt_top

theorem convC_eq_convolution (f h : ℝ → ℂ) :
    convC f h = convolution f h (ContinuousLinearMap.mul ℂ ℂ) volume := by
  funext x
  rw [convolution_def]
  rfl

/-- `f ⋆ h` is continuous for integrable `f` and bounded measurable `h`. -/
theorem continuous_convC_of_bounded {f h : ℝ → ℂ} (hf : Integrable f) (hhm : Measurable h)
    {M : ℝ} (hM : ∀ x, ‖h x‖ ≤ M) : Continuous (convC f h) := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hhli : LocallyIntegrable h := by
    refine fun x => ⟨Metric.ball x 1, Metric.ball_mem_nhds x one_pos, ?_⟩
    exact Measure.integrableOn_of_bounded (M := M) measure_ball_lt_top.ne
      hhm.aestronglyMeasurable (Filter.Eventually.of_forall hM)
  refine continuous_of_uniform_approx_of_continuous fun u hu => ?_
  obtain ⟨ε, hε, hεu⟩ := Metric.mem_uniformity_dist.mp hu
  obtain ⟨k₀, hk₀c, hk₀i', hk₀cont, hk₀int⟩ := hf.exists_hasCompactSupport_integral_sub_le
    (ε := ε / (2 * (M + 1))) (by positivity)
  refine ⟨convC k₀ h, ?_, fun x => hεu ?_⟩
  · rw [convC_eq_convolution]
    exact hk₀c.continuous_convolution_left (ContinuousLinearMap.mul ℂ ℂ) hk₀cont hhli
  · rw [dist_eq_norm]
    have hhx : AEStronglyMeasurable (fun y => h (x - y)) volume :=
      (hhm.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
    have hbx : ∀ᵐ y ∂volume, ‖h (x - y)‖ ≤ M := Filter.Eventually.of_forall fun y => hM _
    have hk₀i : Integrable k₀ := hk₀int
    have hsub : convC f h x - convC k₀ h x = ∫ y, (f y - k₀ y) * h (x - y) := by
      unfold convC
      rw [← integral_sub (hf.mul_bdd hhx hbx) (hk₀i.mul_bdd hhx hbx)]
      congr 1; funext y; ring
    rw [hsub]
    calc ‖∫ y, (f y - k₀ y) * h (x - y)‖ ≤ ∫ y, ‖f y - k₀ y‖ * M := by
          refine (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
            (Filter.Eventually.of_forall fun _ => norm_nonneg _)
            ((hf.sub hk₀i).norm.mul_const M) (Filter.Eventually.of_forall fun y => ?_))
          dsimp only
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hM _) (norm_nonneg _)
      _ = (∫ y, ‖f y - k₀ y‖) * M := integral_mul_const _ _
      _ ≤ ε / (2 * (M + 1)) * M := mul_le_mul_of_nonneg_right hk₀i' hM0
      _ < ε := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
          nlinarith

theorem norm_convPow_le_const (hg : IsExpDensity g D θ) (hθ : 0 < θ) (n : ℕ) (x : ℝ) :
    ‖convPow g n x‖ ≤ D ^ (n + 1) / θ ^ n := by
  have hD := hg.nonneg_D
  rcases le_or_gt x 0 with hx | hx
  · rw [convPow_eq_zero_of_nonpos hg n hx, norm_zero]; positivity
  · refine (norm_convPow_le hg n hx).trans ?_
    have h1 := Real.pow_div_factorial_le_exp (x := θ * x) (le_of_lt (mul_pos hθ hx)) n
    have h2 : (θ * x) ^ n / n ! * Real.exp (-θ * x) ≤ 1 := by
      calc (θ * x) ^ n / n ! * Real.exp (-θ * x) ≤ Real.exp (θ * x) * Real.exp (-θ * x) :=
            mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
        _ = 1 := by rw [← Real.exp_add]; simp
    have hθn : 0 < θ ^ n := pow_pos hθ n
    rw [le_div_iff₀ hθn]
    calc D ^ (n + 1) * x ^ n / n ! * Real.exp (-θ * x) * θ ^ n
        = D ^ (n + 1) * ((θ * x) ^ n / n ! * Real.exp (-θ * x)) := by rw [mul_pow]; ring
      _ ≤ D ^ (n + 1) * 1 := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = D ^ (n + 1) := mul_one _

theorem continuous_convPow_succ (hg : IsExpDensity g D θ) (hθ : 0 < θ) (n : ℕ) :
    Continuous (convPow g (n + 1)) :=
  continuous_convC_of_bounded (hg.integrable hθ) (measurable_convPow hg n)
    (norm_convPow_le_const hg hθ n)

/-- The renewal tail `∑_{n ≥ 2} g^{*n}` is continuous. -/
theorem continuous_renewalTail (hg : IsExpDensity g D θ) (hθ : 0 < θ) :
    Continuous (renewalTail g) := by
  have hD := hg.nonneg_D
  have hon : ∀ X : ℝ, ContinuousOn (renewalTail g) (Iio X) := by
    intro X
    refine continuousOn_tsum (fun n => (continuous_convPow_succ hg hθ n).continuousOn)
      (u := fun n => D ^ (n + 2) * (max X 0) ^ (n + 1) / (n + 1)!) ?_
      (fun n x hx => norm_convPow_le_of_le hg hθ.le (n + 1) (le_of_lt hx))
    have := (summable_nat_add_iff 1).mpr ((Real.summable_pow_div_factorial (D * max X 0)).mul_left D)
    refine this.congr fun n => ?_
    rw [mul_pow]; ring
  refine continuous_iff_continuousAt.mpr fun x => ?_
  exact (hon (x + 1)).continuousAt (Iio_mem_nhds (by linarith))

end PGM.WienerHopf
