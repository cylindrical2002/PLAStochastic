import PLAStochastic.ForMathlib.Analysis.ConvexAntitoneSumIntegral
import PLAStochastic.Swing.Gaussian.Tail.ScalarAntiConcentration
import PLAStochastic.Swing.Gaussian.Tail.QuadraticDrift

/-! # The series `∑_{n≥1} Φ(-a√n)` (roadmap 1.1(d))

For `a > 0` let `g_a(x) = P(Z > a√x)`, `Z ~ N(0,1)`.  Then `g_a` is antitone, convex on
`[0,∞)`, `g_a(0) = 1/2` and `∫₀^∞ g_a = 1/(2a²)` (it is the tail function of `(Z₊/a)²`).
`Fluctuation.tsum_add_one_bounds_of_convex_antitone` therefore gives

  `1/(2a²) - 1/4 ≤ ∑_{n≥1} Φ(-a√n) ≤ 1/(2a²)`,

the bound on `𝔼τ*_a = ∑_n P(W_n > an)` used for `1/2 ≤ β' ≤ 3/4` in Appendix I.
Convexity is proved from the slope inequality with the explicit density: on
`0 ≤ s ≤ t`, `(t-s) φ(t) ≤ P(s < Z ≤ t) ≤ (t-s) φ(s)`, and `√y - √x` is squeezed
between `(y-x)/(2√y)` and `(y-x)/(2√x)`.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
namespace SwingRepair
namespace Fluctuation

/-- `g_a(x) = P(Z > a√x)`. -/
def gaussianTailSqrt (a x : ℝ) : ℝ := (gaussianReal 0 1).real (Ioi (a * Real.sqrt x))

theorem gaussianTailSqrt_nonneg (a x : ℝ) : 0 ≤ gaussianTailSqrt a x := measureReal_nonneg

theorem gaussianTailSqrt_antitone {a : ℝ} (ha : 0 ≤ a) : Antitone (gaussianTailSqrt a) := by
  intro x y hxy
  unfold gaussianTailSqrt
  exact measureReal_mono (Ioi_subset_Ioi (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hxy) ha))
    (measure_ne_top _ _)

theorem gaussianTailSqrt_measurable {a : ℝ} (ha : 0 ≤ a) : Measurable (gaussianTailSqrt a) :=
  (gaussianTailSqrt_antitone ha).measurable

/-! ### The half mass -/

theorem gaussianReal_real_Ioi_zero : (gaussianReal 0 1).real (Ioi (0 : ℝ)) = 1 / 2 := by
  set ν := gaussianReal 0 1 with hν
  have : NullSingletonClass ν := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
  have hprob : IsProbabilityMeasure ν := by rw [hν]; infer_instance
  have hneg : ν.map (fun x : ℝ => -x) = ν := by
    rw [hν, gaussianReal_map_neg, neg_zero]
  have h1 : ν (Iio 0) = ν (Ioi 0) := by
    conv_lhs => rw [← hneg]
    rw [Measure.map_apply measurable_neg measurableSet_Iio]
    congr 1
    ext x
    simp
  have h2 : ν (Iic 0) = ν (Iio 0) := measure_congr Iio_ae_eq_Iic.symm
  have h3 : ν (Ioi 0) + ν (Iic 0) = 1 := by
    rw [← measure_univ (μ := ν), ← Ioi_union_Iic (a := (0 : ℝ)), measure_union _ measurableSet_Iic]
    exact Ioi_disjoint_Iic le_rfl
  rw [h2, h1] at h3
  have h4 : ν (Ioi 0) = 1 / 2 := by
    have : (2 : ℝ≥0∞) * ν (Ioi 0) = 1 := by rw [two_mul]; exact h3
    rw [ENNReal.eq_div_iff two_ne_zero ENNReal.ofNat_ne_top, this]
  rw [Measure.real, h4]
  simp

theorem gaussianTailSqrt_zero (a : ℝ) : gaussianTailSqrt a 0 = 1 / 2 := by
  unfold gaussianTailSqrt
  rw [Real.sqrt_zero, mul_zero]
  exact gaussianReal_real_Ioi_zero

/-! ### Interval masses against the density -/

/-- `P(s < Z ≤ t) ≤ (t - s) φ(s)` for `0 ≤ s ≤ t`. -/
theorem gaussianReal_real_Ioc_le {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    (gaussianReal 0 1).real (Ioc s t) ≤ (t - s) * gaussianPDFReal 0 1 s := by
  have h := gaussianReal_le_density_volume hs (S := Ioc s t) measurableSet_Ioc (fun x hx => hx.1.le)
  rw [Real.volume_Ioc, ← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _)] at h
  rw [Measure.real]
  calc (gaussianReal 0 1 (Ioc s t)).toReal
      ≤ (ENNReal.ofReal (gaussianPDFReal 0 1 s * (t - s))).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
    _ = (t - s) * gaussianPDFReal 0 1 s := by
        rw [ENNReal.toReal_ofReal (mul_nonneg (gaussianPDFReal_nonneg _ _ _) (by linarith))]
        ring

/-- `(t - s) φ(t) ≤ P(s < Z ≤ t)` for `0 ≤ s ≤ t`. -/
theorem le_gaussianReal_real_Ioc {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    (t - s) * gaussianPDFReal 0 1 t ≤ (gaussianReal 0 1).real (Ioc s t) := by
  have h : ENNReal.ofReal (gaussianPDFReal 0 1 t) * volume (Ioc s t) ≤ gaussianReal 0 1 (Ioc s t) := by
    rw [gaussianReal_apply _ (by norm_num) (Ioc s t), ← setLIntegral_const]
    refine setLIntegral_mono' measurableSet_Ioc fun x hx => ?_
    rw [gaussianPDF_def]
    exact ENNReal.ofReal_le_ofReal (gaussianPDFReal_antitone_nonneg (hs.trans hx.1.le) hx.2)
  rw [Real.volume_Ioc, ← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _)] at h
  rw [Measure.real]
  calc (t - s) * gaussianPDFReal 0 1 t
      = (ENNReal.ofReal (gaussianPDFReal 0 1 t * (t - s))).toReal := by
        rw [ENNReal.toReal_ofReal (mul_nonneg (gaussianPDFReal_nonneg _ _ _) (by linarith))]
        ring
    _ ≤ (gaussianReal 0 1 (Ioc s t)).toReal := ENNReal.toReal_mono (measure_ne_top _ _) h

/-- `g_a(x) - g_a(y) = P(a√x < Z ≤ a√y)` for `x ≤ y`. -/
theorem gaussianTailSqrt_sub {a x y : ℝ} (ha : 0 ≤ a) (hxy : x ≤ y) :
    gaussianTailSqrt a x - gaussianTailSqrt a y =
      (gaussianReal 0 1).real (Ioc (a * Real.sqrt x) (a * Real.sqrt y)) := by
  unfold gaussianTailSqrt
  rw [← Ioi_sdiff_Ioi, measureReal_sdiff (Ioi_subset_Ioi
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hxy) ha)) measurableSet_Ioi]

/-! ### Convexity -/

/-- `√y - √x ≥ (y - x)/(2√y)` for `0 ≤ x ≤ y`, in product form. -/
theorem sqrt_sub_sqrt_mul_two_sqrt_ge {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    y - x ≤ (Real.sqrt y - Real.sqrt x) * (2 * Real.sqrt y) := by
  have hsx := Real.sqrt_nonneg x
  have hsy := Real.sqrt_nonneg y
  have hle : Real.sqrt x ≤ Real.sqrt y := Real.sqrt_le_sqrt hxy
  have e : (Real.sqrt y - Real.sqrt x) * (Real.sqrt y + Real.sqrt x) = y - x := by
    calc (Real.sqrt y - Real.sqrt x) * (Real.sqrt y + Real.sqrt x)
        = Real.sqrt y ^ 2 - Real.sqrt x ^ 2 := by ring
      _ = y - x := by rw [Real.sq_sqrt (hx.trans hxy), Real.sq_sqrt hx]
  nlinarith

/-- `√z - √y ≤ (z - y)/(2√y)` for `0 ≤ y ≤ z`, in product form. -/
theorem sqrt_sub_sqrt_mul_two_sqrt_le {y z : ℝ} (hy : 0 ≤ y) (hyz : y ≤ z) :
    (Real.sqrt z - Real.sqrt y) * (2 * Real.sqrt y) ≤ z - y := by
  have hsy := Real.sqrt_nonneg y
  have hsz := Real.sqrt_nonneg z
  have hle : Real.sqrt y ≤ Real.sqrt z := Real.sqrt_le_sqrt hyz
  have e : (Real.sqrt z - Real.sqrt y) * (Real.sqrt z + Real.sqrt y) = z - y := by
    calc (Real.sqrt z - Real.sqrt y) * (Real.sqrt z + Real.sqrt y)
        = Real.sqrt z ^ 2 - Real.sqrt y ^ 2 := by ring
      _ = z - y := by rw [Real.sq_sqrt (hy.trans hyz), Real.sq_sqrt hy]
  nlinarith

theorem gaussianTailSqrt_convexOn {a : ℝ} (ha : 0 < a) :
    ConvexOn ℝ (Ici 0) (gaussianTailSqrt a) := by
  refine convexOn_of_slope_mono_adjacent (convex_Ici 0) ?_
  intro x y z hx _ hxy hyz
  have hx0 : 0 ≤ x := hx
  have hy0 : 0 < y := lt_of_le_of_lt hx0 hxy
  have hsy : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy0
  set φ := gaussianPDFReal 0 1 (a * Real.sqrt y) with hφ
  have hφ0 : 0 ≤ φ := gaussianPDFReal_nonneg _ _ _
  -- the common slope `-k`, `k = a φ(a√y) / (2√y)`
  set k := a * φ / (2 * Real.sqrt y) with hk
  have hk0 : 0 ≤ k := div_nonneg (mul_nonneg ha.le hφ0) (by positivity)
  -- left slope ≤ -k
  have hL : (gaussianTailSqrt a y - gaussianTailSqrt a x) / (y - x) ≤ -k := by
    rw [div_le_iff₀ (by linarith)]
    have hsub := gaussianTailSqrt_sub ha.le hxy.le
    have hmass := le_gaussianReal_real_Ioc (s := a * Real.sqrt x) (t := a * Real.sqrt y)
      (by positivity) (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hxy.le) ha.le)
    have hsq := sqrt_sub_sqrt_mul_two_sqrt_ge hx0 hxy.le
    -- (a√y - a√x) φ ≥ a (y-x) φ / (2√y) = k (y - x)
    have hk' : k * (y - x) = a * φ * (y - x) / (2 * Real.sqrt y) := by rw [hk]; ring
    have hkey : k * (y - x) ≤ (a * Real.sqrt y - a * Real.sqrt x) * φ := by
      rw [hk', div_le_iff₀ (by positivity)]
      have : a * φ * (y - x) ≤ a * φ * ((Real.sqrt y - Real.sqrt x) * (2 * Real.sqrt y)) :=
        mul_le_mul_of_nonneg_left hsq (mul_nonneg ha.le hφ0)
      calc a * φ * (y - x) ≤ a * φ * ((Real.sqrt y - Real.sqrt x) * (2 * Real.sqrt y)) := this
        _ = (a * Real.sqrt y - a * Real.sqrt x) * φ * (2 * Real.sqrt y) := by ring
    linarith
  -- right slope ≥ -k
  have hR : -k ≤ (gaussianTailSqrt a z - gaussianTailSqrt a y) / (z - y) := by
    rw [le_div_iff₀ (by linarith)]
    have hsub := gaussianTailSqrt_sub ha.le hyz.le
    have hmass := gaussianReal_real_Ioc_le (s := a * Real.sqrt y) (t := a * Real.sqrt z)
      (by positivity) (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hyz.le) ha.le)
    have hsq := sqrt_sub_sqrt_mul_two_sqrt_le hy0.le hyz.le
    have hk' : k * (z - y) = a * φ * (z - y) / (2 * Real.sqrt y) := by rw [hk]; ring
    have hkey : (a * Real.sqrt z - a * Real.sqrt y) * φ ≤ k * (z - y) := by
      rw [hk', le_div_iff₀ (by positivity)]
      have : a * φ * ((Real.sqrt z - Real.sqrt y) * (2 * Real.sqrt y)) ≤ a * φ * (z - y) :=
        mul_le_mul_of_nonneg_left hsq (mul_nonneg ha.le hφ0)
      calc (a * Real.sqrt z - a * Real.sqrt y) * φ * (2 * Real.sqrt y)
          = a * φ * ((Real.sqrt z - Real.sqrt y) * (2 * Real.sqrt y)) := by ring
        _ ≤ a * φ * (z - y) := this
    linarith
  exact hL.trans hR

/-! ### The integral `∫₀^∞ g_a = 1/(2a²)` -/

theorem integral_sq_pos_part_standardGaussian :
    (∫ z : ℝ, (max z 0) ^ 2 ∂gaussianReal 0 1) = 1 / 2 := by
  set ν := gaussianReal 0 1 with hν
  have hprob : IsProbabilityMeasure ν := by rw [hν]; infer_instance
  have hsq : Integrable (fun z : ℝ => z ^ 2) ν :=
    (memLp_id_gaussianReal (μ := 0) (v := 1) 2).integrable_sq
  have hpos : Integrable (fun z : ℝ => (max z 0) ^ 2) ν := by
    refine hsq.mono' (by fun_prop) ?_
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    rcases le_total z 0 with h | h
    · rw [max_eq_right h]; nlinarith [sq_nonneg z]
    · rw [max_eq_left h]
  have hneg : Integrable (fun z : ℝ => (max (-z) 0) ^ 2) ν := by
    refine hsq.mono' (by fun_prop) ?_
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    rcases le_total (-z) 0 with h | h
    · rw [max_eq_right h]; nlinarith [sq_nonneg z]
    · rw [max_eq_left h]; nlinarith
  -- symmetry
  have hsymm : (∫ z, (max (-z) 0) ^ 2 ∂ν) = ∫ z, (max z 0) ^ 2 ∂ν := by
    have hmap : ν.map (fun x : ℝ => -x) = ν := by rw [hν, gaussianReal_map_neg, neg_zero]
    conv_rhs => rw [← hmap]
    rw [integral_map measurable_neg.aemeasurable (by fun_prop)]
  -- decomposition
  have hdec : ∀ z : ℝ, (max z 0) ^ 2 + (max (-z) 0) ^ 2 = z ^ 2 := by
    intro z
    rcases le_total z 0 with h | h
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
  have htot : (∫ z, (max z 0) ^ 2 ∂ν) + ∫ z, (max (-z) 0) ^ 2 ∂ν = 1 := by
    rw [← integral_add hpos hneg]
    simp_rw [hdec]
    exact integral_sq_standardGaussian
  linarith

theorem lintegral_gaussianTailSqrt {a : ℝ} (ha : 0 < a) :
    (∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (gaussianTailSqrt a x)) =
      ENNReal.ofReal (1 / (2 * a ^ 2)) := by
  set ν := gaussianReal 0 1 with hν
  have hprob : IsProbabilityMeasure ν := by rw [hν]; infer_instance
  set f : ℝ → ℝ := fun z => (max z 0) ^ 2 / a ^ 2 with hf
  have hf_nn : 0 ≤ᵐ[ν] f := ae_of_all _ fun z => by positivity
  have hf_m : AEMeasurable f ν := by fun_prop
  have hlayer := lintegral_comp_eq_lintegral_meas_lt_mul ν (f := f) (g := fun _ => (1 : ℝ)) hf_nn hf_m
    (fun t _ => continuous_const.intervalIntegrable 0 t) (ae_of_all _ fun _ => zero_le_one)
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one, ENNReal.ofReal_one] at hlayer
  -- identify the level sets
  have hlevel : ∀ t ∈ Ioi (0 : ℝ), {z : ℝ | t < f z} = Ioi (a * Real.sqrt t) := by
    intro t ht
    have ht0 : 0 < t := ht
    ext z
    simp only [mem_ofPred_eq, mem_Ioi, hf]
    rw [lt_div_iff₀ (by positivity)]
    constructor
    · intro h
      have hz : 0 < max z 0 := by
        by_contra hc
        push Not at hc
        have : max z 0 = 0 := le_antisymm hc (le_max_right _ _)
        rw [this] at h
        nlinarith [sq_nonneg a]
      have hz' : max z 0 = z := max_eq_left (by
        by_contra hc; push Not at hc; rw [max_eq_right hc.le] at hz; exact lt_irrefl _ hz)
      rw [hz'] at h
      -- t a² < z², z > 0 ⇒ a√t < z
      have hz0 : 0 < z := by rw [← hz']; exact hz
      have : a * Real.sqrt t = Real.sqrt (t * a ^ 2) := by
        rw [Real.sqrt_mul ht0.le, Real.sqrt_sq ha.le]; ring
      rw [this]
      exact (Real.sqrt_lt' hz0).mpr h
    · intro h
      have hz0 : 0 < z := lt_of_le_of_lt (by positivity) h
      rw [max_eq_left hz0.le]
      have : a * Real.sqrt t = Real.sqrt (t * a ^ 2) := by
        rw [Real.sqrt_mul ht0.le, Real.sqrt_sq ha.le]; ring
      rw [this] at h
      exact (Real.sqrt_lt' hz0).mp h
  have hrhs : (∫⁻ t in Ioi (0 : ℝ), ν {z : ℝ | t < f z}) =
      ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (gaussianTailSqrt a t) := by
    refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    rw [hlevel t ht, gaussianTailSqrt, ofReal_measureReal]
  rw [← hrhs, ← hlayer]
  -- the left side is `∫ f dν = (1/2)/a²`
  have hint : Integrable f ν := by
    have hsq : Integrable (fun z : ℝ => z ^ 2) ν :=
      (memLp_id_gaussianReal (μ := 0) (v := 1) 2).integrable_sq
    refine (hsq.div_const (a ^ 2)).mono' (by fun_prop) ?_
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    apply div_le_div_of_nonneg_right _ (by positivity)
    rcases le_total z 0 with h | h
    · rw [max_eq_right h]; nlinarith [sq_nonneg z]
    · rw [max_eq_left h]
  rw [← ofReal_integral_eq_lintegral_ofReal hint hf_nn]
  congr 1
  simp only [hf]
  rw [integral_div, integral_sq_pos_part_standardGaussian]
  field_simp

theorem gaussianTailSqrt_integrableOn {a : ℝ} (ha : 0 < a) :
    IntegrableOn (gaussianTailSqrt a) (Ioi 0) := by
  refine ⟨(gaussianTailSqrt_measurable ha.le).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x => gaussianTailSqrt_nonneg a x),
    lintegral_gaussianTailSqrt ha]
  exact ENNReal.ofReal_lt_top

theorem integral_gaussianTailSqrt {a : ℝ} (ha : 0 < a) :
    (∫ x in Ioi (0 : ℝ), gaussianTailSqrt a x) = 1 / (2 * a ^ 2) := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x => gaussianTailSqrt_nonneg a x)
    (gaussianTailSqrt_measurable ha.le).aestronglyMeasurable, lintegral_gaussianTailSqrt ha,
    ENNReal.toReal_ofReal (by positivity)]

/-! ### The series bound -/

/-- **`1/(2a²) - 1/4 ≤ ∑_{n≥1} P(Z > a√n) ≤ 1/(2a²)`.** -/
theorem tsum_gaussianTailSqrt_bounds {a : ℝ} (ha : 0 < a) :
    1 / (2 * a ^ 2) - 1 / 4 ≤ ∑' n : ℕ, gaussianTailSqrt a (n + 1 : ℕ) ∧
      ∑' n : ℕ, gaussianTailSqrt a (n + 1 : ℕ) ≤ 1 / (2 * a ^ 2) := by
  have h := tsum_add_one_bounds_of_convex_antitone (gaussianTailSqrt_convexOn ha)
    ((gaussianTailSqrt_antitone ha.le).antitoneOn _) (fun t _ => gaussianTailSqrt_nonneg a t)
    (gaussianTailSqrt_integrableOn ha)
  rw [integral_gaussianTailSqrt ha, gaussianTailSqrt_zero] at h
  refine ⟨?_, h.2⟩
  have := h.1
  linarith

theorem summable_gaussianTailSqrt {a : ℝ} (ha : 0 < a) :
    Summable fun n : ℕ => gaussianTailSqrt a (n + 1 : ℕ) := by
  have := ((gaussianTailSqrt_antitone ha.le).antitoneOn (Ici 0)).summable_of_integrableOn_Ioi_zero
    (gaussianTailSqrt_integrableOn ha) (fun t _ => gaussianTailSqrt_nonneg a t)
  exact (summable_nat_add_iff (f := fun m : ℕ => gaussianTailSqrt a m) 1).mpr this

end Fluctuation
end SwingRepair
