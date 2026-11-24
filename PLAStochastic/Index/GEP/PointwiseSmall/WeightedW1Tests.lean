import PLAStochastic.Index.GEP.Universality.Defs
import PLAStochastic.Index.GEP.Response.Score.UniformBounds

/-!
# WP4 leaves `PointwiseSmall`, `QuadResponse`: tests against the weighted `W₁` distance

For a probability law `μ` on `[0, ∞)` and a test `φ = testFn χ` (`φ(y) = ∫_{(0,y)} χ`) with
`|χ(s)| ≤ L e^{γs}`, Fubini gives the layer-cake form
`∫ φ dμ = ∫_{(0,∞)} χ(s) μ(s, ∞) ds` (`pw_integral_testFn`), provided `x e^{γx}` is
`μ`-integrable.  Hence for two such laws
`|∫ φ dμ - ∫ φ dρ| ≤ ∫_{(0,∞)} |χ| |F_μ - F_ρ| ≤ L d_γ(μ, ρ)` (`pw_abs_sub_le_dEtaL`), where
`d_γ = dEtaL γ` is the weighted `W₁` distance of (U).  This is how the real-axis smallness of
(U) is read off for the first and second moments and for the output tests.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

/-- The integrand of the layer-cake identity on `ℝ × ℝ`. -/
def pwCake (χ : ℝ → ℝ) (x y : ℝ) : ℝ :=
  {p : ℝ × ℝ | 0 < p.2 ∧ p.2 < p.1}.indicator (fun p => χ p.2) (x, y)

theorem measurableSet_cake : MeasurableSet {p : ℝ × ℝ | 0 < p.2 ∧ p.2 < p.1} :=
  (measurableSet_lt measurable_const measurable_snd).inter
    (measurableSet_lt measurable_snd measurable_fst)

theorem measurable_cake {χ : ℝ → ℝ} (hχ : Measurable χ) :
    Measurable (Function.uncurry (pwCake χ)) := by
  have h : Function.uncurry (pwCake χ) =
      {p : ℝ × ℝ | 0 < p.2 ∧ p.2 < p.1}.indicator (fun p => χ p.2) := by
    funext p; rfl
  rw [h]
  exact (hχ.comp measurable_snd).indicator measurableSet_cake

theorem pwCake_eq_left (χ : ℝ → ℝ) (x y : ℝ) : pwCake χ x y = (Ioo 0 x).indicator χ y := by
  by_cases h : 0 < y ∧ y < x
  · rw [pwCake, indicator_of_mem (show (x, y) ∈ {p : ℝ × ℝ | 0 < p.2 ∧ p.2 < p.1} from h),
      indicator_of_mem (show y ∈ Ioo 0 x from h)]
  · rw [pwCake, indicator_of_notMem (show (x, y) ∉ {p : ℝ × ℝ | 0 < p.2 ∧ p.2 < p.1} from h),
      indicator_of_notMem (show y ∉ Ioo 0 x from h)]

theorem pwCake_eq_right (χ : ℝ → ℝ) (x y : ℝ) :
    pwCake χ x y = (Ioi 0).indicator (fun y => (Ioi y).indicator (fun _ => χ y) x) y := by
  by_cases hy : 0 < y
  · rw [indicator_of_mem (show y ∈ Ioi (0 : ℝ) from hy)]
    by_cases hx : y < x
    · rw [pwCake, indicator_of_mem (show (x, y) ∈ {p : ℝ × ℝ | 0 < p.2 ∧ p.2 < p.1} from
        ⟨hy, hx⟩), indicator_of_mem (show x ∈ Ioi y from hx)]
    · rw [pwCake, indicator_of_notMem (show (x, y) ∉ {p : ℝ × ℝ | 0 < p.2 ∧ p.2 < p.1} from
        fun h => hx h.2), indicator_of_notMem (show x ∉ Ioi y from hx)]
  · rw [indicator_of_notMem (show y ∉ Ioi (0 : ℝ) from hy), pwCake,
      indicator_of_notMem (show (x, y) ∉ {p : ℝ × ℝ | 0 < p.2 ∧ p.2 < p.1} from
        fun h => hy h.1)]

/-- **Layer-cake form of a test** (Fubini): for a probability law on `[0,∞)`,
`∫ testFn χ dμ = ∫_{(0,∞)} χ(s) μ(s,∞) ds`, and the right integrand is integrable. -/
theorem pw_integral_testFn {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : μ (Iio 0) = 0)
    {χ : ℝ → ℝ} (hχ : Measurable χ) {L γ : ℝ} (hγ : 0 ≤ γ)
    (hχb : ∀ s, 0 ≤ s → |χ s| ≤ L * Real.exp (γ * s))
    (hint : Integrable (fun x => x * Real.exp (γ * x)) μ) :
    IntegrableOn (fun s => χ s * μ.real (Ioi s)) (Ioi 0) ∧
      ∫ x, testFn χ x ∂μ = ∫ s in Ioi 0, χ s * μ.real (Ioi s) := by
  have hL : 0 ≤ L := by
    have h := hχb 0 le_rfl
    rw [mul_zero, Real.exp_zero, mul_one] at h
    exact (abs_nonneg _).trans h
  have hae : ∀ᵐ x ∂μ, 0 ≤ x := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hμ] with x hx
    simpa using hx
  have hm := measurable_cake hχ
  -- the inner integrals in `y`
  have hin : ∀ x, 0 ≤ x → Integrable (fun y => pwCake χ x y) volume ∧
      ∫ y, ‖pwCake χ x y‖ ≤ L * (x * Real.exp (γ * x)) := by
    intro x hx
    have hb : ∀ y ∈ Ioo 0 x, ‖χ y‖ ≤ L * Real.exp (γ * x) := fun y hy => by
      rw [Real.norm_eq_abs]
      refine (hχb y hy.1.le).trans ?_
      gcongr
      exact hy.2.le
    have hio : IntegrableOn χ (Ioo 0 x) := by
      refine Measure.integrableOn_of_bounded (M := L * Real.exp (γ * x)) ?_
        hχ.aestronglyMeasurable ?_
      · rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top
      · exact ae_restrict_of_forall_mem measurableSet_Ioo hb
    have e : (fun y => pwCake χ x y) = (Ioo 0 x).indicator χ := funext (pwCake_eq_left χ x)
    refine ⟨by rw [e]; exact (integrable_indicator_iff measurableSet_Ioo).2 hio, ?_⟩
    have e' : (fun y => ‖pwCake χ x y‖) = (Ioo 0 x).indicator (fun y => ‖χ y‖) := by
      funext y
      rw [pwCake_eq_left, norm_indicator_eq_indicator_norm]
    rw [e', integral_indicator measurableSet_Ioo]
    have h := setIntegral_mono_on hio.norm (integrableOn_const (C := L * Real.exp (γ * x))
      (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)) measurableSet_Ioo hb
    rw [setIntegral_const, Real.volume_real_Ioo_of_le hx, sub_zero, smul_eq_mul] at h
    linarith
  have hprod : Integrable (Function.uncurry (pwCake χ)) (μ.prod volume) := by
    rw [integrable_prod_iff hm.aestronglyMeasurable]
    refine ⟨hae.mono fun x hx => (hin x hx).1, ?_⟩
    refine (hint.const_mul L).mono' ?_ ?_
    · exact (hm.norm.stronglyMeasurable.integral_prod_right' (ν := volume)).aestronglyMeasurable
    · filter_upwards [hae] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun y => norm_nonneg _)]
      exact (hin x hx).2
  have hswap := integral_integral_swap hprod
  have hleft : ∀ x, ∫ y, pwCake χ x y = testFn χ x := fun x => by
    rw [show (fun y => pwCake χ x y) = (Ioo 0 x).indicator χ from funext (pwCake_eq_left χ x),
      integral_indicator measurableSet_Ioo]
    rfl
  have hright : ∀ y, ∫ x, pwCake χ x y ∂μ =
      (Ioi 0).indicator (fun s => χ s * μ.real (Ioi s)) y := by
    intro y
    simp_rw [pwCake_eq_right χ _ y]
    by_cases hy : 0 < y
    · simp only [indicator_of_mem (show y ∈ Ioi (0 : ℝ) from hy)]
      rw [integral_indicator_const _ measurableSet_Ioi, smul_eq_mul, mul_comm]
    · simp only [indicator_of_notMem (show y ∉ Ioi (0 : ℝ) from hy), integral_zero]
  simp_rw [hleft, hright] at hswap
  have hR := hprod.integral_prod_right
  simp only [Function.uncurry_apply_pair] at hR
  simp_rw [hright] at hR
  refine ⟨(integrable_indicator_iff measurableSet_Ioi).1 hR, ?_⟩
  rw [hswap, integral_indicator measurableSet_Ioi]

/-- **Tests against the weighted `W₁` distance**: for two probability laws on `[0,∞)` and
`|χ(s)| ≤ L e^{γs}`, `|∫ φ dμ - ∫ φ dρ| ≤ L d_γ(μ,ρ)`. -/
theorem pw_abs_sub_le_dEtaL {μ ρ : ProbabilityMeasure ℝ} (hμ : (μ : Measure ℝ) (Iio 0) = 0)
    (hρ : (ρ : Measure ℝ) (Iio 0) = 0) {χ : ℝ → ℝ} (hχ : Measurable χ) {L γ : ℝ} (hγ : 0 ≤ γ)
    (hχb : ∀ s, 0 ≤ s → |χ s| ≤ L * Real.exp (γ * s))
    (hintμ : Integrable (fun x => x * Real.exp (γ * x)) (μ : Measure ℝ))
    (hintρ : Integrable (fun x => x * Real.exp (γ * x)) (ρ : Measure ℝ))
    (hfin : dEtaL γ μ ρ ≠ ⊤) :
    |∫ x, testFn χ x ∂(μ : Measure ℝ) - ∫ x, testFn χ x ∂(ρ : Measure ℝ)| ≤
      L * (dEtaL γ μ ρ).toReal := by
  have hL : 0 ≤ L := by
    have h := hχb 0 le_rfl
    rw [mul_zero, Real.exp_zero, mul_one] at h
    exact (abs_nonneg _).trans h
  obtain ⟨iμ, eμ⟩ := pw_integral_testFn hμ hχ hγ hχb hintμ
  obtain ⟨iρ, eρ⟩ := pw_integral_testFn hρ hχ hγ hχb hintρ
  rw [eμ, eρ, ← integral_sub iμ iρ]
  have hcdf : ∀ (m : ProbabilityMeasure ℝ) (s : ℝ),
      (m : Measure ℝ).real (Ioi s) = 1 - cdf (m : Measure ℝ) s := by
    intro m s
    rw [cdf_eq_real, ← compl_Iic, measureReal_compl measurableSet_Iic, probReal_univ]
  have hpt : ∀ s, χ s * (μ : Measure ℝ).real (Ioi s) - χ s * (ρ : Measure ℝ).real (Ioi s) =
      χ s * (cdf (ρ : Measure ℝ) s - cdf (μ : Measure ℝ) s) := fun s => by
    rw [hcdf, hcdf]; ring
  simp_rw [hpt]
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_lintegral_norm _).trans ?_
  have hle : ∫⁻ s in Ioi 0, ENNReal.ofReal ‖χ s * (cdf (ρ : Measure ℝ) s -
      cdf (μ : Measure ℝ) s)‖ ≤ ENNReal.ofReal L * dEtaL γ μ ρ := by
    rw [dEtaL, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_mono' measurableSet_Ioi fun s hs => ?_
    rw [← ENNReal.ofReal_mul hL]
    apply ENNReal.ofReal_le_ofReal
    rw [Real.norm_eq_abs, abs_mul, abs_sub_comm]
    have h1 := hχb s (le_of_lt hs)
    have h2 := abs_nonneg (cdf (μ : Measure ℝ) s - cdf (ρ : Measure ℝ) s)
    calc |χ s| * |cdf (μ : Measure ℝ) s - cdf (ρ : Measure ℝ) s|
        ≤ L * Real.exp (γ * s) * |cdf (μ : Measure ℝ) s - cdf (ρ : Measure ℝ) s| := by gcongr
      _ = L * (Real.exp (γ * s) * |cdf (μ : Measure ℝ) s - cdf (ρ : Measure ℝ) s|) := by ring
  refine (ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) hle).trans ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hL]

end

end PGM
