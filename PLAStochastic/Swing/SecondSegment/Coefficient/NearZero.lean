import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Measure.Portmanteau

/-! # Logarithmic weights near the origin and open-set bounds in the limit

`second-coefficient.md`, C2.8.  The conditional kernel has a logarithmic
singularity `ℓ(-c) ≤ C(1 + log₊(1/c))` at the origin.  A law with a uniform
small-ball bound `ρ{|r| < s} ≤ 2Ds` integrates the weight `log₊(1/|r|)` over
`{|r| < δ}` with total at most `4D√δ`: the layer-cake level set at height `t` is
contained in the ball of radius `min(δ, e^{-t}) ≤ √δ e^{-t/2}`.

The second part records the open-set half of the portmanteau theorem in the
form used for the limiting first-entrance law: eventual bounds on an open set
pass to the weak limit.

Nothing here refers to Swing.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

/-- The weight `log₊(1/|r|)`; it vanishes at `0` and outside `(-1, 1)`. -/
def nearZeroLogWeight (r : ℝ) : ℝ := max (Real.log (1/|r|)) 0

theorem nearZeroLogWeight_nonneg (r : ℝ) : 0 ≤ nearZeroLogWeight r := le_max_right _ _

theorem measurable_nearZeroLogWeight : Measurable nearZeroLogWeight :=
  (Real.measurable_log.comp (measurable_const.div continuous_abs.measurable)).max measurable_const

theorem nearZeroLogWeight_eq_zero {r : ℝ} (hr : 1 ≤ |r|) : nearZeroLogWeight r = 0 := by
  unfold nearZeroLogWeight
  apply max_eq_right
  apply Real.log_nonpos (by positivity)
  rw [div_le_one (by linarith)]
  exact hr

/-- Above level `t > 0` the weight forces `|r| < e^{-t}`. -/
theorem abs_lt_exp_of_lt_nearZeroLogWeight {r t : ℝ} (ht : 0 < t) (h : t < nearZeroLogWeight r) :
    |r| < Real.exp (-t) := by
  have hlog : t < Real.log (1/|r|) := by
    unfold nearZeroLogWeight at h
    rcases max_cases (Real.log (1/|r|)) (0 : ℝ) with ⟨he, _⟩ | ⟨he, _⟩
    · rwa [he] at h
    · rw [he] at h; linarith
  have hr : |r| ≠ 0 := by
    intro h0
    rw [h0, div_zero, Real.log_zero] at hlog
    linarith
  have hpos : 0 < |r| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hr)
  have hexp : Real.exp t < 1/|r| := by
    have := Real.exp_lt_exp.mpr hlog
    rwa [Real.exp_log (by positivity)] at this
  rw [lt_div_iff₀ hpos] at hexp
  have hid : Real.exp (-t) * Real.exp t = 1 := by rw [← Real.exp_add]; simp
  nlinarith [Real.exp_pos t, Real.exp_pos (-t)]

theorem min_le_sqrt_mul_exp {δ t : ℝ} (hδ : 0 ≤ δ) :
    min δ (Real.exp (-t)) ≤ Real.sqrt δ * Real.exp (-1/2 * t) := by
  set u := Real.sqrt δ with hu
  set v := Real.exp (-1/2 * t) with hv
  have hu0 : 0 ≤ u := Real.sqrt_nonneg δ
  have hv0 : 0 < v := Real.exp_pos _
  have hu2 : u^2 = δ := Real.sq_sqrt hδ
  have hv2 : v^2 = Real.exp (-t) := by
    rw [hv, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rcases le_total u v with h | h
  · calc min δ (Real.exp (-t)) ≤ δ := min_le_left _ _
      _ = u*u := by rw [← hu2]; ring
      _ ≤ u*v := mul_le_mul_of_nonneg_left h hu0
  · calc min δ (Real.exp (-t)) ≤ Real.exp (-t) := min_le_right _ _
      _ = v*v := by rw [← hv2]; ring
      _ ≤ u*v := mul_le_mul_of_nonneg_right h hv0.le

/-- C2.8, layer-cake form: a small-ball bound integrates the logarithmic weight. -/
theorem lintegral_indicator_nearZeroLogWeight_le {ρ : Measure ℝ} {D δ : ℝ} (hD : 0 ≤ D)
    (hδ : 0 < δ) (hball : ∀ s, 0 < s → s ≤ δ → ρ {r : ℝ | |r| < s} ≤ ENNReal.ofReal (2*D*s)) :
    (∫⁻ r, ENNReal.ofReal ({r : ℝ | |r| < δ}.indicator nearZeroLogWeight r) ∂ρ) ≤
      ENNReal.ofReal (4*D*Real.sqrt δ) := by
  set S : Set ℝ := {r : ℝ | |r| < δ} with hS
  have hSm : MeasurableSet S := measurableSet_lt continuous_abs.measurable measurable_const
  set f : ℝ → ℝ := S.indicator nearZeroLogWeight with hfdef
  have hfm : Measurable f := measurable_nearZeroLogWeight.indicator hSm
  have hf0 : ∀ r, 0 ≤ f r := fun r => Set.indicator_nonneg (fun r _ => nearZeroLogWeight_nonneg r) r
  rw [lintegral_eq_lintegral_meas_lt ρ (ae_of_all _ hf0) hfm.aemeasurable]
  set K : ℝ := 2*D*Real.sqrt δ with hK
  have hK0 : 0 ≤ K := by positivity
  have hlevel : ∀ t ∈ Ioi (0 : ℝ), ρ {r | t < f r} ≤ ENNReal.ofReal (K * Real.exp (-1/2 * t)) := by
    intro t ht
    have ht0 : 0 < t := ht
    set m : ℝ := min δ (Real.exp (-t)) with hm
    have hm0 : 0 < m := lt_min hδ (Real.exp_pos _)
    have hsub : {r | t < f r} ⊆ {r : ℝ | |r| < m} := by
      intro r hr
      have hr' : t < f r := hr
      by_cases hrS : r ∈ S
      · rw [hfdef, Set.indicator_of_mem hrS] at hr'
        exact lt_min hrS (abs_lt_exp_of_lt_nearZeroLogWeight ht0 hr')
      · rw [hfdef, Set.indicator_of_notMem hrS] at hr'
        exact absurd hr' (not_lt.mpr ht0.le)
    calc ρ {r | t < f r} ≤ ρ {r : ℝ | |r| < m} := measure_mono hsub
      _ ≤ ENNReal.ofReal (2*D*m) := hball m hm0 (min_le_left _ _)
      _ ≤ ENNReal.ofReal (K * Real.exp (-1/2 * t)) := by
        apply ENNReal.ofReal_le_ofReal
        have := min_le_sqrt_mul_exp (t := t) hδ.le
        rw [hK]
        nlinarith
  have hint : IntegrableOn (fun t : ℝ => K * Real.exp (-1/2 * t)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (by norm_num) 0).const_mul K
  calc (∫⁻ t in Ioi (0 : ℝ), ρ {r | t < f r})
      ≤ ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (K * Real.exp (-1/2 * t)) :=
        setLIntegral_mono' measurableSet_Ioi hlevel
    _ = ENNReal.ofReal (∫ t in Ioi (0 : ℝ), K * Real.exp (-1/2 * t)) :=
        (ofReal_integral_eq_lintegral_ofReal hint
          (ae_of_all _ fun t => mul_nonneg hK0 (Real.exp_pos _).le)).symm
    _ = ENNReal.ofReal (4*D*Real.sqrt δ) := by
        rw [integral_const_mul, integral_exp_mul_Ioi (by norm_num) 0, hK]
        congr 1
        simp only [mul_zero, Real.exp_zero]
        ring

/-- A nonnegative function with a finite lintegral bound is integrable with the
same Bochner bound. -/
theorem integrable_and_integral_le_of_lintegral_le {α : Type*} [MeasurableSpace α]
    {ρ : Measure α} {f : α → ℝ} (hf : AEStronglyMeasurable f ρ) (hf0 : ∀ x, 0 ≤ f x)
    {C : ℝ} (hC : 0 ≤ C) (h : (∫⁻ x, ENNReal.ofReal (f x) ∂ρ) ≤ ENNReal.ofReal C) :
    Integrable f ρ ∧ (∫ x, f x ∂ρ) ≤ C := by
  refine ⟨⟨hf, ?_⟩, ?_⟩
  · rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ hf0)]
    exact h.trans_lt ENNReal.ofReal_lt_top
  · rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hf0) hf]
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
    rwa [ENNReal.toReal_ofReal hC] at this

/-- C2.8, integral form: the weight `1 + log₊(1/|r|)` on `{|r| < δ}` has mass at
most `2Dδ + 4D√δ`. -/
theorem integral_indicator_one_add_nearZeroLogWeight_le {ρ : Measure ℝ} [IsFiniteMeasure ρ]
    {D δ : ℝ} (hD : 0 ≤ D) (hδ : 0 < δ)
    (hball : ∀ s, 0 < s → s ≤ δ → ρ {r : ℝ | |r| < s} ≤ ENNReal.ofReal (2*D*s)) :
    Integrable ({r : ℝ | |r| < δ}.indicator (fun r => 1 + nearZeroLogWeight r)) ρ ∧
      (∫ r, {r : ℝ | |r| < δ}.indicator (fun r => 1 + nearZeroLogWeight r) r ∂ρ) ≤
        2*D*δ + 4*D*Real.sqrt δ := by
  set S : Set ℝ := {r : ℝ | |r| < δ} with hS
  have hSm : MeasurableSet S := measurableSet_lt continuous_abs.measurable measurable_const
  have hw := integrable_and_integral_le_of_lintegral_le
    (measurable_nearZeroLogWeight.indicator hSm).aestronglyMeasurable
    (fun r => Set.indicator_nonneg (fun r _ => nearZeroLogWeight_nonneg r) r) (by positivity)
    (lintegral_indicator_nearZeroLogWeight_le hD hδ hball)
  have h1 : Integrable (S.indicator (fun _ => (1 : ℝ))) ρ := (integrable_const 1).indicator hSm
  have hsplit : S.indicator (fun r => 1 + nearZeroLogWeight r) =
      fun r => S.indicator (fun _ => (1 : ℝ)) r + S.indicator nearZeroLogWeight r := by
    funext r
    by_cases hr : r ∈ S
    · simp [Set.indicator_of_mem hr]
    · simp [Set.indicator_of_notMem hr]
  rw [hsplit]
  refine ⟨h1.add hw.1, ?_⟩
  rw [integral_add h1 hw.1, integral_indicator_const _ hSm, smul_eq_mul, mul_one]
  have hball' : ρ.real S ≤ 2*D*δ := by
    have := hball δ hδ le_rfl
    rw [measureReal_def]
    exact (ENNReal.toReal_le_of_le_ofReal (by positivity) this)
  linarith [hw.2]

/-! ### Open-set bounds in a weak limit -/

/-- Eventual bounds on an open set pass to the weak limit. -/
theorem measure_isOpen_le_of_eventually {ι : Type*} {l : Filter ι} [l.NeBot]
    {ρs : ι → ProbabilityMeasure ℝ} {ρ : ProbabilityMeasure ℝ} (hρ : Tendsto ρs l (𝓝 ρ))
    {G : Set ℝ} (hG : IsOpen G) {b : ℝ≥0∞} (hb : ∀ᶠ i in l, (ρs i : Measure ℝ) G ≤ b) :
    (ρ : Measure ℝ) G ≤ b :=
  (ProbabilityMeasure.le_liminf_measure_open_of_tendsto hρ hG).trans
    (liminf_le_of_frequently_le' hb.frequently)

/-- An open set whose measures are eventually bounded by a null sequence is null
in the weak limit. -/
theorem measure_isOpen_eq_zero_of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot]
    {ρs : ι → ProbabilityMeasure ℝ} {ρ : ProbabilityMeasure ℝ} (hρ : Tendsto ρs l (𝓝 ρ))
    {G : Set ℝ} (hG : IsOpen G) {a : ι → ℝ} (ha : Tendsto a l (𝓝 0))
    (hb : ∀ᶠ i in l, (ρs i : Measure ℝ) G ≤ ENNReal.ofReal (a i)) :
    (ρ : Measure ℝ) G = 0 := by
  refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_) bot_le
  rw [zero_add]
  have hev : ∀ᶠ i in l, a i < ε := ha.eventually (Iio_mem_nhds (by exact_mod_cast hε))
  apply measure_isOpen_le_of_eventually hρ hG
  filter_upwards [hb, hev] with i hi hai
  refine hi.trans ?_
  rw [← ENNReal.ofReal_coe_nnreal]
  exact ENNReal.ofReal_le_ofReal hai.le

end SwingRepair
