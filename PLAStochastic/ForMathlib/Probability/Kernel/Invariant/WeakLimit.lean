import PLAStochastic.ForMathlib.Probability.Kernel.Invariant.UniqueOfCommonMeasure
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Prokhorov

/-! # Passing an invariant law to the limit of a kernel family

`app:limit` closes Theorem 4.3 by letting the budget grow in the invariance
identity `ν_E K_E = ν_E`.  The step is abstract: it uses only that the test
integrals of `K_E` converge to those of `K` uniformly on compact sets, that
`Kf` is continuous, and that the laws converge weakly.  This file proves that
step for kernels on the line, together with the two facts the paper quotes
along the way: bounded Lipschitz functions determine a finite Borel measure,
and a weakly convergent family of probability laws is eventually tight.

The uniform kernel convergence itself is not proved here; it is the named
hypothesis of the theorems below.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair
namespace KernelLimit
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! ### The bounded Lipschitz test class -/

/-- A bounded Lipschitz test function with the explicit constants used by
`app:limit`: Lipschitz constant `L` and sup norm at most `B`. -/
structure IsBddLip (f : ℝ → ℝ) (L B : ℝ) : Prop where
  meas : Measurable f
  lip : ∀ x y : ℝ, |f x - f y| ≤ L * |x - y|
  bdd : ∀ x, |f x| ≤ B

theorem IsBddLip.const_nonneg {f : ℝ → ℝ} {L B : ℝ} (hf : IsBddLip f L B) : 0 ≤ L := by
  have h := hf.lip 0 1
  have habs : |(0 : ℝ) - 1| = 1 := by norm_num
  rw [habs, mul_one] at h
  exact le_trans (abs_nonneg _) h

theorem IsBddLip.lipschitzWith {f : ℝ → ℝ} {L B : ℝ} (hf : IsBddLip f L B) :
    LipschitzWith ⟨L, hf.const_nonneg⟩ f := by
  refine LipschitzWith.of_dist_le_mul (fun x y => ?_)
  rw [Real.dist_eq, Real.dist_eq]
  exact hf.lip x y

theorem IsBddLip.continuous {f : ℝ → ℝ} {L B : ℝ} (hf : IsBddLip f L B) : Continuous f :=
  hf.lipschitzWith.continuous

theorem IsBddLip.le {f : ℝ → ℝ} {L B : ℝ} (hf : IsBddLip f L B) (x : ℝ) : f x ≤ B :=
  (le_abs_self _).trans (hf.bdd x)

/-! ### Clamped cutoffs

Two explicit Lipschitz cutoffs are needed: one descending across a point, used
to recover the distribution function, and one ascending away from a compact
interval, used for tightness.
-/

/-- The clamp of a real number to `[0,1]`. -/
def clamp01 (t : ℝ) : ℝ := min 1 (max 0 t)

theorem clamp01_nonneg (t : ℝ) : 0 ≤ clamp01 t :=
  le_min zero_le_one (le_max_left _ _)

theorem clamp01_le_one (t : ℝ) : clamp01 t ≤ 1 := min_le_left _ _

theorem clamp01_eq_one {t : ℝ} (ht : 1 ≤ t) : clamp01 t = 1 := by
  rw [clamp01, max_eq_right (le_trans zero_le_one ht), min_eq_left ht]

theorem clamp01_eq_zero {t : ℝ} (ht : t ≤ 0) : clamp01 t = 0 := by
  rw [clamp01, max_eq_left ht, min_eq_right zero_le_one]

theorem lipschitzWith_clamp01 : LipschitzWith 1 clamp01 :=
  (LipschitzWith.id.const_max 0).const_min 1

theorem continuous_clamp01 : Continuous clamp01 := lipschitzWith_clamp01.continuous

theorem abs_clamp01_sub_le (u v : ℝ) : |clamp01 u - clamp01 v| ≤ |u - v| := by
  simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using lipschitzWith_clamp01.dist_le_mul u v

/-- The descending cutoff: it equals `1` on `Iic a` and vanishes above
`a + (n+1)⁻¹`. -/
def iicCut (a : ℝ) (n : ℕ) (x : ℝ) : ℝ := clamp01 (1 - ((n : ℝ) + 1) * (x - a))

theorem iicCut_nonneg (a : ℝ) (n : ℕ) (x : ℝ) : 0 ≤ iicCut a n x := clamp01_nonneg _

theorem iicCut_le_one (a : ℝ) (n : ℕ) (x : ℝ) : iicCut a n x ≤ 1 := clamp01_le_one _

theorem iicCut_eq_one {a : ℝ} (n : ℕ) {x : ℝ} (hx : x ≤ a) : iicCut a n x = 1 := by
  refine clamp01_eq_one ?_
  have : ((n : ℝ) + 1) * (x - a) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
  linarith

theorem iicCut_eq_zero {a : ℝ} {n : ℕ} {x : ℝ} (hx : 1 ≤ ((n : ℝ) + 1) * (x - a)) :
    iicCut a n x = 0 :=
  clamp01_eq_zero (by linarith)

theorem isBddLip_iicCut (a : ℝ) (n : ℕ) : IsBddLip (iicCut a n) ((n : ℝ) + 1) 1 := by
  refine ⟨?_, fun x y => ?_, fun x => ?_⟩
  · exact continuous_clamp01.comp (by fun_prop) |>.measurable
  · have h := abs_clamp01_sub_le (1 - ((n : ℝ) + 1) * (x - a)) (1 - ((n : ℝ) + 1) * (y - a))
    have heq : 1 - ((n : ℝ) + 1) * (x - a) - (1 - ((n : ℝ) + 1) * (y - a))
        = -(((n : ℝ) + 1) * (x - y)) := by ring
    rw [heq, abs_neg, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)] at h
    exact h
  · rw [abs_of_nonneg (iicCut_nonneg a n x)]
    exact iicCut_le_one a n x

theorem tendsto_iicCut (a x : ℝ) :
    Tendsto (fun n : ℕ => iicCut a n x) atTop (𝓝 ((Iic a).indicator (fun _ => (1 : ℝ)) x)) := by
  rcases le_or_gt x a with hx | hx
  · rw [indicator_of_mem (mem_Iic.mpr hx)]
    refine Tendsto.congr (fun n => (iicCut_eq_one n hx).symm) tendsto_const_nhds
  · rw [indicator_of_notMem (by simp only [mem_Iic, not_le]; exact hx)]
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / (x - a))
    refine tendsto_atTop_of_eventually_const (i₀ := N) (fun n hn => ?_)
    refine iicCut_eq_zero ?_
    have hxa : 0 < x - a := by linarith
    have hNle : (1 : ℝ) / (x - a) < (n : ℝ) + 1 := by
      have : (N : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hn
      linarith
    calc (1 : ℝ) = (1 / (x - a)) * (x - a) := by field_simp
      _ ≤ ((n : ℝ) + 1) * (x - a) := by
          exact mul_le_mul_of_nonneg_right hNle.le hxa.le

/-! ### Bounded Lipschitz functions determine a finite measure -/

theorem tendsto_integral_iicCut (ρ : Measure ℝ) [IsFiniteMeasure ρ] (a : ℝ) :
    Tendsto (fun n : ℕ => ∫ x, iicCut a n x ∂ρ) atTop (𝓝 (ρ.real (Iic a))) := by
  have hlim : (∫ x, (Iic a).indicator (fun _ => (1 : ℝ)) x ∂ρ) = ρ.real (Iic a) :=
    integral_indicator_one measurableSet_Iic
  rw [← hlim]
  refine tendsto_integral_of_dominated_convergence (bound := fun _ => (1 : ℝ))
    (fun n => (isBddLip_iicCut a n).meas.aestronglyMeasurable) (integrable_const 1)
    (fun n => Eventually.of_forall (fun x => ?_)) (Eventually.of_forall (fun x => ?_))
  · rw [Real.norm_eq_abs, abs_of_nonneg (iicCut_nonneg a n x)]
    exact iicCut_le_one a n x
  · exact tendsto_iicCut a x

/-- The class of `app:limit`: nonnegative bounded Lipschitz functions with sup
norm at most one already determine a finite Borel measure on the line. -/
theorem ext_of_forall_integral_isBddLip_eq {ν₁ ν₂ : Measure ℝ}
    [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂]
    (h : ∀ (L : ℝ) (f : ℝ → ℝ), IsBddLip f L 1 → (∀ x, 0 ≤ f x) →
      (∫ x, f x ∂ν₁) = ∫ x, f x ∂ν₂) :
    ν₁ = ν₂ := by
  refine Measure.ext_of_Iic ν₁ ν₂ (fun a => ?_)
  have hreal : ν₁.real (Iic a) = ν₂.real (Iic a) := by
    refine tendsto_nhds_unique (tendsto_integral_iicCut ν₁ a) ?_
    refine Tendsto.congr (fun n => ?_) (tendsto_integral_iicCut ν₂ a)
    exact (h ((n : ℝ) + 1) (iicCut a n) (isBddLip_iicCut a n) (iicCut_nonneg a n)).symm
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top ν₁ _) (measure_ne_top ν₂ _)).mp hreal

/-! ### Tightness of a weakly convergent family -/

/-- The ascending cutoff away from a centred interval: it vanishes on
`|x| ≤ C` and equals `1` for `|x| ≥ C+1`. -/
def farCut (C : ℝ) (x : ℝ) : ℝ := clamp01 (|x| - C)

theorem farCut_nonneg (C x : ℝ) : 0 ≤ farCut C x := clamp01_nonneg _

theorem farCut_le_one (C x : ℝ) : farCut C x ≤ 1 := clamp01_le_one _

theorem continuous_farCut (C : ℝ) : Continuous (farCut C) :=
  continuous_clamp01.comp (continuous_abs.sub continuous_const)

theorem farCut_eq_zero {C x : ℝ} (hx : |x| ≤ C) : farCut C x = 0 :=
  clamp01_eq_zero (by linarith)

theorem farCut_eq_one {C x : ℝ} (hx : C + 1 ≤ |x|) : farCut C x = 1 :=
  clamp01_eq_one (by linarith)

theorem measurableSet_abs_gt (C : ℝ) : MeasurableSet {x : ℝ | C < |x|} :=
  measurableSet_lt measurable_const continuous_abs.measurable

theorem indicator_one_nonneg (S : Set ℝ) (x : ℝ) : 0 ≤ S.indicator (fun _ => (1 : ℝ)) x :=
  Set.indicator_nonneg (fun _ _ => zero_le_one) x

theorem indicator_one_le_one (S : Set ℝ) (x : ℝ) : S.indicator (fun _ => (1 : ℝ)) x ≤ 1 := by
  by_cases h : x ∈ S
  · rw [Set.indicator_of_mem h]
  · rw [Set.indicator_of_notMem h]
    exact zero_le_one

/-- Beyond `C+1` the cutoff dominates the indicator. -/
theorem measureReal_abs_gt_le_integral_farCut (ρ : Measure ℝ) [IsFiniteMeasure ρ] (C : ℝ) :
    ρ.real {x : ℝ | C + 1 < |x|} ≤ ∫ x, farCut C x ∂ρ := by
  rw [← integral_indicator_one (measurableSet_abs_gt (C + 1))]
  refine integral_mono (Doeblin.integrable_bounded_reward ρ
      (measurable_one.indicator (measurableSet_abs_gt (C + 1)))
      (indicator_one_nonneg _) (indicator_one_le_one _))
    (Doeblin.integrable_bounded_reward ρ (continuous_farCut C).measurable
      (farCut_nonneg C) (farCut_le_one C)) (fun x => ?_)
  by_cases hx : x ∈ {x : ℝ | C + 1 < |x|}
  · rw [Set.indicator_of_mem hx]
    exact ge_of_eq (farCut_eq_one (by simpa using (le_of_lt hx)))
  · rw [Set.indicator_of_notMem hx]
    exact farCut_nonneg C x

/-- Below `C` the cutoff is dominated by the indicator. -/
theorem integral_farCut_le_measureReal_abs_gt (ρ : Measure ℝ) [IsFiniteMeasure ρ] (C : ℝ) :
    (∫ x, farCut C x ∂ρ) ≤ ρ.real {x : ℝ | C < |x|} := by
  rw [← integral_indicator_one (measurableSet_abs_gt C)]
  refine integral_mono (Doeblin.integrable_bounded_reward ρ (continuous_farCut C).measurable
      (farCut_nonneg C) (farCut_le_one C))
    (Doeblin.integrable_bounded_reward ρ
      (measurable_one.indicator (measurableSet_abs_gt C))
      (indicator_one_nonneg _) (indicator_one_le_one _)) (fun x => ?_)
  by_cases hx : x ∈ {x : ℝ | C < |x|}
  · rw [Set.indicator_of_mem hx]
    exact farCut_le_one C x
  · rw [Set.indicator_of_notMem hx, farCut_eq_zero (by simpa using hx)]

/-- A finite measure on the line puts vanishing mass far from the origin. -/
theorem exists_measureReal_abs_gt_lt (ρ : Measure ℝ) [IsFiniteMeasure ρ] {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ρ.real {x : ℝ | C < |x|} < ε := by
  have hmono : Antitone (fun n : ℕ => {x : ℝ | (n : ℝ) < |x|}) := by
    intro m n hmn x hx
    have hx' : (n : ℝ) < |x| := hx
    exact lt_of_le_of_lt (Nat.cast_le.mpr hmn) hx'
  have hempty : (⋂ n : ℕ, {x : ℝ | (n : ℝ) < |x|}) = (∅ : Set ℝ) := by
    refine Set.eq_empty_iff_forall_notMem.mpr (fun x hx => ?_)
    obtain ⟨n, hn⟩ := exists_nat_gt |x|
    exact absurd (Set.mem_iInter.mp hx n) (by simpa using hn.le)
  have h := tendsto_measure_iInter_atTop (μ := ρ)
    (fun n : ℕ => (measurableSet_abs_gt (n : ℝ)).nullMeasurableSet) hmono
    ⟨0, measure_ne_top ρ _⟩
  rw [hempty] at h
  simp only [measure_empty, Function.comp_def] at h
  have hreal : Tendsto (fun n : ℕ => ρ.real {x : ℝ | (n : ℝ) < |x|}) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).comp h
    simpa [Measure.real, Function.comp_def] using this
  obtain ⟨n, hn⟩ := (hreal.eventually (eventually_lt_nhds hε)).exists
  exact ⟨(n : ℝ), hn⟩

/-- A weakly convergent family of probability laws is eventually tight: all the
mass beyond one explicit level is eventually below any given error. -/
theorem exists_eventually_measureReal_abs_gt_le {ι : Type*} {l : Filter ι}
    {νs : ι → Measure ℝ} {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hνs : ∀ i, IsProbabilityMeasure (νs i))
    (hweak : ∀ (g : ℝ → ℝ) (C : ℝ), Continuous g → (∀ x, |g x| ≤ C) →
      Tendsto (fun i => ∫ x, g x ∂(νs i)) l (𝓝 (∫ x, g x ∂ν)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ᶠ i in l, (νs i).real {x : ℝ | C < |x|} ≤ ε := by
  obtain ⟨C, hC⟩ := exists_measureReal_abs_gt_lt ν hε
  refine ⟨C + 1, ?_⟩
  have hlim := hweak (farCut C) 1 (continuous_farCut C)
    (fun x => by rw [abs_of_nonneg (farCut_nonneg C x)]; exact farCut_le_one C x)
  have hlt : (∫ x, farCut C x ∂ν) < ε :=
    lt_of_le_of_lt (integral_farCut_le_measureReal_abs_gt ν C) hC
  filter_upwards [hlim.eventually (eventually_lt_nhds hlt)] with i hi
  let : IsProbabilityMeasure (νs i) := hνs i
  exact le_of_lt (lt_of_le_of_lt (measureReal_abs_gt_le_integral_farCut (νs i) C) hi)

/-! ### The invariant-law limit transfer -/

theorem integral_le_of_le_one {ρ : Measure ℝ} [IsProbabilityMeasure ρ] {f : ℝ → ℝ}
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) :
    (∫ x, f x ∂ρ) ≤ 1 := by
  simpa using (Doeblin.integral_bounded_reward ρ hf hf0 hf1).2

theorem integrable_of_abs_le_one {ρ : Measure ℝ} [IsFiniteMeasure ρ] {f : ℝ → ℝ}
    (hf : Measurable f) (hf1 : ∀ x, |f x| ≤ 1) : Integrable f ρ := by
  refine (integrable_const (1 : ℝ)).mono' hf.aestronglyMeasurable
    (ae_of_all _ (fun x => ?_))
  simpa only [Real.norm_eq_abs] using hf1 x

theorem measurable_kernel_integral {K : Kernel ℝ ℝ} [IsMarkovKernel K] {f : ℝ → ℝ}
    (hf : Measurable f) : Measurable (fun r => ∫ y, f y ∂(K r)) := by
  have hsm : StronglyMeasurable (fun p : ℝ × ℝ => f p.2) :=
    (hf.comp measurable_snd).stronglyMeasurable
  exact (hsm.integral_kernel_prod_right' (κ := K)).measurable

theorem isProbabilityMeasure_bind {K : Kernel ℝ ℝ} [IsMarkovKernel K] (ν : Measure ℝ)
    [IsProbabilityMeasure ν] : IsProbabilityMeasure (ν.bind ⇑K) := by
  refine ⟨?_⟩
  rw [Measure.bind_apply MeasurableSet.univ (Kernel.aemeasurable K)]
  simp

/-- The integral of a bounded nonnegative function against `ν.bind K` is the
`ν`-average of the transition integrals. -/
theorem integral_bind_of_bounded {K : Kernel ℝ ℝ} [IsMarkovKernel K]
    {ν : Measure ℝ} [IsFiniteMeasure ν] {f : ℝ → ℝ} (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) {B : ℝ} (hfB : ∀ x, f x ≤ B) :
    (∫ y, f y ∂(ν.bind ⇑K)) = ∫ r, (∫ y, f y ∂(K r)) ∂ν := by
  have hL : (∫ y, f y ∂(ν.bind ⇑K)) = (∫⁻ y, ENNReal.ofReal (f y) ∂(ν.bind ⇑K)).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hf0) hf.aestronglyMeasurable
  have hR : (∫ r, (∫ y, f y ∂(K r)) ∂ν)
      = (∫⁻ r, ENNReal.ofReal (∫ y, f y ∂(K r)) ∂ν).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall (fun _ => integral_nonneg hf0))
      (measurable_kernel_integral hf).aestronglyMeasurable
  rw [hL, hR]
  congr 1
  have hb := Measure.lintegral_bind (μ := ⇑K) (m := ν)
    (Kernel.aemeasurable K) (ENNReal.measurable_ofReal.comp hf).aemeasurable
  simp only [Function.comp_apply] at hb
  rw [hb]
  exact (lintegral_congr fun r => KernelUnique.kernel_integral_eq_toReal hf hf0 hfB r).symm

/-- The error made by replacing one bounded test integral by another: the
uniform bound on a centred interval plus the mass outside it. -/
theorem abs_integral_sub_le_of_unif {ρ : Measure ℝ} [IsProbabilityMeasure ρ]
    {u v : ℝ → ℝ} (hu : Measurable u) (hv : Measurable v)
    (hu1 : ∀ r, |u r| ≤ 1) (hv1 : ∀ r, |v r| ≤ 1)
    {C δ : ℝ} (hδ : 0 ≤ δ) (hclose : ∀ r : ℝ, |r| ≤ C → |u r - v r| ≤ δ) :
    |(∫ r, u r ∂ρ) - ∫ r, v r ∂ρ| ≤ δ + 2 * ρ.real {x : ℝ | C < |x|} := by
  set S : Set ℝ := {x : ℝ | C < |x|} with hS
  have hSmeas : MeasurableSet S := measurableSet_abs_gt C
  have huint : Integrable u ρ := integrable_of_abs_le_one hu hu1
  have hvint : Integrable v ρ := integrable_of_abs_le_one hv hv1
  have hdint : Integrable (fun r => |u r - v r|) ρ := (huint.sub hvint).abs
  have hindint : Integrable (S.indicator (fun _ => (1 : ℝ))) ρ :=
    (integrable_const (1 : ℝ)).indicator hSmeas
  have hbint : Integrable (fun r => δ + 2 * S.indicator (fun _ => (1 : ℝ)) r) ρ :=
    (integrable_const δ).add (hindint.const_mul 2)
  have hpt : ∀ r : ℝ, |u r - v r| ≤ δ + 2 * S.indicator (fun _ => (1 : ℝ)) r := by
    intro r
    by_cases hr : |r| ≤ C
    · have hmem : r ∉ S := by
        simp only [hS, Set.mem_ofPred_eq, not_lt]
        exact hr
      rw [Set.indicator_of_notMem hmem]
      simpa using hclose r hr
    · have hmem : r ∈ S := by
        simp only [hS, Set.mem_ofPred_eq]
        exact lt_of_not_ge hr
      rw [Set.indicator_of_mem hmem]
      have h2 : |u r - v r| ≤ 2 := by
        calc |u r - v r| ≤ |u r| + |v r| := abs_sub _ _
          _ ≤ 2 := by linarith [hu1 r, hv1 r]
      linarith
  have hindval : (∫ r, S.indicator (fun _ => (1 : ℝ)) r ∂ρ) = ρ.real S :=
    integral_indicator_one hSmeas
  have hval : (∫ r, (δ + 2 * S.indicator (fun _ => (1 : ℝ)) r) ∂ρ) = δ + 2 * ρ.real S := by
    rw [integral_add (integrable_const δ) (hindint.const_mul 2), integral_const,
      integral_const_mul, hindval]
    simp
  calc |(∫ r, u r ∂ρ) - ∫ r, v r ∂ρ| = |∫ r, (u r - v r) ∂ρ| := by
        rw [integral_sub huint hvint]
    _ ≤ ∫ r, |u r - v r| ∂ρ := abs_integral_le_integral_abs
    _ ≤ ∫ r, (δ + 2 * S.indicator (fun _ => (1 : ℝ)) r) ∂ρ := integral_mono hdint hbint hpt
    _ = δ + 2 * ρ.real S := hval

/-- `app:limit`: the invariant-law limit transfer.  If each `νs i` is invariant
for `Ks i`, the laws converge weakly to `ν`, the bounded Lipschitz test
integrals of `Ks i` converge to those of `K` uniformly on bounded sets of
incoming margins, and `Kf` is continuous for every bounded Lipschitz `f`, then
`ν` is invariant for `K`. -/
theorem invariant_of_kernel_tendsto {ι : Type*} {l : Filter ι} [l.NeBot]
    {K : Kernel ℝ ℝ} [IsMarkovKernel K] {Ks : ι → Kernel ℝ ℝ}
    (hKs : ∀ i, IsMarkovKernel (Ks i))
    {νs : ι → Measure ℝ} (hνs : ∀ i, IsProbabilityMeasure (νs i))
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hinv : ∀ i, (Ks i).Invariant (νs i))
    (hweak : ∀ (g : ℝ → ℝ) (C : ℝ), Continuous g → (∀ x, |g x| ≤ C) →
      Tendsto (fun i => ∫ x, g x ∂(νs i)) l (𝓝 (∫ x, g x ∂ν)))
    (hcont : ∀ (f : ℝ → ℝ) (L B : ℝ), IsBddLip f L B →
      Continuous (fun r => ∫ y, f y ∂(K r)))
    (hunif : ∀ (f : ℝ → ℝ) (L B : ℝ), IsBddLip f L B → ∀ (C ε : ℝ), 0 < ε →
      ∀ᶠ i in l, ∀ r : ℝ, |r| ≤ C →
        |(∫ y, f y ∂(Ks i r)) - (∫ y, f y ∂(K r))| ≤ ε) :
    K.Invariant ν := by
  have key : ∀ (L : ℝ) (f : ℝ → ℝ), IsBddLip f L 1 → (∀ x, 0 ≤ f x) →
      (∫ r, (∫ y, f y ∂(K r)) ∂ν) = ∫ x, f x ∂ν := by
    intro L f hf hf0
    have hf1 : ∀ x, f x ≤ 1 := fun x => hf.le x
    have hΨmeas : Measurable (fun r => ∫ y, f y ∂(K r)) := measurable_kernel_integral hf.meas
    have hΨabs : ∀ r : ℝ, |∫ y, f y ∂(K r)| ≤ 1 := by
      intro r
      rw [abs_of_nonneg (integral_nonneg hf0)]
      exact integral_le_of_le_one hf.meas hf0 hf1
    have hΦmeas : ∀ i, Measurable (fun r => ∫ y, f y ∂(Ks i r)) := by
      intro i
      let : IsMarkovKernel (Ks i) := hKs i
      exact measurable_kernel_integral hf.meas
    have hΦabs : ∀ i, ∀ r : ℝ, |∫ y, f y ∂(Ks i r)| ≤ 1 := by
      intro i r
      let : IsMarkovKernel (Ks i) := hKs i
      rw [abs_of_nonneg (integral_nonneg hf0)]
      exact integral_le_of_le_one hf.meas hf0 hf1
    have hid : ∀ i, (∫ r, (∫ y, f y ∂(Ks i r)) ∂(νs i)) = ∫ x, f x ∂(νs i) := by
      intro i
      let : IsMarkovKernel (Ks i) := hKs i
      let : IsProbabilityMeasure (νs i) := hνs i
      exact KernelUnique.integral_kernel_of_invariant (hinv i) hf.meas hf0 hf1
    have hlim1 : Tendsto (fun i => ∫ x, f x ∂(νs i)) l (𝓝 (∫ x, f x ∂ν)) :=
      hweak f 1 hf.continuous hf.bdd
    have hlim2 : Tendsto (fun i => ∫ r, (∫ y, f y ∂(K r)) ∂(νs i)) l
        (𝓝 (∫ r, (∫ y, f y ∂(K r)) ∂ν)) :=
      hweak _ 1 (hcont f L 1 hf) hΨabs
    have herr : Tendsto (fun i => (∫ r, (∫ y, f y ∂(Ks i r)) ∂(νs i))
        - ∫ r, (∫ y, f y ∂(K r)) ∂(νs i)) l (𝓝 0) := by
      rw [NormedAddGroup.tendsto_nhds_zero]
      intro ε hε
      obtain ⟨C, hC⟩ := exists_eventually_measureReal_abs_gt_le hνs hweak
        (show (0 : ℝ) < ε/8 by linarith)
      filter_upwards [hC, hunif f L 1 hf C (ε/2) (by linarith)] with i hCi hui
      let : IsMarkovKernel (Ks i) := hKs i
      let : IsProbabilityMeasure (νs i) := hνs i
      rw [Real.norm_eq_abs]
      calc |(∫ r, (∫ y, f y ∂(Ks i r)) ∂(νs i)) - ∫ r, (∫ y, f y ∂(K r)) ∂(νs i)|
            ≤ ε/2 + 2 * (νs i).real {x : ℝ | C < |x|} :=
            abs_integral_sub_le_of_unif (hΦmeas i) hΨmeas (hΦabs i) hΨabs
              (by linarith : (0 : ℝ) ≤ ε/2) hui
        _ ≤ ε/2 + 2*(ε/8) := by linarith [hCi]
        _ < ε := by linarith
    have hlim3 : Tendsto (fun i => ∫ x, f x ∂(νs i)) l
        (𝓝 (∫ r, (∫ y, f y ∂(K r)) ∂ν)) := by
      have hsum := hlim2.add herr
      rw [add_zero] at hsum
      exact Tendsto.congr hid (Tendsto.congr (fun i => by ring) hsum)
    exact tendsto_nhds_unique hlim3 hlim1
  let : IsProbabilityMeasure (ν.bind ⇑K) := isProbabilityMeasure_bind ν
  show ν.bind ⇑K = ν
  refine ext_of_forall_integral_isBddLip_eq (fun L f hf hf0 => ?_)
  rw [integral_bind_of_bounded hf.meas hf0 (fun x => hf.le x)]
  exact key L f hf hf0

/-! ### From tightness to the weak limit

Prokhorov's theorem turns tightness into a cluster point; the transfer above
identifies every cluster point with the invariant law of `K`; uniqueness then
upgrades the cluster point to a limit.
-/

/-- A continuous bounded function read as a bounded continuous map. -/
def ofContinuousBounded {g : ℝ → ℝ} {B : ℝ} (hg : Continuous g) (hgB : ∀ x, |g x| ≤ B) :
    BoundedContinuousFunction ℝ ℝ where
  toFun := g
  continuous_toFun := hg
  map_bounded' := ⟨2*B, fun x y => by
    rw [Real.dist_eq]
    calc |g x - g y| ≤ |g x| + |g y| := abs_sub _ _
      _ ≤ 2*B := by linarith [hgB x, hgB y]⟩

@[simp] theorem ofContinuousBounded_apply {g : ℝ → ℝ} {B : ℝ} (hg : Continuous g)
    (hgB : ∀ x, |g x| ≤ B) (x : ℝ) : ofContinuousBounded hg hgB x = g x := rfl

theorem tendsto_integral_of_tendsto {ι : Type*} {l : Filter ι}
    {νs : ι → ProbabilityMeasure ℝ} {ν : ProbabilityMeasure ℝ} (h : Tendsto νs l (𝓝 ν))
    (g : ℝ → ℝ) (B : ℝ) (hg : Continuous g) (hgB : ∀ x, |g x| ≤ B) :
    Tendsto (fun i => ∫ x, g x ∂(νs i : Measure ℝ)) l (𝓝 (∫ x, g x ∂(ν : Measure ℝ))) := by
  have h' := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp h
    (ofContinuousBounded hg hgB)
  simpa using h'

/-- Every cluster point of the invariant laws is invariant for the limit kernel. -/
theorem invariant_of_mapClusterPt {ι : Type*} {l : Filter ι} [l.NeBot]
    {K : Kernel ℝ ℝ} [IsMarkovKernel K] {Ks : ι → Kernel ℝ ℝ}
    (hKs : ∀ i, IsMarkovKernel (Ks i))
    {νs : ι → ProbabilityMeasure ℝ} {ν : ProbabilityMeasure ℝ}
    (hinv : ∀ i, (Ks i).Invariant (νs i : Measure ℝ))
    (hcont : ∀ (f : ℝ → ℝ) (L B : ℝ), IsBddLip f L B →
      Continuous (fun r => ∫ y, f y ∂(K r)))
    (hunif : ∀ (f : ℝ → ℝ) (L B : ℝ), IsBddLip f L B → ∀ (C ε : ℝ), 0 < ε →
      ∀ᶠ i in l, ∀ r : ℝ, |r| ≤ C →
        |(∫ y, f y ∂(Ks i r)) - (∫ y, f y ∂(K r))| ≤ ε)
    (hcl : MapClusterPt ν l νs) :
    K.Invariant (ν : Measure ℝ) := by
  have hne : (l ⊓ comap νs (𝓝 ν)).NeBot := by
    rw [Filter.neBot_inf_comap_iff_map, inf_comm]
    exact hcl.clusterPt
  let : (l ⊓ comap νs (𝓝 ν)).NeBot := hne
  have htend : Tendsto νs (l ⊓ comap νs (𝓝 ν)) (𝓝 ν) :=
    le_trans (map_mono inf_le_right) Filter.map_comap_le
  exact invariant_of_kernel_tendsto (l := l ⊓ comap νs (𝓝 ν)) hKs (fun _ => inferInstance) hinv
    (fun g C hg hgC => tendsto_integral_of_tendsto htend g C hg hgC) hcont
    (fun f L B hf C ε hε => (hunif f L B hf C ε hε).filter_mono inf_le_left)

/-- `eq:marginweaklimit`: a tight family of invariant laws whose kernels
converge to `K` uniformly on bounded sets of margins converges weakly to the
unique invariant law of `K`, which in particular exists. -/
theorem exists_invariant_tendsto {ι : Type*} {l : Filter ι} [l.NeBot]
    {K : Kernel ℝ ℝ} [IsMarkovKernel K] {Ks : ι → Kernel ℝ ℝ}
    (hKs : ∀ i, IsMarkovKernel (Ks i))
    {νs : ι → ProbabilityMeasure ℝ}
    (hinv : ∀ i, (Ks i).Invariant (νs i : Measure ℝ))
    (htight : IsTightMeasureSet {m : Measure ℝ | ∃ i, m = (νs i : Measure ℝ)})
    (hcont : ∀ (f : ℝ → ℝ) (L B : ℝ), IsBddLip f L B →
      Continuous (fun r => ∫ y, f y ∂(K r)))
    (hunif : ∀ (f : ℝ → ℝ) (L B : ℝ), IsBddLip f L B → ∀ (C ε : ℝ), 0 < ε →
      ∀ᶠ i in l, ∀ r : ℝ, |r| ≤ C →
        |(∫ y, f y ∂(Ks i r)) - (∫ y, f y ∂(K r))| ≤ ε)
    (huniq : ∀ ν₁ ν₂ : Measure ℝ, IsProbabilityMeasure ν₁ → IsProbabilityMeasure ν₂ →
      K.Invariant ν₁ → K.Invariant ν₂ → ν₁ = ν₂) :
    ∃ ν : ProbabilityMeasure ℝ, K.Invariant (ν : Measure ℝ) ∧ Tendsto νs l (𝓝 ν) := by
  have hsets : {((μ : ProbabilityMeasure ℝ) : Measure ℝ) | μ ∈ Set.range νs}
      = {m : Measure ℝ | ∃ i, m = (νs i : Measure ℝ)} := by
    ext m
    constructor
    · rintro ⟨μ, ⟨i, hi⟩, hμ⟩
      exact ⟨i, by rw [← hμ, hi]⟩
    · rintro ⟨i, hi⟩
      exact ⟨νs i, ⟨i, rfl⟩, hi.symm⟩
  have hcomp : IsCompact (closure (Set.range νs)) :=
    isCompact_closure_of_isTightMeasureSet (by rw [hsets]; exact htight)
  have hmem : ∀ᶠ i in l, νs i ∈ closure (Set.range νs) :=
    Eventually.of_forall (fun i => subset_closure ⟨i, rfl⟩)
  obtain ⟨ν, -, hνcl⟩ := hcomp.exists_clusterPt (f := map νs l) (le_principal_iff.mpr hmem)
  have hinvν : K.Invariant (ν : Measure ℝ) :=
    invariant_of_mapClusterPt hKs hinv hcont hunif hνcl
  refine ⟨ν, hinvν, hcomp.tendsto_nhds_of_unique_mapClusterPt hmem (fun μ _ hμ => ?_)⟩
  exact ProbabilityMeasure.toMeasure_injective
    (huniq _ _ inferInstance inferInstance
      (invariant_of_mapClusterPt hKs hinv hcont hunif hμ) hinvν)

/-! ### Tightness from a uniform first absolute moment -/

theorem compl_Icc_eq_abs_gt (C : ℝ) : (Icc (-C) C)ᶜ = {x : ℝ | C < |x|} := by
  ext x
  constructor
  · intro hx
    exact lt_of_not_ge (fun hc => hx (mem_Icc.mpr (abs_le.mp hc)))
  · intro hx hc
    exact absurd (abs_le.mpr (mem_Icc.mp hc)) (not_le.mpr hx)

/-- Mathlib's tightness for a family of laws on the line, from a uniform bound
on the mass far from the origin. -/
theorem isTightMeasureSet_of_measure_abs_gt {ι : Type*} {νs : ι → ProbabilityMeasure ℝ}
    (h : ∀ ε : ℝ≥0∞, 0 < ε → ∃ C : ℝ, ∀ i, (νs i : Measure ℝ) {x : ℝ | C < |x|} ≤ ε) :
    IsTightMeasureSet {m : Measure ℝ | ∃ i, m = (νs i : Measure ℝ)} := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  obtain ⟨C, hC⟩ := h ε hε
  refine ⟨Icc (-C) C, isCompact_Icc, ?_⟩
  rintro m ⟨i, rfl⟩
  rw [compl_Icc_eq_abs_gt C]
  exact hC i

/-- Markov's inequality makes a uniform first absolute moment a uniform tail
bound: this is how Theorem 4.2 supplies the tightness of the invariant laws. -/
theorem exists_measure_abs_gt_le_of_moment {ι : Type*} {νs : ι → ProbabilityMeasure ℝ}
    {M : ℝ≥0∞} (hMtop : M ≠ ⊤)
    (hbd : ∀ i, (∫⁻ x, ENNReal.ofReal |x| ∂(νs i : Measure ℝ)) ≤ M)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ i, (νs i : Measure ℝ) {x : ℝ | C < |x|} ≤ ε := by
  rcases eq_or_ne ε ⊤ with hεtop | hεtop
  · exact ⟨0, fun i => by rw [hεtop]; exact le_top⟩
  have hεpos : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hεtop
  set C : ℝ := M.toReal / ε.toReal + 1 with hCdef
  have hCpos : 0 < C := by
    have : 0 ≤ M.toReal / ε.toReal := div_nonneg ENNReal.toReal_nonneg hεpos.le
    rw [hCdef]; linarith
  have hprod : M ≤ ε * ENNReal.ofReal C := by
    have hval : ε.toReal * C = M.toReal + ε.toReal := by
      rw [hCdef]
      field_simp
    calc M = ENNReal.ofReal M.toReal := (ENNReal.ofReal_toReal hMtop).symm
      _ ≤ ENNReal.ofReal (ε.toReal * C) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [hval]
          linarith
      _ = ENNReal.ofReal ε.toReal * ENNReal.ofReal C :=
          ENNReal.ofReal_mul ENNReal.toReal_nonneg
      _ = ε * ENNReal.ofReal C := by rw [ENNReal.ofReal_toReal hεtop]
  refine ⟨C, fun i => ?_⟩
  have hsub : {x : ℝ | C < |x|} ⊆ {x : ℝ | ENNReal.ofReal C ≤ ENNReal.ofReal |x|} := by
    intro x hx
    exact ENNReal.ofReal_le_ofReal (le_of_lt hx)
  have hmarkov := meas_ge_le_lintegral_div
    (μ := (νs i : Measure ℝ)) (f := fun x => ENNReal.ofReal |x|)
    (ENNReal.measurable_ofReal.comp continuous_abs.measurable).aemeasurable
    (by simpa using hCpos) ENNReal.ofReal_ne_top
  calc (νs i : Measure ℝ) {x : ℝ | C < |x|}
      ≤ (νs i : Measure ℝ) {x : ℝ | ENNReal.ofReal C ≤ ENNReal.ofReal |x|} :=
        measure_mono hsub
    _ ≤ (∫⁻ x, ENNReal.ofReal |x| ∂(νs i : Measure ℝ)) / ENNReal.ofReal C := hmarkov
    _ ≤ M / ENNReal.ofReal C := by
        exact ENNReal.div_le_div_right (hbd i) _
    _ ≤ ε := ENNReal.div_le_of_le_mul hprod

end KernelLimit
end SwingRepair
