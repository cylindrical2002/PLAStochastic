import PLAStochastic.Affine.Moments.Optimal.Slope.Range
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Coarea for the actual slope range

The two strict monotone branches are derived from convexity and the attained
minimum. Change of variables removes the null set of nondifferentiability both
in the domain and its image; the latter uses the global Lipschitz bound.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace BrownianAffine

def slopeLeft (g : Path 1) : ℝ := sInf (slopeMinimizers g)
def slopeRight (g : Path 1) : ℝ := sSup (slopeMinimizers g)

theorem slopeRange_left (g : Path 1) : slopeRange g (slopeLeft g) = slopeMinimum g :=
  slopeMinimizers_left_mem g

theorem slopeRange_right (g : Path 1) : slopeRange g (slopeRight g) = slopeMinimum g :=
  slopeMinimizers_right_mem g

theorem slopeLeft_le_right (g : Path 1) : slopeLeft g ≤ slopeRight g :=
  slopeMinimizers_endpoints_ordered g

theorem slopeRange_gt_minimum_left (g : Path 1) {a : ℝ} (ha : a < slopeLeft g) :
    slopeMinimum g < slopeRange g a := by
  refine lt_of_le_of_ne (slopeMinimum_le g a) ?_
  intro heq
  have hm : a ∈ slopeMinimizers g := heq.symm
  rw [slopeMinimizers_eq_Icc] at hm
  exact (not_le.mpr ha) hm.1

theorem slopeRange_gt_minimum_right (g : Path 1) {a : ℝ} (ha : slopeRight g < a) :
    slopeMinimum g < slopeRange g a := by
  refine lt_of_le_of_ne (slopeMinimum_le g a) ?_
  intro heq
  have hm : a ∈ slopeMinimizers g := heq.symm
  rw [slopeMinimizers_eq_Icc] at hm
  exact (not_le.mpr ha) hm.2

/-- The entire left branch, including its minimizing endpoint, is strictly decreasing. -/
theorem slopeRange_strictAntiOn_left (g : Path 1) :
    StrictAntiOn (slopeRange g) (Iic (slopeLeft g)) := by
  intro x _ y hy hxy
  rcases lt_or_eq_of_le (show y ≤ slopeLeft g from hy) with hy | rfl
  · apply (convexOn_slopeRange g).lt_left_of_right_lt (mem_univ x) (mem_univ _)
    · rw [openSegment_eq_Ioo (hxy.trans hy)]
      exact ⟨hxy, hy⟩
    · rw [slopeRange_left]
      exact slopeRange_gt_minimum_left g hy
  · rw [slopeRange_left]
    exact slopeRange_gt_minimum_left g hxy

/-- The entire right branch, including its minimizing endpoint, is strictly increasing. -/
theorem slopeRange_strictMonoOn_right (g : Path 1) :
    StrictMonoOn (slopeRange g) (Ici (slopeRight g)) := by
  intro x hx y _ hxy
  rcases lt_or_eq_of_le (show slopeRight g ≤ x from hx) with hx | rfl
  · apply (convexOn_slopeRange g).lt_right_of_left_lt (mem_univ _) (mem_univ y)
    · rw [openSegment_eq_Ioo (hx.trans hxy)]
      exact ⟨hx, hxy⟩
    · rw [slopeRange_right]
      exact slopeRange_gt_minimum_right g hx
  · rw [slopeRange_right]
    exact slopeRange_gt_minimum_right g hxy

theorem slopeRange_image_left (g : Path 1) :
    slopeRange g '' Iio (slopeLeft g) = Ioi (slopeMinimum g) := by
  simpa only [slopeRange_left] using
    (continuous_slopeRange g).continuousOn.image_Iio_of_strictAntiOn
      (slopeRange_strictAntiOn_left g) (slopeRange_tendsto_atBot g)

theorem slopeRange_image_right (g : Path 1) :
    slopeRange g '' Ioi (slopeRight g) = Ioi (slopeMinimum g) := by
  simpa only [slopeRange_right] using
    (continuous_slopeRange g).continuousOn.image_Ioi_of_strictMonoOn
      (slopeRange_strictMonoOn_right g) (slopeRange_tendsto_atTop g)

theorem slopeRange_deriv_zero_between (g : Path 1) {a : ℝ}
    (ha : a ∈ Ioo (slopeLeft g) (slopeRight g)) : deriv (slopeRange g) a = 0 := by
  have he : slopeRange g =ᶠ[𝓝 a] fun _ => slopeMinimum g := by
    filter_upwards [isOpen_Ioo.mem_nhds ha] with b hb
    have hm : b ∈ slopeMinimizers g := by
      rw [slopeMinimizers_eq_Icc]
      exact ⟨hb.1.le, hb.2.le⟩
    exact hm
  rw [he.deriv_eq, deriv_const]

/-- A Lipschitz real map sends Lebesgue-null sets to Lebesgue-null sets. -/
theorem lipschitz_real_image_null {f : ℝ → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    {s : Set ℝ} (hs : volume s = 0) : volume (f '' s) = 0 := by
  have h := hf.hausdorffMeasure_image_le (d := 1) (by norm_num) s
  simpa only [hausdorffMeasure_real, hs, mul_zero, nonpos_iff_eq_zero] using h

/-- One-dimensional change of variables for an injective branch of a Lipschitz map.
The derivative is required only almost everywhere, as supplied by Rademacher. -/
theorem lintegral_image_lipschitz_injOn {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) {s : Set ℝ} (hs : MeasurableSet s) (hinj : InjOn f s)
    (h : ℝ → ℝ≥0∞) :
    ∫⁻ r in f '' s, h r = ∫⁻ a in s, ENNReal.ofReal |deriv f a| * h (f a) := by
  have hbad : volume {a | ¬ DifferentiableAt ℝ f a} = 0 := by
    exact ae_iff.mp hf.ae_differentiableAt
  obtain ⟨N, hNsub, hNm, hN⟩ := exists_measurable_superset_of_null hbad
  have hNae : ∀ᵐ a ∂volume, a ∉ N := by
    exact measure_eq_zero_iff_ae_notMem.mp hN
  have hdom : s \ N =ᵐ[volume] s := by
    filter_upwards [hNae] with a ha
    change (a ∈ s \ N) = (a ∈ s)
    simp only [Set.mem_sdiff, ha, not_false_eq_true, and_true]
  have himN : volume (f '' N) = 0 := lipschitz_real_image_null hf hN
  have him : f '' (s \ N) =ᵐ[volume] f '' s := by
    have hae : ∀ᵐ r ∂volume, r ∉ f '' N := by
      exact measure_eq_zero_iff_ae_notMem.mp himN
    filter_upwards [hae] with r hr
    change (r ∈ f '' (s \ N)) = (r ∈ f '' s)
    apply propext
    constructor
    · exact fun hr => image_mono sdiff_subset hr
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a, ⟨ha, fun hna => hr ⟨a, hna, rfl⟩⟩, rfl⟩
  have hderiv : ∀ a ∈ s \ N, HasDerivWithinAt f (deriv f a) (s \ N) a := by
    intro a ha
    have hd : DifferentiableAt ℝ f a := by
      by_contra hn
      exact ha.2 (hNsub hn)
    exact hd.hasDerivAt.hasDerivWithinAt
  rw [← setLIntegral_congr him, lintegral_image_eq_lintegral_abs_deriv_mul
    (hs.diff hNm) hderiv (hinj.mono sdiff_subset) h]
  exact setLIntegral_congr hdom

theorem slopeRange_lintegral_left (g : Path 1) (h : ℝ → ℝ≥0∞) :
    ∫⁻ a in Iio (slopeLeft g), ENNReal.ofReal |deriv (slopeRange g) a| * h (slopeRange g a) =
      ∫⁻ r in Ioi (slopeMinimum g), h r := by
  rw [← slopeRange_image_left]
  exact (lintegral_image_lipschitz_injOn (slopeRange_lipschitz g) measurableSet_Iio
    ((slopeRange_strictAntiOn_left g).mono Iio_subset_Iic_self).injOn h).symm

theorem slopeRange_lintegral_right (g : Path 1) (h : ℝ → ℝ≥0∞) :
    ∫⁻ a in Ioi (slopeRight g), ENNReal.ofReal |deriv (slopeRange g) a| * h (slopeRange g a) =
      ∫⁻ r in Ioi (slopeMinimum g), h r := by
  rw [← slopeRange_image_right]
  exact (lintegral_image_lipschitz_injOn (slopeRange_lipschitz g) measurableSet_Ioi
    ((slopeRange_strictMonoOn_right g).mono Ioi_subset_Ici_self).injOn h).symm

theorem slopeRange_lintegral_minimizers (g : Path 1) (h : ℝ → ℝ≥0∞) :
    ∫⁻ a in Icc (slopeLeft g) (slopeRight g),
      ENNReal.ofReal |deriv (slopeRange g) a| * h (slopeRange g a) = 0 := by
  have hzero : ∀ᵐ a ∂volume, a ∈ Icc (slopeLeft g) (slopeRight g) →
      ENNReal.ofReal |deriv (slopeRange g) a| * h (slopeRange g a) = 0 := by
    filter_upwards [(countable_singleton (slopeLeft g)).ae_notMem volume,
      (countable_singleton (slopeRight g)).ae_notMem volume] with a hl hr ha
    simp only [mem_singleton_iff] at hl hr
    rw [slopeRange_deriv_zero_between g ⟨lt_of_le_of_ne ha.1 (Ne.symm hl),
      lt_of_le_of_ne ha.2 hr⟩]
    simp
  rw [setLIntegral_congr_fun_ae measurableSet_Icc hzero]
  simp

/-- The manuscript's nonnegative coarea identity, including the possible flat minimum.
Extended nonnegative integration also covers weights with infinite integral. -/
theorem slopeRange_coarea (g : Path 1) (h : ℝ → ℝ≥0∞) :
    ∫⁻ a, ENNReal.ofReal |deriv (slopeRange g) a| * h (slopeRange g a) =
      2 * ∫⁻ r in Ioi (slopeMinimum g), h r := by
  have hpartition : Iio (slopeLeft g) ∪ Icc (slopeLeft g) (slopeRight g) ∪
      Ioi (slopeRight g) = univ := by
    ext a
    simp only [mem_union, mem_Iio, mem_Icc, mem_Ioi, mem_univ, iff_true]
    have := slopeLeft_le_right g
    rcases lt_or_ge a (slopeLeft g) with ha | ha
    · exact Or.inl (Or.inl ha)
    · rcases le_or_gt a (slopeRight g) with hb | hb
      · exact Or.inl (Or.inr ⟨ha, hb⟩)
      · exact Or.inr hb
  have hd₁ : Disjoint (Iio (slopeLeft g)) (Icc (slopeLeft g) (slopeRight g)) := by
    apply Set.disjoint_left.mpr
    intro a ha hb
    exact (not_le.mpr ha) hb.1
  have hd₂ : Disjoint (Iio (slopeLeft g) ∪ Icc (slopeLeft g) (slopeRight g))
      (Ioi (slopeRight g)) := by
    apply Set.disjoint_left.mpr
    intro a ha hb
    rcases ha with ha | ha
    · exact (not_lt_of_ge ((le_of_lt ha).trans (slopeLeft_le_right g))) hb
    · exact (not_lt_of_ge ha.2) hb
  rw [← setLIntegral_univ, ← hpartition, lintegral_union measurableSet_Ioi hd₂,
    lintegral_union measurableSet_Icc hd₁, slopeRange_lintegral_left,
    slopeRange_lintegral_minimizers, slopeRange_lintegral_right, add_zero, two_mul]

/-- Finite real-valued coarea, with integrability of the slope integral deduced. -/
theorem slopeRange_coarea_integrable (g : Path 1) (h : ℝ → ℝ)
    (hh : Measurable h) (hn : ∀ r, slopeMinimum g ≤ r → 0 ≤ h r)
    (hi : IntegrableOn h (Ioi (slopeMinimum g))) :
    Integrable (fun a => |deriv (slopeRange g) a| * h (slopeRange g a)) ∧
      (∫ a, |deriv (slopeRange g) a| * h (slopeRange g a)) =
        2 * ∫ r in Ioi (slopeMinimum g), h r := by
  have hwm : Measurable (fun a => |deriv (slopeRange g) a| * h (slopeRange g a)) := by
    simpa only [Real.norm_eq_abs, Pi.mul_apply, Function.comp_apply] using!
      (measurable_deriv (slopeRange g)).norm.mul (hh.comp (continuous_slopeRange g).measurable)
  have hwn : ∀ a, 0 ≤ |deriv (slopeRange g) a| * h (slopeRange g a) := fun a =>
    mul_nonneg (abs_nonneg _) (hn _ (slopeMinimum_le g a))
  have hrn : 0 ≤ᵐ[volume.restrict (Ioi (slopeMinimum g))] h := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact hn r (le_of_lt hr)
  have heq : (∫⁻ a, ENNReal.ofReal (|deriv (slopeRange g) a| * h (slopeRange g a))) =
      2 * ∫⁻ r in Ioi (slopeMinimum g), ENNReal.ofReal (h r) := by
    simp_rw [ENNReal.ofReal_mul (abs_nonneg _)]
    exact slopeRange_coarea g (fun r => ENNReal.ofReal (h r))
  have hif : (∫⁻ r in Ioi (slopeMinimum g), ENNReal.ofReal (h r)) ≠ ⊤ :=
    (lintegral_ofReal_ne_top_iff_integrable hi.aestronglyMeasurable hrn).mpr hi
  constructor
  · apply (lintegral_ofReal_ne_top_iff_integrable hwm.aestronglyMeasurable
      (Eventually.of_forall hwn)).mp
    rw [heq]
    exact ENNReal.mul_ne_top (by norm_num) hif
  · rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hwn)
      hwm.aestronglyMeasurable, heq, ENNReal.toReal_mul,
      integral_eq_lintegral_of_nonneg_ae hrn hi.aestronglyMeasurable]
    norm_num

theorem slopeRange_integral_rpow (g : Path 1) (hρ : 0 < slopeMinimum g)
    {p : ℝ} (hp : p < -1) :
    Integrable (fun a => |deriv (slopeRange g) a| * slopeRange g a ^ p) ∧
      (∫ a, |deriv (slopeRange g) a| * slopeRange g a ^ p) =
        2 * (-slopeMinimum g ^ (p + 1) / (p + 1)) := by
  have h := slopeRange_coarea_integrable g (fun r => r ^ p)
    (measurable_id.pow_const p)
    (fun r hr => Real.rpow_nonneg (hρ.le.trans hr) p)
    (integrableOn_Ioi_rpow_of_lt hp hρ)
  rw [integral_Ioi_rpow_of_lt hp hρ] at h
  exact h

/-- The inverse-power specialization includes finiteness of the actual slope integral. -/
theorem slopeRange_coarea_power_of_minimum_pos (g : Path 1)
    (hρ : 0 < slopeMinimum g) {q : ℝ} (hq : 0 < q) :
    Integrable (fun a => |deriv (slopeRange g) a| / slopeRange g a ^ (2 * q + 1)) ∧
      optimalError g ^ (-2 * q) = (2 : ℝ) ^ (2 * q) * q *
        ∫ a, |deriv (slopeRange g) a| / slopeRange g a ^ (2 * q + 1) := by
  have h := slopeRange_integral_rpow g hρ (p := -2 * q - 1) (by linarith)
  have hfun : (fun a => |deriv (slopeRange g) a| * slopeRange g a ^ (-2 * q - 1)) =
      (fun a => |deriv (slopeRange g) a| / slopeRange g a ^ (2 * q + 1)) := by
    funext a
    rw [show -2 * q - 1 = -(2 * q + 1) by ring,
      Real.rpow_neg (slopeRange_nonnegative g a)]
    rfl
  rw [hfun] at h
  refine ⟨h.1, ?_⟩
  have hF : 0 < optimalError g := by
    rw [slopeMinimum_eq_two_optimal] at hρ
    linarith
  have htwo : (2 : ℝ) ^ (2 * q) ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) _).ne'
  have hscale : (2 : ℝ) ^ (2 * q) * slopeMinimum g ^ (-2 * q) =
      optimalError g ^ (-2 * q) := by
    rw [slopeMinimum_eq_two_optimal, Real.mul_rpow (by norm_num) hF.le,
      show -2 * q = -(2 * q) by ring, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    field_simp [htwo]
  rw [h.2, show -2 * q - 1 + 1 = -2 * q by ring]
  rw [← hscale]
  field_simp [hq.ne']

/-- The pathwise inverse-power formula in the manuscript, for every continuous nonaffine path. -/
theorem slopeRange_coarea_power (g : Path 1)
    (hg : ¬ ∃ a b : ℝ, g = a • timePath 1 + b • (1 : Path 1))
    {q : ℝ} (hq : 0 < q) :
    Integrable (fun a => |deriv (slopeRange g) a| / slopeRange g a ^ (2 * q + 1)) ∧
      optimalError g ^ (-2 * q) = (2 : ℝ) ^ (2 * q) * q *
        ∫ a, |deriv (slopeRange g) a| / slopeRange g a ^ (2 * q + 1) :=
  slopeRange_coarea_power_of_minimum_pos g (slopeMinimum_positive_of_not_affine g hg) hq

private theorem slopeResidual_slope_difference (g : Path 1) (a b : ℝ) (t : RangeTime) :
    slopeResidual g a t - slopeResidual g b t ≤ |a - b| := by
  have ht : |(t : ℝ)| ≤ 1 := by
    rw [abs_of_nonneg t.property.1]
    exact t.property.2
  calc
    slopeResidual g a t - slopeResidual g b t = (b - a) * (t : ℝ) := by
      unfold slopeResidual
      ring
    _ ≤ |(b - a) * (t : ℝ)| := le_abs_self _
    _ = |b - a| * |(t : ℝ)| := abs_mul _ _
    _ ≤ |b - a| * 1 := mul_le_mul_of_nonneg_left ht (abs_nonneg _)
    _ = |a - b| := by rw [mul_one, abs_sub_comm]

theorem slopeUpper_le_add_abs (g : Path 1) (a b : ℝ) :
    slopeUpper g a ≤ slopeUpper g b + |a - b| := by
  obtain ⟨t, ht⟩ := slopeUpper_attained g a
  have h₁ := slopeResidual_slope_difference g a b t
  have h₂ := slopeResidual_le_upper g b t
  linarith

theorem slopeLower_le_add_abs (g : Path 1) (a b : ℝ) :
    slopeLower g a ≤ slopeLower g b + |a - b| := by
  obtain ⟨t, ht⟩ := slopeLower_attained g b
  have h₁ := slopeResidual_slope_difference g a b t
  have h₂ := slopeLower_le_residual g a t
  linarith

private theorem lipschitzWith_one_of_le_add_abs {f : ℝ → ℝ}
    (hf : ∀ a b, f a ≤ f b + |a - b|) : LipschitzWith 1 f := by
  apply LipschitzWith.of_dist_le_mul
  intro a b
  simp only [Real.dist_eq, NNReal.coe_one, one_mul]
  rw [abs_le]
  have h₁ := hf a b
  have h₂ := hf b a
  rw [abs_sub_comm b a] at h₂
  constructor <;> linarith

theorem slopeUpper_lipschitz (g : Path 1) : LipschitzWith 1 (slopeUpper g) :=
  lipschitzWith_one_of_le_add_abs (slopeUpper_le_add_abs g)

theorem slopeLower_lipschitz (g : Path 1) : LipschitzWith 1 (slopeLower g) :=
  lipschitzWith_one_of_le_add_abs (slopeLower_le_add_abs g)

theorem hasDerivAt_slopeResidual_slope (g : Path 1) (a : ℝ) (t : RangeTime) :
    HasDerivAt (fun b => slopeResidual g b t) (-(t : ℝ)) a := by
  simpa only [slopeResidual, one_mul] using!
    ((hasDerivAt_id a).mul_const (t : ℝ)).const_sub (g t)

/-- At a differentiability slope, every maximizing time equals minus the upper derivative. -/
theorem slopeUpper_deriv_of_maximizer (g : Path 1) {a : ℝ}
    (ha : DifferentiableAt ℝ (slopeUpper g) a) {t : RangeTime}
    (ht : slopeResidual g a t = slopeUpper g a) : deriv (slopeUpper g) a = -(t : ℝ) := by
  have hm : IsLocalMin (fun b => slopeUpper g b - slopeResidual g b t) a := by
    apply Eventually.of_forall
    intro b
    have hb := slopeResidual_le_upper g b t
    change slopeUpper g a - slopeResidual g a t ≤ slopeUpper g b - slopeResidual g b t
    rw [ht, sub_self]
    linarith
  have hz := hm.hasDerivAt_eq_zero (ha.hasDerivAt.sub (hasDerivAt_slopeResidual_slope g a t))
  linarith

/-- The matching lower-envelope derivative statement uses an actual minimizing time. -/
theorem slopeLower_deriv_of_minimizer (g : Path 1) {a : ℝ}
    (ha : DifferentiableAt ℝ (slopeLower g) a) {t : RangeTime}
    (ht : slopeResidual g a t = slopeLower g a) : deriv (slopeLower g) a = -(t : ℝ) := by
  have hm : IsLocalMin (fun b => slopeResidual g b t - slopeLower g b) a := by
    apply Eventually.of_forall
    intro b
    have hb := slopeLower_le_residual g b t
    change slopeResidual g a t - slopeLower g a ≤ slopeResidual g b t - slopeLower g b
    rw [ht, sub_self]
    linarith
  have hz := hm.hasDerivAt_eq_zero ((hasDerivAt_slopeResidual_slope g a t).sub ha.hasDerivAt)
  linarith

/-- The upper and lower extrema are unique at almost every slope, and their times
give the derivative of the actual range. No probabilistic uniqueness assumption is used. -/
theorem slopeRange_ae_unique_extrema_deriv (g : Path 1) :
    ∀ᵐ a ∂volume,
      (∃! t : RangeTime, slopeResidual g a t = slopeUpper g a) ∧
      (∃! t : RangeTime, slopeResidual g a t = slopeLower g a) ∧
      ∀ s t : RangeTime, slopeResidual g a s = slopeUpper g a →
        slopeResidual g a t = slopeLower g a →
        deriv (slopeRange g) a = (t : ℝ) - (s : ℝ) := by
  filter_upwards [(slopeUpper_lipschitz g).ae_differentiableAt,
    (slopeLower_lipschitz g).ae_differentiableAt] with a hu hl
  constructor
  · obtain ⟨s, hs⟩ := slopeUpper_attained g a
    refine ⟨s, hs, ?_⟩
    intro t ht
    apply Subtype.ext
    have h₁ := slopeUpper_deriv_of_maximizer g hu hs
    have h₂ := slopeUpper_deriv_of_maximizer g hu ht
    linarith
  constructor
  · obtain ⟨s, hs⟩ := slopeLower_attained g a
    refine ⟨s, hs, ?_⟩
    intro t ht
    apply Subtype.ext
    have h₁ := slopeLower_deriv_of_minimizer g hl hs
    have h₂ := slopeLower_deriv_of_minimizer g hl ht
    linarith
  · intro s t hs ht
    change deriv (slopeUpper g - slopeLower g) a = (t : ℝ) - (s : ℝ)
    rw [deriv_sub hu hl, slopeUpper_deriv_of_maximizer g hu hs,
      slopeLower_deriv_of_minimizer g hl ht]
    ring

end BrownianAffine
