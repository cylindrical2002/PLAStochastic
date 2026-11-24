import PLAStochastic.Index.KEP.Poisson.ArrivalTransform
import PLAStochastic.Index.Model.ExpConcentration

/-!
# The actual normalized first Poisson gap

Its law is the cumulative-intensity inverse applied to a fresh Exp(1) innovation.
The original intensity ratio bounds give a uniform exponential moment at one
fixed positive parameter, for every physical anchor and every positive intensity.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology

theorem kepPoissonNormalizedGap_continuous {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (n : ℝ) :
    Continuous (fun p : ℝ × ℝ => kepPoissonNormalizedGap hf n p.1 p.2) :=
  (continuous_const.mul (hf.continuous.comp continuous_fst)).mul
    ((kepPoissonArrival_continuous hf n).sub continuous_fst)

theorem kepPoissonNormalizedGap_bracket {f : ℝ → ℝ} {flo fhi L n t : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (hn : 0 < n) (ht : 0 ≤ t) (x : ℝ) :
    (flo / fhi) * t ≤ kepPoissonNormalizedGap hf n x t ∧
      kepPoissonNormalizedGap hf n x t ≤ (fhi / flo) * t := by
  have h := kepPoissonArrival_gap_bracket hf hn ht x
  have hfx := hf.f_pos x
  have hlo := hf.pos
  have hhi := hf.fhi_pos
  have hscale : 0 ≤ n * f x := by positivity
  have hehi : n * f x * (t / (n * flo)) = (f x / flo) * t := by
    field_simp [hn.ne', hlo.ne']
  have helo : n * f x * (t / (n * fhi)) = (f x / fhi) * t := by
    field_simp [hn.ne', hhi.ne']
  constructor
  · calc
      _ ≤ (f x / fhi) * t := mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (hf.lower x) hhi.le) ht
      _ = n * f x * (t / (n * fhi)) := helo.symm
      _ ≤ _ := mul_le_mul_of_nonneg_left h.1 hscale
  · calc
      _ ≤ n * f x * (t / (n * flo)) := mul_le_mul_of_nonneg_left h.2 hscale
      _ = (f x / flo) * t := hehi
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (hf.upper x) hlo.le) ht

theorem kepPoissonNormalizedGap_hasDerivAt {f : ℝ → ℝ} {flo fhi L n : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (hn : 0 < n) (x t : ℝ) :
    HasDerivAt (kepPoissonNormalizedGap hf n x)
      (f x / f (kepPoissonArrival hf n x t)) t := by
  have h := ((kepPoissonArrival_hasDerivAt hf n x t).sub_const x).const_mul (n * f x)
  change HasDerivAt (kepPoissonNormalizedGap hf n x)
    (n * f x * (1 / (n * f (kepPoissonArrival hf n x t)))) t at h
  have he : n * f x * (1 / (n * f (kepPoissonArrival hf n x t))) =
      f x / f (kepPoissonArrival hf n x t) := by
    field_simp [hn.ne', (hf.f_pos _).ne']
  rw [he] at h
  exact h

def kepPoissonBaseMeasure {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (n x : ℝ) : Measure ℝ :=
  (expMeasure 1).map (kepPoissonNormalizedGap hf n x)

theorem measurable_kepPoissonNormalizedGap {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (n x : ℝ) :
    Measurable (kepPoissonNormalizedGap hf n x) :=
  ((kepPoissonNormalizedGap_continuous hf n).comp
    (continuous_const.prodMk continuous_id)).measurable

instance isProbabilityMeasure_kepPoissonBaseMeasure {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (n x : ℝ) :
    IsProbabilityMeasure (kepPoissonBaseMeasure hf n x) :=
  Measure.isProbabilityMeasure_map (measurable_kepPoissonNormalizedGap hf n x).aemeasurable

theorem kepPoissonBaseMeasure_exponential_moment {f : ℝ → ℝ} {flo fhi L n theta : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (hn : 0 < n)
    (ht : 0 ≤ theta) (hcap : theta ≤ flo / (2 * fhi)) (x : ℝ) :
    Integrable (fun z => Real.exp (theta * z)) (kepPoissonBaseMeasure hf n x) ∧
      (∫ z, Real.exp (theta * z) ∂kepPoissonBaseMeasure hf n x) ≤ 2 := by
  have hlo := hf.pos
  have hhi := hf.fhi_pos
  have hc : theta * (fhi / flo) ≤ 1 / 2 := by
    have h := mul_le_mul_of_nonneg_right hcap (div_nonneg hhi.le hlo.le)
    have he : (flo / (2 * fhi)) * (fhi / flo) = (1 / 2 : ℝ) := by
      field_simp [hlo.ne', hhi.ne']
    rwa [he] at h
  have hb : ∀ᵐ t ∂expMeasure 1,
      Real.exp (theta * kepPoissonNormalizedGap hf n x t) ≤ Real.exp ((1 / 2) * t) := by
    filter_upwards [ae_pos_expMeasure_one] with t htpos
    apply Real.exp_le_exp.mpr
    calc
      _ ≤ theta * ((fhi / flo) * t) := mul_le_mul_of_nonneg_left
        (kepPoissonNormalizedGap_bracket hf hn htpos.le x).2 ht
      _ = (theta * (fhi / flo)) * t := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hc htpos.le
  have him : AEStronglyMeasurable
      (fun t : ℝ => Real.exp (theta * kepPoissonNormalizedGap hf n x t)) (expMeasure 1) :=
    (Real.measurable_exp.comp
    (measurable_const.mul (measurable_kepPoissonNormalizedGap hf n x))).aestronglyMeasurable
  have hi := (integrable_exp_mul_expMeasure (by norm_num : (1 / 2 : ℝ) < 1)).mono' him
    (hb.mono fun t h => by simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using h)
  have hm := measurable_kepPoissonNormalizedGap hf n x
  have hfun : Measurable (fun z : ℝ => Real.exp (theta * z)) := by fun_prop
  constructor
  · exact (integrable_map_measure hfun.aestronglyMeasurable hm.aemeasurable).mpr hi
  · rw [kepPoissonBaseMeasure, integral_map hm.aemeasurable hfun.aestronglyMeasurable]
    apply (integral_mono_ae hi (integrable_exp_mul_expMeasure (by norm_num)) hb).trans
    rw [integral_exp_mul_expMeasure (by norm_num : (1 / 2 : ℝ) < 1)]
    norm_num

end

end PGM
