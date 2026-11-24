import PLAStochastic.ForMathlib.Probability.CDF.PositivePartMean
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Integrating a joint CDF along a triangle

Tonelli turns the integral of the joint CDF into a positive-part expectation
of the sum. This avoids any assumption that the joint law has a density.
-/

noncomputable section
open MeasureTheory Set Filter Classical
open scoped ENNReal Topology

namespace BrownianAffine

set_option backward.isDefEq.respectTransparency false

def jointCDFENN (ν : Measure (ℝ × ℝ)) (a b : ℝ) : ℝ≥0∞ :=
  ν {p | p.1 ≤ a ∧ p.2 ≤ b}

theorem measurableSet_jointCDF (a b : ℝ) : MeasurableSet {p : ℝ × ℝ | p.1 ≤ a ∧ p.2 ≤ b} :=
  (measurableSet_le measurable_fst measurable_const).inter
    (measurableSet_le measurable_snd measurable_const)

theorem jointCDFENN_eq_lintegral (ν : Measure (ℝ × ℝ)) (a b : ℝ) :
    jointCDFENN ν a b = ∫⁻ p : ℝ × ℝ, if p.1 ≤ a ∧ p.2 ≤ b then (1 : ℝ≥0∞) else 0 ∂ν := by
  symm
  simpa only [jointCDFENN, indicator_apply, mem_ofPred_eq, Pi.one_apply] using
    (lintegral_indicator_one (μ := ν) (measurableSet_jointCDF a b))

private theorem measurable_triangle_indicator (s : ℝ) :
    Measurable (fun q : ℝ × (ℝ × ℝ) =>
      if q.2.1 ≤ q.1 ∧ q.2.2 ≤ s - q.1 then (1 : ℝ≥0∞) else 0) := by
  apply Measurable.ite _ measurable_const measurable_const
  exact (measurableSet_le (measurable_fst.comp measurable_snd) measurable_fst).inter
    (measurableSet_le (measurable_snd.comp measurable_snd) (measurable_const.sub measurable_fst))

theorem measurable_jointCDF_triangle (ν : Measure (ℝ × ℝ)) [SFinite ν] (s : ℝ) :
    Measurable (fun a => jointCDFENN ν a (s - a)) := by
  simp only [jointCDFENN_eq_lintegral]
  apply Measurable.lintegral_prod_right
  exact measurable_triangle_indicator s

/-- Every point contributes the length of its admissible interval of split locations. -/
theorem lintegral_jointCDF_triangle (ν : Measure (ℝ × ℝ)) [SFinite ν] (s : ℝ) :
    (∫⁻ a : ℝ, jointCDFENN ν a (s - a)) =
      ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (max (s - (p.1 + p.2)) 0) ∂ν := by
  simp only [jointCDFENN_eq_lintegral]
  rw [lintegral_lintegral_swap (measurable_triangle_indicator s).aemeasurable]
  apply lintegral_congr
  intro p
  have he : (fun a : ℝ => if p.1 ≤ a ∧ p.2 ≤ s - a then (1 : ℝ≥0∞) else 0) =
      (Icc p.1 (s - p.2)).indicator 1 := by
    funext a
    simp only [indicator_apply, mem_Icc, Pi.one_apply]
    congr 1
    apply propext
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  rw [he, lintegral_indicator_one measurableSet_Icc, Real.volume_Icc]
  rw [ENNReal.ofReal_max, ENNReal.ofReal_zero, max_eq_left zero_le]
  congr 1
  ring

theorem integral_jointCDF_triangle_all (ν : Measure (ℝ × ℝ)) [IsFiniteMeasure ν] (s : ℝ) :
    (∫ a : ℝ, (jointCDFENN ν a (s - a)).toReal) =
      positivePartMean (ν.map (fun p => p.1 + p.2)) s := by
  have hm : Measurable (fun p : ℝ × ℝ => max (s - (p.1 + p.2)) 0) := by fun_prop
  have he := congrArg ENNReal.toReal (lintegral_jointCDF_triangle ν s)
  rw [← integral_toReal (measurable_jointCDF_triangle ν s).aemeasurable
    (Eventually.of_forall (fun a => measure_lt_top ν _)),
    ← integral_eq_lintegral_of_nonneg_ae
      (Eventually.of_forall (fun p : ℝ × ℝ => le_max_right (s - (p.1 + p.2)) 0))
      hm.aestronglyMeasurable] at he
  rw [he]
  exact (integral_map (μ := ν) (φ := fun p : ℝ × ℝ => p.1 + p.2)
    (by fun_prop) (f := fun x : ℝ => max (s - x) 0) (by fun_prop)).symm

theorem jointCDF_triangle_zero_outside (ν : Measure (ℝ × ℝ))
    (hν : ∀ᵐ p ∂ν, 0 ≤ p.1 ∧ 0 ≤ p.2) {s a : ℝ} (ha : a ∉ Icc 0 s) :
    jointCDFENN ν a (s - a) = 0 := by
  change ν {p | p.1 ≤ a ∧ p.2 ≤ s - a} = 0
  calc
    _ = ν ∅ := by
      apply measure_congr
      filter_upwards [hν] with p hp
      apply propext
      change (p.1 ≤ a ∧ p.2 ≤ s - a) ↔ False
      constructor
      · intro h
        exact ha ⟨by linarith [hp.1, h.1], by linarith [hp.2, h.2]⟩
      · exact False.elim
    _ = 0 := measure_empty

/-- The finite triangle integral for any nonnegative joint law. -/
theorem integral_jointCDF_triangle (ν : Measure (ℝ × ℝ)) [IsFiniteMeasure ν]
    (hν : ∀ᵐ p ∂ν, 0 ≤ p.1 ∧ 0 ≤ p.2) {s : ℝ} (hs : 0 ≤ s) :
    (∫ a : ℝ in 0..s, (jointCDFENN ν a (s - a)).toReal) =
      positivePartMean (ν.map (fun p => p.1 + p.2)) s := by
  rw [intervalIntegral.integral_of_le hs, ← integral_Icc_eq_integral_Ioc]
  calc
    _ = ∫ a : ℝ, (jointCDFENN ν a (s - a)).toReal :=
      setIntegral_eq_integral_of_forall_compl_eq_zero (fun a ha => by
        rw [jointCDF_triangle_zero_outside ν hν ha, ENNReal.toReal_zero])
    _ = _ := integral_jointCDF_triangle_all ν s

end BrownianAffine
