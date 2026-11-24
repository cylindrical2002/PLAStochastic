import PLAStochastic.ForMathlib.Probability.RandomWalk.WienerHopf.Reflection
import PLAStochastic.ForMathlib.Probability.RandomWalk.WienerHopf.AtomlessEntry

/-! # Entrance transforms under reflection of a step law -/

noncomputable section
open MeasureTheory ProbabilityTheory Set Complex
namespace PGM.WienerHopf

variable {ρ : Measure ℝ} [IsProbabilityMeasure ρ]

theorem entryTransform_map_neg {A : Set ℝ} (hA : MeasurableSet A) (s z : ℂ) :
    entryTransform (ρ.map Neg.neg) A s z = entryTransform ρ (Neg.neg ⁻¹' A) s (-z) := by
  have hf : Measurable (fun ω : ℕ → ℝ =>
      s ^ (firstEntry A ω).toNat * cexp (z * (entryValue A ω : ℂ))) :=
    ((Measurable.of_discrete (f := fun n : ℕ∞ => s ^ n.toNat)).comp
      (measurable_firstEntry hA)).mul
        (measurable_const.mul (Complex.measurable_ofReal.comp (measurable_entryValue hA))).cexp
  unfold entryTransform
  rw [← pathLaw_map_reflectPath ρ,
    setIntegral_map (measurableSet_firstEntry_lt_top hA) hf.aestronglyMeasurable
      measurable_reflectPath.aemeasurable]
  have hset : reflectPath ⁻¹' {ω | firstEntry A ω < ⊤} =
      {ω | firstEntry (Neg.neg ⁻¹' A) ω < ⊤} := by
    ext ω
    simp only [mem_preimage, mem_ofPred_eq, firstEntry_reflectPath]
  rw [hset]
  apply setIntegral_congr_fun (measurableSet_firstEntry_lt_top (hA.preimage measurable_neg))
  intro ω _
  dsimp only
  simp only [firstEntry_reflectPath, entryValue_reflectPath, ofReal_neg, mul_neg, neg_mul]

theorem ascTransform_map_neg_eq_desc {f : ℝ → ℝ} (hfm : Measurable f)
    (hρ : ρ = volume.withDensity (fun y => ENNReal.ofReal (f y))) (s z : ℂ) :
    ascTransform (ρ.map Neg.neg) s z = descTransform ρ s (-z) := by
  have hset : Neg.neg ⁻¹' Ioi (0 : ℝ) = Iio 0 := by
    ext x
    simp only [mem_preimage, mem_Ioi, mem_Iio, neg_pos]
  rw [ascTransform, entryTransform_map_neg measurableSet_Ioi, hset,
    ← entryTransform_Iic_eq_Iio hfm hρ]

end PGM.WienerHopf
