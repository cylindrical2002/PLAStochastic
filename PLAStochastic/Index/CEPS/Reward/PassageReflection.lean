import PLAStochastic.Index.CEPS.Reward.Passage
import PLAStochastic.ForMathlib.Probability.RandomWalk.WienerHopf.Reflection

/-! # Strict downcrossing rewards from path reflection -/

noncomputable section
open MeasureTheory Set Complex
namespace PGM.WienerHopf

/-- The overshoot below `-x` is `-S_tau - x`; infinite times contribute zero. -/
def descendingPassageReward (s a : ℂ) (x : ℝ) (ω : ℕ → ℝ) : ℂ :=
  if firstEntry (Iio (-x)) ω < ⊤ then
    s ^ (firstEntry (Iio (-x)) ω).toNat *
      cexp (-a * (-entryValue (Iio (-x)) ω - x : ℝ))
  else 0

def descendingPassageTransform (ρ : Measure ℝ) (s a : ℂ) (x : ℝ) : ℂ :=
  ∫ ω, descendingPassageReward s a x ω ∂pathLaw ρ

theorem passageReward_reflectPath (s a : ℂ) (x : ℝ) (ω : ℕ → ℝ) :
    passageReward s a x (reflectPath ω) = descendingPassageReward s a x ω := by
  have hs : Neg.neg ⁻¹' Ioi x = Iio (-x) := by
    ext y
    simp only [mem_preimage, mem_Ioi, mem_Iio]
    constructor <;> intro h <;> linarith
  simp only [passageReward, firstEntry_reflectPath, entryValue_reflectPath, hs,
    descendingPassageReward]

theorem descendingPassageTransform_eq_reflected {ρ : Measure ℝ} [IsProbabilityMeasure ρ]
    (s a : ℂ) (x : ℝ) :
    descendingPassageTransform ρ s a x = passageTransform (ρ.map Neg.neg) s a x := by
  have hf : Measurable (passageReward s a x) :=
    (measurable_passageReward s a).comp (measurable_const.prodMk measurable_id)
  rw [passageTransform, ← pathLaw_map_reflectPath ρ,
    integral_map measurable_reflectPath.aemeasurable hf.aestronglyMeasurable]
  simp only [descendingPassageTransform, passageReward_reflectPath]

end PGM.WienerHopf
