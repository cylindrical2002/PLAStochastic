import PLAStochastic.Index.CEPS.Normal.HalfLineDerivative

/-! # The invariant actual discount denominators in (P12) and (F10) -/

noncomputable section
open Complex MeasureTheory
open PGM.WienerHopf
namespace PGM

/-- (P6), for the actual `cepsD`; no root or factor theorem is used. -/
theorem cepsNormal_discount_marked (ρW : Measure ℝ) (μ t : ℂ) :
    cepsD ρW μ (t * (1 + μ)) t = 1 - exp (-t) * stepTransform ρW t := by
  rw [cepsD, ← exp_add]
  have he : -(t * (1 + μ)) + μ * t = -t := by ring
  rw [he]

theorem cepsNormal_discount_marked_hasDerivAt (ρW : Measure ℝ) (μ : ℝ) (t : ℂ) :
    HasDerivAt (fun x : ℝ => cepsD ρW x (t * (1 + (x : ℂ))) t) 0 μ := by
  have he : (fun x : ℝ => cepsD ρW x (t * (1 + (x : ℂ))) t) =
      fun _ : ℝ => 1 - exp (-t) * stepTransform ρW t := by
    funext x
    exact cepsNormal_discount_marked ρW x t
  rw [he]
  exact hasDerivAt_const _ _

theorem cepsNormal_discount_fixed (ρW : Measure ℝ) (μ q : ℂ) :
    cepsD ρW μ q 0 = 1 - exp (-q) * stepTransform ρW 0 := by
  simp [cepsD]

theorem cepsNormal_discount_fixed_hasDerivAt (ρW : Measure ℝ) (μ : ℝ) (q : ℂ) :
    HasDerivAt (fun x : ℝ => cepsD ρW x q 0) 0 μ := by
  have he : (fun x : ℝ => cepsD ρW x q 0) =
      fun _ : ℝ => 1 - exp (-q) * stepTransform ρW 0 := by
    funext x
    exact cepsNormal_discount_fixed ρW x q
  rw [he]
  exact hasDerivAt_const _ _

end PGM
