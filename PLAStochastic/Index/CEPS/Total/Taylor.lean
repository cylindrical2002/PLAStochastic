import PLAStochastic.Index.CEPS.Total.LevelBound
import PLAStochastic.Index.CEPS.Total.LevelTaylor
import PLAStochastic.Index.CEPS.Glue.Defs

/-! # The fixed-window Taylor interface for the class-independent actual normal transform -/

noncomputable section
open Complex MeasureTheory
namespace PGM

theorem cepsNormalTaylor : CepsNormalTaylor cepsNormalGn cepsNormalDn := by
  have hlev := ceps_taylor_level
  choose K e hK he hbd using hlev
  refine ⟨cepsLevelOrder, fun D θ vlo vhi η _hD hθ hvlo _hvv hη => ⟨1, one_pos, ?_⟩⟩
  obtain ⟨N, hN⟩ := cepsInputClass_levelIndex_bound (D := D) (vhi := vhi)
    hθ hvlo hη (le_refl cepsLevelOrder)
  let S := Finset.range (N + 1)
  let Kmax := ∑ n ∈ S, K n
  let emax := ∑ n ∈ S, e n
  refine ⟨Kmax, 1, emax, one_pos, 5, ?_⟩
  intro eps heps ν hν y hy
  obtain ⟨hlevel, hnN⟩ := hN ν hν
  let n := cepsLevelIndex ν
  have hnS : n ∈ S := Finset.mem_range.mpr (Nat.lt_succ_of_le hnN)
  have hKle : K n ≤ Kmax := Finset.single_le_sum (fun i _ => hK i) hnS
  have hele : e n ≤ emax := Finset.single_le_sum (fun i _ => zero_le_one.trans (he i)) hnS
  have heps1 : 1 ≤ eps := (he n).trans (hele.trans heps)
  have hmain := hbd n eps (hele.trans heps) ν hlevel y hy
  change ‖cepsScaledTrueNormalExpression (cepsLevelDomain n)
    ((ν : Measure ℝ).map fun x => 1 - x) (2 * eps)⁻¹ (cepsLevelCutoff n) (I * y) - 1 -
      (I * y) * cepsScaledTrueNormalSlope (cepsLevelDomain n)
        ((ν : Measure ℝ).map fun x => 1 - x) (2 * eps)⁻¹ (cepsLevelCutoff n)‖ ≤ _
  apply hmain.trans
  gcongr

end PGM
