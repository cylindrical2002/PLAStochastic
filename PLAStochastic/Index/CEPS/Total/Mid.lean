import PLAStochastic.Index.CEPS.Total.LevelBound
import PLAStochastic.Index.CEPS.Total.LevelMid
import PLAStochastic.Index.CEPS.Glue.Defs

/-! # C-11 for the fixed, class-independent normal transform -/

noncomputable section
open Complex MeasureTheory
namespace PGM

/-- The mid-frequency interface, with degree three and constants uniform over the input class. -/
theorem cepsNormalMid : CepsNormalMid cepsNormalGn := by
  have hlev := ceps_mid_level
  choose K c R e hK hc hR he hbd using hlev
  refine ⟨cepsLevelOrder, fun D θ vlo vhi η _hD hθ hvlo _hvv hη => ⟨1, one_pos, ?_⟩⟩
  obtain ⟨N, hN⟩ := cepsInputClass_levelIndex_bound (D := D) (vhi := vhi)
    hθ hvlo hη (le_refl cepsLevelOrder)
  set S := Finset.range (N + 1)
  have hS : S.Nonempty := ⟨0, by simp [S]⟩
  set Kmax := ∑ n ∈ S, K n
  set cmin := S.inf' hS c
  set Rmin := S.inf' hS R
  set emax := ∑ n ∈ S, e n
  have hKmax : 0 ≤ Kmax := Finset.sum_nonneg fun i _ => hK i
  have hcmin : 0 < cmin := (Finset.lt_inf'_iff hS).mpr fun n _ => hc n
  have hRmin : 0 < Rmin := (Finset.lt_inf'_iff hS).mpr fun n _ => hR n
  refine ⟨Kmax, cmin, 0, Rmin, emax, hcmin, hRmin, 3, ?_⟩
  intro eps heps ν hν y _hy0 hy
  obtain ⟨hlevel, hnN⟩ := hN ν hν
  set n := cepsLevelIndex ν
  have hnS : n ∈ S := Finset.mem_range.mpr (Nat.lt_succ_of_le hnN)
  have hKle : K n ≤ Kmax := Finset.single_le_sum (fun i _ => hK i) hnS
  have hele : e n ≤ emax := Finset.single_le_sum (fun i _ => (zero_le_one.trans (he i))) hnS
  have hcle : cmin ≤ c n := Finset.inf'_le _ hnS
  have hRle : Rmin ≤ R n := Finset.inf'_le _ hnS
  have hmain := hbd n eps (hele.trans heps) ν hlevel y
    (hy.trans (mul_le_mul_of_nonneg_right hRle (sq_nonneg eps)))
  change ‖cepsScaledTrueNormalExpression (cepsLevelDomain n)
    ((ν : Measure ℝ).map fun x => 1 - x) (2 * eps)⁻¹ (cepsLevelCutoff n) (I * y)‖ ≤ _
  refine hmain.trans ?_
  have hexp : Real.exp (-c n * Real.sqrt |y|) ≤ Real.exp (-cmin * Real.sqrt |y|) :=
    Real.exp_le_exp.mpr (by nlinarith [Real.sqrt_nonneg |y|])
  gcongr

end PGM
