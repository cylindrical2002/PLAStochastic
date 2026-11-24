import PLAStochastic.Index.CEPS.Scaled.KernelNormalJets
import PLAStochastic.Index.CEPS.Total.LevelBound
import PLAStochastic.Index.CEPS.Total.LevelDensity
import PLAStochastic.Index.CEPS.Jets.Consistency
import PLAStochastic.Index.CEPS.Glue.Defs

/-! # Finite kernel coefficients on the original least-level input classes -/

noncomputable section
open Complex MeasureTheory PowerSeries Finset
open PGM.WienerHopf
namespace PGM

attribute [local irreducible] cepsLevelDomain

/-- One class radius identifies all coefficients up to the requested order, on the original
least level and every positive high-order Sobolev contour. -/
theorem ceps_normal_series_coefficients_eq_kernel (N : ℕ) {m : ℕ}
    (hm6 : cepsLevelOrder ≤ m) (hmN : N + 3 ≤ m)
    (D θ vlo vhi η : ℝ) (hθ : 0 < θ) (hvlo : 0 < vlo) (hη : 0 < η) :
    ∃ r : ℝ, 0 < r ∧ ∀ ν : ProbabilityMeasure ℝ,
      CepsInputClass D θ vlo vhi m η r ν → ∀ j ≤ N, ∀ y : ℝ,
        coeff j (cepsScaledNormalSeries
            ((cepsLevelDomain (cepsLevelIndex ν)).contour η hη)
            ((ν : Measure ℝ).map fun x => 1 - x) N (I * y)) =
          cepsKernelNormalCoeffJetModel (cepsJetLaw ν) j (I * y) ∧
        coeff j (cepsScaledMeanSeries
            ((cepsLevelDomain (cepsLevelIndex ν)).contour η hη)
            ((ν : Measure ℝ).map fun x => 1 - x) N) =
          cepsKernelMeanCoeffJetModel (cepsJetLaw ν) j := by
  classical
  obtain ⟨L, hL⟩ := cepsInputClass_levelIndex_bound (D := D) (vhi := vhi) hθ hvlo hη hm6
  have hcoeff := fun n => cepsScaledNormalMeanCoefficients_eq_finite_model
    ((cepsLevelDomain n).contour η hη) (cepsLevelRate_pos n) (cepsLevelStepD_pos n)
  choose r hr H using hcoeff
  let S := range (L + 1)
  have hS : S.Nonempty := ⟨0, by simp [S]⟩
  let rmin := S.inf' hS r
  have hrmin : 0 < rmin := (lt_inf'_iff hS).mpr fun n _ => hr n
  refine ⟨min 1 rmin, lt_min one_pos hrmin, fun ν hν j hj y => ?_⟩
  have hν1 := hν.mono (le_refl m) (min_le_left _ _)
  obtain ⟨hlevel, hn⟩ := hL ν hν1
  obtain ⟨f, hf0, hf, hνf, hdist⟩ := hν.density
  have hLD := hlevel.of_continuous_density hf.contDiff.continuous hf0 hνf
  obtain ⟨-, -, hW, -, -⟩ := hLD.stepLaw
  have hneg : ∀ x, x < 0 → f x = 0 := fun x hx => hLD.2.2.1 x hx.le
  have hfW := hf.one_sub hη.le
  have hηc := (cepsLevelDomain (cepsLevelIndex ν)).two_contour_c₀_le hη
  have hL1 : ∫ x, |f x - cepsLambdaDensity x| ≤ r (cepsLevelIndex ν) := by
    have h0 := (hf.sub hν.reference).integral_abs_iteratedDeriv_le hη.le (Nat.zero_le m)
    simp only [iteratedDeriv_zero] at h0
    exact h0.trans (hdist.trans ((min_le_right _ _).trans
      (inf'_le r (mem_range.mpr (Nat.lt_succ_of_le hn)))))
  have hmodel := H (cepsLevelIndex ν) hW (fun _ => rfl) hneg hη hf hfW hηc hL1
    j (by omega) (by simp : 0 ≤ (I * (y : ℂ)).re)
  rw [← cepsJetLaw_eq_cepsJet hf.contDiff.continuous.measurable hf0 hνf] at hmodel
  have hnormal := cepsScaledNormalSeries_coeff_eq_diagonal
    ((cepsLevelDomain (cepsLevelIndex ν)).contour η hη) hW
    (cepsLevelRate_pos _) (cepsLevelStepD_pos _) hfW hηc (le_refl _)
    N hmN (by simp : (I * (y : ℂ)).re = 0) j hj
  have hmean := cepsScaledMeanSeries_coeff_eq_diagonal
    ((cepsLevelDomain (cepsLevelIndex ν)).contour η hη) hW
    (cepsLevelRate_pos _) (cepsLevelStepD_pos _) hfW hηc (le_refl _) N hmN j hj
  exact ⟨hnormal.trans hmodel.1, hmean.trans hmodel.2⟩

end PGM
