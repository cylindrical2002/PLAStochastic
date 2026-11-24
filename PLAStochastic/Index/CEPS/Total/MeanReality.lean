import PLAStochastic.Index.CEPS.Total.MeanClose
import PLAStochastic.Index.CEPS.Total.LevelDensity
import PLAStochastic.Index.CEPS.Scaled.MeanLowScale
import PLAStochastic.ForMathlib.Analysis.Asymptotics.SeriesApproxReal

/-! # Reality of the genuine finite normal mean series on input classes

The original least level and cutoff remain fixed. The high-order coefficients
use a smaller contour at the input weight. Reality follows from the actual mean,
not from a formal replacement of the coefficients by their real parts.
-/

noncomputable section
open Complex MeasureTheory PowerSeries
open PGM.WienerHopf
namespace PGM

attribute [local irreducible] cepsLevelDomain

theorem ceps_normal_mean_series_real (P : ℕ) :
    ∃ m : ℕ, ∀ D θ vlo vhi η : ℝ,
      0 < D → 0 < θ → 0 < vlo → vlo ≤ vhi → ∀ hη : 0 < η,
      ∃ r : ℝ, 0 < r ∧ ∀ ν : ProbabilityMeasure ℝ,
        CepsInputClass D θ vlo vhi m η r ν → ∀ j ≤ P,
          (coeff j (cepsScaledMeanSeries
            ((cepsLevelDomain (cepsLevelIndex ν)).contour η hη)
              ((ν : Measure ℝ).map fun x => 1 - x) P)).im = 0 := by
  obtain ⟨m₀, hcl⟩ := ceps_normal_mean_close (P + 1)
  let m := max m₀ (max cepsLevelOrder (P + 3))
  refine ⟨m, fun D θ vlo vhi η hD hθ hvlo hv hη => ?_⟩
  obtain ⟨r₀, hr₀, L, S, Hclose⟩ := hcl D θ vlo vhi η hD hθ hvlo hv hη
  refine ⟨min r₀ 1, lt_min hr₀ one_pos, fun ν hν j hj => ?_⟩
  have hm6 : cepsLevelOrder ≤ m := (le_max_left _ _).trans (le_max_right _ _)
  have hmP : P + 3 ≤ m := (le_max_right _ _).trans (le_max_right _ _)
  have hν₀ := hν.mono (le_max_left _ _) (min_le_left _ _)
  have hν₁ := hν.mono (le_refl m) (min_le_right _ _)
  obtain ⟨N, hN⟩ := cepsInputClass_levelIndex_bound (D := D) (vhi := vhi) hθ hvlo hη hm6
  have hlevel := (hN ν hν₁).1
  obtain ⟨f, hf0, hf, hνf, hdist⟩ := hν₁.density
  have hLD := hlevel.of_continuous_density hf.contDiff.continuous hf0 hνf
  obtain ⟨-, -, hW, hf6, hM6⟩ := hLD.stepLaw
  let n := cepsLevelIndex ν
  let dom := cepsLevelDomain n
  let M := cepsLevelScale n
  let M' := Real.exp η * (cepsSobolev m η cepsLambdaDensity + 1)
  have hθn := cepsLevelRate_pos n
  have hDn := cepsLevelStepD_pos n
  have hM := (cepsLevelScale_pos n).le
  have hM' : 0 ≤ M' := mul_nonneg (Real.exp_pos _).le
    (by linarith [cepsSobolev_nonneg m η cepsLambdaDensity])
  have hfW := hf.one_sub hη.le
  have hfM' : cepsSobolev m η (fun x => f (1 - x)) ≤ M' := by
    apply (cepsSobolev_one_sub_le hf hη.le).trans
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    have hadd := cepsSobolev_add_le hν₁.reference (hf.sub hν₁.reference)
    have he : (fun x => cepsLambdaDensity x + (f x - cepsLambdaDensity x)) = f := by
      funext x
      ring
    rw [he] at hadd
    linarith
  have hδ : 0 < cepsLevelCutoff n := by
    have hbase := trueDecayScaleBase_pos dom hW hθn hDn hM
    unfold cepsLevelCutoff
    change 0 < min (min dom.renewalMu (dom.μ₀ / 8))
      (min (dom.trueDecayScaleBase M / 4) (1 / 2))
    exact lt_min (lt_min (dom.renewalMu_pos hDn) (by have := dom.μ₀_pos; positivity))
      (lt_min (by positivity) (by norm_num))
  obtain ⟨K, E, -, -, Hmean⟩ := cepsScaledTrueNormalSlope_contour_mean_expansion
    dom hW hθn hDn P hη hM hM' hδ (cepsLevelCutoff_le n).2.2.1
  apply halfScale_coeff_im_eq_zero_of_real_mean
    (f := fun eps => cepsNormalDn eps ν) (g := fun eps => lawC eps ν / eps ^ 2)
    (K := K) (L := L) (E := E) (S := S) _ (fun eps heps => Hclose eps heps ν hν₀) hj
  intro eps heps
  have ht := Hmean eps heps hW hf6 (cepsLevelDomain_two_c₀_le n) hM6
    (by norm_num [cepsLevelOrder]) hfW hfM' hmP
  simpa only [cepsNormalDn, truncEval, ofReal_pow, mul_comm] using ht

end PGM
