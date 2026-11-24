import PLAStochastic.Index.CEPS.Total.LevelMean
import PLAStochastic.Index.CEPS.Total.LevelDensity
import PLAStochastic.Index.CEPS.Total.LevelBound

/-! # The fixed normal slope has a raw arbitrary-order mean expansion on every input class

The coefficients remain indexed by a contour and approximation order. Finite
jet identification is a separate obligation.
-/

noncomputable section
open Complex MeasureTheory PowerSeries Finset
namespace PGM

theorem ceps_normal_mean_raw_expansion (P : ℕ) :
    ∃ m : ℕ, ∀ D θ vlo vhi η : ℝ,
      0 < D → 0 < θ → 0 < vlo → vlo ≤ vhi → ∀ hη : 0 < η,
      ∃ r : ℝ, 0 < r ∧ ∃ K eps₀ : ℝ, ∀ eps : ℝ, eps₀ ≤ eps →
        ∀ ν : ProbabilityMeasure ℝ, CepsInputClass D θ vlo vhi m η r ν →
          ‖cepsNormalDn eps ν + ∑ j ∈ range (P + 1), ((((2 * eps)⁻¹) ^ j : ℝ) : ℂ) *
            coeff j (cepsScaledMeanSeries ((cepsLevelDomain (cepsLevelIndex ν)).contour η hη)
              ((ν : Measure ℝ).map fun x => 1 - x) P)‖ ≤ K * (eps⁻¹) ^ (P + 1) := by
  let m := max cepsLevelOrder (P + 3)
  refine ⟨m, fun D θ vlo vhi η _hD hθ hvlo _hv hη => ⟨1, one_pos, ?_⟩⟩
  let M' := Real.exp η * (cepsSobolev m η cepsLambdaDensity + 1)
  have hM' : 0 ≤ M' := mul_nonneg (Real.exp_pos _).le
    (by linarith [cepsSobolev_nonneg m η cepsLambdaDensity])
  have hlev := fun n => ceps_mean_level n P hη hM'
  choose K e hK he H using hlev
  obtain ⟨N, hN⟩ := cepsInputClass_levelIndex_bound (D := D) (vhi := vhi)
    hθ hvlo hη (le_max_left _ _)
  let S := range (N + 1)
  let Kmax := ∑ n ∈ S, K n
  let emax := ∑ n ∈ S, e n
  refine ⟨Kmax, emax, fun eps heps ν hν => ?_⟩
  obtain ⟨hlevel, hnN⟩ := hN ν hν
  let n := cepsLevelIndex ν
  have hnS : n ∈ S := mem_range.mpr (Nat.lt_succ_of_le hnN)
  have hKle : K n ≤ Kmax := single_le_sum (fun i _ => hK i) hnS
  have hele : e n ≤ emax := single_le_sum (fun i _ => zero_le_one.trans (he i)) hnS
  have heps1 : 1 ≤ eps := (he n).trans (hele.trans heps)
  obtain ⟨f, hf0, hf, hνf, hdist⟩ := hν.density
  have hLD := hlevel.of_continuous_density hf.contDiff.continuous hf0 hνf
  have hfW := hf.one_sub hη.le
  have hfM' : cepsSobolev m η (fun x => f (1 - x)) ≤ M' := by
    apply (cepsSobolev_one_sub_le hf hη.le).trans
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    have hadd := cepsSobolev_add_le hν.reference (hf.sub hν.reference)
    have heq : (fun x => cepsLambdaDensity x + (f x - cepsLambdaDensity x)) = f := by
      funext x
      ring
    rw [heq] at hadd
    linarith
  have hmP : P + 3 ≤ m := le_max_right _ _
  have hmain := H n eps (hele.trans heps) ν f hLD (hfW.mono_order hmP)
    ((cepsSobolev_mono_order hmP η (fun x => f (1 - x))).trans hfM')
  change ‖cepsScaledTrueNormalSlope (cepsLevelDomain n)
      ((ν : Measure ℝ).map fun x => 1 - x) (2 * eps)⁻¹ (cepsLevelCutoff n) + _‖ ≤ _
  apply hmain.trans
  exact mul_le_mul_of_nonneg_right hKle (pow_nonneg (inv_nonneg.mpr (zero_le_one.trans heps1)) _)

end PGM
