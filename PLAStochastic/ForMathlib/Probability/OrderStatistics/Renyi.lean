import PLAStochastic.ForMathlib.Probability.OrderStatistics.SortedUniform
import PLAStochastic.ForMathlib.Probability.OrderStatistics.GammaRatio
import Mathlib.Probability.IdentDistrib

/-!
# Rényi representation of uniform order statistics

For independent uniform `[0, 1]` variables `U 0, …, U (n-1)` and independent `Exp(1)` variables
`E 0, …, E n` with partial sums `Γ k = ∑_{i < k} E i`, the sorted vector `sortVec U` and the
ratio vector `(Γ 1 / Γ (n+1), …, Γ n / Γ (n+1))` have the same law, namely
`n! • volume.restrict (simplex n)`:

* `map_sortVec_uniform` (`PLAStochastic.ForMathlib.Probability.OrderStatistics.SortedUniform`) and `map_gammaRatio_exp` (`PLAStochastic.ForMathlib.Probability.OrderStatistics.GammaRatio`)
  compute the two laws;
* `identDistrib_sortVec_gammaRatio` and `lintegral_sortVec_eq_lintegral_gammaRatio` state the
  resulting equality in distribution.  The two families may live on different probability
  spaces.
-/

noncomputable section

namespace PGM.Renyi

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Nat

variable {n : ℕ} {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  {P : Measure Ω} {P' : Measure Ω'} {U : Fin n → Ω → ℝ} {E : Fin (n + 1) → Ω' → ℝ}

theorem hasLaw_sortVec_uniform (hU : ∀ i, HasLaw (U i) (volume.restrict (Icc (0 : ℝ) 1)) P)
    (hind : iIndepFun U P) :
    HasLaw (fun ω => sortVec fun i => U i ω) ((n ! : ℝ≥0∞) • volume.restrict (simplex n)) P where
  aemeasurable := measurable_sortVec.comp_aemeasurable (hind.hasLaw_pi hU).aemeasurable
  map_eq := map_sortVec_uniform hU hind

theorem hasLaw_gammaRatio_exp (hE : ∀ i, HasLaw (E i) (expMeasure 1) P') (hind : iIndepFun E P') :
    HasLaw (fun ω => gammaRatio fun i => E i ω) ((n ! : ℝ≥0∞) • volume.restrict (simplex n))
      P' where
  aemeasurable := measurable_gammaRatio.comp_aemeasurable (hind.hasLaw_pi hE).aemeasurable
  map_eq := map_gammaRatio_exp hE hind

/-- **Rényi representation.**  The order statistics of `n` iid uniform `[0, 1]` variables have
the law of the normalized partial sums `(Γ 1 / Γ (n+1), …, Γ n / Γ (n+1))` of `n + 1` iid
`Exp(1)` variables. -/
theorem identDistrib_sortVec_gammaRatio
    (hU : ∀ i, HasLaw (U i) (volume.restrict (Icc (0 : ℝ) 1)) P) (hUind : iIndepFun U P)
    (hE : ∀ i, HasLaw (E i) (expMeasure 1) P') (hEind : iIndepFun E P') :
    IdentDistrib (fun ω => sortVec fun i => U i ω) (fun ω => gammaRatio fun i => E i ω) P P' where
  aemeasurable_fst := (hasLaw_sortVec_uniform hU hUind).aemeasurable
  aemeasurable_snd := (hasLaw_gammaRatio_exp hE hEind).aemeasurable
  map_eq := by rw [map_sortVec_uniform hU hUind, map_gammaRatio_exp hE hEind]

/-- Expectations of measurable functionals agree under the Rényi representation. -/
theorem lintegral_sortVec_eq_lintegral_gammaRatio
    (hU : ∀ i, HasLaw (U i) (volume.restrict (Icc (0 : ℝ) 1)) P) (hUind : iIndepFun U P)
    (hE : ∀ i, HasLaw (E i) (expMeasure 1) P') (hEind : iIndepFun E P')
    {Φ : (Fin n → ℝ) → ℝ≥0∞} (hΦ : Measurable Φ) :
    ∫⁻ ω, Φ (sortVec fun i => U i ω) ∂P = ∫⁻ ω, Φ (gammaRatio fun i => E i ω) ∂P' := by
  have h := identDistrib_sortVec_gammaRatio hU hUind hE hEind
  rw [← lintegral_map' hΦ.aemeasurable h.aemeasurable_fst,
    ← lintegral_map' hΦ.aemeasurable h.aemeasurable_snd, h.map_eq]

end PGM.Renyi
