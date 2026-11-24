import PLAStochastic.Index.KEP.ReferenceScale.GammaRegularity
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Four classical derivatives on the unchanged positive reference orbit

At tolerance at least three the deterministic minimum rank excludes Gamma
shapes four and five. Shifting the original mixture by these two zero weights
proves C2 regularity of its genuine second derivative. This is finite-layer
regularity, with no assertion of a uniform derivative norm.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter

theorem kep_gammaMixtureDensity_C1 {p : ℕ → ℝ} (hp0 : ∀ n, 0 ≤ p n)
    (hp : Summable p) (k : ℕ) : ContDiff ℝ 1 (gammaMixtureDensity p (k + 2)) := by
  have hd := hasDerivAt_gammaMixtureDensity hp0 hp k
  have he : deriv (gammaMixtureDensity p (k + 2)) =
      gammaMixtureDensity p (k + 1) - gammaMixtureDensity p (k + 2) :=
    funext fun x => (hd x).deriv
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun x => (hd x).differentiableAt, ?_⟩
  rw [he]
  exact (continuous_gammaMixtureDensity hp0 hp k).sub
    (continuous_gammaMixtureDensity hp0 hp (k + 1))

theorem kep_gammaMixtureDensity_C2 {p : ℕ → ℝ} (hp0 : ∀ n, 0 ≤ p n)
    (hp : Summable p) (k : ℕ) : ContDiff ℝ 2 (gammaMixtureDensity p (k + 3)) := by
  have hd := hasDerivAt_gammaMixtureDensity hp0 hp (k + 1)
  have he : deriv (gammaMixtureDensity p (k + 3)) =
      gammaMixtureDensity p (k + 2) - gammaMixtureDensity p (k + 3) :=
    funext fun x => (hd x).deriv
  change ContDiff ℝ (1 + 1) _
  apply contDiff_succ_iff_deriv.mpr
  refine ⟨fun x => (hd x).differentiableAt, by norm_num, ?_⟩
  rw [he]
  exact (kep_gammaMixtureDensity_C1 hp0 hp k).sub
    (kep_gammaMixtureDensity_C1 hp0 hp (k + 1))

theorem kep_gammaMixtureDensity_shift_two {p : ℕ → ℝ} (hp0 : ∀ n, 0 ≤ p n)
    (hp : Summable p) (h0 : p 0 = 0) (h1 : p 1 = 0) (k : ℕ) (x : ℝ) :
    gammaMixtureDensity p k x = gammaMixtureDensity (fun n => p (n + 2)) (k + 2) x := by
  have hh := (summable_gammaMixtureDensity hp0 hp k x).sum_add_tsum_nat_add 2
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, h0, h1,
    zero_mul, zero_add] at hh
  unfold gammaMixtureDensity
  rw [← hh]
  apply tsum_congr
  intro n
  congr 2
  omega

theorem kep_gammaScaledSecond_C2 {p : ℕ → ℝ} (hp0 : ∀ n, 0 ≤ p n)
    (hp : Summable p) (h0 : p 0 = 0) (h1 : p 1 = 0) (m : ℝ) :
    ContDiff ℝ 2 (gammaScaledSecond p m) := by
  let q := fun n => p (n + 2)
  have hq0 : ∀ n, 0 ≤ q n := fun n => hp0 _
  have hq : Summable q := (summable_nat_add_iff 2).mpr hp
  have he : gammaScaledSecond p m = fun x => m ^ 3 *
      (gammaMixtureDensity q 3 (m * x) - 2 * gammaMixtureDensity q 4 (m * x) +
        gammaMixtureDensity q 5 (m * x)) := by
    funext x
    unfold gammaScaledSecond gammaMixtureSecond
    rw [kep_gammaMixtureDensity_shift_two hp0 hp h0 h1 1,
      kep_gammaMixtureDensity_shift_two hp0 hp h0 h1 2,
      kep_gammaMixtureDensity_shift_two hp0 hp h0 h1 3]
  rw [he]
  exact contDiff_const.mul
    ((((kep_gammaMixtureDensity_C2 hq0 hq 0).comp (contDiff_const.mul contDiff_id)).sub
      (contDiff_const.mul ((kep_gammaMixtureDensity_C2 hq0 hq 1).comp
        (contDiff_const.mul contDiff_id)))).add
      ((kep_gammaMixtureDensity_C2 hq0 hq 2).comp (contDiff_const.mul contDiff_id)))

theorem kepReference_count_ge_six {eps : ℝ} (heps : 3 ≤ eps) {j : ℕ} (hj : 1 ≤ j) :
    ∀ᵐ ω ∂expSeqMeasure, 6 ≤ (epLayerSeq eps expCoord j 0 ω).2 := by
  have heps0 : 0 ≤ eps := by linarith
  filter_upwards [ae_allLayersFinite_exp iidSeq_expCoord (hasLaw_expCoord 0) heps0] with ω hω
  have hp := pow_le_layerPivot_sub heps0 (z := seq (inputPairs expCoord) ω)
    (fun _ => rfl) hω j 0
  have he : layerPivot eps (seq (inputPairs expCoord) ω) j 1 -
      layerPivot eps (seq (inputPairs expCoord) ω) j 0 = (epLayerSeq eps expCoord j 0 ω).2 := by
    simp only [layerPivot, pairRank_one, pairRank_zero, Nat.sub_zero, ← seq_epLayerSeq]
    rfl
  rw [he] at hp
  have hq : 6 ≤ ⌊2 * eps⌋₊ + 1 := by
    have h : 5 ≤ ⌊2 * eps⌋₊ := Nat.le_floor (by push_cast; linarith)
    omega
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have hpow : 1 ≤ (⌊2 * eps⌋₊ + 1) ^ i := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by omega))
  have hqpow : ⌊2 * eps⌋₊ + 1 ≤ (⌊2 * eps⌋₊ + 1) ^ (i + 1) := by
    rw [pow_succ]
    simpa only [one_mul] using Nat.mul_le_mul_right (⌊2 * eps⌋₊ + 1) hpow
  exact (hq.trans hqpow).trans hp

theorem kepReferenceWeights_initial_two_zero {eps : ℝ} (heps : 3 ≤ eps)
    {j : ℕ} (hj : 1 ≤ j) : kepReferenceWeights eps j 0 = 0 ∧ kepReferenceWeights eps j 1 = 0 := by
  have hzero (n : ℕ) (hn : n ≤ 1) : kepReferenceWeights eps j n = 0 := by
    have hz : expSeqMeasure {ω | (epLayerSeq eps expCoord j 0 ω).2 = n + 4} = 0 := by
      apply measure_eq_zero_iff_ae_notMem.mpr
      filter_upwards [kepReference_count_ge_six heps hj] with ω hω
      omega
    change (expSeqMeasure {ω | (epLayerSeq eps expCoord j 0 ω).2 = n + 4}).toReal = 0
    rw [hz, ENNReal.toReal_zero]
  exact ⟨hzero 0 (by omega), hzero 1 le_rfl⟩

theorem kepReference_second_density_C2 {eps : ℝ}
    (heps : kepReferenceClassicalThreshold ≤ eps) (he3 : 3 ≤ eps)
    {j : ℕ} (hj : 1 ≤ j) :
    ContDiff ℝ 2 (gammaScaledSecond (kepReferenceWeights eps j) (kepReferenceSpan eps j)) := by
  have hz := kepReferenceWeights_initial_two_zero he3 hj
  exact kep_gammaScaledSecond_C2 (kepReferenceWeights_nonneg eps j)
    (kepReferenceWeights_summable ((le_max_left _ _).trans heps) hj) hz.1 hz.2 _

end

end PGM
