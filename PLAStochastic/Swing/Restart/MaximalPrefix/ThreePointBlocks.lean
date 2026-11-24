import PLAStochastic.Swing.Algorithm.Measurability
import PLAStochastic.Affine.Lifetime.GaussianBlocks
import PLAStochastic.Swing.Repair.GeometricRejectionTail
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence

/-! # Actual disjoint Gaussian three-point blocks for native prefixes -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Finset
open scoped NNReal ENNReal Topology
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

theorem iid_standardGaussian_hasGaussianLaw (hX : ∀ n, Measurable (X n))
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (n : ℕ) : HasGaussianLaw (X n) μ :=
  (show HasLaw (X n) (gaussianReal 0 1) μ from ⟨(hX n).aemeasurable, hG n⟩).hasGaussianLaw

theorem iid_standardGaussian_isGaussianProcess (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) :
    IsGaussianProcess X μ where
  hasGaussianLaw s := (hi.restrict s).hasGaussianLaw
    (fun i => iid_standardGaussian_hasGaussianLaw hX hG i)

theorem iid_standardGaussian_mean_variance (hX : ∀ n, Measurable (X n))
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (n : ℕ) :
    (∫ ω, X n ω ∂μ) = 0 ∧ variance (X n) μ = 1 := by
  have hl : HasLaw (X n) (gaussianReal 0 1) μ := ⟨(hX n).aemeasurable, hG n⟩
  constructor
  · simpa only [integral_id_gaussianReal] using hl.integral_eq
  · simpa using hl.variance_eq

theorem gaussian_weighted_sum_hasLaw (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    (s : Finset ℕ) (c : ℕ → ℝ) :
    HasLaw (fun ω => ∑ k ∈ s, c k * X k ω)
      (gaussianReal 0 (Real.toNNReal (∑ k ∈ s, (c k) ^ 2))) μ := by
  have : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hg : IsGaussianProcess (fun k ω => c k * X k ω) μ := by
    simpa only [smul_eq_mul] using (iid_standardGaussian_isGaussianProcess hX hi hG).smul c
  have hgs := hg.hasGaussianLaw_fun_sum (I := s)
  have hm : (∫ ω, ∑ k ∈ s, c k * X k ω ∂μ) = 0 := by
    rw [integral_finsetSum s (fun k _ => (iid_standardGaussian_hasGaussianLaw hX hG k).integrable.const_mul (c k))]
    apply Finset.sum_eq_zero
    intro k _
    rw [integral_const_mul, (iid_standardGaussian_mean_variance hX hG k).1, mul_zero]
  have hv : variance (fun ω => ∑ k ∈ s, c k * X k ω) μ = ∑ k ∈ s, (c k) ^ 2 := by
    have hs := IndepFun.variance_sum (X := fun k ω => c k * X k ω) (s := s)
      (fun k _ => (hg.hasGaussianLaw_eval k).memLp_two)
      (fun i _ j _ hij => (hi.indepFun hij).comp (φ := fun x : ℝ => c i * x)
        (ψ := fun x : ℝ => c j * x) (by fun_prop) (by fun_prop))
    have he : (∑ k ∈ s, fun ω => c k * X k ω) = (fun ω => ∑ k ∈ s, c k * X k ω) := by
      funext ω
      simp only [Finset.sum_apply]
    rw [he] at hs
    rw [hs]
    apply Finset.sum_congr rfl
    intro k _
    rw [variance_const_mul, (iid_standardGaussian_mean_variance hX hG k).2, mul_one]
  exact ⟨hgs.aemeasurable, by simpa only [smul_eq_mul, hm, hv] using hgs.map_eq_gaussianReal⟩

/-- The second difference on a block of 2r increments, retaining its actual indices. -/
def nativeGaussianBlock (X : ℕ → Ω → ℝ) (n r : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.Ico n (n + 2 * r), (if k < n + r then (-1 : ℝ) else 1) * X k ω

theorem nativeGaussianBlock_measurable (hX : ∀ n, Measurable (X n)) (n r : ℕ) :
    Measurable (nativeGaussianBlock X n r) := by
  unfold nativeGaussianBlock
  exact Finset.measurable_sum _ (fun k _ => (hX k).const_mul _)

theorem nativeGaussianBlock_hasLaw (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (n r : ℕ) :
    HasLaw (nativeGaussianBlock X n r) (gaussianReal 0 (2 * (r : ℝ≥0))) μ := by
  have h := gaussian_weighted_sum_hasLaw hX hi hG (Finset.Ico n (n + 2 * r))
    (fun k => if k < n + r then (-1 : ℝ) else 1)
  have he : (∑ k ∈ Finset.Ico n (n + 2 * r),
      (if k < n + r then (-1 : ℝ) else 1) ^ 2) = 2 * (r : ℝ) := by
    simp only [ite_pow, neg_one_sq, one_pow, ite_self, sum_const, nsmul_eq_mul, mul_one,
      Nat.card_Ico, Nat.add_sub_cancel_left, Nat.cast_mul, Nat.cast_ofNat]
  have hr : Real.toNNReal (2 * (r : ℝ)) = 2 * (r : ℝ≥0) := by
    ext
    simp
  rw [he, hr] at h
  exact h

omit [MeasurableSpace Ω] in
theorem nativeGaussianBlock_eq_second_difference (X : ℕ → Ω → ℝ) (n r : ℕ) (ω : Ω) :
    nativeGaussianBlock X n r ω = cumulativeSamples X (n + 2 * r) ω -
      2 * cumulativeSamples X (n + r) ω + cumulativeSamples X n ω := by
  unfold nativeGaussianBlock
  rw [← Finset.sum_Ico_consecutive _ (by omega : n ≤ n + r) (by omega : n + r ≤ n + 2 * r)]
  have hleft : (∑ k ∈ Finset.Ico n (n + r),
      (if k < n + r then (-1 : ℝ) else 1) * X k ω) = -(∑ k ∈ Finset.Ico n (n + r), X k ω) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    rw [if_pos (Finset.mem_Ico.mp hk).2, neg_one_mul]
  have hright : (∑ k ∈ Finset.Ico (n + r) (n + 2 * r),
      (if k < n + r then (-1 : ℝ) else 1) * X k ω) =
        ∑ k ∈ Finset.Ico (n + r) (n + 2 * r), X k ω := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [if_neg (not_lt_of_ge (Finset.mem_Ico.mp hk).1), one_mul]
  rw [hleft, hright, Finset.sum_Ico_eq_sub _ (by omega : n ≤ n + r),
    Finset.sum_Ico_eq_sub _ (by omega : n + r ≤ n + 2 * r)]
  unfold cumulativeSamples
  ring

omit [MeasurableSpace Ω] in
/-- Any affine fit, with any inherited offset, must pass every contained three-point block. -/
theorem affine_fit_three_point_block (ω : Ω) {E a q x : ℝ} {n r : ℕ}
    (hfit : ∀ k ∈ Finset.Icc n (n + 2 * r),
      |x + cumulativeSamples X k ω - q - a * (k : ℝ)| ≤ E) :
    |nativeGaussianBlock X n r ω| ≤ 4 * E := by
  have h₀ := abs_le.mp (hfit n (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩))
  have h₁ := abs_le.mp (hfit (n + r) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩))
  have h₂ := abs_le.mp (hfit (n + 2 * r) (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩))
  rw [nativeGaussianBlock_eq_second_difference, abs_le]
  push_cast at h₀ h₁ h₂
  constructor <;> nlinarith

theorem nativeGaussianBlock_pass_le (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {E : ℝ} (hE : 0 < E) (n r : ℕ) (hr : 8 * E ^ 2 ≤ (r : ℝ)) :
    μ {ω | |nativeGaussianBlock X n r ω| ≤ 4 * E} ≤ BrownianAffine.gaussianBlockPass := by
  have hrR : 0 < (r : ℝ) := lt_of_lt_of_le (by positivity) hr
  let σ : ℝ := Real.sqrt (2 * (r : ℝ))
  have hσ : 0 < σ := Real.sqrt_pos.mpr (by positivity)
  have hσsq : σ ^ 2 = 2 * (r : ℝ) := Real.sq_sqrt (by positivity)
  let vσ : ℝ≥0 := ⟨σ ^ 2, sq_nonneg σ⟩
  have hv : 2 * (r : ℝ≥0) / vσ = 1 := by
    apply Subtype.ext
    change (2 * (r : ℝ)) / σ ^ 2 = 1
    rw [hσsq, div_self (by positivity : 2 * (r : ℝ) ≠ 0)]
  have hl : HasLaw (fun ω => nativeGaussianBlock X n r ω / σ) (gaussianReal 0 1) μ := by
    have hd := gaussianReal_div_const (nativeGaussianBlock_hasLaw hX hi hG n r) σ
    change HasLaw (fun ω => nativeGaussianBlock X n r ω / σ)
      (gaussianReal (0 / σ) (2 * (r : ℝ≥0) / vσ)) μ at hd
    simpa only [zero_div, hv] using hd
  have hp := hl.measure_eq (p := fun z => z ∈ Set.Icc (-1 : ℝ) 1) measurableSet_Icc
  have hp' : μ {ω | |nativeGaussianBlock X n r ω / σ| ≤ 1} = BrownianAffine.gaussianBlockPass := by
    simpa only [Set.mem_Icc, Set.Icc_def, abs_le, BrownianAffine.gaussianBlockPass] using hp
  rw [← hp']
  apply measure_mono
  intro ω hω
  change |nativeGaussianBlock X n r ω / σ| ≤ 1
  rw [abs_div, abs_of_pos hσ, div_le_one hσ]
  apply hω.trans
  nlinarith

end SwingRepair
