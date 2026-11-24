import PLAStochastic.Index.GEP.StrongApprox.Tree.Moderation
import PLAStochastic.Index.GEP.StrongApprox.Tree.Construction

/-! # Actual dyadic source/Gaussian coupling: the endpoint probability estimate -/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

/-- The root in the constructed Gaussian tree is the scaled shared normal innovation. -/
theorem saGaussianTree_root_quantile {V : ℝ} (hV : 0 < V) {m : ℕ} (hm : 0 < m)
    (J : ℕ) (z : ℝ) :
    saQuantile (cdf ((saGaussianTreeRegular hV hm J).law : Measure ℝ))
      (cdf (gaussianReal 0 1) z) = Real.sqrt ((m * 2 ^ J : ℕ) * V) * z := by
  have hv : ((m * 2 ^ J : ℕ) : ℝ≥0) * Real.toNNReal V ≠ 0 :=
    mul_ne_zero (by exact_mod_cast (Nat.mul_pos hm (show 0 < 2 ^ J by positivity)).ne')
      (by simp [Real.toNNReal_eq_zero, hV.not_ge])
  change saQuantile (cdf ((saDensity_gaussianPDF 0 hv).law : Measure ℝ))
    (cdf (gaussianReal 0 1) z) = _
  rw [saDensity_gaussianPDF_law 0 hv]
  simpa [Real.toNNReal_of_nonneg hV.le] using saQuantile_gaussian 0 hv z

/-- Every constructed Gaussian split is an affine bridge with its explicit child variance. -/
theorem saGaussianTree_split_quantile {V : ℝ} (hV : 0 < V) {m : ℕ} (hm : 0 < m)
    (j : ℕ) (a z : ℝ) :
    saSplitQuantile (saGaussianTreeRegular hV hm j) a (cdf (gaussianReal 0 1) z) =
      a / 2 + Real.sqrt ((m * 2 ^ j : ℕ) * V / 2) * z := by
  have hv : ((m * 2 ^ j : ℕ) : ℝ≥0) * Real.toNNReal V ≠ 0 :=
    mul_ne_zero (by exact_mod_cast (Nat.mul_pos hm (show 0 < 2 ^ j by positivity)).ne')
      (by simp [Real.toNNReal_eq_zero, hV.not_ge])
  change saSplitQuantile (saDensity_gaussianPDF 0 hv) a (cdf (gaussianReal 0 1) z) = _
  simpa [Real.toNNReal_of_nonneg hV.le] using saSplitQuantile_gaussian hv a z

/-- Endpoint failure probability of the actual dyadic coupling. Its remaining inputs are the
proved scalar conditional-quantile estimates and the actual source-total tails. -/
theorem saDyadicLeafCoupling_bad_bound (ν : ProbabilityMeasure ℝ) {s : ℝ} (hs : 0 < s)
    {m : ℕ} (hm : 0 < m) (hV : 0 < lawVar ν + s ^ 2) (J : ℕ)
    (R D Z : ℝ) (A : ℕ → ℝ) (hR : 0 ≤ R) (hD : 0 ≤ D) (hZ : 0 ≤ Z)
    (hroot : ∀ z : ℝ, |z| ≤ Z →
      |saQuantile (cdf ((saSourceTreeRegular ν hs hm J).law : Measure ℝ))
        (cdf (gaussianReal 0 1) z) - Real.sqrt ((m * 2 ^ J : ℕ) * (lawVar ν + s ^ 2)) * z| ≤ R)
    (hlocal : ∀ d < J, ∀ a z : ℝ, |a| ≤ A d → |z| ≤ Z →
      |saSplitQuantile (saSourceTreeRegular ν hs hm (J - d - 1)) a (cdf (gaussianReal 0 1) z) -
        a / 2 - Real.sqrt ((m * 2 ^ (J - d - 1) : ℕ) * (lawVar ν + s ^ 2) / 2) * z| ≤ D) :
    (saDyadicLeafCoupling ν hs hm hV J).real
      (saLeafBad (2 ^ J) (((J : ℝ) + 1) * (R + 2 * D))) ≤
        2 * Real.exp (-(Z ^ 2 / 2)) + ∑ d ∈ Finset.range J, (2 ^ d : ℕ) *
          (((saSourceTreeRegular ν hs hm (J - d)).law : Measure ℝ).real {a | A d < |a|} +
            2 * Real.exp (-(Z ^ 2 / 2))) := by
  exact saTreeLeafPair_moderated_bad_bound (saSourceTreeRegular ν hs hm)
    (saGaussianTreeRegular hV hm) (saSourceTree_step ν hs hm) J
    (Real.sqrt ((m * 2 ^ J : ℕ) * (lawVar ν + s ^ 2))) R D Z
    (fun d => Real.sqrt ((m * 2 ^ (J - d - 1) : ℕ) * (lawVar ν + s ^ 2) / 2))
    A hR hD hZ (saGaussianTree_root_quantile hV hm J) hroot
    (fun d _ => saGaussianTree_split_quantile hV hm (J - d - 1)) hlocal

/-- Counting the internal nodes loses only one leaf-count factor in the common failure tail. -/
theorem sa_dyadic_failure_sum_le (J : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) :
    2 * δ + ∑ d ∈ Finset.range J, (2 ^ d : ℕ) * (δ + 2 * δ) ≤ 3 * (2 : ℝ) ^ J * δ := by
  have hsum : ∑ d ∈ Finset.range J, (2 ^ d : ℕ) * (δ + 2 * δ) =
      3 * ((2 : ℝ) ^ J - 1) * δ := by
    induction J with
    | zero => simp
    | succ J ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      rw [pow_succ]
      ring
  rw [hsum]
  nlinarith

/-- Concrete tree failure estimate for the logarithmic normal window used in the strong coupling. -/
theorem saDyadicLeafCoupling_bad_bound_window (ν : ProbabilityMeasure ℝ) {s : ℝ} (hs : 0 < s)
    {m : ℕ} (hm : 0 < m) (hV : 0 < lawVar ν + s ^ 2) (J : ℕ)
    (R D H : ℝ) (A : ℕ → ℝ) (hR : 0 ≤ R) (hD : 0 ≤ D) (hH : 0 ≤ H)
    (hroot : ∀ z : ℝ, |z| ≤ Real.sqrt (10 * H) →
      |saQuantile (cdf ((saSourceTreeRegular ν hs hm J).law : Measure ℝ))
        (cdf (gaussianReal 0 1) z) - Real.sqrt ((m * 2 ^ J : ℕ) * (lawVar ν + s ^ 2)) * z| ≤ R)
    (hlocal : ∀ d < J, ∀ a z : ℝ, |a| ≤ A d → |z| ≤ Real.sqrt (10 * H) →
      |saSplitQuantile (saSourceTreeRegular ν hs hm (J - d - 1)) a (cdf (gaussianReal 0 1) z) -
        a / 2 - Real.sqrt ((m * 2 ^ (J - d - 1) : ℕ) * (lawVar ν + s ^ 2) / 2) * z| ≤ D)
    (htail : ∀ d < J,
      ((saSourceTreeRegular ν hs hm (J - d)).law : Measure ℝ).real {a | A d < |a|} ≤
        Real.exp (-(5 * H))) :
    (saDyadicLeafCoupling ν hs hm hV J).real
      (saLeafBad (2 ^ J) (((J : ℝ) + 1) * (R + 2 * D))) ≤
        3 * (2 : ℝ) ^ J * Real.exp (-(5 * H)) := by
  have he := saDyadicLeafCoupling_bad_bound ν hs hm hV J R D (Real.sqrt (10 * H)) A
    hR hD (Real.sqrt_nonneg _) hroot hlocal
  have hpow : -(Real.sqrt (10 * H) ^ 2 / 2) = -(5 * H) := by
    rw [Real.sq_sqrt (by positivity)]
    ring
  rw [hpow] at he
  apply he.trans
  apply le_trans _ (sa_dyadic_failure_sum_le J (Real.exp_nonneg (-(5 * H))))
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro d hd
  exact mul_le_mul_of_nonneg_left
    (add_le_add (htail d (Finset.mem_range.mp hd)) le_rfl) (by positivity)

end

end PGM
