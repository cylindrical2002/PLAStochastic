import PLAStochastic.Index.KEP.ReferenceScale.ActualMixedFirstSeries
import PLAStochastic.Index.KEP.ReferenceScale.KilledPolynomialSeries

/-!
# Both length indices of the actual mixed first-derivative series

The short killed factor pays its own length index, including the total-length
polynomial and physical exponential weight. Endpoints may depend on that index.
This is a quantitative kernel series, not an identification of the greedy graph.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set

theorem kepReference_mixed_first_double_series_polynomial_budget :
    ∃ theta c eps0 : ℝ, 0 < theta ∧ 0 < c ∧
      kepReferenceClassicalThreshold ≤ eps0 ∧
      ∀ p : ℕ, ∃ K : ℝ, 0 < K ∧
        ∀ eps, eps0 ≤ eps → ∀ heps : kepReferenceClassicalThreshold ≤ eps,
          ∀ j, ∀ hj : 1 ≤ j, ∀ σA σB : ℝ,
          (σA = 1 ∨ σA = -1) → (σB = 1 ∨ σB = -1) →
          ∀ N : ℕ, 8 ≤ N → eps ≤ (N / 2 : ℕ) →
          ∀ xA yA xB yB : ℕ → ℝ,
          let C := segMean expSeqMeasure eps (epLayerSeq eps expCoord j)
          let F := fun z : ℕ × ℕ => (z.1 + z.2 + N + 1 : ℝ) ^ p *
            Real.exp (2 * theta * (z.1 + z.2 + N) / C) *
            (∫ a in Icc (1 / 2 : ℝ) 2,
              |kepReferenceFirstKernel heps hj (2 * eps) σA z.1 (xA z.1) (yA z.1) a *
                kepReferenceFirstKernel heps hj (2 * eps) σB (z.2 + N)
                  (xB z.1) (yB z.1) a|)
          Summable F ∧ (∑' z : ℕ × ℕ, F z) ≤
            K * eps ^ (4 * p + 6) * (1 + Real.sqrt (kepReferenceSecondNorm eps j) +
              Real.exp (-c * eps) * kepReferenceSecondNorm eps j) := by
  obtain ⟨D, vlo, vhi, theta0, c, e0, hD, hvlo, hvhi, ht0, hc, he0, hseries⟩ :=
    kepReference_mixed_first_series_polynomial_budget
  let cb := cBr (bIn 1 1) (vIn 1 1)
  let kap := kepTruncatedKappa D vlo vhi
  let theta := min theta0 (kap / (64 * cb))
  have hcb1 : 1 ≤ cb := one_le_cBr (bAbs_le_bIn 1 1)
  have hcb : 0 < cb := by linarith
  have hkap : 0 < kap := kepTruncatedKappa_pos hD hvlo hvhi
  have ht : 0 < theta := lt_min ht0 (by positivity)
  refine ⟨theta, c, e0, ht, hc, he0, ?_⟩
  intro p
  obtain ⟨K0, hK0, hrow⟩ := hseries p
  let E := (p.factorial : ℝ) * Real.exp 1 * (1 + 8 / kap) ^ (p + 1)
  have hE : 0 < E := by dsimp [E]; positivity
  refine ⟨K0 * E * 2 ^ (2 * (p + 1)), by positivity, ?_⟩
  intro eps he heps j hj σA σB hσA hσB N hN hcut xA yA xB yB
  dsimp only
  let C := segMean expSeqMeasure eps (epLayerSeq eps expCoord j)
  let eta := 2 * theta / C
  let r := Real.sqrt (krLam D vlo vhi (2 * eps))
  let U := 1 + Real.sqrt (kepReferenceSecondNorm eps j) +
    Real.exp (-c * eps) * kepReferenceSecondNorm eps j
  let P := fun n k : ℕ => ∫ a in Icc (1 / 2 : ℝ) 2,
    |kepReferenceFirstKernel heps hj (2 * eps) σA n (xA n) (yA n) a *
      kepReferenceFirstKernel heps hj (2 * eps) σB (k + N) (xB n) (yB n) a|
  let F := fun z : ℕ × ℕ => (z.1 + z.2 + N + 1 : ℝ) ^ p *
    Real.exp (2 * theta * (z.1 + z.2 + N) / C) * P z.1 z.2
  let A := fun n : ℕ => (n + 1 : ℝ) ^ p * Real.exp (eta * n)
  let G := fun n k : ℕ => (k + N + 1 : ℝ) ^ p *
    Real.exp (2 * theta0 * (k + N) / C) * P n k
  have heps2 : 2 ≤ eps := (le_max_left _ _).trans heps
  have hepspos : 0 < eps := by linarith
  have hC : eps ^ 2 / cb ≤ C :=
    (segMean_bracket gapLaw_expCoord ((le_max_right _ _).trans heps) j).1
  have hCpos : 0 < C := (div_pos (by positivity) hcb).trans_le hC
  have heta : eta ≤ kepTruncatedKappa D vlo vhi / (4 * (2 * eps) ^ 2) := by
    calc
      eta ≤ 2 * theta / (eps ^ 2 / cb) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hC
      _ ≤ 2 * (kap / (64 * cb)) / (eps ^ 2 / cb) := by
        gcongr
        exact min_le_right _ _
      _ = kap / (32 * eps ^ 2) := by field_simp; ring
      _ ≤ _ := by
        apply div_le_div_of_nonneg_left hkap.le (by positivity)
        nlinarith
  have hP (n k : ℕ) : 0 ≤ P n k :=
    setIntegral_nonneg measurableSet_Icc (fun _ _ => abs_nonneg _)
  have hF (z : ℕ × ℕ) : 0 ≤ F z := mul_nonneg (by positivity) (hP _ _)
  have hG (n k : ℕ) : 0 ≤ G n k := mul_nonneg (by positivity) (hP _ _)
  have hA (n : ℕ) : 0 ≤ A n := by dsimp [A]; positivity
  have hU : 0 ≤ U := by
    have := kepReferenceSecondNorm_nonneg eps j
    dsimp [U]
    positivity
  have hsG (n : ℕ) : Summable (G n) ∧
      (∑' k : ℕ, G n k) ≤ K0 * eps ^ (2 * p + 4) * r ^ n * U := by
    simpa only [G, P, C, r, U, Nat.zero_add] using
      hrow eps he heps j hj σA σB hσA hσB n 0 N hN hcut (xA n) (yA n) (xB n) (yB n)
  have hFG (n k : ℕ) : F (n, k) ≤ A n * G n k := by
    have hpoly : (n + k + N + 1 : ℝ) ≤ (n + 1 : ℝ) * (k + N + 1 : ℝ) := by
      have hnk : (0 : ℝ) ≤ (n : ℝ) * ((k : ℝ) + N) := by positivity
      nlinarith only [hnk]
    have hweight : Real.exp (2 * theta * (n + k + N : ℝ) / C) ≤
        Real.exp (eta * n) * Real.exp (2 * theta0 * (k + N : ℝ) / C) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hcoef : 2 * theta * (k + N : ℝ) / C ≤ 2 * theta0 * (k + N : ℝ) / C := by
        gcongr
        exact min_le_left _ _
      calc
        _ = eta * n + 2 * theta * (k + N : ℝ) / C := by dsimp [eta]; ring
        _ ≤ _ := add_le_add le_rfl hcoef
    calc
      _ ≤ ((n + 1 : ℝ) * (k + N + 1 : ℝ)) ^ p *
          (Real.exp (eta * n) * Real.exp (2 * theta0 * (k + N) / C)) * P n k := by
        apply mul_le_mul_of_nonneg_right _ (hP n k)
        exact mul_le_mul (pow_le_pow_left₀ (by positivity) hpoly p) hweight
          (Real.exp_pos _).le (by positivity)
      _ = _ := by dsimp [A, G]; rw [mul_pow]; ring
  have hsF (n : ℕ) : Summable (fun k : ℕ => F (n, k)) :=
    ((hsG n).1.mul_left (A n)).of_nonneg_of_le (fun k => hF (n, k)) (hFG n)
  have hrowBound (n : ℕ) : (∑' k : ℕ, F (n, k)) ≤
      (K0 * eps ^ (2 * p + 4) * U) *
        ((n + 1 : ℝ) ^ p * Real.exp (eta * n) * r ^ n) := by
    calc
      _ ≤ ∑' k : ℕ, A n * G n k :=
        (hsF n).tsum_le_tsum (hFG n) ((hsG n).1.mul_left _)
      _ = A n * ∑' k : ℕ, G n k := tsum_mul_left
      _ ≤ A n * (K0 * eps ^ (2 * p + 4) * r ^ n * U) :=
        mul_le_mul_of_nonneg_left (hsG n).2 (hA n)
      _ = _ := by dsimp [A]; ring
  have hsR := summable_polynomial_weighted_sqrt_krLam hD hvlo hvhi (by linarith) heta p
  have hsOuter : Summable (fun n : ℕ => ∑' k : ℕ, F (n, k)) :=
    (hsR.mul_left (K0 * eps ^ (2 * p + 4) * U)).of_nonneg_of_le
      (fun n => tsum_nonneg fun k => hF (n, k)) hrowBound
  have hs : Summable F := (summable_prod_of_nonneg hF).mpr ⟨hsF, hsOuter⟩
  refine ⟨hs, ?_⟩
  have hsumR := tsum_polynomial_weighted_sqrt_krLam_le hD hvlo hvhi (by linarith) heta p
  calc
    _ = ∑' n : ℕ, ∑' k : ℕ, F (n, k) := hs.tsum_prod
    _ ≤ ∑' n : ℕ, (K0 * eps ^ (2 * p + 4) * U) *
        ((n + 1 : ℝ) ^ p * Real.exp (eta * n) * r ^ n) :=
      hsOuter.tsum_le_tsum hrowBound (hsR.mul_left _)
    _ = (K0 * eps ^ (2 * p + 4) * U) *
        ∑' n : ℕ, (n + 1 : ℝ) ^ p * Real.exp (eta * n) * r ^ n := tsum_mul_left
    _ ≤ (K0 * eps ^ (2 * p + 4) * U) * (E * (2 * eps) ^ (2 * (p + 1))) :=
      mul_le_mul_of_nonneg_left hsumR (by positivity)
    _ = _ := by
      dsimp [U]
      rw [mul_pow]
      have hexp : eps ^ (2 * p + 4) * eps ^ (2 * (p + 1)) = eps ^ (4 * p + 6) := by
        rw [← pow_add]
        congr 1
        omega
      calc
        _ = (K0 * E * 2 ^ (2 * (p + 1))) *
            (eps ^ (2 * p + 4) * eps ^ (2 * (p + 1))) *
            (1 + Real.sqrt (kepReferenceSecondNorm eps j) +
              Real.exp (-c * eps) * kepReferenceSecondNorm eps j) := by ring
        _ = _ := by rw [hexp]

end

end PGM
