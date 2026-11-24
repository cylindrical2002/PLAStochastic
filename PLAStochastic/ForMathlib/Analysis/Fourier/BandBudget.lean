import PLAStochastic.ForMathlib.Analysis.Fourier.DecayBudget
import PLAStochastic.ForMathlib.Analysis.Fourier.WeightedRemainder
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Three-band angular Fourier budgets -/

noncomputable section

open Filter Topology Finset MeasureTheory

namespace PGM

/-- The high, medium, coefficient and logarithmic low-frequency estimates.
Polynomial exponents are natural numbers, which suffices after rounding up a
nonnegative real exponent. All thresholds and constants are independent of frequency. -/
structure FourierBandEstimates (φ : ℝ → ℝ → ℂ) (a : ℕ → ℝ → ℂ) : Prop where
  delta : ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
    ∃ c U K : ℝ, 0 < c ∧ 0 ≤ U ∧ 0 ≤ K ∧ ∃ d : ℕ,
      (∀ᶠ eps in atTop, ∀ u : ℝ, U ≤ |u| → |u| ≤ eps ^ (1 + δ) →
        ‖φ eps u‖ ≤ K * (1 + |u|) ^ d * Real.exp (-c * Real.sqrt |u|) +
          K * eps ^ d * Real.exp (-c * eps)) ∧
      (∀ k : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∃ d : ℕ, ∀ u : ℝ,
        ‖a k u‖ ≤ B * (1 + |u|) ^ d * Real.exp (-c * Real.sqrt |u|))
  high : ∀ r : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ eps in atTop, ∀ u : ℝ,
    |u| ^ r * ‖φ eps u‖ ≤ K * eps ^ (r + 2)
  low : ∀ P : ℕ, ∀ A : ℝ, 0 < A → ∃ K : ℝ, 0 ≤ K ∧ ∃ d : ℕ,
    ∀ᶠ eps in atTop, ∀ u : ℝ, |u| ≤ (A * Real.log eps) ^ 2 →
      ‖φ eps u - ∑ k ∈ range (P + 1), ((eps⁻¹) ^ k : ℝ) • a k u‖ ≤
        K * (eps⁻¹) ^ (P + 1) * (1 + |u|) ^ d

/-- A finite set of coefficient transforms has a common stretched-exponential moment bound. -/
theorem finite_stretchedExp_moment_bound {a : ℕ → ℝ → ℂ} {c : ℝ} (hc : 0 < c)
    (ha : ∀ k : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∃ d : ℕ, ∀ u : ℝ,
      ‖a k u‖ ≤ B * (1 + |u|) ^ d * Real.exp (-c * Real.sqrt |u|)) (m P : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ u : ℝ,
      ∑ k ∈ range (P + 1), (1 + |u|) ^ m * ‖a k u‖ ≤
        B * Real.exp (-(c / 2) * Real.sqrt |u|) := by
  classical
  have hsingle : ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ,
      (1 + |u|) ^ m * ‖a k u‖ ≤ C * Real.exp (-(c / 2) * Real.sqrt |u|) := by
    intro k
    obtain ⟨B, hB, d, hb⟩ := ha k
    obtain ⟨C, hC, hc'⟩ := polynomial_mul_stretchedExp_le hc (m + d)
    refine ⟨B * C, by positivity, fun u => ?_⟩
    calc
      _ ≤ (1 + |u|) ^ m * (B * (1 + |u|) ^ d * Real.exp (-c * Real.sqrt |u|)) :=
        mul_le_mul_of_nonneg_left (hb u) (by positivity)
      _ = B * ((1 + |u|) ^ (m + d) * Real.exp (-c * Real.sqrt |u|)) := by rw [pow_add]; ring
      _ ≤ _ := by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hc' |u| (abs_nonneg _)) hB
  choose C hC hbound using hsingle
  refine ⟨∑ k ∈ range (P + 1), C k, sum_nonneg fun k _ => hC k, fun u => ?_⟩
  rw [sum_mul]
  exact sum_le_sum fun k _ => hbound k u

/-- A pointwise integrable majorant for the full Fourier remainder.
One algebraic order is reserved for the polynomial logarithmic loss. -/
theorem FourierBandEstimates.remainder_moment_bound {φ : ℝ → ℝ → ℂ} {a : ℕ → ℝ → ℂ}
    (h : FourierBandEstimates φ a) (m n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ eps in atTop, ∀ u : ℝ,
      (1 + |u|) ^ (m + 2) *
        ‖φ eps u - ∑ k ∈ range (n + 1), ((eps⁻¹) ^ k : ℝ) • a k u‖ ≤ C * (eps⁻¹) ^ n := by
  obtain ⟨δ, hδ, hδ1, c, U, K, hc, hU, hK, d, hmed, ha⟩ := h.delta
  let A := max 1 (2 * (n : ℝ) / c)
  have hA1 : 1 ≤ A := le_max_left _ _
  have hA : 0 < A := zero_lt_one.trans_le hA1
  have hnA : (n : ℝ) ≤ (c / 2) * A := by
    have h := le_max_right (1 : ℝ) (2 * (n : ℝ) / c)
    have hd := (div_le_iff₀ hc).mp h
    dsimp [A]
    nlinarith
  obtain ⟨r, hr⟩ := exists_high_frequency_order hδ m n
  obtain ⟨H, hH, hhigh⟩ := h.high r
  obtain ⟨L, hL, dl, hlow⟩ := h.low n A hA
  obtain ⟨M, hM, hm⟩ := polynomial_mul_stretchedExp_le hc (m + 2 + d)
  obtain ⟨B, hB, hb⟩ := finite_stretchedExp_moment_bound hc ha (m + 2) n
  obtain ⟨E, hE, he⟩ := polynomial_mul_exp_le_inverse hc (d + 2 * (m + 2)) n
  let C := L * (1 + A ^ 2) ^ (dl + m + 2) + K * M +
    2 ^ (m + 2) * (K * E + H) + B
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  have hlogs : ∀ᶠ eps : ℝ in atTop, max 1 U ≤ Real.log eps :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (max 1 U))
  filter_upwards [hmed, hhigh, hlow, hlogs, eventually_ge_atTop (1 : ℝ),
    eventually_log_band_polynomial_le A (dl + m + 2)] with eps hmed hhigh hlow hlog heps hlogpoly
  intro u
  have heps0 : 0 < eps := zero_lt_one.trans_le heps
  have hi0 : 0 ≤ eps⁻¹ := (inv_pos.mpr heps0).le
  have hi1 : eps⁻¹ ≤ 1 := (inv_le_one₀ heps0).mpr heps
  have ht0 : 0 ≤ |u| := abs_nonneg _
  have hbase : 0 ≤ 1 + |u| := by positivity
  by_cases hlu : |u| ≤ (A * Real.log eps) ^ 2
  · have hlb : (1 + |u|) ^ (m + 2) *
        ‖φ eps u - ∑ k ∈ range (n + 1), ((eps⁻¹) ^ k : ℝ) • a k u‖ ≤
        (L * (1 + A ^ 2) ^ (dl + m + 2)) * (eps⁻¹) ^ n := by
      calc
        _ ≤ (1 + |u|) ^ (m + 2) * (L * (eps⁻¹) ^ (n + 1) * (1 + |u|) ^ dl) :=
          mul_le_mul_of_nonneg_left (hlow u hlu) (by positivity)
        _ = L * (eps⁻¹) ^ (n + 1) * (1 + |u|) ^ (dl + m + 2) := by rw [pow_add, pow_add]; ring
        _ ≤ L * (eps⁻¹) ^ (n + 1) * ((1 + A ^ 2) ^ (dl + m + 2) * eps) := by
          gcongr
          exact (pow_le_pow_left₀ hbase (by linarith) _).trans hlogpoly
        _ = _ := by rw [pow_succ]; field_simp
    have hrest : 0 ≤ K * M + 2 ^ (m + 2) * (K * E + H) + B := by positivity
    exact hlb.trans (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (pow_nonneg hi0 _))
  · have hcut : (A * Real.log eps) ^ 2 ≤ |u| := (not_le.mp hlu).le
    have htail := stretchedExp_log_cutoff (by positivity : 0 < c / 2) heps hnA ht0 hcut
    have hUu : U ≤ |u| := by
      have hlog1 : 1 ≤ Real.log eps := (le_max_left _ _).trans hlog
      have hlogU : U ≤ Real.log eps := (le_max_right _ _).trans hlog
      have hx : Real.log eps ≤ A * Real.log eps := by nlinarith
      nlinarith
    have hcoeff : (1 + |u|) ^ (m + 2) *
        ‖∑ k ∈ range (n + 1), ((eps⁻¹) ^ k : ℝ) • a k u‖ ≤ B * (eps⁻¹) ^ n := by
      calc
        _ ≤ (1 + |u|) ^ (m + 2) * ∑ k ∈ range (n + 1), ‖((eps⁻¹) ^ k : ℝ) • a k u‖ :=
          mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
        _ ≤ ∑ k ∈ range (n + 1), (1 + |u|) ^ (m + 2) * ‖a k u‖ := by
          rw [mul_sum]
          apply sum_le_sum
          intro k _
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hi0 _)]
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact (mul_le_mul_of_nonneg_right (pow_le_one₀ hi0 hi1) (norm_nonneg _)).trans_eq (one_mul _)
        _ ≤ B * Real.exp (-(c / 2) * Real.sqrt |u|) := hb u
        _ ≤ _ := mul_le_mul_of_nonneg_left htail hB
    have hactual : (1 + |u|) ^ (m + 2) * ‖φ eps u‖ ≤
        (K * M + 2 ^ (m + 2) * (K * E + H)) * (eps⁻¹) ^ n := by
      by_cases hmu : |u| ≤ eps ^ (1 + δ)
      · have hu2 : |u| ≤ eps ^ (2 : ℕ) := by
          refine hmu.trans ?_
          rw [← Real.rpow_natCast]
          exact Real.rpow_le_rpow_of_exponent_le heps (by norm_num; linarith)
        have hpoly : (1 + |u|) ^ (m + 2) * eps ^ d ≤ 2 ^ (m + 2) * eps ^ (d + 2 * (m + 2)) := by
          calc
            _ ≤ (2 * eps ^ 2) ^ (m + 2) * eps ^ d := by gcongr; nlinarith [sq_nonneg eps]
            _ = _ := by rw [mul_pow, ← pow_mul, pow_add]; ring
        have h1 : (1 + |u|) ^ (m + 2) * (K * (1 + |u|) ^ d * Real.exp (-c * Real.sqrt |u|)) ≤
            K * M * (eps⁻¹) ^ n := by
          calc
            _ = K * ((1 + |u|) ^ (m + 2 + d) * Real.exp (-c * Real.sqrt |u|)) := by rw [pow_add]; ring
            _ ≤ K * (M * Real.exp (-(c / 2) * Real.sqrt |u|)) := mul_le_mul_of_nonneg_left (hm |u| ht0) hK
            _ ≤ _ := by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left htail (mul_nonneg hK hM)
        have h2 : (1 + |u|) ^ (m + 2) * (K * eps ^ d * Real.exp (-c * eps)) ≤
            2 ^ (m + 2) * K * E * (eps⁻¹) ^ n := by
          calc
            _ = K * ((1 + |u|) ^ (m + 2) * eps ^ d) * Real.exp (-c * eps) := by ring
            _ ≤ K * (2 ^ (m + 2) * eps ^ (d + 2 * (m + 2))) * Real.exp (-c * eps) := by gcongr
            _ = (2 ^ (m + 2) * K) * (eps ^ (d + 2 * (m + 2)) * Real.exp (-c * eps)) := by ring
            _ ≤ _ := by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (he eps heps) (by positivity : 0 ≤ (2 : ℝ) ^ (m + 2) * K)
        have hh := mul_le_mul_of_nonneg_left (hmed u hUu hmu) (pow_nonneg hbase (m + 2))
        rw [mul_add] at hh
        have hHextra : 0 ≤ 2 ^ (m + 2) * H * (eps⁻¹) ^ n := by positivity
        nlinarith
      · have hh := hr heps (not_le.mp hmu).le hH (norm_nonneg _) (hhigh u)
        have hextra : 0 ≤ K * M * (eps⁻¹) ^ n + 2 ^ (m + 2) * K * E * (eps⁻¹) ^ n := by positivity
        nlinarith
    calc
      _ ≤ (1 + |u|) ^ (m + 2) * (‖φ eps u‖ + ‖∑ k ∈ range (n + 1), ((eps⁻¹) ^ k : ℝ) • a k u‖) :=
        mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by positivity)
      _ ≤ C * (eps⁻¹) ^ n := by
        rw [mul_add]
        apply (add_le_add hactual hcoeff).trans
        have hlow0 : 0 ≤ L * (1 + A ^ 2) ^ (dl + m + 2) * (eps⁻¹) ^ n := by positivity
        dsimp [C]
        nlinarith

end PGM
