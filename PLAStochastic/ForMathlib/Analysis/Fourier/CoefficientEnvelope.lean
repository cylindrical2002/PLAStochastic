import PLAStochastic.ForMathlib.Analysis.Asymptotics.InverseExpansion
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Exponential envelopes of inverse-power coefficients

Recursive coefficient extraction is sufficient when the requested exponential
weight may depend on the finite order. It avoids choosing an inverse Vandermonde
matrix and gives a smaller positive rate. No positivity of the coefficients is used.
-/

noncomputable section

open Finset Filter Topology

namespace PGM

/-- Uniform real-space inverse-power expansions. -/
def UniformInverseExpansion (F : ℝ → ℝ → ℝ) (a : ℕ → ℝ → ℝ) : Prop :=
  ∀ n : ℕ, ∃ K E : ℝ, ∀ eps ≥ E, ∀ x : ℝ,
    |F eps x - inversePolynomial (fun i => a i x) n eps| ≤ K * (eps⁻¹) ^ (n + 1)

/-- Isolating the last coefficient in a uniform finite expansion. -/
theorem inverse_coefficient_bound {F : ℝ → ℝ → ℝ} {a : ℕ → ℝ → ℝ}
    {n : ℕ} {eps x D θ K : ℝ} (he : 1 ≤ eps) (hD : 0 ≤ D)
    (hF : |F eps x| ≤ D * Real.exp (-θ * |x|))
    (ha : ∀ i < n, |a i x| ≤ D * Real.exp (-θ * |x|))
    (hR : |F eps x - inversePolynomial (fun i => a i x) n eps| ≤ K * (eps⁻¹) ^ (n + 1)) :
    |a n x| ≤ ((n : ℝ) + 1) * D * eps ^ n * Real.exp (-θ * |x|) + K * eps⁻¹ := by
  have he0 : 0 < eps := zero_lt_one.trans_le he
  have hi0 : 0 ≤ eps⁻¹ := (inv_pos.mpr he0).le
  have hi1 : eps⁻¹ ≤ 1 := (inv_le_one₀ he0).mpr he
  have hsum : |∑ i ∈ range n, a i x * (eps⁻¹) ^ i| ≤ (n : ℝ) * D * Real.exp (-θ * |x|) := by
    calc
      _ ≤ ∑ i ∈ range n, |a i x * (eps⁻¹) ^ i| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ range n, D * Real.exp (-θ * |x|) := by
        apply sum_le_sum
        intro i hi
        rw [abs_mul, abs_of_nonneg (pow_nonneg hi0 _)]
        exact (mul_le_mul (ha i (mem_range.mp hi)) (pow_le_one₀ hi0 hi1)
          (pow_nonneg hi0 _) (by positivity)).trans_eq (mul_one _)
      _ = _ := by simp; ring
  have hlast : |a n x| * (eps⁻¹) ^ n ≤
      ((n : ℝ) + 1) * D * Real.exp (-θ * |x|) + K * (eps⁻¹) ^ (n + 1) := by
    have htri := abs_sub_le (inversePolynomial (fun i => a i x) n eps) (F eps x)
      (∑ i ∈ range n, a i x * (eps⁻¹) ^ i)
    have htri' := abs_sub (F eps x) (∑ i ∈ range n, a i x * (eps⁻¹) ^ i)
    rw [inversePolynomial, sum_range_succ, add_sub_cancel_left, abs_mul,
      abs_of_nonneg (pow_nonneg hi0 _)] at htri
    rw [abs_sub_comm] at hR
    simp only [inversePolynomial, sum_range_succ] at hR
    nlinarith
  have hmul := mul_le_mul_of_nonneg_right hlast (pow_nonneg he0.le n)
  have hcancel : (eps⁻¹) ^ n * eps ^ n = 1 := by rw [← mul_pow, inv_mul_cancel₀ he0.ne', one_pow]
  have hcancel' : (eps⁻¹) ^ (n + 1) * eps ^ n = eps⁻¹ := by rw [pow_succ', mul_assoc, hcancel, mul_one]
  calc
    _ = (|a n x| * (eps⁻¹) ^ n) * eps ^ n := by rw [mul_assoc, hcancel, mul_one]
    _ ≤ _ := hmul
    _ = _ := by rw [add_mul, mul_assoc K, hcancel']; ring

/-- Optimize the extraction parameter against the spatial exponential envelope. -/
theorem exponential_envelope_of_last_coefficient {F : ℝ → ℝ → ℝ} {a : ℕ → ℝ → ℝ}
    {n : ℕ} {D θ E : ℝ} (hD : 0 ≤ D) (hθ : 0 < θ)
    (hF : ∀ eps ≥ E, ∀ x, |F eps x| ≤ D * Real.exp (-θ * |x|))
    (ha : ∀ i < n, ∀ x, |a i x| ≤ D * Real.exp (-θ * |x|))
    (hR : ∃ K E' : ℝ, ∀ eps ≥ E', ∀ x,
      |F eps x - inversePolynomial (fun i => a i x) n eps| ≤ K * (eps⁻¹) ^ (n + 1)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x,
      |a n x| ≤ B * Real.exp (-(θ / ((n : ℝ) + 1)) * |x|) := by
  obtain ⟨K, E', hR⟩ := hR
  let L := max 1 (max E E')
  let b := θ / ((n : ℝ) + 1)
  have hL : 1 ≤ L := le_max_left _ _
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hb : 0 < b := by dsimp [b]; positivity
  refine ⟨((n : ℝ) + 1) * D * L ^ n + |K| * L⁻¹, by positivity, fun x => ?_⟩
  let eps := L * Real.exp (b * |x|)
  have hex : 1 ≤ Real.exp (b * |x|) := Real.one_le_exp (by positivity)
  have heL : L ≤ eps := by dsimp [eps]; nlinarith
  have he : 1 ≤ eps := hL.trans heL
  have hf := hF eps ((le_max_left E E').trans ((le_max_right _ _).trans heL)) x
  have hr := hR eps ((le_max_right E E').trans ((le_max_right _ _).trans heL)) x
  have hbound := inverse_coefficient_bound he hD hf (fun i hi => ha i hi x) hr
  have hi : eps⁻¹ = L⁻¹ * Real.exp (-b * |x|) := by
    dsimp [eps]
    rw [mul_inv, ← Real.exp_neg, neg_mul]
  have hp : eps ^ n * Real.exp (-θ * |x|) = L ^ n * Real.exp (-b * |x|) := by
    dsimp [eps]
    rw [mul_pow, ← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]
    congr 2
    dsimp [b]
    field_simp
    ring
  calc
    _ ≤ ((n : ℝ) + 1) * D * (eps ^ n * Real.exp (-θ * |x|)) + |K| * eps⁻¹ := by
      have hk := mul_le_mul_of_nonneg_right (le_abs_self K) (inv_nonneg.mpr (by linarith : 0 ≤ eps))
      nlinarith [hbound]
    _ = _ := by rw [hp, hi]; dsimp [b]; ring

/-- Every finite set of coefficients inherits a common positive exponential rate. -/
theorem UniformInverseExpansion.finite_coefficient_envelopes {F : ℝ → ℝ → ℝ}
    {a : ℕ → ℝ → ℝ} (h : UniformInverseExpansion F a)
    (henv : ∃ D θ E : ℝ, 0 ≤ D ∧ 0 < θ ∧
      ∀ eps ≥ E, ∀ x, |F eps x| ≤ D * Real.exp (-θ * |x|)) (N : ℕ) :
    ∃ D θ E : ℝ, 0 ≤ D ∧ 0 < θ ∧
      (∀ eps ≥ E, ∀ x, |F eps x| ≤ D * Real.exp (-θ * |x|)) ∧
      ∀ i ≤ N, ∀ x, |a i x| ≤ D * Real.exp (-θ * |x|) := by
  have haux : ∀ n : ℕ, ∃ D θ E : ℝ, 0 ≤ D ∧ 0 < θ ∧
      (∀ eps ≥ E, ∀ x, |F eps x| ≤ D * Real.exp (-θ * |x|)) ∧
      ∀ i < n, ∀ x, |a i x| ≤ D * Real.exp (-θ * |x|) := by
    intro n
    induction n with
    | zero =>
      obtain ⟨D, θ, E, hD, hθ, hF⟩ := henv
      exact ⟨D, θ, E, hD, hθ, hF, fun i hi => by omega⟩
    | succ n ih =>
      obtain ⟨D, θ, E, hD, hθ, hF, ha⟩ := ih
      obtain ⟨B, hB, hb⟩ := exponential_envelope_of_last_coefficient hD hθ hF ha (h n)
      let θ' := θ / ((n : ℝ) + 1)
      have hθ' : 0 < θ' := by dsimp [θ']; positivity
      have hθle : θ' ≤ θ := by
        dsimp [θ']
        exact div_le_self hθ.le (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
      have hex (x : ℝ) : Real.exp (-θ * |x|) ≤ Real.exp (-θ' * |x|) :=
        Real.exp_le_exp.mpr (by nlinarith [abs_nonneg x])
      refine ⟨D + B, θ', E, by positivity, hθ', ?_, ?_⟩
      · intro eps he x
        exact (hF eps he x).trans (mul_le_mul (by linarith) (hex x) (Real.exp_pos _).le (by positivity))
      · intro i hi x
        rcases (show i ≤ n by omega).lt_or_eq with hi' | rfl
        · exact (ha i hi' x).trans
            (mul_le_mul (by linarith) (hex x) (Real.exp_pos _).le (by positivity))
        · exact (hb x).trans (mul_le_mul_of_nonneg_right (by linarith : B ≤ D + B) (Real.exp_pos _).le)
  obtain ⟨D, θ, E, hD, hθ, hF, ha⟩ := haux (N + 1)
  exact ⟨D, θ, E, hD, hθ, hF, fun i hi => ha i (by omega)⟩

/-- Support restrictions pass to every asymptotic coefficient. -/
theorem UniformInverseExpansion.coefficient_zero {F : ℝ → ℝ → ℝ} {a : ℕ → ℝ → ℝ}
    (h : UniformInverseExpansion F a) {x : ℝ}
    (hz : ∀ᶠ eps in atTop, F eps x = 0) (n : ℕ) : a n x = 0 := by
  have ha : HasInverseExpansion (fun eps => F eps x) (fun k => a k x) := by
    intro k
    obtain ⟨K, E, hK⟩ := h k
    exact ⟨K, E, fun eps he => hK eps he x⟩
  obtain ⟨E, hE⟩ := eventually_atTop.mp hz
  have hb : HasInverseExpansion (fun eps => F eps x) (fun _ => 0) := by
    intro k
    refine ⟨0, E, fun eps he => ?_⟩
    simp [hE eps he, inversePolynomial]
  exact congrFun (ha.unique hb) n

end PGM
