import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Finite asymptotic expansions in inverse powers

All orders are fixed before the real parameter tends to infinity. The remainder
constant and threshold may depend on the order; no convergence of a series is asserted.
-/

namespace PGM

noncomputable section

open Filter Topology Finset

/-- The finite polynomial in the reciprocal parameter, including its constant term. -/
def inversePolynomial (a : ℕ → ℝ) (M : ℕ) (eps : ℝ) : ℝ :=
  ∑ j ∈ range (M + 1), a j * (eps⁻¹) ^ j

/-- An actual remainder estimate at one fixed order. -/
def HasInverseExpansionAtOrder (f : ℝ → ℝ) (a : ℕ → ℝ) (M : ℕ) : Prop :=
  ∃ K eps0 : ℝ, ∀ eps : ℝ, eps0 ≤ eps →
    |f eps - inversePolynomial a M eps| ≤ K * (eps⁻¹) ^ (M + 1)

/-- One coefficient sequence supplies every fixed finite order. -/
def HasInverseExpansion (f : ℝ → ℝ) (a : ℕ → ℝ) : Prop :=
  ∀ M : ℕ, HasInverseExpansionAtOrder f a M

/-- A scalar is bounded by a fixed inverse power at infinity. -/
def IsInverseOrder (f : ℝ → ℝ) (n : ℕ) : Prop :=
  ∃ K eps0 : ℝ, ∀ eps : ℝ, eps0 ≤ eps → |f eps| ≤ K * (eps⁻¹) ^ n

theorem IsInverseOrder.nonneg_witness {f : ℝ → ℝ} {n : ℕ} (h : IsInverseOrder f n) :
    ∃ K eps0 : ℝ, 0 ≤ K ∧ 1 ≤ eps0 ∧ ∀ eps : ℝ, eps0 ≤ eps → |f eps| ≤ K * (eps⁻¹) ^ n := by
  obtain ⟨K, eps0, h⟩ := h
  refine ⟨|K|, max 1 eps0, abs_nonneg _, le_max_left _ _, fun eps heps => ?_⟩
  have he1 : 1 ≤ eps := (le_max_left _ _).trans heps
  exact (h eps ((le_max_right _ _).trans heps)).trans
    (mul_le_mul_of_nonneg_right (le_abs_self K) (pow_nonneg (by positivity) _))

theorem IsInverseOrder.tendsto_zero {f : ℝ → ℝ} {n : ℕ}
    (h : IsInverseOrder f n) (hn : 0 < n) : Tendsto f atTop (𝓝 0) := by
  obtain ⟨K, eps0, -, -, hbound⟩ := h.nonneg_witness
  have hp : Tendsto (fun eps : ℝ => K * (eps⁻¹) ^ n) atTop (𝓝 0) := by
    have ht : Tendsto (fun eps : ℝ => (eps⁻¹) ^ n) atTop (𝓝 ((0 : ℝ) ^ n)) :=
      tendsto_inv_atTop_zero.pow n
    simpa only [zero_pow hn.ne', mul_zero] using ht.const_mul K
  apply tendsto_iff_dist_tendsto_zero.mpr
  simp only [Real.dist_eq, sub_zero]
  exact squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _)
    (eventually_atTop.mpr ⟨eps0, hbound⟩) hp

theorem HasInverseExpansionAtOrder.tendsto_zero_order {f : ℝ → ℝ} {a : ℕ → ℝ}
    (h : HasInverseExpansionAtOrder f a 0) : Tendsto f atTop (𝓝 (a 0)) := by
  have he : IsInverseOrder (fun eps => f eps - a 0) 1 := by
    simpa only [IsInverseOrder, HasInverseExpansionAtOrder, inversePolynomial, zero_add, sum_range_one,
      pow_zero, mul_one] using h
  have ht := he.tendsto_zero (by norm_num)
  have heq : f = (fun eps => (f eps - a 0) + a 0) := by funext eps; ring
  rw [heq]
  simpa only [zero_add] using ht.add_const (a 0)

theorem HasInverseExpansionAtOrder.bounded_zero_order {f : ℝ → ℝ} {a : ℕ → ℝ}
    (h : HasInverseExpansionAtOrder f a 0) : ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ eps in atTop, |f eps| ≤ B := by
  obtain ⟨K, eps0, h0⟩ := h
  refine ⟨|a 0| + |K|, by positivity, eventually_atTop.mpr ⟨max 1 eps0, fun eps heps => ?_⟩⟩
  have he1 : 1 ≤ eps := (le_max_left _ _).trans heps
  have hepos : 0 < eps := by linarith
  have hi0 : 0 ≤ eps⁻¹ := (inv_pos.mpr hepos).le
  have hi1 : eps⁻¹ ≤ 1 := (inv_le_one₀ hepos).mpr he1
  have hb := h0 eps ((le_max_right _ _).trans heps)
  simp only [inversePolynomial, sum_range_one, pow_zero, mul_one, zero_add, pow_one] at hb
  have hk := mul_le_mul_of_nonneg_right (le_abs_self K) hi0
  have hk1 := mul_le_mul_of_nonneg_left hi1 (abs_nonneg K)
  have ha := abs_sub_le (f eps) (a 0) 0
  simp only [sub_zero, mul_one] at ha hk1
  linarith

/-- Once lower coefficients agree, the remainder at order `n` forces the next one. -/
theorem inverseExpansion_coeff_eq {f : ℝ → ℝ} {a b : ℕ → ℝ} {n : ℕ}
    (ha : HasInverseExpansionAtOrder f a n) (hb : HasInverseExpansionAtOrder f b n)
    (hab : ∀ j < n, a j = b j) : a n = b n := by
  obtain ⟨Ka, ea, ha⟩ := ha
  obtain ⟨Kb, eb, hb⟩ := hb
  have hbound : ∀ eps : ℝ, max 1 (max ea eb) ≤ eps → |a n - b n| ≤ (Ka + Kb) * eps⁻¹ := by
    intro eps heps
    have he1 : 1 ≤ eps := (le_max_left _ _).trans heps
    have hea : ea ≤ eps := (le_max_left _ _).trans ((le_max_right _ _).trans heps)
    have heb : eb ≤ eps := (le_max_right _ _).trans ((le_max_right _ _).trans heps)
    have hepos : 0 < eps := by linarith
    have hinv : 0 < eps⁻¹ := inv_pos.mpr hepos
    have heq : inversePolynomial a n eps - inversePolynomial b n eps =
        (a n - b n) * (eps⁻¹) ^ n := by
      unfold inversePolynomial
      rw [sum_range_succ, sum_range_succ]
      have hsum : ∑ j ∈ range n, a j * (eps⁻¹) ^ j = ∑ j ∈ range n, b j * (eps⁻¹) ^ j := by
        apply sum_congr rfl
        intro j hj
        rw [hab j (mem_range.mp hj)]
      rw [hsum]
      ring
    have hle : |(a n - b n) * (eps⁻¹) ^ n| ≤ (Ka + Kb) * (eps⁻¹) ^ (n + 1) := by
      rw [← heq]
      have htri := abs_sub_le (inversePolynomial a n eps) (f eps) (inversePolynomial b n eps)
      rw [abs_sub_comm (inversePolynomial a n eps) (f eps)] at htri
      linarith [ha eps hea, hb eps heb]
    rw [abs_mul, abs_of_pos (pow_pos hinv n), pow_succ] at hle
    apply (mul_le_mul_iff_right₀ (pow_pos hinv n)).mp
    nlinarith
  have hlim : Tendsto (fun eps : ℝ => (Ka + Kb) * eps⁻¹) atTop (𝓝 0) := by
    simpa using tendsto_inv_atTop_zero.const_mul (Ka + Kb)
  have hz : |a n - b n| ≤ 0 := ge_of_tendsto hlim
    (eventually_atTop.mpr ⟨max 1 (max ea eb), hbound⟩)
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hz (abs_nonneg _)))

/-- Inverse-power asymptotic coefficients are unique. -/
theorem HasInverseExpansion.unique {f : ℝ → ℝ} {a b : ℕ → ℝ}
    (ha : HasInverseExpansion f a) (hb : HasInverseExpansion f b) : a = b := by
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih => exact inverseExpansion_coeff_eq (ha n) (hb n) ih

/-- Dropping the top term preserves an actual estimate at the preceding order. -/
theorem HasInverseExpansionAtOrder.drop {f : ℝ → ℝ} {a : ℕ → ℝ} {M : ℕ}
    (h : HasInverseExpansionAtOrder f a (M + 1)) : HasInverseExpansionAtOrder f a M := by
  obtain ⟨K, eps0, h⟩ := h
  refine ⟨|K| + |a (M + 1)|, max 1 eps0, fun eps heps => ?_⟩
  have he1 : 1 ≤ eps := (le_max_left _ _).trans heps
  have he0 : eps0 ≤ eps := (le_max_right _ _).trans heps
  have hepos : 0 < eps := by linarith
  have hinv0 : 0 ≤ eps⁻¹ := (inv_pos.mpr hepos).le
  have hinv1 : eps⁻¹ ≤ 1 := (inv_le_one₀ hepos).mpr he1
  have hpow : 0 ≤ (eps⁻¹) ^ (M + 1) := pow_nonneg hinv0 _
  have hrem := h eps he0
  have heq : f eps - inversePolynomial a M eps =
      (f eps - inversePolynomial a (M + 1) eps) + a (M + 1) * (eps⁻¹) ^ (M + 1) := by
    have hpoly : inversePolynomial a (M + 1) eps =
        inversePolynomial a M eps + a (M + 1) * (eps⁻¹) ^ (M + 1) := by
      unfold inversePolynomial
      rw [sum_range_succ]
    rw [hpoly]
    ring
  rw [heq]
  calc
    |(f eps - inversePolynomial a (M + 1) eps) + a (M + 1) * (eps⁻¹) ^ (M + 1)| ≤
        |f eps - inversePolynomial a (M + 1) eps| + |a (M + 1) * (eps⁻¹) ^ (M + 1)| :=
      abs_add_le _ _
    _ ≤ |K| * (eps⁻¹) ^ (M + 1) + |a (M + 1)| * (eps⁻¹) ^ (M + 1) := by
      rw [abs_mul, abs_of_nonneg hpow]
      apply add_le_add _ le_rfl
      calc
        |f eps - inversePolynomial a (M + 1) eps| ≤ K * (eps⁻¹) ^ (M + 1 + 1) := hrem
        _ ≤ |K| * (eps⁻¹) ^ (M + 1 + 1) := mul_le_mul_of_nonneg_right (le_abs_self K) (by positivity)
        _ ≤ |K| * (eps⁻¹) ^ (M + 1) := by
          rw [pow_succ]
          have ht := mul_le_mul_of_nonneg_left hinv1 (mul_nonneg (abs_nonneg K) hpow)
          simpa only [mul_one, mul_assoc] using ht
    _ = (|K| + |a (M + 1)|) * (eps⁻¹) ^ (M + 1) := by ring

/-- An expansion can be truncated to any lower order. -/
theorem HasInverseExpansionAtOrder.truncate {f : ℝ → ℝ} {a : ℕ → ℝ} {M N : ℕ}
    (h : HasInverseExpansionAtOrder f a M) (hNM : N ≤ M) : HasInverseExpansionAtOrder f a N := by
  induction M with
  | zero =>
    have hN : N = 0 := by omega
    subst N
    exact h
  | succ M ih =>
    by_cases hN : N = M + 1
    · subst N; exact h
    · exact ih h.drop (by omega)

theorem HasInverseExpansionAtOrder.bounded {f : ℝ → ℝ} {a : ℕ → ℝ} {M : ℕ}
    (h : HasInverseExpansionAtOrder f a M) : ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ eps in atTop, |f eps| ≤ B :=
  (h.truncate (Nat.zero_le M)).bounded_zero_order

/-- Two finite estimates for the same function agree on their common coefficients. -/
theorem inverseExpansion_coeff_eq_of_orders {f : ℝ → ℝ} {a b : ℕ → ℝ} {M N j : ℕ}
    (ha : HasInverseExpansionAtOrder f a M) (hb : HasInverseExpansionAtOrder f b N)
    (hjM : j ≤ M) (hjN : j ≤ N) : a j = b j := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
    apply inverseExpansion_coeff_eq (ha.truncate hjM) (hb.truncate hjN)
    intro k hk
    exact ih k hk (by omega) (by omega)

/-- Independent finite-order witnesses determine one unique compatible sequence. -/
theorem existsUnique_inverseExpansion_of_finite_orders {f : ℝ → ℝ}
    (h : ∀ M : ℕ, ∃ a : ℕ → ℝ, HasInverseExpansionAtOrder f a M) :
    ∃! a : ℕ → ℝ, HasInverseExpansion f a := by
  classical
  choose b hb using h
  let a : ℕ → ℝ := fun n => b n n
  have ha : HasInverseExpansion f a := by
    intro M
    obtain ⟨K, eps0, hM⟩ := hb M
    refine ⟨K, eps0, fun eps heps => ?_⟩
    have heq : inversePolynomial a M eps = inversePolynomial (b M) M eps := by
      apply sum_congr rfl
      intro j hj
      have hjM : j ≤ M := by have := mem_range.mp hj; omega
      have hc := inverseExpansion_coeff_eq_of_orders (hb j) (hb M) le_rfl hjM
      change b j j * _ = b M j * _
      rw [hc]
    rw [heq]
    exact hM eps heps
  exact ⟨a, ha, fun b hb => hb.unique ha⟩

/-- An error at the remainder order transfers a finite expansion. -/
theorem HasInverseExpansionAtOrder.transfer {f g : ℝ → ℝ} {a : ℕ → ℝ} {M : ℕ}
    (h : HasInverseExpansionAtOrder g a M)
    (he : ∃ K eps0 : ℝ, ∀ eps : ℝ, eps0 ≤ eps → |f eps - g eps| ≤ K * (eps⁻¹) ^ (M + 1)) :
    HasInverseExpansionAtOrder f a M := by
  obtain ⟨K, eps0, h⟩ := h
  obtain ⟨L, eps1, he⟩ := he
  refine ⟨K + L, max eps0 eps1, fun eps heps => ?_⟩
  have h1 := h eps ((le_max_left _ _).trans heps)
  have h2 := he eps ((le_max_right _ _).trans heps)
  have h3 := abs_sub_le (f eps) (g eps) (inversePolynomial a M eps)
  nlinarith

/-- Natural reciprocal powers and the target integer-power notation coincide. -/
theorem hasInverseExpansion_iff_zpow (f : ℝ → ℝ) (a : ℕ → ℝ) :
    HasInverseExpansion f a ↔ ∀ M : ℕ, ∃ K eps0 : ℝ, ∀ eps : ℝ, eps0 ≤ eps →
      |f eps - ∑ j ∈ range (M + 1), a j * eps ^ (-(j : ℤ))| ≤
        K * eps ^ (-((M : ℤ) + 1)) := by
  have hcast (M : ℕ) : (M : ℤ) + 1 = ((M + 1 : ℕ) : ℤ) := by simp
  simp only [HasInverseExpansion, HasInverseExpansionAtOrder, inversePolynomial,
    hcast, zpow_neg, zpow_natCast, inv_pow]

end

end PGM
