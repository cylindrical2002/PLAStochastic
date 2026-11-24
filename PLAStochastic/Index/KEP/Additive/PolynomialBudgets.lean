import PLAStochastic.Index.KEP.Additive.OfCountTail
import PLAStochastic.Index.GEP.Additive.OfInputs

/-!
# Polynomial cutoffs cost a bounded number of endpoint layers

This closes the all-parameter numerical part of the KEP conditional assembly.
The only remaining probability inputs are actual layer-count bounds and actual
early-termination probabilities. The denominator is the existing exact `gepC`.
-/

set_option autoImplicit false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory

theorem kep_log_polynomial_div_le {eps lam M p : ℝ}
    (heps : 2 ≤ eps) (hlam : Real.log eps ≤ lam) (hM : 1 ≤ M) (hp : 0 ≤ p) :
    Real.log (M * eps ^ p) / lam ≤ Real.log M / Real.log 2 + p := by
  have hepspos : 0 < eps := by linarith
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlogeps : Real.log 2 ≤ Real.log eps := Real.log_le_log (by norm_num) heps
  have hlampos : 0 < lam := lt_of_lt_of_le hlog2 (hlogeps.trans hlam)
  have hMpos : 0 < M := by linarith
  have hrpowpos : 0 < eps ^ p := Real.rpow_pos_of_pos hepspos p
  rw [Real.log_mul hMpos.ne' hrpowpos.ne', Real.log_rpow hepspos, add_div]
  have h1 : Real.log M / lam ≤ Real.log M / Real.log 2 :=
    div_le_div_of_nonneg_left (Real.log_nonneg hM) hlog2 (hlogeps.trans hlam)
  have h2 : p * Real.log eps / lam ≤ p := by
    rw [div_le_iff₀ hlampos]
    exact mul_le_mul_of_nonneg_left hlam hp
  linarith only [h1, h2]

theorem kep_log_count_budget_div_le {eps lam A D p : ℝ}
    (heps : 2 ≤ eps) (hlam : Real.log eps ≤ lam)
    (hA : 1 ≤ A) (hD : 0 ≤ D) (hp : 0 ≤ p) :
    Real.log (A + D * eps ^ p) / lam ≤ Real.log (A + D) / Real.log 2 + p := by
  have heps1 : 1 ≤ eps := by linarith
  have hpow : 1 ≤ eps ^ p := Real.one_le_rpow heps1 hp
  have hbudgetpos : 0 < A + D * eps ^ p := by nlinarith
  have hpoly : A + D * eps ^ p ≤ (A + D) * eps ^ p := by
    nlinarith only [hpow, hA]
  have hlampos : 0 < lam := lt_of_lt_of_le (Real.log_pos (by norm_num : (1 : ℝ) < 2))
    ((Real.log_le_log (by norm_num) heps).trans hlam)
  calc
    Real.log (A + D * eps ^ p) / lam ≤ Real.log ((A + D) * eps ^ p) / lam :=
      div_le_div_of_nonneg_right (Real.log_le_log hbudgetpos hpoly) hlampos.le
    _ ≤ _ := kep_log_polynomial_div_le heps hlam (by linarith) hp

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Full all-parameter height reduction with explicit polynomial count and cutoff inputs.
This is conditional on the stated probability inputs, not a general Model K theorem. -/
theorem H_EP_additive_of_polynomial_count_tail
    {keys : ℕ → Ω → ℕ → ℝ} (hkeys : ∀ n, Measurable (keys n))
    {m : ℝ → ℕ → ℝ} {eps0 B A D R K p r : ℝ}
    (hB : 0 ≤ B) (hA : 1 ≤ A) (hD : 0 ≤ D) (hR : 1 ≤ R) (hK : 0 ≤ K)
    (hp : 0 ≤ p) (hr : 0 ≤ r)
    (hm0 : ∀ eps, eps0 ≤ eps → m eps 0 = 1)
    (hpos : ∀ eps, eps0 ≤ eps → ∀ j, 0 < m eps j)
    (hstep : ∀ eps, eps0 ≤ eps → ∀ j, 2 * m eps j ≤ m eps (j + 1))
    (hc : ∀ eps, eps0 ≤ eps → Real.log eps ≤ gepLogC eps)
    (hlog : ∀ eps, eps0 ≤ eps → ∀ j : ℕ,
      |Real.log (m eps j) - j * gepLogC eps| ≤ B)
    (hcount : ∀ eps, eps0 ≤ eps → ∀ n : ℕ, 2 ≤ n → ∀ L,
      (∫ ω, ((epLayer eps (keys n ω) n L).2 : ℝ) ∂P) ≤
        A * (n : ℝ) / m eps L + D * eps ^ p)
    (htail : ∀ eps, eps0 ≤ eps → ∀ n : ℕ, 2 ≤ n → ∀ L,
      (R * eps ^ r) * m eps L < n →
        P.real {ω | epHeight eps (keys n ω) n ≤ L} ≤ K * m eps L / n) :
    ∃ eps1 C : ℝ, ∀ eps, eps1 ≤ eps → ∀ n : ℕ, 2 ≤ n →
      |(∫ ω, (epHeight eps (keys n ω) n : ℝ) ∂P) -
        Real.log n / Real.log (gepC eps)| ≤ C := by
  refine ⟨max eps0 2,
    2 + B / Real.log 2 + Real.log (A + D) / Real.log 2 + p +
      Real.log R / Real.log 2 + r + 2 * K, ?_⟩
  intro eps heps n hn
  obtain ⟨heps0, heps2⟩ := max_le_iff.mp heps
  have heps1 : 1 ≤ eps := by linarith
  have hepspos : 0 < eps := by linarith
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hclower : Real.log 2 ≤ gepLogC eps :=
    (Real.log_le_log (by norm_num) heps2).trans (hc eps heps0)
  have hcpos : 0 < gepLogC eps := lt_of_lt_of_le hlog2 hclower
  have hDp : 0 ≤ D * eps ^ p := mul_nonneg hD (Real.rpow_nonneg hepspos.le p)
  have hRr : 1 ≤ R * eps ^ r :=
    one_le_mul_of_one_le_of_one_le hR (Real.one_le_rpow heps1 hr)
  have hmain := integral_epHeight_additive_of_count_tail heps1 (hkeys n) hn
    (hm0 eps heps0) (hpos eps heps0) (hstep eps heps0) hcpos (hlog eps heps0)
    hA hDp hRr hK (hcount eps heps0 n hn) (htail eps heps0 n hn)
  have hBc : B / gepLogC eps ≤ B / Real.log 2 :=
    div_le_div_of_nonneg_left hB hlog2 hclower
  have hq : Real.log eps ≤ Real.log (⌊2 * eps⌋₊ + 1) := by
    apply Real.log_le_log hepspos
    have hfloor : 2 * eps < (⌊2 * eps⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one (2 * eps)
    linarith
  have hcnt := kep_log_count_budget_div_le heps2 hq hA hD hp
  have hcut := kep_log_polynomial_div_le heps2 (hc eps heps0) hR hr
  have hKR : 2 * K / (R * eps ^ r) ≤ 2 * K := by
    rw [div_le_iff₀ (by linarith : 0 < R * eps ^ r)]
    nlinarith only [hRr, hK]
  rw [gepC, Real.log_exp]
  linarith only [hmain, hBc, hcnt, hcut, hKR]

end

end PGM
