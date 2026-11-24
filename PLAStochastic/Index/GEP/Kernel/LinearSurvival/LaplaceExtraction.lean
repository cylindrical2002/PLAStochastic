import PLAStochastic.Index.GEP.OrbitClosure.Defs

/-!
# Sharp linear survival: analytic extraction and the drift cutoff

These lemmas retain the exact inverse-square-root exponent. The probability
input is a bound on the Laplace generating function up to the drift time scale;
no fluctuation identity or survival bound is postulated as an axiom.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Finset

/-- Survival below a linear boundary, including time zero. -/
def linearSurvivalSet {Ω : Type*} (X : ℕ → Ω → ℝ) (δ ρ : ℝ) (n : ℕ) : Set Ω :=
  {ω | ∀ j ≤ n, (∑ i ∈ range j, X i ω) ≤ δ + ρ * j}

/-- Increasing the observation horizon only removes surviving paths. -/
theorem linearSurvivalSet_antitone {Ω : Type*} (X : ℕ → Ω → ℝ) (δ ρ : ℝ) :
    Antitone (linearSurvivalSet X δ ρ) := by
  intro m n hmn ω hω j hj
  exact hω j (hj.trans hmn)

/-- The actual finite-horizon survival probabilities are decreasing. -/
theorem linearSurvivalProb_antitone {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (X : ℕ → Ω → ℝ) (δ ρ : ℝ) :
    Antitone (fun n => P.real (linearSurvivalSet X δ ρ n)) := by
  intro m n hmn
  exact measureReal_mono (linearSurvivalSet_antitone X δ ρ hmn)

/-- Exponential damping makes any sequence of probabilities summable. -/
theorem linearSurvival_laplace_summable {q : ℕ → ℝ}
    (hq0 : ∀ j, 0 ≤ q j) (hq1 : ∀ j, q j ≤ 1) {n : ℕ} (hn : 1 ≤ n) :
    Summable (fun j => q j * Real.exp (-(j : ℝ) / n)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have he : Summable (fun j : ℕ => Real.exp (-(j : ℝ) / n)) := by
    have h := summable_geometric_of_lt_one (Real.exp_pos (-(1 : ℝ) / n)).le
      (Real.exp_lt_one_iff.2 (div_neg_of_neg_of_pos (by norm_num) hn0))
    convert h using 1
    ext j
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  exact Summable.of_nonneg_of_le (fun j => mul_nonneg (hq0 j) (Real.exp_pos _).le)
    (fun j => by simpa using mul_le_mul_of_nonneg_right (hq1 j) (Real.exp_pos _).le) he

/-- A nonnegative decreasing sequence is controlled by one Laplace transform.
The factor is independent of the horizon. -/
theorem linearSurvival_laplace_extract {q : ℕ → ℝ} (hq : ∀ j, 0 ≤ q j)
    (hmono : Antitone q) {n : ℕ} (hn : 1 ≤ n)
    (hs : Summable (fun j => q j * Real.exp (-(j : ℝ) / n))) :
    (n : ℝ) * q n ≤ Real.exp 1 * ∑' j, q j * Real.exp (-(j : ℝ) / n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlow : (n : ℝ) * (q n * Real.exp (-1)) ≤
      ∑ j ∈ range n, q j * Real.exp (-(j : ℝ) / n) := by
    calc
      _ = ∑ _j ∈ range n, q n * Real.exp (-1) := by simp
      _ ≤ _ := by
        apply sum_le_sum
        intro j hj
        have hjn : (j : ℝ) ≤ n := by exact_mod_cast (mem_range.1 hj).le
        apply mul_le_mul (hmono (mem_range.1 hj).le) ?_ (Real.exp_pos _).le (hq j)
        apply Real.exp_le_exp.2
        rw [le_div_iff₀ hn0]
        linarith
  have hsum := hs.sum_le_tsum (range n) (fun j _ => mul_nonneg (hq j) (Real.exp_pos _).le)
  have h := mul_le_mul_of_nonneg_left (hlow.trans hsum) (Real.exp_pos 1).le
  calc
    (n : ℝ) * q n = Real.exp 1 * ((n : ℝ) * (q n * Real.exp (-1))) := by
      have he : Real.exp 1 * Real.exp (-1) = 1 := by rw [← Real.exp_add]; norm_num
      calc
        _ = ((n : ℝ) * q n) * (Real.exp 1 * Real.exp (-1)) := by rw [he, mul_one]
        _ = _ := by ring
    _ ≤ _ := h

/-- A square-root bound on the Laplace transform yields the sharp coefficient
bound, without a Tauberian asymptotic or any loss in the exponent. -/
theorem linearSurvival_inv_sqrt_of_laplace {q : ℕ → ℝ} (hq : ∀ j, 0 ≤ q j)
    (hmono : Antitone q) {K : ℝ} {n : ℕ} (hn : 1 ≤ n)
    (hs : Summable (fun j => q j * Real.exp (-(j : ℝ) / n)))
    (hQ : (∑' j, q j * Real.exp (-(j : ℝ) / n)) ≤ K * Real.sqrt n) :
    q n ≤ Real.exp 1 * K / Real.sqrt n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hroot := Real.sqrt_pos.2 hn0
  have h := (linearSurvival_laplace_extract hq hmono hn hs).trans
    (mul_le_mul_of_nonneg_left hQ (Real.exp_pos _).le)
  rw [le_div_iff₀ hroot]
  apply (mul_le_mul_iff_left₀ hroot).mp
  calc
    q n * Real.sqrt n * Real.sqrt n = (n : ℝ) * q n := by
      rw [mul_assoc, ← sq, Real.sq_sqrt hn0.le, mul_comm]
    _ ≤ Real.exp 1 * K * Real.sqrt n := by simpa only [mul_assoc] using h

/-- The integer drift cutoff is within a factor two of its real value. -/
theorem linearSurvival_floor_cutoff {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    let m := ⌊ρ⁻¹ ^ 2⌋₊
    1 ≤ m ∧ ρ * Real.sqrt m ≤ 1 ∧ (Real.sqrt m)⁻¹ ≤ 2 * ρ := by
  dsimp
  have hi : (1 : ℝ) ≤ ρ⁻¹ := (one_le_inv₀ hρ).2 hρ1
  have ht1 : (1 : ℝ) ≤ ρ⁻¹ ^ 2 := by nlinarith
  have hm1 : 1 ≤ ⌊ρ⁻¹ ^ 2⌋₊ := Nat.le_floor (by simpa using ht1)
  have hm1r : (1 : ℝ) ≤ ⌊ρ⁻¹ ^ 2⌋₊ := by exact_mod_cast hm1
  have hmle : (⌊ρ⁻¹ ^ 2⌋₊ : ℝ) ≤ ρ⁻¹ ^ 2 := Nat.floor_le (sq_nonneg _)
  have htlt : ρ⁻¹ ^ 2 < (⌊ρ⁻¹ ^ 2⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have hprod : ρ * ρ⁻¹ = 1 := mul_inv_cancel₀ hρ.ne'
  have hs : 0 < Real.sqrt (⌊ρ⁻¹ ^ 2⌋₊ : ℝ) := Real.sqrt_pos.2 (by linarith)
  have hsquare := Real.sq_sqrt (show (0 : ℝ) ≤ ⌊ρ⁻¹ ^ 2⌋₊ by positivity)
  refine ⟨hm1, ?_, ?_⟩
  · have hr : Real.sqrt (⌊ρ⁻¹ ^ 2⌋₊ : ℝ) ≤ ρ⁻¹ := by
      apply Real.sqrt_le_iff.2
      exact ⟨by positivity, hmle⟩
    calc
      _ ≤ ρ * ρ⁻¹ := mul_le_mul_of_nonneg_left hr hρ.le
      _ = 1 := hprod
  · rw [inv_eq_one_div, div_le_iff₀ hs]
    have hhalf : ρ⁻¹ ^ 2 ≤ 2 * (⌊ρ⁻¹ ^ 2⌋₊ : ℝ) := by linarith
    have hroot : ρ⁻¹ ≤ 2 * Real.sqrt (⌊ρ⁻¹ ^ 2⌋₊ : ℝ) := by
      nlinarith [sq_nonneg (ρ⁻¹ - 2 * Real.sqrt (⌊ρ⁻¹ ^ 2⌋₊ : ℝ))]
    have := mul_le_mul_of_nonneg_left hroot hρ.le
    nlinarith

/-- A sharp survival bound below the drift cutoff extends to all horizons.
The large-drift case uses only that probabilities are at most one. -/
theorem linearSurvival_all_horizons {q : ℕ → ℝ} (hmono : Antitone q)
    (hq1 : ∀ j, q j ≤ 1) {ρ K : ℝ} (hρ : 0 ≤ ρ) (hK : 1 ≤ K)
    (hshort : ∀ n : ℕ, 1 ≤ n → ρ * Real.sqrt n ≤ 1 → q n ≤ K / Real.sqrt n)
    (n : ℕ) (hn : 1 ≤ n) :
    q n ≤ 2 * K * ((Real.sqrt n)⁻¹ + ρ) := by
  have hK0 : 0 ≤ K := by linarith
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hs := Real.sqrt_pos.2 hn0
  by_cases hsmall : ρ * Real.sqrt n ≤ 1
  · have hbound := hshort n hn hsmall
    calc
      q n ≤ K * (Real.sqrt n)⁻¹ := by simpa only [div_eq_mul_inv] using hbound
      _ ≤ _ := by nlinarith [inv_pos.2 hs, mul_nonneg hK0 hρ]
  by_cases hρ1 : ρ ≤ 1
  · have hρ0 : 0 < ρ := by
      by_contra h
      have : ρ = 0 := le_antisymm (le_of_not_gt h) hρ
      simp [this] at hsmall
    let m := ⌊ρ⁻¹ ^ 2⌋₊
    obtain ⟨hm1, hms, hmroot⟩ := linearSurvival_floor_cutoff hρ0 hρ1
    have hmn : m ≤ n := by
      by_contra h
      have hnms : Real.sqrt n ≤ Real.sqrt m := Real.sqrt_le_sqrt (by exact_mod_cast (by omega : n ≤ m))
      have := (mul_le_mul_of_nonneg_left hnms hρ).trans hms
      exact hsmall this
    have hm := hshort m hm1 hms
    calc
      q n ≤ q m := hmono hmn
      _ ≤ K * (Real.sqrt m)⁻¹ := by simpa only [div_eq_mul_inv] using hm
      _ ≤ K * (2 * ρ) := mul_le_mul_of_nonneg_left hmroot hK0
      _ ≤ _ := by nlinarith [inv_nonneg.2 hs.le]
  · have hρlarge : 1 < ρ := lt_of_not_ge hρ1
    calc
      q n ≤ 1 := hq1 n
      _ ≤ _ := by nlinarith [inv_nonneg.2 hs.le, mul_le_mul_of_nonneg_left hρlarge.le hK0]

/-- The full linear-boundary estimate follows from its Laplace bound on the
small-drift time scale. This theorem states the remaining analytic premise
explicitly; it does not assert a fluctuation identity. -/
theorem linearSurvivalProb_le_of_laplace {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    {δ ρ A : ℝ} (hρ : 0 ≤ ρ) (hA : 1 ≤ Real.exp 1 * A)
    (hQ : ∀ n : ℕ, 1 ≤ n → ρ * Real.sqrt n ≤ 1 →
      (∑' j, P.real (linearSurvivalSet X δ ρ j) * Real.exp (-(j : ℝ) / n)) ≤
        A * Real.sqrt n) (n : ℕ) (hn : 1 ≤ n) :
    P.real (linearSurvivalSet X δ ρ n) ≤
      2 * (Real.exp 1 * A) * ((Real.sqrt n)⁻¹ + ρ) := by
  have hq0 : ∀ j, 0 ≤ P.real (linearSurvivalSet X δ ρ j) := fun _ => measureReal_nonneg
  have hq1 : ∀ j, P.real (linearSurvivalSet X δ ρ j) ≤ 1 := fun _ => measureReal_le_one
  have hmono := linearSurvivalProb_antitone P X δ ρ
  apply linearSurvival_all_horizons hmono hq1 hρ hA ?_ n hn
  intro m hm hdrift
  exact linearSurvival_inv_sqrt_of_laplace hq0 hmono hm
    (linearSurvival_laplace_summable hq0 hq1 hm) (hQ m hm hdrift)

end

end PGM
