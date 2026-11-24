import PLAStochastic.Index.GEP.Kernel.LinearSurvival.BlockConcentration
import PLAStochastic.Index.GEP.Kernel.LinearSurvival.Recursion

/-! # Sharp survival from a killed potential and free-sum concentration -/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set

/-- The numerical recursion gives the exact square-root exponent at every horizon. -/
theorem linearSurvival_recursion_all {q : ℕ → ℝ} {N : ℕ} (hN : 1 ≤ N)
    (hq : ∀ n, q n ≤ 1) (hmono : Antitone q) {H c B ρ : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1) (hρ : 0 ≤ ρ)
    (hB : Real.sqrt ((N + 1 : ℕ) : ℝ) ≤ B) (hHB : 4 * H ≤ c * B)
    (hrec : ∀ n : ℕ, N ≤ n → q n ≤ q (n / 2) / 8 +
      (H + ρ * ∑ j ∈ Finset.range n, q j) / (c * Real.sqrt ((n + 1 : ℕ) : ℝ)))
    (n : ℕ) (hn : 1 ≤ n) :
    q n ≤ 32 * B / c * ((Real.sqrt n)⁻¹ + ρ) := by
  have hB1 : 1 ≤ B := (Real.one_le_sqrt.2 (by exact_mod_cast (show 1 ≤ N + 1 by omega))).trans hB
  have hB0 : 0 ≤ B := by linarith
  have hshort (m : ℕ) (hm : 1 ≤ m) (hs : 16 * ρ / c * Real.sqrt m ≤ 1) :
      q m ≤ B / Real.sqrt m := by
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    have hr : 0 < Real.sqrt m := Real.sqrt_pos.2 hm0
    have hroot : Real.sqrt ((m + 1 : ℕ) : ℝ) ≤ 2 * Real.sqrt m := by
      apply Real.sqrt_le_iff.2
      refine ⟨by positivity, ?_⟩
      have hsq := Real.sq_sqrt hm0.le
      have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
      push_cast
      nlinarith
    have hsmall : ρ * Real.sqrt ((m + 1 : ℕ) : ℝ) ≤ c / 8 := by
      have hs' : 16 * ρ * Real.sqrt m / c ≤ 1 := by
        simpa only [div_mul_eq_mul_div] using hs
      have h := (div_le_iff₀ hc).1 hs'
      nlinarith [mul_le_mul_of_nonneg_left hroot hρ]
    exact (linearSurvival_recursion_short hN hq hc hρ hB hHB hrec m hsmall).trans
      (div_le_div_of_nonneg_left hB0 hr
        (Real.sqrt_le_sqrt (by exact_mod_cast (Nat.le_succ m))))
  have hb := linearSurvival_all_horizons hmono hq
    (show 0 ≤ 16 * ρ / c by positivity) hB1 hshort n hn
  calc
    q n ≤ 2 * B * ((Real.sqrt n)⁻¹ + 16 * ρ / c) := hb
    _ ≤ 32 * B / c * ((Real.sqrt n)⁻¹ + ρ) := by
      have hcoef : 2 * B ≤ 32 * B / c := by
        rw [le_div_iff₀ hc]
        nlinarith [mul_le_mul_of_nonneg_left hc1 (show 0 ≤ 2 * B by positivity)]
      have hh := mul_le_mul_of_nonneg_right hcoef (inv_nonneg.2 (Real.sqrt_nonneg (n : ℝ)))
      calc
        _ = 2 * B * (Real.sqrt n)⁻¹ + (32 * B / c) * ρ := by ring
        _ ≤ (32 * B / c) * (Real.sqrt n)⁻¹ + (32 * B / c) * ρ :=
          add_le_add hh le_rfl
        _ = _ := by ring

/-- Actual iid survival has the sharp inverse-square-root bound. The hypotheses
are one-step integrability, a killed-potential inequality, and free-sum interval
concentration; each is discharged for the original regular class downstream. -/
theorem linearSurvival_sharp_of_inputs
    {C lam L : ℝ} (hC : 1 ≤ C) (hlam : 0 ≤ lam)
    (hL : 0 < L) {n₀ : ℕ} (hn₀ : 1 ≤ n₀) :
    ∃ K : ℝ, 0 < K ∧ ∀ μ : ProbabilityMeasure ℝ,
      Integrable (fun y : ℝ => y) (μ : Measure ℝ) →
      ∀ ρ : ℝ, 0 ≤ ρ →
      (∀ d : ℝ, 0 ≤ d →
        (∫ y, linearSurvivalPotential C lam (d - y) ∂(μ : Measure ℝ)) ≤
          linearSurvivalPotential C lam d + ρ) →
      (∀ k : ℕ, n₀ ≤ k → ∀ z r : ℝ, 0 ≤ r →
        (iidLaw μ).real {g | gapKeys g k ∈ Icc z (z + r)} ≤ L * r / Real.sqrt k) →
      ∀ δ : ℝ, 0 ≤ δ → ∀ n : ℕ, 1 ≤ n →
        (iidLaw μ).real (linearSurvivalStay δ n) ≤
          K * (1 + δ) * ((Real.sqrt n)⁻¹ + ρ) := by
  let c := min 1 (1 / (16 * L))
  have hc : 0 < c := lt_min zero_lt_one (by positivity)
  have hc1 : c ≤ 1 := min_le_left _ _
  have hcL : 16 * L * c ≤ 1 := by
    have h : c ≤ 1 / (16 * L) := min_le_right _ _
    have hh := (le_div_iff₀ (by positivity : 0 < 16 * L)).1 h
    nlinarith
  let N := 2 * n₀
  have hN : 1 ≤ N := by dsimp [N]; omega
  let A := max (Real.sqrt ((N + 1 : ℕ) : ℝ)) (4 * C / c)
  have hA : 0 < A := (Real.sqrt_pos.2 (by positivity)).trans_le (le_max_left _ _)
  refine ⟨32 * A / c, by positivity, ?_⟩
  intro μ hi ρ hρ hstep hconc δ hδ n hn
  let q := fun j => (iidLaw μ).real (linearSurvivalStay δ j)
  have hq : ∀ j, q j ≤ 1 := fun _ => measureReal_le_one
  have hmono : Antitone q := fun i j hij =>
    measureReal_mono (linearSurvivalStay_antitone δ hij)
  have hB : Real.sqrt ((N + 1 : ℕ) : ℝ) ≤ A * (1 + δ) := by
    have ha : Real.sqrt ((N + 1 : ℕ) : ℝ) ≤ A := le_max_left _ _
    nlinarith [mul_nonneg hA.le hδ]
  have hHB : 4 * linearSurvivalPotential C lam δ ≤ c * (A * (1 + δ)) := by
    have hh := linearSurvivalPotential_le (lam := lam) (by linarith : 0 ≤ C) δ
    rw [abs_of_nonneg hδ] at hh
    have ha : 4 * C ≤ A * c := (div_le_iff₀ hc).1 (le_max_right _ _)
    have hhC : δ + C ≤ C * (1 + δ) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hC) hδ]
    nlinarith [mul_le_mul_of_nonneg_right ha (show 0 ≤ 1 + δ by positivity)]
  have hrec (j : ℕ) (hj : N ≤ j) : q j ≤ q (j / 2) / 8 +
      (linearSurvivalPotential C lam δ + ρ * ∑ i ∈ Finset.range j, q i) /
        (c * Real.sqrt ((j + 1 : ℕ) : ℝ)) := by
    have hj1 : 1 ≤ j := hN.trans hj
    have hk : n₀ ≤ j - j / 2 := by dsimp [N] at hj; omega
    have hkp : 0 < Real.sqrt ((j - j / 2 : ℕ) : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast (show 0 < j - j / 2 by omega))
    have hratio : Real.sqrt ((j + 1 : ℕ) : ℝ) ≤ 2 * Real.sqrt ((j - j / 2 : ℕ) : ℝ) := by
      apply Real.sqrt_le_iff.2
      refine ⟨by positivity, ?_⟩
      have hs := Real.sq_sqrt (show (0 : ℝ) ≤ (j - j / 2 : ℕ) by positivity)
      have hjle : j + 1 ≤ 4 * (j - j / 2) := by omega
      have hreal : ((j + 1 : ℕ) : ℝ) ≤ 4 * ((j - j / 2 : ℕ) : ℝ) := by exact_mod_cast hjle
      nlinarith
    have hinterval (z : ℝ) : (iidLaw μ).real
        {g | gapKeys g (j - j / 2) ∈ Icc z (z + c * Real.sqrt ((j + 1 : ℕ) : ℝ))} ≤ 1 / 8 := by
      apply (hconc (j - j / 2) hk z (c * Real.sqrt ((j + 1 : ℕ) : ℝ)) (by positivity)).trans
      rw [div_le_iff₀ hkp]
      have hh := mul_le_mul_of_nonneg_left hratio (show 0 ≤ L * c by positivity)
      have hbound := mul_le_mul_of_nonneg_right hcL hkp.le
      nlinarith
    have hh := linearSurvival_split_le μ hi hC hlam hδ
      (show 0 < c * Real.sqrt ((j + 1 : ℕ) : ℝ) by positivity) hstep
      (j / 2) (j - j / 2) hinterval
    have he : j / 2 + (j - j / 2) = j := Nat.add_sub_of_le (Nat.div_le_self _ _)
    simpa only [he, q, one_div, mul_comm (8 : ℝ)⁻¹, ← div_eq_mul_inv] using hh
  have hh := linearSurvival_recursion_all hN hq hmono hc hc1 hρ hB hHB hrec n hn
  convert hh using 1
  ring

end
end PGM
