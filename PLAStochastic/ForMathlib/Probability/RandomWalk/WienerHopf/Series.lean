import PLAStochastic.ForMathlib.Probability.RandomWalk.WienerHopf.Factorization
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# The Wiener–Hopf factorization as an identity of formal power series

For a half-line type set `A` and any `z` with `e^{z ·}` integrable for `ρ`, the coefficient
identities give, in `ℂ⟦X⟧`,

  `(1 - ∑ E[e^{z S_n}; τ_{Aᶜ} = n] Xⁿ) (1 - ∑ E[e^{z S_n}; τ_A = n] Xⁿ) = 1 - φ(z) X`

(`wienerHopf_powerSeries`). No convergence is involved. Evaluating at any `s` for which both
ladder series converge absolutely gives the analytic factorization
(`wienerHopf_of_summable`); this covers the closed unit disk on `Re z = 0`
(`wienerHopf_of_norm_le_one`) and, with ladder-height exponential moments, a strip.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Complex Finset PowerSeries
open scoped ENNReal

namespace PGM.WienerHopf

variable {ρ : Measure ℝ} [IsProbabilityMeasure ρ] {A : Set ℝ}

theorem coeff_mk_mul_mk (u v : ℕ → ℂ) (n : ℕ) :
    coeff n (mk u * mk v) = ∑ k ∈ range (n + 1), u k * v (n - k) := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [coeff_mk]

/-- The Wiener–Hopf factorization in `ℂ⟦X⟧`. -/
theorem wienerHopf_powerSeries (hAm : MeasurableSet A) (hA : IsLadderSet A) {z : ℂ}
    (hz : Integrable (fun y : ℝ => cexp (z * y)) ρ) :
    (1 - mk (entryCoeff ρ Aᶜ z)) * (1 - mk (entryCoeff ρ A z)) =
      1 - C (stepTransform ρ z) * X := by
  set φ := stepTransform ρ z
  set a : ℂ⟦X⟧ := mk fun n => φ ^ n
  set g : ℂ⟦X⟧ := mk (survivalCoeff ρ Aᶜ z)
  set d : ℂ⟦X⟧ := mk (ladderTimeCoeff ρ A z)
  set fB : ℂ⟦X⟧ := mk (entryCoeff ρ Aᶜ z)
  set fA : ℂ⟦X⟧ := mk (entryCoeff ρ A z)
  set q : ℂ⟦X⟧ := C φ * X
  have h1 : a = g + fB * a := by
    ext n
    rw [map_add, coeff_mk_mul_mk, coeff_mk, coeff_mk]
    exact stepTransform_pow_eq_survival_add hAm.compl hz n
  have hint : ∀ (E : Set (ℕ → ℝ)), MeasurableSet E → ∀ m : ℕ,
      Integrable (E.indicator fun ω => cexp (z * partialSum m ω)) (pathLaw ρ) :=
    fun E hE m => (integrable_cexp_partialSum hz m).1.indicator hE
  have h2 : d = 1 + fA * d := by
    ext n
    rw [map_add, coeff_mk_mul_mk, coeff_mk, coeff_one]
    exact ladderTimeCoeff_eq hAm hA (fun k => hint _ (measurableSet_firstEntry_eq hAm k) k)
      (fun m => hint _ (measurableSet_isLadderTime hAm m) m) n
  have h3 : g = d := by
    ext n
    rw [coeff_mk, coeff_mk]
    exact survivalCoeff_compl_eq_ladderTimeCoeff hAm z n
  have h4 : a * (1 - q) = 1 := by
    ext n
    rw [mul_sub, mul_one, map_sub, coeff_one]
    rcases n with _ | n
    · simp [a, q]
    · rw [show a * q = X * (C φ * a) by ring, coeff_succ_X_mul, coeff_C_mul, coeff_mk, coeff_mk,
        pow_succ]
      simp [mul_comm]
  linear_combination (-(1 - fB) * (1 - fA)) * h4 + (1 - q) * (1 - fA) * h1 +
    (1 - q) * (1 - fA) * h3 + (1 - q) * h2

/-- Evaluation of a product of absolutely convergent power series (Cauchy product). -/
theorem tsum_coeff_mul {s : ℂ} {p r : ℂ⟦X⟧}
    (hp : Summable fun n => ‖s ^ n * coeff n p‖) (hr : Summable fun n => ‖s ^ n * coeff n r‖) :
    ∑' n, s ^ n * coeff n (p * r) =
      (∑' n, s ^ n * coeff n p) * ∑' n, s ^ n * coeff n r := by
  rw [tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hp hr]
  refine tsum_congr fun n => ?_
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [show s ^ n = s ^ k * s ^ (n - k) by rw [← pow_add, Nat.add_sub_cancel' hkn]]
  ring

theorem summable_one_sub_mk {s : ℂ} {u : ℕ → ℂ} (hu : Summable fun n => ‖s ^ n * u n‖) :
    Summable fun n => ‖s ^ n * coeff n (1 - mk u)‖ := by
  have h1 : Summable fun n => ‖s ^ n * coeff n (1 : ℂ⟦X⟧)‖ := by
    refine summable_of_ne_finset_zero (s := {0}) fun n hn => ?_
    simp only [Finset.mem_singleton] at hn
    simp [coeff_one, hn]
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) (h1.add hu)
  rw [map_sub, coeff_mk, mul_sub]
  exact norm_sub_le _ _

theorem tsum_one_sub_mk {s : ℂ} {u : ℕ → ℂ} (hu : Summable fun n => ‖s ^ n * u n‖) :
    ∑' n, s ^ n * coeff n (1 - mk u) = 1 - ∑' n, s ^ n * u n := by
  have h1 : ∑' n, s ^ n * coeff n (1 : ℂ⟦X⟧) = 1 := by
    rw [tsum_eq_single 0 (fun n hn => by simp [coeff_one, hn])]
    simp
  have h1s : Summable fun n => s ^ n * coeff n (1 : ℂ⟦X⟧) := by
    refine summable_of_ne_finset_zero (s := {0}) fun n hn => ?_
    simp only [Finset.mem_singleton] at hn
    simp [coeff_one, hn]
  simp_rw [map_sub, coeff_mk, mul_sub]
  rw [h1s.tsum_sub hu.of_norm, h1]

theorem tsum_one_sub_C_mul_X (s φ : ℂ) :
    ∑' n, s ^ n * coeff n (1 - C φ * X : ℂ⟦X⟧) = 1 - s * φ := by
  have hfin : ∀ n ∉ ({0, 1} : Finset ℕ), s ^ n * coeff n (1 - C φ * X : ℂ⟦X⟧) = 0 := by
    intro n hn
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
    rw [map_sub, coeff_one, coeff_C_mul, coeff_X, if_neg hn.1, if_neg hn.2]
    simp
  rw [tsum_eq_sum hfin, Finset.sum_pair (by norm_num)]
  simp [coeff_one]
  ring

/-- **Wiener–Hopf factorization under absolute convergence of the two ladder series.**
If `e^{z ·}` is `ρ`-integrable and `∑ ‖s‖ⁿ E[|e^{z S_n}|; τ = n] < ∞` for both
`τ = τ_{Aᶜ}` and `τ = τ_A`, then
`1 - s φ(z) = (1 - E[s^{τ_{Aᶜ}} e^{z S}; τ_{Aᶜ} < ∞]) (1 - E[s^{τ_A} e^{z S}; τ_A < ∞])`. -/
theorem wienerHopf_of_summable (hAm : MeasurableSet A) (hA : IsLadderSet A) {s z : ℂ}
    (hz : Integrable (fun y : ℝ => cexp (z * y)) ρ)
    (hB : Summable fun n : ℕ => ‖s‖ ^ n *
      ∫ ω in {ω | firstEntry Aᶜ ω = n}, ‖cexp (z * partialSum n ω)‖ ∂pathLaw ρ)
    (hA' : Summable fun n : ℕ => ‖s‖ ^ n *
      ∫ ω in {ω | firstEntry A ω = n}, ‖cexp (z * partialSum n ω)‖ ∂pathLaw ρ) :
    1 - s * stepTransform ρ z =
      (1 - entryTransform ρ Aᶜ s z) * (1 - entryTransform ρ A s z) := by
  have hnorm : ∀ (E : Set ℝ), Summable (fun n : ℕ => ‖s‖ ^ n *
      ∫ ω in {ω | firstEntry E ω = n}, ‖cexp (z * partialSum n ω)‖ ∂pathLaw ρ) →
      Summable fun n => ‖s ^ n * entryCoeff ρ E z n‖ := by
    intro E hE
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) hE
    rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _)
      (pow_nonneg (norm_nonneg _) _)
  have huB := hnorm Aᶜ hB
  have huA := hnorm A hA'
  have hP := congrArg (fun p : ℂ⟦X⟧ => ∑' n, s ^ n * coeff n p)
    (wienerHopf_powerSeries (ρ := ρ) hAm hA hz)
  rw [tsum_coeff_mul (summable_one_sub_mk huB) (summable_one_sub_mk huA),
    tsum_one_sub_mk huB, tsum_one_sub_mk huA, tsum_one_sub_C_mul_X] at hP
  rw [entryTransform_eq_tsum hAm.compl (fun n => (integrable_cexp_partialSum hz n).1.integrableOn)
    hB, entryTransform_eq_tsum hAm (fun n => (integrable_cexp_partialSum hz n).1.integrableOn) hA']
  exact hP.symm

/-- **Wiener–Hopf factorization on the closed unit disk** for `Re z = 0`:
`1 - s φ(z) = (1 - χ₊(s, z)) (1 - χ₋(s, z))` for `‖s‖ ≤ 1`. -/
theorem wienerHopf_of_norm_le_one (ρ : Measure ℝ) [IsProbabilityMeasure ρ] {s z : ℂ}
    (hs : ‖s‖ ≤ 1) (hz : z.re = 0) :
    1 - s * stepTransform ρ z = (1 - ascTransform ρ s z) * (1 - descTransform ρ s z) := by
  have h := wienerHopf_of_summable (ρ := ρ) measurableSet_Iic isLadderSet_Iic (s := s)
    (integrable_cexp_of_re_eq_zero hz)
    (summable_entry_of_bounded measurableSet_Iic.compl hs (by simp [hz]))
    (summable_entry_of_bounded measurableSet_Iic hs (by simp [hz]))
  rwa [compl_Iic] at h

end PGM.WienerHopf
