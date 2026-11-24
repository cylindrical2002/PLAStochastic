import PLAStochastic.ForMathlib.Analysis.Fourier.BandBudget
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable

/-! # Measurability of coefficients forced by the local expansions -/

noncomputable section

open MeasureTheory Filter Topology Finset

namespace PGM

/-- Coefficient measurability is a consequence of the low-frequency expansion,
so the inversion assembly need not add it as a separate hypothesis. -/
theorem FourierBandEstimates.coefficient_aestronglyMeasurable {φ : ℝ → ℝ → ℂ}
    {a : ℕ → ℝ → ℂ} (h : FourierBandEstimates φ a)
    (hφ : ∀ᶠ eps in atTop, AEStronglyMeasurable (φ eps)) (k : ℕ) :
    AEStronglyMeasurable (a k) := by
  classical
  induction k using Nat.strong_induction_on with
  | h k ih =>
    obtain ⟨E, hE⟩ := eventually_atTop.mp hφ
    let Φ : ℝ → ℝ → ℂ := fun eps u => if E ≤ eps then φ eps u else 0
    let b : ℝ → ℝ → ℂ := fun eps u => (eps ^ k : ℝ) •
      (Φ eps u - ∑ i ∈ range k, ((eps⁻¹) ^ i : ℝ) • a i u)
    have hb (eps : ℝ) : AEStronglyMeasurable (b eps) := by
      have hm : AEStronglyMeasurable (Φ eps) := by
        by_cases he : E ≤ eps
        · simpa only [Φ, if_pos he] using hE eps he
        · simpa only [Φ, if_neg he] using (aestronglyMeasurable_const : AEStronglyMeasurable (fun _ : ℝ => (0 : ℂ)))
      exact (hm.sub (Finset.aestronglyMeasurable_fun_sum _ fun i hi =>
        (ih i (mem_range.mp hi)).const_smul ((eps⁻¹) ^ i : ℝ))).const_smul (eps ^ k : ℝ)
    obtain ⟨K, hK, d, hlocal⟩ := h.low k 1 (by norm_num)
    have hlim (u : ℝ) : Tendsto (fun eps => b eps u) atTop (𝓝 (a k u)) := by
      have hlog : ∀ᶠ eps : ℝ in atTop, Real.sqrt |u| ≤ Real.log eps :=
        Real.tendsto_log_atTop.eventually (eventually_ge_atTop (Real.sqrt |u|))
      have hbound : ∀ᶠ eps : ℝ in atTop,
          ‖b eps u - a k u‖ ≤ (K * (1 + |u|) ^ d) * eps⁻¹ := by
        filter_upwards [hlocal, hlog, eventually_ge_atTop E, eventually_ge_atTop (1 : ℝ)]
          with eps hl hs he he1
        have he0 : 0 < eps := zero_lt_one.trans_le he1
        have hlog0 : 0 ≤ Real.log eps := Real.log_nonneg he1
        have hcut : |u| ≤ (1 * Real.log eps) ^ 2 := by
          simp only [one_mul]
          nlinarith [Real.sq_sqrt (abs_nonneg u), Real.sqrt_nonneg |u|]
        have heq : b eps u - a k u = (eps ^ k : ℝ) •
            (φ eps u - ∑ i ∈ range (k + 1), ((eps⁻¹) ^ i : ℝ) • a i u) := by
          dsimp [b, Φ]
          rw [if_pos he, sum_range_succ]
          push_cast
          have hcancel : eps ^ k * (eps⁻¹) ^ k = 1 := by
            rw [← mul_pow, mul_inv_cancel₀ he0.ne', one_pow]
          have hc : (eps ^ k : ℂ) * ((eps⁻¹) ^ k : ℂ) = 1 := by
            exact_mod_cast hcancel
          push_cast at hc
          calc
            _ = (eps ^ k : ℂ) * (φ eps u -
                (∑ i ∈ range k, ((eps⁻¹) ^ i : ℂ) * a i u + ((eps⁻¹) ^ k : ℂ) * a k u)) +
                ((eps ^ k : ℂ) * ((eps⁻¹) ^ k : ℂ) - 1) * a k u := by push_cast; ring
            _ = _ := by push_cast; rw [hc]; ring
        rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg he0.le _)]
        calc
          _ ≤ eps ^ k * (K * (eps⁻¹) ^ (k + 1) * (1 + |u|) ^ d) :=
            mul_le_mul_of_nonneg_left (hl u hcut) (pow_nonneg he0.le _)
          _ = _ := by
            have hc : eps ^ k * (eps⁻¹) ^ k = 1 := by
              rw [← mul_pow, mul_inv_cancel₀ he0.ne', one_pow]
            rw [pow_succ]
            calc
              _ = (eps ^ k * (eps⁻¹) ^ k) * K * (1 + |u|) ^ d * eps⁻¹ := by ring
              _ = _ := by rw [hc]; ring
      apply tendsto_iff_norm_sub_tendsto_zero.mpr
      exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) hbound
        (by simpa only [mul_zero] using tendsto_inv_atTop_zero.const_mul (K * (1 + |u|) ^ d))
    exact aestronglyMeasurable_of_tendsto_ae atTop hb (ae_of_all _ hlim)

end PGM
