import PLAStochastic.Index.GEP.Kernel.Tail.Scalar.DiracTail
import PLAStochastic.Index.GEP.Kernel.Tail.Weighted.OuterGreen
import PLAStochastic.Index.GEP.Kernel.Tail.Weighted.PinLength

/-! # Infinite actual Dirac-tail time budget, including the four outer rows -/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set
set_option maxHeartbeats 1600000

def kernelWeightedDiracTailTerm (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ) (w s x : ℝ)
    (m : ℕ) : ℝ :=
  kernelPhysicalOuterWeight ν w s ((w + 1) / x) *
    (((m : ℝ) + 1 + w) * (Real.exp (s * (((m : ℝ) + 1) + 1) / ((w + 1) / x)) *
      kernelDiracPin ν f w (m + 1) x))

theorem kernelWeightedDiracTailTerm_nonneg (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ}
    (hf0 : ∀ t, 0 ≤ f t) {w x : ℝ} (s : ℝ) (hw : 0 ≤ w) (hx : 0 ≤ x) (m : ℕ) :
    0 ≤ kernelWeightedDiracTailTerm ν f w s x m :=
  mul_nonneg (kernelPhysicalOuterWeight_nonneg ν w s _) (mul_nonneg (by positivity)
    (mul_nonneg (Real.exp_nonneg _) (kernelDiracPin_nonneg ν hf0 w (m + 1) hx)))

/-- All random times in the true Dirac term, with the opposite pin and the
actual two products of outer Green series. The exponent 16 is fixed before
`ζ`, and the chosen density can be the same density as for the bulk term. -/
theorem kernel_regLaw_weighted_dirac_tail_infinite (D θ vlo vhi : ℝ)
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ ζ : ℝ, 0 < ζ → ∃ σ K : ℝ, 0 < σ ∧ 0 < K ∧
      ∀ ν : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
      ∀ f : ℝ → ℝ, Measurable f → (∀ x, 0 ≤ f x) → (∀ x, f x ≤ D) →
        (∀ x ≤ 0, f x = 0) → (∀ x, f x ≤ D * Real.exp (-θ * x)) →
      ∀ w s x : ℝ, 1 ≤ w → 0 ≤ s → s ≤ ρ / w ^ 2 → s ≤ σ → 0 < x →
        Summable (kernelWeightedDiracTailTerm ν f w s x) ∧
        (∑' m, kernelWeightedDiracTailTerm ν f w s x m) ≤ K * w ^ 16 * Real.exp (ζ * x) := by
  obtain ⟨k, hk, hspec⟩ := kernel_regLaw_dirac_pin_spectral D θ vlo vhi (1 / 2)
    hD hθ hvlo hv (by norm_num)
  obtain ⟨ρ, Os, Ol, hρ, hOs, hOl, houter⟩ := kernel_regLaw_physical_outer_weight_bound D θ vlo vhi hD hθ hvlo hv
  refine ⟨min ρ (k / 16), lt_min hρ (by positivity), ?_⟩
  intro ζ hζ
  obtain ⟨c, hc, hsmall⟩ := kernel_regLaw_dirac_pin_small_slope_of_density D θ vlo vhi ζ hθ hvlo hv hζ
  let Ks := Os * (D * Real.exp θ) * (3 * (1 + 1 / (c / 2)) ^ 4)
  let Kl := Ol * (D * (4 + 3 * D) * Real.exp k) * (3 * (1 + 4 / k) ^ 4)
  have hKs : 0 < Ks := by positivity
  have hKl : 0 < Kl := by positivity
  refine ⟨c / 4, Ks + Kl, by positivity, by positivity, ?_⟩
  intro ν hν f hf hf0 hfD hfz hfe w s x hw hs0 hs hsc hx
  let a := (w + 1) / x
  have hw0 : 0 < w := by linarith
  have ha : 0 < a := div_pos (by linarith) hx
  have hnonneg := kernelWeightedDiracTailTerm_nonneg ν hf0 s hw0.le hx.le
  have hso : s ≤ ρ / w ^ 2 := hs.trans (div_le_div_of_nonneg_right (min_le_left _ _) (sq_nonneg w))
  have hsk : s ≤ (2 * k) / (32 * w ^ 2) := by
    apply hs.trans
    convert div_le_div_of_nonneg_right (min_le_right ρ (k / 16)) (sq_nonneg w) using 1
    ring
  have hsum (N : ℕ) : (∑ m ∈ Finset.range N, kernelWeightedDiracTailTerm ν f w s x m) ≤
      (Ks + Kl) * w ^ 16 * Real.exp (ζ * x) := by
    have ho := houter ν hν w s a hw hs0 hso ha
    by_cases halo : a ≤ 1 / 2
    · rw [if_pos halo] at ho
      have hpin (m : ℕ) : Real.exp (s * (((m : ℝ) + 1) + 1) / a) * kernelDiracPin ν f w (m + 1) x ≤
          (D * Real.exp θ * Real.exp (ζ * x)) * Real.exp (-(c / 2) * ((m : ℝ) + 1)) := by
        have hh := hsmall ν hν f hf hf0 hfD hfz hfe w x hw0 hx halo (m + 1) (by omega)
        have hN : 1 ≤ (m : ℝ) + 1 := by nlinarith [Nat.cast_nonneg (α := ℝ) m]
        have hwt := kernel_small_time_weight_absorb ha hc hs0 hsc hN (X := ζ * x)
        have hh' := mul_le_mul_of_nonneg_left hh (Real.exp_nonneg (s * (((m : ℝ) + 1) + 1) / a))
        have hfirst : Real.exp (s * (((m : ℝ) + 1) + 1) / a) * kernelDiracPin ν f w (m + 1) x ≤
            (D * Real.exp θ / (w + 1)) * Real.exp (ζ * x - (c / 2) * ((m : ℝ) + 1) / a) := by
          apply hh'.trans
          simpa only [Nat.cast_add, Nat.cast_one, mul_left_comm] using
            mul_le_mul_of_nonneg_left hwt (show 0 ≤ D * Real.exp θ / (w + 1) by positivity)
        have he : ζ * x - (c / 2) * ((m : ℝ) + 1) / a ≤ ζ * x + (-(c / 2) * ((m : ℝ) + 1)) := by
          have hh' : (c / 2) * ((m : ℝ) + 1) ≤ (c / 2) * ((m : ℝ) + 1) / a :=
            (le_div_iff₀ ha).mpr (by
              have := mul_le_mul_of_nonneg_left (show a ≤ 1 by linarith) (show 0 ≤ (c / 2) * ((m : ℝ) + 1) by positivity)
              nlinarith)
          linarith
        have hh'' := mul_le_mul (div_le_self (show 0 ≤ D * Real.exp θ by positivity) (by linarith : 1 ≤ w + 1))
          (Real.exp_le_exp.mpr he) (Real.exp_nonneg _) (show 0 ≤ D * Real.exp θ by positivity)
        exact hfirst.trans (hh''.trans_eq (by rw [Real.exp_add]; ring))
      have hsum' : (∑ m ∈ Finset.range N, kernelWeightedDiracTailTerm ν f w s x m) ≤
          (Os * w ^ 2) * (D * Real.exp θ * Real.exp (ζ * x)) *
            ((2 + w) * (1 + 1 / (c / 2)) ^ 4) := by
        calc
          _ ≤ ∑ m ∈ Finset.range N, (Os * w ^ 2) *
              (((m : ℝ) + 1 + w) * ((D * Real.exp θ * Real.exp (ζ * x)) * Real.exp (-(c / 2) * ((m : ℝ) + 1)))) := by
            apply Finset.sum_le_sum
            intro m hm
            exact mul_le_mul ho (mul_le_mul_of_nonneg_left (hpin m) (by positivity))
              (mul_nonneg (by positivity) (mul_nonneg (Real.exp_nonneg _) (kernelDiracPin_nonneg ν hf0 w (m + 1) hx.le))) (by positivity)
          _ = (Os * w ^ 2) * (D * Real.exp θ * Real.exp (ζ * x)) *
              ∑ m ∈ Finset.range N, ((m : ℝ) + 1 + w) * Real.exp (-(c / 2) * ((m : ℝ) + 1)) := by
            simp only [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro m hm
            ring
          _ ≤ _ := mul_le_mul_of_nonneg_left (kernel_single_exp_sum_le (half_pos hc) hw0.le N) (by positivity)
      have ht : (2 + w) * (1 + 1 / (c / 2)) ^ 4 ≤ 3 * (1 + 1 / (c / 2)) ^ 4 * w := by
        nlinarith [mul_le_mul_of_nonneg_right (show 2 + w ≤ 3 * w by linarith)
          (show 0 ≤ (1 + 1 / (c / 2)) ^ 4 by positivity)]
      have hh := hsum'.trans (mul_le_mul_of_nonneg_left ht (by positivity))
      have hw16 : w ^ 3 ≤ w ^ 16 := pow_le_pow_right₀ hw (by norm_num)
      have hfinal : Ks * w ^ 3 * Real.exp (ζ * x) ≤ (Ks + Kl) * w ^ 16 * Real.exp (ζ * x) := by
        gcongr
        linarith
      apply hh.trans
      calc
        _ = Ks * w ^ 3 * Real.exp (ζ * x) := by dsimp [Ks]; ring
        _ ≤ _ := hfinal
    · rw [if_neg halo] at ho
      have hu : 0 < k / (4 * w ^ 2) := by positivity
      have hpin (m : ℕ) : Real.exp (s * (((m : ℝ) + 1) + 1) / a) * kernelDiracPin ν f w (m + 1) x ≤
          (D * (4 + 3 * D) * Real.exp k) * w *
            Real.exp (-(k / (4 * w ^ 2)) * ((m : ℝ) + 1)) := by
        have hfirst := (hspec ν hν f hf hf0 hfD w x hw hx (le_of_lt (lt_of_not_ge halo))
          (m + 1) (by omega)).trans (kernel_dirac_spectral_polynomial hD.le hk.le hw)
        have hwt := kernel_large_time_weight_absorb (le_of_lt (lt_of_not_ge halo))
          (by positivity : 0 < 2 * k) hw0 hs0 hsk (show 1 ≤ (m : ℝ) + 1 by nlinarith [Nat.cast_nonneg (α := ℝ) m])
        have hh := mul_le_mul_of_nonneg_left hfirst (Real.exp_nonneg (s * (((m : ℝ) + 1) + 1) / a))
        apply hh.trans
        have hh' := mul_le_mul_of_nonneg_left hwt (show 0 ≤ (D * (4 + 3 * D) * Real.exp k) * w by positivity)
        simpa only [Nat.cast_add, Nat.cast_one, mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0), mul_left_comm] using hh'

      have hsum' : (∑ m ∈ Finset.range N, kernelWeightedDiracTailTerm ν f w s x m) ≤
          (Ol * w ^ 6) * ((D * (4 + 3 * D) * Real.exp k) * w) *
            ((2 + w) * (1 + 1 / (k / (4 * w ^ 2))) ^ 4) := by
        calc
          _ ≤ ∑ m ∈ Finset.range N, (Ol * w ^ 6) *
              (((m : ℝ) + 1 + w) * (((D * (4 + 3 * D) * Real.exp k) * w) *
                Real.exp (-(k / (4 * w ^ 2)) * ((m : ℝ) + 1)))) := by
            apply Finset.sum_le_sum
            intro m hm
            exact mul_le_mul ho (mul_le_mul_of_nonneg_left (hpin m) (by positivity))
              (mul_nonneg (by positivity) (mul_nonneg (Real.exp_nonneg _) (kernelDiracPin_nonneg ν hf0 w (m + 1) hx.le))) (by positivity)
          _ = (Ol * w ^ 6) * ((D * (4 + 3 * D) * Real.exp k) * w) *
              ∑ m ∈ Finset.range N, ((m : ℝ) + 1 + w) * Real.exp (-(k / (4 * w ^ 2)) * ((m : ℝ) + 1)) := by
            simp only [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro m hm
            ring
          _ ≤ _ := mul_le_mul_of_nonneg_left (kernel_single_exp_sum_le hu hw0.le N) (by positivity)
      have hh := hsum'.trans (mul_le_mul_of_nonneg_left (kernel_time_sum_polynomial hk hw) (by positivity))
      have he : 1 ≤ Real.exp (ζ * x) := Real.one_le_exp_iff.mpr (by positivity)
      have hfinal : Kl * w ^ 16 ≤ (Ks + Kl) * w ^ 16 * Real.exp (ζ * x) := by
        calc
          _ ≤ (Ks + Kl) * w ^ 16 := by gcongr; linarith
          _ ≤ _ := le_mul_of_one_le_right (by positivity) he
      apply hh.trans
      calc
        _ = Kl * w ^ 16 := by dsimp [Kl]; ring
        _ ≤ _ := hfinal
  exact ⟨summable_of_sum_range_le hnonneg hsum, Real.tsum_le_of_sum_range_le hnonneg hsum⟩

end
end PGM
