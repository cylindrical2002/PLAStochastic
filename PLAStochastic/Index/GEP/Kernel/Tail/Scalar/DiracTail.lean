import PLAStochastic.Index.GEP.Kernel.Tail.Scalar.PolynomialBudget
import PLAStochastic.Index.GEP.Kernel.Tail.Scalar.DiracPin

/-! # Infinite actual Dirac-tail time budget, including the four outer rows -/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set
set_option maxHeartbeats 1600000

def kernelDiracTailTerm (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ) (w x : ℝ)
    (m : ℕ) : ℝ :=
  kernelOuterWeight ν w ((w + 1) / x) *
    (((m : ℝ) + 1 + w) * kernelDiracPin ν f w (m + 1) x)

theorem kernelDiracTailTerm_nonneg (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ}
    (hf0 : ∀ t, 0 ≤ f t) {w x : ℝ} (hw : 0 ≤ w) (hx : 0 ≤ x) (m : ℕ) :
    0 ≤ kernelDiracTailTerm ν f w x m :=
  mul_nonneg (kernelOuterWeight_nonneg ν w _) (mul_nonneg (by positivity)
    (kernelDiracPin_nonneg ν hf0 w (m + 1) hx))

theorem kernel_dirac_spectral_polynomial {D k w M : ℝ}
    (hD : 0 ≤ D) (hk : 0 ≤ k) (hw : 1 ≤ w) :
    (D / (w + 1)) * (1 + 3 * Real.sqrt (D * w / (1 / 2))) *
      Real.exp (-(k * (M - 2) / (2 * w ^ 2))) ≤
        (D * (4 + 3 * D) * Real.exp k) * w *
          Real.exp (-(2 * k / (4 * w ^ 2)) * M) := by
  have hw0 : 0 < w := by linarith
  have hs : Real.sqrt (D * w / (1 / 2)) ≤ 1 + D * w := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · have hh := sq_nonneg (D * w)
      nlinarith
  have hcoef : (D / (w + 1)) * (1 + 3 * Real.sqrt (D * w / (1 / 2))) ≤
      D * ((4 + 3 * D) * w) := by
    apply mul_le_mul
    · exact div_le_self hD (by linarith)
    · nlinarith
    · positivity
    · exact hD
  have hexp : -(k * (M - 2) / (2 * w ^ 2)) ≤ k + (-(2 * k / (4 * w ^ 2)) * M) := by
    apply (mul_le_mul_iff_right₀ (show 0 < 4 * w ^ 2 by positivity)).mp
    field_simp
    nlinarith [mul_le_mul_of_nonneg_left (show 1 ≤ w ^ 2 by nlinarith) hk]
  have hh := mul_le_mul hcoef (Real.exp_le_exp.mpr hexp) (Real.exp_nonneg _) (by positivity)
  apply hh.trans_eq
  rw [Real.exp_add]
  ring

theorem kernel_single_exp_sum_le {u w : ℝ} (hu : 0 < u) (hw : 0 ≤ w) (M : ℕ) :
    (∑ m ∈ Finset.range M, ((m : ℝ) + 1 + w) * Real.exp (-u * ((m : ℝ) + 1))) ≤
      (2 + w) * (1 + 1 / u) ^ 4 := by
  simpa using kernel_triple_exp_sum_le hu hw 1 1 M

/-- All random times in the true Dirac term, with the opposite pin and the
actual two products of outer Green series. The exponent 16 is fixed before
`ζ`, and the chosen density can be the same density as for the bulk term. -/
theorem kernel_regLaw_dirac_tail_infinite (D θ vlo vhi : ℝ)
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi) :
    ∀ ζ : ℝ, 0 < ζ → ∃ K : ℝ, 0 < K ∧
      ∀ ν : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
      ∀ f : ℝ → ℝ, Measurable f → (∀ x, 0 ≤ f x) → (∀ x, f x ≤ D) →
        (∀ x ≤ 0, f x = 0) → (∀ x, f x ≤ D * Real.exp (-θ * x)) →
      ∀ w x : ℝ, 1 ≤ w → 0 < x →
        Summable (kernelDiracTailTerm ν f w x) ∧
        (∑' m, kernelDiracTailTerm ν f w x m) ≤ K * w ^ 16 * Real.exp (ζ * x) := by
  obtain ⟨k, hk, hspec⟩ := kernel_regLaw_dirac_pin_spectral D θ vlo vhi (1 / 2)
    hD hθ hvlo hv (by norm_num)
  obtain ⟨Os, Ol, hOs, hOl, houter⟩ := kernel_regLaw_outer_weight_bound D θ vlo vhi hD hθ hvlo hv
  intro ζ hζ
  obtain ⟨c, hc, hsmall⟩ := kernel_regLaw_dirac_pin_small_slope_of_density D θ vlo vhi ζ hθ hvlo hv hζ
  let Ks := Os * (D * Real.exp θ) * (3 * (1 + 1 / c) ^ 4)
  let Kl := Ol * (D * (4 + 3 * D) * Real.exp k) * (3 * (1 + 4 / (2 * k)) ^ 4)
  have hKs : 0 < Ks := by positivity
  have hKl : 0 < Kl := by positivity
  refine ⟨Ks + Kl, by positivity, ?_⟩
  intro ν hν f hf hf0 hfD hfz hfe w x hw hx
  let a := (w + 1) / x
  have hw0 : 0 < w := by linarith
  have ha : 0 < a := div_pos (by linarith) hx
  have hnonneg := kernelDiracTailTerm_nonneg ν hf0 hw0.le hx.le
  have hsum (N : ℕ) : (∑ m ∈ Finset.range N, kernelDiracTailTerm ν f w x m) ≤
      (Ks + Kl) * w ^ 16 * Real.exp (ζ * x) := by
    have ho := houter ν hν w a hw ha
    by_cases halo : a ≤ 1 / 2
    · rw [if_pos halo] at ho
      have hpin (m : ℕ) : kernelDiracPin ν f w (m + 1) x ≤
          (D * Real.exp θ * Real.exp (ζ * x)) * Real.exp (-c * ((m : ℝ) + 1)) := by
        have hh := hsmall ν hν f hf hf0 hfD hfz hfe w x hw0 hx halo (m + 1) (by omega)
        have he : ζ * x - c * (m + 1) / a ≤ ζ * x + (-c * ((m : ℝ) + 1)) := by
          have hh' : c * ((m : ℝ) + 1) ≤ c * (m + 1) / a :=
            (le_div_iff₀ ha).mpr (by
              have := mul_le_mul_of_nonneg_left (show a ≤ 1 by linarith) (show 0 ≤ c * (m + 1) by positivity)
              nlinarith)
          linarith
        have hh' := mul_le_mul (div_le_self (show 0 ≤ D * Real.exp θ by positivity) (by linarith : 1 ≤ w + 1))
          (Real.exp_le_exp.mpr he) (Real.exp_nonneg _) (show 0 ≤ D * Real.exp θ by positivity)
        apply hh.trans
        simpa only [Nat.cast_add, Nat.cast_one] using hh'.trans_eq (by rw [Real.exp_add]; ring)
      have hsum' : (∑ m ∈ Finset.range N, kernelDiracTailTerm ν f w x m) ≤
          (Os * w ^ 2) * (D * Real.exp θ * Real.exp (ζ * x)) *
            ((2 + w) * (1 + 1 / c) ^ 4) := by
        calc
          _ ≤ ∑ m ∈ Finset.range N, (Os * w ^ 2) *
              (((m : ℝ) + 1 + w) * ((D * Real.exp θ * Real.exp (ζ * x)) * Real.exp (-c * ((m : ℝ) + 1)))) := by
            apply Finset.sum_le_sum
            intro m hm
            exact mul_le_mul ho (mul_le_mul_of_nonneg_left (hpin m) (by positivity))
              (mul_nonneg (by positivity) (kernelDiracPin_nonneg ν hf0 w (m + 1) hx.le)) (by positivity)
          _ = (Os * w ^ 2) * (D * Real.exp θ * Real.exp (ζ * x)) *
              ∑ m ∈ Finset.range N, ((m : ℝ) + 1 + w) * Real.exp (-c * ((m : ℝ) + 1)) := by
            simp only [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro m hm
            ring
          _ ≤ _ := mul_le_mul_of_nonneg_left (kernel_single_exp_sum_le hc hw0.le N) (by positivity)
      have ht : (2 + w) * (1 + 1 / c) ^ 4 ≤ 3 * (1 + 1 / c) ^ 4 * w := by
        nlinarith [mul_le_mul_of_nonneg_right (show 2 + w ≤ 3 * w by linarith)
          (show 0 ≤ (1 + 1 / c) ^ 4 by positivity)]
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
      have hu : 0 < 2 * k / (4 * w ^ 2) := by positivity
      have hpin (m : ℕ) : kernelDiracPin ν f w (m + 1) x ≤
          (D * (4 + 3 * D) * Real.exp k) * w *
            Real.exp (-(2 * k / (4 * w ^ 2)) * ((m : ℝ) + 1)) := by
        exact (hspec ν hν f hf hf0 hfD w x hw hx (le_of_lt (lt_of_not_ge halo))
          (m + 1) (by omega)).trans (by
            simpa only [Nat.cast_add, Nat.cast_one] using kernel_dirac_spectral_polynomial hD.le hk.le hw)
      have hsum' : (∑ m ∈ Finset.range N, kernelDiracTailTerm ν f w x m) ≤
          (Ol * w ^ 6) * ((D * (4 + 3 * D) * Real.exp k) * w) *
            ((2 + w) * (1 + 1 / (2 * k / (4 * w ^ 2))) ^ 4) := by
        calc
          _ ≤ ∑ m ∈ Finset.range N, (Ol * w ^ 6) *
              (((m : ℝ) + 1 + w) * (((D * (4 + 3 * D) * Real.exp k) * w) *
                Real.exp (-(2 * k / (4 * w ^ 2)) * ((m : ℝ) + 1)))) := by
            apply Finset.sum_le_sum
            intro m hm
            exact mul_le_mul ho (mul_le_mul_of_nonneg_left (hpin m) (by positivity))
              (mul_nonneg (by positivity) (kernelDiracPin_nonneg ν hf0 w (m + 1) hx.le)) (by positivity)
          _ = (Ol * w ^ 6) * ((D * (4 + 3 * D) * Real.exp k) * w) *
              ∑ m ∈ Finset.range N, ((m : ℝ) + 1 + w) * Real.exp (-(2 * k / (4 * w ^ 2)) * ((m : ℝ) + 1)) := by
            simp only [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro m hm
            ring
          _ ≤ _ := mul_le_mul_of_nonneg_left (kernel_single_exp_sum_le hu hw0.le N) (by positivity)
      have hh := hsum'.trans (mul_le_mul_of_nonneg_left (kernel_time_sum_polynomial (by positivity : 0 < 2 * k) hw) (by positivity))
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
