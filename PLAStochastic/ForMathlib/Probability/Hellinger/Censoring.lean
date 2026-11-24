import PLAStochastic.ForMathlib.Probability.Hellinger.Restriction

/-!
# Censoring and uncensoring a Hellinger comparison

On a measurable retained set the full output is recorded. Its complement is
collapsed to one common symbol. The formula for the resulting squared distance
contains the retained integral and the square-root mass difference of that atom.
The full output can be recovered with an error depending only on the reference
probability of leaving the retained set.
-/

set_option autoImplicit false

namespace ProbabilityTheory.HellingerDensity

noncomputable section

open MeasureTheory Set

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- Square Hellinger distance after the complement of `s` is collapsed to one atom. -/
def censoredSq (p q : HellingerDensity μ) (s : Set α) : ℝ :=
  (∫ x in s, (Real.sqrt (p.density x) - Real.sqrt (q.density x)) ^ 2 ∂μ) +
    (Real.sqrt (p.mass sᶜ) - Real.sqrt (q.mass sᶜ)) ^ 2

theorem censoredSq_nonneg (p q : HellingerDensity μ) (s : Set α) :
    0 ≤ p.censoredSq q s := by
  exact add_nonneg (integral_nonneg fun _ => sq_nonneg _) (sq_nonneg _)

theorem censoredSq_le_hellinger_sq (p q : HellingerDensity μ)
    {s : Set α} (hs : MeasurableSet s) : p.censoredSq q s ≤ p.hellinger q ^ 2 := by
  have hnorm := abs_norm_sub_norm_le (p.rootOn sᶜ hs.compl) (q.rootOn sᶜ hs.compl)
  have hsq :
      (Real.sqrt (p.mass sᶜ) - Real.sqrt (q.mass sᶜ)) ^ 2 ≤
        ∫ x in sᶜ, (Real.sqrt (p.density x) - Real.sqrt (q.density x)) ^ 2 ∂μ := by
    have he : ‖p.rootOn sᶜ hs.compl - q.rootOn sᶜ hs.compl‖ ^ 2 =
        ∫ x in sᶜ, (Real.sqrt (p.density x) - Real.sqrt (q.density x)) ^ 2 ∂μ := by
      rw [← real_inner_self_eq_norm_sq, L2.inner_def, ← integral_indicator hs.compl]
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub (p.rootOn sᶜ hs.compl) (q.rootOn sᶜ hs.compl),
        p.rootOn_ae sᶜ hs.compl, q.rootOn_ae sᶜ hs.compl] with x hsub hp hq
      simp only [hsub, Pi.sub_apply, hp, hq]
      by_cases hx : x ∈ sᶜ
      · simp [indicator_of_mem hx, pow_two]
      · simp [indicator_of_notMem hx]
    rw [norm_rootOn, norm_rootOn] at hnorm
    rw [← he]
    have hnorm0 := norm_nonneg (p.rootOn sᶜ hs.compl - q.rootOn sᶜ hs.compl)
    have ha := abs_nonneg (Real.sqrt (p.mass sᶜ) - Real.sqrt (q.mass sᶜ))
    nlinarith only [hnorm, hnorm0, ha, sq_abs
      (Real.sqrt (p.mass sᶜ) - Real.sqrt (q.mass sᶜ))]
  have hpart := integral_add_compl hs (p.sqrt_memLp.sub q.sqrt_memLp).integrable_sq
  simp only [Pi.sub_apply] at hpart
  rw [hellinger_sq, censoredSq, ← hpart]
  exact add_le_add le_rfl hsq

theorem sqrt_mass_le_censored (p q : HellingerDensity μ) (s : Set α) :
    Real.sqrt (p.mass sᶜ) ≤ Real.sqrt (q.mass sᶜ) + Real.sqrt (p.censoredSq q s) := by
  have hi : 0 ≤ ∫ x in s,
      (Real.sqrt (p.density x) - Real.sqrt (q.density x)) ^ 2 ∂μ :=
    integral_nonneg fun _ => sq_nonneg _
  have hc := Real.sq_sqrt (p.censoredSq_nonneg q s)
  have hc0 := Real.sqrt_nonneg (p.censoredSq q s)
  have hs : (Real.sqrt (p.mass sᶜ) - Real.sqrt (q.mass sᶜ)) ^ 2 ≤
      p.censoredSq q s := by
    unfold censoredSq
    linarith only [hi]
  nlinarith only [hs, hc, hc0]

/-- If the censored distance is at most `h` and the reference exit mass is `τ`,
then the full Hellinger distance is at most `h + sqrt (2 τ)`. -/
theorem hellinger_le_censored_add_exit (p q : HellingerDensity μ)
    {s : Set α} (hs : MeasurableSet s) :
    p.hellinger q ≤ Real.sqrt (p.censoredSq q s) + Real.sqrt (2 * q.mass sᶜ) := by
  have hnonp := p.mass_nonneg sᶜ
  have hnonq := q.mass_nonneg sᶜ
  have hp := Real.sq_sqrt hnonp
  have hq := Real.sq_sqrt hnonq
  have h0 := p.hellinger_nonneg q
  have hcen := Real.sq_sqrt (p.censoredSq_nonneg q s)
  have hcen0 := Real.sqrt_nonneg (p.censoredSq q s)
  have hex := Real.sq_sqrt (show 0 ≤ 2 * q.mass sᶜ by positivity)
  have hex0 := Real.sqrt_nonneg (2 * q.mass sᶜ)
  have hroot := sqrt_mass_le_censored p q s
  have hqle : Real.sqrt (q.mass sᶜ) ≤ Real.sqrt (2 * q.mass sᶜ) := by
    apply Real.sqrt_le_sqrt
    linarith only [hnonq]
  have hout :
      (∫ x in sᶜ, (Real.sqrt (p.density x) - Real.sqrt (q.density x)) ^ 2 ∂μ) ≤
        p.mass sᶜ + q.mass sᶜ := by
    calc
      _ ≤ ∫ x in sᶜ, p.density x + q.density x ∂μ := by
        apply integral_mono
          ((p.sqrt_memLp.sub q.sqrt_memLp).integrable_sq.integrableOn)
          ((p.integrable.add q.integrable).integrableOn)
        intro x
        change (Real.sqrt (p.density x) - Real.sqrt (q.density x)) ^ 2 ≤
          p.density x + q.density x
        nlinarith only [Real.sq_sqrt (p.nonneg x), Real.sq_sqrt (q.nonneg x),
          mul_nonneg (Real.sqrt_nonneg (p.density x)) (Real.sqrt_nonneg (q.density x))]
      _ = _ := integral_add p.integrable.integrableOn q.integrable.integrableOn
  have hfull : p.hellinger q ^ 2 ≤ p.censoredSq q s +
      2 * Real.sqrt (p.mass sᶜ) * Real.sqrt (q.mass sᶜ) := by
    have hpart := integral_add_compl hs (p.sqrt_memLp.sub q.sqrt_memLp).integrable_sq
    simp only [Pi.sub_apply] at hpart
    rw [hellinger_sq, censoredSq, ← hpart]
    nlinarith only [hout, hp, hq]
  have hmul := mul_le_mul_of_nonneg_right hroot (Real.sqrt_nonneg (q.mass sᶜ))
  have hmul' := mul_le_mul_of_nonneg_left hqle hcen0
  nlinarith only [hfull, hmul, hmul', hp, hq, hcen, hex, h0, hcen0, hex0]

end

end ProbabilityTheory.HellingerDensity
