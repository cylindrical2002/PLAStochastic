import PLAStochastic.Index.KEP.ReferenceScale.CertificateRadial

/-!
# True physical cutoff fields under inverse dilation

The original physical cutoff is used even at nonpositive slopes. Its radial
fields are extended by zero there and remain the actual first two derivatives
along every positive ray. Their constants are fixed before tolerance, layer
or the selected certificate pair.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PGM

noncomputable section

open MeasureTheory Set

def kepCertificateCoreFirst (M i j : ℕ) (a : ℝ) : ℝ :=
  if M ≤ j - i ∧ 0 < a then -deriv kepCertificateLogCutoff (Real.log a) else 0

def kepCertificateCoreSecond (M i j : ℕ) (a : ℝ) : ℝ :=
  if M ≤ j - i ∧ 0 < a then deriv (deriv kepCertificateLogCutoff) (Real.log a) else 0

theorem kepCertificateCoreCutoff_nonpos (M i j : ℕ) {a : ℝ} (ha : a ≤ 0) :
    kepCertificateCoreCutoff M i j a = 0 := by
  have hz : kepCertificateCutoff a = 0 := kepCertificateCutoff_eq_zero (by
    intro hh
    linarith [hh.1])
  unfold kepCertificateCoreCutoff
  split <;> first | exact hz | rfl

theorem kepCertificateCore_positive_radial (M i j : ℕ) {a : ℝ} (ha : 0 < a) (s : ℝ) :
    kepCertificateCoreCutoff M i j (a / Real.exp s) = kepRadialCoreWeight M i j (Real.log a) s ∧
      kepCertificateCoreFirst M i j (a / Real.exp s) = kepRadialCoreWeightFirst M i j (Real.log a) s ∧
      kepCertificateCoreSecond M i j (a / Real.exp s) = kepRadialCoreWeightSecond M i j (Real.log a) s := by
  have hdiv : 0 < a / Real.exp s := div_pos ha (Real.exp_pos s)
  have hlog : Real.log (a / Real.exp s) = Real.log a - s := by
    rw [Real.log_div ha.ne' (Real.exp_ne_zero _), Real.log_exp]
  refine ⟨?_, ?_, ?_⟩
  · rw [kepRadialCoreWeight_eq_physical _ _ _ ha, Real.exp_neg, div_eq_mul_inv]
  · by_cases hM : M ≤ j - i <;>
      simp only [kepCertificateCoreFirst, kepRadialCoreWeightFirst, hM, hdiv, and_self,
        false_and, if_true, if_false, hlog]
  · by_cases hM : M ≤ j - i <;>
      simp only [kepCertificateCoreSecond, kepRadialCoreWeightSecond, hM, hdiv, and_self,
        false_and, if_true, if_false, hlog]

theorem kepCertificateCore_physical_derivatives (M i j : ℕ) (a s : ℝ) :
    HasDerivAt (fun t => kepCertificateCoreCutoff M i j (a / Real.exp t))
      (kepCertificateCoreFirst M i j (a / Real.exp s)) s ∧
    HasDerivAt (fun t => kepCertificateCoreFirst M i j (a / Real.exp t))
      (kepCertificateCoreSecond M i j (a / Real.exp s)) s := by
  by_cases ha : 0 < a
  · have h0 := funext fun t => (kepCertificateCore_positive_radial M i j ha t).1
    have h1 := funext fun t => (kepCertificateCore_positive_radial M i j ha t).2.1
    have h2 := (kepCertificateCore_positive_radial M i j ha s).2.2
    rw [h0, h1, (kepCertificateCore_positive_radial M i j ha s).2.1, h2]
    exact kepRadialCoreWeight_derivatives M i j (Real.log a) s
  · have hnonpos (t : ℝ) : a / Real.exp t ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (not_lt.mp ha) (Real.exp_pos t).le
    have h0 : (fun t => kepCertificateCoreCutoff M i j (a / Real.exp t)) = fun _ => (0 : ℝ) :=
      funext fun t => kepCertificateCoreCutoff_nonpos M i j (hnonpos t)
    have h1 (t : ℝ) : kepCertificateCoreFirst M i j (a / Real.exp t) = 0 := by
      simp only [kepCertificateCoreFirst, not_lt.mpr (hnonpos t), and_false, if_false]
    have h2 : kepCertificateCoreSecond M i j (a / Real.exp s) = 0 := by
      simp only [kepCertificateCoreSecond, not_lt.mpr (hnonpos s), and_false, if_false]
    rw [h0, funext h1, h1 s, h2]
    exact ⟨hasDerivAt_const s (0 : ℝ), hasDerivAt_const s (0 : ℝ)⟩

theorem measurable_kepCertificateCoreFirst (M i j : ℕ) : Measurable (kepCertificateCoreFirst M i j) := by
  have hm := (kepCertificateLogCutoff_C2.2.1.measurable.comp Real.measurable_log).neg
  unfold kepCertificateCoreFirst
  have hs : MeasurableSet {a : ℝ | M ≤ j - i ∧ 0 < a} := by
    by_cases hM : M ≤ j - i
    · simp only [hM, true_and]
      change MeasurableSet (Ioi (0 : ℝ))
      exact measurableSet_Ioi
    · simp only [hM, false_and, ofPred_false]
      exact MeasurableSet.empty
  exact Measurable.ite hs hm measurable_const

theorem measurable_kepCertificateCoreSecond (M i j : ℕ) : Measurable (kepCertificateCoreSecond M i j) := by
  have hm := kepCertificateLogCutoff_C2.2.2.1.measurable.comp Real.measurable_log
  unfold kepCertificateCoreSecond
  have hs : MeasurableSet {a : ℝ | M ≤ j - i ∧ 0 < a} := by
    by_cases hM : M ≤ j - i
    · simp only [hM, true_and]
      change MeasurableSet (Ioi (0 : ℝ))
      exact measurableSet_Ioi
    · simp only [hM, false_and, ofPred_false]
      exact MeasurableSet.empty
  exact Measurable.ite hs hm measurable_const

theorem kepCertificateCore_physical_bounds :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ M i j : ℕ, ∀ a : ℝ,
      |kepCertificateCoreCutoff M i j a| ≤ B ∧
        |kepCertificateCoreFirst M i j a| ≤ B ∧ |kepCertificateCoreSecond M i j a| ≤ B := by
  obtain ⟨B, hB, hb⟩ := kepCertificateLogCutoff_global_bounds
  refine ⟨B, hB, ?_⟩
  intro M i j a
  have hcore := kepCertificateCoreCutoff_bounds M i j a
  refine ⟨(by rw [abs_of_nonneg hcore.1]; exact hcore.2.trans hB), ?_, ?_⟩
  · unfold kepCertificateCoreFirst
    split
    · simpa only [abs_neg] using (hb (Real.log a)).2.1
    · simpa only [abs_zero] using (zero_le_one.trans hB)
  · unfold kepCertificateCoreSecond
    split
    · exact (hb (Real.log a)).2.2
    · simpa only [abs_zero] using (zero_le_one.trans hB)

end

end PGM
