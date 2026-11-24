import PLAStochastic.Index.KEP.ReferenceScale.CertificateCutoffBounds
import PLAStochastic.Index.KEP.ReferenceScale.SurvivingCore
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# True cutoff derivatives along logarithmic radial dilations

The certificate slope changes by the inverse dilation. The pair label remains
fixed. All cutoff derivatives are globally bounded, including outside the
compact slope band and for short-bridge labels.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PGM

noncomputable section

open Set MeasureTheory

theorem kepCertificateLogCutoff_hasCompactSupport : HasCompactSupport kepCertificateLogCutoff := by
  have hsupp : Function.support kepCertificateLogCutoff ⊆
      Icc (Real.log (1 / 2 : ℝ)) (Real.log 2) := by
    intro s hs
    have ha : Real.exp s ∈ Icc (1 / 2 : ℝ) 2 := by
      by_contra hn
      exact hs (kepCertificateCutoff_eq_zero hn)
    constructor
    · simpa only [Real.log_exp] using Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 2) ha.1
    · simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos s) ha.2
  exact isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (closure_minimal hsupp isClosed_Icc)

theorem kepCertificateLogCutoff_global_bounds :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ s : ℝ,
      |kepCertificateLogCutoff s| ≤ A ∧ |deriv kepCertificateLogCutoff s| ≤ A ∧
        |deriv (deriv kepCertificateLogCutoff) s| ≤ A := by
  have hs := kepCertificateLogCutoff_hasCompactSupport
  have hc := kepCertificateLogCutoff_C2
  obtain ⟨a, ha⟩ := hc.2.1.bounded_above_of_compact_support hs.deriv
  obtain ⟨b, hb⟩ := hc.2.2.1.bounded_above_of_compact_support hs.deriv.deriv
  let A := max 1 (max a b)
  refine ⟨A, le_max_left _ _, ?_⟩
  intro s
  refine ⟨(abs_kepCertificateCutoff_le (Real.exp s)).trans (le_max_left _ _), ?_, ?_⟩
  · exact (show |deriv kepCertificateLogCutoff s| ≤ a by simpa only [Real.norm_eq_abs] using ha s).trans
      ((le_max_left a b).trans (le_max_right 1 (max a b)))
  · exact (show |deriv (deriv kepCertificateLogCutoff) s| ≤ b by simpa only [Real.norm_eq_abs] using hb s).trans
      ((le_max_right a b).trans (le_max_right 1 (max a b)))

def kepRadialCoreWeight (M i j : ℕ) (ell s : ℝ) : ℝ :=
  if M ≤ j - i then kepCertificateLogCutoff (ell - s) else 0

def kepRadialCoreWeightFirst (M i j : ℕ) (ell s : ℝ) : ℝ :=
  if M ≤ j - i then -deriv kepCertificateLogCutoff (ell - s) else 0

def kepRadialCoreWeightSecond (M i j : ℕ) (ell s : ℝ) : ℝ :=
  if M ≤ j - i then deriv (deriv kepCertificateLogCutoff) (ell - s) else 0

theorem kepRadialCoreWeight_derivatives (M i j : ℕ) (ell s : ℝ) :
    HasDerivAt (kepRadialCoreWeight M i j ell) (kepRadialCoreWeightFirst M i j ell s) s ∧
      HasDerivAt (kepRadialCoreWeightFirst M i j ell) (kepRadialCoreWeightSecond M i j ell s) s := by
  have hc := kepCertificateLogCutoff_C2
  unfold kepRadialCoreWeight kepRadialCoreWeightFirst kepRadialCoreWeightSecond
  by_cases hM : M ≤ j - i
  · have hinner := (hasDerivAt_const s ell).sub (hasDerivAt_id s)
    constructor
    · simp only [hM, if_true]
      convert (hc.2.2.2.1 (ell - s)).comp s hinner using 1 <;> first | rfl | ring
    · simp only [hM, if_true]
      convert ((hc.2.2.2.2 (ell - s)).comp s hinner).neg using 1 <;> first | rfl | ring
  · simp only [hM, if_false]
    exact ⟨hasDerivAt_const s (0 : ℝ), hasDerivAt_const s (0 : ℝ)⟩

theorem kepRadialCoreWeight_eq_physical (M i j : ℕ) {a : ℝ} (ha : 0 < a) (s : ℝ) :
    kepRadialCoreWeight M i j (Real.log a) s =
      kepCertificateCoreCutoff M i j (a * Real.exp (-s)) := by
  have he : Real.exp (Real.log a - s) = a * Real.exp (-s) := by
    rw [sub_eq_add_neg, Real.exp_add, Real.exp_log ha]
  by_cases hM : M ≤ j - i <;>
    simp only [kepRadialCoreWeight, kepCertificateCoreCutoff, hM, if_true, if_false,
      kepCertificateLogCutoff, he]

theorem kepRadialCutoff_uniform_budgets :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ M i j : ℕ, ∀ ell s : ℝ,
      0 ≤ kepRadialCoreWeight M i j ell s ∧ kepRadialCoreWeight M i j ell s ≤ 1 ∧
      |1 - kepRadialCoreWeight M i j ell s| ≤ 1 ∧
      |kepRadialCoreWeightFirst M i j ell s| ≤ A ∧
      |kepRadialCoreWeightSecond M i j ell s| ≤ A := by
  obtain ⟨A, hA, hbound⟩ := kepCertificateLogCutoff_global_bounds
  refine ⟨A, hA, ?_⟩
  intro M i j ell s
  have hb := kepCertificateCutoff_bounds (Real.exp (ell - s))
  by_cases hM : M ≤ j - i
  · simp only [kepRadialCoreWeight, kepRadialCoreWeightFirst, kepRadialCoreWeightSecond,
      hM, if_true, abs_neg]
    refine ⟨hb.1, hb.2, ?_, (hbound _).2.1, (hbound _).2.2⟩
    rw [abs_of_nonneg (by change 0 ≤ 1 - kepCertificateCutoff (Real.exp (ell - s)); linarith)]
    change 1 - kepCertificateCutoff (Real.exp (ell - s)) ≤ 1
    linarith
  · simp only [kepRadialCoreWeight, kepRadialCoreWeightFirst, kepRadialCoreWeightSecond,
      hM, if_false, sub_zero, abs_one, abs_zero]
    exact ⟨le_rfl, zero_le_one, le_rfl, by linarith, by linarith⟩

end

end PGM
