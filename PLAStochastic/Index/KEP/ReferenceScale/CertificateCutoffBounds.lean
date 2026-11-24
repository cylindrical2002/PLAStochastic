import PLAStochastic.Index.KEP.ReferenceScale.CertificateCutoff

/-!
# Fixed cutoff derivative constants and compact physical slope bounds

The constants depend only on the explicit cutoff, before epsilon or any layer
is selected. They are bounds for its genuine classical derivatives.
-/

set_option autoImplicit false

namespace PGM

noncomputable section

open Set

theorem kepCertificateLogCutoff_uniform_bounds :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ s ∈ Ioc (Real.log (1 / 2 : ℝ)) (Real.log 2),
      |kepCertificateLogCutoff s| ≤ A ∧ |deriv kepCertificateLogCutoff s| ≤ A ∧
        |deriv (deriv kepCertificateLogCutoff) s| ≤ A := by
  have hc := kepCertificateLogCutoff_C2
  obtain ⟨a, ha⟩ := isCompact_Icc.bddAbove_image hc.2.1.abs.continuousOn
    (K := Icc (Real.log (1 / 2 : ℝ)) (Real.log 2))
  obtain ⟨b, hb⟩ := isCompact_Icc.bddAbove_image hc.2.2.1.abs.continuousOn
    (K := Icc (Real.log (1 / 2 : ℝ)) (Real.log 2))
  let A := max 1 (max a b)
  refine ⟨A, le_max_left _ _, ?_⟩
  intro s hs
  have hsc : s ∈ Icc (Real.log (1 / 2 : ℝ)) (Real.log 2) := ⟨hs.1.le, hs.2⟩
  refine ⟨(abs_kepCertificateCutoff_le (Real.exp s)).trans (le_max_left _ _),
    (ha (mem_image_of_mem _ hsc)).trans ?_, (hb (mem_image_of_mem _ hsc)).trans ?_⟩
  · exact (le_max_left a b).trans (le_max_right 1 (max a b))
  · exact (le_max_right a b).trans (le_max_right 1 (max a b))

theorem kep_logSlope_exp_bounds {s : ℝ}
    (hs : s ∈ Ioc (Real.log (1 / 2 : ℝ)) (Real.log 2)) :
    (1 / 2 : ℝ) ≤ Real.exp s ∧ Real.exp s ≤ 2 ∧
      Real.exp (2 * s) ≤ 4 ∧ Real.exp (-s) ≤ 2 := by
  have hlo : (1 / 2 : ℝ) ≤ Real.exp s := by
    have hh := Real.exp_le_exp.mpr hs.1.le
    rwa [Real.exp_log (by norm_num : (0 : ℝ) < 1 / 2)] at hh
  have hhi : Real.exp s ≤ 2 := by
    have hh := Real.exp_le_exp.mpr hs.2
    rwa [Real.exp_log (by norm_num : (0 : ℝ) < 2)] at hh
  refine ⟨hlo, hhi, ?_, ?_⟩
  · rw [two_mul, Real.exp_add]
    nlinarith [Real.exp_pos s]
  · have he : -Real.log (1 / 2 : ℝ) = Real.log 2 := by rw [one_div, Real.log_inv, neg_neg]
    have hh := Real.exp_le_exp.mpr (neg_le_neg hs.1.le)
    rwa [he, Real.exp_log (by norm_num : (0 : ℝ) < 2)] at hh

end

end PGM
