import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support
import PLAStochastic.Index.KEP.ReferenceScale.CertificateScalar

/-!
# A fixed smooth cutoff for the actual certificate slope

The cutoff is one on `[3/4,3/2]`, lies between zero and one, and has support
strictly inside `[1/2,2]`. Its logarithmic version and its first derivative
therefore vanish at both integration endpoints. It is independent of epsilon
and of the reference layer.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ContDiff

def kepCertificateCutoffBump : ContDiffBump (5 / 4 : ℝ) :=
  ⟨1 / 2, 2 / 3, by norm_num, by norm_num⟩

def kepCertificateCutoff (a : ℝ) : ℝ := kepCertificateCutoffBump a

def kepCertificateLogCutoff (s : ℝ) : ℝ := kepCertificateCutoff (Real.exp s)

theorem contDiff_kepCertificateCutoff : ContDiff ℝ ∞ kepCertificateCutoff :=
  kepCertificateCutoffBump.contDiff

theorem contDiff_kepCertificateLogCutoff : ContDiff ℝ ∞ kepCertificateLogCutoff :=
  contDiff_kepCertificateCutoff.comp Real.contDiff_exp

theorem kepCertificateCutoff_bounds (a : ℝ) :
    0 ≤ kepCertificateCutoff a ∧ kepCertificateCutoff a ≤ 1 :=
  ⟨kepCertificateCutoffBump.nonneg, kepCertificateCutoffBump.le_one⟩

theorem abs_kepCertificateCutoff_le (a : ℝ) : |kepCertificateCutoff a| ≤ 1 := by
  rw [abs_of_nonneg (kepCertificateCutoff_bounds a).1]
  exact (kepCertificateCutoff_bounds a).2

theorem kepCertificateCutoff_eq_one {a : ℝ} (ha : a ∈ Icc (3 / 4 : ℝ) (3 / 2)) :
    kepCertificateCutoff a = 1 := by
  apply kepCertificateCutoffBump.one_of_mem_closedBall
  rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
  change -(1 / 2 : ℝ) ≤ a - 5 / 4 ∧ a - 5 / 4 ≤ 1 / 2
  constructor <;> linarith [ha.1, ha.2]

theorem kepCertificateCutoff_eq_zero {a : ℝ} (ha : a ∉ Icc (1 / 2 : ℝ) 2) :
    kepCertificateCutoff a = 0 := by
  apply kepCertificateCutoffBump.zero_of_le_dist
  rw [Real.dist_eq]
  change (2 / 3 : ℝ) ≤ |a - 5 / 4|
  have hcases : a < (1 / 2 : ℝ) ∨ 2 < a := by
    simpa only [mem_Icc, not_and_or, not_le] using ha
  rcases hcases with ha | ha
  · rw [abs_of_neg (by linarith : a - 5 / 4 < 0)]
    linarith
  · rw [abs_of_pos (by linarith : 0 < a - 5 / 4)]
    linarith

theorem kepCertificateCutoff_endpoints :
    kepCertificateCutoff (1 / 2) = 0 ∧ kepCertificateCutoff 2 = 0 ∧
      deriv kepCertificateCutoff (1 / 2) = 0 ∧ deriv kepCertificateCutoff 2 = 0 := by
  have hlo : (1 / 2 : ℝ) ∉ tsupport kepCertificateCutoff := by
    change (1 / 2 : ℝ) ∉ tsupport (kepCertificateCutoffBump : ℝ → ℝ)
    rw [kepCertificateCutoffBump.tsupport_eq, Metric.mem_closedBall, Real.dist_eq]
    norm_num [kepCertificateCutoffBump]
  have hhi : (2 : ℝ) ∉ tsupport kepCertificateCutoff := by
    change (2 : ℝ) ∉ tsupport (kepCertificateCutoffBump : ℝ → ℝ)
    rw [kepCertificateCutoffBump.tsupport_eq, Metric.mem_closedBall, Real.dist_eq]
    norm_num [kepCertificateCutoffBump]
  exact ⟨image_eq_zero_of_notMem_tsupport hlo, image_eq_zero_of_notMem_tsupport hhi,
    deriv_of_notMem_tsupport hlo, deriv_of_notMem_tsupport hhi⟩

theorem kepCertificateLogCutoff_C2 :
    Continuous kepCertificateLogCutoff ∧ Continuous (deriv kepCertificateLogCutoff) ∧
      Continuous (deriv (deriv kepCertificateLogCutoff)) ∧
      (∀ s, HasDerivAt kepCertificateLogCutoff (deriv kepCertificateLogCutoff s) s) ∧
      (∀ s, HasDerivAt (deriv kepCertificateLogCutoff)
        (deriv (deriv kepCertificateLogCutoff) s) s) := by
  have hc := contDiff_kepCertificateLogCutoff
  have hc' := (contDiff_infty_iff_deriv.mp hc).2
  exact ⟨hc.continuous, hc'.continuous, (contDiff_infty_iff_deriv.mp hc').2.continuous,
    fun s => ((contDiff_infty_iff_deriv.mp hc).1 s).hasDerivAt,
    fun s => ((contDiff_infty_iff_deriv.mp hc').1 s).hasDerivAt⟩

theorem kepCertificateLogCutoff_endpoints :
    kepCertificateLogCutoff (Real.log (1 / 2)) = 0 ∧
      kepCertificateLogCutoff (Real.log 2) = 0 ∧
      deriv kepCertificateLogCutoff (Real.log (1 / 2)) = 0 ∧
      deriv kepCertificateLogCutoff (Real.log 2) = 0 := by
  have he (a : ℝ) (ha : 0 < a) :
      deriv kepCertificateLogCutoff (Real.log a) = a * deriv kepCertificateCutoff a := by
    have hh := (((contDiff_infty_iff_deriv.mp contDiff_kepCertificateCutoff).1
      (Real.exp (Real.log a))).hasDerivAt).comp
      (Real.log a) (Real.hasDerivAt_exp (Real.log a))
    rw [Real.exp_log ha] at hh
    exact hh.deriv.trans (mul_comm _ _)
  rcases kepCertificateCutoff_endpoints with ⟨hl, hh, hl', hh'⟩
  simp only [kepCertificateLogCutoff, Real.exp_log (by norm_num : (0 : ℝ) < 1 / 2),
    Real.exp_log (by norm_num : (0 : ℝ) < 2), hl, hh, he _ (by norm_num : (0 : ℝ) < 1 / 2),
    he _ (by norm_num : (0 : ℝ) < 2), hl', hh', mul_zero, and_self]

end

end PGM
