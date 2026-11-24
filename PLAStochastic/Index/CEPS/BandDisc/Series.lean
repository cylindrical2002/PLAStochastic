import PLAStochastic.Index.CEPS.Band.ClassicalMain
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# True discount derivatives of absolutely convergent exponential series

Every derivative is justified by a summable time moment on a larger half-plane.
The lower boundary is open in this generic statement; class budgets below leave
an explicit positive margin before applying it at a closed-window endpoint.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

/-- The signed time-moment series, including either time zero or a one-step shift. -/
def cepsDiscJet (c : ℕ → ℂ) (s k : ℕ) (q : ℂ) : ℂ :=
  ∑' n : ℕ, (-((n + s : ℕ) : ℂ)) ^ k * Complex.exp (-q * (n + s : ℕ)) * c n

/-- The absolute reference time moments that pay termwise complex differentiation. -/
def CepsDiscMoments (c : ℕ → ℂ) (s : ℕ) (b : ℝ) : Prop :=
  ∀ j : ℕ, Summable (fun n : ℕ => (n + 1 : ℝ) ^ j *
    ‖Complex.exp (-((b : ℝ) : ℂ) * (n + s : ℕ)) * c n‖)

lemma cepsDiscJet_term_norm_le {c : ℕ → ℂ} {s : ℕ} (hs : s ≤ 1)
    {b : ℝ} {q : ℂ} (hq : b ≤ q.re) (k n : ℕ) :
    ‖(-((n + s : ℕ) : ℂ)) ^ k * Complex.exp (-q * (n + s : ℕ)) * c n‖ ≤
      (n + 1 : ℝ) ^ k * ‖Complex.exp (-(b : ℂ) * (n + s : ℕ)) * c n‖ := by
  rw [mul_assoc, norm_mul, norm_pow, norm_neg, Complex.norm_natCast,
    norm_mul, norm_mul, Complex.norm_exp, Complex.norm_exp]
  simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.natCast_re,
    Complex.natCast_im, mul_zero, sub_zero, Complex.ofReal_re]
  have hn : (n + s : ℕ) ≤ n + 1 := Nat.add_le_add_left hs n
  have hnr : ((n + s : ℕ) : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast hn
  gcongr

lemma cepsDiscJet_summable {c : ℕ → ℂ} {s : ℕ} (hs : s ≤ 1)
    {b : ℝ} (hM : CepsDiscMoments c s b) {q : ℂ} (hq : b ≤ q.re) (k : ℕ) :
    Summable (fun n : ℕ => (-((n + s : ℕ) : ℂ)) ^ k *
      Complex.exp (-q * (n + s : ℕ)) * c n) :=
  Summable.of_norm_bounded (hM k) (cepsDiscJet_term_norm_le hs hq k)

lemma cepsDiscJet_term_hasDerivAt (c : ℕ → ℂ) (s k n : ℕ) (q : ℂ) :
    HasDerivAt (fun z : ℂ => (-((n + s : ℕ) : ℂ)) ^ k *
      Complex.exp (-z * (n + s : ℕ)) * c n)
      ((-((n + s : ℕ) : ℂ)) ^ (k + 1) *
        Complex.exp (-q * (n + s : ℕ)) * c n) q := by
  have h := (((hasDerivAt_id q).neg.mul_const ((n + s : ℕ) : ℂ)).cexp.const_mul
    ((-((n + s : ℕ) : ℂ)) ^ k)).mul_const (c n)
  simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using h


/-- Actual complex differentiation, rather than a definition of a candidate jet. -/
theorem cepsDiscJet_hasDerivAt {c : ℕ → ℂ} {s : ℕ} (hs : s ≤ 1)
    {b : ℝ} (hM : CepsDiscMoments c s b) {q : ℂ} (hq : b < q.re) (k : ℕ) :
    HasDerivAt (cepsDiscJet c s k) (cepsDiscJet c s (k + 1) q) q := by
  let T : Set ℂ := {z | b < z.re}
  have hT : IsOpen T := isOpen_lt continuous_const Complex.continuous_re
  exact hasDerivAt_tsum_of_isPreconnected (hM (k + 1)) hT
    (convex_halfSpace_re_gt b).isPreconnected
    (fun n z _ => cepsDiscJet_term_hasDerivAt c s k n z)
    (fun n z hz => cepsDiscJet_term_norm_le hs hz.le (k + 1) n)
    hq (cepsDiscJet_summable hs hM hq.le k) hq

/-- The actual series is holomorphic on its open summability half-plane. -/
theorem cepsDiscJet_analyticAt {c : ℕ → ℂ} {s : ℕ} (hs : s ≤ 1)
    {b : ℝ} (hM : CepsDiscMoments c s b) {q : ℂ} (hq : b < q.re) (k : ℕ) :
    AnalyticAt ℂ (cepsDiscJet c s k) q := by
  exact DifferentiableOn.analyticAt
    (fun z hz => (cepsDiscJet_hasDerivAt hs hM hz k).differentiableAt.differentiableWithinAt)
    ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hq)

/-- All iterated derivatives agree with the absolutely convergent signed time moments. -/
theorem cepsDiscJet_iteratedDeriv {c : ℕ → ℂ} {s : ℕ} (hs : s ≤ 1)
    {b : ℝ} (hM : CepsDiscMoments c s b) (k : ℕ) {q : ℂ} (hq : b < q.re) :
    iteratedDeriv k (cepsDiscJet c s 0) q = cepsDiscJet c s k q := by
  induction k generalizing q with
  | zero => rfl
  | succ k ih =>
    rw [iteratedDeriv_succ]
    have he : iteratedDeriv k (cepsDiscJet c s 0) =ᶠ[𝓝 q] cepsDiscJet c s k := by
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hq]
        with z hz
      exact ih hz
    rw [he.deriv_eq]
    exact (cepsDiscJet_hasDerivAt hs hM hq k).deriv

/-- Every iterated derivative itself has a genuine derivative on the open half-plane. -/
theorem cepsDiscJet_hasDerivAt_iteratedDeriv {c : ℕ → ℂ} {s : ℕ} (hs : s ≤ 1)
    {b : ℝ} (hM : CepsDiscMoments c s b) (k : ℕ) {q : ℂ} (hq : b < q.re) :
    HasDerivAt (iteratedDeriv k (cepsDiscJet c s 0))
      (cepsDiscJet c s (k + 1) q) q := by
  have he : iteratedDeriv k (cepsDiscJet c s 0) =ᶠ[𝓝 q] cepsDiscJet c s k := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hq]
      with z hz
    exact cepsDiscJet_iteratedDeriv hs hM k hz
  exact (cepsDiscJet_hasDerivAt hs hM hq k).congr_of_eventuallyEq he

/-- A reference absolute moment bounds a genuine iterated derivative. -/
theorem cepsDiscJet_norm_iteratedDeriv_le {c : ℕ → ℂ} {s : ℕ} (hs : s ≤ 1)
    {b : ℝ} (hM : CepsDiscMoments c s b) (k : ℕ) {q : ℂ} (hq : b < q.re) :
    ‖iteratedDeriv k (cepsDiscJet c s 0) q‖ ≤
      ∑' n : ℕ, (n + 1 : ℝ) ^ k *
        ‖Complex.exp (-(b : ℂ) * (n + s : ℕ)) * c n‖ := by
  rw [cepsDiscJet_iteratedDeriv hs hM k hq]
  have hn := (hM k).of_nonneg_of_le (fun _ => norm_nonneg _)
    (cepsDiscJet_term_norm_le hs hq.le k)
  exact (norm_tsum_le_tsum_norm hn).trans
    (hn.tsum_le_tsum (cepsDiscJet_term_norm_le hs hq.le k) (hM k))

end
end PGM
