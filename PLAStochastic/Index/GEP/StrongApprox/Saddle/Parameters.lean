import PLAStochastic.Index.GEP.StrongApprox.Tilt.Cumulants
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Topology.Order.IntermediateValue

/-!
# WP5: saddle parameters for Gaussian-smoothed centered gaps

The interval of target means is slightly smaller than the image of the common
tilt interval.  This gives an interior saddle even at the endpoints of the
target interval, without any law-dependent enlargement of the constants.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology

/-- The fixed interval of means used in saddle estimates. -/
def saMeanRadius (vlo B θ : ℝ) : ℝ := vlo / 2 * saTiltRadius vlo B θ

theorem saMeanRadius_pos {vlo B θ : ℝ} (hvlo : 0 < vlo) (hθ : 0 < θ) :
    0 < saMeanRadius vlo B θ :=
  mul_pos (half_pos hvlo) (saTiltRadius_pos hvlo hθ)

/-- Inverse of the tilted mean on the fixed admissible tilt interval. -/
def saSaddle (vlo B θ : ℝ) (ν : ProbabilityMeasure ℝ) (s : ℝ) : ℝ → ℝ :=
  Function.invFunOn (deriv (saSmoothCGF ν s))
    (Icc (-saTiltRadius vlo B θ) (saTiltRadius vlo B θ))

variable {vlo vhi κ₃ B θ : ℝ} {ν : ProbabilityMeasure ℝ}

theorem UnivClass.saSmoothCGF_mean_growth (h : UnivClass vlo vhi κ₃ B θ ν)
    (hvlo : 0 < vlo) (hθ : 0 < θ) (s : ℝ) {a b : ℝ}
    (ha : |a| ≤ saTiltRadius vlo B θ) (hb : |b| ≤ saTiltRadius vlo B θ) (hab : a ≤ b) :
    (3 / 4 * vlo) * (b - a) ≤ deriv (saSmoothCGF ν s) b - deriv (saSmoothCGF ν s) a := by
  let r := saTiltRadius vlo B θ
  have hd : ∀ t ∈ Icc (-r) r, DifferentiableAt ℝ (deriv (saSmoothCGF ν s)) t := by
    intro t ht
    have htθ : |t| < θ := lt_of_le_of_lt
      ((abs_le.mpr ht).trans (saTiltRadius_le_half vlo B hθ)) (by linarith)
    exact (h.hasDerivAt_deriv_saSmoothCGF htθ s).differentiableAt
  have hlow : ∀ t ∈ interior (Icc (-r) r),
      3 / 4 * vlo ≤ deriv (deriv (saSmoothCGF ν s)) t := by
    intro t ht
    have htr : |t| ≤ r := abs_le.mpr (interior_subset (s := Icc (-r) r) ht)
    have hh := (h.saSmoothCGF_variance_bracket hvlo hθ htr s).1
    have hh' : 3 / 4 * vlo ≤ iteratedDeriv 2 (saSmoothCGF ν s) t := by
      nlinarith [h.var_ge, sq_nonneg s]
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using hh'
  exact (convex_Icc (-r) r).mul_sub_le_image_sub_of_le_deriv
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hd t (interior_subset (s := Icc (-r) r) ht)).differentiableWithinAt)
    hlow a (abs_le.mp ha) b (abs_le.mp hb) hab

theorem UnivClass.saSmoothCGF_mean_strictMono (h : UnivClass vlo vhi κ₃ B θ ν)
    (hvlo : 0 < vlo) (hθ : 0 < θ) (s : ℝ) :
    StrictMonoOn (deriv (saSmoothCGF ν s))
      (Icc (-saTiltRadius vlo B θ) (saTiltRadius vlo B θ)) := by
  intro a ha b hb hab
  have hg := h.saSmoothCGF_mean_growth hvlo hθ s (abs_le.mpr ha) (abs_le.mpr hb) hab.le
  have hh : 0 < (3 / 4 * vlo) * (b - a) := by positivity
  linarith

theorem UnivClass.saSmoothCGF_mean_separation (h : UnivClass vlo vhi κ₃ B θ ν)
    (hvlo : 0 < vlo) (hθ : 0 < θ) (s : ℝ) {a b : ℝ}
    (ha : |a| ≤ saTiltRadius vlo B θ) (hb : |b| ≤ saTiltRadius vlo B θ) :
    (3 / 4 * vlo) * |b - a| ≤ |deriv (saSmoothCGF ν s) b - deriv (saSmoothCGF ν s) a| := by
  rcases le_total a b with hab | hab
  · have hh := h.saSmoothCGF_mean_growth hvlo hθ s ha hb hab
    rw [abs_of_nonneg (sub_nonneg.mpr hab)]
    exact hh.trans (le_abs_self _)
  · have hh := h.saSmoothCGF_mean_growth hvlo hθ s hb ha hab
    rw [abs_sub_comm b a, abs_of_nonneg (sub_nonneg.mpr hab), abs_sub_comm]
    exact hh.trans (le_abs_self _)

/-- All means up to three quarters of `vlo * radius` are attained uniquely. -/
theorem UnivClass.existsUnique_saSaddle (h : UnivClass vlo vhi κ₃ B θ ν)
    (hvlo : 0 < vlo) (hθ : 0 < θ) (s : ℝ) {w : ℝ}
    (hw : |w| ≤ 3 / 4 * vlo * saTiltRadius vlo B θ) :
    ∃! lam : ℝ, lam ∈ Icc (-saTiltRadius vlo B θ) (saTiltRadius vlo B θ) ∧
      deriv (saSmoothCGF ν s) lam = w := by
  let r := saTiltRadius vlo B θ
  have hr : 0 < r := saTiltRadius_pos hvlo hθ
  have hr0 : |(0 : ℝ)| ≤ r := by simpa using hr.le
  have hrp : |r| ≤ r := by rw [abs_of_pos hr]
  have hrn : |-r| ≤ r := by rwa [abs_neg]
  have hp := h.saSmoothCGF_mean_growth hvlo hθ s hr0 hrp hr.le
  have hn := h.saSmoothCGF_mean_growth hvlo hθ s hrn hr0 (by linarith)
  rw [h.deriv_saSmoothCGF_zero hθ s] at hp hn
  have hw' : w ∈ Icc (deriv (saSmoothCGF ν s) (-r)) (deriv (saSmoothCGF ν s) r) := by
    obtain ⟨hw1, hw2⟩ := abs_le.mp hw
    constructor <;> dsimp [r] at * <;> linarith
  have hc : ContinuousOn (deriv (saSmoothCGF ν s)) (Icc (-r) r) := by
    intro t ht
    have htθ : |t| < θ := lt_of_le_of_lt
      ((abs_le.mpr ht).trans (saTiltRadius_le_half vlo B hθ)) (by linarith)
    exact (h.hasDerivAt_deriv_saSmoothCGF htθ s).continuousAt.continuousWithinAt
  obtain ⟨lam, hlam, heq⟩ := intermediate_value_Icc (by linarith : -r ≤ r) hc hw'
  refine ⟨lam, ⟨hlam, heq⟩, ?_⟩
  intro t ht
  exact (h.saSmoothCGF_mean_strictMono hvlo hθ s).injOn ht.1 hlam (ht.2.trans heq.symm)

theorem UnivClass.saSaddle_spec (h : UnivClass vlo vhi κ₃ B θ ν)
    (hvlo : 0 < vlo) (hθ : 0 < θ) (s : ℝ) {w : ℝ}
    (hw : |w| ≤ 3 / 4 * vlo * saTiltRadius vlo B θ) :
    saSaddle vlo B θ ν s w ∈ Icc (-saTiltRadius vlo B θ) (saTiltRadius vlo B θ) ∧
      deriv (saSmoothCGF ν s) (saSaddle vlo B θ ν s w) = w := by
  obtain ⟨lam, hlam, -⟩ := h.existsUnique_saSaddle hvlo hθ s hw
  exact Function.invFunOn_pos ⟨lam, hlam.1, hlam.2⟩

theorem UnivClass.saSaddle_leftInvOn (h : UnivClass vlo vhi κ₃ B θ ν)
    (hvlo : 0 < vlo) (hθ : 0 < θ) (s : ℝ) :
    LeftInvOn (saSaddle vlo B θ ν s) (deriv (saSmoothCGF ν s))
      (Icc (-saTiltRadius vlo B θ) (saTiltRadius vlo B θ)) :=
  (h.saSmoothCGF_mean_strictMono hvlo hθ s).injOn.leftInvOn_invFunOn

theorem UnivClass.saSaddle_zero (h : UnivClass vlo vhi κ₃ B θ ν)
    (hvlo : 0 < vlo) (hθ : 0 < θ) (s : ℝ) : saSaddle vlo B θ ν s 0 = 0 := by
  have hh := h.saSaddle_leftInvOn hvlo hθ s
    (show (0 : ℝ) ∈ Icc (-saTiltRadius vlo B θ) (saTiltRadius vlo B θ) from
      ⟨by linarith [saTiltRadius_pos (B := B) hvlo hθ], (saTiltRadius_pos hvlo hθ).le⟩)
  rwa [h.deriv_saSmoothCGF_zero hθ s] at hh

theorem UnivClass.saSaddle_lipschitz (h : UnivClass vlo vhi κ₃ B θ ν)
    (hvlo : 0 < vlo) (hθ : 0 < θ) (s : ℝ) {a b : ℝ}
    (ha : |a| ≤ 3 / 4 * vlo * saTiltRadius vlo B θ)
    (hb : |b| ≤ 3 / 4 * vlo * saTiltRadius vlo B θ) :
    |saSaddle vlo B θ ν s b - saSaddle vlo B θ ν s a| ≤ 4 / (3 * vlo) * |b - a| := by
  obtain ⟨hA, hAe⟩ := h.saSaddle_spec hvlo hθ s ha
  obtain ⟨hB, hBe⟩ := h.saSaddle_spec hvlo hθ s hb
  have hh := h.saSmoothCGF_mean_separation hvlo hθ s (abs_le.mpr hA) (abs_le.mpr hB)
  rw [hAe, hBe] at hh
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  linarith

theorem UnivClass.abs_saSaddle_le (h : UnivClass vlo vhi κ₃ B θ ν)
    (hvlo : 0 < vlo) (hθ : 0 < θ) (s : ℝ) {w : ℝ}
    (hw : |w| ≤ 3 / 4 * vlo * saTiltRadius vlo B θ) :
    |saSaddle vlo B θ ν s w| ≤ 4 / (3 * vlo) * |w| := by
  have hr := saTiltRadius_pos (B := B) hvlo hθ
  have hh := h.saSaddle_lipschitz hvlo hθ s
    (a := 0) (b := w) (by simpa using (by positivity : (0 : ℝ) ≤
      3 / 4 * vlo * saTiltRadius vlo B θ)) hw
  rwa [h.saSaddle_zero hvlo hθ s, sub_zero, sub_zero] at hh

theorem UnivClass.continuousAt_saSaddle (h : UnivClass vlo vhi κ₃ B θ ν)
    (hvlo : 0 < vlo) (hθ : 0 < θ) (s : ℝ) {w : ℝ}
    (hw : |w| < 3 / 4 * vlo * saTiltRadius vlo B θ) :
    ContinuousAt (saSaddle vlo B θ ν s) w := by
  let R := 3 / 4 * vlo * saTiltRadius vlo B θ
  have hL : LipschitzOnWith (Real.toNNReal (4 / (3 * vlo))) (saSaddle vlo B θ ν s)
      (Icc (-R) R) := by
    apply LipschitzOnWith.of_dist_le'
    intro a ha b hb
    simpa only [Real.dist_eq] using
      h.saSaddle_lipschitz hvlo hθ s (abs_le.mpr hb) (abs_le.mpr ha)
  exact hL.continuousOn.continuousAt (Icc_mem_nhds (abs_lt.mp hw).1 (abs_lt.mp hw).2)

/-- Inverse-mean derivative on an open interval containing the requested mean window. -/
theorem UnivClass.hasDerivAt_saSaddle (h : UnivClass vlo vhi κ₃ B θ ν)
    (hvlo : 0 < vlo) (hθ : 0 < θ) (s : ℝ) {w : ℝ}
    (hw : |w| < 3 / 4 * vlo * saTiltRadius vlo B θ) :
    HasDerivAt (saSaddle vlo B θ ν s)
      (iteratedDeriv 2 (saSmoothCGF ν s) (saSaddle vlo B θ ν s w))⁻¹ w := by
  obtain ⟨hmem, -⟩ := h.saSaddle_spec hvlo hθ s hw.le
  have hlt : |saSaddle vlo B θ ν s w| < θ :=
    lt_of_le_of_lt ((abs_le.mpr hmem).trans (saTiltRadius_le_half vlo B hθ)) (by linarith)
  have hd : HasDerivAt (deriv (saSmoothCGF ν s))
      (iteratedDeriv 2 (saSmoothCGF ν s) (saSaddle vlo B θ ν s w))
      (saSaddle vlo B θ ν s w) := by
    rw [h.iteratedDeriv_two_saSmoothCGF hlt s]
    exact h.hasDerivAt_deriv_saSmoothCGF hlt s
  have hv : 0 < iteratedDeriv 2 (saSmoothCGF ν s) (saSaddle vlo B θ ν s w) := by
    have := (h.saSmoothCGF_variance_bracket hvlo hθ (abs_le.mpr hmem) s).1
    have := h.var_ge
    nlinarith [sq_nonneg s]
  refine hd.of_local_left_inverse (h.continuousAt_saSaddle hvlo hθ s hw) hv.ne' ?_
  filter_upwards [(isOpen_lt continuous_abs continuous_const).eventually_mem hw] with y hy
  exact (h.saSaddle_spec hvlo hθ s hy.le).2

/-- The local Legendre transform, evaluated at the canonical saddle. -/
def saRate (vlo B θ : ℝ) (ν : ProbabilityMeasure ℝ) (s w : ℝ) : ℝ :=
  saSaddle vlo B θ ν s w * w - saSmoothCGF ν s (saSaddle vlo B θ ν s w)

theorem UnivClass.saRate_zero (h : UnivClass vlo vhi κ₃ B θ ν)
    (hvlo : 0 < vlo) (hθ : 0 < θ) (s : ℝ) : saRate vlo B θ ν s 0 = 0 := by
  simp [saRate, h.saSaddle_zero hvlo hθ s]

/-- The first rate derivative is the saddle parameter itself. -/
theorem UnivClass.hasDerivAt_saRate (h : UnivClass vlo vhi κ₃ B θ ν)
    (hvlo : 0 < vlo) (hθ : 0 < θ) (s : ℝ) {w : ℝ}
    (hw : |w| < 3 / 4 * vlo * saTiltRadius vlo B θ) :
    HasDerivAt (saRate vlo B θ ν s) (saSaddle vlo B θ ν s w) w := by
  have hi := h.hasDerivAt_saSaddle hvlo hθ s hw
  obtain ⟨hmem, heq⟩ := h.saSaddle_spec hvlo hθ s hw.le
  have hlt : |saSaddle vlo B θ ν s w| < θ :=
    lt_of_le_of_lt ((abs_le.mpr hmem).trans (saTiltRadius_le_half vlo B hθ)) (by linarith)
  have hd := (h.analyticAt_saSmoothCGF hlt s).differentiableAt.hasDerivAt
  rw [heq] at hd
  have hh := (hi.mul (hasDerivAt_id w)).sub (hd.comp w hi)
  simp only [id_eq] at hh
  convert hh using 1 <;> first | rfl | ring

theorem UnivClass.deriv_saRate (h : UnivClass vlo vhi κ₃ B θ ν)
    (hvlo : 0 < vlo) (hθ : 0 < θ) (s : ℝ) {w : ℝ}
    (hw : |w| < 3 / 4 * vlo * saTiltRadius vlo B θ) :
    deriv (saRate vlo B θ ν s) w = saSaddle vlo B θ ν s w :=
  (h.hasDerivAt_saRate hvlo hθ s hw).deriv

/-- The second rate derivative is the inverse tilted variance. -/
theorem UnivClass.iteratedDeriv_two_saRate (h : UnivClass vlo vhi κ₃ B θ ν)
    (hvlo : 0 < vlo) (hθ : 0 < θ) (s : ℝ) {w : ℝ}
    (hw : |w| < 3 / 4 * vlo * saTiltRadius vlo B θ) :
    iteratedDeriv 2 (saRate vlo B θ ν s) w =
      (iteratedDeriv 2 (saSmoothCGF ν s) (saSaddle vlo B θ ν s w))⁻¹ := by
  have heq : deriv (saRate vlo B θ ν s) =ᶠ[𝓝 w] saSaddle vlo B θ ν s := by
    filter_upwards [(isOpen_lt continuous_abs continuous_const).eventually_mem hw] with y hy
    exact h.deriv_saRate hvlo hθ s hy
  rw [show (2 : ℕ) = 1 + 1 by rfl, iteratedDeriv_succ, iteratedDeriv_one, heq.deriv_eq]
  exact (h.hasDerivAt_saSaddle hvlo hθ s hw).deriv

/-- The derivative of the inverse variance, with its exact cubic denominator. -/
theorem UnivClass.hasDerivAt_iteratedDeriv_two_saRate (h : UnivClass vlo vhi κ₃ B θ ν)
    (hvlo : 0 < vlo) (hθ : 0 < θ) (s : ℝ) {w : ℝ}
    (hw : |w| < 3 / 4 * vlo * saTiltRadius vlo B θ) :
    HasDerivAt (iteratedDeriv 2 (saRate vlo B θ ν s))
      (-iteratedDeriv 3 (saSmoothCGF ν s) (saSaddle vlo B θ ν s w) /
        (iteratedDeriv 2 (saSmoothCGF ν s) (saSaddle vlo B θ ν s w)) ^ 3) w := by
  let lam := saSaddle vlo B θ ν s w
  obtain ⟨hmem, -⟩ := h.saSaddle_spec hvlo hθ s hw.le
  have hlt : |lam| < θ := lt_of_le_of_lt
    ((abs_le.mpr hmem).trans (saTiltRadius_le_half vlo B hθ)) (by linarith)
  have han : AnalyticOnNhd ℝ (saSmoothCGF ν s) {t : ℝ | |t| < θ} :=
    fun t ht => h.analyticAt_saSmoothCGF ht s
  have hc : DifferentiableAt ℝ (iteratedDeriv 2 (saSmoothCGF ν s)) lam := by
    rw [iteratedDeriv_eq_iterate]
    exact (han.iterated_deriv 2 lam hlt).differentiableAt
  have hd : HasDerivAt (iteratedDeriv 2 (saSmoothCGF ν s))
      (iteratedDeriv 3 (saSmoothCGF ν s) lam) lam := by
    rw [congrFun (iteratedDeriv_succ (n := 2) (f := saSmoothCGF ν s)) lam]
    exact hc.hasDerivAt
  have hv : 0 < iteratedDeriv 2 (saSmoothCGF ν s) lam := by
    have := (h.saSmoothCGF_variance_bracket hvlo hθ (abs_le.mpr hmem) s).1
    have := h.var_ge
    change 0 < iteratedDeriv 2 (saSmoothCGF ν s) (saSaddle vlo B θ ν s w)
    nlinarith [sq_nonneg s]
  have hh := (hd.comp w (h.hasDerivAt_saSaddle hvlo hθ s hw)).inv
    (by change iteratedDeriv 2 (saSmoothCGF ν s) lam ≠ 0; exact hv.ne')
  have heq : iteratedDeriv 2 (saRate vlo B θ ν s) =ᶠ[𝓝 w]
      fun t => (iteratedDeriv 2 (saSmoothCGF ν s) (saSaddle vlo B θ ν s t))⁻¹ := by
    filter_upwards [(isOpen_lt continuous_abs continuous_const).eventually_mem hw] with t ht
    exact h.iteratedDeriv_two_saRate hvlo hθ s ht
  apply (hh.congr_of_eventuallyEq heq).congr_deriv
  change -(iteratedDeriv 3 (saSmoothCGF ν s) lam *
      (iteratedDeriv 2 (saSmoothCGF ν s) lam)⁻¹) /
        (iteratedDeriv 2 (saSmoothCGF ν s) lam) ^ 2 =
      -iteratedDeriv 3 (saSmoothCGF ν s) lam / (iteratedDeriv 2 (saSmoothCGF ν s) lam) ^ 3
  field_simp [hv.ne']

theorem UnivClass.abs_iteratedDeriv_three_saRate_le (h : UnivClass vlo vhi κ₃ B θ ν)
    (hvlo : 0 < vlo) (hθ : 0 < θ) (s : ℝ) {w : ℝ}
    (hw : |w| < 3 / 4 * vlo * saTiltRadius vlo B θ) :
    |iteratedDeriv 3 (saRate vlo B θ ν s) w| ≤
      saCumulantThird B θ * (4 / (3 * vlo)) ^ 3 := by
  obtain ⟨hmem, -⟩ := h.saSaddle_spec hvlo hθ s hw.le
  have hlam := (abs_le.mpr hmem).trans (saTiltRadius_le_half vlo B hθ)
  have hlt : |saSaddle vlo B θ ν s w| < θ := lt_of_le_of_lt hlam (by linarith)
  have hnum : |iteratedDeriv 3 (saSmoothCGF ν s) (saSaddle vlo B θ ν s w)| ≤
      saCumulantThird B θ := by
    rw [h.iteratedDeriv_three_saSmoothCGF hlt s]
    exact h.abs_iteratedDeriv_three_centered_cgf_le hθ hlam
  have hv := (h.saSmoothCGF_variance_bracket hvlo hθ (abs_le.mpr hmem) s).1
  have hvlow : 3 / 4 * vlo ≤ iteratedDeriv 2 (saSmoothCGF ν s) (saSaddle vlo B θ ν s w) := by
    nlinarith [h.var_ge, sq_nonneg s]
  have hvpos : 0 < iteratedDeriv 2 (saSmoothCGF ν s) (saSaddle vlo B θ ν s w) := by
    linarith
  have hinv : (iteratedDeriv 2 (saSmoothCGF ν s) (saSaddle vlo B θ ν s w))⁻¹ ≤
      4 / (3 * vlo) := by
    rw [inv_eq_one_div, div_le_div_iff₀ hvpos (by positivity)]
    linarith
  rw [congrFun (iteratedDeriv_succ (n := 2) (f := saRate vlo B θ ν s)) w,
    (h.hasDerivAt_iteratedDeriv_two_saRate hvlo hθ s hw).deriv,
    abs_div, abs_neg, abs_pow, abs_of_pos hvpos, div_eq_mul_inv, ← inv_pow]
  exact mul_le_mul hnum (pow_le_pow_left₀ (inv_nonneg.mpr hvpos.le) hinv 3)
    (pow_nonneg (inv_nonneg.mpr hvpos.le) _) (saCumulantThird_pos B hθ).le

theorem UnivClass.abs_saSaddle_lt_radius (h : UnivClass vlo vhi κ₃ B θ ν)
    (hvlo : 0 < vlo) (hθ : 0 < θ) (s : ℝ) {w : ℝ}
    (hw : |w| < 3 / 4 * vlo * saTiltRadius vlo B θ) :
    |saSaddle vlo B θ ν s w| < saTiltRadius vlo B θ := by
  apply (h.abs_saSaddle_le hvlo hθ s hw.le).trans_lt
  rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
  linarith

/-- Analyticity of the inverse follows from the analytic inverse function theorem. -/
theorem UnivClass.analyticAt_saSaddle (h : UnivClass vlo vhi κ₃ B θ ν)
    (hvlo : 0 < vlo) (hθ : 0 < θ) (s : ℝ) {w : ℝ}
    (hw : |w| < 3 / 4 * vlo * saTiltRadius vlo B θ) :
    AnalyticAt ℝ (saSaddle vlo B θ ν s) w := by
  let lam := saSaddle vlo B θ ν s w
  have hr := h.abs_saSaddle_lt_radius hvlo hθ s hw
  have htθ : |lam| < θ := lt_of_lt_of_le hr
    ((saTiltRadius_le_half vlo B hθ).trans (by linarith))
  have han : AnalyticOnNhd ℝ (saSmoothCGF ν s) {t : ℝ | |t| < θ} :=
    fun t ht => h.analyticAt_saSmoothCGF ht s
  have hmean : AnalyticAt ℝ (deriv (saSmoothCGF ν s)) lam := han.deriv lam htθ
  have hp : 0 < iteratedDeriv 2 (saSmoothCGF ν s) lam := by
    have hb := (h.saSmoothCGF_variance_bracket hvlo hθ hr.le s).1
    have := h.var_ge
    change 0 < iteratedDeriv 2 (saSmoothCGF ν s) (saSaddle vlo B θ ν s w)
    nlinarith [sq_nonneg s]
  have hp' : deriv (deriv (saSmoothCGF ν s)) lam ≠ 0 := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using hp.ne'
  have heq : saSaddle vlo B θ ν s ∘ deriv (saSmoothCGF ν s) =ᶠ[𝓝 lam] id := by
    filter_upwards [(isOpen_lt continuous_abs continuous_const).eventually_mem hr] with t ht
    exact h.saSaddle_leftInvOn hvlo hθ s (abs_le.mp ht.le)
  have hc : AnalyticAt ℝ (saSaddle vlo B θ ν s ∘ deriv (saSmoothCGF ν s)) lam :=
    analyticAt_id.congr heq.symm
  have hh := (analyticAt_comp_iff_of_deriv_ne_zero hmean hp').mp hc
  rwa [(h.saSaddle_spec hvlo hθ s hw.le).2] at hh

theorem UnivClass.analyticAt_saRate (h : UnivClass vlo vhi κ₃ B θ ν)
    (hvlo : 0 < vlo) (hθ : 0 < θ) (s : ℝ) {w : ℝ}
    (hw : |w| < 3 / 4 * vlo * saTiltRadius vlo B θ) :
    AnalyticAt ℝ (saRate vlo B θ ν s) w := by
  have hi := h.analyticAt_saSaddle hvlo hθ s hw
  have htθ : |saSaddle vlo B θ ν s w| < θ :=
    (h.abs_saSaddle_lt_radius hvlo hθ s hw).trans_le
      ((saTiltRadius_le_half vlo B hθ).trans (by linarith))
  exact (hi.mul analyticAt_id).sub ((h.analyticAt_saSmoothCGF htθ s).comp hi)

end

end PGM
