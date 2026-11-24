import PLAStochastic.Index.GEP.Kernel.BV.Scale
import PLAStochastic.Index.GEP.Kernel.BV.LastStep

/-!
# Pointwise regular and uniformly small parts of the original killed chain

The last original killed step converts the constructed BV decomposition into
an interval-Lipschitz part and a uniformly small remainder. Every equality here
is pointwise, and both endpoint jumps remain included in the variation budget.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set

def kBVVarBudget (D vlo vhi w : ℝ) (n : ℕ) (N : ℝ) : ℝ :=
  kBVClassVarConst D vlo vhi * Real.sqrt (w / (n : ℝ)) *
    Real.exp (-(kBVClassRate D vlo vhi * n / w ^ 2)) * N

def kBVRemBudget (D vlo vhi w : ℝ) (n : ℕ) (N : ℝ) : ℝ :=
  kBVClassRemConst D vlo vhi / Real.sqrt (n : ℝ) * kBVClassRho D vlo vhi ^ (n / 2) *
    Real.exp (-(kBVClassRate D vlo vhi * n / w ^ 2)) * N

/-- A final real step preserves the exact decomposition, the variation budget,
and interval support, and gives pointwise Lipschitz and uniform-error bounds. -/
theorem kBV_last_step_decomposition {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {D β a α w b e : ℝ} (hν : LocBd D ν) (hD : 0 ≤ D) (ha : a ≠ 0)
    (hw : 0 ≤ w) (hb : 0 ≤ b) (he : 0 ≤ e) {u : ℝ → ℂ}
    (hu : Measurable u) (h1 : Integrable u) (h2 : MemLp u 2)
    (hsupp : ∀ x, x ∉ Icc α (α + w) → u x = 0) {G R : KernelL2}
    (hGR : h2.toLp u = G + R) (hG : kBVHasRep (Icc α (α + w)) b G) (hR : ‖R‖ ≤ e) :
    ∃ g r : ℝ → ℂ, Measurable g ∧ Integrable g ∧ MemLp g 2 ∧
      Measurable r ∧ Integrable r ∧ MemLp r 2 ∧
      (∀ x, x ∉ Icc α (α + w) → g x = 0 ∧ r x = 0) ∧
      (∀ x, kStep (Icc α (α + w)) ν β a u x = g x + r x) ∧
      eVariationOn g univ ≤ ENNReal.ofReal b ∧
      (∀ x ∈ Icc α (α + w), ∀ y ∈ Icc α (α + w),
        ‖g x - g y‖ ≤ (D / |a| * b) * |x - y|) ∧
      (∀ x, ‖r x‖ ≤ Real.sqrt (D / |a|) * e) := by
  obtain ⟨g, r, hg, hg1, hg2, hr, hr1, hr2, hs, hsum, hvar, hnorm⟩ :=
    kBV_decomposition_representatives hu h1 h2 hsupp hGR hG
  have hgbv : BoundedVariationOn g univ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hvar
  have heq : u = g + r := funext hsum
  refine ⟨kStep (Icc α (α + w)) ν β a g, kStep (Icc α (α + w)) ν β a r,
    measurable_kStep measurableSet_Icc ν hg,
    (integrable_kConv ν hg hg1 β a).indicator measurableSet_Icc,
    ((memLp_two_kConv ν hg hg1 hg2 β a).1).indicator measurableSet_Icc,
    measurable_kStep measurableSet_Icc ν hr,
    (integrable_kConv ν hr hr1 β a).indicator measurableSet_Icc,
    ((memLp_two_kConv ν hr hr1 hr2 β a).1).indicator measurableSet_Icc, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact ⟨indicator_of_notMem hx _, indicator_of_notMem hx _⟩
  · intro x
    rw [heq, kernel_kStep_add hν ha hg hg2 hr hr2]
    rfl
  · exact (kBV_variation_kStep_le hg hgbv hg1 (by linarith) β a).trans hvar
  · intro x hx y hy
    have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hvar
    rw [ENNReal.toReal_ofReal hb] at hreal
    exact (kernel_kStep_lip_on hν hD ha hgbv hg1 hx hy).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hreal (div_nonneg hD (abs_nonneg a))) (abs_nonneg _))
  · intro x
    have hk := kernel_kStep_norm_sq_le (β := β) hν hD ha hr hr2 (Icc α (α + w)) x
    change ‖kStep (Icc α (α + w)) ν β a r x‖ ^ 2 ≤ D / |a| * kBVNormSq r at hk
    rw [hnorm] at hk
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) he)).mp
    rw [mul_pow, Real.sq_sqrt (div_nonneg hD (abs_nonneg a))]
    exact hk.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg R) hR 2)
      (div_nonneg hD (abs_nonneg a)))

/-- A pointwise decomposition of the original `(n+1)`-step killed integral
iterate. The regular part has the sharp long-kernel variation and interval
Lipschitz scale; the error is uniformly exponentially small at every point. -/
theorem kBV_regLaw_pointwise_decomposition {D θ vlo vhi : ℝ} (hD : 0 < D) (hθ : 0 < θ)
    (hvlo : 0 < vlo) {ν : ProbabilityMeasure ℝ} (hν : RegLaw D θ vlo vhi ν)
    (β : ℝ) {a α w : ℝ} (ha : 1 / 2 ≤ |a|) (hw : 1 ≤ w)
    {u : ℝ → ℂ} (hu : Measurable u) (h2 : MemLp u 2)
    (hsupp : ∀ x, x ∉ Icc α (α + w) → u x = 0) (n : ℕ) (hn : 8 ≤ n) :
    ∃ g r : ℝ → ℂ, Measurable g ∧ Integrable g ∧ MemLp g 2 ∧
      Measurable r ∧ Integrable r ∧ MemLp r 2 ∧
      (∀ x, x ∉ Icc α (α + w) → g x = 0 ∧ r x = 0) ∧
      (∀ x, ((kStep (Icc α (α + w)) (ν : Measure ℝ) β a)^[n + 1] u) x = g x + r x) ∧
      eVariationOn g univ ≤ ENNReal.ofReal (kBVVarBudget D vlo vhi w n ‖h2.toLp u‖) ∧
      (∀ x ∈ Icc α (α + w), ∀ y ∈ Icc α (α + w),
        ‖g x - g y‖ ≤ (D / |a| * kBVVarBudget D vlo vhi w n ‖h2.toLp u‖) * |x - y|) ∧
      (∀ x, ‖r x‖ ≤ Real.sqrt (D / |a|) * kBVRemBudget D vlo vhi w n ‖h2.toLp u‖) := by
  have h1 : Integrable u := kill_integrable_of_support
    (by simp : volume (Icc α (α + w)) ≠ ⊤) hsupp h2
  have hreg := kBV_kStep_iterate_regular (J := Icc α (α + w)) measurableSet_Icc
    (ν : Measure ℝ) β a hu h1 h2 n
  have hs := kBV_kStep_iterate_support (ν : Measure ℝ) β a hsupp n
  obtain ⟨G, R, hGR, hG, hR⟩ := kBV_regLaw_scaled_decomposition hD hθ hvlo hν β ha hw hu h2 hsupp n hn
  rw [kBVKilledL2_pow_toLp measurableSet_Icc (ν : Measure ℝ) β a hu h1 h2 hsupp n] at hGR
  have ha0 : a ≠ 0 := by intro h; simp only [h, abs_zero] at ha; linarith
  have hconst := kBVClass_constants hD hvlo (hν.var_ge.trans hν.var_le)
  have hb : 0 ≤ kBVVarBudget D vlo vhi w n ‖h2.toLp u‖ := by
    unfold kBVVarBudget
    exact mul_nonneg (mul_nonneg (mul_nonneg hconst.2.2.2.2.le (Real.sqrt_nonneg _))
      (Real.exp_pos _).le) (norm_nonneg _)
  have he : 0 ≤ kBVRemBudget D vlo vhi w n ‖h2.toLp u‖ := by
    unfold kBVRemBudget
    exact mul_nonneg (mul_nonneg
      (mul_nonneg (div_nonneg hconst.2.2.2.1.le (Real.sqrt_nonneg _)) (pow_nonneg hconst.1 _))
      (Real.exp_pos _).le) (norm_nonneg _)
  have hfinal := kBV_last_step_decomposition (β := β) (hν.envBd.locBd hD.le hθ.le) hD.le ha0
    (by linarith : 0 ≤ w) hb he hreg.1 hreg.2.1 hreg.2.2 hs hGR hG hR
  simpa only [Function.iterate_succ_apply'] using hfinal

end
end PGM
