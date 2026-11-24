import PLAStochastic.Swing.StationaryLimit.LeadingCoefficient.IntegralPassage

/-!
# Uniform-integrability inheritance for the margin laws

This file supplies the functional-analytic step which is easy to lose when
passing from the finite reflected-margin laws to their weak limit.  A uniform
second absolute moment is used to prove that the limiting law has a finite
first absolute moment and that the first moments are uniformly integrable.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair
namespace LeadingCoefficient
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {ν : Measure ℝ}

/-! A bounded continuous truncation of the absolute value. -/

def absTrunc (C : ℝ) (x : ℝ) : ℝ := min |x| C

theorem absTrunc_nonneg {C x : ℝ} (hC : 0 ≤ C) : 0 ≤ absTrunc C x := by
  exact le_min (abs_nonneg _) hC

theorem absTrunc_le {C x : ℝ} : absTrunc C x ≤ C := min_le_right _ _

theorem absTrunc_le_abs {C x : ℝ} : absTrunc C x ≤ |x| := min_le_left _ _

theorem continuous_absTrunc (C : ℝ) : Continuous (absTrunc C) := by
  exact continuous_abs.min continuous_const

theorem measurable_absTrunc (C : ℝ) : Measurable (absTrunc C) :=
  (continuous_absTrunc C).measurable

theorem absTrunc_lipschitz (C : ℝ) :
    ∀ x y : ℝ, |absTrunc C x - absTrunc C y| ≤ |x-y| := by
  have habs : LipschitzWith 1 (fun x : ℝ => |x|) := by
    refine LipschitzWith.of_dist_le_mul (fun x y => ?_)
    rw [Real.dist_eq, Real.dist_eq]
    simpa using (abs_abs_sub_abs_le_abs_sub x y)
  have hmin := habs.min_const C
  intro x y
  simpa [absTrunc, Real.dist_eq, one_mul] using hmin.dist_le_mul x y

theorem isBddLip_absTrunc (C : ℝ) (hC : 0 ≤ C) :
    KernelLimit.IsBddLip (absTrunc C) 1 C := by
  refine ⟨measurable_absTrunc C, ?_, ?_⟩
  · intro x y
    simpa [one_mul] using absTrunc_lipschitz C x y
  · intro x
    have h0 : 0 ≤ absTrunc C x := absTrunc_nonneg hC
    have hle : absTrunc C x ≤ C := absTrunc_le
    rw [abs_of_nonneg h0]
    exact hle

/-! The square-moment hypothesis used below is deliberately stated in Bochner
form.  This lets callers feed it directly from the stationary-margin moment
lemmas, while the proof itself only uses bounded continuous truncations. -/

theorem absTrunc_integrable [IsFiniteMeasure ν]
    {C : ℝ} (hC : 0 ≤ C) : Integrable (absTrunc C) ν := by
  exact Integrable.of_bound (measurable_absTrunc C).aestronglyMeasurable
    C (ae_of_all _ (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (absTrunc_nonneg hC)]
      exact absTrunc_le))

theorem absTrunc_le_one_add_sq {C x : ℝ} :
    absTrunc C x ≤ 1 + |x| ^ 2 := by
  by_cases hx : |x| ≤ 1
  · have hax : absTrunc C x ≤ |x| := absTrunc_le_abs
    exact hax.trans (by nlinarith [sq_nonneg (|x|)])
  · have hx' : 1 < |x| := lt_of_not_ge hx
    have hsq : |x| ≤ |x| ^ 2 := by
      nlinarith [abs_nonneg x]
    exact (absTrunc_le_abs).trans (by linarith)

/-! Weak convergence plus a uniform square-moment bound gives the first
moment required by the reward transfer. -/

theorem limit_integrable_abs_of_uniform_sq_moment
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {νs : ι → ProbabilityMeasure ℝ} {ν : ProbabilityMeasure ℝ}
    (hν : Tendsto νs l (𝓝 ν))
    {M : ℝ}
    (hmom : ∀ i, Integrable (fun x : ℝ => |x| ^ 2) (νs i : Measure ℝ))
    (hbound : ∀ i, (∫ x : ℝ, |x| ^ 2 ∂(νs i : Measure ℝ)) ≤ M) :
    Integrable (fun x : ℝ => |x|) (ν : Measure ℝ) := by
  have htrunc_bound : ∀ (C : ℝ), 0 ≤ C →
      ∀ i, (∫ x : ℝ, absTrunc C x ∂(νs i : Measure ℝ)) ≤ 1 + M := by
    intro C hC i
    let _ : IsProbabilityMeasure (νs i : Measure ℝ) := inferInstance
    have htr : Integrable (absTrunc C) (νs i : Measure ℝ) := absTrunc_integrable hC
    have hdom : Integrable (fun x : ℝ => 1 + |x| ^ 2) (νs i : Measure ℝ) :=
      (integrable_const (1 : ℝ)).add (hmom i)
    have hmono : ∀ x : ℝ, absTrunc C x ≤ 1 + |x| ^ 2 :=
      fun x => absTrunc_le_one_add_sq
    calc
      (∫ x : ℝ, absTrunc C x ∂(νs i : Measure ℝ)) ≤
          ∫ x : ℝ, (1 + |x| ^ 2) ∂(νs i : Measure ℝ) :=
        integral_mono htr hdom hmono
      _ = 1 + ∫ x : ℝ, |x| ^ 2 ∂(νs i : Measure ℝ) := by
        rw [integral_add (integrable_const (1 : ℝ)) (hmom i), integral_const]
        simp
      _ ≤ 1 + M := by linarith [hbound i]
  have htrunc_lim : ∀ (n : ℕ),
      (∫ x : ℝ, absTrunc (n : ℝ) x ∂(ν : Measure ℝ)) ≤ 1 + M := by
    intro n
    have hn : (0 : ℝ) ≤ (n : ℝ) := by positivity
    have ht := KernelLimit.tendsto_integral_of_tendsto hν
      (absTrunc (n : ℝ)) (n : ℝ) (continuous_absTrunc _) (fun x => by
        calc
          |absTrunc (n : ℝ) x| = absTrunc (n : ℝ) x :=
            abs_of_nonneg (absTrunc_nonneg hn)
          _ ≤ (n : ℝ) := absTrunc_le)
    exact le_of_tendsto ht (Eventually.of_forall (fun i => htrunc_bound _ hn i))
  have hlin_eq :
      (∫⁻ x : ℝ, ENNReal.ofReal |x| ∂(ν : Measure ℝ)) =
        ⨆ n : ℕ, ∫⁻ x : ℝ, ENNReal.ofReal (absTrunc (n : ℝ) x)
          ∂(ν : Measure ℝ) := by
    have hmeas : ∀ n : ℕ, Measurable (fun x : ℝ =>
        ENNReal.ofReal (absTrunc (n : ℝ) x)) := by
      intro n
      exact ENNReal.measurable_ofReal.comp (measurable_absTrunc _)
    have hmono : Monotone (fun n : ℕ => fun x : ℝ =>
        ENNReal.ofReal (absTrunc (n : ℝ) x)) := by
      intro n m hnm x
      apply ENNReal.ofReal_le_ofReal
      exact min_le_min_left _ (by exact_mod_cast hnm)
    rw [← lintegral_iSup hmeas hmono]
    apply lintegral_congr_ae
    filter_upwards with x
    have hle : ∀ n : ℕ, ENNReal.ofReal (absTrunc (n : ℝ) x) ≤
        ENNReal.ofReal |x| := fun n => ENNReal.ofReal_le_ofReal absTrunc_le_abs
    apply (le_antisymm (iSup_le hle) ?_).symm
    obtain ⟨n, hn⟩ := exists_nat_ge |x|
    apply le_iSup_of_le n
    rw [absTrunc, min_eq_left hn]
  have hlin_le :
      (∫⁻ x : ℝ, ENNReal.ofReal |x| ∂(ν : Measure ℝ)) ≤
        ENNReal.ofReal (1 + M) := by
    rw [hlin_eq]
    apply iSup_le
    intro n
    have hn : (0 : ℝ) ≤ (n : ℝ) := by positivity
    have htr : Integrable (absTrunc (n : ℝ)) (ν : Measure ℝ) := by
      let _ : IsFiniteMeasure (ν : Measure ℝ) := inferInstance
      exact absTrunc_integrable hn
    have hnon : 0 ≤ᵐ[(ν : Measure ℝ)] absTrunc (n : ℝ) :=
      Eventually.of_forall (fun x => absTrunc_nonneg hn)
    rw [← ofReal_integral_eq_lintegral_ofReal htr hnon]
    exact ENNReal.ofReal_le_ofReal (htrunc_lim n)
  refine ⟨continuous_abs.measurable.aestronglyMeasurable, ?_⟩
  have htop : ENNReal.ofReal (1 + M) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hfinite : (∫⁻ x : ℝ, ‖(fun x : ℝ => |x|) x‖ₑ ∂(ν : Measure ℝ)) ≠ ⊤ := by
    have heq : (fun x : ℝ => ‖(fun x : ℝ => |x|) x‖ₑ) =
      (fun x : ℝ => ENNReal.ofReal |x|) := by
      funext x
      change ‖|x|‖ₑ = ENNReal.ofReal |x|
      rw [← ofReal_norm, Real.norm_eq_abs, abs_abs]
    rw [heq]
    exact (lt_of_le_of_lt hlin_le htop.lt_top).ne
  exact lt_top_iff_ne_top.mpr hfinite

end LeadingCoefficient
end SwingRepair
