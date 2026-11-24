import PLAStochastic.Index.KEP.Poisson.ChildScale
import Mathlib.Probability.Kernel.Composition.MapComap

/-!
# The actual child state kernel in fixed parent physical units

The anchor is the actual parent position plus its reference physical scale
times the observed cumulative gap. The output dilation is the original
intensity ratio. The proved reference scale estimate pays the single-step
comparison in terms of that physical cumulative state.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory

theorem measurable_kepPoissonParentScale {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (x : ℝ) :
    Measurable (fun p : ℝ × ℝ => (f x / f p.1) * p.2) :=
  (measurable_const.div (hf.continuous.measurable.comp measurable_fst)).mul measurable_snd

def kepPoissonFixedScaleKernel {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (eps n x : ℝ) (j : ℕ) : Kernel ℝ ℝ :=
  ((Kernel.id : Kernel ℝ ℝ) ×ₖ kepPoissonLayerKernel hf eps n j).map
    (fun p : ℝ × ℝ => (f x / f p.1) * p.2)

instance isMarkovKernel_kepPoissonFixedScaleKernel {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (eps n x : ℝ) (j : ℕ) :
    IsMarkovKernel (kepPoissonFixedScaleKernel hf eps n x j) :=
  Kernel.IsMarkovKernel.map _ (measurable_kepPoissonParentScale hf x)

theorem kepPoissonFixedScaleKernel_apply {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (eps n x y : ℝ) (j : ℕ) :
    kepPoissonFixedScaleKernel hf eps n x j y = kepPoissonFixedScaleMeasure hf eps n x y j := by
  have hF : Measurable (fun z : ℝ => (f x / f y) * z) :=
    measurable_const.mul measurable_id
  ext s hs
  rw [kepPoissonFixedScaleKernel, Kernel.map_apply' _ (measurable_kepPoissonParentScale hf x) y hs,
    Kernel.id_prod_apply' _ y ((measurable_kepPoissonParentScale hf x) hs),
    kepPoissonLayerKernel_apply, kepPoissonFixedScaleMeasure,
    Measure.map_apply hF hs]
  rfl

def kepPoissonParentAnchor {f : ℝ → ℝ} {flo fhi L : ℝ}
    (_hf : KepIntensityProfile f flo fhi L) (eps n x : ℝ) (j : ℕ) (S : ℝ) : ℝ :=
  x + (kepReferenceSpan eps j / (n * f x)) * S

theorem measurable_kepPoissonParentAnchor {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (eps n x : ℝ) (j : ℕ) :
    Measurable (kepPoissonParentAnchor hf eps n x j) :=
  measurable_const.add (measurable_const.mul measurable_id)

def kepPoissonParentStepKernel {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (eps n x : ℝ) (j : ℕ) : Kernel ℝ ℝ :=
  (kepPoissonFixedScaleKernel hf eps n x j).comap
    (kepPoissonParentAnchor hf eps n x j) (measurable_kepPoissonParentAnchor hf eps n x j)

instance isMarkovKernel_kepPoissonParentStepKernel {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (eps n x : ℝ) (j : ℕ) :
    IsMarkovKernel (kepPoissonParentStepKernel hf eps n x j) := by
  unfold kepPoissonParentStepKernel
  infer_instance

theorem kepPoissonParentStepKernel_apply {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (eps n x S : ℝ) (j : ℕ) :
    kepPoissonParentStepKernel hf eps n x j S =
      kepPoissonFixedScaleMeasure hf eps n x (kepPoissonParentAnchor hf eps n x j S) j := by
  rw [kepPoissonParentStepKernel, Kernel.comap_apply, kepPoissonFixedScaleKernel_apply]

theorem kepPoisson_log_absolute_state_drift {f : ℝ → ℝ} {flo fhi L n m S : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (hn : 0 < n) (hm : 0 ≤ m) (x : ℝ) :
    |Real.log (f x / f (x + (m / (n * f x)) * S))| ≤
      (L / flo ^ 2) * (m / n) * |S| := by
  have hlo := hf.pos
  have hfx := hf.f_pos x
  have hL := hf.lip_nonneg
  have hell : 0 ≤ m / (n * f x) := by positivity
  have h := hf.log_difference_le x (x + (m / (n * f x)) * S)
  rw [Real.log_div hfx.ne' (hf.f_pos _).ne']
  apply h.trans
  rw [abs_sub_comm x _, add_sub_cancel_left, abs_mul, abs_of_nonneg hell]
  have hb : m / (n * f x) ≤ m / (n * flo) :=
    div_le_div_of_nonneg_left hm (mul_pos hn hlo)
      (mul_le_mul_of_nonneg_left (hf.lower x) hn.le)
  calc
    _ ≤ (L / flo) * ((m / (n * flo)) * |S|) := by gcongr
    _ = _ := by field_simp [hn.ne', hlo.ne']

theorem kepPoisson_parent_step_comparison {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) :
    ∃ K E : ℝ, 0 < K ∧ kepReferenceClassicalThreshold ≤ E ∧
      ∀ eps, E ≤ eps → ∀ n : ℝ, 0 < n → ∀ j : ℕ, 0 ≤ kepReferenceSpan eps j →
        ∀ r : ℝ,
          (∀ y, measureHellinger (kepPoissonLayerMeasure hf eps n y j)
            (kepReferenceLaw eps j) ≤ r) →
          ∀ x S, measureHellinger (kepPoissonParentStepKernel hf eps n x j S)
            (kepReferenceLaw eps j) ≤
              r + K * eps ^ 98 *
                ((L / flo ^ 2) * (kepReferenceSpan eps j / n) * |S|) ^ (2 / 3 : ℝ) := by
  obtain ⟨K, E, hK, hE, hs⟩ := kepPoisson_child_scale_comparison hf
  refine ⟨K, E, hK, hE, ?_⟩
  intro eps heps n hn j hm r hchild x S
  have hbase := hs eps heps n j x (kepPoissonParentAnchor hf eps n x j S) r
    (hchild (kepPoissonParentAnchor hf eps n x j S))
  have hnew : measureHellinger
      (kepPoissonFixedScaleMeasure hf eps n x (kepPoissonParentAnchor hf eps n x j S) j)
      (kepReferenceLaw eps j) ≤
      r + K * eps ^ 98 *
        ((L / flo ^ 2) * (kepReferenceSpan eps j / n) * |S|) ^ (2 / 3 : ℝ) := by
    apply hbase.trans
    apply add_le_add le_rfl
    apply mul_le_mul_of_nonneg_left
    · exact Real.rpow_le_rpow (abs_nonneg _)
        (kepPoisson_log_absolute_state_drift hf hn hm x) (by norm_num)
    · exact mul_nonneg hK.le (by positivity)
  simpa only [kepPoissonParentStepKernel_apply] using hnew

end

end PGM
