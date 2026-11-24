import PLAStochastic.Index.KEP.Poisson.LayerObjects
import PLAStochastic.Index.KEP.Poisson.IntensityDrift
import PLAStochastic.Index.KEP.ReferenceScale.UnconditionalScale

/-!
# Actual child laws in the fixed physical units of their parent

The dilation is the original intensity ratio. Data processing and the proved
reference scale regularity pay its Hellinger cost. The only comparison premise
is the induction hypothesis for the actual child law at its own anchor.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory

def kepPoissonFixedScaleMeasure {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (eps n x y : ℝ) (j : ℕ) : Measure ℝ :=
  (kepPoissonLayerMeasure hf eps n y j).map (fun z => (f x / f y) * z)

instance isProbabilityMeasure_kepPoissonFixedScaleMeasure {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (eps n x y : ℝ) (j : ℕ) :
    IsProbabilityMeasure (kepPoissonFixedScaleMeasure hf eps n x y j) :=
  Measure.isProbabilityMeasure_map (measurable_const.mul measurable_id).aemeasurable

theorem kepPoisson_fixed_scale_value {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (eps n x y : ℝ) (j : ℕ) (g : ℕ → ℝ) :
    (f x / f y) * kepPoissonLayerGap hf eps n y j g =
      (n * f x / kepReferenceSpan eps j) *
        (pairLayer eps j (kepPoissonPairs hf n y g) 0).1 := by
  unfold kepPoissonLayerGap
  have he : (f x / f y) * (n * f y / kepReferenceSpan eps j) =
      n * f x / kepReferenceSpan eps j := by
    rw [div_eq_mul_inv]
    field_simp [(hf.f_pos y).ne']
  rw [← mul_assoc, he]

theorem kepPoisson_child_scale_comparison {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) :
    ∃ K E : ℝ, 0 < K ∧ kepReferenceClassicalThreshold ≤ E ∧
      ∀ eps, E ≤ eps → ∀ n : ℝ, ∀ j : ℕ, ∀ x y r : ℝ,
        measureHellinger (kepPoissonLayerMeasure hf eps n y j) (kepReferenceLaw eps j) ≤ r →
        measureHellinger (kepPoissonFixedScaleMeasure hf eps n x y j) (kepReferenceLaw eps j) ≤
          r + K * eps ^ 98 * |Real.log (f x / f y)| ^ (2 / 3 : ℝ) := by
  obtain ⟨tm, htm, hs⟩ := kepReference_uniform_second_norm_and_scale
  obtain ⟨K, E, hK, hE, hscale⟩ := hs tm htm le_rfl
  refine ⟨K, E, hK, hE, ?_⟩
  intro eps heps n j x y r hchild
  let P := kepPoissonLayerMeasure hf eps n y j
  let Q : Measure ℝ := (kepReferenceLaw eps j : Measure ℝ)
  let F : ℝ → ℝ := fun z => (f x / f y) * z
  have hF : Measurable F := measurable_const.mul measurable_id
  let : IsProbabilityMeasure (P.map F) := Measure.isProbabilityMeasure_map hF.aemeasurable
  let : IsProbabilityMeasure (Q.map F) := Measure.isProbabilityMeasure_map hF.aemeasurable
  have hfirst : measureHellinger (P.map F) (Q.map F) ≤ r :=
    (measureHellinger_map P Q hF).trans hchild
  have hlog : 0 < f x / f y := div_pos (hf.f_pos x) (hf.f_pos y)
  have heF : (fun z : ℝ => Real.exp (Real.log (f x / f y)) * z) = F := by
    rw [Real.exp_log hlog]
  have hsecond : measureHellinger (Q.map F) Q ≤
      K * eps ^ 98 * |Real.log (f x / f y)| ^ (2 / 3 : ℝ) := by
    simpa only [heF] using (hscale eps heps).2 j (Real.log (f x / f y))
  exact (measureHellinger_triangle (P.map F) (Q.map F) Q).trans (add_le_add hfirst hsecond)

end

end PGM
