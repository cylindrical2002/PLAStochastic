import PLAStochastic.Index.KEP.Poisson.ParentState
import PLAStochastic.ForMathlib.Probability.Moments.ExponentialPolynomial

/-!
# Positivity and fixed-unit moments of the actual Poisson laws

The original hierarchy sums nonnegative physical gaps, including its defined
value on infinite blocks. The intensity bounds pay the fixed-unit dilation of
each conditional exponential moment uniformly in the physical anchor.
-/

set_option autoImplicit false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory

theorem pairLayer_fst_nonneg {z : ℕ → ℝ × ℕ} (hz : ∀ k, 0 ≤ (z k).1)
    (eps : ℝ) (j k : ℕ) : 0 ≤ (pairLayer eps j z k).1 := by
  induction j generalizing k with
  | zero => exact hz k
  | succ j ih =>
    rw [pairLayer, Function.iterate_succ_apply']
    simp only [layerMap_apply, Prod.fst_sum]
    exact Finset.sum_nonneg fun i _ => ih i

theorem kepPoissonPairs_fst_nonneg {f : ℝ → ℝ} {flo fhi L n : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (hn : 0 < n) (x : ℝ)
    {g : ℕ → ℝ} (hg : ∀ k, 0 ≤ g k) (k : ℕ) :
    0 ≤ (kepPoissonPairs hf n x g k).1 := by
  change 0 ≤ kepPoissonArrival hf n x (gapKeys g (k + 1)) -
    kepPoissonArrival hf n x (gapKeys g k)
  have he : gapKeys g (k + 1) = gapKeys g k + g k := by
    simp only [gapKeys, Finset.sum_range_succ]
  rw [he, ← kepPoissonArrival_restart]
  exact sub_nonneg.mpr (kepPoissonArrival_ge hf hn (hg k) _)

theorem kepPoissonLayerGap_nonneg {f : ℝ → ℝ} {flo fhi L eps n : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (hn : 0 < n) (x : ℝ) (j : ℕ)
    (hm : 0 ≤ kepReferenceSpan eps j) {g : ℕ → ℝ} (hg : ∀ k, 0 ≤ g k) :
    0 ≤ kepPoissonLayerGap hf eps n x j g :=
  mul_nonneg (div_nonneg (mul_nonneg hn.le (hf.f_pos x).le) hm)
    (pairLayer_fst_nonneg (kepPoissonPairs_fst_nonneg hf hn x hg) eps j 0)

theorem kepPoissonLayerMeasure_ae_nonneg {f : ℝ → ℝ} {flo fhi L eps n : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (hn : 0 < n) (x : ℝ) (j : ℕ)
    (hm : 0 ≤ kepReferenceSpan eps j) :
    ∀ᵐ z ∂kepPoissonLayerMeasure hf eps n x j, 0 ≤ z := by
  apply (ae_map_iff (measurable_kepPoissonLayerGap_anchor hf eps n x j).aemeasurable
    measurableSet_Ici).mpr
  filter_upwards [ae_all_iff.mpr fun k =>
    iidSeq_expCoord.ae_pos_of_expMeasure_one (hasLaw_expCoord 0) k] with g hg
  exact kepPoissonLayerGap_nonneg hf hn x j hm (fun k => (hg k).le)

theorem KepIntensityProfile.ratio_le {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (x y : ℝ) :
    f x / f y ≤ fhi / flo := by
  calc
    _ ≤ fhi / f y := div_le_div_of_nonneg_right (hf.upper x) (hf.f_pos y).le
    _ ≤ _ := div_le_div_of_nonneg_left hf.fhi_pos.le hf.pos (hf.lower y)

theorem kepPoisson_fixed_scale_exp_moment {f : ℝ → ℝ} {flo fhi L eps n theta B : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (hn : 0 < n) (htheta : 0 ≤ theta)
    (j : ℕ) (hm : 0 ≤ kepReferenceSpan eps j)
    (hchild : ∀ y, Integrable (fun z => Real.exp (theta * z)) (kepPoissonLayerMeasure hf eps n y j) ∧
      ∫ z, Real.exp (theta * z) ∂kepPoissonLayerMeasure hf eps n y j ≤ B)
    (x y : ℝ) :
    Integrable (fun z => Real.exp ((theta / (fhi / flo)) * z))
      (kepPoissonFixedScaleMeasure hf eps n x y j) ∧
    ∫ z, Real.exp ((theta / (fhi / flo)) * z) ∂kepPoissonFixedScaleMeasure hf eps n x y j ≤ B := by
  let t := theta / (fhi / flo)
  let c := f x / f y
  have hR : 0 < fhi / flo := div_pos hf.fhi_pos hf.pos
  have ht : 0 ≤ t := div_nonneg htheta hR.le
  have hct : t * c ≤ theta := by
    calc
      _ ≤ t * (fhi / flo) := mul_le_mul_of_nonneg_left (hf.ratio_le x y) ht
      _ = theta := div_mul_cancel₀ _ hR.ne'
  have hF : Measurable (fun z : ℝ => c * z) := measurable_const.mul measurable_id
  have hi : Integrable (fun z => Real.exp (t * (c * z)))
      (kepPoissonLayerMeasure hf eps n y j) := by
    apply (hchild y).1.mono' (by fun_prop)
    filter_upwards [kepPoissonLayerMeasure_ae_nonneg hf hn y j hm] with z hz
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (by nlinarith only [mul_le_mul_of_nonneg_right hct hz])
  have hib : ∫ z, Real.exp (t * (c * z)) ∂kepPoissonLayerMeasure hf eps n y j ≤ B := by
    apply (integral_mono_ae hi (hchild y).1 _).trans (hchild y).2
    filter_upwards [kepPoissonLayerMeasure_ae_nonneg hf hn y j hm] with z hz
    exact Real.exp_le_exp.mpr (by nlinarith only [mul_le_mul_of_nonneg_right hct hz])
  refine ⟨?_, ?_⟩
  · change Integrable (fun z => Real.exp (t * z))
      ((kepPoissonLayerMeasure hf eps n y j).map (fun z => c * z))
    exact (integrable_map_measure (by fun_prop) hF.aemeasurable).mpr hi
  · change (∫ z, Real.exp (t * z) ∂(kepPoissonLayerMeasure hf eps n y j).map
      (fun z => c * z)) ≤ B
    rw [integral_map hF.aemeasurable (by fun_prop)]
    exact hib

end

end PGM
