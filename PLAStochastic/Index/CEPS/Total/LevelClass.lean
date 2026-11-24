import PLAStochastic.Index.CEPS.Total.Level
import PLAStochastic.Index.CEPS.Assembly.Interfaces
import PLAStochastic.Index.CEPS.Assembly.Output

/-!
# WP10: every input class lies in finitely many levels

For `ν` in `CepsInputClass D θ vlo vhi m η r` with `m ≥ cepsLevelOrder`, the continuous Sobolev
density `f` of `ν` satisfies the pointwise `RegLaw` bounds (a continuous function that is a.e.
below a continuous bound is everywhere below it), the step density `f(1 - ·)` is in the weighted
Sobolev class with `‖f(1-·)‖ ≤ e^η (‖f_Λ‖ + r)`, and lowering the weight to `2^{-n} ≤ η` keeps
both. Hence `CepsLevel n ν` for every `n` with `2^n` above all class constants
(`cepsInputClass_level`), and `cepsLevelIndex ν ≤ n`.
-/

noncomputable section
open MeasureTheory Set Filter Topology

namespace PGM

/-! ### Weighted Sobolev size under reflection and weight change -/

theorem exp_mul_abs_le_shift {η x : ℝ} (hη : 0 ≤ η) :
    Real.exp (η * |x|) ≤ Real.exp η * Real.exp (η * |1 - x|) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have : |x| ≤ 1 + |1 - x| := by
    have := abs_sub_abs_le_abs_sub x 1
    rw [abs_one, abs_sub_comm] at this
    linarith
  nlinarith

theorem CepsSobolevClass.one_sub {m : ℕ} {η : ℝ} {f : ℝ → ℝ} (hf : CepsSobolevClass m η f)
    (hη : 0 ≤ η) : CepsSobolevClass m η (fun x => f (1 - x)) := by
  refine ⟨hf.contDiff.comp (by fun_prop), fun r hr => ?_⟩
  have hg := (hf.integrable r hr).comp_sub_left (1 : ℝ)
  have hcont : Continuous (iteratedDeriv r f) :=
    hf.contDiff.continuous_iteratedDeriv r (by exact_mod_cast hr)
  rw [iteratedDeriv_comp_const_sub]
  refine (hg.norm.const_mul (Real.exp η)).mono' (by fun_prop) (ae_of_all _ fun x => ?_)
  simp only [smul_eq_mul, norm_mul, Real.norm_eq_abs, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_pos (Real.exp_pos _)]
  have h := exp_mul_abs_le_shift (x := x) hη
  calc Real.exp (η * |x|) * |iteratedDeriv r f (1 - x)| ≤
      Real.exp η * Real.exp (η * |1 - x|) * |iteratedDeriv r f (1 - x)| := by gcongr
    _ = Real.exp η * (Real.exp (η * |1 - x|) * |iteratedDeriv r f (1 - x)|) := by ring

theorem cepsSobolev_one_sub_le {m : ℕ} {η : ℝ} {f : ℝ → ℝ} (hf : CepsSobolevClass m η f)
    (hη : 0 ≤ η) :
    cepsSobolev m η (fun x => f (1 - x)) ≤ Real.exp η * cepsSobolev m η f := by
  unfold cepsSobolev
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun r hr => ?_
  have hr' : r ≤ m := by have := Finset.mem_range.mp hr; omega
  have hi := hf.integrable_abs hr'
  rw [iteratedDeriv_comp_const_sub, ← integral_const_mul,
    ← integral_sub_left_eq_self (fun y => Real.exp η * (Real.exp (η * |y|) *
      |iteratedDeriv r f y|)) volume (1 : ℝ)]
  refine integral_mono_of_nonneg (ae_of_all _ fun x => by positivity)
    ((hi.comp_sub_left (1 : ℝ)).const_mul _) (ae_of_all _ fun x => ?_)
  simp only [smul_eq_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  have h := exp_mul_abs_le_shift (x := x) hη
  calc Real.exp (η * |x|) * |iteratedDeriv r f (1 - x)| ≤
      Real.exp η * Real.exp (η * |1 - x|) * |iteratedDeriv r f (1 - x)| := by gcongr
    _ = _ := by ring

theorem CepsSobolevClass.mono_weight {m : ℕ} {η η' : ℝ} {f : ℝ → ℝ} (hf : CepsSobolevClass m η f)
    (hle : η' ≤ η) : CepsSobolevClass m η' f := by
  refine ⟨hf.contDiff, fun r hr => ?_⟩
  have hcont : Continuous (iteratedDeriv r f) :=
    hf.contDiff.continuous_iteratedDeriv r (by exact_mod_cast hr)
  refine (hf.integrable r hr).norm.mono' (by fun_prop) (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), Real.norm_eq_abs, abs_mul,
    abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_right hle (abs_nonneg x))) (abs_nonneg _)

theorem cepsSobolev_mono_weight {m : ℕ} {η η' : ℝ} {f : ℝ → ℝ} (hf : CepsSobolevClass m η f)
    (hle : η' ≤ η) : cepsSobolev m η' f ≤ cepsSobolev m η f := by
  unfold cepsSobolev
  refine Finset.sum_le_sum fun r hr => ?_
  have hr' : r ≤ m := by have := Finset.mem_range.mp hr; omega
  refine integral_mono_of_nonneg (ae_of_all _ fun x => by positivity) (hf.integrable_abs hr')
    (ae_of_all _ fun x => ?_)
  exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_right hle (abs_nonneg x))) (abs_nonneg _)

/-! ### A continuous density inherits the pointwise bounds of any density -/

theorem continuous_le_of_ae_le {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ᵐ x, f x ≤ g x) : ∀ x, f x ≤ g x := by
  intro x
  by_contra hne
  set U := {x | g x < f x}
  have hU : IsOpen U := isOpen_lt hg hf
  have hne' : U.Nonempty := ⟨x, lt_of_not_ge hne⟩
  have hzero : volume U = 0 := by
    have := ae_iff.mp h
    simpa only [not_le] using this
  exact (hU.measure_ne_zero volume hne') hzero

theorem ae_eq_of_withDensity_eq {f g : ℝ → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (h : volume.withDensity (fun x => ENNReal.ofReal (f x)) =
      volume.withDensity (fun x => ENNReal.ofReal (g x))) : f =ᵐ[volume] g := by
  have he := (withDensity_eq_iff_of_sigmaFinite (μ := volume)
    (ENNReal.measurable_ofReal.comp hf).aemeasurable
    (ENNReal.measurable_ofReal.comp hg).aemeasurable).mp h
  filter_upwards [he] with x hx
  have := congrArg ENNReal.toReal hx
  simpa [ENNReal.toReal_ofReal (hf0 x), ENNReal.toReal_ofReal (hg0 x)] using this

/-- A continuous density of a law with a density vanishing on `(-∞, 0]` and bounded by
`D e^{-θx}` has the same pointwise bounds. -/
theorem continuous_density_bounds {f g : ℝ → ℝ} (hf : Continuous f) (hg : Measurable g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) (hgneg : ∀ x, x ≤ 0 → g x = 0) {D θ : ℝ}
    (hgb : ∀ x, g x ≤ D * Real.exp (-θ * x))
    (h : volume.withDensity (fun x => ENNReal.ofReal (f x)) =
      volume.withDensity (fun x => ENNReal.ofReal (g x))) :
    (∀ x, x ≤ 0 → f x = 0) ∧ ∀ x, f x ≤ D * Real.exp (-θ * x) := by
  have hae := ae_eq_of_withDensity_eq hf.measurable hg hf0 hg0 h
  have hb : ∀ x, f x ≤ D * Real.exp (-θ * x) :=
    continuous_le_of_ae_le hf (by fun_prop) (by
      filter_upwards [hae] with x hx
      rw [hx]; exact hgb x)
  refine ⟨?_, hb⟩
  -- `f ≤ 0` on `(-∞, 0)`
  have hneg : Iio (0 : ℝ) ⊆ {x | f x ≤ 0} := by
    intro x hx
    by_contra hpos
    set U := Iio (0 : ℝ) ∩ {x | 0 < f x}
    have hU : IsOpen U := isOpen_Iio.inter (isOpen_lt continuous_const hf)
    have hne : U.Nonempty := ⟨x, hx, show 0 < f x from lt_of_not_ge hpos⟩
    have hzero : volume U = 0 := by
      refine measure_mono_null (t := {x | ¬ (f x = g x)}) (fun y hy => ?_) (ae_iff.mp hae)
      intro he
      have := hgneg y (le_of_lt hy.1)
      have h2 := hy.2
      simp only [Set.mem_ofPred_eq] at h2
      linarith [he.symm ▸ this]
    exact (hU.measure_ne_zero volume hne) hzero
  have hcl : closure (Iio (0 : ℝ)) ⊆ {x | f x ≤ 0} :=
    (isClosed_le hf continuous_const).closure_subset_iff.mpr hneg
  rw [closure_Iio] at hcl
  intro x hx
  exact le_antisymm (hcl hx) (hf0 x)

/-- **Input classes lie in finitely many levels.** -/
theorem cepsInputClass_level {D θ vlo vhi η r : ℝ} {m : ℕ} (hm : cepsLevelOrder ≤ m)
    (hη : 0 < η) {n : ℕ} (hn1 : D ≤ cepsLevelScale n)
    (hn2 : cepsLevelRate n ≤ θ) (hn3 : cepsLevelRate n ≤ vlo) (hn4 : vhi ≤ cepsLevelScale n)
    (hn5 : cepsLevelRate n ≤ η)
    (hn6 : Real.exp η * (cepsSobolev m η cepsLambdaDensity + r) ≤ cepsLevelScale n)
    {ν : ProbabilityMeasure ℝ} (h : CepsInputClass D θ vlo vhi m η r ν) : CepsLevel n ν := by
  obtain ⟨⟨g, hgm, hg0, hgneg, hgb, hνg⟩, hmean, hvge, hvle⟩ := h.reg
  obtain ⟨f, hf0, hfS, hν, hdist⟩ := h.density
  have hfc : Continuous f := hfS.contDiff.continuous
  obtain ⟨hfneg, hfb⟩ := continuous_density_bounds hfc hgm hf0 hg0 hgneg hgb (hν.symm.trans hνg)
  have hrate := cepsLevelRate_pos n
  have hS6 : CepsSobolevClass cepsLevelOrder η f := hfS.mono_order hm
  have hSW : CepsSobolevClass cepsLevelOrder η (fun x => f (1 - x)) := hS6.one_sub hη.le
  refine ⟨f, hfc.measurable, hf0, hfneg, fun x => ?_, hν, hmean, hn3.trans hvge, hvle.trans hn4,
    hSW.mono_weight hn5, ?_⟩
  · rcases le_or_gt x 0 with hx | hx
    · rw [hfneg x hx]; exact mul_nonneg (cepsLevelScale_pos n).le (Real.exp_pos _).le
    · refine (hfb x).trans (mul_le_mul hn1 (Real.exp_le_exp.mpr (by nlinarith))
        (Real.exp_pos _).le (cepsLevelScale_pos n).le)
  · calc cepsSobolev cepsLevelOrder (cepsLevelRate n) (fun x => f (1 - x))
        ≤ cepsSobolev cepsLevelOrder η (fun x => f (1 - x)) := cepsSobolev_mono_weight hSW hn5
      _ ≤ Real.exp η * cepsSobolev cepsLevelOrder η f := cepsSobolev_one_sub_le hS6 hη.le
      _ ≤ Real.exp η * cepsSobolev m η f := by
          gcongr; exact cepsSobolev_mono_order hm η f
      _ ≤ Real.exp η * (cepsSobolev m η cepsLambdaDensity + r) := by
          gcongr
          have hsub := hfS.sub h.reference
          have hadd := cepsSobolev_add_le h.reference hsub
          have he : (fun x => cepsLambdaDensity x + (f x - cepsLambdaDensity x)) = f := by
            funext x; ring
          rw [he] at hadd
          linarith
      _ ≤ cepsLevelScale n := hn6

end PGM
