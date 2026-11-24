import PLAStochastic.ForMathlib.Probability.OrderStatistics.Renyi
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Inverse

/-!
# Model K: sorted iid samples from a Lipschitz density on a compact interval

Model K draws `n` iid samples from a density `f` on `[A, B]` with `0 < f₋ ≤ f ≤ f₊` and `f`
Lipschitz (`DensityK`); the keys are the sorted samples.  The law of one sample is
`densityLaw f A B`.

* `cdfK f A x = ∫ t in A..x, f t` is continuous and strictly increasing on `[A, B]` and maps it
  onto `[0, 1]` (`cdfK_strictMonoOn`, `cdfK_continuousOn`, `cdfK_image`); `quantK f A B` is its
  inverse (`quantK_cdfK`, `cdfK_quantK`, `quantK_strictMonoOn`).  `quantK` clamps its argument
  to `[0, 1]`, so it is monotone and measurable on all of `ℝ`.
* `quantK` is differentiable with `Q' = 1 / f ∘ Q` on `(0, 1)` (`deriv_quantK`) and one-sidedly
  on `[0, 1]` (`derivWithin_quantK`); `1 / f₊ ≤ Q' ≤ 1 / f₋`, and `Q'` is Lipschitz on `[0, 1]`
  with constant `Lf / f₋ ^ 3` (`abs_derivWithin_quantK_sub_le`, `lipschitzOnWith_inv_f_quantK`).
* Probability integral transform: `cdfK f A` carries `densityLaw f A B` to the uniform law on
  `[0, 1]` (`hasLaw_cdfK`, `hasLaw_cdfK_comp`), `quantK` carries it back (`hasLaw_quantK`),
  `quantK (cdfK X) = X` almost surely (`quantK_cdfK_ae_eq`), and independence is preserved
  (`iIndepFun_cdfK`).
* Sorting commutes with monotone maps (`Renyi.sortVec_comp_of_monotoneOn`), so the sorted
  sample is `quantK` applied to the sorted uniforms (`sortVec_ae_eq_quantK_sortVec`); with the
  Rényi representation this gives `identDistrib_sortVec_quantK_gammaRatio`.
* For the constant density `1 / (B - A)`, `quantK u = A + (B - A) u` (`quantK_const`), and the
  sorted sample has the law of `A + (B - A) / Γ (n+1) * Γ (i+1)`
  (`identDistrib_sortVec_uniformK`).
-/
noncomputable section

namespace PGM

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal Nat

/-- The Model K density hypotheses on `[A, B]`. -/
structure DensityK (f : ℝ → ℝ) (A B fmin fmax Lf : ℝ) : Prop where
  lt : A < B
  pos : 0 < fmin
  lower : ∀ x ∈ Set.Icc A B, fmin ≤ f x
  upper : ∀ x ∈ Set.Icc A B, f x ≤ fmax
  lip : ∀ x ∈ Set.Icc A B, ∀ y ∈ Set.Icc A B, |f x - f y| ≤ Lf * |x - y|
  integral_one : ∫ x in A..B, f x = 1

/-- The law of one Model K sample: density `f` with respect to Lebesgue measure on `[A, B]`. -/
def densityLaw (f : ℝ → ℝ) (A B : ℝ) : Measure ℝ :=
  (volume.restrict (Set.Icc A B)).withDensity (fun x => ENNReal.ofReal (f x))

/-- The distribution function `x ↦ ∫ t in A..x, f t`. -/
def cdfK (f : ℝ → ℝ) (A x : ℝ) : ℝ :=
  ∫ t in A..x, f t

/-- The quantile function: the inverse of `cdfK f A : [A, B] → [0, 1]`.  The argument is first
clamped to `[0, 1]`, so `quantK f A B` is monotone (hence measurable) on all of `ℝ`. -/
def quantK (f : ℝ → ℝ) (A B : ℝ) (u : ℝ) : ℝ :=
  Function.invFunOn (cdfK f A) (Set.Icc A B) (max 0 (min u 1))

variable {f : ℝ → ℝ} {A B fmin fmax Lf : ℝ}

namespace DensityK

variable (hf : DensityK f A B fmin fmax Lf)
include hf

theorem le : A ≤ B := hf.lt.le

theorem left_mem : A ∈ Icc A B := left_mem_Icc.2 hf.le

theorem right_mem : B ∈ Icc A B := right_mem_Icc.2 hf.le

theorem lf_nonneg : 0 ≤ Lf := by
  have h := hf.lip A hf.left_mem B hf.right_mem
  have hpos : 0 < |A - B| := abs_pos.2 (sub_ne_zero.2 hf.lt.ne)
  exact nonneg_of_mul_nonneg_left ((abs_nonneg _).trans h) hpos

theorem fmin_le_fmax : fmin ≤ fmax :=
  (hf.lower A hf.left_mem).trans (hf.upper A hf.left_mem)

theorem fmax_pos : 0 < fmax := hf.pos.trans_le hf.fmin_le_fmax

theorem f_pos {x : ℝ} (hx : x ∈ Icc A B) : 0 < f x := hf.pos.trans_le (hf.lower x hx)

theorem lipschitzOnWith : LipschitzOnWith (Real.toNNReal Lf) f (Icc A B) :=
  LipschitzOnWith.of_dist_le_mul fun x hx y hy => by
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hf.lf_nonneg]
    exact hf.lip x hx y hy

theorem continuousOn : ContinuousOn f (Icc A B) := hf.lipschitzOnWith.continuousOn

theorem intervalIntegrable {x y : ℝ} (hx : x ∈ Icc A B) (hy : y ∈ Icc A B) :
    IntervalIntegrable f volume x y :=
  (hf.continuousOn.mono (uIcc_subset_Icc hx hy)).intervalIntegrable

end DensityK

/-! ### The distribution function -/

section cdf

theorem cdfK_left : cdfK f A A = 0 := intervalIntegral.integral_same

variable (hf : DensityK f A B fmin fmax Lf)
include hf

theorem cdfK_right : cdfK f A B = 1 := hf.integral_one

theorem cdfK_sub {x y : ℝ} (hx : x ∈ Icc A B) (hy : y ∈ Icc A B) :
    cdfK f A y - cdfK f A x = ∫ t in x..y, f t :=
  intervalIntegral.integral_interval_sub_left (hf.intervalIntegrable hf.left_mem hy)
    (hf.intervalIntegrable hf.left_mem hx)

theorem cdfK_sub_ge {x y : ℝ} (hx : x ∈ Icc A B) (hy : y ∈ Icc A B) (hxy : x ≤ y) :
    fmin * (y - x) ≤ cdfK f A y - cdfK f A x := by
  rw [cdfK_sub hf hx hy]
  have h := intervalIntegral.integral_mono_on hxy intervalIntegrable_const
    (hf.intervalIntegrable hx hy) fun t ht =>
      hf.lower t ⟨hx.1.trans ht.1, ht.2.trans hy.2⟩
  rw [intervalIntegral.integral_const, smul_eq_mul] at h
  linarith

theorem cdfK_sub_le {x y : ℝ} (hx : x ∈ Icc A B) (hy : y ∈ Icc A B) (hxy : x ≤ y) :
    cdfK f A y - cdfK f A x ≤ fmax * (y - x) := by
  rw [cdfK_sub hf hx hy]
  have h := intervalIntegral.integral_mono_on hxy (hf.intervalIntegrable hx hy)
    intervalIntegrable_const fun t ht =>
      hf.upper t ⟨hx.1.trans ht.1, ht.2.trans hy.2⟩
  rw [intervalIntegral.integral_const, smul_eq_mul] at h
  linarith

theorem cdfK_strictMonoOn : StrictMonoOn (cdfK f A) (Icc A B) := fun x hx y hy hxy => by
  have h := cdfK_sub_ge hf hx hy hxy.le
  have : 0 < fmin * (y - x) := mul_pos hf.pos (sub_pos.2 hxy)
  linarith

theorem cdfK_continuousOn : ContinuousOn (cdfK f A) (Icc A B) := by
  have h := intervalIntegral.continuousOn_primitive_interval' (a := A)
    (hf.intervalIntegrable hf.left_mem hf.right_mem) (by rw [uIcc_of_le hf.le]; exact hf.left_mem)
  rwa [uIcc_of_le hf.le] at h

theorem cdfK_mem_Icc {x : ℝ} (hx : x ∈ Icc A B) : cdfK f A x ∈ Icc 0 1 := by
  have h1 := (cdfK_strictMonoOn hf).monotoneOn hf.left_mem hx hx.1
  have h2 := (cdfK_strictMonoOn hf).monotoneOn hx hf.right_mem hx.2
  rw [cdfK_left] at h1
  rw [cdfK_right hf] at h2
  exact ⟨h1, h2⟩

theorem cdfK_image : cdfK f A '' Icc A B = Icc 0 1 := by
  refine Subset.antisymm ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact cdfK_mem_Icc hf hx
  · have h := intermediate_value_Icc hf.le (cdfK_continuousOn hf)
    rwa [cdfK_left, cdfK_right hf] at h

theorem cdfK_bijOn : BijOn (cdfK f A) (Icc A B) (Icc 0 1) :=
  ⟨fun _ hx => cdfK_mem_Icc hf hx, (cdfK_strictMonoOn hf).injOn, (cdfK_image hf).symm.subset⟩

end cdf

/-! ### The quantile function -/

section quant

private theorem clamp01_mem (u : ℝ) : max 0 (min u 1) ∈ Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩

private theorem clamp01_of_mem {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) : max 0 (min u 1) = u := by
  rw [min_eq_left hu.2, max_eq_right hu.1]

private theorem clamp01_mono : Monotone fun u : ℝ => max 0 (min u 1) :=
  fun _ _ h => max_le_max le_rfl (min_le_min_right _ h)

theorem quantK_clamp (u : ℝ) : quantK f A B (max 0 (min u 1)) = quantK f A B u := by
  unfold quantK
  rw [clamp01_of_mem (clamp01_mem u)]

variable (hf : DensityK f A B fmin fmax Lf)
include hf

theorem exists_cdfK_eq {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) : ∃ x ∈ Icc A B, cdfK f A x = u := by
  rw [← cdfK_image hf] at hu
  exact hu

theorem quantK_mem (u : ℝ) : quantK f A B u ∈ Icc A B :=
  Function.invFunOn_mem (exists_cdfK_eq hf (clamp01_mem u))

theorem cdfK_quantK {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) : cdfK f A (quantK f A B u) = u := by
  have h : cdfK f A (quantK f A B u) = max 0 (min u 1) :=
    Function.invFunOn_eq (exists_cdfK_eq hf (clamp01_mem u))
  rw [h, clamp01_of_mem hu]

theorem quantK_cdfK {x : ℝ} (hx : x ∈ Icc A B) : quantK f A B (cdfK f A x) = x :=
  (cdfK_strictMonoOn hf).injOn (quantK_mem hf _) hx (cdfK_quantK hf (cdfK_mem_Icc hf hx))

theorem quantK_zero : quantK f A B 0 = A := by
  simpa [cdfK_left] using quantK_cdfK hf hf.left_mem

theorem quantK_one : quantK f A B 1 = B := by
  simpa [cdfK_right hf] using quantK_cdfK hf hf.right_mem

theorem quantK_strictMonoOn : StrictMonoOn (quantK f A B) (Icc 0 1) := fun u hu v hv huv => by
  by_contra h
  have h' := (cdfK_strictMonoOn hf).monotoneOn (quantK_mem hf v) (quantK_mem hf u) (not_lt.1 h)
  rw [cdfK_quantK hf hu, cdfK_quantK hf hv] at h'
  exact absurd huv (not_lt.2 h')

theorem quantK_monotone : Monotone (quantK f A B) := fun u v huv => by
  rw [← quantK_clamp u, ← quantK_clamp v]
  exact (quantK_strictMonoOn hf).monotoneOn (clamp01_mem u) (clamp01_mem v) (clamp01_mono huv)

theorem measurable_quantK : Measurable (quantK f A B) := (quantK_monotone hf).measurable

theorem le_quantK_iff {x u : ℝ} (hx : x ∈ Icc A B) (hu : u ∈ Icc (0 : ℝ) 1) :
    x ≤ quantK f A B u ↔ cdfK f A x ≤ u := by
  rw [← (cdfK_strictMonoOn hf).le_iff_le hx (quantK_mem hf u), cdfK_quantK hf hu]

theorem quantK_image : quantK f A B '' Icc 0 1 = Icc A B := by
  refine Subset.antisymm ?_ fun x hx => ⟨cdfK f A x, cdfK_mem_Icc hf hx, quantK_cdfK hf hx⟩
  rintro _ ⟨u, -, rfl⟩
  exact quantK_mem hf u

theorem quantK_sub_le {u v : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) (hv : v ∈ Icc (0 : ℝ) 1) (huv : u ≤ v) :
    quantK f A B v - quantK f A B u ≤ (v - u) / fmin := by
  have h := cdfK_sub_ge hf (quantK_mem hf u) (quantK_mem hf v) (quantK_monotone hf huv)
  rw [cdfK_quantK hf hu, cdfK_quantK hf hv] at h
  rw [le_div_iff₀ hf.pos]
  linarith

theorem abs_quantK_sub_le {u v : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) (hv : v ∈ Icc (0 : ℝ) 1) :
    |quantK f A B u - quantK f A B v| ≤ |u - v| / fmin := by
  rcases le_total u v with h | h
  · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 (quantK_monotone hf h)), abs_sub_comm,
      abs_of_nonneg (sub_nonneg.2 h)]
    exact quantK_sub_le hf hu hv h
  · rw [abs_of_nonneg (sub_nonneg.2 (quantK_monotone hf h)), abs_of_nonneg (sub_nonneg.2 h)]
    exact quantK_sub_le hf hv hu h

theorem quantK_lipschitzOnWith :
    LipschitzOnWith (Real.toNNReal (1 / fmin)) (quantK f A B) (Icc 0 1) :=
  LipschitzOnWith.of_dist_le_mul fun u hu v hv => by
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (one_div_pos.2 hf.pos).le,
      one_div_mul_eq_div]
    exact abs_quantK_sub_le hf hu hv

theorem quantK_continuousOn : ContinuousOn (quantK f A B) (Icc 0 1) :=
  (quantK_lipschitzOnWith hf).continuousOn

theorem quantK_mem_Ioo {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) : quantK f A B u ∈ Ioo A B := by
  have hm := quantK_mem hf u
  have hc := cdfK_quantK hf (Ioo_subset_Icc_self hu)
  refine ⟨lt_of_le_of_ne hm.1 fun h => ?_, lt_of_le_of_ne hm.2 fun h => ?_⟩
  · rw [← h, cdfK_left] at hc
    exact hu.1.ne hc
  · rw [h, cdfK_right hf] at hc
    exact hu.2.ne' hc

end quant

/-! ### Differentiability of the quantile function -/

section derivative

variable (hf : DensityK f A B fmin fmax Lf)
include hf

theorem hasDerivAt_cdfK {x : ℝ} (hx : x ∈ Ioo A B) : HasDerivAt (cdfK f A) (f x) x := by
  have hcont : ContinuousOn f (Ioo A B) := hf.continuousOn.mono Ioo_subset_Icc_self
  exact intervalIntegral.integral_hasDerivAt_right
    (hf.intervalIntegrable hf.left_mem (Ioo_subset_Icc_self hx))
    (hcont.stronglyMeasurableAtFilter isOpen_Ioo x hx)
    (hcont.continuousAt (Ioo_mem_nhds hx.1 hx.2))

/-- One-sided derivatives of `cdfK` at the endpoints are included. -/
theorem hasDerivWithinAt_cdfK {x : ℝ} (hx : x ∈ Icc A B) :
    HasDerivWithinAt (cdfK f A) (f x) (Icc A B) x := by
  have : Fact (x ∈ Icc A B) := ⟨hx⟩
  exact intervalIntegral.integral_hasDerivWithinAt_right (hf.intervalIntegrable hf.left_mem hx)
    (hf.continuousOn.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc x)
    (hf.continuousOn x hx)

/-- `Q' = 1 / f ∘ Q` on the open interval `(0, 1)`. -/
theorem hasDerivAt_quantK {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (quantK f A B) (1 / f (quantK f A B u)) u := by
  have hQ := quantK_mem_Ioo hf hu
  have hnhds : Icc (0 : ℝ) 1 ∈ 𝓝 u := Icc_mem_nhds hu.1 hu.2
  rw [one_div]
  exact HasDerivAt.of_local_left_inverse ((quantK_continuousOn hf).continuousAt hnhds)
    (hasDerivAt_cdfK hf hQ) (hf.f_pos (Ioo_subset_Icc_self hQ)).ne'
    (Filter.mem_of_superset hnhds fun v hv => cdfK_quantK hf hv)

/-- `Q' = 1 / f ∘ Q` on `[0, 1]`, with one-sided derivatives at the endpoints. -/
theorem hasDerivWithinAt_quantK {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    HasDerivWithinAt (quantK f A B) (1 / f (quantK f A B u)) (Icc 0 1) u := by
  have hQ := quantK_mem hf u
  have hne : f (quantK f A B u) ≠ 0 := (hf.f_pos hQ).ne'
  have hg : Tendsto (quantK f A B) (𝓝[Icc 0 1] u) (𝓝[Icc A B] (quantK f A B u)) :=
    (quantK_continuousOn hf u hu).tendsto_nhdsWithin fun v _ => quantK_mem hf v
  have hcdf : HasFDerivWithinAt (cdfK f A)
      (ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 _ hne) : ℝ →L[ℝ] ℝ) (Icc A B)
      (quantK f A B u) :=
    hasDerivWithinAt_cdfK hf hQ
  rw [one_div]
  exact hcdf.of_local_left_inverse hg hu (eventually_nhdsWithin_of_forall fun v hv =>
    cdfK_quantK hf hv)

theorem differentiableOn_quantK : DifferentiableOn ℝ (quantK f A B) (Icc 0 1) :=
  fun _ hu => (hasDerivWithinAt_quantK hf hu).differentiableWithinAt

theorem deriv_quantK {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    deriv (quantK f A B) u = 1 / f (quantK f A B u) :=
  (hasDerivAt_quantK hf hu).deriv

theorem derivWithin_quantK {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    derivWithin (quantK f A B) (Icc 0 1) u = 1 / f (quantK f A B u) :=
  (hasDerivWithinAt_quantK hf hu).derivWithin (uniqueDiffOn_Icc zero_lt_one u hu)

theorem inv_f_quantK_mem_Icc (u : ℝ) : 1 / f (quantK f A B u) ∈ Icc (1 / fmax) (1 / fmin) := by
  have hx := quantK_mem hf u
  exact ⟨one_div_le_one_div_of_le (hf.f_pos hx) (hf.upper _ hx),
    one_div_le_one_div_of_le hf.pos (hf.lower _ hx)⟩

/-- `1 / f₊ ≤ Q' ≤ 1 / f₋` on `(0, 1)`. -/
theorem deriv_quantK_mem_Icc {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    deriv (quantK f A B) u ∈ Icc (1 / fmax) (1 / fmin) := by
  rw [deriv_quantK hf hu]
  exact inv_f_quantK_mem_Icc hf u

/-- `1 / f₊ ≤ Q' ≤ 1 / f₋` on `[0, 1]` (one-sided at the endpoints). -/
theorem derivWithin_quantK_mem_Icc {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    derivWithin (quantK f A B) (Icc 0 1) u ∈ Icc (1 / fmax) (1 / fmin) := by
  rw [derivWithin_quantK hf hu]
  exact inv_f_quantK_mem_Icc hf u

/-- `u ↦ 1 / f (Q u)` is Lipschitz on `[0, 1]` with constant `Lf / f₋ ^ 3`. -/
theorem abs_inv_f_quantK_sub_le {u v : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) (hv : v ∈ Icc (0 : ℝ) 1) :
    |1 / f (quantK f A B u) - 1 / f (quantK f A B v)| ≤ Lf / fmin ^ 3 * |u - v| := by
  have hx := quantK_mem hf u
  have hy := quantK_mem hf v
  have hfx := hf.f_pos hx
  have hfy := hf.f_pos hy
  have hxy : 0 < f (quantK f A B u) * f (quantK f A B v) := mul_pos hfx hfy
  have hprod : fmin * fmin ≤ f (quantK f A B u) * f (quantK f A B v) :=
    mul_le_mul (hf.lower _ hx) (hf.lower _ hy) hf.pos.le hfx.le
  have hK : 0 ≤ Lf / fmin ^ 3 * |u - v| :=
    mul_nonneg (div_nonneg hf.lf_nonneg (pow_nonneg hf.pos.le 3)) (abs_nonneg _)
  have hmin := hf.pos.ne'
  rw [div_sub_div _ _ hfx.ne' hfy.ne', one_mul, mul_one, abs_div, abs_of_pos hxy,
    div_le_iff₀ hxy]
  calc |f (quantK f A B v) - f (quantK f A B u)|
      ≤ Lf * |quantK f A B v - quantK f A B u| := hf.lip _ hy _ hx
    _ ≤ Lf * (|v - u| / fmin) :=
        mul_le_mul_of_nonneg_left (abs_quantK_sub_le hf hv hu) hf.lf_nonneg
    _ = Lf / fmin ^ 3 * |u - v| * (fmin * fmin) := by
        rw [abs_sub_comm v u]
        field_simp
    _ ≤ Lf / fmin ^ 3 * |u - v| * (f (quantK f A B u) * f (quantK f A B v)) :=
        mul_le_mul_of_nonneg_left hprod hK

theorem lipschitzOnWith_inv_f_quantK :
    LipschitzOnWith (Real.toNNReal (Lf / fmin ^ 3)) (fun u => 1 / f (quantK f A B u)) (Icc 0 1) :=
  LipschitzOnWith.of_dist_le_mul fun u hu v hv => by
    rw [Real.dist_eq, Real.dist_eq,
      Real.coe_toNNReal _ (div_nonneg hf.lf_nonneg (pow_nonneg hf.pos.le 3))]
    exact abs_inv_f_quantK_sub_le hf hu hv

/-- `Q'` is Lipschitz on `[0, 1]` with constant `Lf / f₋ ^ 3` (one-sided derivatives at the
endpoints). -/
theorem abs_derivWithin_quantK_sub_le {u v : ℝ} (hu : u ∈ Icc (0 : ℝ) 1)
    (hv : v ∈ Icc (0 : ℝ) 1) :
    |derivWithin (quantK f A B) (Icc 0 1) u - derivWithin (quantK f A B) (Icc 0 1) v| ≤
      Lf / fmin ^ 3 * |u - v| := by
  rw [derivWithin_quantK hf hu, derivWithin_quantK hf hv]
  exact abs_inv_f_quantK_sub_le hf hu hv

/-- `Q'` is Lipschitz on `(0, 1)` with constant `Lf / f₋ ^ 3`. -/
theorem abs_deriv_quantK_sub_le {u v : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (hv : v ∈ Ioo (0 : ℝ) 1) :
    |deriv (quantK f A B) u - deriv (quantK f A B) v| ≤ Lf / fmin ^ 3 * |u - v| := by
  rw [deriv_quantK hf hu, deriv_quantK hf hv]
  exact abs_inv_f_quantK_sub_le hf (Ioo_subset_Icc_self hu) (Ioo_subset_Icc_self hv)

end derivative

/-! ### The law of one sample and the probability integral transform -/

section pit

theorem densityLaw_apply (s : Set ℝ) :
    densityLaw f A B s = ∫⁻ x in s ∩ Icc A B, ENNReal.ofReal (f x) := by
  rw [densityLaw, withDensity_apply' _ s, Measure.restrict_restrict' measurableSet_Icc]

theorem densityLaw_absolutelyContinuous : densityLaw f A B ≪ volume.restrict (Icc A B) :=
  withDensity_absolutelyContinuous _ _

theorem ae_densityLaw_mem : ∀ᵐ x ∂(densityLaw f A B), x ∈ Icc A B :=
  densityLaw_absolutelyContinuous.ae_le (ae_restrict_mem measurableSet_Icc)

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

theorem ae_mem_Icc_of_hasLaw {X : Ω → ℝ} (hX : HasLaw X (densityLaw f A B) P) :
    ∀ᵐ ω ∂P, X ω ∈ Icc A B :=
  ae_of_ae_map hX.aemeasurable (hX.map_eq ▸ ae_densityLaw_mem)

variable (hf : DensityK f A B fmin fmax Lf)
include hf

theorem lintegral_Icc_left {x : ℝ} (hx : x ∈ Icc A B) :
    ∫⁻ t in Icc A x, ENNReal.ofReal (f t) = ENNReal.ofReal (cdfK f A x) := by
  have hint : IntegrableOn f (Icc A x) :=
    (hf.continuousOn.mono (Icc_subset_Icc le_rfl hx.2)).integrableOn_Icc
  rw [cdfK, intervalIntegral.integral_of_le hx.1, ← integral_Icc_eq_integral_Ioc,
    ofReal_integral_eq_lintegral_ofReal hint]
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact (hf.f_pos ⟨ht.1, ht.2.trans hx.2⟩).le

theorem densityLaw_Icc_left {x : ℝ} (hx : x ∈ Icc A B) :
    densityLaw f A B (Icc A x) = ENNReal.ofReal (cdfK f A x) := by
  rw [densityLaw_apply, inter_eq_left.2 (Icc_subset_Icc le_rfl hx.2), lintegral_Icc_left hf hx]

theorem isProbabilityMeasure_densityLaw : IsProbabilityMeasure (densityLaw f A B) := by
  constructor
  rw [densityLaw_apply, univ_inter, lintegral_Icc_left hf hf.right_mem, cdfK_right hf,
    ENNReal.ofReal_one]

theorem aemeasurable_cdfK : AEMeasurable (cdfK f A) (densityLaw f A B) :=
  ((cdfK_continuousOn hf).aemeasurable measurableSet_Icc).mono_ac densityLaw_absolutelyContinuous

/-- **Probability integral transform.**  Under the Model K law, `cdfK f A` is uniform on
`[0, 1]`. -/
theorem hasLaw_cdfK : HasLaw (cdfK f A) (volume.restrict (Icc 0 1)) (densityLaw f A B) where
  aemeasurable := aemeasurable_cdfK hf
  map_eq := by
    have := isProbabilityMeasure_densityLaw hf
    refine Measure.ext_of_Iic _ _ fun a => ?_
    rw [Measure.map_apply_of_aemeasurable (aemeasurable_cdfK hf) measurableSet_Iic,
      densityLaw_apply, Measure.restrict_apply measurableSet_Iic]
    rcases lt_or_ge a 0 with ha | ha
    · have h1 : cdfK f A ⁻¹' Iic a ∩ Icc A B = ∅ := by
        refine eq_empty_of_forall_notMem fun x hx => ?_
        have := (cdfK_mem_Icc hf hx.2).1
        have : cdfK f A x ≤ a := hx.1
        linarith
      have h2 : Iic a ∩ Icc (0 : ℝ) 1 = ∅ := by
        refine eq_empty_of_forall_notMem fun x hx => ?_
        have := hx.2.1
        have := mem_Iic.1 hx.1
        linarith
      rw [h1, h2, Measure.restrict_empty, lintegral_zero_measure, measure_empty]
    rcases le_or_gt a 1 with ha1 | ha1
    · have hq := quantK_mem hf a
      have h1 : cdfK f A ⁻¹' Iic a ∩ Icc A B = Icc A (quantK f A B a) := by
        ext x
        constructor
        · rintro ⟨hx, hxI⟩
          exact ⟨hxI.1, (le_quantK_iff hf hxI ⟨ha, ha1⟩).2 hx⟩
        · intro hx
          have hxI : x ∈ Icc A B := ⟨hx.1, hx.2.trans hq.2⟩
          exact ⟨(le_quantK_iff hf hxI ⟨ha, ha1⟩).1 hx.2, hxI⟩
      have h2 : Iic a ∩ Icc (0 : ℝ) 1 = Icc 0 a := by
        ext x
        simp only [mem_inter_iff, mem_Iic, mem_Icc]
        constructor
        · rintro ⟨h1, h2, -⟩
          exact ⟨h2, h1⟩
        · rintro ⟨h1, h2⟩
          exact ⟨h2, h1, h2.trans ha1⟩
      rw [h1, h2, lintegral_Icc_left hf hq, cdfK_quantK hf ⟨ha, ha1⟩, Real.volume_Icc, sub_zero]
    · have h1 : cdfK f A ⁻¹' Iic a ∩ Icc A B = Icc A B :=
        inter_eq_right.2 fun x hx => mem_Iic.2 ((cdfK_mem_Icc hf hx).2.trans ha1.le)
      have h2 : Iic a ∩ Icc (0 : ℝ) 1 = Icc 0 1 :=
        inter_eq_right.2 fun x hx => mem_Iic.2 (hx.2.trans ha1.le)
      rw [h1, h2, lintegral_Icc_left hf hf.right_mem, cdfK_right hf, Real.volume_Icc, sub_zero]

/-- **Inverse transform sampling.**  `quantK f A B` carries the uniform law on `[0, 1]` to the
Model K law. -/
theorem hasLaw_quantK : HasLaw (quantK f A B) (densityLaw f A B) (volume.restrict (Icc 0 1)) where
  aemeasurable := (measurable_quantK hf).aemeasurable
  map_eq := by
    rw [← (hasLaw_cdfK hf).map_eq, AEMeasurable.map_map_of_aemeasurable
      (measurable_quantK hf).aemeasurable (aemeasurable_cdfK hf),
      Measure.map_congr (f := quantK f A B ∘ cdfK f A) (g := id)
        (ae_densityLaw_mem.mono fun x hx => quantK_cdfK hf hx),
      Measure.map_id]

/-- `U = cdfK f A ∘ X` is uniform on `[0, 1]` when `X` has the Model K law. -/
theorem hasLaw_cdfK_comp {X : Ω → ℝ} (hX : HasLaw X (densityLaw f A B) P) :
    HasLaw (fun ω => cdfK f A (X ω)) (volume.restrict (Icc 0 1)) P :=
  (hasLaw_cdfK hf).comp hX

/-- `X = quantK (cdfK X)` almost surely. -/
theorem quantK_cdfK_ae_eq {X : Ω → ℝ} (hX : HasLaw X (densityLaw f A B) P) :
    (fun ω => quantK f A B (cdfK f A (X ω))) =ᵐ[P] X :=
  (ae_mem_Icc_of_hasLaw hX).mono fun _ hω => quantK_cdfK hf hω

/-- Independence is preserved by the probability integral transform. -/
theorem iIndepFun_cdfK {ι : Type*} {X : ι → Ω → ℝ} (hX : ∀ i, HasLaw (X i) (densityLaw f A B) P)
    (hind : iIndepFun X P) : iIndepFun (fun i ω => cdfK f A (X i ω)) P :=
  hind.comp₀ (fun _ => cdfK f A) (fun i => (hX i).aemeasurable) fun i => by
    rw [(hX i).map_eq]
    exact aemeasurable_cdfK hf

end pit

/-! ### Sorting and the Rényi representation of the sorted sample -/

namespace Renyi

/-- Sorting commutes with a map that is monotone on a set containing all coordinates. -/
theorem sortVec_comp_of_monotoneOn {n : ℕ} {g : ℝ → ℝ} {s : Set ℝ} (hg : MonotoneOn g s)
    {u : Fin n → ℝ} (hu : ∀ i, u i ∈ s) : sortVec (g ∘ u) = g ∘ sortVec u :=
  sortVec_eq_of_monotone (u := g ∘ u) (σ := Tuple.sort u) fun _ _ hij =>
    hg (hu _) (hu _) (monotone_sortVec u hij)

/-- Sorting commutes with a map that is strictly monotone on a set containing all coordinates. -/
theorem sortVec_comp_of_strictMonoOn {n : ℕ} {g : ℝ → ℝ} {s : Set ℝ} (hg : StrictMonoOn g s)
    {u : Fin n → ℝ} (hu : ∀ i, u i ∈ s) : sortVec (g ∘ u) = g ∘ sortVec u :=
  sortVec_comp_of_monotoneOn hg.monotoneOn hu

/-- Sorting commutes with a monotone map. -/
theorem sortVec_comp_of_monotone {n : ℕ} {g : ℝ → ℝ} (hg : Monotone g) (u : Fin n → ℝ) :
    sortVec (g ∘ u) = g ∘ sortVec u :=
  sortVec_comp_of_monotoneOn (hg.monotoneOn univ) fun _ => mem_univ _

end Renyi

section sorted

variable {n : ℕ} {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω}
  {P' : Measure Ω'}

variable (hf : DensityK f A B fmin fmax Lf)
include hf

theorem measurable_comp_quantK : Measurable fun v : Fin n → ℝ => quantK f A B ∘ v :=
  measurable_pi_lambda _ fun i => (measurable_quantK hf).comp (measurable_pi_apply i)

/-- The sorted Model K sample is `quantK` applied to the sorted uniforms `cdfK f A ∘ X`. -/
theorem sortVec_ae_eq_quantK_sortVec {X : Fin n → Ω → ℝ}
    (hX : ∀ i, HasLaw (X i) (densityLaw f A B) P) :
    (fun ω => Renyi.sortVec fun i => X i ω) =ᵐ[P]
      fun ω => quantK f A B ∘ Renyi.sortVec fun i => cdfK f A (X i ω) := by
  have h : ∀ᵐ ω ∂P, ∀ i, X i ω ∈ Icc A B := ae_all_iff.2 fun i => ae_mem_Icc_of_hasLaw (hX i)
  filter_upwards [h] with ω hω
  rw [← Renyi.sortVec_comp_of_monotone (quantK_monotone hf)]
  congr 1
  funext i
  exact (quantK_cdfK hf (hω i)).symm

/-- **Rényi representation of Model K.**  The sorted sample of `n` iid draws from the Model K
law has the law of `quantK f A B ∘ (Γ 1 / Γ (n+1), …, Γ n / Γ (n+1))`, where `Γ` are the partial
sums of `n + 1` iid `Exp(1)` variables. -/
theorem identDistrib_sortVec_quantK_gammaRatio {X : Fin n → Ω → ℝ}
    (hX : ∀ i, HasLaw (X i) (densityLaw f A B) P) (hind : iIndepFun X P)
    {E : Fin (n + 1) → Ω' → ℝ} (hE : ∀ i, HasLaw (E i) (expMeasure 1) P')
    (hEind : iIndepFun E P') :
    IdentDistrib (fun ω => Renyi.sortVec (fun i => X i ω))
      (fun ω' => quantK f A B ∘ Renyi.gammaRatio (fun i => E i ω')) P P' := by
  have h1 := Renyi.identDistrib_sortVec_gammaRatio (fun i => hasLaw_cdfK_comp hf (hX i))
    (iIndepFun_cdfK hf hX hind) hE hEind
  have h2 := h1.comp (measurable_comp_quantK hf)
  have h3 := IdentDistrib.of_ae_eq
    (Renyi.measurable_sortVec.comp_aemeasurable
      (aemeasurable_pi_lambda _ fun i => (hX i).aemeasurable))
    (sortVec_ae_eq_quantK_sortVec hf hX)
  exact h3.trans h2

end sorted

/-! ### The constant density -/

section uniform

variable {n : ℕ} {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω}
  {P' : Measure Ω'}

/-- The constant density `1 / (B - A)` satisfies the Model K hypotheses. -/
theorem densityK_const (hAB : A < B) (hc : ∀ x ∈ Icc A B, f x = 1 / (B - A)) :
    DensityK f A B (1 / (B - A)) (1 / (B - A)) 0 where
  lt := hAB
  pos := one_div_pos.2 (sub_pos.2 hAB)
  lower x hx := (hc x hx).ge
  upper x hx := (hc x hx).le
  lip x hx y hy := by rw [hc x hx, hc y hy, sub_self, abs_zero, zero_mul]
  integral_one := by
    rw [intervalIntegral.integral_congr (g := fun _ => 1 / (B - A))
      fun x hx => hc x (by rwa [uIcc_of_le hAB.le] at hx), intervalIntegral.integral_const,
      smul_eq_mul]
    field_simp [(sub_pos.2 hAB).ne']

theorem cdfK_const (hAB : A < B) (hc : ∀ x ∈ Icc A B, f x = 1 / (B - A)) {x : ℝ}
    (hx : x ∈ Icc A B) : cdfK f A x = (x - A) / (B - A) := by
  unfold cdfK
  rw [intervalIntegral.integral_congr (g := fun _ => 1 / (B - A)) fun t ht => hc t ?_,
    intervalIntegral.integral_const, smul_eq_mul]
  · field_simp [(sub_pos.2 hAB).ne']
  · rw [uIcc_of_le hx.1] at ht
    exact ⟨ht.1, ht.2.trans hx.2⟩

/-- For the constant density, the quantile function is affine. -/
theorem quantK_const (hAB : A < B) (hc : ∀ x ∈ Icc A B, f x = 1 / (B - A)) {u : ℝ}
    (hu : u ∈ Icc (0 : ℝ) 1) : quantK f A B u = A + (B - A) * u := by
  have hBA : 0 < B - A := sub_pos.2 hAB
  have hx : A + (B - A) * u ∈ Icc A B := by
    have h1 : 0 ≤ (B - A) * u := mul_nonneg hBA.le hu.1
    have h2 : (B - A) * u ≤ B - A := mul_le_of_le_one_right hBA.le hu.2
    constructor <;> linarith
  have h := quantK_cdfK (densityK_const hAB hc) hx
  rwa [cdfK_const hAB hc hx, show (A + (B - A) * u - A) / (B - A) = u by
    rw [add_sub_cancel_left, mul_div_cancel_left₀ _ hBA.ne']] at h

/-- **Constant density.**  The sorted sample of `n` iid uniform `[A, B]` draws has the law of
`A + (B - A) · Γ (i+1) / Γ (n+1)`. -/
theorem identDistrib_sortVec_uniformK_gammaRatio (hAB : A < B)
    (hc : ∀ x ∈ Icc A B, f x = 1 / (B - A)) {X : Fin n → Ω → ℝ}
    (hX : ∀ i, HasLaw (X i) (densityLaw f A B) P) (hind : iIndepFun X P)
    {E : Fin (n + 1) → Ω' → ℝ} (hE : ∀ i, HasLaw (E i) (expMeasure 1) P')
    (hEind : iIndepFun E P') :
    IdentDistrib (fun ω => Renyi.sortVec (fun i => X i ω))
      (fun ω' i => A + (B - A) * Renyi.gammaRatio (fun j => E j ω') i) P P' := by
  have hf := densityK_const hAB hc
  have hlaw := Renyi.hasLaw_gammaRatio_exp hE hEind
  refine (identDistrib_sortVec_quantK_gammaRatio hf hX hind hE hEind).trans
    (IdentDistrib.of_ae_eq ((measurable_comp_quantK hf).comp_aemeasurable hlaw.aemeasurable) ?_)
  have hsimp : ∀ᵐ v ∂((n ! : ℝ≥0∞) • volume.restrict (Renyi.simplex n)), v ∈ Renyi.simplex n :=
    Measure.ae_smul_measure (ae_restrict_mem Renyi.measurableSet_simplex) _
  filter_upwards [ae_of_ae_map hlaw.aemeasurable (hlaw.map_eq ▸ hsimp)] with ω hω
  funext i
  exact quantK_const hAB hc ⟨(hω.2.1 i).le, (hω.2.2 i).le⟩

/-- **Constant density, affine form.**  The sorted sample of `n` iid uniform `[A, B]` draws has
the law of `A + ((B - A) / Γ (n+1)) · Γ (i+1)`: a positive affine image, with random factor
`(B - A) / Γ (n+1)`, of the partial sums `Γ (i+1) = E 0 + ⋯ + E i` of iid `Exp(1)` variables. -/
theorem identDistrib_sortVec_uniformK (hAB : A < B) (hc : ∀ x ∈ Icc A B, f x = 1 / (B - A))
    {X : Fin n → Ω → ℝ} (hX : ∀ i, HasLaw (X i) (densityLaw f A B) P) (hind : iIndepFun X P)
    {E : Fin (n + 1) → Ω' → ℝ} (hE : ∀ i, HasLaw (E i) (expMeasure 1) P')
    (hEind : iIndepFun E P') :
    IdentDistrib (fun ω => Renyi.sortVec (fun i => X i ω))
      (fun ω' (i : Fin n) => A + (B - A) / Renyi.gammaSum (fun j => E j ω') (n + 1) *
        Renyi.gammaSum (fun j => E j ω') ((i : ℕ) + 1)) P P' := by
  have h := identDistrib_sortVec_uniformK_gammaRatio hAB hc hX hind hE hEind
  convert h using 3 with ω' i
  rw [Renyi.gammaRatio, mul_div_assoc', div_mul_eq_mul_div]

end uniform

end PGM
