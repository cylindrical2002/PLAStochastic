import PLAStochastic.Swing.ConstantEvaluation.Fluctuation.LadderDuality

/-! # Exponential tilting of the drift (roadmap 1.4, step 1)

For a standard Gaussian vector `v ∈ ℝⁿ` and a drift `d ∈ ℝⁿ`,

  `𝔼 G(v + d) = 𝔼 [G(w) exp(⟨d, w⟩ - |d|²/2)]`   (Cameron–Martin, finite form).

Applied to the drift `(0, a, …, a)` acting on `(X_0, X_1, …, X_m)`: on the event that the
drifted walk `S'_j = ∑_{k<j} (X_{k+1} + a)` has a weak descending record at `m` (so `S'_m ≤ 0`,
i.e. `⟨𝟙, w⟩ ≤ 0` for the drifted coordinates), the tilt weight `exp(a⟨𝟙,w⟩ - m a²/2)` is
*antitone* in `a ≥ 0`.  Hence

  `∫_{E_m(c)} g(X_0, S'^{(c)}_m) ≤ ∫_{E_m(a)} g(X_0, S'^{(a)}_m)`   for `0 ≤ a ≤ c`,

which is the drift-monotonicity of the descending-ladder occupation measure — the input to the
stochastic monotonicity of `Law(M_a)/a` that replaces the paper's convolution-exponential
argument.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
namespace SwingRepair
namespace Fluctuation

/-! ### One-dimensional tilt -/

/-- `φ(w - d)/φ(w) = exp(d w - d²/2)`. -/
def tiltDensity (d w : ℝ) : ℝ≥0∞ := ENNReal.ofReal (Real.exp (d * w - d ^ 2 / 2))

theorem measurable_tiltDensity (d : ℝ) : Measurable (tiltDensity d) := by
  unfold tiltDensity; fun_prop

theorem gaussianPDF_eq_mul_tilt (d w : ℝ) :
    gaussianPDF d 1 w = gaussianPDF 0 1 w * tiltDensity d w := by
  unfold gaussianPDF tiltDensity
  rw [← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _)]
  congr 1
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  conv_rhs => rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

theorem gaussianReal_eq_withDensity_tilt (d : ℝ) :
    gaussianReal d 1 = (gaussianReal 0 1).withDensity (tiltDensity d) := by
  rw [gaussianReal_of_var_ne_zero _ one_ne_zero, gaussianReal_of_var_ne_zero _ one_ne_zero,
    ← withDensity_mul _ (measurable_gaussianPDF 0 1) (measurable_tiltDensity d)]
  congr 1
  funext w
  exact gaussianPDF_eq_mul_tilt d w

/-! ### Products over `Measure.pi` -/

theorem lintegral_pi_prod {ι : Type*} [Fintype ι] {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
    (μ : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (μ i)]
    (f : ∀ i, α i → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ w, ∏ i, f i (w i) ∂Measure.pi μ = ∏ i, ∫⁻ x, f i x ∂μ i := by
  classical
  have hind : iIndepFun (fun i (w : ∀ i, α i) => f i (w i)) (Measure.pi μ) :=
    iIndepFun_pi fun i => (hf i).aemeasurable
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ _ hind
    (fun i => (hf i).comp (measurable_pi_apply i))]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← lintegral_map (hf i) (measurable_pi_apply i), Measure.pi_map_eval,
    Finset.prod_eq_one (fun j _ => measure_univ), one_smul]

/-- The product of drifted unit Gaussians is the tilt of the standard product. -/
theorem pi_gaussian_drift_eq_withDensity {n : ℕ} (d : Fin n → ℝ) :
    Measure.pi (fun i : Fin n => gaussianReal (d i) 1) =
      (Measure.pi fun _ : Fin n => gaussianReal 0 1).withDensity
        (fun w => ∏ i, tiltDensity (d i) (w i)) := by
  refine Measure.pi_eq fun s hs => ?_
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs),
    ← lintegral_indicator (MeasurableSet.univ_pi hs)]
  have hpt : ∀ w : Fin n → ℝ,
      (univ.pi s).indicator (fun w => ∏ i, tiltDensity (d i) (w i)) w =
        ∏ i, (s i).indicator (tiltDensity (d i)) (w i) := by
    intro w
    by_cases hw : w ∈ univ.pi s
    · rw [indicator_of_mem hw]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [indicator_of_mem (mem_univ_pi.mp hw i)]
    · rw [indicator_of_notMem hw]
      rw [mem_univ_pi] at hw
      push Not at hw
      obtain ⟨i, hi⟩ := hw
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (by rw [indicator_of_notMem hi])).symm
  simp_rw [hpt]
  rw [lintegral_pi_prod _ _ (fun i => (measurable_tiltDensity (d i)).indicator (hs i))]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [lintegral_indicator (hs i), gaussianReal_eq_withDensity_tilt (d i), withDensity_apply _ (hs i)]

/-- **Cameron–Martin (finite form).** -/
theorem lintegral_pi_gaussian_add {n : ℕ} (d : Fin n → ℝ) {G : (Fin n → ℝ) → ℝ≥0∞}
    (hG : Measurable G) :
    ∫⁻ v, G (fun i => v i + d i) ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1) =
      ∫⁻ w, G w * ENNReal.ofReal (Real.exp (∑ i, (d i * w i - d i ^ 2 / 2)))
        ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1) := by
  have hmeas : Measurable fun v : Fin n → ℝ => fun i => v i + d i :=
    measurable_pi_lambda _ fun i =>
      ((measurable_pi_apply i : Measurable fun v : Fin n → ℝ => v i).add_const (d i))
  have : ∀ i : Fin n, SigmaFinite ((gaussianReal 0 1).map (fun x : ℝ => x + d i)) := fun i => by
    rw [gaussianReal_map_add_const]; infer_instance
  have hmap := Measure.pi_map_pi (μ := fun _ : Fin n => gaussianReal 0 1)
    (f := fun i (x : ℝ) => x + d i) (fun i => (measurable_add_const (d i)).aemeasurable)
  rw [← lintegral_map hG hmeas, hmap]
  simp_rw [gaussianReal_map_add_const, zero_add]
  have hdens : Measurable fun w : Fin n → ℝ => ∏ i, tiltDensity (d i) (w i) :=
    Finset.measurable_prod _ fun i _ =>
      (measurable_tiltDensity (d i)).comp (measurable_pi_apply i : Measurable fun w : Fin n → ℝ => w i)
  rw [pi_gaussian_drift_eq_withDensity, lintegral_withDensity_eq_lintegral_mul _ hdens hG]
  refine lintegral_congr fun w => ?_
  simp only [Pi.mul_apply]
  rw [mul_comm]
  congr 1
  unfold tiltDensity
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le), Real.exp_sum]

/-! ### The drift `(0, a, …, a)` and its antitone tilt -/

/-- The drift vector `(0, a, …, a)` on `Fin (m + 1)`. -/
def shiftDrift (a : ℝ) (m : ℕ) : Fin (m + 1) → ℝ := Fin.cons 0 (fun _ => a)

@[simp] theorem shiftDrift_zero (a : ℝ) (m : ℕ) : shiftDrift a m 0 = 0 := by
  simp [shiftDrift]

@[simp] theorem shiftDrift_succ (a : ℝ) (m : ℕ) (j : Fin m) : shiftDrift a m j.succ = a := by
  simp [shiftDrift]

theorem sum_shiftDrift (a : ℝ) (m : ℕ) (w : Fin (m + 1) → ℝ) :
    ∑ i, (shiftDrift a m i * w i - shiftDrift a m i ^ 2 / 2) =
      a * ∑ j : Fin m, w j.succ - m * (a ^ 2 / 2) := by
  rw [Fin.sum_univ_succ]
  simp only [shiftDrift_zero, shiftDrift_succ, zero_mul, zero_pow two_ne_zero, zero_div, sub_zero,
    zero_add, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Finset.mul_sum]

/-- Under the support condition `∑_{j} w_{j+1} ≤ 0`, the drifted expectation is antitone in the
drift `a ≥ 0`. -/
theorem lintegral_pi_gaussian_shiftDrift_antitone {m : ℕ} {a c : ℝ} (ha : 0 ≤ a) (hac : a ≤ c)
    {G : (Fin (m + 1) → ℝ) → ℝ≥0∞} (hG : Measurable G)
    (hsupp : ∀ w, G w ≠ 0 → ∑ j : Fin m, w j.succ ≤ 0) :
    ∫⁻ v, G (fun i => v i + shiftDrift c m i)
        ∂(Measure.pi fun _ : Fin (m + 1) => gaussianReal 0 1) ≤
      ∫⁻ v, G (fun i => v i + shiftDrift a m i)
        ∂(Measure.pi fun _ : Fin (m + 1) => gaussianReal 0 1) := by
  rw [lintegral_pi_gaussian_add _ hG, lintegral_pi_gaussian_add _ hG]
  refine lintegral_mono fun w => ?_
  by_cases hw : G w = 0
  · simp [hw]
  · refine mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_))
    rw [sum_shiftDrift, sum_shiftDrift]
    have hS := hsupp w hw
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    nlinarith [mul_nonneg (sub_nonneg.mpr hac) (neg_nonneg.mpr hS),
      mul_nonneg (mul_nonneg hm (sub_nonneg.mpr hac)) (add_nonneg ha (ha.trans hac))]

/-! ### Transfer to the walk `S'` -/

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℝ} {μ : Measure Ω}

/-- The tail partial sums of a vector `w ∈ ℝ^{m+1}`: `∑_{i < j} w_{i+1}`. -/
def tailWalk (m : ℕ) (w : Fin (m + 1) → ℝ) (j : ℕ) : ℝ :=
  ∑ i : Fin m, if (i : ℕ) < j then w i.succ else 0

theorem tailWalk_measurable (m j : ℕ) : Measurable fun w : Fin (m + 1) → ℝ => tailWalk m w j := by
  unfold tailWalk
  refine Finset.measurable_sum _ fun i _ => ?_
  split_ifs
  · exact (measurable_pi_apply i.succ : Measurable fun w : Fin (m + 1) → ℝ => w i.succ)
  · exact measurable_const

theorem tailWalk_self (m : ℕ) (w : Fin (m + 1) → ℝ) :
    tailWalk m w m = ∑ j : Fin m, w j.succ := by
  unfold tailWalk
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [if_pos i.isLt]

theorem tailWalk_zero (m : ℕ) (w : Fin (m + 1) → ℝ) : tailWalk m w 0 = 0 := by
  unfold tailWalk
  simp

omit [MeasurableSpace Ω] in
/-- On the drifted sample vector, `tailWalk` is the shifted walk `S'_j`. -/
theorem tailWalk_sample (a : ℝ) (m : ℕ) (ω : Ω) {j : ℕ} (hj : j ≤ m) :
    tailWalk m (fun i : Fin (m + 1) => X i ω + shiftDrift a m i) j = shiftWalk X a j ω := by
  unfold tailWalk shiftWalk gaussianDriftWalk cumulativeSamples
  simp only [shiftDrift_succ, Fin.val_succ, zero_add]
  have h1 : (∑ i : Fin m, if (i : ℕ) < j then X ((i : ℕ) + 1) ω + a else 0) =
      ∑ i ∈ Finset.range m, if i < j then X (i + 1) ω + a else 0 := by
    rw [Finset.sum_fin_eq_sum_range]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [dif_pos (Finset.mem_range.mp hi)]
  rw [h1, ← Finset.sum_range_add_sum_Ico _ hj, Finset.sum_congr rfl
    (fun i hi => if_pos (Finset.mem_range.mp hi)),
    Finset.sum_eq_zero (fun i hi => if_neg (by have := (Finset.mem_Ico.mp hi).1; omega)),
    add_zero, Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have : ∀ i, X (i + 1) ω = X (1 + i) ω := fun i => by rw [add_comm]
  simp only [this]
  ring

/-- The functional realising `1_{E_m} g(X_0, S'_m)` on the drifted sample vector. -/
def descentFunctional (m : ℕ) (g : ℝ → ℝ → ℝ≥0∞) (w : Fin (m + 1) → ℝ) : ℝ≥0∞ :=
  {w : Fin (m + 1) → ℝ | ∀ j < m, tailWalk m w m ≤ tailWalk m w j}.indicator
    (fun w => g (w 0) (tailWalk m w m)) w

theorem descentFunctional_measurable (m : ℕ) {g : ℝ → ℝ → ℝ≥0∞}
    (hg : Measurable (Function.uncurry g)) : Measurable (descentFunctional m g) := by
  unfold descentFunctional
  refine Measurable.indicator ?_ ?_
  · exact hg.comp ((measurable_pi_apply (0 : Fin (m + 1))).prodMk (tailWalk_measurable m m))
  · have : {w : Fin (m + 1) → ℝ | ∀ j < m, tailWalk m w m ≤ tailWalk m w j} =
        ⋂ j, ⋂ (_ : j < m), {w | tailWalk m w m ≤ tailWalk m w j} := by
      ext w; simp
    rw [this]
    exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
      measurableSet_le (tailWalk_measurable m m) (tailWalk_measurable m j)

theorem descentFunctional_support (m : ℕ) (g : ℝ → ℝ → ℝ≥0∞) (w : Fin (m + 1) → ℝ)
    (hw : descentFunctional m g w ≠ 0) : ∑ j : Fin m, w j.succ ≤ 0 := by
  rw [← tailWalk_self]
  unfold descentFunctional at hw
  by_cases hmem : w ∈ {w : Fin (m + 1) → ℝ | ∀ j < m, tailWalk m w m ≤ tailWalk m w j}
  · rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm; rw [tailWalk_zero]
    · have := hmem 0 hm
      rwa [tailWalk_zero] at this
  · exact absurd (indicator_of_notMem hmem _) hw

omit [MeasurableSpace Ω] in
theorem descentFunctional_sample (a : ℝ) (m : ℕ) (g : ℝ → ℝ → ℝ≥0∞) (ω : Ω) :
    descentFunctional m g (fun i : Fin (m + 1) => X i ω + shiftDrift a m i) =
      (weakDescentSet X a m).indicator (fun ω => g (X 0 ω) (shiftWalk X a m ω)) ω := by
  unfold descentFunctional
  have hset : (fun i : Fin (m + 1) => X i ω + shiftDrift a m i) ∈
      {w : Fin (m + 1) → ℝ | ∀ j < m, tailWalk m w m ≤ tailWalk m w j} ↔ ω ∈ weakDescentSet X a m := by
    simp only [weakDescentSet, mem_ofPred_eq]
    constructor
    · intro h j hj
      have := h j hj
      rwa [tailWalk_sample a m ω le_rfl, tailWalk_sample a m ω hj.le] at this
    · intro h j hj
      rw [tailWalk_sample a m ω le_rfl, tailWalk_sample a m ω hj.le]
      exact h j hj
  by_cases hmem : ω ∈ weakDescentSet X a m
  · rw [indicator_of_mem (hset.mpr hmem), indicator_of_mem hmem, tailWalk_sample a m ω le_rfl]
    simp
  · rw [indicator_of_notMem (fun h => hmem (hset.mp h)), indicator_of_notMem hmem]

/-- **Drift monotonicity of the descending-ladder occupation integrals.** -/
theorem lintegral_weakDescent_antitone (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {a c : ℝ} (ha : 0 ≤ a) (hac : a ≤ c) (m : ℕ)
    {g : ℝ → ℝ → ℝ≥0∞} (hg : Measurable (Function.uncurry g)) :
    ∫⁻ ω, (weakDescentSet X c m).indicator (fun ω => g (X 0 ω) (shiftWalk X c m ω)) ω ∂μ ≤
      ∫⁻ ω, (weakDescentSet X a m).indicator (fun ω => g (X 0 ω) (shiftWalk X a m ω)) ω ∂μ := by
  have hprob : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hvec := map_vector_eq_pi hX hi hG (m := m + 1) (fun i => (i : ℕ)) Fin.val_injective
  have hV : Measurable fun ω (i : Fin (m + 1)) => X i ω := measurable_pi_lambda _ fun i => hX i
  have hGm := descentFunctional_measurable m hg
  have key : ∀ b : ℝ,
      ∫⁻ ω, (weakDescentSet X b m).indicator (fun ω => g (X 0 ω) (shiftWalk X b m ω)) ω ∂μ =
        ∫⁻ v, descentFunctional m g (fun i => v i + shiftDrift b m i)
          ∂(Measure.pi fun _ : Fin (m + 1) => gaussianReal 0 1) := by
    intro b
    simp_rw [← descentFunctional_sample (X := X) b m g]
    have hm : Measurable fun v : Fin (m + 1) → ℝ => fun i => v i + shiftDrift b m i :=
      measurable_pi_lambda _ fun i =>
        ((measurable_pi_apply i : Measurable fun v : Fin (m + 1) → ℝ => v i).add_const _)
    have hm' : Measurable fun v : Fin (m + 1) → ℝ =>
        descentFunctional m g (fun i => v i + shiftDrift b m i) := hGm.comp hm
    rw [← hvec, lintegral_map hm' hV]
  rw [key c, key a]
  exact lintegral_pi_gaussian_shiftDrift_antitone ha hac hGm (descentFunctional_support m g)

end Fluctuation
end SwingRepair
