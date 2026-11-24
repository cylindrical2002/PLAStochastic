import PLAStochastic.ForMathlib.Probability.Kernel.Invariant.WeakPropagation

/-! # The mean passage for a weakly convergent family of margin laws

`eq:transient-subsequentialmeans`, abstract form.  The normalised segment means
are integrals `∫ f_i dρ_i` of nonnegative functions of linear growth against
laws `ρ_i ⇒ ρ`.  "To justify averaging, use compact-uniform conditional
convergence on each side of zero, the vanishing limiting mass of a shrinking
zero neighbourhood, and the bound `g_E(r)/(E log E) ≤ C(1 + r_+)`.  Any moment
of order greater than one controls the remote positive tail; tightness controls
the negative tail."

Concretely the line is cut into three pieces by two Lipschitz cutoffs:

* the far region `|x| > C`, where a uniform second moment and the linear growth
  bound make both `∫ f_i dρ_i` and `∫ f dρ` small (Markov);
* the zero neighbourhood `|x| < 2δ`, where the limit law has small mass because
  it has no atom at `0`, and hence so do the `ρ_i` eventually (weak convergence
  against a continuous bump);
* the annulus `δ ≤ |x| ≤ C + 1`, where `f_i → f` uniformly, and where `f` times
  the annulus window is a bounded continuous function, so weak convergence
  applies.

Nothing here refers to Swing; the concrete instantiation is in
`TransientMeanPassage`.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
namespace SwingRepair
namespace KernelLimit
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

/-! ### Uniform integral bounds pass to a weak limit -/

/-- A uniform bound on the integrals of a continuous nonnegative function along
a weakly convergent family passes to the limit law, together with integrability. -/
theorem limit_integral_le_of_forall_integral_le {ι : Type*} {l : Filter ι} [l.NeBot]
    {ρs : ι → ProbabilityMeasure ℝ} {ρ : ProbabilityMeasure ℝ} (hρ : Tendsto ρs l (𝓝 ρ))
    {g : ℝ → ℝ} (hg : Continuous g) (hg0 : ∀ x, 0 ≤ g x) {M : ℝ}
    (hint : ∀ i, Integrable g (ρs i : Measure ℝ))
    (hbd : ∀ i, (∫ x, g x ∂(ρs i : Measure ℝ)) ≤ M) :
    Integrable g (ρ : Measure ℝ) ∧ (∫ x, g x ∂(ρ : Measure ℝ)) ≤ M := by
  set gn : ℕ → ℝ → ℝ := fun n x => min (g x) (n : ℝ) with hgn
  have hgn_cont : ∀ n, Continuous (gn n) := fun n => hg.min continuous_const
  have hgn_nn : ∀ n x, 0 ≤ gn n x := fun n x => le_min (hg0 x) (Nat.cast_nonneg n)
  have hgn_le : ∀ n x, gn n x ≤ (n : ℝ) := fun n x => min_le_right _ _
  have hgn_le_g : ∀ n x, gn n x ≤ g x := fun n x => min_le_left _ _
  have hgn_abs : ∀ n x, |gn n x| ≤ (n : ℝ) := fun n x => by
    rw [abs_of_nonneg (hgn_nn n x)]
    exact hgn_le n x
  have hgn_int : ∀ (ν : Measure ℝ) [IsProbabilityMeasure ν] (n : ℕ), Integrable (gn n) ν :=
    fun ν _ n => integrable_of_abs_le (hgn_cont n).measurable (hgn_abs n)
  have hbd_n : ∀ n, (∫ x, gn n x ∂(ρ : Measure ℝ)) ≤ M := by
    intro n
    have ht := tendsto_integral_of_tendsto hρ (gn n) (n : ℝ) (hgn_cont n) (hgn_abs n)
    refine le_of_tendsto ht (Eventually.of_forall fun i => ?_)
    exact (integral_mono (hgn_int _ n) (hint i) (fun x => hgn_le_g n x)).trans (hbd i)
  have hmono : Monotone (fun n : ℕ => fun x => ENNReal.ofReal (gn n x)) := by
    intro n m hnm x
    exact ENNReal.ofReal_le_ofReal (min_le_min_left _ (by exact_mod_cast hnm))
  have hsup : (∫⁻ x, ENNReal.ofReal (g x) ∂(ρ : Measure ℝ)) =
      ⨆ n : ℕ, ∫⁻ x, ENNReal.ofReal (gn n x) ∂(ρ : Measure ℝ) := by
    have hmeas : ∀ n, Measurable (fun x => ENNReal.ofReal (gn n x)) := fun n =>
      ENNReal.measurable_ofReal.comp (hgn_cont n).measurable
    rw [← lintegral_iSup hmeas hmono]
    refine lintegral_congr fun x => ?_
    apply le_antisymm
    · obtain ⟨n, hn⟩ := exists_nat_ge (g x)
      refine le_iSup_of_le n ?_
      simp only [hgn]
      rw [min_eq_left hn]
    · exact iSup_le fun n => ENNReal.ofReal_le_ofReal (hgn_le_g n x)
  have hlin_le : (∫⁻ x, ENNReal.ofReal (g x) ∂(ρ : Measure ℝ)) ≤ ENNReal.ofReal M := by
    rw [hsup]
    refine iSup_le fun n => ?_
    rw [← ofReal_integral_eq_lintegral_ofReal (hgn_int _ n) (ae_of_all _ (hgn_nn n))]
    exact ENNReal.ofReal_le_ofReal (hbd_n n)
  have hgint : Integrable g (ρ : Measure ℝ) := by
    refine ⟨hg.measurable.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ hg0)]
    exact lt_of_le_of_lt hlin_le ENNReal.ofReal_lt_top
  refine ⟨hgint, ?_⟩
  have hM : 0 ≤ M := (integral_nonneg (hgn_nn 0)).trans (hbd_n 0)
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hg0) hg.measurable.aestronglyMeasurable]
  calc (∫⁻ x, ENNReal.ofReal (g x) ∂(ρ : Measure ℝ)).toReal
      ≤ (ENNReal.ofReal M).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hlin_le
    _ = M := ENNReal.toReal_ofReal hM

/-! ### Integrability from linear growth and a second moment -/

theorem abs_le_one_add_sq (x : ℝ) : |x| ≤ 1 + |x|^2 := by
  nlinarith [abs_nonneg x, sq_nonneg (|x| - 1)]

theorem integrable_of_le_linear {ν : Measure ℝ} [IsProbabilityMeasure ν] {h : ℝ → ℝ}
    (hh : AEStronglyMeasurable h ν) (hh0 : ∀ x, 0 ≤ h x) {A : ℝ} (hA : 0 ≤ A)
    (hlin : ∀ x, h x ≤ A * (1 + |x|)) (hsq : Integrable (fun x : ℝ => |x|^2) ν) :
    Integrable h ν := by
  refine (((integrable_const (2 : ℝ)).add hsq).const_mul A).mono' hh (ae_of_all _ fun x => ?_)
  simp only [Pi.add_apply, Real.norm_eq_abs, abs_of_nonneg (hh0 x)]
  have := abs_le_one_add_sq x
  have := hlin x
  nlinarith

/-! ### The cutoffs -/

/-- A bump equal to `1` on `|x| ≤ δ`, vanishing for `|x| ≥ 2δ`. -/
def nearCut (δ x : ℝ) : ℝ := clamp01 (2 - |x| / δ)

theorem nearCut_nonneg (δ x : ℝ) : 0 ≤ nearCut δ x := clamp01_nonneg _

theorem nearCut_le_one (δ x : ℝ) : nearCut δ x ≤ 1 := clamp01_le_one _

theorem continuous_nearCut (δ : ℝ) : Continuous (nearCut δ) :=
  continuous_clamp01.comp (continuous_const.sub (continuous_abs.div_const δ))

theorem nearCut_eq_one {δ x : ℝ} (hδ : 0 < δ) (hx : |x| ≤ δ) : nearCut δ x = 1 := by
  apply clamp01_eq_one
  have : |x| / δ ≤ 1 := (div_le_one hδ).mpr hx
  linarith

theorem nearCut_eq_zero {δ x : ℝ} (hδ : 0 < δ) (hx : 2 * δ ≤ |x|) : nearCut δ x = 0 := by
  apply clamp01_eq_zero
  have : 2 ≤ |x| / δ := by
    rw [le_div_iff₀ hδ]
    linarith
  linarith

/-- The bump is dominated by the indicator of the closed ball of radius `2δ`. -/
theorem integral_nearCut_le {ν : Measure ℝ} [IsFiniteMeasure ν] {δ : ℝ} (hδ : 0 < δ) :
    (∫ x, nearCut δ x ∂ν) ≤ ν.real {x : ℝ | |x| ≤ 2 * δ} := by
  have hS : MeasurableSet {x : ℝ | |x| ≤ 2 * δ} :=
    measurableSet_le continuous_abs.measurable measurable_const
  rw [← integral_indicator_one hS]
  refine integral_mono (Doeblin.integrable_bounded_reward ν (continuous_nearCut δ).measurable
      (nearCut_nonneg δ) (nearCut_le_one δ))
    (Doeblin.integrable_bounded_reward ν (measurable_one.indicator hS)
      (indicator_one_nonneg _) (indicator_one_le_one _)) (fun x => ?_)
  by_cases hx : x ∈ {x : ℝ | |x| ≤ 2 * δ}
  · rw [Set.indicator_of_mem hx]
    exact nearCut_le_one δ x
  · rw [Set.indicator_of_notMem hx, nearCut_eq_zero hδ (le_of_not_ge hx)]

/-- The annulus window `(1 - farCut C)(1 - nearCut δ)`. -/
def annulusWindow (δ C x : ℝ) : ℝ := (1 - farCut C x) * (1 - nearCut δ x)

theorem annulusWindow_nonneg (δ C x : ℝ) : 0 ≤ annulusWindow δ C x :=
  mul_nonneg (by linarith [farCut_le_one C x]) (by linarith [nearCut_le_one δ x])

theorem annulusWindow_le_one (δ C x : ℝ) : annulusWindow δ C x ≤ 1 := by
  unfold annulusWindow
  have h1 : 1 - farCut C x ≤ 1 := by linarith [farCut_nonneg C x]
  have h2 : 1 - nearCut δ x ≤ 1 := by linarith [nearCut_nonneg δ x]
  have h1' : 0 ≤ 1 - farCut C x := by linarith [farCut_le_one C x]
  have h2' : 0 ≤ 1 - nearCut δ x := by linarith [nearCut_le_one δ x]
  nlinarith

theorem continuous_annulusWindow (δ C : ℝ) : Continuous (annulusWindow δ C) :=
  (continuous_const.sub (continuous_farCut C)).mul (continuous_const.sub (continuous_nearCut δ))

theorem annulusWindow_eq_zero_of_near {δ C x : ℝ} (hδ : 0 < δ) (hx : |x| ≤ δ) :
    annulusWindow δ C x = 0 := by
  unfold annulusWindow
  rw [nearCut_eq_one hδ hx]
  ring

theorem annulusWindow_eq_zero_of_far {δ C x : ℝ} (hx : C + 1 ≤ |x|) :
    annulusWindow δ C x = 0 := by
  unfold annulusWindow
  rw [farCut_eq_one hx]
  ring

/-- The three-piece decomposition of the identity. -/
theorem decomposition (δ C x : ℝ) (v : ℝ) :
    v = v * farCut C x + v * (1 - farCut C x) * nearCut δ x + v * annulusWindow δ C x := by
  unfold annulusWindow
  ring

/-! ### The far region -/

/-- Markov: the far part of a function of linear growth is controlled by the second moment. -/
theorem integral_mul_farCut_le {ν : Measure ℝ} [IsProbabilityMeasure ν] {h : ℝ → ℝ}
    (hh : AEStronglyMeasurable h ν) (hh0 : ∀ x, 0 ≤ h x) {A : ℝ} (hA : 0 ≤ A)
    (hlin : ∀ x, h x ≤ A * (1 + |x|)) (hsq : Integrable (fun x : ℝ => |x|^2) ν) {M : ℝ}
    (hM : (∫ x, |x|^2 ∂ν) ≤ M) {C : ℝ} (hC : 1 ≤ C) :
    (∫ x, h x * farCut C x ∂ν) ≤ 2 * A * M / C := by
  have hCpos : 0 < C := by linarith
  have hpt : ∀ x, h x * farCut C x ≤ (2 * A / C) * |x|^2 := by
    intro x
    by_cases hx : |x| ≤ C
    · rw [farCut_eq_zero hx, mul_zero]
      positivity
    · have hx' : C < |x| := lt_of_not_ge hx
      have h1 : h x * farCut C x ≤ h x := mul_le_of_le_one_right (hh0 x) (farCut_le_one C x)
      have h2 : h x ≤ A * (2 * |x|) := by
        refine (hlin x).trans ?_
        apply mul_le_mul_of_nonneg_left _ hA
        linarith
      have h3 : A * (2 * |x|) ≤ (2 * A / C) * |x|^2 := by
        have hratio : 1 ≤ |x| / C := by
          rw [le_div_iff₀ hCpos]
          linarith
        have heq : (2 * A / C) * |x|^2 = A * (2 * |x|) * (|x| / C) := by
          field_simp
        rw [heq]
        have h0 : 0 ≤ A * (2 * |x|) := by positivity
        nlinarith
      linarith
  have hhint : Integrable h ν := integrable_of_le_linear hh hh0 hA hlin hsq
  have hint1 : Integrable (fun x => h x * farCut C x) ν :=
    hhint.mul_bdd (c := 1) (continuous_farCut C).measurable.aestronglyMeasurable
      (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (farCut_nonneg C x)]
        exact farCut_le_one C x)
  calc (∫ x, h x * farCut C x ∂ν) ≤ ∫ x, (2 * A / C) * |x|^2 ∂ν :=
        integral_mono hint1 (hsq.const_mul _) hpt
    _ = (2 * A / C) * ∫ x, |x|^2 ∂ν := integral_const_mul _ _
    _ ≤ (2 * A / C) * M := mul_le_mul_of_nonneg_left hM (by positivity)
    _ = 2 * A * M / C := by ring

/-! ### The zero neighbourhood -/

theorem integral_mul_nearCut_le {ν : Measure ℝ} [IsProbabilityMeasure ν] {h : ℝ → ℝ}
    (hh : AEStronglyMeasurable h ν) (hh0 : ∀ x, 0 ≤ h x) {A : ℝ} (hA : 0 ≤ A)
    (hlin : ∀ x, h x ≤ A * (1 + |x|)) (hsq : Integrable (fun x : ℝ => |x|^2) ν)
    {δ C : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1/2) :
    (∫ x, h x * (1 - farCut C x) * nearCut δ x ∂ν) ≤ 2 * A * ∫ x, nearCut δ x ∂ν := by
  have hpt : ∀ x, h x * (1 - farCut C x) * nearCut δ x ≤ 2 * A * nearCut δ x := by
    intro x
    by_cases hx : 2 * δ ≤ |x|
    · rw [nearCut_eq_zero hδ hx]
      simp
    · have hx' : |x| < 2 * δ := lt_of_not_ge hx
      have h1 : h x * (1 - farCut C x) ≤ h x :=
        mul_le_of_le_one_right (hh0 x) (by linarith [farCut_nonneg C x])
      have h2 : h x ≤ 2 * A := by
        refine (hlin x).trans ?_
        have : 1 + |x| ≤ 2 := by linarith
        nlinarith
      have hn := nearCut_nonneg δ x
      have := h1.trans h2
      nlinarith [mul_le_mul_of_nonneg_right this hn]
  have hhint : Integrable h ν := integrable_of_le_linear hh hh0 hA hlin hsq
  have hint1 : Integrable (fun x => h x * (1 - farCut C x) * nearCut δ x) ν := by
    have hb : Integrable (fun x => h x * (1 - farCut C x)) ν :=
      hhint.mul_bdd (c := 1) (continuous_const.sub (continuous_farCut C)).measurable.aestronglyMeasurable
        (ae_of_all _ fun x => by
          rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [farCut_le_one C x])]
          linarith [farCut_nonneg C x])
    exact hb.mul_bdd (c := 1) (continuous_nearCut δ).measurable.aestronglyMeasurable
      (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (nearCut_nonneg δ x)]
        exact nearCut_le_one δ x)
  have hint2 : Integrable (fun x => 2 * A * nearCut δ x) ν :=
    (Doeblin.integrable_bounded_reward ν (continuous_nearCut δ).measurable
      (nearCut_nonneg δ) (nearCut_le_one δ)).const_mul _
  calc (∫ x, h x * (1 - farCut C x) * nearCut δ x ∂ν) ≤ ∫ x, 2 * A * nearCut δ x ∂ν :=
        integral_mono hint1 hint2 hpt
    _ = 2 * A * ∫ x, nearCut δ x ∂ν := integral_const_mul _ _

/-- A finite measure with no atom at `0` puts small mass on small balls. -/
theorem exists_small_ball_measureReal_le {ν : Measure ℝ} [IsFiniteMeasure ν]
    (h0 : ν {0} = 0) {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/2 ∧ ν.real {x : ℝ | |x| ≤ 2 * δ} ≤ η := by
  set s : ℕ → Set ℝ := fun n => {x : ℝ | |x| ≤ 1 / ((n : ℝ) + 1)} with hs
  have hs_meas : ∀ n, NullMeasurableSet (s n) ν := fun n =>
    (measurableSet_le continuous_abs.measurable measurable_const).nullMeasurableSet
  have hanti : Antitone s := by
    intro m n hmn x hx
    simp only [hs, Set.mem_ofPred_eq] at hx ⊢
    refine hx.trans ?_
    apply one_div_le_one_div_of_le (by positivity)
    have : (m : ℝ) ≤ n := by exact_mod_cast hmn
    linarith
  have hinter : (⋂ n, s n) = {0} := by
    ext x
    simp only [Set.mem_iInter, hs, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · intro h
      by_contra hx
      have hpos : 0 < |x| := abs_pos.mpr hx
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hpos
      exact absurd (h n) (not_le.mpr hn)
    · rintro rfl n
      simp only [abs_zero]
      positivity
  have ht := tendsto_measure_iInter_atTop hs_meas hanti ⟨0, measure_ne_top _ _⟩
  rw [hinter, h0] at ht
  have hreal : Tendsto (fun n => ν.real (s n)) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).comp ht
    simpa [Measure.real, Function.comp_def] using this
  obtain ⟨n, hn⟩ := (hreal.eventually (eventually_le_nhds hη)).exists
  refine ⟨1 / (2 * ((n : ℝ) + 1)), by positivity, ?_, ?_⟩
  · have : (2 : ℝ) ≤ 2 * ((n : ℝ) + 1) := by
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    exact one_div_le_one_div_of_le (by norm_num) this
  · have heq : {x : ℝ | |x| ≤ 2 * (1 / (2 * ((n : ℝ) + 1)))} = s n := by
      ext x
      simp only [hs, Set.mem_ofPred_eq]
      have : 2 * (1 / (2 * ((n : ℝ) + 1))) = 1 / ((n : ℝ) + 1) := by
        field_simp
      rw [this]
    rw [heq]
    exact hn

/-! ### The annulus -/

/-- `f` times the annulus window is continuous when `f` is continuous away from `0`. -/
theorem continuous_mul_annulusWindow {f : ℝ → ℝ} (hf : ∀ x, x ≠ 0 → ContinuousAt f x)
    {δ C : ℝ} (hδ : 0 < δ) :
    Continuous (fun x => f x * annulusWindow δ C x) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : |x| < δ
  · have hev : (fun y => f y * annulusWindow δ C y) =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      have hopen : IsOpen {y : ℝ | |y| < δ} := isOpen_lt continuous_abs continuous_const
      filter_upwards [hopen.mem_nhds hx] with y hy
      rw [annulusWindow_eq_zero_of_near hδ (le_of_lt hy), mul_zero]
    exact (continuousAt_const).congr hev.symm
  · have hx0 : x ≠ 0 := by
      intro h
      apply hx
      rw [h, abs_zero]
      exact hδ
    exact (hf x hx0).mul (continuous_annulusWindow δ C).continuousAt

theorem abs_mul_annulusWindow_le {f : ℝ → ℝ} (hf0 : ∀ x, 0 ≤ f x) {A : ℝ} (hA : 0 ≤ A)
    (hlin : ∀ x, f x ≤ A * (1 + |x|)) {δ C : ℝ} (hC : 0 ≤ C) (x : ℝ) :
    |f x * annulusWindow δ C x| ≤ A * (C + 2) := by
  rw [abs_of_nonneg (mul_nonneg (hf0 x) (annulusWindow_nonneg δ C x))]
  by_cases hx : C + 1 ≤ |x|
  · rw [annulusWindow_eq_zero_of_far hx, mul_zero]
    positivity
  · have hx' : |x| < C + 1 := lt_of_not_ge hx
    calc f x * annulusWindow δ C x ≤ f x :=
          mul_le_of_le_one_right (hf0 x) (annulusWindow_le_one δ C x)
      _ ≤ A * (1 + |x|) := hlin x
      _ ≤ A * (C + 2) := by
          apply mul_le_mul_of_nonneg_left _ hA
          linarith

/-! ### The transfer theorem -/

/-- **The abstract mean passage.**  Let `ρ_i ⇒ ρ` be probability laws on the line
with a uniform second moment, let `f_i ≥ 0` and `f ≥ 0` have a common linear
growth bound, let `f` be continuous away from `0`, let `ρ` have no atom at `0`,
and let `f_i → f` uniformly on every annulus `δ ≤ |x| ≤ C`.  Then
`∫ f_i dρ_i → ∫ f dρ`. -/
theorem tendsto_integral_of_transfer {ι : Type*} {l : Filter ι} [l.NeBot]
    {ρs : ι → ProbabilityMeasure ℝ} {ρ : ProbabilityMeasure ℝ} (hρ : Tendsto ρs l (𝓝 ρ))
    {fs : ι → ℝ → ℝ} {f : ℝ → ℝ} {A : ℝ} (hA : 0 ≤ A)
    (hfs_meas : ∀ i, AEStronglyMeasurable (fs i) (ρs i : Measure ℝ))
    (hfs_nn : ∀ i x, 0 ≤ fs i x) (hfs_lin : ∀ i x, fs i x ≤ A * (1 + |x|))
    (hf_meas : Measurable f) (hf_nn : ∀ x, 0 ≤ f x) (hf_lin : ∀ x, f x ≤ A * (1 + |x|))
    (hf_cont : ∀ x, x ≠ 0 → ContinuousAt f x)
    (hρ0 : (ρ : Measure ℝ) {0} = 0)
    {M : ℝ} (hsq : ∀ i, Integrable (fun x : ℝ => |x|^2) (ρs i : Measure ℝ))
    (hM : ∀ i, (∫ x, |x|^2 ∂(ρs i : Measure ℝ)) ≤ M)
    (hunif : ∀ δ C : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ i in l, ∀ x : ℝ, δ ≤ |x| → |x| ≤ C → |fs i x - f x| ≤ ε) :
    Tendsto (fun i => ∫ x, fs i x ∂(ρs i : Measure ℝ)) l (𝓝 (∫ x, f x ∂(ρ : Measure ℝ))) := by
  -- the second moment of the limit
  have hsqcont : Continuous (fun x : ℝ => |x|^2) := continuous_abs.pow 2
  obtain ⟨hsqρ, hMρ⟩ := limit_integral_le_of_forall_integral_le (g := fun x : ℝ => |x|^2) hρ
    hsqcont (fun x => by positivity) hsq hM
  have hM0 : 0 ≤ M := (integral_nonneg (fun x : ℝ => by positivity : ∀ x : ℝ, 0 ≤ |x|^2)).trans hMρ
  have hfint : Integrable f (ρ : Measure ℝ) :=
    integrable_of_le_linear hf_meas.aestronglyMeasurable hf_nn hA hf_lin hsqρ
  have hfsint : ∀ i, Integrable (fs i) (ρs i : Measure ℝ) := fun i =>
    integrable_of_le_linear (hfs_meas i) (hfs_nn i) hA (hfs_lin i) (hsq i)
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε' : 0 < ε := hε
  -- the far cutoff
  set C : ℝ := 16 * (A + 1) * (M + 1) / ε + 1 with hCdef
  have hC1 : 1 ≤ C := by
    have : 0 ≤ 16 * (A + 1) * (M + 1) / ε := by positivity
    linarith
  have hC0 : 0 ≤ C := by linarith
  have hCfar : 2 * A * M / C ≤ ε / 8 := by
    rw [div_le_iff₀ (by linarith)]
    have h1 : ε / 8 * C = 2 * (A + 1) * (M + 1) + ε / 8 := by
      rw [hCdef]
      field_simp
      ring
    rw [h1]
    nlinarith
  -- the zero neighbourhood
  set η : ℝ := ε / (32 * (A + 1)) with hηdef
  have hη : 0 < η := by positivity
  obtain ⟨δ, hδ, hδ1, hδmass⟩ := exists_small_ball_measureReal_le (ν := (ρ : Measure ℝ)) hρ0 hη
  have hAη : 2 * A * (2 * η) ≤ ε / 8 := by
    rw [hηdef]
    have : 2 * A * (2 * (ε / (32 * (A + 1)))) = (ε / 8) * (A / (A + 1)) := by
      field_simp
      ring
    rw [this]
    have : A / (A + 1) ≤ 1 := by
      rw [div_le_one (by linarith)]
      linarith
    nlinarith
  -- bounded pieces
  have hfar_bdd : ∀ x, ‖farCut C x‖ ≤ 1 := fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (farCut_nonneg C x)]
    exact farCut_le_one C x
  have hbulk_bdd : ∀ x, ‖1 - farCut C x‖ ≤ 1 := fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [farCut_le_one C x])]
    linarith [farCut_nonneg C x]
  have hnear_bdd : ∀ x, ‖nearCut δ x‖ ≤ 1 := fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (nearCut_nonneg δ x)]
    exact nearCut_le_one δ x
  have hwin_bdd : ∀ x, ‖annulusWindow δ C x‖ ≤ 1 := fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (annulusWindow_nonneg δ C x)]
    exact annulusWindow_le_one δ C x
  have hfar_meas : AEStronglyMeasurable (farCut C) (ρ : Measure ℝ) :=
    (continuous_farCut C).measurable.aestronglyMeasurable
  -- the window function is bounded continuous
  set g : ℝ → ℝ := fun x => f x * annulusWindow δ C x with hgdef
  have hgcont : Continuous g := continuous_mul_annulusWindow hf_cont hδ
  have hgbdd : ∀ x, |g x| ≤ A * (C + 2) := fun x =>
    abs_mul_annulusWindow_le hf_nn hA hf_lin hC0 x
  -- the eventual estimates
  have hnear_lim : (∫ x, nearCut δ x ∂(ρ : Measure ℝ)) ≤ η :=
    (integral_nearCut_le hδ).trans hδmass
  have hnear_ev : ∀ᶠ i in l, (∫ x, nearCut δ x ∂(ρs i : Measure ℝ)) ≤ 2 * η := by
    have ht := tendsto_integral_of_tendsto hρ (nearCut δ) 1 (continuous_nearCut δ)
      (fun x => by rw [abs_of_nonneg (nearCut_nonneg δ x)]; exact nearCut_le_one δ x)
    have hlt : (∫ x, nearCut δ x ∂(ρ : Measure ℝ)) < 2 * η := by linarith
    filter_upwards [ht.eventually (eventually_lt_nhds hlt)] with i hi
    exact le_of_lt hi
  have hunif_ev := hunif δ (C + 1) hδ (ε / 8) (by linarith)
  have hg_ev : ∀ᶠ i in l,
      |(∫ x, g x ∂(ρs i : Measure ℝ)) - ∫ x, g x ∂(ρ : Measure ℝ)| < ε / 8 := by
    have ht := tendsto_integral_of_tendsto hρ g (A * (C + 2)) hgcont hgbdd
    have := ht.eventually (Metric.ball_mem_nhds _ (by linarith : (0 : ℝ) < ε / 8))
    filter_upwards [this] with i hi
    simpa [Real.dist_eq] using hi
  -- assemble
  filter_upwards [hnear_ev, hunif_ev, hg_ev] with i hnear_i hunif_i hg_i
  rw [Real.dist_eq]
  -- decompositions
  have hfs_dec : (∫ x, fs i x ∂(ρs i : Measure ℝ)) =
      (∫ x, fs i x * farCut C x ∂(ρs i : Measure ℝ)) +
      (∫ x, fs i x * (1 - farCut C x) * nearCut δ x ∂(ρs i : Measure ℝ)) +
      ∫ x, fs i x * annulusWindow δ C x ∂(ρs i : Measure ℝ) := by
    have h1 : Integrable (fun x => fs i x * farCut C x) (ρs i : Measure ℝ) :=
      (hfsint i).mul_bdd (c := 1) (continuous_farCut C).measurable.aestronglyMeasurable
        (ae_of_all _ hfar_bdd)
    have h2 : Integrable (fun x => fs i x * (1 - farCut C x) * nearCut δ x) (ρs i : Measure ℝ) :=
      ((hfsint i).mul_bdd (c := 1)
        (continuous_const.sub (continuous_farCut C)).measurable.aestronglyMeasurable
        (ae_of_all _ hbulk_bdd)).mul_bdd (c := 1)
        (continuous_nearCut δ).measurable.aestronglyMeasurable (ae_of_all _ hnear_bdd)
    have h3 : Integrable (fun x => fs i x * annulusWindow δ C x) (ρs i : Measure ℝ) :=
      (hfsint i).mul_bdd (c := 1) (continuous_annulusWindow δ C).measurable.aestronglyMeasurable
        (ae_of_all _ hwin_bdd)
    have h12 : (∫ x, fs i x * farCut C x ∂(ρs i : Measure ℝ)) +
        (∫ x, fs i x * (1 - farCut C x) * nearCut δ x ∂(ρs i : Measure ℝ)) =
        ∫ x, (fs i x * farCut C x + fs i x * (1 - farCut C x) * nearCut δ x) ∂(ρs i : Measure ℝ) :=
      (integral_add h1 h2).symm
    have h123 : (∫ x, (fs i x * farCut C x + fs i x * (1 - farCut C x) * nearCut δ x)
          ∂(ρs i : Measure ℝ)) + (∫ x, fs i x * annulusWindow δ C x ∂(ρs i : Measure ℝ)) =
        ∫ x, (fs i x * farCut C x + fs i x * (1 - farCut C x) * nearCut δ x +
          fs i x * annulusWindow δ C x) ∂(ρs i : Measure ℝ) :=
      (integral_add (h1.add h2) h3).symm
    rw [h12, h123]
    exact integral_congr_ae (ae_of_all _ fun x => decomposition δ C x (fs i x))
  have hf_dec : (∫ x, f x ∂(ρ : Measure ℝ)) =
      (∫ x, f x * farCut C x ∂(ρ : Measure ℝ)) +
      (∫ x, f x * (1 - farCut C x) * nearCut δ x ∂(ρ : Measure ℝ)) +
      ∫ x, g x ∂(ρ : Measure ℝ) := by
    have h1 : Integrable (fun x => f x * farCut C x) (ρ : Measure ℝ) :=
      hfint.mul_bdd (c := 1) hfar_meas (ae_of_all _ hfar_bdd)
    have h2 : Integrable (fun x => f x * (1 - farCut C x) * nearCut δ x) (ρ : Measure ℝ) :=
      (hfint.mul_bdd (c := 1)
        (continuous_const.sub (continuous_farCut C)).measurable.aestronglyMeasurable
        (ae_of_all _ hbulk_bdd)).mul_bdd (c := 1)
        (continuous_nearCut δ).measurable.aestronglyMeasurable (ae_of_all _ hnear_bdd)
    have h3 : Integrable g (ρ : Measure ℝ) :=
      hfint.mul_bdd (c := 1) (continuous_annulusWindow δ C).measurable.aestronglyMeasurable
        (ae_of_all _ hwin_bdd)
    have h12 : (∫ x, f x * farCut C x ∂(ρ : Measure ℝ)) +
        (∫ x, f x * (1 - farCut C x) * nearCut δ x ∂(ρ : Measure ℝ)) =
        ∫ x, (f x * farCut C x + f x * (1 - farCut C x) * nearCut δ x) ∂(ρ : Measure ℝ) :=
      (integral_add h1 h2).symm
    have h123 : (∫ x, (f x * farCut C x + f x * (1 - farCut C x) * nearCut δ x)
          ∂(ρ : Measure ℝ)) + (∫ x, g x ∂(ρ : Measure ℝ)) =
        ∫ x, (f x * farCut C x + f x * (1 - farCut C x) * nearCut δ x + g x) ∂(ρ : Measure ℝ) :=
      (integral_add (h1.add h2) h3).symm
    rw [h12, h123]
    exact integral_congr_ae (ae_of_all _ fun x => decomposition δ C x (f x))
  -- the six estimates
  have e1 : (∫ x, fs i x * farCut C x ∂(ρs i : Measure ℝ)) ≤ ε / 8 :=
    (integral_mul_farCut_le (hfs_meas i) (hfs_nn i) hA (hfs_lin i) (hsq i) (hM i) hC1).trans hCfar
  have e1' : 0 ≤ ∫ x, fs i x * farCut C x ∂(ρs i : Measure ℝ) :=
    integral_nonneg fun x => mul_nonneg (hfs_nn i x) (farCut_nonneg C x)
  have e2 : (∫ x, fs i x * (1 - farCut C x) * nearCut δ x ∂(ρs i : Measure ℝ)) ≤ ε / 8 := by
    refine (integral_mul_nearCut_le (hfs_meas i) (hfs_nn i) hA (hfs_lin i) (hsq i) hδ hδ1).trans ?_
    calc 2 * A * ∫ x, nearCut δ x ∂(ρs i : Measure ℝ) ≤ 2 * A * (2 * η) :=
          mul_le_mul_of_nonneg_left hnear_i (by positivity)
      _ ≤ ε / 8 := hAη
  have e2' : 0 ≤ ∫ x, fs i x * (1 - farCut C x) * nearCut δ x ∂(ρs i : Measure ℝ) :=
    integral_nonneg fun x => mul_nonneg (mul_nonneg (hfs_nn i x)
      (by linarith [farCut_le_one C x])) (nearCut_nonneg δ x)
  have e3 : |(∫ x, fs i x * annulusWindow δ C x ∂(ρs i : Measure ℝ)) -
      ∫ x, g x ∂(ρs i : Measure ℝ)| ≤ ε / 8 := by
    have hfsw : Integrable (fun x => fs i x * annulusWindow δ C x) (ρs i : Measure ℝ) :=
      (hfsint i).mul_bdd (c := 1) (continuous_annulusWindow δ C).measurable.aestronglyMeasurable
        (ae_of_all _ hwin_bdd)
    have hgi : Integrable g (ρs i : Measure ℝ) :=
      integrable_of_abs_le hgcont.measurable hgbdd
    have hpt : ∀ x, |fs i x * annulusWindow δ C x - g x| ≤ ε / 8 := by
      intro x
      simp only [hgdef]
      rw [← sub_mul, abs_mul, abs_of_nonneg (annulusWindow_nonneg δ C x)]
      by_cases hx : |x| < δ
      · rw [annulusWindow_eq_zero_of_near hδ hx.le, mul_zero]
        linarith
      · by_cases hx' : C + 1 ≤ |x|
        · rw [annulusWindow_eq_zero_of_far hx', mul_zero]
          linarith
        · have hd := hunif_i x (le_of_not_gt hx) (le_of_lt (lt_of_not_ge hx'))
          calc |fs i x - f x| * annulusWindow δ C x ≤ |fs i x - f x| :=
                mul_le_of_le_one_right (abs_nonneg _) (annulusWindow_le_one δ C x)
            _ ≤ ε / 8 := hd
    calc |(∫ x, fs i x * annulusWindow δ C x ∂(ρs i : Measure ℝ)) -
          ∫ x, g x ∂(ρs i : Measure ℝ)|
        = |∫ x, (fs i x * annulusWindow δ C x - g x) ∂(ρs i : Measure ℝ)| := by
          rw [integral_sub hfsw hgi]
      _ ≤ ∫ x, |fs i x * annulusWindow δ C x - g x| ∂(ρs i : Measure ℝ) :=
          abs_integral_le_integral_abs
      _ ≤ ∫ _x, ε / 8 ∂(ρs i : Measure ℝ) :=
          integral_mono (hfsw.sub hgi).abs (integrable_const _) hpt
      _ = ε / 8 := by simp
  have e5 : (∫ x, f x * (1 - farCut C x) * nearCut δ x ∂(ρ : Measure ℝ)) ≤ ε / 8 := by
    refine (integral_mul_nearCut_le hf_meas.aestronglyMeasurable hf_nn hA hf_lin hsqρ hδ hδ1).trans ?_
    calc 2 * A * ∫ x, nearCut δ x ∂(ρ : Measure ℝ) ≤ 2 * A * (2 * η) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          linarith
      _ ≤ ε / 8 := hAη
  have e5' : 0 ≤ ∫ x, f x * (1 - farCut C x) * nearCut δ x ∂(ρ : Measure ℝ) :=
    integral_nonneg fun x => mul_nonneg (mul_nonneg (hf_nn x)
      (by linarith [farCut_le_one C x])) (nearCut_nonneg δ x)
  have e6 : (∫ x, f x * farCut C x ∂(ρ : Measure ℝ)) ≤ ε / 8 :=
    (integral_mul_farCut_le hf_meas.aestronglyMeasurable hf_nn hA hf_lin hsqρ hMρ hC1).trans hCfar
  have e6' : 0 ≤ ∫ x, f x * farCut C x ∂(ρ : Measure ℝ) :=
    integral_nonneg fun x => mul_nonneg (hf_nn x) (farCut_nonneg C x)
  rw [hfs_dec, hf_dec]
  have hgw : (∫ x, fs i x * annulusWindow δ C x ∂(ρs i : Measure ℝ)) -
      ∫ x, g x ∂(ρ : Measure ℝ) =
      ((∫ x, fs i x * annulusWindow δ C x ∂(ρs i : Measure ℝ)) -
        ∫ x, g x ∂(ρs i : Measure ℝ)) +
      ((∫ x, g x ∂(ρs i : Measure ℝ)) - ∫ x, g x ∂(ρ : Measure ℝ)) := by ring
  have hgw_abs : |(∫ x, fs i x * annulusWindow δ C x ∂(ρs i : Measure ℝ)) -
      ∫ x, g x ∂(ρ : Measure ℝ)| ≤ ε / 8 + ε / 8 := by
    rw [hgw]
    exact (abs_add_le _ _).trans (add_le_add e3 hg_i.le)
  rw [abs_le] at hgw_abs
  rw [abs_lt]
  constructor <;> linarith [hgw_abs.1, hgw_abs.2]

end KernelLimit
end SwingRepair
