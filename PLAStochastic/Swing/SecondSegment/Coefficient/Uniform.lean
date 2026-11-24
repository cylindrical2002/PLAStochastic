import PLAStochastic.Swing.SecondSegment.Coefficient.PointwiseLimit

/-! # Uniform convergence of the conditional mean on negative compacts

`second-coefficient.md`, C2.2: for `0 < δ`,
`sup_{r ∈ [-M,-δ]} |g_E(r)/E - ℓ(r)| → 0`, where `g_E(r) = E L_E(r)` is the
frozen conditional mean at margin `r`.

The finite-budget means need not be monotone in `r`, but they are monotone
along a cone: the band `[r + W - 2E, r + W]` grows when `r` increases by `h`
and `E` by `h/2`, so `g_E(r) ≤ g_{E+h/2}(r+h)` pathwise in mean.  On a grid of
mesh `h` this sandwiches `g_E(r)/E` between finitely many shifted means, each of
which converges to `ℓ` at a grid point (`frozenMean_div_tendsto_kernel`).  The
Lipschitz bound C2.5 for `ℓ` then closes the uniform estimate.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℝ} {μ : Measure Ω}

/-- `g_E(r)`: the frozen conditional mean of the second segment at margin `r`. -/
def secondSegmentFrozenMean (X : ℕ → Ω → ℝ) (μ : Measure Ω) (E r : ℝ) : ℝ :=
  ∫ ω, frozenPrefixLengthReal X r E ω ∂μ

theorem secondSegmentFrozenMean_eq_restartMean (X : ℕ → Ω → ℝ) (μ : Measure Ω) (E r : ℝ) :
    secondSegmentFrozenMean X μ E r = nativeRestartMean X μ E (r - E) := by
  rw [nativeRestartMean_eq_frozen X μ E (r - E), sub_add_cancel]
  rfl

theorem secondSegmentFrozenMean_measurable [SFinite μ] (hX : ∀ n, Measurable (X n)) (E : ℝ) :
    Measurable (secondSegmentFrozenMean X μ E) := by
  have h : secondSegmentFrozenMean X μ E = fun r => nativeRestartMean X μ E (r - E) := by
    funext r
    exact secondSegmentFrozenMean_eq_restartMean X μ E r
  rw [h]
  exact (nativeRestartMean_measurable hX E).comp (measurable_id.sub_const E)

theorem secondSegmentFrozenMean_nonneg (X : ℕ → Ω → ℝ) (μ : Measure Ω) (E r : ℝ) :
    0 ≤ secondSegmentFrozenMean X μ E r :=
  integral_nonneg fun ω => frozenPrefixLengthReal_nonneg X r E ω

/-! ### Cone monotonicity -/

omit [MeasurableSpace Ω] in
/-- Raising the margin by `h` and the budget by at least `h/2` enlarges every
frozen band, hence the maximal feasible prefix. -/
theorem frozenPrefixLength_mono_cone {r r' E E' : ℝ} (hr : r ≤ r') (hE : r' - r ≤ 2*(E' - E))
    (ω : Ω) : frozenPrefixLength X r E ω ≤ frozenPrefixLength X r' E' ω := by
  have key : ∀ n : ℕ, (n : WithTop ℕ) ≤ frozenPrefixLength X r E ω →
      (n : WithTop ℕ) ≤ frozenPrefixLength X r' E' ω := by
    intro n hn
    obtain ⟨m, hm⟩ := (le_frozenPrefixLength_iff X r E n ω).mp hn
    refine (le_frozenPrefixLength_iff X r' E' n ω).mpr ⟨m, fun j hj => ?_⟩
    obtain ⟨h1, h2⟩ := hm j hj
    constructor <;> linarith
  cases h : frozenPrefixLength X r E ω using WithTop.recTopCoe with
  | top =>
    have hk : ∀ n : ℕ, (n : WithTop ℕ) ≤ frozenPrefixLength X r' E' ω :=
      fun n => key n (by rw [h]; exact le_top)
    cases h' : frozenPrefixLength X r' E' ω using WithTop.recTopCoe with
    | top => exact le_rfl
    | coe m =>
      have := hk (m+1)
      rw [h'] at this
      have h2 : m + 1 ≤ m := WithTop.coe_le_coe.mp this
      omega
  | coe k => exact key k (by rw [h]; simp)

omit [MeasurableSpace Ω] in
theorem frozenPrefixLengthReal_mono_cone {r r' E E' : ℝ} (hr : r ≤ r')
    (hE : r' - r ≤ 2*(E' - E)) {ω : Ω} (hfin : frozenPrefixLength X r' E' ω ≠ ⊤) :
    frozenPrefixLengthReal X r E ω ≤ frozenPrefixLengthReal X r' E' ω := by
  have hle := frozenPrefixLength_mono_cone (X := X) hr hE ω
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hfin
  rw [← hm] at hle
  unfold frozenPrefixLengthReal
  rw [← hm]
  cases h : frozenPrefixLength X r E ω using WithTop.recTopCoe with
  | top => rw [h] at hle; exact absurd hle (by simp)
  | coe k =>
    rw [h] at hle
    simp only [WithTop.untopD_coe]
    exact_mod_cast WithTop.coe_le_coe.mp hle

/-- The cone monotonicity of the conditional means. -/
theorem secondSegmentFrozenMean_mono_cone
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {r r' E E' : ℝ} (hr : r ≤ r')
    (hEE : r' - r ≤ 2*(E' - E)) (hE : 0 < E) (hE' : 0 < E') :
    secondSegmentFrozenMean X μ E r ≤ secondSegmentFrozenMean X μ E' r' := by
  refine integral_mono_ae (frozenPrefixLengthReal_integrable hX hi hG r hE)
    (frozenPrefixLengthReal_integrable hX hi hG r' hE') ?_
  filter_upwards [frozenPrefixLength_tendsto_ae hX hi hG r'] with ω hω
  exact frozenPrefixLengthReal_mono_cone hr hEE (hω.2.1 E')

/-! ### Shifted pointwise limits -/

theorem secondSegmentFrozenMean_shift_tendsto
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {s : ℝ} (hs : s < 0) (a : ℝ) :
    Tendsto (fun E => secondSegmentFrozenMean X μ (E + a) s / E) atTop
      (𝓝 (secondSegmentLimitKernel X μ s)) := by
  have h1 := (frozenMean_div_tendsto_kernel hX hi hG hs).comp
    (tendsto_atTop_add_const_right atTop a tendsto_id)
  have h2 : Tendsto (fun E : ℝ => 1 + a / E) atTop (𝓝 1) := by
    have := (tendsto_const_nhds (x := a)).div_atTop (tendsto_id (α := ℝ))
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).add this
  have h3 := h1.mul h2
  rw [mul_one] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_gt_atTop (max 0 (-a))] with E hE
  have hE0 : 0 < E := lt_of_le_of_lt (le_max_left _ _) hE
  have hEa : E + a ≠ 0 := by
    have := lt_of_le_of_lt (le_max_right _ _) hE
    linarith
  simp only [Function.comp_apply, id]
  unfold secondSegmentFrozenMean
  field_simp

/-! ### C2.2 -/

/-- **C2.2.**  For every `δ > 0`, the normalised conditional means converge to
`ℓ` uniformly on `[-M, -δ]`. -/
theorem secondSegmentFrozenMean_tendstoUniformlyOn
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {δ M : ℝ} (hδ : 0 < δ) :
    TendstoUniformlyOn (fun E r => secondSegmentFrozenMean X μ E r / E)
      (secondSegmentLimitKernel X μ) atTop (Icc (-M) (-δ)) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  set Lc : ℝ := 2 / (δ/2)^2 with hLc
  have hLc0 : 0 < Lc := by positivity
  set h : ℝ := min (δ/2) (ε / (4*Lc)) with hhdef
  have hh0 : 0 < h := lt_min (by linarith) (by positivity)
  have hhδ : h ≤ δ/2 := min_le_left _ _
  have hhε : Lc * h ≤ ε/4 := by
    have := min_le_right (δ/2) (ε / (4*Lc))
    rw [← hhdef] at this
    calc Lc * h ≤ Lc * (ε / (4*Lc)) := mul_le_mul_of_nonneg_left this hLc0.le
      _ = ε/4 := by field_simp
  set J : ℕ := ⌊max M 0 / h⌋₊ + 1 with hJ
  set s : ℕ → ℝ := fun j => -M + j*h with hsdef
  have hev : ∀ j ∈ Finset.range J, ∀ᶠ E in atTop, s j + h < 0 →
      (secondSegmentLimitKernel X μ (s j) - ε/4 ≤
          secondSegmentFrozenMean X μ (E + -(h/2)) (s j) / E ∧
        secondSegmentFrozenMean X μ (E + h/2) (s j + h) / E ≤
          secondSegmentLimitKernel X μ (s j + h) + ε/4) := by
    intro j _
    by_cases hneg : s j + h < 0
    · have hs1 : s j < 0 := by linarith
      have hlo := secondSegmentFrozenMean_shift_tendsto hX hi hG hs1 (-(h/2))
      have hup := secondSegmentFrozenMean_shift_tendsto hX hi hG hneg (h/2)
      have hlo' := hlo.eventually (eventually_ge_nhds
        (show secondSegmentLimitKernel X μ (s j) - ε/4 < secondSegmentLimitKernel X μ (s j) by
          linarith))
      have hup' := hup.eventually (eventually_le_nhds
        (show secondSegmentLimitKernel X μ (s j + h) <
          secondSegmentLimitKernel X μ (s j + h) + ε/4 by linarith))
      filter_upwards [hlo', hup'] with E h1 h2
      exact fun _ => ⟨h1, h2⟩
    · exact Eventually.of_forall fun E hE => absurd hE hneg
  have hall := (Filter.eventually_all_finset (Finset.range J)).mpr hev
  filter_upwards [hall, eventually_gt_atTop h] with E hEall hEh
  intro r hr
  obtain ⟨hrM, hrδ⟩ := hr
  have hE0 : 0 < E := hh0.trans hEh
  set j : ℕ := ⌊(r + M)/h⌋₊ with hjdef
  have hq0 : 0 ≤ (r + M)/h := div_nonneg (by linarith) hh0.le
  have hj1 : (j : ℝ) ≤ (r + M)/h := Nat.floor_le hq0
  have hj2 : (r + M)/h < j + 1 := Nat.lt_floor_add_one _
  have hsj : s j ≤ r := by
    have := (le_div_iff₀ hh0).mp hj1
    simp only [hsdef]
    linarith
  have hsj' : r < s j + h := by
    have := (div_lt_iff₀ hh0).mp hj2
    simp only [hsdef]
    linarith
  have hjJ : j ∈ Finset.range J := by
    rw [Finset.mem_range, hJ]
    have : j ≤ ⌊max M 0 / h⌋₊ := by
      apply Nat.floor_le_floor
      apply div_le_div_of_nonneg_right _ hh0.le
      have := le_max_left M 0
      linarith
    omega
  have hsneg : s j + h < 0 := by linarith
  obtain ⟨hlo, hup⟩ := hEall j hjJ hsneg
  -- the cone sandwich
  have hcone_lo :
      secondSegmentFrozenMean X μ (E + -(h/2)) (s j) ≤ secondSegmentFrozenMean X μ E r :=
    secondSegmentFrozenMean_mono_cone hX hi hG hsj (by linarith) (by linarith) hE0
  have hcone_up :
      secondSegmentFrozenMean X μ E r ≤ secondSegmentFrozenMean X μ (E + h/2) (s j + h) :=
    secondSegmentFrozenMean_mono_cone hX hi hG hsj'.le (by linarith) hE0 (by linarith)
  have hlo2 :
      secondSegmentFrozenMean X μ (E + -(h/2)) (s j) / E ≤ secondSegmentFrozenMean X μ E r / E :=
    div_le_div_of_nonneg_right hcone_lo hE0.le
  have hup2 :
      secondSegmentFrozenMean X μ E r / E ≤
        secondSegmentFrozenMean X μ (E + h/2) (s j + h) / E :=
    div_le_div_of_nonneg_right hcone_up hE0.le
  -- the Lipschitz bound for `ℓ`
  have hδ2 : 0 < δ/2 := by linarith
  have hl1 := abs_secondSegmentLimitKernel_sub_le hX hi hG hδ2 (r := s j) (s := r)
    (by linarith) (by linarith)
  have hl2 := abs_secondSegmentLimitKernel_sub_le hX hi hG hδ2 (r := s j + h) (s := r)
    (by linarith) (by linarith)
  rw [← hLc] at hl1 hl2
  have hd1 : |s j - r| ≤ h := by rw [abs_le]; constructor <;> linarith
  have hd2 : |s j + h - r| ≤ h := by rw [abs_le]; constructor <;> linarith
  have hb1 : Lc * |s j - r| ≤ ε/4 := (mul_le_mul_of_nonneg_left hd1 hLc0.le).trans hhε
  have hb2 : Lc * |s j + h - r| ≤ ε/4 := (mul_le_mul_of_nonneg_left hd2 hLc0.le).trans hhε
  rw [abs_le] at hl1 hl2
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith [hl1.1, hl1.2, hl2.1, hl2.2]

end SwingRepair
