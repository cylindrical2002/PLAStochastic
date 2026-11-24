import PLAStochastic.Swing.Ladder.ZeroDrift.SpreadOutDeficit

/-!
# Blackwell's renewal theorem for one spread-out law

For a `SpreadOutLaw ν κ` (a probability law on `(0,∞)` with a Lebesgue component
`κ · Leb|[1,2]` and a finite second moment) the renewal measure `U = ∑ ν^{*n}` satisfies

`U((b-x, b]) → x / E H` as `b → ∞`, uniformly for `x` in every compact range `[0,K]`.

The proof is the quantitative harmonic-function argument of
`Swing.Ladder.Blackwell.UniformWindowLimit`, run for a single law: a pigeonhole over `N`
consecutive blocks makes the window supremum (resp. infimum) almost constant on one block,
the deficit estimate of `SpreadOutDeficit` turns that into smallness of the smoothed
deficit, and the stationary identity pins the limiting value.  No renewal theorem is
assumed.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical MeasureTheory
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

namespace SpreadOutLaw

variable {ν : Measure ℝ} {κ : ℝ}

/-! ## The remote tail -/

theorem convPow_tail_le_theta (h : SpreadOutLaw ν κ)
    {K β₀ : ℝ} (hβ₀ : K < β₀) (n : ℕ) {j : ℕ} (hj : j ≤ n + 1) {c : ℝ} (hc : β₀ ≤ c) :
    (measureConvPow ν j).real (Ioi (c - K)) ≤
      blackwellTheta (∫ x, x ^ 2 ∂ν) K β₀ n := by
  have hB0 := h.sqMoment_nonneg
  set B := (∫ x, x ^ 2 ∂ν) with hBdef
  have hpos : 0 < c - K := by linarith
  refine (h.convPow_tail_le j hpos).trans ?_
  unfold blackwellTheta
  have hj' : (j : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast hj
  have h1 : (j : ℝ) ^ 3 * B ≤ ((n : ℝ) + 1) ^ 3 * B := by gcongr
  have h2 : (β₀ - K) ^ 2 ≤ (c - K) ^ 2 := by gcongr
  have hd : 0 < (β₀ - K) ^ 2 := by
    have : 0 < β₀ - K := by linarith
    positivity
  exact div_le_div₀ (by positivity) h1 hd h2

/-! ## Assembly at fixed drift and window length -/

/-- **Upper bound.**  Beyond `β₀ + N T` the window mass exceeds `x/μ_a` by at
most the total error. -/
theorem renewalWindow_sub_le_total (h : SpreadOutLaw ν κ)
    {x K : ℝ} (hx : 0 ≤ x) (hxK : x ≤ K)
    {η : ℝ} (hη : 0 < η) (hη4 : η ≤ 1 / 4) (n m₀ : ℕ) (hn : 1 ≤ n) (hm₀ : m₀ ≤ n)
    {T β₀ : ℝ} (hT : 0 < T) (hβ₀ : K < β₀) (N : ℕ) (hN : 0 < N)
    {b : ℝ} (hb : β₀ + N * T ≤ b) :
    renewalWindow ν x b -
        x / ladderMean ν ≤
      blackwellTotal κ
        (∫ x, x ^ 2 ∂ν) (spreadOutWindowBound κ K) K η T β₀
        n m₀ N := by
  have hprob := h.isProbabilityMeasure
  have hQprob := h.equilibrium_isProbabilityMeasure
  set B := (∫ x, x ^ 2 ∂ν) with hBdef
  set P := spreadOutWindowBound κ K with hPdef
  set θ := blackwellTheta B K β₀ n with hθdef
  set A := blackwellAmplification κ η n with hAdef
  set R₀ := blackwellRemainder κ B P η T n m₀ with hR₀def
  set μ0 := ladderMean ν with hμ0def
  set W : ℝ → ℝ := renewalWindow ν x with hWdef
  have hσprob : IsProbabilityMeasure (blackwellSmoothing ν m₀) :=
    blackwellSmoothing_isProbabilityMeasure ν hQprob m₀
  set σ := blackwellSmoothing ν m₀ with hσdef
  have hK : 0 ≤ K := hx.trans hxK
  have hκ : 0 < κ := h.pos
  have hB0 : 0 ≤ B := h.sqMoment_nonneg
  have hP : 0 < P := spreadOutWindowBound_pos h.pos hK
  have hθ0 : 0 ≤ θ := blackwellTheta_nonneg hB0 n
  have hA0 : 0 ≤ A := by
    rw [hAdef]
    unfold blackwellAmplification
    refine mul_nonneg (by positivity) (Finset.sum_nonneg fun m _ => ?_)
    exact (one_div_pos.mpr (minorConst_pos hκ hη m)).le
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hW0 : ∀ u, 0 ≤ W u := fun u => renewalWindow_nonneg ν x u
  have hWP : ∀ u, W u ≤ P := fun u =>
    h.renewalWindow_le_bound hx hxK u
  have hUP : ∀ u, ladderRenewalMeasure ν (Ioc (u - x) u) ≤ ENNReal.ofReal P := fun u =>
    h.window_le_ofReal hx hxK u
  set L : ℝ → ℝ := windowSup W with hLdef
  have hL0 : ∀ β, 0 ≤ L β := fun β => windowSup_nonneg hW0 hWP β
  have hLP : ∀ β, L β ≤ P := fun β => windowSup_le hWP β
  -- pigeonhole over the blocks
  obtain ⟨j, hjN, hjstep⟩ := exists_block_small_decrease
    (f := fun j : ℕ => L (β₀ + j * T)) (fun j => hL0 _) (fun j => hLP _) hN
  set β : ℝ := β₀ + j * T with hβdef
  set β' : ℝ := β₀ + (j + 1 : ℕ) * T with hβ'def
  have hββ' : β' = β + T := by
    rw [hβ'def, hβdef]
    push_cast
    ring
  have hβ₀β : β₀ ≤ β := by
    rw [hβdef]
    have : (0 : ℝ) ≤ j * T := by positivity
    linarith
  have hstep : L β - L β' ≤ P / N := hjstep
  -- the near-supremum point
  set ϵ : ℝ := P / N with hϵdef
  have hϵ : 0 < ϵ := by positivity
  obtain ⟨bs, hbs, hWbs⟩ := exists_near_window_sSup hWP β' hϵ
  have hbsβ : β ≤ bs := by linarith [hbs, hββ', hT]
  -- the deficit
  set S : ℝ := bs - β with hSdef
  have hTS : T ≤ S := by linarith [hbs, hββ']
  set Ψ : ℝ → ℝ := fun y => L β - W (bs - y) with hΨdef
  have hΨmeas : Measurable Ψ := measurable_const.sub (measurable_renewalWindow_shift ν x bs)
  have hΨP : ∀ y, Ψ y ≤ P := fun y => by
    show L β - W (bs - y) ≤ P
    linarith [hLP β, hW0 (bs - y)]
  have hΨlow : ∀ y, -P ≤ Ψ y := fun y => by
    show -P ≤ L β - W (bs - y)
    linarith [hL0 β, hWP (bs - y)]
  have hΨnn : ∀ y, y ≤ S → 0 ≤ Ψ y := fun y hy => by
    show 0 ≤ L β - W (bs - y)
    have : W (bs - y) ≤ L β := le_windowSup hWP (by linarith)
    linarith
  -- the correction terms are bounded by `θ`
  have hcorr : ∀ m : ℕ, m < n + 1 →
      (∑ i ∈ Finset.range (m + 1),
        (measureConvPow ν i (Ioc (bs - x) bs)).toReal) ≤ ((n : ℝ) + 1) * θ := by
    intro m hm
    have hterm : ∀ i ∈ Finset.range (m + 1),
        (measureConvPow ν i (Ioc (bs - x) bs)).toReal ≤ θ := by
      intro i hi'
      have hi'' : i ≤ n + 1 := by
        have := Finset.mem_range.mp hi'
        omega
      have hsub : Ioc (bs - x) bs ⊆ Ioi (bs - K) := by
        intro y hy
        show bs - K < y
        linarith [hy.1]
      calc (measureConvPow ν i (Ioc (bs - x) bs)).toReal
          ≤ (measureConvPow ν i).real (Ioi (bs - K)) :=
            measureReal_mono hsub (measure_ne_top _ _)
        _ ≤ θ := h.convPow_tail_le_theta hβ₀ n hi'' (hβ₀β.trans hbsβ)
    calc (∑ i ∈ Finset.range (m + 1), (measureConvPow ν i (Ioc (bs - x) bs)).toReal)
        ≤ ∑ _i ∈ Finset.range (m + 1), θ := Finset.sum_le_sum hterm
      _ = ((m : ℝ) + 1) * θ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
      _ ≤ ((n : ℝ) + 1) * θ := by
          have : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by
            have : (m : ℝ) ≤ n := by exact_mod_cast (Nat.lt_succ_iff.mp hm)
            linarith
          exact mul_le_mul_of_nonneg_right this hθ0
  set D : ℝ := 2 * P / N + ((n : ℝ) + 1) * θ with hDdef
  have hΨint : ∀ m : ℕ, m < n + 1 → (∫ y, Ψ y ∂(measureConvPow ν (m + 1))) ≤ D := by
    intro m hm
    have h := window_deficit_integral_eq ν hP.le hUP (m + 1) bs (L β)
    change (∫ y, (L β - W (bs - y)) ∂(measureConvPow ν (m + 1))) ≤ D
    rw [h]
    have hc := hcorr m hm
    have hWbs' : L β' - ϵ ≤ W bs := hWbs
    rw [hDdef]
    have : 2 * P / N = P / N + P / N := by ring
    rw [this]
    linarith
  -- the core estimate
  have hcore := h.deficit_integral_smoothing_le hK hη hη4 n m₀ hn hT hTS
    hΨmeas hΨP hΨlow hΨnn hΨint
  -- the stationary identity through the smoothing
  have hstat := h.integral_window_smoothing_sub_le hx hxK m₀ bs
  have htail : (measureConvPow ν m₀).real (Ioi (bs - K)) ≤ θ :=
    h.convPow_tail_le_theta hβ₀ n (by omega) (hβ₀β.trans hbsβ)
  have hstat' : (∫ w, W (bs - w) ∂σ) - x / μ0 ≤ (P + K / κ) * θ := by
    have h1 := (abs_le.mp hstat).2
    have h2 : (P + K / κ) * (measureConvPow ν m₀).real (Ioi (bs - K)) ≤ (P + K / κ) * θ :=
      mul_le_mul_of_nonneg_left htail (by positivity)
    linarith
  -- `∫ Ψ dσ = L β - ∫ W(bs - ·) dσ`
  have hWint : Integrable (fun w => W (bs - w)) σ := by
    refine (integrable_const P).mono' (measurable_renewalWindow_shift ν x bs).aestronglyMeasurable ?_
    filter_upwards with w
    rw [Real.norm_eq_abs, abs_of_nonneg (hW0 _)]
    exact hWP _
  have hΨσ : (∫ y, Ψ y ∂σ) = L β - ∫ w, W (bs - w) ∂σ := by
    change (∫ y, (L β - W (bs - y)) ∂σ) = _
    rw [integral_sub (integrable_const _) hWint, integral_const, Measure.real, measure_univ,
      ENNReal.toReal_one, one_smul]
  have hΨΦ : (∫ y, Ψ y ∂σ) ≤ ∫ y, max (Ψ y) 0 ∂σ := by
    refine integral_mono ?_ ?_ fun y => le_max_left _ _
    · refine (integrable_const P).mono' hΨmeas.aestronglyMeasurable ?_
      filter_upwards with y
      rw [Real.norm_eq_abs, abs_le]
      exact ⟨hΨlow y, hΨP y⟩
    · refine (integrable_const P).mono' (hΨmeas.max measurable_const).aestronglyMeasurable ?_
      filter_upwards with y
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
      exact max_le (hΨP y) hP.le
  -- from `L β` to `W b`
  have hWb : W b ≤ L β := by
    have h1 : W b ≤ L (β₀ + N * T) := le_windowSup hWP hb
    have h2 : L (β₀ + N * T) ≤ L β := by
      refine windowSup_antitone hWP ?_
      rw [hβdef]
      have : (j : ℝ) ≤ N := by exact_mod_cast hjN.le
      nlinarith
    exact h1.trans h2
  -- assemble
  have hmain : L β - x / μ0 ≤ A * D + R₀ + (P + K / κ) * θ := by
    have : L β - x / μ0 = (∫ y, Ψ y ∂σ) + ((∫ w, W (bs - w) ∂σ) - x / μ0) := by
      rw [hΨσ]
      ring
    rw [this]
    linarith
  unfold blackwellTotal
  change W b - x / μ0 ≤ A * D + R₀ + (P + K / κ) * θ
  linarith

/-- **Lower bound.**  Beyond `β₀ + N T` the window mass falls short of `x/μ_a`
by at most the total error. -/
theorem sub_renewalWindow_le_total (h : SpreadOutLaw ν κ)
    {x K : ℝ} (hx : 0 ≤ x) (hxK : x ≤ K)
    {η : ℝ} (hη : 0 < η) (hη4 : η ≤ 1 / 4) (n m₀ : ℕ) (hn : 1 ≤ n) (hm₀ : m₀ ≤ n)
    {T β₀ : ℝ} (hT : 0 < T) (hβ₀ : K < β₀) (N : ℕ) (hN : 0 < N)
    {b : ℝ} (hb : β₀ + N * T ≤ b) :
    x / ladderMean ν -
        renewalWindow ν x b ≤
      blackwellTotal κ
        (∫ x, x ^ 2 ∂ν) (spreadOutWindowBound κ K) K η T β₀
        n m₀ N := by
  have hprob := h.isProbabilityMeasure
  have hQprob := h.equilibrium_isProbabilityMeasure
  set B := (∫ x, x ^ 2 ∂ν) with hBdef
  set P := spreadOutWindowBound κ K with hPdef
  set θ := blackwellTheta B K β₀ n with hθdef
  set A := blackwellAmplification κ η n with hAdef
  set R₀ := blackwellRemainder κ B P η T n m₀ with hR₀def
  set μ0 := ladderMean ν with hμ0def
  set W : ℝ → ℝ := renewalWindow ν x with hWdef
  have hσprob : IsProbabilityMeasure (blackwellSmoothing ν m₀) :=
    blackwellSmoothing_isProbabilityMeasure ν hQprob m₀
  set σ := blackwellSmoothing ν m₀ with hσdef
  have hK : 0 ≤ K := hx.trans hxK
  have hκ : 0 < κ := h.pos
  have hB0 : 0 ≤ B := h.sqMoment_nonneg
  have hP : 0 < P := spreadOutWindowBound_pos h.pos hK
  have hθ0 : 0 ≤ θ := blackwellTheta_nonneg hB0 n
  have hA0 : 0 ≤ A := by
    rw [hAdef]
    unfold blackwellAmplification
    refine mul_nonneg (by positivity) (Finset.sum_nonneg fun m _ => ?_)
    exact (one_div_pos.mpr (minorConst_pos hκ hη m)).le
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hW0 : ∀ u, 0 ≤ W u := fun u => renewalWindow_nonneg ν x u
  have hWP : ∀ u, W u ≤ P := fun u =>
    h.renewalWindow_le_bound hx hxK u
  have hWlow : ∀ u, -P ≤ W u := fun u => by linarith [hW0 u, hP]
  have hUP : ∀ u, ladderRenewalMeasure ν (Ioc (u - x) u) ≤ ENNReal.ofReal P := fun u =>
    h.window_le_ofReal hx hxK u
  set ℓ : ℝ → ℝ := windowInf W with hℓdef
  have hℓ0 : ∀ β, 0 ≤ ℓ β := fun β => windowInf_nonneg hW0 β
  have hℓP : ∀ β, ℓ β ≤ P := fun β => windowInf_le_bound hW0 hWP β
  -- pigeonhole over the blocks
  obtain ⟨j, hjN, hjstep⟩ := exists_block_small_increase
    (f := fun j : ℕ => ℓ (β₀ + j * T)) (fun j => hℓ0 _) (fun j => hℓP _) hN
  set β : ℝ := β₀ + j * T with hβdef
  set β' : ℝ := β₀ + (j + 1 : ℕ) * T with hβ'def
  have hββ' : β' = β + T := by
    rw [hβ'def, hβdef]
    push_cast
    ring
  have hβ₀β : β₀ ≤ β := by
    rw [hβdef]
    have : (0 : ℝ) ≤ j * T := by positivity
    linarith
  have hstep : ℓ β' - ℓ β ≤ P / N := hjstep
  -- the near-infimum point
  set ϵ : ℝ := P / N with hϵdef
  have hϵ : 0 < ϵ := by positivity
  obtain ⟨bs, hbs, hWbs⟩ := exists_near_window_sInf hWlow β' hϵ
  have hbsβ : β ≤ bs := by linarith [hbs, hββ', hT]
  -- the deficit
  set S : ℝ := bs - β with hSdef
  have hTS : T ≤ S := by linarith [hbs, hββ']
  set Ψ : ℝ → ℝ := fun y => W (bs - y) - ℓ β with hΨdef
  have hΨmeas : Measurable Ψ := (measurable_renewalWindow_shift ν x bs).sub measurable_const
  have hΨP : ∀ y, Ψ y ≤ P := fun y => by
    show W (bs - y) - ℓ β ≤ P
    linarith [hℓ0 β, hWP (bs - y)]
  have hΨlow : ∀ y, -P ≤ Ψ y := fun y => by
    show -P ≤ W (bs - y) - ℓ β
    linarith [hℓP β, hW0 (bs - y)]
  have hΨnn : ∀ y, y ≤ S → 0 ≤ Ψ y := fun y hy => by
    show 0 ≤ W (bs - y) - ℓ β
    have : ℓ β ≤ W (bs - y) := windowInf_le hW0 (by linarith)
    linarith
  set D : ℝ := 2 * P / N + ((n : ℝ) + 1) * θ with hDdef
  have hΨint : ∀ m : ℕ, m < n + 1 → (∫ y, Ψ y ∂(measureConvPow ν (m + 1))) ≤ D := by
    intro m _hm
    have h := window_deficit_integral_eq ν hP.le hUP (m + 1) bs (ℓ β)
    have hneg : (∫ y, Ψ y ∂(measureConvPow ν (m + 1))) =
        -∫ y, (ℓ β - W (bs - y)) ∂(measureConvPow ν (m + 1)) := by
      rw [← integral_neg]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      show W (bs - y) - ℓ β = -(ℓ β - W (bs - y))
      ring
    rw [hneg, h]
    have hc : 0 ≤ ∑ i ∈ Finset.range (m + 1), (measureConvPow ν i (Ioc (bs - x) bs)).toReal :=
      Finset.sum_nonneg fun i _ => ENNReal.toReal_nonneg
    have hWbs' : W bs ≤ ℓ β' + ϵ := hWbs
    have hθ' : 0 ≤ ((n : ℝ) + 1) * θ := by positivity
    rw [hDdef]
    have : 2 * P / N = P / N + P / N := by ring
    rw [this]
    linarith
  -- the core estimate
  have hcore := h.deficit_integral_smoothing_le hK hη hη4 n m₀ hn hT hTS
    hΨmeas hΨP hΨlow hΨnn hΨint
  -- the stationary identity through the smoothing
  have hstat := h.integral_window_smoothing_sub_le hx hxK m₀ bs
  have htail : (measureConvPow ν m₀).real (Ioi (bs - K)) ≤ θ :=
    h.convPow_tail_le_theta hβ₀ n (by omega) (hβ₀β.trans hbsβ)
  have hstat' : x / μ0 - (∫ w, W (bs - w) ∂σ) ≤ (P + K / κ) * θ := by
    have h1 := (abs_le.mp hstat).1
    have h2 : (P + K / κ) * (measureConvPow ν m₀).real (Ioi (bs - K)) ≤ (P + K / κ) * θ :=
      mul_le_mul_of_nonneg_left htail (by positivity)
    linarith
  -- `∫ Ψ dσ = ∫ W(bs - ·) dσ - ℓ β`
  have hWint : Integrable (fun w => W (bs - w)) σ := by
    refine (integrable_const P).mono' (measurable_renewalWindow_shift ν x bs).aestronglyMeasurable ?_
    filter_upwards with w
    rw [Real.norm_eq_abs, abs_of_nonneg (hW0 _)]
    exact hWP _
  have hΨσ : (∫ y, Ψ y ∂σ) = (∫ w, W (bs - w) ∂σ) - ℓ β := by
    change (∫ y, (W (bs - y) - ℓ β) ∂σ) = _
    rw [integral_sub hWint (integrable_const _), integral_const, Measure.real, measure_univ,
      ENNReal.toReal_one, one_smul]
  have hΨΦ : (∫ y, Ψ y ∂σ) ≤ ∫ y, max (Ψ y) 0 ∂σ := by
    refine integral_mono ?_ ?_ fun y => le_max_left _ _
    · refine (integrable_const P).mono' hΨmeas.aestronglyMeasurable ?_
      filter_upwards with y
      rw [Real.norm_eq_abs, abs_le]
      exact ⟨hΨlow y, hΨP y⟩
    · refine (integrable_const P).mono' (hΨmeas.max measurable_const).aestronglyMeasurable ?_
      filter_upwards with y
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
      exact max_le (hΨP y) hP.le
  -- from `ℓ β` to `W b`
  have hWb : ℓ β ≤ W b := by
    have h1 : ℓ (β₀ + N * T) ≤ W b := windowInf_le hW0 hb
    have h2 : ℓ β ≤ ℓ (β₀ + N * T) := by
      refine windowInf_monotone hW0 ?_
      rw [hβdef]
      have : (j : ℝ) ≤ N := by exact_mod_cast hjN.le
      nlinarith
    exact h2.trans h1
  -- assemble
  have hmain : x / μ0 - ℓ β ≤ A * D + R₀ + (P + K / κ) * θ := by
    have : x / μ0 - ℓ β = (x / μ0 - (∫ w, W (bs - w) ∂σ)) + ∫ y, Ψ y ∂σ := by
      rw [hΨσ]
      ring
    rw [this]
    linarith
  unfold blackwellTotal
  change x / μ0 - W b ≤ A * D + R₀ + (P + K / κ) * θ
  linarith

/-! ## Blackwell's theorem -/

/-- **Blackwell's renewal theorem for a spread-out law**, uniform over window lengths in a
compact range. -/
theorem renewalWindow_uniform (h : SpreadOutLaw ν κ) {K ε : ℝ} (hK : 0 ≤ K) (hε : 0 < ε) :
    ∃ b₀ : ℝ, 0 < b₀ ∧ ∀ b : ℝ, b₀ ≤ b → ∀ x : ℝ, 0 ≤ x → x ≤ K →
      |(ladderRenewalMeasure ν (Ioc (b - x) b)).toReal - x / ladderMean ν| ≤ ε := by
  have hκ := h.pos
  have hP : 0 < spreadOutWindowBound κ K := spreadOutWindowBound_pos hκ hK
  obtain ⟨η, T, β₀, n, m₀, N, hη, hη4, hn, hm₀, hT, hβ₀, hN, htot⟩ :=
    exists_blackwellTotal_le (B := ∫ x, x ^ 2 ∂ν) hκ hP hK hε
  refine ⟨β₀ + N * T, ?_, fun b hb x hx hxK => ?_⟩
  · have hNT : (0 : ℝ) < (N : ℝ) * T := by
      have : (0 : ℝ) < N := by exact_mod_cast hN
      positivity
    linarith
  · have h1 := h.renewalWindow_sub_le_total hx hxK hη hη4 n m₀ hn hm₀ hT hβ₀ N hN hb
    have h2 := h.sub_renewalWindow_le_total hx hxK hη hη4 n m₀ hn hm₀ hT hβ₀ N hN hb
    unfold renewalWindow at h1 h2
    rw [abs_le]
    constructor <;> linarith

end SpreadOutLaw

end SwingRepair
