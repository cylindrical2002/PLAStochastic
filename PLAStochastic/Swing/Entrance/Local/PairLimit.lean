import PLAStochastic.Swing.Entrance.Local.Freezing
import PLAStochastic.Swing.Entrance.Local.WindowEstimates
import PLAStochastic.Swing.Entrance.Local.Rates

/-!
# The local pair after the cut forgets the past (E16)

Let `π` be the limit law of the zero-drift pair, in the sense of the hypothesis `hpair`:
for every bounded continuous `g`, `E g(U_D, O_D) → ∫ g dπ` as `D → ∞`, where `(U_D, O_D)` is
the undershoot/overshoot of the zero-drift Gaussian walk at the level `D`
(`zeroDriftUndershoot`, `zeroDriftOvershoot`). This is the joint age/residual renewal limit
(E15) proved separately.

Given the stopped σ-algebra `𝓕_τ` of the cut, the local residual is the Gaussian walk with
the frozen drift `-b`, `b = s β`, started below the frozen width `D`. On the truncation event
`entranceGood E δ M` one has `D ∈ [d_E/2, d_E]` and `|b| ≤ M/E`, and then

* the drift is invisible on the window `q_E` (E10, Cameron–Martin),
* the crossing happens within the window (E11, ballot),
* the zero-drift pair is close to `π` because `D ≥ d_E/2 → ∞` (`hpair`).

Main statement (`entrancePair_conditional_limit`): for every bounded continuous `g` and every
`ε > 0`, for all large `E` and every `𝓕_τ`-event `A ⊆ entranceGood E δ M`,

`|∫_A g(U_E, O_E) dμ - μ(A) ∫ g dπ| ≤ ε`.
-/

namespace SwingRepair

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

omit [MeasurableSpace Ω] in
/-- On the truncation event the cut is finite, the frozen width lies in `[d_E/2, d_E]` and the
frozen drift is at most `M/E`. -/
theorem entranceGood_cut_bounds {E δ M : ℝ} (hE : 0 < E) {ω : Ω}
    (hg : entranceGood (entrancePath X ω) E δ M) :
    entranceCutIndex X E ω ≠ ⊤ ∧ entranceCutLevel E / 2 ≤ entranceCutWidth X E ω ∧
      entranceCutWidth X E ω ≤ entranceCutLevel E ∧ |entranceCutDrift X E ω| ≤ M / E := by
  obtain ⟨hne, -, -, hβ, hD1, hD2⟩ := (entranceGood_iff _ E δ M).mp hg
  refine ⟨fun h => hne ((entranceCutIndex_eq_top_iff X E ω).mp h), hD1, hD2, ?_⟩
  have hs : |entranceCutSide X E ω| = 1 := by
    rcases entranceSide_eq_one_or (y := entrancePath X ω) (E := E) (entranceCutNat (entrancePath X ω) E)
      with h | h
    · simp [entranceCutSide, h]
    · simp [entranceCutSide, h]
  rw [entranceCutDrift, abs_mul, hs, one_mul, le_div_iff₀ hE, mul_comm]
  rwa [abs_mul, abs_of_pos hE] at hβ

/-- On a measurable subset of the truncation event, a bounded measurable function of the actual
local pair `(U_E, O_E)` at the cut is integrable: there the pair is the crossing pair of the
frozen width, the frozen drift and the reflected future, a measurable function of `ω`. -/
theorem entrancePair_integrableOn [IsFiniteMeasure μ] (hX : ∀ n, Measurable (X n))
    {g : ℝ × ℝ → ℝ} (hg : Measurable g) {C : ℝ} (hC : ∀ p, |g p| ≤ C) {E δ M : ℝ} (hE : 0 < E)
    {A : Set Ω} (hA : MeasurableSet A)
    (hAgood : A ⊆ {ω | entranceGood (entrancePath X ω) E δ M}) :
    IntegrableOn (fun ω =>
      g (entranceUndershoot (entrancePath X ω) E (entranceCutNat (entrancePath X ω) E),
        entranceOvershoot (entrancePath X ω) E (entranceCutNat (entrancePath X ω) E))) A μ := by
  have hκ := entranceCutIndex_isStoppingTime hX E
  have hZm : Measurable fun ω => (entranceCutWidth X E ω, entranceCutDrift X E ω) :=
    ((measurable_entranceCutWidth hX E).prodMk (measurable_entranceCutDrift hX E)).mono
      hκ.measurableSpace_le le_rfl
  have hF : Measurable fun ω => g (crossingPair (entranceCutWidth X E ω) (entranceCutDrift X E ω)
      (entranceReflectedFuture X E ω)) :=
    hg.comp (measurable_crossingPair.comp (hZm.prodMk (measurable_entranceReflectedFuture hX E)))
  have hI : Integrable (fun ω => g (crossingPair (entranceCutWidth X E ω)
      (entranceCutDrift X E ω) (entranceReflectedFuture X E ω))) μ :=
    Integrable.of_bound hF.aestronglyMeasurable C
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hC _)
  refine hI.integrableOn.congr_fun (fun ω hω => ?_) hA
  rw [entrancePair_eq_crossingPair (entranceGood_cut_bounds hE (hAgood hω)).1]

/-- The window error of a drift `|b| ≤ M/E` is at most that of `M/E`. -/
theorem driftError_mono {b M E : ℝ} (hb : |b| ≤ M / E) (q : ℕ) :
    2 * |b| * q * gaussianAbsMean + q * b ^ 2 ≤
      2 * (M / E) * q * gaussianAbsMean + q * (M / E) ^ 2 := by
  have hK := gaussianAbsMean_nonneg
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hb2 : b ^ 2 ≤ (M / E) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg b) hb 2
  have h1 : 2 * |b| * q * gaussianAbsMean ≤ 2 * (M / E) * q * gaussianAbsMean := by
    have := mul_le_mul_of_nonneg_right hb (mul_nonneg hq hK)
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hb2 hq]

/-- For large `E` the probability that the zero-drift walk does not cross a level
`D ≤ d_E` within the window is small. -/
theorem eventually_zeroDrift_late_le (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {t : ℝ} (ht : 0 < t) :
    ∀ᶠ E in atTop, ∀ D, D ≤ entranceCutLevel E →
      μ.real {ω | (entranceWindow E : ℕ∞) < zeroDriftCrossing X D ω} ≤ t := by
  have := hi.isProbabilityMeasure
  have hrate := tendsto_entranceBallotRate.const_mul gaussianBallotConstant
  rw [mul_zero] at hrate
  filter_upwards [hrate.eventually (Iic_mem_nhds ht), eventually_ge_atTop 1] with E hE hE1 D hD
  have hd0 : 0 ≤ entranceCutLevel E := Real.rpow_nonneg (by linarith) _
  calc μ.real {ω | (entranceWindow E : ℕ∞) < zeroDriftCrossing X D ω}
      ≤ μ.real {ω | (entranceWindow E : ℕ∞) < zeroDriftCrossing X (entranceCutLevel E) ω} :=
        measureReal_mono (zeroDrift_late_mono hD _)
    _ ≤ gaussianBallotConstant * (entranceCutLevel E + 1) *
          (Real.sqrt (entranceWindow E))⁻¹ :=
        zeroDrift_late_le hX hi hG hd0 (entranceWindow_pos hE1)
    _ ≤ t := by rw [mul_assoc]; exact hE

/-- Uniform version of (E10)–(E15): the drifted crossing pair at levels `D ∈ [d_E/2, d_E]` with
drifts `|b| ≤ M/E` has expectations uniformly close to `∫ g dπ`. -/
theorem crossingPair_uniform_limit (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {g : ℝ × ℝ → ℝ} (hg : Measurable g) {C : ℝ}
    (hC : ∀ p, |g p| ≤ C) {c : ℝ}
    (hlim : Tendsto (fun D : ℝ => ∫ ω, g (zeroDriftUndershoot X D ω, zeroDriftOvershoot X D ω) ∂μ)
      atTop (𝓝 c))
    (M : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ E in atTop, ∀ D b : ℝ, entranceCutLevel E / 2 ≤ D → D ≤ entranceCutLevel E →
      |b| ≤ M / E → |∫ η, g (crossingPair D b (fun j => X j η)) ∂μ - c| ≤ ε := by
  have := hi.isProbabilityMeasure
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  set t := ε / (8 * (C + 1)) with ht
  have htpos : 0 < t := by positivity
  have h8 : 8 * (C + 1) * t = ε := by rw [ht]; field_simp
  have h1 : ∀ᶠ D in atTop,
      |∫ ω, g (zeroDriftUndershoot X D ω, zeroDriftOvershoot X D ω) ∂μ - c| ≤ ε / 2 := by
    filter_upwards [hlim.eventually (Metric.closedBall_mem_nhds c (half_pos hε))] with D hD
    simpa only [Metric.mem_closedBall, Real.dist_eq] using hD
  obtain ⟨D0, hD0⟩ := eventually_atTop.mp h1
  have h2 : ∀ᶠ E in atTop, D0 ≤ entranceCutLevel E / 2 := by
    filter_upwards [tendsto_entranceCutLevel.eventually (eventually_ge_atTop (2 * D0))] with E hE
    linarith
  have h3 : ∀ᶠ E in atTop, 2 * (M / E) * entranceWindow E * gaussianAbsMean +
      entranceWindow E * (M / E) ^ 2 ≤ t :=
    (tendsto_entranceDriftError M gaussianAbsMean).eventually (Iic_mem_nhds htpos)
  filter_upwards [h2, h3, eventually_zeroDrift_late_le hX hi hG htpos] with E hE2 hE3 hE4
    D b hD1 hD2 hb
  have hcomp := crossingPair_drift_le hX hi hG hg hC D b (entranceWindow E)
  have herr := (driftError_mono hb (entranceWindow E)).trans hE3
  have hP0 := hE4 D hD2
  have hlimD := hD0 D (hE2.trans hD1)
  have hsum : 2 * C * ((2 * |b| * (entranceWindow E : ℝ) * gaussianAbsMean +
      (entranceWindow E : ℝ) * b ^ 2) +
      μ.real {ω | (entranceWindow E : ℕ∞) < zeroDriftCrossing X D ω}) ≤ ε / 2 := by
    have : 2 * C * ((2 * |b| * (entranceWindow E : ℝ) * gaussianAbsMean +
        (entranceWindow E : ℝ) * b ^ 2) +
        μ.real {ω | (entranceWindow E : ℕ∞) < zeroDriftCrossing X D ω}) ≤ 2 * C * (2 * t) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    nlinarith
  calc |∫ η, g (crossingPair D b (fun j => X j η)) ∂μ - c|
      ≤ |∫ η, g (crossingPair D b (fun j => X j η)) ∂μ -
          ∫ ω, g (zeroDriftUndershoot X D ω, zeroDriftOvershoot X D ω) ∂μ| +
        |∫ ω, g (zeroDriftUndershoot X D ω, zeroDriftOvershoot X D ω) ∂μ - c| :=
          abs_sub_le _ _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add (hcomp.trans hsum) hlimD
    _ = ε := add_halves ε

/-- **(E16)** Conditional limit of the local pair after the cut. Assume the zero-drift pair
converges to `π` against bounded continuous test functions (`hpair`, the renewal limit (E15)).
Then for every bounded continuous `g` and `ε > 0`, for all large `E`, every event `A` of the
stopped σ-algebra of the cut contained in the truncation event satisfies
`|∫_A g(U_E, O_E) dμ - μ(A) ∫ g dπ| ≤ ε`, where `(U_E, O_E)` is the actual undershoot/overshoot
of the local residual at the cut. -/
theorem entrancePair_conditional_limit (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {π : Measure (ℝ × ℝ)}
    (hpair : ∀ g : ℝ × ℝ → ℝ, Continuous g → (∃ C, ∀ p, |g p| ≤ C) →
      Tendsto (fun D : ℝ => ∫ ω, g (zeroDriftUndershoot X D ω, zeroDriftOvershoot X D ω) ∂μ)
        atTop (𝓝 (∫ p, g p ∂π)))
    (δ M : ℝ) {g : ℝ × ℝ → ℝ} (hg : Continuous g) (hgb : ∃ C, ∀ p, |g p| ≤ C) :
    ∀ ε > 0, ∀ᶠ E in atTop, ∀ A : Set Ω, MeasurableSet[entranceCutSigma hX E] A →
      A ⊆ {ω | entranceGood (entrancePath X ω) E δ M} →
      |∫ ω in A, g (entranceUndershoot (entrancePath X ω) E (entranceCutNat (entrancePath X ω) E),
          entranceOvershoot (entrancePath X ω) E (entranceCutNat (entrancePath X ω) E)) ∂μ -
        μ.real A * ∫ p, g p ∂π| ≤ ε := by
  intro ε hε
  have := hi.isProbabilityMeasure
  obtain ⟨C, hC⟩ := hgb
  set c := ∫ p, g p ∂π
  have hunif := crossingPair_uniform_limit hX hi hG hg.measurable hC (hpair g hg ⟨C, hC⟩) M hε
  filter_upwards [hunif, eventually_gt_atTop 0] with E hE hEpos A hA hAgood
  have hκ := entranceCutIndex_isStoppingTime hX E
  have hAm : MeasurableSet A := hκ.measurableSpace_le _ hA
  set Z : Ω → ℝ × ℝ := fun ω => (entranceCutWidth X E ω, entranceCutDrift X E ω)
  have hZ : Measurable[entranceCutSigma hX E] Z :=
    (measurable_entranceCutWidth hX E).prodMk (measurable_entranceCutDrift hX E)
  set G : (ℝ × ℝ) × (ℕ → ℝ) → ℝ := fun r => g (crossingPair r.1.1 r.1.2 r.2) - c
  have hGm : Measurable G := (hg.measurable.comp measurable_crossingPair).sub_const c
  have hGb : ∀ r, |G r| ≤ C + |c| := fun r =>
    (abs_sub _ _).trans (by linarith [hC (crossingPair r.1.1 r.1.2 r.2)])
  have hfreeze := entrance_setIntegral_freeze hX hi hG hEpos.le hZ hGm hGb hA
  have hpairA : ∀ ω ∈ A,
      g (entranceUndershoot (entrancePath X ω) E (entranceCutNat (entrancePath X ω) E),
        entranceOvershoot (entrancePath X ω) E (entranceCutNat (entrancePath X ω) E)) =
        G (Z ω, entranceReflectedFuture X E ω) + c := by
    intro ω hω
    rw [entrancePair_eq_crossingPair (entranceGood_cut_bounds hEpos (hAgood hω)).1]
    simp only [G, Z, sub_add_cancel]
  have hint := entrancePair_integrableOn (μ := μ) hX hg.measurable hC hEpos hAm hAgood
  have hΦ : ∀ ω ∈ A, ‖∫ η, G (Z ω, fun j => X j η) ∂μ‖ ≤ ε := by
    intro ω hω
    obtain ⟨-, hD1, hD2, hb⟩ := entranceGood_cut_bounds hEpos (hAgood hω)
    have hgi : Integrable (fun η => g (crossingPair (Z ω).1 (Z ω).2 (fun j => X j η))) μ :=
      Integrable.of_bound ((hg.measurable.comp (measurable_crossingPair_fixed _ _)).comp
        (measurable_pi_lambda _ hX)).aestronglyMeasurable C
        (ae_of_all _ fun η => by rw [Real.norm_eq_abs]; exact hC _)
    have heq : ∫ η, G (Z ω, fun j => X j η) ∂μ =
        ∫ η, g (crossingPair (Z ω).1 (Z ω).2 (fun j => X j η)) ∂μ - c := by
      simp only [G]
      rw [integral_sub hgi (integrable_const c), integral_const, probReal_univ, one_smul]
    rw [heq, Real.norm_eq_abs]
    exact hE _ _ hD1 hD2 hb
  calc |∫ ω in A, g (entranceUndershoot (entrancePath X ω) E (entranceCutNat (entrancePath X ω) E),
          entranceOvershoot (entrancePath X ω) E (entranceCutNat (entrancePath X ω) E)) ∂μ -
        μ.real A * c|
      = |∫ ω in A, G (Z ω, entranceReflectedFuture X E ω) ∂μ| := by
        rw [← smul_eq_mul, ← setIntegral_const c, ← integral_sub hint integrableOn_const]
        congr 1
        refine setIntegral_congr_fun hAm fun ω hω => ?_
        rw [hpairA ω hω]
        ring
    _ = ‖∫ ω in A, ∫ η, G (Z ω, fun j => X j η) ∂μ ∂μ‖ := by rw [hfreeze, Real.norm_eq_abs]
    _ ≤ ε * μ.real A := norm_setIntegral_le_of_norm_le_const (measure_lt_top _ _) hΦ
    _ ≤ ε := mul_le_of_le_one_right hε.le measureReal_le_one

end

end SwingRepair
