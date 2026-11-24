import PLAStochastic.Swing.Entrance.Local.LocalWindow
import PLAStochastic.Swing.Entrance.MarginCases
import PLAStochastic.Swing.Entrance.Mixture
import PLAStochastic.Swing.Entrance.Weights
import PLAStochastic.Swing.Entrance.Grid.Truncation
import PLAStochastic.Swing.Ladder.ZeroDrift.JointLimit
import PLAStochastic.Swing.SecondSegment.Coefficient.MarginLimit
import Mathlib.MeasureTheory.Measure.Portmanteau

/-! # The first-restart entrance law

**Theorem.**  For the native Swing filter on iid standard Gaussian increments, the law of the
first-restart margin `R_{1,E}` converges weakly, as `E → ∞`, to

`ρ = θ Law(-O) + (1 - θ) Law(-(U + O))`,

where `(U, O)` is the zero-drift ascending-ladder equilibrium age/residual pair and
`θ = P(I > 0)` for the Brownian selection area `I` at the first pinch.

**Proof.**  Fix a bounded Lipschitz test `g` and `ε > 0`.

* With high probability the adaptive cut lies in the truncation event `G` (E7).
* On `G`, conditionally on the past of the cut, the local residual crosses within the window and
  stays below `E/2` there, up to small probability (E11)–(E12). Its undershoot/overshoot pair
  is asymptotically independent of the past with law `π` (E16, with the renewal limit E15).
* On `G` with the window conditions, the margin is `-O` up to `M/E` when the area at the cut
  is positive beyond the deterministic error, and `-(U + O)` up to `M/E + w_E` when it is
  negative beyond the active threshold (E13, E17–E22, E26–E27).
* The two sign events have limiting probabilities `θ` and `1 - θ` (E20, E25).

Combining these in `abs_integral_sub_mixture_le` gives
`|E g(R_{1,E}) - (θ ∫ g(-o) dπ + (1 - θ) ∫ g(-(u + o)) dπ)| ≤ ε` for all large `E`.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace SwingRepair

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℝ} {μ : Measure Ω}

theorem measurable_nativeFirstMargin (hX : ∀ k, Measurable (X k)) (E : ℝ) :
    Measurable (nativeFirstMargin X E) :=
  measurable_const.sub ((nativeRestartNext_measurable (fun k => X (1 + k))
    (fun k => hX (1 + k)) E).comp ((hX 0).prodMk measurable_id)).abs

omit [MeasurableSpace Ω] in
theorem entranceGood_abs {y : ℕ → ℝ} {E δ M : ℝ} (h : entranceGood y E δ M) :
    entranceGood y E δ |M| := by
  obtain ⟨n, hn, h1, h2, h3, h4, h5⟩ := h
  exact ⟨n, hn, h1, h2.trans (mul_le_mul_of_nonneg_right (le_abs_self M) (sq_nonneg E)),
    h3.trans (le_abs_self M), h4, h5⟩

omit [MeasurableSpace Ω] in
theorem eventually_real_of_nnreal {P : ℝ → Prop} (h : ∀ᶠ E : ℝ≥0 in atTop, P (E : ℝ)) :
    ∀ᶠ E : ℝ in atTop, P E := by
  filter_upwards [tendsto_real_toNNReal_atTop.eventually h, eventually_ge_atTop 0] with E hE h0
  rwa [Real.coe_toNNReal E h0] at hE

/-- **The entrance limit against bounded Lipschitz tests.** -/
theorem tendsto_integral_nativeFirstMargin (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {g : ℝ → ℝ} (hg : Continuous g) {C L : ℝ}
    (hgC : ∀ x, |g x| ≤ C) (hL : 0 ≤ L) (hgL : ∀ x y, |g x - g y| ≤ L * |x - y|) :
    Tendsto (fun E : ℝ => ∫ ω, g (nativeFirstMargin X E ω) ∂μ) atTop
      (𝓝 (∫ x, g x ∂(entranceLaw X μ))) := by
  have hprob : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  set π := equilibriumPairLaw (gaussianAscendingLadderLaw X μ 0) with hπ
  set θ := entranceSelectionProb with hθ
  set a := ∫ p, g (-p.2) ∂π with ha
  set b := ∫ p, g (-(p.1 + p.2)) ∂π with hb
  rw [integral_entranceLaw hX hi hG hg hgC]
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hgC 0)
  set K : ℝ := 3 + 12 * C + 2 * |a| + 2 * |b| with hK
  have hKpos : 0 < K := by positivity
  rw [Metric.tendsto_nhds]
  intro ε hε
  set ε' := ε / (2 * K) with hε'def
  have hε' : 0 < ε' := by positivity
  -- the truncation event
  obtain ⟨δ, hδ, M₀, hgoodP⟩ :=
    entranceGood_prob_gaussian hX hi hG (ENNReal.ofReal_pos.mpr hε')
  set M := |M₀| with hMdef
  have hM : 0 ≤ M := abs_nonneg _
  have hgoodP' : ∀ᶠ E : ℝ in atTop,
      μ.real {ω | ¬ entranceGood (entrancePath X ω) E δ M} ≤ ε' := by
    filter_upwards [eventually_real_of_nnreal (P := fun E : ℝ =>
      μ {ξ | ¬ entranceGood (entrancePath X ξ) E δ M₀} ≤ ENNReal.ofReal ε') hgoodP] with E hE
    have hsub : {ω | ¬ entranceGood (entrancePath X ω) E δ M} ⊆
        {ω | ¬ entranceGood (entrancePath X ω) E δ M₀} := fun ω hω h => hω (entranceGood_abs h)
    rw [measureReal_def]
    exact ENNReal.toReal_le_of_le_ofReal hε'.le ((measure_mono hsub).trans hE)
  -- the local pair after the cut
  have hpair : ∀ g' : ℝ × ℝ → ℝ, Continuous g' → (∃ C', ∀ p, |g' p| ≤ C') →
      Tendsto (fun D : ℝ => ∫ ω, g' (zeroDriftUndershoot X D ω, zeroDriftOvershoot X D ω) ∂μ)
        atTop (𝓝 (∫ p, g' p ∂π)) :=
    fun g' hg' ⟨C', hC'⟩ => zeroDriftAgeResidual_tendsto_of_continuous hX hi hG hg' hC'
  have hg₁ : Continuous fun p : ℝ × ℝ => g (-p.2) := hg.comp continuous_snd.neg
  have hg₂ : Continuous fun p : ℝ × ℝ => g (-(p.1 + p.2)) :=
    hg.comp (continuous_fst.add continuous_snd).neg
  have hP₁ := entrancePair_conditional_limit hX hi hG hpair δ M hg₁ ⟨C, fun p => hgC _⟩ ε' hε'
  have hP₂ := entrancePair_conditional_limit hX hi hG hpair δ M hg₂ ⟨C, fun p => hgC _⟩ ε' hε'
  have hLate := entranceCrossing_late_conditional hX hi hG δ M ε' hε'
  have hMax := entranceLocal_max_conditional hX hi hG δ M ε' hε'
  -- the selection weights
  have hW₁ := (tendsto_entranceCutArea_sign hX hi hG (c := fun E : ℝ≥0 => entranceAreaError E M)
    ((tendsto_entranceAreaError M).comp (NNReal.tendsto_coe_atTop.mpr tendsto_id))).1
  have hW₂ := (tendsto_entranceCutArea_sign hX hi hG
    (c := fun E : ℝ≥0 => entranceActiveThreshold E δ M)
    ((tendsto_entranceActiveThreshold hδ M).comp (NNReal.tendsto_coe_atTop.mpr tendsto_id))).2
  have hS₁ : ∀ᶠ E : ℝ in atTop, |μ.real {ω | entranceAreaError E M <
      entranceCutArea E (fun k => X k ω)} - θ| ≤ ε' := by
    refine eventually_real_of_nnreal (P := fun E : ℝ => |μ.real {ω | entranceAreaError E M <
      entranceCutArea E (fun k => X k ω)} - θ| ≤ ε') ?_
    filter_upwards [hW₁.eventually (Metric.closedBall_mem_nhds θ hε')] with E hE
    rwa [Real.dist_eq] at hE
  have hS₂ : ∀ᶠ E : ℝ in atTop, |μ.real {ω | entranceCutArea E (fun k => X k ω) <
      -entranceActiveThreshold E δ M} - (1 - θ)| ≤ ε' := by
    refine eventually_real_of_nnreal (P := fun E : ℝ => |μ.real {ω |
      entranceCutArea E (fun k => X k ω) < -entranceActiveThreshold E δ M} - (1 - θ)| ≤ ε') ?_
    filter_upwards [hW₂.eventually (Metric.closedBall_mem_nhds (1 - θ) hε')] with E hE
    rwa [Real.dist_eq] at hE
  -- the deterministic errors
  have hη : Tendsto (fun E : ℝ => L * (M / E + entranceWidthError E δ)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun E : ℝ => M / E) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    simpa using (h1.add (tendsto_entranceWidthError hδ)).const_mul L
  have hηev := hη.eventually (Iic_mem_nhds hε')
  filter_upwards [hgoodP', hP₁, hP₂, hLate, hMax, hS₁, hS₂, hηev, eventually_ge_atTop 1,
    eventually_gt_atTop M] with E hgE hp1 hp2 hlate hmax hs1 hs2 hηE hE1 hME
  have hEpos : (0 : ℝ) < E := by linarith
  have hκ := entranceCutIndex_isStoppingTime hX E
  -- the events of the decomposition
  set Gs := {ω | entranceGood (entrancePath X ω) E δ M} with hGs
  set J : Ω → ℝ := fun ω =>
    entranceGridArea (entrancePath X ω) E (entranceCutNat (entrancePath X ω) E) with hJ
  set Sp := {ω | entranceAreaError E M < J ω} with hSp
  set Sm := {ω | J ω < -entranceActiveThreshold E δ M} with hSm
  set A := Gs ∩ Sp with hA
  set B := Gs ∩ Sm with hB
  set Late := {ω | (entranceWindow E : ℕ∞) < entranceCrossing (entrancePath X ω) E
    (entranceCutNat (entrancePath X ω) E)} with hLateDef
  set Mx := {ω | ∃ j ≤ entranceWindow E, E / 2 < |entranceLocal (entrancePath X ω) E
    (entranceCutNat (entrancePath X ω) E) j|} with hMxDef
  set Bad := Late ∪ Mx with hBad
  have hJσ : Measurable[entranceCutSigma hX E] J := measurable_entranceGridArea_cut hX E
  have hGσ : MeasurableSet[entranceCutSigma hX E] Gs := measurableSet_cutSigma_entranceGood hX E δ M
  have hAσ : MeasurableSet[entranceCutSigma hX E] A :=
    hGσ.inter (measurableSet_lt measurable_const hJσ)
  have hBσ : MeasurableSet[entranceCutSigma hX E] B :=
    hGσ.inter (measurableSet_lt hJσ measurable_const)
  have hAm : MeasurableSet A := hκ.measurableSpace_le _ hAσ
  have hBm : MeasurableSet B := hκ.measurableSpace_le _ hBσ
  have hAG : A ⊆ Gs := inter_subset_left
  have hBG : B ⊆ Gs := inter_subset_left
  have harea0 : 0 ≤ entranceAreaError E M := by
    unfold entranceAreaError
    have : (0 : ℝ) ≤ entranceWindow E := Nat.cast_nonneg _
    positivity
  have hact0 : 0 ≤ entranceActiveThreshold E δ M := by
    unfold entranceActiveThreshold entranceWidthError
    have : (0 : ℝ) ≤ entranceWindow E := Nat.cast_nonneg _
    have := entranceCutLevel_pos hEpos
    positivity
  have hdisj : Disjoint A B := by
    rw [Set.disjoint_left]
    intro ω hωA hωB
    have h1 : entranceAreaError E M < J ω := hωA.2
    have h2 : J ω < -entranceActiveThreshold E δ M := hωB.2
    linarith
  -- integrability of the local pair
  have hVint : IntegrableOn (fun ω => g (-entranceOvershoot (entrancePath X ω) E
      (entranceCutNat (entrancePath X ω) E))) A μ :=
    entrancePair_integrableOn hX hg₁.measurable (fun p => hgC _) hEpos hAm hAG
  have hWint : IntegrableOn (fun ω => g (-(entranceUndershoot (entrancePath X ω) E
      (entranceCutNat (entrancePath X ω) E) + entranceOvershoot (entrancePath X ω) E
      (entranceCutNat (entrancePath X ω) E)))) B μ :=
    entrancePair_integrableOn hX hg₂.measurable (fun p => hgC _) hEpos hBm hBG
  -- the pointwise description outside the bad set
  have hlocal : ∀ ω ∈ Gs, ω ∉ Bad → ∃ n T : ℕ, entranceCut (entrancePath X ω) E = n ∧
      entranceCutNat (entrancePath X ω) E = n ∧ entranceCrossing (entrancePath X ω) E n = T ∧
      T ≤ entranceWindow E ∧
      ∀ j ≤ entranceWindow E, |entranceLocal (entrancePath X ω) E n j| ≤ E / 2 := by
    intro ω hωG hωB
    obtain ⟨n, hcut, -⟩ := hωG
    have hn := entranceCutNat_of_eq hcut
    have hnl : ¬ (entranceWindow E : ℕ∞) < entranceCrossing (entrancePath X ω) E
        (entranceCutNat (entrancePath X ω) E) := fun h => hωB (Or.inl h)
    have hnm : ¬ ∃ j ≤ entranceWindow E, E / 2 < |entranceLocal (entrancePath X ω) E
        (entranceCutNat (entrancePath X ω) E) j| := fun h => hωB (Or.inr h)
    rw [hn] at hnl hnm
    push Not at hnl hnm
    obtain ⟨T, hT⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_le_ne_top (ENat.natCast_ne_top _) hnl)
    refine ⟨n, T, hcut, hn, hT.symm, ?_, hnm⟩
    rw [← hT] at hnl
    exact_mod_cast hnl
  have hAη : ∀ ω ∈ A, ω ∉ Bad → |nativeFirstMargin X E ω -
      -entranceOvershoot (entrancePath X ω) E (entranceCutNat (entrancePath X ω) E)| ≤
        M / E + entranceWidthError E δ := by
    intro ω hωA hωB
    obtain ⟨n, T, hcut, hn, hT, hTq, hQ⟩ := hlocal ω (hAG hωA) hωB
    have h := (nativeFirstMargin_selection_cases hE1 hME hδ (hAG hωA) hcut hT hTq hQ).1
    have hJω : entranceAreaError E M < entranceGridArea (entrancePath X ω) E n := by
      have := hωA.2
      simp only [hSp, hJ, mem_ofPred_eq, hn] at this
      exact this
    rw [hn]
    have hw : 0 ≤ entranceWidthError E δ := by
      unfold entranceWidthError
      have : (0 : ℝ) ≤ entranceWindow E := Nat.cast_nonneg _
      have := entranceCutLevel_pos hEpos
      positivity
    linarith [h hJω]
  have hBη : ∀ ω ∈ B, ω ∉ Bad → |nativeFirstMargin X E ω -
      -(entranceUndershoot (entrancePath X ω) E (entranceCutNat (entrancePath X ω) E) +
        entranceOvershoot (entrancePath X ω) E (entranceCutNat (entrancePath X ω) E))| ≤
        M / E + entranceWidthError E δ := by
    intro ω hωB' hωB
    obtain ⟨n, T, hcut, hn, hT, hTq, hQ⟩ := hlocal ω (hBG hωB') hωB
    have h := (nativeFirstMargin_selection_cases hE1 hME hδ (hBG hωB') hcut hT hTq hQ).2
    have hJω : entranceGridArea (entrancePath X ω) E n < -entranceActiveThreshold E δ M := by
      have := hωB'.2
      simp only [hSm, hJ, mem_ofPred_eq, hn] at this
      exact this
    rw [hn]
    exact h hJω
  have hηnn : 0 ≤ M / E + entranceWidthError E δ := by
    unfold entranceWidthError
    have : (0 : ℝ) ≤ entranceWindow E := Nat.cast_nonneg _
    have := entranceCutLevel_pos hEpos
    positivity
  have hmix := abs_integral_sub_mixture_le (μ := μ) hg hgC hgL hL
    (measurable_nativeFirstMargin hX E) hAm hBm hdisj hVint hWint hηnn hAη hBη a b
  -- the conditional estimates on `A` and `B`
  have hpA : |∫ ω in A, g (-entranceOvershoot (entrancePath X ω) E
      (entranceCutNat (entrancePath X ω) E)) ∂μ - μ.real A * a| ≤ ε' := hp1 A hAσ hAG
  have hpB : |∫ ω in B, g (-(entranceUndershoot (entrancePath X ω) E
      (entranceCutNat (entrancePath X ω) E) + entranceOvershoot (entrancePath X ω) E
      (entranceCutNat (entrancePath X ω) E))) ∂μ - μ.real B * b| ≤ ε' := hp2 B hBσ hBG
  have hA1 : μ.real A ≤ 1 := measureReal_le_one
  have hB1 : μ.real B ≤ 1 := measureReal_le_one
  have hbadA : μ.real (A ∩ Bad) ≤ 2 * ε' := by
    have h1 := hlate A hAσ hAG
    have h2 := hmax A hAσ hAG
    calc μ.real (A ∩ Bad) = μ.real ((A ∩ Late) ∪ (A ∩ Mx)) := by rw [inter_union_distrib_left]
      _ ≤ μ.real (A ∩ Late) + μ.real (A ∩ Mx) := measureReal_union_le _ _
      _ ≤ ε' * μ.real A + ε' * μ.real A := add_le_add h1 h2
      _ ≤ 2 * ε' := by nlinarith [measureReal_nonneg (μ := μ) (s := A)]
  have hbadB : μ.real (B ∩ Bad) ≤ 2 * ε' := by
    have h1 := hlate B hBσ hBG
    have h2 := hmax B hBσ hBG
    calc μ.real (B ∩ Bad) = μ.real ((B ∩ Late) ∪ (B ∩ Mx)) := by rw [inter_union_distrib_left]
      _ ≤ μ.real (B ∩ Late) + μ.real (B ∩ Mx) := measureReal_union_le _ _
      _ ≤ ε' * μ.real B + ε' * μ.real B := add_le_add h1 h2
      _ ≤ 2 * ε' := by nlinarith [measureReal_nonneg (μ := μ) (s := B)]
  -- the weights of `A` and `B`
  have hGc : μ.real Gsᶜ ≤ ε' := hgE
  have hwA : |μ.real A - θ| ≤ 2 * ε' := by
    have h1 : μ.real A ≤ μ.real Sp := measureReal_mono inter_subset_right
    have h2 : μ.real Sp ≤ μ.real A + μ.real Gsᶜ := by
      calc μ.real Sp ≤ μ.real (A ∪ Gsᶜ) := measureReal_mono fun ω hω => by
            by_cases h : ω ∈ Gs
            · exact Or.inl ⟨h, hω⟩
            · exact Or.inr h
        _ ≤ μ.real A + μ.real Gsᶜ := measureReal_union_le _ _
    have h3 : |μ.real Sp - θ| ≤ ε' := hs1
    rw [abs_le] at h3 ⊢
    constructor <;> linarith
  have hwB : |μ.real B - (1 - θ)| ≤ 2 * ε' := by
    have h1 : μ.real B ≤ μ.real Sm := measureReal_mono inter_subset_right
    have h2 : μ.real Sm ≤ μ.real B + μ.real Gsᶜ := by
      calc μ.real Sm ≤ μ.real (B ∪ Gsᶜ) := measureReal_mono fun ω hω => by
            by_cases h : ω ∈ Gs
            · exact Or.inl ⟨h, hω⟩
            · exact Or.inr h
        _ ≤ μ.real B + μ.real Gsᶜ := measureReal_union_le _ _
    have h3 : |μ.real Sm - (1 - θ)| ≤ ε' := hs2
    rw [abs_le] at h3 ⊢
    constructor <;> linarith
  -- assembly
  have hta : |μ.real A - θ| * |a| ≤ 2 * ε' * |a| := mul_le_mul_of_nonneg_right hwA (abs_nonneg a)
  have htb : |μ.real B - (1 - θ)| * |b| ≤ 2 * ε' * |b| :=
    mul_le_mul_of_nonneg_right hwB (abs_nonneg b)
  have hsplit : |∫ ω, g (nativeFirstMargin X E ω) ∂μ - (θ * a + (1 - θ) * b)| ≤
      |∫ ω, g (nativeFirstMargin X E ω) ∂μ - (μ.real A * a + μ.real B * b)| +
        |μ.real A - θ| * |a| + |μ.real B - (1 - θ)| * |b| := by
    calc |∫ ω, g (nativeFirstMargin X E ω) ∂μ - (θ * a + (1 - θ) * b)|
        = |(∫ ω, g (nativeFirstMargin X E ω) ∂μ - (μ.real A * a + μ.real B * b)) +
            ((μ.real A - θ) * a + (μ.real B - (1 - θ)) * b)| := by ring_nf
      _ ≤ |∫ ω, g (nativeFirstMargin X E ω) ∂μ - (μ.real A * a + μ.real B * b)| +
            (|(μ.real A - θ) * a| + |(μ.real B - (1 - θ)) * b|) :=
          (abs_add_le _ _).trans (add_le_add_right (abs_add_le _ _) _)
      _ = _ := by rw [abs_mul, abs_mul]; ring
  have hrest : 1 - μ.real A - μ.real B ≤ 4 * ε' := by
    rw [abs_le] at hwA hwB
    linarith
  have hfin : |∫ ω, g (nativeFirstMargin X E ω) ∂μ - (θ * a + (1 - θ) * b)| ≤ ε' * K := by
    have hCbad : 2 * C * (μ.real (A ∩ Bad) + μ.real (B ∩ Bad)) ≤ 2 * C * (4 * ε') := by
      gcongr; linarith
    have hCrest : C * (1 - μ.real A - μ.real B) ≤ C * (4 * ε') := by gcongr
    rw [hK]
    linarith
  rw [Real.dist_eq]
  calc |∫ ω, g (nativeFirstMargin X E ω) ∂μ - (θ * a + (1 - θ) * b)| ≤ ε' * K := hfin
    _ = ε / 2 := by rw [hε'def]; field_simp
    _ < ε := half_lt_self hε

/-- **The first-restart entrance law.**  The laws of the first-restart margins `R_{1,E}`
converge weakly to `ρ = θ Law(-O) + (1 - θ) Law(-(U + O))` as `E → ∞`. -/
theorem nativeTransientMarginProb_tendsto_entranceLaw (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) :
    let _ : IsProbabilityMeasure μ := hi.isProbabilityMeasure
    Tendsto (fun E : ℝ => nativeTransientMarginProb μ hX E 1) atTop
      (𝓝 (⟨entranceLaw X μ, entranceLaw_isProbabilityMeasure hX hi hG⟩ : ProbabilityMeasure ℝ)) := by
  intro _
  refine tendsto_iff_forall_lipschitz_integral_tendsto.mpr ?_
  intro g ⟨C, hC⟩ ⟨K, hK⟩
  have hgC : ∀ x, |g x| ≤ |g 0| + C := fun x => by
    have := hC x 0
    rw [Real.dist_eq] at this
    calc |g x| = |(g x - g 0) + g 0| := by ring_nf
      _ ≤ |g x - g 0| + |g 0| := abs_add_le _ _
      _ ≤ |g 0| + C := by linarith
  have hgL : ∀ x y, |g x - g y| ≤ (K : ℝ) * |x - y| := fun x y => by
    have := hK.dist_le_mul x y
    rwa [Real.dist_eq, Real.dist_eq] at this
  refine (tendsto_integral_nativeFirstMargin hX hi hG hK.continuous hgC K.coe_nonneg hgL).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with E hE
  rw [nativeTransientMarginProb_coe, ← map_nativeFirstMargin_eq_transientMarginLaw hX hi hG hE,
    integral_map (measurable_nativeFirstMargin hX E).aemeasurable
      hK.continuous.aestronglyMeasurable]

end

end SwingRepair
