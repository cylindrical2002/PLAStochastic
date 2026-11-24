import PLAStochastic.Swing.ConstantEvaluation.Fluctuation.OvershootMeanIdentity
import PLAStochastic.Swing.ConstantEvaluation.Fluctuation.DriftTilt
import PLAStochastic.Swing.ConstantEvaluation.Fluctuation.GaussianLogSeries

/-! # Stochastic monotonicity of `𝖡(a)` (roadmap 1.4, assembly)

With `Y_a = X_0 + a + I'_a` (`ladderDualVariable`) and `p_a = μ(posWalkSet X a)`:

* **Tilt + duality.**  `∫ g(X_0, I'_b) dμ = (∑_m ∫_{E_m(b)} g(X_0, S'_m)) · p_b`
  (`lintegral_shiftInf_eq_tsum_mul`), and the bracket is antitone in `b`
  (`lintegral_weakDescent_antitone`), so `p_a ∫ g(X_0, I'_c) ≤ p_c ∫ g(X_0, I'_a)` for
  `0 < a ≤ c` (`lintegral_shiftInf_antitone`).
* **CDF.**  For `r ≤ a`, `𝖡(a)(-∞, r] = 𝔼(Y_a - (a - r))₊ / a` (`swingOvershootMeasure_Iic`);
  for `r ≥ a` it is `1`.
* **Spitzer.**  `p_c · a ≤ p_a · c` (`exp_neg_spitzerExponent_mul_le` with
  `measure_posWalkSet_eq_spitzer`).

Since `Y_c - (c - r) = X_0 + r + I'_c`, the tilt bound with `g_r(x, i) = (x + r + i)₊` and the
Spitzer bound give `𝖡(c)(-∞, r] ≤ 𝖡(a)(-∞, r]`.  Both laws are atomless, so all tails are
ordered and every monotone integrable observable is ordered (`stochasticallyLE_of_tails`,
layer cake).  Conclusion: `OvershootStochasticMonotone X μ`.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
namespace SwingRepair
open Fluctuation

/-! ### Stochastic order from ordered tails -/

section StochasticOrder

variable {ν₁ ν₂ : Measure ℝ}

/-- An upper set of `ℝ` is `∅`, `univ`, `Ioi s` or `Ici s`; its measure is therefore ordered
whenever the two tail families are. -/
theorem measure_le_of_isUpperSet [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂]
    (hIoi : ∀ r, ν₁ (Ioi r) ≤ ν₂ (Ioi r)) (hIci : ∀ r, ν₁ (Ici r) ≤ ν₂ (Ici r))
    {U : Set ℝ} (hU : IsUpperSet U) : ν₁ U ≤ ν₂ U := by
  rcases U.eq_empty_or_nonempty with hUe | hUne
  · simp [hUe]
  by_cases hbdd : BddBelow U
  · set s := sInf U with hs
    have hIoi_sub : Ioi s ⊆ U := by
      intro x hx
      obtain ⟨u, hu, hux⟩ := exists_lt_of_csInf_lt hUne hx
      exact hU hux.le hu
    have hsub_Ici : U ⊆ Ici s := fun u hu => csInf_le hbdd hu
    by_cases hsU : s ∈ U
    · have : U = Ici s := by
        refine Subset.antisymm hsub_Ici fun x hx => ?_
        rcases eq_or_lt_of_le (mem_Ici.mp hx) with h | h
        · rw [← h]; exact hsU
        · exact hIoi_sub h
      rw [this]; exact hIci s
    · have : U = Ioi s := by
        refine Subset.antisymm (fun x hx => ?_) hIoi_sub
        rcases eq_or_lt_of_le (mem_Ici.mp (hsub_Ici hx)) with h | h
        · exact absurd (h ▸ hx) hsU
        · exact h
      rw [this]; exact hIoi s
  · have : U = univ := by
      refine eq_univ_of_forall fun x => ?_
      obtain ⟨y, hy, hyx⟩ := not_bddBelow_iff.mp hbdd x
      exact hU hyx.le hy
    rw [this, measure_univ, measure_univ]

theorem measure_le_of_isLowerSet [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂]
    (hIoi : ∀ r, ν₁ (Ioi r) ≤ ν₂ (Ioi r)) (hIci : ∀ r, ν₁ (Ici r) ≤ ν₂ (Ici r))
    {L : Set ℝ} (hL : IsLowerSet L) (hLm : MeasurableSet L) : ν₂ L ≤ ν₁ L := by
  have hc := measure_le_of_isUpperSet hIoi hIci hL.compl
  have h1 : ν₁ L = 1 - ν₁ Lᶜ := by rw [← prob_compl_eq_one_sub hLm.compl, compl_compl]
  have h2 : ν₂ L = 1 - ν₂ Lᶜ := by rw [← prob_compl_eq_one_sub hLm.compl, compl_compl]
  rw [h1, h2]
  exact tsub_le_tsub_left hc 1

theorem ofReal_max_zero (y : ℝ) : ENNReal.ofReal (max y 0) = ENNReal.ofReal y := by
  rcases le_total 0 y with h | h
  · rw [max_eq_left h]
  · rw [max_eq_right h, ENNReal.ofReal_of_nonpos h, ENNReal.ofReal_zero]

/-- **Ordered tails give the stochastic order** on monotone integrable observables. -/
theorem stochasticallyLE_of_tails [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂]
    (hIoi : ∀ r, ν₁ (Ioi r) ≤ ν₂ (Ioi r)) (hIci : ∀ r, ν₁ (Ici r) ≤ ν₂ (Ici r)) :
    StochasticallyLE ν₁ ν₂ := by
  intro g hg hmono hg1 hg2
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hg1,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part hg2]
  -- positive parts by layer cake over upper sets
  have hpos : ∀ ν : Measure ℝ, ∫⁻ x, ENNReal.ofReal (g x) ∂ν =
      ∫⁻ t in Ioi (0 : ℝ), ν {x | t < g x} := by
    intro ν
    have h := lintegral_eq_lintegral_meas_lt ν (f := fun x => max (g x) 0)
      (ae_of_all _ fun x => le_max_right _ _) (hg.max measurable_const).aemeasurable
    simp_rw [ofReal_max_zero] at h
    rw [h]
    refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    congr 1
    ext x
    simp only [mem_ofPred_eq, lt_max_iff]
    exact ⟨fun h => h.elim id fun h0 => absurd (lt_trans (mem_Ioi.mp ht) h0) (lt_irrefl _),
      fun h => Or.inl h⟩
  have hneg : ∀ ν : Measure ℝ, ∫⁻ x, ENNReal.ofReal (-g x) ∂ν =
      ∫⁻ t in Ioi (0 : ℝ), ν {x | g x < -t} := by
    intro ν
    have h := lintegral_eq_lintegral_meas_lt ν (f := fun x => max (-g x) 0)
      (ae_of_all _ fun x => le_max_right _ _) (hg.neg.max measurable_const).aemeasurable
    simp_rw [ofReal_max_zero] at h
    rw [h]
    refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    congr 1
    ext x
    simp only [mem_ofPred_eq, lt_max_iff, lt_neg]
    exact ⟨fun h => h.elim id fun h0 => absurd (lt_trans (mem_Ioi.mp ht) h0) (lt_irrefl _),
      fun h => Or.inl h⟩
  have hP : ∫⁻ x, ENNReal.ofReal (g x) ∂ν₁ ≤ ∫⁻ x, ENNReal.ofReal (g x) ∂ν₂ := by
    rw [hpos ν₁, hpos ν₂]
    refine lintegral_mono fun t => ?_
    exact measure_le_of_isUpperSet hIoi hIci fun x y hxy hx => lt_of_lt_of_le hx (hmono hxy)
  have hN : ∫⁻ x, ENNReal.ofReal (-g x) ∂ν₂ ≤ ∫⁻ x, ENNReal.ofReal (-g x) ∂ν₁ := by
    rw [hneg ν₁, hneg ν₂]
    refine lintegral_mono fun t => ?_
    exact measure_le_of_isLowerSet hIoi hIci (fun x y hyx hx => lt_of_le_of_lt (hmono hyx) hx)
      (measurableSet_lt hg measurable_const)
  have hfin : ∀ ν : Measure ℝ, Integrable g ν → ∫⁻ x, ENNReal.ofReal (g x) ∂ν ≠ ∞ := by
    intro ν hgν
    exact ne_top_of_le_ne_top hgν.hasFiniteIntegral.ne (lintegral_ofReal_le_lintegral_enorm g)
  have hfin' : ∀ ν : Measure ℝ, Integrable g ν → ∫⁻ x, ENNReal.ofReal (-g x) ∂ν ≠ ∞ := by
    intro ν hgν
    have := (lintegral_ofReal_le_lintegral_enorm (μ := ν) (fun x => -g x))
    simp only [enorm_neg] at this
    exact ne_top_of_le_ne_top hgν.hasFiniteIntegral.ne this
  have h1 := ENNReal.toReal_mono (hfin ν₂ hg2) hP
  have h2 := ENNReal.toReal_mono (hfin' ν₁ hg1) hN
  linarith

end StochasticOrder

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℝ} {μ : Measure Ω}

/-! ### The tilted occupation identity -/

/-- `∫ g(X_0, I'_b) = (∑_m ∫_{E_m} g(X_0, S'_m)) · p_b`. -/
theorem lintegral_shiftInf_eq_tsum_mul (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {b : ℝ} (hb : 0 < b)
    {g : ℝ → ℝ → ℝ≥0∞} (hg : Measurable (Function.uncurry g)) :
    ∫⁻ ω, g (X 0 ω) (shiftInf X b ω) ∂μ =
      (∑' m : ℕ, ∫⁻ ω, (weakDescentSet X b m).indicator
        (fun ω => g (X 0 ω) (shiftWalk X b m ω)) ω ∂μ) * μ (posWalkSet X b) := by
  have hprob : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  rw [← ENNReal.tsum_mul_right]
  have hterm : ∀ m : ℕ,
      (∫⁻ ω, (weakDescentSet X b m).indicator (fun ω => g (X 0 ω) (shiftWalk X b m ω)) ω ∂μ) *
        μ (posWalkSet X b) =
      ∫⁻ ω, (lastMinSet X b m).indicator (fun ω => g (X 0 ω) (shiftWalk X b m ω)) ω ∂μ := by
    intro m
    rw [lintegral_lastMinSet_eq hX hi b m hg, measure_strictFutureSet hX hi hG b m]
  simp_rw [hterm]
  rw [← lintegral_tsum]
  · refine lintegral_congr_ae ?_
    filter_upwards [lastMinSet_exists_ae hX hi hG hb] with ω hω
    exact (tsum_lastMinSet_indicator hω g).symm
  · intro m
    refine Measurable.aemeasurable ?_
    refine Measurable.indicator ?_ (measurableSet_lastMinSet hX b m)
    exact hg.comp ((hX 0).prodMk (shiftWalk_measurable hX b m))

/-- **Drift monotonicity of `Law(X_0, I'_a)/p_a`.** -/
theorem lintegral_shiftInf_antitone (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {a c : ℝ} (ha : 0 < a) (hac : a ≤ c)
    {g : ℝ → ℝ → ℝ≥0∞} (hg : Measurable (Function.uncurry g)) :
    μ (posWalkSet X a) * ∫⁻ ω, g (X 0 ω) (shiftInf X c ω) ∂μ ≤
      μ (posWalkSet X c) * ∫⁻ ω, g (X 0 ω) (shiftInf X a ω) ∂μ := by
  have hc : 0 < c := ha.trans_le hac
  rw [lintegral_shiftInf_eq_tsum_mul hX hi hG hc hg, lintegral_shiftInf_eq_tsum_mul hX hi hG ha hg]
  have hD : (∑' m : ℕ, ∫⁻ ω, (weakDescentSet X c m).indicator
        (fun ω => g (X 0 ω) (shiftWalk X c m ω)) ω ∂μ) ≤
      ∑' m : ℕ, ∫⁻ ω, (weakDescentSet X a m).indicator
        (fun ω => g (X 0 ω) (shiftWalk X a m ω)) ω ∂μ :=
    ENNReal.tsum_le_tsum fun m => lintegral_weakDescent_antitone hX hi hG ha.le hac m hg
  calc μ (posWalkSet X a) * ((∑' m : ℕ, ∫⁻ ω, (weakDescentSet X c m).indicator
          (fun ω => g (X 0 ω) (shiftWalk X c m ω)) ω ∂μ) * μ (posWalkSet X c))
      ≤ μ (posWalkSet X a) * ((∑' m : ℕ, ∫⁻ ω, (weakDescentSet X a m).indicator
          (fun ω => g (X 0 ω) (shiftWalk X a m ω)) ω ∂μ) * μ (posWalkSet X c)) := by
        gcongr
    _ = μ (posWalkSet X c) * ((∑' m : ℕ, ∫⁻ ω, (weakDescentSet X a m).indicator
          (fun ω => g (X 0 ω) (shiftWalk X a m ω)) ω ∂μ) * μ (posWalkSet X a)) := by ring

/-! ### The CDF of `𝖡(a)` -/

/-- `J_a(s) = 𝔼(Y_a - s)₊`. -/
def dualPosPartLIntegral (X : ℕ → Ω → ℝ) (μ : Measure Ω) (a s : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ENNReal.ofReal (ladderDualVariable X a ω - s) ∂μ

theorem ladderDualVariable_measurable (hX : ∀ n, Measurable (X n)) (a : ℝ) :
    Measurable (ladderDualVariable X a) :=
  ((hX 0).add_const a).add (shiftInf_measurable hX a)

/-- `J_a(a - r) = ∫ g_r(X_0, I'_a)` with `g_r(x, i) = (x + r + i)₊`. -/
theorem dualPosPartLIntegral_eq (a r : ℝ) :
    dualPosPartLIntegral X μ a (a - r) =
      ∫⁻ ω, (fun x i : ℝ => ENNReal.ofReal (x + r + i)) (X 0 ω) (shiftInf X a ω) ∂μ := by
  unfold dualPosPartLIntegral
  refine lintegral_congr fun ω => ?_
  have hY : ladderDualVariable X a ω = X 0 ω + a + shiftInf X a ω := rfl
  rw [hY]
  congr 1
  ring

theorem measurable_uncurry_ofReal_add (r : ℝ) :
    Measurable (Function.uncurry fun x i : ℝ => ENNReal.ofReal (x + r + i)) :=
  ENNReal.measurable_ofReal.comp ((measurable_fst.add_const r).add measurable_snd)

/-- `J_a(0) = a`. -/
theorem dualPosPartLIntegral_zero (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {a : ℝ} (ha : 0 < a) :
    dualPosPartLIntegral X μ a 0 = ENNReal.ofReal a := by
  obtain ⟨hint, -, hmean, -⟩ := ladderDualVariable_posPart_moments hX hi hG ha
  unfold dualPosPartLIntegral
  simp only [sub_zero]
  have hmax : ∫⁻ ω, ENNReal.ofReal (ladderDualVariable X a ω) ∂μ =
      ∫⁻ ω, ENNReal.ofReal (max (ladderDualVariable X a ω) 0) ∂μ :=
    lintegral_congr fun ω => (ofReal_max_zero _).symm
  rw [hmax, ← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun ω => le_max_right _ _),
    hmean]

/-- `p_a · P(H_a > o) = P(Y_a > o)` for `o ≥ 0`. -/
theorem measure_posWalkSet_mul_ladderLaw_Ioi (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {a : ℝ} (ha : 0 < a) {o : ℝ} (ho : 0 ≤ o) :
    μ (posWalkSet X a) * gaussianAscendingLadderLaw X μ a (Ioi o) =
      μ {ω | o < ladderDualVariable X a ω} := by
  have hH := gaussianAscendingLadderHeight_measurable hX a
  have h := ladder_duality hX hi hG ha (f := (Ioi o).indicator 1)
    (measurable_one.indicator measurableSet_Ioi)
  have hL : ∫⁻ ω, (Ioi o).indicator 1 (gaussianAscendingLadderHeight X a ω) ∂μ =
      gaussianAscendingLadderLaw X μ a (Ioi o) := by
    rw [gaussianAscendingLadderLaw, Measure.map_apply hH measurableSet_Ioi,
      ← lintegral_indicator_one (hH measurableSet_Ioi)]
    rfl
  have hR : ∀ ω, (Ioi 0).indicator ((Ioi o).indicator (1 : ℝ → ℝ≥0∞))
      (X 0 ω + a + shiftInf X a ω) = {ω | o < ladderDualVariable X a ω}.indicator 1 ω := by
    intro ω
    have hY : ladderDualVariable X a ω = X 0 ω + a + shiftInf X a ω := rfl
    by_cases hlt : o < ladderDualVariable X a ω
    · rw [indicator_of_mem (show ω ∈ {ω | o < ladderDualVariable X a ω} from hlt),
        indicator_of_mem (show X 0 ω + a + shiftInf X a ω ∈ Ioi 0 by
          rw [← hY]; exact lt_of_le_of_lt ho hlt),
        indicator_of_mem (show X 0 ω + a + shiftInf X a ω ∈ Ioi o by rw [← hY]; exact hlt)]
      rfl
    · rw [indicator_of_notMem (show ω ∉ {ω | o < ladderDualVariable X a ω} from hlt)]
      by_cases h0 : X 0 ω + a + shiftInf X a ω ∈ Ioi 0
      · rw [indicator_of_mem h0, indicator_of_notMem (show X 0 ω + a + shiftInf X a ω ∉ Ioi o by
          rw [← hY]; exact hlt)]
      · rw [indicator_of_notMem h0]
  rw [hL] at h
  rw [h]
  simp_rw [hR]
  exact lintegral_indicator_one (measurableSet_lt measurable_const
    (ladderDualVariable_measurable hX a))

/-- Layer cake with a shift: `∫_{[s,∞)} P(Y > o) do = 𝔼(Y - s)₊`. -/
theorem lintegral_Ici_measure_lt (hX : ∀ n, Measurable (X n)) (a s : ℝ) :
    ∫⁻ o in Ici s, μ {ω | o < ladderDualVariable X a ω} = dualPosPartLIntegral X μ a s := by
  have hY := ladderDualVariable_measurable hX a
  have hlc := lintegral_eq_lintegral_meas_lt μ (f := fun ω => max (ladderDualVariable X a ω - s) 0)
    (ae_of_all _ fun ω => le_max_right _ _) ((hY.sub_const s).max measurable_const).aemeasurable
  simp_rw [ofReal_max_zero] at hlc
  unfold dualPosPartLIntegral
  rw [hlc]
  set F : ℝ → ℝ≥0∞ := fun o => μ {ω | o < ladderDualVariable X a ω} with hF
  set G : ℝ → ℝ≥0∞ := fun t => μ {ω | t < max (ladderDualVariable X a ω - s) 0} with hG
  have hIci : ∫⁻ o in Ici s, F o = ∫⁻ o in Ioi s, F o :=
    (setLIntegral_congr (Ioi_ae_eq_Ici' (measure_singleton s))).symm
  rw [hIci, ← lintegral_indicator measurableSet_Ioi, ← lintegral_indicator measurableSet_Ioi]
  calc ∫⁻ o, (Ioi s).indicator F o
      = ∫⁻ u, (Ioi s).indicator F (u + s) :=
        (lintegral_add_right_eq_self (fun o => (Ioi s).indicator F o) s).symm
    _ = ∫⁻ u, (Ioi 0).indicator G u := by
        refine lintegral_congr fun u => ?_
        by_cases hu : 0 < u
        · rw [indicator_of_mem (show u + s ∈ Ioi s by simp only [mem_Ioi]; linarith),
            indicator_of_mem (show u ∈ Ioi 0 from hu)]
          simp only [hF, hG]
          congr 1
          ext ω
          simp only [mem_ofPred_eq, lt_max_iff]
          constructor
          · intro h; left; linarith
          · rintro (h | h)
            · linarith
            · exact absurd (hu.trans h) (lt_irrefl _)
        · rw [indicator_of_notMem (show u ∉ Ioi 0 from hu),
            indicator_of_notMem (show u + s ∉ Ioi s by
              simp only [mem_Ioi]; intro h; exact hu (by linarith))]

/-- `𝖡(a)(-∞, r] = J_a(a - r) · (p_a⁻¹ · m_a⁻¹)` for `r ≤ a`, where `m_a` is the ladder mean. -/
theorem swingOvershootMeasure_Iic_aux (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {a : ℝ} (ha : 0 < a) {r : ℝ} (hr : r ≤ a) :
    swingOvershootMeasure X μ a (Iic r) =
      dualPosPartLIntegral X μ a (a - r) *
        ((μ (posWalkSet X a))⁻¹ * (ladderMeanENN (gaussianAscendingLadderLaw X μ a))⁻¹) := by
  have hprob : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hp0 : μ (posWalkSet X a) ≠ 0 := measure_posWalkSet_pos hX hi hG ha
  have hpt : μ (posWalkSet X a) ≠ ⊤ := measure_ne_top _ _
  have hpre : ((fun o : ℝ => a - o) ⁻¹' Iic r) ∩ Ici 0 = Ici (a - r) := by
    ext o
    simp only [mem_inter_iff, mem_preimage, mem_Iic, mem_Ici]
    constructor
    · rintro ⟨h, _⟩; linarith
    · intro h; exact ⟨by linarith, by linarith⟩
  rw [swingOvershootMeasure_apply _ _ _ measurableSet_Iic, hpre]
  have hdens : ∀ o ∈ Ici (a - r), swingEquilibriumDensity X μ a o =
      μ {ω | o < ladderDualVariable X a ω} * (μ (posWalkSet X a))⁻¹ *
        (ladderMeanENN (gaussianAscendingLadderLaw X μ a))⁻¹ := by
    intro o ho
    have ho0 : 0 ≤ o := le_trans (by linarith) (mem_Ici.mp ho)
    have hν : gaussianAscendingLadderLaw X μ a (Ioi o) =
        μ {ω | o < ladderDualVariable X a ω} * (μ (posWalkSet X a))⁻¹ := by
      rw [← measure_posWalkSet_mul_ladderLaw_Ioi hX hi hG ha ho0, mul_comm (μ (posWalkSet X a)),
        mul_assoc, ENNReal.mul_inv_cancel hp0 hpt, mul_one]
    rw [swingEquilibriumDensity, hν, div_eq_mul_inv]
  rw [setLIntegral_congr_fun measurableSet_Ici hdens]
  have hmeas : Measurable fun o : ℝ => μ {ω | o < ladderDualVariable X a ω} :=
    Antitone.measurable fun o o' h => measure_mono fun ω hω => lt_of_le_of_lt h hω
  rw [lintegral_mul_const _ (hmeas.mul_const _), lintegral_mul_const _ hmeas,
    lintegral_Ici_measure_lt hX a (a - r), mul_assoc]

/-- `𝖡(a)(-∞, a] = 1`. -/
theorem swingOvershootMeasure_Iic_self (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {a : ℝ} (ha : 0 < a) :
    swingOvershootMeasure X μ a (Iic a) = 1 := by
  have := swingOvershootMeasure_isProbability hX hi hG ha
  rw [← measure_univ (μ := swingOvershootMeasure X μ a),
    swingOvershootMeasure_apply _ _ _ measurableSet_Iic,
    swingOvershootMeasure_apply _ _ _ MeasurableSet.univ]
  congr 2
  ext o
  simp only [mem_inter_iff, mem_preimage, mem_Iic, mem_Ici, preimage_univ, mem_univ, true_and]
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨by linarith, h⟩

/-- **The CDF of `𝖡(a)`**: `𝖡(a)(-∞, r] = J_a(a - r) / a` for `r ≤ a`. -/
theorem swingOvershootMeasure_Iic (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {a : ℝ} (ha : 0 < a) {r : ℝ} (hr : r ≤ a) :
    swingOvershootMeasure X μ a (Iic r) =
      dualPosPartLIntegral X μ a (a - r) / ENNReal.ofReal a := by
  have h1 := swingOvershootMeasure_Iic_aux hX hi hG ha le_rfl
  rw [swingOvershootMeasure_Iic_self hX hi hG ha, sub_self, dualPosPartLIntegral_zero hX hi hG ha]
    at h1
  have hK : (μ (posWalkSet X a))⁻¹ * (ladderMeanENN (gaussianAscendingLadderLaw X μ a))⁻¹ =
      (ENNReal.ofReal a)⁻¹ :=
    ENNReal.eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact h1.symm)
  rw [swingOvershootMeasure_Iic_aux hX hi hG ha hr, hK, div_eq_mul_inv]

/-- `𝖡(a)` has no atoms. -/
theorem swingOvershootMeasure_singleton (X : ℕ → Ω → ℝ) (μ : Measure Ω) (a r : ℝ) :
    swingOvershootMeasure X μ a {r} = 0 := by
  rw [swingOvershootMeasure_apply _ _ _ (measurableSet_singleton r)]
  refine setLIntegral_measure_zero _ _ (measure_mono_null ?_ (measure_singleton (a - r)))
  intro o ho
  simp only [mem_inter_iff, mem_preimage, mem_singleton_iff] at ho ⊢
  linarith [ho.1]

theorem swingOvershootMeasure_Ici_eq_Ioi (X : ℕ → Ω → ℝ) (μ : Measure Ω) (a r : ℝ) :
    swingOvershootMeasure X μ a (Ici r) = swingOvershootMeasure X μ a (Ioi r) :=
  (measure_congr (Ioi_ae_eq_Ici' (swingOvershootMeasure_singleton X μ a r))).symm

/-! ### The comparison -/

/-- `p_c · a ≤ p_a · c` in `ℝ≥0∞`. -/
theorem measure_posWalkSet_mul_ofReal_le (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {a c : ℝ} (ha : 0 < a) (hac : a ≤ c) :
    μ (posWalkSet X c) * ENNReal.ofReal a ≤ μ (posWalkSet X a) * ENNReal.ofReal c := by
  have hc : 0 < c := ha.trans_le hac
  rw [measure_posWalkSet_eq_spitzer hX hi hG ha, measure_posWalkSet_eq_spitzer hX hi hG hc,
    ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  exact ENNReal.ofReal_le_ofReal (exp_neg_spitzerExponent_mul_le ha hac)

/-- **CDF comparison**: `𝖡(c)(-∞, r] ≤ 𝖡(a)(-∞, r]` for `0 < a ≤ c`. -/
theorem swingOvershootMeasure_Iic_antitone (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {a c : ℝ} (ha : 0 < a) (hac : a ≤ c) (r : ℝ) :
    swingOvershootMeasure X μ c (Iic r) ≤ swingOvershootMeasure X μ a (Iic r) := by
  have hc : 0 < c := ha.trans_le hac
  have hprob := hi.isProbabilityMeasure
  have hBa := swingOvershootMeasure_isProbability hX hi hG ha
  have hBc := swingOvershootMeasure_isProbability hX hi hG hc
  rcases le_or_gt r a with hra | har
  · have hrc : r ≤ c := hra.trans hac
    rw [swingOvershootMeasure_Iic hX hi hG ha hra, swingOvershootMeasure_Iic hX hi hG hc hrc,
      dualPosPartLIntegral_eq, dualPosPartLIntegral_eq]
    set Ja := ∫⁻ ω, (fun x i : ℝ => ENNReal.ofReal (x + r + i)) (X 0 ω) (shiftInf X a ω) ∂μ
    set Jc := ∫⁻ ω, (fun x i : ℝ => ENNReal.ofReal (x + r + i)) (X 0 ω) (shiftInf X c ω) ∂μ
    set pa := μ (posWalkSet X a)
    set pc := μ (posWalkSet X c)
    have hpa0 : pa ≠ 0 := measure_posWalkSet_pos hX hi hG ha
    have hpat : pa ≠ ⊤ := measure_ne_top _ _
    have hpc0 : pc ≠ 0 := measure_posWalkSet_pos hX hi hG hc
    have hpct : pc ≠ ⊤ := measure_ne_top _ _
    have ha0 : ENNReal.ofReal a ≠ 0 := (ENNReal.ofReal_pos.mpr ha).ne'
    have hat : ENNReal.ofReal a ≠ ⊤ := ENNReal.ofReal_ne_top
    have hc0 : ENNReal.ofReal c ≠ 0 := (ENNReal.ofReal_pos.mpr hc).ne'
    have hct : ENNReal.ofReal c ≠ ⊤ := ENNReal.ofReal_ne_top
    -- tilt: `pa * Jc ≤ pc * Ja`
    have htilt : pa * Jc ≤ pc * Ja :=
      lintegral_shiftInf_antitone hX hi hG ha hac (measurable_uncurry_ofReal_add r)
    -- Spitzer: `pc * a ≤ pa * c`
    have hsp := measure_posWalkSet_mul_ofReal_le hX hi hG ha hac
    have hprod : (pa * pc) * (Jc * ENNReal.ofReal a) ≤ (pa * pc) * (Ja * ENNReal.ofReal c) := by
      calc (pa * pc) * (Jc * ENNReal.ofReal a) = (pa * Jc) * (pc * ENNReal.ofReal a) := by ring
        _ ≤ (pc * Ja) * (pa * ENNReal.ofReal c) := mul_le_mul' htilt hsp
        _ = (pa * pc) * (Ja * ENNReal.ofReal c) := by ring
    have hcancel : Jc * ENNReal.ofReal a ≤ Ja * ENNReal.ofReal c :=
      (ENNReal.mul_le_mul_iff_right (mul_ne_zero hpa0 hpc0) (ENNReal.mul_ne_top hpat hpct)).mp
        hprod
    rw [ENNReal.div_le_iff hc0 hct, ← ENNReal.mul_div_right_comm,
      ENNReal.le_div_iff_mul_le (Or.inl ha0) (Or.inl hat)]
    exact hcancel
  · have h1 : swingOvershootMeasure X μ a (Iic r) = 1 := by
      refine le_antisymm prob_le_one ?_
      rw [← swingOvershootMeasure_Iic_self hX hi hG ha]
      exact measure_mono (Iic_subset_Iic.mpr har.le)
    rw [h1]
    exact prob_le_one

/-- **Stochastic monotonicity of `𝖡`** (`OvershootStochasticMonotone X μ`) for the i.i.d.
standard Gaussian increment sequence: for `0 < a ≤ c`, `𝖡(a) ≤_st 𝖡(c)`. -/
theorem overshootStochasticMonotone_gaussian (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) : OvershootStochasticMonotone X μ := by
  intro a c ha hac
  have hc : 0 < c := ha.trans_le hac
  have hBa := swingOvershootMeasure_isProbability hX hi hG ha
  have hBc := swingOvershootMeasure_isProbability hX hi hG hc
  have hIoi : ∀ r, swingOvershootMeasure X μ a (Ioi r) ≤ swingOvershootMeasure X μ c (Ioi r) := by
    intro r
    rw [← compl_Iic, prob_compl_eq_one_sub measurableSet_Iic,
      prob_compl_eq_one_sub measurableSet_Iic]
    exact tsub_le_tsub_left (swingOvershootMeasure_Iic_antitone hX hi hG ha hac r) 1
  have hIci : ∀ r, swingOvershootMeasure X μ a (Ici r) ≤ swingOvershootMeasure X μ c (Ici r) := by
    intro r
    rw [swingOvershootMeasure_Ici_eq_Ioi, swingOvershootMeasure_Ici_eq_Ioi]
    exact hIoi r
  exact stochasticallyLE_of_tails hIoi hIci

end SwingRepair
