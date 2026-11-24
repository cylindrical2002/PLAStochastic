import PLAStochastic.Index.GEP.RawDisc.RealSegment

/-!
# WP4 `RawDisc` assembly, part 6: the one-letter laws and the insertion kernel

`wLaw ν ρ i` is the product law with `ρ` at coordinate `i` and `ν` elsewhere (`wLaw ν ν i = ν^∞`,
`wLaw ν σ i = wordLaw ν σ {i}`).  Inserting `x ~ ρ` at coordinate `i` of a `ν^∞` path gives
`wLaw ν ρ i`, so the `i`-th summand `J_i` of the insertion kernel
`I_F = insKernel ε ν (F ∘ S_T) = ∑_i J_i` integrates to `∫ J_i dρ = E_{wLaw ν ρ i}[1{i<T} F(S_T)]`
(`integral_insTerm`).

The integrability of all these objects is controlled by the survival values of the positive test
`e^{l y}`, `sW ν ρ i k = E_{wLaw ν ρ i}[e^{l S_k} 1{k<T}]`, as soon as
`∑_k ∑_{i ≤ k} sW ν ρ i k < ∞` (`WSummable`):
* `T < ∞` a.s. under every `wLaw ν ρ i` (`ae_fin_wLaw`);
* `E_{wLaw ν ρ i}[1{i<T} e^{l S_T}] ≤ 2 ∑_{k ≥ i} sW ν ρ i k` (`lintegral_stopExp_le`: the last
  gap before `T` is independent of the survival up to it), summable in `i`
  (`WSummable.tsum_ne_top`); together with the insertion bounds this is `WSummable.facts`.
For `ρ = ν` this is `∑_k (k+1) E_ν[e^{l S_k} 1{k<T}] < ∞`; for `ρ = σ` it comes from the survival
bound itself (Cauchy estimate of the linear coefficient, `abs_survLin_le`).
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

/-! ## One-letter laws -/

/-- The product law with `ρ` at coordinate `i` and `ν` elsewhere. -/
def wLaw (ν ρ : ProbabilityMeasure ℝ) (i : ℕ) : Measure (ℕ → ℝ) :=
  piLaw (Function.update (fun _ => ν) i ρ)

instance (ν ρ : ProbabilityMeasure ℝ) (i : ℕ) : IsProbabilityMeasure (wLaw ν ρ i) := by
  unfold wLaw; infer_instance

theorem wLaw_self (ν : ProbabilityMeasure ℝ) (i : ℕ) : wLaw ν ν i = iidLaw ν := by
  unfold wLaw
  rw [iidLaw_eq_piLaw]
  exact congrArg piLaw (Function.update_eq_self i (fun _ : ℕ => ν))

theorem wLaw_sigma (ν σ : ProbabilityMeasure ℝ) (i : ℕ) : wLaw ν σ i = wordLaw ν σ {i} := by
  rw [wLaw, wordLaw_eq_piLaw]
  refine piLaw_congr fun j => ?_
  by_cases h : j = i
  · subst h; simp
  · simp [h]

theorem smallMgf_wLaw {l : ℝ} {ν ρ : ProbabilityMeasure ℝ} (hν : SmallMgf l ν)
    (hρ : SmallMgf l ρ) (i : ℕ) : ∀ j, SmallMgf l (Function.update (fun _ => ν) i ρ j) :=
  fun j => by
    by_cases h : j = i
    · subst h; rw [Function.update_self]; exact hρ
    · rw [Function.update_of_ne h]; exact hν

theorem wLaw_agree (ν ρ : ProbabilityMeasure ℝ) (i : ℕ) :
    ∀ j < i, Function.update (fun _ => ν) i ρ j = (fun _ : ℕ => ν) j := fun _ hj =>
  Function.update_of_ne hj.ne _ _

theorem wLaw_agree' (ν ρ ρ' : ProbabilityMeasure ℝ) (i : ℕ) :
    ∀ j < i, Function.update (fun _ => ν) i ρ j = Function.update (fun _ => ν) i ρ' j :=
  fun _ hj => by rw [Function.update_of_ne hj.ne, Function.update_of_ne hj.ne]

theorem ae_nonneg_wLaw {l : ℝ} {ν ρ : ProbabilityMeasure ℝ} (hν : SmallMgf l ν)
    (hρ : SmallMgf l ρ) (i : ℕ) : ∀ᵐ g ∂(wLaw ν ρ i), ∀ j, 0 ≤ g j := by
  filter_upwards [ae_pos_piLaw fun j => (smallMgf_wLaw hν hρ i j).pos] with g hg j
  exact (hg j).le

/-! ## Survival values of the exponential test -/

/-- The positive exponential test `e^{l y}`. -/
def expTest (l y : ℝ) : ℝ := Real.exp (l * y)

theorem measurable_expTest (l : ℝ) : Measurable (expTest l) := by
  unfold expTest; fun_prop

/-- Survival values `E_{wLaw ν ρ i}[e^{l S_k} 1{k<T}]`. -/
def sW (eps l : ℝ) (ν ρ : ProbabilityMeasure ℝ) (i k : ℕ) : ℝ :=
  survInt eps (wLaw ν ρ i) k (expTest l)

theorem sW_nonneg (eps l : ℝ) (ν ρ : ProbabilityMeasure ℝ) (i k : ℕ) : 0 ≤ sW eps l ν ρ i k :=
  integral_nonneg fun g => Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) g

variable {eps l : ℝ} {ν ρ : ProbabilityMeasure ℝ}

theorem integrable_expInd_wLaw (hν : SmallMgf l ν) (hρ : SmallMgf l ρ) (i k : ℕ) :
    Integrable ((survSet eps k).indicator (fun g => expTest l (gapKeys g k))) (wLaw ν ρ i) :=
  integrable_survInd (C := 1) eps k (fun j => (smallMgf_wLaw hν hρ i j).pos)
    (fun j => (smallMgf_wLaw hν hρ i j).lle) (measurable_expTest l)
    (fun y _ => by rw [one_mul, expTest, abs_of_pos (Real.exp_pos _)])

/-- The ENNReal survival integrand of the exponential test. -/
def expIndL (eps l : ℝ) (k : ℕ) (g : ℕ → ℝ) : ℝ≥0∞ :=
  (survSet eps k).indicator (fun g => ENNReal.ofReal (Real.exp (l * gapKeys g k))) g

theorem measurable_expIndL (eps l : ℝ) (k : ℕ) : Measurable (expIndL eps l k) :=
  (((rawAsm_measurable_gapKeys k).const_mul l).exp.ennreal_ofReal).indicator
    (measurableSet_survSet eps k)

theorem expIndL_update (eps l : ℝ) (k : ℕ) (g : ℕ → ℝ) (y : ℝ) :
    expIndL eps l k (Function.update g k y) = expIndL eps l k g := by
  unfold expIndL
  by_cases hs : g ∈ survSet eps k
  · rw [Set.indicator_of_mem ((mem_survSet_update le_rfl g y).2 hs), Set.indicator_of_mem hs,
      gapKeys_update_self]
  · rw [Set.indicator_of_notMem (fun h => hs ((mem_survSet_update le_rfl g y).1 h)),
      Set.indicator_of_notMem hs]

theorem ofReal_sW (hν : SmallMgf l ν) (hρ : SmallMgf l ρ) (i k : ℕ) :
    ENNReal.ofReal (sW eps l ν ρ i k) = ∫⁻ g, expIndL eps l k g ∂(wLaw ν ρ i) := by
  rw [sW, survInt, ofReal_integral_eq_lintegral_ofReal (integrable_expInd_wLaw hν hρ i k)
    (Eventually.of_forall fun g => Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) g)]
  refine lintegral_congr fun g => ?_
  unfold expIndL
  by_cases hs : g ∈ survSet eps k
  · simp [Set.indicator_of_mem hs, expTest]
  · simp [Set.indicator_of_notMem hs]

theorem measure_survSet_le_sW (hl : 0 ≤ l) (hν : SmallMgf l ν) (hρ : SmallMgf l ρ) (i k : ℕ) :
    wLaw ν ρ i (survSet eps k) ≤ ENNReal.ofReal (sW eps l ν ρ i k) := by
  rw [ofReal_sW hν hρ, ← lintegral_indicator_one (measurableSet_survSet eps k)]
  refine lintegral_mono_ae ?_
  filter_upwards [ae_nonneg_wLaw hν hρ i] with g hg
  unfold expIndL
  by_cases hs : g ∈ survSet eps k
  · rw [Set.indicator_of_mem hs, Set.indicator_of_mem hs]
    exact ENNReal.one_le_ofReal.2 (Real.one_le_exp (mul_nonneg hl (gapKeys_nonneg hg k)))
  · rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem hs]

/-- **`T < ∞` a.s.** under a one-letter law whose survival values tend to zero. -/
theorem ae_fin_wLaw (hl : 0 ≤ l) (hν : SmallMgf l ν) (hρ : SmallMgf l ρ) (i : ℕ)
    (h0 : Tendsto (fun k => sW eps l ν ρ i k) atTop (𝓝 0)) :
    ∀ᵐ g ∂(wLaw ν ρ i), gapSegLen eps g ≠ ⊤ := by
  have hle : ∀ k, wLaw ν ρ i {g | gapSegLen eps g = ⊤} ≤ ENNReal.ofReal (sW eps l ν ρ i k) :=
    fun k => (measure_mono fun g (hg : gapSegLen eps g = ⊤) =>
      show g ∈ survSet eps k by simp [survSet, hg]).trans (measure_survSet_le_sW hl hν hρ i k)
  have ht : Tendsto (fun k => ENNReal.ofReal (sW eps l ν ρ i k)) atTop (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]; exact ENNReal.tendsto_ofReal h0
  have h := ge_of_tendsto' ht hle
  exact measure_eq_zero_iff_ae_notMem.1 (le_antisymm h (by simp))

/-- **The stopped exponential test** under a one-letter law: the last gap before `T` is independent
of the survival up to it. -/
theorem lintegral_stopExp_le (hν : SmallMgf l ν) (hρ : SmallMgf l ρ) (i : ℕ)
    (hfin : ∀ᵐ g ∂(wLaw ν ρ i), gapSegLen eps g ≠ ⊤) :
    ∫⁻ g, (survSet eps i).indicator (fun g => ENNReal.ofReal (Real.exp (l * stopSum eps g))) g
        ∂(wLaw ν ρ i) ≤
      2 * ∑' k, if i ≤ k then ENNReal.ofReal (sW eps l ν ρ i k) else 0 := by
  set B : ℝ → ℝ≥0∞ := fun y => ENNReal.ofReal (Real.exp (l * y)) with hB
  have hBm : Measurable B := ((measurable_id.const_mul l).exp).ennreal_ofReal
  have hpt : ∀ᵐ g ∂(wLaw ν ρ i),
      (survSet eps i).indicator (fun g => ENNReal.ofReal (Real.exp (l * stopSum eps g))) g ≤
        ∑' k, if i ≤ k then expIndL eps l k g * B (g k) else 0 := by
    filter_upwards [hfin] with g hT
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 hT
    by_cases him : i < m
    · rw [Set.indicator_of_mem ((mem_survSet_iff_of_eq hm.symm i).2 him)]
      refine le_trans (le_of_eq ?_) (ENNReal.le_tsum (m - 1))
      rw [if_pos (by omega), expIndL, Set.indicator_of_mem
        ((mem_survSet_iff_of_eq hm.symm (m - 1)).2 (by omega)), hB,
        ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, ← mul_add, ← gapKeys_succ,
        Nat.sub_add_cancel (by omega), stopSum_of_eq hm.symm]
    · rw [Set.indicator_of_notMem (fun h => him ((mem_survSet_iff_of_eq hm.symm i).1 h))]
      simp
  have hmeas : ∀ k, AEMeasurable (fun g => if i ≤ k then expIndL eps l k g * B (g k) else 0)
      (wLaw ν ρ i) := fun k => by
    split_ifs
    · exact ((measurable_expIndL eps l k).mul (hBm.comp (measurable_pi_apply k))).aemeasurable
    · exact aemeasurable_const
  calc ∫⁻ g, (survSet eps i).indicator
        (fun g => ENNReal.ofReal (Real.exp (l * stopSum eps g))) g ∂(wLaw ν ρ i)
      ≤ ∫⁻ g, ∑' k, (if i ≤ k then expIndL eps l k g * B (g k) else 0) ∂(wLaw ν ρ i) :=
        lintegral_mono_ae hpt
    _ = ∑' k, ∫⁻ g, (if i ≤ k then expIndL eps l k g * B (g k) else 0) ∂(wLaw ν ρ i) :=
        lintegral_tsum hmeas
    _ ≤ ∑' k, 2 * (if i ≤ k then ENNReal.ofReal (sW eps l ν ρ i k) else 0) := by
        refine ENNReal.tsum_le_tsum fun k => ?_
        split_ifs
        · rw [wLaw, lintegral_mul_coord _ k (measurable_expIndL eps l k)
            (fun g y => expIndL_update eps l k g y) hBm, ← wLaw, ← ofReal_sW hν hρ, mul_comm 2]
          gcongr
          exact (smallMgf_wLaw hν hρ i k).lle
        · simp
    _ = 2 * ∑' k, if i ≤ k then ENNReal.ofReal (sW eps l ν ρ i k) else 0 :=
        ENNReal.tsum_mul_left

/-- The column-summability of the survival values of the exponential test. -/
def WSummable (eps l : ℝ) (ν ρ : ProbabilityMeasure ℝ) : Prop :=
  Summable fun k => ∑ i ∈ Finset.range (k + 1), sW eps l ν ρ i k

theorem tsum_ite_le_eq (f : ℕ → ℕ → ℝ≥0∞) :
    ∑' i, ∑' k, (if i ≤ k then f i k else 0) = ∑' k, ∑ i ∈ Finset.range (k + 1), f i k := by
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun k => ?_
  rw [tsum_eq_sum (s := Finset.range (k + 1)) fun i hi => by
    rw [Finset.mem_range] at hi; rw [if_neg (by omega)]]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [if_pos (by omega)]

theorem WSummable.tendsto_zero (h : WSummable eps l ν ρ) (i : ℕ) :
    Tendsto (fun k => sW eps l ν ρ i k) atTop (𝓝 0) := by
  have h0 := h.tendsto_atTop_zero
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h0
    (Eventually.of_forall fun k => sW_nonneg eps l ν ρ i k) ?_
  filter_upwards [eventually_ge_atTop i] with k hk
  exact Finset.single_le_sum (f := fun i => sW eps l ν ρ i k)
    (fun i _ => sW_nonneg eps l ν ρ i k) (Finset.mem_range.2 (by omega))

theorem WSummable.tsum_ne_top (h : WSummable eps l ν ρ) :
    ∑' i, ∑' k, (if i ≤ k then ENNReal.ofReal (sW eps l ν ρ i k) else 0) ≠ ⊤ := by
  rw [tsum_ite_le_eq]
  have e : ∀ k, ∑ i ∈ Finset.range (k + 1), ENNReal.ofReal (sW eps l ν ρ i k) =
      ENNReal.ofReal (∑ i ∈ Finset.range (k + 1), sW eps l ν ρ i k) := fun k =>
    (ENNReal.ofReal_sum_of_nonneg fun i _ => sW_nonneg eps l ν ρ i k).symm
  simp_rw [e]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => Finset.sum_nonneg fun i _ =>
    sW_nonneg eps l ν ρ i k) h]
  exact ENNReal.ofReal_ne_top

/-! ## The insertion kernel -/

/-- `1{i<T} F(S_T)`. -/
def stopInd (eps : ℝ) (F : ℝ → ℝ) (i : ℕ) : (ℕ → ℝ) → ℝ :=
  (survSet eps i).indicator (fun g => F (stopSum eps g))

theorem measurable_stopInd (eps : ℝ) {F : ℝ → ℝ} (hF : Measurable F) (i : ℕ) :
    Measurable (stopInd eps F i) :=
  (hF.comp (measurable_stopSum eps)).indicator (measurableSet_survSet eps i)

/-- The `i`-th summand `J_i` of the insertion kernel of `F ∘ S_T`. -/
def insTerm (eps : ℝ) (ν : ProbabilityMeasure ℝ) (F : ℝ → ℝ) (i : ℕ) (x : ℝ) : ℝ :=
  ∫ g, {g : ℕ → ℝ | (i : ℕ∞) < gapSegLen eps g}.indicator
    (fun g => F (stopSum eps (Function.update g i x))) g ∂(iidLaw ν)

theorem insKernel_eq_tsum (eps : ℝ) (ν : ProbabilityMeasure ℝ) (F : ℝ → ℝ) (x : ℝ) :
    insKernel eps ν (fun g => F (stopSum eps g)) x = ∑' i, insTerm eps ν F i x := rfl

theorem insTerm_eq (eps : ℝ) (ν : ProbabilityMeasure ℝ) (F : ℝ → ℝ) (i : ℕ) (x : ℝ) :
    insTerm eps ν F i x = ∫ g, stopInd eps F i (Function.update g i x) ∂(iidLaw ν) := by
  unfold insTerm stopInd
  refine integral_congr_ae (Eventually.of_forall fun g => ?_)
  change (survSet eps i).indicator _ g = _
  dsimp only
  by_cases hs : g ∈ survSet eps i
  · rw [Set.indicator_of_mem hs, Set.indicator_of_mem ((mem_survSet_update le_rfl g x).2 hs)]
  · rw [Set.indicator_of_notMem hs,
      Set.indicator_of_notMem (fun h => hs ((mem_survSet_update le_rfl g x).1 h))]

theorem measurable_insTerm (eps : ℝ) (ν : ProbabilityMeasure ℝ) {F : ℝ → ℝ} (hF : Measurable F)
    (i : ℕ) : Measurable (insTerm eps ν F i) := by
  have h := measurable_integral_update ν i (measurable_stopInd eps hF i)
  have e : insTerm eps ν F i = fun y => ∫ g, stopInd eps F i (Function.update g i y) ∂(iidLaw ν) :=
    funext (insTerm_eq eps ν F i)
  rw [e]
  exact h

/-- **Insertion identity**: `∫ J_i dρ = E_{wLaw ν ρ i}[1{i<T} F(S_T)]`. -/
theorem integral_insTerm {F : ℝ → ℝ} (hF : Measurable F) (i : ℕ)
    (hint : Integrable (stopInd eps F i) (wLaw ν ρ i)) :
    ∫ x, insTerm eps ν F i x ∂(ρ : Measure ℝ) = ∫ g, stopInd eps F i g ∂(wLaw ν ρ i) := by
  rw [wLaw, integral_piLaw_update (fun _ => ν) i ρ (measurable_stopInd eps hF i) hint]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  rw [insTerm_eq]
  rfl

theorem lintegral_enorm_insTerm_le {F : ℝ → ℝ} (hF : Measurable F) (i : ℕ) :
    ∫⁻ x, ‖insTerm eps ν F i x‖ₑ ∂(ρ : Measure ℝ) ≤
      ∫⁻ g, ‖stopInd eps F i g‖ₑ ∂(wLaw ν ρ i) := by
  calc ∫⁻ x, ‖insTerm eps ν F i x‖ₑ ∂(ρ : Measure ℝ)
      ≤ ∫⁻ x, ∫⁻ g, ‖stopInd eps F i (Function.update g i x)‖ₑ ∂(iidLaw ν) ∂(ρ : Measure ℝ) :=
        lintegral_mono fun x => by
          rw [insTerm_eq]; exact enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ g, ‖stopInd eps F i g‖ₑ ∂(wLaw ν ρ i) :=
        (lintegral_piLaw_update (fun _ => ν) i ρ (measurable_stopInd eps hF i).enorm).symm

theorem enorm_stopInd_le {F : ℝ → ℝ} (hFb : ∀ y, 0 ≤ y → |F y| ≤ Real.exp (l * y)) (i : ℕ)
    {g : ℕ → ℝ} (hg : ∀ j, 0 ≤ g j) :
    ‖stopInd eps F i g‖ₑ ≤
      (survSet eps i).indicator (fun g => ENNReal.ofReal (Real.exp (l * stopSum eps g))) g := by
  unfold stopInd
  by_cases hs : g ∈ survSet eps i
  · rw [Set.indicator_of_mem hs, Set.indicator_of_mem hs, Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal (hFb _ (rawAsm_stopSum_nonneg hg))
  · rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem hs, enorm_zero]

/-- The consequences of `WSummable` for one direction `ρ`. -/
theorem WSummable.facts (hl : 0 ≤ l) (hν : SmallMgf l ν) (hρ : SmallMgf l ρ)
    (h : WSummable eps l ν ρ) {F : ℝ → ℝ} (hF : Measurable F)
    (hFb : ∀ y, 0 ≤ y → |F y| ≤ Real.exp (l * y)) :
    (∀ i, ∀ᵐ g ∂(wLaw ν ρ i), gapSegLen eps g ≠ ⊤) ∧
    (∀ i, Integrable ((survSet eps i).indicator (fun g => Real.exp (l * stopSum eps g)))
      (wLaw ν ρ i)) ∧
    (∀ i, Integrable (stopInd eps F i) (wLaw ν ρ i)) ∧
    ∑' i, ∫⁻ x, ‖insTerm eps ν F i x‖ₑ ∂(ρ : Measure ℝ) ≠ ⊤ := by
  have hfin : ∀ i, ∀ᵐ g ∂(wLaw ν ρ i), gapSegLen eps g ≠ ⊤ := fun i =>
    ae_fin_wLaw hl hν hρ i (h.tendsto_zero i)
  have htot := h.tsum_ne_top
  have hbnd : ∀ i, ∫⁻ g, (survSet eps i).indicator
      (fun g => ENNReal.ofReal (Real.exp (l * stopSum eps g))) g ∂(wLaw ν ρ i) ≠ ⊤ := by
    intro i
    refine ne_top_of_le_ne_top ?_ (lintegral_stopExp_le hν hρ i (hfin i))
    refine ENNReal.mul_ne_top (by norm_num) (ne_top_of_le_ne_top htot ?_)
    exact ENNReal.le_tsum (f := fun i => ∑' k,
      if i ≤ k then ENNReal.ofReal (sW eps l ν ρ i k) else 0) i
  have hmE : ∀ i, Measurable ((survSet eps i).indicator
      (fun g => Real.exp (l * stopSum eps g))) := fun i =>
    ((measurable_stopSum eps).const_mul l).exp.indicator (measurableSet_survSet eps i)
  have hintE : ∀ i, Integrable ((survSet eps i).indicator
      (fun g => Real.exp (l * stopSum eps g))) (wLaw ν ρ i) := by
    intro i
    refine ⟨(hmE i).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun g =>
      Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) g)]
    refine lt_of_le_of_lt (le_of_eq ?_) (hbnd i).lt_top
    refine lintegral_congr fun g => ?_
    by_cases hs : g ∈ survSet eps i
    · simp [Set.indicator_of_mem hs]
    · simp [Set.indicator_of_notMem hs]
  have hintS : ∀ i, Integrable (stopInd eps F i) (wLaw ν ρ i) := by
    intro i
    refine (hintE i).mono' (measurable_stopInd eps hF i).aestronglyMeasurable ?_
    filter_upwards [ae_nonneg_wLaw hν hρ i] with g hg
    unfold stopInd
    by_cases hs : g ∈ survSet eps i
    · rw [Set.indicator_of_mem hs, Set.indicator_of_mem hs, Real.norm_eq_abs]
      exact hFb _ (rawAsm_stopSum_nonneg hg)
    · rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem hs, norm_zero]
  refine ⟨hfin, hintE, hintS, ?_⟩
  refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) htot) ?_
  rw [← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun i => ?_
  refine (lintegral_enorm_insTerm_le hF i).trans ?_
  refine le_trans ?_ (lintegral_stopExp_le hν hρ i (hfin i))
  refine lintegral_mono_ae ?_
  filter_upwards [ae_nonneg_wLaw hν hρ i] with g hg
  exact enorm_stopInd_le hFb i hg

end

end PGM
