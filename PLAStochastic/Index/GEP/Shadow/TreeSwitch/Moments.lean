import PLAStochastic.Index.GEP.Shadow.TreeSwitch.DisagreementProbability

/-!
# WP3 tree switch: moments consumed by (tree-mean) and (tree-W2)

Source: `research/2026-09-28-gep-closure/memory-route.md` §6 ("Cauchy–Schwarz 和停时二阶矩",
"统一归一化四阶矩").  The Cauchy–Schwarz steps of the source are replaced by the AM–GM form
`∫_B f ≤ (s ∫ f² + P(B)/s)/2` (`setIntegral_le_amgm`), which needs no Hölder inequality.

* `pow_le_exp_mul`, `ExpMom.integral_pow_le`, `integral_pow_le_of_map`: an exponential moment
  `E e^{θZ} ≤ B` of a nonnegative law gives `E Z^n ≤ n! B / θ^n`.
* `setIntegral_le_amgm` (the logarithmic comparison is `abs_log_sub_log_le` of `PGM/GEPMetric`).
* `momClass_stop_sq`, `pasLen_sq_le`: `E T_Y² ≤ K2 (eps²/vmin)²` for the passive stop of a law of
  the moment class (`oneLayer_bracket`), transported to a pair space.
* `actLen_shPair_sq_le`: `E T_X² ≤ K2 (eps²/vIn)²` for the active stop of every actual layer.
* measurability of the two stops and of the two stopped passive sums.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Finset Set

/-! ## Moments from exponential moments -/

theorem pow_le_exp_mul {x θ : ℝ} (hx : 0 ≤ x) (hθ : 0 < θ) (n : ℕ) :
    x ^ n ≤ (n.factorial : ℝ) / θ ^ n * Real.exp (θ * x) := by
  have h := Real.pow_div_factorial_le_exp (θ * x) (mul_nonneg hθ.le hx) n
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  rw [div_le_iff₀ hf, mul_pow] at h
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  nlinarith [pow_pos hθ n]

/-- Moments of a nonnegative law with an exponential moment. -/
theorem ExpMom.integral_pow_le {θ B : ℝ} {ρ : ProbabilityMeasure ℝ} (h : ExpMom θ B ρ)
    (hθ : 0 < θ) (hpos : (ρ : Measure ℝ) (Iic 0) = 0) (n : ℕ) :
    Integrable (fun x : ℝ => x ^ n) (ρ : Measure ℝ) ∧
      ∫ x, x ^ n ∂(ρ : Measure ℝ) ≤ (n.factorial : ℝ) / θ ^ n * B := by
  have hae : ∀ᵐ x ∂(ρ : Measure ℝ), 0 ≤ x := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hpos] with x hx
    simp only [Set.mem_Iic, not_le] at hx
    exact hx.le
  have hbd : Integrable (fun x => (n.factorial : ℝ) / θ ^ n * Real.exp (θ * x))
      (ρ : Measure ℝ) := h.integrable.const_mul _
  have hint : Integrable (fun x : ℝ => x ^ n) (ρ : Measure ℝ) :=
    hbd.mono' (by fun_prop) (by
      filter_upwards [hae] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hx n)]
      exact pow_le_exp_mul hx hθ n)
  refine ⟨hint, ?_⟩
  calc ∫ x, x ^ n ∂(ρ : Measure ℝ)
      ≤ ∫ x, (n.factorial : ℝ) / θ ^ n * Real.exp (θ * x) ∂(ρ : Measure ℝ) :=
        integral_mono_ae hint hbd (by
          filter_upwards [hae] with x hx using pow_le_exp_mul hx hθ n)
    _ = (n.factorial : ℝ) / θ ^ n * ∫ x, Real.exp (θ * x) ∂(ρ : Measure ℝ) :=
        integral_const_mul _ _
    _ ≤ (n.factorial : ℝ) / θ ^ n * B := by
        gcongr
        exact h.le

/-- Transport of `ExpMom.integral_pow_le` to a random variable with that law. -/
theorem integral_pow_le_of_map {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Z : Ω → ℝ}
    (hZ : Measurable Z) {ρ : ProbabilityMeasure ℝ} (hmap : P.map Z = (ρ : Measure ℝ))
    {θ B : ℝ} (h : ExpMom θ B ρ) (hθ : 0 < θ) (hpos : (ρ : Measure ℝ) (Iic 0) = 0) (n : ℕ) :
    Integrable (fun ω => Z ω ^ n) P ∧ ∫ ω, Z ω ^ n ∂P ≤ (n.factorial : ℝ) / θ ^ n * B := by
  obtain ⟨hi, hle⟩ := h.integral_pow_le hθ hpos n
  have hm : AEStronglyMeasurable (fun x : ℝ => x ^ n) (P.map Z) := by fun_prop
  refine ⟨?_, ?_⟩
  · rw [← hmap] at hi
    exact (integrable_map_measure hm hZ.aemeasurable).mp hi
  · rw [← integral_map hZ.aemeasurable hm, hmap]
    exact hle

/-! ## Two elementary inequalities -/

/-- **AM–GM on an event**: `∫_B f ≤ (s ∫ f² + P(B)/s)/2` for `f ≥ 0` with `f² ∈ L¹`. -/
theorem setIntegral_le_amgm {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {f : Ω → ℝ} (hfm : AEStronglyMeasurable f P)
    (hf2 : Integrable (fun ω => f ω ^ 2) P) (hf0 : ∀ ω, 0 ≤ f ω) {B : Set Ω}
    (hB : MeasurableSet B) {s : ℝ} (hs : 0 < s) :
    Integrable f P ∧ ∫ ω in B, f ω ∂P ≤ (s * ∫ ω, f ω ^ 2 ∂P + P.real B / s) / 2 := by
  have hpt : ∀ ω, f ω ≤ (s * f ω ^ 2 + 1 / s) / 2 := fun ω => by
    have h1 : 0 ≤ (s * f ω - 1) ^ 2 := sq_nonneg _
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
    have e1 : (s * f ω ^ 2 + 1 / s) * s = (s * f ω) ^ 2 + 1 := by field_simp
    have h2 : f ω * 2 * s ≤ (s * f ω ^ 2 + 1 / s) * s := by rw [e1]; nlinarith
    exact le_of_mul_le_mul_right h2 hs
  have hbd : Integrable (fun ω => (s * f ω ^ 2 + 1 / s) / 2) P :=
    ((hf2.const_mul s).add (integrable_const _)).div_const 2
  have hint : Integrable f P :=
    hbd.mono' hfm (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hf0 ω)]; exact hpt ω)
  refine ⟨hint, ?_⟩
  calc ∫ ω in B, f ω ∂P ≤ ∫ ω in B, (s * f ω ^ 2 + 1 / s) / 2 ∂P :=
        setIntegral_mono_on hint.integrableOn hbd.integrableOn hB fun ω _ => hpt ω
    _ = (s * ∫ ω in B, f ω ^ 2 ∂P + P.real B / s) / 2 := by
        rw [integral_div, integral_add (hf2.const_mul s).integrableOn (integrable_const _),
          integral_const_mul, setIntegral_const]
        simp only [smul_eq_mul]
        ring
    _ ≤ (s * ∫ ω, f ω ^ 2 ∂P + P.real B / s) / 2 := by
        have h := setIntegral_le_integral (s := B) hf2
          (Filter.Eventually.of_forall fun ω => sq_nonneg (f ω))
        have := mul_le_mul_of_nonneg_left h hs.le
        linarith

/-! ## Measurability of the two stops and the stopped passive sums -/

variable {Ω : Type*} [MeasurableSpace Ω] {V : ℕ → Ω → ℝ × ℝ}

theorem measurable_actLen_tr (hV : ∀ t, Measurable (V t)) (eps : ℝ) :
    Measurable (actLen eps V) :=
  (isStoppingRule_gapSegLen eps).measurable.comp (measurable_pi_lambda _ fun t => (hV t).fst)

theorem measurable_pasLen_tr (hV : ∀ t, Measurable (V t)) (eps : ℝ) :
    Measurable (pasLen eps V) :=
  (isStoppingRule_gapSegLen eps).measurable.comp (measurable_pi_lambda _ fun t => (hV t).snd)

theorem measurable_actSum_tr (hV : ∀ t, Measurable (V t)) (eps : ℝ) :
    Measurable (actSum eps V) := by
  have hN : Measurable fun ω => (actLen eps V ω).toNat :=
    (Measurable.of_discrete (f := ENat.toNat)).comp (measurable_actLen_tr hV eps)
  have hm : Measurable (fun p : Ω × ℕ => ∑ t ∈ range p.2, (V t p.1).2) :=
    measurable_from_prod_countable_left fun n => by
      change Measurable fun ω => ∑ t ∈ range n, (V t ω).2
      exact Finset.measurable_sum _ fun t _ => (hV t).snd
  exact hm.comp (measurable_id.prodMk hN)

theorem measurable_pasSum_tr (hV : ∀ t, Measurable (V t)) (eps : ℝ) :
    Measurable (pasSum eps V) :=
  (measurable_stopSum eps).comp (measurable_pi_lambda _ fun t => (hV t).snd)

theorem measurableSet_actLen_ne_pasLen (hV : ∀ t, Measurable (V t)) (eps : ℝ) :
    MeasurableSet {ω | actLen eps V ω ≠ pasLen eps V ω} :=
  (measurableSet_eq_fun (measurable_actLen_tr hV eps) (measurable_pasLen_tr hV eps)).compl

/-! ## Second moments of the two stops -/

/-- `E T² ≤ K2 (eps²/vmin)²` for the first stop of iid gaps of the moment class. -/
theorem momClass_stop_sq {b β vmin eps : ℝ} (hvmin0 : 0 < vmin) (heps : epsZero b β ≤ eps)
    {ρ : ProbabilityMeasure ℝ} (hρ : MomClass b β vmin ρ) :
    Integrable (fun g => ((gapSegLen eps g).toNat : ℝ) ^ 2) (iidLaw ρ) ∧
      ∫ g, ((gapSegLen eps g).toNat : ℝ) ^ 2 ∂(iidLaw ρ) ≤ K2 * (eps ^ 2 / vmin) ^ 2 := by
  have hv0 : 0 < lawVar ρ := hvmin0.trans_le hρ.var_ge
  set σ := Real.sqrt (lawVar ρ) with hσdef
  have hσ : 0 < σ := Real.sqrt_pos.2 hv0
  have hσ2 : σ ^ 2 = lawVar ρ := Real.sq_sqrt hv0.le
  set κ := ∫ x, |x - 1| ^ 3 ∂(ρ : Measure ℝ) with hκdef
  have hX : GapLaw (iidLaw ρ) gapCoord 1 σ κ :=
    gapLaw_iidLaw hρ.memLp3 hρ.mean one_pos hσ2.symm hσ le_rfl
  have hκ : 0 ≤ κ := integral_nonneg fun _ => by positivity
  have heps1 : 1 ≤ eps := le_trans (one_le_epsZero b β) heps
  have hepspos : 0 < eps := by linarith
  obtain ⟨c1, c2, c3, c4, -, -, -⟩ := largeConditions one_pos hσ hκ
    (by rw [hσ2, one_pow, mul_one]; exact hρ.var_le) hρ.third_le heps
  set G := eps ^ 2 / lawVar ρ with hG
  have hGdef : G = 1 ^ 2 * eps ^ 2 / σ ^ 2 := by rw [hσ2, one_pow, one_mul]
  rw [← hGdef] at c1 c2
  obtain ⟨-, -, -, hT2, -, -, -, hM2, -, -, -⟩ := oneLayer_bracket hX hepspos hGdef c1 c2 c3 c4
  refine ⟨hT2, hM2.trans ?_⟩
  have hGv : G ≤ eps ^ 2 / vmin := div_le_div_of_nonneg_left (sq_nonneg eps) hvmin0 hρ.var_ge
  have hG0 : 0 ≤ G := by positivity
  gcongr
  exact K2_pos.le

omit [MeasurableSpace Ω] in
theorem pasLen_eq_gapSegLen (eps : ℝ) (V : ℕ → Ω → ℝ × ℝ) (ω : Ω) :
    pasLen eps V ω = gapSegLen eps (seq (fun t ω => (V t ω).2) ω) := rfl

/-- The passive stop on a pair space whose passive law is of the moment class. -/
theorem pasLen_sq_le {P : Measure Ω} (hV : IIDSeqE P V) {ν : ProbabilityMeasure ℝ}
    (hν : P.map (fun ω => (V 0 ω).2) = (ν : Measure ℝ)) {b β vmin eps : ℝ} (hvmin0 : 0 < vmin)
    (heps : epsZero b β ≤ eps) (hρ : MomClass b β vmin ν) :
    Integrable (fun ω => ((pasLen eps V ω).toNat : ℝ) ^ 2) P ∧
      ∫ ω, ((pasLen eps V ω).toNat : ℝ) ^ 2 ∂P ≤ K2 * (eps ^ 2 / vmin) ^ 2 := by
  have hY := hV.iidSeq_pas
  have hmap := map_seq_eq_iidLaw hY ν hν.symm
  obtain ⟨hi, hle⟩ := momClass_stop_sq hvmin0 heps hρ
  have hf : Measurable fun g : ℕ → ℝ => ((gapSegLen eps g).toNat : ℝ) ^ 2 :=
    (measurable_toNat_gapSegLen eps).pow_const 2
  have hs : Measurable (seq fun t ω => (V t ω).2) := measurable_seq hY.measurable
  refine ⟨?_, ?_⟩
  · rw [← hmap] at hi
    exact (integrable_map_measure hf.aestronglyMeasurable hs.aemeasurable).mp hi
  · have e1 := integral_map (μ := P) hs.aemeasurable hf.aestronglyMeasurable
    rw [hmap] at e1
    simp only [pasLen_eq_gapSegLen]
    rw [← e1]
    exact hle

/-- `T ≤ T²` for naturals: the first moment of a stop from its second moment. -/
theorem integrable_toNat_of_sq {P : Measure Ω} {T : Ω → ℕ∞} (hT : Measurable T)
    (h2 : Integrable (fun ω => ((T ω).toNat : ℝ) ^ 2) P) :
    Integrable (fun ω => ((T ω).toNat : ℝ)) P :=
  h2.mono' ((Measurable.of_discrete (f := fun n : ℕ∞ => (n.toNat : ℝ))).comp hT).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
      have h : ((T ω).toNat : ℝ) ≤ ((T ω).toNat : ℝ) ^ 2 := by
        rcases Nat.eq_zero_or_pos (T ω).toNat with h0 | h0
        · rw [h0]; simp
        · have : (1 : ℝ) ≤ (T ω).toNat := by exact_mod_cast h0
          nlinarith
      exact h)

/-- The active stop of every actual layer has `E T_X² ≤ K2 (eps²/vIn)²`. -/
theorem actLen_shPair_sq_le {P : Measure Ω} [IsProbabilityMeasure P] {g : ℕ → Ω → ℝ}
    {μ₀ σ₀ κ₀ eps : ℝ} (hg : GapLaw P g μ₀ σ₀ κ₀)
    (heps : epsZero (bIn μ₀ σ₀) (βIn σ₀ (lkap P (inputPairs g))) ≤ eps) (ℓ : ℕ) :
    Integrable (fun p => ((actLen eps (shPair P eps g ℓ) p).toNat : ℝ) ^ 2) (shP P) ∧
      ∫ p, ((actLen eps (shPair P eps g ℓ) p).toNat : ℝ) ^ 2 ∂(shP P) ≤
        K2 * (eps ^ 2 / vIn μ₀ σ₀) ^ 2 := by
  have hL := (layerOK_all (layerOK_input hg) (bAbs_le_bIn μ₀ σ₀) (βAbs_le_βIn _ _)
    (vIn_pos hg.mu_pos hg.sigma_pos) (vIn_le μ₀ σ₀) KcAbs_le_KcIn heps ℓ).1
  set Z := epLayerSeq eps g ℓ with hZ
  have hX := hL.law
  have hμ : 0 < lmean P Z := hX.mu_pos
  have hσ : 0 < lsig P Z := hX.sigma_pos
  have hκ : 0 ≤ lkap P Z := hX.kappa_nonneg
  have heps1 : 1 ≤ eps := le_trans (one_le_epsZero _ _) heps
  have hepspos : 0 < eps := by linarith
  obtain ⟨c1, c2, c3, c4, -, -, -⟩ := largeConditions hμ hσ hκ hL.var_le hL.third_le heps
  set G := lmean P Z ^ 2 * eps ^ 2 / lsig P Z ^ 2 with hGdef
  obtain ⟨-, -, -, hT2, -, -, -, hM2, -, -, -⟩ := oneLayer_bracket hX hepspos hGdef c1 c2 c3 c4
  have hvmin := vIn_pos hg.mu_pos hg.sigma_pos
  have hGv : G ≤ eps ^ 2 / vIn μ₀ σ₀ := by
    rw [hGdef, div_le_div_iff₀ (by positivity) hvmin]
    have := hL.var_ge
    nlinarith [sq_nonneg eps]
  have hG0 : 0 ≤ G := by positivity
  have hfun : (fun p : Ω × (ℕ → ℝ) => ((actLen eps (shPair P eps g ℓ) p).toNat : ℝ) ^ 2) =
      fun p => ((layerSegLen eps (fun t ω => (Z t ω).1) p.1).toNat : ℝ) ^ 2 := by
    funext p
    rw [actLen_shPair_eq eps g ℓ (shMean_pos hg heps ℓ).ne']
    rfl
  rw [hfun]
  refine ⟨hT2.comp_fst _, ?_⟩
  rw [shP, integral_fun_fst (fun ω => ((layerSegLen eps (fun t ω => (Z t ω).1) ω).toNat : ℝ) ^ 2)]
  simp only [probReal_univ, one_smul]
  refine hM2.trans ?_
  gcongr
  exact K2_pos.le

end

end PGM
