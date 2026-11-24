import PLAStochastic.Index.GEP.Shadow.CyclicReduction
import PLAStochastic.Index.GEP.Shadow.ConditionalGamma
import PLAStochastic.Index.GEP.OrbitClosure.OneLayerEnvelope

/-!
# WP3: local bounds for the first stopping time of the original input

`memory-route.md` §3 needs `P(T₀ = t) ≤ K E⁻¹ e^{-c t / E}` (`E = eps²`) for the actual
Model G input, with no density or exponential-moment assumption on the gap law
(pla-local `thm:local(d)`).  We obtain it from the cyclic-two reduction already used in WP2:

* every `t ≥ 1`: `P(T₀ = t) ≤ (2/t) P(𝒦_t ≥ 1) ≤ (2/t) · P(max_{j ≤ t} |S_j - j μ₀| > μ₀ eps/6)`
  and Kolmogorov's inequality give `P(T₀ = t) ≤ 72 σ₀² / (μ₀² eps²)`;
* `t ≥ 16`: a cyclic failure makes one of sixteen blocks of length `⌊t/8⌋` feasible
  (`cyclicCount_pos_block`), so `P(T₀ = t) ≤ (32/t) P(T₀ > ⌊t/8⌋)`, and the geometric
  tail of `T₀` (`layerSegLen_tail_of_large`) is exponential on the scale `eps²`.

The constants `locC`, `locK` depend only on `μ₀, σ₀`.  Nothing here uses the marks.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Finset
open scoped ENNReal

variable {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E] {P : Measure Ω}

/-! ## Injective reindexing of iid coordinates -/

/-- Injective reindexing of finitely many coordinates preserves the joint law. -/
theorem IIDSeqE.map_precomp {W : ℕ → Ω → E} (hW : IIDSeqE P W) {t : ℕ} {f : Fin t → ℕ}
    (hf : Function.Injective f) :
    P.map (fun ω (i : Fin t) => W (f i) ω) = P.map (fun ω (i : Fin t) => W (i : ℕ) ω) := by
  have e1 := (hW.indep.precomp hf).map_fun_eq_pi_map (fun i => (hW.measurable _).aemeasurable)
  have e2 := (hW.indep.precomp (g := fun i : Fin t => (i : ℕ)) Fin.val_injective).map_fun_eq_pi_map
    (fun i => (hW.measurable _).aemeasurable)
  simp only [(hW.ident _).map_eq] at e1 e2
  exact e1.trans e2.symm

/-- A block event has the same probability at every starting index. -/
theorem IIDSeqE.measure_block_shift {W : ℕ → Ω → E} (hW : IIDSeqE P W) (u m : ℕ)
    {E' : Set (Fin m → E)} (hE' : MeasurableSet E') :
    P {ω | (fun i : Fin m => W (u + i) ω) ∈ E'} =
      P {ω | (fun i : Fin m => W (i : ℕ) ω) ∈ E'} := by
  have h1 : Measurable (fun ω (i : Fin m) => W (u + i) ω) :=
    measurable_pi_lambda _ fun i => hW.measurable _
  have h2 : Measurable (fun ω (i : Fin m) => W (i : ℕ) ω) :=
    measurable_pi_lambda _ fun i => hW.measurable _
  have h := congrArg (fun μ : Measure (Fin m → E) => μ E')
    (hW.map_precomp (f := fun i : Fin m => u + (i : ℕ))
      (fun a b hab => Fin.val_injective (Nat.add_left_cancel hab)))
  simp only [Measure.map_apply h1 hE', Measure.map_apply h2 hE'] at h
  exact h

/-! ## The original input as normalised active pairs -/

variable [IsProbabilityMeasure P] {g : ℕ → Ω → ℝ} {μ₀ σ₀ κ₀ eps : ℝ}

/-- The pairs `(g t / μ₀, g t / μ₀)`; only their active coordinate is used. -/
def normGapPair (g : ℕ → Ω → ℝ) (μ₀ : ℝ) : ℕ → Ω → ℝ × ℝ :=
  fun t ω => (g t ω / μ₀, g t ω / μ₀)

omit [IsProbabilityMeasure P] in
theorem iidSeqE_normGapPair (hg : GapLaw P g μ₀ σ₀ κ₀) : IIDSeqE P (normGapPair g μ₀) :=
  (⟨hg.iid.measurable, hg.iid.indep, hg.iid.ident⟩ : IIDSeqE P g).comp
    (fun x => (x / μ₀, x / μ₀)) ((measurable_id.div_const _).prodMk (measurable_id.div_const _))

omit [MeasurableSpace Ω] [IsProbabilityMeasure P] in
theorem actLen_normGapPair (hμ : μ₀ ≠ 0) (ω : Ω) :
    actLen eps (normGapPair g μ₀) ω = layerSegLen eps g ω := by
  simp only [actLen, normGapPair, layerSegLen, div_eq_inv_mul]
  exact gapSegLen_const_mul eps _ (inv_ne_zero hμ)

omit [IsProbabilityMeasure P] in
theorem ae_pos_normGapPair (hg : GapLaw P g μ₀ σ₀ κ₀) (hpos : ∀ᵐ ω ∂P, 0 < g 0 ω) :
    ∀ᵐ ω ∂P, ∀ i, 0 < (normGapPair g μ₀ i ω).1 := by
  have hall : ∀ᵐ ω ∂P, ∀ i, 0 < g i ω :=
    ae_all_iff.mpr fun i => (hg.iid.ident i).symm.ae_snd measurableSet_Ioi hpos
  filter_upwards [hall] with ω hω i
  exact div_pos (hω i) hg.mu_pos

omit [MeasurableSpace Ω] [IsProbabilityMeasure P] in
theorem gapKeys_normGapPair (μ₀ : ℝ) (ω : Ω) (j : ℕ) :
    gapKeys (fun i => (normGapPair g μ₀ i ω).1) j = gapKeys (seq g ω) j / μ₀ := by
  simp only [gapKeys, normGapPair, seq, Finset.sum_div]

/-! ## Kolmogorov's inequality for the centred input walk -/

private theorem integral_partialSum_centred_sq' (hX : GapLaw P g μ₀ σ₀ κ₀) (n : ℕ) :
    ∫ ω, partialSum (centred g μ₀) n ω ^ 2 ∂P = n * σ₀ ^ 2 := by
  rw [partialSum_eq_weightedSum_one, integral_weightedSum_sq hX.indepIncrements
    (PredictableWeight.one _) (fun t => (hX.memLp_centred t).mono_exponent (by norm_num))
    hX.integral_centred]
  simp [hX.integral_centred_sq]

theorem measurable_partialSum_centred (hg : ∀ t, Measurable (g t)) (μ₀ : ℝ) (k : ℕ) :
    Measurable (partialSum (centred g μ₀) k) :=
  Finset.measurable_sum _ fun t _ => (hg t).sub_const μ₀

/-- The maximal deviation event of the centred walk up to time `n`. -/
def walkDev (g : ℕ → Ω → ℝ) (μ₀ lam : ℝ) (n : ℕ) : Set Ω :=
  {ω | ∃ k ≤ n, lam ≤ |partialSum (centred g μ₀) k ω|}

theorem measurableSet_walkDev (hg : ∀ t, Measurable (g t)) (μ₀ lam : ℝ) (n : ℕ) :
    MeasurableSet (walkDev g μ₀ lam n) := by
  have : walkDev g μ₀ lam n = ⋃ k, ⋃ (_ : k ≤ n), {ω | lam ≤ |partialSum (centred g μ₀) k ω|} := by
    ext ω; simp [walkDev]
  rw [this]
  exact MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun _ =>
    measurableSet_le measurable_const (measurable_partialSum_centred hg μ₀ k).abs

/-- Kolmogorov: `P(max_{k ≤ n} |S_k - k μ₀| ≥ lam) ≤ n σ₀² / lam²`. -/
theorem measureReal_walkDev_le (hg : GapLaw P g μ₀ σ₀ κ₀) {lam : ℝ} (hlam : 0 < lam) (n : ℕ) :
    P.real (walkDev g μ₀ lam n) ≤ n * σ₀ ^ 2 / lam ^ 2 := by
  have hk := kolmogorov_maximal hg.indepIncrements
    (fun t => (hg.memLp_centred t).mono_exponent (by norm_num)) hg.integral_centred hlam n
  rw [integral_partialSum_centred_sq' hg] at hk
  rw [le_div_iff₀ (by positivity), mul_comm]
  exact hk

/-! ## Uniform local bound: `P(T₀ = t) ≤ 72 σ₀² / (μ₀² eps²)` -/

omit [MeasurableSpace Ω] in
/-- A cyclic failure at `t` forces the centred walk to deviate by `μ₀ eps / 6` before `t`. -/
theorem walkDev_of_cyclicCount (hμ : 0 < μ₀) (heps : 0 ≤ eps) {t : ℕ} (ω : Ω)
    (h : 1 ≤ cyclicCount eps (fun i : Fin t => (normGapPair g μ₀ i ω).1)) :
    ω ∈ walkDev g μ₀ (μ₀ * eps / 6) t := by
  have hw := cyclicCount_pos_walk (eps := eps) (t := t) (r := t)
    (g := fun i => (normGapPair g μ₀ i ω).1) le_rfl h
  rw [Nat.sub_self] at hw
  rcases hw with ⟨j, hj, hlt⟩ | ⟨j, hj, hlt⟩
  · refine ⟨j, hj, ?_⟩
    rw [gapKeys_normGapPair, gapKeys_eq_centred g μ₀] at hlt
    have e : (j * μ₀ + partialSum (centred g μ₀) j ω) / μ₀ - j =
        partialSum (centred g μ₀) j ω / μ₀ := by field_simp; ring
    rw [e, abs_div, abs_of_pos hμ, lt_div_iff₀ hμ] at hlt
    linarith
  · exfalso
    have hj0 : j = 0 := by omega
    subst hj0
    simp only [gapKeys_zero, Nat.cast_zero, sub_zero, abs_zero] at hlt
    linarith

/-- **Uniform local bound** for the actual input, from cyclic-two and Kolmogorov. -/
theorem measureReal_layerSegLen_eq_le (hg : GapLaw P g μ₀ σ₀ κ₀) (hpos : ∀ᵐ ω ∂P, 0 < g 0 ω)
    (heps : 0 < eps) {t : ℕ} (ht : 0 < t) :
    P.real {ω | layerSegLen eps g ω = (t : ℕ∞)} ≤ 72 * σ₀ ^ 2 / (μ₀ ^ 2 * eps ^ 2) := by
  have hμ := hg.mu_pos
  have hV := iidSeqE_normGapPair hg
  have hposV := ae_pos_normGapPair hg hpos
  have hE := measurableSet_walkDev hg.iid.measurable μ₀ (μ₀ * eps / 6) t
  have hcyc := hV.actLen_sum_le_cyclic hposV heps.le ht hE
    (fun ω _ h => walkDev_of_cyclicCount hμ heps.le ω h) (A := Set.univ) MeasurableSet.univ
  simp only [Set.mem_univ, and_true, actLen_normGapPair hμ.ne'] at hcyc
  have hlam : 0 < μ₀ * eps / 6 := by positivity
  have hK := measureReal_walkDev_le hg hlam t
  have hreal : P.real {ω | layerSegLen eps g ω = (t : ℕ∞)} ≤
      2 / t * P.real (walkDev g μ₀ (μ₀ * eps / 6) t) := by
    have h := ENNReal.toReal_mono (by finiteness) hcyc
    rw [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_ofNat,
      ENNReal.toReal_natCast] at h
    have e : walkDev g μ₀ (μ₀ * eps / 6) t ∩ {_ω : Ω | True} =
        walkDev g μ₀ (μ₀ * eps / 6) t := by ext ω; simp
    rw [e] at h
    exact h
  have ht0 : (0 : ℝ) < t := by exact_mod_cast ht
  calc P.real {ω | layerSegLen eps g ω = (t : ℕ∞)}
      ≤ 2 / t * (t * σ₀ ^ 2 / (μ₀ * eps / 6) ^ 2) :=
        hreal.trans (mul_le_mul_of_nonneg_left hK (by positivity))
    _ = 72 * σ₀ ^ 2 / (μ₀ ^ 2 * eps ^ 2) := by
        field_simp
        ring

/-! ## Block bound for `t ≥ 16` -/

omit [IsProbabilityMeasure P] in
/-- A block event of the input has the tail probability of `T₀` at every start `u`. -/
theorem measure_block_lt_layerSegLen (hg : GapLaw P g μ₀ σ₀ κ₀) (u m : ℕ) :
    P {ω | (m : ℕ∞) < gapSegLen eps (fun i => g (u + i) ω)} =
      P {ω | (m : ℕ∞) < layerSegLen eps g ω} := by
  obtain ⟨E', hE', hiff⟩ := exists_prefix_set_lt_gapSegLen eps m
  have hW : IIDSeqE P g := ⟨hg.iid.measurable, hg.iid.indep, hg.iid.ident⟩
  have h1 : {ω | (m : ℕ∞) < gapSegLen eps (fun i => g (u + i) ω)} =
      {ω | (fun i : Fin m => g (u + i) ω) ∈ E'} := by
    ext ω; exact hiff _
  have h2 : {ω | (m : ℕ∞) < layerSegLen eps g ω} =
      {ω | (fun i : Fin m => g i ω) ∈ E'} := by
    ext ω; exact hiff (seq g ω)
  rw [h1, h2]
  exact hW.measure_block_shift u m hE'

omit [IsProbabilityMeasure P] in
/-- **Block bound**: for `t ≥ 16`, `P(T₀ = t) ≤ (2/t) · 16 · P(T₀ > ⌊t/8⌋)`. -/
theorem measure_layerSegLen_eq_le_block (hg : GapLaw P g μ₀ σ₀ κ₀)
    (hpos : ∀ᵐ ω ∂P, 0 < g 0 ω) (heps : 0 ≤ eps) {t : ℕ} (ht : 16 ≤ t) :
    P {ω | layerSegLen eps g ω = (t : ℕ∞)} ≤
      2 / (t : ℝ≥0∞) * (16 * P {ω | ((t / 8 : ℕ) : ℕ∞) < layerSegLen eps g ω}) := by
  classical
  have hμ := hg.mu_pos
  have hV := iidSeqE_normGapPair hg
  have hposV := ae_pos_normGapPair hg hpos
  set m := t / 8 with hm
  set S : ℕ → Set Ω := fun j => {ω | (m : ℕ∞) < gapSegLen eps (fun i => g (j * m + i) ω)}
    with hS
  have hSm : ∀ j, MeasurableSet (S j) := by
    intro j
    obtain ⟨E', hE', hiff⟩ := exists_prefix_set_lt_gapSegLen eps m
    have : S j = {ω | (fun i : Fin m => g (j * m + i) ω) ∈ E'} := by
      ext ω; exact hiff _
    rw [this]
    exact (measurable_pi_lambda _ fun i => hg.iid.measurable _) hE'
  have hE : MeasurableSet (⋃ j ∈ Finset.range 16, S j) :=
    Finset.measurableSet_biUnion _ fun j _ => hSm j
  have hsub : ∀ ω, (∀ i, 0 < (normGapPair g μ₀ i ω).1) →
      1 ≤ cyclicCount eps (fun i : Fin t => (normGapPair g μ₀ i ω).1) →
      ω ∈ ⋃ j ∈ Finset.range 16, S j := by
    intro ω hω h
    obtain ⟨j, hj16, -, hjT⟩ := cyclicCount_pos_block heps ht hω h
    refine Set.mem_iUnion₂.2 ⟨j, Finset.mem_range.2 hj16, ?_⟩
    show (m : ℕ∞) < gapSegLen eps (fun i => g (j * m + i) ω)
    have e : (fun i => (normGapPair g μ₀ (j * m + i) ω).1) =
        fun i => μ₀⁻¹ * g (j * m + i) ω := by
      funext i; simp [normGapPair, div_eq_inv_mul]
    rw [e, gapSegLen_const_mul eps _ (inv_ne_zero hμ.ne')] at hjT
    exact hjT
  have hcyc := hV.actLen_sum_le_cyclic hposV heps (by omega) hE hsub (A := Set.univ)
    MeasurableSet.univ
  simp only [Set.mem_univ, and_true, actLen_normGapPair hμ.ne'] at hcyc
  have e : (⋃ j ∈ Finset.range 16, S j) ∩ {_ω : Ω | True} = ⋃ j ∈ Finset.range 16, S j := by
    ext ω; simp
  rw [e] at hcyc
  refine hcyc.trans ?_
  gcongr
  calc P (⋃ j ∈ Finset.range 16, S j) ≤ ∑ j ∈ Finset.range 16, P (S j) :=
        measure_biUnion_finset_le _ _
    _ = ∑ j ∈ Finset.range 16, P {ω | (m : ℕ∞) < layerSegLen eps g ω} :=
        Finset.sum_congr rfl fun j _ => measure_block_lt_layerSegLen hg (j * m) m
    _ = 16 * P {ω | (m : ℕ∞) < layerSegLen eps g ω} := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; norm_num

/-! ## Exponential tail of `T₀` on the actual space -/

/-- The rate `tailRate · σ₀² / μ₀²` of the input stopping tail. -/
def inTailRate (μ₀ σ₀ : ℝ) : ℝ := tailRate * (σ₀ ^ 2 / μ₀ ^ 2)

theorem inTailRate_pos {μ₀ σ₀ : ℝ} (hμ : 0 < μ₀) (hσ : 0 < σ₀) : 0 < inTailRate μ₀ σ₀ := by
  unfold inTailRate; have := tailRate_pos; positivity

/-- `P(T₀ > m) ≤ (72/71) exp(-inTailRate · m / eps²)` for the actual input. -/
theorem measureReal_layerSegLen_gt_le_exp (hg : GapLaw P g μ₀ σ₀ κ₀)
    (heps : epsZero (bIn μ₀ σ₀) (βIn σ₀ (lkap P (inputPairs g))) ≤ eps) (m : ℕ) :
    P.real {ω | (m : ℕ∞) < layerSegLen eps g ω} ≤
      72 / 71 * Real.exp (-(inTailRate μ₀ σ₀) * m / eps ^ 2) := by
  have hL0 := layerOK_input hg
  set κ := lkap P (inputPairs g) with hκdef
  have hμ0 : lmean P (inputPairs g) = μ₀ := hg.mean
  have hv0 : lvar P (inputPairs g) = σ₀ ^ 2 := by unfold lvar; rw [hμ0]; exact hg.var
  have hs0 : lsig P (inputPairs g) = σ₀ := by
    unfold lsig; rw [hv0]; exact Real.sqrt_sq hg.sigma_pos.le
  have hX : GapLaw P g μ₀ σ₀ κ := by
    have := hL0.law
    rw [hμ0, hs0] at this
    exact this
  have hκ0 : 0 ≤ κ := le_trans (integral_nonneg fun _ => by positivity) hX.third
  have hv : σ₀ ^ 2 ≤ bIn μ₀ σ₀ * μ₀ ^ 2 := by
    have := hL0.var_le; rwa [hμ0, hs0] at this
  have hβ : κ ≤ βIn σ₀ κ * σ₀ ^ 3 := by
    have := hL0.third_le; rwa [hs0] at this
  have heps1 : 1 ≤ eps := (one_le_epsZero _ _).trans heps
  have hepspos : 0 < eps := by linarith
  obtain ⟨c1, c2, c3, c4, -, -, -⟩ := largeConditions hg.mu_pos hg.sigma_pos hκ0 hv hβ heps
  set G := μ₀ ^ 2 * eps ^ 2 / σ₀ ^ 2 with hG
  obtain ⟨L, hL1, hLG, htail⟩ := layerSegLen_tail_of_large hX hepspos hG c1 c2 c3 c4
  set j := m / L with hj
  have hsub : {ω | (m : ℕ∞) < layerSegLen eps g ω} ⊆
      {ω | ((j * L : ℕ) : ℕ∞) < layerSegLen eps g ω} := by
    intro ω hω
    have : j * L ≤ m := Nat.div_mul_le_self m L
    exact lt_of_le_of_lt (show ((j * L : ℕ) : ℕ∞) ≤ (m : ℕ∞) from Nat.cast_le.2 this) hω
  have hP : P.real {ω | (m : ℕ∞) < layerSegLen eps g ω} ≤ (71 / 72 : ℝ) ^ j :=
    (measureReal_mono hsub).trans (htail j)
  have hmL : (m : ℝ) < (j + 1) * L := by
    have : m < j * L + L := Nat.lt_div_mul_add (by omega)
    have : (m : ℝ) < (j * L + L : ℕ) := by exact_mod_cast this
    push_cast at this
    linarith
  have hσ2 : 0 < σ₀ ^ 2 := by have := hg.sigma_pos; positivity
  have hμ2 : 0 < μ₀ ^ 2 := by have := hg.mu_pos; positivity
  have hLv : (L : ℝ) * (σ₀ ^ 2 / μ₀ ^ 2) ≤ 5185 * eps ^ 2 := by
    have h1 : (L : ℝ) * (σ₀ ^ 2 / μ₀ ^ 2) ≤ 5185 * G * (σ₀ ^ 2 / μ₀ ^ 2) :=
      mul_le_mul_of_nonneg_right hLG (by positivity)
    refine h1.trans (le_of_eq ?_)
    have hμ := hg.mu_pos
    have hσ := hg.sigma_pos
    rw [hG]; field_simp
  have ha : 0 < Real.log (72 / 71) := Real.log_pos (by norm_num)
  have hr0 : 0 ≤ σ₀ ^ 2 / μ₀ ^ 2 := by positivity
  have hkey : inTailRate μ₀ σ₀ * m / eps ^ 2 ≤ Real.log (72 / 71) * (j + 1) := by
    rw [div_le_iff₀ (by positivity)]
    have h1 : (σ₀ ^ 2 / μ₀ ^ 2) * m ≤ (j + 1) * 5185 * eps ^ 2 := by
      have := mul_le_mul_of_nonneg_left hmL.le hr0
      have hj0 : (0 : ℝ) ≤ j + 1 := by positivity
      nlinarith
    unfold inTailRate tailRate
    calc Real.log (72 / 71) / 5185 * (σ₀ ^ 2 / μ₀ ^ 2) * m =
          Real.log (72 / 71) / 5185 * ((σ₀ ^ 2 / μ₀ ^ 2) * m) := by ring
      _ ≤ Real.log (72 / 71) / 5185 * ((j + 1) * 5185 * eps ^ 2) := by gcongr
      _ = Real.log (72 / 71) * (j + 1) * eps ^ 2 := by ring
  have e1 : (71 / 72 : ℝ) ^ j = Real.exp (Real.log (72 / 71)) *
      Real.exp (-(Real.log (72 / 71) * (j + 1))) := by
    rw [← Real.exp_add, show Real.log (72 / 71) + -(Real.log (72 / 71) * (j + 1)) =
      j * (-Real.log (72 / 71)) by ring, Real.exp_nat_mul, Real.exp_neg,
      Real.exp_log (by norm_num)]
    norm_num
  refine hP.trans ?_
  rw [e1, Real.exp_log (by norm_num)]
  gcongr
  rw [neg_mul, neg_div]
  linarith

/-! ## The local exponential bound `P(T₀ = t) ≤ locK eps⁻² e^{-locC t / eps²}` -/

/-- The local rate `inTailRate / 16`. -/
def locC (μ₀ σ₀ : ℝ) : ℝ := inTailRate μ₀ σ₀ / 16

/-- The local constant. -/
def locK (μ₀ σ₀ : ℝ) : ℝ :=
  max (72 * σ₀ ^ 2 / μ₀ ^ 2 * Real.exp (16 * locC μ₀ σ₀)) (32 * (72 / 71))

theorem locC_pos {μ₀ σ₀ : ℝ} (hμ : 0 < μ₀) (hσ : 0 < σ₀) : 0 < locC μ₀ σ₀ := by
  unfold locC; have := inTailRate_pos hμ hσ; positivity

theorem locK_pos (μ₀ σ₀ : ℝ) : 0 < locK μ₀ σ₀ :=
  lt_max_of_lt_right (by norm_num)

/-- **Local exponential bound** for the actual Model G input (pla-local `thm:local(d)`):
`P(T₀ = t) ≤ locK / eps² · exp(-locC t / eps²)` for every `t ≥ 1`. -/
theorem measureReal_layerSegLen_eq_le_exp (hg : GapLaw P g μ₀ σ₀ κ₀)
    (hpos : ∀ᵐ ω ∂P, 0 < g 0 ω)
    (heps : epsZero (bIn μ₀ σ₀) (βIn σ₀ (lkap P (inputPairs g))) ≤ eps) {t : ℕ} (ht : 1 ≤ t) :
    P.real {ω | layerSegLen eps g ω = (t : ℕ∞)} ≤
      locK μ₀ σ₀ / eps ^ 2 * Real.exp (-(locC μ₀ σ₀) * t / eps ^ 2) := by
  have hμ := hg.mu_pos
  have hσ := hg.sigma_pos
  have hc := locC_pos hμ hσ
  have heps1 : 1 ≤ eps := (one_le_epsZero _ _).trans heps
  have hepspos : 0 < eps := by linarith
  have hE1 : 1 ≤ eps ^ 2 := by nlinarith
  have hE : 0 < eps ^ 2 := by positivity
  have ht0 : (0 : ℝ) < t := by exact_mod_cast ht
  set c := locC μ₀ σ₀ with hcdef
  by_cases hsmall : (t : ℝ) ≤ 16 ∨ (t : ℝ) ≤ eps ^ 2
  · -- the uniform bound, absorbing `e^{-c t / eps²} ≥ e^{-16 c}`
    have hratio : (t : ℝ) / eps ^ 2 ≤ 16 := by
      rw [div_le_iff₀ hE]
      rcases hsmall with h | h
      · nlinarith
      · linarith
    have hexp : 1 ≤ Real.exp (16 * c) * Real.exp (-c * t / eps ^ 2) := by
      rw [← Real.exp_add]
      refine Real.one_le_exp ?_
      have : c * (t / eps ^ 2) ≤ c * 16 := mul_le_mul_of_nonneg_left hratio hc.le
      rw [neg_mul, neg_div, mul_div_assoc]
      linarith
    calc P.real {ω | layerSegLen eps g ω = (t : ℕ∞)}
        ≤ 72 * σ₀ ^ 2 / (μ₀ ^ 2 * eps ^ 2) :=
          measureReal_layerSegLen_eq_le hg hpos hepspos (by omega)
      _ = 72 * σ₀ ^ 2 / μ₀ ^ 2 / eps ^ 2 * 1 := by
          rw [mul_one, div_div]
      _ ≤ 72 * σ₀ ^ 2 / μ₀ ^ 2 / eps ^ 2 *
          (Real.exp (16 * c) * Real.exp (-c * t / eps ^ 2)) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = 72 * σ₀ ^ 2 / μ₀ ^ 2 * Real.exp (16 * c) / eps ^ 2 * Real.exp (-c * t / eps ^ 2) := by
          ring
      _ ≤ locK μ₀ σ₀ / eps ^ 2 * Real.exp (-c * t / eps ^ 2) := by
          gcongr
          exact le_max_left _ _
  · push Not at hsmall
    obtain ⟨h16, hbig⟩ := hsmall
    have ht16 : 16 ≤ t := by exact_mod_cast h16.le
    have hblock := measure_layerSegLen_eq_le_block hg hpos hepspos.le ht16
    set m := t / 8 with hm
    have hreal : P.real {ω | layerSegLen eps g ω = (t : ℕ∞)} ≤
        2 / t * (16 * P.real {ω | (m : ℕ∞) < layerSegLen eps g ω}) := by
      have h := ENNReal.toReal_mono (by finiteness) hblock
      rw [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_ofNat, ENNReal.toReal_natCast,
        ENNReal.toReal_mul, ENNReal.toReal_ofNat] at h
      exact h
    have htail := measureReal_layerSegLen_gt_le_exp hg heps m
    -- `⌊t/8⌋ ≥ t/16` for `t ≥ 16`
    have hm16 : (t : ℝ) / 16 ≤ m := by
      have h8 : t ≤ 8 * m + 7 := by omega
      have h8r : (t : ℝ) ≤ 8 * m + 7 := by exact_mod_cast h8
      rw [div_le_iff₀ (by norm_num)]
      linarith
    have hexp : Real.exp (-(inTailRate μ₀ σ₀) * m / eps ^ 2) ≤ Real.exp (-c * t / eps ^ 2) := by
      refine Real.exp_le_exp.2 ?_
      have hr := inTailRate_pos hμ hσ
      rw [hcdef, locC, neg_mul, neg_mul, neg_div, neg_div, neg_le_neg_iff,
        div_le_div_iff_of_pos_right hE]
      calc inTailRate μ₀ σ₀ / 16 * t = inTailRate μ₀ σ₀ * (t / 16) := by ring
        _ ≤ inTailRate μ₀ σ₀ * m := mul_le_mul_of_nonneg_left hm16 hr.le
    have h32 : 2 / (t : ℝ) * 16 ≤ 32 / eps ^ 2 := by
      rw [show 2 / (t : ℝ) * 16 = 32 / t by ring]
      exact div_le_div_of_nonneg_left (by norm_num) hE hbig.le
    calc P.real {ω | layerSegLen eps g ω = (t : ℕ∞)}
        ≤ 2 / t * (16 * P.real {ω | (m : ℕ∞) < layerSegLen eps g ω}) := hreal
      _ ≤ 2 / t * (16 * (72 / 71 * Real.exp (-(inTailRate μ₀ σ₀) * m / eps ^ 2))) := by
          gcongr
      _ ≤ 2 / t * (16 * (72 / 71 * Real.exp (-c * t / eps ^ 2))) := by gcongr
      _ = 2 / t * 16 * (72 / 71) * Real.exp (-c * t / eps ^ 2) := by ring
      _ ≤ 32 / eps ^ 2 * (72 / 71) * Real.exp (-c * t / eps ^ 2) := by gcongr
      _ = 32 * (72 / 71) / eps ^ 2 * Real.exp (-c * t / eps ^ 2) := by ring
      _ ≤ locK μ₀ σ₀ / eps ^ 2 * Real.exp (-c * t / eps ^ 2) := by
          gcongr
          exact le_max_right _ _

end

end PGM
