import PLAStochastic.Index.GEP.Shadow.LocalStop
import PLAStochastic.Index.GEP.Shadow.ConditionalGamma
import PLAStochastic.Index.GEP.Shadow.Variance
import PLAStochastic.Index.GEP.OrbitClosure.RegularClass

/-!
# WP3: the exponential density envelope of the first shadow layer

`memory-route.md` §3: given the gaps, the unnormalised layer-one mark is `Gamma(T₀, 1)`, so its
density is `h₁(a) = ∑_t P(T₀ = t) γ_t(a)`.  The local bound `P(T₀ = t) ≤ K E⁻¹ e^{-c t/E}`
(`measureReal_layerSegLen_eq_le_exp`) and the exponential series give
`h₁(a) ≤ K E⁻¹ e^{-(1 - e^{-c/E}) a}`; rescaling by `m₁ = C₀ ≍ E` yields a fixed envelope
`f_{Y₁}(z) ≤ envK1 · e^{-envC1 z}` whose constants depend only on `μ₀, σ₀`.

The original gap law may be lattice or heavy-tailed: only `GapLaw`, positivity and the
`epsZero` threshold enter.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Finset
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {g : ℕ → Ω → ℝ} {μ₀ σ₀ κ₀ eps : ℝ}

/-! ## The layer-one count is the first stopping time -/

omit [MeasurableSpace Ω] in
theorem epLayerSeq_one_zero_snd (eps : ℝ) (g : ℕ → Ω → ℝ) (ω : Ω) :
    (epLayerSeq eps g 1 0 ω).2 = (layerSegLen eps g ω).toNat := by
  change (nextLayer eps (inputPairs g) 0 ω).2 = _
  simp only [nextLayer, layerMap, Function.iterate_zero, id_eq, firstBlock, Prod.snd_sum,
    seq, inputPairs, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
  rfl

/-! ## The layer-one mark law is a Gamma mixture over `T₀` -/

/-- `Law(M₁) = ∑_{n} P(T₀ = n + 1) · Gamma(n + 1, 1)`. -/
theorem shP_mark_one_eq_tsum [IsProbabilityMeasure P] (hg : GapLaw P g μ₀ σ₀ κ₀)
    (heps : epsZero (bIn μ₀ σ₀) (βIn σ₀ (lkap P (inputPairs g))) ≤ eps)
    {A : Set ℝ} (hA : MeasurableSet A) :
    shP P {p | (shTri eps g 1 0 p).2 ∈ A} =
      ∑' n : ℕ, P {ω | layerSegLen eps g ω = ((n + 1 : ℕ) : ℕ∞)} *
        gammaMeasure ((n + 1 : ℕ) : ℝ) 1 A := by
  have hmeasM : Measurable fun p : Ω × (ℕ → ℝ) => (shTri eps g 1 0 p).2 :=
    (measurable_shTri hg.iid.measurable eps 1 0).snd
  have hN : Measurable fun ω => (epLayerSeq eps g 1 0 ω).2 :=
    (measurable_epLayerSeq_entry hg.iid.measurable eps 1 0).snd
  set B : ℕ → Set (Ω × (ℕ → ℝ)) := fun n =>
    {p | (shTri eps g 1 0 p).2 ∈ A ∧ (epLayerSeq eps g 1 0 p.1).2 = n + 1} with hB
  have hBm : ∀ n, MeasurableSet (B n) := fun n =>
    (hmeasM hA).inter ((hN (measurableSet_singleton (n + 1))).preimage measurable_fst)
  have hdisj : Pairwise (Function.onFun Disjoint B) := by
    intro i j hij
    refine Set.disjoint_left.2 fun p hi hj => hij ?_
    have := hi.2.symm.trans hj.2
    omega
  have hae : {p | (shTri eps g 1 0 p).2 ∈ A} =ᵐ[shP P] ⋃ n, B n := by
    have hmp : MeasurePreserving Prod.fst (shP P) P := measurePreserving_fst
    have h1 := hmp.quasiMeasurePreserving.ae (ae_one_le_epLayerSeq_count hg heps 1 0)
    filter_upwards [h1] with p hp
    apply propext
    constructor
    · intro h
      exact Set.mem_iUnion.2 ⟨(epLayerSeq eps g 1 0 p.1).2 - 1, h, by
        show (epLayerSeq eps g 1 0 p.1).2 = (epLayerSeq eps g 1 0 p.1).2 - 1 + 1
        omega⟩
    · intro h
      obtain ⟨n, hn, -⟩ := Set.mem_iUnion.1 h
      exact hn
  rw [measure_congr hae, measure_iUnion hdisj hBm]
  refine tsum_congr fun n => ?_
  rw [hB]
  simp only
  rw [measure_shTri_mark_count hg.iid.measurable eps 1 0 (by omega : 1 ≤ n + 1) hA]
  congr 2
  ext ω
  simp only [Set.mem_ofPred_eq, epLayerSeq_one_zero_snd]
  exact ENat.toNat_eq_iff (by omega)

/-! ## The Gamma mixture with geometric weights -/

/-- `γ_{n+1}(x) = x^n e^{-x} / n!` for `x ≥ 0`. -/
theorem gammaPDF_succ_eq {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    gammaPDF ((n + 1 : ℕ) : ℝ) 1 x = ENNReal.ofReal (x ^ n * Real.exp (-x) / n.factorial) := by
  rw [gammaPDF_of_nonneg hx]
  congr 1
  push_cast
  rw [Real.Gamma_nat_eq_factorial, add_sub_cancel_right, Real.rpow_natCast, Real.one_rpow,
    one_mul]
  ring

/-- `∑_n K r^{n+1} x^n e^{-x} / n! = K r e^{-(1-r) x} ≤ K e^{-(1-r) x}`. -/
theorem tsum_gamma_mixture_le {K r : ℝ} (hK : 0 ≤ K) (hr0 : 0 < r) (hr1 : r ≤ 1) {x : ℝ}
    (hx : 0 ≤ x) :
    ∑' n : ℕ, ENNReal.ofReal (K * r ^ (n + 1)) *
        ENNReal.ofReal (x ^ n * Real.exp (-x) / n.factorial) ≤
      ENNReal.ofReal (K * Real.exp (-(1 - r) * x)) := by
  have hterm : ∀ n : ℕ, ENNReal.ofReal (K * r ^ (n + 1)) *
      ENNReal.ofReal (x ^ n * Real.exp (-x) / n.factorial) =
        ENNReal.ofReal (K * r * Real.exp (-x) * ((r * x) ^ n / n.factorial)) := by
    intro n
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [mul_pow, pow_succ]
    ring
  simp_rw [hterm]
  have hsum : Summable fun n : ℕ => K * r * Real.exp (-x) * ((r * x) ^ n / n.factorial) :=
    (Real.summable_pow_div_factorial (r * x)).mul_left _
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsum, tsum_mul_left]
  have hexp : ∑' n : ℕ, (r * x) ^ n / (n.factorial : ℝ) = Real.exp (r * x) := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  rw [hexp]
  refine ENNReal.ofReal_le_ofReal ?_
  have e : K * r * Real.exp (-x) * Real.exp (r * x) = K * r * Real.exp (-(1 - r) * x) := by
    rw [mul_assoc (K * r), ← Real.exp_add]
    congr 2
    ring
  rw [e]
  have h1 : Real.exp (-(1 - r) * x) * (K * r) ≤ Real.exp (-(1 - r) * x) * K :=
    mul_le_mul_of_nonneg_left (by nlinarith) (Real.exp_pos _).le
  linarith

/-! ## The envelope of the unnormalised layer-one mark -/

/-- The unnormalised rate `1 - e^{-locC / eps²}`. -/
def rawC1 (μ₀ σ₀ eps : ℝ) : ℝ := 1 - Real.exp (-(locC μ₀ σ₀) / eps ^ 2)

variable [IsProbabilityMeasure P]

/-- `Law(M₁) ≤ (locK / eps²) e^{-rawC1 · x} 1_{x > 0} dx`. -/
theorem map_shTri_mark_one_le (hg : GapLaw P g μ₀ σ₀ κ₀) (hpos : ∀ᵐ ω ∂P, 0 < g 0 ω)
    (heps : epsZero (bIn μ₀ σ₀) (βIn σ₀ (lkap P (inputPairs g))) ≤ eps) :
    (shP P).map (fun p => (shTri eps g 1 0 p).2) ≤
      volume.withDensity fun x =>
        ENNReal.ofReal (envFun (locK μ₀ σ₀ / eps ^ 2) (rawC1 μ₀ σ₀ eps) x) := by
  have hmeasM : Measurable fun p : Ω × (ℕ → ℝ) => (shTri eps g 1 0 p).2 :=
    (measurable_shTri hg.iid.measurable eps 1 0).snd
  have heps1 : 1 ≤ eps := (one_le_epsZero _ _).trans heps
  have hE : 0 < eps ^ 2 := by positivity
  set K := locK μ₀ σ₀ / eps ^ 2 with hKdef
  have hK0 : 0 ≤ K := by have := locK_pos μ₀ σ₀; positivity
  set r := Real.exp (-(locC μ₀ σ₀) / eps ^ 2) with hrdef
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r ≤ 1 := by
    rw [hrdef]
    refine Real.exp_le_one_iff.2 ?_
    have := locC_pos hg.mu_pos hg.sigma_pos
    rw [neg_div]
    linarith [div_pos this hE]
  -- the weights
  have hq : ∀ n : ℕ, P {ω | layerSegLen eps g ω = ((n + 1 : ℕ) : ℕ∞)} ≤
      ENNReal.ofReal (K * r ^ (n + 1)) := by
    intro n
    rw [← ofReal_measureReal]
    refine ENNReal.ofReal_le_ofReal ?_
    refine (measureReal_layerSegLen_eq_le_exp hg hpos heps (by omega)).trans (le_of_eq ?_)
    rw [hKdef, hrdef, ← Real.exp_nat_mul]
    congr 2
    push_cast
    ring
  rw [Measure.le_iff]
  intro A hA
  rw [Measure.map_apply hmeasM hA]
  change shP P {p | (shTri eps g 1 0 p).2 ∈ A} ≤ _
  rw [shP_mark_one_eq_tsum hg heps hA, withDensity_apply _ hA]
  have hgm : ∀ n : ℕ, Measurable (gammaPDF ((n + 1 : ℕ) : ℝ) 1) := fun n =>
    (measurable_gammaPDFReal _ _).ennreal_ofReal
  calc ∑' n : ℕ, P {ω | layerSegLen eps g ω = ((n + 1 : ℕ) : ℕ∞)} *
        gammaMeasure ((n + 1 : ℕ) : ℝ) 1 A
      ≤ ∑' n : ℕ, ENNReal.ofReal (K * r ^ (n + 1)) * ∫⁻ x in A, gammaPDF ((n + 1 : ℕ) : ℝ) 1 x := by
        refine ENNReal.tsum_le_tsum fun n => ?_
        rw [gammaMeasure, withDensity_apply _ hA]
        exact mul_le_mul' (hq n) le_rfl
    _ = ∫⁻ x in A, ∑' n : ℕ, ENNReal.ofReal (K * r ^ (n + 1)) * gammaPDF ((n + 1 : ℕ) : ℝ) 1 x := by
        simp_rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        exact (lintegral_tsum fun n => ((hgm n).const_mul _).aemeasurable).symm
    _ ≤ ∫⁻ x in A, ENNReal.ofReal (envFun K (1 - r) x) := by
        refine lintegral_mono_ae (ae_restrict_of_ae ?_)
        have hne : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ 0 := by
          rw [ae_iff]
          simp
        filter_upwards [hne] with x hx
        rcases lt_or_gt_of_ne hx with hneg | hposx
        · simp only [gammaPDF_of_neg hneg, mul_zero, tsum_zero]
          exact zero_le
        · simp only [envFun, Set.indicator_of_mem (show x ∈ Ioi (0 : ℝ) from hposx)]
          simp_rw [gammaPDF_succ_eq hposx.le]
          exact tsum_gamma_mixture_le hK0 hr0 hr1 hposx.le

/-! ## Normalisation: the first shadow law -/

/-- The first-layer envelope constant. -/
def envK1 (μ₀ σ₀ : ℝ) : ℝ := cPlus * locK μ₀ σ₀ / vIn μ₀ σ₀

/-- The first-layer envelope rate. -/
def envC1 (μ₀ σ₀ : ℝ) : ℝ := locC μ₀ σ₀ / (256 * bIn μ₀ σ₀)

theorem envK1_pos {μ₀ σ₀ : ℝ} (hμ : 0 < μ₀) (hσ : 0 < σ₀) : 0 < envK1 μ₀ σ₀ := by
  unfold envK1
  have := locK_pos μ₀ σ₀
  have := cPlus_pos
  have := vIn_pos hμ hσ
  positivity

theorem envC1_pos {μ₀ σ₀ : ℝ} (hμ : 0 < μ₀) (hσ : 0 < σ₀) : 0 < envC1 μ₀ σ₀ := by
  unfold envC1
  have := locC_pos hμ hσ
  have : 0 < bIn μ₀ σ₀ := bAbs_pos.trans_le (bAbs_le_bIn μ₀ σ₀)
  positivity

/-- `1 - e^{-u} ≥ u / 2` for `0 ≤ u ≤ 1`. -/
theorem one_sub_exp_neg_ge_half {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    u / 2 ≤ 1 - Real.exp (-u) := by
  have h1 : Real.exp (-u) ≤ 1 / (1 + u) := by
    rw [Real.exp_neg, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by linarith) (by linarith [Real.add_one_le_exp u])
  have h2 : 1 / (1 + u) ≤ 1 - u / 2 := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  linarith

/-- `tailRate ≤ 1`. -/
theorem tailRate_le_one : tailRate ≤ 1 := by
  unfold tailRate
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 72 / 71 by norm_num)
  rw [div_le_one (by norm_num)]
  linarith

/-- **The first shadow law has a fixed exponential density envelope** (`memory-route.md`
§3), with constants depending only on `μ₀, σ₀`; the original gap law may be lattice or
heavy-tailed. -/
theorem envBd_shLaw_one (hg : GapLaw P g μ₀ σ₀ κ₀) (hpos : ∀ᵐ ω ∂P, 0 < g 0 ω)
    (heps : epsZero (bIn μ₀ σ₀) (βIn σ₀ (lkap P (inputPairs g))) ≤ eps) :
    EnvBd (envK1 μ₀ σ₀) (envC1 μ₀ σ₀) (shLaw P eps g 1) := by
  have hμ := hg.mu_pos
  have hσ := hg.sigma_pos
  have heps1 : 1 ≤ eps := (one_le_epsZero _ _).trans heps
  have hE : 0 < eps ^ 2 := by positivity
  have hb : 0 < bIn μ₀ σ₀ := bAbs_pos.trans_le (bAbs_le_bIn μ₀ σ₀)
  have hv := vIn_pos hμ hσ
  have hcP := cPlus_pos
  have hlocK := locK_pos μ₀ σ₀
  have hlocC := locC_pos hμ hσ
  -- the normalisation constant `C = m₁ = segMean₀`
  set C := shCount P eps g 1 with hCdef
  have hL := layerOK_all (layerOK_input hg) (bAbs_le_bIn μ₀ σ₀) (βAbs_le_βIn _ _) hv
    (vIn_le μ₀ σ₀) KcAbs_le_KcIn heps 0
  have hCeq : C = segMean P eps (epLayerSeq eps g 0) := by
    rw [hCdef, shCount_succ hg heps 0, shCount_zero, one_mul, actMean_shPair_eq_segMean hg heps 0]
  have hCm : eps ^ 2 / (128 * bIn μ₀ σ₀) ≤ C := hCeq ▸ hL.2.2.2.1
  have hCp : C ≤ cPlus * eps ^ 2 / vIn μ₀ σ₀ := hCeq ▸ hL.2.2.2.2
  have hC : 0 < C := lt_of_lt_of_le (by positivity) hCm
  -- `Law(Y₁) = Law(M₁) / C`
  have hlaw : shLaw P eps g 1 = ((shP P).map (fun p => (shTri eps g 1 0 p).2)).map
      (fun x => x / C) := by
    have hdiv : Measurable fun x : ℝ => x / C := measurable_id.div_const C
    rw [shLaw, Measure.map_map hdiv (measurable_shTri hg.iid.measurable eps 1 0).snd]
    rfl
  have hmap := map_div_const_le (map_shTri_mark_one_le hg hpos heps) hC
  unfold EnvBd
  rw [hlaw]
  refine hmap.trans (withDensity_mono (Filter.Eventually.of_forall fun z => ?_))
  refine ENNReal.ofReal_le_ofReal ?_
  simp only [envFun, Set.indicator_apply, Set.mem_Ioi]
  by_cases hz : 0 < z
  · have hCz : 0 < C * z := mul_pos hC hz
    rw [if_pos hCz, if_pos hz]
    -- `C / eps² ∈ [1/(128 b), cPlus / vIn]`
    have h1 : C / eps ^ 2 ≤ cPlus / vIn μ₀ σ₀ := by
      rw [div_le_div_iff₀ hE hv]
      rw [le_div_iff₀ hv] at hCp
      linarith
    have h2 : 1 / (128 * bIn μ₀ σ₀) ≤ C / eps ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) hE]
      rw [div_le_iff₀ (by positivity)] at hCm
      linarith
    -- `rawC1 · C ≥ envC1`: `1 - e^{-u} ≥ u/2` with `u = locC / eps² ≤ 1`
    have hu1 : locC μ₀ σ₀ / eps ^ 2 ≤ 1 := by
      rw [div_le_one hE]
      have hκ0 : 0 ≤ lkap P (inputPairs g) := by
        have hL0 := layerOK_input hg
        exact le_trans (integral_nonneg fun _ => by positivity) hL0.law.third
      have hμ0 : lmean P (inputPairs g) = μ₀ := hg.mean
      have hv0 : lvar P (inputPairs g) = σ₀ ^ 2 := by unfold lvar; rw [hμ0]; exact hg.var
      have hs0 : lsig P (inputPairs g) = σ₀ := by
        unfold lsig; rw [hv0]; exact Real.sqrt_sq hσ.le
      have hL0 := layerOK_input hg
      have hvb : σ₀ ^ 2 ≤ bIn μ₀ σ₀ * μ₀ ^ 2 := by
        have := hL0.var_le; rwa [hμ0, hs0] at this
      have hβ : lkap P (inputPairs g) ≤ βIn σ₀ (lkap P (inputPairs g)) * σ₀ ^ 3 := by
        have := hL0.third_le; rwa [hs0] at this
      obtain ⟨c1, -, -, -, -, -, -⟩ := largeConditions hμ hσ hκ0 hvb hβ heps
      have hratio : σ₀ ^ 2 / μ₀ ^ 2 ≤ eps ^ 2 / 10000 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        rw [le_div_iff₀ (by positivity)] at c1
        nlinarith
      have htr := tailRate_le_one
      have htr0 := tailRate_pos
      unfold locC inTailRate
      have : tailRate * (σ₀ ^ 2 / μ₀ ^ 2) ≤ 1 * (eps ^ 2 / 10000) :=
        mul_le_mul htr hratio (by positivity) zero_le_one
      linarith
    have hraw : locC μ₀ σ₀ / eps ^ 2 / 2 ≤ rawC1 μ₀ σ₀ eps := by
      unfold rawC1
      rw [neg_div]
      exact one_sub_exp_neg_ge_half (by positivity) hu1
    have hraw0 : 0 ≤ rawC1 μ₀ σ₀ eps := le_trans (by positivity) hraw
    have hexp : Real.exp (-rawC1 μ₀ σ₀ eps * (C * z)) ≤ Real.exp (-envC1 μ₀ σ₀ * z) := by
      refine Real.exp_le_exp.2 ?_
      rw [neg_mul, neg_mul, neg_le_neg_iff]
      calc envC1 μ₀ σ₀ * z = locC μ₀ σ₀ / eps ^ 2 / 2 * (eps ^ 2 / (128 * bIn μ₀ σ₀)) * z := by
            unfold envC1; field_simp; ring
        _ ≤ rawC1 μ₀ σ₀ eps * C * z := by
            gcongr
        _ = rawC1 μ₀ σ₀ eps * (C * z) := by ring
    calc C * (locK μ₀ σ₀ / eps ^ 2 * Real.exp (-rawC1 μ₀ σ₀ eps * (C * z)))
        = C / eps ^ 2 * locK μ₀ σ₀ * Real.exp (-rawC1 μ₀ σ₀ eps * (C * z)) := by ring
      _ ≤ cPlus / vIn μ₀ σ₀ * locK μ₀ σ₀ * Real.exp (-envC1 μ₀ σ₀ * z) := by gcongr
      _ = envK1 μ₀ σ₀ * Real.exp (-envC1 μ₀ σ₀ * z) := by unfold envK1; ring
  · have hCz : ¬ 0 < C * z := not_lt.2 (mul_nonpos_of_nonneg_of_nonpos hC.le (not_lt.1 hz))
    rw [if_neg hCz, if_neg hz, mul_zero]

/-- **The first shadow law is a regular law**: the envelope above together with the
mean-one normalisation and the variance bracket of `GEPShadowVariance`.  The variance
bracket carries the explicit scale conditions `hscale`, `hsmall` of that module. -/
theorem regLaw_shLawPM_one (hg : GapLaw P g μ₀ σ₀ κ₀) (hpos : ∀ᵐ ω ∂P, 0 < g 0 ω)
    (heps : epsZero (bIn μ₀ σ₀) (βIn σ₀ (lkap P (inputPairs g))) ≤ eps)
    (hscale : cBr (bIn μ₀ σ₀) (vIn μ₀ σ₀) ≤ eps ^ 2)
    (hsmall : 4 * cBr (bIn μ₀ σ₀) (vIn μ₀ σ₀) * (σ₀ ^ 2 / μ₀ ^ 2 + 1) ≤
      vIn μ₀ σ₀ * eps ^ 2) :
    RegLaw (envK1 μ₀ σ₀) (envC1 μ₀ σ₀) (vIn μ₀ σ₀ / 4) KcIn
      (shLawPM P hg.iid.measurable eps 1) :=
  regLaw_of_envBd_of_moments (lawMean_shLawPM hg heps 1)
    (shLaw_variance_bracket hg heps hscale hsmall le_rfl).1
    (shLaw_variance_bracket hg heps hscale hsmall le_rfl).2
    (envBd_shLaw_one hg hpos heps) (envK1_pos hg.mu_pos hg.sigma_pos).le

end

end PGM
