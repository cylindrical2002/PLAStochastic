import PLAStochastic.Index.KRE.Uniform.HeightRecursion
import PLAStochastic.Index.KRE.Uniform.LayerBounds

/-!
# `thm:uniform`: the ALG-RE height under Model K, uniformly in the nonuniformity

The theorem of `research/2026-09-24-re-curvature-uniform/tex/main.tex`.  Fix class parameters
(`DensityClassParams`) and let `𝔉_δ` be the densities on `[0, 1]` with `f₋ ≤ f ≤ f₊`,
`Lip f ≤ δ L` and `|f b - f a| ≥ δ V` (`DensityClassParams.Mem`).  Along every HEIGHT sequence
`N → ∞`, `ε → ∞`, `log ε = o(log N)`:

* `K_RE_uniform`: eventually an event `G` of the exponential variables alone, with
  `P(Gᶜ) ≤ K / N²`, carries
  `|H - log₂ (log N / log ε) - log₂⁺ (log N / log (ε / δ))| ≤ K` simultaneously for every
  `δ ∈ [0, 1]` and every `f ∈ 𝔉_δ`, where `H` is the ALG-RE height on the Rényi keys of `f`;
* `K_RE_uniform_integral`: the same bound for the expected height of the sorted iid sample;
* `cor:cases`: `K_RE_fixed_density` (a fixed nonconstant density gives
  `2 log₂ (log N / log ε) + O_f(1)`), `K_RE_uniform_small` (`δ ≤ N^{-1/2}` gives the Model G
  value `log₂ (log N / log ε) + O(1)`) and `K_RE_uniform_ratio` (the ratio limit `1 + θ`).

The good event is `(kreBad expCoord N ε (tRE N) (jK N))ᶜ`.  On it the per-layer bounds hold
(`uniformLayerFacts_of_good`), and the deterministic two-phase recursion turns them into the
height bound (`twoPhase_of_layerFacts`).
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Finset Filter Topology

universe u

/-! ## The pathwise theorem -/

/-- **`thm:uniform`, pathwise.**  For fixed class parameters there is `K` such that along every
HEIGHT sequence, eventually, an event `G` of the canonical exponential sequence alone, with
`P(Gᶜ) ≤ K / N²`, carries `|H - twoPhase N ε δ| ≤ K` for every `δ ∈ [0, 1]` and every
`f ∈ 𝔉_δ`, where `H` is the ALG-RE height on the Rényi keys of `f`. -/
theorem K_RE_uniform (c : DensityClassParams) :
    ∃ K : ℝ, ∀ {N : ℕ → ℕ} {ε : ℕ → ℝ},
      Tendsto (fun k => (N k : ℝ)) atTop atTop → Tendsto ε atTop atTop →
      Tendsto (fun k => Real.log (ε k) / Real.log (N k)) atTop (𝓝 0) →
      ∀ᶠ k in atTop, ∃ G : Set (ℕ → ℝ), MeasurableSet G ∧
        expSeqMeasure.real Gᶜ ≤ K / (N k : ℝ) ^ 2 ∧
        ∀ ω ∈ G, ∀ δ : ℝ, ∀ f : ℝ → ℝ, c.Mem δ f →
          |(reHeight (ε k) (renyiKeys f (N k) ω) (N k) : ℝ) - twoPhase (N k) (ε k) δ| ≤ K := by
  obtain ⟨cN, CN, Cu, C0, c1, c2, c3, KL, hcN, hCN, hCu, hC0, hc1, hc2, hc3, hKL, hlay⟩ :=
    uniformLayerFacts_of_good c
  obtain ⟨K₁, hK₁⟩ := twoPhase_of_layerFacts hcN hCN hCu hC0 hc1 hc2 hc3 hKL
  refine ⟨max K₁ 63, fun {N ε} hN hε hεN => ?_⟩
  filter_upwards [hlay hN hε hεN, hK₁ hN hε hεN, hN.eventually_ge_atTop 160000,
    hε.eventually_ge_atTop (2 * epsZero 1 18)] with k hL hR h160 he
  have h160' : 160000 ≤ N k := by exact_mod_cast h160
  have hn1 : 1 ≤ N k := by omega
  refine ⟨(kreBad expCoord (N k) (ε k) (tRE (N k)) (jK (N k)))ᶜ,
    (measurableSet_kreBad measurable_expCoord _ _ _ _).compl, ?_, ?_⟩
  · rw [compl_compl]
    have hbad := measureReal_kreBad_le iidSeq_expCoord (hasLaw_expCoord 0) hn1
      (eps := ε k) (by linarith) (tRE (N k)) (jK (N k))
    have hmass := kreBadMass_le hn1
    have hN2 : (0 : ℝ) < (N k : ℝ) ^ 2 := by positivity
    have : (63 : ℝ) / (N k : ℝ) ^ 2 ≤ max K₁ 63 / (N k : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right (le_max_right _ _) hN2.le
    linarith
  · intro ω hω δ f hf
    exact (hR _ δ hf.1 hf.2.1 (hL ω (by simpa using hω) δ f hf)).trans (le_max_left _ _)

/-! ## The two terms of `twoPhase` -/

/-- Eventually along HEIGHT, for every `δ ∈ [0, 1]`, the second term of `twoPhase` lies between
`0` and the first term, and the first term is at most `log₂ log N`. -/
theorem eventually_twoPhase_terms {N : ℕ → ℕ} {ε : ℕ → ℝ}
    (hN : Tendsto (fun k => (N k : ℝ)) atTop atTop) (hε : Tendsto ε atTop atTop)
    (hεN : Tendsto (fun k => Real.log (ε k) / Real.log (N k)) atTop (𝓝 0)) :
    ∀ᶠ k in atTop, ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 →
      0 ≤ (if δ = 0 then 0 else max 0 (Real.logb 2 (Real.log (N k) / Real.log (ε k / δ)))) ∧
      (if δ = 0 then 0 else max 0 (Real.logb 2 (Real.log (N k) / Real.log (ε k / δ)))) ≤
        Real.logb 2 (Real.log (N k) / Real.log (ε k)) ∧
      Real.logb 2 (Real.log (N k) / Real.log (ε k)) ≤ Real.logb 2 (Real.log (N k)) := by
  have hL : Tendsto (fun k => Real.log (N k)) atTop atTop := Real.tendsto_log_atTop.comp hN
  filter_upwards [hε.eventually_ge_atTop (Real.exp 1), hL.eventually_gt_atTop 0,
    hεN.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1))]
    with k he hLpos hratio δ hδ0 hδ1
  set Y := Real.log (N k)
  have hε0 : 0 < ε k := lt_of_lt_of_le (Real.exp_pos 1) he
  have hlogε : 1 ≤ Real.log (ε k) := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) he
  have hεY : Real.log (ε k) ≤ Y := by
    rw [div_le_one hLpos] at hratio; exact hratio
  have hr1 : 1 ≤ Y / Real.log (ε k) := by rw [le_div_iff₀ (by linarith)]; linarith
  have hΦ1 : 0 ≤ Real.logb 2 (Y / Real.log (ε k)) := Real.logb_nonneg (by norm_num) hr1
  have hΦ1le : Real.logb 2 (Y / Real.log (ε k)) ≤ Real.logb 2 Y :=
    Real.logb_le_logb_of_le (by norm_num) (by positivity) (div_le_self hLpos.le hlogε)
  refine ⟨?_, ?_, hΦ1le⟩ <;> split_ifs with h0
  · exact le_rfl
  · exact le_max_left _ _
  · exact hΦ1
  · have hδ : 0 < δ := lt_of_le_of_ne hδ0 (Ne.symm h0)
    have hge : Real.log (ε k) ≤ Real.log (ε k / δ) :=
      Real.log_le_log hε0 (le_div_self hε0.le hδ hδ1)
    refine max_le hΦ1 ?_
    apply Real.logb_le_logb_of_le (by norm_num)
    · exact div_pos hLpos (by linarith)
    · exact div_le_div_of_nonneg_left hLpos.le (by linarith) hge

/-! ## Expectation -/

/-- Eventually along HEIGHT, `0 ≤ twoPhase N ε δ ≤ 4 N` for every `δ ∈ [0, 1]`. -/
theorem eventually_twoPhase_mem {N : ℕ → ℕ} {ε : ℕ → ℝ}
    (hN : Tendsto (fun k => (N k : ℝ)) atTop atTop) (hε : Tendsto ε atTop atTop)
    (hεN : Tendsto (fun k => Real.log (ε k) / Real.log (N k)) atTop (𝓝 0)) :
    ∀ᶠ k in atTop, ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 →
      0 ≤ twoPhase (N k) (ε k) δ ∧ twoPhase (N k) (ε k) δ ≤ 4 * (N k : ℝ) := by
  have hL : Tendsto (fun k => Real.log (N k)) atTop atTop := Real.tendsto_log_atTop.comp hN
  filter_upwards [eventually_twoPhase_terms hN hε hεN, hL.eventually_gt_atTop 0,
    hN.eventually_ge_atTop 1] with k hk hLpos hN1 δ hδ0 hδ1
  obtain ⟨h1, h2, h3⟩ := hk δ hδ0 hδ1
  set Y := Real.log (N k)
  have hYN : Real.logb 2 Y ≤ 2 * (N k : ℝ) := by
    have h1 : Real.logb 2 Y ≤ Y / Real.log 2 := by
      rw [Real.logb]; exact div_le_div_of_nonneg_right
        ((Real.log_le_sub_one_of_pos hLpos).trans (by linarith)) (Real.log_pos one_lt_two).le
    have h2 : Y ≤ N k - 1 := Real.log_le_sub_one_of_pos (by linarith)
    have h3 : (1 / 2 : ℝ) ≤ Real.log 2 := by
      have := Real.log_two_gt_d9; linarith
    have hY0 : 0 ≤ Y := hLpos.le
    have : Y / Real.log 2 ≤ 2 * Y := by
      rw [div_le_iff₀ (Real.log_pos one_lt_two)]; nlinarith
    linarith
  unfold twoPhase
  constructor <;> linarith

/-- **`thm:uniform`, expectation.**  For fixed class parameters there is `K` such that along
every HEIGHT sequence, eventually, for every `δ ∈ [0, 1]`, every `f ∈ 𝔉_δ` and every iid
sample with density `f`, the expected ALG-RE height of the sorted sample is within `K` of
`twoPhase N ε δ`. -/
theorem K_RE_uniform_integral (c : DensityClassParams) :
    ∃ K : ℝ, ∀ {N : ℕ → ℕ} {ε : ℕ → ℝ},
      Tendsto (fun k => (N k : ℝ)) atTop atTop → Tendsto ε atTop atTop →
      Tendsto (fun k => Real.log (ε k) / Real.log (N k)) atTop (𝓝 0) →
      ∀ᶠ k in atTop, ∀ δ : ℝ, ∀ f : ℝ → ℝ, c.Mem δ f →
        ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (X : ℕ → Ω → ℝ), (∀ i, HasLaw (X i) (densityLaw f 0 1) P) → iIndepFun X P →
          |∫ ω, (reHeight (ε k) (kKeys X (N k) ω) (N k) : ℝ) ∂P - twoPhase (N k) (ε k) δ| ≤ K := by
  obtain ⟨K, hK⟩ := K_RE_uniform c
  refine ⟨|K| + 1, fun {N ε} hN hε hεN => ?_⟩
  have hsmall : ∀ᶠ k in atTop, 5 * |K| / (N k : ℝ) ≤ 1 := by
    have h0 : Tendsto (fun k => 5 * |K| / (N k : ℝ)) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv] using hN.inv_tendsto_atTop.const_mul (5 * |K|)
    exact h0.eventually (ge_mem_nhds one_pos)
  filter_upwards [hK hN hε hεN, eventually_twoPhase_mem hN hε hεN, hsmall,
    hN.eventually_ge_atTop 1, hε.eventually_ge_atTop 1] with k hG hΦ hs hN1 he1
  intro δ f hf Ω _ P _ X hX hind
  obtain ⟨G, hGm, hGc, hGH⟩ := hG
  have hfK := hf.2.2.1
  have hn1 : 1 ≤ N k := by exact_mod_cast hN1
  rw [integral_reHeight_kKeys hfK hX hind (ε k) (N k)]
  set H : (ℕ → ℝ) → ℝ := fun ω =>
    (reHeight (ε k) (fun t => quantK f 0 1 (expPartial t ω / expPartial (N k) ω)) (N k) : ℝ)
  set Φ := twoPhase (N k) (ε k) δ
  obtain ⟨hΦ0, hΦN⟩ := hΦ δ hf.1 hf.2.1
  have hHint : Integrable H expSeqMeasure :=
    integrable_reHeight he1 hn1 (measurable_kreKeys hfK (N k)).aemeasurable
  have hHN : ∀ ω, H ω ≤ N k := fun ω => by
    have h := reHeight_le_log (eps := ε k)
      (p := fun t => quantK f 0 1 (expPartial t ω / expPartial (N k) ω)) he1 hn1
    have h2 : Nat.log 2 (N k) + 1 ≤ N k := Nat.log_lt_self 2 (by omega)
    have h3 := h.trans h2
    simp only [H]
    exact_mod_cast h3
  have hB : ∀ ω, |H ω - Φ| ≤ 5 * (N k : ℝ) := fun ω => by
    have := hHN ω
    have : 0 ≤ H ω := Nat.cast_nonneg _
    rw [abs_le]; constructor <;> linarith
  have hpt : ∀ ω, |H ω - Φ| ≤ G.indicator (fun _ => |K|) ω + Gᶜ.indicator (fun _ => 5 * (N k : ℝ)) ω :=
    fun ω => by
      by_cases hω : ω ∈ G
      · rw [Set.indicator_of_mem hω, Set.indicator_of_notMem (by simpa using hω), add_zero]
        exact (hGH ω hω δ f hf).trans (le_abs_self K)
      · rw [Set.indicator_of_notMem hω, Set.indicator_of_mem (by simpa using hω), zero_add]
        exact hB ω
  have hint1 : Integrable (fun ω => |H ω - Φ|) expSeqMeasure :=
    (hHint.sub (integrable_const Φ)).abs
  have hint2 : Integrable (fun ω => G.indicator (fun _ => |K|) ω +
      Gᶜ.indicator (fun _ => 5 * (N k : ℝ)) ω) expSeqMeasure :=
    ((integrable_const |K|).indicator hGm).add ((integrable_const _).indicator hGm.compl)
  have hmono := integral_mono hint1 hint2 hpt
  rw [integral_add ((integrable_const |K|).indicator hGm)
      ((integrable_const _).indicator hGm.compl),
    integral_indicator hGm, integral_indicator hGm.compl, setIntegral_const, setIntegral_const,
    smul_eq_mul, smul_eq_mul] at hmono
  have hPG : expSeqMeasure.real G ≤ 1 := measureReal_le_one
  have hGc' : 5 * (N k : ℝ) * expSeqMeasure.real Gᶜ ≤ 1 := by
    have hN0 : (0 : ℝ) < N k := by positivity
    have hGc2 : expSeqMeasure.real Gᶜ ≤ |K| / (N k : ℝ) ^ 2 :=
      hGc.trans (div_le_div_of_nonneg_right (le_abs_self K) (by positivity))
    calc 5 * (N k : ℝ) * expSeqMeasure.real Gᶜ ≤ 5 * (N k : ℝ) * (|K| / (N k : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left hGc2 (by positivity)
      _ = 5 * |K| / (N k : ℝ) := by field_simp
      _ ≤ 1 := hs
  have hconst : ∫ ω, H ω ∂expSeqMeasure - Φ = ∫ ω, (H ω - Φ) ∂expSeqMeasure := by
    rw [integral_sub hHint (integrable_const Φ), integral_const, probReal_univ, one_smul]
  rw [hconst]
  calc |∫ ω, (H ω - Φ) ∂expSeqMeasure| ≤ ∫ ω, |H ω - Φ| ∂expSeqMeasure :=
        abs_integral_le_integral_abs
    _ ≤ expSeqMeasure.real G * |K| + expSeqMeasure.real Gᶜ * (5 * (N k : ℝ)) := hmono
    _ ≤ |K| + 1 := by nlinarith [measureReal_nonneg (μ := expSeqMeasure) (s := G), abs_nonneg K]

/-! ## `cor:cases` -/

/-- Eventually along HEIGHT, `1 ≤ log ε ≤ log N`. -/
theorem eventually_logRatio {N : ℕ → ℕ} {ε : ℕ → ℝ}
    (hN : Tendsto (fun k => (N k : ℝ)) atTop atTop) (hε : Tendsto ε atTop atTop)
    (hεN : Tendsto (fun k => Real.log (ε k) / Real.log (N k)) atTop (𝓝 0)) :
    ∀ᶠ k in atTop, 1 ≤ Real.log (ε k) ∧ 1 ≤ Real.log (N k) / Real.log (ε k) := by
  have hL : Tendsto (fun k => Real.log (N k)) atTop atTop := Real.tendsto_log_atTop.comp hN
  filter_upwards [hε.eventually_ge_atTop (Real.exp 1), hL.eventually_gt_atTop 0,
    hεN.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1))] with k he hLpos hratio
  have hlogε : 1 ≤ Real.log (ε k) := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) he
  rw [div_le_one hLpos] at hratio
  exact ⟨hlogε, by rw [le_div_iff₀ (by linarith)]; linarith⟩

/-- A nonconstant Model K density on `[0, 1]` takes two different values at interior points. -/
theorem exists_interior_ne {f : ℝ → ℝ} {fmin fmax Lf : ℝ} (hf : DensityK f 0 1 fmin fmax Lf)
    (hnc : ∃ x ∈ Set.Icc (0 : ℝ) 1, ∃ y ∈ Set.Icc (0 : ℝ) 1, f x ≠ f y) :
    ∃ a b : ℝ, 0 < a ∧ a < b ∧ b < 1 ∧ f a ≠ f b := by
  by_contra h
  simp only [not_exists, not_and, not_not] at h
  have hconst : Set.EqOn f (fun _ => f (1 / 2)) (Set.Ioo 0 1) := by
    intro x hx
    rcases lt_trichotomy x (1 / 2) with hlt | heq | hgt
    · exact h x (1 / 2) hx.1 hlt (by norm_num)
    · simp [heq]
    · exact (h (1 / 2) x (by norm_num) hgt hx.2).symm
  have hIcc : Set.EqOn f (fun _ => f (1 / 2)) (Set.Icc 0 1) :=
    hconst.of_subset_closure hf.continuousOn continuousOn_const Set.Ioo_subset_Icc_self
      (by rw [closure_Ioo zero_ne_one])
  obtain ⟨x, hx, y, hy, hxy⟩ := hnc
  exact hxy ((hIcc hx).trans (hIcc hy).symm)

/-- **`cor:cases`(a): a fixed nonconstant density.**  The expected ALG-RE height is
`2 log₂ (log N / log ε) + O_f(1)`: twice the Model G value. -/
theorem K_RE_fixed_density {f : ℝ → ℝ} {fmin fmax Lf : ℝ} (hf : DensityK f 0 1 fmin fmax Lf)
    (hnc : ∃ x ∈ Set.Icc (0 : ℝ) 1, ∃ y ∈ Set.Icc (0 : ℝ) 1, f x ≠ f y) :
    ∃ C : ℝ, ∀ {N : ℕ → ℕ} {ε : ℕ → ℝ},
      Tendsto (fun k => (N k : ℝ)) atTop atTop → Tendsto ε atTop atTop →
      Tendsto (fun k => Real.log (ε k) / Real.log (N k)) atTop (𝓝 0) →
      ∀ᶠ k in atTop, ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X : ℕ → Ω → ℝ), (∀ i, HasLaw (X i) (densityLaw f 0 1) P) → iIndepFun X P →
        |∫ ω, (reHeight (ε k) (kKeys X (N k) ω) (N k) : ℝ) ∂P -
          2 * Real.logb 2 (Real.log (N k) / Real.log (ε k))| ≤ C := by
  obtain ⟨a, b, ha, hab, hb, hne⟩ := exists_interior_ne hf hnc
  have hV : 0 < |f b - f a| := abs_pos.2 (sub_ne_zero.2 (Ne.symm hne))
  let c : DensityClassParams :=
    { fmin := min fmin 1, fmax := max fmax 1, L := Lf + 1, V := |f b - f a|, a := a, b := b,
      fmin_pos := lt_min hf.pos one_pos, fmin_le_one := min_le_right _ _,
      one_le_fmax := le_max_right _ _, L_pos := by linarith [hf.lf_nonneg], V_pos := hV,
      a_pos := ha, a_lt_b := hab, b_lt_one := hb }
  have hmem : c.Mem 1 f := by
    refine ⟨zero_le_one, le_rfl, ?_, by simp [c]⟩
    exact
      { lt := hf.lt
        pos := lt_min hf.pos one_pos
        lower := fun x hx => (min_le_left _ _).trans (hf.lower x hx)
        upper := fun x hx => (hf.upper x hx).trans (le_max_left _ _)
        lip := fun x hx y hy => (hf.lip x hx y hy).trans (by
          show Lf * |x - y| ≤ 1 * (Lf + 1) * |x - y|
          nlinarith [abs_nonneg (x - y)])
        integral_one := hf.integral_one }
  obtain ⟨K, hK⟩ := K_RE_uniform_integral.{u} c
  refine ⟨K, fun {N ε} hN hε hεN => ?_⟩
  filter_upwards [hK hN hε hεN, eventually_logRatio hN hε hεN] with k hk hr
  intro Ω _ P _ X hX hind
  have h := hk 1 f hmem P X hX hind
  have hr0 : 0 ≤ Real.logb 2 (Real.log (N k) / Real.log (ε k)) :=
    Real.logb_nonneg (by norm_num) hr.2
  have hΦ : twoPhase (N k) (ε k) 1 = 2 * Real.logb 2 (Real.log (N k) / Real.log (ε k)) := by
    unfold twoPhase
    rw [if_neg one_ne_zero, div_one, max_eq_right hr0]
    ring
  rwa [hΦ] at h

/-- **`cor:cases`(b): a nearly constant density.**  If `δ ≤ N^{-1/2}`, the expected ALG-RE
height is `log₂ (log N / log ε) + O(1)`, the Model G value, uniformly over `𝔉_δ`. -/
theorem K_RE_uniform_small (c : DensityClassParams) :
    ∃ K : ℝ, ∀ {N : ℕ → ℕ} {ε : ℕ → ℝ},
      Tendsto (fun k => (N k : ℝ)) atTop atTop → Tendsto ε atTop atTop →
      Tendsto (fun k => Real.log (ε k) / Real.log (N k)) atTop (𝓝 0) →
      ∀ᶠ k in atTop, ∀ δ : ℝ, ∀ f : ℝ → ℝ, c.Mem δ f → δ ≤ (N k : ℝ) ^ (-(1 / 2 : ℝ)) →
        ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (X : ℕ → Ω → ℝ), (∀ i, HasLaw (X i) (densityLaw f 0 1) P) → iIndepFun X P →
          |∫ ω, (reHeight (ε k) (kKeys X (N k) ω) (N k) : ℝ) ∂P -
            Real.logb 2 (Real.log (N k) / Real.log (ε k))| ≤ K := by
  obtain ⟨K, hK⟩ := K_RE_uniform_integral.{u} c
  refine ⟨K + 1, fun {N ε} hN hε hεN => ?_⟩
  have hL : Tendsto (fun k => Real.log (N k)) atTop atTop := Real.tendsto_log_atTop.comp hN
  filter_upwards [hK hN hε hεN, eventually_logRatio hN hε hεN, hL.eventually_gt_atTop 0,
    hN.eventually_ge_atTop 1, hε.eventually_gt_atTop 0] with k hk hr hLpos hN1 hε0
  intro δ f hf hδN Ω _ P _ X hX hind
  have h := hk δ f hf P X hX hind
  set Y := Real.log (N k)
  have h2 : (if δ = 0 then 0 else max 0 (Real.logb 2 (Y / Real.log (ε k / δ)))) ≤ (1 : ℝ) ∧
      (0 : ℝ) ≤ (if δ = 0 then 0 else max 0 (Real.logb 2 (Y / Real.log (ε k / δ)))) := by
    split_ifs with h0
    · norm_num
    · refine ⟨max_le zero_le_one ?_, le_max_left _ _⟩
      have hδ : 0 < δ := lt_of_le_of_ne hf.1 (Ne.symm h0)
      have hN0 : (0 : ℝ) < N k := by linarith
      have hlogδ : Real.log δ ≤ -(1 / 2) * Y := by
        have := Real.log_le_log hδ hδN
        rwa [Real.log_rpow hN0] at this
      have hq : Y / 2 ≤ Real.log (ε k / δ) := by
        rw [Real.log_div hε0.ne' hδ.ne']; linarith [hr.1]
      have hq0 : 0 < Real.log (ε k / δ) := by linarith
      have : Y / Real.log (ε k / δ) ≤ 2 := by
        rw [div_le_iff₀ hq0]; linarith
      calc Real.logb 2 (Y / Real.log (ε k / δ)) ≤ Real.logb 2 2 :=
            Real.logb_le_logb_of_le (by norm_num) (div_pos hLpos hq0) this
        _ = 1 := Real.logb_self_eq_one one_lt_two
  unfold twoPhase at h
  rw [abs_le] at h ⊢
  constructor <;> linarith [h.1, h.2, h2.1, h2.2]

/-- **`cor:cases`(c): the ratio limit.**  Along a HEIGHT sequence with densities
`f_k ∈ 𝔉_{δ_k}` for which the ratio `θ` of the two terms of `twoPhase` has a limit,
`θ ∈ [0, 1]` and the expected ALG-RE height divided by `log₂ (log N / log ε)` tends to
`1 + θ ∈ [1, 2]`. -/
theorem K_RE_uniform_ratio (c : DensityClassParams) {N : ℕ → ℕ} {ε : ℕ → ℝ}
    (hN : Tendsto (fun k => (N k : ℝ)) atTop atTop) (hε : Tendsto ε atTop atTop)
    (hεN : Tendsto (fun k => Real.log (ε k) / Real.log (N k)) atTop (𝓝 0))
    {δ : ℕ → ℝ} {f : ℕ → ℝ → ℝ} (hf : ∀ k, c.Mem (δ k) (f k)) {θ : ℝ}
    (hθ : Tendsto (fun k =>
      (if δ k = 0 then 0 else max 0 (Real.logb 2 (Real.log (N k) / Real.log (ε k / δ k)))) /
        Real.logb 2 (Real.log (N k) / Real.log (ε k))) atTop (𝓝 θ))
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → ℕ → Ω → ℝ) (hX : ∀ k i, HasLaw (X k i) (densityLaw (f k) 0 1) P)
    (hind : ∀ k, iIndepFun (X k) P) :
    (0 ≤ θ ∧ θ ≤ 1) ∧ Tendsto (fun k => (∫ ω, (reHeight (ε k) (kKeys (X k) (N k) ω) (N k) : ℝ) ∂P) /
      Real.logb 2 (Real.log (N k) / Real.log (ε k))) atTop (𝓝 (1 + θ)) := by
  obtain ⟨K, hK⟩ := K_RE_uniform_integral.{u} c
  set Φ₁ : ℕ → ℝ := fun k => Real.logb 2 (Real.log (N k) / Real.log (ε k))
  set Φ₂ : ℕ → ℝ := fun k =>
    if δ k = 0 then 0 else max 0 (Real.logb 2 (Real.log (N k) / Real.log (ε k / δ k)))
  set E : ℕ → ℝ := fun k => ∫ ω, (reHeight (ε k) (kKeys (X k) (N k) ω) (N k) : ℝ) ∂P
  -- `Φ₁ → ∞`
  have hpos : ∀ᶠ k in atTop, 0 < Real.log (ε k) / Real.log (N k) := by
    filter_upwards [eventually_logRatio hN hε hεN] with k hk
    have h1 := hk.1
    have h2 : Real.log (ε k) ≤ Real.log (N k) := by
      have := hk.2; rw [le_div_iff₀ (by linarith)] at this; linarith
    exact div_pos (by linarith) (by linarith)
  have hinv : Tendsto (fun k => Real.log (N k) / Real.log (ε k)) atTop atTop := by
    have h0 : Tendsto (fun k => Real.log (ε k) / Real.log (N k)) atTop (𝓝[>] 0) :=
      tendsto_nhdsWithin_iff.2 ⟨hεN, hpos⟩
    refine h0.inv_tendsto_nhdsGT_zero.congr fun k => ?_
    simp only [Pi.inv_apply, inv_div]
  have hΦ₁ : Tendsto Φ₁ atTop atTop := (Real.tendsto_logb_atTop one_lt_two).comp hinv
  -- the error term
  have herr : Tendsto (fun k => (E k - Φ₁ k - Φ₂ k) / Φ₁ k) atTop (𝓝 0) := by
    have hb : Tendsto (fun k => |K| / Φ₁ k) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hΦ₁
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [hK hN hε hεN, hΦ₁.eventually_gt_atTop 0] with k hk hk0
    have h := hk (δ k) (f k) (hf k) P (X k) (hX k) (hind k)
    have h' : |E k - Φ₁ k - Φ₂ k| ≤ K := by rw [sub_sub]; exact h
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hk0]
    exact div_le_div_of_nonneg_right (h'.trans (le_abs_self K)) hk0.le
  -- `θ ∈ [0, 1]`, since eventually `0 ≤ Φ₂ ≤ Φ₁`
  have hratio : ∀ᶠ k in atTop, 0 ≤ Φ₂ k / Φ₁ k ∧ Φ₂ k / Φ₁ k ≤ 1 := by
    filter_upwards [eventually_twoPhase_terms hN hε hεN, hΦ₁.eventually_gt_atTop 0]
      with k hk hk0
    obtain ⟨h1, h2, -⟩ := hk (δ k) (hf k).1 (hf k).2.1
    exact ⟨div_nonneg h1 hk0.le, (div_le_one hk0).2 h2⟩
  refine ⟨⟨ge_of_tendsto hθ (hratio.mono fun k hk => hk.1),
    le_of_tendsto hθ (hratio.mono fun k hk => hk.2)⟩, ?_⟩
  have hsum := (tendsto_const_nhds (x := (1 : ℝ))).add (hθ.add herr)
  rw [add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [hΦ₁.eventually_gt_atTop 0] with k hk0
  have : Φ₁ k ≠ 0 := hk0.ne'
  show 1 + (Φ₂ k / Φ₁ k + (E k - Φ₁ k - Φ₂ k) / Φ₁ k) = E k / Φ₁ k
  field_simp
  ring

end

end PGM
