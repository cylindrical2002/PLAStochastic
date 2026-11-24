import PLAStochastic.Index.GEP.Response.Score.OutputDerivative

/-!
# WP4 leaf 4A-S, part 7: continuity on the closed interval `[0,1]`

`MixDiff` also asks for continuity at the endpoints, where the score of the path is unbounded
(the endpoint laws may have density gaps).  We use the reference point `1/2`: for every
`s ∈ [0,1]`, `ν_s = r_s · ν_{1/2}` with `0 ≤ r_s ≤ 3`, so each prefix expectation
`E_{ν_s}[G]` of a functional of `t` gaps is `E_{ν_{1/2}}[G ∏_{j<t} r_s(g_j)]`, continuous in `s`
by dominated convergence (`continuousOn_prefix_integral`).  The series over `{k < T}` (for `C`)
and over `{T = t}` (for the output test) converge uniformly on `[0,1]`, by the stopping tail and
the output moment that hold uniformly along the path (`continuousOn_tsum`); this is the
"指数奖励与停止尾同时给端点连续性" of `joint-response.md` §5.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

variable {ν₀ ν₁ : ProbabilityMeasure ℝ} {f₀ f₁ : ℝ → ℝ}

theorem half_mem_Ioo : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩

theorem abs_mixRatio_half_le (hS : MixSetup ν₀ ν₁ f₀ f₁) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (y : ℝ) : |mixRatio f₀ f₁ (1 / 2) s y| ≤ 3 := by
  refine (abs_mixRatio_le hS.nonneg₀ hS.nonneg₁ half_mem_Ioo s y).trans ?_
  have h1 : |s - 1 / 2| ≤ 1 / 2 := by rw [abs_le]; constructor <;> linarith [hs.1, hs.2]
  have h2 : scoreBd (1 / 2) = 4 := by unfold scoreBd; norm_num
  rw [h2]
  linarith

theorem continuous_prod_mixRatio (s₀ : ℝ) (t : ℕ) (g : ℕ → ℝ) :
    Continuous fun s => ∏ j ∈ Finset.range t, mixRatio f₀ f₁ s₀ s (g j) := by
  refine continuous_finsetProd _ fun j _ => ?_
  unfold mixRatio
  fun_prop

/-- **Continuity of prefix expectations along the whole path.** -/
theorem continuousOn_prefix_integral (hS : MixSetup ν₀ ν₁ f₀ f₁) {t : ℕ}
    {G : ℝ → (ℕ → ℝ) → ℝ} (hGm : ∀ s, Measurable (G s)) (hdep : ∀ s, DepPrefix t (G s))
    (hcont : ∀ᵐ g ∂(iidLaw (mixPM ν₀ ν₁ (1 / 2))), ContinuousOn (fun s => G s g) (Icc 0 1))
    {B : (ℕ → ℝ) → ℝ} (hB : Integrable B (iidLaw (mixPM ν₀ ν₁ (1 / 2))))
    (hGB : ∀ s ∈ Icc (0 : ℝ) 1, ∀ᵐ g ∂(iidLaw (mixPM ν₀ ν₁ (1 / 2))), |G s g| ≤ B g) :
    ContinuousOn (fun s => ∫ g, G s g ∂(iidLaw (mixPM ν₀ ν₁ s))) (Icc 0 1) := by
  have hrep : ∀ s ∈ Icc (0 : ℝ) 1, ∫ g, G s g ∂(iidLaw (mixPM ν₀ ν₁ s)) =
      ∫ g, (∏ j ∈ Finset.range t, mixRatio f₀ f₁ (1 / 2) s (g j)) * G s g
        ∂(iidLaw (mixPM ν₀ ν₁ (1 / 2))) := by
    intro s hs
    rw [integral_iidLaw_prefix (mixPM ν₀ ν₁ (1 / 2)) (mixPM ν₀ ν₁ s)
      (measurable_mixRatioNN hS.meas₀ hS.meas₁ (1 / 2) s) (hS.eq_withDensity half_mem_Ioo hs)
      (hGm s) (hdep s)]
    refine integral_congr_ae (Eventually.of_forall fun g => ?_)
    simp only [hS.coe_ratioNN half_mem_Ioo hs]
  refine ContinuousOn.congr ?_ hrep
  refine continuousOn_of_dominated (bound := fun g => 3 ^ t * B g) (fun s _ =>
    ((Finset.measurable_prod _ fun j _ =>
      (hS.measurable_ratio (1 / 2) s).comp (measurable_pi_apply j)).mul
        (hGm s)).aestronglyMeasurable) (fun s hs => ?_) (hB.const_mul _) ?_
  · filter_upwards [hGB s hs] with g hg
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (abs_prod_le_pow fun j _ => abs_mixRatio_half_le hS hs _) hg
      (abs_nonneg _) (by positivity)
  · filter_upwards [hcont] with g hg
    exact ((continuous_prod_mixRatio (1 / 2) t g).continuousOn).mul hg

/-! ## Continuity of `C_ε` -/

theorem lawC_eq_tsum {eps : ℝ} {ν : ProbabilityMeasure ℝ}
    (hfin : ∀ᵐ g ∂(iidLaw ν), gapSegLen eps g ≠ ⊤) :
    lawC eps ν = ∑' k : ℕ, (iidLaw ν).real {g | (k : ℕ∞) < gapSegLen eps g} := by
  have h1 : lawC eps ν = (∫⁻ g, ENNReal.ofReal ((gapSegLen eps g).toNat : ℝ)
      ∂(iidLaw ν)).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun g => Nat.cast_nonneg _)
      (measurable_toNat_gapSegLen eps).aestronglyMeasurable
  have h2 : ∫⁻ g, ENNReal.ofReal ((gapSegLen eps g).toNat : ℝ) ∂(iidLaw ν) =
      ∑' k : ℕ, iidLaw ν {g | (k : ℕ∞) < gapSegLen eps g} := by
    calc ∫⁻ g, ENNReal.ofReal ((gapSegLen eps g).toNat : ℝ) ∂(iidLaw ν)
        = ∫⁻ g, ∑' k : ℕ, (1 : ℝ≥0∞) *
            {g : ℕ → ℝ | (k : ℕ∞) < gapSegLen eps g}.indicator (fun _ => (1 : ℝ≥0∞)) g
            ∂(iidLaw ν) := by
          refine lintegral_congr_ae ?_
          filter_upwards [hfin] with g hg
          obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 hg
          rw [tsum_mul_indicator_lt hn.symm, ← hn, ENat.toNat_natCast, Finset.sum_const,
            Finset.card_range, nsmul_eq_mul, mul_one, ENNReal.ofReal_natCast]
      _ = ∑' k : ℕ, iidLaw ν {g | (k : ℕ∞) < gapSegLen eps g} := by
          simp_rw [one_mul]
          rw [lintegral_tsum fun k =>
            (measurable_const.indicator (measurableSet_lt_gapSegLen eps k)).aemeasurable]
          congr 1
          funext k
          rw [lintegral_indicator_const (measurableSet_lt_gapSegLen eps k), one_mul]
  rw [h1, h2, ENNReal.tsum_toReal_eq fun k => measure_ne_top _ _]
  rfl

/-- **`C_ε` is continuous along the closed path.** -/
theorem continuousOn_lawC_mix (hS : MixSetup ν₀ ν₁ f₀ f₁) {eps K a : ℝ} (hK : 0 ≤ K)
    (ha : 0 ≤ a) (ha1 : a < 1)
    (hfin : ∀ s ∈ Icc (0 : ℝ) 1, ∀ᵐ g ∂(iidLaw (mixPM ν₀ ν₁ s)), gapSegLen eps g ≠ ⊤)
    (htail : ∀ s ∈ Icc (0 : ℝ) 1, ∀ m : ℕ,
      iidLaw (mixPM ν₀ ν₁ s) {g | (m : ℕ∞) < gapSegLen eps g} ≤ ENNReal.ofReal (K * a ^ m)) :
    ContinuousOn (fun s => lawC eps (mixPM ν₀ ν₁ s)) (Icc 0 1) := by
  have hrep : ∀ s ∈ Icc (0 : ℝ) 1, lawC eps (mixPM ν₀ ν₁ s) =
      ∑' k : ℕ, ∫ g, {g : ℕ → ℝ | (k : ℕ∞) < gapSegLen eps g}.indicator (fun _ => (1 : ℝ)) g
        ∂(iidLaw (mixPM ν₀ ν₁ s)) := by
    intro s hs
    rw [lawC_eq_tsum (hfin s hs)]
    refine tsum_congr fun k => ?_
    rw [integral_indicator_const _ (measurableSet_lt_gapSegLen eps k), smul_eq_mul, mul_one]
  refine ContinuousOn.congr ?_ hrep
  refine continuousOn_tsum (u := fun k => K * a ^ k) (fun k => ?_)
    ((summable_geometric_of_lt_one ha ha1).mul_left K) (fun k s hs => ?_)
  · refine continuousOn_prefix_integral hS (t := k) (B := fun _ => 1)
      (G := fun _ => {g : ℕ → ℝ | (k : ℕ∞) < gapSegLen eps g}.indicator (fun _ => (1 : ℝ)))
      (fun _ => measurable_const.indicator (measurableSet_lt_gapSegLen eps k))
      (fun _ g g' h => ?_) (Eventually.of_forall fun g => continuousOn_const)
      (integrable_const _) (fun s _ => Eventually.of_forall fun g => ?_)
    · by_cases hg : (k : ℕ∞) < gapSegLen eps g
      · rw [Set.indicator_of_mem (show g ∈ {g : ℕ → ℝ | (k : ℕ∞) < gapSegLen eps g} from hg),
          Set.indicator_of_mem (show g' ∈ {g : ℕ → ℝ | (k : ℕ∞) < gapSegLen eps g} from
            (lt_gapSegLen_congr h).1 hg)]
      · rw [Set.indicator_of_notMem (show g ∉ {g : ℕ → ℝ | (k : ℕ∞) < gapSegLen eps g} from hg),
          Set.indicator_of_notMem (show g' ∉ {g : ℕ → ℝ | (k : ℕ∞) < gapSegLen eps g} from
            fun h' => hg ((lt_gapSegLen_congr h).2 h'))]
    · by_cases hg : g ∈ {g : ℕ → ℝ | (k : ℕ∞) < gapSegLen eps g}
      · rw [Set.indicator_of_mem hg, abs_one]
      · rw [Set.indicator_of_notMem hg, abs_zero]; exact zero_le_one
  · rw [integral_indicator_const _ (measurableSet_lt_gapSegLen eps k), smul_eq_mul, mul_one,
      Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
    have h := htail s hs k
    rw [← ofReal_measureReal] at h
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h

/-! ## Continuity of the output test -/

/-- Exponential moments of a deterministic partial sum (independence of the gaps). -/
theorem integrable_exp_gapKeys {ρ : ProbabilityMeasure ℝ} {κ : ℝ}
    (hρ : Integrable (fun x => Real.exp (κ * x)) (ρ : Measure ℝ)) (t : ℕ) :
    Integrable (fun g => Real.exp (κ * gapKeys g t)) (iidLaw ρ) := by
  have hm : Measurable fun g : ℕ → ℝ => Real.exp (κ * gapKeys g t) :=
    Real.measurable_exp.comp (measurable_const.mul ((measurable_pi_apply t).comp measurable_gapKeys))
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun g => (Real.exp_pos _).le)]
  have e : ∀ g : ℕ → ℝ, ENNReal.ofReal (Real.exp (κ * gapKeys g t)) =
      ∏ j ∈ Finset.range t, ENNReal.ofReal (Real.exp (κ * g j)) := by
    intro g
    rw [gapKeys, Finset.mul_sum, Real.exp_sum,
      ENNReal.ofReal_prod_of_nonneg fun j _ => (Real.exp_pos _).le]
  simp_rw [e]
  have hX : ∀ j : ℕ, Measurable fun g : ℕ → ℝ => ENNReal.ofReal (Real.exp (κ * g j)) :=
    fun j => (Real.measurable_exp.comp (measurable_const.mul (measurable_pi_apply j))).ennreal_ofReal
  have hind : iIndepFun (fun (j : ℕ) (g : ℕ → ℝ) => ENNReal.ofReal (Real.exp (κ * g j)))
      (iidLaw ρ) :=
    (iIndepFun_coord ρ).comp (fun _ x => ENNReal.ofReal (Real.exp (κ * x)))
      fun _ => (Real.measurable_exp.comp (measurable_const.mul measurable_id)).ennreal_ofReal
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun _ _ hind hX]
  refine ENNReal.prod_lt_top fun j _ => ?_
  rw [lintegral_coord ρ j (f := fun x => ENNReal.ofReal (Real.exp (κ * x)))
    (Real.measurable_exp.comp (measurable_const.mul measurable_id)).ennreal_ofReal]
  have := hρ.2
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun x => (Real.exp_pos _).le)] at this
  exact this

theorem tsum_indicator_gapSegLen_eq_real {eps : ℝ} {Φ : (ℕ → ℝ) → ℝ} {g : ℕ → ℝ}
    (hg : gapSegLen eps g ≠ ⊤) :
    ∑' t : ℕ, {g : ℕ → ℝ | gapSegLen eps g = t}.indicator Φ g = Φ g := by
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 hg
  rw [tsum_eq_single n]
  · rw [Set.indicator_of_mem (show g ∈ {g : ℕ → ℝ | gapSegLen eps g = n} from hn.symm)]
  · intro t ht
    rw [Set.indicator_of_notMem (show g ∉ {g : ℕ → ℝ | gapSegLen eps g = t} by
      simp only [Set.mem_ofPred_eq, ← hn, Nat.cast_inj]; exact fun h => ht h.symm)]

/-- An integrable functional is the sum of its pieces on `{T = t}`. -/
theorem integral_eq_tsum_gapSegLen {eps : ℝ} {P : Measure (ℕ → ℝ)} {Φ : (ℕ → ℝ) → ℝ}
    (hΦm : Measurable Φ) (hΦ : Integrable Φ P) (hfin : ∀ᵐ g ∂P, gapSegLen eps g ≠ ⊤) :
    ∫ g, Φ g ∂P = ∑' t : ℕ, ∫ g, {g : ℕ → ℝ | gapSegLen eps g = t}.indicator Φ g ∂P := by
  have hm : ∀ t : ℕ, Measurable ({g : ℕ → ℝ | gapSegLen eps g = t}.indicator Φ) := fun t =>
    hΦm.indicator (measurableSet_gapSegLen_eq eps t)
  rw [← integral_tsum (fun t => (hm t).aestronglyMeasurable)]
  · exact integral_congr_ae (by
      filter_upwards [hfin] with g hg using (tsum_indicator_gapSegLen_eq_real hg).symm)
  · rw [← lintegral_tsum fun t => (hm t).enorm.aemeasurable]
    refine ne_top_of_le_ne_top hΦ.2.ne (lintegral_mono_ae ?_)
    filter_upwards [hfin] with g hg
    have e : ∀ t : ℕ, ‖{g : ℕ → ℝ | gapSegLen eps g = t}.indicator Φ g‖ₑ =
        1 * {g : ℕ → ℝ | gapSegLen eps g = t}.indicator (fun g => ‖Φ g‖ₑ) g := fun t => by
      rw [enorm_indicator_eq_indicator_enorm, one_mul]
    simp_rw [e]
    rw [tsum_indicator_gapSegLen_eq hg (fun _ => 1), one_mul]

/-- The output moment in path form. -/
theorem integrable_exp_output {eps θY BY : ℝ} {ν : ProbabilityMeasure ℝ}
    (hE : ExpMom θY BY (lawPhi eps ν)) :
    Integrable (fun g => Real.exp (θY * (stopSum eps g / lawC eps ν))) (iidLaw ν) ∧
      ∫ g, Real.exp (θY * (stopSum eps g / lawC eps ν)) ∂(iidLaw ν) ≤ BY := by
  have hmap : (lawPhi eps ν : Measure ℝ) = (iidLaw ν).map fun g => stopSum eps g / lawC eps ν :=
    rfl
  have hSm : Measurable fun g => stopSum eps g / lawC eps ν := (measurable_stopSum eps).div_const _
  have hem : Measurable fun y : ℝ => Real.exp (θY * y) := by fun_prop
  have h1 := hE.integrable
  rw [hmap, integrable_map_measure hem.aestronglyMeasurable hSm.aemeasurable] at h1
  refine ⟨h1, ?_⟩
  have h2 := hE.le
  rw [hmap, integral_map hSm.aemeasurable hem.aestronglyMeasurable] at h2
  exact h2

variable {η M : ℝ} {ψ : ℝ → ℝ}

/-- `|φ_ψ(y)| ≤ (M/η) e^{2ηy}` for `y ≥ 0`. -/
theorem OutTest.abs_testFn_le_exp (hψ : OutTest η M ψ) (hη : 0 < η) {y : ℝ} (hy : 0 ≤ y) :
    |testFn ψ y| ≤ M / η * Real.exp (2 * η * y) := by
  have hM := hψ.nonneg
  refine (hψ.abs_testFn_le hη.le hy).trans ?_
  have h1 := le_exp_div (t := y) hη
  calc M * Real.exp (η * y) * y ≤ M * Real.exp (η * y) * (Real.exp (η * y) / η) := by gcongr
    _ = M / η * Real.exp (2 * η * y) := by
        rw [div_eq_mul_inv, div_eq_mul_inv, show 2 * η * y = η * y + η * y by ring, Real.exp_add]
        ring

/-- **The output test is continuous along the closed path.** -/
theorem continuousOn_outFn_mix (hS : MixSetup ν₀ ν₁ f₀ f₁) {eps K a β : ℝ} (hK : 0 ≤ K)
    (ha : 0 ≤ a) (hβ : 0 < β) (hβa : Real.exp (2 * β) * a < 1)
    (hfin : ∀ s ∈ Icc (0 : ℝ) 1, ∀ᵐ g ∂(iidLaw (mixPM ν₀ ν₁ s)), gapSegLen eps g ≠ ⊤)
    (htail : ∀ s ∈ Icc (0 : ℝ) 1, ∀ m : ℕ,
      iidLaw (mixPM ν₀ ν₁ s) {g | (m : ℕ∞) < gapSegLen eps g} ≤ ENNReal.ofReal (K * a ^ m))
    {θY BY : ℝ} (hY : ∀ s ∈ Icc (0 : ℝ) 1, ExpMom θY BY (lawPhi eps (mixPM ν₀ ν₁ s)))
    (hSpos : ∀ s ∈ Icc (0 : ℝ) 1, ∀ᵐ g ∂(iidLaw (mixPM ν₀ ν₁ s)), 0 < stopSum eps g)
    {clo : ℝ} (hclo : 0 < clo) (hC : ∀ s ∈ Icc (0 : ℝ) 1, clo ≤ lawC eps (mixPM ν₀ ν₁ s))
    (hρexp : Integrable (fun x => Real.exp (2 * η / clo * x)) (mixPM ν₀ ν₁ (1 / 2) : Measure ℝ))
    (hη : 0 < η) (hηY : 4 * η ≤ θY) (hψ : OutTest η M ψ) :
    ContinuousOn (fun s => outFn eps (mixPM ν₀ ν₁ s) ψ) (Icc 0 1) := by
  have hM := hψ.nonneg
  have ha1 : a < 1 := by
    have : 1 ≤ Real.exp (2 * β) := Real.one_le_exp (by positivity)
    nlinarith
  have hCc := continuousOn_lawC_mix hS hK ha ha1 hfin htail
  have hhalf : (1 / 2 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  set Cf : ℝ → ℝ := fun s => lawC eps (mixPM ν₀ ν₁ s) with hCf
  set Φ : ℝ → (ℕ → ℝ) → ℝ := fun s g => testFn ψ (stopSum eps g / Cf s) with hΦ
  have hΦm : ∀ s, Measurable (Φ s) := fun s =>
    hψ.measurable_testFn.comp ((measurable_stopSum eps).div_const _)
  have hΦst : ∀ s, IsStoppedFn eps (Φ s) := fun s =>
    (isStoppedFn_stopSum eps).comp fun x => testFn ψ (x / Cf s)
  -- the pointwise exponential bound
  have hΦb : ∀ s ∈ Icc (0 : ℝ) 1, ∀ g, 0 < stopSum eps g →
      |Φ s g| ≤ M / η * Real.exp (θY * (stopSum eps g / Cf s)) := by
    intro s hs g hg
    have hY0 : 0 ≤ stopSum eps g / Cf s := div_nonneg hg.le (hclo.le.trans (hC s hs))
    refine (hψ.abs_testFn_le_exp hη hY0).trans ?_
    gcongr
    nlinarith
  set BT := 1 + (Real.exp (2 * β) - 1) * K / (1 - Real.exp (2 * β) * a) with hBT
  -- the decomposition along `{T = t}`
  have hrep : ∀ s ∈ Icc (0 : ℝ) 1, outFn eps (mixPM ν₀ ν₁ s) ψ =
      ∑' t : ℕ, ∫ g, {g : ℕ → ℝ | gapSegLen eps g = t}.indicator (Φ s) g
        ∂(iidLaw (mixPM ν₀ ν₁ s)) := by
    intro s hs
    rw [outFn_eq_integral eps _ hψ]
    have hint : Integrable (Φ s) (iidLaw (mixPM ν₀ ν₁ s)) := by
      refine ((integrable_exp_output (hY s hs)).1.const_mul (M / η)).mono'
        (hΦm s).aestronglyMeasurable ?_
      filter_upwards [hSpos s hs] with g hg
      rw [Real.norm_eq_abs]
      exact hΦb s hs g hg
    exact integral_eq_tsum_gapSegLen (hΦm s) hint (hfin s hs)
  refine ContinuousOn.congr ?_ hrep
  refine continuousOn_tsum (u := fun t => M / η * ((BT + BY) / 2) * Real.exp (-β) ^ t)
    (fun t => ?_) ((summable_geometric_of_lt_one (Real.exp_pos _).le
      (Real.exp_lt_one_iff.2 (by linarith))).mul_left _) (fun t s hs => ?_)
  · -- continuity of each term
    refine continuousOn_prefix_integral hS (t := t)
      (G := fun s => {g : ℕ → ℝ | gapSegLen eps g = t}.indicator (Φ s))
      (B := fun g => M / η * Real.exp (2 * η / clo * gapKeys g t))
      (fun s => (hΦm s).indicator (measurableSet_gapSegLen_eq eps t))
      (fun s => (hΦst s).depPrefix_indicator t) (Eventually.of_forall fun g => ?_)
      ((integrable_exp_gapKeys hρexp t).const_mul _) (fun s hs => ?_)
    · by_cases hg : g ∈ {g : ℕ → ℝ | gapSegLen eps g = t}
      · simp only [Set.indicator_of_mem hg]
        refine hψ.continuous_testFn.comp_continuousOn (continuousOn_const.div hCc fun s hs => ?_)
        exact (hclo.trans_le (hC s hs)).ne'
      · simp only [Set.indicator_of_notMem hg]
        exact continuousOn_const
    · filter_upwards [hSpos (1 / 2) hhalf] with g hg
      by_cases hgt : g ∈ {g : ℕ → ℝ | gapSegLen eps g = t}
      · rw [Set.indicator_of_mem hgt]
        have hT : gapSegLen eps g = t := hgt
        have hSt : stopSum eps g = gapKeys g t := by rw [stopSum, hT, ENat.toNat_natCast]
        have hY0 : 0 ≤ stopSum eps g / Cf s := div_nonneg hg.le (hclo.le.trans (hC s hs))
        refine (hψ.abs_testFn_le_exp hη hY0).trans ?_
        rw [← hSt]
        have hle : 2 * η * (stopSum eps g / Cf s) ≤ 2 * η / clo * stopSum eps g := by
          have h1 : stopSum eps g / Cf s ≤ stopSum eps g / clo :=
            div_le_div_of_nonneg_left hg.le hclo (hC s hs)
          calc 2 * η * (stopSum eps g / Cf s) ≤ 2 * η * (stopSum eps g / clo) := by gcongr
            _ = 2 * η / clo * stopSum eps g := by ring
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hle) (by positivity)
      · rw [Set.indicator_of_notMem hgt, abs_zero]
        positivity
  · -- the uniform bound
    have hTe := integrable_exp_gapSegLen (hfin s hs) hK ha (htail s hs) (by positivity) hβa
    have hYe := integrable_exp_output (hY s hs)
    rw [Real.norm_eq_abs]
    refine (abs_integral_le_integral_abs).trans ?_
    have hdom : ∀ᵐ g ∂(iidLaw (mixPM ν₀ ν₁ s)),
        |{g : ℕ → ℝ | gapSegLen eps g = t}.indicator (Φ s) g| ≤
          M / η * Real.exp (-β) ^ t * ((Real.exp (2 * β * (gapSegLen eps g).toNat) +
            Real.exp (θY * (stopSum eps g / Cf s))) / 2) := by
      filter_upwards [hSpos s hs] with g hg
      by_cases hgt : g ∈ {g : ℕ → ℝ | gapSegLen eps g = t}
      · rw [Set.indicator_of_mem hgt]
        have hT : (gapSegLen eps g).toNat = t := by
          have : gapSegLen eps g = t := hgt
          rw [this, ENat.toNat_natCast]
        have hY0 : 0 ≤ stopSum eps g / Cf s := div_nonneg hg.le (hclo.le.trans (hC s hs))
        refine (hψ.abs_testFn_le_exp hη hY0).trans ?_
        rw [hT]
        have e1 : Real.exp (-β) ^ t * Real.exp (β * t) = 1 := by
          rw [← Real.exp_nat_mul, ← Real.exp_add]; simp; ring_nf
        have hsq := two_mul_le_add_sq (Real.exp (β * t))
          (Real.exp (2 * η * (stopSum eps g / Cf s)))
        have e2 : Real.exp (β * t) ^ 2 = Real.exp (2 * β * t) := by
          rw [← Real.exp_nat_mul]; ring_nf
        have e3 : Real.exp (2 * η * (stopSum eps g / Cf s)) ^ 2 =
            Real.exp (4 * η * (stopSum eps g / Cf s)) := by
          rw [← Real.exp_nat_mul]; ring_nf
        have e4 : Real.exp (4 * η * (stopSum eps g / Cf s)) ≤
            Real.exp (θY * (stopSum eps g / Cf s)) :=
          Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hηY hY0)
        have hMη : 0 ≤ M / η := by positivity
        calc M / η * Real.exp (2 * η * (stopSum eps g / Cf s))
            = M / η * Real.exp (-β) ^ t *
                (Real.exp (β * t) * Real.exp (2 * η * (stopSum eps g / Cf s))) := by
              rw [← mul_assoc, mul_assoc (M / η), e1, mul_one]
          _ ≤ M / η * Real.exp (-β) ^ t * ((Real.exp (2 * β * t) +
                Real.exp (θY * (stopSum eps g / Cf s))) / 2) := by
              gcongr
              rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
              nlinarith
      · rw [Set.indicator_of_notMem hgt, abs_zero]
        positivity
    have hint : Integrable (fun g => M / η * Real.exp (-β) ^ t *
        ((Real.exp (2 * β * (gapSegLen eps g).toNat) +
          Real.exp (θY * (stopSum eps g / Cf s))) / 2)) (iidLaw (mixPM ν₀ ν₁ s)) :=
      ((hTe.1.add hYe.1).div_const 2).const_mul _
    refine (integral_mono_of_nonneg (Eventually.of_forall fun g => abs_nonneg _) hint hdom).trans ?_
    rw [integral_const_mul, integral_div, integral_add hTe.1 hYe.1]
    have hMη : 0 ≤ M / η * Real.exp (-β) ^ t := by positivity
    calc M / η * Real.exp (-β) ^ t * ((∫ g, Real.exp (2 * β * (gapSegLen eps g).toNat)
          ∂(iidLaw (mixPM ν₀ ν₁ s)) + ∫ g, Real.exp (θY * (stopSum eps g / Cf s))
          ∂(iidLaw (mixPM ν₀ ν₁ s))) / 2)
        ≤ M / η * Real.exp (-β) ^ t * ((BT + BY) / 2) := by
          gcongr
          · exact hTe.2
          · exact hYe.2
      _ = M / η * ((BT + BY) / 2) * Real.exp (-β) ^ t := by ring

end

end PGM
