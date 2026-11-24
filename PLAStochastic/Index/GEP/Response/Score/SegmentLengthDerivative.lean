import PLAStochastic.Index.GEP.Response.Score.Insertion
import PLAStochastic.Index.GEP.Response.Score.UniformBounds

/-!
# WP4 leaf 4A-S, part 5: the derivative of `C_ε` along the mixture path

Fix `s₀ ∈ (0,1)`, the base law `ν̄ = ν_{s₀}` and the score `h` (`PLAStochastic/Index/GEP/Response/Score/MixturePath.lean`).
Since `{k < T}` reads only `g 0, …, g (k-1)`, the finite-dimensional likelihood ratio gives

  `C_ε(ν_s) = ∑_k P_s(k < T) = E_ν̄[∑_{k<T} ∏_{j<k} (1 + (s - s₀) h(g_j))]`   (`lawC_mix_eq`),

a polynomial in `s` for each path.  Its `s`-derivative at `s₀` is `∑_{k<T} ∑_{i<k} h(g_i)`, and
the dominated (Lipschitz) differentiation lemma applies because the Lipschitz constant
`K₀ T² (1 + δK₀)^T` is integrable for small `δ` (exponential stopping moment).  The single-gap
insertion identity (`integral_tsum_insert`) identifies the derivative with the kernel-bv §8
influence: `C'(s₀) = ∫ J_C d(ν₁ - ν₀)` (`hasDerivAt_lawC_mix`; JR §5, IL §8 (mix)).
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

/-- Two laws with densities, the data of a mixture path. -/
structure MixSetup (ν₀ ν₁ : ProbabilityMeasure ℝ) (f₀ f₁ : ℝ → ℝ) : Prop where
  nonneg₀ : ∀ y, 0 ≤ f₀ y
  nonneg₁ : ∀ y, 0 ≤ f₁ y
  meas₀ : Measurable f₀
  meas₁ : Measurable f₁
  dens₀ : (ν₀ : Measure ℝ) = volume.withDensity fun x => ENNReal.ofReal (f₀ x)
  dens₁ : (ν₁ : Measure ℝ) = volume.withDensity fun x => ENNReal.ofReal (f₁ x)

variable {ν₀ ν₁ : ProbabilityMeasure ℝ} {f₀ f₁ : ℝ → ℝ}

namespace MixSetup

theorem eq_withDensity (hS : MixSetup ν₀ ν₁ f₀ f₁) {s₀ : ℝ} (hs₀ : s₀ ∈ Ioo (0 : ℝ) 1) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) :
    (mixPM ν₀ ν₁ s : Measure ℝ) = (mixPM ν₀ ν₁ s₀ : Measure ℝ).withDensity
      fun y => (mixRatioNN f₀ f₁ s₀ s y : ℝ≥0∞) :=
  mixPM_eq_withDensity_ratio hS.nonneg₀ hS.nonneg₁ hS.meas₀ hS.meas₁ hS.dens₀ hS.dens₁ hs₀ hs

theorem score (hS : MixSetup ν₀ ν₁ f₀ f₁) {s₀ : ℝ} (hs₀ : s₀ ∈ Ioo (0 : ℝ) 1) (a : ℝ → ℝ)
    (ha : Integrable a (mixPM ν₀ ν₁ s₀ : Measure ℝ)) :
    ∫ y, a y * mixScore f₀ f₁ s₀ y ∂(mixPM ν₀ ν₁ s₀ : Measure ℝ) =
      ∫ y, a y ∂(ν₁ : Measure ℝ) - ∫ y, a y ∂(ν₀ : Measure ℝ) :=
  integral_mul_mixScore hS.nonneg₀ hS.nonneg₁ hS.meas₀ hS.meas₁ hS.dens₀ hS.dens₁ hs₀ ha

theorem abs_score_le (hS : MixSetup ν₀ ν₁ f₀ f₁) {s₀ : ℝ} (hs₀ : s₀ ∈ Ioo (0 : ℝ) 1) (y : ℝ) :
    |mixScore f₀ f₁ s₀ y| ≤ scoreBd s₀ :=
  abs_mixScore_le hS.nonneg₀ hS.nonneg₁ hs₀ y

theorem measurable_score (hS : MixSetup ν₀ ν₁ f₀ f₁) (s₀ : ℝ) :
    Measurable (mixScore f₀ f₁ s₀) :=
  measurable_mixScore hS.meas₀ hS.meas₁ s₀

theorem measurable_ratio (hS : MixSetup ν₀ ν₁ f₀ f₁) (s₀ s : ℝ) :
    Measurable (mixRatio f₀ f₁ s₀ s) :=
  measurable_mixRatio hS.meas₀ hS.meas₁ s₀ s

theorem ratio_nonneg (hS : MixSetup ν₀ ν₁ f₀ f₁) {s₀ : ℝ} (hs₀ : s₀ ∈ Ioo (0 : ℝ) 1) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (y : ℝ) : 0 ≤ mixRatio f₀ f₁ s₀ s y :=
  mixRatio_nonneg hS.nonneg₀ hS.nonneg₁ hs₀ hs y

theorem coe_ratioNN (hS : MixSetup ν₀ ν₁ f₀ f₁) {s₀ : ℝ} (hs₀ : s₀ ∈ Ioo (0 : ℝ) 1) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (y : ℝ) :
    (mixRatioNN f₀ f₁ s₀ s y : ℝ) = mixRatio f₀ f₁ s₀ s y :=
  coe_mixRatioNN hS.nonneg₀ hS.nonneg₁ hs₀ hs y

theorem le_smul_left (_hS : MixSetup ν₀ ν₁ f₀ f₁) {s₀ : ℝ} (hs₀ : s₀ ∈ Ioo (0 : ℝ) 1) :
    (ν₀ : Measure ℝ) ≤ ENNReal.ofReal (1 / (1 - s₀)) • (mixPM ν₀ ν₁ s₀ : Measure ℝ) :=
  mixPM_le_smul_left ν₀ ν₁ hs₀

theorem le_smul_right (_hS : MixSetup ν₀ ν₁ f₀ f₁) {s₀ : ℝ} (hs₀ : s₀ ∈ Ioo (0 : ℝ) 1) :
    (ν₁ : Measure ℝ) ≤ ENNReal.ofReal (1 / s₀) • (mixPM ν₀ ν₁ s₀ : Measure ℝ) :=
  mixPM_le_smul_right ν₀ ν₁ hs₀

end MixSetup

/-! ## Products of density ratios -/

theorem abs_prod_le_pow {n : ℕ} {a : ℕ → ℝ} {q : ℝ} (ha : ∀ j < n, |a j| ≤ q) :
    |∏ j ∈ Finset.range n, a j| ≤ q ^ n := by
  calc |∏ j ∈ Finset.range n, a j| = ∏ j ∈ Finset.range n, |a j| := Finset.abs_prod _ _
    _ ≤ ∏ _j ∈ Finset.range n, q :=
        Finset.prod_le_prod (fun j _ => abs_nonneg _) fun j hj => ha j (Finset.mem_range.1 hj)
    _ = q ^ n := by rw [Finset.prod_const, Finset.card_range]

/-- The telescoping bound `|∏ a - ∏ b| ≤ n q^n ε`. -/
theorem abs_prod_sub_prod_le {n : ℕ} {a b : ℕ → ℝ} {q ε : ℝ} (hq : 1 ≤ q) (hε : 0 ≤ ε)
    (ha : ∀ j < n, |a j| ≤ q) (hb : ∀ j < n, |b j| ≤ q) (hab : ∀ j < n, |a j - b j| ≤ ε) :
    |∏ j ∈ Finset.range n, a j - ∏ j ∈ Finset.range n, b j| ≤ n * q ^ n * ε := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ha' : ∀ j < n, |a j| ≤ q := fun j hj => ha j (by omega)
    have hb' : ∀ j < n, |b j| ≤ q := fun j hj => hb j (by omega)
    have hab' : ∀ j < n, |a j - b j| ≤ ε := fun j hj => hab j (by omega)
    have h1 := ih ha' hb' hab'
    have hPa := abs_prod_le_pow ha'
    have hq0 : 0 ≤ q := zero_le_one.trans hq
    have hqn : q ^ n ≤ q ^ (n + 1) := pow_le_pow_right₀ hq (Nat.le_succ n)
    rw [Finset.prod_range_succ, Finset.prod_range_succ]
    have e : (∏ j ∈ Finset.range n, a j) * a n - (∏ j ∈ Finset.range n, b j) * b n =
        (∏ j ∈ Finset.range n, a j) * (a n - b n) +
          (∏ j ∈ Finset.range n, a j - ∏ j ∈ Finset.range n, b j) * b n := by ring
    rw [e]
    calc |(∏ j ∈ Finset.range n, a j) * (a n - b n) +
          (∏ j ∈ Finset.range n, a j - ∏ j ∈ Finset.range n, b j) * b n|
        ≤ |∏ j ∈ Finset.range n, a j| * |a n - b n| +
          |∏ j ∈ Finset.range n, a j - ∏ j ∈ Finset.range n, b j| * |b n| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ q ^ n * ε + (n * q ^ n * ε) * q := by
          gcongr
          · exact hab n (Nat.lt_succ_self n)
          · exact hb n (Nat.lt_succ_self n)
      _ ≤ q ^ (n + 1) * ε + (n * q ^ (n + 1)) * ε := by
          have : n * q ^ n * ε * q = n * q ^ (n + 1) * ε := by ring
          rw [this]
          gcongr
      _ = ((n + 1 : ℕ) : ℝ) * q ^ (n + 1) * ε := by push_cast; ring

/-- The density ratios near the base point: `|r_s| ≤ q` and `|r_s - r_{s'}| ≤ K₀ |s - s'|`. -/
theorem abs_mixRatio_le_of_near (hS : MixSetup ν₀ ν₁ f₀ f₁) {s₀ : ℝ} (hs₀ : s₀ ∈ Ioo (0 : ℝ) 1)
    {δ s : ℝ} (hs : |s - s₀| ≤ δ) (y : ℝ) :
    |mixRatio f₀ f₁ s₀ s y| ≤ 1 + δ * scoreBd s₀ :=
  (abs_mixRatio_le hS.nonneg₀ hS.nonneg₁ hs₀ s y).trans (by
    gcongr; exact (scoreBd_pos hs₀).le)

theorem abs_mixRatio_sub (hS : MixSetup ν₀ ν₁ f₀ f₁) {s₀ : ℝ} (hs₀ : s₀ ∈ Ioo (0 : ℝ) 1)
    (s s' y : ℝ) :
    |mixRatio f₀ f₁ s₀ s y - mixRatio f₀ f₁ s₀ s' y| ≤ scoreBd s₀ * |s - s'| := by
  have e : mixRatio f₀ f₁ s₀ s y - mixRatio f₀ f₁ s₀ s' y = (s - s') * mixScore f₀ f₁ s₀ y := by
    simp only [mixRatio]; ring
  rw [e, abs_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (hS.abs_score_le hs₀ y) (abs_nonneg _)

/-- Lipschitz bound of a product of density ratios near the base point. -/
theorem abs_prod_mixRatio_sub_le (hS : MixSetup ν₀ ν₁ f₀ f₁) {s₀ : ℝ} (hs₀ : s₀ ∈ Ioo (0 : ℝ) 1)
    {δ s s' : ℝ} (hδ : 0 ≤ δ) (hs : |s - s₀| ≤ δ) (hs' : |s' - s₀| ≤ δ) (n : ℕ) (g : ℕ → ℝ) :
    |∏ j ∈ Finset.range n, mixRatio f₀ f₁ s₀ s (g j) -
        ∏ j ∈ Finset.range n, mixRatio f₀ f₁ s₀ s' (g j)| ≤
      n * (1 + δ * scoreBd s₀) ^ n * (scoreBd s₀ * |s - s'|) := by
  have hK := (scoreBd_pos hs₀).le
  refine abs_prod_sub_prod_le (by nlinarith) (by positivity)
    (fun j _ => abs_mixRatio_le_of_near hS hs₀ hs _)
    (fun j _ => abs_mixRatio_le_of_near hS hs₀ hs' _)
    (fun j _ => abs_mixRatio_sub hS hs₀ s s' _)

/-- The derivative of a product of density ratios at the base point. -/
theorem hasDerivAt_prod_mixRatio (s₀ : ℝ) (n : ℕ) (g : ℕ → ℝ) :
    HasDerivAt (fun s => ∏ j ∈ Finset.range n, mixRatio f₀ f₁ s₀ s (g j))
      (∑ i ∈ Finset.range n, mixScore f₀ f₁ s₀ (g i)) s₀ := by
  have hd : ∀ i ∈ Finset.range n, HasDerivAt (fun s => mixRatio f₀ f₁ s₀ s (g i))
      (mixScore f₀ f₁ s₀ (g i)) s₀ := by
    intro i _
    have := ((hasDerivAt_id s₀).sub_const s₀).mul_const (mixScore f₀ f₁ s₀ (g i))
    simpa [mixRatio] using this.const_add 1
  have h := HasDerivAt.fun_finsetProd hd
  have e : ∀ i ∈ Finset.range n, (∏ j ∈ (Finset.range n).erase i,
      mixRatio f₀ f₁ s₀ s₀ (g j)) • mixScore f₀ f₁ s₀ (g i) = mixScore f₀ f₁ s₀ (g i) := by
    intro i _
    rw [Finset.prod_eq_one fun j _ => by simp [mixRatio], one_smul]
  rwa [Finset.sum_congr rfl e] at h

/-! ## The representation of `C_ε` -/

/-- The prefix-sum functional `∑_{k<T} ∏_{j<k} r(g_j)`. -/
def cSum (eps : ℝ) (r : ℝ → ℝ) (g : ℕ → ℝ) : ℝ :=
  ∑ k ∈ Finset.range (gapSegLen eps g).toNat, ∏ j ∈ Finset.range k, r (g j)

theorem measurable_cSum (eps : ℝ) {r : ℝ → ℝ} (hr : Measurable r) : Measurable (cSum eps r) := by
  have hm : Measurable fun p : (ℕ → ℝ) × ℕ =>
      ∑ k ∈ Finset.range p.2, ∏ j ∈ Finset.range k, r (p.1 j) :=
    measurable_from_prod_countable_left fun n => by
      change Measurable fun x : ℕ → ℝ => ∑ k ∈ Finset.range n, ∏ j ∈ Finset.range k, r (x j)
      exact Finset.measurable_sum _ fun k _ =>
        Finset.measurable_prod _ fun j _ => hr.comp (measurable_pi_apply j)
  exact hm.comp (measurable_id.prodMk (measurable_gapSegLen_toNat eps))

theorem tsum_mul_indicator_lt {eps : ℝ} {g : ℕ → ℝ} {n : ℕ} (hn : gapSegLen eps g = n)
    {β : Type*} [NonAssocSemiring β] [TopologicalSpace β] [T2Space β]
    (d : ℕ → β) :
    ∑' k : ℕ, d k * {g : ℕ → ℝ | (k : ℕ∞) < gapSegLen eps g}.indicator (fun _ => (1 : β)) g =
      ∑ k ∈ Finset.range n, d k := by
  rw [tsum_eq_sum (s := Finset.range n)]
  · refine Finset.sum_congr rfl fun k hk => ?_
    rw [Set.indicator_of_mem (show g ∈ {g : ℕ → ℝ | (k : ℕ∞) < gapSegLen eps g} by
      simp only [Set.mem_ofPred_eq, hn, Nat.cast_lt]; exact Finset.mem_range.1 hk), mul_one]
  · intro k hk
    rw [Set.indicator_of_notMem (show g ∉ {g : ℕ → ℝ | (k : ℕ∞) < gapSegLen eps g} by
      simp only [Set.mem_ofPred_eq, hn, Nat.cast_lt]; exact fun h => hk (Finset.mem_range.2 h)),
      mul_zero]

/-- **`C_ε` along the path as one expectation under the base law.** -/
theorem lawC_mix_eq (hS : MixSetup ν₀ ν₁ f₀ f₁) {s₀ : ℝ} (hs₀ : s₀ ∈ Ioo (0 : ℝ) 1) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) {eps : ℝ}
    (hfin : ∀ᵐ g ∂(iidLaw (mixPM ν₀ ν₁ s)), gapSegLen eps g ≠ ⊤)
    (hfin₀ : ∀ᵐ g ∂(iidLaw (mixPM ν₀ ν₁ s₀)), gapSegLen eps g ≠ ⊤) :
    lawC eps (mixPM ν₀ ν₁ s) =
      ∫ g, cSum eps (mixRatio f₀ f₁ s₀ s) g ∂(iidLaw (mixPM ν₀ ν₁ s₀)) := by
  set r : ℝ → ℝ≥0∞ := fun y => ENNReal.ofReal (mixRatio f₀ f₁ s₀ s y) with hr
  have hrm : Measurable r := (hS.measurable_ratio s₀ s).ennreal_ofReal
  have hμ : (mixPM ν₀ ν₁ s : Measure ℝ) = (mixPM ν₀ ν₁ s₀ : Measure ℝ).withDensity r :=
    hS.eq_withDensity hs₀ hs
  have hG : ∀ k : ℕ, Measurable ({g : ℕ → ℝ | (k : ℕ∞) < gapSegLen eps g}.indicator
      (fun _ => (1 : ℝ≥0∞))) := fun k =>
    measurable_const.indicator (measurableSet_lt_gapSegLen eps k)
  have hGd : ∀ k : ℕ, DepPrefix k ({g : ℕ → ℝ | (k : ℕ∞) < gapSegLen eps g}.indicator
      (fun _ => (1 : ℝ≥0∞))) := by
    intro k g g' h
    by_cases hg : (k : ℕ∞) < gapSegLen eps g
    · rw [Set.indicator_of_mem (show g ∈ {g : ℕ → ℝ | (k : ℕ∞) < gapSegLen eps g} from hg),
        Set.indicator_of_mem (show g' ∈ {g : ℕ → ℝ | (k : ℕ∞) < gapSegLen eps g} from
          (lt_gapSegLen_congr h).1 hg)]
    · rw [Set.indicator_of_notMem (show g ∉ {g : ℕ → ℝ | (k : ℕ∞) < gapSegLen eps g} from hg),
        Set.indicator_of_notMem (show g' ∉ {g : ℕ → ℝ | (k : ℕ∞) < gapSegLen eps g} from
          fun h' => hg ((lt_gapSegLen_congr h).2 h'))]
  have hl := lintegral_tsum_prefix (mixPM ν₀ ν₁ s₀) (mixPM ν₀ ν₁ s) hrm hμ hG hGd
  have hL : ∫⁻ g, ENNReal.ofReal ((gapSegLen eps g).toNat : ℝ) ∂(iidLaw (mixPM ν₀ ν₁ s)) =
      ∫⁻ g, ENNReal.ofReal (cSum eps (mixRatio f₀ f₁ s₀ s) g) ∂(iidLaw (mixPM ν₀ ν₁ s₀)) := by
    calc _ = ∫⁻ g, ∑' k : ℕ, {g : ℕ → ℝ | (k : ℕ∞) < gapSegLen eps g}.indicator
          (fun _ => (1 : ℝ≥0∞)) g ∂(iidLaw (mixPM ν₀ ν₁ s)) := by
          refine lintegral_congr_ae ?_
          filter_upwards [hfin] with g hg
          obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 hg
          have := tsum_mul_indicator_lt hn.symm (fun _ => (1 : ℝ≥0∞))
          simp only [one_mul] at this
          rw [this, ← hn, ENat.toNat_natCast, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
            mul_one, ENNReal.ofReal_natCast]
      _ = _ := hl
      _ = _ := by
          refine lintegral_congr_ae ?_
          filter_upwards [hfin₀] with g hg
          obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 hg
          rw [tsum_mul_indicator_lt hn.symm, cSum, ← hn, ENat.toNat_natCast,
            ENNReal.ofReal_sum_of_nonneg (fun k _ => Finset.prod_nonneg fun j _ =>
              hS.ratio_nonneg hs₀ hs _)]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [ENNReal.ofReal_prod_of_nonneg (fun j _ => hS.ratio_nonneg hs₀ hs _)]
  have h1 : lawC eps (mixPM ν₀ ν₁ s) = (∫⁻ g, ENNReal.ofReal ((gapSegLen eps g).toNat : ℝ)
      ∂(iidLaw (mixPM ν₀ ν₁ s))).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun g => Nat.cast_nonneg _)
      (measurable_toNat_gapSegLen eps).aestronglyMeasurable
  rw [h1, hL]
  exact (integral_eq_lintegral_of_nonneg_ae (f := cSum eps (mixRatio f₀ f₁ s₀ s))
    (Eventually.of_forall fun g =>
      Finset.sum_nonneg fun k _ => Finset.prod_nonneg fun j _ => hS.ratio_nonneg hs₀ hs _)
    (measurable_cSum eps (hS.measurable_ratio s₀ s)).aestronglyMeasurable).symm

/-! ## Differentiation at the base point -/

/-- The derivative functional `∑_{k<T} ∑_{i<k} h(g_i)`. -/
def cSumDer (eps : ℝ) (h : ℝ → ℝ) (g : ℕ → ℝ) : ℝ :=
  ∑ k ∈ Finset.range (gapSegLen eps g).toNat, ∑ i ∈ Finset.range k, h (g i)

theorem measurable_cSumDer (eps : ℝ) {h : ℝ → ℝ} (hh : Measurable h) :
    Measurable (cSumDer eps h) := by
  have hm : Measurable fun p : (ℕ → ℝ) × ℕ =>
      ∑ k ∈ Finset.range p.2, ∑ i ∈ Finset.range k, h (p.1 i) :=
    measurable_from_prod_countable_left fun n => by
      change Measurable fun x : ℕ → ℝ => ∑ k ∈ Finset.range n, ∑ i ∈ Finset.range k, h (x i)
      exact Finset.measurable_sum _ fun k _ =>
        Finset.measurable_sum _ fun i _ => hh.comp (measurable_pi_apply i)
  exact hm.comp (measurable_id.prodMk (measurable_gapSegLen_toNat eps))

theorem cSum_base (eps s₀ : ℝ) (g : ℕ → ℝ) :
    cSum eps (mixRatio f₀ f₁ s₀ s₀) g = (gapSegLen eps g).toNat := by
  simp [cSum, mixRatio]

theorem hasDerivAt_cSum (eps s₀ : ℝ) (g : ℕ → ℝ) :
    HasDerivAt (fun s => cSum eps (mixRatio f₀ f₁ s₀ s) g)
      (cSumDer eps (mixScore f₀ f₁ s₀) g) s₀ :=
  HasDerivAt.fun_sum fun k _ => hasDerivAt_prod_mixRatio s₀ k g

theorem abs_cSum_sub_le (hS : MixSetup ν₀ ν₁ f₀ f₁) {s₀ : ℝ} (hs₀ : s₀ ∈ Ioo (0 : ℝ) 1)
    (eps : ℝ) {δ s s' : ℝ} (hδ : 0 ≤ δ) (hs : |s - s₀| ≤ δ) (hs' : |s' - s₀| ≤ δ)
    (g : ℕ → ℝ) :
    |cSum eps (mixRatio f₀ f₁ s₀ s) g - cSum eps (mixRatio f₀ f₁ s₀ s') g| ≤
      ((gapSegLen eps g).toNat : ℝ) ^ 2 * (1 + δ * scoreBd s₀) ^ (gapSegLen eps g).toNat *
        (scoreBd s₀ * |s - s'|) := by
  set n := (gapSegLen eps g).toNat
  have hK := (scoreBd_pos hs₀).le
  have hq : 1 ≤ 1 + δ * scoreBd s₀ := by nlinarith
  rw [cSum, cSum, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ k ∈ Finset.range n, |∏ j ∈ Finset.range k, mixRatio f₀ f₁ s₀ s (g j) -
        ∏ j ∈ Finset.range k, mixRatio f₀ f₁ s₀ s' (g j)|
      ≤ ∑ _k ∈ Finset.range n, (n : ℝ) * (1 + δ * scoreBd s₀) ^ n * (scoreBd s₀ * |s - s'|) := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hkn : k ≤ n := (Finset.mem_range.1 hk).le
        refine (abs_prod_mixRatio_sub_le hS hs₀ hδ hs hs' k g).trans ?_
        gcongr
    _ = (n : ℝ) ^ 2 * (1 + δ * scoreBd s₀) ^ n * (scoreBd s₀ * |s - s'|) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

/-- `n² q^n ≤ (16/κ²) e^{κ n}` when `q ≤ e^{κ/4}`. -/
theorem sq_mul_pow_le_exp {κ q : ℝ} (hκ : 0 < κ) (hq0 : 0 ≤ q) (hq : q ≤ Real.exp (κ / 4))
    (n : ℕ) : (n : ℝ) ^ 2 * q ^ n ≤ 16 / κ ^ 2 * Real.exp (κ * n) := by
  have h1 : (n : ℝ) ≤ Real.exp (κ / 4 * n) / (κ / 4) := le_exp_div (by positivity)
  have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h2 : (n : ℝ) ^ 2 ≤ (Real.exp (κ / 4 * n) / (κ / 4)) ^ 2 := pow_le_pow_left₀ h0 h1 2
  have h3 : q ^ n ≤ Real.exp (κ / 4 * n) := by
    calc q ^ n ≤ Real.exp (κ / 4) ^ n := pow_le_pow_left₀ hq0 hq n
      _ = Real.exp (κ / 4 * n) := by rw [← Real.exp_nat_mul]; ring_nf
  calc (n : ℝ) ^ 2 * q ^ n ≤ (Real.exp (κ / 4 * n) / (κ / 4)) ^ 2 * Real.exp (κ / 4 * n) :=
        mul_le_mul h2 h3 (by positivity) (by positivity)
    _ = 16 / κ ^ 2 * (Real.exp (κ / 4 * n) * Real.exp (κ / 4 * n) * Real.exp (κ / 4 * n)) := by
        field_simp
        ring
    _ = 16 / κ ^ 2 * Real.exp (κ * (3 / 4) * n) := by
        rw [← Real.exp_add, ← Real.exp_add]; ring_nf
    _ ≤ 16 / κ ^ 2 * Real.exp (κ * n) := by
        gcongr
        nlinarith

/-- The radius of the Lipschitz ball at the base point. -/
def baseRad (s₀ κ : ℝ) : ℝ := min (min s₀ (1 - s₀)) (κ / (4 * scoreBd s₀)) / 2

theorem baseRad_pos {s₀ κ : ℝ} (hs₀ : s₀ ∈ Ioo (0 : ℝ) 1) (hκ : 0 < κ) : 0 < baseRad s₀ κ := by
  have h1 : 0 < 1 - s₀ := by linarith [hs₀.2]
  have := scoreBd_pos hs₀
  have := hs₀.1
  unfold baseRad
  positivity

theorem ball_baseRad_subset (s₀ κ : ℝ) :
    Metric.ball s₀ (baseRad s₀ κ) ⊆ Icc (0 : ℝ) 1 := by
  intro s hs
  rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hs
  have h1 : baseRad s₀ κ ≤ s₀ / 2 := by
    unfold baseRad
    have := min_le_left (min s₀ (1 - s₀)) (κ / (4 * scoreBd s₀))
    have := min_le_left s₀ (1 - s₀)
    linarith
  have h2 : baseRad s₀ κ ≤ (1 - s₀) / 2 := by
    unfold baseRad
    have := min_le_left (min s₀ (1 - s₀)) (κ / (4 * scoreBd s₀))
    have := min_le_right s₀ (1 - s₀)
    linarith
  constructor <;> linarith

theorem pow_baseRad_le {s₀ κ : ℝ} (hs₀ : s₀ ∈ Ioo (0 : ℝ) 1) (hκ : 0 < κ) :
    1 + baseRad s₀ κ * scoreBd s₀ ≤ Real.exp (κ / 4) := by
  have hK := scoreBd_pos hs₀
  have h1 : baseRad s₀ κ * scoreBd s₀ ≤ κ / 4 := by
    have : baseRad s₀ κ ≤ κ / (4 * scoreBd s₀) / 2 := by
      unfold baseRad
      have := min_le_right (min s₀ (1 - s₀)) (κ / (4 * scoreBd s₀))
      linarith
    calc baseRad s₀ κ * scoreBd s₀ ≤ κ / (4 * scoreBd s₀) / 2 * scoreBd s₀ :=
          mul_le_mul_of_nonneg_right this hK.le
      _ = κ / 8 := by field_simp; ring
      _ ≤ κ / 4 := by linarith
  linarith [Real.add_one_le_exp (κ / 4)]

/-- **Identification of `C'` with the influence `J_C`.** -/
theorem integral_cSumDer_eq (hS : MixSetup ν₀ ν₁ f₀ f₁) {s₀ : ℝ} (hs₀ : s₀ ∈ Ioo (0 : ℝ) 1)
    {eps : ℝ} (hfin₀ : ∀ᵐ g ∂(iidLaw (mixPM ν₀ ν₁ s₀)), gapSegLen eps g ≠ ⊤)
    (hT2 : Integrable (fun g => ((gapSegLen eps g).toNat : ℝ) ^ 2) (iidLaw (mixPM ν₀ ν₁ s₀))) :
    Integrable (lawJC eps (mixPM ν₀ ν₁ s₀)) (ν₀ : Measure ℝ) ∧
      Integrable (lawJC eps (mixPM ν₀ ν₁ s₀)) (ν₁ : Measure ℝ) ∧
      ∫ g, cSumDer eps (mixScore f₀ f₁ s₀) g ∂(iidLaw (mixPM ν₀ ν₁ s₀)) =
        ∫ x, lawJC eps (mixPM ν₀ ν₁ s₀) x ∂(ν₁ : Measure ℝ) -
          ∫ x, lawJC eps (mixPM ν₀ ν₁ s₀) x ∂(ν₀ : Measure ℝ) := by
  set νb := mixPM ν₀ ν₁ s₀ with hνb
  set G : ℕ → ℕ → (ℕ → ℝ) → ℝ := fun k _ =>
    {g : ℕ → ℝ | (k : ℕ∞) < gapSegLen eps g}.indicator (fun _ => (1 : ℝ)) with hG
  have hGm : ∀ k i, Measurable (G k i) := fun k _ =>
    measurable_const.indicator (measurableSet_lt_gapSegLen eps k)
  -- summability
  have hsum : ∑' k, ∑ i ∈ Finset.range k, ∫⁻ g, ‖G k i g‖ₑ ∂(iidLaw νb) ≠ ⊤ := by
    have e1 : ∑' k, ∑ i ∈ Finset.range k, ∫⁻ g, ‖G k i g‖ₑ ∂(iidLaw νb) =
        ∫⁻ g, ∑' k : ℕ, ∑ i ∈ Finset.range k, ‖G k i g‖ₑ ∂(iidLaw νb) := by
      rw [lintegral_tsum fun k => (Finset.measurable_sum _ fun i _ => (hGm k i).enorm).aemeasurable]
      congr 1
      funext k
      exact (lintegral_finsetSum _ fun i _ => (hGm k i).enorm).symm
    rw [e1]
    refine ne_top_of_le_ne_top (hT2.2.ne) (lintegral_mono_ae ?_)
    filter_upwards [hfin₀] with g hg
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 hg
    have e2 : ∀ k : ℕ, ∑ i ∈ Finset.range k, ‖G k i g‖ₑ = (k : ℝ≥0∞) *
        {g : ℕ → ℝ | (k : ℕ∞) < gapSegLen eps g}.indicator (fun _ => (1 : ℝ≥0∞)) g := by
      intro k
      simp only [hG, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      congr 1
      by_cases hk : g ∈ {g : ℕ → ℝ | (k : ℕ∞) < gapSegLen eps g}
      · rw [Set.indicator_of_mem hk, Set.indicator_of_mem hk, enorm_one]
      · rw [Set.indicator_of_notMem hk, Set.indicator_of_notMem hk, enorm_zero]
    simp_rw [e2]
    rw [tsum_mul_indicator_lt hn.symm, ← hn, ENat.toNat_natCast]
    rw [Real.enorm_eq_ofReal (by positivity)]
    calc ∑ k ∈ Finset.range n, (k : ℝ≥0∞) ≤ ∑ _k ∈ Finset.range n, (n : ℝ≥0∞) :=
          Finset.sum_le_sum fun k hk => by exact_mod_cast (Finset.mem_range.1 hk).le
      _ = ENNReal.ofReal ((n : ℝ) ^ 2) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
            ENNReal.ofReal_pow (Nat.cast_nonneg n), ENNReal.ofReal_natCast, sq]
  obtain ⟨hI₀, hI₁, hE⟩ := integral_tsum_insert νb ν₀ ν₁ (hS.measurable_score s₀)
    (hS.abs_score_le hs₀) (hS.score hs₀) ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    (hS.le_smul_left hs₀) (hS.le_smul_right hs₀) (fun k => Finset.range k) G hGm hsum
  have hk : (fun y => ∑' k, ∑ i ∈ Finset.range k,
      ∫ g, G k i (Function.update g i y) ∂(iidLaw νb)) = lawJC eps νb := by
    funext y
    rw [lawJC]
    refine tsum_congr fun k => Finset.sum_congr rfl fun i _ => ?_
    have e : (fun g : ℕ → ℝ => G k i (Function.update g i y)) =
        {g : ℕ → ℝ | (k : ℕ∞) < gapSegLen eps (Function.update g i y)}.indicator
          (fun _ => (1 : ℝ)) := by
      funext g
      simp only [hG]
      by_cases hg : (k : ℕ∞) < gapSegLen eps (Function.update g i y)
      · rw [Set.indicator_of_mem (show Function.update g i y ∈
          {g : ℕ → ℝ | (k : ℕ∞) < gapSegLen eps g} from hg), Set.indicator_of_mem
          (show g ∈ {g : ℕ → ℝ | (k : ℕ∞) < gapSegLen eps (Function.update g i y)} from hg)]
      · rw [Set.indicator_of_notMem (show Function.update g i y ∉
          {g : ℕ → ℝ | (k : ℕ∞) < gapSegLen eps g} from hg), Set.indicator_of_notMem
          (show g ∉ {g : ℕ → ℝ | (k : ℕ∞) < gapSegLen eps (Function.update g i y)} from hg)]
    have hmeas : MeasurableSet {g : ℕ → ℝ | (k : ℕ∞) < gapSegLen eps (Function.update g i y)} :=
      (measurableSet_lt_gapSegLen eps k).preimage (by classical exact measurable_update_left)
    change ∫ g, (fun g : ℕ → ℝ => G k i (Function.update g i y)) g ∂(iidLaw νb) = _
    rw [e, integral_indicator_const _ hmeas, smul_eq_mul, mul_one]
  rw [hk] at hI₀ hI₁ hE
  refine ⟨hI₀, hI₁, ?_⟩
  rw [← hE]
  refine integral_congr_ae ?_
  filter_upwards [hfin₀] with g hg
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 hg
  have e3 : ∀ k : ℕ, ∑ i ∈ Finset.range k, G k i g * mixScore f₀ f₁ s₀ (g i) =
      (∑ i ∈ Finset.range k, mixScore f₀ f₁ s₀ (g i)) *
        {g : ℕ → ℝ | (k : ℕ∞) < gapSegLen eps g}.indicator (fun _ => (1 : ℝ)) g := by
    intro k
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  simp_rw [e3]
  rw [tsum_mul_indicator_lt hn.symm, cSumDer, ← hn, ENat.toNat_natCast]

/-- **The derivative of `C_ε` along the mixture path** (JR §5; kernel-bv §8). -/
theorem hasDerivAt_lawC_mix (hS : MixSetup ν₀ ν₁ f₀ f₁) {s₀ : ℝ} (hs₀ : s₀ ∈ Ioo (0 : ℝ) 1)
    {eps : ℝ} (hfin : ∀ s ∈ Icc (0 : ℝ) 1, ∀ᵐ g ∂(iidLaw (mixPM ν₀ ν₁ s)), gapSegLen eps g ≠ ⊤)
    {κ : ℝ} (hκ : 0 < κ)
    (hexp : Integrable (fun g => Real.exp (κ * (gapSegLen eps g).toNat))
      (iidLaw (mixPM ν₀ ν₁ s₀))) :
    Integrable (lawJC eps (mixPM ν₀ ν₁ s₀)) (ν₀ : Measure ℝ) ∧
      Integrable (lawJC eps (mixPM ν₀ ν₁ s₀)) (ν₁ : Measure ℝ) ∧
      HasDerivAt (fun s => lawC eps (mixPM ν₀ ν₁ s))
        (∫ x, lawJC eps (mixPM ν₀ ν₁ s₀) x ∂(ν₁ : Measure ℝ) -
          ∫ x, lawJC eps (mixPM ν₀ ν₁ s₀) x ∂(ν₀ : Measure ℝ)) s₀ ∧
      ∃ L : ℝ, ∀ s ∈ Metric.ball s₀ (baseRad s₀ κ), ∀ s' ∈ Metric.ball s₀ (baseRad s₀ κ),
        |lawC eps (mixPM ν₀ ν₁ s) - lawC eps (mixPM ν₀ ν₁ s')| ≤ L * |s - s'| := by
  set νb := mixPM ν₀ ν₁ s₀ with hνb
  set P := iidLaw νb with hP
  set K₀ := scoreBd s₀ with hK₀
  set δ := baseRad s₀ κ with hδ
  have hK := scoreBd_pos hs₀
  have hδ0 : 0 < δ := baseRad_pos hs₀ hκ
  have hq := pow_baseRad_le hs₀ hκ
  have hs₀I : s₀ ∈ Icc (0 : ℝ) 1 := ⟨hs₀.1.le, hs₀.2.le⟩
  have hfin₀ := hfin s₀ hs₀I
  set T : (ℕ → ℝ) → ℝ := fun g => ((gapSegLen eps g).toNat : ℝ) with hT
  have hTm : Measurable T := measurable_from_top.comp (measurable_gapSegLen_toNat eps)
  set F : ℝ → (ℕ → ℝ) → ℝ := fun s g => cSum eps (mixRatio f₀ f₁ s₀ s) g with hF
  set bnd : (ℕ → ℝ) → ℝ := fun g => K₀ * (16 / κ ^ 2) * Real.exp (κ * T g) with hbnd
  have hbnd_int : Integrable bnd P := hexp.const_mul _
  have hbnd0 : ∀ g, 0 ≤ bnd g := fun g => by positivity
  have hT2 : Integrable (fun g => T g ^ 2) P := by
    refine (hexp.const_mul (16 / κ ^ 2)).mono' (hTm.pow_const 2).aestronglyMeasurable
      (Eventually.of_forall fun g => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have := sq_mul_pow_le_exp hκ zero_le_one (Real.one_le_exp (by positivity))
      (gapSegLen eps g).toNat
    simpa using this
  have hTint : Integrable T P := by
    refine ((hexp.const_mul (1 / κ))).mono' hTm.aestronglyMeasurable
      (Eventually.of_forall fun g => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
    have := le_exp_div (t := T g) hκ
    rw [div_eq_mul_inv] at this
    calc T g ≤ Real.exp (κ * T g) * κ⁻¹ := this
      _ = 1 / κ * Real.exp (κ * T g) := by ring
  -- the Lipschitz estimate on the ball
  have hlip : ∀ g, ∀ s ∈ Metric.ball s₀ δ, ∀ s' ∈ Metric.ball s₀ δ,
      |F s g - F s' g| ≤ bnd g * |s - s'| := by
    intro g s hs s' hs'
    have hs1 : |s - s₀| ≤ δ := (Metric.mem_ball.1 hs).le
    have hs2 : |s' - s₀| ≤ δ := (Metric.mem_ball.1 hs').le
    refine (abs_cSum_sub_le hS hs₀ eps hδ0.le hs1 hs2 g).trans ?_
    have := sq_mul_pow_le_exp hκ (by positivity) hq (gapSegLen eps g).toNat
    calc ((gapSegLen eps g).toNat : ℝ) ^ 2 * (1 + δ * K₀) ^ (gapSegLen eps g).toNat *
          (K₀ * |s - s'|) ≤ 16 / κ ^ 2 * Real.exp (κ * (gapSegLen eps g).toNat) *
          (K₀ * |s - s'|) := by gcongr
      _ = bnd g * |s - s'| := by simp only [hbnd, hT]; ring
  have hderiv := hasDerivAt_integral_of_dominated_loc_of_lip (μ := P) (F := F)
    (F' := cSumDer eps (mixScore f₀ f₁ s₀)) (x₀ := s₀) (bound := bnd)
    (Metric.ball_mem_nhds s₀ hδ0)
    (Eventually.of_forall fun s => (measurable_cSum eps (hS.measurable_ratio s₀ s)).aestronglyMeasurable)
    (by
      have e : F s₀ = T := funext fun g => cSum_base eps s₀ g
      rw [e]; exact hTint)
    (measurable_cSumDer eps (hS.measurable_score s₀)).aestronglyMeasurable
    (Eventually.of_forall fun g => LipschitzOnWith.of_dist_le_mul fun s hs s' hs' => by
      rw [Real.dist_eq, Real.dist_eq, Real.coe_nnabs, abs_of_nonneg (hbnd0 g)]
      exact hlip g s hs s' hs')
    hbnd_int (Eventually.of_forall fun g => hasDerivAt_cSum eps s₀ g)
  have hloc : ∀ s ∈ Icc (0 : ℝ) 1, lawC eps (mixPM ν₀ ν₁ s) = ∫ g, F s g ∂P := fun s hs =>
    lawC_mix_eq hS hs₀ hs (hfin s hs) hfin₀
  obtain ⟨hJ₀, hJ₁, hid⟩ := integral_cSumDer_eq hS hs₀ hfin₀ hT2
  refine ⟨hJ₀, hJ₁, ?_, ∫ g, bnd g ∂P, fun s hs s' hs' => ?_⟩
  · rw [← hid]
    refine hderiv.2.congr_of_eventuallyEq ?_
    filter_upwards [Icc_mem_nhds hs₀.1 hs₀.2] with s hs using hloc s hs
  · have hsI := ball_baseRad_subset s₀ κ hs
    have hs'I := ball_baseRad_subset s₀ κ hs'
    have hFint : ∀ t ∈ Metric.ball s₀ δ, Integrable (F t) P := by
      intro t ht
      refine (hTint.norm.add (hbnd_int.mul_const |t - s₀|)).mono'
        (measurable_cSum eps (hS.measurable_ratio s₀ t)).aestronglyMeasurable
        (Eventually.of_forall fun g => ?_)
      have h1 := hlip g t ht s₀ (Metric.mem_ball_self hδ0)
      have e : F s₀ g = T g := cSum_base eps s₀ g
      rw [e] at h1
      simp only [Pi.add_apply, Real.norm_eq_abs]
      have := abs_sub_abs_le_abs_sub (F t g) (T g)
      linarith
    rw [hloc s hsI, hloc s' hs'I, ← integral_sub (hFint s hs) (hFint s' hs'),
      ← integral_mul_const]
    refine (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg
      (Eventually.of_forall fun g => abs_nonneg _) (hbnd_int.mul_const _)
      (Eventually.of_forall fun g => hlip g s hs s' hs'))

end

end PGM
