import PLAStochastic.Swing.Ladder.Renewal.RecordValues
import PLAStochastic.Swing.Ladder.Renewal.ExpansionInterface

/-! # The residual-life integral in section form

`eq:overshootrenewalidentity` is a Stieltjes integral against the renewal
measure.  Exchanging the two variables writes it as an integral over the ladder
height of the renewal mass of a window ending at the level.  In that form the
uniform renewal expansion applies directly to each window, which is the shape
used by the passage to the equilibrium overshoot tail.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical MeasureTheory
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

instance ladderRenewalMeasure_sfinite (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    SFinite (ladderRenewalMeasure ν) := by
  rw [ladderRenewalMeasure]
  exact sfinite_sum_of_countable _

/-- Exchanging the two variables in the residual-life integral. -/
theorem renewalOvershootTail_eq_window (ν : Measure ℝ) [IsProbabilityMeasure ν] (b t : ℝ) :
    renewalOvershootTail ν b t =
      ∫⁻ h, (ladderRenewalMeasure ν) (Ioi (b+t-h) ∩ Icc 0 b) ∂ν := by
  set U := ladderRenewalMeasure ν with hUdef
  set m := U.restrict (Icc (0 : ℝ) b) with hmdef
  have hS : MeasurableSet {p : ℝ × ℝ | b+t-p.1 < p.2} :=
    measurableSet_lt (measurable_const.sub measurable_fst) measurable_snd
  have h1 : (m.prod ν) {p : ℝ × ℝ | b+t-p.1 < p.2} = renewalOvershootTail ν b t := by
    rw [Measure.prod_apply hS, renewalOvershootTail, hmdef]
    refine lintegral_congr fun s => ?_
    congr 1
  have h2 : (m.prod ν) {p : ℝ × ℝ | b+t-p.1 < p.2} =
      ∫⁻ h, U (Ioi (b+t-h) ∩ Icc 0 b) ∂ν := by
    rw [Measure.prod_apply_symm hS]
    refine lintegral_congr fun h => ?_
    have hpre : (fun s : ℝ => (s, h)) ⁻¹' {p : ℝ × ℝ | b+t-p.1 < p.2} = Ioi (b+t-h) := by
      ext s
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_Ioi]
      constructor <;> intro hh <;> linarith
    rw [hmdef, hpre, Measure.restrict_apply measurableSet_Ioi]
  rw [← h1, h2]

/-- The equilibrium overshoot numerator as an integral over the ladder height. -/
theorem lintegral_tail_eq_lintegral_sub (ν : Measure ℝ) [SFinite ν] (t : ℝ) :
    (∫⁻ o in Ioi t, ν (Ioi o)) = ∫⁻ h, ENNReal.ofReal (h-t) ∂ν := by
  have hS : MeasurableSet {p : ℝ × ℝ | p.1 < p.2} := measurableSet_lt measurable_fst measurable_snd
  have h1 : ((volume.restrict (Ioi t)).prod ν) {p : ℝ × ℝ | p.1 < p.2} =
      ∫⁻ o in Ioi t, ν (Ioi o) := by
    rw [Measure.prod_apply hS]
    refine lintegral_congr fun o => ?_
    congr 1
  have h2 : ((volume.restrict (Ioi t)).prod ν) {p : ℝ × ℝ | p.1 < p.2} =
      ∫⁻ h, ENNReal.ofReal (h-t) ∂ν := by
    rw [Measure.prod_apply_symm hS]
    refine lintegral_congr fun h => ?_
    have hpre : (fun o : ℝ => (o, h)) ⁻¹' {p : ℝ × ℝ | p.1 < p.2} = Iio h := by
      ext o
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_Iio]
    rw [hpre, Measure.restrict_apply measurableSet_Iio]
    have hset : Iio h ∩ Ioi t = Ioo t h := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ioi, Set.mem_Ioo]
      exact ⟨fun hx => ⟨hx.2, hx.1⟩, fun hx => ⟨hx.2, hx.1⟩⟩
    rw [hset, Real.volume_Ioo]
  rw [← h1, h2]

theorem equilibriumOvershootTail_eq_lintegral (ν : Measure ℝ) [SFinite ν] (t : ℝ) :
    equilibriumOvershootTail ν t =
      (∫⁻ h, ENNReal.ofReal (h-t) ∂ν) / ladderMeanENN ν := by
  rw [equilibriumOvershootTail, lintegral_tail_eq_lintegral_sub]

/-! ### The renewal window as a difference of renewal functions -/

theorem window_of_neg {b x : ℝ} (hx : x < 0) :
    Ioi x ∩ Icc (0 : ℝ) b = Icc 0 b := by
  ext y
  simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Icc]
  exact ⟨fun h => h.2, fun h => ⟨lt_of_lt_of_le hx h.1, h⟩⟩

theorem window_of_mid {b x : ℝ} (hx0 : 0 ≤ x) :
    Ioi x ∩ Icc (0 : ℝ) b = Ioc x b := by
  ext y
  simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Icc, Set.mem_Ioc]
  constructor
  · rintro ⟨h1, -, h3⟩
    exact ⟨h1, h3⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, le_of_lt (lt_of_le_of_lt hx0 h1), h2⟩

theorem window_of_ge {b x : ℝ} (hx : b ≤ x) :
    Ioi x ∩ Icc (0 : ℝ) b = (∅ : Set ℝ) := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro y hy
  have h1 : x < y := hy.1
  have h2 : y ≤ b := hy.2.2
  linarith

theorem ladderRenewalMeasure_Ioc_toReal (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hfin : ∀ u : ℝ, ladderRenewalMeasure ν (Icc 0 u) ≠ ⊤) {x b : ℝ}
    (hx0 : 0 ≤ x) (hxb : x ≤ b) :
    ((ladderRenewalMeasure ν) (Ioc x b)).toReal =
      ladderRenewalFunction ν b - ladderRenewalFunction ν x := by
  set U := ladderRenewalMeasure ν with hUdef
  have hsplit : Icc (0 : ℝ) b = Icc 0 x ∪ Ioc x b := by
    ext y
    simp only [Set.mem_Icc, Set.mem_union, Set.mem_Ioc]
    constructor
    · rintro ⟨h1, h2⟩
      rcases le_or_gt y x with h | h
      · exact Or.inl ⟨h1, h⟩
      · exact Or.inr ⟨h, h2⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨h1, le_trans h2 hxb⟩
      · exact ⟨le_trans hx0 (le_of_lt h1), h2⟩
  have hdisj : Disjoint (Icc (0 : ℝ) x) (Ioc x b) := by
    rw [Set.disjoint_left]
    intro y hy hy'
    exact absurd hy'.1 (not_lt.mpr hy.2)
  have hadd : U (Icc 0 b) = U (Icc 0 x) + U (Ioc x b) := by
    rw [hsplit, measure_union hdisj measurableSet_Ioc]
  have hfinb : U (Icc 0 b) ≠ ⊤ := hfin b
  have hfinx : U (Icc 0 x) ≠ ⊤ := hfin x
  have hfinIoc : U (Ioc x b) ≠ ⊤ := by
    intro h
    rw [h, add_top] at hadd
    exact hfinb hadd
  rw [ladderRenewalFunction, ladderRenewalFunction, ← hUdef]
  have := congrArg ENNReal.toReal hadd
  rw [ENNReal.toReal_add hfinx hfinIoc] at this
  linarith

/-- The residual-life window in terms of the renewal function. -/
theorem renewalWindow_toReal (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hfin : ∀ u : ℝ, ladderRenewalMeasure ν (Icc 0 u) ≠ ⊤) {b t h : ℝ} :
    ((ladderRenewalMeasure ν) (Ioi (b+t-h) ∩ Icc 0 b)).toReal =
      if h ≤ t then 0
      else if h-t ≤ b then
        ladderRenewalFunction ν b - ladderRenewalFunction ν (b-(h-t))
      else ladderRenewalFunction ν b := by
  by_cases h1 : h ≤ t
  · rw [if_pos h1, window_of_ge (by linarith), measure_empty, ENNReal.toReal_zero]
  · rw [if_neg h1]
    by_cases h2 : h-t ≤ b
    · rw [if_pos h2, show b+t-h = b-(h-t) by ring,
        window_of_mid (b := b) (show (0 : ℝ) ≤ b-(h-t) by linarith),
        ladderRenewalMeasure_Ioc_toReal ν hfin (by linarith) (by linarith [not_le.mp h1])]
    · rw [if_neg h2, window_of_neg (by linarith [not_le.mp h2]), ladderRenewalFunction]

/-! ### Pointwise comparison with the limiting linear value -/

/-- Under the uniform renewal expansion the renewal window differs from its
limiting linear value by the exponential remainder, except on the far tail of
the ladder height where both terms are bounded separately. -/
theorem renewalWindow_sub_abs_le {L : ℝ → Measure ℝ} {S : Set ℝ} {C c : ℝ}
    (hexp : UniformLadderRenewalExpansion L S C c) {a : ℝ} (ha : a ∈ S)
    [IsProbabilityMeasure (L a)]
    (hfin : ∀ u : ℝ, ladderRenewalMeasure (L a) (Icc 0 u) ≠ ⊤)
    {b t h : ℝ} (hb : 0 ≤ b) :
    |((ladderRenewalMeasure (L a)) (Ioi (b+t-h) ∩ Icc 0 b)).toReal -
        max (h-t) 0 / ladderMean (L a)| ≤
      (if h-t ≤ b then C*Real.exp (-c*b) + C*Real.exp (-c*(b-max (h-t) 0))
        else (b+(h-t))/ladderMean (L a) + |ladderRenewalConstant (L a)| + C) := by
  have hexp' := hexp
  obtain ⟨hc, hC, hD⟩ := hexp'
  have hwin := renewalWindow_toReal (L a) hfin (b := b) (t := t) (h := h)
  have hmu : 0 ≤ ladderMean (L a) := ENNReal.toReal_nonneg
  by_cases h1 : h ≤ t
  · rw [hwin, if_pos h1, if_pos (by linarith : h-t ≤ b),
      max_eq_right (by linarith : h-t ≤ 0)]
    simp only [zero_div, sub_zero, abs_zero]
    have h2 : 0 ≤ C*Real.exp (-c*b) := by positivity
    have h3 : 0 ≤ C*Real.exp (-c*(b-0)) := by positivity
    linarith
  · have hu : 0 < h-t := by linarith [not_le.mp h1]
    rw [max_eq_left hu.le]
    have hDb := hD a ha b hb
    by_cases h2 : h-t ≤ b
    · rw [hwin, if_neg h1, if_pos h2, if_pos h2]
      have hDbu := hD a ha (b-(h-t)) (by linarith)
      have hsplit : ladderRenewalFunction (L a) b -
          ladderRenewalFunction (L a) (b-(h-t)) - (h-t)/ladderMean (L a) =
          (ladderRenewalFunction (L a) b -
            (b/ladderMean (L a) + ladderRenewalConstant (L a))) -
          (ladderRenewalFunction (L a) (b-(h-t)) -
            ((b-(h-t))/ladderMean (L a) + ladderRenewalConstant (L a))) := by
        ring
      rw [hsplit]
      calc |_| ≤ |ladderRenewalFunction (L a) b -
              (b/ladderMean (L a) + ladderRenewalConstant (L a))| +
            |ladderRenewalFunction (L a) (b-(h-t)) -
              ((b-(h-t))/ladderMean (L a) + ladderRenewalConstant (L a))| := abs_sub _ _
        _ ≤ C*Real.exp (-c*b) + C*Real.exp (-c*(b-(h-t))) := add_le_add hDb hDbu
    · rw [hwin, if_neg h1, if_neg h2, if_neg h2]
      have hbmu : 0 ≤ b/ladderMean (L a) := div_nonneg hb hmu
      have humu : 0 ≤ (h-t)/ladderMean (L a) := div_nonneg hu.le hmu
      have habs := abs_le.mp hDb
      have hCe : C*Real.exp (-c*b) ≤ C := by
        have hexp1 : Real.exp (-c*b) ≤ 1 := by
          refine Real.exp_le_one_iff.mpr ?_
          nlinarith
        nlinarith [Real.exp_pos (-c*b)]
      have hK1 : ladderRenewalConstant (L a) ≤ |ladderRenewalConstant (L a)| := le_abs_self _
      have hK2 : -|ladderRenewalConstant (L a)| ≤ ladderRenewalConstant (L a) := neg_abs_le _
      have hFb : |ladderRenewalFunction (L a) b| ≤
          b/ladderMean (L a) + |ladderRenewalConstant (L a)| + C := by
        rw [abs_le]
        constructor
        · nlinarith [habs.1]
        · nlinarith [habs.2]
      calc |ladderRenewalFunction (L a) b - (h-t)/ladderMean (L a)|
          ≤ |ladderRenewalFunction (L a) b| + |(h-t)/ladderMean (L a)| := abs_sub _ _
        _ = |ladderRenewalFunction (L a) b| + (h-t)/ladderMean (L a) := by
            rw [abs_of_nonneg humu]
        _ ≤ (b/ladderMean (L a) + |ladderRenewalConstant (L a)| + C) +
              (h-t)/ladderMean (L a) := by linarith
        _ = (b+(h-t))/ladderMean (L a) + |ladderRenewalConstant (L a)| + C := by
            rw [add_div]
            ring

/-! ### Fixed-height consequence of the BG window estimate -/

/-- At every fixed ladder height, the renewal window converges to its linear
limit as the passage level tends to infinity.  This is the pointwise part of
the residual-life argument that is used after the Blanchet--Glynn expansion;
the tail integration and uniformity in the height remain separate estimates.
-/
theorem renewalWindow_toReal_tendsto {L : ℝ → Measure ℝ} {S : Set ℝ} {C c : ℝ}
    (hexp : UniformLadderRenewalExpansion L S C c) {a : ℝ} (ha : a ∈ S)
    [IsProbabilityMeasure (L a)]
    (hfin : ∀ u : ℝ, ladderRenewalMeasure (L a) (Icc 0 u) ≠ ⊤)
    {t h : ℝ} :
    Tendsto (fun b : ℝ =>
      ((ladderRenewalMeasure (L a)) (Ioi (b+t-h) ∩ Icc 0 b)).toReal)
      atTop (𝓝 (max (h-t) 0 / ladderMean (L a))) := by
  obtain ⟨hc, hC, hD⟩ := hexp
  let k : ℝ := max (h-t) 0
  have hk : 0 ≤ k := by
    exact le_max_right _ _
  have hcb : Tendsto (fun b : ℝ => C * Real.exp (-c*b)) atTop (𝓝 0) := by
    have hmul : Tendsto (fun b : ℝ => c*b) atTop atTop := by
      simpa only [id] using (tendsto_id.const_mul_atTop hc)
    have hneg : Tendsto (fun b : ℝ => -c*b) atTop atBot := by
      refine Filter.Tendsto.congr (fun b => ?_) (tendsto_neg_atTop_atBot.comp hmul)
      simp only [Function.comp_def]
      ring
    have he : Tendsto (fun b : ℝ => Real.exp (-c*b)) atTop (𝓝 0) := by
      simpa only [Function.comp_def] using Real.tendsto_exp_atBot.comp hneg
    simpa only [mul_zero] using (tendsto_const_nhds.mul he)
  have hshift_at : Tendsto (fun b : ℝ => b-k) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro z
    filter_upwards [eventually_ge_atTop (z+k)] with b hb
    linarith
  have hshift_mul : Tendsto (fun b : ℝ => c*(b-k)) atTop atTop :=
    hshift_at.const_mul_atTop hc
  have hshift_exp : Tendsto (fun b : ℝ => Real.exp (-c*(b-k))) atTop (𝓝 0) := by
    have hneg : Tendsto (fun b : ℝ => -c*(b-k)) atTop atBot := by
      refine Filter.Tendsto.congr (fun b => ?_) (tendsto_neg_atTop_atBot.comp hshift_mul)
      simp only [Function.comp_def]
      ring
    simpa only [Function.comp_def] using Real.tendsto_exp_atBot.comp hneg
  have hcb' : Tendsto (fun b : ℝ => C * Real.exp (-c*(b-k))) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_const_nhds.mul hshift_exp)
  have herr : Tendsto (fun b : ℝ =>
      C * Real.exp (-c*b) + C * Real.exp (-c*(b-k))) atTop (𝓝 0) := by
    simpa only [add_zero] using hcb.add hcb'
  have habs : Tendsto (fun b : ℝ =>
      |((ladderRenewalMeasure (L a)) (Ioi (b+t-h) ∩ Icc 0 b)).toReal -
        max (h-t) 0 / ladderMean (L a)|) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    · exact tendsto_const_nhds
    · exact herr
    · filter_upwards with b
      exact abs_nonneg _
    · filter_upwards [eventually_ge_atTop (max (0 : ℝ) (h-t))] with b hb
      have hb0 : 0 ≤ b := le_trans (le_max_left _ _) hb
      have hbranch : h-t ≤ b := le_trans (le_max_right _ _) hb
      have hwin := renewalWindow_sub_abs_le ⟨hc, hC, hD⟩ ha hfin (b := b) (t := t) (h := h) hb0
      rw [show max (h-t) 0 = k by rfl] at hwin ⊢
      simpa only [if_pos hbranch] using hwin
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa only [Real.norm_eq_abs] using habs

/-! ### The window as a bounded measurable function of the ladder height -/

/-- The renewal window, as a real-valued function of the ladder height. -/
def renewalWindowReal (ν : Measure ℝ) (b t h : ℝ) : ℝ :=
  ((ladderRenewalMeasure ν) (Ioi (b+t-h) ∩ Icc 0 b)).toReal

theorem ladderRenewalFunction_monotone (ν : Measure ℝ)
    (hfin : ∀ u : ℝ, ladderRenewalMeasure ν (Icc 0 u) ≠ ⊤) :
    Monotone (ladderRenewalFunction ν) := by
  intro u v huv
  refine ENNReal.toReal_mono (hfin v) (measure_mono ?_)
  exact Icc_subset_Icc le_rfl huv

theorem ladderRenewalFunction_measurable (ν : Measure ℝ)
    (hfin : ∀ u : ℝ, ladderRenewalMeasure ν (Icc 0 u) ≠ ⊤) :
    Measurable (ladderRenewalFunction ν) :=
  (ladderRenewalFunction_monotone ν hfin).measurable

theorem renewalWindowReal_nonneg (ν : Measure ℝ) (b t h : ℝ) :
    0 ≤ renewalWindowReal ν b t h := ENNReal.toReal_nonneg

theorem renewalWindowReal_le (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hfin : ∀ u : ℝ, ladderRenewalMeasure ν (Icc 0 u) ≠ ⊤) {b t h : ℝ} :
    renewalWindowReal ν b t h ≤ ladderRenewalFunction ν b := by
  refine ENNReal.toReal_mono (hfin b) (measure_mono ?_)
  exact Set.inter_subset_right

theorem renewalWindowReal_measurable (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hfin : ∀ u : ℝ, ladderRenewalMeasure ν (Icc 0 u) ≠ ⊤) (b t : ℝ) :
    Measurable (renewalWindowReal ν b t) := by
  have heq : renewalWindowReal ν b t = fun h : ℝ =>
      if h ≤ t then 0
      else if h-t ≤ b then
        ladderRenewalFunction ν b - ladderRenewalFunction ν (b-(h-t))
      else ladderRenewalFunction ν b := by
    funext h
    exact renewalWindow_toReal ν hfin
  rw [heq]
  refine Measurable.ite (measurableSet_le measurable_id measurable_const) measurable_const ?_
  refine Measurable.ite
    (measurableSet_le (measurable_id.sub_const t) measurable_const) ?_ measurable_const
  exact measurable_const.sub
    ((ladderRenewalFunction_measurable ν hfin).comp (measurable_const.sub
      (measurable_id.sub_const t)))

/-! ### The two tails as Bochner integrals -/

theorem renewalOvershootTail_toReal (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hfin : ∀ u : ℝ, ladderRenewalMeasure ν (Icc 0 u) ≠ ⊤) (b t : ℝ) :
    (renewalOvershootTail ν b t).toReal = ∫ h, renewalWindowReal ν b t h ∂ν := by
  have hnn : 0 ≤ᵐ[ν] renewalWindowReal ν b t :=
    Filter.Eventually.of_forall (renewalWindowReal_nonneg ν b t)
  rw [integral_eq_lintegral_of_nonneg_ae hnn
    (renewalWindowReal_measurable ν hfin b t).aestronglyMeasurable]
  congr 1
  rw [renewalOvershootTail_eq_window]
  refine lintegral_congr fun h => ?_
  rw [renewalWindowReal, ENNReal.ofReal_toReal]
  intro hcon
  exact (hfin b) (top_unique (hcon ▸ measure_mono Set.inter_subset_right))

theorem equilibriumOvershootTail_toReal (ν : Measure ℝ) [IsProbabilityMeasure ν] (t : ℝ) :
    (equilibriumOvershootTail ν t).toReal =
      (∫ h, max (h-t) 0 ∂ν) / ladderMean ν := by
  have hnn : 0 ≤ᵐ[ν] fun h : ℝ => max (h-t) 0 :=
    Filter.Eventually.of_forall fun h => le_max_right _ _
  have hmeas : Measurable fun h : ℝ => max (h-t) 0 :=
    (measurable_id.sub_const t).max measurable_const
  rw [equilibriumOvershootTail_eq_lintegral, ENNReal.toReal_div, ladderMean]
  congr 1
  rw [integral_eq_lintegral_of_nonneg_ae hnn hmeas.aestronglyMeasurable]
  congr 1
  refine lintegral_congr fun h => ?_
  rcases le_or_gt h t with hh | hh
  · rw [max_eq_right (by linarith), ENNReal.ofReal_zero,
      ENNReal.ofReal_eq_zero.mpr (by linarith)]
  · rw [max_eq_left (by linarith)]

/-! ### Integrating the pointwise comparison -/

/-- A single dominating function for the residual-life comparison: an
exponentially small constant plus a far-tail term. -/
theorem renewalWindowReal_sub_le_dominant {L : ℝ → Measure ℝ} {S : Set ℝ} {C c : ℝ}
    (hexp : UniformLadderRenewalExpansion L S C c) {a : ℝ} (ha : a ∈ S)
    [IsProbabilityMeasure (L a)]
    (hfin : ∀ u : ℝ, ladderRenewalMeasure (L a) (Icc 0 u) ≠ ⊤)
    {b t h : ℝ} (hb : 0 ≤ b) :
    |renewalWindowReal (L a) b t h - max (h-t) 0 / ladderMean (L a)| ≤
      2*C*Real.exp (-c*(b/2)) +
        (if t+b/2 < h then
          3*C + |ladderRenewalConstant (L a)| + 2*(h-t)/ladderMean (L a) else 0) := by
  unfold renewalWindowReal
  have hc : 0 < c := hexp.1
  have hC : 0 ≤ C := hexp.2.1
  have hmu : 0 ≤ ladderMean (L a) := ENNReal.toReal_nonneg
  have hbase := renewalWindow_sub_abs_le hexp ha hfin (b := b) (t := t) (h := h) hb
  have hK : 0 ≤ |ladderRenewalConstant (L a)| := abs_nonneg _
  have hexphalf : 0 < Real.exp (-c*(b/2)) := Real.exp_pos _
  by_cases hcase : t+b/2 < h
  · rw [if_pos hcase]
    have hut : 0 < h-t := by linarith
    have humu : 0 ≤ 2*(h-t)/ladderMean (L a) := by positivity
    by_cases hbr : h-t ≤ b
    · rw [if_pos hbr] at hbase
      have hmax : max (h-t) 0 = h-t := max_eq_left hut.le
      rw [hmax] at hbase ⊢
      have he1 : Real.exp (-c*b) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
      have he2 : Real.exp (-c*(b-(h-t))) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by nlinarith)
      have hCe : C*Real.exp (-c*b) + C*Real.exp (-c*(b-(h-t))) ≤ 2*C := by nlinarith
      have hpos : 0 ≤ 2*C*Real.exp (-c*(b/2)) := by positivity
      linarith
    · rw [if_neg hbr] at hbase
      have hbig : b < h-t := lt_of_not_ge hbr
      have hmax : max (h-t) 0 = h-t := max_eq_left hut.le
      rw [hmax] at hbase ⊢
      have hstep : (b+(h-t))/ladderMean (L a) ≤ 2*(h-t)/ladderMean (L a) := by
        apply div_le_div_of_nonneg_right (by linarith) hmu
      have hpos : 0 ≤ 2*C*Real.exp (-c*(b/2)) := by positivity
      linarith
  · rw [if_neg hcase, add_zero]
    have hle : h-t ≤ b/2 := by linarith [not_lt.mp hcase]
    have hmaxle : max (h-t) 0 ≤ b/2 := max_le hle (by linarith)
    have hmaxnn : 0 ≤ max (h-t) 0 := le_max_right _ _
    have hbr : h-t ≤ b := by linarith
    rw [if_pos hbr] at hbase
    have he1 : Real.exp (-c*b) ≤ Real.exp (-c*(b/2)) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have he2 : Real.exp (-c*(b-max (h-t) 0)) ≤ Real.exp (-c*(b/2)) :=
      Real.exp_le_exp.mpr (by nlinarith)
    nlinarith

/-- The residual-life tail converges to the equilibrium overshoot tail, with an
explicit bound: an exponentially small term plus two far-tail terms of the
ladder height. -/
theorem renewalOvershootTail_sub_equilibrium_le {L : ℝ → Measure ℝ} {S : Set ℝ} {C c : ℝ}
    (hexp : UniformLadderRenewalExpansion L S C c) {a : ℝ} (ha : a ∈ S)
    [IsProbabilityMeasure (L a)]
    (hfin : ∀ u : ℝ, ladderRenewalMeasure (L a) (Icc 0 u) ≠ ⊤)
    {t : ℝ} (hint : Integrable (fun h => max (h-t) 0) (L a))
    {b : ℝ} (hb : 0 ≤ b) :
    |(renewalOvershootTail (L a) b t).toReal - (equilibriumOvershootTail (L a) t).toReal| ≤
      2*C*Real.exp (-c*(b/2)) +
        (3*C + |ladderRenewalConstant (L a)|) * (L a).real (Ioi (t+b/2)) +
        (2/ladderMean (L a)) * ∫ h in Ioi (t+b/2), (h-t) ∂(L a) := by
  have hC : 0 ≤ C := hexp.2.1
  have hmu : 0 ≤ ladderMean (L a) := ENNReal.toReal_nonneg
  set ν := L a with hνdef
  set μ0 : ℝ := ladderMean (L a) with hμdef
  set K0 : ℝ := 3*C + |ladderRenewalConstant (L a)| with hK0def
  set W : ℝ → ℝ := renewalWindowReal ν b t with hWdef
  set g : ℝ → ℝ := fun h => max (h-t) 0 / μ0 with hgdef
  set far : ℝ → ℝ := (Ioi (t+b/2)).indicator (fun h => K0 + 2*(h-t)/μ0) with hfardef
  -- integrability
  have hWmeas : Measurable W := renewalWindowReal_measurable ν hfin b t
  have hWint : Integrable W ν := by
    refine Integrable.mono' (integrable_const (ladderRenewalFunction ν b))
      hWmeas.aestronglyMeasurable ?_
    filter_upwards with h
    rw [Real.norm_eq_abs, abs_of_nonneg (renewalWindowReal_nonneg ν b t h)]
    exact renewalWindowReal_le ν hfin
  have hgint : Integrable g ν := hint.div_const μ0
  have hmaxOn : IntegrableOn (fun h => max (h-t) 0) (Ioi (t+b/2)) ν := hint.integrableOn
  have hsubOn : IntegrableOn (fun h => h-t) (Ioi (t+b/2)) ν := by
    refine IntegrableOn.congr_fun hmaxOn (fun h hh => ?_) measurableSet_Ioi
    have hh' : t+b/2 < h := hh
    exact max_eq_left (by linarith)
  have hscaleOn : IntegrableOn (fun h => 2*(h-t)/μ0) (Ioi (t+b/2)) ν := by
    refine IntegrableOn.congr_fun (hsubOn.const_mul (2/μ0)) (fun h _ => ?_) measurableSet_Ioi
    field_simp
  have hfarOn : IntegrableOn (fun h => K0 + 2*(h-t)/μ0) (Ioi (t+b/2)) ν :=
    (integrable_const K0).add hscaleOn
  have hfarint : Integrable far ν := hfarOn.integrable_indicator measurableSet_Ioi
  have hdomint : Integrable (fun h => 2*C*Real.exp (-c*(b/2)) + far h) ν :=
    (integrable_const _).add hfarint
  -- pointwise domination
  have hpoint : ∀ h, |W h - g h| ≤ 2*C*Real.exp (-c*(b/2)) + far h := by
    intro h
    have hb0 := renewalWindowReal_sub_le_dominant hexp ha hfin (b := b) (t := t) (h := h) hb
    by_cases hcase : t+b/2 < h
    · rw [hfardef, Set.indicator_of_mem (show h ∈ Ioi (t+b/2) from hcase)]
      rw [if_pos hcase] at hb0
      rw [hK0def]
      calc |W h - g h| ≤ 2*C*Real.exp (-c*(b/2)) +
            (3*C + |ladderRenewalConstant (L a)| + 2*(h-t)/μ0) := hb0
        _ = 2*C*Real.exp (-c*(b/2)) + (3*C + |ladderRenewalConstant (L a)| + 2*(h-t)/μ0) := rfl
    · rw [hfardef, Set.indicator_of_notMem (show h ∉ Ioi (t+b/2) from hcase), add_zero]
      rw [if_neg hcase, add_zero] at hb0
      exact hb0
  -- integrate
  have hsub : (renewalOvershootTail ν b t).toReal - (equilibriumOvershootTail ν t).toReal =
      ∫ h, (W h - g h) ∂ν := by
    rw [renewalOvershootTail_toReal ν hfin b t, equilibriumOvershootTail_toReal ν t,
      integral_sub hWint hgint, hgdef, integral_div]
  rw [hsub]
  calc |∫ h, (W h - g h) ∂ν| ≤ ∫ h, |W h - g h| ∂ν :=
        abs_integral_le_integral_abs
    _ ≤ ∫ h, (2*C*Real.exp (-c*(b/2)) + far h) ∂ν :=
        integral_mono ((hWint.sub hgint).abs) hdomint hpoint
    _ = 2*C*Real.exp (-c*(b/2)) + ∫ h, far h ∂ν := by
        rw [integral_add (integrable_const _) hfarint, integral_const]
        simp
    _ = 2*C*Real.exp (-c*(b/2)) +
          (K0 * ν.real (Ioi (t+b/2)) + (2/μ0) * ∫ h in Ioi (t+b/2), (h-t) ∂ν) := by
        congr 1
        rw [hfardef, integral_indicator measurableSet_Ioi,
          integral_add (integrable_const K0) hscaleOn, integral_const]
        congr 1
        · rw [smul_eq_mul, mul_comm]
          congr 1
          rw [Measure.real, Measure.real, Measure.restrict_apply_univ]
        · rw [← integral_const_mul]
          refine setIntegral_congr_fun measurableSet_Ioi (fun h _ => ?_)
          field_simp
    _ = 2*C*Real.exp (-c*(b/2)) + K0 * ν.real (Ioi (t+b/2)) +
          (2/μ0) * ∫ h in Ioi (t+b/2), (h-t) ∂ν := by ring

end SwingRepair
