import PLAStochastic.Swing.Ladder.Renewal.PositionUniformWindow
import PLAStochastic.Swing.Ladder.Renewal.ResidualLifeUniform
import PLAStochastic.Swing.Ladder.Renewal.WalkOvershootLimit

/-!
# The stationary renewal identity

Blackwell's theorem has two halves: the window mass of the renewal measure is
asymptotically shift invariant, and the value of the limit is `1/μ`.  This file
proves the second half **exactly**, with no asymptotics at all.

The input is the a.s.-crossing identity `renewalOvershootTail ν c 0 = 1`: the
renewal sequence exceeds every level.  Two Tonelli exchanges and one Lebesgue
translation then give

`∫ U((b-x-y, b-y]) dQ(y) = x / μ`,

where `Q` is the equilibrium overshoot law.  Equivalently `Q * U` has constant
Lebesgue density `1/μ` on `[0,∞)`: the stationary renewal process has Lebesgue
intensity.  Consequently the Blackwell error has the exact representation

`U((b-x,b]) - x/μ = ∫ [U((b-x,b]) - U((b-x-y, b-y])] dQ(y)`,

so the whole remaining content of `UniformRenewalWindowLimit` is asymptotic
shift invariance of the window mass; nothing about the value of the limit is
left open.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical MeasureTheory
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

/-! ### The renewal sequence exceeds every level -/

/-- The overshoot of the actual walk above a level is almost surely strictly
positive, so its law charges no nonpositive set. -/
theorem gaussianWalkOvershootLaw_Iic_zero [IsProbabilityMeasure μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {M a : ℝ} (ha : 0 < a) (haM : a ≤ M)
    {b : ℝ} (hb : 0 ≤ b) :
    gaussianWalkOvershootLaw X μ a b (Iic 0) = 0 := by
  rw [gaussianWalkOvershootLaw,
    Measure.map_apply (gaussianWalkOvershoot_measurable hX a b) measurableSet_Iic,
    measure_eq_zero_iff_ae_notMem]
  filter_upwards [gaussianWalkOvershoot_ae_eq_ladder hX hi hG ha haM hb,
    gaussianLadderSum_exists_gt_ae hX hi hG ha haM] with ω hω hex
  have hpos : 0 < gaussianLadderOvershoot X a b ω := by
    have hb' := hex b
    rw [gaussianLadderOvershoot, gaussianLadderPassage, dif_pos hb']
    have := Nat.find_spec hb'
    linarith
  simp only [Set.mem_preimage, mem_Iic, not_le]
  rw [hω]
  exact hpos

/-- **The a.s.-crossing identity.**  `∫_{[0,c]} ν(Ioi (c-s)) U(ds) = 1`: the
ladder sequence exceeds the level `c` exactly once, so the renewal-theoretic
first-passage decomposition has total mass one.  This is the identity that
pins the Blackwell constant. -/
theorem renewalOvershootTail_zero_eq_one [IsProbabilityMeasure μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {M a : ℝ} (ha : 0 < a) (haM : a ≤ M)
    {b : ℝ} (hb : 0 ≤ b) :
    renewalOvershootTail (gaussianAscendingLadderLaw X μ a) b 0 = 1 := by
  have hprob := gaussianWalkOvershootLaw_isProbabilityMeasure (μ := μ) hX a b
  have hIoi := gaussianWalkOvershootLaw_Ioi hX hi hG ha haM hb (le_refl (0 : ℝ))
  have hcompl : (Ioi (0 : ℝ)) = (Iic (0 : ℝ))ᶜ := by
    ext y
    simp
  rw [← hIoi, hcompl, measure_compl measurableSet_Iic (measure_ne_top _ _),
    gaussianWalkOvershootLaw_Iic_zero hX hi hG ha haM hb, measure_univ, tsub_zero]


/-! ### The stationary renewal identity -/

/--
**`Q * U` has constant Lebesgue density `1/μ`.**  Stated in the window form
actually used: the `Q`-average of the shifted window masses of the renewal
measure is exactly `x/μ`.  Only the a.s.-crossing identity enters; there is no
asymptotics and no renewal expansion.
-/
theorem lintegral_equilibrium_window_eq (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hUneg : ladderRenewalMeasure ν (Iio 0) = 0)
    (hcross : ∀ c : ℝ, 0 ≤ c → renewalOvershootTail ν c 0 = 1)
    (hnn : 0 ≤ᵐ[ν] fun z : ℝ => z)
    (hm0 : ladderMeanENN ν ≠ 0) (hmtop : ladderMeanENN ν ≠ ⊤)
    {b x : ℝ} (_hx : 0 ≤ x) (hxb : x ≤ b) :
    (∫⁻ y, ladderRenewalMeasure ν (Ioc (b - x - y) (b - y))
        ∂(equilibriumOvershootLaw ν)) = ENNReal.ofReal x / ladderMeanENN ν := by
  set U := ladderRenewalMeasure ν with hUdef
  set Q := equilibriumOvershootLaw ν with hQdef
  set m := ladderMeanENN ν with hmdef
  have hQprob : IsProbabilityMeasure Q :=
    equilibriumOvershootLaw_isProbabilityMeasure ν hnn hm0 hmtop
  have hminv : m⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hm0
  have hbx : 0 ≤ b - x := by linarith
  have hS : MeasurableSet {p : ℝ × ℝ | p.1 + p.2 ∈ Ioc (b - x) b} :=
    measurableSet_Ioc.preimage (measurable_fst.add measurable_snd)
  -- (1) the left side is a product-measure evaluation
  have hA : (Q.prod U) {p : ℝ × ℝ | p.1 + p.2 ∈ Ioc (b - x) b} =
      ∫⁻ y, U (Ioc (b - x - y) (b - y)) ∂Q := by
    rw [Measure.prod_apply hS]
    refine lintegral_congr fun y => ?_
    congr 1
    ext s
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_Ioc]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith, by linarith⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith, by linarith⟩
  -- (2) the same evaluation with the roles exchanged
  have hB : (Q.prod U) {p : ℝ × ℝ | p.1 + p.2 ∈ Ioc (b - x) b} =
      ∫⁻ s, Q (Ioc (b - x - s) (b - s)) ∂U := by
    rw [Measure.prod_apply_symm hS]
    refine lintegral_congr fun s => ?_
    congr 1
    ext y
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_Ioc]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith, by linarith⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith, by linarith⟩
  -- (3) expand `Q` and translate the inner Lebesgue integral
  have hmeasTail : Measurable (fun o : ℝ => ν (Ioi o)) := measurable_ladderTail ν
  have hQwin : ∀ s : ℝ, Q (Ioc (b - x - s) (b - s)) =
      m⁻¹ * ∫⁻ z in (Ioc (b - x) b) ∩ Ici s, ν (Ioi (z - s)) := by
    intro s
    rw [hQdef, equilibriumOvershootLaw_apply ν measurableSet_Ioc]
    have hpull : (∫⁻ y in (Ioc (b - x - s) (b - s)) ∩ Ici (0 : ℝ), ν (Ioi y) / m) =
        m⁻¹ * ∫⁻ y in (Ioc (b - x - s) (b - s)) ∩ Ici (0 : ℝ), ν (Ioi y) := by
      simp_rw [ENNReal.div_eq_inv_mul]
      exact lintegral_const_mul' _ _ hminv
    rw [hpull]
    congr 1
    have hmp : MeasurePreserving (fun z : ℝ => z - s) volume volume :=
      measurePreserving_sub_right volume s
    have hset : MeasurableSet ((Ioc (b - x - s) (b - s)) ∩ Ici (0 : ℝ)) :=
      measurableSet_Ioc.inter measurableSet_Ici
    have hchange := hmp.setLIntegral_comp_preimage hset hmeasTail
    have hpre : (fun z : ℝ => z - s) ⁻¹'
        ((Ioc (b - x - s) (b - s)) ∩ Ici (0 : ℝ)) = (Ioc (b - x) b) ∩ Ici s := by
      ext z
      simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ici]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨⟨by linarith, by linarith⟩, by linarith⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨⟨by linarith, by linarith⟩, by linarith⟩
    rw [hpre] at hchange
    exact hchange.symm
  -- (4) swap the two integrals and use the crossing identity
  set G : ℝ × ℝ → ℝ≥0∞ := fun p =>
    if p.2 ∈ Ioc (b - x) b ∧ p.1 ≤ p.2 then ν (Ioi (p.2 - p.1)) else 0 with hGdef
  have hGmeas : Measurable G := by
    have hset : MeasurableSet {p : ℝ × ℝ | p.2 ∈ Ioc (b - x) b ∧ p.1 ≤ p.2} := by
      exact (measurableSet_Ioc.preimage measurable_snd).inter
        (measurableSet_le measurable_fst measurable_snd)
    have hfun : Measurable (fun p : ℝ × ℝ => ν (Ioi (p.2 - p.1))) :=
      hmeasTail.comp (measurable_snd.sub measurable_fst)
    exact hfun.ite hset measurable_const
  have hinner : ∀ s : ℝ, (∫⁻ z in (Ioc (b - x) b) ∩ Ici s, ν (Ioi (z - s))) =
      ∫⁻ z, G (s, z) := by
    intro s
    rw [← lintegral_indicator ((measurableSet_Ioc).inter measurableSet_Ici)]
    refine lintegral_congr fun z => ?_
    by_cases hz : z ∈ (Ioc (b - x) b) ∩ Ici s
    · rw [Set.indicator_of_mem hz, hGdef]
      simp only []
      rw [if_pos ⟨hz.1, hz.2⟩]
    · rw [Set.indicator_of_notMem hz, hGdef]
      simp only []
      rw [if_neg (by
        intro hc
        exact hz ⟨hc.1, hc.2⟩)]
  have hswap : (∫⁻ s, (∫⁻ z, G (s, z)) ∂U) = ∫⁻ z, (∫⁻ s, G (s, z) ∂U) := by
    exact lintegral_lintegral_swap hGmeas.aemeasurable
  have hcol : ∀ z : ℝ, (∫⁻ s, G (s, z) ∂U) =
      Set.indicator (Ioc (b - x) b) (fun _ => (1 : ℝ≥0∞)) z := by
    intro z
    by_cases hz : z ∈ Ioc (b - x) b
    · rw [Set.indicator_of_mem hz]
      have hz0 : 0 ≤ z := le_trans hbx (le_of_lt hz.1)
      have hrewrite : (∫⁻ s, G (s, z) ∂U) = ∫⁻ s in Iic z, ν (Ioi (z - s)) ∂U := by
        rw [← lintegral_indicator (measurableSet_Iic (a := z))]
        refine lintegral_congr fun s => ?_
        by_cases hs : s ∈ Iic z
        · rw [Set.indicator_of_mem hs, hGdef]
          simp only []
          rw [if_pos ⟨hz, hs⟩]
        · rw [Set.indicator_of_notMem hs, hGdef]
          simp only []
          rw [if_neg (by
            intro hc
            exact hs hc.2)]
      have haeset : Iic z =ᵐ[U] Icc (0 : ℝ) z := by
        rw [ae_eq_set]
        constructor
        · have hsub : Iic z \ Icc (0 : ℝ) z ⊆ Iio 0 := by
            intro w hw
            obtain ⟨hw1, hw2⟩ := hw
            rcases le_or_gt 0 w with h | h
            · exact absurd ⟨h, hw1⟩ hw2
            · exact h
          exact measure_mono_null hsub hUneg
        · have hsub : Icc (0 : ℝ) z \ Iic z = (∅ : Set ℝ) := by
            rw [Set.eq_empty_iff_forall_notMem]
            intro w hw
            exact absurd hw.1.2 hw.2
          rw [hsub, measure_empty]
      rw [hrewrite, setLIntegral_congr haeset]
      have hval : (∫⁻ s in Icc (0 : ℝ) z, ν (Ioi (z - s)) ∂U) =
          renewalOvershootTail ν z 0 := by
        rw [renewalOvershootTail, hUdef]
        refine setLIntegral_congr_fun measurableSet_Icc (fun s _ => ?_)
        congr 2
        ring
      rw [hval]
      exact hcross z hz0
    · rw [Set.indicator_of_notMem hz]
      have hzero : ∀ s : ℝ, G (s, z) = 0 := by
        intro s
        rw [hGdef]
        simp only []
        rw [if_neg (by
          intro hc
          exact hz hc.1)]
      simp only [hzero, lintegral_zero]
  -- (5) assemble
  have hfinal : (∫⁻ y, U (Ioc (b - x - y) (b - y)) ∂Q) =
      m⁻¹ * ENNReal.ofReal x := by
    rw [← hA, hB]
    have hstep : (∫⁻ s, Q (Ioc (b - x - s) (b - s)) ∂U) =
        m⁻¹ * ∫⁻ s, (∫⁻ z, G (s, z)) ∂U := by
      rw [← lintegral_const_mul' _ _ hminv]
      refine lintegral_congr fun s => ?_
      rw [hQwin s, hinner s]
    rw [hstep, hswap]
    congr 1
    rw [lintegral_congr hcol, lintegral_indicator measurableSet_Ioc]
    rw [setLIntegral_one, Real.volume_Ioc]
    congr 1
    ring
  rw [hfinal, ENNReal.div_eq_inv_mul]


/-! ### Measurability of the shifted window mass -/

theorem measurable_ladderRenewal_window_shift (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (b x : ℝ) :
    Measurable (fun y : ℝ =>
      ladderRenewalMeasure ν (Ioc (b - x - y) (b - y))) := by
  have hS : MeasurableSet {p : ℝ × ℝ | p.1 + p.2 ∈ Ioc (b - x) b} :=
    measurableSet_Ioc.preimage (measurable_fst.add measurable_snd)
  have hbase := measurable_measure_prodMk_left
    (ν := ladderRenewalMeasure ν) hS
  have hEq : (fun y : ℝ => ladderRenewalMeasure ν (Ioc (b - x - y) (b - y))) =
      fun y : ℝ => ladderRenewalMeasure ν
        (Prod.mk y ⁻¹' {p : ℝ × ℝ | p.1 + p.2 ∈ Ioc (b - x) b}) := by
    funext y
    congr 1
    ext s
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_Ioc]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith, by linarith⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith, by linarith⟩
  rw [hEq]
  exact hbase

/-! ### The Gaussian instance -/

theorem lintegral_equilibrium_window_eq_gaussian [IsProbabilityMeasure μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {δ M a : ℝ} (hδ : 0 < δ) (hδa : δ ≤ a) (haM : a ≤ M)
    {b x : ℝ} (hx : 0 ≤ x) (hxb : x ≤ b) :
    (∫⁻ y, ladderRenewalMeasure (gaussianAscendingLadderLaw X μ a)
        (Ioc (b - x - y) (b - y))
      ∂(equilibriumOvershootLaw (gaussianAscendingLadderLaw X μ a))) =
      ENNReal.ofReal x / ladderMeanENN (gaussianAscendingLadderLaw X μ a) := by
  have ha : 0 < a := lt_of_lt_of_le hδ hδa
  have hprob := gaussianAscendingLadderLaw_isProbabilityMeasure hX hi a
  exact lintegral_equilibrium_window_eq _
    (ladderRenewalMeasure_Iio_zero hX hi hG ha)
    (fun c hc => renewalOvershootTail_zero_eq_one hX hi hG ha haM hc)
    (gaussianAscendingLadderLaw_ae_nonneg hX a)
    (gaussianAscendingLadderLaw_mean_ne_zero hX hG ha haM)
    (gaussianAscendingLadderLaw_mean_ne_top hX hi hG hδ hδa haM) hx hxb

/-- The real-valued form: the `Q`-average of the shifted window masses is
exactly `x/μ_a`.  Finiteness of every window mass comes from the
position-uniform window bound, so no integrability is assumed. -/
theorem integral_equilibrium_window_eq_gaussian [IsProbabilityMeasure μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {δ M a : ℝ} (hδ : 0 < δ) (hδa : δ ≤ a) (haM : a ≤ M)
    {b x : ℝ} (hx : 0 ≤ x) (hxb : x ≤ b) :
    (∫ y, (ladderRenewalMeasure (gaussianAscendingLadderLaw X μ a)
        (Ioc (b - x - y) (b - y))).toReal
      ∂(equilibriumOvershootLaw (gaussianAscendingLadderLaw X μ a))) =
      x / ladderMean (gaussianAscendingLadderLaw X μ a) := by
  have ha : 0 < a := lt_of_lt_of_le hδ hδa
  have hprob := gaussianAscendingLadderLaw_isProbabilityMeasure hX hi a
  set ν := gaussianAscendingLadderLaw X μ a with hνdef
  have hmeas : Measurable (fun y : ℝ =>
      ladderRenewalMeasure ν (Ioc (b - x - y) (b - y))) :=
    measurable_ladderRenewal_window_shift ν b x
  have hfin : ∀ y : ℝ,
      ladderRenewalMeasure ν (Ioc (b - x - y) (b - y)) < ⊤ := by
    intro y
    have hbnd := ladderRenewalMeasure_Ioc_le_const (X := X) (μ := μ)
      hX hi hG ha haM (b - x - y) hx
    rw [show b - x - y + x = b - y by ring] at hbnd
    exact lt_of_le_of_lt hbnd ENNReal.ofReal_lt_top
  rw [integral_toReal hmeas.aemeasurable
    (Filter.Eventually.of_forall hfin),
    lintegral_equilibrium_window_eq_gaussian hX hi hG hδ hδa haM hx hxb,
    ENNReal.toReal_div, ENNReal.toReal_ofReal hx]
  rfl

/-- **The exact Blackwell error representation.**  Nothing about the value of
the limit is left open: the whole error is a `Q`-average of *differences* of
window masses at shifted positions. -/
theorem ladderRenewalMeasure_window_sub_eq_integral [IsProbabilityMeasure μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {δ M a : ℝ} (hδ : 0 < δ) (hδa : δ ≤ a) (haM : a ≤ M)
    {b x : ℝ} (hx : 0 ≤ x) (hxb : x ≤ b) :
    (ladderRenewalMeasure (gaussianAscendingLadderLaw X μ a)
        (Ioc (b - x) b)).toReal -
      x / ladderMean (gaussianAscendingLadderLaw X μ a) =
      ∫ y, ((ladderRenewalMeasure (gaussianAscendingLadderLaw X μ a)
          (Ioc (b - x) b)).toReal -
        (ladderRenewalMeasure (gaussianAscendingLadderLaw X μ a)
          (Ioc (b - x - y) (b - y))).toReal)
        ∂(equilibriumOvershootLaw (gaussianAscendingLadderLaw X μ a)) := by
  have ha : 0 < a := lt_of_lt_of_le hδ hδa
  have hprob := gaussianAscendingLadderLaw_isProbabilityMeasure hX hi a
  set ν := gaussianAscendingLadderLaw X μ a with hνdef
  have hQprob := gaussianAscendingLadderEquilibrium_isProbabilityMeasure
    hX hi hG hδ hδa haM
  set Q := equilibriumOvershootLaw ν with hQdef
  set W : ℝ → ℝ := fun y =>
    (ladderRenewalMeasure ν (Ioc (b - x - y) (b - y))).toReal with hWdef
  have hmeas : Measurable W :=
    (measurable_ladderRenewal_window_shift ν b x).ennreal_toReal
  have hbdd : ∀ y : ℝ, |W y| ≤
      2 * Real.exp 1 * (1 + x) / gaussianAscendingLadderCommonDensity M := by
    intro y
    have hbnd := ladderRenewalMeasure_Ioc_le_const (X := X) (μ := μ)
      hX hi hG ha haM (b - x - y) hx
    rw [show b - x - y + x = b - y by ring] at hbnd
    have hc := gaussianAscendingLadderCommonDensity_pos M
    have hvalue : (ENNReal.ofReal (2 * Real.exp 1 * (1 + x) /
        gaussianAscendingLadderCommonDensity M)).toReal =
        2 * Real.exp 1 * (1 + x) / gaussianAscendingLadderCommonDensity M :=
      ENNReal.toReal_ofReal (by positivity)
    rw [hWdef]
    simp only []
    rw [abs_of_nonneg ENNReal.toReal_nonneg, ← hvalue]
    exact ENNReal.toReal_mono ENNReal.ofReal_ne_top hbnd
  have hWint : Integrable W Q := by
    refine (integrable_const (2 * Real.exp 1 * (1 + x) /
        gaussianAscendingLadderCommonDensity M)).mono'
      hmeas.aestronglyMeasurable ?_
    filter_upwards with y
    rw [Real.norm_eq_abs]
    exact hbdd y
  have hconst : Integrable (fun _ : ℝ =>
      (ladderRenewalMeasure ν (Ioc (b - x) b)).toReal) Q := integrable_const _
  rw [integral_sub hconst hWint, integral_const]
  have hQuniv : Q.real univ = 1 := by
    rw [Measure.real, measure_univ, ENNReal.toReal_one]
  rw [hQuniv, one_smul]
  congr 1
  exact (integral_equilibrium_window_eq_gaussian hX hi hG hδ hδa haM hx hxb).symm


/-! ### The limit value is forced -/

/-- A generic bounded-pointwise dominated convergence step along `atTop`. -/
theorem tendsto_integral_of_bounded_pointwise
    {Q : Measure ℝ} [IsProbabilityMeasure Q] {F : ℝ → ℝ → ℝ} {c C : ℝ}
    (hFmeas : ∀ b, Measurable (F b)) (hFbound : ∀ b y, |F b y| ≤ C)
    (hlim : ∀ y, Tendsto (fun b => F b y) atTop (𝓝 c)) :
    Tendsto (fun b => ∫ y, F b y ∂Q) atTop (𝓝 c) := by
  have hconv : Tendsto (fun b => ∫ y, F b y ∂Q) atTop (𝓝 (∫ _y : ℝ, c ∂Q)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun _ : ℝ => C) ?_ ?_ (integrable_const C) ?_
    · filter_upwards with b
      exact (hFmeas b).aestronglyMeasurable
    · filter_upwards with b
      filter_upwards with y
      rw [Real.norm_eq_abs]
      exact hFbound b y
    · filter_upwards with y
      exact hlim y
  have hconst : (∫ _y : ℝ, c ∂Q) = c := by
    rw [integral_const]
    have hQuniv : Q.real univ = 1 := by
      rw [Measure.real, measure_univ, ENNReal.toReal_one]
    rw [hQuniv, one_smul]
  rwa [hconst] at hconv

/--
**Identification of the Blackwell constant.**  If the renewal window mass has
*any* limit along `b → ∞`, that limit is necessarily `x/μ_a`.  The proof is
dominated convergence against the exact stationary identity; the domination
comes from the position-uniform window bound, so nothing is assumed.

Together with `ladderRenewalMeasure_window_sub_eq_integral` this settles the
"value of the limit" half of Blackwell's theorem for the actual ladder family.
What remains open in `UniformRenewalWindowLimit` is existence of the limit and
its uniformity in the drift and the window length.
-/
theorem window_limit_eq_of_tendsto [IsProbabilityMeasure μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {δ M a : ℝ} (hδ : 0 < δ) (hδa : δ ≤ a) (haM : a ≤ M)
    {x c : ℝ} (hx : 0 ≤ x)
    (hc : Tendsto (fun b : ℝ =>
      (ladderRenewalMeasure (gaussianAscendingLadderLaw X μ a)
        (Ioc (b - x) b)).toReal) atTop (𝓝 c)) :
    c = x / ladderMean (gaussianAscendingLadderLaw X μ a) := by
  have ha : 0 < a := lt_of_lt_of_le hδ hδa
  have hprob := gaussianAscendingLadderLaw_isProbabilityMeasure hX hi a
  have hQprob := gaussianAscendingLadderEquilibrium_isProbabilityMeasure
    hX hi hG hδ hδa haM
  have hcM : 0 < gaussianAscendingLadderCommonDensity M :=
    gaussianAscendingLadderCommonDensity_pos M
  have hexp : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hFbound : ∀ b y : ℝ,
      |(ladderRenewalMeasure (gaussianAscendingLadderLaw X μ a)
        (Ioc (b - x - y) (b - y))).toReal| ≤
      2 * Real.exp 1 * (1 + x) / gaussianAscendingLadderCommonDensity M := by
    intro b y
    have hbnd := ladderRenewalMeasure_Ioc_le_const (X := X) (μ := μ)
      hX hi hG ha haM (b - x - y) hx
    rw [show b - x - y + x = b - y by ring] at hbnd
    have hmono := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbnd
    rw [ENNReal.toReal_ofReal (by positivity)] at hmono
    rw [abs_of_nonneg ENNReal.toReal_nonneg]
    exact hmono
  have hlim : ∀ y : ℝ, Tendsto (fun b : ℝ =>
      (ladderRenewalMeasure (gaussianAscendingLadderLaw X μ a)
        (Ioc (b - x - y) (b - y))).toReal) atTop (𝓝 c) := by
    intro y
    have hshift : Tendsto (fun b : ℝ => b - y) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_id
    have hcomp := hc.comp hshift
    refine hcomp.congr fun b => ?_
    simp only [Function.comp_apply]
    congr 3
    ring
  have hconv := tendsto_integral_of_bounded_pointwise
    (Q := equilibriumOvershootLaw (gaussianAscendingLadderLaw X μ a))
    (F := fun b y => (ladderRenewalMeasure (gaussianAscendingLadderLaw X μ a)
      (Ioc (b - x - y) (b - y))).toReal)
    (c := c)
    (fun b => (measurable_ladderRenewal_window_shift
      (gaussianAscendingLadderLaw X μ a) b x).ennreal_toReal)
    hFbound hlim
  have heventually : ∀ᶠ b : ℝ in atTop,
      (∫ y, (ladderRenewalMeasure (gaussianAscendingLadderLaw X μ a)
        (Ioc (b - x - y) (b - y))).toReal
        ∂(equilibriumOvershootLaw (gaussianAscendingLadderLaw X μ a))) =
      x / ladderMean (gaussianAscendingLadderLaw X μ a) := by
    filter_upwards [eventually_ge_atTop x] with b hb
    exact integral_equilibrium_window_eq_gaussian hX hi hG hδ hδa haM hx hb
  have hconv' : Tendsto (fun _ : ℝ =>
      x / ladderMean (gaussianAscendingLadderLaw X μ a)) atTop (𝓝 c) :=
    hconv.congr' heventually
  exact (tendsto_nhds_unique tendsto_const_nhds hconv').symm

end SwingRepair
