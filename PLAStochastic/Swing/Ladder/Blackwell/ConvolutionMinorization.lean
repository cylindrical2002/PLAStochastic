import PLAStochastic.Swing.Ladder.Blackwell.WindowRenewalEquation

/-!
# Convolution powers of the common Lebesgue component

The ladder family has a common Lebesgue component on `[1,2]`
(`gaussianAscendingLadderLaw_common_minorization`).  The Blackwell argument
needs to transfer smallness in `ν^{*m}`-mean to smallness of a Lebesgue window
integral, and for that it needs an explicit positive Lebesgue minorization of
`ν^{*m}` on an interval.

The single analytic input is the interval convolution bound
`restrict_Icc_conv_restrict_Icc_ge`: convolving Lebesgue measure on `[p,q]`
with Lebesgue measure on `[1,2]` dominates `η` times Lebesgue measure on
`[p+1+η, q+2-η]`, for every `0 < η ≤ 1` with `η ≤ q-p`.  Iterating it gives
intervals whose length grows by `1-2η` per step, at the cost of a factor `η`
in the constant; the resulting intervals cover `[1,∞)` up to the single point
`2` and a set of measure `η`.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical MeasureTheory
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-! ## Convolution evaluated on a set -/

theorem measure_conv_apply (ρ σ : Measure ℝ) [SFinite ρ] [SFinite σ]
    {A : Set ℝ} (hA : MeasurableSet A) :
    (ρ ∗ σ) A = ∫⁻ x, σ {y : ℝ | x + y ∈ A} ∂ρ := by
  have hS : MeasurableSet {z : ℝ × ℝ | z.1 + z.2 ∈ A} :=
    hA.preimage (measurable_fst.add measurable_snd)
  have hmap : (ρ ∗ σ) A = (ρ.prod σ) {z : ℝ × ℝ | z.1 + z.2 ∈ A} := by
    rw [Measure.conv, Measure.map_apply (by fun_prop) hA]
    rfl
  rw [hmap, Measure.prod_apply hS]
  rfl

/-- Translating the `[1,2]` component: the mass it gives to the preimage of `A`
is the Lebesgue mass of `A` in the translated window. -/
theorem restrict_Icc_preimage_translate (x : ℝ) {A : Set ℝ} (hA : MeasurableSet A) :
    (volume.restrict (Icc (1 : ℝ) 2)) {y : ℝ | x + y ∈ A} =
      volume (A ∩ Icc (x + 1) (x + 2)) := by
  have hpre : MeasurableSet {y : ℝ | x + y ∈ A} :=
    hA.preimage (measurable_const.add measurable_id)
  rw [Measure.restrict_apply hpre]
  have hmp : MeasurePreserving (fun y : ℝ => x + y) volume volume :=
    measurePreserving_add_left volume x
  have himg : (fun y : ℝ => x + y) ⁻¹' (A ∩ Icc (x + 1) (x + 2)) =
      {y : ℝ | x + y ∈ A} ∩ Icc (1 : ℝ) 2 := by
    ext y
    simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Icc]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, by linarith, by linarith⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, by linarith, by linarith⟩
  have hmeasA : MeasurableSet (A ∩ Icc (x + 1) (x + 2)) := hA.inter measurableSet_Icc
  have hpm := hmp.measure_preimage hmeasA.nullMeasurableSet
  rw [himg] at hpm
  exact hpm

/-! ## The interval overlap bound -/

theorem interval_overlap_ge {p q η t : ℝ} (_hη : 0 < η) (hη1 : η ≤ 1)
    (hpq : η ≤ q - p) (ht : t ∈ Icc (p + 1 + η) (q + 2 - η)) :
    ENNReal.ofReal η ≤ volume (Icc p q ∩ Icc (t - 2) (t - 1)) := by
  obtain ⟨ht1, ht2⟩ := ht
  have hinter : Icc p q ∩ Icc (t - 2) (t - 1) = Icc (max p (t - 2)) (min q (t - 1)) := by
    rw [Icc_inter_Icc]
  rw [hinter, Real.volume_Icc]
  refine ENNReal.ofReal_le_ofReal ?_
  have h1 : p + η ≤ q := by linarith
  have h2 : t - 2 + η ≤ q := by linarith
  have h3 : p + η ≤ t - 1 := by linarith
  have h4 : t - 2 + η ≤ t - 1 := by linarith
  have hmax : max p (t - 2) + η ≤ min q (t - 1) := by
    rcases max_cases p (t - 2) with ⟨hm, -⟩ | ⟨hm, -⟩ <;> rw [hm] <;>
      rcases min_cases q (t - 1) with ⟨hn, -⟩ | ⟨hn, -⟩ <;> rw [hn] <;> linarith
  linarith

/-! ## The interval convolution bound -/

theorem restrict_Icc_conv_restrict_Icc_ge {p q η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    (hpq : η ≤ q - p) :
    ENNReal.ofReal η • volume.restrict (Icc (p + 1 + η) (q + 2 - η)) ≤
      (volume.restrict (Icc p q)) ∗ (volume.restrict (Icc (1 : ℝ) 2)) := by
  refine Measure.le_iff.mpr fun A hA => ?_
  -- the right-hand side as an iterated integral
  have hRHS : ((volume.restrict (Icc p q)) ∗ (volume.restrict (Icc (1 : ℝ) 2))) A =
      ∫⁻ x in Icc p q, volume (A ∩ Icc (x + 1) (x + 2)) := by
    rw [measure_conv_apply _ _ hA]
    exact lintegral_congr fun x => restrict_Icc_preimage_translate x hA
  -- rewrite the inner Lebesgue mass as an integral and swap
  set G : ℝ × ℝ → ℝ≥0∞ := fun z =>
    if z.2 ∈ A ∧ z.1 ∈ Icc p q ∧ z.1 + 1 ≤ z.2 ∧ z.2 ≤ z.1 + 2 then 1 else 0 with hGdef
  have hGval : ∀ x t : ℝ, G (x, t) =
      (if t ∈ A ∧ x ∈ Icc p q ∧ x + 1 ≤ t ∧ t ≤ x + 2 then (1 : ℝ≥0∞) else 0) :=
    fun _ _ => rfl
  have hGmeas : Measurable G := by
    refine Measurable.ite ?_ measurable_const measurable_const
    refine ((hA.preimage measurable_snd).inter ?_)
    refine ((measurableSet_Icc.preimage measurable_fst).inter ?_)
    exact (measurableSet_le (measurable_fst.add_const 1) measurable_snd).inter
      (measurableSet_le measurable_snd (measurable_fst.add_const 2))
  have hinnerx : ∀ x : ℝ, x ∈ Icc p q →
      volume (A ∩ Icc (x + 1) (x + 2)) = ∫⁻ t, G (x, t) := by
    intro x hx
    rw [← lintegral_indicator_one (hA.inter measurableSet_Icc)]
    refine lintegral_congr fun t => ?_
    rw [hGval]
    by_cases ht : t ∈ A ∩ Icc (x + 1) (x + 2)
    · rw [Set.indicator_of_mem ht, Pi.one_apply,
        if_pos ⟨ht.1, hx, ht.2.1, ht.2.2⟩]
    · rw [Set.indicator_of_notMem ht, if_neg (by
        rintro ⟨h1, -, h2, h3⟩
        exact ht ⟨h1, h2, h3⟩)]
  have hstep1 : (∫⁻ x in Icc p q, volume (A ∩ Icc (x + 1) (x + 2))) =
      ∫⁻ x in Icc p q, (∫⁻ t, G (x, t)) :=
    setLIntegral_congr_fun measurableSet_Icc hinnerx
  have hstep2 : (∫⁻ x in Icc p q, (∫⁻ t, G (x, t))) =
      ∫⁻ x, (∫⁻ t, G (x, t)) := by
    rw [← lintegral_indicator measurableSet_Icc]
    refine lintegral_congr fun x => ?_
    by_cases hx : x ∈ Icc p q
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx]
      have hzero : ∀ t : ℝ, G (x, t) = 0 := by
        intro t
        rw [hGval, if_neg (by
          rintro ⟨-, h2, -, -⟩
          exact hx h2)]
      simp only [hzero, lintegral_zero]
  have hswap : (∫⁻ x, (∫⁻ t, G (x, t))) = ∫⁻ t, (∫⁻ x, G (x, t)) :=
    lintegral_lintegral_swap hGmeas.aemeasurable
  have hcol : ∀ t : ℝ, (∫⁻ x, G (x, t)) =
      Set.indicator A (fun t => volume (Icc p q ∩ Icc (t - 2) (t - 1))) t := by
    intro t
    by_cases htA : t ∈ A
    · rw [Set.indicator_of_mem htA]
      rw [← lintegral_indicator_one (measurableSet_Icc.inter measurableSet_Icc)]
      refine lintegral_congr fun x => ?_
      rw [hGval]
      by_cases hx : x ∈ Icc p q ∩ Icc (t - 2) (t - 1)
      · rw [Set.indicator_of_mem hx, Pi.one_apply,
          if_pos ⟨htA, hx.1, by linarith [hx.2.2], by linarith [hx.2.1]⟩]
      · rw [Set.indicator_of_notMem hx, if_neg (by
          rintro ⟨-, h2, h3, h4⟩
          refine hx ⟨h2, ?_⟩
          constructor
          · linarith
          · linarith)]
    · rw [Set.indicator_of_notMem htA]
      have hzero : ∀ x : ℝ, G (x, t) = 0 := by
        intro x
        rw [hGval, if_neg (by
          rintro ⟨h1, -, -, -⟩
          exact htA h1)]
      simp only [hzero, lintegral_zero]
  -- assemble
  have hLHS : (ENNReal.ofReal η • volume.restrict (Icc (p + 1 + η) (q + 2 - η))) A =
      ENNReal.ofReal η * volume (A ∩ Icc (p + 1 + η) (q + 2 - η)) := by
    rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hA]
  rw [hLHS, hRHS, hstep1, hstep2, hswap, lintegral_congr hcol,
    lintegral_indicator hA]
  have hbound : ∀ t ∈ A ∩ Icc (p + 1 + η) (q + 2 - η),
      ENNReal.ofReal η ≤ volume (Icc p q ∩ Icc (t - 2) (t - 1)) := by
    intro t ht
    exact interval_overlap_ge hη hη1 hpq ht.2
  calc ENNReal.ofReal η * volume (A ∩ Icc (p + 1 + η) (q + 2 - η))
      = ∫⁻ _t in A ∩ Icc (p + 1 + η) (q + 2 - η), ENNReal.ofReal η := by
        rw [setLIntegral_const, mul_comm]
    _ ≤ ∫⁻ t in A ∩ Icc (p + 1 + η) (q + 2 - η),
          volume (Icc p q ∩ Icc (t - 2) (t - 1)) :=
        setLIntegral_mono' (hA.inter measurableSet_Icc) hbound
    _ ≤ ∫⁻ t in A, volume (Icc p q ∩ Icc (t - 2) (t - 1)) :=
        lintegral_mono_set Set.inter_subset_left


/-! ## Iterating the minorization along convolution powers -/

/-- The interval carrying the Lebesgue component of `ν^{*(m+1)}`. -/
def minorIcc (η : ℝ) (m : ℕ) : Set ℝ :=
  Icc (1 + (m : ℝ) * (1 + η)) (2 + (m : ℝ) * (2 - η))

/-- The constant of that component. -/
def minorConst (κ η : ℝ) (m : ℕ) : ℝ := κ ^ (m + 1) * η ^ m

theorem minorIcc_succ (η : ℝ) (m : ℕ) :
    minorIcc η (m + 1) =
      Icc ((1 + (m : ℝ) * (1 + η)) + 1 + η) ((2 + (m : ℝ) * (2 - η)) + 2 - η) := by
  unfold minorIcc
  congr 1
  · push_cast
    ring
  · push_cast
    ring

theorem minorConst_succ (κ η : ℝ) (m : ℕ) :
    minorConst κ η (m + 1) = minorConst κ η m * κ * η := by
  unfold minorConst
  ring

/-- The `κ`-component of a measure, transported through one convolution step. -/
theorem measure_ge_translate_of_minorization {ν : Measure ℝ} {κ : ℝ}
    (hmin : ENNReal.ofReal κ • volume.restrict (Icc (1 : ℝ) 2) ≤ ν)
    {A : Set ℝ} (hA : MeasurableSet A) (x : ℝ) :
    ENNReal.ofReal κ * volume (A ∩ Icc (x + 1) (x + 2)) ≤ ν {y : ℝ | x + y ∈ A} := by
  have hpre : MeasurableSet {y : ℝ | x + y ∈ A} :=
    hA.preimage (measurable_const.add measurable_id)
  have h := Measure.le_iff.mp hmin {y : ℝ | x + y ∈ A} hpre
  rwa [Measure.smul_apply, smul_eq_mul,
    restrict_Icc_preimage_translate x hA] at h

/-- The interval convolution bound, in the integral form used by the
induction. -/
theorem setLIntegral_window_ge {p q η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    (hpq : η ≤ q - p) {A : Set ℝ} (hA : MeasurableSet A) :
    ENNReal.ofReal η * volume (A ∩ Icc (p + 1 + η) (q + 2 - η)) ≤
      ∫⁻ x in Icc p q, volume (A ∩ Icc (x + 1) (x + 2)) := by
  have hbase := Measure.le_iff.mp
    (restrict_Icc_conv_restrict_Icc_ge hη hη1 hpq) A hA
  rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hA,
    measure_conv_apply _ _ hA] at hbase
  refine le_trans hbase (le_of_eq ?_)
  exact lintegral_congr fun x => restrict_Icc_preimage_translate x hA

/--
**The explicit Lebesgue component of every convolution power.**  From a common
component `κ · Leb|[1,2]` of `ν`, the `(m+1)`-st convolution power dominates
`κ^{m+1} η^m · Leb` on an interval whose length grows by `1 - 2η` at each step.
-/
theorem measureConvPow_ge_minor (ν : Measure ℝ) [IsProbabilityMeasure ν] {κ η : ℝ}
    (hκ0 : 0 ≤ κ) (hη : 0 < η) (hη4 : η ≤ 1 / 4)
    (hmin : ENNReal.ofReal κ • volume.restrict (Icc (1 : ℝ) 2) ≤ ν) (m : ℕ) :
    ENNReal.ofReal (minorConst κ η m) • volume.restrict (minorIcc η m) ≤
      measureConvPow ν (m + 1) := by
  have hη1 : η ≤ 1 := by linarith
  induction m with
  | zero =>
    have hone : measureConvPow ν 1 = ν := by
      rw [measureConvPow_succ, measureConvPow_zero, Measure.dirac_zero_conv]
    have hI : minorIcc η 0 = Icc (1 : ℝ) 2 := by
      unfold minorIcc
      norm_num
    have hc : minorConst κ η 0 = κ := by
      unfold minorConst
      ring
    rw [hone, hI, hc]
    exact hmin
  | succ m ih =>
    refine Measure.le_iff.mpr fun A hA => ?_
    set p : ℝ := 1 + (m : ℝ) * (1 + η) with hp
    set q : ℝ := 2 + (m : ℝ) * (2 - η) with hq
    have hIm : minorIcc η m = Icc p q := rfl
    have hpq : η ≤ q - p := by
      have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      rw [hp, hq]
      nlinarith
    -- one convolution step
    have hconv : measureConvPow ν (m + 1 + 1) A =
        ∫⁻ x, ν {y : ℝ | x + y ∈ A} ∂(measureConvPow ν (m + 1)) := by
      rw [measureConvPow_succ, measure_conv_apply _ _ hA]
    have hmono1 : (∫⁻ x, ν {y : ℝ | x + y ∈ A}
          ∂(ENNReal.ofReal (minorConst κ η m) • volume.restrict (minorIcc η m))) ≤
        ∫⁻ x, ν {y : ℝ | x + y ∈ A} ∂(measureConvPow ν (m + 1)) :=
      lintegral_mono' ih (le_refl _)
    have hsmul : (∫⁻ x, ν {y : ℝ | x + y ∈ A}
          ∂(ENNReal.ofReal (minorConst κ η m) • volume.restrict (minorIcc η m))) =
        ENNReal.ofReal (minorConst κ η m) *
          ∫⁻ x in Icc p q, ν {y : ℝ | x + y ∈ A} := by
      rw [lintegral_smul_measure, hIm, smul_eq_mul]
    have hinner : (∫⁻ x in Icc p q,
          ENNReal.ofReal κ * volume (A ∩ Icc (x + 1) (x + 2))) ≤
        ∫⁻ x in Icc p q, ν {y : ℝ | x + y ∈ A} :=
      lintegral_mono fun x => measure_ge_translate_of_minorization hmin hA x
    have hpull : (∫⁻ x in Icc p q,
          ENNReal.ofReal κ * volume (A ∩ Icc (x + 1) (x + 2))) =
        ENNReal.ofReal κ * ∫⁻ x in Icc p q, volume (A ∩ Icc (x + 1) (x + 2)) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    have hIC := setLIntegral_window_ge (p := p) (q := q) hη hη1 hpq hA
    -- assemble
    have hgoal : (ENNReal.ofReal (minorConst κ η (m + 1)) •
        volume.restrict (minorIcc η (m + 1))) A =
        ENNReal.ofReal (minorConst κ η m) * (ENNReal.ofReal κ *
          (ENNReal.ofReal η * volume (A ∩ Icc (p + 1 + η) (q + 2 - η)))) := by
      rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hA,
        minorIcc_succ, minorConst_succ, ← hp, ← hq]
      have hmc : 0 ≤ minorConst κ η m := by
        unfold minorConst
        positivity
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hmc]
      ring
    rw [hgoal, hconv]
    calc ENNReal.ofReal (minorConst κ η m) * (ENNReal.ofReal κ *
            (ENNReal.ofReal η * volume (A ∩ Icc (p + 1 + η) (q + 2 - η))))
        ≤ ENNReal.ofReal (minorConst κ η m) * (ENNReal.ofReal κ *
            ∫⁻ x in Icc p q, volume (A ∩ Icc (x + 1) (x + 2))) := by
          gcongr
      _ = ENNReal.ofReal (minorConst κ η m) *
            ∫⁻ x in Icc p q, ENNReal.ofReal κ *
              volume (A ∩ Icc (x + 1) (x + 2)) := by rw [hpull]
      _ ≤ ENNReal.ofReal (minorConst κ η m) *
            ∫⁻ x in Icc p q, ν {y : ℝ | x + y ∈ A} := by gcongr
      _ = ∫⁻ x, ν {y : ℝ | x + y ∈ A}
            ∂(ENNReal.ofReal (minorConst κ η m) •
              volume.restrict (minorIcc η m)) := hsmul.symm
      _ ≤ ∫⁻ x, ν {y : ℝ | x + y ∈ A} ∂(measureConvPow ν (m + 1)) := hmono1


/-! ## The minorizing intervals cover `[1,∞)` up to one small gap -/

/--
For `0 < η ≤ 1/4` the intervals `minorIcc η m` cover every `t ≥ 1` except the
gap `(2, 2+2η)` between the first two.  The index is explicit.
-/
theorem exists_mem_minorIcc {η t : ℝ} (hη : 0 < η) (hη4 : η ≤ 1 / 4)
    (ht1 : 1 ≤ t) (hgap : t ≤ 2 ∨ 2 + 2 * η ≤ t) :
    ∃ m : ℕ, t ∈ minorIcc η m ∧ (m : ℝ) ≤ t := by
  rcases hgap with hle | hge
  · refine ⟨0, ?_, ?_⟩
    · unfold minorIcc
      norm_num
      exact ⟨ht1, hle⟩
    · norm_num
      linarith
  · have hpos : (0 : ℝ) < 1 + η := by linarith
    set m : ℕ := ⌊(t - 1) / (1 + η)⌋₊ with hm
    have hnn : 0 ≤ (t - 1) / (1 + η) := by
      apply div_nonneg _ hpos.le
      linarith
    have hmle : (m : ℝ) ≤ (t - 1) / (1 + η) := Nat.floor_le hnn
    have hltm : (t - 1) / (1 + η) < (m : ℝ) + 1 := Nat.lt_floor_add_one _
    have hlow : 1 + (m : ℝ) * (1 + η) ≤ t := by
      have hmul := (le_div_iff₀ hpos).mp hmle
      linarith
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by
      have hge1 : (1 : ℝ) ≤ (t - 1) / (1 + η) := by
        rw [le_div_iff₀ hpos]
        linarith
      have : 1 ≤ m := Nat.one_le_floor_iff _ |>.mpr hge1
      exact_mod_cast this
    have hupper : t ≤ 2 + (m : ℝ) * (2 - η) := by
      have hlt : t < 1 + ((m : ℝ) + 1) * (1 + η) := by
        have := (div_lt_iff₀ hpos).mp hltm
        linarith
      nlinarith
    refine ⟨m, ⟨hlow, hupper⟩, ?_⟩
    nlinarith [hm1, hη.le]

/-! ## The Gaussian instance -/

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

/-- The actual Gaussian ladder family: every convolution power has an explicit
Lebesgue component, with constants depending only on `M` and `η`. -/
theorem gaussianAscendingLadderLaw_convPow_ge_minor [IsProbabilityMeasure μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {M a η : ℝ} (ha : 0 ≤ a) (haM : a ≤ M) (hη : 0 < η) (hη4 : η ≤ 1 / 4)
    (m : ℕ) :
    ENNReal.ofReal
        (minorConst (gaussianAscendingLadderCommonDensity M) η m) •
      volume.restrict (minorIcc η m) ≤
      measureConvPow (gaussianAscendingLadderLaw X μ a) (m + 1) := by
  have hprob := gaussianAscendingLadderLaw_isProbabilityMeasure hX hi a
  exact measureConvPow_ge_minor _
    (gaussianAscendingLadderCommonDensity_pos M).le hη hη4
    (gaussianAscendingLadderLaw_common_minorization hX (hG 0) ha haM) m

end SwingRepair
