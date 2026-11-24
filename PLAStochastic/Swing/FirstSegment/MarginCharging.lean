import PLAStochastic.Swing.Gaussian.Tail.ScalarAntiConcentration
import PLAStochastic.Swing.FirstSegment.TwoStepCharging

/-! # Guarded charging for the actual output margin

The scalar anti-concentration estimates of `GaussianAntiConcentration` are
transported to a past-measurable state through the product law of the fresh
increments.  The state carries the actual observation offset `v` and the
actual upper rejection threshold `r`; neither is given a Gaussian law.
-/
noncomputable section
open Classical
open MeasureTheory ProbabilityTheory BrownianAffine Filter Set
open scoped NNReal ENNReal Topology
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem gaussianReal_Ioi_real_pos {t : ℝ} (ht : 0 ≤ t) :
    0 < (gaussianReal 0 1).real (Ioi t) := by
  have hl := gaussianReal_Ioc_density_lower (a := t) (b := t+1) ht (by linarith)
  have hsub : gaussianReal 0 1 (Ioc t (t+1)) ≤ gaussianReal 0 1 (Ioi t) :=
    measure_mono (fun z hz => hz.1)
  have hpos : 0 < gaussianPDFReal 0 1 (t+1) := gaussianPDFReal_pos 0 1 _ (by norm_num)
  have hstep : ENNReal.ofReal (gaussianPDFReal 0 1 (t+1)) ≤ gaussianReal 0 1 (Ioi t) := by
    refine le_trans ?_ (hl.trans hsub)
    exact ENNReal.ofReal_le_ofReal (by nlinarith)
  have h := ENNReal.toReal_mono (measure_ne_top (gaussianReal 0 1) _) hstep
  rw [ENNReal.toReal_ofReal hpos.le] at h
  exact lt_of_lt_of_le hpos h

/-- One-step charging of the output-margin target against the actual rejection
event, on the layer where the rejection threshold is below one. -/
theorem independent_gaussian_margin_one_step_charge {Ω α : Type*}
    [MeasurableSpace Ω] [MeasurableSpace α] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → α} {Z : Ω → ℝ} (hX : Measurable X) (hZ : Measurable Z)
    (hi : IndepFun X Z μ) (hlaw : μ.map Z = gaussianReal 0 1)
    {U : Set α} (hU : MeasurableSet U) {r v : α → ℝ} (hr : Measurable r) (hv : Measurable v)
    {Eb p q : ℝ} (hpq : p ≤ q)
    (hsmall : ∀ x ∈ U, r x ≤ 1) :
    μ.real {ω | X ω ∈ U ∧ Z ω ∈ marginTargetSet Eb (v (X ω)) p q ∧ r (X ω) < Z ω} ≤
      marginAntiConcentrationConstant*(q-p)*μ.real {ω | X ω ∈ U ∧ r (X ω) < Z ω} := by
  let F (w : α × ℝ) : ℝ :=
    if w.2 ∈ marginTargetSet Eb (v w.1) p q ∧ r w.1 < w.2 then 1 else 0
  let G (w : α × ℝ) : ℝ := if r w.1 < w.2 then 1 else 0
  have htarget : MeasurableSet {w : α × ℝ | w.2 ∈ marginTargetSet Eb (v w.1) p q} := by
    have hmap : Measurable (fun w : α × ℝ => Eb-|v w.1+w.2|) :=
      measurable_const.sub (((hv.comp measurable_fst).add measurable_snd).abs)
    exact measurableSet_Icc.preimage hmap
  have hFm : Measurable F := measurable_const.ite
    (htarget.inter (measurableSet_lt (hr.comp measurable_fst) measurable_snd)) measurable_const
  have hGm : Measurable G := measurable_const.ite
    (measurableSet_lt (hr.comp measurable_fst) measurable_snd) measurable_const
  have hFb : ∀ w, |F w| ≤ 1 := by intro w; dsimp only [F]; split_ifs <;> norm_num
  have hGb : ∀ w, |G w| ≤ 1 := by intro w; dsimp only [G]; split_ifs <;> norm_num
  have hsection : ∀ x ∈ U, (∫ z, F (x,z) ∂μ.map Z) ≤
      marginAntiConcentrationConstant*(q-p)*(∫ z, G (x,z) ∂μ.map Z)+0 := by
    intro x hx
    rw [hlaw]
    have hFset : (fun z => F (x,z)) =
        fun z => if z ∈ marginTargetSet Eb (v x) p q ∩ Ioi (r x) then (1 : ℝ) else 0 := by
      funext z
      dsimp only [F]
      congr 1
    have hGset : (fun z => G (x,z)) = fun z => if z ∈ Ioi (r x) then (1 : ℝ) else 0 := by
      funext z
      dsimp only [G]
      congr 1
    have hFv : (∫ z, F (x,z) ∂gaussianReal 0 1) =
        (gaussianReal 0 1).real (marginTargetSet Eb (v x) p q ∩ Ioi (r x)) :=
      (congrArg (fun f : ℝ → ℝ => ∫ z, f z ∂gaussianReal 0 1) hFset).trans
        (integral_if_one_eq_measureReal
          ((measurableSet_marginTargetSet Eb (v x) p q).inter measurableSet_Ioi))
    have hGv : (∫ z, G (x,z) ∂gaussianReal 0 1) = (gaussianReal 0 1).real (Ioi (r x)) :=
      (congrArg (fun f : ℝ → ℝ => ∫ z, f z ∂gaussianReal 0 1) hGset).trans
        (integral_if_one_eq_measureReal measurableSet_Ioi)
    rw [hFv, hGv, add_zero]
    have hbound := gaussianReal_marginTarget_small_threshold (Eb := Eb) (v := v x) hpq
      (hsmall x hx)
    have h := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (measure_ne_top _ _)) hbound
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal
      (mul_nonneg marginAntiConcentrationConstant_pos.le (sub_nonneg.mpr hpq))] at h
  have hc := IndepFun.integral_state_guard_le hX.aemeasurable hZ.aemeasurable hi hU hFm hGm
    (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 1) hFb hGb hsection
  have hA : MeasurableSet {ω | X ω ∈ U ∧ Z ω ∈ marginTargetSet Eb (v (X ω)) p q ∧ r (X ω) < Z ω} :=
    (hU.preimage hX).inter ((htarget.preimage (hX.prodMk hZ)).inter
      (measurableSet_lt (hr.comp hX) hZ))
  have hB : MeasurableSet {ω | X ω ∈ U ∧ r (X ω) < Z ω} :=
    (hU.preimage hX).inter (measurableSet_lt (hr.comp hX) hZ)
  have heF : (fun ω => if X ω ∈ U then F (X ω,Z ω) else 0) =
      fun ω => if ω ∈ {ω | X ω ∈ U ∧ Z ω ∈ marginTargetSet Eb (v (X ω)) p q ∧ r (X ω) < Z ω}
        then (1 : ℝ) else 0 := by
    funext ω
    dsimp only [F, Set.mem_ofPred_eq]
    split_ifs <;> tauto
  have heG : (fun ω => if X ω ∈ U then G (X ω,Z ω) else 0) =
      fun ω => if ω ∈ {ω | X ω ∈ U ∧ r (X ω) < Z ω} then (1 : ℝ) else 0 := by
    funext ω
    dsimp only [G, Set.mem_ofPred_eq]
    split_ifs <;> tauto
  have hFL := (congrArg (fun f : Ω → ℝ => ∫ ω, f ω ∂μ) heF).trans
    (integral_if_one_eq_measureReal hA)
  have hGL := (congrArg (fun f : Ω → ℝ => ∫ ω, f ω ∂μ) heG).trans
    (integral_if_one_eq_measureReal hB)
  rw [hFL, hGL, zero_mul, add_zero] at hc
  exact hc

/-- Two-step charging of the output-margin target against the actual proxy
acceptance followed by a rejection, on the layer where the rejection threshold
exceeds one. -/
theorem independent_gaussian_margin_two_step_charge {Ω α : Type*}
    [MeasurableSpace Ω] [MeasurableSpace α] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → α} {Y : Ω → ℝ × ℝ} (hX : Measurable X) (hY : Measurable Y)
    (hi : IndepFun X Y μ) (hlaw : μ.map Y = (gaussianReal 0 1).prod (gaussianReal 0 1))
    {U : Set α} (hU : MeasurableSet U) {r v : α → ℝ} (hr : Measurable r) (hv : Measurable v)
    {Eb p q M : ℝ} (hpq : p ≤ q) (hM : 0 ≤ M+1)
    (hlarge : ∀ x ∈ U, 1 < r x) :
    μ.real {ω | X ω ∈ U ∧ (Y ω).1 ∈ marginTargetSet Eb (v (X ω)) p q ∧ r (X ω) < (Y ω).1} ≤
      4*(q-p)/(gaussianReal 0 1).real (Ioi (M+1))*
        μ.real {ω | X ω ∈ U ∧ (Y ω).1 ∈ Icc (r (X ω)-1) (r (X ω)-1/2) ∧ M+1 < (Y ω).2} := by
  set β : ℝ := (gaussianReal 0 1).real (Ioi (M+1)) with hβ
  have hβpos : 0 < β := gaussianReal_Ioi_real_pos hM
  let F (w : α × (ℝ × ℝ)) : ℝ :=
    if w.2.1 ∈ marginTargetSet Eb (v w.1) p q ∧ r w.1 < w.2.1 then 1 else 0
  let G (w : α × (ℝ × ℝ)) : ℝ :=
    if w.2.1 ∈ Icc (r w.1-1) (r w.1-1/2) ∧ M+1 < w.2.2 then 1 else 0
  have htarget : MeasurableSet {w : α × (ℝ × ℝ) | w.2.1 ∈ marginTargetSet Eb (v w.1) p q} := by
    have hmap : Measurable (fun w : α × (ℝ × ℝ) => Eb-|v w.1+w.2.1|) :=
      measurable_const.sub (((hv.comp measurable_fst).add measurable_snd.fst).abs)
    exact measurableSet_Icc.preimage hmap
  have hFm : Measurable F := measurable_const.ite
    (htarget.inter (measurableSet_lt (hr.comp measurable_fst) measurable_snd.fst)) measurable_const
  have hGm : Measurable G := measurable_const.ite
    (((measurableSet_le ((hr.comp measurable_fst).sub_const 1) measurable_snd.fst).inter
      (measurableSet_le measurable_snd.fst ((hr.comp measurable_fst).sub_const (1/2)))).inter
        (measurableSet_lt measurable_const measurable_snd.snd)) measurable_const
  have hFb : ∀ w, |F w| ≤ 1 := by intro w; dsimp only [F]; split_ifs <;> norm_num
  have hGb : ∀ w, |G w| ≤ 1 := by intro w; dsimp only [G]; split_ifs <;> norm_num
  have hsection : ∀ x ∈ U, (∫ y, F (x,y) ∂μ.map Y) ≤
      4*(q-p)/β*(∫ y, G (x,y) ∂μ.map Y)+0 := by
    intro x hx
    rw [hlaw]
    have hFset : (fun y : ℝ × ℝ => F (x,y)) =
        fun y => if y ∈ (marginTargetSet Eb (v x) p q ∩ Ioi (r x)) ×ˢ (Set.univ : Set ℝ)
          then (1 : ℝ) else 0 := by
      funext y
      dsimp only [F]
      congr 1
      simp only [Set.mem_prod, mem_inter_iff, mem_Ioi, Set.mem_univ, and_true]
    have hGset : (fun y : ℝ × ℝ => G (x,y)) =
        fun y => if y ∈ Icc (r x-1) (r x-1/2) ×ˢ Ioi (M+1) then (1 : ℝ) else 0 := rfl
    have hFv : (∫ y, F (x,y) ∂(gaussianReal 0 1).prod (gaussianReal 0 1)) =
        (gaussianReal 0 1).real (marginTargetSet Eb (v x) p q ∩ Ioi (r x)) := by
      calc
        _ = ((gaussianReal 0 1).prod (gaussianReal 0 1)).real
              ((marginTargetSet Eb (v x) p q ∩ Ioi (r x)) ×ˢ (Set.univ : Set ℝ)) :=
          (congrArg (fun f : ℝ × ℝ → ℝ => ∫ y, f y ∂(gaussianReal 0 1).prod (gaussianReal 0 1))
            hFset).trans (integral_if_one_eq_measureReal
              (((measurableSet_marginTargetSet Eb (v x) p q).inter
                measurableSet_Ioi).prod MeasurableSet.univ))
        _ = _ := by rw [measureReal_prod_prod, probReal_univ, mul_one]
    have hGv : (∫ y, G (x,y) ∂(gaussianReal 0 1).prod (gaussianReal 0 1)) =
        (gaussianReal 0 1).real (Icc (r x-1) (r x-1/2))*β := by
      calc
        _ = ((gaussianReal 0 1).prod (gaussianReal 0 1)).real
              (Icc (r x-1) (r x-1/2) ×ˢ Ioi (M+1)) :=
          (congrArg (fun f : ℝ × ℝ → ℝ => ∫ y, f y ∂(gaussianReal 0 1).prod (gaussianReal 0 1))
            hGset).trans (integral_if_one_eq_measureReal (measurableSet_Icc.prod measurableSet_Ioi))
        _ = _ := measureReal_prod_prod _ _
    rw [hFv, hGv, add_zero]
    have hbound := gaussianReal_marginTarget_large_threshold (Eb := Eb) (v := v x) hpq (hlarge x hx)
    have h := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (measure_ne_top _ _)) hbound
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal
      (by nlinarith [sub_nonneg.mpr hpq] : (0 : ℝ) ≤ 4*(q-p))] at h
    have hgoal : 4*(q-p)/β*((gaussianReal 0 1).real (Icc (r x-1) (r x-1/2))*β) =
        4*(q-p)*(gaussianReal 0 1).real (Icc (r x-1) (r x-1/2)) := by
      field_simp
    rw [hgoal]
    exact h
  have hc := IndepFun.integral_state_guard_le hX.aemeasurable hY.aemeasurable hi hU hFm hGm
    (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 1) hFb hGb hsection
  have hA : MeasurableSet
      {ω | X ω ∈ U ∧ (Y ω).1 ∈ marginTargetSet Eb (v (X ω)) p q ∧ r (X ω) < (Y ω).1} :=
    (hU.preimage hX).inter ((htarget.preimage (hX.prodMk hY)).inter
      (measurableSet_lt (hr.comp hX) hY.fst))
  have hB : MeasurableSet
      {ω | X ω ∈ U ∧ (Y ω).1 ∈ Icc (r (X ω)-1) (r (X ω)-1/2) ∧ M+1 < (Y ω).2} :=
    (hU.preimage hX).inter (((measurableSet_le ((hr.comp hX).sub_const 1) hY.fst).inter
      (measurableSet_le hY.fst ((hr.comp hX).sub_const (1/2)))).inter
        (measurableSet_lt measurable_const hY.snd))
  have heF : (fun ω => if X ω ∈ U then F (X ω,Y ω) else 0) =
      fun ω => if ω ∈ {ω | X ω ∈ U ∧ (Y ω).1 ∈ marginTargetSet Eb (v (X ω)) p q ∧
        r (X ω) < (Y ω).1} then (1 : ℝ) else 0 := by
    funext ω
    dsimp only [F, Set.mem_ofPred_eq]
    split_ifs <;> tauto
  have heG : (fun ω => if X ω ∈ U then G (X ω,Y ω) else 0) =
      fun ω => if ω ∈ {ω | X ω ∈ U ∧ (Y ω).1 ∈ Icc (r (X ω)-1) (r (X ω)-1/2) ∧ M+1 < (Y ω).2}
        then (1 : ℝ) else 0 := by
    funext ω
    dsimp only [G, Set.mem_ofPred_eq]
    split_ifs <;> tauto
  have hFL := (congrArg (fun f : Ω → ℝ => ∫ ω, f ω ∂μ) heF).trans
    (integral_if_one_eq_measureReal hA)
  have hGL := (congrArg (fun f : Ω → ℝ => ∫ ω, f ω ∂μ) heG).trans
    (integral_if_one_eq_measureReal hB)
  rw [hFL, hGL, zero_mul, add_zero] at hc
  exact hc

theorem gaussianReal_Iio_real_pos {t : ℝ} (ht : t ≤ 0) :
    0 < (gaussianReal 0 1).real (Iio t) := by
  have hl := gaussianReal_Ioc_density_lower_below (a := t-1) (b := t-1/2) (by linarith)
    (by linarith)
  have hsub : gaussianReal 0 1 (Ioc (t-1) (t-1/2)) ≤ gaussianReal 0 1 (Iio t) := by
    refine measure_mono (fun z hz => ?_)
    exact mem_Iio.mpr (lt_of_le_of_lt hz.2 (by linarith))
  have hpos : 0 < (1/2)*gaussianPDFReal 0 1 (t-1) := by
    have := gaussianPDFReal_pos 0 1 (t-1) (by norm_num)
    linarith
  have hstep : ENNReal.ofReal ((1/2)*gaussianPDFReal 0 1 (t-1)) ≤ gaussianReal 0 1 (Iio t) := by
    refine le_trans ?_ (hl.trans hsub)
    exact ENNReal.ofReal_le_ofReal (by nlinarith [gaussianPDFReal_nonneg (0 : ℝ) 1 (t-1)])
  have h := ENNReal.toReal_mono (measure_ne_top (gaussianReal 0 1) _) hstep
  rw [ENNReal.toReal_ofReal hpos.le] at h
  exact lt_of_lt_of_le hpos h

/-- One-step charging of the output-margin target against the actual lower
rejection event. -/
theorem independent_gaussian_margin_one_step_charge_below {Ω α : Type*}
    [MeasurableSpace Ω] [MeasurableSpace α] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → α} {Z : Ω → ℝ} (hX : Measurable X) (hZ : Measurable Z)
    (hi : IndepFun X Z μ) (hlaw : μ.map Z = gaussianReal 0 1)
    {U : Set α} (hU : MeasurableSet U) {r v : α → ℝ} (hr : Measurable r) (hv : Measurable v)
    {Eb p q : ℝ} (hpq : p ≤ q)
    (hsmall : ∀ x ∈ U, -1 ≤ r x) :
    μ.real {ω | X ω ∈ U ∧ Z ω ∈ marginTargetSet Eb (v (X ω)) p q ∧ Z ω < r (X ω)} ≤
      2*marginAntiConcentrationConstant*(q-p)*μ.real {ω | X ω ∈ U ∧ Z ω < r (X ω)} := by
  let F (w : α × ℝ) : ℝ :=
    if w.2 ∈ marginTargetSet Eb (v w.1) p q ∧ w.2 < r w.1 then 1 else 0
  let G (w : α × ℝ) : ℝ := if w.2 < r w.1 then 1 else 0
  have htarget : MeasurableSet {w : α × ℝ | w.2 ∈ marginTargetSet Eb (v w.1) p q} := by
    have hmap : Measurable (fun w : α × ℝ => Eb-|v w.1+w.2|) :=
      measurable_const.sub (((hv.comp measurable_fst).add measurable_snd).abs)
    exact measurableSet_Icc.preimage hmap
  have hFm : Measurable F := measurable_const.ite
    (htarget.inter (measurableSet_lt measurable_snd (hr.comp measurable_fst))) measurable_const
  have hGm : Measurable G := measurable_const.ite
    (measurableSet_lt measurable_snd (hr.comp measurable_fst)) measurable_const
  have hFb : ∀ w, |F w| ≤ 1 := by intro w; dsimp only [F]; split_ifs <;> norm_num
  have hGb : ∀ w, |G w| ≤ 1 := by intro w; dsimp only [G]; split_ifs <;> norm_num
  have hsection : ∀ x ∈ U, (∫ z, F (x,z) ∂μ.map Z) ≤
      2*marginAntiConcentrationConstant*(q-p)*(∫ z, G (x,z) ∂μ.map Z)+0 := by
    intro x hx
    rw [hlaw]
    have hFset : (fun z => F (x,z)) =
        fun z => if z ∈ marginTargetSet Eb (v x) p q ∩ Iio (r x) then (1 : ℝ) else 0 := by
      funext z
      dsimp only [F]
      congr 1
    have hGset : (fun z => G (x,z)) = fun z => if z ∈ Iio (r x) then (1 : ℝ) else 0 := by
      funext z
      dsimp only [G]
      congr 1
    have hFv : (∫ z, F (x,z) ∂gaussianReal 0 1) =
        (gaussianReal 0 1).real (marginTargetSet Eb (v x) p q ∩ Iio (r x)) :=
      (congrArg (fun f : ℝ → ℝ => ∫ z, f z ∂gaussianReal 0 1) hFset).trans
        (integral_if_one_eq_measureReal
          ((measurableSet_marginTargetSet Eb (v x) p q).inter measurableSet_Iio))
    have hGv : (∫ z, G (x,z) ∂gaussianReal 0 1) = (gaussianReal 0 1).real (Iio (r x)) :=
      (congrArg (fun f : ℝ → ℝ => ∫ z, f z ∂gaussianReal 0 1) hGset).trans
        (integral_if_one_eq_measureReal measurableSet_Iio)
    rw [hFv, hGv, add_zero]
    have hbound := gaussianReal_marginTarget_small_threshold_below (Eb := Eb) (v := v x) hpq
      (hsmall x hx)
    have h := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (measure_ne_top _ _)) hbound
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal
      (by nlinarith [marginAntiConcentrationConstant_pos, sub_nonneg.mpr hpq] :
        (0 : ℝ) ≤ 2*marginAntiConcentrationConstant*(q-p))] at h
  have hc := IndepFun.integral_state_guard_le hX.aemeasurable hZ.aemeasurable hi hU hFm hGm
    (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 1) hFb hGb hsection
  have hA : MeasurableSet {ω | X ω ∈ U ∧ Z ω ∈ marginTargetSet Eb (v (X ω)) p q ∧ Z ω < r (X ω)} :=
    (hU.preimage hX).inter ((htarget.preimage (hX.prodMk hZ)).inter
      (measurableSet_lt hZ (hr.comp hX)))
  have hB : MeasurableSet {ω | X ω ∈ U ∧ Z ω < r (X ω)} :=
    (hU.preimage hX).inter (measurableSet_lt hZ (hr.comp hX))
  have heF : (fun ω => if X ω ∈ U then F (X ω,Z ω) else 0) =
      fun ω => if ω ∈ {ω | X ω ∈ U ∧ Z ω ∈ marginTargetSet Eb (v (X ω)) p q ∧ Z ω < r (X ω)}
        then (1 : ℝ) else 0 := by
    funext ω
    dsimp only [F, Set.mem_ofPred_eq]
    split_ifs <;> tauto
  have heG : (fun ω => if X ω ∈ U then G (X ω,Z ω) else 0) =
      fun ω => if ω ∈ {ω | X ω ∈ U ∧ Z ω < r (X ω)} then (1 : ℝ) else 0 := by
    funext ω
    dsimp only [G, Set.mem_ofPred_eq]
    split_ifs <;> tauto
  have hFL := (congrArg (fun f : Ω → ℝ => ∫ ω, f ω ∂μ) heF).trans
    (integral_if_one_eq_measureReal hA)
  have hGL := (congrArg (fun f : Ω → ℝ => ∫ ω, f ω ∂μ) heG).trans
    (integral_if_one_eq_measureReal hB)
  rw [hFL, hGL, zero_mul, add_zero] at hc
  exact hc

/-- Two-step charging of the output-margin target against the actual lower
proxy acceptance followed by a lower rejection. -/
theorem independent_gaussian_margin_two_step_charge_below {Ω α : Type*}
    [MeasurableSpace Ω] [MeasurableSpace α] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → α} {Y : Ω → ℝ × ℝ} (hX : Measurable X) (hY : Measurable Y)
    (hi : IndepFun X Y μ) (hlaw : μ.map Y = (gaussianReal 0 1).prod (gaussianReal 0 1))
    {U : Set α} (hU : MeasurableSet U) {r v : α → ℝ} (hr : Measurable r) (hv : Measurable v)
    {Eb p q M : ℝ} (hpq : p ≤ q) (hM : 0 ≤ M+1)
    (hlarge : ∀ x ∈ U, r x < -1) :
    μ.real {ω | X ω ∈ U ∧ (Y ω).1 ∈ marginTargetSet Eb (v (X ω)) p q ∧ (Y ω).1 < r (X ω)} ≤
      4*(q-p)/(gaussianReal 0 1).real (Iio (-(M+1)))*
        μ.real {ω | X ω ∈ U ∧ (Y ω).1 ∈ Icc (r (X ω)+1/2) (r (X ω)+1) ∧ (Y ω).2 < -(M+1)} := by
  set β : ℝ := (gaussianReal 0 1).real (Iio (-(M+1))) with hβ
  have hβpos : 0 < β := gaussianReal_Iio_real_pos (by linarith)
  let F (w : α × (ℝ × ℝ)) : ℝ :=
    if w.2.1 ∈ marginTargetSet Eb (v w.1) p q ∧ w.2.1 < r w.1 then 1 else 0
  let G (w : α × (ℝ × ℝ)) : ℝ :=
    if w.2.1 ∈ Icc (r w.1+1/2) (r w.1+1) ∧ w.2.2 < -(M+1) then 1 else 0
  have htarget : MeasurableSet {w : α × (ℝ × ℝ) | w.2.1 ∈ marginTargetSet Eb (v w.1) p q} := by
    have hmap : Measurable (fun w : α × (ℝ × ℝ) => Eb-|v w.1+w.2.1|) :=
      measurable_const.sub (((hv.comp measurable_fst).add measurable_snd.fst).abs)
    exact measurableSet_Icc.preimage hmap
  have hFm : Measurable F := measurable_const.ite
    (htarget.inter (measurableSet_lt measurable_snd.fst (hr.comp measurable_fst))) measurable_const
  have hGm : Measurable G := measurable_const.ite
    (((measurableSet_le ((hr.comp measurable_fst).add_const (1/2)) measurable_snd.fst).inter
      (measurableSet_le measurable_snd.fst ((hr.comp measurable_fst).add_const 1))).inter
        (measurableSet_lt measurable_snd.snd measurable_const)) measurable_const
  have hFb : ∀ w, |F w| ≤ 1 := by intro w; dsimp only [F]; split_ifs <;> norm_num
  have hGb : ∀ w, |G w| ≤ 1 := by intro w; dsimp only [G]; split_ifs <;> norm_num
  have hsection : ∀ x ∈ U, (∫ y, F (x,y) ∂μ.map Y) ≤
      4*(q-p)/β*(∫ y, G (x,y) ∂μ.map Y)+0 := by
    intro x hx
    rw [hlaw]
    have hFset : (fun y : ℝ × ℝ => F (x,y)) =
        fun y => if y ∈ (marginTargetSet Eb (v x) p q ∩ Iio (r x)) ×ˢ (Set.univ : Set ℝ)
          then (1 : ℝ) else 0 := by
      funext y
      dsimp only [F]
      congr 1
      simp only [Set.mem_prod, mem_inter_iff, mem_Iio, Set.mem_univ, and_true]
    have hGset : (fun y : ℝ × ℝ => G (x,y)) =
        fun y => if y ∈ Icc (r x+1/2) (r x+1) ×ˢ Iio (-(M+1)) then (1 : ℝ) else 0 := rfl
    have hFv : (∫ y, F (x,y) ∂(gaussianReal 0 1).prod (gaussianReal 0 1)) =
        (gaussianReal 0 1).real (marginTargetSet Eb (v x) p q ∩ Iio (r x)) := by
      calc
        _ = ((gaussianReal 0 1).prod (gaussianReal 0 1)).real
              ((marginTargetSet Eb (v x) p q ∩ Iio (r x)) ×ˢ (Set.univ : Set ℝ)) :=
          (congrArg (fun f : ℝ × ℝ → ℝ => ∫ y, f y ∂(gaussianReal 0 1).prod (gaussianReal 0 1))
            hFset).trans (integral_if_one_eq_measureReal
              (((measurableSet_marginTargetSet Eb (v x) p q).inter
                measurableSet_Iio).prod MeasurableSet.univ))
        _ = _ := by rw [measureReal_prod_prod, probReal_univ, mul_one]
    have hGv : (∫ y, G (x,y) ∂(gaussianReal 0 1).prod (gaussianReal 0 1)) =
        (gaussianReal 0 1).real (Icc (r x+1/2) (r x+1))*β := by
      calc
        _ = ((gaussianReal 0 1).prod (gaussianReal 0 1)).real
              (Icc (r x+1/2) (r x+1) ×ˢ Iio (-(M+1))) :=
          (congrArg (fun f : ℝ × ℝ → ℝ => ∫ y, f y ∂(gaussianReal 0 1).prod (gaussianReal 0 1))
            hGset).trans (integral_if_one_eq_measureReal (measurableSet_Icc.prod measurableSet_Iio))
        _ = _ := measureReal_prod_prod _ _
    rw [hFv, hGv, add_zero]
    have hbound := gaussianReal_marginTarget_large_threshold_below (Eb := Eb) (v := v x) hpq
      (hlarge x hx)
    have h := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (measure_ne_top _ _)) hbound
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal
      (by nlinarith [sub_nonneg.mpr hpq] : (0 : ℝ) ≤ 4*(q-p))] at h
    have hgoal : 4*(q-p)/β*((gaussianReal 0 1).real (Icc (r x+1/2) (r x+1))*β) =
        4*(q-p)*(gaussianReal 0 1).real (Icc (r x+1/2) (r x+1)) := by
      field_simp
    rw [hgoal]
    exact h
  have hc := IndepFun.integral_state_guard_le hX.aemeasurable hY.aemeasurable hi hU hFm hGm
    (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 1) hFb hGb hsection
  have hA : MeasurableSet
      {ω | X ω ∈ U ∧ (Y ω).1 ∈ marginTargetSet Eb (v (X ω)) p q ∧ (Y ω).1 < r (X ω)} :=
    (hU.preimage hX).inter ((htarget.preimage (hX.prodMk hY)).inter
      (measurableSet_lt hY.fst (hr.comp hX)))
  have hB : MeasurableSet
      {ω | X ω ∈ U ∧ (Y ω).1 ∈ Icc (r (X ω)+1/2) (r (X ω)+1) ∧ (Y ω).2 < -(M+1)} :=
    (hU.preimage hX).inter (((measurableSet_le ((hr.comp hX).add_const (1/2)) hY.fst).inter
      (measurableSet_le hY.fst ((hr.comp hX).add_const 1))).inter
        (measurableSet_lt hY.snd measurable_const))
  have heF : (fun ω => if X ω ∈ U then F (X ω,Y ω) else 0) =
      fun ω => if ω ∈ {ω | X ω ∈ U ∧ (Y ω).1 ∈ marginTargetSet Eb (v (X ω)) p q ∧
        (Y ω).1 < r (X ω)} then (1 : ℝ) else 0 := by
    funext ω
    dsimp only [F, Set.mem_ofPred_eq]
    split_ifs <;> tauto
  have heG : (fun ω => if X ω ∈ U then G (X ω,Y ω) else 0) =
      fun ω => if ω ∈ {ω | X ω ∈ U ∧ (Y ω).1 ∈ Icc (r (X ω)+1/2) (r (X ω)+1) ∧ (Y ω).2 < -(M+1)}
        then (1 : ℝ) else 0 := by
    funext ω
    dsimp only [G, Set.mem_ofPred_eq]
    split_ifs <;> tauto
  have hFL := (congrArg (fun f : Ω → ℝ => ∫ ω, f ω ∂μ) heF).trans
    (integral_if_one_eq_measureReal hA)
  have hGL := (congrArg (fun f : Ω → ℝ => ∫ ω, f ω ∂μ) heG).trans
    (integral_if_one_eq_measureReal hB)
  rw [hFL, hGL, zero_mul, add_zero] at hc
  exact hc

end SwingRepair
