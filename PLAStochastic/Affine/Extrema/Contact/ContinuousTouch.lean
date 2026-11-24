import PLAStochastic.Affine.Extrema.Contact.Geometry

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

/-- Evaluation of a continuous real path at nonnegative times. -/
def continuousPathProcess (t : ℝ≥0) (f : C(ℝ,ℝ)) : ℝ := f t

/-- Every interval contact sublevel is a continuous prefix-norm inequality,
including nonpositive interval widths. -/
theorem continuousPathTouch_le_iff (f : C(ℝ,ℝ)) (x r : ℝ) (U : ℝ≥0) :
    intervalTouchTime continuousPathProcess x r f ≤ (U : ℝ≥0∞) ↔
      r/2 ≤ ‖unitPath f U + ContinuousMap.const _ (x-r/2)‖ := by
  by_cases hr : 0 < r
  · rw [intervalTouchTime_repr f (fun _ => rfl),
      pathClosedHit_eq_firstReach _ (by positivity),
      firstReach_le_iff (monotone_prefixNorm _) (continuous_prefixNorm _)]
    rfl
  · have hz : intervalTouchTime continuousPathProcess x r f=0 := by
      apply le_antisymm _ bot_le
      apply intervalTouchTime_le_of_outside (t := 0)
      intro h
      exact hr (h.1.trans h.2)
    rw [hz]
    exact iff_of_true (by positivity)
      ((div_nonpos_of_nonpos_of_nonneg (le_of_not_gt hr) (by norm_num)).trans (norm_nonneg _))

/-- Joint measurability in both endpoints and the entire continuous path. -/
theorem measurable_continuousPathTouch_comp {α : Type*} [MeasurableSpace α]
    {f : α → C(ℝ,ℝ)} {x r : α → ℝ}
    (hf : Measurable f) (hx : Measurable x) (hr : Measurable r) :
    Measurable (fun a => intervalTouchTime continuousPathProcess (x a) (r a) (f a)) := by
  apply measurable_of_Iic
  intro u
  by_cases hu : u=⊤
  · simp only [hu,Iic_top,preimage_univ,MeasurableSet.univ]
  · obtain ⟨U,hU⟩ := WithTop.ne_top_iff_exists.mp hu
    have hU' : (U : ℝ≥0∞)=u := hU
    rw [←hU']
    have he : (fun a => intervalTouchTime continuousPathProcess (x a) (r a) (f a)) ⁻¹'
        Iic (U : ℝ≥0∞) = {a | r a/2 ≤ ‖unitPath (f a) U+ContinuousMap.const _ (x a-r a/2)‖} := by
      ext a
      exact continuousPathTouch_le_iff (f a) (x a) (r a) U
    rw [he]
    apply measurableSet_le (hr.div_const 2)
    exact (((continuous_unitPath_in_path U).measurable.comp hf).add
      ((show Continuous (fun v : ℝ => ContinuousMap.const (Icc (0 : ℝ) 1) v) by
        apply ContinuousMap.continuous_of_continuous_uncurry
        exact continuous_fst).measurable.comp (hx.sub (hr.div_const 2)))).norm

theorem measurable_continuousPathClock_comp {α : Type*} [MeasurableSpace α]
    {f : α → C(ℝ,ℝ)} {x r : α → ℝ}
    (hf : Measurable f) (hx : Measurable x) (hr : Measurable r) :
    Measurable (fun a => intervalTouchClock continuousPathProcess (x a) (r a) (f a)) :=
  (WithTop.measurable_untopD 0).comp (measurable_continuousPathTouch_comp hf hx hr)

/-- Restart the entire continuous path, with a variable real restart time. -/
def restartContinuousPath (f : C(ℝ,ℝ)) (s : ℝ) : C(ℝ,ℝ) :=
  ⟨fun t => f (s+t)-f s, (f.continuous.comp (continuous_const.add continuous_id)).sub continuous_const⟩

theorem continuous_restartContinuousPath :
    Continuous (fun p : C(ℝ,ℝ) × ℝ => restartContinuousPath p.1 p.2) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact (continuous_eval.comp ((continuous_fst.comp continuous_fst).prodMk
    ((continuous_snd.comp continuous_fst).add continuous_snd))).sub
    (continuous_eval.comp ((continuous_fst.comp continuous_fst).prodMk
      (continuous_snd.comp continuous_fst)))

theorem restartContinuousPath_touch_apply (f : C(ℝ,ℝ)) (x r : ℝ) (t : ℝ≥0) :
    restartContinuousPath f (intervalTouchClock continuousPathProcess x r f) t =
      brownianRestartAt continuousPathProcess (intervalTouchTime continuousPathProcess x r) t f := by
  rfl

/-- All parameters in the true two-contact layer may vary measurably together. -/
theorem measurableSet_continuousPath_orderedContactLayer {α : Type*} [MeasurableSpace α]
    {f : α → C(ℝ,ℝ)} {x r e d : α → ℝ}
    (hf : Measurable f) (hx : Measurable x) (hr : Measurable r)
    (he : Measurable e) (hd : Measurable d) (T : ℝ≥0)
    {S D₁ D₂ : Set ℝ} (hS : MeasurableSet S) (hD₁ : MeasurableSet D₁)
    (hD₂ : MeasurableSet D₂) :
    MeasurableSet {a | orderedContactLayerEvent continuousPathProcess
      (x a) (r a) (e a) (d a) T S D₁ D₂ (f a)} := by
  let s : α → ℝ≥0 := fun a => intervalTouchClock continuousPathProcess (x a) (r a) (f a)
  let F : α → C(ℝ,ℝ) := fun a => restartContinuousPath (f a) (s a)
  have hs : Measurable s := measurable_continuousPathClock_comp hf hx hr
  have hF : Measurable F := continuous_restartContinuousPath.measurable.comp
    (hf.prodMk hs.coe_nnreal_real)
  have hU : Measurable (fun a => T-s a) := measurable_const.sub hs
  have heval : Measurable (fun a => F a (T-s a : ℝ≥0)) :=
    continuous_eval.measurable.comp (hF.prodMk hU.coe_nnreal_real)
  have hendpoint : Measurable (fun a => x a+f a (s a)) :=
    hx.add (continuous_eval.measurable.comp (hf.prodMk hs.coe_nnreal_real))
  have hτ := measurable_continuousPathTouch_comp hF he (hr.add he)
  have hτ' := measurable_continuousPathTouch_comp hF he ((hr.add he).add hd)
  have hv := measurable_continuousPathClock_comp hF he (hr.add he)
  have hres : MeasurableSet {a | (s a : ℝ) ∈ D₁ ∩ Ioo (0 : ℝ) (T : ℝ) ∧
      x a+f a (s a)=0 ∧
      ((T-s a : ℝ≥0) : ℝ≥0∞) < intervalTouchTime continuousPathProcess (e a) (r a+e a+d a) (F a) ∧
      intervalTouchTime continuousPathProcess (e a) (r a+e a) (F a) ≤ (T-s a : ℝ≥0) ∧
      F a (T-s a : ℝ≥0) ∈ S ∧
      (intervalTouchClock continuousPathProcess (e a) (r a+e a) (F a) : ℝ) ∈ D₂} :=
    ((hD₁.inter measurableSet_Ioo).preimage hs.coe_nnreal_real).inter
      ((measurableSet_eq_fun hendpoint measurable_const).inter
        ((measurableSet_lt hU.coe_nnreal_ennreal hτ').inter
          ((measurableSet_le hτ hU.coe_nnreal_ennreal).inter
            ((hS.preimage heval).inter (hD₂.preimage hv.coe_nnreal_real)))))
  convert hres using 1
  ext a
  have ht (R : ℝ) : intervalTouchTime continuousPathProcess (e a) R (F a) =
      intervalTouchTime (brownianRestartAt continuousPathProcess
        (intervalTouchTime continuousPathProcess (x a) (r a))) (e a) R (f a) := by
    rfl
  simp only [orderedContactLayerEvent,intervalTouchEndpoint,continuousPathProcess,
    mem_ofPred_eq,mem_preimage]
  change _ ↔ _ ∧ _ ∧ _
  simp only [ht,intervalTouchClock]
  simp only [F,s,restartContinuousPath_touch_apply,add_sub_cancel_left,and_assoc]
  rfl

end BrownianAffine
