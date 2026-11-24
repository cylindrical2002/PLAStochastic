import PLAStochastic.Affine.Process.IntervalExit.JointLaw

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators NNReal ENNReal
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- The continuous version admits genuinely measurable stopped observations. -/
theorem measurable_continuousBrownian_stoppedPair (hB : IsBrownianReal B μ)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime (augmentedBrownianFiltration hB.toIsPreBrownianReal) τ) :
    Measurable[hτ.measurableSpace]
      (fun ω => ((((τ ω).untopA : ℝ≥0) : ℝ),continuousBrownianPath hB ω (((τ ω).untopA : ℝ≥0) : ℝ))) := by
  have ha : StronglyAdapted (augmentedBrownianFiltration hB.toIsPreBrownianReal)
      (fun t ω => continuousBrownianPath hB ω t) :=
    fun t => (adapted_continuousBrownian_coordinate hB t).stronglyMeasurable
  have hp := ha.isStronglyProgressive_of_continuous (fun ω =>
    (continuousBrownianPath hB ω).continuous.comp NNReal.continuous_coe)
  have hv := measurable_stoppedValue hp hτ
  exact (hτ.measurable.untopA).coe_nnreal_real.prodMk hv

/-- The whole future coordinate process is independent of the stopped time and location. -/
theorem brownianRestartAt_indep_stoppedPair (hB : IsBrownianReal B μ)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime (augmentedBrownianFiltration hB.toIsPreBrownianReal) τ)
    (hf : ∀ᵐ ω ∂μ, τ ω ≠ ⊤) :
    IndepFun (fun ω t => brownianRestartAt B τ t ω)
      (fun ω => ((((τ ω).untopA : ℝ≥0) : ℝ),continuousBrownianPath hB ω (((τ ω).untopA : ℝ≥0) : ℝ))) μ := by
  have hi := Augmented.brownianRestartAt_indep_stopped hB hτ hf
  have hm := measurable_continuousBrownian_stoppedPair hB hτ
  apply indepFun_iff_measure_inter_preimage_eq_mul.mpr
  intro S D hS hD
  exact (Indep_iff _ _ μ).mp hi _ _ ⟨S,hS,rfl⟩ (hm hD)

/-- The continuous future path, with its uniform-topology Borel structure, is independent
of the stopped pair. This supports later tests with a random remaining duration. -/
theorem brownianRestartAt_unitPath_indep_stoppedPair (hB : IsBrownianReal B μ)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime (augmentedBrownianFiltration hB.toIsPreBrownianReal) τ)
    (hf : ∀ᵐ ω ∂μ, τ ω ≠ ⊤) (T : ℝ≥0) :
    IndepFun (fun ω => unitPath (processPath (brownianRestartAt B τ) ω) T)
      (fun ω => ((((τ ω).untopA : ℝ≥0) : ℝ),continuousBrownianPath hB ω (((τ ω).untopA : ℝ≥0) : ℝ))) μ := by
  let J : Ω → ℝ × ℝ := fun ω => ((((τ ω).untopA : ℝ≥0) : ℝ),continuousBrownianPath hB ω (((τ ω).untopA : ℝ≥0) : ℝ))
  have hi := brownianRestartAt_indep_stoppedPair hB hτ hf
  have hs := hi.comp (φ := fun f : ℝ≥0 → ℝ => fun s : ErrorSample => f (T*errorSampleTime s))
    (ψ := id) (by fun_prop) measurable_id
  have hBR := Augmented.isBrownianReal_brownianRestartAt hB hτ hf
  have hsp : IndepFun (fun ω => pathObservations (unitPath (processPath (brownianRestartAt B τ) ω) T)) J μ := by
    apply hs.congr _ EventuallyEq.rfl
    filter_upwards [hBR.cont] with ω hc
    funext s
    exact (unitPath_processPath_sample hc T s).symm
  obtain ⟨F,hF,hFeq⟩ := measurableEmbedding_pathObservations.exists_measurable_extend
    (g := id) measurable_id (fun _ => ⟨(0 : Path 1)⟩)
  have h := hsp.comp hF measurable_id
  simpa only [Function.comp_def,id_eq,show ∀ f, F (pathObservations f)=f from
    fun f => congrFun hFeq f] using h

/-- The genuine future path after first contact is independent of the actual exit pair. -/
theorem intervalTouch_futurePath_indep_exitPair (hB : IsBrownianReal B μ)
    {r x : ℝ} (hr : 0 < r) (T : ℝ≥0) :
    IndepFun (fun ω => unitPath (processPath (brownianRestartAt B (intervalTouchTime B x r)) ω) T)
      (fun ω => ((intervalTouchClock B x r ω : ℝ),intervalTouchEndpoint B x r ω)) μ := by
  have hτ := brownianIntervalTouch_isStoppingTime hB x hr
  have hf : ∀ᵐ ω ∂μ, brownianIntervalTouch hB x r ω ≠ ⊤ := by
    filter_upwards [brownianIntervalTouch_ae_eq hB x r,intervalTouchTime_ae_ne_top hB x r] with ω he hf
    rwa [he]
  have hi := (brownianRestartAt_unitPath_indep_stoppedPair hB hτ hf T).comp
    (φ := id) (ψ := fun p : ℝ × ℝ => (p.1,x+p.2)) measurable_id (by fun_prop)
  apply hi.congr
  · have hBR := Augmented.isBrownianReal_brownianRestartAt hB hτ hf
    have hAR := isBrownianReal_restart_intervalTouch hB x hr
    filter_upwards [hBR.cont,hAR.cont,brownianIntervalTouch_ae_eq hB x r] with ω hc ha he
    apply DFunLike.ext
    intro s
    dsimp only [Function.comp_def,id_eq]
    rw [unitPath_processPath_apply hc,unitPath_processPath_apply ha]
    simp only [brownianRestartAt,brownianRestart,he]
  · filter_upwards [brownianIntervalTouch_ae_eq hB x r,intervalTouchTime_ae_ne_top hB x r,
      continuousBrownianPath_all_times_ae_eq hB] with ω he hf hp
    obtain ⟨t,ht⟩ := WithTop.ne_top_iff_exists.mp hf
    have hτt : brownianIntervalTouch hB x r ω = t := he.trans ht.symm
    have hct : intervalTouchClock B x r ω = t := by rw [intervalTouchClock,← ht]; rfl
    dsimp only [Function.comp_def,id_eq]
    have hua : (brownianIntervalTouch hB x r ω).untopA = t := by rw [hτt]; rfl
    dsimp only [intervalTouchEndpoint]
    rw [hua,hp t,hct]

/-- Independence identifies the full joint law needed for a random remaining-time test. -/
theorem intervalTouch_futurePath_joint_law (hB : IsBrownianReal B μ)
    {r x : ℝ} (hr : 0 < r) (hx : x ∈ Ioo 0 r) (T : ℝ≥0) :
    μ.map (fun ω => (((intervalTouchClock B x r ω : ℝ),intervalTouchEndpoint B x r ω),
      unitPath (processPath (brownianRestartAt B (intervalTouchTime B x r)) ω) T)) =
      (intervalExitJointMeasure B μ x r).prod
        (μ.map (fun ω => unitPath (processPath (brownianRestartAt B (intervalTouchTime B x r)) ω) T)) := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  exact IndepFun.map_prod_eq_prod_map_map
    (((intervalTouchClock_aemeasurable hB hr x).coe_nnreal_real).prodMk (intervalTouchEndpoint_aemeasurable hB hr hx))
    (aemeasurable_brownianUnitPath (isBrownianReal_restart_intervalTouch hB x hr) T)
    (intervalTouch_futurePath_indep_exitPair hB hr T).symm

theorem intervalTouch_futurePath_joint_boundary_density (hB : IsBrownianReal B μ)
    {r x : ℝ} (hr : 0 < r) (hx : x ∈ Ioo 0 r) (T : ℝ≥0) :
    μ.map (fun ω => (((intervalTouchClock B x r ω : ℝ),intervalTouchEndpoint B x r ω),
      unitPath (processPath (brownianRestartAt B (intervalTouchTime B x r)) ω) T)) =
      ((positiveTimeDensity (fun t => heatBoundaryLeft r t x/2)).map (fun t => (t,0)) +
        (positiveTimeDensity (fun t => heatBoundaryRight r t x/2)).map (fun t => (t,r))).prod
        (μ.map (fun ω => unitPath (processPath (brownianRestartAt B (intervalTouchTime B x r)) ω) T)) := by
  rw [intervalTouch_futurePath_joint_law hB hr hx T,intervalExitJointMeasure_eq_boundary_density hB hr hx]

/-- The independent future path reconstructs the actual path after the true contact time. -/
theorem intervalTouch_futurePath_reconstruction_ae (hB : IsBrownianReal B μ)
    {r : ℝ} (hr : 0 < r) (x : ℝ) (T : ℝ≥0) :
    ∀ᵐ ω ∂μ, ∀ u : Icc (0 : ℝ) 1,
      x+B (intervalTouchClock B x r ω+(T*⟨(u : ℝ),u.property.1⟩ : ℝ≥0)) ω =
        intervalTouchEndpoint B x r ω+
          unitPath (processPath (brownianRestartAt B (intervalTouchTime B x r)) ω) T u := by
  filter_upwards [(isBrownianReal_restart_intervalTouch hB x hr).cont] with ω hc
  intro u
  rw [unitPath_processPath_apply hc]
  dsimp only [intervalTouchEndpoint,intervalTouchClock,brownianRestartAt,brownianRestart]
  ring

end BrownianAffine
