import PLAStochastic.Affine.Process.IntervalExit.RestartPath

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B C : ℝ≥0 → Ω → ℝ}

/-- Brownian coordinate laws determine the law in the uniform topology. -/
theorem identDistrib_brownianUnitPath (hB : IsBrownianReal B μ)
    (hC : IsBrownianReal C μ) (T : ℝ≥0) :
    IdentDistrib (fun ω => unitPath (processPath B ω) T)
      (fun ω => unitPath (processPath C ω) T) μ μ := by
  have hs := identDistrib_countable_observations hB.toIsPreBrownianReal
    hC.toIsPreBrownianReal (fun s : ErrorSample => T*errorSampleTime s)
  have hsp : IdentDistrib (fun ω => pathObservations (unitPath (processPath B ω) T))
      (fun ω => pathObservations (unitPath (processPath C ω) T)) μ μ := by
    refine (IdentDistrib.of_ae_eq hs.aemeasurable_fst ?_).symm.trans
      (hs.trans (IdentDistrib.of_ae_eq hs.aemeasurable_snd ?_))
    · filter_upwards [hB.cont] with ω hc
      funext s
      exact (unitPath_processPath_sample hc T s).symm
    · filter_upwards [hC.cont] with ω hc
      funext s
      exact (unitPath_processPath_sample hc T s).symm
  obtain ⟨F,hF,hFeq⟩ := measurableEmbedding_pathObservations.exists_measurable_extend
    (g := id) measurable_id (fun _ => ⟨(0 : Path 1)⟩)
  have h := hsp.comp hF
  simpa only [Function.comp_def,id_eq,show ∀ f, F (pathObservations f)=f from
    fun f => congrFun hFeq f] using h

/-- The future-path factor in the true exit law is the original Brownian path law. -/
theorem intervalTouch_futurePath_joint_original_law (hB : IsBrownianReal B μ)
    {r x : ℝ} (hr : 0 < r) (hx : x ∈ Ioo 0 r) (T : ℝ≥0) :
    μ.map (fun ω => (((intervalTouchClock B x r ω : ℝ),intervalTouchEndpoint B x r ω),
      unitPath (processPath (brownianRestartAt B (intervalTouchTime B x r)) ω) T)) =
      (intervalExitJointMeasure B μ x r).prod
        (μ.map (fun ω => unitPath (processPath B ω) T)) := by
  rw [intervalTouch_futurePath_joint_law hB hr hx T,
    (identDistrib_brownianUnitPath (isBrownianReal_restart_intervalTouch hB x hr) hB T).map_eq]

/-- Nonnegative tests can depend jointly on the true exit pair and the full future path. -/
theorem lintegral_intervalTouch_futurePath (hB : IsBrownianReal B μ)
    {r x : ℝ} (hr : 0 < r) (hx : x ∈ Ioo 0 r) (T : ℝ≥0)
    {G : (ℝ × ℝ) × Path 1 → ℝ≥0∞} (hG : Measurable G) :
    (∫⁻ ω, G (((intervalTouchClock B x r ω : ℝ),intervalTouchEndpoint B x r ω),
      unitPath (processPath (brownianRestartAt B (intervalTouchTime B x r)) ω) T) ∂μ) =
      ∫⁻ p, ∫⁻ ω, G (p,unitPath (processPath B ω) T) ∂μ ∂intervalExitJointMeasure B μ x r := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  have hmJ := ((intervalTouchClock_aemeasurable hB hr x).coe_nnreal_real).prodMk
    (intervalTouchEndpoint_aemeasurable hB hr hx)
  have hmP := aemeasurable_brownianUnitPath (isBrownianReal_restart_intervalTouch hB x hr) T
  rw [← lintegral_map' hG.aemeasurable (hmJ.prodMk hmP),
    intervalTouch_futurePath_joint_original_law hB hr hx T,lintegral_prod _ hG.aemeasurable]
  apply lintegral_congr
  intro p
  exact lintegral_map' (hG.comp (by fun_prop)).aemeasurable (aemeasurable_brownianUnitPath hB T)

/-- Actual exit observations admit integration against the two proved time densities. -/
theorem lintegral_intervalExitJointMeasure (hB : IsBrownianReal B μ)
    {r x : ℝ} (hr : 0 < r) (hx : x ∈ Ioo 0 r)
    {F : ℝ × ℝ → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ p, F p ∂intervalExitJointMeasure B μ x r) =
      (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (heatBoundaryLeft r t x/2)*F (t,0)) +
      (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (heatBoundaryRight r t x/2)*F (t,r)) := by
  rw [intervalExitJointMeasure_eq_boundary_density hB hr hx,lintegral_add_measure,
    lintegral_map hF (by fun_prop),lintegral_map hF (by fun_prop)]
  unfold positiveTimeDensity
  have hL : Measurable (fun t => ENNReal.ofReal (heatBoundaryLeft r t x/2)) :=
    (((measurable_heatBoundaryLeft r).comp (show Measurable (fun t : ℝ => (x,t)) by fun_prop)).div_const 2).ennreal_ofReal
  have hR : Measurable (fun t => ENNReal.ofReal (heatBoundaryRight r t x/2)) :=
    (((measurable_heatBoundaryRight r).comp (show Measurable (fun t : ℝ => (x,t)) by fun_prop)).div_const 2).ennreal_ofReal
  rw [lintegral_withDensity_eq_lintegral_mul _ hL
      (show Measurable (fun t => F (t,0)) from hF.comp (by fun_prop)),
    lintegral_withDensity_eq_lintegral_mul _ hR
      (show Measurable (fun t => F (t,r)) from hF.comp (by fun_prop))]
  rfl

/-- Strong Markov disintegration at the actual first contact, with both boundary densities. -/
theorem lintegral_intervalTouch_futurePath_boundary (hB : IsBrownianReal B μ)
    {r x : ℝ} (hr : 0 < r) (hx : x ∈ Ioo 0 r) (T : ℝ≥0)
    {G : (ℝ × ℝ) × Path 1 → ℝ≥0∞} (hG : Measurable G) :
    (∫⁻ ω, G (((intervalTouchClock B x r ω : ℝ),intervalTouchEndpoint B x r ω),
      unitPath (processPath (brownianRestartAt B (intervalTouchTime B x r)) ω) T) ∂μ) =
      (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (heatBoundaryLeft r t x/2)*
        ∫⁻ ω, G ((t,0),unitPath (processPath B ω) T) ∂μ) +
      (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (heatBoundaryRight r t x/2)*
        ∫⁻ ω, G ((t,r),unitPath (processPath B ω) T) ∂μ) := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  let P := μ.map (fun ω => unitPath (processPath B ω) T)
  have hm : Measurable (fun p => ∫⁻ f, G (p,f) ∂P) := hG.lintegral_prod_right'
  have he (p : ℝ × ℝ) : (∫⁻ f, G (p,f) ∂P) =
      ∫⁻ ω, G (p,unitPath (processPath B ω) T) ∂μ :=
    lintegral_map' (hG.comp (by fun_prop)).aemeasurable (aemeasurable_brownianUnitPath hB T)
  rw [lintegral_intervalTouch_futurePath hB hr hx T hG]
  simp_rw [← he]
  exact lintegral_intervalExitJointMeasure hB hr hx hm

end BrownianAffine
