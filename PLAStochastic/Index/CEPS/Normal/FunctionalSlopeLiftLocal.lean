import PLAStochastic.Index.CEPS.Normal.FunctionalSlopeLift
import PLAStochastic.ForMathlib.Analysis.Complex.CompactSpatialDerivLocal

/-! # Local compact-function lifts of actual removable divided differences -/

noncomputable section
open Complex Set Metric Filter Topology MeasureTheory
namespace PGM

variable {E K : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace K] [CompactSpace K]

theorem exists_eventually_spatial_ball_differentiableOn {f : E → ℂ → ℂ} {x : E}
    (hf : AnalyticAt ℂ (fun u : E × ℂ => f u.1 u.2) (x, 0)) :
    ∃ r > 0, ∀ᶠ p in 𝓝 x, DifferentiableOn ℂ (f p) (ball 0 r) := by
  obtain ⟨r, hr, hb⟩ := Metric.mem_nhds_iff.mp hf.eventually_analyticAt
  refine ⟨r, hr, ?_⟩
  filter_upwards [ball_mem_nhds x hr] with p hp
  intro z hz
  have hmem : (p, z) ∈ ball (x, (0 : ℂ)) r := by
    rw [mem_ball, dist_eq_norm, Prod.norm_def]
    exact max_lt (by simpa [mem_ball, dist_eq_norm] using hp)
      (by simpa [mem_ball, dist_eq_norm] using hz)
  exact (hb hmem).curry_right.differentiableAt.differentiableWithinAt

theorem second_dslope_eq_integral_of_differentiableOn_ball {f : ℂ → ℂ} {r : ℝ}
    (hf : DifferentiableOn ℂ f (ball 0 r)) {a b c : ℂ}
    (ha : a ∈ ball 0 r) (hb : b ∈ ball 0 r) (hc : c ∈ ball 0 r) :
    dslope (dslope f a) b c = ∫ t in (0 : ℝ)..1, ∫ s in (0 : ℝ)..1,
      (s : ℂ) * deriv (deriv f) (a + (s : ℂ) * (b + (t : ℂ) * (c - b) - a)) := by
  have hs : DifferentiableOn ℂ (dslope f a) (ball 0 r) :=
    (differentiableOn_dslope (isOpen_ball.mem_nhds ha)).mpr hf
  rw [cepsNormal_dslope_eq_integral hs hb hc]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le zero_le_one] at ht
  exact cepsNormal_deriv_dslope_eq_integral hf ha (cepsNormal_segment_mem_ball hb hc ht)

/-- Only a genuine local functional germ is needed. The scalar analytic germ pays
a common spatial ball, and the functional germ pays the actual second derivative
on all compact segments and their endpoint collisions. -/
theorem functionalSecondSlopeLift_eventually_apply_local
    {H : E × C(CompactSlopeSquare K, ℂ) → C(CompactSlopeSquare K, ℂ)}
    {f : E → ℂ → ℂ} {a b X : E → C(K, ℂ)} {x : E}
    (hf : AnalyticAt ℂ (fun u : E × ℂ => f u.1 u.2) (x, 0))
    (hH : AnalyticAt ℂ H (x, 0))
    (he : ∀ᶠ u in 𝓝 (x, (0 : C(CompactSlopeSquare K, ℂ))), ∀ q, H u q = f u.1 (u.2 q))
    (ha : AnalyticAt ℂ a x) (hb : AnalyticAt ℂ b x) (hX : AnalyticAt ℂ X x)
    (ha₀ : a x = 0) (hb₀ : b x = 0) (hX₀ : X x = 0) :
    ∀ᶠ u in 𝓝 x, ∀ k, functionalSecondSlopeLift H a b X u k =
      dslope (dslope (f u) (a u k)) (b u k) (X u k) := by
  obtain ⟨r, hr, hfr⟩ := exists_eventually_spatial_ball_differentiableOn hf
  let S := functionalSecondSlopeSegment a b X
  have ha' := ((compactSlopePullbackCLM (K := K)).analyticAt _).comp ha
  have hb' := ((compactSlopePullbackCLM (K := K)).analyticAt _).comp hb
  have hX' := ((compactSlopePullbackCLM (K := K)).analyticAt _).comp hX
  have hs : AnalyticAt ℂ S x :=
    ha'.add (analyticAt_const.mul ((hb'.add (analyticAt_const.mul (hX'.sub hb'))).sub ha'))
  have hs₀ : S x = 0 := by simp [S, functionalSecondSlopeSegment, ha₀, hb₀, hX₀]
  have ht : Tendsto (fun u => (u, S u)) (𝓝 x) (𝓝 (x, (0 : C(CompactSlopeSquare K, ℂ)))) := by
    simpa only [hs₀, id_eq] using! (continuousAt_id.prodMk hs.continuousAt).tendsto
  have hta : Tendsto a (𝓝 x) (𝓝 (0 : C(K, ℂ))) := by
    simpa only [ha₀] using ha.continuousAt.tendsto
  have htb : Tendsto b (𝓝 x) (𝓝 (0 : C(K, ℂ))) := by
    simpa only [hb₀] using hb.continuousAt.tendsto
  have htX : Tendsto X (𝓝 x) (𝓝 (0 : C(K, ℂ))) := by
    simpa only [hX₀] using hX.continuousAt.tendsto
  filter_upwards [hfr, ht.eventually (compactSpatialIteratedDeriv_eventually_apply hH he 2),
    hta.eventually (ball_mem_nhds _ hr), htb.eventually (ball_mem_nhds _ hr),
    htX.eventually (ball_mem_nhds _ hr)] with u hfu hDu hau hbu hXu
  intro k
  have haU : a u k ∈ ball 0 r := mem_ball_zero_iff.mpr
    ((a u).norm_coe_le_norm k |>.trans_lt (by simpa [mem_ball, dist_eq_norm] using hau))
  have hbU : b u k ∈ ball 0 r := mem_ball_zero_iff.mpr
    ((b u).norm_coe_le_norm k |>.trans_lt (by simpa [mem_ball, dist_eq_norm] using hbu))
  have hXU : X u k ∈ ball 0 r := mem_ball_zero_iff.mpr
    ((X u).norm_coe_le_norm k |>.trans_lt (by simpa [mem_ball, dist_eq_norm] using hXu))
  change doubleUnitSegmentIntegralCLM
    ((compactSlopeInnerCoord * compactSpatialDeriv (compactSpatialDeriv H) (u, S u)).curry k) = _
  rw [second_dslope_eq_integral_of_differentiableOn_ball hfu haU hbU hXU]
  apply doubleUnitSegmentIntegralCLM_eq_integral
  intro t s
  rw [ContinuousMap.curry_apply, ContinuousMap.mul_apply]
  have hd : compactSpatialDeriv (compactSpatialDeriv H) (u, S u) (k, (t, s)) =
      deriv (deriv (f u)) (S u (k, (t, s))) := by
    simpa only [compactSpatialIteratedDeriv, iteratedDeriv_succ, iteratedDeriv_zero] using!
      hDu (k, (t, s))
  rw [hd]
  rfl

theorem analyticAt_functional_second_dslope_of_local_lift
    {H : E × C(CompactSlopeSquare K, ℂ) → C(CompactSlopeSquare K, ℂ)}
    {f : E → ℂ → ℂ} {a b X : E → C(K, ℂ)} {x : E}
    (hf : AnalyticAt ℂ (fun u : E × ℂ => f u.1 u.2) (x, 0))
    (hH : AnalyticAt ℂ H (x, 0))
    (he : ∀ᶠ u in 𝓝 (x, (0 : C(CompactSlopeSquare K, ℂ))), ∀ q, H u q = f u.1 (u.2 q))
    (ha : AnalyticAt ℂ a x) (hb : AnalyticAt ℂ b x) (hX : AnalyticAt ℂ X x)
    (ha₀ : a x = 0) (hb₀ : b x = 0) (hX₀ : X x = 0) (k : K) :
    AnalyticAt ℂ (fun u => dslope (dslope (f u) (a u k)) (b u k) (X u k)) x := by
  have hs₀ : functionalSecondSlopeSegment a b X x = 0 := by
    simp [functionalSecondSlopeSegment, ha₀, hb₀, hX₀]
  have hH' : AnalyticAt ℂ H (x, functionalSecondSlopeSegment a b X x) := by
    simpa only [hs₀] using hH
  have h := ((ContinuousMap.evalCLM ℂ k).analyticAt _).comp
    (functionalSecondSlopeLift_analyticAt hH' ha hb hX)
  apply h.congr
  filter_upwards [functionalSecondSlopeLift_eventually_apply_local hf hH he ha hb hX ha₀ hb₀ hX₀]
    with u hu
  exact hu k

end PGM
