import PLAStochastic.Index.CEPS.Normal.FunctionalSlopeLiftLocal

/-! # Local functional first divided differences, including the zero-scale section -/

noncomputable section
open Complex Set Metric Filter Topology MeasureTheory
namespace PGM

variable {E K : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace K] [CompactSpace K]

abbrev CompactSlopeLine (K : Type*) := K × UnitSegment

def compactSlopeLinePullbackCLM : C(K, ℂ) →L[ℂ] C(CompactSlopeLine K, ℂ) :=
  ContinuousMap.compCLM ℂ ℂ ⟨Prod.fst, continuous_fst⟩

def compactSlopeLineIntegralCLM : C(CompactSlopeLine K, ℂ) →L[ℂ] C(K, ℂ) :=
  (ContinuousLinearMap.compLeftContinuous ℂ K (unitSegmentIntegralCLM (F := ℂ))).comp compactCurryCLM

def compactSlopeLineCoord : C(CompactSlopeLine K, ℂ) :=
  ⟨fun q => (q.2.val : ℂ), by fun_prop⟩

def functionalFirstSlopeSegment (a X : E → C(K, ℂ)) (u : E) : C(CompactSlopeLine K, ℂ) :=
  compactSlopeLinePullbackCLM (a u) + compactSlopeLineCoord *
    (compactSlopeLinePullbackCLM (X u) - compactSlopeLinePullbackCLM (a u))

def functionalFirstSlopeLift
    (H : E × C(CompactSlopeLine K, ℂ) → C(CompactSlopeLine K, ℂ))
    (a X : E → C(K, ℂ)) (u : E) : C(K, ℂ) :=
  compactSlopeLineIntegralCLM (compactSpatialDeriv H (u, functionalFirstSlopeSegment a X u))

theorem functionalFirstSlopeLift_analyticAt
    {H : E × C(CompactSlopeLine K, ℂ) → C(CompactSlopeLine K, ℂ)}
    {a X : E → C(K, ℂ)} {x : E}
    (hH : AnalyticAt ℂ H (x, functionalFirstSlopeSegment a X x))
    (ha : AnalyticAt ℂ a x) (hX : AnalyticAt ℂ X x) :
    AnalyticAt ℂ (functionalFirstSlopeLift H a X) x := by
  have ha' := ((compactSlopeLinePullbackCLM (K := K)).analyticAt _).comp ha
  have hX' := ((compactSlopeLinePullbackCLM (K := K)).analyticAt _).comp hX
  have hs : AnalyticAt ℂ (functionalFirstSlopeSegment a X) x :=
    ha'.add (analyticAt_const.mul (hX'.sub ha'))
  have hD := (compactSpatialDeriv_analyticAt hH).comp
    (x := x) (f := fun u => (u, functionalFirstSlopeSegment a X u)) (analyticAt_id.prod hs)
  exact ((compactSlopeLineIntegralCLM (K := K)).analyticAt _).comp hD

theorem functionalFirstSlopeLift_eventually_apply_local
    {H : E × C(CompactSlopeLine K, ℂ) → C(CompactSlopeLine K, ℂ)}
    {f : E → ℂ → ℂ} {a X : E → C(K, ℂ)} {x : E}
    (hf : AnalyticAt ℂ (fun u : E × ℂ => f u.1 u.2) (x, 0))
    (hH : AnalyticAt ℂ H (x, 0))
    (he : ∀ᶠ u in 𝓝 (x, (0 : C(CompactSlopeLine K, ℂ))), ∀ q, H u q = f u.1 (u.2 q))
    (ha : AnalyticAt ℂ a x) (hX : AnalyticAt ℂ X x)
    (ha₀ : a x = 0) (hX₀ : X x = 0) :
    ∀ᶠ u in 𝓝 x, ∀ k, functionalFirstSlopeLift H a X u k = dslope (f u) (a u k) (X u k) := by
  obtain ⟨r, hr, hfr⟩ := exists_eventually_spatial_ball_differentiableOn hf
  let S := functionalFirstSlopeSegment a X
  have ha' := ((compactSlopeLinePullbackCLM (K := K)).analyticAt _).comp ha
  have hX' := ((compactSlopeLinePullbackCLM (K := K)).analyticAt _).comp hX
  have hs : AnalyticAt ℂ S x := ha'.add (analyticAt_const.mul (hX'.sub ha'))
  have hs₀ : S x = 0 := by simp [S, functionalFirstSlopeSegment, ha₀, hX₀]
  have ht : Tendsto (fun u => (u, S u)) (𝓝 x) (𝓝 (x, (0 : C(CompactSlopeLine K, ℂ)))) := by
    simpa only [hs₀, id_eq] using! (continuousAt_id.prodMk hs.continuousAt).tendsto
  have hta : Tendsto a (𝓝 x) (𝓝 (0 : C(K, ℂ))) := by
    simpa only [ha₀] using ha.continuousAt.tendsto
  have htX : Tendsto X (𝓝 x) (𝓝 (0 : C(K, ℂ))) := by
    simpa only [hX₀] using hX.continuousAt.tendsto
  filter_upwards [hfr, ht.eventually (compactSpatialIteratedDeriv_eventually_apply hH he 1),
    hta.eventually (ball_mem_nhds _ hr), htX.eventually (ball_mem_nhds _ hr)] with u hfu hDu hau hXu
  intro k
  have haU : a u k ∈ ball 0 r := mem_ball_zero_iff.mpr
    ((a u).norm_coe_le_norm k |>.trans_lt (by simpa [mem_ball, dist_eq_norm] using hau))
  have hXU : X u k ∈ ball 0 r := mem_ball_zero_iff.mpr
    ((X u).norm_coe_le_norm k |>.trans_lt (by simpa [mem_ball, dist_eq_norm] using hXu))
  change unitSegmentIntegralCLM ((compactSpatialDeriv H (u, S u)).curry k) = _
  rw [cepsNormal_dslope_eq_integral hfu haU hXU]
  apply unitSegmentIntegralCLM_eq_integral
  intro t
  rw [ContinuousMap.curry_apply]
  have hd : compactSpatialDeriv H (u, S u) (k, t) = deriv (f u) (S u (k, t)) := by
    simpa only [compactSpatialIteratedDeriv, iteratedDeriv_succ, iteratedDeriv_zero] using!
      hDu (k, t)
  rw [hd]
  rfl

end PGM
