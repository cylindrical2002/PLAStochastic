import PLAStochastic.Index.CEPS.Scaled.ComplexJetKernel

/-! # Genuine joint spatial-function kernel lifts and their original root charts -/

noncomputable section
open Complex Set Filter Topology
namespace PGM

/-- The genuine square-root charts of the finite Newton model. -/
structure CepsComplexJetRootChart (p : ℕ → ℂ) (lam : ℝ) (z : ℂ) : Prop where
  variance_ne : p (cepsJetCode (.inl 0)) ≠ 0
  variance_chart : 2 / p (cepsJetCode (.inl 0)) ∈ slitPlane
  frequency_chart : z + (lam : ℂ) ^ 2 / (2 * p (cepsJetCode (.inl 0))) ∈ slitPlane
  gap_plus_ne : cepsComplexCumulantRootGap p lam z 1 ≠ 0
  gap_minus_ne : cepsComplexCumulantRootGap p lam z (-1) ≠ 0

/-- Every original positive-variance vector has the required charts away from the joint origin. -/
theorem cepsComplexJetRootChart_real (p : ℕ → ℝ) (hp : 0 < p (cepsJetCode (.inl 0)))
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) (hne : lam ≠ 0 ∨ z ≠ 0) :
    CepsComplexJetRootChart (fun i => (p i : ℂ)) lam z := by
  refine ⟨by exact_mod_cast hp.ne', ?_,
    cepsCumulantRootBase_radicand_mem_slitPlane p hp lam hz hne, ?_, ?_⟩
  · have he : (2 : ℂ) / (p (cepsJetCode (.inl 0)) : ℂ) =
        ((2 / p (cepsJetCode (.inl 0)) : ℝ) : ℂ) := by push_cast; rfl
    rw [he, mem_slitPlane_iff]
    exact Or.inl (by simpa only [ofReal_re] using (div_pos (by norm_num : (0 : ℝ) < 2) hp))
  · rw [cepsComplexCumulantRootGap_real]
    exact cepsCumulantRootGap_ne_zero p hp lam hz hne (by norm_num)
  · rw [cepsComplexCumulantRootGap_real]
    exact cepsCumulantRootGap_ne_zero p hp lam hz hne (by norm_num)

variable {E K : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace K] [CompactSpace K]

/-- This spatial lift uses actual finite Newton roots and actual removable slopes. -/
def cepsComplexKernelGSpatialLift (p : E → ℕ → ℂ) (N : ℕ) (lam : ℝ) (z b : E → ℂ) :
    E × C(K, ℂ) → C(K, ℂ) :=
  cepsContinuousKernelGJetModel (fun v => p v.1) N lam
    (fun v => z v.1) (fun v => b v.1) Prod.snd

theorem cepsComplexKernelGSpatialLift_apply {p : E → ℕ → ℂ} (N : ℕ) (lam : ℝ)
    {z b : E → ℂ} {x : E} (X : C(K, ℂ))
    (hp : ∀ i, AnalyticAt ℂ (fun x => p x i) x)
    (hb : AnalyticAt ℂ b x) (hz : AnalyticAt ℂ z x) (k : K) :
    cepsComplexKernelGSpatialLift p N lam z b (x, X) k =
      cepsComplexKernelGJetModel (p x) N lam (z x) (b x) (X k) := by
  exact cepsContinuousKernelGJetModel_apply N lam Prod.snd
    (fun i => (hp i).comp (x := (x, X)) (f := Prod.fst) analyticAt_fst)
    (hb.comp (x := (x, X)) (f := Prod.fst) analyticAt_fst)
    (hz.comp (x := (x, X)) (f := Prod.fst) analyticAt_fst) k

set_option maxHeartbeats 800000 in
theorem cepsComplexKernelGSpatialLift_analyticAt {p : E → ℕ → ℂ} (N : ℕ) (lam : ℝ)
    {z b : E → ℂ} {x : E} (X : C(K, ℂ))
    (hp : ∀ i, AnalyticAt ℂ (fun x => p x i) x)
    (hb : AnalyticAt ℂ b x) (hz : AnalyticAt ℂ z x)
    (hchart : CepsComplexJetRootChart (p x) lam (z x)) :
    AnalyticAt ℂ (cepsComplexKernelGSpatialLift p N lam z b) (x, X) := by
  exact cepsContinuousKernelGJetModel_analyticAt N lam
    (fun i => (hp i).comp (x := (x, X)) (f := Prod.fst) analyticAt_fst)
    (hb.comp (x := (x, X)) (f := Prod.fst) analyticAt_fst)
    (hz.comp (x := (x, X)) (f := Prod.fst) analyticAt_fst)
    analyticAt_snd hchart.variance_ne hchart.variance_chart hchart.frequency_chart
      hchart.gap_plus_ne hchart.gap_minus_ne

/-- Both divided differences of the complete finite spatial kernel are jointly analytic
in arbitrary complex jet parameter spaces, including all marker collisions. -/
theorem cepsComplexKernelGJetModel_moving_slopes_analyticAt
    {U : Set E} (hU : IsOpen U) {x : E} (hx : x ∈ U) (N : ℕ) (lam : ℝ)
    {p : E → ℕ → ℂ} {b z a d t : E → ℂ}
    (hp : ∀ i, AnalyticOnNhd ℂ (fun x => p x i) U)
    (hb : AnalyticOnNhd ℂ b U) (hz : AnalyticOnNhd ℂ z U)
    (hchart : ∀ u ∈ U, CepsComplexJetRootChart (p u) lam (z u))
    (ha : AnalyticAt ℂ a x) (hd : AnalyticAt ℂ d x) (ht : AnalyticAt ℂ t x) :
    AnalyticAt ℂ (fun x => dslope (cepsComplexKernelGJetModel (p x) N lam (z x) (b x)) (a x) (d x)) x ∧
    AnalyticAt ℂ (fun x => dslope (dslope
      (cepsComplexKernelGJetModel (p x) N lam (z x) (b x)) (a x)) (d x) (t x)) x := by
  constructor
  · apply analyticAt_moving_dslope_of_compact_lift hU hx
      (H := cepsComplexKernelGSpatialLift p N lam z b) (ha := ha) (hb := hd)
    · intro v hv
      exact cepsComplexKernelGSpatialLift_analyticAt N lam v.2 (fun i => hp i v.1 hv.1)
        (hb v.1 hv.1) (hz v.1 hv.1) (hchart v.1 hv.1)
    · intro u hu X s
      exact cepsComplexKernelGSpatialLift_apply N lam X (fun i => hp i u hu) (hb u hu) (hz u hu) s
    · intro u _
      exact cepsComplexKernelGJetModel_spatial_differentiable (p u) N lam (z u) (b u)
  · apply analyticAt_moving_second_dslope_of_compact_lift hU hx
      (H := cepsComplexKernelGSpatialLift p N lam z b) (ha := ha) (hb := hd) (hc := ht)
    · intro v hv
      exact cepsComplexKernelGSpatialLift_analyticAt N lam v.2 (fun i => hp i v.1 hv.1)
        (hb v.1 hv.1) (hz v.1 hv.1) (hchart v.1 hv.1)
    · intro u hu X s
      exact cepsComplexKernelGSpatialLift_apply N lam X (fun i => hp i u hu) (hb u hu) (hz u hu) s
    · intro u _
      exact cepsComplexKernelGJetModel_spatial_differentiable (p u) N lam (z u) (b u)

/-- The root-chart conditions hold on a genuine parameter neighborhood of any admissible
center; they are not an extra premise imposed on nearby finite vectors. -/
theorem CepsComplexJetRootChart.eventually {p : E → ℕ → ℂ} {z : E → ℂ} {x : E}
    (hp : ∀ i, AnalyticAt ℂ (fun x => p x i) x) (hz : AnalyticAt ℂ z x)
    {lam : ℝ} (h : CepsComplexJetRootChart (p x) lam (z x)) :
    ∀ᶠ u in 𝓝 x, CepsComplexJetRootChart (p u) lam (z u) := by
  have hV := hp (cepsJetCode (.inl 0))
  have hratio : AnalyticAt ℂ (fun u => 2 / p u (cepsJetCode (.inl 0))) x :=
    analyticAt_const.div hV h.variance_ne
  have hrad : AnalyticAt ℂ (fun u => z u + (lam : ℂ) ^ 2 /
      (2 * p u (cepsJetCode (.inl 0)))) x :=
    hz.add (analyticAt_const.div (analyticAt_const.mul hV)
      (mul_ne_zero (by norm_num) h.variance_ne))
  have hbaseP : AnalyticAt ℂ (fun u => cepsComplexCumulantRootBase (p u) lam (z u) 1) x := by
    simpa only [cepsComplexCumulantRootModel] using
      (cepsComplexCumulantRootModel_analyticAt (b := fun _ => (0 : ℂ)) hp analyticAt_const hz
        0 lam 1 h.variance_ne h.variance_chart h.frequency_chart h.gap_plus_ne 0)
  have hbaseM : AnalyticAt ℂ (fun u => cepsComplexCumulantRootBase (p u) lam (z u) (-1)) x := by
    simpa only [cepsComplexCumulantRootModel] using
      (cepsComplexCumulantRootModel_analyticAt (b := fun _ => (0 : ℂ)) hp analyticAt_const hz
        0 lam (-1) h.variance_ne h.variance_chart h.frequency_chart h.gap_minus_ne 0)
  have hGP : AnalyticAt ℂ (fun u => cepsComplexCumulantRootGap (p u) lam (z u) 1) x :=
    analyticAt_const.add (hV.mul hbaseP)
  have hGM : AnalyticAt ℂ (fun u => cepsComplexCumulantRootGap (p u) lam (z u) (-1)) x :=
    analyticAt_const.add (hV.mul hbaseM)
  filter_upwards [hV.continuousAt.eventually_ne h.variance_ne,
    hratio.continuousAt.eventually (isOpen_slitPlane.mem_nhds h.variance_chart),
    hrad.continuousAt.eventually (isOpen_slitPlane.mem_nhds h.frequency_chart),
    hGP.continuousAt.eventually_ne h.gap_plus_ne,
    hGM.continuousAt.eventually_ne h.gap_minus_ne] with u hv hvr hzr hgp hgm
  exact ⟨hv, hvr, hzr, hgp, hgm⟩

end PGM
