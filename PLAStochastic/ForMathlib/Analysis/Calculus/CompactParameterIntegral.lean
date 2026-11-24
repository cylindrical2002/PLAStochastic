import PLAStochastic.ForMathlib.Analysis.SpecialFunctions.ExponentialUnitMoments

/-! # Genuine differentiation under a compact spatial integral -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

theorem hasDerivAt_compactParameterIntegral
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α] [T2Space α]
    {μ : Measure α} [IsFiniteMeasureOnCompacts μ]
    {K : Set α} (hK : IsCompact K) {F F' : ℝ → α → ℝ}
    (hF : ∀ x, 0 < x → Continuous (F x))
    (hF' : ContinuousOn (Function.uncurry F') (Ioi 0 ×ˢ K))
    (hd : ∀ x, 0 < x → ∀ a ∈ K, HasDerivAt (F · a) (F' x a) x)
    {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => ∫ a in K, F y a ∂μ) (∫ a in K, F' x a ∂μ) x := by
  have hsub : Icc (x/2) (2*x) ×ˢ K ⊆ Ioi 0 ×ˢ K := by
    rintro ⟨y,a⟩ ⟨hy,ha⟩
    have hy0 : x/2 ≤ y := hy.1
    exact ⟨by change 0 < y; linarith,ha⟩
  obtain ⟨M,hM⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn (hF'.mono hsub)
  have hm : ∀ᶠ y in 𝓝 x, AEStronglyMeasurable (F y) (μ.restrict K) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact (hF y hy).aestronglyMeasurable
  have hmx : AEStronglyMeasurable (F' x) (μ.restrict K) := by
    apply ContinuousOn.aestronglyMeasurable _ hK.measurableSet
    have hc : ContinuousOn (fun a : α => (x,a)) K := continuous_const.prodMk continuous_id |>.continuousOn
    exact hF'.comp hc (fun a ha => ⟨hx,ha⟩)
  have hb : ∀ᵐ a ∂μ.restrict K, ∀ y ∈ Ioo (x/2) (2*x), ‖F' y a‖ ≤ M := by
    filter_upwards [ae_restrict_mem hK.measurableSet] with a ha y hy
    exact hM (y,a) ⟨⟨hy.1.le,hy.2.le⟩,ha⟩
  have hd' : ∀ᵐ a ∂μ.restrict K, ∀ y ∈ Ioo (x/2) (2*x), HasDerivAt (F · a) (F' y a) y := by
    filter_upwards [ae_restrict_mem hK.measurableSet] with a ha y hy
    exact hd y (by linarith [hy.1]) a ha
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Ioo_mem_nhds (by linarith : x/2<x) (by linarith : x<2*x)) hm
    ((hF x hx).continuousOn.integrableOn_compact hK) hmx hb
    (integrableOn_const (C := M) (hs := hK.measure_lt_top.ne)) hd').2

end BrownianAffine
