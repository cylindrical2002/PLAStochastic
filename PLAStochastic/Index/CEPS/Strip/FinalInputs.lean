import PLAStochastic.Index.CEPS.Strip.SubtractedPair
import PLAStochastic.Index.CEPS.Strip.MarkedEndpoint
import PLAStochastic.Index.CEPS.Strip.MarkedDiscount
import PLAStochastic.Index.CEPS.Final.EndpointInputs
import PLAStochastic.Index.CEPS.Final.IntegrandMeasurability

/-! # The outer-strip inputs of the final kernel assembly

The four propositions consumed by `Final/` are exactly the outer-strip results proved in
this directory.
-/

noncomputable section
namespace PGM

theorem cepsStripPairBudget_holds (d N : ℕ) : CepsStripPairBudget d N :=
  fun _M _vlo _vhi _F₀ hM hlo hhi hF₀ =>
    cepsComplexKernelSubtractedPair_strip_budget d N hM hlo hhi hF₀

theorem cepsStripEndpointBudget_holds (d N : ℕ) : CepsStripEndpointBudget d N :=
  fun _M _vlo _vhi hM hlo hhi => cepsComplexKernelMarkedEndpoint_strip_budget d N hM hlo hhi

theorem cepsDiscountBudget_holds (d N : ℕ) : CepsDiscountBudget d N :=
  fun _M hM => cepsComplexKernelMarkedDiscount_budget d N hM

theorem cepsStripBridgeAnalytic_holds (d N : ℕ) : CepsStripBridgeAnalytic d N := by
  intro M vlo vhi F₀ hM hlo hhi hF₀
  obtain ⟨δ, δb, hδ, hδb, h⟩ := cepsComplexKernelFactors_strip_analytic d N hM hlo hhi hF₀
  exact ⟨δ, δb, hδ, hδb, fun q hq hv hhiq hi lam z b hz hF hb =>
    ⟨(h q hq hv hhiq hi lam z b hz hF hb).1, fun hl => ((h q hq hv hhiq hi lam z b hz hF hb).2.2 hl).1⟩⟩

end PGM
