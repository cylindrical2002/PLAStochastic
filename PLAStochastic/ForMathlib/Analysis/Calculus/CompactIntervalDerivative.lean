import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Differentiation under a fixed compact interval

Joint continuity of the integrand and its actual parameter derivative supplies
the local domination. No global bound on the parameter is required.
-/

set_option autoImplicit false

namespace MeasureTheory

noncomputable section

open Set Filter
open scoped Topology

theorem continuous_integral_Ioc_of_continuous
    {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    [LocallyCompactSpace X] {F : X → ℝ → ℝ}
    (hF : Continuous (Function.uncurry F)) (a b : ℝ) :
    Continuous (fun x => ∫ z in Ioc a b, F x z) := by
  have h := continuous_parametric_integral_of_continuous
    (μ := volume) hF (isCompact_Icc (a := a) (b := b))
  simpa only [integral_Icc_eq_integral_Ioc] using h

set_option backward.isDefEq.respectTransparency.types false in
theorem hasDerivAt_integral_Ioc_of_continuous
    {F F' : ℝ → ℝ → ℝ}
    (hF : Continuous (Function.uncurry F))
    (hF' : Continuous (Function.uncurry F'))
    (hd : ∀ x z, HasDerivAt (fun t => F t z) (F' x z) x)
    (a b x : ℝ) :
    HasDerivAt (fun t => ∫ z in Ioc a b, F t z)
      (∫ z in Ioc a b, F' x z) x := by
  have hm (t : ℝ) : Continuous (F t) :=
    hF.comp (continuous_const.prodMk continuous_id)
  have hm' (t : ℝ) : Continuous (F' t) :=
    hF'.comp (continuous_const.prodMk continuous_id)
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod (isCompact_Icc (a := a) (b := b))).exists_bound_of_continuousOn
      (hF'.continuousOn : ContinuousOn (Function.uncurry F')
        (Icc (x - 1) (x + 1) ×ˢ Icc a b))
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioc a b)) (s := Ioo (x - 1) (x + 1))
    (F := F) (F' := F') (bound := fun _ => M)
    (Ioo_mem_nhds (by linarith) (by linarith))
    (Eventually.of_forall fun t => (hm t).aestronglyMeasurable)
    ((hm x).integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    (hm' x).aestronglyMeasurable
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with z hz t ht
      exact hM (t, z) ⟨⟨ht.1.le, ht.2.le⟩, ⟨hz.1.le, hz.2⟩⟩)
    (integrableOn_const (hs := by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top))
    (ae_of_all _ fun z t _ => hd t z)).2

end

end MeasureTheory
