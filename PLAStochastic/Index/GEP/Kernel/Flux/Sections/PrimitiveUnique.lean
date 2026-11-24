import PLAStochastic.Index.GEP.Response.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Uniqueness of the derivative in the original `AEPrimitive`

Only local interval integrability is used. The original functions may be
specified almost everywhere and no pointwise differentiability is assumed.
-/

namespace PGM
noncomputable section
open MeasureTheory Set Filter
open scoped Topology

theorem kernel_locallyIntegrable_of_intervals {f : ℝ → ℝ}
    (hf : ∀ R, IntervalIntegrable f volume 0 R) : LocallyIntegrable f volume := by
  intro x
  refine ⟨Ioc (x - 1) (x + 1), Ioc_mem_nhds (by linarith) (by linarith), ?_⟩
  exact ((hf (x - 1)).symm.trans (hf (x + 1))).1

/-- Any two continuous integral representatives of the same original function
agree at every positive point. -/
theorem kernel_primitive_representatives_eq {J K f g : ℝ → ℝ}
    (hf : ∀ R, IntervalIntegrable f volume 0 R)
    (hg : ∀ R, IntervalIntegrable g volume 0 R) {c d : ℝ}
    (hF : ∀ᵐ x ∂volume.restrict (Ioi 0), J x = c + ∫ t in (0 : ℝ)..x, f t)
    (hG : ∀ᵐ x ∂volume.restrict (Ioi 0), K x = d + ∫ t in (0 : ℝ)..x, g t)
    (hJK : J =ᵐ[volume.restrict (Ioi 0)] K) :
    EqOn (fun x => c + ∫ t in (0 : ℝ)..x, f t)
      (fun x => d + ∫ t in (0 : ℝ)..x, g t) (Ioi 0) := by
  have hcf : Continuous (fun x => c + ∫ t in (0 : ℝ)..x, f t) :=
    continuous_const.add (intervalIntegral.continuous_primitive (fun a b => (hf a).symm.trans (hf b)) 0)
  have hcg : Continuous (fun x => d + ∫ t in (0 : ℝ)..x, g t) :=
    continuous_const.add (intervalIntegral.continuous_primitive (fun a b => (hg a).symm.trans (hg b)) 0)
  apply Measure.eqOn_open_of_ae_eq (μ := volume) ?_ isOpen_Ioi hcf.continuousOn hcg.continuousOn
  filter_upwards [hF, hG, hJK] with x hx hy hxy
  exact hx.symm.trans (hxy.trans hy)

/-- The derivative in the original response interface is unique almost
everywhere on the positive half-line, also for a.e.-equal input functions. -/
theorem kernel_aePrimitive_unique_of_ae_eq {J K f g : ℝ → ℝ}
    (hF : AEPrimitive J f) (hG : AEPrimitive K g)
    (hJK : J =ᵐ[volume.restrict (Ioi 0)] K) :
    f =ᵐ[volume.restrict (Ioi 0)] g := by
  obtain ⟨hf, c, hc⟩ := hF
  obtain ⟨hg, d, hd⟩ := hG
  have he := kernel_primitive_representatives_eq hf hg hc hd hJK
  have hdf := LocallyIntegrable.ae_hasDerivAt_integral (kernel_locallyIntegrable_of_intervals hf)
  have hdg := LocallyIntegrable.ae_hasDerivAt_integral (kernel_locallyIntegrable_of_intervals hg)
  filter_upwards [ae_restrict_of_ae hdf, ae_restrict_of_ae hdg,
    ae_restrict_mem measurableSet_Ioi] with x hfx hgx hx
  have hfx' := (hfx 0).const_add c
  have hgx' := (hgx 0).const_add d
  have he' : (fun y => d + ∫ t in (0 : ℝ)..y, g t) =ᶠ[𝓝 x]
      (fun y => c + ∫ t in (0 : ℝ)..y, f t) := by
    filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
    exact (he hy).symm
  exact (hfx'.congr_of_eventuallyEq he').unique hgx'

theorem kernel_aePrimitive_unique {J f g : ℝ → ℝ}
    (hf : AEPrimitive J f) (hg : AEPrimitive J g) :
    f =ᵐ[volume.restrict (Ioi 0)] g :=
  kernel_aePrimitive_unique_of_ae_eq hf hg Filter.EventuallyEq.rfl

theorem kernel_bdryKernel_unique {eps : ℝ} {ν : ProbabilityMeasure ℝ} {ψ B₁ B₂ : ℝ → ℝ}
    (h₁ : IsBdryKernel eps ν ψ B₁) (h₂ : IsBdryKernel eps ν ψ B₂) :
    B₁ =ᵐ[volume.restrict (Ioi 0)] B₂ := by
  filter_upwards [kernel_aePrimitive_unique h₁ h₂] with x hx
  exact add_left_cancel hx

end
end PGM
