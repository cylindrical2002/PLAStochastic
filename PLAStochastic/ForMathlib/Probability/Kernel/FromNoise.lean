import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.Composition.Prod

/-!
# A measurable probability kernel sampled from fresh noise

The joint sampling representation gives both its pointwise law and the
composition law under any probability distribution of the observed state.
-/

set_option autoImplicit false

namespace ProbabilityTheory

noncomputable section

open MeasureTheory

variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

def kernelFromNoise (nu : Measure β) (F : α × β → γ) : Kernel α γ :=
  ((Kernel.id : Kernel α α) ×ₖ Kernel.const α nu).map F

theorem isMarkovKernel_kernelFromNoise (nu : Measure β) [IsProbabilityMeasure nu]
    (F : α × β → γ) (hF : Measurable F) : IsMarkovKernel (kernelFromNoise nu F) :=
  Kernel.IsMarkovKernel.map _ hF

theorem kernelFromNoise_apply (nu : Measure β) [SFinite nu] {F : α × β → γ}
    (hF : Measurable F) (x : α) :
    kernelFromNoise nu F x = nu.map (fun y => F (x, y)) := by
  have hFx : Measurable (fun y => F (x, y)) := hF.comp (measurable_const.prodMk measurable_id)
  ext s hs
  rw [kernelFromNoise, Kernel.map_apply' _ hF x hs,
    Kernel.id_prod_apply' _ x (hF hs), Kernel.const_apply, Measure.map_apply hFx hs]
  rfl

theorem kernelFromNoise_comp (nu : Measure β) [SFinite nu] {F : α × β → γ}
    (hF : Measurable F) (mu : Measure α) [SFinite mu] :
    kernelFromNoise nu F ∘ₘ mu = (mu.prod nu).map F := by
  rw [kernelFromNoise, ← Measure.map_comp _ _ hF,
    ← Measure.compProd_eq_comp_prod, Measure.compProd_const]

end

end ProbabilityTheory
