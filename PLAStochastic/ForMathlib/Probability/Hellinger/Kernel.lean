import PLAStochastic.ForMathlib.Probability.Hellinger.RadonNikodym
import Mathlib.Probability.Kernel.Composition.RadonNikodym
import Mathlib.Probability.Kernel.Composition.MeasureComp

/-!
# Hellinger comparison through general probability kernels

Attaching the same Markov kernel preserves Hellinger distance for the joint law.
Taking any measurable output of the joint law contracts it. The conditional
probability kernel needs no density and may depend on the input count.
-/

set_option autoImplicit false

namespace ProbabilityTheory

noncomputable section

open MeasureTheory
open scoped ProbabilityTheory

variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

theorem measureHellinger_sq (P Q : Measure α)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    measureHellinger P Q ^ 2 = ∫ x,
      (Real.sqrt ((P.rnDeriv (P + Q) x).toReal) -
        Real.sqrt ((Q.rnDeriv (P + Q) x).toReal)) ^ 2 ∂(P + Q) :=
  HellingerDensity.hellinger_sq _ _

theorem measureHellinger_compProd_eq (P Q : Measure α)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (κ : Kernel α β) [IsMarkovKernel κ] :
    measureHellinger (P ⊗ₘ κ) (Q ⊗ₘ κ) = measureHellinger P Q := by
  have hs : measureHellinger (P ⊗ₘ κ) (Q ⊗ₘ κ) ^ 2 = measureHellinger P Q ^ 2 := by
    rw [measureHellinger_sq, ← Measure.compProd_add_left]
    calc
      (∫ z, (Real.sqrt (((P ⊗ₘ κ).rnDeriv ((P + Q) ⊗ₘ κ) z).toReal) -
          Real.sqrt (((Q ⊗ₘ κ).rnDeriv ((P + Q) ⊗ₘ κ) z).toReal)) ^ 2 ∂((P + Q) ⊗ₘ κ)) =
          ∫ z, (Real.sqrt ((P.rnDeriv (P + Q) z.1).toReal) -
            Real.sqrt ((Q.rnDeriv (P + Q) z.1).toReal)) ^ 2 ∂((P + Q) ⊗ₘ κ) := by
        apply integral_congr_ae
        filter_upwards [rnDeriv_measure_compProd_left P (P + Q) κ,
          rnDeriv_measure_compProd_left Q (P + Q) κ] with z hp hq
        rw [hp, hq]
      _ = ∫ x, (Real.sqrt ((P.rnDeriv (P + Q) x).toReal) -
          Real.sqrt ((Q.rnDeriv (P + Q) x).toReal)) ^ 2 ∂(P + Q) := by
        have hm : Measurable (fun x =>
            (Real.sqrt ((P.rnDeriv (P + Q) x).toReal) -
              Real.sqrt ((Q.rnDeriv (P + Q) x).toReal)) ^ 2) := by fun_prop
        rw [← integral_map measurable_fst.aemeasurable hm.aestronglyMeasurable,
          ← Measure.fst, Measure.fst_compProd]
      _ = measureHellinger P Q ^ 2 := (measureHellinger_sq P Q).symm
  nlinarith [measureHellinger_nonneg (P ⊗ₘ κ) (Q ⊗ₘ κ), measureHellinger_nonneg P Q]

theorem measureHellinger_comp_le (P Q : Measure α)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (κ : Kernel α β) [IsMarkovKernel κ] :
    measureHellinger (κ ∘ₘ P) (κ ∘ₘ Q) ≤ measureHellinger P Q := by
  have h := measureHellinger_map (P ⊗ₘ κ) (Q ⊗ₘ κ) measurable_snd
  have hP : (P ⊗ₘ κ).map Prod.snd = κ ∘ₘ P := Measure.snd_compProd P κ
  have hQ : (Q ⊗ₘ κ).map Prod.snd = κ ∘ₘ Q := Measure.snd_compProd Q κ
  simp only [hP, hQ] at h
  rw [measureHellinger_compProd_eq] at h
  exact h

theorem measureHellinger_compProd_map_le (P Q : Measure α)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (κ : Kernel α β) [IsMarkovKernel κ] {F : α × β → γ} (hF : Measurable F) :
    let : IsProbabilityMeasure ((P ⊗ₘ κ).map F) :=
      Measure.isProbabilityMeasure_map hF.aemeasurable
    let : IsProbabilityMeasure ((Q ⊗ₘ κ).map F) :=
      Measure.isProbabilityMeasure_map hF.aemeasurable
    measureHellinger ((P ⊗ₘ κ).map F) ((Q ⊗ₘ κ).map F) ≤ measureHellinger P Q := by
  have h := measureHellinger_map (P ⊗ₘ κ) (Q ⊗ₘ κ) hF
  rwa [measureHellinger_compProd_eq] at h

end

end ProbabilityTheory
