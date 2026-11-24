import PLAStochastic.Index.CEPS.BrownianCoeff.IntegralBudget
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-! # Measurability of the full drift kernel, including its fixed cutoff -/

noncomputable section

open MeasureTheory

namespace PGM

theorem cepsBrownianSquare_continuous_drift (v z : ℂ) :
    Continuous (fun lam : ℝ => cepsBrownianSquare v lam z) := by
  unfold cepsBrownianSquare
  fun_prop

theorem cepsBrownianH_measurable_drift (v z : ℂ) :
    Measurable (fun lam : ℝ => cepsBrownianH v lam z) := by
  have ha : Continuous (fun lam : ℝ => (lam : ℂ) / v) := by fun_prop
  have hu := cepsBrownianSquare_continuous_drift v z
  have hI := cepsBrownianEntranceIntegral_continuous.comp (ha.prodMk hu)
  have hS := cepsBrownianSinhc_differentiable.continuous.comp hu
  have he : (fun lam : ℝ => cepsBrownianH v lam z) =
      fun lam : ℝ => (2 / v * cepsBrownianEntranceIntegral ((lam : ℂ) / v)
        (cepsBrownianSquare v lam z)) / cepsBrownianSinhc (cepsBrownianSquare v lam z) := by
    funext lam
    exact cepsBrownianH_integral v lam z
  rw [he]
  exact (measurable_const.mul hI.measurable).div hS.measurable

theorem cepsBrownianR_measurable_drift (v z : ℂ) :
    Measurable (fun lam : ℝ => cepsBrownianR v lam z) := by
  unfold cepsBrownianR Complex.sqrt
  fun_prop

theorem cepsBrownianKernel_measurable_drift (v z : ℂ) :
    Measurable (fun lam : ℝ => cepsBrownianKernel v lam z) := by
  have ha : Measurable (fun lam : ℝ => (lam : ℂ) / v) := by fun_prop
  have hu := (cepsBrownianSquare_continuous_drift v z).measurable
  have hS := cepsBrownianSinhc_differentiable.continuous.measurable.comp hu
  have hD := cepsBrownianSinhc_differentiable.deriv.continuous.measurable.comp hu
  have hH := cepsBrownianH_measurable_drift v z
  have hR := cepsBrownianR_measurable_drift v z
  have hInf : Measurable (fun lam : ℝ => cepsBrownianHInf v lam z) := by
    unfold cepsBrownianHInf
    exact measurable_const.div (Complex.measurable_ofReal.add hR)
  have hXi : Measurable (fun lam : ℝ => cepsBrownianXiPlus v lam z) := by
    unfold cepsBrownianXiPlus
    exact (Complex.measurable_ofReal.neg.add hR).div_const v
  unfold cepsBrownianKernel
  exact (((hH.pow_const 2).mul ha.cexp).mul hD).div (hS.pow_const 2) |>.add
    (Measurable.ite (measurableSet_le measurable_const measurable_id)
      (((hInf.pow_const 2).mul hXi.neg.cexp).mul
        ((measurable_const.div hR).sub measurable_const)) measurable_const)

end PGM
