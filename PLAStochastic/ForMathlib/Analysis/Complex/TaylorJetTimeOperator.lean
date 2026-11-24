import PLAStochastic.ForMathlib.Analysis.Complex.TaylorJetLinear

/-! # Exact finite Taylor jets of the complete scaled time operator and pair -/

noncomputable section
open Complex PowerSeries
namespace PGM

theorem analyticAt_completePair {A U V : ℂ → ℂ}
    (hA : AnalyticAt ℂ A 0) (hU : AnalyticAt ℂ U 0) (hV : AnalyticAt ℂ V 0)
    (lam : ℝ) (z : ℂ) : AnalyticAt ℂ (fun b => exp ((b * z) * (1 + b * lam)) * A b ^ 2 *
      (-(1 / (1 + b * lam)) * V b - b * U b)) 0 := by
  have hS : AnalyticAt ℂ (fun b : ℂ => -(1 / (1 + b * lam))) 0 :=
    (analyticAt_const.div (analyticAt_const.add (analyticAt_id.mul analyticAt_const)) (by simp)).neg
  have hE : AnalyticAt ℂ (fun b : ℂ => exp ((b * z) * (1 + b * lam))) 0 := by fun_prop
  exact (hE.mul (hA.pow 2)).mul ((hS.mul hV).sub (analyticAt_id.mul hU))

theorem complexTaylorSeries_coeff_eq_timeOperator {U U' V V' : ℂ → ℂ}
    (hU : AnalyticAt ℂ U 0) (hU' : AnalyticAt ℂ U' 0)
    (hV : AnalyticAt ℂ V 0) (hV' : AnalyticAt ℂ V' 0) (N : ℕ) (lam : ℝ)
    (heU : ∀ j ≤ N, coeff j (complexTaylorSeries U 0) = coeff j (complexTaylorSeries U' 0))
    (heV : ∀ j ≤ N, coeff j (complexTaylorSeries V 0) = coeff j (complexTaylorSeries V' 0)) :
    ∀ j ≤ N, coeff j (complexTaylorSeries (fun b => -(1 / (1 + b * lam)) * V b - b * U b) 0) =
      coeff j (complexTaylorSeries (fun b => -(1 / (1 + b * lam)) * V' b - b * U' b) 0) := by
  have hS : AnalyticAt ℂ (fun b : ℂ => -(1 / (1 + b * lam))) 0 :=
    (analyticAt_const.div (analyticAt_const.add (analyticAt_id.mul analyticAt_const)) (by simp)).neg
  have heL := complexTaylorSeries_coeff_eq_mul hS hV hS hV' N (fun _ _ => rfl) heV
  have heR := complexTaylorSeries_coeff_eq_mul analyticAt_id hU analyticAt_id hU' N (fun _ _ => rfl) heU
  exact complexTaylorSeries_coeff_eq_sub (hS.mul hV) (analyticAt_id.mul hU)
    (hS.mul hV') (analyticAt_id.mul hU') N heL heR

theorem complexTaylorSeries_coeff_eq_completePair {A A' U U' V V' : ℂ → ℂ}
    (hA : AnalyticAt ℂ A 0) (hA' : AnalyticAt ℂ A' 0)
    (hU : AnalyticAt ℂ U 0) (hU' : AnalyticAt ℂ U' 0)
    (hV : AnalyticAt ℂ V 0) (hV' : AnalyticAt ℂ V' 0) (N : ℕ) (lam : ℝ) (z : ℂ)
    (heA : ∀ j ≤ N, coeff j (complexTaylorSeries A 0) = coeff j (complexTaylorSeries A' 0))
    (heU : ∀ j ≤ N, coeff j (complexTaylorSeries U 0) = coeff j (complexTaylorSeries U' 0))
    (heV : ∀ j ≤ N, coeff j (complexTaylorSeries V 0) = coeff j (complexTaylorSeries V' 0)) :
    ∀ j ≤ N, coeff j (complexTaylorSeries (fun b => exp ((b * z) * (1 + b * lam)) * A b ^ 2 *
      (-(1 / (1 + b * lam)) * V b - b * U b)) 0) =
      coeff j (complexTaylorSeries (fun b => exp ((b * z) * (1 + b * lam)) * A' b ^ 2 *
        (-(1 / (1 + b * lam)) * V' b - b * U' b)) 0) := by
  have hS : AnalyticAt ℂ (fun b : ℂ => -(1 / (1 + b * lam))) 0 :=
    (analyticAt_const.div (analyticAt_const.add (analyticAt_id.mul analyticAt_const)) (by simp)).neg
  have hE : AnalyticAt ℂ (fun b : ℂ => exp ((b * z) * (1 + b * lam))) 0 := by fun_prop
  have heSq := complexTaylorSeries_coeff_eq_composition hA hA' (F := fun x : ℂ => x ^ 2)
    (by fun_prop) N heA
  have heEA := complexTaylorSeries_coeff_eq_mul hE (hA.pow 2) hE (hA'.pow 2) N (fun _ _ => rfl) heSq
  have heT := complexTaylorSeries_coeff_eq_timeOperator hU hU' hV hV' N lam heU heV
  exact complexTaylorSeries_coeff_eq_mul (hE.mul (hA.pow 2))
    ((hS.mul hV).sub (analyticAt_id.mul hU)) (hE.mul (hA'.pow 2))
    ((hS.mul hV').sub (analyticAt_id.mul hU')) N heEA heT

end PGM
