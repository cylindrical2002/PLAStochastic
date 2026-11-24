import PLAStochastic.ForMathlib.Analysis.Complex.ParametricDeriv
import PLAStochastic.ForMathlib.Analysis.Complex.TimeOperatorHolomorphy

/-! # Genuine complete time-operator pair germs with Banach-space parameters -/

noncomputable section
open Complex
namespace PGM

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem analyticAt_complete_parametric_time_pair
    {A U : E × ℂ → ℂ} {b z : E → ℂ} {x : E} (lam : ℂ)
    (hA : AnalyticAt ℂ A (x, z x)) (hU : AnalyticAt ℂ U (x, z x))
    (hb : AnalyticAt ℂ b x) (hz : AnalyticAt ℂ z x) (hw : 1 + b x * lam ≠ 0) :
    AnalyticAt ℂ (fun u => exp ((b u * z u) * (1 + b u * lam)) * (A (u, z u)) ^ 2 *
      (-(1 / (1 + b u * lam)) * deriv (fun w => U (u, w)) (z u) - b u * U (u, z u))) x := by
  have ha := hA.comp (x := x) (f := fun u => (u, z u)) (analyticAt_id.prod hz)
  have hu := hU.comp (x := x) (f := fun u => (u, z u)) (analyticAt_id.prod hz)
  have hd : AnalyticAt ℂ (fun u => deriv (fun w => U (u, w)) (z u)) x := by
    simpa only [iteratedDeriv_one, id_eq] using! hU.iteratedDeriv_snd_comp analyticAt_id hz 1
  have hwidth : AnalyticAt ℂ (fun u => 1 + b u * lam) x :=
    analyticAt_const.add (hb.mul analyticAt_const)
  exact (((hb.mul hz).mul hwidth).cexp.mul (ha.pow 2)).mul
    ((((analyticAt_const.div hwidth hw).neg).mul hd).sub (hb.mul hu))

end PGM
