import PLAStochastic.ForMathlib.Analysis.Complex.ImplicitQuadraticJet
import Mathlib.Analysis.Asymptotics.Lemmas

/-! # One fixed-derivative Newton step improves a finite implicit-root jet -/

noncomputable section
open Complex Set Metric Filter Topology Asymptotics
namespace PGM

def quadraticNewtonStep (P g : ℂ → ℂ) (lam z gap : ℂ) (b : ℂ) : ℂ :=
  g b - (g b ^ 2 * P (b * g b) + lam * g b - z * (1 + b * lam)) / gap

theorem isBigO_complex_pow_nhds_zero_of_le {n m : ℕ} (hnm : n ≤ m) :
    (fun b : ℂ => b ^ m) =O[𝓝 0] (fun b => b ^ n) := by
  refine isBigO_iff.mpr ⟨1, ?_⟩
  filter_upwards [ball_mem_nhds (0 : ℂ) (by norm_num : 0 < (1 : ℝ))] with b hb
  simp only [norm_pow, one_mul]
  exact pow_le_pow_of_le_one (norm_nonneg b) (mem_ball_zero_iff.mp hb).le hnm

theorem quadraticNewtonStep_improves_order {H P f g : ℂ → ℂ} {lam z : ℂ}
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) (hH : AnalyticAt ℂ H 0)
    (hS : AnalyticAt ℂ (fun b : ℂ => dslope H (b * g b) (b * f b)) 0)
    (hzero : f 0 = g 0) (hgap : lam + 2 * f 0 * H 0 ≠ 0)
    (he : ∀ᶠ b : ℂ in 𝓝 0, f b ^ 2 * H (b * f b) + lam * f b = z * (1 + b * lam))
    (N k : ℕ)
    (hunit : (fun s => P s - H s) =O[𝓝 0] (fun s : ℂ => s ^ (N + 1)))
    (hfg : (fun b => f b - g b) =O[𝓝 0] (fun b : ℂ => b ^ k)) :
    (fun b => f b - quadraticNewtonStep P g lam z (lam + 2 * f 0 * H 0) b) =O[𝓝 0]
      (fun b : ℂ => b ^ (min (k + 1) (N + 1))) := by
  let gap := lam + 2 * f 0 * H 0
  let E : ℂ → ℂ := fun b => lam + (f b + g b) * H (b * f b) +
    b * g b ^ 2 * dslope H (b * g b) (b * f b)
  have hcomp : AnalyticAt ℂ (fun b : ℂ => H (b * f b)) 0 :=
    hH.comp_of_eq ((analyticAt_id (𝕜 := ℂ)).mul hf) (by simp)
  have hE : AnalyticAt ℂ E 0 :=
    (analyticAt_const.add ((hf.add hg).mul hcomp)).add
      (((analyticAt_id (𝕜 := ℂ)).mul (hg.pow 2)).mul hS)
  have hE0 : E 0 = gap := by
    dsimp only [gap, E]
    simp only [zero_mul, add_zero]
    rw [← hzero]
    ring
  have hvan : (fun b : ℂ => 1 - E b / gap) =O[𝓝 0] (fun b => b) := by
    have han : AnalyticAt ℂ (fun b : ℂ => 1 - E b / gap) 0 :=
      analyticAt_const.sub (hE.div_const (c := gap))
    have ht := han.differentiableAt.hasDerivAt.isBigO_sub
    have hd : gap ≠ 0 := hgap
    simpa only [hE0, div_self hd, sub_self, sub_zero] using! ht
  have hfirst : (fun b : ℂ => (f b - g b) * (1 - E b / gap)) =O[𝓝 0]
      (fun b : ℂ => b ^ (min (k + 1) (N + 1))) := by
    have ht := (hfg.mul hvan).congr_right (fun b => (pow_succ b k).symm)
    exact ht.trans (isBigO_complex_pow_nhds_zero_of_le (min_le_left _ _))
  have hgb : (fun b : ℂ => g b) =O[𝓝 0] (fun _ => (1 : ℂ)) :=
    isBigO_const_of_tendsto hg.continuousAt.tendsto one_ne_zero
  have hbg : (fun b : ℂ => b * g b) =O[𝓝 0] (fun b => b) := by
    simpa only [mul_one] using! (isBigO_refl (fun b : ℂ => b) (𝓝 0)).mul hgb
  have hbg0 : Tendsto (fun b : ℂ => b * g b) (𝓝 0) (𝓝 0) := by
    simpa using! (continuousAt_id.mul hg.continuousAt).tendsto
  have hu : (fun b : ℂ => P (b * g b) - H (b * g b)) =O[𝓝 0]
      (fun b => b ^ (N + 1)) :=
    (hunit.comp_tendsto hbg0).trans (hbg.pow (N + 1))
  have hsecond : (fun b : ℂ => g b ^ 2 * (P (b * g b) - H (b * g b)) / gap) =O[𝓝 0]
      (fun b : ℂ => b ^ (min (k + 1) (N + 1))) := by
    have ht := ((hgb.pow 2).mul hu).const_mul_left gap⁻¹
    have ht' : (fun b : ℂ => g b ^ 2 * (P (b * g b) - H (b * g b)) / gap) =O[𝓝 0]
        (fun b => b ^ (N + 1)) := by
      simpa only [one_pow, one_mul, div_eq_mul_inv, mul_comm] using! ht
    exact ht'.trans (isBigO_complex_pow_nhds_zero_of_le (min_le_right _ _))
  apply (hfirst.add hsecond).congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [he] with b hb
  have hslope := sub_smul_dslope H (b * g b) (b * f b)
  simp only [smul_eq_mul] at hslope
  dsimp only [quadraticNewtonStep, E]
  dsimp only [gap]
  generalize H (b * f b) = A at hb hslope ⊢
  generalize H (b * g b) = B at hslope ⊢
  generalize P (b * g b) = C at ⊢
  generalize dslope H (b * g b) (b * f b) = S at hslope ⊢
  field_simp [hgap]
  linear_combination -hb - g b ^ 2 * hslope

end PGM
