import PLAStochastic.ForMathlib.Analysis.Complex.ContinuousFDerivTwo
import PLAStochastic.ForMathlib.Analysis.Complex.TaylorSeriesBudget
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-! # Commutation of genuine complex partial derivatives and scale Taylor coefficients -/

noncomputable section
open Complex Set Metric Filter Topology PowerSeries
namespace PGM

theorem differentiableOn_deriv_snd {U : Set (ℂ × ℂ)} (hU : IsOpen U)
    {F : ℂ × ℂ → ℂ} (hF : DifferentiableOn ℂ F U) :
    DifferentiableOn ℂ (fun x : ℂ × ℂ => deriv (fun z => F (x.1, z)) x.2) U := by
  have hs : DifferentiableOn ℂ (fun x : ℂ × ℂ => F (x.2, x.1))
      ((fun x : ℂ × ℂ => (x.2, x.1)) ⁻¹' U) :=
    hF.comp (by fun_prop) (fun _ hx => hx)
  exact (differentiableOn_deriv_fst (hU.preimage (by fun_prop)) hs).comp
    (f := fun x : ℂ × ℂ => (x.2, x.1)) (by fun_prop) (fun _ hx => hx)

theorem differentiableOn_complex_fderiv {U : Set (ℂ × ℂ)} (hU : IsOpen U)
    {F : ℂ × ℂ → ℂ} (hF : DifferentiableOn ℂ F U) :
    DifferentiableOn ℂ (fderiv ℂ F) U := by
  have hp := differentiableOn_deriv_fst hU hF
  have hq := differentiableOn_deriv_snd hU hF
  apply ((hp.smul_const (ContinuousLinearMap.fst ℂ ℂ ℂ)).add
    (hq.smul_const (ContinuousLinearMap.snd ℂ ℂ ℂ))).congr
  intro x hx
  exact fderiv_eq_complex_partials ((hF x hx).differentiableAt (hU.mem_nhds hx))

theorem deriv_fst_snd_comm {U : Set (ℂ × ℂ)} (hU : IsOpen U)
    {F : ℂ × ℂ → ℂ} (hF : DifferentiableOn ℂ F U) {b z : ℂ} (hx : (b, z) ∈ U) :
    deriv (fun b => deriv (fun z => F (b, z)) z) b =
      deriv (fun z => deriv (fun b => F (b, z)) b) z := by
  have hd := ((differentiableOn_complex_fderiv hU hF) (b, z) hx).differentiableAt (hU.mem_nhds hx)
  have hnear : ∀ᶠ x in 𝓝 (b, z), HasFDerivAt F (fderiv ℂ F x) x := by
    filter_upwards [hU.mem_nhds hx] with x hx using ((hF x hx).differentiableAt (hU.mem_nhds hx)).hasFDerivAt
  have hs := second_derivative_symmetric_of_eventually hnear hd.hasFDerivAt
    ((1, 0) : ℂ × ℂ) ((0, 1) : ℂ × ℂ)
  have hp : ∀ x ∈ U, deriv (fun b => F (b, x.2)) x.1 = fderiv ℂ F x (1, 0) := by
    intro x hx
    have hh := (((hF x hx).differentiableAt (hU.mem_nhds hx)).hasFDerivAt.comp x.1
      ((hasFDerivAt_id (𝕜 := ℂ) x.1).prodMk (hasFDerivAt_const (𝕜 := ℂ) x.2 x.1))).hasDerivAt.deriv
    simpa [Function.comp_def] using hh
  have hq : ∀ x ∈ U, deriv (fun z => F (x.1, z)) x.2 = fderiv ℂ F x (0, 1) := by
    intro x hx
    have hh := (((hF x hx).differentiableAt (hU.mem_nhds hx)).hasFDerivAt.comp x.2
      ((hasFDerivAt_const (𝕜 := ℂ) x.1 x.2).prodMk (hasFDerivAt_id (𝕜 := ℂ) x.2))).hasDerivAt.deriv
    simpa [Function.comp_def] using hh
  have heq : (fun w => deriv (fun ζ => F (w, ζ)) z) =ᶠ[𝓝 b]
      (fun w => fderiv ℂ F (w, z) (0, 1)) := by
    filter_upwards [((continuous_id.prodMk continuous_const).continuousAt.eventually (hU.mem_nhds hx))]
      with w hw using hq (w, z) hw
  have hep : (fun w => deriv (fun ζ => F (ζ, w)) b) =ᶠ[𝓝 z]
      (fun w => fderiv ℂ F (b, w) (1, 0)) := by
    filter_upwards [((continuous_const.prodMk continuous_id).continuousAt.eventually (hU.mem_nhds hx))]
      with w hw using hp (b, w) hw
  rw [heq.deriv_eq, hep.deriv_eq]
  have h₁ := ((hd.hasFDerivAt.clm_apply (hasFDerivAt_const (𝕜 := ℂ) ((0, 1) : ℂ × ℂ) (b, z))).comp b
    ((hasFDerivAt_id (𝕜 := ℂ) b).prodMk (hasFDerivAt_const (𝕜 := ℂ) z b))).hasDerivAt.deriv
  have h₂ := ((hd.hasFDerivAt.clm_apply (hasFDerivAt_const (𝕜 := ℂ) ((1, 0) : ℂ × ℂ) (b, z))).comp z
    ((hasFDerivAt_const (𝕜 := ℂ) b z).prodMk (hasFDerivAt_id (𝕜 := ℂ) z))).hasDerivAt.deriv
  simp [Function.comp_def] at h₁ h₂
  exact h₁.trans (hs.trans h₂.symm)

theorem iteratedDeriv_fst_deriv_snd_comm {U : Set (ℂ × ℂ)} (hU : IsOpen U)
    {F : ℂ × ℂ → ℂ} (hF : DifferentiableOn ℂ F U) (n : ℕ) {b z : ℂ} (hx : (b, z) ∈ U) :
    iteratedDeriv n (fun b => deriv (fun z => F (b, z)) z) b =
      deriv (fun z => iteratedDeriv n (fun b => F (b, z)) b) z := by
  induction n generalizing b z with
  | zero => simp
  | succ n ih =>
    have hJ := differentiableOn_iteratedDeriv_fst hU hF n
    have he : (fun w => iteratedDeriv n (fun b => deriv (fun z => F (b, z)) z) w) =ᶠ[𝓝 b]
        (fun w => deriv (fun z => iteratedDeriv n (fun b => F (b, z)) w) z) := by
      filter_upwards [((continuous_id.prodMk continuous_const).continuousAt.eventually (hU.mem_nhds hx))]
        with w hw using ih hw
    rw [iteratedDeriv_succ, he.deriv_eq]
    simpa only [iteratedDeriv_succ] using deriv_fst_snd_comm hU hJ hx

theorem deriv_complexTaylorSeries_coeff_snd {U : Set (ℂ × ℂ)} (hU : IsOpen U)
    {F : ℂ × ℂ → ℂ} (hF : DifferentiableOn ℂ F U) (n : ℕ) {b z : ℂ} (hx : (b, z) ∈ U) :
    deriv (fun z => coeff n (complexTaylorSeries (fun b => F (b, z)) b)) z =
      coeff n (complexTaylorSeries (fun b => deriv (fun z => F (b, z)) z) b) := by
  have hd := differentiableAt_slice_snd hU (differentiableOn_iteratedDeriv_fst hU hF n) hx
  simp only [complexTaylorSeries, coeff_mk]
  rw [deriv_const_mul _ hd, iteratedDeriv_fst_deriv_snd_comm hU hF n hx]

theorem iteratedDeriv_fst_snd_comm {U : Set (ℂ × ℂ)} (hU : IsOpen U)
    {F : ℂ × ℂ → ℂ} (hF : DifferentiableOn ℂ F U) (n m : ℕ) {b z : ℂ} (hx : (b, z) ∈ U) :
    iteratedDeriv n (fun b => iteratedDeriv m (fun z => F (b, z)) z) b =
      iteratedDeriv m (fun z => iteratedDeriv n (fun b => F (b, z)) b) z := by
  induction m generalizing b z with
  | zero => simp
  | succ m ih =>
    have hs : DifferentiableOn ℂ (fun x : ℂ × ℂ => F (x.2, x.1))
        ((fun x : ℂ × ℂ => (x.2, x.1)) ⁻¹' U) :=
      hF.comp (by fun_prop) (fun _ hx => hx)
    have hJ : DifferentiableOn ℂ
        (fun x : ℂ × ℂ => iteratedDeriv m (fun z => F (x.1, z)) x.2) U :=
      (differentiableOn_iteratedDeriv_fst (hU.preimage (by fun_prop)) hs m).comp
        (f := fun x : ℂ × ℂ => (x.2, x.1)) (by fun_prop) (fun _ hx => hx)
    have he : (fun w => iteratedDeriv n (fun b => iteratedDeriv m (fun z => F (b, z)) w) b) =ᶠ[𝓝 z]
        (fun w => iteratedDeriv m (fun z => iteratedDeriv n (fun b => F (b, z)) b) w) := by
      filter_upwards [((continuous_const.prodMk continuous_id).continuousAt.eventually (hU.mem_nhds hx))]
        with w hw using ih hw
    simpa only [iteratedDeriv_succ, he.deriv_eq] using
      iteratedDeriv_fst_deriv_snd_comm hU hJ n hx

theorem analyticAt_slice_fst_on_polydisc {F : ℂ × ℂ → ℂ} {B : ℝ} {z : ℂ}
    (hB : 0 < B) (hF : DifferentiableOn ℂ F (ball 0 B ×ˢ ball z B)) :
    AnalyticAt ℂ (fun b => F (b, z)) 0 := by
  have hs : DifferentiableOn ℂ (fun b => F (b, z)) (ball 0 B) :=
    hF.comp (f := fun b : ℂ => (b, z))
      (differentiableOn_id.prodMk (differentiableOn_const z))
      (fun _ hb => ⟨hb, mem_ball_self hB⟩)
  exact hs.analyticAt (ball_mem_nhds _ hB)

end PGM
