import PLAStochastic.ForMathlib.Analysis.Complex.ParametricBanachInverseGerm
import PLAStochastic.ForMathlib.Analysis.Complex.CompactLiftDerivative

/-! # Actual compact inverses with spatially varying Banach parameters -/

noncomputable section
open Complex Filter Topology Metric
namespace PGM

variable {E F K : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [TopologicalSpace K] [CompactSpace K]

def compactParameterEvalCLM (k : K) : (E × C(K, ℂ)) →L[ℂ] (E × ℂ) :=
  (ContinuousLinearMap.fst ℂ E C(K, ℂ)).prod
    ((ContinuousMap.evalCLM ℂ k).comp (ContinuousLinearMap.snd ℂ E C(K, ℂ)))

omit [CompactSpace K] in
theorem compactParameterEvalCLM_apply (k : K) (p : E) (S : C(K, ℂ)) :
    compactParameterEvalCLM k (p, S) = (p, S k) := rfl

theorem compactParameterEvalCLM_norm_le_one (k : K) :
    ‖compactParameterEvalCLM (E := E) k‖ ≤ 1 := by
  refine (compactParameterEvalCLM (E := E) k).opNorm_le_bound (by norm_num) ?_
  intro u
  change ‖(u.1, u.2 k)‖ ≤ 1 * ‖u‖
  rw [Prod.norm_def, one_mul, Prod.norm_def]
  exact max_le_max le_rfl ((u.2).norm_coe_le_norm k)

theorem hasFDerivAt_indexed_compact_lift_of_scalar_block
    {L : K → F →L[ℂ] E} {f : E × ℂ → ℂ} {H : F × C(K, ℂ) → C(K, ℂ)}
    {p₀ : E} {P₀ : F} {V : ℂ} (hbase : ∀ k, L k P₀ = p₀)
    (hH : AnalyticAt ℂ H (P₀, 0))
    (hdf : HasFDerivAt f (V • ContinuousLinearMap.snd ℂ E ℂ) (p₀, 0))
    (happly : ∀ᶠ u in 𝓝 (P₀, (0 : C(K, ℂ))), ∀ k, H u k = f (L k u.1, u.2 k)) :
    HasFDerivAt H (V • ContinuousLinearMap.snd ℂ F C(K, ℂ)) (P₀, 0) := by
  have he : fderiv ℂ H (P₀, 0) = V • ContinuousLinearMap.snd ℂ F C(K, ℂ) := by
    apply ContinuousLinearMap.ext
    intro u
    apply ContinuousMap.ext
    intro k
    let M : F × C(K, ℂ) →L[ℂ] E × ℂ :=
      ((L k).comp (ContinuousLinearMap.fst ℂ F C(K, ℂ))).prod
        ((ContinuousMap.evalCLM ℂ k).comp (ContinuousLinearMap.snd ℂ F C(K, ℂ)))
    have hdf' : HasFDerivAt f (V • ContinuousLinearMap.snd ℂ E ℂ) (M (P₀, 0)) := by
      simpa [M, hbase] using hdf
    have hdS := hdf'.comp (P₀, (0 : C(K, ℂ))) M.hasFDerivAt
    have hdH := (ContinuousMap.evalCLM ℂ k).hasFDerivAt.comp (P₀, (0 : C(K, ℂ)))
      hH.differentiableAt.hasFDerivAt
    have heq : (fun v : F × C(K, ℂ) => f (M v)) =ᶠ[𝓝 (P₀, 0)] (fun v => H v k) := by
      filter_upwards [happly] with v hv
      exact (hv k).symm
    have hunique := (hdH.congr_of_eventuallyEq heq).unique hdS
    have hv := congrArg (fun T : F × C(K, ℂ) →L[ℂ] ℂ => T u) hunique
    simpa [M] using hv
  rw [← he]
  exact hH.differentiableAt.hasFDerivAt

variable [CompleteSpace F]

/-- Parameters may vary with the compact index through uniformly contractive
evaluation maps. The functional inverse agrees with every actual scalar inverse
on a single genuine neighborhood. -/
theorem exists_analytic_indexed_compact_inverse_germ
    {L : K → F →L[ℂ] E} {f g : E × ℂ → ℂ} {H : F × C(K, ℂ) → C(K, ℂ)}
    {p₀ : E} {P₀ : F} {V : ℂ}
    (hbase : ∀ k, L k P₀ = p₀) (hL : ∀ k, ‖L k‖ ≤ 1)
    (hH : AnalyticAt ℂ H (P₀, 0))
    (hHD : HasFDerivAt H (V • ContinuousLinearMap.snd ℂ F C(K, ℂ)) (P₀, 0))
    (hV : V ≠ 0) (hH₀ : H (P₀, 0) = 0)
    (happly : ∀ᶠ u in 𝓝 (P₀, (0 : C(K, ℂ))), ∀ k, H u k = f (L k u.1, u.2 k))
    (hleft : ∀ᶠ u in 𝓝 (p₀, (0 : ℂ)), g (u.1, f u) = u.2) :
    ∃ G : F × C(K, ℂ) → C(K, ℂ), AnalyticAt ℂ G (P₀, 0) ∧ G (P₀, 0) = 0 ∧
      (∀ᶠ u in 𝓝 (P₀, (0 : C(K, ℂ))), H (u.1, G u) = u.2) ∧
      (∀ᶠ u in 𝓝 (P₀, (0 : C(K, ℂ))), ∀ k, G u k = g (L k u.1, u.2 k)) := by
  obtain ⟨G, hG, hG₀, hright, _⟩ := exists_analytic_parametric_banach_inverse_germ hH hHD hV hH₀
  refine ⟨G, hG, hG₀, hright, ?_⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hleft
  have hc : ContinuousAt (fun u : F × C(K, ℂ) => (u.1, G u)) (P₀, 0) :=
    continuousAt_fst.prodMk hG.continuousAt
  have ht : Tendsto (fun u : F × C(K, ℂ) => (u.1, G u)) (𝓝 (P₀, 0)) (𝓝 (P₀, 0)) := by
    simpa only [hG₀] using hc.tendsto
  have hnear : ∀ᶠ u in 𝓝 (P₀, (0 : C(K, ℂ))), (u.1, G u) ∈ ball (P₀, 0) r :=
    ht (ball_mem_nhds _ hr)
  filter_upwards [hright, ht happly, hnear] with u hu he hn
  intro k
  have hnorm : max ‖u.1 - P₀‖ ‖G u‖ < r := by
    rw [mem_ball, dist_eq_norm] at hn
    simpa [Prod.norm_def] using hn
  have hparam : ‖L k u.1 - p₀‖ ≤ ‖u.1 - P₀‖ := by
    rw [← hbase k, ← map_sub]
    exact ((L k).le_opNorm _).trans (by
      simpa using mul_le_mul_of_nonneg_right (hL k) (norm_nonneg (u.1 - P₀)))
  have hk : (L k u.1, G u k) ∈ ball (p₀, (0 : ℂ)) r := by
    rw [mem_ball, dist_eq_norm]
    simpa [Prod.norm_def] using max_lt
      (hparam.trans_lt (max_lt_iff.mp hnorm).1)
      ((G u).norm_coe_le_norm k |>.trans_lt (max_lt_iff.mp hnorm).2)
  have hs : g (L k u.1, f (L k u.1, G u k)) = G u k := hball hk
  have hf := congrArg (fun S : C(K, ℂ) => S k) hu
  change H (u.1, G u) k = u.2 k at hf
  rw [he k] at hf
  rw [hf] at hs
  exact hs.symm

end PGM
