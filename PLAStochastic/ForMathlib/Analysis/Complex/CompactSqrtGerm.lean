import PLAStochastic.ForMathlib.Analysis.Complex.ParametricInverseLift
import PLAStochastic.ForMathlib.Analysis.Complex.ParametricInverseGerm
import PLAStochastic.ForMathlib.Analysis.Complex.CompactLiftDerivative
import PLAStochastic.ForMathlib.Analysis.Complex.ScalarBlockDerivative
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add

/-! # Genuine square-root germs in compact continuous-function spaces -/

noncomputable section
open Complex Filter Topology
namespace PGM

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

/-- The scalar and compact-function square roots agree on a common genuine
neighborhood, including nonconstant function arguments. -/
theorem exists_analytic_compact_sqrt_germ (s₀ : ℂ) (hs₀ : s₀ ≠ 0) :
    ∃ g : ℂ → ℂ, ∃ G : C(K, ℂ) → C(K, ℂ),
      AnalyticAt ℂ g 0 ∧ g 0 = s₀ ∧ AnalyticAt ℂ G 0 ∧ G 0 = ContinuousMap.const K s₀ ∧
      (∀ᶠ z in 𝓝 (0 : ℂ), (g z) ^ 2 = s₀ ^ 2 + z) ∧
      (∀ᶠ S in 𝓝 (0 : C(K, ℂ)), (G S) ^ 2 = ContinuousMap.const K (s₀ ^ 2) + S) ∧
      (∀ᶠ S in 𝓝 (0 : C(K, ℂ)), ∀ k, G S k = g (S k)) := by
  let f : ℂ × ℂ → ℂ := fun u => (s₀ + u.2) ^ 2 - s₀ ^ 2
  have hf : AnalyticAt ℂ f (0, 0) :=
    ((analyticAt_const.add analyticAt_snd).pow 2).sub analyticAt_const
  have hz : ∀ p : ℂ, f (p, 0) = 0 := by intro p; simp [f]
  have hs : HasDerivAt (fun s : ℂ => f (0, s)) (2 * s₀) 0 := by
    simpa [f, Pi.pow_def, id_eq] using!
      (((hasDerivAt_id (0 : ℂ)).const_add s₀).pow 2).sub_const (s₀ ^ 2)
  have hd : HasFDerivAt f ((2 * s₀) • ContinuousLinearMap.snd ℂ ℂ ℂ) (0, 0) :=
    hasFDerivAt_scalar_block_of_zero_section hf.differentiableAt
      (Filter.Eventually.of_forall hz) hs
  have hV : 2 * s₀ ≠ 0 := mul_ne_zero (by norm_num) hs₀
  obtain ⟨g, hg, hg₀, hgr, hgl⟩ := exists_analytic_parametric_inverse_germ hf hd hV (hz 0)
  let H : ℂ × C(K, ℂ) → C(K, ℂ) := fun u =>
    (ContinuousMap.const K s₀ + u.2) ^ 2 - ContinuousMap.const K (s₀ ^ 2)
  have hH : AnalyticAt ℂ H (0, 0) :=
    ((analyticAt_const.add analyticAt_snd).pow 2).sub analyticAt_const
  have he : ∀ᶠ u in 𝓝 ((0 : ℂ), (0 : C(K, ℂ))), ∀ k, H u k = f (u.1, u.2 k) := by
    apply Filter.Eventually.of_forall
    intro u k
    simp [H, f]
  have hdH := hasFDerivAt_compact_lift_of_scalar_block hH hd he
  have hH₀ : H (0, 0) = 0 := by
    apply ContinuousMap.ext
    intro k
    simp [H]
  obtain ⟨G, hG, hG₀, hGr, hGe⟩ :=
    exists_analytic_parametric_inverse_lift_germ hH hdH hV hH₀ he hgl
  have hm : AnalyticAt ℂ (fun z : ℂ => ((0 : ℂ), z)) 0 :=
    analyticAt_const.prod analyticAt_id
  have hM : AnalyticAt ℂ (fun S : C(K, ℂ) => ((0 : ℂ), S)) 0 :=
    analyticAt_const.prod analyticAt_id
  refine ⟨fun z => s₀ + g (0, z), fun S => ContinuousMap.const K s₀ + G (0, S),
    analyticAt_const.add (hg.comp hm), by simp [hg₀],
    analyticAt_const.add (hG.comp hM), by simp [hG₀], ?_, ?_, ?_⟩
  · filter_upwards [hm.continuousAt.tendsto.eventually hgr] with z hz
    change (s₀ + g (0, z)) ^ 2 - s₀ ^ 2 = z at hz
    exact (eq_add_of_sub_eq hz).trans (add_comm z (s₀ ^ 2))
  · filter_upwards [hM.continuousAt.tendsto.eventually hGr] with S hS
    change (ContinuousMap.const K s₀ + G (0, S)) ^ 2 - ContinuousMap.const K (s₀ ^ 2) = S at hS
    exact (eq_add_of_sub_eq hS).trans (add_comm S (ContinuousMap.const K (s₀ ^ 2)))
  · filter_upwards [hM.continuousAt.tendsto.eventually hGe] with S hS
    intro k
    simp only [ContinuousMap.add_apply, ContinuousMap.const_apply, hS k]

end PGM
