import PLAStochastic.ForMathlib.Analysis.Complex.CompactSqrtGerm
import PLAStochastic.ForMathlib.Analysis.Complex.IndexedCompactInverse
import PLAStochastic.ForMathlib.Analysis.Complex.ParametricInverseDerivative

/-! # Genuine coherent scalar and compact-function Morse inverses -/

noncomputable section
open Complex Filter Topology
namespace PGM

variable {E F K : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  [TopologicalSpace K] [CompactSpace K]

/-- An actual analytic quadratic unit gives a genuine Morse inverse. Functional
parameters may vary with position through contractive evaluations. -/
theorem exists_analytic_compact_morse_inverse_oriented
    {L : K → F →L[ℂ] E} {U : E × ℂ → ℂ} {W : F × C(K, ℂ) → C(K, ℂ)}
    {p₀ : E} {P₀ : F} {s₀ : ℂ}
    (hbase : ∀ k, L k P₀ = p₀) (hL : ∀ k, ‖L k‖ ≤ 1) (hs₀ : s₀ ≠ 0)
    (hU : AnalyticAt ℂ U (p₀, 0)) (hU₀ : U (p₀, 0) = s₀ ^ 2)
    (hW : AnalyticAt ℂ W (P₀, 0))
    (hW₀ : W (P₀, 0) = ContinuousMap.const K (s₀ ^ 2))
    (he : ∀ᶠ u in 𝓝 (P₀, (0 : C(K, ℂ))), ∀ k, W u k = U (L k u.1, u.2 k)) :
    ∃ r : E × ℂ → ℂ, ∃ R : F × C(K, ℂ) → C(K, ℂ),
      AnalyticAt ℂ r (p₀, 0) ∧ r (p₀, 0) = 0 ∧
      HasFDerivAt r (s₀⁻¹ • ContinuousLinearMap.snd ℂ E ℂ) (p₀, 0) ∧
      AnalyticAt ℂ R (P₀, 0) ∧ R (P₀, 0) = 0 ∧
      (∀ᶠ u in 𝓝 (p₀, (0 : ℂ)), (r u) ^ 2 * U (u.1, r u) = u.2 ^ 2) ∧
      (∀ᶠ u in 𝓝 (P₀, (0 : C(K, ℂ))), (R u) ^ 2 * W (u.1, R u) = u.2 ^ 2) ∧
      (∀ᶠ u in 𝓝 (P₀, (0 : C(K, ℂ))), ∀ k, R u k = r (L k u.1, u.2 k)) ∧
      (∀ᶠ p in 𝓝 p₀, r (p, 0) = 0) := by
  obtain ⟨g, G, hg, hg₀, hG, hG₀, hgr, hGr, hGe⟩ :=
    exists_analytic_compact_sqrt_germ (K := K) s₀ hs₀
  let a : E × ℂ → ℂ := fun u => U u - s₀ ^ 2
  let A : F × C(K, ℂ) → C(K, ℂ) := fun u => W u - ContinuousMap.const K (s₀ ^ 2)
  have ha : AnalyticAt ℂ a (p₀, 0) := hU.sub analyticAt_const
  have hA : AnalyticAt ℂ A (P₀, 0) := hW.sub analyticAt_const
  have ha₀ : a (p₀, 0) = 0 := by simp [a, hU₀]
  have hA₀ : A (P₀, 0) = 0 := by simp [A, hW₀]
  have hg' : AnalyticAt ℂ g (a (p₀, 0)) := by simpa only [ha₀] using hg
  have hG' : AnalyticAt ℂ G (A (P₀, 0)) := by simpa only [hA₀] using hG
  let f : E × ℂ → ℂ := fun u => u.2 * g (a u)
  let H : F × C(K, ℂ) → C(K, ℂ) := fun u => u.2 * G (A u)
  have hf : AnalyticAt ℂ f (p₀, 0) := analyticAt_snd.mul (hg'.comp ha)
  have hH : AnalyticAt ℂ H (P₀, 0) := analyticAt_snd.mul (hG'.comp hA)
  have hz : ∀ p : E, f (p, 0) = 0 := by intro p; simp [f]
  have hcoef : AnalyticAt ℂ (fun x : ℂ => g (a (p₀, x))) 0 :=
    (hg'.comp ha).comp (analyticAt_const.prod analyticAt_id)
  have hs : HasDerivAt (fun x : ℂ => f (p₀, x)) s₀ 0 := by
    simpa [f, ha₀, hg₀, Pi.mul_def, id_eq] using!
      (hasDerivAt_id (0 : ℂ)).mul hcoef.differentiableAt.hasDerivAt
  have hd := hasFDerivAt_scalar_block_of_zero_section hf.differentiableAt
    (Filter.Eventually.of_forall hz) hs
  obtain ⟨r, hr, hr₀, hrr, hrl⟩ := exists_analytic_parametric_inverse_germ hf hd hs₀ (hz p₀)
  have hdr := hasFDerivAt_parametric_inverse_of_scalar_block hd hr.differentiableAt hr₀ hs₀ hrr
  have htA : Tendsto A (𝓝 (P₀, (0 : C(K, ℂ)))) (𝓝 (0 : C(K, ℂ))) := by
    simpa only [hA₀] using hA.continuousAt.tendsto
  have hHe : ∀ᶠ u in 𝓝 (P₀, (0 : C(K, ℂ))), ∀ k,
      H u k = f (L k u.1, u.2 k) := by
    filter_upwards [he, htA.eventually hGe] with u hu hs
    intro k
    simp only [H, f, ContinuousMap.mul_apply, hs k]
    congr 1
    simp [A, a, hu k]
  have hdH := hasFDerivAt_indexed_compact_lift_of_scalar_block hbase hH hd hHe
  have hH₀ : H (P₀, 0) = 0 := by simp [H]
  obtain ⟨R, hR, hR₀, hRR, hRe⟩ := exists_analytic_indexed_compact_inverse_germ
    hbase hL hH hdH hs₀ hH₀ hHe hrl
  have htr : Tendsto (fun u : E × ℂ => (u.1, r u))
      (𝓝 (p₀, (0 : ℂ))) (𝓝 (p₀, (0 : ℂ))) := by
    simpa only [hr₀] using (continuousAt_fst.prodMk hr.continuousAt).tendsto
  have htR : Tendsto (fun u : F × C(K, ℂ) => (u.1, R u))
      (𝓝 (P₀, (0 : C(K, ℂ)))) (𝓝 (P₀, (0 : C(K, ℂ)))) := by
    simpa only [hR₀] using (continuousAt_fst.prodMk hR.continuousAt).tendsto
  have hta : Tendsto a (𝓝 (p₀, (0 : ℂ))) (𝓝 (0 : ℂ)) := by
    simpa only [ha₀] using ha.continuousAt.tendsto
  refine ⟨r, R, hr, hr₀, hdr, hR, hR₀, ?_, ?_, hRe, ?_⟩
  · filter_upwards [hrr, htr.eventually (hta.eventually hgr)] with u hu hs
    change f (u.1, r u) = u.2 at hu
    change (g (a (u.1, r u))) ^ 2 = s₀ ^ 2 + a (u.1, r u) at hs
    have hs' : (g (a (u.1, r u))) ^ 2 = U (u.1, r u) := by
      simpa [a] using hs
    rw [← hs', ← mul_pow]
    exact congrArg (fun z : ℂ => z ^ 2) hu
  · filter_upwards [hRR, htR.eventually (htA.eventually hGr)] with u hu hs
    change H (u.1, R u) = u.2 at hu
    change (G (A (u.1, R u))) ^ 2 = ContinuousMap.const K (s₀ ^ 2) + A (u.1, R u) at hs
    have hs' : (G (A (u.1, R u))) ^ 2 = W (u.1, R u) := by
      simpa [A] using hs
    rw [← hs', ← mul_pow]
    exact congrArg (fun S : C(K, ℂ) => S ^ 2) hu
  · have hm : AnalyticAt ℂ (fun p : E => (p, (0 : ℂ))) p₀ :=
      analyticAt_id.prod analyticAt_const
    filter_upwards [hm.continuousAt.tendsto.eventually hrl] with p hp
    change r (p, f (p, 0)) = 0 at hp
    simpa only [hz] using hp

/-- The same genuine inverse construction without its optional derivative readout. -/
theorem exists_analytic_compact_morse_inverse
    {L : K → F →L[ℂ] E} {U : E × ℂ → ℂ} {W : F × C(K, ℂ) → C(K, ℂ)}
    {p₀ : E} {P₀ : F} {s₀ : ℂ}
    (hbase : ∀ k, L k P₀ = p₀) (hL : ∀ k, ‖L k‖ ≤ 1) (hs₀ : s₀ ≠ 0)
    (hU : AnalyticAt ℂ U (p₀, 0)) (hU₀ : U (p₀, 0) = s₀ ^ 2)
    (hW : AnalyticAt ℂ W (P₀, 0))
    (hW₀ : W (P₀, 0) = ContinuousMap.const K (s₀ ^ 2))
    (he : ∀ᶠ u in 𝓝 (P₀, (0 : C(K, ℂ))), ∀ k, W u k = U (L k u.1, u.2 k)) :
    ∃ r : E × ℂ → ℂ, ∃ R : F × C(K, ℂ) → C(K, ℂ),
      AnalyticAt ℂ r (p₀, 0) ∧ r (p₀, 0) = 0 ∧
      AnalyticAt ℂ R (P₀, 0) ∧ R (P₀, 0) = 0 ∧
      (∀ᶠ u in 𝓝 (p₀, (0 : ℂ)), (r u) ^ 2 * U (u.1, r u) = u.2 ^ 2) ∧
      (∀ᶠ u in 𝓝 (P₀, (0 : C(K, ℂ))), (R u) ^ 2 * W (u.1, R u) = u.2 ^ 2) ∧
      (∀ᶠ u in 𝓝 (P₀, (0 : C(K, ℂ))), ∀ k, R u k = r (L k u.1, u.2 k)) ∧
      (∀ᶠ p in 𝓝 p₀, r (p, 0) = 0) := by
  obtain ⟨r, R, hr, hr₀, _, hR, hR₀, hrr, hRR, heR, hz⟩ :=
    exists_analytic_compact_morse_inverse_oriented hbase hL hs₀ hU hU₀ hW hW₀ he
  exact ⟨r, R, hr, hr₀, hR, hR₀, hrr, hRR, heR, hz⟩

end PGM
