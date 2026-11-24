import PLAStochastic.ForMathlib.Analysis.Complex.CompactIntegralAnalytic
import Mathlib.Analysis.Analytic.Constructions

/-! # Genuine compact-function lifts of arbitrary analytic Banach-space germs -/

noncomputable section
open Complex Filter Topology
namespace PGM

variable {E F K : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [TopologicalSpace K] [CompactSpace K]

omit [NormedSpace ℂ E] [CompactSpace K] in
private theorem compact_eval_update {n : ℕ} [DecidableEq (Fin n)] (v : Fin n → C(K, E)) (i : Fin n)
    (X : C(K, E)) (k : K) :
    (fun j => Function.update v i X j k) = Function.update (fun j => v j k) i (X k) := by
  funext j
  by_cases h : j = i <;> simp [Function.update, h]

def compactMultilinearLift {n : ℕ} (f : ContinuousMultilinearMap ℂ (fun _ : Fin n => E) F) :
    ContinuousMultilinearMap ℂ (fun _ : Fin n => C(K, E)) C(K, F) :=
  (show MultilinearMap ℂ (fun _ : Fin n => C(K, E)) C(K, F) from
    { toFun := fun v => ⟨fun k => f (fun i => v i k),
        f.cont.comp (continuous_pi (fun i => (v i).continuous))⟩
      map_update_add' := by
        intro _ v i X Y
        apply ContinuousMap.ext
        intro k
        change f (fun j => Function.update v i (X + Y) j k) =
          f (fun j => Function.update v i X j k) + f (fun j => Function.update v i Y j k)
        simp only [compact_eval_update, ContinuousMap.add_apply]
        exact f.map_update_add (fun j => v j k) i (X k) (Y k)
      map_update_smul' := by
        intro _ v i c X
        apply ContinuousMap.ext
        intro k
        change f (fun j => Function.update v i (c • X) j k) =
          c • f (fun j => Function.update v i X j k)
        simp only [compact_eval_update, ContinuousMap.smul_apply]
        exact f.map_update_smul (fun j => v j k) i c (X k) }).mkContinuous ‖f‖ (by
    intro v
    apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg f)
      (Finset.prod_nonneg (fun i _ => norm_nonneg (v i))))).mpr
    intro k
    apply (f.le_opNorm (fun i => v i k)).trans
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg f)
    exact Finset.prod_le_prod (fun i _ => norm_nonneg (v i k))
      (fun i _ => (v i).norm_coe_le_norm k))

theorem compactMultilinearLift_apply {n : ℕ}
    (f : ContinuousMultilinearMap ℂ (fun _ : Fin n => E) F) (v : Fin n → C(K, E)) (k : K) :
    compactMultilinearLift f v k = f (fun i => v i k) := rfl

theorem compactMultilinearLift_norm_le {n : ℕ}
    (f : ContinuousMultilinearMap ℂ (fun _ : Fin n => E) F) : ‖compactMultilinearLift (K := K) f‖ ≤ ‖f‖ :=
  MultilinearMap.mkContinuous_norm_le _ (norm_nonneg f) _

def compactPowerSeriesLift (p : FormalMultilinearSeries ℂ E F) :
    FormalMultilinearSeries ℂ C(K, E) C(K, F) := fun n => compactMultilinearLift (p n)

theorem compactPowerSeriesLift_radius (p : FormalMultilinearSeries ℂ E F) :
    p.radius ≤ (compactPowerSeriesLift (K := K) p).radius :=
  FormalMultilinearSeries.radius_le_of_le (fun n => compactMultilinearLift_norm_le (p n))

/-- An arbitrary local analytic Banach-space germ admits an actual analytic lift
to compact continuous functions, with a single uniform pointwise neighborhood.
The lift is defined by its convergent multilinear series, so no global scalar
continuation or continuity assumption is needed. -/
theorem exists_analytic_compact_germ_lift [CompleteSpace F] {f : E → F} {x : E}
    (hf : AnalyticAt ℂ f x) :
    ∃ H : C(K, E) → C(K, F), AnalyticAt ℂ H (ContinuousMap.const K x) ∧
      H (ContinuousMap.const K x) = ContinuousMap.const K (f x) ∧
      (∀ᶠ U in 𝓝 (ContinuousMap.const K x), ∀ k, H U k = f (U k)) := by
  obtain ⟨p, r, hp⟩ := hf
  let q := compactPowerSeriesLift (K := K) p
  have hrq : r ≤ q.radius := hp.r_le.trans (compactPowerSeriesLift_radius p)
  have hq : AnalyticAt ℂ q.sum 0 :=
    (q.hasFPowerSeriesOnBall (hp.r_pos.trans_le hrq)).analyticAt
  let a : C(K, E) → C(K, E) := fun U => U - ContinuousMap.const K x
  have ha : AnalyticAt ℂ a (ContinuousMap.const K x) := analyticAt_id.sub analyticAt_const
  have ha₀ : a (ContinuousMap.const K x) = 0 := sub_self _
  let H : C(K, E) → C(K, F) := fun U => q.sum (a U)
  have hH : AnalyticAt ℂ H (ContinuousMap.const K x) := by
    have hq' : AnalyticAt ℂ q.sum (a (ContinuousMap.const K x)) := by
      simpa only [ha₀] using hq
    exact hq'.comp ha
  have ht : Tendsto a (𝓝 (ContinuousMap.const K x)) (𝓝 (0 : C(K, E))) := by
    simpa only [ha₀] using ha.continuousAt.tendsto
  have he : ∀ᶠ U in 𝓝 (ContinuousMap.const K x), ∀ k, H U k = f (U k) := by
    filter_upwards [ht.eventually (Metric.eball_mem_nhds _ hp.r_pos)] with U hU
    intro k
    have hk : U k - x ∈ Metric.eball (0 : E) r := by
      have hn : ‖U k - x‖ ≤ ‖a U‖ := by
        simpa [a] using (a U).norm_coe_le_norm k
      have hm : ENNReal.ofReal ‖a U‖ < r := by
        simpa only [Metric.mem_eball, edist_dist, dist_eq_norm, sub_zero] using hU
      simpa only [Metric.mem_eball, edist_dist, dist_eq_norm, sub_zero] using
        (ENNReal.ofReal_le_ofReal hn).trans_lt hm
    have hUq : a U ∈ Metric.eball (0 : C(K, E)) q.radius :=
      (Metric.mem_eball.mp hU).trans_le hrq
    have hs : HasSum (fun n : ℕ => p n (fun _ : Fin n => U k - x)) (H U k) := by
      simpa only [H, q, a, compactPowerSeriesLift, compactMultilinearLift_apply,
        ContinuousMap.sub_apply, ContinuousMap.const_apply] using!
        (ContinuousMap.evalCLM ℂ k).hasSum (q.hasSum hUq)
    have hs' : HasSum (fun n : ℕ => p n (fun _ : Fin n => U k - x)) (f (U k)) := by
      simpa only [add_sub_cancel] using hp.hasSum hk
    exact hs.unique hs'
  refine ⟨H, hH, ?_, he⟩
  apply ContinuousMap.ext
  intro k
  exact he.self_of_nhds k

def compactScalarParameterCLM : E × C(K, ℂ) →L[ℂ] C(K, E × ℂ) :=
  (show E × C(K, ℂ) →ₗ[ℂ] C(K, E × ℂ) from
    { toFun := fun u => ⟨fun k => (u.1, u.2 k), continuous_const.prodMk u.2.continuous⟩
      map_add' := by intro u v; apply ContinuousMap.ext; intro k; rfl
      map_smul' := by intro c u; apply ContinuousMap.ext; intro k; rfl }).mkContinuous 1 (by
    intro u
    rw [one_mul]
    apply (ContinuousMap.norm_le _ (norm_nonneg u)).mpr
    intro k
    change ‖(u.1, u.2 k)‖ ≤ ‖u‖
    rw [Prod.norm_def, Prod.norm_def]
    exact max_le_max le_rfl (u.2.norm_coe_le_norm k))

/-- Compact spatial arguments may be nonconstant, while arbitrary Banach
parameters stay common. This is an actual lift of every local analytic germ. -/
theorem exists_analytic_parametric_compact_germ_lift {f : E × ℂ → ℂ} {p₀ : E}
    (hf : AnalyticAt ℂ f (p₀, 0)) :
    ∃ H : E × C(K, ℂ) → C(K, ℂ), AnalyticAt ℂ H (p₀, 0) ∧
      H (p₀, 0) = ContinuousMap.const K (f (p₀, 0)) ∧
      (∀ᶠ u in 𝓝 (p₀, (0 : C(K, ℂ))), ∀ k, H u k = f (u.1, u.2 k)) := by
  obtain ⟨G, hG, hG₀, he⟩ := exists_analytic_compact_germ_lift (K := K) hf
  let M := compactScalarParameterCLM (E := E) (K := K)
  have hM₀ : M (p₀, 0) = ContinuousMap.const K (p₀, (0 : ℂ)) := rfl
  have hG' : AnalyticAt ℂ G (M (p₀, 0)) := by simpa only [hM₀] using hG
  have ht : Tendsto M (𝓝 (p₀, (0 : C(K, ℂ))))
      (𝓝 (ContinuousMap.const K (p₀, (0 : ℂ)))) := by
    simpa only [hM₀] using M.continuous.continuousAt.tendsto (x := (p₀, 0))
  refine ⟨G ∘ M, hG'.comp (M.analyticAt _), by simpa [hM₀] using hG₀, ?_⟩
  filter_upwards [ht.eventually he] with u hu
  intro k
  exact hu k

end PGM
