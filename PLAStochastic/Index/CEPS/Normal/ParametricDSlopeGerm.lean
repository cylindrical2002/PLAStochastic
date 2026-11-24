import PLAStochastic.Index.CEPS.Normal.FunctionalFirstSlopeLiftLocal
import PLAStochastic.ForMathlib.Analysis.Complex.CompactAnalyticGermLift

/-! # Actual scalar divided differences in arbitrary Banach parameter germs -/

noncomputable section
open Complex Filter Topology
namespace PGM

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The true removable scalar slope is jointly analytic in arbitrary Banach
parameters at its collision, using an actual local compact-function lift. -/
theorem analyticAt_parametric_dslope_zero {f : E × ℂ → ℂ} {p₀ : E}
    (hf : AnalyticAt ℂ f (p₀, 0)) :
    AnalyticAt ℂ (fun u : E × ℂ => dslope (fun z => f (u.1, z)) 0 u.2) (p₀, 0) := by
  let A := E × ℂ
  let K := PUnit.{1}
  obtain ⟨H, hH, _, he⟩ :=
    exists_analytic_parametric_compact_germ_lift (K := CompactSlopeLine K) hf
  let M : A × C(CompactSlopeLine K, ℂ) → E × C(CompactSlopeLine K, ℂ) :=
    fun u => (u.1.1, u.2)
  have hM : AnalyticAt ℂ M ((p₀, 0), 0) :=
    (analyticAt_fst.comp analyticAt_fst).prod analyticAt_snd
  let H' := H ∘ M
  have hH' : AnalyticAt ℂ H' ((p₀, 0), 0) := hH.comp (x := ((p₀, 0), 0)) (f := M) hM
  have ht : Tendsto M (𝓝 ((p₀, (0 : ℂ)), (0 : C(CompactSlopeLine K, ℂ))))
      (𝓝 (p₀, (0 : C(CompactSlopeLine K, ℂ)))) := hM.continuousAt.tendsto
  have he' : ∀ᶠ u in 𝓝 ((p₀, (0 : ℂ)), (0 : C(CompactSlopeLine K, ℂ))), ∀ q,
      H' u q = f (u.1.1, u.2 q) := by
    filter_upwards [ht.eventually he] with u hu
    exact hu
  let f' : A × ℂ → ℂ := fun u => f (u.1.1, u.2)
  have hf' : AnalyticAt ℂ f' ((p₀, 0), 0) := by
    simpa only [Function.comp_apply] using!
      hf.comp (x := ((p₀, 0), 0)) (f := fun u : A × ℂ => (u.1.1, u.2))
        ((analyticAt_fst.comp analyticAt_fst).prod analyticAt_snd)
  let a : A → C(K, ℂ) := fun _ => 0
  let X : A → C(K, ℂ) := fun u => ContinuousMap.const K u.2
  have ha : AnalyticAt ℂ a (p₀, 0) := analyticAt_const
  have hX : AnalyticAt ℂ X (p₀, 0) := analyticAt_snd.continuousMap_const
  have ha₀ : a (p₀, 0) = 0 := rfl
  have hX₀ : X (p₀, 0) = 0 := rfl
  have hs₀ : functionalFirstSlopeSegment a X (p₀, 0) = 0 := by
    simp [functionalFirstSlopeSegment, ha₀, hX₀]
  have hHs : AnalyticAt ℂ H' ((p₀, 0), functionalFirstSlopeSegment a X (p₀, 0)) := by
    simpa only [hs₀] using hH'
  have hG := ((ContinuousMap.evalCLM ℂ PUnit.unit.{1}).analyticAt _).comp
    (functionalFirstSlopeLift_analyticAt hHs ha hX)
  apply hG.congr
  filter_upwards [functionalFirstSlopeLift_eventually_apply_local
    (f := fun u : A => fun z => f (u.1, z)) hf' hH' he' ha hX ha₀ hX₀]
    with u hu
  exact hu PUnit.unit.{1}

theorem analyticAt_parametric_second_dslope_zero {f : E × ℂ → ℂ} {p₀ : E}
    (hf : AnalyticAt ℂ f (p₀, 0)) :
    AnalyticAt ℂ (fun u : E × ℂ =>
      dslope (dslope (fun z => f (u.1, z)) 0) 0 u.2) (p₀, 0) :=
  analyticAt_parametric_dslope_zero (analyticAt_parametric_dslope_zero hf)

end PGM
