import PLAStochastic.Index.CEPS.Normal.ActualMorseData
import PLAStochastic.Index.CEPS.Normal.DividedDifference

/-! # Equality of the global and root-zone regular normal forms -/

noncomputable section
open Complex Set Metric Filter Topology MeasureTheory
open PGM.WienerHopf
namespace PGM

theorem cepsNormal_dslope_eqOn_of_eqOn {f g : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hfg : EqOn f g U) {a : ℂ} (ha : a ∈ U) :
    EqOn (dslope f a) (dslope g a) U := by
  intro z hz
  by_cases hza : z = a
  · rw [hza, dslope_same, dslope_same]
    have heq : f =ᶠ[𝓝 a] g := Filter.eventually_of_mem (hU.mem_nhds ha) (fun _ hx => hfg hx)
    exact heq.deriv_eq
  · rw [dslope_of_ne _ hza, dslope_of_ne _ hza, slope_def_field, slope_def_field,
      hfg hz, hfg ha]

theorem cepsNormal_actual_regular_forms_eq
    {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
    (hθ : 0 < θ) (hD : 0 < D) {μ q : ℂ} (hμ : ‖μ‖ ≤ dom.μ₀)
    (hq : ‖q‖ ≤ dom.q₀) (L : ℂ → ℂ → ℂ → ℂ) (l : ℂ) {t : ℂ}
    (ht : t ∈ ball (0 : ℂ) dom.ρA) :
    (cepsWHNormalData D θ ρW μ q).regularEntrance L μ q l t =
        (cepsNormalData D θ ρW μ q).regularEntrance L μ q l t ∧
      (cepsWHNormalData D θ ρW μ q).regularBridge L μ q l =
        (cepsNormalData D θ ρW μ q).regularBridge L μ q l := by
  let bp := cepsRootPlus D θ ρW μ q
  let bm := cepsRootMinus D θ ρW μ q
  let G := (cepsWHNormalData D θ ρW μ q).normalG L μ q l
  let H := (cepsNormalData D θ ρW μ q).normalG L μ q l
  have hp : bp ∈ ball (0 : ℂ) dom.ρA := CepsC6.ball_c₀_subset dom
    (CepsC6.rootPlus_mem_ball dom hW hθ hD hμ hq)
  have hm : bm ∈ ball (0 : ℂ) dom.ρA := CepsC6.ball_c₀_subset dom
    (CepsC6.rootMinus_mem_ball dom hW hθ hD hμ hq)
  have hGH : EqOn G H (ball 0 dom.ρA) := by
    intro z hz
    change cexp (-z * l) * cepsQ D θ ρW μ q z * cexp (-2 * L μ q z) =
      cexp (-z * l) * cepsQuotA D θ ρW μ q z * cexp (-2 * L μ q z)
    rw [CepsC6.cepsQ_eq_cepsQuotA dom hW hθ hD hμ hq hz]
  have hS := cepsNormal_dslope_eqOn_of_eqOn isOpen_ball hGH hm
  have hN := cepsNormal_dslope_eqOn_of_eqOn isOpen_ball hS hp
  constructor
  · change -cexp (L μ q t) * dslope (dslope G bm) bp t /
      (cepsQ D θ ρW μ q t * dslope G bm bp) =
      -cexp (L μ q t) * dslope (dslope H bm) bp t /
      (cepsQuotA D θ ρW μ q t * dslope H bm bp)
    rw [hN ht, hS hp, CepsC6.cepsQ_eq_cepsQuotA dom hW hθ hD hμ hq ht]
  · change -G bp * G bm / dslope G bm bp = -H bp * H bm / dslope H bm bp
    rw [hGH hp, hGH hm, hS hp]

end PGM
