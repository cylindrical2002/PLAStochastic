import PLAStochastic.Index.GEP.Kernel.Row.Long.MeasurableChoice
import Mathlib.Topology.Order.ProjIcc

/-!
# Jointly measurable BV parts on a fixed band

Continuous candidates on the band are extended by zero, so both boundary
jumps stay in the variation budget. The measurable selection preserves this
budget and the band Lipschitz constant, with at most four times the uniform
remainder. The input is a proved pointwise decomposition, not a measurability
assumption on the decompositions chosen by that theorem.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

def krRegularExtend {w : ℝ} (hw : 0 ≤ w) (F : C(Icc (0 : ℝ) w, ℂ)) : ℝ → ℂ :=
  (Icc (0 : ℝ) w).indicator (fun x => F (projIcc 0 w hw x))

theorem krRegularExtend_of_mem {w : ℝ} (hw : 0 ≤ w) (F : C(Icc (0 : ℝ) w, ℂ))
    {x : ℝ} (hx : x ∈ Icc 0 w) : krRegularExtend hw F x = F ⟨x, hx⟩ := by
  rw [krRegularExtend, indicator_of_mem hx, projIcc_of_mem hw hx]

theorem krRegularExtend_of_notMem {w : ℝ} (hw : 0 ≤ w) (F : C(Icc (0 : ℝ) w, ℂ))
    {x : ℝ} (hx : x ∉ Icc 0 w) : krRegularExtend hw F x = 0 := indicator_of_notMem hx _

theorem kr_measurable_bv_decomposition {X : Type*} [MeasurableSpace X] [Nonempty X]
    {w V L δ : ℝ} (hw : 0 ≤ w) (hL : 0 ≤ L) (hδ : 0 ≤ δ)
    {q : X → ℝ → ℂ} (hq : Measurable fun p : X × ℝ => q p.1 p.2)
    (hqs : ∀ a x, x ∉ Icc 0 w → q a x = 0)
    (hex : ∀ a, ∃ g : ℝ → ℂ,
      (∀ x, x ∉ Icc 0 w → g x = 0) ∧
      eVariationOn g univ ≤ ENNReal.ofReal V ∧
      (∀ x ∈ Icc 0 w, ∀ y ∈ Icc 0 w, ‖g x - g y‖ ≤ L * |x-y|) ∧
      (∀ x, ‖q a x - g x‖ ≤ δ)) :
    ∃ G R : X → ℝ → ℂ,
      Measurable (fun p : X × ℝ => G p.1 p.2) ∧
      Measurable (fun p : X × ℝ => R p.1 p.2) ∧
      (∀ a x, x ∉ Icc 0 w → G a x = 0 ∧ R a x = 0) ∧
      (∀ a x, q a x = G a x + R a x) ∧
      (∀ a, eVariationOn (G a) univ ≤ ENNReal.ofReal V) ∧
      (∀ a, ∀ x ∈ Icc 0 w, ∀ y ∈ Icc 0 w, ‖G a x - G a y‖ ≤ L * |x-y|) ∧
      (∀ a x, ‖R a x‖ ≤ 4 * δ) := by
  classical
  let I := Icc (0 : ℝ) w
  let B : C(I, ℂ) → Prop := fun F =>
    eVariationOn (krRegularExtend hw F) univ ≤ ENNReal.ofReal V ∧
      ∀ x y : I, ‖F x - F y‖ ≤ L * |(x : ℝ) - y|
  have hqI : Measurable (fun p : X × I => q p.1 p.2) :=
    hq.comp (measurable_fst.prodMk (measurable_subtype_coe.comp measurable_snd))
  have hcont : ∀ a, ∃ F : C(I, ℂ), B F ∧ ∀ x : I, ‖q a x - F x‖ ≤ δ := by
    intro a
    obtain ⟨g, hgs, hgv, hgl, hgr⟩ := hex a
    have hgc : Continuous (fun x : I => g x) := by
      have hLip : LipschitzWith ⟨L, hL⟩ (fun x : I => g x) :=
        (lipschitzWith_iff_dist_le_mul).2 fun x y => by
          rw [Subtype.dist_eq, Real.dist_eq, dist_eq_norm]
          exact hgl x x.property y y.property
      exact hLip.continuous
    let F : C(I, ℂ) := ⟨fun x => g x, hgc⟩
    have hext : krRegularExtend hw F = g := by
      funext x
      by_cases hx : x ∈ Icc 0 w
      · exact krRegularExtend_of_mem hw F hx
      · rw [krRegularExtend_of_notMem hw F hx, hgs x hx]
    refine ⟨F, ⟨?_, ?_⟩, fun x => hgr x⟩
    · rw [hext]
      exact hgv
    · intro x y
      exact hgl x x.property y y.property
  obtain ⟨F, hFM, hFB, hFR⟩ := kr_measurable_continuous_approx hw hδ hqI hcont
  let G : X → ℝ → ℂ := fun a => krRegularExtend hw (F a)
  let R : X → ℝ → ℂ := fun a x => q a x - G a x
  have hGM : Measurable (fun p : X × ℝ => G p.1 p.2) := by
    have hproj : Measurable (fun p : X × ℝ => (p.1, projIcc 0 w hw p.2)) :=
      measurable_fst.prodMk (continuous_projIcc.measurable.comp measurable_snd)
    exact (hFM.comp hproj).indicator (measurableSet_Icc.preimage measurable_snd)
  refine ⟨G, R, hGM, hq.sub hGM, ?_, ?_, fun a => (hFB a).1, ?_, ?_⟩
  · intro a x hx
    have hg0 : G a x = 0 := krRegularExtend_of_notMem hw (F a) hx
    exact ⟨hg0, by dsimp only [R]; rw [hqs a x hx, hg0, sub_self]⟩
  · intro a x
    dsimp only [R]
    ring
  · intro a x hx y hy
    dsimp only [G]
    rw [krRegularExtend_of_mem hw (F a) hx, krRegularExtend_of_mem hw (F a) hy]
    exact (hFB a).2 ⟨x, hx⟩ ⟨y, hy⟩
  · intro a x
    by_cases hx : x ∈ Icc 0 w
    · dsimp only [R, G]
      rw [krRegularExtend_of_mem hw (F a) hx]
      exact hFR a ⟨x, hx⟩
    · dsimp only [R, G]
      rw [hqs a x hx, krRegularExtend_of_notMem hw (F a) hx, sub_self, norm_zero]
      positivity

end
end PGM
