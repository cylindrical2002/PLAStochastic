import PLAStochastic.Index.GEP.Kernel.Row.Measurable
import PLAStochastic.Index.GEP.Kernel.Row.Long.InfiniteGreen
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.ContinuousMap.Compact

/-!
# Jointly measurable regular representatives from uniform approximations

A countable dense family of continuous regular candidates suffices to make
the choice measurable. Candidate membership may include an exact variation
and Lipschitz budget; those budgets are unchanged. The uniform error increases
by at most a factor four. The countable tests use the actual kernel values,
so no measurability of an arbitrary pointwise choice is assumed.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set TopologicalSpace
open scoped ENNReal Topology

/-- On a fixed compact interval, an approximate continuous representative can
be selected jointly measurably while preserving any candidate-class property. -/
theorem kr_measurable_continuous_approx {X : Type*} [MeasurableSpace X] [Nonempty X]
    {w δ : ℝ} (hw : 0 ≤ w) (hδ : 0 ≤ δ)
    {q : X → Icc (0 : ℝ) w → ℂ}
    (hq : Measurable fun p : X × Icc (0 : ℝ) w => q p.1 p.2)
    {B : C(Icc (0 : ℝ) w, ℂ) → Prop}
    (hex : ∀ a, ∃ F : C(Icc (0 : ℝ) w, ℂ), B F ∧ ∀ x, ‖q a x - F x‖ ≤ δ) :
    ∃ F : X → C(Icc (0 : ℝ) w, ℂ),
      Measurable (fun p : X × Icc (0 : ℝ) w => F p.1 p.2) ∧
      (∀ a, B (F a)) ∧ (∀ a x, ‖q a x - F a x‖ ≤ 4 * δ) := by
  classical
  by_cases hδp : 0 < δ
  · let I := Icc (0 : ℝ) w
    have : Nonempty I := ⟨⟨0, by exact ⟨le_rfl, hw⟩⟩⟩
    let Family := {F : C(I, ℂ) // B F}
    obtain ⟨F₀, hF₀, -⟩ := hex (Classical.choice ‹Nonempty X›)
    have : Nonempty Family := ⟨⟨F₀, hF₀⟩⟩
    let candidates : ℕ → Family := denseSeq Family
    let points : ℕ → I := denseSeq I
    have hc : DenseRange candidates := denseRange_denseSeq Family
    have hp : DenseRange points := denseRange_denseSeq I
    let good : X → ℕ → Prop := fun a n =>
      ∀ m : ℕ, ‖q a (points m) - (candidates n).val (points m)‖ ≤ 2 * δ
    have hgoodM : ∀ n, MeasurableSet {a | good a n} := by
      intro n
      change MeasurableSet {a | ∀ m : ℕ,
        ‖q a (points m) - (candidates n).val (points m)‖ ≤ 2 * δ}
      simp only [ofPred_forall]
      apply MeasurableSet.iInter
      intro m
      exact measurableSet_le ((hq.comp (measurable_id.prodMk measurable_const)).sub_const _).norm
        measurable_const
    have hgood : ∀ a, ∃ n, good a n := by
      intro a
      obtain ⟨F, hF, hqF⟩ := hex a
      obtain ⟨n, hn⟩ := hc.exists_dist_lt (⟨F, hF⟩ : Family) hδp
      refine ⟨n, fun m => ?_⟩
      have hd : ‖F (points m) - (candidates n).val (points m)‖ ≤ δ := by
        have he := ContinuousMap.dist_apply_le_dist (f := F) (g := (candidates n).val) (points m)
        have he' : ‖F (points m) - (candidates n).val (points m)‖ ≤ dist F (candidates n).val := by
          simpa only [dist_eq_norm] using he
        exact he'.trans (le_of_lt hn)
      calc
        _ ≤ ‖q a (points m) - F (points m)‖ + ‖F (points m) - (candidates n).val (points m)‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ δ + δ := add_le_add (hqF _) hd
        _ = 2 * δ := by ring
    let F : X → C(I, ℂ) := fun a => (candidates (Nat.find (hgood a))).val
    have hFM : Measurable (fun p : X × I => F p.1 p.2) := by
      apply Measurable.find
        (fun n => (candidates n).val.continuous.measurable.comp measurable_snd)
        (fun n => (hgoodM n).preimage measurable_fst)
        (fun p : X × I => hgood p.1)
    refine ⟨F, hFM, fun a => (candidates (Nat.find (hgood a))).property, ?_⟩
    intro a x
    obtain ⟨F₁, hF₁, hqF₁⟩ := hex a
    have hnear : ∀ y : I, ‖F a y - F₁ y‖ ≤ 3 * δ := by
      intro y
      apply hp.induction_on (p := fun y => ‖F a y - F₁ y‖ ≤ 3 * δ) y
      · exact isClosed_le (((F a).continuous.sub F₁.continuous).norm) continuous_const
      · intro m
        have hh := Nat.find_spec (hgood a) m
        have hh' : ‖F a (points m) - q a (points m)‖ ≤ 2 * δ := by
          simpa only [F, norm_sub_rev] using hh
        calc
          _ ≤ ‖F a (points m) - q a (points m)‖ + ‖q a (points m) - F₁ (points m)‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
          _ ≤ 2 * δ + δ := add_le_add hh' (hqF₁ _)
          _ = 3 * δ := by ring
    calc
      _ ≤ ‖q a x - F₁ x‖ + ‖F₁ x - F a x‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ δ + 3 * δ := add_le_add (hqF₁ x) (by simpa only [norm_sub_rev] using hnear x)
      _ = 4 * δ := by ring
  · have hδ0 : δ = 0 := by linarith
    choose F hF hqF using hex
    have heq : ∀ a x, q a x = F a x := by
      intro a x
      have h := hqF a x
      rw [hδ0] at h
      exact sub_eq_zero.mp (norm_le_zero_iff.mp h)
    refine ⟨F, ?_, hF, ?_⟩
    · convert hq using 1
      funext p
      exact (heq p.1 p.2).symm
    · intro a x
      rw [heq a x, sub_self, norm_zero, hδ0]
      norm_num

end
end PGM
