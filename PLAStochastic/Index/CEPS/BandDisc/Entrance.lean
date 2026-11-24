import PLAStochastic.Index.CEPS.BandDisc.Generating
import PLAStochastic.ForMathlib.Probability.RandomWalk.WienerHopf.Uniform

/-! # The actual entrance lower bound on the source's fixed right-half-plane disc -/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set

/-- The first-step top exit has a class-uniform positive mass on an explicit drift window.
A strict gap between `1-2δ` and `1+μ` avoids any endpoint convention. -/
theorem cepsBandDisc_top_first_exit_mass {D θ vlo vhi : ℝ}
    (hD : 0 < D) (hθ : 0 < θ) {ν : ProbabilityMeasure ℝ}
    (hν : RegLaw D θ vlo vhi ν) (l : ℝ) {μ : ℝ} (hμ : |μ| ≤ 1 / (64 * D)) :
    1 / (32 * D) ≤ 1 - krSurv (Icc 0 l) (ν : Measure ℝ) (1 + μ) 1 1 l := by
  obtain ⟨f, hfm, hf0, hfz, hfle, hfeq⟩ := hν.density
  have hX : WienerHopf.IsGapLaw (ν : Measure ℝ) f D θ vhi := by
    refine ⟨inferInstance, hfeq, hfm, hf0, hfz, fun x _ => hfle x, ?_, hν.mean, ?_⟩
    · have hm := (hν.tail_mean hθ).1
      have hs := (hν.tail_sq hθ).1
      have he : (fun x : ℝ => (x - 1) ^ 2) = fun x => x ^ 2 - 2 * x + 1 := by
        funext x; ring
      rw [he]
      exact (hs.sub (hm.const_mul 2)).add (integrable_const _)
    · simpa only [lawVar, hν.mean] using hν.var_le
  let δ : ℝ := 1 / (64 * D)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hmass := hX.measureReal_Iic_ge hθ.le hD (t := 2 * δ) (by positivity)
  have heq : 1 / (16 * D) - 2 * δ = 1 / (32 * D) := by dsimp [δ]; field_simp; ring
  rw [heq] at hmass
  let E : Set (ℕ → ℝ) := {g | g 0 ∈ Iic (1 - 2 * δ)}
  have hE : MeasurableSet E := (measurable_pi_apply 0) measurableSet_Iic
  have hsurv : krSurv (Icc 0 l) (ν : Measure ℝ) (1 + μ) 1 1 l ≤
      (iidLaw ν).real Eᶜ := by
    apply krSurv_le_measureReal ν measurableSet_Icc hE.compl 1 l
    intro g hg
    have h := (hg 1 (by norm_num)).2
    simp only [kWalk, gapKeys, Finset.sum_range_one, Nat.cast_one, one_mul] at h
    have hμlo : -δ ≤ μ := (abs_le.mp hμ).1
    show g ∉ E
    intro he
    change g 0 ≤ 1 - 2 * δ at he
    linarith
  have hev := (measurePreserving_eval_infinitePi (fun _ : ℕ => (ν : Measure ℝ)) 0).measure_preimage
    (s := Iic (1 - 2 * δ)) measurableSet_Iic.nullMeasurableSet
  have hreal : (iidLaw ν).real E = (ν : Measure ℝ).real (Iic (1 - 2 * δ)) := by
    exact congrArg ENNReal.toReal hev
  rw [measureReal_compl hE, probReal_univ, hreal] at hsurv
  linarith

/-- The local target from `(C10)`--`(C13)`, with the explicit harmless choice `q₀=1/2`.
The constant is fixed before the law, width, drift and discount. -/
theorem cepsBandDisc_topSurv_local_lower {D θ vlo vhi : ℝ}
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hvhi : vlo ≤ vhi) :
    ∃ c : ℝ, 0 < c ∧ ∀ ν : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
      ∀ w : ℝ, 2 ≤ w → ∀ l : ℝ, w / 2 ≤ l → l ≤ 2 * w →
        ∀ μ : ℝ, |μ| ≤ 1 / (64 * D) → ∀ q : ℂ, 0 ≤ q.re → ‖q‖ ≤ 1 / 2 →
          c / w ^ 2 ≤ ‖cepsTopSurv ν (1 + μ) 1 q l‖ := by
  obtain ⟨a₀, ha₀, hsmall⟩ := cepsBandDisc_survival_small_lower hD hθ hvlo hvhi
  let p : ℝ := 1 / (32 * D)
  have hp : 0 < p := by dsimp [p]; positivity
  let c : ℝ := min (1 / 2) ((p / 4) * a₀)
  refine ⟨c, lt_min (by norm_num) (by positivity), ?_⟩
  intro ν hν w hw l hl hlw μ hμ q hqr hqnorm
  have hw2 : 0 < w ^ 2 := sq_pos_of_pos (by linarith)
  have hl0 : 0 ≤ l := by linarith
  by_cases hqsmall : ‖q‖ ≤ a₀ / w ^ 2
  · have h := hsmall ν hν w hw l hl hlw (1 + μ) 1 (by norm_num) l
      (by simp [hl0]) q hqr hqsmall
    refine (show c / w ^ 2 ≤ 1 / 2 from ?_).trans h
    rw [div_le_iff₀ hw2]
    have hc : c ≤ 1 / 2 := min_le_left _ _
    nlinarith
  · have hqbig : a₀ / w ^ 2 ≤ ‖q‖ := (lt_of_not_ge hqsmall).le
    let s : ℕ → ℝ := fun n => krSurv (Icc 0 l) (ν : Measure ℝ) (1 + μ) 1 n l
    have hs0 : ∀ n, 0 ≤ s n := fun n => krSurv_nonneg measurableSet_Icc ν (1 + μ) 1 n l
    have hs : Summable s := by
      have hq0 : -(krKappa D vlo vhi / (16 * w ^ 2)) ≤ (0 : ℂ).re := by
        simp only [Complex.zero_re]
        exact neg_nonpos.mpr (div_nonneg (krKappa_pos hD hvlo hvhi).le (by positivity))
      simpa [s] using (cepsBand_survival_moments hD hθ hvlo hvhi hν hw hl hlw
        (1 + μ) (a := 1) (by norm_num) hq0 0 l).1
    have hmono : ∀ n, s (n + 1) ≤ s n := fun n =>
      krSurv_le_of_le measurableSet_Icc ν (1 + μ) 1 (Nat.le_succ n) l
    have hsone : s 0 = 1 := by simp [s, krSurv, krRow_zero, hl0]
    have hatom : p ≤ 1 - s 1 := cepsBandDisc_top_first_exit_mass hD hθ hν l hμ
    have h := cepsBandDisc_discount_atom_lower hs0 hs hmono hsone hp.le hatom hqr hqnorm
    change (p / 4) * ‖q‖ ≤ ‖cepsTopSurv ν (1 + μ) 1 q l‖ at h
    refine (show c / w ^ 2 ≤ (p / 4) * ‖q‖ from ?_).trans h
    calc _ ≤ ((p / 4) * a₀) / w ^ 2 :=
        div_le_div_of_nonneg_right (min_le_right _ _) hw2.le
      _ = (p / 4) * (a₀ / w ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hqbig (by positivity)

end
end PGM
