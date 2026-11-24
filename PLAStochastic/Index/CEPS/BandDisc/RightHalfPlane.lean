import PLAStochastic.Index.CEPS.BandDisc.Entrance
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# The actual entrance lower bound on the entire right discount half-plane

A logarithmic representative near `z=1` handles every discrete discount period.
Away from `z=1`, the global exit-atom bound in `|1-z|` pays the lower bound.
This strengthens the source's fixed-disc conclusion, without claiming a global
linear bound in `|q|` or an extension to negative real parts.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set

/-- A diffusive block and one positive exit atom give nonvanishing at every discount period. -/
theorem cepsBandDisc_entrance_right_lower {s : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n)
    (hs : Summable s) (hs1 : Summable (fun n : ℕ => (n + 1 : ℝ) * s n))
    (hmono : ∀ n, s (n + 1) ≤ s n) (hzero : s 0 = 1)
    {N : ℕ} (hN : 0 < N) (hblock : ∀ n, s (n + N) ≤ (1 / 2) * s n)
    {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1 - s 1) {q : ℂ} (hq : 0 ≤ q.re) :
    p / (16 * (N : ℝ)) ≤ ‖∑' n : ℕ, Complex.exp (-q * n) * (s n : ℂ)‖ := by
  let z := Complex.exp (-q)
  have hz0 : z ≠ 0 := Complex.exp_ne_zero _
  have hz : ‖z‖ ≤ 1 := by
    dsimp [z]
    rw [Complex.norm_exp, Complex.neg_re]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr hq)
  have hpmax : p ≤ 1 := by linarith [hs0 1]
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hNr1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have he : ∀ n : ℕ, z ^ n = Complex.exp (-q * n) := by
    intro n
    dsimp [z]
    rw [← Complex.exp_nat_mul]
    congr 1
    ring
  by_cases hzsmall : ‖1 - z‖ ≤ 1 / (8 * (N : ℝ))
  · let r := -Complex.log z
    have hzr : ‖z - 1‖ ≤ 1 / 2 := by
      rw [norm_sub_rev]
      refine hzsmall.trans ?_
      apply (div_le_iff₀ (by positivity : 0 < 8 * (N : ℝ))).mpr
      nlinarith
    have hrnorm : ‖r‖ ≤ (3 / 2) * ‖1 - z‖ := by
      have h := Complex.norm_log_one_add_half_le_self hzr
      rw [show (1 : ℂ) + (z - 1) = z by ring, norm_sub_rev] at h
      simpa only [r, norm_neg] using h
    have hrre : 0 ≤ r.re := by
      dsimp [r]
      rw [Complex.log_re]
      exact neg_nonneg.mpr (Real.log_nonpos (norm_nonneg z) hz)
    have hrN : 4 * (N : ℝ) * ‖r‖ ≤ 1 := by
      have hzN := (le_div_iff₀ (by positivity : 0 < 8 * (N : ℝ))).mp hzsmall
      nlinarith [mul_le_mul_of_nonneg_left hrnorm (show 0 ≤ 4 * (N : ℝ) by positivity)]
    have hsmall := cepsBandDisc_entrance_small_lower hs0 hs hs1 hzero hN hblock hrre hrN
    have her : ∀ n : ℕ, Complex.exp (-r * n) = z ^ n := by
      intro n
      dsimp [r]
      rw [neg_neg, mul_comm, Complex.exp_nat_mul, Complex.exp_log hz0]
    simp_rw [her, he] at hsmall
    refine (show p / (16 * (N : ℝ)) ≤ 1 / 2 from ?_).trans hsmall
    apply (div_le_iff₀ (by positivity : 0 < 16 * (N : ℝ))).mpr
    nlinarith
  · have hbig : 1 / (8 * (N : ℝ)) ≤ ‖1 - z‖ := (lt_of_not_ge hzsmall).le
    have h := cepsBandDisc_generating_atom_lower hs0 hs hmono hzero hp hp1 hz
    simp_rw [he] at h
    refine (show p / (16 * (N : ℝ)) ≤ (p / 2) * ‖1 - z‖ from ?_).trans h
    calc _ = (p / 2) * (1 / (8 * (N : ℝ))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hbig (by positivity)

/-- The class-uniform `w⁻²` bound is valid on the full right half-plane.
Negative real parts remain outside this theorem. -/
theorem cepsBandDisc_topSurv_right_lower {D θ vlo vhi : ℝ}
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hvhi : vlo ≤ vhi) :
    ∃ c : ℝ, 0 < c ∧ ∀ ν : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
      ∀ w : ℝ, 2 ≤ w → ∀ l : ℝ, w / 2 ≤ l → l ≤ 2 * w →
        ∀ μ : ℝ, |μ| ≤ 1 / (64 * D) → ∀ q : ℂ, 0 ≤ q.re →
          c / w ^ 2 ≤ ‖cepsTopSurv ν (1 + μ) 1 q l‖ := by
  obtain ⟨C, hC, hb⟩ := cepsBandDisc_uniform_block hD hθ hvlo hvhi
  let p : ℝ := 1 / (32 * D)
  have hp : 0 < p := by dsimp [p]; positivity
  refine ⟨p / (16 * C), by positivity, ?_⟩
  intro ν hν w hw l hl hlw μ hμ q hq
  obtain ⟨N, hN, hNC, hblock⟩ := hb ν hν w hw
  let s : ℕ → ℝ := fun n => krSurv (Icc 0 l) (ν : Measure ℝ) (1 + μ) 1 n l
  have hs0 : ∀ n, 0 ≤ s n := fun n => krSurv_nonneg measurableSet_Icc ν (1 + μ) 1 n l
  have hq0 : -(krKappa D vlo vhi / (16 * w ^ 2)) ≤ (0 : ℂ).re := by
    simp only [Complex.zero_re]
    exact neg_nonpos.mpr (div_nonneg (krKappa_pos hD hvlo hvhi).le (by positivity))
  have hs : Summable s := by
    simpa [s] using (cepsBand_survival_moments hD hθ hvlo hvhi hν hw hl hlw
      (1 + μ) (a := 1) (by norm_num) hq0 0 l).1
  have hs1 : Summable (fun n : ℕ => (n + 1 : ℝ) * s n) := by
    simpa [s] using (cepsBand_survival_moments hD hθ hvlo hvhi hν hw hl hlw
      (1 + μ) (a := 1) (by norm_num) hq0 1 l).1
  have hmono : ∀ n, s (n + 1) ≤ s n := fun n =>
    krSurv_le_of_le measurableSet_Icc ν (1 + μ) 1 (Nat.le_succ n) l
  have hsone : s 0 = 1 := by
    have hl0 : 0 ≤ l := by linarith
    simp [s, krSurv, krRow_zero, hl0]
  have hatom : p ≤ 1 - s 1 := cepsBandDisc_top_first_exit_mass hD hθ hν l hμ
  have hstep : ∀ n, s (n + N) ≤ (1 / 2) * s n := fun n =>
    krSurv_add_le ν (hblock l hl hlw (1 + μ) 1 (by norm_num)) n l
  have h := cepsBandDisc_entrance_right_lower hs0 hs hs1 hmono hsone hN hstep hp.le hatom hq
  change p / (16 * (N : ℝ)) ≤ ‖cepsTopSurv ν (1 + μ) 1 q l‖ at h
  refine (show p / (16 * C) / w ^ 2 ≤ p / (16 * (N : ℝ)) from ?_).trans h
  rw [div_div]
  apply div_le_div_of_nonneg_left hp.le (by positivity)
  nlinarith

/-- The WP8 strip entrance at zero mark is the same top-started entrance. -/
theorem cepsBandDisc_stripEntrance_right_lower {D θ vlo vhi : ℝ}
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hvhi : vlo ≤ vhi) :
    ∃ c : ℝ, 0 < c ∧ ∀ ν : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
      ∀ w : ℝ, 2 ≤ w → ∀ l : ℝ, w / 2 ≤ l → l ≤ 2 * w →
        ∀ μ : ℝ, |μ| ≤ 1 / (64 * D) → ∀ q : ℂ, 0 ≤ q.re →
          c / w ^ 2 ≤ ‖cepsStripEntrance ν 0 μ q l‖ := by
  simpa only [cepsTopSurv_eq_stripEntrance] using
    cepsBandDisc_topSurv_right_lower hD hθ hvlo hvhi

end
end PGM
