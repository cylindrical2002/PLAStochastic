import PLAStochastic.Index.GEP.Kernel.Output.Finite.StopPieceBounds
import PLAStochastic.Index.GEP.Kernel.Flux.Sections.PrimitiveSeries

/-!
# Summability on the actual marked stopping-time triangle

Only indices `i < t` occur. The window exponential estimate gives a geometric
majorant after the original finite-dimensional moment and stopping-tail bounds
are combined.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter

def fluxWindowMoment (eps : ℝ) (ν : ProbabilityMeasure ℝ) (κ : ℝ) (a : ℕ × ℕ) : ℝ :=
  if a.2 < a.1 then
    ∫ g in winSet eps a.2 a.1, Real.exp (κ * fluxUnmarkedSum a.1 a.2 g) ∂iidLaw ν
  else 0

theorem fluxWindowMoment_nonneg (eps : ℝ) (ν : ProbabilityMeasure ℝ) (κ : ℝ) (a : ℕ × ℕ) :
    0 ≤ fluxWindowMoment eps ν κ a := by
  unfold fluxWindowMoment
  split
  · exact integral_nonneg fun g => (Real.exp_pos _).le
  · exact le_rfl

theorem flux_triangle_geometric_summable {K ρ : ℝ} (hK : 0 ≤ K) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    Summable (fun a : ℕ × ℕ => if a.2 < a.1 then K * ρ ^ a.1 else 0) := by
  apply (summable_prod_of_nonneg (fun a => by dsimp; split <;> positivity)).mpr
  constructor
  · intro t
    exact (hasSum_sum_of_ne_finset_zero (s := Finset.range t)
      (fun i hi => if_neg (by simpa only [Finset.mem_range] using hi))).summable
  · have he (t : ℕ) : (∑' i : ℕ, if i < t then K * ρ ^ t else 0) = K * ((t : ℝ) * ρ ^ t) := by
      rw [tsum_eq_sum (s := Finset.range t)
        (fun i hi => if_neg (by simpa only [Finset.mem_range] using hi))]
      simp only [Finset.sum_ite_of_true (fun i hi => Finset.mem_range.mp hi), Finset.sum_const,
        Finset.card_range, nsmul_eq_mul]
      ring
    simp_rw [he]
    exact (hasSum_coe_mul_geometric_of_norm_lt_one
      (by simpa only [Real.norm_eq_abs, abs_of_nonneg hρ0] using hρ1)).summable.mul_left K

theorem flux_window_moment_summable {D θ vlo vhi : ℝ} {ν : ProbabilityMeasure ℝ}
    (hν : RegLaw D θ vlo vhi ν) (hθ : 0 < θ) {eps q κ : ℝ}
    (hq0 : 0 < q) (hq1 : q ≤ 1)
    (htail : ∀ m : ℕ, iidLaw ν {g | (m : ℕ∞) < gapSegLen eps g} ≤
      ENNReal.ofReal (72 / 71 * (q ^ 4) ^ m))
    (hκ0 : 0 ≤ κ) (hκ : 2 * κ ≤ θ / 4)
    (hdecay : q * Real.exp (8 * D / θ ^ 2 * κ) < 1) :
    Summable (fluxWindowMoment eps ν κ) := by
  let r := Real.exp (8 * D / θ ^ 2 * κ)
  have hr : 1 ≤ r := Real.one_le_exp (by have := hν.D_nonneg; positivity)
  let ρ := q * r
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ < 1 := hdecay
  have hK : 0 ≤ winConst / q ^ 2 := by have := winConst_pos; positivity
  refine Summable.of_nonneg_of_le (fluxWindowMoment_nonneg eps ν κ) ?_
    (flux_triangle_geometric_summable hK hρ0 hρ1)
  intro a
  unfold fluxWindowMoment
  split_ifs with ha
  · calc
      _ ≤ winConst * q ^ (a.1 - 2) * r ^ (a.1 - 1) :=
        flux_window_exp_le hν hθ hq0 hq1 htail hκ0 hκ ha
      _ ≤ winConst * (ρ ^ a.1 / q ^ 2) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left
          (pow_sub_two_mul_pow_sub_one_le hq0 hq1 hr le_rfl a.1) winConst_pos.le
      _ = _ := by ring
  · exact le_rfl

end
end PGM
