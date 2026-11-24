import PLAStochastic.Index.GEP.Kernel.Flux.Prefix.SurvivingWindow
import PLAStochastic.Index.GEP.Kernel.Flux.Sections.PrimitiveSeries

/-!
# The actual full `lawJC` has an integrable spatial derivative

Finite-prefix interval endpoints give absolutely continuous derivative measures.
A predetermined window avoids the inserted coordinate and supplies an exponential
majorant for their total variation.  Both the derivative series and the constants
are therefore absolutely summable. No three-point flux or regularity estimate is
assumed in the resulting primitive identity.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Finset
open scoped Interval

/-- Indexing exactly the original double influence series. -/
abbrev FluxInfluenceIndex := Σ k : ℕ, Fin k

theorem flux_geometric_index_summable {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    Summable (fun a : FluxInfluenceIndex => (72 / 71 / q ^ 2) * (q ^ 2) ^ a.1) := by
  have hr : ‖q ^ 2‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg q)]
    nlinarith [mul_pos hq0 (sub_pos.mpr hq1)]
  apply (summable_sigma_of_nonneg (fun a => by positivity)).mpr
  constructor
  · intro k
    exact (hasSum_fintype _).summable
  · simp only [tsum_fintype, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    convert! (hasSum_coe_mul_geometric_of_norm_lt_one hr).summable.mul_left (72 / 71 / q ^ 2)
      using 1
    funext k
    ring

theorem flux_geometric_index_eq {q : ℝ} (hq : 0 < q) (a : FluxInfluenceIndex) :
    (72 / 71 / q ^ 2) * (q ^ 2) ^ a.1 = 72 / 71 * q ^ (2 * (a.1 - 1)) := by
  have hk : 0 < a.1 := Nat.zero_lt_of_lt a.2.isLt
  have hp : q ^ (2 * (a.1 - 1)) * q ^ 2 = (q ^ 2) ^ a.1 := by
    rw [← pow_add, ← pow_mul]
    congr 1
    omega
  rw [div_mul_eq_mul_div, ← hp]
  field_simp

/-- The original full influence has an integrable a.e. derivative under the
actual iid assumptions and an exponential stopping tail. -/
theorem flux_lawJC_primitive_of_tail {ν : ProbabilityMeasure ℝ}
    (hac : (ν : Measure ℝ) ≪ volume) (hpos : ∀ᵐ x ∂(ν : Measure ℝ), 0 < x)
    {eps q : ℝ} (heps : 1 ≤ eps) (hq0 : 0 < q) (hq1 : q < 1)
    (htail : ∀ m : ℕ, iidLaw ν {g | (m : ℕ∞) < gapSegLen eps g} ≤
      ENNReal.ofReal (72 / 71 * (q ^ 4) ^ m)) :
    ∃ j : ℝ → ℝ, AEPrimitive (lawJC eps ν) j ∧ Integrable j := by
  classical
  let B : FluxInfluenceIndex → ℝ := fun a => (72 / 71 / q ^ 2) * (q ^ 2) ^ a.1
  have hB : Summable B := flux_geometric_index_summable hq0 hq1
  have hB0 : ∀ a, 0 ≤ B a := fun a => by positivity
  have hQ : ∀ a : FluxInfluenceIndex, ∀ x, |pwQ eps ν a.1 a.2 x| ≤ B a := by
    intro a x
    rw [abs_of_nonneg (pwQ_nonneg eps ν a.1 a.2 x)]
    change pwQ eps ν a.1 a.2 x ≤ (72 / 71 / q ^ 2) * (q ^ 2) ^ a.1
    rw [flux_geometric_index_eq hq0 a]
    exact pwQ_le hq0.le hq1.le htail a.2.isLt x
  have hp : ∀ a : FluxInfluenceIndex, ∃ j : ℝ → ℝ,
      AEPrimitive (pwQ eps ν a.1 a.2) j ∧ Integrable j ∧ (∫ x, ‖j x‖) ≤ 2 * B a := by
    intro a
    obtain ⟨j, hj, hiJ, hb⟩ := flux_pwQ_window_primitive_all hac hpos heps a.2.isLt
    refine ⟨j, hj, hiJ, hb.trans ?_⟩
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
    change (iidLaw ν).real (fluxWindow eps a.1 a.2) ≤ (72 / 71 / q ^ 2) * (q ^ 2) ^ a.1
    rw [flux_geometric_index_eq hq0 a]
    exact fluxWindow_le hq0.le hq1.le htail a.2.isLt
  choose j hj hji hjB using hp
  have hs : Summable (fun a => ∫ x, ‖j a x‖) :=
    Summable.of_nonneg_of_le (fun a => integral_nonneg fun x => norm_nonneg _)
      hjB (hB.mul_left 2)
  have hc : ∀ a : FluxInfluenceIndex, ∃ c : ℝ,
      (∀ᵐ x ∂volume.restrict (Ioi (0 : ℝ)),
        pwQ eps ν a.1 a.2 x = c + ∫ t in (0 : ℝ)..x, j a t) ∧ |c| ≤ 3 * B a := by
    intro a
    obtain ⟨c, hc, hb⟩ := kernel_aePrimitive_constant_bound (hj a) (hji a) (fun x _ => hQ a x)
    refine ⟨c, hc, ?_⟩
    have hh := hjB a
    simp only [Real.norm_eq_abs] at hh
    linarith
  choose c hc hcB using hc
  have hcs : Summable c := Summable.of_norm_bounded (hB.mul_left 3)
    (fun a => by simpa only [Real.norm_eq_abs] using hcB a)
  have hslocal : ∀ R : ℝ, Summable fun a => ∫ t in Ι (0 : ℝ) R, ‖j a t‖ := by
    intro R
    exact Summable.of_nonneg_of_le
      (fun a => integral_nonneg fun t => norm_nonneg _)
      (fun a => setIntegral_le_integral (hji a).norm (Eventually.of_forall fun t => norm_nonneg _)) hs
  have hpseries := kernel_aePrimitive_tsum (fun a R => (hji a).intervalIntegrable) hc hcs hslocal
  have he : (fun x => ∑' a : FluxInfluenceIndex, pwQ eps ν a.1 a.2 x) = lawJC eps ν := by
    funext x
    have hsum : Summable (fun a : FluxInfluenceIndex => pwQ eps ν a.1 a.2 x) :=
      Summable.of_norm_bounded hB (fun a => by simpa only [Real.norm_eq_abs] using hQ a x)
    rw [hsum.tsum_sigma]
    simp only [tsum_fintype, lawJC_eq_pwQ]
    apply tsum_congr
    intro k
    exact Fin.sum_univ_eq_sum_range (fun i => pwQ eps ν k i x) k
  rw [he] at hpseries
  exact ⟨fun x => ∑' a, j a x, hpseries, kernel_integrable_tsum hji hs⟩

/-- On the original regular class, the stopping tail discharges the only
probabilistic hypothesis of the complete `lawJC` primitive construction. -/
theorem flux_lawJC_aePrimitive (D θ vlo vhi : ℝ)
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi) :
    ∃ e0 : ℝ, ∀ eps, e0 ≤ eps → ∀ ν : ProbabilityMeasure ℝ,
      RegLaw D θ vlo vhi ν → ∃ j : ℝ → ℝ, AEPrimitive (lawJC eps ν) j ∧ Integrable j := by
  obtain ⟨e0, he01, hf⟩ := regLaw_facts hD hθ hvlo hv
  refine ⟨e0, fun eps heps ν hν => ?_⟩
  obtain ⟨_, _, htail, _⟩ := hf eps heps ν hν
  have heps1 : 1 ≤ eps := he01.trans heps
  have heps0 : 0 < eps := by linarith
  let c := tailRate * regV vlo
  have hc : 0 < c := mul_pos tailRate_pos (regV_pos hvlo)
  let q := Real.exp (-c / (4 * eps ^ 2))
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := by
    apply Real.exp_lt_one_iff.mpr
    exact div_neg_of_neg_of_pos (neg_neg_of_pos hc) (by positivity)
  have hq4 : q ^ 4 = tailA vlo eps := by
    rw [show q = Real.exp (-c / (4 * eps ^ 2)) from rfl, ← Real.exp_nat_mul, tailA]
    congr 1
    dsimp [c]
    field_simp
  have ht : ∀ m : ℕ, iidLaw ν {g | (m : ℕ∞) < gapSegLen eps g} ≤
      ENNReal.ofReal (72 / 71 * (q ^ 4) ^ m) := by
    rw [hq4]
    exact htail
  have hac : (ν : Measure ℝ) ≪ volume := by
    obtain ⟨f, _, _, _, _, hfν⟩ := hν.density
    rw [hfν]
    exact withDensity_absolutelyContinuous _ _
  exact flux_lawJC_primitive_of_tail hac hν.ae_pos heps1 hq0 hq1 ht

/-- The original normalized influence `lawJC / lawC` has the primitive required
by the first clause of `KernelC`; no flux identity is assumed. -/
theorem flux_normalized_lawJC_aePrimitive (D θ vlo vhi : ℝ)
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi) :
    ∃ e0 : ℝ, ∀ eps, e0 ≤ eps → ∀ ν : ProbabilityMeasure ℝ,
      RegLaw D θ vlo vhi ν → ∃ j : ℝ → ℝ,
        AEPrimitive (fun x => lawJC eps ν x / lawC eps ν) j ∧ Integrable j := by
  obtain ⟨e0, hf⟩ := flux_lawJC_aePrimitive D θ vlo vhi hD hθ hvlo hv
  refine ⟨e0, fun eps heps ν hν => ?_⟩
  obtain ⟨j, ⟨hI, c, hc⟩, hj⟩ := hf eps heps ν hν
  refine ⟨fun x => j x / lawC eps ν, ⟨fun R => (hI R).div_const _, c / lawC eps ν, ?_⟩,
    hj.div_const _⟩
  filter_upwards [hc] with x hx
  rw [hx, intervalIntegral.integral_div, add_div]

end

end PGM
