import PLAStochastic.Index.GEP.Kernel.LinearSurvival.SurvivalMoments
import PLAStochastic.Index.GEP.OrbitClosure.SumDensity
import PLAStochastic.Index.GEP.OrbitClosure.RegularClass
import PLAStochastic.Index.GEP.OrbitClosure.CyclicReduction

/-!
# Uniform concentration of the free increment sums

The density bound is inherited from the original regular gap law. Both signs
and arbitrary translations of the increment are covered by the affine law.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

theorem kernel_conv_map_affine (μ ν : Measure ℝ) [SFinite μ] [SFinite ν] (a b c : ℝ) :
    (μ.map (fun x => a * x + b)) ∗ (ν.map (fun x => a * x + c)) =
      (μ ∗ ν).map (fun x => a * x + (b + c)) := by
  unfold Measure.conv
  rw [Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop), Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext x
  simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd]
  ring

theorem kernel_convPow_map_affine (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a b : ℝ) (n : ℕ) :
    convPow (μ.map (fun x => a * x + b)) n =
      (convPow μ n).map (fun x => a * x + n * b) := by
  let : IsProbabilityMeasure (μ.map (fun x => a * x + b)) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  induction n with
  | zero => simp [convPow]
  | succ n ih =>
    rw [convPow_succ, ih, kernel_conv_map_affine, ← convPow_succ]
    congr 1
    funext x
    push_cast
    ring

theorem kernel_LocBd_map_affine {μ : Measure ℝ} {M a : ℝ}
    (hM : LocBd M μ) (hM0 : 0 ≤ M) (ha : a ≠ 0) (b : ℝ) :
    LocBd (M / |a|) (μ.map (fun x => a * x + b)) := by
  intro A hA
  rw [Measure.map_apply (by fun_prop) hA]
  have hm := hM ((fun x => a * x + b) ⁻¹' A) (hA.preimage (by fun_prop))
  have hv : volume ((fun x => a * x + b) ⁻¹' A) =
      ENNReal.ofReal |a⁻¹| * volume A := by
    change volume ((fun x => a * x) ⁻¹' ((fun x => x + b) ⁻¹' A)) = _
    rw [Real.volume_preimage_mul_left ha]
    congr 1
    exact (measurePreserving_add_right volume b).measure_preimage hA.nullMeasurableSet
  rw [hv, ← mul_assoc, ← ENNReal.ofReal_mul hM0, abs_inv, ← div_eq_mul_inv] at hm
  exact hm

theorem kernel_exp_decay_le_sqrt {c n : ℝ} (hc : 0 < c) (hn : 1 ≤ n) :
    Real.exp (-c * (n - 2)) ≤ Real.exp (2 * c) / c / Real.sqrt n := by
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  have hsn : Real.sqrt n ≤ n := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) hn0.le).mp
    rw [Real.sq_sqrt hn0.le]
    nlinarith
  have he : c * Real.sqrt n ≤ Real.exp (c * n) := by
    have hmul := mul_le_mul_of_nonneg_left hsn hc.le
    linarith [Real.add_one_le_exp (c * n)]
  have hi : Real.exp (-c * n) ≤ (c * Real.sqrt n)⁻¹ := by
    rw [neg_mul, Real.exp_neg, inv_le_inv₀ (Real.exp_pos _) (mul_pos hc hs)]
    exact he
  calc
    Real.exp (-c * (n - 2)) = Real.exp (2 * c) * Real.exp (-c * n) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (2 * c) * (c * Real.sqrt n)⁻¹ :=
      mul_le_mul_of_nonneg_left hi (Real.exp_pos _).le
    _ = _ := by ring

/-- Free sums from the original regular class have a common `L / sqrt n`
density bound for every `n ≥ 2`. -/
theorem kernel_regLaw_sum_density (D θ vlo vhi : ℝ) (hD : 0 < D) (hθ : 0 < θ)
    (hvlo : 0 < vlo) (hv : vlo ≤ vhi) :
    ∃ L : ℝ, 0 < L ∧ ∀ ν : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
      ∀ n : ℕ, 2 ≤ n → LocBd (L / Real.sqrt n) (convPow (ν : Measure ℝ) n) := by
  obtain ⟨L₀, c₂, hL₀, hc₂, hbound⟩ := locBd_convPow (regV_pos hvlo)
    (regV_le_regB hv) (one_le_regBeta D θ vlo)
  let c := c₂ / D ^ 2
  have hc : 0 < c := div_pos hc₂ (sq_pos_of_pos hD)
  let L := L₀ + D * (Real.exp (2 * c) / c)
  refine ⟨L, by dsimp [L]; positivity, ?_⟩
  intro ν hν n hn
  have hloc := hbound ν D hD (hν.momClass hθ hvlo) (hν.envBd.locBd hD.le hθ.le) n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hcoeff : L₀ / Real.sqrt n + D * Real.exp (-c₂ * ((n : ℝ) - 2) / D ^ 2) ≤
      L / Real.sqrt n := by
    have he := kernel_exp_decay_le_sqrt hc hn1
    have heq : -c₂ * ((n : ℝ) - 2) / D ^ 2 = -c * ((n : ℝ) - 2) := by dsimp [c]; ring
    rw [heq]
    dsimp [L]
    calc
      _ ≤ L₀ / Real.sqrt n + D * (Real.exp (2 * c) / c / Real.sqrt n) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left he hD.le)
      _ = _ := by ring
  intro A hA
  exact (hloc A hA).trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hcoeff) le_rfl)

/-- Affine increment sums inherit the same class constant, up to the fixed
lower slope bound; their drift is unrestricted. -/
theorem kernel_survival_sum_density (D θ vlo vhi : ℝ) (hD : 0 < D) (hθ : 0 < θ)
    (hvlo : 0 < vlo) (hv : vlo ≤ vhi) :
    ∃ L : ℝ, 0 < L ∧ ∀ ν : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
      ∀ a : ℝ, 1 / 2 ≤ |a| → ∀ ρ : ℝ, ∀ n : ℕ, 2 ≤ n →
      LocBd (L / Real.sqrt n) (convPow (kernelSurvivalLaw ν a ρ : Measure ℝ) n) := by
  obtain ⟨L, hL, hb⟩ := kernel_regLaw_sum_density D θ vlo vhi hD hθ hvlo hv
  refine ⟨2 * L, by positivity, ?_⟩
  intro ν hν a ha ρ n hn
  have ha0 : a ≠ 0 := by intro he; simp only [he, abs_zero] at ha; linarith
  have heq : (kernelSurvivalLaw ν a ρ : Measure ℝ) =
      (ν : Measure ℝ).map (fun x => a * x + (-a - ρ)) := by
    change (ν : Measure ℝ).map _ = _
    congr 1
    funext x
    ring
  rw [heq, kernel_convPow_map_affine]
  have hm := kernel_LocBd_map_affine (hb ν hν n hn) (by positivity) ha0 (n * (-a - ρ))
  have hcoeff : (L / Real.sqrt n) / |a| ≤ 2 * L / Real.sqrt n := by
    rw [div_le_iff₀ (by linarith : 0 < |a|)]
    calc
      L / Real.sqrt n = (2 * L / Real.sqrt n) * (1 / 2) := by ring
      _ ≤ (2 * L / Real.sqrt n) * |a| :=
        mul_le_mul_of_nonneg_left ha (by positivity)
  intro A hA
  exact (hm A hA).trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hcoeff) le_rfl)

theorem kernel_survival_sum_concentration (D θ vlo vhi : ℝ) (hD : 0 < D) (hθ : 0 < θ)
    (hvlo : 0 < vlo) (hv : vlo ≤ vhi) :
    ∃ L : ℝ, 0 < L ∧ ∀ ν : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
      ∀ a : ℝ, 1 / 2 ≤ |a| → ∀ ρ : ℝ, ∀ n : ℕ, 2 ≤ n → ∀ z r : ℝ, 0 ≤ r →
      (iidLaw (kernelSurvivalLaw ν a ρ)).real {g | gapKeys g n ∈ Icc z (z + r)} ≤
        L * r / Real.sqrt n := by
  obtain ⟨L, hL, hb⟩ := kernel_survival_sum_density D θ vlo vhi hD hθ hvlo hv
  refine ⟨L, hL, ?_⟩
  intro ν hν a ha ρ n hn z r hr
  have hh := hb ν hν a ha ρ n hn (Icc z (z + r)) measurableSet_Icc
  have hmeas : Measurable (fun g : ℕ → ℝ => gapKeys g n) :=
    (measurable_pi_apply n).comp measurable_gapKeys
  rw [← map_gapKeys_eq_convPow, Measure.map_apply hmeas measurableSet_Icc,
    Real.volume_Icc, add_sub_cancel_left, ← ENNReal.ofReal_mul (by positivity)] at hh
  have ht := ENNReal.toReal_le_of_le_ofReal (show 0 ≤ (L / Real.sqrt n) * r by positivity) hh
  simpa only [Measure.real, div_mul_eq_mul_div, Set.preimage] using ht

end
end PGM
