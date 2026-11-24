import PLAStochastic.Index.GEP.Kernel.Marked.Pin.FullSaddle
import PLAStochastic.Index.GEP.Kernel.Marked.Pin.FarWindow

/-! # Actual marked pin pairs outside a near-critical slope window -/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set
set_option maxHeartbeats 800000

/-- A pointwise far-window bound for the original marked pair, retaining a
summable killed-time exponent. All constants precede the input law and window.
The designated gap is nonnegative; its growth is the explicit `exp (θ*t/2)`.
At least one random step remains; the separate Dirac bridge is not included. -/
theorem kernel_regLaw_full_marked_pin_far_window (D θ vlo vhi : ℝ)
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi) :
    ∃ δ q k K : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧ 0 < q ∧ 0 < k ∧ 0 < K ∧
      ∀ ν : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
      ∃ f : ℝ → ℝ, Measurable f ∧ (∀ x, 0 ≤ f x) ∧
        (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x)) ∧
        ∀ a : ℝ, |a - 1| ≤ δ → ∀ w : ℝ, 1 ≤ w → ∀ t : ℝ, 0 ≤ t →
        ∀ A : ℝ, A ≤ w * |a - 1| → ∀ y z : ℝ, |z - y| = w →
        ∀ l r M : ℕ, 1 ≤ l + r → 1 ≤ M →
          kernelMarkedFullDens (Icc 0 w) ν f 1 a t l r y z * krDens (Icc 0 w) ν f 1 a M z y ≤
            K * w * Real.exp (θ / 2 * t - q * A - k * ((l : ℝ) + r + M) / w ^ 2) := by
  obtain ⟨δ, c, d, k, K, hδ, hδhi, hc, hd, hk, hK, hdecay⟩ :=
    kernel_regLaw_saddle_full_marked_pin_decay D θ vlo vhi hD hθ hvlo hv
  obtain ⟨δ', c', hδ', _, _, hsaddle⟩ := kernel_regLaw_saddle_rate D θ vlo vhi hθ hvlo hv
  let q := min c d
  have hq : 0 < q := lt_min hc hd
  refine ⟨min δ δ', q, k, K * Real.exp (θ + 8 * k), lt_min hδ hδ',
    (min_le_left _ _).trans hδhi, hq, hk, by positivity, ?_⟩
  intro ν hν
  obtain ⟨f, hf, hf0, hνf, hb⟩ := hdecay ν hν
  refine ⟨f, hf, hf0, hνf, ?_⟩
  intro a ha w hw t ht A hA y z hyz l r M hlr hM
  have haδ := ha.trans (min_le_left δ δ')
  have haδ' := ha.trans (min_le_right δ δ')
  have hh := hb a haδ 0 w hw t y z l r M hlr hM
  have hyz2 : (z - y) ^ 2 = w ^ 2 := by rw [← sq_abs (z - y), hyz]
  simp only [zero_add, hyz, hyz2] at hh
  let N : ℝ := (l : ℝ) + r + M
  let Q := min (w ^ 2 / (M : ℝ)) w
  let lam := kernelTiltSaddle D θ vlo ν a
  have hw0 : 0 < w := by linarith
  have hM0 : 0 < (M : ℝ) := by exact_mod_cast hM
  have hmN : (M : ℝ) ≤ N := by
    dsimp [N]
    linarith [Nat.cast_nonneg (α := ℝ) l, Nat.cast_nonneg (α := ℝ) r]
  have hs : |a - 1| ≤ 1 := (haδ.trans hδhi).trans (by norm_num)
  have henergy := kernelFar_crossing_energy hw0.le hM0 hmN hs
  have hQ0 : 0 ≤ Q := le_min (by positivity) hw0.le
  have hcost : q * w * |a - 1| ≤ c * N * (a - 1) ^ 2 + d * Q := by
    have h₁ := mul_le_mul_of_nonneg_left henergy hq.le
    have h₂ := mul_le_mul_of_nonneg_right (min_le_left c d)
      (show 0 ≤ N * (a - 1) ^ 2 by positivity)
    have h₃ := mul_le_mul_of_nonneg_right (min_le_right c d) hQ0
    change q * (w * |a - 1|) ≤ q * (N * (a - 1) ^ 2 + Q) at h₁
    change q * (N * (a - 1) ^ 2) ≤ c * (N * (a - 1) ^ 2) at h₂
    change q * Q ≤ d * Q at h₃
    nlinarith
  have hlam := (hsaddle ν hν a haδ').1
  have hlam' : |lam| ≤ θ / 2 := (hlam.trans (min_le_left _ _)).trans
    ((saTiltRadius_le_half _ _ (by positivity)).trans (by linarith))
  have ha0 : 0 < a := by linarith [(abs_le.mp haδ).1]
  have halo : 1 / 2 ≤ a := by linarith [(abs_le.mp haδ).1]
  have hquot : -lam / a ≤ θ := by
    apply (div_le_iff₀ ha0).mpr
    have hh' := (neg_le_abs lam).trans hlam'
    nlinarith
  have hins : lam * t - lam / a ≤ θ / 2 * t + θ := by
    have hh' := mul_le_mul_of_nonneg_right ((le_abs_self lam).trans hlam') ht
    rw [neg_div] at hquot
    linarith only [hh', hquot]
  have htime : k * 8 / w ^ 2 ≤ 8 * k := by
    apply (div_le_iff₀ (sq_pos_of_pos hw0)).mpr
    have hw2 : 1 ≤ w ^ 2 := by nlinarith
    nlinarith
  have hqA := mul_le_mul_of_nonneg_left hA hq.le
  have hexp : -c * N * (a - 1) ^ 2 + lam * t - lam / a - d * Q -
      k * (N - 8) / w ^ 2 ≤ (θ + 8 * k) + (θ / 2 * t - q * A - k * N / w ^ 2) := by
    have he : k * (N - 8) / w ^ 2 = k * N / w ^ 2 - k * 8 / w ^ 2 := by ring
    rw [he]
    nlinarith
  apply hh.trans
  have hex := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp)
    (show 0 ≤ K * w by positivity)
  change K * w * Real.exp (-c * N * (a - 1) ^ 2 + lam * t - lam / a - d * Q -
      k * (N - 8) / w ^ 2) ≤ _
  refine hex.trans_eq ?_
  rw [Real.exp_add]
  ring

end
end PGM
