import PLAStochastic.Index.GEP.Kernel.Tail.Scalar.Infinite
import PLAStochastic.Index.GEP.Kernel.Marked.Pin.FullFarWindow

/-!
# Actual infinite bulk budgets on a far saddle annulus

The retained killed-time exponent pays for all three random lengths before
slope integration. Width powers are explicit, so logarithmic windows can be
chosen after the desired error order.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

theorem kernel_pair_saddle_budget (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ)
    {w a x y z k K U : ℝ} (hw : 1 ≤ w) (hk : 0 < k) (hK : 0 ≤ K)
    (hp : ∀ l r M : ℕ, 1 ≤ l+r → 1 ≤ M →
      kernelMarkedFullDens (Icc 0 w) ν f 1 a x l r y z *
        krDens (Icc 0 w) ν f 1 a M z y ≤
      K*w*Real.exp (U-k*((l : ℝ)+r+M)/w^2)) (L R M : ℕ) :
    kernelPairTailSum ν f w a x y z L R M ≤
      (K*(3*(1+4/k)^4))*w^10*Real.exp U := by
  have hw0 : 0 < w := by linarith
  have hb (l r m : ℕ) : kernelMarkedFullDens (Icc 0 w) ν f 1 a x l r y z *
      krDens (Icc 0 w) ν f 1 a (m+1) z y ≤
      (K*w*Real.exp U)*Real.exp (-(k/(4*w^2))*((l : ℝ)+r+(m+1))) := by
    by_cases hlr : 1 ≤ l+r
    · have hh := hp l r (m+1) hlr (by omega)
      apply hh.trans
      rw [mul_assoc (K*w) (Real.exp U), ← Real.exp_add]
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
      have hN : 0 ≤ (l : ℝ)+r+(m+1) := by positivity
      push_cast
      have he : k*((l : ℝ)+r+(m+1))/w^2 =
          4*((k/(4*w^2))*((l : ℝ)+r+(m+1))) := by field_simp
      rw [he]
      nlinarith [mul_nonneg (show 0 ≤ k/(4*w^2) by positivity) hN]
    · have hl : l=0 := by omega
      have hr : r=0 := by omega
      simp only [hl,hr,kernelMarkedFullDens,zero_mul]
      positivity
  have hh := kernelPairTailSum_le_of_exp ν f hw0.le
    (show 0 < k/(4*w^2) by positivity) (show 0 ≤ K*w*Real.exp U by positivity) hb L R M
  exact (hh.trans (mul_le_mul_of_nonneg_left (kernel_time_sum_polynomial hk hw)
    (show 0 ≤ K*w*Real.exp U by positivity))).trans_eq (by ring)

theorem kernel_bulk_saddle_budget (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ)
    {w a x y z k K O U : ℝ} (hw : 1 ≤ w) (hk : 0 < k) (hK : 0 ≤ K) (_hO : 0 ≤ O)
    (ho : kernelOuterWeight ν w a ≤ O*w^6)
    (hp : ∀ l r M : ℕ, 1 ≤ l+r → 1 ≤ M →
      kernelMarkedFullDens (Icc 0 w) ν f 1 a x l r y z *
        krDens (Icc 0 w) ν f 1 a M z y ≤
      K*w*Real.exp (U-k*((l : ℝ)+r+M)/w^2)) (L R M : ℕ) :
    kernelOuterWeight ν w a * kernelPairTailSum ν f w a x y z L R M ≤
      (O*K*(3*(1+4/k)^4))*w^16*Real.exp U := by
  calc
    _ ≤ kernelOuterWeight ν w a * ((K*(3*(1+4/k)^4))*w^10*Real.exp U) :=
      mul_le_mul_of_nonneg_left (kernel_pair_saddle_budget ν f hw hk hK hp L R M)
        (kernelOuterWeight_nonneg ν w a)
    _ ≤ (O*w^6) * ((K*(3*(1+4/k)^4))*w^10*Real.exp U) :=
      mul_le_mul_of_nonneg_right ho (by positivity)
    _ = _ := by ring

/-- The actual infinite nonnegative bulk at a fixed slope has the same
annular exponential factor as the original marked pair. -/
theorem kernel_bulk_saddle_infinite (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ}
    (hf0 : ∀ t, 0 ≤ f t) {w a x y z k K O U : ℝ}
    (hw : 1 ≤ w) (hk : 0 < k) (hK : 0 ≤ K) (hO : 0 ≤ O)
    (ho : kernelOuterWeight ν w a ≤ O*w^6)
    (hp : ∀ l r M : ℕ, 1 ≤ l+r → 1 ≤ M →
      kernelMarkedFullDens (Icc 0 w) ν f 1 a x l r y z *
        krDens (Icc 0 w) ν f 1 a M z y ≤
      K*w*Real.exp (U-k*((l : ℝ)+r+M)/w^2)) :
    (∑' p : ℕ × ℕ × ℕ, ENNReal.ofReal (kernelBulkTailTerm ν f w x y z a p)) ≤
      ENNReal.ofReal ((O*K*(3*(1+4/k)^4))*w^16*Real.exp U) := by
  rw [kernel_ennreal_triple_eq_iSup_cube]
  apply iSup_le
  intro N
  rw [kernelBulkTailTerm_cube ν hf0 (by linarith)]
  exact ENNReal.ofReal_le_ofReal (kernel_bulk_saddle_budget ν f hw hk hK hO ho hp N N N)

/-- Integrating over any subset of the compact saddle region adds only its
fixed length. The subset can depend on the growing annulus threshold. -/
theorem kernel_bulk_saddle_integral (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ}
    (hf0 : ∀ t, 0 ≤ f t) {w x y z k K O U : ℝ} {S : Set ℝ}
    (hw : 1 ≤ w) (hk : 0 < k) (hK : 0 ≤ K) (hO : 0 ≤ O)
    (hS : S ⊆ Icc (1/2 : ℝ) 2)
    (ho : ∀ a ∈ S, kernelOuterWeight ν w a ≤ O*w^6)
    (hp : ∀ a ∈ S, ∀ l r M : ℕ, 1 ≤ l+r → 1 ≤ M →
      kernelMarkedFullDens (Icc 0 w) ν f 1 a x l r y z *
        krDens (Icc 0 w) ν f 1 a M z y ≤
      K*w*Real.exp (U-k*((l : ℝ)+r+M)/w^2))
    (hSm : MeasurableSet S) :
    (∫⁻ a in S, ∑' p : ℕ × ℕ × ℕ, ENNReal.ofReal (kernelBulkTailTerm ν f w x y z a p)) ≤
      ENNReal.ofReal ((2*O*K*(3*(1+4/k)^4))*w^16*Real.exp U) := by
  let B := (O*K*(3*(1+4/k)^4))*w^16*Real.exp U
  have hB : 0 ≤ B := by dsimp [B]; positivity
  calc
    _ ≤ ∫⁻ _a in S, ENNReal.ofReal B := lintegral_mono_ae (by
      filter_upwards [ae_restrict_mem hSm] with a ha
      exact kernel_bulk_saddle_infinite ν hf0 hw hk hK hO (ho a ha) (hp a ha))
    _ ≤ ∫⁻ _a in Icc (1/2 : ℝ) 2, ENNReal.ofReal B := lintegral_mono_set hS
    _ = ENNReal.ofReal (B*(3/2)) := by
      simp only [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc]
      norm_num
      rw [← ENNReal.ofReal_mul hB]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by dsimp [B] at *; nlinarith)

end
end PGM
