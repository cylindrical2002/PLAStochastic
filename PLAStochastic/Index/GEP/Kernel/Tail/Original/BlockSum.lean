import PLAStochastic.Index.GEP.Kernel.Tail.Weighted.Joint
import PLAStochastic.Index.GEP.Kernel.Influence.Coarea.BlockIndex

/-! # Abstract nonnegative block sums shared by scalar and physical-weight IF -/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
set_option maxHeartbeats 1000000

def kernelIFBlockReorder : KernelIFBlockIndex ≃ (ℕ × ℕ × ℕ) × ℕ × ℕ × Bool where
  toFun p := ((p.2.1,p.2.2.1,p.2.2.2.1),p.1,p.2.2.2.2.1,p.2.2.2.2.2)
  invFun p := (p.2.1,p.1.1,p.1.2.1,p.1.2.2,p.2.2.1,p.2.2.2)
  left_inv p := by rcases p with ⟨u,l,h,m,v,σ⟩; rfl
  right_inv p := by rcases p with ⟨⟨l,h,m⟩,u,v,σ⟩; rfl

theorem kernel_block_tsum_split (B : ℕ → ℕ → ℕ → ℕ → ℕ → ℝ≥0∞)
    (D : ℕ → ℕ → ℕ → ℝ≥0∞) :
    (∑' p : KernelIFBlockIndex, (B p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 +
      (if p.2.1 = 0 ∧ p.2.2.1 = 0 then D p.1 p.2.2.2.1 p.2.2.2.2.1 else 0))) =
      2 * ((∑' p : ℕ × ℕ × ℕ, ∑' u : ℕ, ∑' v : ℕ, B u p.1 p.2.1 p.2.2 v) +
        ∑' m : ℕ, ∑' u : ℕ, ∑' v : ℕ, D u m v) := by
  classical
  rw [← kernelIFBlockReorder.symm.tsum_eq]
  change (∑' p : (ℕ × ℕ × ℕ) × ℕ × ℕ × Bool,
    (B p.2.1 p.1.1 p.1.2.1 p.1.2.2 p.2.2.1 +
      (if p.1.1 = 0 ∧ p.1.2.1 = 0 then D p.2.1 p.1.2.2 p.2.2.1 else 0))) = _
  simp only [ENNReal.tsum_prod']
  have hb (z : ℝ≥0∞) : (∑' _ : Bool, z) = 2 * z := by
    rw [tsum_fintype]
    simp [two_mul]
  simp_rw [hb, ENNReal.tsum_mul_left, ENNReal.tsum_add]
  simp only [ite_and]
  have hi (P : Prop) [Decidable P] (F G : ℕ → ℝ≥0∞) :
      (∑' n, if P then F n else G n) = if P then ∑' n, F n else ∑' n, G n := by
    by_cases h : P <;> simp [h]
  simp_rw [hi, tsum_zero]
  simp only [tsum_ite_eq]


theorem kernel_real_outer_pair_sum (A B C D : ℕ → ℝ)
    (hA : ∀ n, 0 ≤ A n) (hB : ∀ n, 0 ≤ B n) (hC : ∀ n, 0 ≤ C n) (hD : ∀ n, 0 ≤ D n)
    (hAs : Summable A) (hBs : Summable B) (hCs : Summable C) (hDs : Summable D) :
    (∑' u : ℕ, ∑' v : ℕ, ENNReal.ofReal (A u * B v + C u * D v)) =
      ENNReal.ofReal ((∑' u, A u) * (∑' v, B v) + (∑' u, C u) * (∑' v, D v)) := by
  simp_rw [ENNReal.ofReal_add (mul_nonneg (hA _) (hB _)) (mul_nonneg (hC _) (hD _)),
    ENNReal.ofReal_mul (hA _), ENNReal.ofReal_mul (hC _),
    ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]
  rw [← ENNReal.ofReal_tsum_of_nonneg hA hAs, ← ENNReal.ofReal_tsum_of_nonneg hB hBs,
    ← ENNReal.ofReal_tsum_of_nonneg hC hCs, ← ENNReal.ofReal_tsum_of_nonneg hD hDs,
    ← ENNReal.ofReal_mul (tsum_nonneg hA), ← ENNReal.ofReal_mul (tsum_nonneg hC),
    ← ENNReal.ofReal_add (mul_nonneg (tsum_nonneg hA) (tsum_nonneg hB))
      (mul_nonneg (tsum_nonneg hC) (tsum_nonneg hD))]

theorem kernel_outer_factor_sum {O : ℕ → ℕ → ℝ} {W P : ℝ}
    (hO : ∀ u v, 0 ≤ O u v) (hW : 0 ≤ W)
    (hs : (∑' u, ∑' v, ENNReal.ofReal (O u v)) = ENNReal.ofReal W) :
    (∑' u, ∑' v, ENNReal.ofReal (O u v * P)) = ENNReal.ofReal (W * P) := by
  simp_rw [ENNReal.ofReal_mul (hO _ _), ENNReal.tsum_mul_right]
  rw [hs, ← ENNReal.ofReal_mul hW]

theorem kernel_block_sum_lintegral {ι : Type*} [Countable ι]
    {F : ℝ → ι → ℕ → ℕ → ℝ≥0∞} (hF : ∀ p u v, Measurable (fun a => F a p u v))
    (S : Set ℝ) :
    (∑' p, ∑' u : ℕ, ∑' v : ℕ, ∫⁻ a in S, F a p u v) =
      ∫⁻ a in S, ∑' p, ∑' u : ℕ, ∑' v : ℕ, F a p u v := by
  have hh := (lintegral_tsum (μ := volume.restrict S)
    (fun p : ι × ℕ × ℕ => (hF p.1 p.2.1 p.2.2).aemeasurable)).symm
  simpa only [ENNReal.tsum_prod'] using hh

end
end PGM
