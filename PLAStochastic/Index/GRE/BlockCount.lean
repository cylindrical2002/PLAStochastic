import PLAStochastic.Index.Model.BlockGaps
import PLAStochastic.Index.Algorithm.RankHierarchy

/-!
# Model G, rank-equispaced promotion: block laws and the count reduction

The layer-`ℓ` keys of ALG-RE are the input keys at the ranks `j Δ_ℓ`, so the segment
count of layer `ℓ` is the ALG-OPT count of the block walk with gaps
`blockGap g Δ_ℓ` (`PLAcount_eq_blockCount`).  Every block law belongs to one fixed
class: relative variance `v₀ / d ≤ v₀` and normalised third moment `≤ 2 + β₀`
(`blockGap_class`), and its scale is `G_d = d · G₀`.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Finset

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- ALG-OPT segment count on the first `K` keys of the block walk. -/
def blockCount (eps : ℝ) (g : ℕ → Ω → ℝ) (d K : ℕ) (ω : Ω) : ℕ :=
  finSegCount eps (gapKeys (seq (blockGap g d) ω)) K

omit mΩ in
/-- The ALG-RE segment count on a lattice is the block-walk count. -/
theorem PLAcount_eq_blockCount (eps : ℝ) (g : ℕ → Ω → ℝ) (d K : ℕ) (ω : Ω) :
    PLAcount eps (fun i => g i ω) d K = blockCount eps g d K ω := by
  unfold PLAcount blockCount
  congr 1
  funext j
  rw [gapKeys_blockGap]
  rfl

/-- The block laws stay in one class, uniformly in the block length. -/
theorem blockGap_class {g : ℕ → Ω → ℝ} {μ₀ σ₀ κ₀ : ℝ} (hg : GapLaw P g μ₀ σ₀ κ₀)
    {d : ℕ} (hd : 1 ≤ d) :
    GapLaw P (blockGap g d) (d * μ₀) (Real.sqrt d * σ₀)
        (2 * d * Real.sqrt d * σ₀ ^ 3 + d * κ₀) ∧
      (Real.sqrt d * σ₀) ^ 2 ≤ σ₀ ^ 2 / μ₀ ^ 2 * (d * μ₀) ^ 2 ∧
      2 * d * Real.sqrt d * σ₀ ^ 3 + d * κ₀ ≤ (2 + κ₀ / σ₀ ^ 3) * (Real.sqrt d * σ₀) ^ 3 ∧
      (d * μ₀) ^ 2 * eps ^ 2 / (Real.sqrt d * σ₀) ^ 2 = d * (μ₀ ^ 2 * eps ^ 2 / σ₀ ^ 2) := by
  have hμ := hg.mu_pos
  have hσ := hg.sigma_pos
  have hκ := hg.kappa_nonneg
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  have hsq : Real.sqrt (d : ℝ) ^ 2 = d := Real.sq_sqrt hdpos.le
  have hsqrt1 : 1 ≤ Real.sqrt (d : ℝ) := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt hd'
  refine ⟨hg.block hd, ?_, ?_, ?_⟩
  · rw [mul_pow, hsq]
    have : σ₀ ^ 2 / μ₀ ^ 2 * (d * μ₀) ^ 2 = d * (d * σ₀ ^ 2) := by field_simp
    rw [this]
    have : 0 ≤ d * σ₀ ^ 2 := by positivity
    nlinarith
  · have hs3 : (Real.sqrt d * σ₀) ^ 3 = d * Real.sqrt d * σ₀ ^ 3 := by
      rw [mul_pow, show Real.sqrt (d : ℝ) ^ 3 = Real.sqrt d ^ 2 * Real.sqrt d by ring, hsq]
    rw [hs3]
    have hk : d * κ₀ ≤ κ₀ / σ₀ ^ 3 * (d * Real.sqrt d * σ₀ ^ 3) := by
      have : κ₀ / σ₀ ^ 3 * (d * Real.sqrt d * σ₀ ^ 3) = d * Real.sqrt d * κ₀ := by
        field_simp
      rw [this]
      have : d * κ₀ ≤ d * κ₀ * Real.sqrt d := le_mul_of_one_le_right (by positivity) hsqrt1
      linarith
    linarith
  · rw [mul_pow, mul_pow, hsq]
    field_simp

end

end PGM
