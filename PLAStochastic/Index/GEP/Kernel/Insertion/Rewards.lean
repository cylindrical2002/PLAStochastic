import PLAStochastic.Index.GEP.Kernel.Insertion.SlopeWindow
import PLAStochastic.Index.GEP.Kernel.Insertion.ExteriorReward

/-! # The actual scalar and output rewards in the near insertion coefficient -/
namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set

/-- Positivity of both physical pin lengths, expressed in the marked direction. -/
def krInsertionEffective (w : ℝ) (up : Bool) (l r m : ℕ) : Prop :=
  0 < ((l+r+1 : ℕ) : ℝ)-(if up then w else -w) ∧
    0 < krInsertionOtherFactor w up m

/-- The exact scalar normalization, restricted to the effective facets. -/
def krInsertionScalarReward (C w : ℝ) (up : Bool)
    (l r : ℕ) (t : ℕ × ℕ × ℕ) (_a : ℝ) (_g : ℕ → ℝ) : ℝ := by
  classical
  exact if krInsertionEffective w up l r t.2.1 then 1/C else 0

/-- The original reconstructed physical sum with the justified positive extension
of the boundary reward; both exterior paths remain in this single reward. -/
def krInsertionOutputReward (ν : ProbabilityMeasure ℝ) (C : ℝ) (ψ : ℝ → ℝ)
    (w : ℝ) (up outerUp : Bool) (l r : ℕ) (t : ℕ × ℕ × ℕ) (a : ℝ) (g : ℕ → ℝ) : ℝ := by
  classical
  exact if krInsertionEffective w up l r t.2.1 then
    kernelPositiveBoundaryReward ν C ψ (kernelIFPhysicalSum a
      (kernelIFLeftOfBlocks (t.1,l,r,t.2.1,t.2.2,outerUp)).1.2.2 g)
  else 0

/-- The actual near contribution for one marked and one exterior orientation. -/
def krInsertionNearKernel (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ) (w A : ℝ)
    (up outerUp : Bool) (W : ℕ → ℕ → (ℕ × ℕ × ℕ) → ℝ → (ℕ → ℝ) → ℝ)
    (x : ℝ) : ℝ :=
  ∫ a in kernelNearSlopes w A, ∑' q : ℕ × ℕ,
    krInsertionCoefficient ν f w up outerUp W q.1 q.2 a*
      kernelMarkedFullDens (Icc 0 w) ν f 1 a x q.1 q.2
        (if up then 0 else w) (if up then w else 0)

theorem measurable_krInsertionScalarReward (C w : ℝ) (up : Bool)
    (l r : ℕ) (t : ℕ × ℕ × ℕ) :
    Measurable (fun p : ℝ × (ℕ → ℝ) => krInsertionScalarReward C w up l r t p.1 p.2) :=
  measurable_const

theorem measurable_krInsertionOutputReward {η M : ℝ} {ψ : ℝ → ℝ}
    (hψ : OutTest η M ψ) (ν : ProbabilityMeasure ℝ) (C w : ℝ) (up outerUp : Bool)
    (l r : ℕ) (t : ℕ × ℕ × ℕ) :
    Measurable (fun p : ℝ × (ℕ → ℝ) => krInsertionOutputReward ν C ψ w up outerUp l r t p.1 p.2) := by
  unfold krInsertionOutputReward
  split_ifs
  · exact (measurable_kernelPositiveBoundaryReward hψ ν C).comp (measurable_kernelIFPhysicalSum_joint _)
  · exact measurable_const

theorem krInsertion_scalar_reward_bound {C w ε M : ℝ} (hC : 0 < C) (hM : 0 ≤ M)
    (hε : 0 ≤ ε) (hInv : 1/C ≤ M/w^2) (up : Bool)
    (l r : ℕ) (t : ℕ × ℕ × ℕ) (a : ℝ) (g : ℕ → ℝ) :
    |krInsertionScalarReward C w up l r t a g| ≤
      (M/w^2)*Real.exp (ε*((t.1 : ℝ)+l+r+t.2.1+t.2.2+2)/w^2) := by
  unfold krInsertionScalarReward
  split_ifs
  · rw [abs_of_pos (by positivity)]
    exact hInv.trans (le_mul_of_one_le_right (div_nonneg hM (sq_nonneg _))
      (Real.one_le_exp_iff.mpr (by positivity)))
  · simp only [abs_zero]
    positivity

theorem krInsertion_output_reward_bound {D θ vlo vhi η M C a w ε N : ℝ}
    {ν : ProbabilityMeasure ℝ} {ψ : ℝ → ℝ} (hν : RegLaw D θ vlo vhi ν)
    (hθ : 0 < θ) (hψ : OutTest η M ψ) (hη : 0 ≤ η) (hC : 0 < C)
    (hscale : η/C ≤ θ/4) (ha : 1/2 ≤ a) (hw : 1 ≤ w) (hε : 0 ≤ ε)
    (hnear : η/C ≤ ε/(2*w^2)) (hN : 0 ≤ N)
    (hEnv : M*(8*D/θ^2)/C*Real.exp ε ≤ N/w^2)
    (up outerUp : Bool) (l r : ℕ) (t : ℕ × ℕ × ℕ) (g : ℕ → ℝ)
    (hout : krInsertionOuter w outerUp l r t a g ≠ 0) :
    |krInsertionOutputReward ν C ψ w up outerUp l r t a g| ≤
      (N/w^2)*Real.exp (ε*((t.1 : ℝ)+l+r+t.2.1+t.2.2+2)/w^2) := by
  unfold krInsertionOutputReward
  split_ifs
  · have hh := kernel_positive_reward_near_bound hν hθ hψ hη hC hscale ha hw hε hnear
      (kernelIFLeftOfBlocks (t.1,l,r,t.2.1,t.2.2,outerUp)).1.2.2 hout
    have he : (((kernelIFLeftOfBlocks (t.1,l,r,t.2.1,t.2.2,outerUp)).1.1 : ℕ) : ℝ) =
        (t.1 : ℝ)+l+r+t.2.1+t.2.2+2 := by
      simp only [kernelIFLeftOfBlocks,Nat.cast_add,Nat.cast_one]
      ring
    rw [he] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right hEnv (Real.exp_nonneg _))
  · simp only [abs_zero]
    positivity


/-- The only effective single-gap root is outside the entire near window. -/
theorem kernelNearSlopes_dirac_notMem {w A x : ℝ} (hw : 0 < w) (hA : A ≤ w/4)
    (hx : 0 < x) (hxw : 2*x ≤ w+1) : (w+1)/x ∉ kernelNearSlopes w A := by
  intro hm
  have hh := ((kernelNearSlopes_subset hw hA) hm).2
  have hh' := (div_lt_iff₀ hx).mp hh
  linarith

end
end PGM
