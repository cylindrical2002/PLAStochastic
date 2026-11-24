import PLAStochastic.Index.GEP.Kernel.Insertion.SlopeIntegratedGreen

/-!
# Width-scale cutoff for the near-critical insertion decomposition

The short square uses floor(w/8). Its complement begins at order w, so the
regular row budget grows only as w^(1/4), and its geometric error decays at
an exponential rate in w.
-/
namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

/-- One cutoff meets both short-step conditions and retains a linear lower bound. -/
theorem krInsertion_cutoff {w : ℝ} (hw : 96 ≤ w) :
    12 ≤ ⌊w/8⌋₊ ∧ (⌊w/8⌋₊ : ℝ) ≤ w/8 ∧ w/16 ≤ (⌊w/8⌋₊ : ℝ) := by
  have hw0 : 0 ≤ w/8 := by linarith
  refine ⟨(Nat.le_floor_iff hw0).2 (by norm_num; linarith),Nat.floor_le hw0,?_⟩
  have ht := Nat.lt_floor_add_one (w/8)
  linarith

/-- The row variation budget has the original fourth-root width scale. -/
theorem krInsertion_cutoff_fourth {w : ℝ} (hw : 96 ≤ w) :
    Real.sqrt w/krFourthRoot (⌊w/8⌋₊ : ℝ)+1 ≤ 3*krFourthRoot w := by
  have hw0 : 0 < w := by linarith
  obtain ⟨hP,_,hPw⟩ := krInsertion_cutoff hw
  have hP0 : 0 < (⌊w/8⌋₊ : ℝ) := by exact_mod_cast (show 0 < ⌊w/8⌋₊ by omega)
  have hp := krFourthRoot_pos hP0
  have hq := krFourthRoot_nonneg w
  have hbase : krFourthRoot w ≤ 2*krFourthRoot (⌊w/8⌋₊ : ℝ) := by
    apply (pow_le_pow_iff_left₀ hq (by positivity) (by decide : (4 : ℕ) ≠ 0)).mp
    rw [mul_pow,krFourthRoot_pow_four hw0.le,krFourthRoot_pow_four hP0.le]
    norm_num
    linarith
  have hratio : Real.sqrt w/krFourthRoot (⌊w/8⌋₊ : ℝ) ≤ 2*krFourthRoot w := by
    apply (div_le_iff₀ hp).2
    rw [← krFourthRoot_sq w]
    nlinarith [mul_le_mul_of_nonneg_left hbase hq]
  have h1 : 1 ≤ krFourthRoot w := by
    have h := krFourthRoot_le_krFourthRoot (by linarith : (1 : ℝ) ≤ w)
    simpa only [krFourthRoot,Real.sqrt_one] using h
  linarith

/-- No logarithmic loss is needed to convert the long-row error into exp(-cw). -/
theorem krInsertion_cutoff_geometric {w q : ℝ} (hw : 96 ≤ w) (hq0 : 0 ≤ q)
    (hq1 : q ≤ 1) :
    q^(⌊w/8⌋₊/3-1) ≤ Real.exp (-((1-q)/96)*w) := by
  obtain ⟨hP,_,hPw⟩ := krInsertion_cutoff hw
  have hn : ⌊w/8⌋₊ ≤ 6*(⌊w/8⌋₊/3-1) := by omega
  have hn' : (⌊w/8⌋₊ : ℝ) ≤ 6*((⌊w/8⌋₊/3-1 : ℕ) : ℝ) := by exact_mod_cast hn
  have hN : w/96 ≤ ((⌊w/8⌋₊/3-1 : ℕ) : ℝ) := by linarith
  calc
    _ ≤ (Real.exp (q-1))^(⌊w/8⌋₊/3-1) :=
      pow_le_pow_left₀ hq0 (by linarith [Real.add_one_le_exp (q-1)]) _
    _ = Real.exp (((⌊w/8⌋₊/3-1 : ℕ) : ℝ)*(q-1)) := (Real.exp_nat_mul _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)

/-- The number of short terms and their exponential length weight cost only w². -/
theorem krInsertion_cutoff_short_factor {w ε : ℝ} (hw : 96 ≤ w) (_hε0 : 0 ≤ ε)
    (hε : ε ≤ 1) :
    ((⌊w/8⌋₊+1 : ℕ) : ℝ)^2*Real.exp (2*ε*(⌊w/8⌋₊ : ℝ)/w^2) ≤
      w^2*Real.exp 1 := by
  obtain ⟨_,hP,_⟩ := krInsertion_cutoff hw
  have hw0 : 0 < w := by linarith
  have hP0 : 0 ≤ (⌊w/8⌋₊ : ℝ) := Nat.cast_nonneg _
  have hcount : ((⌊w/8⌋₊+1 : ℕ) : ℝ)^2 ≤ w^2 := by
    rw [Nat.cast_add,Nat.cast_one]
    nlinarith
  have hnum : 2*ε*(⌊w/8⌋₊ : ℝ) ≤ w^2 := by
    nlinarith [mul_le_mul_of_nonneg_right hε hP0]
  apply mul_le_mul hcount (Real.exp_le_exp.mpr ((div_le_one (sq_pos_of_pos hw0)).2 hnum))
    (Real.exp_pos _).le (sq_nonneg _)

end
end PGM
