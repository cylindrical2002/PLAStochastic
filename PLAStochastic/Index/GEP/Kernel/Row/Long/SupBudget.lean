import PLAStochastic.Index.GEP.Kernel.Row.Long.AbsoluteBudget

/-!
# Summable uniform upper envelopes of actual boundary rows

The supremum is bounded before summing lengths. This is stronger than a
pointwise Green bound and is required for signed rewards of the total length.
-/
namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

def krRowSupBudget (D K L vlo vhi w A : ℝ) (n : ℕ) : ℝ :=
  if n < 2 * krT w then krC₁ D K L * (1+A) / n
  else krC₄ D K L * (1+A) / w^2 * Real.sqrt (krLam D vlo vhi w) ^ (n-2*krT w)

variable {D θ vlo vhi K L w A a β a' : ℝ} (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ}

theorem krRowSupBudget_nonneg (H : KrBand D θ vlo vhi K L ν f w A a β a') (n : ℕ) :
    0 ≤ krRowSupBudget D K L vlo vhi w A n := by
  have hC₁ := krC₁_nonneg (K := K) (L := L) H.hD0 H.hK H.hL0.le
  have hC₄ : 0 ≤ krC₄ D K L := Real.sqrt_nonneg _
  have hA := H.hA
  unfold krRowSupBudget
  split_ifs <;> positivity

theorem krDens_le_rowSupBudget (H : KrBand D θ vlo vhi K L ν f w A a β a')
    {b : ℝ} (hb : b=0 ∨ b=w) {n : ℕ} (hn : 1 ≤ n) (z : ℝ) :
    krDens (Icc 0 w) ν f β a' n b z ≤ krRowSupBudget D K L vlo vhi w A n := by
  unfold krRowSupBudget
  split_ifs with h
  · apply krDens_bdry_medium ν H hb hn
    have hnr : (n : ℝ) ≤ 2 * (krT w : ℝ) := by exact_mod_cast h.le
    linarith [H.hTw]
  · have he : n = krT w + (n-2*krT w) + krT w := by omega
    have h := krDens_bdry_row_large ν H hb H.hT1 H.hTw H.hwT (n-2*krT w) z
    rw [← he] at h
    exact h.trans_eq (by ring)

theorem sum_krRowSupBudget_le (H : KrBand D θ vlo vhi K L ν f w A a β a') (N : ℕ) :
    ∑ n ∈ Finset.range N, krRowSupBudget D K L vlo vhi w A (n+1) ≤
      krCG D K L vlo vhi * (1+A) * (1+Real.log w) := by
  have hw0 := H.hw0
  have hw := H.hw
  have hA := H.hA
  have hκ := H.kappa_pos
  have hC₁ := krC₁_nonneg (K := K) (L := L) H.hD0 H.hK H.hL0.le
  have hC₄ : 0 ≤ krC₄ D K L := Real.sqrt_nonneg _
  have hlogw : 0 ≤ Real.log w := Real.log_nonneg hw
  set T := krT w with hTdef
  have hT1 := H.hT1
  have hTw := H.hTw
  have hwT := H.hwT
  have hF : ∀ n, 0 ≤ krRowSupBudget D K L vlo vhi w A (n + 1) :=
    fun n => krRowSupBudget_nonneg ν H (n+1)
  set M := 2 * T - 1 with hMdef
  have hM : M + 1 = 2 * T := by omega
  have hM1 : 1 ≤ M := by omega
  have hMr : (M : ℝ) + 1 = 2 * T := by exact_mod_cast hM
  refine (kr_sum_split hF M N).trans ?_
  -- medium block: n + 1 ≤ M ≤ 2 w²
  have h1 : ∑ n ∈ Finset.range M, krRowSupBudget D K L vlo vhi w A (n + 1) ≤
      krC₁ D K L * (1 + A) * (2 + 2 * Real.log w) := by
    have h2 : ∑ n ∈ Finset.range M, krRowSupBudget D K L vlo vhi w A (n + 1) ≤
        ∑ n ∈ Finset.range M, krC₁ D K L * (1 + A) * (1 / ((n : ℝ) + 1)) := by
      refine Finset.sum_le_sum fun n hn => ?_
      have hn' : ((n + 1 : ℕ) : ℝ) ≤ 2 * w ^ 2 := by
        have : ((n + 1 : ℕ) : ℝ) ≤ (M : ℝ) := by
          exact_mod_cast Nat.succ_le_of_lt (Finset.mem_range.1 hn)
        linarith
      have hlt : n + 1 < 2 * krT w := by
        have := Finset.mem_range.1 hn
        change n < M at this
        omega
      simp only [krRowSupBudget, if_pos hlt]
      push_cast
      ring_nf
      exact le_rfl
    rw [← Finset.mul_sum] at h2
    have h3 := kr_sum_inv_le_log hM1
    have hlog : Real.log (M : ℝ) ≤ 1 + 2 * Real.log w := by
      have hM0 : (0 : ℝ) < M := by exact_mod_cast hM1
      calc Real.log (M : ℝ) ≤ Real.log (2 * w ^ 2) := Real.log_le_log hM0 (by linarith)
        _ = Real.log 2 + 2 * Real.log w := by
            rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
            push_cast
            ring
        _ ≤ 1 + 2 * Real.log w := by
            have := Real.log_le_sub_one_of_pos (x := 2) (by norm_num)
            linarith
    have h4 : krC₁ D K L * (1 + A) * ∑ n ∈ Finset.range M, 1 / ((n : ℝ) + 1) ≤
        krC₁ D K L * (1 + A) * (2 + 2 * Real.log w) :=
      mul_le_mul_of_nonneg_left (h3.trans (by linarith)) (by positivity)
    linarith
  -- large block: n = M + j, n + 1 = T + j + T
  have h5 : ∑ j ∈ Finset.range (N - M), krRowSupBudget D K L vlo vhi w A (M + j + 1) ≤
      2 * krC₄ D K L / krKappa D vlo vhi * (1 + A) := by
    have h6 : ∀ j, krRowSupBudget D K L vlo vhi w A (M + j + 1) ≤
        krC₄ D K L * (1 + A) / w ^ 2 * Real.sqrt (krLam D vlo vhi w) ^ j := fun j => by
      have hge : ¬ M+j+1 < 2 * krT w := by omega
      have hidx : M+j+1-2*krT w = j := by omega
      simp only [krRowSupBudget, if_neg hge, hidx]
      exact le_rfl
    refine (Finset.sum_le_sum fun j _ => h6 j).trans ?_
    rw [← Finset.mul_sum]
    calc krC₄ D K L * (1 + A) / w ^ 2 *
          ∑ j ∈ Finset.range (N - M), Real.sqrt (krLam D vlo vhi w) ^ j
        ≤ krC₄ D K L * (1 + A) / w ^ 2 * (2 * w ^ 2 / krKappa D vlo vhi) :=
          mul_le_mul_of_nonneg_left (H.geom_tail _) (by positivity)
      _ = 2 * krC₄ D K L / krKappa D vlo vhi * (1 + A) := by
          field_simp
  have h7 : 0 ≤ 2 * krC₄ D K L / krKappa D vlo vhi * (1 + A) * Real.log w := by positivity
  unfold krCG
  nlinarith

theorem sum_expw_krRowSupBudget_le (H : KrBand D θ vlo vhi K L ν f w A a β a')
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ krKappa D vlo vhi / 16) (N : ℕ) :
    ∑ n ∈ Finset.range N, Real.exp (ε * ((n+1 : ℕ) : ℝ) / w^2) *
      krRowSupBudget D K L vlo vhi w A (n+1) ≤
      Real.exp (3*ε) * ((krCG D K L vlo vhi + 4*krC₄ D K L / krKappa D vlo vhi) *
        (1+A) * (1+Real.log w)) := by
  have hw0 := H.hw0
  have hA := H.hA
  have hκ := H.kappa_pos
  have hC4 : 0 ≤ krC₄ D K L := Real.sqrt_nonneg _
  have hlog : 0 ≤ Real.log w := Real.log_nonneg H.hw
  have h := kr_expw_sum_le (F := fun n => krRowSupBudget D K L vlo vhi w A (n+1))
    (fun n => krRowSupBudget_nonneg ν H (n+1)) (2 * krT w - 1) 1
    (fun N => sum_krRowSupBudget_le ν H N)
    (C := krC₄ D K L * (1 + A) / w ^ 2) (r := Real.sqrt (krLam D vlo vhi w))
    (fun j => by
      have hT := H.hT1
      have hge : ¬ 2*krT w-1+j+1 < 2*krT w := by omega
      have hidx : 2*krT w-1+j+1-2*krT w = j := by omega
      simp only [krRowSupBudget, if_neg hge, hidx]
      exact le_rfl)
    (by positivity) H.sqrt_lam_nonneg hε0 hw0 H.two_T_le (H.expw_factor_lt_one hε0 hε) N
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le)
  have hinv := H.inv_expw_factor hε0 hε
  calc krCG D K L vlo vhi * (1 + A) * (1 + Real.log w) +
        krC₄ D K L * (1 + A) / w ^ 2 /
          (1 - Real.sqrt (krLam D vlo vhi w) * Real.exp (ε / w ^ 2))
      = krCG D K L vlo vhi * (1 + A) * (1 + Real.log w) + krC₄ D K L * (1 + A) / w ^ 2 *
          (1 / (1 - Real.sqrt (krLam D vlo vhi w) * Real.exp (ε / w ^ 2))) := by ring
    _ ≤ krCG D K L vlo vhi * (1 + A) * (1 + Real.log w) + krC₄ D K L * (1 + A) / w ^ 2 *
          (4 * w ^ 2 / krKappa D vlo vhi) := by gcongr
    _ = krCG D K L vlo vhi * (1 + A) * (1 + Real.log w) +
          4 * krC₄ D K L / krKappa D vlo vhi * (1 + A) * 1 := by
        field_simp
    _ ≤ krCG D K L vlo vhi * (1 + A) * (1 + Real.log w) +
          4 * krC₄ D K L / krKappa D vlo vhi * (1 + A) * (1 + Real.log w) := by
        gcongr
        linarith
    _ = _ := by ring

theorem krRow_expw_sup_absolute_budget (H : KrBand D θ vlo vhi K L ν f w A a β a')
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ krKappa D vlo vhi / 16) :
    Summable (fun n : ℕ => Real.exp (ε * ((n+1 : ℕ) : ℝ) / w^2) *
      krRowSupBudget D K L vlo vhi w A (n+1)) ∧
    (∑' n : ℕ, Real.exp (ε * ((n+1 : ℕ) : ℝ) / w^2) *
      krRowSupBudget D K L vlo vhi w A (n+1)) ≤
      Real.exp (3*ε) * ((krCG D K L vlo vhi + 4*krC₄ D K L / krKappa D vlo vhi) *
        (1+A) * (1+Real.log w)) := by
  have h0 : ∀ n : ℕ, 0 ≤ Real.exp (ε * ((n+1 : ℕ) : ℝ) / w^2) *
      krRowSupBudget D K L vlo vhi w A (n+1) := fun n =>
    mul_nonneg (Real.exp_pos _).le (krRowSupBudget_nonneg ν H (n+1))
  exact ⟨summable_of_sum_range_le h0 (sum_expw_krRowSupBudget_le ν H hε0 hε),
    Real.tsum_le_of_sum_range_le h0 (sum_expw_krRowSupBudget_le ν H hε0 hε)⟩

end
end PGM
