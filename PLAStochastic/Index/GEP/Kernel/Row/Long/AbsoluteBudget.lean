import PLAStochastic.Index.GEP.Kernel.Row.Long.TimeWeightedGreen

/-!
# Absolute budgets for all long rows

These are budgets for each actual time index before summation, so arbitrary
signed rewards depending jointly on left and right lengths can use them.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

def krRowVarBudget (D K L vlo vhi w A : ℝ) (n : ℕ) : ℝ :=
  kBVClassVarConst D vlo vhi * Real.sqrt (krC₂ D K L) * (1 + A) *
    krVarTerm D vlo vhi w n

def krRowRemBudget (D K L vlo vhi A : ℝ) (n : ℕ) : ℝ :=
  Real.sqrt (2 * D) * (kBVClassRemConst D vlo vhi * Real.sqrt (3 * krC₂ D K L) *
    (1 + A) * kBVClassRho D vlo vhi ^ (n / 3 - 1))

variable {D θ vlo vhi K L w A a β a' : ℝ} (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ}

theorem krRow_expw_absolute_budgets
    (H : KrBand D θ vlo vhi K L ν f w A a β a')
    {P : ℕ} (hP : 12 ≤ P) {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ krEps D vlo vhi) :
    Summable (fun i : ℕ => Real.exp (ε * ((P + 1 + i : ℕ) : ℝ) / w ^ 2) *
      krRowVarBudget D K L vlo vhi w A (P + 1 + i)) ∧
    (∑' i : ℕ, Real.exp (ε * ((P + 1 + i : ℕ) : ℝ) / w ^ 2) *
      krRowVarBudget D K L vlo vhi w A (P + 1 + i)) ≤
      2 * Real.exp (3 * ε) * krCV D K L vlo vhi * (1 + A) *
        (Real.sqrt w / krFourthRoot P + 1) ∧
    Summable (fun i : ℕ => Real.exp (ε * ((P + 1 + i : ℕ) : ℝ) / w ^ 2) *
      krRowRemBudget D K L vlo vhi A (P + 1 + i)) ∧
    (∑' i : ℕ, Real.exp (ε * ((P + 1 + i : ℕ) : ℝ) / w ^ 2) *
      krRowRemBudget D K L vlo vhi A (P + 1 + i)) ≤
      2 * Real.exp (5 * ε) * krCR D K L vlo vhi * (1 + A) *
        ((1 + kBVClassRho D vlo vhi) / 2) ^ (P / 3 - 1) := by
  have hw0 := H.hw0
  have hw := H.hw
  have hA := H.hA
  have hcc := H.classConsts
  set ω : ℕ → ℝ := fun i => Real.exp (ε * ((P + 1 + i : ℕ) : ℝ) / w ^ 2) with hω_def
  have hω0 : ∀ i, 0 ≤ ω i := fun i => (Real.exp_pos _).le
  have hV0 : ∀ i, 0 ≤ ω i * (kBVClassVarConst D vlo vhi * Real.sqrt (krC₂ D K L) * (1 + A) *
      krVarTerm D vlo vhi w (P + 1 + i)) := fun i =>
    mul_nonneg (hω0 i) (mul_nonneg (mul_nonneg (mul_nonneg hcc.2.2.2.2.le (Real.sqrt_nonneg _))
      (by linarith)) (krVarTerm_nonneg hw0 _))
  -- the variation sum
  have hrate := hcc.2.2.1
  have hrate' : ε ≤ kBVClassRate D vlo vhi / 2 := by
    have := hε.trans H.krEps_le_kappa
    unfold kBVClassRate
    unfold krKappa at this
    linarith
  have hρε : 0 < kBVClassRate D vlo vhi - ε := by linarith
  have hVsum : ∀ M : ℕ, ∑ i ∈ Finset.range M, ω i * (kBVClassVarConst D vlo vhi * Real.sqrt (krC₂ D K L) *
      (1 + A) * krVarTerm D vlo vhi w (P + 1 + i)) ≤
      2 * Real.exp (3 * ε) * krCV D K L vlo vhi * (1 + A) * (Real.sqrt w / krFourthRoot P + 1) := by
    intro M
    have hterm : ∀ i ∈ Finset.range M, ω i * (kBVClassVarConst D vlo vhi * Real.sqrt (krC₂ D K L) *
        (1 + A) * krVarTerm D vlo vhi w (P + 1 + i)) ≤
        (kBVClassVarConst D vlo vhi * Real.sqrt (krC₂ D K L) * (1 + A) * Real.exp (3 * ε)) *
          krVarTermGen (kBVClassRate D vlo vhi - ε) w (P + 1 + i) := fun i _ => by
      have := H.expw_varTerm hε0 (kBVClassRate D vlo vhi) (P + 1 + i)
      have e : ω i * (kBVClassVarConst D vlo vhi * Real.sqrt (krC₂ D K L) * (1 + A) *
          krVarTerm D vlo vhi w (P + 1 + i)) =
          (kBVClassVarConst D vlo vhi * Real.sqrt (krC₂ D K L) * (1 + A)) *
            (Real.exp (ε * ((P + 1 + i : ℕ) : ℝ) / w ^ 2) *
              krVarTermGen (kBVClassRate D vlo vhi) w (P + 1 + i)) := by
        simp only [hω_def, krVarTerm]
        ring
      rw [e, mul_assoc _ (Real.exp (3 * ε))]
      exact mul_le_mul_of_nonneg_left this
        (mul_nonneg (mul_nonneg hcc.2.2.2.2.le (Real.sqrt_nonneg _)) (by linarith))
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.mul_sum]
    have hs := kr_sum_krVarTermGen_le hρε hw
      (by linarith [H.rate_le_one, one_le_pow₀ (n := 2) hw]) (by omega : 1 ≤ P) M
    have hq0 : 0 ≤ Real.sqrt w / krFourthRoot P :=
      div_nonneg (Real.sqrt_nonneg _) (krFourthRoot_nonneg _)
    have hinv : 2 * Real.sqrt 6 / (kBVClassRate D vlo vhi - ε) ≤
        4 * Real.sqrt 6 / kBVClassRate D vlo vhi := by
      rw [div_le_div_iff₀ hρε hrate]
      nlinarith [Real.sqrt_nonneg 6]
    have hs' : 16 * Real.sqrt w / krFourthRoot P + 2 * Real.sqrt 6 / (kBVClassRate D vlo vhi - ε) ≤
        2 * ((16 + 2 * Real.sqrt 6 / kBVClassRate D vlo vhi) * (Real.sqrt w / krFourthRoot P + 1)) := by
      have h2 : 0 ≤ 2 * Real.sqrt 6 / kBVClassRate D vlo vhi := by positivity
      have hcx := mul_nonneg h2 hq0
      have e1 : 16 * Real.sqrt w / krFourthRoot P = 16 * (Real.sqrt w / krFourthRoot P) := by ring
      have e2 : 2 * ((16 + 2 * Real.sqrt 6 / kBVClassRate D vlo vhi) *
          (Real.sqrt w / krFourthRoot P + 1)) =
          32 * (Real.sqrt w / krFourthRoot P) + 32 +
            2 * (2 * Real.sqrt 6 / kBVClassRate D vlo vhi * (Real.sqrt w / krFourthRoot P)) +
            2 * (2 * Real.sqrt 6 / kBVClassRate D vlo vhi) := by ring
      have e3 : 4 * Real.sqrt 6 / kBVClassRate D vlo vhi =
          2 * (2 * Real.sqrt 6 / kBVClassRate D vlo vhi) := by ring
      rw [e1, e2]
      rw [e3] at hinv
      linarith
    calc kBVClassVarConst D vlo vhi * Real.sqrt (krC₂ D K L) * (1 + A) * Real.exp (3 * ε) *
          ∑ i ∈ Finset.range M, krVarTermGen (kBVClassRate D vlo vhi - ε) w (P + 1 + i)
        ≤ kBVClassVarConst D vlo vhi * Real.sqrt (krC₂ D K L) * (1 + A) * Real.exp (3 * ε) *
          (2 * ((16 + 2 * Real.sqrt 6 / kBVClassRate D vlo vhi) *
            (Real.sqrt w / krFourthRoot P + 1))) :=
          mul_le_mul_of_nonneg_left (hs.trans hs')
            (mul_nonneg (mul_nonneg (mul_nonneg hcc.2.2.2.2.le (Real.sqrt_nonneg _))
              (by linarith)) (Real.exp_pos _).le)
      _ = _ := by unfold krCV; ring
  -- the remainder sum
  set ρ' := kBVClassRho D vlo vhi * Real.exp (3 * ε / w ^ 2) with hρ'_def
  have hρ'0 : 0 ≤ ρ' := mul_nonneg hcc.1 (Real.exp_pos _).le
  have hρ'le := H.rho_expw_le hε0 hε
  have hρ'1 : ρ' < 1 := by linarith [hcc.2.1]
  have hRsum : ∀ M : ℕ, ∑ i ∈ Finset.range M, ω i * (Real.sqrt (2 * D) * (kBVClassRemConst D vlo vhi *
      Real.sqrt (3 * krC₂ D K L) * (1 + A) * kBVClassRho D vlo vhi ^ ((P + 1 + i) / 3 - 1))) ≤
      2 * Real.exp (5 * ε) * krCR D K L vlo vhi * (1 + A) *
        ((1 + kBVClassRho D vlo vhi) / 2) ^ (P / 3 - 1) := by
    intro M
    set Cr := Real.sqrt (2 * D) * kBVClassRemConst D vlo vhi * Real.sqrt (3 * krC₂ D K L) * (1 + A)
      with hCr_def
    have hCr0 : 0 ≤ Cr :=
      mul_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hcc.2.2.2.1.le)
        (Real.sqrt_nonneg _)) (by linarith)
    have hterm : ∀ i ∈ Finset.range M, ω i * (Real.sqrt (2 * D) * (kBVClassRemConst D vlo vhi *
        Real.sqrt (3 * krC₂ D K L) * (1 + A) * kBVClassRho D vlo vhi ^ ((P + 1 + i) / 3 - 1))) ≤
        (Cr * Real.exp (5 * ε)) * ρ' ^ ((P + 1 + i) / 3 - 1) := fun i _ => by
      have := kr_expw_rho (ε := ε) (w := w) hε0 hw hcc.1 (P + 1 + i)
      have e : ω i * (Real.sqrt (2 * D) * (kBVClassRemConst D vlo vhi *
          Real.sqrt (3 * krC₂ D K L) * (1 + A) * kBVClassRho D vlo vhi ^ ((P + 1 + i) / 3 - 1))) =
          Cr * (Real.exp (ε * ((P + 1 + i : ℕ) : ℝ) / w ^ 2) *
            kBVClassRho D vlo vhi ^ ((P + 1 + i) / 3 - 1)) := by
        simp only [hω_def, hCr_def]
        ring
      rw [e]
      refine (mul_le_mul_of_nonneg_left this hCr0).trans (le_of_eq ?_)
      rw [hρ'_def]
      ring
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.mul_sum]
    have hsum := kr_sum_rho_pow_le hρ'0 hρ'1 (by omega : 3 ≤ P) M
    have hpow : ρ' ^ (P / 3 - 1) ≤ ((1 + kBVClassRho D vlo vhi) / 2) ^ (P / 3 - 1) :=
      pow_le_pow_left₀ hρ'0 hρ'le _
    have hhalf : 0 < (1 - kBVClassRho D vlo vhi) / 2 := by linarith [hcc.2.1]
    have hinv : 1 / (1 - ρ') ≤ 1 / ((1 - kBVClassRho D vlo vhi) / 2) :=
      one_div_le_one_div_of_le hhalf (by linarith)
    have hgeom : 3 * ρ' ^ (P / 3 - 1) / (1 - ρ') ≤
        3 * ((1 + kBVClassRho D vlo vhi) / 2) ^ (P / 3 - 1) / ((1 - kBVClassRho D vlo vhi) / 2) := by
      have hρ1' : 0 ≤ (1 + kBVClassRho D vlo vhi) / 2 := by linarith [hcc.1]
      exact div_le_div₀ (mul_nonneg (by norm_num) (pow_nonneg hρ1' _)) (by gcongr) hhalf
        (by linarith)
    calc Cr * Real.exp (5 * ε) * ∑ i ∈ Finset.range M, ρ' ^ ((P + 1 + i) / 3 - 1)
        ≤ Cr * Real.exp (5 * ε) *
          (3 * ((1 + kBVClassRho D vlo vhi) / 2) ^ (P / 3 - 1) / ((1 - kBVClassRho D vlo vhi) / 2)) :=
          mul_le_mul_of_nonneg_left (hsum.trans hgeom) (mul_nonneg hCr0 (Real.exp_pos _).le)
      _ = _ := by
          simp only [hCr_def]
          unfold krCR
          field_simp
  let V : ℕ → ℝ := fun i => ω i * (kBVClassVarConst D vlo vhi * Real.sqrt (krC₂ D K L) *
    (1 + A) * krVarTerm D vlo vhi w (P + 1 + i))
  let Rc : ℕ → ℝ := fun i => ω i * (Real.sqrt (2 * D) * (kBVClassRemConst D vlo vhi *
    Real.sqrt (3 * krC₂ D K L) * (1 + A) *
      kBVClassRho D vlo vhi ^ ((P + 1 + i) / 3 - 1)))
  have hRc0 : ∀ i, 0 ≤ Rc i := fun i =>
    mul_nonneg (hω0 i) (mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (mul_nonneg (mul_nonneg hcc.2.2.2.1.le (Real.sqrt_nonneg _))
        (by linarith)) (pow_nonneg hcc.1 _)))
  have hVs : Summable V := summable_of_sum_range_le hV0 hVsum
  have hRcs : Summable Rc := summable_of_sum_range_le hRc0 hRsum
  exact ⟨hVs, Real.tsum_le_of_sum_range_le hV0 hVsum,
    hRcs, Real.tsum_le_of_sum_range_le hRc0 hRsum⟩

end
end PGM
