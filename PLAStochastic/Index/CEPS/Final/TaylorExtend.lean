import PLAStochastic.Index.CEPS.Final.TaylorSeries

/-!
# More coordinates

A box Taylor representation in the first `d₁` coordinates is one in the first `d ≥ d₁`
coordinates, with the coefficients extended by zero (`cepsJetExtend`). Also: the constant
coefficient of a weighted representation is the value at the reference point.
-/

namespace PGM

noncomputable section

open Finset

variable {p₀ : ℕ → ℝ}

/-- Restriction of a multi-index to the first `d₁` coordinates. -/
def cepsJetRestrict {d₁ d : ℕ} (h : d₁ ≤ d) (α : Fin d → ℕ) : Fin d₁ → ℕ :=
  fun i => α (Fin.castLE h i)

/-- Extension of a coefficient family by zero to more coordinates. -/
def cepsJetExtend {M : Type*} [Zero M] {d₁ d : ℕ} (h : d₁ ≤ d) (T : (Fin d₁ → ℕ) → M) :
    (Fin d → ℕ) → M :=
  fun α => if ∀ i : Fin d, d₁ ≤ (i : ℕ) → α i = 0 then T (cepsJetRestrict h α) else 0

theorem cepsJetExtend_zero {M : Type*} [Zero M] {d₁ d : ℕ} (h : d₁ ≤ d)
    (T : (Fin d₁ → ℕ) → M) : cepsJetExtend h T 0 = T 0 := by
  unfold cepsJetExtend
  split_ifs with hc
  · rfl
  · exact absurd (fun _ _ => rfl) hc

theorem iteratedDeriv_cepsJetExtend {d₁ d : ℕ} (h : d₁ ≤ d) (T : (Fin d₁ → ℕ) → ℝ → ℂ)
    (m : ℕ) (α : Fin d → ℕ) :
    iteratedDeriv m (cepsJetExtend h T α) =
      cepsJetExtend h (fun β => iteratedDeriv m (T β)) α := by
  unfold cepsJetExtend
  split_ifs
  · rfl
  · exact funext fun _ => iteratedDeriv_const_zero

theorem prod_fin_castLE {M : Type*} [CommMonoid M] {d₁ d : ℕ} (h : d₁ ≤ d) (f : Fin d → M)
    (hf : ∀ i : Fin d, d₁ ≤ (i : ℕ) → f i = 1) :
    ∏ i : Fin d, f i = ∏ i : Fin d₁, f (Fin.castLE h i) := by
  classical
  rw [show (∏ i : Fin d₁, f (Fin.castLE h i)) = ∏ i ∈ univ.map (Fin.castLEEmb h), f i from
    (prod_map univ (Fin.castLEEmb h) f).symm]
  refine (prod_subset (subset_univ _) fun i _ hi => hf i ?_).symm
  by_contra hlt
  push Not at hlt
  exact hi (mem_map.mpr ⟨⟨i, hlt⟩, mem_univ _, Fin.ext rfl⟩)

theorem sum_fin_castLE_le {d₁ d : ℕ} (h : d₁ ≤ d) (f : Fin d → ℝ) (hf : ∀ i, 0 ≤ f i) :
    ∑ i : Fin d₁, f (Fin.castLE h i) ≤ ∑ i : Fin d, f i := by
  classical
  rw [show (∑ i : Fin d₁, f (Fin.castLE h i)) = ∑ i ∈ univ.map (Fin.castLEEmb h), f i from
    (sum_map univ (Fin.castLEEmb h) f).symm]
  exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun i _ _ => hf i

/-- The extended box sum is the original one. -/
theorem sum_box_extend {M : Type*} [AddCommMonoid M] {d₁ d N : ℕ} (h : d₁ ≤ d)
    (G : (Fin d₁ → ℕ) → ℝ → M) (y : Fin d → ℝ) :
    ∑ α ∈ cepsTaylorBox d N, (if ∀ i : Fin d, d₁ ≤ (i : ℕ) → α i = 0 then
        G (cepsJetRestrict h α) (cepsMonomial y α) else 0) =
      ∑ β ∈ cepsTaylorBox d₁ N, G β (cepsMonomial (fun i => y (Fin.castLE h i)) β) := by
  classical
  rw [← sum_filter]
  refine sum_nbij' (cepsJetRestrict h)
    (fun β i => if hi : (i : ℕ) < d₁ then β ⟨i, hi⟩ else 0) ?_ ?_ ?_ ?_ ?_
  · intro α hα
    rw [mem_filter, mem_cepsTaylorBox] at hα
    exact mem_cepsTaylorBox.mpr fun i => hα.1 _
  · intro β hβ
    rw [mem_cepsTaylorBox] at hβ
    rw [mem_filter, mem_cepsTaylorBox]
    refine ⟨fun i => ?_, fun i hi => ?_⟩
    · split_ifs
      · exact hβ _
      · exact Nat.zero_le _
    · simp [Nat.not_lt.mpr hi]
  · intro α hα
    rw [mem_filter] at hα
    funext i
    by_cases hi : (i : ℕ) < d₁
    · simp only [hi, dite_true, cepsJetRestrict]
      rfl
    · simp only [hi, dite_false]
      exact (hα.2 i (Nat.not_lt.mp hi)).symm
  · intro β _
    funext i
    simp [cepsJetRestrict]
  · intro α hα
    rw [mem_filter] at hα
    congr 1
    unfold cepsMonomial
    exact prod_fin_castLE h _ fun i hi => by rw [hα.2 i hi, pow_zero]

theorem CepsJetScal.extend {d₁ d : ℕ} (h : d₁ ≤ d) {F : (ℕ → ℝ) → ℂ}
    {T : (Fin d₁ → ℕ) → ℂ} (hF : CepsJetScal p₀ F T) : CepsJetScal p₀ F (cepsJetExtend h T) := by
  intro N
  obtain ⟨ρ, K, hρ, H⟩ := hF N
  refine ⟨ρ, |K|, hρ, fun p hp => ?_⟩
  have hsum : ∑ α ∈ cepsTaylorBox d N,
      cepsJetExtend h T α * (cepsMonomial (fun i : Fin d => p i - p₀ i) α : ℂ) =
      ∑ β ∈ cepsTaylorBox d₁ N, T β * (cepsMonomial (fun i : Fin d₁ => p i - p₀ i) β : ℂ) := by
    have e1 : ∑ α ∈ cepsTaylorBox d N,
        cepsJetExtend h T α * (cepsMonomial (fun i : Fin d => p i - p₀ i) α : ℂ) =
        ∑ α ∈ cepsTaylorBox d N, (if ∀ i : Fin d, d₁ ≤ (i : ℕ) → α i = 0 then
          (fun β m => T β * (m : ℂ)) (cepsJetRestrict h α)
            (cepsMonomial (fun i : Fin d => p i - p₀ i) α) else 0) :=
      sum_congr rfl fun α _ => by unfold cepsJetExtend; split_ifs <;> simp
    rw [e1]
    exact sum_box_extend h (fun β m => T β * (m : ℂ)) (fun i : Fin d => p i - p₀ i)
  rw [hsum]
  have hs := sum_fin_castLE_le h (fun i : Fin d => |p i - p₀ i|) fun _ => abs_nonneg _
  refine (H p fun i => hp (Fin.castLE h i)).trans ?_
  exact mul_le_mul (le_abs_self K) (pow_le_pow_left₀ (sum_nonneg fun _ _ => abs_nonneg _) hs _)
    (pow_nonneg (sum_nonneg fun _ _ => abs_nonneg _) _) (abs_nonneg _)

theorem CepsJetDecay.extend {d₁ d : ℕ} (h : d₁ ≤ d) {F : ℝ → (ℕ → ℝ) → ℂ}
    {T : (Fin d₁ → ℕ) → ℝ → ℂ} (hF : CepsJetDecay p₀ F T) :
    CepsJetDecay p₀ F (cepsJetExtend h T) := by
  refine ⟨fun α => ?_, fun N => ?_⟩
  · unfold cepsJetExtend
    split_ifs
    · exact hF.1 _
    · exact ⟨0, 1, one_pos, 0, fun u => by simp⟩
  · obtain ⟨ρ, K, c, hρ, hc, e, H⟩ := hF.2 N
    refine ⟨ρ, |K|, c, hρ, hc, e, fun u p hp => ?_⟩
    have hsum : ∑ α ∈ cepsTaylorBox d N,
        cepsJetExtend h T α u * (cepsMonomial (fun i : Fin d => p i - p₀ i) α : ℂ) =
        ∑ β ∈ cepsTaylorBox d₁ N,
          T β u * (cepsMonomial (fun i : Fin d₁ => p i - p₀ i) β : ℂ) := by
      have e1 : ∑ α ∈ cepsTaylorBox d N,
          cepsJetExtend h T α u * (cepsMonomial (fun i : Fin d => p i - p₀ i) α : ℂ) =
          ∑ α ∈ cepsTaylorBox d N, (if ∀ i : Fin d, d₁ ≤ (i : ℕ) → α i = 0 then
            (fun β m => T β u * (m : ℂ)) (cepsJetRestrict h α)
              (cepsMonomial (fun i : Fin d => p i - p₀ i) α) else 0) :=
        sum_congr rfl fun α _ => by unfold cepsJetExtend; split_ifs <;> simp
      rw [e1]
      exact sum_box_extend h (fun β m => T β u * (m : ℂ)) (fun i : Fin d => p i - p₀ i)
    rw [hsum]
    have hs := sum_fin_castLE_le h (fun i : Fin d => |p i - p₀ i|) fun _ => abs_nonneg _
    have hw := (cepsStretchedWeight_pos c e u).le
    refine (H u p fun i => hp (Fin.castLE h i)).trans ?_
    exact mul_le_mul (mul_le_mul_of_nonneg_right (le_abs_self K) hw)
      (pow_le_pow_left₀ (sum_nonneg fun _ _ => abs_nonneg _) hs _)
      (pow_nonneg (sum_nonneg fun _ _ => abs_nonneg _) _) (mul_nonneg (abs_nonneg _) hw)

/-- The constant coefficient of a weighted representation is the value at the reference
point. -/
theorem CepsJetDecay.coeff_zero {d : ℕ} {F : ℝ → (ℕ → ℝ) → ℂ} {T : (Fin d → ℕ) → ℝ → ℂ}
    (hF : CepsJetDecay p₀ F T) (u : ℝ) : T 0 u = F u p₀ := by
  obtain ⟨ρ, K, c, hρ, hc, e, H⟩ := hF.2 0
  have h0 := H u p₀ fun i => by simpa using hρ.le
  have hpoly := cepsJet_boxPoly_at_ref (p₀ := p₀) (d := d) 0 (fun α => T α u)
  simp only [smul_eq_mul] at hpoly
  simp_rw [mul_comm (T _ u)] at h0
  rw [hpoly] at h0
  simp only [sub_self, abs_zero, sum_const_zero, zero_add, pow_one, mul_zero] at h0
  exact (sub_eq_zero.mp (norm_le_zero_iff.mp h0)).symm

end

end PGM
