import PLAStochastic.Index.CEPS.Final.TaylorBox

/-!
# Box Taylor representations in finitely many jet coordinates

Around a reference vector `p₀ : ℕ → ℝ` and in the first `d` coordinates, with displacement
`yᵢ = pᵢ - p₀ᵢ` and size `|y| = ∑ᵢ |yᵢ|`:

* `CepsJetScal p₀ F T`: for every `N`, `‖F p - ∑_{α ∈ box N} T α yᵅ‖ ≤ K |y|^{N+1}` on a small box;
* `CepsJetDecay p₀ F T`: a frequency-dependent version with stretched-exponential weights in
  `u`, `‖T α u‖ ≤ K (1+|u|)ᵉ e^{-c√|u|}` and remainders `K (1+|u|)ᵉ e^{-c√|u|} |y|^{N+1}`,
  the constants depending on `α` and `N` (the shape of `CepsT3`).

Closure under sums, constant multiples, products (`cepsBoxMul`), powers, polynomial
multipliers in `u`, and decaying functions of `u` alone.
-/

namespace PGM

noncomputable section

open Finset

section Defs

variable (p₀ : ℕ → ℝ) {d : ℕ}

/-- Order-`N` box Taylor approximation of a scalar function around `p₀`. -/
def CepsJetScalAt (N : ℕ) (F : (ℕ → ℝ) → ℂ) (T : (Fin d → ℕ) → ℂ) : Prop :=
  ∃ ρ K : ℝ, 0 < ρ ∧ ∀ p : ℕ → ℝ, (∀ i : Fin d, |p i - p₀ i| ≤ ρ) →
    ‖F p - ∑ α ∈ cepsTaylorBox d N,
        T α * (cepsMonomial (fun i : Fin d => p i - p₀ i) α : ℂ)‖ ≤
      K * (∑ i : Fin d, |p i - p₀ i|) ^ (N + 1)

/-- Box Taylor representation of a scalar function around `p₀` (all orders, fixed
coefficients). -/
def CepsJetScal (F : (ℕ → ℝ) → ℂ) (T : (Fin d → ℕ) → ℂ) : Prop :=
  ∀ N : ℕ, CepsJetScalAt p₀ N F T

/-- Order-`N` box Taylor approximation with stretched-exponential weights in `u`. -/
def CepsJetDecayAt (N : ℕ) (F : ℝ → (ℕ → ℝ) → ℂ) (T : (Fin d → ℕ) → ℝ → ℂ) : Prop :=
  ∃ ρ K c : ℝ, 0 < ρ ∧ 0 < c ∧ ∃ e : ℕ, ∀ (u : ℝ) (p : ℕ → ℝ),
    (∀ i : Fin d, |p i - p₀ i| ≤ ρ) →
      ‖F u p - ∑ α ∈ cepsTaylorBox d N,
          T α u * (cepsMonomial (fun i : Fin d => p i - p₀ i) α : ℂ)‖ ≤
        K * cepsStretchedWeight c e u * (∑ i : Fin d, |p i - p₀ i|) ^ (N + 1)

end Defs

/-- Stretched-exponential bounds of a coefficient family. -/
def CepsJetDecayCoeff {d : ℕ} (T : (Fin d → ℕ) → ℝ → ℂ) : Prop :=
  ∀ α, ∃ K c : ℝ, 0 < c ∧ ∃ e : ℕ, ∀ u, ‖T α u‖ ≤ K * cepsStretchedWeight c e u

/-- Box Taylor representation with stretched-exponential weights (the shape of `CepsT3`). -/
def CepsJetDecay (p₀ : ℕ → ℝ) {d : ℕ} (F : ℝ → (ℕ → ℝ) → ℂ) (T : (Fin d → ℕ) → ℝ → ℂ) :
    Prop :=
  CepsJetDecayCoeff T ∧ ∀ N : ℕ, CepsJetDecayAt p₀ N F T

variable {p₀ : ℕ → ℝ} {d : ℕ}

/-! ## The small box -/

theorem cepsJet_small_box_pos {ρ : ℝ} (hρ : 0 < ρ) : 0 < min ρ (1 / ((d : ℝ) + 1)) :=
  lt_min hρ (by positivity)

theorem cepsJet_small_box {ρ : ℝ} {p : ℕ → ℝ}
    (h : ∀ i : Fin d, |p i - p₀ i| ≤ min ρ (1 / ((d : ℝ) + 1))) :
    (∀ i : Fin d, |p i - p₀ i| ≤ ρ) ∧ (∀ i : Fin d, |p i - p₀ i| ≤ 1) ∧
      (∑ i : Fin d, |p i - p₀ i|) ≤ 1 := by
  have hd : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  have hle1 : 1 / ((d : ℝ) + 1) ≤ 1 := by
    rw [div_le_one hd]; linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  refine ⟨fun i => (h i).trans (min_le_left _ _),
    fun i => ((h i).trans (min_le_right _ _)).trans hle1, ?_⟩
  calc (∑ i : Fin d, |p i - p₀ i|) ≤ ∑ _i : Fin d, 1 / ((d : ℝ) + 1) :=
        sum_le_sum fun i _ => (h i).trans (min_le_right _ _)
    _ = (d : ℝ) / ((d : ℝ) + 1) := by simp [div_eq_mul_inv]
    _ ≤ 1 := by rw [div_le_one hd]; linarith

theorem cepsJet_size_nonneg (p : ℕ → ℝ) : 0 ≤ ∑ i : Fin d, |p i - p₀ i| :=
  sum_nonneg fun _ _ => abs_nonneg _

theorem cepsJet_abs_le_size (p : ℕ → ℝ) (i : Fin d) :
    |p i - p₀ i| ≤ ∑ j : Fin d, |p j - p₀ j| :=
  single_le_sum (f := fun j : Fin d => |p j - p₀ j|) (fun _ _ => abs_nonneg _) (mem_univ i)

theorem cepsJet_size_le_of_box {ρ : ℝ} {p : ℕ → ℝ} (h : ∀ i : Fin d, |p i - p₀ i| ≤ ρ) :
    (∑ i : Fin d, |p i - p₀ i|) ≤ d * ρ := by
  calc (∑ i : Fin d, |p i - p₀ i|) ≤ ∑ _i : Fin d, ρ := sum_le_sum fun i _ => h i
    _ = d * ρ := by simp

theorem norm_cepsMonomial_le_one {y : Fin d → ℝ} (hy : ∀ i, |y i| ≤ 1) (α : Fin d → ℕ) :
    ‖(cepsMonomial y α : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_cepsMonomial_le_one hy α

theorem cepsTaylorBox_zero (d : ℕ) : cepsTaylorBox d 0 = {0} := by
  ext α
  rw [mem_cepsTaylorBox, mem_singleton]
  exact ⟨fun h => funext fun i => Nat.le_zero.mp (h i), fun h i => by simp [h]⟩

/-- The box polynomial at the reference point is the constant coefficient. -/
theorem cepsJet_boxPoly_at_ref {M : Type*} [AddCommMonoid M] [Module ℂ M] (N : ℕ)
    (T : (Fin d → ℕ) → M) :
    ∑ α ∈ cepsTaylorBox d N, (cepsMonomial (fun i : Fin d => p₀ i - p₀ i) α : ℂ) • T α =
      T 0 := by
  classical
  have h0 : (fun i : Fin d => p₀ i - p₀ i) = 0 := funext fun i => sub_self _
  rw [h0]
  simp_rw [cepsMonomial_zero_arg]
  rw [sum_eq_single 0 (fun b _ hb => by simp [hb]) (fun h => absurd (zero_mem_cepsTaylorBox d N) h)]
  simp

/-! ## Scalar representations at a fixed order -/

namespace CepsJetScalAt

variable {N : ℕ} {F G : (ℕ → ℝ) → ℂ} {T S : (Fin d → ℕ) → ℂ}

theorem congr_coeff (h : CepsJetScalAt p₀ N F T) {T' : (Fin d → ℕ) → ℂ}
    (hT : ∀ α ∈ cepsTaylorBox d N, T α = T' α) : CepsJetScalAt p₀ N F T' := by
  obtain ⟨ρ, K, hρ, H⟩ := h
  refine ⟨ρ, K, hρ, fun p hp => ?_⟩
  have e : ∑ α ∈ cepsTaylorBox d N, T α * (cepsMonomial (fun i : Fin d => p i - p₀ i) α : ℂ) =
      ∑ α ∈ cepsTaylorBox d N, T' α * (cepsMonomial (fun i : Fin d => p i - p₀ i) α : ℂ) :=
    sum_congr rfl fun α hα => by rw [hT α hα]
  rw [← e]
  exact H p hp

theorem of_close (h : CepsJetScalAt p₀ N G T)
    (hc : ∃ ρ K : ℝ, 0 < ρ ∧ ∀ p : ℕ → ℝ, (∀ i : Fin d, |p i - p₀ i| ≤ ρ) →
      ‖F p - G p‖ ≤ K * (∑ i : Fin d, |p i - p₀ i|) ^ (N + 1)) :
    CepsJetScalAt p₀ N F T := by
  obtain ⟨ρ₁, K₁, hρ₁, H₁⟩ := h
  obtain ⟨ρ₂, K₂, hρ₂, H₂⟩ := hc
  refine ⟨min ρ₁ ρ₂, K₂ + K₁, lt_min hρ₁ hρ₂, fun p hp => ?_⟩
  have h1 := H₁ p fun i => (hp i).trans (min_le_left _ _)
  have h2 := H₂ p fun i => (hp i).trans (min_le_right _ _)
  calc _ = ‖(F p - G p) + (G p - ∑ α ∈ cepsTaylorBox d N,
        T α * (cepsMonomial (fun i : Fin d => p i - p₀ i) α : ℂ))‖ := by ring_nf
    _ ≤ _ := norm_add_le _ _
    _ ≤ _ := add_le_add h2 h1
    _ = _ := by ring

theorem congr_fun (h : CepsJetScalAt p₀ N G T)
    (hc : ∃ ρ : ℝ, 0 < ρ ∧ ∀ p : ℕ → ℝ, (∀ i : Fin d, |p i - p₀ i| ≤ ρ) → F p = G p) :
    CepsJetScalAt p₀ N F T := by
  obtain ⟨ρ, hρ, H⟩ := hc
  exact h.of_close ⟨ρ, 0, hρ, fun p hp => by rw [H p hp, sub_self, norm_zero, zero_mul]⟩

theorem add (hF : CepsJetScalAt p₀ N F T) (hG : CepsJetScalAt p₀ N G S) :
    CepsJetScalAt p₀ N (fun p => F p + G p) (fun α => T α + S α) := by
  obtain ⟨ρ₁, K₁, hρ₁, H₁⟩ := hF
  obtain ⟨ρ₂, K₂, hρ₂, H₂⟩ := hG
  refine ⟨min ρ₁ ρ₂, K₁ + K₂, lt_min hρ₁ hρ₂, fun p hp => ?_⟩
  have h1 := H₁ p fun i => (hp i).trans (min_le_left _ _)
  have h2 := H₂ p fun i => (hp i).trans (min_le_right _ _)
  simp_rw [add_mul, sum_add_distrib]
  calc _ = ‖(F p - ∑ α ∈ cepsTaylorBox d N,
        T α * (cepsMonomial (fun i : Fin d => p i - p₀ i) α : ℂ)) +
      (G p - ∑ α ∈ cepsTaylorBox d N,
        S α * (cepsMonomial (fun i : Fin d => p i - p₀ i) α : ℂ))‖ := by ring_nf
    _ ≤ _ := norm_add_le _ _
    _ ≤ _ := add_le_add h1 h2
    _ = _ := by ring

theorem const_mul (hF : CepsJetScalAt p₀ N F T) (a : ℂ) :
    CepsJetScalAt p₀ N (fun p => a * F p) (fun α => a * T α) := by
  obtain ⟨ρ, K, hρ, H⟩ := hF
  refine ⟨ρ, ‖a‖ * K, hρ, fun p hp => ?_⟩
  have e : a * F p - ∑ α ∈ cepsTaylorBox d N,
      a * T α * (cepsMonomial (fun i : Fin d => p i - p₀ i) α : ℂ) =
      a * (F p - ∑ α ∈ cepsTaylorBox d N,
        T α * (cepsMonomial (fun i : Fin d => p i - p₀ i) α : ℂ)) := by
    rw [mul_sub, mul_sum]
    exact congrArg _ (sum_congr rfl fun _ _ => by ring)
  rw [e, norm_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (H p hp) (norm_nonneg _)

theorem zero : CepsJetScalAt p₀ N (fun _ => (0 : ℂ)) (fun _ : Fin d → ℕ => (0 : ℂ)) := by
  refine ⟨1, 0, one_pos, fun p _ => ?_⟩
  simp

theorem sum {ι : Type*} (s : Finset ι) {F : ι → (ℕ → ℝ) → ℂ} {T : ι → (Fin d → ℕ) → ℂ}
    (h : ∀ i ∈ s, CepsJetScalAt p₀ N (F i) (T i)) :
    CepsJetScalAt p₀ N (fun p => ∑ i ∈ s, F i p) (fun α => ∑ i ∈ s, T i α) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zero : CepsJetScalAt p₀ N (fun _ => (0 : ℂ)) (fun _ : Fin d → ℕ => (0 : ℂ)))
  | insert a s ha ih =>
    simp_rw [sum_insert ha]
    exact (h a (mem_insert_self a s)).add (ih fun i hi => h i (mem_insert_of_mem hi))

theorem const (a : ℂ) :
    CepsJetScalAt p₀ N (fun _ => a) (fun α : Fin d → ℕ => if α = 0 then a else 0) := by
  classical
  refine ⟨1, 0, one_pos, fun p _ => ?_⟩
  rw [sum_eq_single 0 (fun b _ hb => by simp [hb])
    (fun h => absurd (zero_mem_cepsTaylorBox d N) h)]
  simp [cepsMonomial_zero_index]

theorem mul (hF : CepsJetScalAt p₀ N F T) (hG : CepsJetScalAt p₀ N G S) :
    CepsJetScalAt p₀ N (fun p => F p * G p) (cepsBoxMul T S) := by
  obtain ⟨ρ₁, K₁, hρ₁, H₁⟩ := hF
  obtain ⟨ρ₂, K₂, hρ₂, H₂⟩ := hG
  set A := ∑ α ∈ cepsTaylorBox d N, ‖T α‖
  set B := ∑ β ∈ cepsTaylorBox d N, ‖S β‖
  have hA : 0 ≤ A := sum_nonneg fun _ _ => norm_nonneg _
  have hB : 0 ≤ B := sum_nonneg fun _ _ => norm_nonneg _
  refine ⟨min (min ρ₁ ρ₂) (1 / ((d : ℝ) + 1)), |K₁| * (B + |K₂|) + A * |K₂| + A * B,
    cepsJet_small_box_pos (lt_min hρ₁ hρ₂), fun p hp => ?_⟩
  obtain ⟨hp', hy, hs⟩ := cepsJet_small_box hp
  set s := ∑ i : Fin d, |p i - p₀ i|
  have hs0 : 0 ≤ s := cepsJet_size_nonneg p
  have hsN : s ^ (N + 1) ≤ 1 := pow_le_one₀ hs0 hs
  have h1 := (H₁ p fun i => (hp' i).trans (min_le_left _ _)).trans
    (mul_le_mul_of_nonneg_right (le_abs_self K₁) (pow_nonneg hs0 _))
  have h2 := (H₂ p fun i => (hp' i).trans (min_le_right _ _)).trans
    (mul_le_mul_of_nonneg_right (le_abs_self K₂) (pow_nonneg hs0 _))
  have h2' : ‖G p - ∑ β ∈ cepsTaylorBox d N,
      S β * (cepsMonomial (fun i : Fin d => p i - p₀ i) β : ℂ)‖ ≤ |K₂| :=
    h2.trans (mul_le_of_le_one_right (abs_nonneg _) hsN)
  refine (norm_mul_sub_boxPoly_le T S hy (F p) (G p)).trans ?_
  calc _ ≤ |K₁| * s ^ (N + 1) * (B + |K₂|) + A * (|K₂| * s ^ (N + 1)) + A * B * s ^ (N + 1) := by
        gcongr
    _ = _ := by ring

theorem pow (hF : CepsJetScalAt p₀ N F T) (n : ℕ) :
    CepsJetScalAt p₀ N (fun p => F p ^ n)
      (Nat.rec (fun α : Fin d → ℕ => if α = 0 then (1 : ℂ) else 0)
        (fun _ P => cepsBoxMul P T) n) := by
  induction n with
  | zero => simpa using (const (p₀ := p₀) (N := N) (d := d) (1 : ℂ))
  | succ n ih => simpa only [pow_succ] using ih.mul hF

end CepsJetScalAt

/-- The `n`-th Cauchy power of a coefficient family. -/
def cepsBoxPow {R : Type*} [CommSemiring R] {d : ℕ} (T : (Fin d → ℕ) → R) :
    ℕ → (Fin d → ℕ) → R
  | 0 => fun α => if α = 0 then 1 else 0
  | n + 1 => cepsBoxMul (cepsBoxPow T n) T

namespace CepsJetScal

variable {F G : (ℕ → ℝ) → ℂ} {T S : (Fin d → ℕ) → ℂ}

theorem add (hF : CepsJetScal p₀ F T) (hG : CepsJetScal p₀ G S) :
    CepsJetScal p₀ (fun p => F p + G p) (fun α => T α + S α) := fun N => (hF N).add (hG N)

theorem const_mul (hF : CepsJetScal p₀ F T) (a : ℂ) :
    CepsJetScal p₀ (fun p => a * F p) (fun α => a * T α) := fun N => (hF N).const_mul a

theorem sum {ι : Type*} (s : Finset ι) {F : ι → (ℕ → ℝ) → ℂ} {T : ι → (Fin d → ℕ) → ℂ}
    (h : ∀ i ∈ s, CepsJetScal p₀ (F i) (T i)) :
    CepsJetScal p₀ (fun p => ∑ i ∈ s, F i p) (fun α => ∑ i ∈ s, T i α) :=
  fun N => CepsJetScalAt.sum s fun i hi => h i hi N

theorem const (a : ℂ) :
    CepsJetScal p₀ (fun _ => a) (fun α : Fin d → ℕ => if α = 0 then a else 0) :=
  fun _ => CepsJetScalAt.const a

theorem mul (hF : CepsJetScal p₀ F T) (hG : CepsJetScal p₀ G S) :
    CepsJetScal p₀ (fun p => F p * G p) (cepsBoxMul T S) := fun N => (hF N).mul (hG N)

theorem pow (hF : CepsJetScal p₀ F T) (n : ℕ) :
    CepsJetScal p₀ (fun p => F p ^ n) (cepsBoxPow T n) := by
  induction n with
  | zero => simpa [cepsBoxPow] using (const (p₀ := p₀) (d := d) (1 : ℂ))
  | succ n ih => simpa only [pow_succ, cepsBoxPow] using ih.mul hF

theorem sub (hF : CepsJetScal p₀ F T) (hG : CepsJetScal p₀ G S) :
    CepsJetScal p₀ (fun p => F p - G p) (fun α => T α - S α) := by
  have := hF.add (hG.const_mul (-1))
  simpa [sub_eq_add_neg] using this

theorem congr_fun (h : CepsJetScal p₀ G T)
    (hc : ∃ ρ : ℝ, 0 < ρ ∧ ∀ p : ℕ → ℝ, (∀ i : Fin d, |p i - p₀ i| ≤ ρ) → F p = G p) :
    CepsJetScal p₀ F T := fun N => (h N).congr_fun hc

/-- The constant coefficient is the value at the reference point. -/
theorem coeff_zero (h : CepsJetScal p₀ F T) : T 0 = F p₀ := by
  obtain ⟨ρ, K, hρ, H⟩ := h 0
  have h0 := H p₀ fun i => by simpa using hρ.le
  have hpoly := cepsJet_boxPoly_at_ref (p₀ := p₀) (d := d) 0 T
  simp only [smul_eq_mul] at hpoly
  simp_rw [mul_comm (T _)] at h0
  rw [hpoly] at h0
  simp only [sub_self, abs_zero, sum_const_zero, zero_add, pow_one, mul_zero] at h0
  exact (sub_eq_zero.mp (norm_le_zero_iff.mp h0)).symm

/-- A function vanishing at the reference point is `O(|y|)` near it. -/
theorem norm_le_of_ref (h : CepsJetScal p₀ F T) (h0 : F p₀ = 0) :
    ∃ ρ K : ℝ, 0 < ρ ∧ 0 ≤ K ∧ ∀ p : ℕ → ℝ, (∀ i : Fin d, |p i - p₀ i| ≤ ρ) →
      ‖F p‖ ≤ K * ∑ i : Fin d, |p i - p₀ i| := by
  have hT0 := h.coeff_zero
  obtain ⟨ρ, K, hρ, H⟩ := h 0
  refine ⟨ρ, |K|, hρ, abs_nonneg _, fun p hp => ?_⟩
  have := H p hp
  rw [cepsTaylorBox_zero, sum_singleton, hT0, h0, zero_mul, sub_zero, zero_add, pow_one] at this
  exact this.trans (mul_le_mul_of_nonneg_right (le_abs_self K) (cepsJet_size_nonneg p))

end CepsJetScal

/-! ## Weighted representations at a fixed order -/

theorem cepsJetDecayCoeff_common {T : (Fin d → ℕ) → ℝ → ℂ} (hT : CepsJetDecayCoeff T)
    (s : Finset (Fin d → ℕ)) :
    ∃ K c : ℝ, 0 ≤ K ∧ 0 < c ∧ ∃ e : ℕ, ∀ α ∈ s, ∀ u,
      ‖T α u‖ ≤ K * cepsStretchedWeight c e u :=
  exists_common_stretched_bound s T fun α _ => hT α

namespace CepsJetDecayAt

variable {N : ℕ} {F G : ℝ → (ℕ → ℝ) → ℂ} {T S : (Fin d → ℕ) → ℝ → ℂ}

theorem congr_coeff (h : CepsJetDecayAt p₀ N F T) {T' : (Fin d → ℕ) → ℝ → ℂ}
    (hT : ∀ α ∈ cepsTaylorBox d N, ∀ u, T α u = T' α u) : CepsJetDecayAt p₀ N F T' := by
  obtain ⟨ρ, K, c, hρ, hc, e, H⟩ := h
  refine ⟨ρ, K, c, hρ, hc, e, fun u p hp => ?_⟩
  have e' : ∑ α ∈ cepsTaylorBox d N,
      T α u * (cepsMonomial (fun i : Fin d => p i - p₀ i) α : ℂ) =
      ∑ α ∈ cepsTaylorBox d N, T' α u * (cepsMonomial (fun i : Fin d => p i - p₀ i) α : ℂ) :=
    sum_congr rfl fun α hα => by rw [hT α hα u]
  rw [← e']
  exact H u p hp

theorem of_close (h : CepsJetDecayAt p₀ N G T)
    (hcl : ∃ ρ K c : ℝ, 0 < ρ ∧ 0 < c ∧ ∃ e : ℕ, ∀ (u : ℝ) (p : ℕ → ℝ),
      (∀ i : Fin d, |p i - p₀ i| ≤ ρ) →
        ‖F u p - G u p‖ ≤ K * cepsStretchedWeight c e u * (∑ i : Fin d, |p i - p₀ i|) ^ (N + 1)) :
    CepsJetDecayAt p₀ N F T := by
  obtain ⟨ρ₁, K₁, c₁, hρ₁, hc₁, e₁, H₁⟩ := h
  obtain ⟨ρ₂, K₂, c₂, hρ₂, hc₂, e₂, H₂⟩ := hcl
  refine ⟨min ρ₁ ρ₂, |K₂| + |K₁|, min c₁ c₂, lt_min hρ₁ hρ₂, lt_min hc₁ hc₂, e₁ + e₂,
    fun u p hp => ?_⟩
  have h1 := H₁ u p fun i => (hp i).trans (min_le_left _ _)
  have h2 := H₂ u p fun i => (hp i).trans (min_le_right _ _)
  have hs := pow_nonneg (cepsJet_size_nonneg (p₀ := p₀) (d := d) p) (N + 1)
  have hw₁ := cepsStretchedWeight_le_of_le (min_le_left c₁ c₂) (Nat.le_add_right e₁ e₂) u
  have hw₂ := cepsStretchedWeight_le_of_le (min_le_right c₁ c₂) (Nat.le_add_left e₂ e₁) u
  have hwp := cepsStretchedWeight_pos c₁ e₁ u
  have hwp₂ := cepsStretchedWeight_pos c₂ e₂ u
  calc _ = ‖(F u p - G u p) + (G u p - ∑ α ∈ cepsTaylorBox d N,
        T α u * (cepsMonomial (fun i : Fin d => p i - p₀ i) α : ℂ))‖ := by ring_nf
    _ ≤ _ := norm_add_le _ _
    _ ≤ |K₂| * cepsStretchedWeight (min c₁ c₂) (e₁ + e₂) u * (∑ i : Fin d, |p i - p₀ i|) ^ (N + 1)
        + |K₁| * cepsStretchedWeight (min c₁ c₂) (e₁ + e₂) u *
          (∑ i : Fin d, |p i - p₀ i|) ^ (N + 1) := by
        refine add_le_add (h2.trans ?_) (h1.trans ?_)
        · exact mul_le_mul_of_nonneg_right (mul_le_mul (le_abs_self _) hw₂ hwp₂.le
            (abs_nonneg _)) hs
        · exact mul_le_mul_of_nonneg_right (mul_le_mul (le_abs_self _) hw₁ hwp.le
            (abs_nonneg _)) hs
    _ = _ := by ring

theorem congr_fun (h : CepsJetDecayAt p₀ N G T)
    (hc : ∃ ρ : ℝ, 0 < ρ ∧ ∀ (u : ℝ) (p : ℕ → ℝ), (∀ i : Fin d, |p i - p₀ i| ≤ ρ) →
      F u p = G u p) : CepsJetDecayAt p₀ N F T := by
  obtain ⟨ρ, hρ, H⟩ := hc
  exact h.of_close ⟨ρ, 0, 1, hρ, one_pos, 0, fun u p hp => by
    rw [H u p hp, sub_self, norm_zero, zero_mul, zero_mul]⟩

theorem add (hF : CepsJetDecayAt p₀ N F T) (hG : CepsJetDecayAt p₀ N G S) :
    CepsJetDecayAt p₀ N (fun u p => F u p + G u p) (fun α u => T α u + S α u) := by
  obtain ⟨ρ₁, K₁, c₁, hρ₁, hc₁, e₁, H₁⟩ := hF
  obtain ⟨ρ₂, K₂, c₂, hρ₂, hc₂, e₂, H₂⟩ := hG
  refine ⟨min ρ₁ ρ₂, |K₁| + |K₂|, min c₁ c₂, lt_min hρ₁ hρ₂, lt_min hc₁ hc₂, e₁ + e₂,
    fun u p hp => ?_⟩
  have h1 := H₁ u p fun i => (hp i).trans (min_le_left _ _)
  have h2 := H₂ u p fun i => (hp i).trans (min_le_right _ _)
  have hs := pow_nonneg (cepsJet_size_nonneg (p₀ := p₀) (d := d) p) (N + 1)
  have hw₁ := cepsStretchedWeight_le_of_le (min_le_left c₁ c₂) (Nat.le_add_right e₁ e₂) u
  have hw₂ := cepsStretchedWeight_le_of_le (min_le_right c₁ c₂) (Nat.le_add_left e₂ e₁) u
  have hwp := cepsStretchedWeight_pos c₁ e₁ u
  have hwp₂ := cepsStretchedWeight_pos c₂ e₂ u
  simp_rw [add_mul, sum_add_distrib]
  calc _ = ‖(F u p - ∑ α ∈ cepsTaylorBox d N,
        T α u * (cepsMonomial (fun i : Fin d => p i - p₀ i) α : ℂ)) +
      (G u p - ∑ α ∈ cepsTaylorBox d N,
        S α u * (cepsMonomial (fun i : Fin d => p i - p₀ i) α : ℂ))‖ := by ring_nf
    _ ≤ _ := norm_add_le _ _
    _ ≤ |K₁| * cepsStretchedWeight (min c₁ c₂) (e₁ + e₂) u * (∑ i : Fin d, |p i - p₀ i|) ^ (N + 1)
        + |K₂| * cepsStretchedWeight (min c₁ c₂) (e₁ + e₂) u *
          (∑ i : Fin d, |p i - p₀ i|) ^ (N + 1) := by
        refine add_le_add (h1.trans ?_) (h2.trans ?_)
        · exact mul_le_mul_of_nonneg_right (mul_le_mul (le_abs_self _) hw₁ hwp.le
            (abs_nonneg _)) hs
        · exact mul_le_mul_of_nonneg_right (mul_le_mul (le_abs_self _) hw₂ hwp₂.le
            (abs_nonneg _)) hs
    _ = _ := by ring

theorem zero : CepsJetDecayAt p₀ N (fun _ _ => 0) (fun (_ : Fin d → ℕ) _ => 0) :=
  ⟨1, 0, 1, one_pos, one_pos, 0, fun u p _ => by simp⟩

theorem sum {ι : Type*} (s : Finset ι) {F : ι → ℝ → (ℕ → ℝ) → ℂ}
    {T : ι → (Fin d → ℕ) → ℝ → ℂ} (h : ∀ i ∈ s, CepsJetDecayAt p₀ N (F i) (T i)) :
    CepsJetDecayAt p₀ N (fun u p => ∑ i ∈ s, F i u p) (fun α u => ∑ i ∈ s, T i α u) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zero : CepsJetDecayAt p₀ N (fun _ _ => 0) (fun (_ : Fin d → ℕ) _ => 0))
  | insert a s ha ih =>
    simp_rw [sum_insert ha]
    exact (h a (mem_insert_self a s)).add (ih fun i hi => h i (mem_insert_of_mem hi))

/-- Multiplication by a polynomially bounded function of `u`. -/
theorem poly_mul (hF : CepsJetDecayAt p₀ N F T) {q : ℝ → ℂ} {Kq : ℝ} {n : ℕ}
    (hq : ∀ u, ‖q u‖ ≤ Kq * (1 + |u|) ^ n) :
    CepsJetDecayAt p₀ N (fun u p => q u * F u p) (fun α u => q u * T α u) := by
  obtain ⟨ρ, K, c, hρ, hc, e, H⟩ := hF
  refine ⟨ρ, |Kq| * |K|, c, hρ, hc, n + e, fun u p hp => ?_⟩
  have h1 := H u p hp
  have hs := pow_nonneg (cepsJet_size_nonneg (p₀ := p₀) (d := d) p) (N + 1)
  have hq' : ‖q u‖ ≤ |Kq| * (1 + |u|) ^ n :=
    (hq u).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
  simp_rw [mul_assoc, ← mul_sum, ← mul_sub, norm_mul]
  have hw : (1 + |u|) ^ n * cepsStretchedWeight c e u = cepsStretchedWeight c (n + e) u := by
    rw [← cepsStretchedWeight_zero_rate, cepsStretchedWeight_mul, zero_add]
  calc ‖q u‖ * ‖F u p - ∑ α ∈ cepsTaylorBox d N,
        T α u * (cepsMonomial (fun i : Fin d => p i - p₀ i) α : ℂ)‖
      ≤ (|Kq| * (1 + |u|) ^ n) * (|K| * cepsStretchedWeight c e u *
          (∑ i : Fin d, |p i - p₀ i|) ^ (N + 1)) :=
        mul_le_mul hq' (h1.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (le_abs_self K) (cepsStretchedWeight_pos c e u).le) hs)) (norm_nonneg _)
          (by positivity)
    _ = |Kq| * |K| * ((1 + |u|) ^ n * cepsStretchedWeight c e u) *
          (∑ i : Fin d, |p i - p₀ i|) ^ (N + 1) := by ring
    _ = _ := by rw [hw]; ring

/-- Multiplication of a weighted representation by a scalar one. -/
theorem mul_scal {G : (ℕ → ℝ) → ℂ} {S : (Fin d → ℕ) → ℂ} (hT : CepsJetDecayCoeff T)
    (hF : CepsJetDecayAt p₀ N F T) (hG : CepsJetScalAt p₀ N G S) :
    CepsJetDecayAt p₀ N (fun u p => F u p * G p)
      (fun γ u => cepsBoxMul (fun α => T α u) S γ) := by
  obtain ⟨ρ₁, K₁, c₁, hρ₁, hc₁, e₁, H₁⟩ := hF
  obtain ⟨ρ₂, K₂, hρ₂, H₂⟩ := hG
  obtain ⟨KT, cT, hKT, hcT, eT, HT⟩ := cepsJetDecayCoeff_common hT (cepsTaylorBox d N)
  set B := ∑ β ∈ cepsTaylorBox d N, ‖S β‖
  set n := (cepsTaylorBox d N).card
  have hB : 0 ≤ B := sum_nonneg fun _ _ => norm_nonneg _
  refine ⟨min (min ρ₁ ρ₂) (1 / ((d : ℝ) + 1)),
    |K₁| * (B + |K₂|) + n * KT * |K₂| + n * KT * B, min c₁ cT,
    cepsJet_small_box_pos (lt_min hρ₁ hρ₂), lt_min hc₁ hcT, e₁ + eT, fun u p hp => ?_⟩
  obtain ⟨hp', hy, hs⟩ := cepsJet_small_box hp
  set s := ∑ i : Fin d, |p i - p₀ i|
  have hs0 : 0 ≤ s := cepsJet_size_nonneg p
  have hsN : s ^ (N + 1) ≤ 1 := pow_le_one₀ hs0 hs
  set w := cepsStretchedWeight (min c₁ cT) (e₁ + eT) u
  have hw0 : 0 ≤ w := (cepsStretchedWeight_pos _ _ _).le
  have hw₁ : cepsStretchedWeight c₁ e₁ u ≤ w :=
    cepsStretchedWeight_le_of_le (min_le_left _ _) (Nat.le_add_right _ _) u
  have hwT : cepsStretchedWeight cT eT u ≤ w :=
    cepsStretchedWeight_le_of_le (min_le_right _ _) (Nat.le_add_left _ _) u
  have h1 : ‖F u p - ∑ α ∈ cepsTaylorBox d N,
      T α u * (cepsMonomial (fun i : Fin d => p i - p₀ i) α : ℂ)‖ ≤ |K₁| * w * s ^ (N + 1) :=
    (H₁ u p fun i => (hp' i).trans (min_le_left _ _)).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul (le_abs_self _) hw₁
        (cepsStretchedWeight_pos _ _ _).le (abs_nonneg _)) (pow_nonneg hs0 _))
  have h2 : ‖G p - ∑ β ∈ cepsTaylorBox d N,
      S β * (cepsMonomial (fun i : Fin d => p i - p₀ i) β : ℂ)‖ ≤ |K₂| * s ^ (N + 1) :=
    (H₂ p fun i => (hp' i).trans (min_le_right _ _)).trans
      (mul_le_mul_of_nonneg_right (le_abs_self K₂) (pow_nonneg hs0 _))
  have h2' := h2.trans (mul_le_of_le_one_right (abs_nonneg _) hsN)
  have hA : ∑ α ∈ cepsTaylorBox d N, ‖T α u‖ ≤ n * KT * w := by
    calc ∑ α ∈ cepsTaylorBox d N, ‖T α u‖ ≤ ∑ _α ∈ cepsTaylorBox d N, KT * w :=
          sum_le_sum fun α hα => (HT α hα u).trans (mul_le_mul_of_nonneg_left hwT hKT)
      _ = n * KT * w := by rw [sum_const, nsmul_eq_mul]; ring
  refine (norm_mul_sub_boxPoly_le (fun α => T α u) S hy (F u p) (G p)).trans ?_
  have hA0 : 0 ≤ ∑ α ∈ cepsTaylorBox d N, ‖T α u‖ := sum_nonneg fun _ _ => norm_nonneg _
  calc _ ≤ |K₁| * w * s ^ (N + 1) * (B + |K₂|) + (n * KT * w) * (|K₂| * s ^ (N + 1)) +
        (n * KT * w) * B * s ^ (N + 1) := by
        gcongr
    _ = _ := by ring

end CepsJetDecayAt

namespace CepsJetDecayCoeff

variable {T S : (Fin d → ℕ) → ℝ → ℂ}

theorem add (hT : CepsJetDecayCoeff T) (hS : CepsJetDecayCoeff S) :
    CepsJetDecayCoeff (fun α u => T α u + S α u) := by
  intro α
  obtain ⟨K, c, _, hc, e, H⟩ := exists_common_stretched_bound {0, 1}
    (fun i : ℕ => if i = 0 then T α else S α) (by
      intro i hi
      rcases mem_insert.mp hi with rfl | hi
      · simpa using hT α
      · rw [mem_singleton] at hi; subst hi; simpa using hS α)
  refine ⟨2 * K, c, hc, e, fun u => ?_⟩
  have h1 := H 0 (by simp) u
  have h2 := H 1 (by simp) u
  simp only [if_true, one_ne_zero, if_false] at h1 h2
  calc ‖T α u + S α u‖ ≤ ‖T α u‖ + ‖S α u‖ := norm_add_le _ _
    _ ≤ _ := by linarith

theorem sum {ι : Type*} (s : Finset ι) {T : ι → (Fin d → ℕ) → ℝ → ℂ}
    (h : ∀ i ∈ s, CepsJetDecayCoeff (T i)) :
    CepsJetDecayCoeff (fun α u => ∑ i ∈ s, T i α u) := by
  intro α
  obtain ⟨K, c, _, hc, e, H⟩ := exists_common_stretched_bound s (fun i => T i α)
    (fun i hi => h i hi α)
  refine ⟨s.card * K, c, hc, e, fun u => ?_⟩
  calc ‖∑ i ∈ s, T i α u‖ ≤ ∑ i ∈ s, ‖T i α u‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ s, K * cepsStretchedWeight c e u := sum_le_sum fun i hi => H i hi u
    _ = _ := by rw [sum_const, nsmul_eq_mul]; ring

theorem poly_mul (hT : CepsJetDecayCoeff T) {q : ℝ → ℂ} {Kq : ℝ} {n : ℕ}
    (hq : ∀ u, ‖q u‖ ≤ Kq * (1 + |u|) ^ n) :
    CepsJetDecayCoeff (fun α u => q u * T α u) := by
  intro α
  obtain ⟨K, c, hc, e, H⟩ := hT α
  refine ⟨|Kq| * |K|, c, hc, n + e, fun u => ?_⟩
  have hq' : ‖q u‖ ≤ |Kq| * (1 + |u|) ^ n :=
    (hq u).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
  have hw : (1 + |u|) ^ n * cepsStretchedWeight c e u = cepsStretchedWeight c (n + e) u := by
    rw [← cepsStretchedWeight_zero_rate, cepsStretchedWeight_mul, zero_add]
  rw [norm_mul]
  calc ‖q u‖ * ‖T α u‖ ≤ (|Kq| * (1 + |u|) ^ n) * (|K| * cepsStretchedWeight c e u) :=
        mul_le_mul hq' ((H u).trans (mul_le_mul_of_nonneg_right (le_abs_self _)
          (cepsStretchedWeight_pos _ _ _).le)) (norm_nonneg _) (by positivity)
    _ = |Kq| * |K| * ((1 + |u|) ^ n * cepsStretchedWeight c e u) := by ring
    _ = _ := by rw [hw]

theorem mul_scal (hT : CepsJetDecayCoeff T) (S : (Fin d → ℕ) → ℂ) :
    CepsJetDecayCoeff (fun γ u => cepsBoxMul (fun α => T α u) S γ) := by
  intro γ
  obtain ⟨K, c, hK, hc, e, H⟩ := cepsJetDecayCoeff_common hT (cepsLowerBox γ)
  refine ⟨(∑ β ∈ cepsLowerBox γ, ‖S (γ - β)‖) * K, c, hc, e, fun u => ?_⟩
  unfold cepsBoxMul
  calc ‖∑ β ∈ cepsLowerBox γ, T β u * S (γ - β)‖
      ≤ ∑ β ∈ cepsLowerBox γ, ‖T β u‖ * ‖S (γ - β)‖ :=
        (norm_sum_le _ _).trans (le_of_eq (sum_congr rfl fun β _ => norm_mul _ _))
    _ ≤ ∑ β ∈ cepsLowerBox γ, K * cepsStretchedWeight c e u * ‖S (γ - β)‖ :=
        sum_le_sum fun β hβ => mul_le_mul_of_nonneg_right (H β hβ u) (norm_nonneg _)
    _ = _ := by rw [← mul_sum]; ring

end CepsJetDecayCoeff

namespace CepsJetDecay

variable {F G : ℝ → (ℕ → ℝ) → ℂ} {T S : (Fin d → ℕ) → ℝ → ℂ}

theorem add (hF : CepsJetDecay p₀ F T) (hG : CepsJetDecay p₀ G S) :
    CepsJetDecay p₀ (fun u p => F u p + G u p) (fun α u => T α u + S α u) :=
  ⟨hF.1.add hG.1, fun N => (hF.2 N).add (hG.2 N)⟩

theorem sum {ι : Type*} (s : Finset ι) {F : ι → ℝ → (ℕ → ℝ) → ℂ}
    {T : ι → (Fin d → ℕ) → ℝ → ℂ} (h : ∀ i ∈ s, CepsJetDecay p₀ (F i) (T i)) :
    CepsJetDecay p₀ (fun u p => ∑ i ∈ s, F i u p) (fun α u => ∑ i ∈ s, T i α u) :=
  ⟨CepsJetDecayCoeff.sum s fun i hi => (h i hi).1,
    fun N => CepsJetDecayAt.sum s fun i hi => (h i hi).2 N⟩

theorem poly_mul (hF : CepsJetDecay p₀ F T) {q : ℝ → ℂ} {Kq : ℝ} {n : ℕ}
    (hq : ∀ u, ‖q u‖ ≤ Kq * (1 + |u|) ^ n) :
    CepsJetDecay p₀ (fun u p => q u * F u p) (fun α u => q u * T α u) :=
  ⟨hF.1.poly_mul hq, fun N => (hF.2 N).poly_mul hq⟩

theorem const_mul (hF : CepsJetDecay p₀ F T) (a : ℂ) :
    CepsJetDecay p₀ (fun u p => a * F u p) (fun α u => a * T α u) :=
  hF.poly_mul (q := fun _ => a) (Kq := ‖a‖) (n := 0) fun _ => by simp

theorem mul_scal {G : (ℕ → ℝ) → ℂ} {S : (Fin d → ℕ) → ℂ} (hF : CepsJetDecay p₀ F T)
    (hG : CepsJetScal p₀ G S) :
    CepsJetDecay p₀ (fun u p => F u p * G p) (fun γ u => cepsBoxMul (fun α => T α u) S γ) :=
  ⟨hF.1.mul_scal S, fun N => (hF.2 N).mul_scal hF.1 (hG N)⟩

theorem congr_fun (h : CepsJetDecay p₀ G T)
    (hc : ∃ ρ : ℝ, 0 < ρ ∧ ∀ (u : ℝ) (p : ℕ → ℝ), (∀ i : Fin d, |p i - p₀ i| ≤ ρ) →
      F u p = G u p) : CepsJetDecay p₀ F T :=
  ⟨h.1, fun N => (h.2 N).congr_fun hc⟩

/-- A decaying function of `u` alone. -/
theorem of_fun {f : ℝ → ℂ} {K c : ℝ} (hc : 0 < c) {e : ℕ}
    (hf : ∀ u, ‖f u‖ ≤ K * cepsStretchedWeight c e u) :
    CepsJetDecay p₀ (fun u _ => f u) (fun (α : Fin d → ℕ) u => if α = 0 then f u else 0) := by
  classical
  refine ⟨fun α => ?_, fun N => ⟨1, 0, 1, one_pos, one_pos, 0, fun u p _ => ?_⟩⟩
  · by_cases hα : α = 0
    · exact ⟨K, c, hc, e, fun u => by simpa [hα] using hf u⟩
    · exact ⟨0, 1, one_pos, 0, fun u => by simp [hα]⟩
  · rw [sum_eq_single 0 (fun b _ hb => by simp [hb])
      (fun h => absurd (zero_mem_cepsTaylorBox d N) h)]
    simp [cepsMonomial_zero_index]

end CepsJetDecay

end

end PGM
