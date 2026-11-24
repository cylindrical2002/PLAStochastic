import PLAStochastic.Index.CEPS.Assembly.Interfaces

/-!
# Box Taylor polynomials in finitely many jet coordinates: algebra

Elementary facts used by the jet Taylor representations of `Final.TaylorRep`:

* stretched weights `cepsStretchedWeight c e u = (1+|u|)ᵉ e^{-c√|u|}` multiply, are monotone in
  `e` and antitone in `c`, and compare under a change of scale;
* monomials `cepsMonomial y α = ∏ yᵢ^{αᵢ}` multiply, are at most `1` on the unit cube and at most
  `|y|^{N+1}` outside the Taylor box of order `N`;
* the Cauchy product `cepsBoxMul` of coefficient families and the reindexing of a product of two
  box polynomials (`sum_box_mul_sum_box`);
* the pointwise product estimate `norm_mul_sub_boxPoly_le`.
-/

namespace PGM

noncomputable section

open Finset

/-! ## Stretched weights -/

theorem cepsStretchedWeight_mul (c₁ c₂ : ℝ) (e₁ e₂ : ℕ) (u : ℝ) :
    cepsStretchedWeight c₁ e₁ u * cepsStretchedWeight c₂ e₂ u =
      cepsStretchedWeight (c₁ + c₂) (e₁ + e₂) u := by
  unfold cepsStretchedWeight
  rw [pow_add, show -(c₁ + c₂) * Real.sqrt |u| = -c₁ * Real.sqrt |u| + -c₂ * Real.sqrt |u| by
    ring, Real.exp_add]
  ring

theorem cepsStretchedWeight_le_of_le {c c' : ℝ} {e e' : ℕ} (hc : c' ≤ c) (he : e ≤ e')
    (u : ℝ) : cepsStretchedWeight c e u ≤ cepsStretchedWeight c' e' u := by
  unfold cepsStretchedWeight
  have h1 : (1 : ℝ) ≤ 1 + |u| := by linarith [abs_nonneg u]
  have hs := Real.sqrt_nonneg |u|
  exact mul_le_mul (pow_le_pow_right₀ h1 he) (Real.exp_le_exp.mpr (by nlinarith))
    (Real.exp_pos _).le (by positivity)

theorem cepsStretchedWeight_pos (c : ℝ) (e : ℕ) (u : ℝ) : 0 < cepsStretchedWeight c e u := by
  unfold cepsStretchedWeight
  have : (0 : ℝ) < 1 + |u| := by linarith [abs_nonneg u]
  positivity

theorem cepsStretchedWeight_zero_rate (e : ℕ) (u : ℝ) :
    cepsStretchedWeight 0 e u = (1 + |u|) ^ e := by
  simp [cepsStretchedWeight]

theorem one_le_cepsStretchedWeight_zero (e : ℕ) (u : ℝ) : 1 ≤ cepsStretchedWeight 0 e u := by
  rw [cepsStretchedWeight_zero_rate]
  exact one_le_pow₀ (by linarith [abs_nonneg u])

theorem cepsStretchedWeight_at_zero (c : ℝ) (e : ℕ) : cepsStretchedWeight c e 0 = 1 := by
  simp [cepsStretchedWeight]

/-- Comparable arguments: `|x| ≤ A |x₀|` and `B |x₀| ≤ |x|`. -/
theorem cepsStretchedWeight_le_of_comparable {c : ℝ} (hc : 0 ≤ c) (e : ℕ) {A B : ℝ}
    (hA : 1 ≤ A) (hB : 0 ≤ B) {x x₀ : ℝ} (hup : |x| ≤ A * |x₀|) (hlo : B * |x₀| ≤ |x|) :
    cepsStretchedWeight c e x ≤ A ^ e * cepsStretchedWeight (c * Real.sqrt B) e x₀ := by
  unfold cepsStretchedWeight
  have h0 := abs_nonneg x₀
  have hpow : (1 + |x|) ^ e ≤ A ^ e * (1 + |x₀|) ^ e := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by nlinarith) e
  have hsq : Real.sqrt B * Real.sqrt |x₀| ≤ Real.sqrt |x| := by
    rw [← Real.sqrt_mul hB]
    exact Real.sqrt_le_sqrt hlo
  have hexp : Real.exp (-c * Real.sqrt |x|) ≤ Real.exp (-(c * Real.sqrt B) * Real.sqrt |x₀|) :=
    Real.exp_le_exp.mpr (by nlinarith)
  calc (1 + |x|) ^ e * Real.exp (-c * Real.sqrt |x|)
      ≤ (A ^ e * (1 + |x₀|) ^ e) * Real.exp (-(c * Real.sqrt B) * Real.sqrt |x₀|) :=
        mul_le_mul hpow hexp (Real.exp_pos _).le (by positivity)
    _ = A ^ e * ((1 + |x₀|) ^ e * Real.exp (-(c * Real.sqrt B) * Real.sqrt |x₀|)) := by ring

/-- A rescaled argument `a u`. -/
theorem cepsStretchedWeight_mul_arg_le {c : ℝ} (hc : 0 ≤ c) (e : ℕ) (a u : ℝ) :
    cepsStretchedWeight c e (a * u) ≤
      (max 1 |a|) ^ e * cepsStretchedWeight (c * Real.sqrt |a|) e u := by
  apply cepsStretchedWeight_le_of_comparable hc e (le_max_left _ _) (abs_nonneg a)
  · rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (abs_nonneg u)
  · rw [abs_mul]

/-- Powers of `|u|` are polynomial weights. -/
theorem abs_pow_le_cepsStretchedWeight_zero (n : ℕ) (u : ℝ) :
    |u| ^ n ≤ cepsStretchedWeight 0 n u := by
  rw [cepsStretchedWeight_zero_rate]
  exact pow_le_pow_left₀ (abs_nonneg u) (by linarith) n

/-- A finite family of stretched bounds with positive rates has a common one. -/
theorem exists_common_stretched_bound {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℂ)
    (h : ∀ i ∈ s, ∃ K c : ℝ, 0 < c ∧ ∃ e : ℕ, ∀ u, ‖f i u‖ ≤ K * cepsStretchedWeight c e u) :
    ∃ K c : ℝ, 0 ≤ K ∧ 0 < c ∧ ∃ e : ℕ, ∀ i ∈ s, ∀ u,
      ‖f i u‖ ≤ K * cepsStretchedWeight c e u := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, 1, le_rfl, one_pos, 0, fun i hi => absurd hi (Finset.notMem_empty i)⟩
  | insert a s ha ih =>
    obtain ⟨K₁, c₁, hc₁, e₁, h₁⟩ := h a (mem_insert_self a s)
    obtain ⟨K₂, c₂, hK₂, hc₂, e₂, h₂⟩ := ih fun i hi => h i (mem_insert_of_mem hi)
    refine ⟨max (max K₁ 0) K₂, min c₁ c₂, by positivity, lt_min hc₁ hc₂, e₁ + e₂,
      fun i hi u => ?_⟩
    have hw₁ := cepsStretchedWeight_le_of_le (min_le_left c₁ c₂) (Nat.le_add_right e₁ e₂) u
    have hw₂ := cepsStretchedWeight_le_of_le (min_le_right c₁ c₂) (Nat.le_add_left e₂ e₁) u
    have hpos := (cepsStretchedWeight_pos (min c₁ c₂) (e₁ + e₂) u).le
    rcases mem_insert.mp hi with rfl | hi
    · calc ‖f i u‖ ≤ K₁ * cepsStretchedWeight c₁ e₁ u := h₁ u
        _ ≤ max K₁ 0 * cepsStretchedWeight c₁ e₁ u :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (cepsStretchedWeight_pos _ _ _).le
        _ ≤ max (max K₁ 0) K₂ * cepsStretchedWeight (min c₁ c₂) (e₁ + e₂) u :=
          mul_le_mul (le_max_left _ _) hw₁ (cepsStretchedWeight_pos _ _ _).le (by positivity)
    · calc ‖f i u‖ ≤ K₂ * cepsStretchedWeight c₂ e₂ u := h₂ i hi u
        _ ≤ max (max K₁ 0) K₂ * cepsStretchedWeight (min c₁ c₂) (e₁ + e₂) u :=
          mul_le_mul (le_max_right _ _) hw₂ (cepsStretchedWeight_pos _ _ _).le (by positivity)

/-! ## Boxes and monomials -/

theorem mem_cepsTaylorBox {d N : ℕ} {α : Fin d → ℕ} :
    α ∈ cepsTaylorBox d N ↔ ∀ i, α i ≤ N := by
  simp [cepsTaylorBox, Fintype.mem_piFinset]

theorem zero_mem_cepsTaylorBox (d N : ℕ) : (0 : Fin d → ℕ) ∈ cepsTaylorBox d N :=
  mem_cepsTaylorBox.mpr fun _ => Nat.zero_le _

/-- The multi-indices below `γ`. -/
def cepsLowerBox {d : ℕ} (γ : Fin d → ℕ) : Finset (Fin d → ℕ) :=
  Fintype.piFinset fun i => range (γ i + 1)

theorem mem_cepsLowerBox {d : ℕ} {γ β : Fin d → ℕ} : β ∈ cepsLowerBox γ ↔ β ≤ γ := by
  simp [cepsLowerBox, Fintype.mem_piFinset, Pi.le_def]

theorem cepsLowerBox_subset {d N : ℕ} {γ : Fin d → ℕ} (hγ : γ ∈ cepsTaylorBox d N) :
    cepsLowerBox γ ⊆ cepsTaylorBox d N := by
  intro β hβ
  rw [mem_cepsLowerBox] at hβ
  rw [mem_cepsTaylorBox] at hγ ⊢
  exact fun i => (hβ i).trans (hγ i)

theorem cepsMonomial_add {d : ℕ} (y : Fin d → ℝ) (α β : Fin d → ℕ) :
    cepsMonomial y (α + β) = cepsMonomial y α * cepsMonomial y β := by
  unfold cepsMonomial
  rw [← prod_mul_distrib]
  exact prod_congr rfl fun i _ => by rw [Pi.add_apply, pow_add]

theorem cepsMonomial_zero_index {d : ℕ} (y : Fin d → ℝ) : cepsMonomial y 0 = 1 := by
  simp [cepsMonomial]

theorem cepsMonomial_zero_arg {d : ℕ} (α : Fin d → ℕ) :
    cepsMonomial (0 : Fin d → ℝ) α = if α = 0 then 1 else 0 := by
  unfold cepsMonomial
  split_ifs with h
  · subst h; simp
  · obtain ⟨i, hi⟩ : ∃ i, α i ≠ 0 := by
      by_contra hc
      push Not at hc
      exact h (funext hc)
    exact prod_eq_zero (mem_univ i) (by simp [zero_pow hi])

theorem abs_cepsMonomial_le_one {d : ℕ} {y : Fin d → ℝ} (hy : ∀ i, |y i| ≤ 1)
    (α : Fin d → ℕ) : |cepsMonomial y α| ≤ 1 := by
  unfold cepsMonomial
  rw [abs_prod]
  exact prod_le_one (fun _ _ => abs_nonneg _) fun i _ => by
    rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) (hy i)

/-- Outside the box of order `N` a monomial on the unit cube is at most `|y|^{N+1}`. -/
theorem abs_cepsMonomial_le_of_not_mem {d N : ℕ} {y : Fin d → ℝ} (hy : ∀ i, |y i| ≤ 1)
    {α : Fin d → ℕ} (hα : α ∉ cepsTaylorBox d N) :
    |cepsMonomial y α| ≤ (∑ i, |y i|) ^ (N + 1) := by
  classical
  rw [mem_cepsTaylorBox] at hα
  push Not at hα
  obtain ⟨i, hi⟩ := hα
  unfold cepsMonomial
  rw [abs_prod, ← mul_prod_erase univ _ (mem_univ i)]
  have hrest : ∏ j ∈ univ.erase i, |y j ^ α j| ≤ 1 :=
    prod_le_one (fun _ _ => abs_nonneg _) fun j _ => by
      rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) (hy j)
  have hyi : |y i| ≤ ∑ j, |y j| :=
    single_le_sum (f := fun j => |y j|) (fun j _ => abs_nonneg _) (mem_univ i)
  calc |y i ^ α i| * ∏ j ∈ univ.erase i, |y j ^ α j| ≤ |y i ^ α i| * 1 :=
        mul_le_mul_of_nonneg_left hrest (abs_nonneg _)
    _ = |y i| ^ α i := by rw [mul_one, abs_pow]
    _ ≤ |y i| ^ (N + 1) := pow_le_pow_of_le_one (abs_nonneg _) (hy i) hi
    _ ≤ (∑ j, |y j|) ^ (N + 1) := pow_le_pow_left₀ (abs_nonneg _) hyi _

/-! ## Cauchy products of coefficient families -/

/-- The Cauchy product of two coefficient families. -/
def cepsBoxMul {R : Type*} [CommSemiring R] {d : ℕ} (T S : (Fin d → ℕ) → R)
    (γ : Fin d → ℕ) : R :=
  ∑ β ∈ cepsLowerBox γ, T β * S (γ - β)

/-- Reindexing a product of two box sums by total multi-index. -/
theorem sum_box_mul_sum_box {M : Type*} [AddCommMonoid M] {d N : ℕ}
    (A : (Fin d → ℕ) → (Fin d → ℕ) → M) :
    ∑ α ∈ cepsTaylorBox d N, ∑ β ∈ cepsTaylorBox d N, A α β =
      ∑ γ ∈ cepsTaylorBox d N, ∑ β ∈ cepsLowerBox γ, A β (γ - β) +
        ∑ x ∈ (cepsTaylorBox d N ×ˢ cepsTaylorBox d N).filter
          (fun x => x.1 + x.2 ∉ cepsTaylorBox d N), A x.1 x.2 := by
  classical
  rw [← sum_product' (f := A), ← sum_filter_add_sum_filter_not
    (cepsTaylorBox d N ×ˢ cepsTaylorBox d N) (fun x => x.1 + x.2 ∈ cepsTaylorBox d N)]
  congr 1
  rw [sum_sigma']
  refine sum_nbij' (fun x => ⟨x.1 + x.2, x.1⟩) (fun x => (x.2, x.1 - x.2)) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    simp only [mem_filter, mem_product] at hx
    simp only [mem_sigma]
    refine ⟨hx.2, mem_cepsLowerBox.mpr fun i => ?_⟩
    simp
  · intro x hx
    simp only [mem_sigma, mem_cepsLowerBox] at hx
    obtain ⟨hγ, hβ⟩ := hx
    have hsum : x.2 + (x.1 - x.2) = x.1 := by
      funext i; simp [Nat.add_sub_cancel' (hβ i)]
    simp only [mem_filter, mem_product]
    refine ⟨⟨cepsLowerBox_subset hγ (mem_cepsLowerBox.mpr hβ), ?_⟩, by rw [hsum]; exact hγ⟩
    rw [mem_cepsTaylorBox] at hγ ⊢
    exact fun i => (Nat.sub_le _ _).trans (hγ i)
  · intro x _
    exact Prod.ext rfl (funext fun i => by simp)
  · intro x hx
    simp only [mem_sigma, mem_cepsLowerBox] at hx
    have hsum : x.2 + (x.1 - x.2) = x.1 := by
      funext i; simp [Nat.add_sub_cancel' (hx.2 i)]
    simp [hsum]
  · intro x _
    have h : x.1 + x.2 - x.1 = x.2 := funext fun i => by simp
    simp only [h]

/-- The pointwise product estimate: the product of two numbers minus the box polynomial of the
Cauchy product, through the box errors of the factors. -/
theorem norm_mul_sub_boxPoly_le {d N : ℕ} (T S : (Fin d → ℕ) → ℂ) {y : Fin d → ℝ}
    (hy : ∀ i, |y i| ≤ 1) (a b : ℂ) :
    ‖a * b - ∑ γ ∈ cepsTaylorBox d N, cepsBoxMul T S γ * (cepsMonomial y γ : ℂ)‖ ≤
      ‖a - ∑ α ∈ cepsTaylorBox d N, T α * (cepsMonomial y α : ℂ)‖ *
          ((∑ β ∈ cepsTaylorBox d N, ‖S β‖) +
            ‖b - ∑ β ∈ cepsTaylorBox d N, S β * (cepsMonomial y β : ℂ)‖) +
        (∑ α ∈ cepsTaylorBox d N, ‖T α‖) *
          ‖b - ∑ β ∈ cepsTaylorBox d N, S β * (cepsMonomial y β : ℂ)‖ +
        (∑ α ∈ cepsTaylorBox d N, ‖T α‖) * (∑ β ∈ cepsTaylorBox d N, ‖S β‖) *
          (∑ i, |y i|) ^ (N + 1) := by
  classical
  set P := ∑ α ∈ cepsTaylorBox d N, T α * (cepsMonomial y α : ℂ) with hP
  set Q := ∑ β ∈ cepsTaylorBox d N, S β * (cepsMonomial y β : ℂ) with hQ
  have hmono : ∀ α, ‖(cepsMonomial y α : ℂ)‖ ≤ 1 := fun α => by
    rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_cepsMonomial_le_one hy α
  have hPb : ‖P‖ ≤ ∑ α ∈ cepsTaylorBox d N, ‖T α‖ := by
    refine (norm_sum_le _ _).trans (sum_le_sum fun α _ => ?_)
    rw [norm_mul]; exact mul_le_of_le_one_right (norm_nonneg _) (hmono α)
  have hQb : ‖Q‖ ≤ ∑ β ∈ cepsTaylorBox d N, ‖S β‖ := by
    refine (norm_sum_le _ _).trans (sum_le_sum fun β _ => ?_)
    rw [norm_mul]; exact mul_le_of_le_one_right (norm_nonneg _) (hmono β)
  have hb : ‖b‖ ≤ (∑ β ∈ cepsTaylorBox d N, ‖S β‖) + ‖b - Q‖ := by
    calc ‖b‖ = ‖Q + (b - Q)‖ := by ring_nf
      _ ≤ ‖Q‖ + ‖b - Q‖ := norm_add_le _ _
      _ ≤ _ := by linarith
  -- the product of the two box polynomials
  have hPQ : P * Q = ∑ γ ∈ cepsTaylorBox d N, cepsBoxMul T S γ * (cepsMonomial y γ : ℂ) +
      ∑ x ∈ (cepsTaylorBox d N ×ˢ cepsTaylorBox d N).filter
        (fun x => x.1 + x.2 ∉ cepsTaylorBox d N),
        T x.1 * S x.2 * (cepsMonomial y (x.1 + x.2) : ℂ) := by
    rw [hP, hQ, sum_mul_sum]
    have hA : ∀ α β, T α * (cepsMonomial y α : ℂ) * (S β * (cepsMonomial y β : ℂ)) =
        T α * S β * (cepsMonomial y (α + β) : ℂ) := fun α β => by
      rw [cepsMonomial_add]; push_cast; ring
    simp_rw [hA]
    rw [sum_box_mul_sum_box (A := fun α β => T α * S β * (cepsMonomial y (α + β) : ℂ))]
    congr 1
    refine sum_congr rfl fun γ hγ => ?_
    unfold cepsBoxMul
    rw [sum_mul]
    refine sum_congr rfl fun β hβ => ?_
    have hsum : β + (γ - β) = γ := by
      funext i; simp [Nat.add_sub_cancel' (mem_cepsLowerBox.mp hβ i)]
    rw [hsum]
  have hbad : ‖∑ x ∈ (cepsTaylorBox d N ×ˢ cepsTaylorBox d N).filter
        (fun x => x.1 + x.2 ∉ cepsTaylorBox d N),
        T x.1 * S x.2 * (cepsMonomial y (x.1 + x.2) : ℂ)‖ ≤
      (∑ α ∈ cepsTaylorBox d N, ‖T α‖) * (∑ β ∈ cepsTaylorBox d N, ‖S β‖) *
        (∑ i, |y i|) ^ (N + 1) := by
    refine (norm_sum_le _ _).trans ?_
    have hle : ∀ x ∈ (cepsTaylorBox d N ×ˢ cepsTaylorBox d N).filter
        (fun x => x.1 + x.2 ∉ cepsTaylorBox d N),
        ‖T x.1 * S x.2 * (cepsMonomial y (x.1 + x.2) : ℂ)‖ ≤
          ‖T x.1‖ * ‖S x.2‖ * (∑ i, |y i|) ^ (N + 1) := by
      intro x hx
      rw [mem_filter] at hx
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (abs_cepsMonomial_le_of_not_mem hy hx.2) (by positivity)
    refine (sum_le_sum hle).trans ?_
    rw [← sum_mul, sum_mul_sum, ← sum_product']
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => by positivity
  have hsplit : a * b - ∑ γ ∈ cepsTaylorBox d N, cepsBoxMul T S γ * (cepsMonomial y γ : ℂ) =
      (a - P) * b + P * (b - Q) + (∑ x ∈ (cepsTaylorBox d N ×ˢ cepsTaylorBox d N).filter
        (fun x => x.1 + x.2 ∉ cepsTaylorBox d N),
        T x.1 * S x.2 * (cepsMonomial y (x.1 + x.2) : ℂ)) := by
    rw [show a * b - ∑ γ ∈ cepsTaylorBox d N, cepsBoxMul T S γ * (cepsMonomial y γ : ℂ) =
      (a - P) * b + P * (b - Q) +
        (P * Q - ∑ γ ∈ cepsTaylorBox d N, cepsBoxMul T S γ * (cepsMonomial y γ : ℂ)) by ring,
      hPQ, add_sub_cancel_left]
  rw [hsplit]
  refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_)) hbad)
  · rw [norm_mul]; exact mul_le_mul_of_nonneg_left hb (norm_nonneg _)
  · rw [norm_mul]; exact mul_le_mul_of_nonneg_right hPb (norm_nonneg _)

end

end PGM
