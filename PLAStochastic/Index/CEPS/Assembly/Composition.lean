import PLAStochastic.Index.CEPS.Assembly.Interfaces
import PLAStochastic.Index.CEPS.Family.Reduction
import PLAStochastic.ForMathlib.Analysis.Asymptotics.SeriesExpansion
import PLAStochastic.ForMathlib.Analysis.Fourier.InverseAsymptotics

/-!
# Track F: composing the jet expansions with the Taylor expansions of the coefficients

Along a family whose jet displacements `y_i(ε) = J_i(ν_ε) - J_i(Λ)` expand with the formal
series `Y_i = ∑_{n ≥ 1} jetCoeff i n g · Xⁿ`, the finite Taylor expansions of T3 give

* `Φ_k(u; J ν_ε) = ∑_{j ≤ N} h^j A_{k,j}(u) + O(h^{N+1} (1+|u|)^d)` uniformly in `u`, with
  `A_{k,j}(u) = ∑_α T_{k,α}(u) [X^j] ∏ᵢ Yᵢ^{αᵢ}` (`phiComp`);
* the same for the scalar coefficients `c_k` (`scalComp`).

Collecting powers of `h` gives the output characteristic coefficients
`a_n = ∑_{k ≤ n} A_{k,n-k}` with `A_{0,0} = φ_Λ` (`outCoeff`). Since `Φ_0` does not depend on the
jets, `a_n` reads only the jet coefficients of order `≤ n - 1`, hence only `g 1, …, g (n-1)`:
the output coefficient map is triangular (`cepsTriangular_outDensityCoeff`).
-/

namespace PGM

noncomputable section

open MeasureTheory Filter Topology Finset PowerSeries

/-! ## Orders uniform in the frequency -/

theorem one_le_one_add_abs (u : ℝ) : (1 : ℝ) ≤ 1 + |u| := by linarith [abs_nonneg u]

theorem one_add_abs_pow_le {u : ℝ} {d d' : ℕ} (h : d ≤ d') : (1 + |u|) ^ d ≤ (1 + |u|) ^ d' :=
  pow_le_pow_right₀ (one_le_one_add_abs u) h

/-- `E ε u = O(h^n (1+|u|)^d)` uniformly in the frequency `u`. -/
def UnifPolyOrder (E : ℝ → ℝ → ℂ) (n : ℕ) : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∃ d : ℕ, ∀ᶠ eps in atTop, ∀ u : ℝ,
    ‖E eps u‖ ≤ K * (1 + |u|) ^ d * (eps⁻¹) ^ n

theorem unifPolyOrder_zero (n : ℕ) : UnifPolyOrder (fun _ _ => 0) n :=
  ⟨0, le_rfl, 0, Eventually.of_forall fun _ _ => by simp⟩

theorem UnifPolyOrder.congr {E E' : ℝ → ℝ → ℂ} {n : ℕ} (h : UnifPolyOrder E n)
    (he : ∀ᶠ eps in atTop, ∀ u, E eps u = E' eps u) : UnifPolyOrder E' n := by
  obtain ⟨K, hK, d, hd⟩ := h
  refine ⟨K, hK, d, ?_⟩
  filter_upwards [hd, he] with eps h1 h2 u
  rw [← h2 u]
  exact h1 u

theorem UnifPolyOrder.add {E E' : ℝ → ℝ → ℂ} {n : ℕ} (h : UnifPolyOrder E n)
    (h' : UnifPolyOrder E' n) : UnifPolyOrder (fun eps u => E eps u + E' eps u) n := by
  obtain ⟨K, hK, d, hd⟩ := h
  obtain ⟨K', hK', d', hd'⟩ := h'
  refine ⟨K + K', by positivity, max d d', ?_⟩
  filter_upwards [hd, hd', eventually_gt_atTop (0 : ℝ)] with eps h1 h2 hpos u
  have hi : 0 ≤ (eps⁻¹) ^ n := by positivity
  have hp : (1 + |u|) ^ d ≤ (1 + |u|) ^ max d d' := one_add_abs_pow_le (le_max_left _ _)
  have hp' : (1 + |u|) ^ d' ≤ (1 + |u|) ^ max d d' := one_add_abs_pow_le (le_max_right _ _)
  calc
    ‖E eps u + E' eps u‖ ≤ ‖E eps u‖ + ‖E' eps u‖ := norm_add_le _ _
    _ ≤ K * (1 + |u|) ^ d * (eps⁻¹) ^ n + K' * (1 + |u|) ^ d' * (eps⁻¹) ^ n :=
      add_le_add (h1 u) (h2 u)
    _ ≤ K * (1 + |u|) ^ max d d' * (eps⁻¹) ^ n + K' * (1 + |u|) ^ max d d' * (eps⁻¹) ^ n := by
      gcongr
    _ = (K + K') * (1 + |u|) ^ max d d' * (eps⁻¹) ^ n := by ring

theorem UnifPolyOrder.neg {E : ℝ → ℝ → ℂ} {n : ℕ} (h : UnifPolyOrder E n) :
    UnifPolyOrder (fun eps u => -E eps u) n := by
  obtain ⟨K, hK, d, hd⟩ := h
  exact ⟨K, hK, d, hd.mono fun eps he u => by rw [norm_neg]; exact he u⟩

theorem UnifPolyOrder.sub {E E' : ℝ → ℝ → ℂ} {n : ℕ} (h : UnifPolyOrder E n)
    (h' : UnifPolyOrder E' n) : UnifPolyOrder (fun eps u => E eps u - E' eps u) n := by
  simpa only [sub_eq_add_neg] using h.add h'.neg

theorem UnifPolyOrder.sum {ι : Type*} (s : Finset ι) {E : ι → ℝ → ℝ → ℂ} {n : ℕ}
    (h : ∀ i ∈ s, UnifPolyOrder (E i) n) :
    UnifPolyOrder (fun eps u => ∑ i ∈ s, E i eps u) n := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [sum_empty] using unifPolyOrder_zero n
  | insert a s ha ih =>
    simp only [sum_insert ha]
    exact (h a (mem_insert_self a s)).add (ih fun i hi => h i (mem_insert_of_mem hi))

/-- A real function of inverse order `m` times a polynomially bounded frequency function. -/
theorem UnifPolyOrder.of_real_mul {f : ℝ → ℝ} {T : ℝ → ℂ} {m : ℕ} (hf : IsInverseOrder f m)
    {B : ℝ} {d : ℕ} (hT : ∀ u, ‖T u‖ ≤ B * (1 + |u|) ^ d) :
    UnifPolyOrder (fun eps u => (f eps : ℂ) * T u) m := by
  obtain ⟨K, e0, hK, -, hb⟩ := hf.nonneg_witness
  have hB : 0 ≤ B := by
    have h0 := (norm_nonneg _).trans (hT 0)
    simpa only [abs_zero, add_zero, one_pow, mul_one] using h0
  refine ⟨K * B, mul_nonneg hK hB, d, eventually_atTop.mpr ⟨e0, fun eps he u => ?_⟩⟩
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc
    |f eps| * ‖T u‖ ≤ (K * (eps⁻¹) ^ m) * (B * (1 + |u|) ^ d) :=
      mul_le_mul (hb eps he) (hT u) (norm_nonneg _) ((abs_nonneg _).trans (hb eps he))
    _ = K * B * (1 + |u|) ^ d * (eps⁻¹) ^ m := by ring

/-- Multiplying by `h^k` raises the order by `k`. -/
theorem UnifPolyOrder.inv_pow_smul {E : ℝ → ℝ → ℂ} {n : ℕ} (h : UnifPolyOrder E n) (k : ℕ) :
    UnifPolyOrder (fun eps u => ((eps⁻¹) ^ k : ℝ) • E eps u) (k + n) := by
  obtain ⟨K, hK, d, hd⟩ := h
  refine ⟨K, hK, d, ?_⟩
  filter_upwards [hd, eventually_gt_atTop (0 : ℝ)] with eps he hpos u
  have hi : 0 ≤ (eps⁻¹) ^ k := by positivity
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hi, pow_add]
  calc
    (eps⁻¹) ^ k * ‖E eps u‖ ≤ (eps⁻¹) ^ k * (K * (1 + |u|) ^ d * (eps⁻¹) ^ n) :=
      mul_le_mul_of_nonneg_left (he u) hi
    _ = K * (1 + |u|) ^ d * ((eps⁻¹) ^ k * (eps⁻¹) ^ n) := by ring

theorem IsInverseOrder.sum {ι : Type*} (s : Finset ι) {f : ι → ℝ → ℝ} {n : ℕ}
    (h : ∀ i ∈ s, IsInverseOrder (f i) n) : IsInverseOrder (fun eps => ∑ i ∈ s, f i eps) n := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, 0, fun _ _ => by simp⟩
  | insert a s ha ih =>
    simp only [sum_insert ha]
    exact (h a (mem_insert_self a s)).add (ih fun i hi => h i (mem_insert_of_mem hi))

theorem IsInverseOrder.abs {f : ℝ → ℝ} {n : ℕ} (h : IsInverseOrder f n) :
    IsInverseOrder (fun eps => |f eps|) n := by
  simpa only [IsInverseOrder, abs_abs] using h

theorem isInverseOrder_inv_pow (k : ℕ) : IsInverseOrder (fun eps => (eps⁻¹) ^ k) k := by
  refine ⟨1, 1, fun eps he => ?_⟩
  have hpos : 0 < eps := by linarith
  show |(eps⁻¹) ^ k| ≤ 1 * (eps⁻¹) ^ k
  rw [one_mul, abs_of_nonneg (by positivity)]

theorem HasInverseExpansionAtOrder.congr_coeff {f : ℝ → ℝ} {a b : ℕ → ℝ} {N : ℕ}
    (h : HasInverseExpansionAtOrder f a N) (hc : ∀ n ≤ N, a n = b n) :
    HasInverseExpansionAtOrder f b N := by
  obtain ⟨K, e0, hK⟩ := h
  refine ⟨K, e0, fun eps he => ?_⟩
  have hp : inversePolynomial b N eps = inversePolynomial a N eps :=
    sum_congr rfl fun n hn => by rw [hc n (by have := mem_range.mp hn; omega)]
  rw [hp]
  exact hK eps he

/-! ## Stretched-exponential bounds -/

theorem cepsStretchedWeight_mono {c c' : ℝ} {d d' : ℕ} (hc : c' ≤ c) (hd : d ≤ d') (u : ℝ) :
    cepsStretchedWeight c d u ≤ cepsStretchedWeight c' d' u := by
  unfold cepsStretchedWeight
  have hs : 0 ≤ Real.sqrt |u| := Real.sqrt_nonneg _
  exact mul_le_mul (one_add_abs_pow_le hd) (Real.exp_le_exp.mpr (by nlinarith))
    (Real.exp_pos _).le (by positivity)

theorem cepsStretchedWeight_le_poly {c : ℝ} (hc : 0 ≤ c) (d : ℕ) (u : ℝ) :
    cepsStretchedWeight c d u ≤ (1 + |u|) ^ d := by
  unfold cepsStretchedWeight
  have he : Real.exp (-c * Real.sqrt |u|) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [Real.sqrt_nonneg |u|])
  exact (mul_le_mul_of_nonneg_left he (by positivity)).trans_eq (mul_one _)

theorem cepsStretchedWeight_zero (c : ℝ) (d : ℕ) : cepsStretchedWeight c d 0 = 1 := by
  simp [cepsStretchedWeight]

/-- A frequency function bounded by a stretched-exponential weight. -/
def StretchedBounded (T : ℝ → ℂ) : Prop :=
  ∃ K c : ℝ, 0 < c ∧ ∃ d : ℕ, ∀ u, ‖T u‖ ≤ K * cepsStretchedWeight c d u

theorem StretchedBounded.exists_nonneg {T : ℝ → ℂ} (h : StretchedBounded T) :
    ∃ K c : ℝ, 0 ≤ K ∧ 0 < c ∧ ∃ d : ℕ, ∀ u, ‖T u‖ ≤ K * cepsStretchedWeight c d u := by
  obtain ⟨K, c, hc, d, hb⟩ := h
  have hK : 0 ≤ K := by
    have h0 := (norm_nonneg _).trans (hb 0)
    rwa [cepsStretchedWeight_zero, mul_one] at h0
  exact ⟨K, c, hK, hc, d, hb⟩

theorem stretchedBounded_zero : StretchedBounded (fun _ => 0) :=
  ⟨0, 1, one_pos, 0, fun u => by simp⟩

theorem StretchedBounded.add {T T' : ℝ → ℂ} (h : StretchedBounded T) (h' : StretchedBounded T') :
    StretchedBounded (fun u => T u + T' u) := by
  obtain ⟨K, c, hK, hc, d, hb⟩ := h.exists_nonneg
  obtain ⟨K', c', hK', hc', d', hb'⟩ := h'.exists_nonneg
  refine ⟨K + K', min c c', lt_min hc hc', max d d', fun u => ?_⟩
  have h1 := cepsStretchedWeight_mono (min_le_left c c') (le_max_left d d') u
  have h2 := cepsStretchedWeight_mono (min_le_right c c') (le_max_right d d') u
  calc
    ‖T u + T' u‖ ≤ ‖T u‖ + ‖T' u‖ := norm_add_le _ _
    _ ≤ K * cepsStretchedWeight c d u + K' * cepsStretchedWeight c' d' u := add_le_add (hb u) (hb' u)
    _ ≤ K * cepsStretchedWeight (min c c') (max d d') u +
        K' * cepsStretchedWeight (min c c') (max d d') u := by gcongr
    _ = _ := by ring

theorem StretchedBounded.const_mul {T : ℝ → ℂ} (h : StretchedBounded T) (z : ℂ) :
    StretchedBounded (fun u => z * T u) := by
  obtain ⟨K, c, hK, hc, d, hb⟩ := h.exists_nonneg
  refine ⟨‖z‖ * K, c, hc, d, fun u => ?_⟩
  rw [norm_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hb u) (norm_nonneg _)

theorem StretchedBounded.mul_const {T : ℝ → ℂ} (h : StretchedBounded T) (z : ℂ) :
    StretchedBounded (fun u => T u * z) := by
  simpa only [mul_comm] using h.const_mul z

theorem StretchedBounded.sum {ι : Type*} (s : Finset ι) {T : ι → ℝ → ℂ}
    (h : ∀ i ∈ s, StretchedBounded (T i)) : StretchedBounded (fun u => ∑ i ∈ s, T i u) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [sum_empty] using stretchedBounded_zero
  | insert a s ha ih =>
    simp only [sum_insert ha]
    exact (h a (mem_insert_self a s)).add (ih fun i hi => h i (mem_insert_of_mem hi))

/-- Stretched bounds are polynomial bounds. -/
theorem StretchedBounded.poly {T : ℝ → ℂ} (h : StretchedBounded T) :
    ∃ B : ℝ, ∃ d : ℕ, ∀ u, ‖T u‖ ≤ B * (1 + |u|) ^ d := by
  obtain ⟨K, c, hK, hc, d, hb⟩ := h.exists_nonneg
  exact ⟨K, d, fun u => (hb u).trans (mul_le_mul_of_nonneg_left
    (cepsStretchedWeight_le_poly hc.le d u) hK)⟩

/-- Finitely many stretched bounds share one rate. -/
theorem StretchedBounded.common_rate {ι : Type*} (s : Finset ι) {T : ι → ℝ → ℂ}
    (h : ∀ i ∈ s, StretchedBounded (T i)) :
    ∃ c : ℝ, 0 < c ∧ ∀ i ∈ s, ∃ B : ℝ, 0 ≤ B ∧ ∃ d : ℕ, ∀ u : ℝ,
      ‖T i u‖ ≤ B * (1 + |u|) ^ d * Real.exp (-c * Real.sqrt |u|) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_pos, fun i hi => absurd hi (Finset.notMem_empty i)⟩
  | insert a s ha ih =>
    obtain ⟨c₀, hc₀, hs⟩ := ih fun i hi => h i (mem_insert_of_mem hi)
    obtain ⟨K, c, hK, hc, d, hb⟩ := (h a (mem_insert_self a s)).exists_nonneg
    refine ⟨min c₀ c, lt_min hc₀ hc, fun i hi => ?_⟩
    have hex (c' : ℝ) (hc' : min c₀ c ≤ c') (u : ℝ) :
        Real.exp (-c' * Real.sqrt |u|) ≤ Real.exp (-(min c₀ c) * Real.sqrt |u|) :=
      Real.exp_le_exp.mpr (by nlinarith [Real.sqrt_nonneg |u|])
    rcases mem_insert.mp hi with rfl | hi
    · refine ⟨K, hK, d, fun u => (hb u).trans ?_⟩
      unfold cepsStretchedWeight
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_left (hex c (min_le_right _ _) u) (by positivity)
    · obtain ⟨B, hB, d', hb'⟩ := hs i hi
      refine ⟨B, hB, d', fun u => (hb' u).trans ?_⟩
      exact mul_le_mul_of_nonneg_left (hex c₀ (min_le_left _ _) u) (by positivity)

/-! ## The finite reindexing of a double sum -/

theorem sum_range_sum_range_sub {M : Type*} [AddCommMonoid M] (P : ℕ) (f : ℕ → ℕ → M) :
    ∑ k ∈ range (P + 1), ∑ j ∈ range (P + 1 - k), f k j =
      ∑ n ∈ range (P + 1), ∑ k ∈ range (n + 1), f k (n - k) := by
  induction P with
  | zero => simp
  | succ P ih =>
    rw [sum_range_succ (fun n => ∑ k ∈ range (n + 1), f k (n - k)) (P + 1), ← ih]
    have h1 : ∀ k ∈ range (P + 1 + 1), ∑ j ∈ range (P + 1 + 1 - k), f k j =
        ∑ j ∈ range (P + 1 - k), f k j + f k (P + 1 - k) := by
      intro k hk
      have hk' : P + 1 + 1 - k = (P + 1 - k) + 1 := by have := mem_range.mp hk; omega
      rw [hk', sum_range_succ]
    rw [sum_congr rfl h1, sum_add_distrib,
      sum_range_succ (fun k => ∑ j ∈ range (P + 1 - k), f k j) (P + 1)]
    simp

/-! ## Jet series and the composed coefficients -/

namespace CepsJetData

variable (J : CepsJetData)

/-- The jet series of coordinate `i` along density coefficients `g`, without constant term. -/
def jetSeries (i : ℕ) (g : ℕ → ℝ → ℝ) : PowerSeries ℝ :=
  PowerSeries.mk fun n => if n = 0 then 0 else J.jetCoeff i n g

/-- The series of the Taylor monomial `y^α` at order `k`. -/
def monoSeries (k : ℕ) (g : ℕ → ℝ → ℝ) (α : Fin (J.dim k) → ℕ) : PowerSeries ℝ :=
  ∏ i : Fin (J.dim k), J.jetSeries i g ^ α i

/-- `A_{k,j}(u) = ∑_{α} T_{k,α}(u) [X^j] y^α`: the `h^j` coefficient of `Φ_k(u; J ν_ε)`. -/
def phiComp (k j : ℕ) (g : ℕ → ℝ → ℝ) (u : ℝ) : ℂ :=
  ∑ α ∈ cepsTaylorBox (J.dim k) j, J.phiTaylor k α u * ((coeff j (J.monoSeries k g α) : ℝ) : ℂ)

/-- The `h^j` coefficient of `c_k(J ν_ε)`. -/
def scalComp (k j : ℕ) (g : ℕ → ℝ → ℝ) : ℝ :=
  ∑ α ∈ cepsTaylorBox (J.dim k) j, J.scalTaylor k α * coeff j (J.monoSeries k g α)

/-- The `h^j` coefficient of `Φ_k(u; J ν_ε)`, with `Φ_0 = φ_Λ`. -/
def phiTerm (k j : ℕ) (g : ℕ → ℝ → ℝ) (u : ℝ) : ℂ :=
  if k = 0 then (if j = 0 then cepsLambdaChar u else 0) else J.phiComp k j g u

/-- The output characteristic coefficients `a_n = ∑_{k ≤ n} A_{k,n-k}`. -/
def outCoeff (g : ℕ → ℝ → ℝ) (n : ℕ) (u : ℝ) : ℂ :=
  ∑ k ∈ range (n + 1), J.phiTerm k (n - k) g u

/-- The scalar coefficients of `lawC / ε²`. -/
def scalCoeff (g : ℕ → ℝ → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ range (n + 1), J.scalComp k (n - k) g

/-- The output density coefficient map `G`. -/
def outDensityCoeff (g : ℕ → ℝ → ℝ) (n : ℕ) : ℝ → ℝ :=
  angularRealInverse (J.outCoeff g n)

theorem constantCoeff_jetSeries (i : ℕ) (g : ℕ → ℝ → ℝ) :
    constantCoeff (J.jetSeries i g) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, jetSeries, coeff_mk, if_pos rfl]

theorem cepsTaylorBox_mono {d j N : ℕ} (h : j ≤ N) : cepsTaylorBox d j ⊆ cepsTaylorBox d N := by
  intro α hα
  simp only [cepsTaylorBox, Fintype.mem_piFinset, mem_range] at hα ⊢
  exact fun i => (hα i).trans_le (by omega)

theorem coeff_monoSeries_eq_zero {k j : ℕ} (g : ℕ → ℝ → ℝ) {α : Fin (J.dim k) → ℕ}
    (hα : α ∉ cepsTaylorBox (J.dim k) j) : coeff j (J.monoSeries k g α) = 0 := by
  simp only [cepsTaylorBox, Fintype.mem_piFinset, mem_range, not_forall, not_lt] at hα
  obtain ⟨i, hi⟩ := hα
  exact coeff_prod_pow_eq_zero univ (fun i : Fin (J.dim k) => J.jetSeries i g) α
    (fun i _ => J.constantCoeff_jetSeries i g) (mem_univ i) (by omega)

theorem sum_box_eq_phiComp {k j N : ℕ} (hj : j ≤ N) (g : ℕ → ℝ → ℝ) (u : ℝ) :
    ∑ α ∈ cepsTaylorBox (J.dim k) N, J.phiTaylor k α u * ((coeff j (J.monoSeries k g α) : ℝ) : ℂ) =
      J.phiComp k j g u := by
  refine (sum_subset (cepsTaylorBox_mono hj) fun α _ hα => ?_).symm
  rw [J.coeff_monoSeries_eq_zero g hα, Complex.ofReal_zero, mul_zero]

theorem sum_box_eq_scalComp {k j N : ℕ} (hj : j ≤ N) (g : ℕ → ℝ → ℝ) :
    ∑ α ∈ cepsTaylorBox (J.dim k) N, J.scalTaylor k α * coeff j (J.monoSeries k g α) =
      J.scalComp k j g := by
  refine (sum_subset (cepsTaylorBox_mono hj) fun α _ hα => ?_).symm
  rw [J.coeff_monoSeries_eq_zero g hα, mul_zero]

/-! ### Triangularity -/

theorem coeff_jetSeries_congr {J : CepsJetData} (hJF : CepsJF J) {g g' : ℕ → ℝ → ℝ} {n : ℕ}
    (hgg : ∀ j, 1 ≤ j → j ≤ n → g j = g' j) (i : ℕ) {m : ℕ} (hm : m ≤ n) :
    coeff m (J.jetSeries i g) = coeff m (J.jetSeries i g') := by
  simp only [jetSeries, coeff_mk]
  split_ifs
  · rfl
  · exact hJF.triangular i m g g' fun j hj1 hj2 => hgg j hj1 (hj2.trans hm)

theorem phiComp_congr {J : CepsJetData} (hJF : CepsJF J) {g g' : ℕ → ℝ → ℝ} {j : ℕ}
    (hgg : ∀ i, 1 ≤ i → i ≤ j → g i = g' i) (k : ℕ) (u : ℝ) :
    J.phiComp k j g u = J.phiComp k j g' u := by
  refine sum_congr rfl fun α _ => ?_
  rw [monoSeries, monoSeries, coeff_prod_pow_congr univ _ _ α
    (fun i _ m hm => coeff_jetSeries_congr hJF hgg i hm)]

theorem outCoeff_congr {J : CepsJetData} (hJF : CepsJF J) {g g' : ℕ → ℝ → ℝ} {n : ℕ}
    (hgg : ∀ i, 1 ≤ i → i < n → g i = g' i) : J.outCoeff g n = J.outCoeff g' n := by
  funext u
  refine sum_congr rfl fun k hk => ?_
  unfold phiTerm
  by_cases h0 : k = 0
  · simp only [if_pos h0]
  · simp only [if_neg h0]
    refine phiComp_congr (j := n - k) hJF (fun i hi1 hi2 => hgg i hi1 ?_) k u
    omega

end CepsJetData

/-- **Triangularity.** The output density coefficient of order `n` depends only on the input
coefficients of orders `1, …, n - 1`, because `Φ_0` does not depend on the jets. -/
theorem cepsTriangular_outDensityCoeff {J : CepsJetData} (hJF : CepsJF J) :
    CepsTriangular J.outDensityCoeff := by
  intro g g' n hgg
  unfold CepsJetData.outDensityCoeff
  rw [CepsJetData.outCoeff_congr hJF hgg]

/-! ## Expansions along a family -/

namespace CepsJetData

variable {J : CepsJetData}

/-- The jet expansion along an expanding family starts at the reference jet `J Λ`. -/
theorem jetCoeff_zero (hJF : CepsJF J) (i : ℕ) (g : ℕ → ℝ → ℝ) :
    J.jetCoeff i 0 g = J.ref i := by
  obtain ⟨m, hm⟩ := hJF.expansion i 0
  obtain ⟨η, hη, hΛ⟩ := exists_cepsSobolevClass_cepsLambdaDensity m
  obtain ⟨D, θ, hD, hθ, hreg⟩ := exists_regLaw_cepsLambda
  have hev : CepsEventuallyRegular (fun _ => cepsLambda) :=
    ⟨D, θ, _, _, hD, hθ, BrownianAffine.optimalDispersionConstant_pos, le_rfl,
      Eventually.of_forall fun _ => hreg⟩
  have h := hm (fun _ => cepsLambda) (fun _ _ => 0) η hev hη (cepsFamilyExpansion_cepsLambda hΛ 0)
  have hlim := HasInverseExpansionAtOrder.tendsto_zero_order h
  have h0 : J.jetCoeff i 0 (fun _ _ => 0) = J.ref i :=
    tendsto_nhds_unique hlim tendsto_const_nhds
  rw [← h0]
  exact hJF.triangular i 0 g _ fun j hj1 hj2 => by omega

/-- JF in series form: the jet displacements expand with the jet series. -/
theorem jetSeries_expansion (hJF : CepsJF J) {ν : ℝ → ProbabilityMeasure ℝ}
    {g : ℕ → ℝ → ℝ} {i P : ℕ}
    (h : HasInverseExpansionAtOrder (fun eps => J.jet (ν eps) i) (fun n => J.jetCoeff i n g) P) :
    HasSeriesExpansionAtOrder (fun eps => J.jet (ν eps) i - J.ref i) (J.jetSeries i g) P := by
  have hs : HasSeriesExpansionAtOrder (fun eps => J.jet (ν eps) i)
      (PowerSeries.mk fun n => J.jetCoeff i n g) P := by
    simpa only [HasSeriesExpansionAtOrder, coeff_mk] using h
  refine (hs.sub (hasSeriesExpansionAtOrder_const (J.ref i) P)).congr_series fun n _ => ?_
  simp only [map_sub, coeff_mk, coeff_C, jetSeries]
  split_ifs with hn
  · subst hn; rw [jetCoeff_zero hJF, sub_self]
  · rw [sub_zero]

/-- Smallness of the displacement along an expanding family. -/
theorem disp_eventually_small {k : ℕ} {ν : ℝ → ProbabilityMeasure ℝ} {g : ℕ → ℝ → ℝ} {N : ℕ}
    (hy : ∀ i : Fin (J.dim k),
      HasSeriesExpansionAtOrder (fun eps => J.disp k (J.jet (ν eps)) i) (J.jetSeries i g) N)
    {ρ : ℝ} (hρ : 0 < ρ) : ∀ᶠ eps in atTop, ∀ i, |J.disp k (J.jet (ν eps)) i| ≤ ρ := by
  rw [eventually_all]
  intro i
  have ht := ((hy i).isInverseOrder_one (J.constantCoeff_jetSeries i g)).tendsto_zero one_pos
  have hev := (Metric.tendsto_nhds.mp ht) ρ hρ
  filter_upwards [hev] with eps he
  rw [Real.dist_eq, sub_zero] at he
  exact he.le

theorem dispSize_pow_isInverseOrder {k : ℕ} {ν : ℝ → ProbabilityMeasure ℝ}
    {g : ℕ → ℝ → ℝ} {N : ℕ}
    (hy : ∀ i : Fin (J.dim k),
      HasSeriesExpansionAtOrder (fun eps => J.disp k (J.jet (ν eps)) i) (J.jetSeries i g) N)
    (M : ℕ) : IsInverseOrder (fun eps => J.dispSize k (J.jet (ν eps)) ^ M) M := by
  have h1 : IsInverseOrder (fun eps => J.dispSize k (J.jet (ν eps))) 1 :=
    IsInverseOrder.sum univ fun i _ =>
      ((hy i).isInverseOrder_one (J.constantCoeff_jetSeries i g)).abs
  simpa only [one_mul] using h1.pow M

/-- The Taylor monomials along the family expand with the monomial series. -/
theorem monomial_expansion {k : ℕ} {ν : ℝ → ProbabilityMeasure ℝ} {g : ℕ → ℝ → ℝ} {N : ℕ}
    (hy : ∀ i : Fin (J.dim k),
      HasSeriesExpansionAtOrder (fun eps => J.disp k (J.jet (ν eps)) i) (J.jetSeries i g) N)
    (α : Fin (J.dim k) → ℕ) :
    HasSeriesExpansionAtOrder (fun eps => cepsMonomial (J.disp k (J.jet (ν eps))) α)
      (J.monoSeries k g α) N := by
  unfold cepsMonomial monoSeries
  exact HasSeriesExpansionAtOrder.prod univ fun i _ => (hy i).pow (α i)

/-- **Composition for `Φ_k`, `k ≥ 1`.** -/
theorem phi_expansion_along (hT3 : CepsT3 J) {k : ℕ} (hk : 1 ≤ k)
    {ν : ℝ → ProbabilityMeasure ℝ} {g : ℕ → ℝ → ℝ} {N : ℕ}
    (hy : ∀ i : Fin (J.dim k),
      HasSeriesExpansionAtOrder (fun eps => J.disp k (J.jet (ν eps)) i) (J.jetSeries i g) N) :
    UnifPolyOrder (fun eps u => J.phi k u (J.jet (ν eps)) -
      ∑ j ∈ range (N + 1), ((eps⁻¹) ^ j : ℝ) • J.phiComp k j g u) (N + 1) := by
  obtain ⟨ρ, K, c, hρ, hc, d, hrem⟩ := hT3.phi_remainder k hk N
  -- the Taylor remainder
  have h1 : UnifPolyOrder (fun eps u =>
      J.phi k u (J.jet (ν eps)) - J.phiTaylorPoly k N u (J.jet (ν eps))) (N + 1) := by
    obtain ⟨L, e0, hL, -, hb⟩ := (dispSize_pow_isInverseOrder hy (N + 1)).nonneg_witness
    refine ⟨|K| * L, by positivity, d, ?_⟩
    filter_upwards [disp_eventually_small hy hρ, eventually_ge_atTop e0] with eps hs he u
    have hr := hrem u (J.jet (ν eps)) hs
    have hsz : 0 ≤ J.dispSize k (J.jet (ν eps)) :=
      sum_nonneg fun _ _ => abs_nonneg _
    have hbe := hb eps he
    rw [abs_of_nonneg (by positivity)] at hbe
    calc
      _ ≤ K * cepsStretchedWeight c d u * J.dispSize k (J.jet (ν eps)) ^ (N + 1) := hr
      _ ≤ |K| * (1 + |u|) ^ d * (L * (eps⁻¹) ^ (N + 1)) := by
        have hw := cepsStretchedWeight_le_poly hc.le d u
        have hw0 := cepsStretchedWeight_nonneg c d u
        calc
          K * cepsStretchedWeight c d u * J.dispSize k (J.jet (ν eps)) ^ (N + 1) ≤
              |K| * cepsStretchedWeight c d u * J.dispSize k (J.jet (ν eps)) ^ (N + 1) := by
            gcongr
            exact le_abs_self K
          _ ≤ |K| * (1 + |u|) ^ d * (L * (eps⁻¹) ^ (N + 1)) := by gcongr
      _ = |K| * L * (1 + |u|) ^ d * (eps⁻¹) ^ (N + 1) := by ring
  -- the Taylor polynomial against the composed coefficients
  have hcomp (eps u : ℝ) : ∑ j ∈ range (N + 1), ((eps⁻¹) ^ j : ℝ) • J.phiComp k j g u =
      ∑ α ∈ cepsTaylorBox (J.dim k) N, J.phiTaylor k α u *
        ((inversePolynomial (fun j => coeff j (J.monoSeries k g α)) N eps : ℝ) : ℂ) := by
    calc
      _ = ∑ j ∈ range (N + 1), ∑ α ∈ cepsTaylorBox (J.dim k) N,
          ((eps⁻¹) ^ j : ℝ) • (J.phiTaylor k α u * ((coeff j (J.monoSeries k g α) : ℝ) : ℂ)) := by
        refine sum_congr rfl fun j hj => ?_
        rw [← J.sum_box_eq_phiComp (N := N) (by have := mem_range.mp hj; omega) g u, smul_sum]
      _ = ∑ α ∈ cepsTaylorBox (J.dim k) N, ∑ j ∈ range (N + 1),
          ((eps⁻¹) ^ j : ℝ) • (J.phiTaylor k α u * ((coeff j (J.monoSeries k g α) : ℝ) : ℂ)) :=
        sum_comm
      _ = _ := by
        refine sum_congr rfl fun α _ => ?_
        rw [inversePolynomial, Complex.ofReal_sum, mul_sum]
        refine sum_congr rfl fun j _ => ?_
        rw [Complex.real_smul]
        push_cast
        ring
  have h2 : UnifPolyOrder (fun eps u => J.phiTaylorPoly k N u (J.jet (ν eps)) -
      ∑ j ∈ range (N + 1), ((eps⁻¹) ^ j : ℝ) • J.phiComp k j g u) (N + 1) := by
    have hsum : UnifPolyOrder (fun eps u => ∑ α ∈ cepsTaylorBox (J.dim k) N,
        ((cepsMonomial (J.disp k (J.jet (ν eps))) α -
          inversePolynomial (fun j => coeff j (J.monoSeries k g α)) N eps : ℝ) : ℂ) *
          J.phiTaylor k α u) (N + 1) := by
      refine UnifPolyOrder.sum _ fun α _ => ?_
      obtain ⟨B, dB, hB⟩ := StretchedBounded.poly (hT3.phiTaylor_bound k hk α)
      exact UnifPolyOrder.of_real_mul (monomial_expansion hy α) hB
    refine hsum.congr (Eventually.of_forall fun eps u => ?_)
    rw [hcomp, phiTaylorPoly, ← sum_sub_distrib]
    refine sum_congr rfl fun α _ => ?_
    push_cast
    ring
  refine (h1.add h2).congr (Eventually.of_forall fun eps u => ?_)
  ring

/-- **Composition for `c_k`.** -/
theorem scal_expansion_along (hT3 : CepsT3 J) (k : ℕ) {ν : ℝ → ProbabilityMeasure ℝ}
    {g : ℕ → ℝ → ℝ} {N : ℕ}
    (hy : ∀ i : Fin (J.dim k),
      HasSeriesExpansionAtOrder (fun eps => J.disp k (J.jet (ν eps)) i) (J.jetSeries i g) N) :
    HasInverseExpansionAtOrder (fun eps => J.scal k (J.jet (ν eps))) (fun j => J.scalComp k j g)
      N := by
  obtain ⟨ρ, K, hρ, hrem⟩ := hT3.scal_remainder k N
  have hpoly : HasSeriesExpansionAtOrder (fun eps => J.scalTaylorPoly k N (J.jet (ν eps)))
      (∑ α ∈ cepsTaylorBox (J.dim k) N, PowerSeries.C (J.scalTaylor k α) * J.monoSeries k g α)
      N :=
    HasSeriesExpansionAtOrder.sum _ fun α _ => (monomial_expansion hy α).const_mul _
  have hpoly' : HasInverseExpansionAtOrder (fun eps => J.scalTaylorPoly k N (J.jet (ν eps)))
      (fun j => J.scalComp k j g) N := by
    refine HasInverseExpansionAtOrder.congr_coeff hpoly fun n hn => ?_
    rw [map_sum, ← J.sum_box_eq_scalComp hn g]
    exact sum_congr rfl fun α _ => coeff_C_mul _ _ _
  refine hpoly'.transfer ?_
  obtain ⟨L, e0, hL, -, hb⟩ := (dispSize_pow_isInverseOrder hy (N + 1)).nonneg_witness
  obtain ⟨e1, he1⟩ := eventually_atTop.mp (disp_eventually_small hy hρ)
  refine ⟨|K| * L, max e0 e1, fun eps he => ?_⟩
  have hr := hrem (J.jet (ν eps)) (he1 eps ((le_max_right _ _).trans he))
  have hbe := hb eps ((le_max_left _ _).trans he)
  have hsz : 0 ≤ J.dispSize k (J.jet (ν eps)) := sum_nonneg fun _ _ => abs_nonneg _
  rw [abs_of_nonneg (by positivity)] at hbe
  calc
    _ ≤ K * J.dispSize k (J.jet (ν eps)) ^ (N + 1) := hr
    _ ≤ |K| * J.dispSize k (J.jet (ν eps)) ^ (N + 1) := by gcongr; exact le_abs_self K
    _ ≤ |K| * (L * (eps⁻¹) ^ (N + 1)) := by gcongr
    _ = |K| * L * (eps⁻¹) ^ (N + 1) := by ring

/-- **The output characteristic expansion.** Summing the compositions over `k ≤ P`. -/
theorem outChar_sum_expansion (hT3 : CepsT3 J) {ν : ℝ → ProbabilityMeasure ℝ}
    {g : ℕ → ℝ → ℝ} {P : ℕ}
    (hy : ∀ k, 1 ≤ k → k ≤ P → ∀ i : Fin (J.dim k),
      HasSeriesExpansionAtOrder (fun eps => J.disp k (J.jet (ν eps)) i) (J.jetSeries i g)
        (P - k)) :
    UnifPolyOrder (fun eps u =>
      ∑ k ∈ range (P + 1), ((eps⁻¹) ^ k : ℝ) • J.phi k u (J.jet (ν eps)) -
        ∑ n ∈ range (P + 1), ((eps⁻¹) ^ n : ℝ) • J.outCoeff g n u) (P + 1) := by
  have hre (eps u : ℝ) : ∑ n ∈ range (P + 1), ((eps⁻¹) ^ n : ℝ) • J.outCoeff g n u =
      ∑ k ∈ range (P + 1), ((eps⁻¹) ^ k : ℝ) •
        ∑ j ∈ range (P + 1 - k), ((eps⁻¹) ^ j : ℝ) • J.phiTerm k j g u := by
    have h := sum_range_sum_range_sub P
      (fun k j => ((eps⁻¹) ^ (k + j) : ℝ) • J.phiTerm k j g u)
    simp only [smul_sum, smul_smul, ← pow_add]
    rw [h]
    refine sum_congr rfl fun n hn => ?_
    rw [outCoeff, smul_sum]
    refine sum_congr rfl fun k hk => ?_
    have hkn : k + (n - k) = n := by have := mem_range.mp hk; omega
    rw [hkn]
  have hterm : ∀ k ∈ range (P + 1), UnifPolyOrder (fun eps u => ((eps⁻¹) ^ k : ℝ) •
      (J.phi k u (J.jet (ν eps)) -
        ∑ j ∈ range (P + 1 - k), ((eps⁻¹) ^ j : ℝ) • J.phiTerm k j g u)) (P + 1) := by
    intro k hk
    have hkP : k ≤ P := by have := mem_range.mp hk; omega
    by_cases hk0 : k = 0
    · subst hk0
      refine (unifPolyOrder_zero (P + 1)).congr (Eventually.of_forall fun eps u => ?_)
      rw [Nat.sub_zero, sum_range_succ', hT3.phi_zero]
      simp [phiTerm]
    · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
      have h := (phi_expansion_along hT3 hk1 (hy k hk1 hkP)).inv_pow_smul k
      have hord : k + (P - k + 1) = P + 1 := by omega
      rw [hord] at h
      refine h.congr (Eventually.of_forall fun eps u => ?_)
      have hr : P + 1 - k = P - k + 1 := by omega
      rw [hr]
      simp only [phiTerm, if_neg hk0]
  refine (UnifPolyOrder.sum _ hterm).congr (Eventually.of_forall fun eps u => ?_)
  rw [hre, ← sum_sub_distrib]
  refine sum_congr rfl fun k _ => ?_
  rw [smul_sub]

/-- **The scalar expansion.** -/
theorem scal_sum_expansion (hT3 : CepsT3 J) {ν : ℝ → ProbabilityMeasure ℝ}
    {g : ℕ → ℝ → ℝ} {P : ℕ}
    (hy : ∀ k ≤ P, ∀ i : Fin (J.dim k),
      HasSeriesExpansionAtOrder (fun eps => J.disp k (J.jet (ν eps)) i) (J.jetSeries i g)
        (P - k)) :
    HasInverseExpansionAtOrder
      (fun eps => ∑ k ∈ range (P + 1), (eps⁻¹) ^ k * J.scal k (J.jet (ν eps)))
      (J.scalCoeff g) P := by
  have hre (eps : ℝ) : inversePolynomial (J.scalCoeff g) P eps =
      ∑ k ∈ range (P + 1), (eps⁻¹) ^ k *
        ∑ j ∈ range (P + 1 - k), J.scalComp k j g * (eps⁻¹) ^ j := by
    have h := sum_range_sum_range_sub P (fun k j => J.scalComp k j g * (eps⁻¹) ^ (k + j))
    simp only [mul_sum]
    rw [inversePolynomial]
    have h' : ∑ k ∈ range (P + 1), ∑ j ∈ range (P + 1 - k),
        (eps⁻¹) ^ k * (J.scalComp k j g * (eps⁻¹) ^ j) =
        ∑ k ∈ range (P + 1), ∑ j ∈ range (P + 1 - k), J.scalComp k j g * (eps⁻¹) ^ (k + j) :=
      sum_congr rfl fun k _ => sum_congr rfl fun j _ => by rw [pow_add]; ring
    rw [h', h]
    refine sum_congr rfl fun n _ => ?_
    rw [scalCoeff, sum_mul]
    refine sum_congr rfl fun k hk => ?_
    have hkn : k + (n - k) = n := by have := mem_range.mp hk; omega
    rw [hkn]
  have hterm : ∀ k ∈ range (P + 1), IsInverseOrder (fun eps => (eps⁻¹) ^ k *
      (J.scal k (J.jet (ν eps)) -
        ∑ j ∈ range (P + 1 - k), J.scalComp k j g * (eps⁻¹) ^ j)) (P + 1) := by
    intro k hk
    have hkP : k ≤ P := by have := mem_range.mp hk; omega
    have h := (isInverseOrder_inv_pow k).mul (scal_expansion_along hT3 k (hy k hkP)).remainder
    have hord : k + (P - k + 1) = P + 1 := by omega
    have hr : P + 1 - k = P - k + 1 := by omega
    rw [hord] at h
    simpa only [hr, inversePolynomial] using h
  have h := IsInverseOrder.sum _ hterm
  obtain ⟨K, e0, hK⟩ := h
  refine ⟨K, e0, fun eps he => ?_⟩
  rw [hre, ← sum_sub_distrib]
  have hs : ∑ k ∈ range (P + 1), ((eps⁻¹) ^ k * J.scal k (J.jet (ν eps)) -
      (eps⁻¹) ^ k * ∑ j ∈ range (P + 1 - k), J.scalComp k j g * (eps⁻¹) ^ j) =
      ∑ k ∈ range (P + 1), (eps⁻¹) ^ k * (J.scal k (J.jet (ν eps)) -
        ∑ j ∈ range (P + 1 - k), J.scalComp k j g * (eps⁻¹) ^ j) :=
    sum_congr rfl fun k _ => by ring
  rw [hs]
  exact hK eps he

/-! ### Stretched-exponential bounds of the composed coefficients -/

theorem phiComp_stretched (hT3 : CepsT3 J) {k : ℕ} (hk : 1 ≤ k) (j : ℕ) (g : ℕ → ℝ → ℝ) :
    StretchedBounded (J.phiComp k j g) :=
  StretchedBounded.sum _ fun α _ => StretchedBounded.mul_const (hT3.phiTaylor_bound k hk α) _

theorem outCoeff_stretched (hT3 : CepsT3 J) (g : ℕ → ℝ → ℝ) (n : ℕ) :
    StretchedBounded (J.outCoeff g n) := by
  refine StretchedBounded.sum _ fun k _ => ?_
  unfold phiTerm
  by_cases hk : k = 0
  · simp only [if_pos hk]
    by_cases hj : n - k = 0
    · simp only [if_pos hj]
      exact hT3.lambdaChar_bound
    · simpa only [if_neg hj] using stretchedBounded_zero
  · simp only [if_neg hk]
    exact phiComp_stretched hT3 (Nat.one_le_iff_ne_zero.mpr hk) _ g

end CepsJetData

end

end PGM
