import PLAStochastic.Index.Model.IIDPairs

/-!
# The cyclic-two estimate

Source: `proofs/proofK_local_count_cyclic_core.tex` (`klc:lem:failure-types`,
`klc:lem:cyclic-two`, `klc:lem:marked-cyclic`, `klc:cor:marked-cyclic-two`).

For a vector `z : Fin t → ℝ`, `vkeys z j = z 0 + ⋯ + z (j - 1)` are its keys,
`rot z r i = z ((i + r) mod t)` its cyclic rotations, `stopsAt eps z` says that the first
strict PLA failure of the keys is exactly at key `t` (`T_eps(z) = t`), and
`cyclicCount eps z` counts the rotations with this property (`𝒦_{t,eps}(z)`).

* feasibility of a prefix is a bound on the oscillation of the residuals `i - a * p i`
  (`prefixAffineFeasible_iff_osc`), and, for increasing keys, the pairwise slope condition
  `L ≤ U` (`prefixAffineFeasible_iff_slopes`, through the one-dimensional Helly fact
  `exists_common_point_of_pairwise`);
* the two directed failure types (`failure_types`): at the boundary slope `U` (type (A))
  or `L` (type (B)) the prefix residuals, or their reflection, form an admissible window
  (`AdmWindow`: oscillation `≤ 2 eps`, an attained full drop, a strict new record);
* for the periodic residuals `R_i(a) = i - a X_i` with drift `d(a) = t - a S`
  (`cutResid`, `cutResid_add_period`) all cuts of one type share one slope
  (`cutType_slope_unique`, the strict monotonicity of the cyclic drawdown), and the window
  claim (`AdmWindow.window_claim`) leaves at most one cut of each type (`cutType_unique`);
  hence **cyclic two**, `cyclicCount eps z ≤ 2` (`cyclicCount_le_two`);
* `stopsAt` of the first `t` gaps is `segLen eps (gapKeys g) = t` (`stopsAt_iff_segLen`,
  `stopsAt_iff_pairSegLen`);
* for an iid pair sequence, the **marked cyclic identity** (`marked_cyclic_identity`) and
  the estimate `P(T_eps = t, S_t^Q = k) ≤ (2 / t) P(S_t^Q = k)` (`marked_cyclic_two`,
  `marked_cyclic_two_pairSegLen`).
-/
namespace PGM

open Finset

/-! ## Feasibility through residual oscillation and slopes -/

/-- Affine feasibility of a prefix is the existence of a slope whose residuals
`i - a * p i` oscillate by at most `2 * eps` on the prefix. -/
theorem prefixAffineFeasible_iff_osc {eps : ℝ} {p : ℕ → ℝ} {len : ℕ} :
    prefixAffineFeasible eps p len ↔
      ∃ a : ℝ, ∀ i < len, ∀ j < len,
        ((i : ℝ) - a * p i) - ((j : ℝ) - a * p j) ≤ 2 * eps := by
  constructor
  · rintro ⟨a, b, hab⟩
    refine ⟨a, fun i hi j hj => ?_⟩
    have h1 := (abs_le.mp (hab i hi)).2
    have h2 := (abs_le.mp (hab j hj)).1
    linarith
  · rintro ⟨a, ha⟩
    rcases Nat.eq_zero_or_pos len with h0 | hlen
    · subst h0
      exact prefixAffineFeasible_zero eps p
    have hne : (range len).Nonempty := ⟨0, mem_range.2 hlen⟩
    set R : ℕ → ℝ := fun i => (i : ℝ) - a * p i with hR
    obtain ⟨i₁, hi₁, hM⟩ := (range len).exists_mem_eq_sup' hne R
    obtain ⟨i₂, hi₂, hm⟩ := (range len).exists_mem_eq_inf' hne R
    set M := (range len).sup' hne R
    set m := (range len).inf' hne R
    have hMm : M - m ≤ 2 * eps := by
      rw [hM, hm]
      exact ha i₁ (mem_range.1 hi₁) i₂ (mem_range.1 hi₂)
    refine ⟨a, (M + m) / 2, fun i hi => ?_⟩
    have hiM : R i ≤ M := le_sup' R (mem_range.2 hi)
    have hmi : m ≤ R i := inf'_le R (mem_range.2 hi)
    have hRi : R i = (i : ℝ) - a * p i := rfl
    rw [abs_le]
    constructor <;> linarith

/-- **One-dimensional Helly.** Finitely many closed intervals `[l k, u k]` have a
common point as soon as every left end lies below every right end. -/
theorem exists_common_point_of_pairwise {ι : Type*} (s : Finset ι) (l u : ι → ℝ)
    (h : ∀ k ∈ s, ∀ m ∈ s, l k ≤ u m) : ∃ a : ℝ, ∀ k ∈ s, l k ≤ a ∧ a ≤ u k := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · exact ⟨0, fun k hk => absurd hk (Finset.notMem_empty k)⟩
  · exact ⟨s.sup' hs l, fun k hk =>
      ⟨le_sup' l hk, sup'_le hs l fun m hm => h m hm k hk⟩⟩

theorem lowerSlope_le_iff {eps a : ℝ} {p : ℕ → ℝ} {i j : ℕ} (h : p j < p i) :
    ((i : ℝ) - j - 2 * eps) / (p i - p j) ≤ a ↔
      ((i : ℝ) - a * p i) - ((j : ℝ) - a * p j) ≤ 2 * eps := by
  rw [div_le_iff₀ (sub_pos.2 h)]
  constructor <;> intro h' <;> nlinarith

theorem le_upperSlope_iff {eps a : ℝ} {p : ℕ → ℝ} {i j : ℕ} (h : p j < p i) :
    a ≤ ((i : ℝ) - j + 2 * eps) / (p i - p j) ↔
      ((j : ℝ) - a * p j) - ((i : ℝ) - a * p i) ≤ 2 * eps := by
  rw [le_div_iff₀ (sub_pos.2 h)]
  constructor <;> intro h' <;> nlinarith

/-- **Slope form of feasibility** (`klc:eq:slope-interval`).  For increasing keys a
prefix is feasible exactly when every lower pair slope lies below every upper pair
slope, i.e. `L ≤ U`; this is the one-dimensional Helly fact for the pair intervals. -/
theorem prefixAffineFeasible_iff_slopes {eps : ℝ} (heps : 0 ≤ eps) {p : ℕ → ℝ} {len : ℕ}
    (hp : ∀ j i, j < i → i < len → p j < p i) :
    prefixAffineFeasible eps p len ↔
      ∀ i j k l, j < i → i < len → l < k → k < len →
        ((i : ℝ) - j - 2 * eps) / (p i - p j) ≤ ((k : ℝ) - l + 2 * eps) / (p k - p l) := by
  rw [prefixAffineFeasible_iff_osc]
  constructor
  · rintro ⟨a, ha⟩ i j k l hji hi hlk hk
    exact ((lowerSlope_le_iff (hp j i hji hi)).2 (ha i hi j (hji.trans hi))).trans
      ((le_upperSlope_iff (hp l k hlk hk)).2 (ha l (hlk.trans hk) k hk))
  · intro h
    obtain ⟨a, ha⟩ := exists_common_point_of_pairwise
      ((range len ×ˢ range len).filter fun ij => ij.2 < ij.1)
      (fun ij => ((ij.1 : ℝ) - ij.2 - 2 * eps) / (p ij.1 - p ij.2))
      (fun ij => ((ij.1 : ℝ) - ij.2 + 2 * eps) / (p ij.1 - p ij.2))
      (by
        rintro ⟨i, j⟩ hij ⟨k, l⟩ hkl
        simp only [mem_filter, mem_product, mem_range] at hij hkl
        exact h i j k l hij.2 hij.1.1 hkl.2 hkl.1.1)
    refine ⟨a, fun i hi j hj => ?_⟩
    rcases lt_trichotomy j i with hji | rfl | hij
    · have := (ha (i, j) (by simp [hi, hj, hji])).1
      exact (lowerSlope_le_iff (hp j i hji hi)).1 this
    · simp only [sub_self]
      linarith
    · have := (ha (j, i) (by simp [hi, hj, hij])).2
      exact (le_upperSlope_iff (hp i j hij hj)).1 this

/-! ## Admissible windows and the two failure types -/

/-- The window `[r, r + t)` of a residual sequence `ρ`, with endpoint `r + t`, is
admissible at level `D`: (i) its oscillation is at most `D`; (ii) a pair `p < q` of the
window attains the full drop `ρ p - ρ q = D`; (iii) the endpoint is a strict new upper
record. -/
structure AdmWindow (ρ : ℕ → ℝ) (D : ℝ) (r t : ℕ) : Prop where
  osc : ∀ i j, r ≤ i → i < r + t → r ≤ j → j < r + t → ρ i - ρ j ≤ D
  drop : ∃ p q, r ≤ p ∧ p < q ∧ q < r + t ∧ ρ p - ρ q = D
  record : ∀ i, r ≤ i → i < r + t → ρ i < ρ (r + t)

/-- **The two directed failure types** (`klc:lem:failure-types`).  If the first `n`
keys are feasible but the first `n + 1` are not, then either (A) at the upper boundary
slope `a = U` the residuals `i - a * p i` of the prefix form an admissible window whose
endpoint `n` is a strict new upper record, or (B) at the lower boundary slope `a = L`
the reflected residuals do. -/
theorem failure_types {eps : ℝ} (heps : 0 ≤ eps) {p : ℕ → ℝ} (hp : StrictMono p) {n : ℕ}
    (hfeas : prefixAffineFeasible eps p n) (hinf : ¬ prefixAffineFeasible eps p (n + 1)) :
    (∃ a, AdmWindow (fun i => (i : ℝ) - a * p i) (2 * eps) 0 n) ∨
      (∃ a, AdmWindow (fun i => -((i : ℝ) - a * p i)) (2 * eps) 0 n) := by
  have hp' : ∀ j i, j < i → i < n + 1 → p j < p i := fun j i h _ => hp h
  set lo : ℕ × ℕ → ℝ := fun ij => ((ij.1 : ℝ) - ij.2 - 2 * eps) / (p ij.1 - p ij.2)
    with hlo
  set up : ℕ × ℕ → ℝ := fun ij => ((ij.1 : ℝ) - ij.2 + 2 * eps) / (p ij.1 - p ij.2)
    with hup
  have hself : ∀ i j, j < i → lo (i, j) ≤ up (i, j) := by
    intro i j hji
    simp only [hlo, hup]
    exact div_le_div_of_nonneg_right (by linarith) (sub_pos.2 (hp hji)).le
  -- two keys always lie on a line
  rcases Nat.lt_or_ge n 2 with hn | hn
  · exfalso
    apply hinf
    rw [prefixAffineFeasible_iff_slopes heps hp']
    intro i j k l hji hi hlk hk
    obtain ⟨rfl, rfl, rfl, rfl⟩ : i = 1 ∧ j = 0 ∧ k = 1 ∧ l = 0 := by omega
    exact hself 1 0 (by omega)
  set P := (range n ×ˢ range n).filter fun ij : ℕ × ℕ => ij.2 < ij.1 with hP
  have hmemP : ∀ i j, (i, j) ∈ P ↔ j < i ∧ i < n := by
    intro i j
    simp only [hP, mem_filter, mem_product, mem_range]
    omega
  have hPne : P.Nonempty := ⟨(1, 0), (hmemP 1 0).2 ⟨by omega, by omega⟩⟩
  obtain ⟨⟨i₀, j₀⟩, h₀, hU⟩ := P.exists_mem_eq_inf' hPne up
  obtain ⟨⟨i₁, j₁⟩, h₁, hL⟩ := P.exists_mem_eq_sup' hPne lo
  set U := P.inf' hPne up with hUdef
  set L := P.sup' hPne lo with hLdef
  obtain ⟨a₀, ha₀⟩ := prefixAffineFeasible_iff_osc.1 hfeas
  have hLa₀ : L ≤ a₀ := sup'_le hPne lo fun ij hij => by
    obtain ⟨hji, hi⟩ := (hmemP ij.1 ij.2).1 hij
    exact (lowerSlope_le_iff (hp hji)).2 (ha₀ ij.1 hi ij.2 (hji.trans hi))
  have ha₀U : a₀ ≤ U := le_inf' hPne up fun ij hij => by
    obtain ⟨hji, hi⟩ := (hmemP ij.1 ij.2).1 hij
    exact (le_upperSlope_iff (hp hji)).2 (ha₀ ij.2 (hji.trans hi) ij.1 hi)
  have hloL : ∀ i j, j < i → i < n → lo (i, j) ≤ L := fun i j hji hi =>
    le_sup' lo ((hmemP i j).2 ⟨hji, hi⟩)
  have hUup : ∀ i j, j < i → i < n → U ≤ up (i, j) := fun i j hji hi =>
    inf'_le up ((hmemP i j).2 ⟨hji, hi⟩)
  have hLU : L ≤ U := hLa₀.trans ha₀U
  -- every slope of `[L, U]` keeps the prefix residuals in a strip of width `2 eps`
  have hosc : ∀ a, L ≤ a → a ≤ U → ∀ i < n, ∀ j < n,
      ((i : ℝ) - a * p i) - ((j : ℝ) - a * p j) ≤ 2 * eps := by
    intro a hLa haU i hi j hj
    rcases lt_trichotomy j i with hji | rfl | hij
    · exact (lowerSlope_le_iff (hp hji)).1 ((hloL i j hji hi).trans hLa)
    · simp only [sub_self]
      linarith
    · exact (le_upperSlope_iff (hp hij)).1 (haU.trans (hUup j i hij hj))
  by_cases hA : ∃ j < n, 2 * eps < ((n : ℝ) - U * p n) - ((j : ℝ) - U * p j)
  · left
    obtain ⟨j, hj, hjA⟩ := hA
    refine ⟨U, ⟨fun i k _ hi _ hk => ?_, ?_, fun i _ hi => ?_⟩⟩
    · exact hosc U hLU le_rfl i (by omega) k (by omega)
    · obtain ⟨hji, hi⟩ := (hmemP i₀ j₀).1 h₀
      refine ⟨j₀, i₀, Nat.zero_le _, hji, by omega, ?_⟩
      have h := hU
      simp only [hup] at h
      rw [eq_div_iff (sub_pos.2 (hp hji)).ne'] at h
      linarith
    · have := hosc U hLU le_rfl i (by omega) j hj
      simp only [zero_add]
      linarith
  by_cases hB : ∃ j < n, 2 * eps < ((j : ℝ) - L * p j) - ((n : ℝ) - L * p n)
  · right
    obtain ⟨j, hj, hjB⟩ := hB
    refine ⟨L, ⟨fun i k _ hi _ hk => ?_, ?_, fun i _ hi => ?_⟩⟩
    · have := hosc L le_rfl hLU k (by omega) i (by omega)
      linarith
    · obtain ⟨hji, hi⟩ := (hmemP i₁ j₁).1 h₁
      refine ⟨j₁, i₁, Nat.zero_le _, hji, by omega, ?_⟩
      have h := hL
      simp only [hlo] at h
      rw [eq_div_iff (sub_pos.2 (hp hji)).ne'] at h
      linarith
    · have := hosc L le_rfl hLU j hj i (by omega)
      simp only [zero_add]
      linarith
  -- neither type: then the prefix of length `n + 1` would be feasible
  exfalso
  push Not at hA hB
  have hAlo : ∀ j < n, lo (n, j) ≤ U := fun j hj => (lowerSlope_le_iff (hp hj)).2 (hA j hj)
  have hBup : ∀ j < n, L ≤ up (n, j) := fun j hj => (le_upperSlope_iff (hp hj)).2 (hB j hj)
  apply hinf
  rw [prefixAffineFeasible_iff_slopes heps hp']
  intro i j k l hji hi hlk hk
  change lo (i, j) ≤ up (k, l)
  rcases Nat.lt_or_ge i n with hin | hin <;> rcases Nat.lt_or_ge k n with hkn | hkn
  · exact (hloL i j hji hin).trans (hLU.trans (hUup k l hlk hkn))
  · rw [show k = n by omega]
    exact (hloL i j hji hin).trans (hBup l (by omega))
  · rw [show i = n by omega]
    exact (hAlo j (by omega)).trans (hUup k l hlk hkn)
  · rw [show i = n by omega, show k = n by omega]
    have hjn : j < n := by omega
    have hln : l < n := by omega
    rcases lt_trichotomy j l with hjl | rfl | hlj
    · -- a violation would force type (B)
      by_contra hcon
      push Not at hcon
      have h1 : lo (l, j) ≤ up (n, l) := (hloL l j hjl hln).trans (hBup l hln)
      simp only [hlo, hup] at h1 hcon
      rw [div_le_div_iff₀ (sub_pos.2 (hp hjl)) (sub_pos.2 (hp hln))] at h1
      rw [div_lt_div_iff₀ (sub_pos.2 (hp hln)) (sub_pos.2 (hp hjn))] at hcon
      nlinarith [mul_nonneg heps (sub_pos.2 (hp hln)).le]
    · exact hself _ _ hjn
    · -- a violation would force type (A)
      by_contra hcon
      push Not at hcon
      have h1 : lo (n, j) ≤ up (j, l) := (hAlo j hjn).trans (hUup j l hlj hjn)
      simp only [hlo, hup] at h1 hcon
      rw [div_le_div_iff₀ (sub_pos.2 (hp hjn)) (sub_pos.2 (hp hlj))] at h1
      rw [div_lt_div_iff₀ (sub_pos.2 (hp hln)) (sub_pos.2 (hp hjn))] at hcon
      nlinarith [mul_nonneg heps (sub_pos.2 (hp hjn)).le]

/-! ## Admissible windows of a periodic residual sequence -/

section Periodic

variable {ρ : ℕ → ℝ} {t : ℕ} {d D : ℝ}

theorem add_mul_period_of_periodic (hper : ∀ i, ρ (i + t) = ρ i + d) (k i : ℕ) :
    ρ (i + k * t) = ρ i + k * d := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show i + (k + 1) * t = (i + k * t) + t by ring, hper, ih]
    push_cast
    ring

/-- Admissibility is invariant under a translation of the residuals and of the
indices. -/
theorem AdmWindow.of_shift {ρ' : ℕ → ℝ} {c : ℝ} {r : ℕ} (h : ∀ i, ρ' i = ρ (r + i) + c)
    (hA : AdmWindow ρ' D 0 t) : AdmWindow ρ D r t where
  osc i j hi hi' hj hj' := by
    have := hA.osc (i - r) (j - r) (by omega) (by omega) (by omega) (by omega)
    rw [h, h, show r + (i - r) = i by omega, show r + (j - r) = j by omega] at this
    linarith
  drop := by
    obtain ⟨p, q, -, hpq, hq, hD⟩ := hA.drop
    refine ⟨r + p, r + q, by omega, by omega, by omega, ?_⟩
    rw [h, h] at hD
    linarith
  record i hi hi' := by
    have := hA.record (i - r) (by omega) (by omega)
    rw [h, h, show r + (i - r) = i by omega, zero_add] at this
    linarith

/-- An admissible window stays admissible after translation by one period. -/
theorem AdmWindow.add_period (hper : ∀ i, ρ (i + t) = ρ i + d) {r : ℕ} (h : AdmWindow ρ D r t) :
    AdmWindow ρ D (r + t) t where
  osc i j hi hi' hj hj' := by
    obtain ⟨i, rfl⟩ : ∃ i', i = i' + t := ⟨i - t, by omega⟩
    obtain ⟨j, rfl⟩ : ∃ j', j = j' + t := ⟨j - t, by omega⟩
    rw [hper, hper]
    have := h.osc i j (by omega) (by omega) (by omega) (by omega)
    linarith
  drop := by
    obtain ⟨p, q, hp, hpq, hq, hD⟩ := h.drop
    refine ⟨p + t, q + t, by omega, by omega, by omega, ?_⟩
    rw [hper, hper]
    linarith
  record i hi hi' := by
    obtain ⟨i, rfl⟩ : ∃ i', i = i' + t := ⟨i - t, by omega⟩
    rw [hper, hper]
    have := h.record i (by omega) (by omega)
    linarith

/-- The cyclic drawdown bound: with nonnegative period drift, the oscillation bound on
one window bounds the drop along every proper cyclic arc `i < j < i + t`. -/
theorem periodic_arc_bound (ht : 0 < t) (hd : 0 ≤ d) (hper : ∀ i, ρ (i + t) = ρ i + d) {r : ℕ}
    (hosc : ∀ i j, r ≤ i → i < r + t → r ≤ j → j < r + t → ρ i - ρ j ≤ D) :
    ∀ i j, i < j → j < i + t → ρ i - ρ j ≤ D := by
  intro i j hij hji
  have hrt : r ≤ r * t := Nat.le_mul_of_pos_right r ht
  have hmod := Nat.mod_add_div (i + r * t - r) t
  have hlt := Nat.mod_lt (i + r * t - r) ht
  set i' := r + (i + r * t - r) % t with hi'
  set m := (i + r * t - r) / t with hm
  have e1 : i + r * t = i' + m * t := by rw [mul_comm m t]; omega
  have e2 : j + r * t = (i' + (j - i)) + m * t := by omega
  have key : ρ i - ρ j = ρ i' - ρ (i' + (j - i)) := by
    have h1 := add_mul_period_of_periodic hper r i
    have h2 := add_mul_period_of_periodic hper r j
    have h3 := add_mul_period_of_periodic hper m i'
    have h4 := add_mul_period_of_periodic hper m (i' + (j - i))
    rw [e1] at h1
    rw [e2] at h2
    linarith
  rw [key]
  rcases Nat.lt_or_ge (i' + (j - i)) (r + t) with hin | hout
  · exact hosc _ _ (by omega) (by omega) (by omega) hin
  · have h5 := hper (i' + (j - i) - t)
    rw [show i' + (j - i) - t + t = i' + (j - i) by omega] at h5
    have := hosc i' (i' + (j - i) - t) (by omega) (by omega) (by omega) (by omega)
    linarith

/-- The crossing relation `klc:eq:first-crossing`: every full-drop pair of an
admissible window `[r, r + t)` straddles the start `s` of a later admissible window,
`r < s < r + t`. -/
theorem AdmWindow.crossing (hper : ∀ i, ρ (i + t) = ρ i + d) {r s : ℕ} (hrs : r < s)
    (hsr : s < r + t) (hr : AdmWindow ρ D r t) (hs : AdmWindow ρ D s t) {p q : ℕ} (hp : r ≤ p)
    (hpq : p < q) (hq : q < r + t) (hD : ρ p - ρ q = D) : p < s ∧ s ≤ q := by
  constructor
  · by_contra hps
    push Not at hps
    have h1 := hr.record p hp (by omega)
    have h2 := hs.osc (r + t) q (by omega) (by omega) (by omega) (by omega)
    linarith
  · by_contra hqs
    push Not at hqs
    have h1 := hs.record (p + t) (by omega) (by omega)
    rw [hper, hper] at h1
    have h2 := hr.osc s q (by omega) (by omega) (by omega) hq
    linarith

/-- **Window claim** (proof of `klc:lem:cyclic-two`).  With positive period drift, no
two admissible windows start at `r < s < r + t`: there is at most one admissible residue
class modulo `t`. -/
theorem AdmWindow.window_claim (hd : 0 < d) (hper : ∀ i, ρ (i + t) = ρ i + d) {r s : ℕ}
    (hrs : r < s) (hsr : s < r + t) (hr : AdmWindow ρ D r t) (hs : AdmWindow ρ D s t) : False := by
  obtain ⟨p, q, hp, hpq, hq, hD⟩ := hr.drop
  obtain ⟨p', q', hp', hpq', hq', hD'⟩ := hs.drop
  have c1 := AdmWindow.crossing hper hrs hsr hr hs hp hpq hq hD
  have c2 := AdmWindow.crossing hper hsr (by omega) hs (hr.add_period hper) hp' hpq' hq' hD'
  -- `p` is a maximum of the window at `r`, `p'` one of the window at `s`
  have h1 : ρ p' - ρ q ≤ D := hr.osc p' q (by omega) (by omega) (by omega) hq
  have h2 : ρ (p + t) - ρ q' ≤ D := hs.osc (p + t) q' (by omega) (by omega) (by omega) hq'
  rw [hper] at h2
  linarith

end Periodic

/-! ## Vectors, rotations, and the cyclic count -/

/-- Extension of a finite vector by zero. -/
def vext {t : ℕ} (z : Fin t → ℝ) : ℕ → ℝ := fun q => if h : q < t then z ⟨q, h⟩ else 0

/-- Keys of a vector: `vkeys z j = z 0 + ⋯ + z (j - 1)` for `j ≤ t`. -/
def vkeys {t : ℕ} (z : Fin t → ℝ) : ℕ → ℝ := gapKeys (vext z)

/-- Cyclic rotation: `rot z r i = z ((i + r) mod t)`. -/
def rot {t : ℕ} (z : Fin t → ℝ) (r : Fin t) : Fin t → ℝ := fun i => z (i + r)

/-- `T_eps(z) = t`: the first `t` keys `0, …, t - 1` of `z` are feasible and the first
`t + 1` keys are not, so the first strict PLA failure is exactly at key `t`. -/
def stopsAt (eps : ℝ) {t : ℕ} (z : Fin t → ℝ) : Prop :=
  prefixAffineFeasible eps (vkeys z) t ∧ ¬ prefixAffineFeasible eps (vkeys z) (t + 1)

open Classical in
/-- The cyclic count `𝒦_{t,eps}(z)` of `klc:eq:cyclic-count`: the number of cyclic
starts whose first strict failure is at the last gap. -/
noncomputable def cyclicCount (eps : ℝ) {t : ℕ} (z : Fin t → ℝ) : ℕ :=
  #{r : Fin t | stopsAt eps (rot z r)}

/-- The cumulative positions `X` of the periodic extension of the gaps of `z`. -/
def pkeys {t : ℕ} (z : Fin t → ℝ) : ℕ → ℝ := gapKeys (fun q => vext z (q % t))

theorem pkeys_add_period {t : ℕ} (z : Fin t → ℝ) (i : ℕ) :
    pkeys z (i + t) = pkeys z i + pkeys z t := by
  simp only [pkeys, gapKeys]
  rw [add_comm i t, Finset.sum_range_add, add_comm]
  congr 1
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Nat.add_mod_left]

theorem pkeys_strictMono {t : ℕ} (ht : 0 < t) {z : Fin t → ℝ} (hz : ∀ i, 0 < z i) :
    StrictMono (pkeys z) := by
  apply strictMono_nat_of_lt_succ
  intro i
  simp only [pkeys, gapKeys, Finset.sum_range_succ]
  have : 0 < vext z (i % t) := by simp [vext, Nat.mod_lt i ht, hz]
  linarith

/-- The keys of a rotation are translated periodic positions. -/
theorem vkeys_rot {t : ℕ} (z : Fin t → ℝ) (r : Fin t) {i : ℕ} (hi : i ≤ t) :
    vkeys (rot z r) i = pkeys z (r + i) - pkeys z r := by
  rw [pkeys, ← gapKeys_shift]
  simp only [vkeys, gapKeys]
  refine Finset.sum_congr rfl fun q hq => ?_
  have hq' : q < t := by rw [mem_range] at hq; omega
  have hr : ((r : ℕ) + q) % t < t := Nat.mod_lt _ (by omega)
  simp only [vext, rot, hq', hr, dif_pos]
  congr 1
  ext
  simp [Fin.val_add, add_comm]

theorem stopsAt_rot_iff {eps : ℝ} {t : ℕ} (z : Fin t → ℝ) (r : Fin t) :
    stopsAt eps (rot z r) ↔ prefixAffineFeasible eps (fun i => pkeys z (r + i)) t ∧
      ¬ prefixAffineFeasible eps (fun i => pkeys z (r + i)) (t + 1) := by
  have key : ∀ len ≤ t + 1, prefixAffineFeasible eps (vkeys (rot z r)) len ↔
      prefixAffineFeasible eps (fun i => pkeys z (r + i)) len := by
    intro len hlen
    refine (prefixAffineFeasible_congr fun i hi => ?_).trans
      (prefixAffineFeasible_affine_iff (p := fun i => pkeys z (r + i)) (s := 1)
        (c := -pkeys z r) one_ne_zero)
    rw [vkeys_rot z r (by omega)]
    ring
  unfold stopsAt
  rw [key t (by omega), key (t + 1) le_rfl]

/-- The periodic residuals `σ (j - a X_j)` at slope `a`; `σ = 1` is type (A) and
`σ = -1` is type (B). -/
def cutResid {t : ℕ} (z : Fin t → ℝ) (σ a : ℝ) : ℕ → ℝ :=
  fun j => σ * ((j : ℝ) - a * pkeys z j)

/-- The cyclic start `r` has a first failure of type `σ` at its last gap. -/
def CutType (eps : ℝ) {t : ℕ} (z : Fin t → ℝ) (σ : ℝ) (r : Fin t) : Prop :=
  ∃ a, AdmWindow (cutResid z σ a) (2 * eps) r t

/-- `R_{i+t}(a) = R_i(a) + d(a)` with drift `d(a) = t - a S` (`klc:eq:periodic-residual`). -/
theorem cutResid_add_period {t : ℕ} (z : Fin t → ℝ) (σ a : ℝ) (i : ℕ) :
    cutResid z σ a (i + t) = cutResid z σ a i + σ * ((t : ℝ) - a * pkeys z t) := by
  simp only [cutResid, pkeys_add_period]
  push_cast
  ring

/-- The strict new record forces a positive (signed) period drift. -/
theorem cutResid_drift_pos {t : ℕ} {z : Fin t → ℝ} {σ a D : ℝ} {r : ℕ}
    (h : AdmWindow (cutResid z σ a) D r t) (ht : 0 < t) : 0 < σ * ((t : ℝ) - a * pkeys z t) := by
  have := h.record r le_rfl (by omega)
  rw [cutResid_add_period] at this
  linarith

/-- Every last-step first failure of a rotation has type (A) or type (B). -/
theorem cutType_of_stopsAt {eps : ℝ} (heps : 0 ≤ eps) {t : ℕ} (ht : 0 < t)
    {z : Fin t → ℝ} (hz : ∀ i, 0 < z i) {r : Fin t} (h : stopsAt eps (rot z r)) :
    CutType eps z 1 r ∨ CutType eps z (-1) r := by
  rw [stopsAt_rot_iff] at h
  have hmono : StrictMono fun i => pkeys z (r + i) :=
    fun a b hab => pkeys_strictMono ht hz (by omega)
  rcases failure_types heps hmono h.1 h.2 with ⟨a, ha⟩ | ⟨a, ha⟩
  · refine Or.inl ⟨a, AdmWindow.of_shift (c := -(r : ℝ)) (fun i => ?_) ha⟩
    simp only [cutResid]
    push_cast
    ring
  · refine Or.inr ⟨a, AdmWindow.of_shift (c := (r : ℝ)) (fun i => ?_) ha⟩
    simp only [cutResid]
    push_cast
    ring

/-- Strict monotonicity of the cyclic drawdown: the attained full drop at slope `a₁`
exceeds `D` at any slope `a₂` further in the direction of `σ`, which the arc bound at
`a₂` forbids. -/
theorem not_pos_slope_gap {t : ℕ} (ht : 0 < t) {z : Fin t → ℝ} (hz : ∀ i, 0 < z i)
    {σ D a₁ a₂ : ℝ} {r₁ r₂ : ℕ} (h₁ : AdmWindow (cutResid z σ a₁) D r₁ t)
    (h₂ : AdmWindow (cutResid z σ a₂) D r₂ t) : ¬ 0 < σ * (a₂ - a₁) := by
  intro hlt
  obtain ⟨p, q, hp, hpq, hq, hD⟩ := h₁.drop
  have hb := periodic_arc_bound ht (cutResid_drift_pos h₂ ht).le
    (cutResid_add_period z σ a₂) h₂.osc p q hpq (by omega)
  have hprod : 0 < σ * (a₂ - a₁) * (pkeys z q - pkeys z p) :=
    mul_pos hlt (sub_pos.2 (pkeys_strictMono ht hz hpq))
  have hid : cutResid z σ a₂ p - cutResid z σ a₂ q =
      (cutResid z σ a₁ p - cutResid z σ a₁ q) + σ * (a₂ - a₁) * (pkeys z q - pkeys z p) := by
    simp only [cutResid]
    ring
  linarith

/-- **All cuts of one type share one boundary slope.**  The cyclic drawdown
`D_σ(a) = max_{i < j < i + t} (R^σ_i(a) - R^σ_j(a))` is strictly monotone in `a`, and
equals `2 eps` at the boundary slope of every cut of type `σ`. -/
theorem cutType_slope_unique {t : ℕ} (ht : 0 < t) {z : Fin t → ℝ} (hz : ∀ i, 0 < z i)
    {σ D a₁ a₂ : ℝ} (hσ : σ ≠ 0) {r₁ r₂ : ℕ} (h₁ : AdmWindow (cutResid z σ a₁) D r₁ t)
    (h₂ : AdmWindow (cutResid z σ a₂) D r₂ t) : a₁ = a₂ := by
  rcases lt_trichotomy (σ * (a₂ - a₁)) 0 with h | h | h
  · exact absurd (by linarith [show σ * (a₁ - a₂) = -(σ * (a₂ - a₁)) by ring])
      (not_pos_slope_gap ht hz h₂ h₁)
  · rcases mul_eq_zero.1 h with h | h
    · exact absurd h hσ
    · linarith
  · exact absurd h (not_pos_slope_gap ht hz h₁ h₂)

/-- At most one cyclic start has a first failure of a given type at its last gap. -/
theorem cutType_unique {eps : ℝ} {t : ℕ} {z : Fin t → ℝ} (hz : ∀ i, 0 < z i) {σ : ℝ}
    (hσ : σ ≠ 0) {r₁ r₂ : Fin t} (h₁ : CutType eps z σ r₁) (h₂ : CutType eps z σ r₂) :
    r₁ = r₂ := by
  have ht : 0 < t := r₁.pos
  obtain ⟨a₁, h₁⟩ := h₁
  obtain ⟨a₂, h₂⟩ := h₂
  obtain rfl := cutType_slope_unique ht hz hσ h₁ h₂
  have hd := cutResid_drift_pos h₁ ht
  by_contra hne
  rcases lt_or_gt_of_ne (Fin.val_injective.ne hne) with hlt | hlt
  · exact AdmWindow.window_claim hd (cutResid_add_period z σ a₁) hlt (by omega) h₁ h₂
  · exact AdmWindow.window_claim hd (cutResid_add_period z σ a₁) hlt (by omega) h₂ h₁

/-- **Cyclic two** (`klc:lem:cyclic-two`).  For `eps ≥ 0` and a positive vector `z`, at
most two cyclic starts have their first strict PLA failure at the last gap. -/
theorem cyclicCount_le_two {eps : ℝ} (heps : 0 ≤ eps) {t : ℕ} {z : Fin t → ℝ}
    (hz : ∀ i, 0 < z i) : cyclicCount eps z ≤ 2 := by
  classical
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · simp [cyclicCount]
  have hsub : ({r : Fin t | stopsAt eps (rot z r)} : Finset (Fin t)) ⊆
      ({r : Fin t | CutType eps z 1 r} : Finset (Fin t)) ∪
        ({r : Fin t | CutType eps z (-1) r} : Finset (Fin t)) := by
    intro r hr
    simp only [mem_filter, mem_univ, true_and, mem_union] at hr ⊢
    exact cutType_of_stopsAt heps ht hz hr
  have h₁ : #{r : Fin t | CutType eps z 1 r} ≤ 1 :=
    card_le_one.2 fun a ha b hb => cutType_unique hz one_ne_zero
      (by simpa using ha) (by simpa using hb)
  have h₂ : #{r : Fin t | CutType eps z (-1) r} ≤ 1 :=
    card_le_one.2 fun a ha b hb => cutType_unique hz (σ := -1) (by norm_num)
      (by simpa using ha) (by simpa using hb)
  unfold cyclicCount
  calc _ ≤ _ := card_le_card hsub
    _ ≤ _ := card_union_le _ _
    _ ≤ 2 := by omega

/-! ## Relation to the ALG-OPT segment length -/

theorem segLen_eq_natCast_iff {eps : ℝ} {p : ℕ → ℝ} (t : ℕ) :
    segLen eps p = t ↔
      prefixAffineFeasible eps p t ∧ ¬ prefixAffineFeasible eps p (t + 1) := by
  constructor
  · intro h
    refine ⟨?_, (segLen_le_iff t).1 h.le⟩
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · exact prefixAffineFeasible_zero eps p
    · obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
      exact (lt_segLen_iff s).1 (by rw [h]; exact_mod_cast Nat.lt_succ_self s)
  · rintro ⟨h1, h2⟩
    apply le_antisymm ((segLen_le_iff t).2 h2)
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · simp
    · obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
      have h' := (ENat.add_one_le_iff (ENat.natCast_ne_top s)).2 ((lt_segLen_iff s).2 h1)
      exact_mod_cast h'

theorem vkeys_eq_gapKeys (g : ℕ → ℝ) {t j : ℕ} (hj : j ≤ t) :
    vkeys (fun i : Fin t => g i) j = gapKeys g j := by
  simp only [vkeys, gapKeys]
  refine Finset.sum_congr rfl fun q hq => ?_
  have : q < t := by rw [mem_range] at hq; omega
  simp [vext, this]

/-- `T_eps = t` for the first `t` gaps is the statement that the first ALG-OPT segment of
the gap keys has exactly `t` keys. -/
theorem stopsAt_iff_segLen {eps : ℝ} (g : ℕ → ℝ) (t : ℕ) :
    stopsAt eps (fun i : Fin t => g i) ↔ segLen eps (gapKeys g) = t := by
  have key : ∀ len ≤ t + 1, prefixAffineFeasible eps (vkeys (fun i : Fin t => g i)) len ↔
      prefixAffineFeasible eps (gapKeys g) len := fun len hlen =>
    prefixAffineFeasible_congr fun i hi => vkeys_eq_gapKeys g (by omega)
  rw [segLen_eq_natCast_iff, stopsAt, key t (by omega), key (t + 1) le_rfl]

theorem stopsAt_iff_pairSegLen {eps : ℝ} (z : ℕ → ℝ × ℕ) (t : ℕ) :
    stopsAt eps (fun i : Fin t => (z i).1) ↔ pairSegLen eps z = t :=
  stopsAt_iff_segLen (fun s => (z s).1) t

/-! ## The marked cyclic identity -/

section Marked

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Z : ℕ → Ω → ℝ × ℕ}

theorem measurable_vkeys_fst (t : ℕ) :
    Measurable fun v : Fin t → ℝ × ℕ => vkeys (fun i => (v i).1) := by
  refine measurable_pi_lambda _ fun j => ?_
  simp only [vkeys, gapKeys]
  refine Finset.measurable_sum _ fun q _ => ?_
  by_cases hq : q < t
  · simp only [vext, hq, dif_pos]
    exact (measurable_pi_apply _).fst
  · simp only [vext, hq, dif_neg, not_false_eq_true]
    exact measurable_const

theorem measurableSet_stopsAt_fst (eps : ℝ) (t : ℕ) :
    MeasurableSet {v : Fin t → ℝ × ℕ | stopsAt eps (fun i => (v i).1)} :=
  (measurable_vkeys_fst t (measurableSet_prefixAffineFeasible eps t)).inter
    (measurable_vkeys_fst t (measurableSet_prefixAffineFeasible eps (t + 1))).compl

/-- The law of the first `t` pairs of an iid pair sequence is invariant under every cyclic
rotation. -/
theorem map_rotPairs_eq [IsProbabilityMeasure P] (hZ : IIDPairs P Z) {t : ℕ} (r : Fin t) :
    P.map (fun ω (i : Fin t) => Z ((i + r : Fin t) : ℕ) ω) =
      P.map (fun ω (i : Fin t) => Z (i : ℕ) ω) := by
  have hmarg : ∀ n, P.map (Z n) = P.map (Z 0) := fun n => (hZ.ident n).map_eq
  have e1 := (hZ.indep.precomp (g := fun i : Fin t => ((i + r : Fin t) : ℕ))
    (fun a b hab => add_right_cancel (Fin.val_injective hab))).map_fun_eq_pi_map
    (fun i => (hZ.measurable _).aemeasurable)
  have e2 := (hZ.indep.precomp (g := fun i : Fin t => (i : ℕ)) Fin.val_injective).map_fun_eq_pi_map
    (fun i => (hZ.measurable _).aemeasurable)
  rw [e1, e2]
  congr 1
  funext i
  rw [hmarg (i + r : Fin t), hmarg i]

/-- **Marked cyclic identity** (`klc:lem:marked-cyclic`).  For an iid pair sequence and
`t ≥ 1`,
`P(T_eps = t, S_t^Q = k) = (1 / t) E[1{S_t^Q = k} 𝒦_{t,eps}(G_0, …, G_{t-1})]`. -/
theorem marked_cyclic_identity [IsProbabilityMeasure P] (hZ : IIDPairs P Z) (eps : ℝ)
    {t : ℕ} (ht : 0 < t) (k : ℕ) :
    P {ω | stopsAt eps (fun i : Fin t => (Z i ω).1) ∧ ∑ i ∈ range t, (Z i ω).2 = k} =
      (t : ℝ≥0∞)⁻¹ * ∫⁻ ω, {ω | ∑ i ∈ range t, (Z i ω).2 = k}.indicator
        (fun ω => (cyclicCount eps (fun i : Fin t => (Z i ω).1) : ℝ≥0∞)) ω ∂P := by
  classical
  have : NeZero t := ⟨ht.ne'⟩
  set E : Set (Fin t → ℝ × ℕ) :=
    {v | stopsAt eps (fun i => (v i).1) ∧ ∑ i, (v i).2 = k} with hE
  have hEm : MeasurableSet E := (measurableSet_stopsAt_fst eps t).inter
    ((Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).snd)
      (measurableSet_singleton k))
  -- the rotated events
  set A : Fin t → Set Ω := fun r =>
    {ω | stopsAt eps (rot (fun i : Fin t => (Z i ω).1) r) ∧ ∑ i ∈ range t, (Z i ω).2 = k}
    with hA
  have hApre : ∀ r, A r = (fun ω (i : Fin t) => Z ((i + r : Fin t) : ℕ) ω) ⁻¹' E := by
    intro r
    ext ω
    simp only [hA, hE, Set.mem_ofPred_eq, Set.mem_preimage]
    have hsum : ∑ x : Fin t, (Z ((x + r : Fin t) : ℕ) ω).2 = ∑ i ∈ range t, (Z i ω).2 := by
      rw [← Fin.sum_univ_eq_sum_range (fun i => (Z i ω).2) t]
      exact Equiv.sum_comp (Equiv.addRight r) (fun i : Fin t => (Z i ω).2)
    rw [hsum]
    rfl
  have hmeas : ∀ r : Fin t, Measurable fun ω (i : Fin t) => Z ((i + r : Fin t) : ℕ) ω :=
    fun r => measurable_pi_lambda _ fun i => hZ.measurable _
  have hAm : ∀ r, MeasurableSet (A r) := fun r => by rw [hApre r]; exact hmeas r hEm
  have hA0 : A 0 = {ω | stopsAt eps (fun i : Fin t => (Z i ω).1) ∧
      ∑ i ∈ range t, (Z i ω).2 = k} := by
    have hrot0 : ∀ f : Fin t → ℝ, rot f 0 = f := fun f => funext fun i => by
      simp only [rot, add_zero]
    ext ω
    simp only [hA, Set.mem_ofPred_eq, hrot0]
  have hPA : ∀ r, P (A r) = P (A 0) := by
    intro r
    rw [hApre r, hApre 0, ← Measure.map_apply (hmeas r) hEm, ← Measure.map_apply (hmeas 0) hEm,
      map_rotPairs_eq hZ r, map_rotPairs_eq hZ 0]
  -- the count is a sum of rotated indicators
  have hpt : ∀ ω, {ω | ∑ i ∈ range t, (Z i ω).2 = k}.indicator
      (fun ω => (cyclicCount eps (fun i : Fin t => (Z i ω).1) : ℝ≥0∞)) ω =
        ∑ r : Fin t, (A r).indicator 1 ω := by
    intro ω
    by_cases hk : ∑ i ∈ range t, (Z i ω).2 = k
    · rw [Set.indicator_of_mem (show ω ∈ {ω | ∑ i ∈ range t, (Z i ω).2 = k} from hk)]
      simp only [cyclicCount, Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one,
        Nat.cast_zero]
      refine Finset.sum_congr rfl fun r _ => ?_
      simp [hA, Set.indicator, hk]
    · rw [Set.indicator_of_notMem (show ω ∉ {ω | ∑ i ∈ range t, (Z i ω).2 = k} from hk)]
      symm
      refine Finset.sum_eq_zero fun r _ => ?_
      simp [hA, Set.indicator, hk]
  simp_rw [hpt]
  rw [lintegral_finsetSum _ fun r _ => measurable_one.indicator (hAm r)]
  simp_rw [lintegral_indicator_one (hAm _), hPA]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ENNReal.inv_mul_cancel_left (by exact_mod_cast ht.ne') (ENNReal.natCast_ne_top t), hA0]

/-- **Marked cyclic-two estimate** (`klc:cor:marked-cyclic-two`):
`P(T_eps = t, S_t^Q = k) ≤ (2 / t) P(S_t^Q = k)`.  No independence between the gap and
the mark of one pair is used. -/
theorem marked_cyclic_two [IsProbabilityMeasure P] (hZ : IIDPairs P Z) {eps : ℝ}
    (heps : 0 ≤ eps) (hpos : ∀ i, ∀ᵐ ω ∂P, 0 < (Z i ω).1) {t : ℕ} (ht : 0 < t) (k : ℕ) :
    P {ω | stopsAt eps (fun i : Fin t => (Z i ω).1) ∧ ∑ i ∈ range t, (Z i ω).2 = k} ≤
      2 / (t : ℝ≥0∞) * P {ω | ∑ i ∈ range t, (Z i ω).2 = k} := by
  rw [marked_cyclic_identity hZ eps ht k]
  have hSm : MeasurableSet {ω | ∑ i ∈ range t, (Z i ω).2 = k} :=
    (Finset.measurable_sum _ fun i _ => (hZ.measurable i).snd) (measurableSet_singleton k)
  have hae : ∀ᵐ ω ∂P, ∀ i, 0 < (Z i ω).1 := ae_all_iff.2 hpos
  have hle : ∫⁻ ω, {ω | ∑ i ∈ range t, (Z i ω).2 = k}.indicator
      (fun ω => (cyclicCount eps (fun i : Fin t => (Z i ω).1) : ℝ≥0∞)) ω ∂P ≤
        ∫⁻ ω, {ω | ∑ i ∈ range t, (Z i ω).2 = k}.indicator (fun _ => (2 : ℝ≥0∞)) ω ∂P := by
    refine lintegral_mono_ae (hae.mono fun ω hω => ?_)
    refine Set.indicator_le_indicator ?_
    exact_mod_cast cyclicCount_le_two heps (fun i => hω i)
  rw [lintegral_indicator_const hSm] at hle
  calc (t : ℝ≥0∞)⁻¹ * _ ≤ (t : ℝ≥0∞)⁻¹ * (2 * P {ω | ∑ i ∈ range t, (Z i ω).2 = k}) := by
        gcongr
    _ = 2 / (t : ℝ≥0∞) * P {ω | ∑ i ∈ range t, (Z i ω).2 = k} := by
        rw [div_eq_mul_inv]
        ring

/-- The marked cyclic-two estimate for the first ALG-OPT segment of the pair sequence:
`P(τ = t, pairRank t = k) ≤ (2 / t) P(pairRank t = k)`. -/
theorem marked_cyclic_two_pairSegLen [IsProbabilityMeasure P] (hZ : IIDPairs P Z) {eps : ℝ}
    (heps : 0 ≤ eps) (hpos : ∀ i, ∀ᵐ ω ∂P, 0 < (Z i ω).1) {t : ℕ} (ht : 0 < t) (k : ℕ) :
    P {ω | pairSegLen eps (seq Z ω) = t ∧ pairRank (seq Z ω) t = k} ≤
      2 / (t : ℝ≥0∞) * P {ω | pairRank (seq Z ω) t = k} := by
  have hset : {ω | pairSegLen eps (seq Z ω) = t ∧ pairRank (seq Z ω) t = k} =
      {ω | stopsAt eps (fun i : Fin t => (Z i ω).1) ∧ ∑ i ∈ range t, (Z i ω).2 = k} := by
    ext ω
    exact and_congr (stopsAt_iff_pairSegLen (seq Z ω) t).symm Iff.rfl
  rw [hset]
  exact marked_cyclic_two hZ heps hpos ht k

end Marked

end PGM
