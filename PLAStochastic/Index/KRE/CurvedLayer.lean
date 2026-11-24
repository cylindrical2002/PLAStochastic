import PLAStochastic.Index.Algorithm.GreedyMinimality
import PLAStochastic.Index.Algorithm.SlopeTransfer
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Sqrt

/-!
# One lattice layer of ALG-RE under a smooth monotone change of keys

Deterministic layer step for Model K.  The reference keys `z` are strictly
increasing (for instance the partial sums `z t = ∑ i < t + 1, e i` of positive
gaps, `strictMono_sum_range_succ`), the normaliser `S` puts `z t / S` into
`[0, 1]` for `t < N`, and the curved keys are `φ (z t / S)` with `φ' ≥ δ > 0` and
`φ'` `L`-Lipschitz on `[0, 1]`.  A lattice layer of spacing `Δ ≥ 1` and size `K`
(`(K - 1) Δ < N`) reads the reference lattice keys `z (j Δ)` and the curved
lattice keys `φ (z (j Δ) / S)`.  The good event supplies the span bound
`z b - z a ≤ Kst ((b - a) + log N)` and `N / 2 ≤ S` (`CurvedLattice`), and for the
short-window bound also the tube bound
`|z b - z a - (b - a)| ≤ Kst (√((b - a) log N) + log N)`.

With `Ψbar τ θ = (τ + 2θ) (L / (2δ)) Kst (τ Δ + log N) / (N / 2)`:

* window transfer: a window of at most `τ + 1` lattice keys that is `θ`-feasible for
  the reference keys is `(θ + Ψbar τ θ)`-feasible for the curved keys, and conversely
  (`CurvedLattice.curved_of_feasible`, `CurvedLattice.of_feasible_curved`);
* noise-regime upper bound: `finSegCount eps curved ≤ finSegCount (eps/2) ref + K / τ₀`
  when `eps/2 + Ψbar τ₀ (eps/2) ≤ eps` (`CurvedLattice.finSegCount_curved_le`);
* noise-regime lower bound: `finSegCount (2 eps) ref ≤ finSegCount eps curved` when
  `eps + Ψbar τ₁ eps ≤ 2 eps` and no window of `τ₁` reference lattice keys is
  `2 eps`-feasible (`CurvedLattice.finSegCount_le_curved`);
* short windows: under the tube bound, every window of at most `τb` curved lattice
  keys is `eps`-feasible, hence `finSegCount eps curved ≤ K / τb + 1`
  (`CurvedLattice.curved_short_feasible`, `CurvedLattice.finSegCount_curved_le_div`).
-/

namespace PGM

open Finset

/-- Partial sums of positive gaps are strictly increasing. -/
theorem strictMono_sum_range_succ {e : ℕ → ℝ} (he : ∀ i, 0 < e i) :
    StrictMono fun t => ∑ i ∈ range (t + 1), e i :=
  strictMono_nat_of_lt_succ fun t => by
    rw [Finset.sum_range_succ _ (t + 1)]
    linarith [he (t + 1)]

/-- Deterministic setting of one lattice layer with curved keys `φ (z t / S)`: the
    reference keys `z` are strictly increasing, `z t / S ∈ [0, 1]` for `t < N`, `φ` has
    derivative `φ' ≥ δ > 0` within `[0, 1]` and `φ'` is `L`-Lipschitz there, the lattice
    of spacing `Δ ≥ 1` and size `K` fits into `[0, N)`, and the good-event span bound and
    `N / 2 ≤ S` hold. -/
structure CurvedLattice (φ φ' : ℝ → ℝ) (z : ℕ → ℝ) (S L δ Kst : ℝ) (N Δ K : ℕ) : Prop where
  strictMono : StrictMono z
  deriv : ∀ x ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt φ (φ' x) (Set.Icc 0 1) x
  lip : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1, |φ' x - φ' y| ≤ L * |x - y|
  delta_pos : 0 < δ
  le_deriv : ∀ x ∈ Set.Icc (0 : ℝ) 1, δ ≤ φ' x
  mem_Icc : ∀ t < N, z t / S ∈ Set.Icc (0 : ℝ) 1
  one_le_spacing : 1 ≤ Δ
  size : (K - 1) * Δ < N
  Kst_nonneg : 0 ≤ Kst
  span : ∀ a b : ℕ, a ≤ b → b < N → z b - z a ≤ Kst * ((b - a : ℝ) + Real.log N)
  half_le : (N : ℝ) / 2 ≤ S

namespace CurvedLattice

variable {φ φ' : ℝ → ℝ} {z : ℕ → ℝ} {S L δ Kst : ℝ} {N Δ K : ℕ}

theorem L_nonneg (H : CurvedLattice φ φ' z S L δ Kst N Δ K) : 0 ≤ L := by
  have h := H.lip 1 ⟨zero_le_one, le_rfl⟩ 0 ⟨le_rfl, zero_le_one⟩
  norm_num at h
  exact (abs_nonneg _).trans h

theorem N_pos (H : CurvedLattice φ φ' z S L δ Kst N Δ K) : 0 < N := by
  have := H.size
  omega

theorem half_pos (H : CurvedLattice φ φ' z S L δ Kst N Δ K) : (0 : ℝ) < (N : ℝ) / 2 := by
  have : (0 : ℝ) < N := by exact_mod_cast H.N_pos
  linarith

theorem S_pos (H : CurvedLattice φ φ' z S L δ Kst N Δ K) : 0 < S :=
  lt_of_lt_of_le H.half_pos H.half_le

theorem mul_lt (H : CurvedLattice φ φ' z S L δ Kst N Δ K) {i : ℕ} (hi : i < K) :
    i * Δ < N :=
  lt_of_le_of_lt (Nat.mul_le_mul_right Δ (by omega : i ≤ K - 1)) H.size

/-- The good-event span bound on the lattice. -/
theorem span_le (H : CurvedLattice φ φ' z S L δ Kst N Δ K) {a j : ℕ} (hj : a + j < K) :
    z ((a + j) * Δ) - z (a * Δ) ≤ Kst * ((j * Δ : ℝ) + Real.log N) := by
  have h := H.span (a * Δ) ((a + j) * Δ) (Nat.mul_le_mul_right Δ (Nat.le_add_right a j))
    (H.mul_lt hj)
  have e : (((a + j) * Δ : ℕ) : ℝ) - ((a * Δ : ℕ) : ℝ) = (j : ℝ) * Δ := by
    push_cast
    ring
  rwa [e] at h

/-- `Ψbar τ θ ≥ 0` for `θ ≥ 0`. -/
theorem psi_nonneg (H : CurvedLattice φ φ' z S L δ Kst N Δ K) (τ : ℕ) {θ : ℝ} (hθ : 0 ≤ θ) :
    0 ≤ ((τ : ℝ) + 2 * θ) * (L / (2 * δ)) * (Kst * ((τ * Δ : ℝ) + Real.log N)) / (N / 2) := by
  have hL := H.L_nonneg
  have hδ := H.delta_pos
  have hK := H.Kst_nonneg
  have hlog := Real.log_natCast_nonneg N
  have hN := H.half_pos
  have h1 : 0 ≤ L / (2 * δ) := div_nonneg hL (by linarith)
  have h2 : 0 ≤ Kst * ((τ * Δ : ℝ) + Real.log N) := mul_nonneg hK (by positivity)
  exact div_nonneg (mul_nonneg (mul_nonneg (by positivity) h1) h2) hN.le

/-- The cost of a window of `τ' + 1 ≤ τ + 1` lattice keys with span `D` is at most
    `Ψbar τ θ`. -/
theorem cost_le (H : CurvedLattice φ φ' z S L δ Kst N Δ K) {τ' τ : ℕ} (hτ : τ' ≤ τ)
    {θ D : ℝ} (hθ : 0 ≤ θ) (hD0 : 0 ≤ D) (hD : D ≤ Kst * ((τ * Δ : ℝ) + Real.log N)) :
    ((τ' : ℝ) + 2 * θ) * (L / (2 * δ)) * D / S ≤
      ((τ : ℝ) + 2 * θ) * (L / (2 * δ)) * (Kst * ((τ * Δ : ℝ) + Real.log N)) / (N / 2) := by
  have hτ' : (τ' : ℝ) ≤ τ := by exact_mod_cast hτ
  have hA : 0 ≤ (τ' : ℝ) + 2 * θ := by positivity
  have hLδ : 0 ≤ L / (2 * δ) := div_nonneg H.L_nonneg (by linarith [H.delta_pos])
  have hN := H.half_pos
  calc ((τ' : ℝ) + 2 * θ) * (L / (2 * δ)) * D / S
      ≤ ((τ' : ℝ) + 2 * θ) * (L / (2 * δ)) * D / (N / 2) :=
        div_le_div_of_nonneg_left (mul_nonneg (mul_nonneg hA hLδ) hD0) hN H.half_le
    _ ≤ ((τ : ℝ) + 2 * θ) * (L / (2 * δ)) * (Kst * ((τ * Δ : ℝ) + Real.log N)) / (N / 2) :=
        div_le_div_of_nonneg_right
          (mul_le_mul (mul_le_mul_of_nonneg_right (by linarith) hLδ) hD hD0
            (mul_nonneg (by linarith) hLδ)) hN.le

/-- Span of a window of `τ' + 1` lattice keys starting at `a`. -/
theorem window_span (H : CurvedLattice φ φ' z S L δ Kst N Δ K) {a τ' τ : ℕ}
    (hτ : τ' ≤ τ) (haK : a + τ' < K) :
    0 ≤ z ((a + τ') * Δ) - z ((a + 0) * Δ) ∧
      z ((a + τ') * Δ) - z ((a + 0) * Δ) ≤ Kst * ((τ * Δ : ℝ) + Real.log N) := by
  rw [add_zero]
  refine ⟨sub_nonneg.mpr (H.strictMono.monotone
    (Nat.mul_le_mul_right Δ (Nat.le_add_right a τ'))), (H.span_le haK).trans ?_⟩
  have hτ' : (τ' : ℝ) * Δ ≤ τ * Δ :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hτ) (Nat.cast_nonneg Δ)
  exact mul_le_mul_of_nonneg_left (by linarith) H.Kst_nonneg

/-- The side conditions of the curvature transfer on a window of `τ' + 1` lattice keys. -/
theorem window_mem (H : CurvedLattice φ φ' z S L δ Kst N Δ K) {a τ' : ℕ}
    (haK : a + τ' < K) :
    (∀ j ≤ τ', shiftSeq (fun j => z (j * Δ)) a j / S ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ j ≤ τ', shiftSeq (fun j => z (j * Δ)) a 0 ≤ shiftSeq (fun j => z (j * Δ)) a j ∧
        shiftSeq (fun j => z (j * Δ)) a j ≤ shiftSeq (fun j => z (j * Δ)) a τ') := by
  refine ⟨fun j hj => H.mem_Icc _ (H.mul_lt (by omega)), fun j hj => ?_⟩
  simp only [shiftSeq_apply]
  exact ⟨H.strictMono.monotone (Nat.mul_le_mul_right Δ (by omega)),
    H.strictMono.monotone (Nat.mul_le_mul_right Δ (by omega))⟩

/-- A window of at least two lattice keys has positive span. -/
theorem window_lt (H : CurvedLattice φ φ' z S L δ Kst N Δ K) {a τ' : ℕ} (hτ' : 1 ≤ τ') :
    shiftSeq (fun j => z (j * Δ)) a 0 < shiftSeq (fun j => z (j * Δ)) a τ' := by
  simp only [shiftSeq_apply]
  exact H.strictMono (Nat.mul_lt_mul_of_pos_right (by omega) (by have := H.one_le_spacing; omega))

/-- A nonempty feasible prefix forces a nonnegative tolerance. -/
theorem nonneg_of_feasible {θ : ℝ} {p : ℕ → ℝ} {len : ℕ} (hlen : 1 ≤ len)
    (h : prefixAffineFeasible θ p len) : 0 ≤ θ := by
  obtain ⟨_, _, hab⟩ := h
  exact (abs_nonneg _).trans (hab 0 (by omega))

/-- **Window transfer, forward.**  A window of `len ≤ τ + 1` reference lattice keys
    that is `θ`-feasible is `(θ + Ψbar τ θ)`-feasible for the curved lattice keys. -/
theorem curved_of_feasible (H : CurvedLattice φ φ' z S L δ Kst N Δ K) {θ : ℝ}
    {τ a len : ℕ} (hlen : len ≤ τ + 1) (haK : a + len ≤ K)
    (h : prefixAffineFeasible θ (shiftSeq (fun j => z (j * Δ)) a) len) :
    prefixAffineFeasible
      (θ + ((τ : ℝ) + 2 * θ) * (L / (2 * δ)) * (Kst * ((τ * Δ : ℝ) + Real.log N)) / (N / 2))
      (shiftSeq (fun j => φ (z (j * Δ) / S)) a) len := by
  rcases Nat.eq_zero_or_pos len with h0 | hpos
  · subst h0
    exact prefixAffineFeasible_zero _ _
  have hθ := nonneg_of_feasible hpos h
  obtain ⟨τ', rfl⟩ : ∃ τ', len = τ' + 1 := ⟨len - 1, by omega⟩
  rcases Nat.eq_zero_or_pos τ' with h0 | hτ'
  · subst h0
    exact prefixAffineFeasible_one (by linarith [H.psi_nonneg τ hθ]) _
  obtain ⟨hzI, hz⟩ := H.window_mem (a := a) (τ' := τ') (by omega)
  have ht := prefixAffineFeasible_curved_of_feasible (I := Set.Icc (0 : ℝ) 1)
    (z := shiftSeq (fun j => z (j * Δ)) a) (τ := τ') Set.ordConnected_Icc H.deriv H.lip
    H.delta_pos H.le_deriv H.S_pos hzI hz (H.window_lt hτ') h
  obtain ⟨hD0, hD⟩ := H.window_span (a := a) (τ' := τ') (τ := τ) (by omega) (by omega)
  exact prefixAffineFeasible_of_le ht
    (add_le_add le_rfl (H.cost_le (τ' := τ') (by omega) hθ hD0 hD))

/-- **Window transfer, reverse.**  A window of `len ≤ τ + 1` curved lattice keys that
    is `θ`-feasible is `(θ + Ψbar τ θ)`-feasible for the reference lattice keys. -/
theorem of_feasible_curved (H : CurvedLattice φ φ' z S L δ Kst N Δ K) {θ : ℝ}
    {τ a len : ℕ} (hlen : len ≤ τ + 1) (haK : a + len ≤ K)
    (h : prefixAffineFeasible θ (shiftSeq (fun j => φ (z (j * Δ) / S)) a) len) :
    prefixAffineFeasible
      (θ + ((τ : ℝ) + 2 * θ) * (L / (2 * δ)) * (Kst * ((τ * Δ : ℝ) + Real.log N)) / (N / 2))
      (shiftSeq (fun j => z (j * Δ)) a) len := by
  rcases Nat.eq_zero_or_pos len with h0 | hpos
  · subst h0
    exact prefixAffineFeasible_zero _ _
  have hθ := nonneg_of_feasible hpos h
  obtain ⟨τ', rfl⟩ : ∃ τ', len = τ' + 1 := ⟨len - 1, by omega⟩
  rcases Nat.eq_zero_or_pos τ' with h0 | hτ'
  · subst h0
    exact prefixAffineFeasible_one (by linarith [H.psi_nonneg τ hθ]) _
  obtain ⟨hzI, hz⟩ := H.window_mem (a := a) (τ' := τ') (by omega)
  have ht := prefixAffineFeasible_of_feasible_curved (I := Set.Icc (0 : ℝ) 1)
    (z := shiftSeq (fun j => z (j * Δ)) a) (τ := τ') Set.ordConnected_Icc H.deriv H.lip
    H.delta_pos H.le_deriv H.S_pos hzI hz (H.window_lt hτ') h
  obtain ⟨hD0, hD⟩ := H.window_span (a := a) (τ' := τ') (τ := τ) (by omega) (by omega)
  exact prefixAffineFeasible_of_le ht
    (add_le_add le_rfl (H.cost_le (τ' := τ') (by omega) hθ hD0 hD))

/-- **Window transfer, forward** (window form): `[a, b)` with `b - a ≤ τ + 1`, `b ≤ K`. -/
theorem windowFeasible_curved_of_feasible (H : CurvedLattice φ φ' z S L δ Kst N Δ K)
    {θ : ℝ} {τ a b : ℕ} (hab : b - a ≤ τ + 1) (hbK : b ≤ K)
    (h : windowFeasible θ (fun j => z (j * Δ)) a b) :
    windowFeasible
      (θ + ((τ : ℝ) + 2 * θ) * (L / (2 * δ)) * (Kst * ((τ * Δ : ℝ) + Real.log N)) / (N / 2))
      (fun j => φ (z (j * Δ) / S)) a b := by
  unfold windowFeasible at h ⊢
  rcases le_or_gt a b with hle | hlt
  · exact H.curved_of_feasible hab (by omega) h
  · rw [Nat.sub_eq_zero_of_le hlt.le]
    exact prefixAffineFeasible_zero _ _

/-- **Window transfer, reverse** (window form): `[a, b)` with `b - a ≤ τ + 1`, `b ≤ K`. -/
theorem windowFeasible_of_feasible_curved (H : CurvedLattice φ φ' z S L δ Kst N Δ K)
    {θ : ℝ} {τ a b : ℕ} (hab : b - a ≤ τ + 1) (hbK : b ≤ K)
    (h : windowFeasible θ (fun j => φ (z (j * Δ) / S)) a b) :
    windowFeasible
      (θ + ((τ : ℝ) + 2 * θ) * (L / (2 * δ)) * (Kst * ((τ * Δ : ℝ) + Real.log N)) / (N / 2))
      (fun j => z (j * Δ)) a b := by
  unfold windowFeasible at h ⊢
  rcases le_or_gt a b with hle | hlt
  · exact H.of_feasible_curved hab (by omega) h
  · rw [Nat.sub_eq_zero_of_le hlt.le]
    exact prefixAffineFeasible_zero _ _

/-- **Noise-regime upper bound.**  If `1 ≤ τ₀` and `eps/2 + Ψbar τ₀ (eps/2) ≤ eps`, the
    curved lattice keys need at most `finSegCount (eps/2) ref + K / τ₀` segments. -/
theorem finSegCount_curved_le (H : CurvedLattice φ φ' z S L δ Kst N Δ K) {eps : ℝ}
    {τ₀ : ℕ} (heps : 0 ≤ eps) (hτ₀ : 1 ≤ τ₀)
    (hΨ : eps / 2 + ((τ₀ : ℝ) + 2 * (eps / 2)) * (L / (2 * δ)) *
      (Kst * ((τ₀ * Δ : ℝ) + Real.log N)) / (N / 2) ≤ eps) :
    finSegCount eps (fun j => φ (z (j * Δ) / S)) K ≤
      finSegCount (eps / 2) (fun j => z (j * Δ)) K + K / τ₀ := by
  obtain ⟨m, c, hc, hm⟩ := exists_short_windowPartition (by linarith : (0 : ℝ) ≤ eps / 2)
    (fun j => z (j * Δ)) K hτ₀
  have hc' : WindowPartition (windowFeasible eps (fun j => φ (z (j * Δ) / S))) K m c :=
    { start := hc.start
      finish := hc.finish
      lt_succ := hc.lt_succ
      window := fun i hi => by
        obtain ⟨hw, hlen⟩ := hc.window i hi
        exact prefixAffineFeasible_of_le (H.windowFeasible_curved_of_feasible (τ := τ₀)
          (by omega) (hc.le_finish (by omega : i + 1 ≤ m)) hw) hΨ }
  exact (finSegCount_le_of_partition hc').trans hm

/-- **Noise-regime lower bound.**  If `eps + Ψbar τ₁ eps ≤ 2 eps` and no window of `τ₁`
    reference lattice keys is `2 eps`-feasible, the curved lattice keys need at least
    `finSegCount (2 eps) ref` segments. -/
theorem finSegCount_le_curved (H : CurvedLattice φ φ' z S L δ Kst N Δ K) {eps : ℝ}
    {τ₁ : ℕ}
    (hΨ : eps + ((τ₁ : ℝ) + 2 * eps) * (L / (2 * δ)) *
      (Kst * ((τ₁ * Δ : ℝ) + Real.log N)) / (N / 2) ≤ 2 * eps)
    (hV : ∀ a, a + τ₁ ≤ K → ¬ windowFeasible (2 * eps) (fun j => z (j * Δ)) a (a + τ₁)) :
    finSegCount (2 * eps) (fun j => z (j * Δ)) K ≤
      finSegCount eps (fun j => φ (z (j * Δ) / S)) K := by
  apply finSegCount_le_of_windowFeasible
  intro a b hab hbK hw
  have hlen : b - a < τ₁ := by
    by_contra hge
    have hsub : windowFeasible eps (fun j => φ (z (j * Δ) / S)) a (a + τ₁) :=
      windowFeasible_sub hw le_rfl (by omega) (by omega)
    exact hV a (by omega) (prefixAffineFeasible_of_le
      (H.windowFeasible_of_feasible_curved (τ := τ₁) (by omega) (by omega) hsub) hΨ)
  exact prefixAffineFeasible_of_le
    (H.windowFeasible_of_feasible_curved (τ := τ₁) (by omega) hbK hw) hΨ

/-- The good-event tube bound on a window of lattice keys: the reference keys
    `z ((a + j) Δ)`, `j ≤ τ'`, stay within `x` of the line `z (a Δ) + j Δ`. -/
theorem window_tube (H : CurvedLattice φ φ' z S L δ Kst N Δ K)
    (htube : ∀ a b : ℕ, a ≤ b → b < N →
      |z b - z a - (b - a)| ≤ Kst * (Real.sqrt ((b - a) * Real.log N) + Real.log N))
    {τb : ℕ} {x : ℝ} (hx : Kst * (Real.sqrt (τb * Δ * Real.log N) + Real.log N) ≤ x)
    {a τ' : ℕ} (hτ' : τ' ≤ τb) (haK : a + τ' < K) :
    ∀ j ≤ τ', |shiftSeq (fun j => z (j * Δ)) a j -
      (shiftSeq (fun j => z (j * Δ)) a 0 + j * (Δ : ℝ))| ≤ x := by
  intro j hj
  simp only [shiftSeq_apply, add_zero]
  have h := htube (a * Δ) ((a + j) * Δ) (Nat.mul_le_mul_right Δ (Nat.le_add_right a j))
    (H.mul_lt (by omega))
  have e : (((a + j) * Δ : ℕ) : ℝ) - ((a * Δ : ℕ) : ℝ) = (j : ℝ) * Δ := by
    push_cast
    ring
  rw [e] at h
  have e2 : z ((a + j) * Δ) - (z (a * Δ) + j * (Δ : ℝ)) =
      z ((a + j) * Δ) - z (a * Δ) - j * (Δ : ℝ) := by ring
  rw [e2]
  refine h.trans (le_trans ?_ hx)
  have hlog := Real.log_natCast_nonneg N
  have hj' : (j : ℝ) ≤ τb := by exact_mod_cast hj.trans hτ'
  have hs : (j : ℝ) * Δ * Real.log N ≤ τb * Δ * Real.log N :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hj' (Nat.cast_nonneg Δ)) hlog
  exact mul_le_mul_of_nonneg_left (by linarith [Real.sqrt_le_sqrt hs]) H.Kst_nonneg

/-- **Short windows are feasible.**  Under the tube bound, if
    `x ≥ Kst (√(τb Δ log N) + log N)` and `x / Δ + (τb + 2 x / Δ) (L / (2δ))
    Kst (τb Δ + log N) / (N / 2) ≤ eps`, every window of at most `τb` curved lattice
    keys is `eps`-feasible. -/
theorem curved_short_feasible (H : CurvedLattice φ φ' z S L δ Kst N Δ K)
    (htube : ∀ a b : ℕ, a ≤ b → b < N →
      |z b - z a - (b - a)| ≤ Kst * (Real.sqrt ((b - a) * Real.log N) + Real.log N))
    {eps x : ℝ} {τb : ℕ} (hx : Kst * (Real.sqrt (τb * Δ * Real.log N) + Real.log N) ≤ x)
    (hxeps : x / Δ + ((τb : ℝ) + 2 * (x / Δ)) * (L / (2 * δ)) *
      (Kst * ((τb * Δ : ℝ) + Real.log N)) / (N / 2) ≤ eps) :
    ∀ a len, a + len ≤ K → len ≤ τb →
      prefixAffineFeasible eps (shiftSeq (fun j => φ (z (j * Δ) / S)) a) len := by
  intro a len haK hlen
  have hΔ : (0 : ℝ) < Δ := by have := H.one_le_spacing; exact_mod_cast (by omega : 0 < Δ)
  have hx0 : 0 ≤ x := by
    have hlog := Real.log_natCast_nonneg N
    exact le_trans (mul_nonneg H.Kst_nonneg (by positivity)) hx
  have hxΔ : 0 ≤ x / Δ := div_nonneg hx0 hΔ.le
  have heps : 0 ≤ eps := by linarith [H.psi_nonneg τb hxΔ]
  rcases Nat.eq_zero_or_pos len with h0 | hpos
  · subst h0
    exact prefixAffineFeasible_zero _ _
  obtain ⟨τ', rfl⟩ : ∃ τ', len = τ' + 1 := ⟨len - 1, by omega⟩
  rcases Nat.eq_zero_or_pos τ' with h0 | hτ'
  · subst h0
    exact prefixAffineFeasible_one heps _
  obtain ⟨hzI, hz⟩ := H.window_mem (a := a) (τ' := τ') (by omega)
  have ht := prefixAffineFeasible_curved_of_tube (I := Set.Icc (0 : ℝ) 1)
    (z := shiftSeq (fun j => z (j * Δ)) a) (τ := τ') (x := x) (μ := (Δ : ℝ))
    Set.ordConnected_Icc H.deriv H.lip H.delta_pos H.le_deriv H.S_pos hzI hz
    (H.window_lt hτ') hΔ (H.window_tube htube hx (by omega) (by omega))
  obtain ⟨hD0, hD⟩ := H.window_span (a := a) (τ' := τ') (τ := τb) (by omega) (by omega)
  exact prefixAffineFeasible_of_le ht
    ((add_le_add le_rfl (H.cost_le (τ' := τ') (by omega) hxΔ hD0 hD)).trans hxeps)

/-- **Short-window count bound.**  Under the hypotheses of `curved_short_feasible` and
    `1 ≤ τb`, the curved lattice keys need at most `K / τb + 1` segments. -/
theorem finSegCount_curved_le_div (H : CurvedLattice φ φ' z S L δ Kst N Δ K)
    (htube : ∀ a b : ℕ, a ≤ b → b < N →
      |z b - z a - (b - a)| ≤ Kst * (Real.sqrt ((b - a) * Real.log N) + Real.log N))
    {eps x : ℝ} {τb : ℕ} (hτb : 1 ≤ τb)
    (hx : Kst * (Real.sqrt (τb * Δ * Real.log N) + Real.log N) ≤ x)
    (hxeps : x / Δ + ((τb : ℝ) + 2 * (x / Δ)) * (L / (2 * δ)) *
      (Kst * ((τb * Δ : ℝ) + Real.log N)) / (N / 2) ≤ eps) :
    finSegCount eps (fun j => φ (z (j * Δ) / S)) K ≤ K / τb + 1 :=
  finSegCount_le_div_add_one_of_short hτb (H.curved_short_feasible htube hx hxeps)

end CurvedLattice

end PGM
