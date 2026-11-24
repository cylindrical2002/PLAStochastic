import PLAStochastic.Index.KEP.CountRoute.WindowTrials

/-!
# Expected layer size from a window quantile condition

Source: `pgm-analysis/research/2026-09-28-kep-additive/count-route.md`, §3.1 (conditional
counting theorem) and `conditional-assembly.md`, §5.  The induction over layers is replaced
by a tail recursion on a single sample: the suffix window of layer `L + 1` is controlled by
the suffix window of layer `L` (deterministic contraction, `winCount_succ_le`) plus a bridge
window handled by the adaptive trials of `integral_winCount_le`.

Fix depths `D : ℕ → ℕ` and gaps `g : ℕ → ℕ` (`1 ≤ g L`), and the **window quantile
condition**: for every layer `L ≥ 1`, rank `r`, remaining count `m` with `r + 1 + m = N` and
`D L ≤ m`, and anchor value `u ∈ [0, 1)`, the anchored pairs `anchPairsW Q u w`,
`w ∼ orderLaw m`, have leading layer-`L` pivot at least `g L` with probability at least `p`.
Write `𝔥 L = N - D L` for the horizon of layer `L` and `q = ⌊2 eps⌋₊ + 1`.

* **Head** (`integral_winCount_head_le`): `E #{layer-L pivots < 𝔥 L} ≤ (N / g L + 2) / p`.
* **Bridge** (`integral_winCount_bridge_le`):
  `E #{layer-L pivots in [𝔥 (L+1), 𝔥 L)} ≤ (D (L+1) / g L + 2) / p`.
* **Tail** (`integral_winCount_tail_le`): if `D (L+1) / g L ≤ Wb` for all `L ≥ 1`, then for
  every `L`, `E #{layer-L pivots in [𝔥 L, N)} ≤ (Wb + 2) / p + q + D 0 + D 1`; proved by
  the recursion `tail (L+1) ≤ (bridge L + tail L) / q + 1` with `q ≥ 2` (`eps ≥ 1/2`).
* **Layer size** (`integral_epLayer_snd_le_of_window_quantile`): for `L ≥ 1`,
  `E[layer-L size] ≤ (N / g L + 2) / p + ((Wb + 2) / p + q + D 0 + D 1)`.
-/

set_option autoImplicit false

namespace PGM

noncomputable section

open MeasureTheory Finset

section

variable {N : ℕ} {Q : ℝ → ℝ} {eps : ℝ}

/-! ## Integrability and elementary integral bounds -/

theorem integrable_winCount_samplePairs (hQ : Measurable Q) (heps : 0 ≤ eps) {L a b : ℕ}
    (hb : b ≤ N) :
    Integrable (fun v : Fin N → ℝ => (winCount eps (samplePairs Q v) L a b : ℝ))
      (Renyi.orderLaw N) := by
  have hint : ∀ i ∈ range N,
      Integrable (fun v => (winActive eps Q L a b N i).indicator 1 v) (Renyi.orderLaw N) :=
    fun i _ => (integrable_const (1 : ℝ)).indicator (measurableSet_winActive hQ eps L a b i)
  exact (integrable_finsetSum _ hint).congr
    (ae_of_all _ fun v => (winCount_samplePairs_eq_sum_indicator heps Q hb v).symm)

theorem integral_winCount_le_const (hQ : Measurable Q) (heps : 0 ≤ eps) {L a b : ℕ}
    (hb : b ≤ N) {c : ℝ} (h : ∀ v : Fin N → ℝ, (winCount eps (samplePairs Q v) L a b : ℝ) ≤ c) :
    ∫ v, (winCount eps (samplePairs Q v) L a b : ℝ) ∂(Renyi.orderLaw N) ≤ c := by
  calc ∫ v, (winCount eps (samplePairs Q v) L a b : ℝ) ∂(Renyi.orderLaw N)
      ≤ ∫ _v, c ∂(Renyi.orderLaw N) :=
        integral_mono (integrable_winCount_samplePairs hQ heps hb) (integrable_const _) h
    _ = c := by simp

theorem integral_winCount_nonneg {L a b : ℕ} :
    0 ≤ ∫ v, (winCount eps (samplePairs Q v) L a b : ℝ) ∂(Renyi.orderLaw N) :=
  integral_nonneg fun _ => Nat.cast_nonneg _

/-- **Window splitting, in expectation.** -/
theorem integral_winCount_le_add (hQ : Measurable Q) (heps : 0 ≤ eps) (L : ℕ) {a c b : ℕ}
    (hcb : c ≤ b) (hb : b ≤ N) :
    ∫ v, (winCount eps (samplePairs Q v) L a b : ℝ) ∂(Renyi.orderLaw N) ≤
      ∫ v, (winCount eps (samplePairs Q v) L a c : ℝ) ∂(Renyi.orderLaw N) +
        ∫ v, (winCount eps (samplePairs Q v) L c b : ℝ) ∂(Renyi.orderLaw N) := by
  have h1 := integrable_winCount_samplePairs hQ heps (L := L) (a := a) (hcb.trans hb)
  have h2 := integrable_winCount_samplePairs hQ heps (L := L) (a := c) hb
  rw [← integral_add h1 h2]
  refine integral_mono (integrable_winCount_samplePairs hQ heps hb) (h1.add h2) fun v => ?_
  have := winCount_le_winCount_add heps (samplePairs_snd Q v)
    (allLayersFinite_samplePairs eps Q v) L (a := a) hcb
  exact (Nat.cast_le.2 this).trans (le_of_eq (Nat.cast_add _ _))

/-- **One-layer contraction, in expectation.** -/
theorem integral_winCount_succ_le (hQ : Measurable Q) (heps : 0 ≤ eps) (L a : ℕ) {b : ℕ}
    (hb : b ≤ N) :
    ∫ v, (winCount eps (samplePairs Q v) (L + 1) a b : ℝ) ∂(Renyi.orderLaw N) ≤
      (∫ v, (winCount eps (samplePairs Q v) L a b : ℝ) ∂(Renyi.orderLaw N)) /
        (⌊2 * eps⌋₊ + 1 : ℝ) + 1 := by
  have hint := integrable_winCount_samplePairs hQ heps (L := L) (a := a) hb
  have hval : ∫ v, ((winCount eps (samplePairs Q v) L a b : ℝ) / (⌊2 * eps⌋₊ + 1 : ℝ) + 1)
      ∂(Renyi.orderLaw N) =
      (∫ v, (winCount eps (samplePairs Q v) L a b : ℝ) ∂(Renyi.orderLaw N)) /
        (⌊2 * eps⌋₊ + 1 : ℝ) + 1 := by
    rw [integral_add (hint.div_const _) (integrable_const _), integral_div, integral_const]
    simp
  rw [← hval]
  exact integral_mono (integrable_winCount_samplePairs hQ heps hb)
    ((hint.div_const _).add (integrable_const _)) fun v =>
      winCount_succ_le_real heps (samplePairs_snd Q v) (allLayersFinite_samplePairs eps Q v) L a b

/-! ## Head and bridge windows -/

/-- **Head.**  The expected number of layer-`L` pivots before the horizon `N - D` is at most
    `(N / g + 2) / p`, under the quantile condition at depth `D` and gap `g`. -/
theorem integral_winCount_head_le (hQ : Measurable Q) (heps : 0 ≤ eps) {L D g : ℕ}
    (hg : 1 ≤ g) {p : ℝ} (hp : 0 < p)
    (hS : ∀ r m, r + 1 + m = N → D ≤ m → ∀ u : ℝ, 0 ≤ u → u < 1 →
      ENNReal.ofReal p ≤ Renyi.orderLaw m {w | g ≤ layerPivot eps (anchPairsW Q u w) L 1}) :
    ∫ v, (winCount eps (samplePairs Q v) L 0 (N - D) : ℝ) ∂(Renyi.orderLaw N) ≤
      ((N : ℝ) / g + 2) / p := by
  refine (integral_winCount_le hQ heps (a := 0) (𝔥 := N - D) (gap₀ := g) (by omega) hg hp
    ?_).trans ?_
  · intro r _ hr m hm u hu0 hu1
    refine (hS r m hm (by omega) u hu0 hu1).trans (measure_mono fun w hw => ?_)
    simp only [Set.mem_ofPred_eq] at hw ⊢
    exact (min_le_left _ _).trans hw
  · have h : ((N - D - 0 : ℕ) : ℝ) ≤ N := by exact_mod_cast (by omega : N - D - 0 ≤ N)
    have hg' : (0 : ℝ) ≤ g := Nat.cast_nonneg _
    exact div_le_div_of_nonneg_right
      (add_le_add (div_le_div_of_nonneg_right h hg') le_rfl) hp.le

/-- **Bridge.**  The expected number of layer-`L` pivots in `[N - D', N - D)` is at most
    `(D' / g + 2) / p`, under the quantile condition at depth `D` and gap `g`. -/
theorem integral_winCount_bridge_le (hQ : Measurable Q) (heps : 0 ≤ eps) {L D D' g : ℕ}
    (hg : 1 ≤ g) {p : ℝ} (hp : 0 < p)
    (hS : ∀ r m, r + 1 + m = N → D ≤ m → ∀ u : ℝ, 0 ≤ u → u < 1 →
      ENNReal.ofReal p ≤ Renyi.orderLaw m {w | g ≤ layerPivot eps (anchPairsW Q u w) L 1}) :
    ∫ v, (winCount eps (samplePairs Q v) L (N - D') (N - D) : ℝ) ∂(Renyi.orderLaw N) ≤
      ((D' : ℝ) / g + 2) / p := by
  refine (integral_winCount_le hQ heps (a := N - D') (𝔥 := N - D) (gap₀ := g) (by omega) hg hp
    ?_).trans ?_
  · intro r _ hr m hm u hu0 hu1
    refine (hS r m hm (by omega) u hu0 hu1).trans (measure_mono fun w hw => ?_)
    simp only [Set.mem_ofPred_eq] at hw ⊢
    exact (min_le_left _ _).trans hw
  · have h : ((N - D - (N - D') : ℕ) : ℝ) ≤ D' := by
      exact_mod_cast (by omega : N - D - (N - D') ≤ D')
    have hg' : (0 : ℝ) ≤ g := Nat.cast_nonneg _
    exact div_le_div_of_nonneg_right
      (add_le_add (div_le_div_of_nonneg_right h hg') le_rfl) hp.le

/-! ## The suffix window: tail recursion -/

/-- `q = ⌊2 eps⌋₊ + 1 ≥ 2` for `eps ≥ 1/2`. -/
theorem two_le_floor_add_one (heps : 1 / 2 ≤ eps) : (2 : ℝ) ≤ (⌊2 * eps⌋₊ + 1 : ℝ) := by
  have h : 1 ≤ ⌊2 * eps⌋₊ := Nat.le_floor (by push_cast; linarith)
  have h' : (1 : ℝ) ≤ (⌊2 * eps⌋₊ : ℝ) := by exact_mod_cast h
  linarith

/-- **Tail.**  Under the window quantile condition for all layers `L ≥ 1` with
    `D (L+1) / g L ≤ Wb`, the expected number of layer-`L` pivots in the suffix window
    `[N - D L, N)` is at most `(Wb + 2) / p + q + D 0 + D 1`, uniformly in `L` and `N`. -/
theorem integral_winCount_tail_le (hQ : Measurable Q) (heps : 1 / 2 ≤ eps) {D g : ℕ → ℕ}
    (hg : ∀ L, 1 ≤ g L) {p Wb : ℝ} (hp : 0 < p)
    (hW : ∀ L, 1 ≤ L → (D (L + 1) : ℝ) / g L ≤ Wb)
    (hS : ∀ L, 1 ≤ L → ∀ r m, r + 1 + m = N → D L ≤ m → ∀ u : ℝ, 0 ≤ u → u < 1 →
      ENNReal.ofReal p ≤ Renyi.orderLaw m {w | g L ≤ layerPivot eps (anchPairsW Q u w) L 1}) :
    ∀ L, ∫ v, (winCount eps (samplePairs Q v) L (N - D L) N : ℝ) ∂(Renyi.orderLaw N) ≤
      (Wb + 2) / p + (⌊2 * eps⌋₊ + 1 : ℝ) + D 0 + D 1 := by
  have heps0 : 0 ≤ eps := by linarith
  set q : ℝ := (⌊2 * eps⌋₊ + 1 : ℝ) with hqdef
  have hq2 : (2 : ℝ) ≤ q := two_le_floor_add_one heps
  have hq0 : 0 < q := by linarith
  have hWb : 0 ≤ Wb := le_trans (by positivity) (hW 1 le_rfl)
  have hWp : 0 ≤ (Wb + 2) / p := by positivity
  have hD0 : (0 : ℝ) ≤ D 0 := Nat.cast_nonneg _
  have hD1 : (0 : ℝ) ≤ D 1 := Nat.cast_nonneg _
  set C : ℝ := (Wb + 2) / p + q + D 0 + D 1 with hCdef
  have hC0 : 0 ≤ C := by linarith
  -- layer `0`: the suffix window `[N - D', N)` holds `min D' N ≤ D'` pivots
  have hzero : ∀ D' : ℕ, ∫ v, (winCount eps (samplePairs Q v) 0 (N - D') N : ℝ)
      ∂(Renyi.orderLaw N) ≤ D' := by
    intro D'
    refine integral_winCount_le_const hQ heps0 le_rfl fun v => ?_
    rw [winCount_zero eps (samplePairs_snd Q v)]
    exact_mod_cast (by omega : N - (N - D') ≤ D')
  intro L
  induction L with
  | zero => exact (hzero (D 0)).trans (by linarith)
  | succ L ih =>
    cases L with
    | zero =>
      have h1 := integral_winCount_succ_le hQ heps0 0 (N - D 1) (le_refl N)
      have h2 := hzero (D 1)
      have h3 : (∫ v, (winCount eps (samplePairs Q v) 0 (N - D 1) N : ℝ) ∂(Renyi.orderLaw N)) / q
          ≤ ∫ v, (winCount eps (samplePairs Q v) 0 (N - D 1) N : ℝ) ∂(Renyi.orderLaw N) :=
        div_le_self integral_winCount_nonneg (by linarith)
      linarith
    | succ L =>
      -- `tail (L+2) ≤ (bridge (L+1) + tail (L+1)) / q + 1`
      have h1 := integral_winCount_succ_le hQ heps0 (L + 1) (N - D (L + 2)) (le_refl N)
      have h2 := integral_winCount_le_add hQ heps0 (L + 1) (a := N - D (L + 2))
        (c := N - D (L + 1)) (b := N) (by omega) le_rfl
      have hbridge := integral_winCount_bridge_le hQ heps0 (L := L + 1) (D := D (L + 1))
        (D' := D (L + 2)) (hg (L + 1)) hp (hS (L + 1) (by omega))
      have hbridge' : ((D (L + 2) : ℝ) / g (L + 1) + 2) / p ≤ (Wb + 2) / p :=
        div_le_div_of_nonneg_right (add_le_add (hW (L + 1) (by omega)) le_rfl) hp.le
      have hsum : ∫ v, (winCount eps (samplePairs Q v) (L + 1) (N - D (L + 2)) N : ℝ)
          ∂(Renyi.orderLaw N) ≤ (Wb + 2) / p + C := by linarith
      have hdiv : (∫ v, (winCount eps (samplePairs Q v) (L + 1) (N - D (L + 2)) N : ℝ)
          ∂(Renyi.orderLaw N)) / q ≤ ((Wb + 2) / p + C) / q :=
        div_le_div_of_nonneg_right hsum hq0.le
      -- closing the recursion: `((Wb + 2) / p + C) / q + 1 ≤ C` since `q ≥ 2`
      have hclose : ((Wb + 2) / p + C) / q + 1 ≤ C := by
        rw [div_add_one hq0.ne', div_le_iff₀ hq0]
        have hCq : C * 1 ≤ C * (q - 1) := mul_le_mul_of_nonneg_left (by linarith) hC0
        have hC' : (Wb + 2) / p + q ≤ C := by linarith
        nlinarith
      linarith

/-! ## Expected layer size -/

/-- **Expected layer-`L` size from the window quantile condition.**  For `L ≥ 1`,
    `E[(epLayer eps (extendKeys (Q ∘ v)) N L).2] ≤ (N / g L + 2) / p + R`, `v ∼ orderLaw N`,
    with the uniform remainder `R = (Wb + 2) / p + q + D 0 + D 1`, `q = ⌊2 eps⌋₊ + 1`. -/
theorem integral_epLayer_snd_le_of_window_quantile (hQ : Measurable Q) (heps : 1 / 2 ≤ eps)
    {D g : ℕ → ℕ} (hg : ∀ L, 1 ≤ g L) {p Wb : ℝ} (hp : 0 < p)
    (hW : ∀ L, 1 ≤ L → (D (L + 1) : ℝ) / g L ≤ Wb)
    (hS : ∀ L, 1 ≤ L → ∀ r m, r + 1 + m = N → D L ≤ m → ∀ u : ℝ, 0 ≤ u → u < 1 →
      ENNReal.ofReal p ≤ Renyi.orderLaw m {w | g L ≤ layerPivot eps (anchPairsW Q u w) L 1})
    {L : ℕ} (hL : 1 ≤ L) :
    ∫ v, ((epLayer eps (extendKeys (Q ∘ v)) N L).2 : ℝ) ∂(Renyi.orderLaw N) ≤
      ((N : ℝ) / g L + 2) / p + ((Wb + 2) / p + (⌊2 * eps⌋₊ + 1 : ℝ) + D 0 + D 1) := by
  have heps0 : 0 ≤ eps := by linarith
  have hid : ∀ v : Fin N → ℝ, ((epLayer eps (extendKeys (Q ∘ v)) N L).2 : ℝ) =
      (winCount eps (samplePairs Q v) L 0 N : ℝ) := by
    intro v
    rw [epLayer_snd_eq_card_samplePivot heps0 Q v L]
    unfold winCount
    congr 2
    ext j
    simp [samplePivot]
  calc ∫ v, ((epLayer eps (extendKeys (Q ∘ v)) N L).2 : ℝ) ∂(Renyi.orderLaw N)
      = ∫ v, (winCount eps (samplePairs Q v) L 0 N : ℝ) ∂(Renyi.orderLaw N) :=
        integral_congr_ae (ae_of_all _ hid)
    _ ≤ ∫ v, (winCount eps (samplePairs Q v) L 0 (N - D L) : ℝ) ∂(Renyi.orderLaw N) +
        ∫ v, (winCount eps (samplePairs Q v) L (N - D L) N : ℝ) ∂(Renyi.orderLaw N) :=
        integral_winCount_le_add hQ heps0 L (by omega) le_rfl
    _ ≤ _ := add_le_add (integral_winCount_head_le hQ heps0 (hg L) hp (hS L hL))
        (integral_winCount_tail_le hQ heps hg hp hW hS L)

end

end

end PGM
