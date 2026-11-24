import PLAStochastic.Index.GEP.SurvivalBound.KilledRow.WordExpansion
import PLAStochastic.Index.GEP.RawDisc.ProductLaws

/-!
# WP4 `SurvivalBound`: the complex word functional and its Fubini rules

Source: `research/2026-09-30-lean-gep-direct-term/task-survival.md` (P2), `rawdisc-design.md` §0.

The complex product integral `∫ H d((1 - z) ν + z σ)^{⊗n}` is never formed as a measure; it is the
word sum

`surv_wint ν σ z n H = ∑_{S ⊆ {0,…,n-1}} (1-z)^{n-|S|} z^{|S|} ∫ H d wordLaw ν σ S`

(`surv_wcoef z n S = (1-z)^{n-|S|} z^{|S|}`).  The word expansion of the killed row
(`kRow_eq_sum_words`) says that `kRow J ν σ z β a n φ y₀` is `surv_wint` of the walk integrand.
This file gives the rules used to cut a certificate integrand into rows:

* **coordinate agreement** (`surv_integral_wordLaw_congr`): a functional reading only the
  coordinates in `A` has the same integral under two words that agree on `A`
  (`Measure.infinitePi_map_pi` applied to `A.indicator`);
* **Fubini over disjoint coordinate sets** (`surv_integral_diag`, `surv_integral_diag'`): if
  `F g h` reads `g` only on `A` and `h` only on `B`, `A ∩ B = ∅`, then
  `∫ F g g = ∫∫ F g h` (the projections `A.indicator`, `B.indicator` are independent);
* **prefix Fubini** (`surv_integral_cat`, `surv_wint_cat`): with the concatenation
  `surv_cat n₁ g h`, `surv_wint (n₁ + n₂) H = surv_wint n₁ (g ↦ surv_wint n₂ (h ↦ H (cat n₁ g h)))`;
* **permutations** (`surv_wint_perm`): reindexing by an injective `π` preserving `{0,…,n-1}`;
* **last `ν` letter** (`surv_sum_powerset_last`, `surv_wcoef_last`): a word of length `L` is either
  all `σ` or has a last `ν` letter `m`, after which all letters are `σ`;
* **one-coordinate insertion and translation** (`surv_integral_wordLaw_update`,
  `surv_integral_wordLaw_shift`): at a `ν`-coordinate `m` with density `f`,
  `∫ F = ∫ dt ∫ f(t - R g) F(update g m (t - R g))` for any measurable `R`.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Finset
open scoped ENNReal

/-! ## The word functional -/

/-- The coefficient `(1-z)^{n-|S|} z^{|S|}` of the word `S` of length `n`. -/
def surv_wcoef (z : ℂ) (n : ℕ) (S : Finset ℕ) : ℂ := (1 - z) ^ (n - S.card) * z ^ S.card

/-- The complex word functional `∫ H d((1 - z) ν + z σ)^{⊗n}`, expanded over the words. -/
def surv_wint (ν σ : ProbabilityMeasure ℝ) (z : ℂ) (n : ℕ) (H : (ℕ → ℝ) → ℂ) : ℂ :=
  ∑ S ∈ (Finset.range n).powerset, surv_wcoef z n S * ∫ g, H g ∂(wordLaw ν σ S)

/-- The killed row is the word functional of its walk integrand. -/
theorem kRow_eq_surv_wint {J : Set ℝ} (hJ : MeasurableSet J) (ν σ : ProbabilityMeasure ℝ)
    (z : ℂ) (β a : ℝ) {φ : ℝ → ℂ} (hφ : Measurable φ) {M : ℝ} (hM : ∀ y, ‖φ y‖ ≤ M)
    (n : ℕ) (y₀ : ℝ) :
    kRow J ν σ z β a n φ y₀ = surv_wint ν σ z n (fun g =>
      (∏ l ∈ Finset.range (n + 1), J.indicator (fun _ => (1 : ℂ)) (kWalk y₀ β a g l)) *
        φ (kWalk y₀ β a g n)) :=
  kRow_eq_sum_words hJ ν σ z β a hφ hM n y₀

theorem surv_wint_const_mul (ν σ : ProbabilityMeasure ℝ) (z : ℂ) (n : ℕ) (c : ℂ)
    (H : (ℕ → ℝ) → ℂ) :
    surv_wint ν σ z n (fun g => c * H g) = c * surv_wint ν σ z n H := by
  unfold surv_wint
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [integral_const_mul]
  ring

theorem surv_wint_congr (ν σ : ProbabilityMeasure ℝ) (z : ℂ) (n : ℕ) {H H' : (ℕ → ℝ) → ℂ}
    (h : ∀ S ∈ (Finset.range n).powerset, ∀ᵐ g ∂(wordLaw ν σ S), H g = H' g) :
    surv_wint ν σ z n H = surv_wint ν σ z n H' := by
  unfold surv_wint
  refine Finset.sum_congr rfl fun S hS => ?_
  rw [integral_congr_ae (h S hS)]

theorem surv_wint_add (ν σ : ProbabilityMeasure ℝ) (z : ℂ) (n : ℕ) {H H' : (ℕ → ℝ) → ℂ}
    (h : ∀ S, Integrable H (wordLaw ν σ S)) (h' : ∀ S, Integrable H' (wordLaw ν σ S)) :
    surv_wint ν σ z n (fun g => H g + H' g) = surv_wint ν σ z n H + surv_wint ν σ z n H' := by
  unfold surv_wint
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [integral_add (h S) (h' S)]
  ring

theorem surv_wint_finsetSum {ι : Type*} (ν σ : ProbabilityMeasure ℝ) (z : ℂ) (n : ℕ)
    (s : Finset ι) {H : ι → (ℕ → ℝ) → ℂ} (h : ∀ i ∈ s, ∀ S, Integrable (H i) (wordLaw ν σ S)) :
    surv_wint ν σ z n (fun g => ∑ i ∈ s, H i g) = ∑ i ∈ s, surv_wint ν σ z n (H i) := by
  unfold surv_wint
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [integral_finsetSum _ fun i hi => h i hi S, Finset.mul_sum]

theorem norm_surv_wcoef (z : ℂ) (n : ℕ) (S : Finset ℕ) :
    ‖surv_wcoef z n S‖ = ‖1 - z‖ ^ (n - S.card) * ‖z‖ ^ S.card := by
  rw [surv_wcoef, norm_mul, norm_pow, norm_pow]

/-- The triangle inequality for the word functional. -/
theorem norm_surv_wint_le (ν σ : ProbabilityMeasure ℝ) (z : ℂ) (n : ℕ) (H : (ℕ → ℝ) → ℂ) :
    ‖surv_wint ν σ z n H‖ ≤
      ∑ S ∈ (Finset.range n).powerset, ‖surv_wcoef z n S‖ * ∫ g, ‖H g‖ ∂(wordLaw ν σ S) := by
  unfold surv_wint
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun S _ => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (norm_nonneg _)

/-- The total variation of the word coefficients: `∑_S ‖coef S‖ = (‖1 - z‖ + ‖z‖)ⁿ`. -/
theorem surv_sum_norm_wcoef (z : ℂ) (n : ℕ) :
    ∑ S ∈ (Finset.range n).powerset, ‖surv_wcoef z n S‖ = (‖1 - z‖ + ‖z‖) ^ n := by
  have h := Finset.prod_add (fun _ : ℕ => ‖z‖) (fun _ : ℕ => ‖1 - z‖) (Finset.range n)
  rw [Finset.prod_const, Finset.card_range, add_comm (‖z‖)] at h
  rw [h]
  refine Finset.sum_congr rfl fun S hS => ?_
  rw [Finset.prod_const, Finset.prod_const, norm_surv_wcoef,
    Finset.card_sdiff_of_subset (Finset.mem_powerset.1 hS), Finset.card_range]
  ring

/-- A bounded integrand gives `‖surv_wint n H‖ ≤ (‖1 - z‖ + ‖z‖)ⁿ M`. -/
theorem norm_surv_wint_le_of_bound (ν σ : ProbabilityMeasure ℝ) (z : ℂ) (n : ℕ)
    {H : (ℕ → ℝ) → ℂ} {M : ℝ} (hM : ∀ g, ‖H g‖ ≤ M) :
    ‖surv_wint ν σ z n H‖ ≤ (‖1 - z‖ + ‖z‖) ^ n * M := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  refine (norm_surv_wint_le ν σ z n H).trans ?_
  have hS : ∀ S ∈ (Finset.range n).powerset,
      ‖surv_wcoef z n S‖ * ∫ g, ‖H g‖ ∂(wordLaw ν σ S) ≤ ‖surv_wcoef z n S‖ * M := by
    intro S _
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have h := integral_mono_of_nonneg (μ := wordLaw ν σ S) (f := fun g => ‖H g‖)
      (g := fun _ => M) (Filter.Eventually.of_forall fun g => norm_nonneg _)
      (integrable_const M) (Filter.Eventually.of_forall hM)
    simpa using h
  refine (Finset.sum_le_sum hS).trans (le_of_eq ?_)
  rw [← Finset.sum_mul, surv_sum_norm_wcoef]

/-! ## Coordinate agreement -/

open Classical in
/-- The coordinate projection `g ↦ A.indicator g` is a coordinatewise map. -/
theorem surv_indicator_eq_pi (A : Set ℕ) :
    (fun g : ℕ → ℝ => A.indicator g) = fun g l => (if l ∈ A then id else fun _ => 0) (g l) := by
  funext g l
  by_cases hl : l ∈ A <;> simp [hl]

theorem surv_measurable_indicator (A : Set ℕ) :
    Measurable (fun g : ℕ → ℝ => A.indicator g) := by
  classical
  rw [surv_indicator_eq_pi]
  refine measurable_pi_lambda _ fun l => ?_
  by_cases hl : l ∈ A
  · simp only [hl, if_true]; exact measurable_pi_apply l
  · simp only [hl, if_false]; exact measurable_const

/-- **Coordinate agreement.**  A measurable functional that reads only the coordinates in `A`
has the same integral under two words agreeing on `A`. -/
theorem surv_integral_wordLaw_congr {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ν σ : ProbabilityMeasure ℝ) {A : Set ℕ} {S S' : Finset ℕ} (hSS : ∀ l ∈ A, (l ∈ S ↔ l ∈ S'))
    {F : (ℕ → ℝ) → E} (hF : StronglyMeasurable F)
    (hdep : ∀ g g' : ℕ → ℝ, (∀ l ∈ A, g l = g' l) → F g = F g') :
    ∫ g, F g ∂(wordLaw ν σ S) = ∫ g, F g ∂(wordLaw ν σ S') := by
  classical
  have hproj : ∀ g, F g = F (A.indicator g) := fun g =>
    hdep _ _ fun l hl => (indicator_of_mem hl g).symm
  have hmi := surv_measurable_indicator A
  have hf : ∀ l, Measurable ((if l ∈ A then id else fun _ => (0 : ℝ)) : ℝ → ℝ) := by
    intro l
    by_cases hl : l ∈ A
    · simp only [hl, if_true]; exact measurable_id
    · simp only [hl, if_false]; exact measurable_const
  have e : ∀ W : Finset ℕ, ∫ g, F g ∂(wordLaw ν σ W) =
      ∫ g, F g ∂(Measure.infinitePi fun l => (wordCoord ν σ W l).map
        (if l ∈ A then id else fun _ => (0 : ℝ))) := by
    intro W
    rw [← Measure.infinitePi_map_pi (wordCoord ν σ W) hf, ← surv_indicator_eq_pi,
      integral_map hmi.aemeasurable hF.aestronglyMeasurable, wordLaw_eq_infinitePi]
    exact integral_congr_ae (Filter.Eventually.of_forall hproj)
  rw [e, e]
  congr 2
  funext l
  by_cases hl : l ∈ A
  · have : wordCoord ν σ S l = wordCoord ν σ S' l := by
      unfold wordCoord
      by_cases h1 : l ∈ S
      · rw [if_pos h1, if_pos ((hSS l hl).1 h1)]
      · rw [if_neg h1, if_neg (fun h => h1 ((hSS l hl).2 h))]
    rw [this]
  · simp only [hl, if_false, Measure.map_const, measure_univ, one_smul]

/-! ## Fubini over disjoint coordinate sets -/

theorem surv_measurable_indicator_sigma (A : Set ℕ) :
    Measurable[kCoordSigma A] (fun g : ℕ → ℝ => A.indicator g) := by
  classical
  let _ : MeasurableSpace (ℕ → ℝ) := kCoordSigma A
  rw [surv_indicator_eq_pi]
  refine measurable_pi_lambda _ fun l => ?_
  by_cases hl : l ∈ A
  · simp only [hl, if_true, id]; exact kill_measurable_coord hl
  · simp only [hl, if_false]; exact measurable_const

/-- **Fubini over disjoint coordinate sets.**  If `F g h` reads `g` only on `A` and `h` only on
`B` with `A ∩ B = ∅`, and `F` is bounded and jointly measurable, then under a word law
`∫ F g g = ∫_g ∫_h F g h`. -/
theorem surv_integral_diag (ν σ : ProbabilityMeasure ℝ) (S : Finset ℕ) {A B : Set ℕ}
    (hAB : Disjoint A B) {F : (ℕ → ℝ) → (ℕ → ℝ) → ℂ} (hF : Measurable (Function.uncurry F))
    {M : ℝ} (hM : ∀ g h, ‖F g h‖ ≤ M)
    (hA : ∀ g g' h, (∀ l ∈ A, g l = g' l) → F g h = F g' h)
    (hB : ∀ g h h', (∀ l ∈ B, h l = h' l) → F g h = F g h') :
    ∫ g, F g g ∂(wordLaw ν σ S) =
      ∫ g, ∫ h, F g h ∂(wordLaw ν σ S) ∂(wordLaw ν σ S) := by
  set W := wordLaw ν σ S with hW
  have hpA : ∀ g h, F g h = F (A.indicator g) h := fun g h =>
    hA _ _ _ fun l hl => (indicator_of_mem hl g).symm
  have hpB : ∀ g h, F g h = F g (B.indicator h) := fun g h =>
    hB _ _ _ fun l hl => (indicator_of_mem hl h).symm
  have hmA := surv_measurable_indicator A
  have hmB := surv_measurable_indicator B
  have hind : IndepFun (fun g : ℕ → ℝ => A.indicator g) (fun g : ℕ → ℝ => B.indicator g) W := by
    rw [hW, wordLaw_eq_infinitePi]
    exact kill_indepFun_of_disjoint hAB (surv_measurable_indicator_sigma A)
      (surv_measurable_indicator_sigma B)
  have hmap := hind.map_prod_eq_prod_map_map hmA.aemeasurable hmB.aemeasurable
  have hint : Integrable (Function.uncurry F) ((W.map fun g => A.indicator g).prod
      (W.map fun g => B.indicator g)) :=
    (integrable_const M).mono' hF.aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => hM p.1 p.2)
  have hpair : Measurable fun g : ℕ → ℝ => (A.indicator g, B.indicator g) := hmA.prodMk hmB
  calc ∫ g, F g g ∂W = ∫ g, Function.uncurry F (A.indicator g, B.indicator g) ∂W := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
        simp only [Function.uncurry_apply_pair]
        rw [← hpA, ← hpB]
    _ = ∫ p, Function.uncurry F p ∂(W.map fun g => (A.indicator g, B.indicator g)) := by
        rw [integral_map hpair.aemeasurable hF.aestronglyMeasurable]
    _ = ∫ x, ∫ y, F x y ∂(W.map fun g => B.indicator g) ∂(W.map fun g => A.indicator g) := by
        rw [hmap, integral_prod _ hint]
        rfl
    _ = ∫ g, ∫ y, F (A.indicator g) y ∂(W.map fun g => B.indicator g) ∂W := by
        rw [integral_map hmA.aemeasurable]
        exact (hF.stronglyMeasurable.integral_prod_right'
          (ν := W.map fun g => B.indicator g)).aestronglyMeasurable
    _ = ∫ g, ∫ h, F g h ∂W ∂W := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
        simp only
        rw [integral_map hmB.aemeasurable]
        · refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
          simp only
          rw [← hpA, ← hpB]
        · exact (hF.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable

/-- Fubini over disjoint coordinate sets, second coordinate outside. -/
theorem surv_integral_diag' (ν σ : ProbabilityMeasure ℝ) (S : Finset ℕ) {A B : Set ℕ}
    (hAB : Disjoint A B) {F : (ℕ → ℝ) → (ℕ → ℝ) → ℂ} (hF : Measurable (Function.uncurry F))
    {M : ℝ} (hM : ∀ g h, ‖F g h‖ ≤ M)
    (hA : ∀ g g' h, (∀ l ∈ A, g l = g' l) → F g h = F g' h)
    (hB : ∀ g h h', (∀ l ∈ B, h l = h' l) → F g h = F g h') :
    ∫ g, F g g ∂(wordLaw ν σ S) =
      ∫ h, ∫ g, F g h ∂(wordLaw ν σ S) ∂(wordLaw ν σ S) := by
  rw [surv_integral_diag ν σ S hAB hF hM hA hB]
  refine integral_integral_swap ?_
  exact (integrable_const M).mono' hF.aestronglyMeasurable
    (Filter.Eventually.of_forall fun p => hM p.1 p.2)

/-! ## Prefix Fubini -/

/-- Concatenation: the first `n` coordinates of `g`, then the coordinates of `h`. -/
def surv_cat (n : ℕ) (g h : ℕ → ℝ) : ℕ → ℝ := fun l => if l < n then g l else h (l - n)

theorem surv_cat_self (n : ℕ) (g : ℕ → ℝ) : surv_cat n g (fun l => g (n + l)) = g := by
  funext l
  unfold surv_cat
  split_ifs with h
  · rfl
  · show g (n + (l - n)) = g l
    rw [show n + (l - n) = l by omega]

theorem surv_cat_apply_lt {n l : ℕ} (hl : l < n) (g h : ℕ → ℝ) : surv_cat n g h l = g l := by
  simp [surv_cat, hl]

theorem surv_cat_apply_add (n l : ℕ) (g h : ℕ → ℝ) : surv_cat n g h (n + l) = h l := by
  simp [surv_cat]

theorem measurable_surv_cat (n : ℕ) :
    Measurable (fun p : (ℕ → ℝ) × (ℕ → ℝ) => surv_cat n p.1 p.2) := by
  refine measurable_pi_lambda _ fun l => ?_
  unfold surv_cat
  by_cases h : l < n
  · simp only [h, if_true]; exact (measurable_pi_apply l).comp measurable_fst
  · simp only [h, if_false]; exact (measurable_pi_apply (l - n)).comp measurable_snd

/-- **Prefix Fubini for one word**: under `wordLaw ν σ S`, the first `n` coordinates and the
shifted rest are independent word laws. -/
theorem surv_integral_cat (ν σ : ProbabilityMeasure ℝ) (S : Finset ℕ) (n : ℕ)
    {H : (ℕ → ℝ) → ℂ} (hH : Measurable H) {M : ℝ} (hM : ∀ g, ‖H g‖ ≤ M) :
    ∫ g, H g ∂(wordLaw ν σ S) =
      ∫ g, ∫ h, H (surv_cat n g h)
        ∂(wordLaw ν σ (S.preimage (n + ·) (add_right_injective n).injOn))
        ∂(wordLaw ν σ (S.filter (· < n))) := by
  set F : (ℕ → ℝ) → (ℕ → ℝ) → ℂ := fun g₁ g₂ => H (surv_cat n g₁ (fun l => g₂ (n + l))) with hFdef
  have hFm : Measurable (Function.uncurry F) := by
    have h1 : Measurable fun p : (ℕ → ℝ) × (ℕ → ℝ) => (p.1, fun l => p.2 (n + l)) :=
      measurable_fst.prodMk (measurable_pi_lambda _ fun l =>
        (measurable_pi_apply (n + l)).comp measurable_snd)
    exact hH.comp ((measurable_surv_cat n).comp h1)
  have hdisj : Disjoint {l : ℕ | l < n} {l : ℕ | n ≤ l} := by
    rw [Set.disjoint_left]
    intro l h1 h2
    simp only [Set.mem_ofPred_eq] at h1 h2
    omega
  have hA : ∀ g g' h, (∀ l ∈ {l : ℕ | l < n}, g l = g' l) → F g h = F g' h := by
    intro g g' h hgg
    simp only [hFdef]
    congr 1
    funext l
    unfold surv_cat
    split_ifs with hl
    · exact hgg l hl
    · rfl
  have hB : ∀ g h h', (∀ l ∈ {l : ℕ | n ≤ l}, h l = h' l) → F g h = F g h' := by
    intro g h h' hhh
    simp only [hFdef]
    congr 1
    funext l
    unfold surv_cat
    split_ifs with hl
    · rfl
    · exact hhh (n + (l - n)) (by simp)
  have hdiag : ∫ g, H g ∂(wordLaw ν σ S) = ∫ g, F g g ∂(wordLaw ν σ S) := by
    simp only [hFdef, surv_cat_self]
  rw [hdiag, surv_integral_diag ν σ S hdisj hFm (fun g h => hM _) hA hB]
  have hinner : ∀ g : ℕ → ℝ, ∫ h, F g h ∂(wordLaw ν σ S) = ∫ h, H (surv_cat n g h)
      ∂(wordLaw ν σ (S.preimage (n + ·) (add_right_injective n).injOn)) := by
    intro g
    exact integral_wordLaw_comp ν σ S (add_right_injective n)
      (F := fun h => H (surv_cat n g h))
      ((hH.comp ((measurable_surv_cat n).comp (measurable_const.prodMk measurable_id)))).aestronglyMeasurable
  simp only [hinner]
  refine surv_integral_wordLaw_congr ν σ (A := {l : ℕ | l < n}) ?_ ?_ ?_
  · intro l hl
    simp only [Set.mem_ofPred_eq] at hl
    simp [Finset.mem_filter, hl]
  · exact (hH.comp (measurable_surv_cat n)).stronglyMeasurable.integral_prod_right'
  · intro g g' hgg
    refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
    simp only
    congr 1
    funext l
    unfold surv_cat
    split_ifs with hl
    · exact hgg l hl
    · rfl

theorem surv_wcoef_union (z : ℂ) {n₁ n₂ : ℕ} {A B : Finset ℕ} (hA : A ⊆ Finset.range n₁)
    (hB : B ⊆ Finset.range n₂) :
    surv_wcoef z (n₁ + n₂) (A ∪ B.image (n₁ + ·)) = surv_wcoef z n₁ A * surv_wcoef z n₂ B := by
  have hdisj : Disjoint A (B.image (n₁ + ·)) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    have := Finset.mem_range.1 (hA ha)
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.1 hb
    omega
  have hcA : A.card ≤ n₁ := by simpa using Finset.card_le_card hA
  have hcB : B.card ≤ n₂ := by simpa using Finset.card_le_card hB
  have hc : (A ∪ B.image (n₁ + ·)).card = A.card + B.card := by
    rw [Finset.card_union_of_disjoint hdisj,
      Finset.card_image_of_injective _ (add_right_injective n₁)]
  unfold surv_wcoef
  rw [hc, show n₁ + n₂ - (A.card + B.card) = (n₁ - A.card) + (n₂ - B.card) by omega, pow_add,
    pow_add]
  ring

/-- **Prefix Fubini for the word functional**:
`surv_wint (n₁ + n₂) H = surv_wint n₁ (g ↦ surv_wint n₂ (h ↦ H (surv_cat n₁ g h)))`. -/
theorem surv_wint_cat (ν σ : ProbabilityMeasure ℝ) (z : ℂ) (n₁ n₂ : ℕ) {H : (ℕ → ℝ) → ℂ}
    (hH : Measurable H) {M : ℝ} (hM : ∀ g, ‖H g‖ ≤ M) :
    surv_wint ν σ z (n₁ + n₂) H =
      surv_wint ν σ z n₁ (fun g => surv_wint ν σ z n₂ (fun h => H (surv_cat n₁ g h))) := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hcm : Measurable (fun p : (ℕ → ℝ) × (ℕ → ℝ) => H (surv_cat n₁ p.1 p.2)) :=
    hH.comp (measurable_surv_cat n₁)
  -- the right side as a double sum
  have hR : ∀ A : Finset ℕ, ∫ g, surv_wint ν σ z n₂ (fun h => H (surv_cat n₁ g h))
      ∂(wordLaw ν σ A) = ∑ B ∈ (Finset.range n₂).powerset, surv_wcoef z n₂ B *
        ∫ g, ∫ h, H (surv_cat n₁ g h) ∂(wordLaw ν σ B) ∂(wordLaw ν σ A) := by
    intro A
    unfold surv_wint
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun B _ => ?_
      rw [integral_const_mul]
    · intro B _
      refine Integrable.const_mul ?_ _
      refine (integrable_const M).mono'
        (hcm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable)
        (Filter.Eventually.of_forall fun g => ?_)
      have h := norm_integral_le_of_norm_le_const (μ := wordLaw ν σ B)
        (f := fun h => H (surv_cat n₁ g h)) (C := M) (Filter.Eventually.of_forall fun h => hM _)
      simpa using h
  conv_rhs => rw [surv_wint]
  simp only [hR, Finset.mul_sum]
  rw [← Finset.sum_product']
  unfold surv_wint
  -- the word bijection
  refine Finset.sum_nbij' (fun S => (S.filter (· < n₁), S.preimage (n₁ + ·)
      (add_right_injective n₁).injOn)) (fun p => p.1 ∪ p.2.image (n₁ + ·)) ?_ ?_ ?_ ?_ ?_
  · intro S hS
    simp only [Finset.mem_powerset] at hS
    simp only [Finset.mem_product, Finset.mem_powerset]
    constructor
    · intro l hl
      simpa using (Finset.mem_filter.1 hl).2
    · intro l hl
      have := Finset.mem_range.1 (hS (Finset.mem_preimage.1 hl))
      simp only [Finset.mem_range]
      omega
  · intro p hp
    simp only [Finset.mem_product, Finset.mem_powerset] at hp
    simp only [Finset.mem_powerset]
    intro l hl
    rcases Finset.mem_union.1 hl with h | h
    · have := Finset.mem_range.1 (hp.1 h)
      simp only [Finset.mem_range]; omega
    · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 h
      have := Finset.mem_range.1 (hp.2 hb)
      simp only [Finset.mem_range]; omega
  · intro S hS
    simp only [Finset.mem_powerset] at hS
    ext l
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_image, Finset.mem_preimage]
    constructor
    · rintro (⟨h, -⟩ | ⟨b, hb, rfl⟩)
      · exact h
      · exact hb
    · intro hl
      by_cases h : l < n₁
      · exact Or.inl ⟨hl, h⟩
      · refine Or.inr ⟨l - n₁, ?_, by omega⟩
        rwa [show n₁ + (l - n₁) = l by omega]
  · intro p hp
    simp only [Finset.mem_product, Finset.mem_powerset] at hp
    ext l
    · simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_image]
      constructor
      · rintro ⟨h | ⟨b, -, rfl⟩, hl⟩
        · exact h
        · omega
      · intro h
        exact ⟨Or.inl h, Finset.mem_range.1 (hp.1 h)⟩
    · simp only [Finset.mem_preimage, Finset.mem_union, Finset.mem_image]
      constructor
      · rintro (h | ⟨b, hb, hbl⟩)
        · have := Finset.mem_range.1 (hp.1 h); omega
        · rwa [show l = b by omega]
      · intro h
        exact Or.inr ⟨l, h, rfl⟩
  · intro S hS
    simp only [Finset.mem_powerset] at hS
    have hinv : S.filter (· < n₁) ∪ (S.preimage (n₁ + ·) (add_right_injective n₁).injOn).image
        (n₁ + ·) = S := by
      ext l
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_image, Finset.mem_preimage]
      constructor
      · rintro (⟨h, -⟩ | ⟨b, hb, rfl⟩)
        · exact h
        · exact hb
      · intro hl
        by_cases h : l < n₁
        · exact Or.inl ⟨hl, h⟩
        · refine Or.inr ⟨l - n₁, ?_, by omega⟩
          rwa [show n₁ + (l - n₁) = l by omega]
    have hsub1 : S.filter (· < n₁) ⊆ Finset.range n₁ := by
      intro l hl; simpa using (Finset.mem_filter.1 hl).2
    have hsub2 : S.preimage (n₁ + ·) (add_right_injective n₁).injOn ⊆ Finset.range n₂ := by
      intro l hl
      have := Finset.mem_range.1 (hS (Finset.mem_preimage.1 hl))
      simp only [Finset.mem_range]; omega
    have hc := surv_wcoef_union z hsub1 hsub2
    rw [hinv] at hc
    simp only
    rw [surv_integral_cat ν σ S n₁ hH hM, hc]
    ring

/-! ## Permutations of the coordinates -/

theorem surv_perm_surj {n : ℕ} {π : ℕ → ℕ} (hπ : Function.Injective π)
    (hπn : ∀ l, π l < n ↔ l < n) {s : ℕ} (hs : s < n) : ∃ l, l < n ∧ π l = s := by
  have himg : (Finset.range n).image π = Finset.range n := by
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro x hx
      obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 hx
      exact Finset.mem_range.2 ((hπn l).2 (Finset.mem_range.1 hl))
    · rw [Finset.card_image_of_injective _ hπ]
  have : s ∈ (Finset.range n).image π := by rw [himg]; exact Finset.mem_range.2 hs
  obtain ⟨l, hl, hls⟩ := Finset.mem_image.1 this
  exact ⟨l, Finset.mem_range.1 hl, hls⟩

/-- **Permutation invariance** of the word functional: for injective `π` preserving
`{0, …, n-1}`, `surv_wint n (H ∘ (· ∘ π)) = surv_wint n H`. -/
theorem surv_wint_perm (ν σ : ProbabilityMeasure ℝ) (z : ℂ) (n : ℕ) {π : ℕ → ℕ}
    (hπ : Function.Injective π) (hπn : ∀ l, π l < n ↔ l < n) {H : (ℕ → ℝ) → ℂ}
    (hH : Measurable H) :
    surv_wint ν σ z n (fun g => H (fun l => g (π l))) = surv_wint ν σ z n H := by
  unfold surv_wint
  have himg : ∀ S ⊆ Finset.range n, (S.preimage π hπ.injOn).image π = S := by
    intro S hS
    ext s
    simp only [Finset.mem_image, Finset.mem_preimage]
    constructor
    · rintro ⟨l, hl, rfl⟩; exact hl
    · intro hs
      obtain ⟨l, -, rfl⟩ := surv_perm_surj hπ hπn (Finset.mem_range.1 (hS hs))
      exact ⟨l, hs, rfl⟩
  refine Finset.sum_nbij' (fun S => S.preimage π hπ.injOn) (fun T => T.image π) ?_ ?_ ?_ ?_ ?_
  · intro S hS
    simp only [Finset.mem_powerset] at hS ⊢
    intro l hl
    exact Finset.mem_range.2 ((hπn l).1 (Finset.mem_range.1 (hS (Finset.mem_preimage.1 hl))))
  · intro T hT
    simp only [Finset.mem_powerset] at hT ⊢
    intro x hx
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 hx
    exact Finset.mem_range.2 ((hπn l).2 (Finset.mem_range.1 (hT hl)))
  · intro S hS
    simp only [Finset.mem_powerset] at hS
    exact himg S hS
  · intro T _
    ext l
    simp only [Finset.mem_preimage, Finset.mem_image]
    constructor
    · rintro ⟨l', hl', he⟩; rwa [← hπ he]
    · intro h; exact ⟨l, h, rfl⟩
  · intro S hS
    simp only [Finset.mem_powerset] at hS
    have hc : (S.preimage π hπ.injOn).card = S.card := by
      conv_rhs => rw [← himg S hS]
      rw [Finset.card_image_of_injective _ hπ]
    rw [integral_wordLaw_comp ν σ S hπ hH.aestronglyMeasurable]
    unfold surv_wcoef
    rw [hc]

/-! ## The last `ν` letter of a word -/

/-- A word of length `L` is all `σ`, or has a last `ν` letter `m` (all later letters `σ`). -/
theorem surv_sum_powerset_last {M : Type*} [AddCommMonoid M] (L : ℕ) (F : Finset ℕ → M) :
    ∑ S ∈ (Finset.range L).powerset, F S =
      F (Finset.range L) + ∑ m ∈ Finset.range L,
        ∑ S ∈ (Finset.range m).powerset, F (S ∪ Finset.Ico (m + 1) L) := by
  induction L generalizing F with
  | zero => simp
  | succ L ih =>
    have e1 : ∀ m ∈ Finset.range L, ∀ S : Finset ℕ,
        insert L (S ∪ Finset.Ico (m + 1) L) = S ∪ Finset.Ico (m + 1) (L + 1) := by
      intro m hm S
      have hm' := Finset.mem_range.1 hm
      ext x
      simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_Ico]
      by_cases hx : x ∈ S
      · simp only [hx, true_or, or_true]
      · simp only [hx, false_or]
        omega
    have e2 : ∀ S : Finset ℕ, S ∪ Finset.Ico (L + 1) (L + 1) = S := by simp
    rw [Finset.sum_range_succ, Finset.range_add_one,
      Finset.sum_powerset_insert Finset.notMem_range_self, ih (fun S => F (insert L S))]
    simp only [e2]
    rw [Finset.sum_congr rfl fun m hm => Finset.sum_congr rfl fun S _ => congrArg F (e1 m hm S)]
    abel

/-- The coefficient of a word with last `ν` letter `m`:
`coef_L(S ∪ [m+1, L)) = coef_m(S) (1 - z) z^{L-1-m}`. -/
theorem surv_wcoef_last (z : ℂ) {L m : ℕ} (hm : m < L) {S : Finset ℕ}
    (hS : S ⊆ Finset.range m) :
    surv_wcoef z L (S ∪ Finset.Ico (m + 1) L) = surv_wcoef z m S * ((1 - z) * z ^ (L - 1 - m)) := by
  have hdisj : Disjoint S (Finset.Ico (m + 1) L) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    have := Finset.mem_range.1 (hS ha)
    have := (Finset.mem_Ico.1 hb).1
    omega
  have hcS : S.card ≤ m := by simpa using Finset.card_le_card hS
  have hc : (S ∪ Finset.Ico (m + 1) L).card = S.card + (L - 1 - m) := by
    rw [Finset.card_union_of_disjoint hdisj, Nat.card_Ico]
    omega
  unfold surv_wcoef
  rw [hc, show L - (S.card + (L - 1 - m)) = (m - S.card) + 1 by omega, pow_add, pow_add, pow_one]
  ring

/-! ## One-coordinate insertion and translation -/

/-- **Fubini in one coordinate** of a word law (complex bounded integrands). -/
theorem surv_integral_wordLaw_update (ν σ : ProbabilityMeasure ℝ) (S : Finset ℕ) (m : ℕ)
    {F : (ℕ → ℝ) → ℂ} (hF : Measurable F) {M : ℝ} (hM : ∀ g, ‖F g‖ ≤ M) :
    ∫ g, F g ∂(wordLaw ν σ S) =
      ∫ g, ∫ x, F (Function.update g m x) ∂(wordCoord ν σ S m) ∂(wordLaw ν σ S) := by
  set ρ : ℕ → ProbabilityMeasure ℝ := fun i => if i ∈ S then σ else ν with hρ
  have hW : wordLaw ν σ S = piLaw ρ := rfl
  have hc : wordCoord ν σ S m = (ρ m : Measure ℝ) := rfl
  have hmap := map_update_piLaw ρ m (ρ m)
  rw [Function.update_eq_self] at hmap
  have hU := measurable_update_pair m
  have hint : Integrable (fun p : ℝ × (ℕ → ℝ) => F (Function.update p.2 m p.1))
      ((ρ m : Measure ℝ).prod (piLaw ρ)) :=
    (integrable_const M).mono' (hF.comp hU).aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => hM _)
  rw [hc, hW]
  calc ∫ g, F g ∂(piLaw ρ)
      = ∫ g, F g ∂(((ρ m : Measure ℝ).prod (piLaw ρ)).map
          (fun p : ℝ × (ℕ → ℝ) => Function.update p.2 m p.1)) := by rw [hmap]
    _ = ∫ p, F (Function.update p.2 m p.1) ∂((ρ m : Measure ℝ).prod (piLaw ρ)) :=
        integral_map hU.aemeasurable hF.aestronglyMeasurable
    _ = ∫ g, ∫ x, F (Function.update g m x) ∂(ρ m : Measure ℝ) ∂(piLaw ρ) :=
        integral_prod_symm _ hint

/-- A density of a probability measure is integrable with integral one. -/
theorem surv_integrable_density {ν : ProbabilityMeasure ℝ} {f : ℝ → ℝ} (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x)
    (hνf : (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x))) :
    Integrable f ∧ ∫ x, f x = 1 := by
  have hl : ∫⁻ x, ENNReal.ofReal (f x) = 1 := by
    have h := congrArg (fun μ : Measure ℝ => μ univ) hνf
    simp only [measure_univ] at h
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h
    exact h.symm
  have hint : Integrable f := by
    refine ⟨hf.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hf0), hl]
    exact ENNReal.one_lt_top
  refine ⟨hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hf0)
    hf.aestronglyMeasurable, hl, ENNReal.toReal_one]

/-- **Translation of a `ν`-coordinate.**  If the coordinate `m` of the word `S` is `ν = f dx`, then
for every measurable `R`,
`∫ F = ∫ dt ∫ f(t - R g) F(update g m (t - R g)) d wordLaw S(g)`. -/
theorem surv_integral_wordLaw_shift (ν σ : ProbabilityMeasure ℝ) (S : Finset ℕ) {m : ℕ}
    (hm : m ∉ S) {f : ℝ → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hνf : (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    {R : (ℕ → ℝ) → ℝ} (hR : Measurable R) {F : (ℕ → ℝ) → ℂ} (hF : Measurable F) {M : ℝ}
    (hM : ∀ g, ‖F g‖ ≤ M) :
    ∫ g, F g ∂(wordLaw ν σ S) =
      ∫ t, ∫ g, (f (t - R g) : ℂ) * F (Function.update g m (t - R g)) ∂(wordLaw ν σ S) := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  obtain ⟨hfi, -⟩ := surv_integrable_density hf hf0 hνf
  have hcoord : wordCoord ν σ S m = (ν : Measure ℝ) := by simp [wordCoord, hm]
  rw [surv_integral_wordLaw_update ν σ S m hF hM, hcoord]
  have hinner : ∀ g : ℕ → ℝ, ∫ x, F (Function.update g m x) ∂(ν : Measure ℝ) =
      ∫ t, (f (t - R g) : ℂ) * F (Function.update g m (t - R g)) := by
    intro g
    rw [hνf, integral_withDensity_eq_integral_toReal_smul (by fun_prop)
      (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
    have e : ∀ x, (ENNReal.ofReal (f x)).toReal • F (Function.update g m x) =
        (f x : ℂ) * F (Function.update g m x) := by
      intro x
      rw [ENNReal.toReal_ofReal (hf0 x), Complex.real_smul]
    simp only [e]
    exact (integral_sub_right_eq_self (fun x => (f x : ℂ) * F (Function.update g m x)) (R g)).symm
  simp only [hinner]
  have hU : Measurable fun p : (ℕ → ℝ) × ℝ => Function.update p.1 m (p.2 - R p.1) :=
    (measurable_update_pair m).comp ((measurable_snd.sub (hR.comp measurable_fst)).prodMk
      measurable_fst)
  have hfm : Measurable fun p : (ℕ → ℝ) × ℝ => f (p.2 - R p.1) :=
    hf.comp (measurable_snd.sub (hR.comp measurable_fst))
  refine integral_integral_swap ?_
  have hdom : Integrable (fun p : (ℕ → ℝ) × ℝ => M * f (p.2 - R p.1))
      ((wordLaw ν σ S).prod volume) := by
    refine Integrable.const_mul ?_ M
    refine (integrable_prod_iff hfm.aestronglyMeasurable).2 ⟨?_, ?_⟩
    · exact Filter.Eventually.of_forall fun g => hfi.comp_sub_right (R g)
    · have e : ∀ g : ℕ → ℝ, ∫ t, ‖f (t - R g)‖ = ∫ t, f t := by
        intro g
        simp only [Real.norm_eq_abs, abs_of_nonneg (hf0 _)]
        exact integral_sub_right_eq_self (fun t => f t) (R g)
      simp only [e]
      exact integrable_const _
  refine hdom.mono' ?_ (Filter.Eventually.of_forall fun p => ?_)
  · exact ((Complex.measurable_ofReal.comp hfm).mul (hF.comp hU)).aestronglyMeasurable
  · show ‖(f (p.2 - R p.1) : ℂ) * F (Function.update p.1 m (p.2 - R p.1))‖ ≤
      M * f (p.2 - R p.1)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hf0 _), mul_comm]
    exact mul_le_mul_of_nonneg_right (hM _) (hf0 _)

end

end PGM
