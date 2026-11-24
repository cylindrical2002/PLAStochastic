import PLAStochastic.Index.GEP.Kernel.Flux.Prefix.ThreePointWidth
import Mathlib.Analysis.Convex.Radon

/-!
# Three-point constraints characterize the actual feasible prefix

Helly's theorem applies to the convex strips of admissible slope/intercept
pairs.  Together with the exact three-point width, this identifies the actual
prefix event with finitely many explicit linear facet inequalities.  It is a
geometric prerequisite for the coarea formula, not that formula itself.
-/

namespace PGM

noncomputable section

open Set Finset

/-- The strip of fitting lines allowed by one actual key. -/
def kernelFitStrip (eps : ℝ) (p : ℕ → ℝ) (i : ℕ) : Set (ℝ × ℝ) :=
  {q | |(i : ℝ) - (q.1 * p i + q.2)| ≤ eps}

theorem convex_kernelFitStrip (eps : ℝ) (p : ℕ → ℝ) (i : ℕ) :
    Convex ℝ (kernelFitStrip eps p i) := by
  intro x hx y hy a b ha hb hab
  change |(i : ℝ) - ((a * x.1 + b * y.1) * p i + (a * x.2 + b * y.2))| ≤ eps
  have he : (i : ℝ) - ((a * x.1 + b * y.1) * p i + (a * x.2 + b * y.2)) =
      a * ((i : ℝ) - (x.1 * p i + x.2)) + b * ((i : ℝ) - (y.1 * p i + y.2)) := by
    nlinarith [congrArg (fun z : ℝ => z * i) hab]
  rw [he]
  calc
    _ ≤ |a * ((i : ℝ) - (x.1 * p i + x.2))| +
        |b * ((i : ℝ) - (y.1 * p i + y.2))| := abs_add_le _ _
    _ = a * |(i : ℝ) - (x.1 * p i + x.2)| +
        b * |(i : ℝ) - (y.1 * p i + y.2)| := by
      rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ a * eps + b * eps := add_le_add
      (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)
    _ = eps := by rw [← add_mul, hab, one_mul]

/-- The three-point width bound constructs one line in all three fitting strips. -/
theorem kernelFitStrip_triple {eps : ℝ} {p : ℕ → ℝ} {r s t : ℕ}
    (hA : p r < p s) (hB : p s < p t)
    (hw : fluxWidth ((s : ℝ) - r) ((t : ℝ) - s) (p s - p r) (p t - p s) ≤ eps) :
    ∃ q : ℝ × ℝ, q ∈ kernelFitStrip eps p r ∧ q ∈ kernelFitStrip eps p s ∧
      q ∈ kernelFitStrip eps p t := by
  obtain ⟨a, b, hb, hs, ht⟩ :=
    (fluxTripleFeasible_iff (sub_pos.mpr hA) (sub_pos.mpr hB)).mpr hw
  refine ⟨(a, b + r - a * p r), ?_, ?_, ?_⟩
  · change |(r : ℝ) - (a * p r + (b + r - a * p r))| ≤ eps
    convert hb using 1
    rw [← abs_neg]
    congr 1
    ring
  · change |(s : ℝ) - (a * p s + (b + r - a * p r))| ≤ eps
    convert hs using 1
    congr 1
    ring
  · change |(t : ℝ) - (a * p t + (b + r - a * p r))| ≤ eps
    convert ht using 1
    congr 1
    ring

/-- A prefix of at least three strictly increasing keys is feasible exactly
when all its ordered triples satisfy the explicit optimal-width bound. -/
theorem kernel_prefix_feasible_iff_triples {eps : ℝ} {p : ℕ → ℝ} {n : ℕ}
    (hn : 3 ≤ n) (hp : ∀ r s, r < s → s < n → p r < p s) :
    prefixAffineFeasible eps p n ↔
      ∀ r s t : ℕ, r < s → s < t → t < n →
        fluxWidth ((s : ℝ) - r) ((t : ℝ) - s) (p s - p r) (p t - p s) ≤ eps := by
  classical
  constructor
  · intro hf r s t hrs hst ht
    have hnpos : n = (n - 1) + 1 := by omega
    rw [hnpos] at hf
    exact fluxWidth_le_of_prefix hf hrs hst (by omega) (hp r s hrs (by omega)) (hp s t hst ht)
  · intro hw
    have ht (r s t : ℕ) (hrs : r < s) (hst : s < t) (htn : t < n) :
        ∃ q : ℝ × ℝ, q ∈ kernelFitStrip eps p r ∧ q ∈ kernelFitStrip eps p s ∧
          q ∈ kernelFitStrip eps p t :=
      kernelFitStrip_triple (hp r s hrs (by omega)) (hp s t hst htn) (hw r s t hrs hst htn)
    have hu (r s t : ℕ) (hrn : r < n) (hsn : s < n) (htn : t < n)
        (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t) :
        ∃ q : ℝ × ℝ, q ∈ kernelFitStrip eps p r ∧ q ∈ kernelFitStrip eps p s ∧
          q ∈ kernelFitStrip eps p t := by
      rcases lt_or_gt_of_ne hrs with hrs | hsr
      · rcases lt_or_gt_of_ne hst with hst | hts
        · exact ht r s t hrs hst htn
        · rcases lt_or_gt_of_ne hrt with hrt | htr
          · obtain ⟨q, hq1, hq2, hq3⟩ := ht r t s hrt hts hsn
            exact ⟨q, hq1, hq3, hq2⟩
          · obtain ⟨q, hq1, hq2, hq3⟩ := ht t r s htr hrs hsn
            exact ⟨q, hq2, hq3, hq1⟩
      · rcases lt_or_gt_of_ne hrt with hrt | htr
        · obtain ⟨q, hq1, hq2, hq3⟩ := ht s r t hsr hrt htn
          exact ⟨q, hq2, hq1, hq3⟩
        · rcases lt_or_gt_of_ne hst with hst | hts
          · obtain ⟨q, hq1, hq2, hq3⟩ := ht s t r hst htr hrn
            exact ⟨q, hq3, hq1, hq2⟩
          · obtain ⟨q, hq1, hq2, hq3⟩ := ht t s r hts hsr hrn
            exact ⟨q, hq3, hq2, hq1⟩
    have hdim : Module.finrank ℝ (ℝ × ℝ) + 1 = 3 := by simp [Module.finrank_prod]
    have hall : (⋂ i ∈ range n, kernelFitStrip eps p i).Nonempty := by
      apply Convex.helly_theorem (𝕜 := ℝ) (by simpa only [hdim, card_range] using hn)
        (fun i _ => convex_kernelFitStrip eps p i)
      intro I hI hcard
      rw [hdim] at hcard
      obtain ⟨r, s, t, hrs, hrt, hst, rfl⟩ := card_eq_three.mp hcard
      have hrn : r < n := mem_range.mp (hI (by simp))
      have hsn : s < n := mem_range.mp (hI (by simp))
      have htn : t < n := mem_range.mp (hI (by simp))
      obtain ⟨q, hq1, hq2, hq3⟩ := hu r s t hrn hsn htn hrs hrt hst
      exact ⟨q, by simpa using And.intro hq1 (And.intro hq2 hq3)⟩
    obtain ⟨q, hq⟩ := hall
    refine ⟨q.1, q.2, fun i hi => ?_⟩
    exact mem_iInter₂.mp hq i (mem_range.mpr hi)

/-- The exact prefix event is a finite conjunction of the two oriented linear
facet inequalities.  No density smoothness is used in this identification. -/
theorem kernel_prefix_feasible_iff_facets {eps : ℝ} {p : ℕ → ℝ} {n : ℕ}
    (hn : 3 ≤ n) (hp : ∀ r s, r < s → s < n → p r < p s) :
    prefixAffineFeasible eps p n ↔
      ∀ r s t : ℕ, r < s → s < t → t < n →
        fluxFacet ((s : ℝ) - r) ((t : ℝ) - s) eps 1 (p s - p r) (p t - p s) ≤ 0 ∧
        0 ≤ fluxFacet ((s : ℝ) - r) ((t : ℝ) - s) eps (-1) (p s - p r) (p t - p s) := by
  rw [kernel_prefix_feasible_iff_triples hn hp]
  apply forall_congr'
  intro r
  apply forall_congr'
  intro s
  apply forall_congr'
  intro t
  apply forall_congr'
  intro hrs
  apply forall_congr'
  intro hst
  apply forall_congr'
  intro htn
  exact fluxWidth_le_iff_facets (sub_pos.mpr (hp r s hrs (by omega)))
    (sub_pos.mpr (hp s t hst htn))

/-- Interpolation preserves strict key order when both endpoint key sequences are ordered. -/
theorem kernel_ordered_mix {p q : ℕ → ℝ} {a b : ℝ} {n : ℕ}
    (hp : ∀ r s, r < s → s < n → p r < p s)
    (hq : ∀ r s, r < s → s < n → q r < q s)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    ∀ r s, r < s → s < n → a * p r + b * q r < a * p s + b * q s := by
  intro r s hrs hsn
  by_cases ha0 : a = 0
  · have hb1 : b = 1 := by linarith
    simpa [ha0, hb1] using hq r s hrs hsn
  · exact add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left (hp r s hrs hsn) (lt_of_le_of_ne ha (Ne.symm ha0)))
      (mul_le_mul_of_nonneg_left (hq r s hrs hsn).le hb)

/-- The actual feasible event is convex in strictly increasing key coordinates.
The fitting line may change: the proof uses the exact finite linear facets. -/
theorem kernel_prefix_feasible_mix {eps : ℝ} {p q : ℕ → ℝ} {a b : ℝ} {n : ℕ}
    (hn : 3 ≤ n) (hp : ∀ r s, r < s → s < n → p r < p s)
    (hq : ∀ r s, r < s → s < n → q r < q s)
    (hpF : prefixAffineFeasible eps p n) (hqF : prefixAffineFeasible eps q n)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    prefixAffineFeasible eps (fun i => a * p i + b * q i) n := by
  apply (kernel_prefix_feasible_iff_facets hn (kernel_ordered_mix hp hq ha hb hab)).mpr
  intro r s t hrs hst htn
  obtain ⟨hp1, hp2⟩ := (kernel_prefix_feasible_iff_facets hn hp).mp hpF r s t hrs hst htn
  obtain ⟨hq1, hq2⟩ := (kernel_prefix_feasible_iff_facets hn hq).mp hqF r s t hrs hst htn
  have he (σ : ℝ) :
      fluxFacet ((s : ℝ) - r) ((t : ℝ) - s) eps σ
          ((a * p s + b * q s) - (a * p r + b * q r))
          ((a * p t + b * q t) - (a * p s + b * q s)) =
        a * fluxFacet ((s : ℝ) - r) ((t : ℝ) - s) eps σ (p s - p r) (p t - p s) +
        b * fluxFacet ((s : ℝ) - r) ((t : ℝ) - s) eps σ (q s - q r) (q t - q s) := by
    unfold fluxFacet
    ring
  rw [he 1, he (-1)]
  exact ⟨add_nonpos (mul_nonpos_of_nonneg_of_nonpos ha hp1)
    (mul_nonpos_of_nonneg_of_nonpos hb hq1),
    add_nonneg (mul_nonneg ha hp2) (mul_nonneg hb hq2)⟩

/-- Replacing one gap commutes with convex interpolation, including all prefix sums. -/
theorem kernel_gapKeys_update_mix (g : ℕ → ℝ) (i : ℕ) (x y a b : ℝ) (hab : a + b = 1)
    (k : ℕ) :
    gapKeys (Function.update g i (a * x + b * y)) k =
      a * gapKeys (Function.update g i x) k + b * gapKeys (Function.update g i y) k := by
  classical
  have he (j : ℕ) : Function.update g i (a * x + b * y) j =
      a * Function.update g i x j + b * Function.update g i y j := by
    by_cases hji : j = i
    · subst j
      simp
    · simp only [Function.update_of_ne hji]
      rw [← add_mul, hab, one_mul]
  simp only [gapKeys, he, Finset.sum_add_distrib, Finset.mul_sum]

/-- Every one-gap section of the actual positive-gap feasible event is convex,
so it is an interval (possibly empty or unbounded). -/
theorem convex_kernel_gap_section {eps : ℝ} {g : ℕ → ℝ} {i k : ℕ}
    (hk : 2 ≤ k) (hg : ∀ j < k, j ≠ i → 0 < g j) :
    Convex ℝ {x : ℝ | 0 < x ∧
      prefixAffineFeasible eps (gapKeys (Function.update g i x)) (k + 1)} := by
  classical
  intro x hx y hy a b ha hb hab
  change 0 < a * x + b * y ∧
    prefixAffineFeasible eps (gapKeys (Function.update g i (a * x + b * y))) (k + 1)
  have hpos {z : ℝ} (hz : 0 < z) : ∀ j < k, 0 < Function.update g i z j := by
    intro j hj
    by_cases hji : j = i
    · subst j
      simpa using hz
    · simpa only [Function.update_of_ne hji] using hg j hj hji
  have hord {z : ℝ} (hz : 0 < z) :
      ∀ r s, r < s → s < k + 1 →
        gapKeys (Function.update g i z) r < gapKeys (Function.update g i z) s :=
    fun r s hrs hsk => cert_gapKeys_lt (hpos hz) r s hrs (by omega)
  constructor
  · by_cases ha0 : a = 0
    · have hb1 : b = 1 := by linarith
      simpa [ha0, hb1] using hy.1
    · exact add_pos_of_pos_of_nonneg (mul_pos (lt_of_le_of_ne ha (Ne.symm ha0)) hx.1)
        (mul_nonneg hb hy.1.le)
  · have he := kernel_prefix_feasible_mix (by omega : 3 ≤ k + 1) (hord hx.1) (hord hy.1)
      hx.2 hy.2 ha hb hab
    have hkeys : gapKeys (Function.update g i (a * x + b * y)) =
        fun r => a * gapKeys (Function.update g i x) r + b * gapKeys (Function.update g i y) r :=
      funext (kernel_gapKeys_update_mix g i x y a b hab)
    rwa [hkeys]

end

end PGM
