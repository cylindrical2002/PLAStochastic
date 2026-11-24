import PLAStochastic.Index.ModelK.Density
import PLAStochastic.Index.Model.ExpSequence
import PLAStochastic.Index.Algorithm.MeasurableEndpointHeight
import PLAStochastic.Index.Algorithm.AffineInvariance
import PLAStochastic.Index.GEP.FirstOrderHeight
import PLAStochastic.Index.GRE.LogLogTheta

/-!
# Model K with constant density

Let `X 0, X 1, …` be iid with the constant density `1 / (B - A)` on `[A, B]`, and let the
keys for sample size `n` be the sorted first `n` samples (`kKeys X n`).

* By the Rényi representation (`identDistrib_sortVec_uniformK`), the sorted sample has the law
  of `A + s · Γ (i+1)` with `Γ (i+1) = E 0 + ⋯ + E i` for iid `Exp(1)` variables `E` and the
  a.s. positive random factor `s = (B - A) / Γ (n+1)`.  Both heights are invariant under
  nonzero affine maps of the keys, so the expected heights of Model K equal those of the gap
  model with iid `Exp(1)` gaps `E 1, E 2, …` and offset `E 0`
  (`integral_epHeight_kKeys_const`, `integral_reHeight_kKeys_const`).
* Hence H-G-EP and H-G-RE transfer: `E H_EP / (log n / (2 log ε)) → 1` (`H_K_EP_const`) and
  `E H_RE = Θ(log log n)` (`H_K_RE_const_upper`, `H_K_RE_const_lower`, `H_K_RE_const_theta`).
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Finset Filter Topology

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {f : ℝ → ℝ} {A B : ℝ}

/-- The Model K keys for sample size `n`: the sorted first `n` samples, extended by `0`. -/
def kKeys (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℕ → ℝ :=
  extendKeys (Renyi.sortVec (fun i : Fin n => X i ω))

/-- The partial sums of the canonical coordinates, read through `Fin (n + 1)`. -/
theorem gammaSum_expCoord {n : ℕ} (ω' : ℕ → ℝ) {k : ℕ} (hk : k ≤ n + 1) :
    Renyi.gammaSum (fun j : Fin (n + 1) => expCoord j ω') k = ∑ j ∈ range k, expCoord j ω' := by
  unfold Renyi.gammaSum
  rw [Finset.sum_filter, Fin.sum_univ_eq_sum_range (fun j => if j < k then expCoord j ω' else 0),
    ← Finset.sum_filter]
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

/-- **Transfer for an affine-invariant height.**  Let `h` read only the first `n` keys and be
invariant under nonzero affine maps of the keys.  Then its expectation on the Model K keys with
constant density equals its expectation on the keys `E 0 + E 1 + ⋯ + E t` of the canonical
iid `Exp(1)` sequence. -/
theorem integral_height_kKeys_const (hAB : A < B) (hc : ∀ x ∈ Set.Icc A B, f x = 1 / (B - A))
    {X : ℕ → Ω → ℝ} (hX : ∀ i, HasLaw (X i) (densityLaw f A B) P) (hind : iIndepFun X P)
    {n : ℕ} {h : (ℕ → ℝ) → ℕ} (hmeas : Measurable fun v : Fin n → ℝ => h (extendKeys v))
    (hcongr : ∀ p p' : ℕ → ℝ, (∀ i < n, p i = p' i) → h p = h p')
    (haff : ∀ (p : ℕ → ℝ) (s c : ℝ), s ≠ 0 → h (fun i => s * p i + c) = h p) :
    ∫ ω, (h (kKeys X n ω) : ℝ) ∂P =
      ∫ ω', (h (fun t => expCoord 0 ω' + ∑ i ∈ range t, expCoord (i + 1) ω') : ℝ)
        ∂expSeqMeasure := by
  have hXn : iIndepFun (fun i : Fin n => X i) P := hind.precomp Fin.val_injective
  have hEn : iIndepFun (fun j : Fin (n + 1) => expCoord j) expSeqMeasure :=
    iidSeq_expCoord.indep.precomp Fin.val_injective
  have hid := identDistrib_sortVec_uniformK hAB hc (fun i : Fin n => hX i) hXn
    (fun j : Fin (n + 1) => hasLaw_expCoord j) hEn
  have hu : Measurable fun v : Fin n → ℝ => (h (extendKeys v) : ℝ) :=
    measurable_from_nat.comp hmeas
  have hint := (hid.comp hu).integral_eq
  simp only [Function.comp_def] at hint
  rw [show (fun ω => (h (kKeys X n ω) : ℝ)) =
    fun ω => (h (extendKeys (Renyi.sortVec fun i : Fin n => X i ω)) : ℝ) from rfl, hint]
  refine integral_congr_ae ?_
  have hpos : ∀ᵐ ω' ∂expSeqMeasure, ∀ t, 0 < expCoord t ω' :=
    ae_all_iff.2 fun t => iidSeq_expCoord.ae_pos_of_expMeasure_one (hasLaw_expCoord 0) t
  filter_upwards [hpos] with ω' hω'
  have hΓ : 0 < Renyi.gammaSum (fun j : Fin (n + 1) => expCoord j ω') (n + 1) := by
    rw [gammaSum_expCoord ω' le_rfl]
    exact Finset.sum_pos (fun i _ => hω' i) (by simp)
  have hs : (B - A) / Renyi.gammaSum (fun j : Fin (n + 1) => expCoord j ω') (n + 1) ≠ 0 :=
    (div_pos (sub_pos.2 hAB) hΓ).ne'
  rw [← haff (fun t => expCoord 0 ω' + ∑ i ∈ range t, expCoord (i + 1) ω') _ A hs]
  congr 1
  apply hcongr
  intro i hi
  rw [extendKeys_of_lt _ hi, gammaSum_expCoord ω' (k := i + 1) (by omega),
    Finset.sum_range_succ']
  ring

/-- **Transfer, ALG-PGM.**  The expected endpoint height on `n` sorted uniform `[A, B]` samples
equals that of the gap model with iid `Exp(1)` gaps `E 1, E 2, …` and offset `E 0`. -/
theorem integral_epHeight_kKeys_const (hAB : A < B) (hc : ∀ x ∈ Set.Icc A B, f x = 1 / (B - A))
    {X : ℕ → Ω → ℝ} (hX : ∀ i, HasLaw (X i) (densityLaw f A B) P) (hind : iIndepFun X P)
    (eps : ℝ) (n : ℕ) :
    ∫ ω, (epHeight eps (kKeys X n ω) n : ℝ) ∂P =
      ∫ ω', (epHeight eps (fun t => expCoord 0 ω' +
        gapKeys (seq (fun s => expCoord (s + 1)) ω') t) n : ℝ) ∂expSeqMeasure :=
  integral_height_kKeys_const (h := fun p => epHeight eps p n) hAB hc hX hind
    (measurable_epHeight_extendKeys eps n) (fun _ _ hpp => epHeight_congr hpp)
    (fun _ _ _ hs => epHeight_affine hs n)

/-- **Transfer, ALG-RE.**  The expected rank-equispaced height on `n` sorted uniform `[A, B]`
samples equals that of the gap model with iid `Exp(1)` gaps `E 1, E 2, …` and offset `E 0`. -/
theorem integral_reHeight_kKeys_const (hAB : A < B) (hc : ∀ x ∈ Set.Icc A B, f x = 1 / (B - A))
    {X : ℕ → Ω → ℝ} (hX : ∀ i, HasLaw (X i) (densityLaw f A B) P) (hind : iIndepFun X P)
    (eps : ℝ) (n : ℕ) :
    ∫ ω, (reHeight eps (kKeys X n ω) n : ℝ) ∂P =
      ∫ ω', (reHeight eps (fun s => expCoord 0 ω' + ∑ i ∈ range s, expCoord (i + 1) ω') n : ℝ)
        ∂expSeqMeasure :=
  integral_height_kKeys_const (h := fun p => reHeight eps p n) hAB hc hX hind
    (measurable_reHeight_extendKeys eps n) (fun _ _ hpp => reHeight_congr hpp)
    (fun _ _ _ hs => reHeight_affine hs n)

/-- **H-K-EP, constant density.**  For sorted iid uniform `[A, B]` keys, along any sequence with
`n → ∞`, `ε → ∞` and `log ε = o(log n)`, `E H_EP / (log n / (2 log ε)) → 1`. -/
theorem H_K_EP_const (hAB : A < B) (hc : ∀ x ∈ Set.Icc A B, f x = 1 / (B - A))
    {X : ℕ → Ω → ℝ} (hX : ∀ i, HasLaw (X i) (densityLaw f A B) P) (hind : iIndepFun X P)
    {n : ℕ → ℕ} {ε : ℕ → ℝ}
    (hn : Tendsto (fun k => (n k : ℝ)) atTop atTop) (hε : Tendsto ε atTop atTop)
    (hεn : Tendsto (fun k => Real.log (ε k) / Real.log (n k)) atTop (𝓝 0)) :
    Tendsto (fun k =>
        (∫ ω, (epHeight (ε k) (kKeys X (n k) ω) (n k) : ℝ) ∂P) /
          (Real.log (n k) / (2 * Real.log (ε k)))) atTop (𝓝 1) := by
  simp only [integral_epHeight_kKeys_const hAB hc hX hind]
  exact H_G_EP gapLaw_expCoord_succ (expCoord 0) hn hε hεn

/-- **H-K-RE upper bound, constant density.**  `E H_RE = O(log log n)`. -/
theorem H_K_RE_const_upper (hAB : A < B) (hc : ∀ x ∈ Set.Icc A B, f x = 1 / (B - A))
    {X : ℕ → Ω → ℝ} (hX : ∀ i, HasLaw (X i) (densityLaw f A B) P) (hind : iIndepFun X P)
    {n : ℕ → ℕ} {ε : ℕ → ℝ}
    (hn : Tendsto (fun k => (n k : ℝ)) atTop atTop) (hε : Tendsto ε atTop atTop)
    (hεn : Tendsto (fun k => Real.log (ε k) / Real.log (n k)) atTop (𝓝 0)) :
    ∃ C : ℝ, ∀ᶠ k in atTop,
      ∫ ω, (reHeight (ε k) (kKeys X (n k) ω) (n k) : ℝ) ∂P ≤ C * Real.log (Real.log (n k)) := by
  simp only [integral_reHeight_kKeys_const hAB hc hX hind]
  exact H_G_RE_upper gapLaw_expCoord_succ (measurable_expCoord 0) hn hε hεn

/-- **H-K-RE lower bound, constant density.**  Under (RE-LOWER)
`log ε ≤ D (log n)^(1-η)`, `E H_RE = Ω(log log n)`. -/
theorem H_K_RE_const_lower (hAB : A < B) (hc : ∀ x ∈ Set.Icc A B, f x = 1 / (B - A))
    {X : ℕ → Ω → ℝ} (hX : ∀ i, HasLaw (X i) (densityLaw f A B) P) (hind : iIndepFun X P)
    {n : ℕ → ℕ} {ε : ℕ → ℝ}
    (hn : Tendsto (fun k => (n k : ℝ)) atTop atTop) (hε : Tendsto ε atTop atTop)
    {η D : ℝ} (hη0 : 0 < η) (hη1 : η < 1) (hD : 0 < D)
    (hRE : ∀ᶠ k in atTop, Real.log (ε k) ≤ D * Real.log (n k) ^ (1 - η)) :
    ∃ c > 0, ∀ᶠ k in atTop,
      c * Real.log (Real.log (n k)) ≤ ∫ ω, (reHeight (ε k) (kKeys X (n k) ω) (n k) : ℝ) ∂P := by
  simp only [integral_reHeight_kKeys_const hAB hc hX hind]
  exact H_G_RE_lower gapLaw_expCoord_succ (measurable_expCoord 0) hn hε hη0 hη1 hD hRE

/-- **H-K-RE, constant density.**  Under (RE-LOWER), `E H_RE = Θ(log log n)`. -/
theorem H_K_RE_const_theta (hAB : A < B) (hc : ∀ x ∈ Set.Icc A B, f x = 1 / (B - A))
    {X : ℕ → Ω → ℝ} (hX : ∀ i, HasLaw (X i) (densityLaw f A B) P) (hind : iIndepFun X P)
    {n : ℕ → ℕ} {ε : ℕ → ℝ}
    (hn : Tendsto (fun k => (n k : ℝ)) atTop atTop) (hε : Tendsto ε atTop atTop)
    (hεn : Tendsto (fun k => Real.log (ε k) / Real.log (n k)) atTop (𝓝 0))
    {η D : ℝ} (hη0 : 0 < η) (hη1 : η < 1) (hD : 0 < D)
    (hRE : ∀ᶠ k in atTop, Real.log (ε k) ≤ D * Real.log (n k) ^ (1 - η)) :
    ∃ c > 0, ∃ C : ℝ, ∀ᶠ k in atTop,
      c * Real.log (Real.log (n k)) ≤ ∫ ω, (reHeight (ε k) (kKeys X (n k) ω) (n k) : ℝ) ∂P ∧
        ∫ ω, (reHeight (ε k) (kKeys X (n k) ω) (n k) : ℝ) ∂P ≤ C * Real.log (Real.log (n k)) := by
  simp only [integral_reHeight_kKeys_const hAB hc hX hind]
  exact H_G_RE_theta gapLaw_expCoord_succ (measurable_expCoord 0) hn hε hεn hη0 hη1 hD hRE

end

end PGM
