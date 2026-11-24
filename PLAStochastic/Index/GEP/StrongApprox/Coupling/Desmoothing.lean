import PLAStochastic.Index.GEP.Universality.StrongApproxInterface

/-! # Extending block endpoint couplings and removing Gaussian smoothing

These deterministic estimates keep the final error in the coordinates of `SAEvent`.
The stochastic construction must still supply the endpoint and fluctuation bounds.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Finset

/-- Endpoint control and two within-block oscillation bounds control every prefix. -/
theorem sa_block_prefix_error {S W : ℕ → ℝ} {n m : ℕ} (hm : 0 < m)
    {a b c : ℝ}
    (hend : ∀ j ≤ n / m, |S (j * m) - W (j * m)| ≤ a)
    (hS : ∀ j ≤ n / m, ∀ r < m, j * m + r ≤ n →
      |S (j * m + r) - S (j * m)| ≤ b)
    (hW : ∀ j ≤ n / m, ∀ r < m, j * m + r ≤ n →
      |W (j * m + r) - W (j * m)| ≤ c) :
    ∀ k ≤ n, |S k - W k| ≤ a + b + c := by
  intro k hk
  have hj : k / m ≤ n / m := Nat.div_le_div_right hk
  have hr : k % m < m := Nat.mod_lt _ hm
  have he : k / m * m + k % m = k := by simpa [Nat.mul_comm] using Nat.div_add_mod k m
  have h₀ := hend (k / m) hj
  have h₁ := hS (k / m) hj (k % m) hr (by omega)
  have h₂ := hW (k / m) hj (k % m) hr (by omega)
  rw [he] at h₁ h₂
  calc
    |S k - W k| = |(S (k / m * m) - W (k / m * m)) +
        (S k - S (k / m * m)) + (W (k / m * m) - W k)| := by ring_nf
    _ ≤ |S (k / m * m) - W (k / m * m)| +
        |S k - S (k / m * m)| + |W (k / m * m) - W k| := abs_add_three _ _ _
    _ ≤ a + b + c := by rw [abs_sub_comm (W (k / m * m))]; linarith

/-- The variance correction from adding a Gaussian of standard deviation `s`. -/
theorem sa_sqrt_variance_error {v s : ℝ} (hv : 0 < v) :
    |Real.sqrt (v + s ^ 2) - Real.sqrt v| ≤ s ^ 2 / (2 * Real.sqrt v) := by
  have hroot : 0 < Real.sqrt v := Real.sqrt_pos.2 hv
  have hmono : Real.sqrt v ≤ Real.sqrt (v + s ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
  have hsq := Real.sq_sqrt hv.le
  have hsq' := Real.sq_sqrt (show 0 ≤ v + s ^ 2 by positivity)
  rw [abs_of_nonneg (sub_nonneg.2 hmono), le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (Real.sqrt (v + s ^ 2) - Real.sqrt v)]

/-- Removing the added noise and the variance correction yields the original walk error. -/
theorem sa_desmoothing_error {X ξ Z : ℕ → ℝ} {v s a b c : ℝ} {n : ℕ}
    (hv : 0 < v)
    (happrox : ∀ k ≤ n,
      |gapKeys X k - k + s * gapKeys ξ k - Real.sqrt (v + s ^ 2) * gapKeys Z k| ≤ a)
    (hnoise : ∀ k ≤ n, |gapKeys ξ k| ≤ b)
    (hgauss : ∀ k ≤ n, |gapKeys Z k| ≤ c) :
    ∀ k ≤ n, |gapKeys X k - k - Real.sqrt v * gapKeys Z k| ≤
      a + |s| * b + s ^ 2 / (2 * Real.sqrt v) * c := by
  intro k hk
  have he := happrox k hk
  have hn := mul_le_mul_of_nonneg_left (hnoise k hk) (abs_nonneg s)
  have hg := mul_le_mul (sa_sqrt_variance_error (s := s) hv) (hgauss k hk)
    (abs_nonneg _) (by positivity : 0 ≤ s ^ 2 / (2 * Real.sqrt v))
  calc
    |gapKeys X k - k - Real.sqrt v * gapKeys Z k| =
        |(gapKeys X k - k + s * gapKeys ξ k -
          Real.sqrt (v + s ^ 2) * gapKeys Z k) + (-s * gapKeys ξ k) +
          ((Real.sqrt (v + s ^ 2) - Real.sqrt v) * gapKeys Z k)| := by ring_nf
    _ ≤ |gapKeys X k - k + s * gapKeys ξ k - Real.sqrt (v + s ^ 2) * gapKeys Z k| +
        |-s * gapKeys ξ k| + |(Real.sqrt (v + s ^ 2) - Real.sqrt v) * gapKeys Z k| :=
      abs_add_three _ _ _
    _ ≤ a + |s| * b + s ^ 2 / (2 * Real.sqrt v) * c := by
      rw [abs_mul, abs_neg, abs_mul]
      linarith

/-- For block endpoint couplings, smoothing noise is needed only at the left endpoint
of each block. The within-block fluctuations use the original source and Gaussian laws. -/
theorem sa_block_desmoothing_error {X ξ Z : ℕ → ℝ} {v s a b c r : ℝ}
    {n m : ℕ} (hv : 0 < v) (hm : 0 < m)
    (hend : ∀ j ≤ n / m,
      |gapKeys X (j * m) - j * m + s * gapKeys ξ (j * m) -
        Real.sqrt (v + s ^ 2) * gapKeys Z (j * m)| ≤ a)
    (hX : ∀ j ≤ n / m, ∀ k < m, j * m + k ≤ n →
      |gapKeys X (j * m + k) - gapKeys X (j * m) - k| ≤ b)
    (hZ : ∀ j ≤ n / m, ∀ k < m, j * m + k ≤ n →
      |gapKeys Z (j * m + k) - gapKeys Z (j * m)| ≤ c)
    (hξ : ∀ k ≤ n, |gapKeys ξ k| ≤ r)
    (hglobal : ∀ k ≤ n, |gapKeys Z k| ≤ r) :
    ∀ k ≤ n, |gapKeys X k - k - Real.sqrt v * gapKeys Z k| ≤
      a + |s| * r + b + Real.sqrt (v + s ^ 2) * c + s ^ 2 / (2 * Real.sqrt v) * r := by
  have he : ∀ j ≤ n / m,
      |(gapKeys X (j * m) - (j * m : ℕ)) - Real.sqrt (v + s ^ 2) * gapKeys Z (j * m)| ≤
        a + |s| * r := by
    intro j hj
    have hjm : j * m ≤ n := (Nat.mul_le_mul_right m hj).trans (Nat.div_mul_le_self _ _)
    have h₀ := hend j hj
    have h₁ := mul_le_mul_of_nonneg_left (hξ (j * m) hjm) (abs_nonneg s)
    have htri := abs_sub (gapKeys X (j * m) - j * m + s * gapKeys ξ (j * m) -
      Real.sqrt (v + s ^ 2) * gapKeys Z (j * m)) (s * gapKeys ξ (j * m))
    rw [abs_mul] at htri
    push_cast
    convert htri.trans (add_le_add h₀ h₁) using 1
    congr 1
    ring
  have hp := sa_block_prefix_error (S := fun k => gapKeys X k - k)
    (W := fun k => Real.sqrt (v + s ^ 2) * gapKeys Z k) hm he
    (fun j hj k hk hkn => by
      convert hX j hj k hk hkn using 1
      push_cast
      congr 1
      ring)
    (fun j hj k hk hkn => by
      have hb := mul_le_mul_of_nonneg_left (hZ j hj k hk hkn) (Real.sqrt_nonneg (v + s ^ 2))
      rwa [← mul_sub, abs_mul, abs_of_nonneg (Real.sqrt_nonneg (v + s ^ 2))])
  intro k hk
  have hc := mul_le_mul (sa_sqrt_variance_error (s := s) hv) (hglobal k hk)
    (abs_nonneg _) (by positivity : 0 ≤ s ^ 2 / (2 * Real.sqrt v))
  calc
    |gapKeys X k - k - Real.sqrt v * gapKeys Z k| =
        |(gapKeys X k - k - Real.sqrt (v + s ^ 2) * gapKeys Z k) +
          (Real.sqrt (v + s ^ 2) - Real.sqrt v) * gapKeys Z k| := by ring_nf
    _ ≤ |gapKeys X k - k - Real.sqrt (v + s ^ 2) * gapKeys Z k| +
        |(Real.sqrt (v + s ^ 2) - Real.sqrt v) * gapKeys Z k| := abs_add_le _ _
    _ ≤ _ := by rw [abs_mul]; exact add_le_add (hp k hk) hc

/-- A measurable construction with exact iid marginals and a good event gives the frozen
strong-approximation coupling interface. -/
theorem sa_coupling_of_good_event {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : ProbabilityMeasure ℝ)
    {X Z : Ω → ℕ → ℝ} (hX : Measurable X) (hZ : Measurable Z)
    (hlawX : P.map X = iidLaw ν) (hlawZ : P.map Z = iidLaw gaussPM)
    {n : ℕ} {a p : ℝ} {G : Set Ω}
    (hgood : ∀ ω ∈ G, ∀ k ≤ n,
      |gapKeys (X ω) k - k - Real.sqrt (lawVar ν) * gapKeys (Z ω) k| ≤ a)
    (hbad : P.real Gᶜ ≤ p) : HasSACoupling ν n a p := by
  let f : Ω → ((ℕ → ℝ) × (ℕ → ℝ)) := fun ω => (X ω, Z ω)
  have hf : Measurable f := hX.prodMk hZ
  refine ⟨P.map f, Measure.isProbabilityMeasure_map hf.aemeasurable, ?_, ?_, ?_⟩
  · rw [Measure.map_map measurable_fst hf]
    exact hlawX
  · rw [Measure.map_map measurable_snd hf]
    exact hlawZ
  · rw [map_measureReal_apply hf (measurableSet_SAEvent _ _ _)]
    refine (measureReal_mono ?_).trans hbad
    intro ω hω hG
    obtain ⟨k, hk, herr⟩ := hω
    exact (not_lt_of_ge (hgood ω hG k hk)) herr

end

end PGM
