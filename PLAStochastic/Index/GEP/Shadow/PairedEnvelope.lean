import PLAStochastic.Index.GEP.Shadow.PairedJointStop

/-!
# WP3: the paired one-layer envelope

`memory-route.md` §4–5 in one step: for iid active/passive pairs whose passive law `ρ` is in
`MomClass b β vmin` with `E e^{θ₁ Y} ≤ B₁` and a local bound `Dm`, whose active stop has the
tail `P(T_X > R) ≤ At e^{-aT R/eps²}` and mean in `[cm eps², cp eps²]`, and with
`E (X - Y)² ≤ Kd / eps²`, the law of `A^X / C_X` (`A^X = actSum`, `C_X = actMean`) is dominated
by `K e^{-c z} 1_{z > 0} dz` for all `eps ≥ e₁(Dm)`, with `K, c` **independent of `Dm`**
(`pairedLaw_envelope`).  This is the paired form of `lawPhi_envelope`
(`PLAStochastic/Index/GEP/OrbitClosure/OneLayerEnvelope.lean`); as there, the independence of the input density bound closes
the layer induction.

Proof of `pairedStopLaw_le`:
1. `map_actSum_eq_sum`: `Law(A^X) = ∑_t ν_t`, `ν_t = pStopMeas eps P V t`.
2. `F n = L₀/√n + Dm e^{-c₂(n-2)/Dm²}` from `locBd_convPow`.  Since `t > 2 eps` gives
   `⌊t/2⌋ ≥ N(Dm)` once `eps ≥ N(Dm) + 1`, `F(⌊t/2⌋) ≤ 2 L₀ ⌊t/2⌋^{-1/2}` (`dm_exp_le_inv_sqrt`);
   this replaces the `sum_aux_le` step of WP2.
3. `PairedHyp.pStopMeas_le_kernel` for `t > 2 eps`, `pStopMeas_eq_zero` otherwise.  With
   `δ = Kd/E` the residual term is `(C/E) t⁻¹ e^{-γ₂(t/E + Q_t(a))}`, and
   `sum_inv_exp_qdev_le` sums it to `(K/E) e^{-(γ₂/4) a/E}`; the main term is summed by
   `sum_kernel_le`.
4. `A^X > 0` a.s. restricts the bound to `(0, ∞)`.

`pairedLaw_envelope` rescales by `C_X ∈ [cm eps², cp eps²]` (`map_div_const_le`).
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-! ## Real analysis -/

/-- **The residual summation kernel**: `∑_t t⁻¹ e^{-γ(t/E + Q_t(a))} ≤ K e^{-(γ/4) a/E}`,
with `K` depending on `γ` only. -/
theorem sum_inv_exp_qdev_le {γ : ℝ} (hγ : 0 < γ) :
    ∃ K : ℝ, 0 < K ∧ ∀ E : ℝ, 1 ≤ E → ∀ a : ℝ, 0 ≤ a →
      ∑' t : ℕ, ENNReal.ofReal ((t : ℝ)⁻¹ * Real.exp (-γ * (t / E + qdev t a))) ≤
        ENNReal.ofReal (K * Real.exp (-(γ / 4) * a / E)) := by
  obtain ⟨K₁, hK₁, hsum⟩ := sum_sqrt_exp_qdev_le (b := γ / 2) (by positivity)
  refine ⟨K₁, hK₁, fun E hE a ha => ?_⟩
  have hE0 : 0 < E := by linarith
  set c : ℝ := Real.exp (-(γ / 4) * a / E) with hc
  have hc0 : 0 ≤ c := (Real.exp_pos _).le
  have hpt : ∀ t : ℕ, (t : ℝ)⁻¹ * Real.exp (-γ * (t / E + qdev t a)) ≤
      c * ((Real.sqrt t)⁻¹ * Real.exp (-(γ / 2) * qdev t a)) := by
    intro t
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · simp
    have ht0 : (0 : ℝ) < t := by exact_mod_cast ht
    have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
    have hq := qdev_add_ge hE ht0 ha
    have hq0 : 0 ≤ qdev t a := le_min (div_nonneg (sq_nonneg _) ht0.le) (abs_nonneg _)
    have hexp : Real.exp (-γ * (t / E + qdev t a)) ≤
        c * Real.exp (-(γ / 2) * qdev t a) := by
      rw [hc, ← Real.exp_add, Real.exp_le_exp]
      have ht' : 0 ≤ t / E := div_nonneg ht0.le hE0.le
      have h4 : a / (4 * E) ≤ (t / E + qdev t a) / 2 := by
        have : a / (4 * E) = a / (2 * E) / 2 := by ring
        rw [this]; linarith
      have e1 : -(γ / 4) * a / E = -(γ * (a / (4 * E))) := by ring
      rw [e1]
      have key : γ * (a / (4 * E)) ≤ γ * ((t / E + qdev t a) / 2) :=
        mul_le_mul_of_nonneg_left h4 hγ.le
      have key2 : 0 ≤ γ * (t / E) := mul_nonneg hγ.le ht'
      nlinarith
    have hinv : (t : ℝ)⁻¹ ≤ (Real.sqrt t)⁻¹ := by
      rw [inv_le_inv₀ ht0 (Real.sqrt_pos.2 ht0)]
      calc Real.sqrt t ≤ Real.sqrt t * Real.sqrt t :=
            le_mul_of_one_le_right (Real.sqrt_nonneg _) (Real.one_le_sqrt.2 ht1)
        _ = t := Real.mul_self_sqrt ht0.le
    calc (t : ℝ)⁻¹ * Real.exp (-γ * (t / E + qdev t a))
        ≤ (Real.sqrt t)⁻¹ * (c * Real.exp (-(γ / 2) * qdev t a)) :=
          mul_le_mul hinv hexp (Real.exp_pos _).le (by positivity)
      _ = c * ((Real.sqrt t)⁻¹ * Real.exp (-(γ / 2) * qdev t a)) := by ring
  calc ∑' t : ℕ, ENNReal.ofReal ((t : ℝ)⁻¹ * Real.exp (-γ * (t / E + qdev t a)))
      ≤ ∑' t : ℕ, ENNReal.ofReal c *
          ENNReal.ofReal ((Real.sqrt t)⁻¹ * Real.exp (-(γ / 2) * qdev t a)) := by
        refine ENNReal.tsum_le_tsum fun t => ?_
        rw [← ENNReal.ofReal_mul hc0]
        exact ENNReal.ofReal_le_ofReal (hpt t)
    _ = ENNReal.ofReal c *
          ∑' t : ℕ, ENNReal.ofReal ((Real.sqrt t)⁻¹ * Real.exp (-(γ / 2) * qdev t a)) :=
        ENNReal.tsum_mul_left
    _ ≤ ENNReal.ofReal c * ENNReal.ofReal K₁ := by gcongr; exact hsum a ha
    _ = ENNReal.ofReal (K₁ * c) := by rw [← ENNReal.ofReal_mul hc0, mul_comm]

/-- The input-density part of the local bound is eventually below `L₀/√n`. -/
theorem dm_exp_le_inv_sqrt {L₀ c₂ Dm : ℝ} (hL₀ : 0 < L₀) (hc₂ : 0 < c₂) (hDm : 0 < Dm) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Dm * Real.exp (-c₂ * ((n : ℝ) - 2) / Dm ^ 2) ≤ L₀ / Real.sqrt n := by
  set c : ℝ := c₂ / Dm ^ 2 with hc
  have hc0 : 0 < c := by positivity
  set A : ℝ := Dm * Real.exp (2 * c) / (L₀ * c) with hA
  have hA0 : 0 < A := by positivity
  refine ⟨⌈A ^ 2⌉₊ + 1, fun n hn => ?_⟩
  have hn1 : (1 : ℝ) ≤ n := by
    have : 1 ≤ n := by omega
    exact_mod_cast this
  have hn0 : (0 : ℝ) < n := by linarith
  have hnA : A ^ 2 ≤ n := by
    have h1 : A ^ 2 ≤ (⌈A ^ 2⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈A ^ 2⌉₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
    push_cast at h2
    linarith
  have hsA : A ≤ Real.sqrt n := by
    rw [← Real.sqrt_sq hA0.le]
    exact Real.sqrt_le_sqrt hnA
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 hn0
  have hsq : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hn0.le
  -- `e^{-c(n-2)} = e^{2c} e^{-cn} ≤ e^{2c} / (c n)`
  have he : Real.exp (-c₂ * ((n : ℝ) - 2) / Dm ^ 2) = Real.exp (2 * c) * Real.exp (-(c * n)) := by
    rw [← Real.exp_add, hc]
    congr 1
    ring
  have hcn : Real.exp (-(c * n)) ≤ 1 / (c * n) := by
    have h1 : c * n ≤ Real.exp (c * n) := by linarith [Real.add_one_le_exp (c * n)]
    have h2 : Real.exp (c * n) * Real.exp (-(c * n)) = 1 := by
      rw [← Real.exp_add]; simp
    rw [le_div_iff₀ (by positivity)]
    nlinarith [Real.exp_pos (-(c * n))]
  rw [he]
  calc Dm * (Real.exp (2 * c) * Real.exp (-(c * n)))
      ≤ Dm * (Real.exp (2 * c) * (1 / (c * n))) := by gcongr
    _ = A * L₀ / n := by rw [hA]; field_simp
    _ ≤ Real.sqrt n * L₀ / n := by gcongr
    _ = L₀ / Real.sqrt n := by
        rw [div_eq_div_iff (by positivity) hsn.ne']
        calc Real.sqrt n * L₀ * Real.sqrt n = L₀ * (Real.sqrt n * Real.sqrt n) := by ring
          _ = L₀ * n := by rw [hsq]

/-- `⌊t/2⌋ ≥ t/3` in the form `t⁻¹ ⌊t/2⌋^{-1/2} ≤ √3 t^{-3/2}` (a copy of the private WP2
lemma). -/
theorem inv_mul_inv_sqrt_half_le' (t : ℕ) :
    (t : ℝ)⁻¹ * (Real.sqrt ((t / 2 : ℕ) : ℝ))⁻¹ ≤ Real.sqrt 3 * ((t : ℝ) * Real.sqrt t)⁻¹ := by
  rcases Nat.eq_zero_or_pos (t / 2) with h0 | hr
  · rw [h0, Nat.cast_zero, Real.sqrt_zero, inv_zero, mul_zero]
    positivity
  · have ht2 : 2 ≤ t := by omega
    have ht0 : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
    have hr0 : (0 : ℝ) < ((t / 2 : ℕ) : ℝ) := by exact_mod_cast hr
    have htr : (t : ℝ) ≤ 3 * ((t / 2 : ℕ) : ℝ) := by
      exact_mod_cast (show t ≤ 3 * (t / 2) by omega)
    have hsq : Real.sqrt t ≤ Real.sqrt 3 * Real.sqrt ((t / 2 : ℕ) : ℝ) := by
      rw [← Real.sqrt_mul (by norm_num)]
      exact Real.sqrt_le_sqrt htr
    have e1 : (t : ℝ)⁻¹ * (Real.sqrt ((t / 2 : ℕ) : ℝ))⁻¹ =
        1 / ((t : ℝ) * Real.sqrt ((t / 2 : ℕ) : ℝ)) := by
      rw [one_div, mul_inv]
    have e2 : Real.sqrt 3 * ((t : ℝ) * Real.sqrt t)⁻¹ =
        Real.sqrt 3 / ((t : ℝ) * Real.sqrt t) := by
      rw [div_eq_mul_inv]
    rw [e1, e2, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hsq ht0.le]

/-- A local bound is monotone in its constant. -/
theorem LocBd.mono_le {D D' : ℝ} {μ : Measure ℝ} (h : LocBd D μ) (hDD : D ≤ D') :
    LocBd D' μ := fun A hA =>
  (h A hA).trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal hDD) _)

/-! ## The paired stopped sum -/

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The passive sum along the active tree has an exponential density envelope** on the time
scale `E = eps²`; `K, γ` do not depend on the passive density bound `Dm`. -/
theorem pairedStopLaw_le {b β vmin θ₁ B₁ At aT Kd : ℝ} (hvmin0 : 0 < vmin) (hvb : vmin ≤ b)
    (hβ1 : 1 ≤ β) (hθ₁ : 0 < θ₁) (hB₁ : 0 < B₁) (hAt : 0 ≤ At) (haT : 0 < aT) (hKd : 0 ≤ Kd) :
    ∃ K γ : ℝ, 0 < K ∧ 0 < γ ∧ ∀ Dm : ℝ, 0 < Dm → ∃ e : ℝ, ∀ eps, e ≤ eps →
      ∀ (P : Measure Ω) [IsProbabilityMeasure P] (V : ℕ → Ω → ℝ × ℝ)
        (ρ : ProbabilityMeasure ℝ), PairedHyp P V ρ eps At aT (Kd / eps ^ 2) →
        MomClass b β vmin ρ → ExpMom θ₁ B₁ ρ → LocBd Dm (ρ : Measure ℝ) →
        P.map (actSum eps V) ≤ volume.withDensity fun a =>
          ENNReal.ofReal ((Ioi (0 : ℝ)).indicator
            (fun a => K / eps ^ 2 * Real.exp (-γ * a / eps ^ 2)) a) := by
  obtain ⟨L₀, c₂, hL₀, hc₂, hloc⟩ := locBd_convPow hvmin0 hvb hβ1
  set c := bernsteinRate θ₁ B₁ with hcdef
  have hc0 : 0 < c := bernsteinRate_pos hθ₁ hB₁
  set γ₁ := pRate1 c aT with hγ₁def
  set γ₂ := pRate2 c aT with hγ₂def
  have hγ₁ : 0 < γ₁ := pRate1_pos hc0 haT
  have hγ₂ : 0 < γ₂ := pRate2_pos hc0 haT
  obtain ⟨K₁, hK₁, hsumk⟩ := sum_kernel_le hγ₁
  obtain ⟨K₂, hK₂, hsum2⟩ := sum_inv_exp_qdev_le hγ₂
  set C₁ := 8 + 32 * At with hC₁
  set C₂ := 584 + 32 * At with hC₂
  have hC₁0 : 0 < C₁ := by positivity
  have hC₂0 : 0 < C₂ := by positivity
  set A₁ := 2 * Real.sqrt 3 * L₀ * C₁ with hA₁
  set A₂ := 2 * Real.sqrt 3 * L₀ * C₂ * Real.sqrt Kd with hA₂
  have hA₁0 : 0 < A₁ := by positivity
  have hA₂0 : 0 ≤ A₂ := by positivity
  refine ⟨A₁ * K₁ + A₂ * K₂, min γ₁ γ₂ / 4, by positivity,
    by have := lt_min hγ₁ hγ₂; positivity, fun Dm hDm => ?_⟩
  obtain ⟨N, hN⟩ := dm_exp_le_inv_sqrt hL₀ hc₂ hDm
  refine ⟨max 8 ((N : ℝ) + 1), fun eps heps P _ V ρ h hρ hexp hρD => ?_⟩
  have heps8 : 8 ≤ eps := le_trans (le_max_left _ _) heps
  have hepsN : (N : ℝ) + 1 ≤ eps := le_trans (le_max_right _ _) heps
  have heps0 : 0 ≤ eps := by linarith
  have hE1 : 1 ≤ eps ^ 2 := by nlinarith
  have hE : 0 < eps ^ 2 := by positivity
  -- the local bounds `F n = L₀/√n + Dm e^{-c₂(n-2)/Dm²}`
  set F : ℕ → ℝ := fun n => L₀ / Real.sqrt n + Dm * Real.exp (-c₂ * ((n : ℝ) - 2) / Dm ^ 2)
    with hFdef
  have hF : ∀ n, 1 ≤ n → LocBd (F n) (convPow (ρ : Measure ℝ) n) := by
    intro n hn
    rcases Nat.lt_or_ge n 2 with hn2 | hn2
    · obtain rfl : n = 1 := by omega
      rw [convPow_one]
      refine hρD.mono_le ?_
      have e : -c₂ * (((1 : ℕ) : ℝ) - 2) / Dm ^ 2 = c₂ / Dm ^ 2 := by push_cast; ring
      have h1 : 1 ≤ Real.exp (-c₂ * (((1 : ℕ) : ℝ) - 2) / Dm ^ 2) :=
        Real.one_le_exp (by rw [e]; positivity)
      have h2 : 0 ≤ L₀ / Real.sqrt ((1 : ℕ) : ℝ) := by positivity
      show Dm ≤ L₀ / Real.sqrt ((1 : ℕ) : ℝ) + Dm * Real.exp (-c₂ * (((1 : ℕ) : ℝ) - 2) / Dm ^ 2)
      nlinarith
    · exact hloc ρ Dm hDm hρ hρD n hn2
  have hFa : ∀ n m, 1 ≤ n → n ≤ m → F m ≤ F n := by
    intro n m hn hnm
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hnm' : (n : ℝ) ≤ m := by exact_mod_cast hnm
    exact add_le_add (div_le_div_of_nonneg_left hL₀.le (Real.sqrt_pos.2 hn0)
      (Real.sqrt_le_sqrt hnm')) (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2
        (div_le_div_of_nonneg_right (by nlinarith) (sq_nonneg Dm))) hDm.le)
  have hFt : ∀ t : ℕ, 2 * eps < t → F (t / 2) ≤ 2 * L₀ * (Real.sqrt ((t / 2 : ℕ) : ℝ))⁻¹ := by
    intro t ht
    have hNt : N ≤ t / 2 := by
      have h1 : ((2 * N + 2 : ℕ) : ℝ) < t := by push_cast; linarith
      have h2 : 2 * N + 2 < t := by exact_mod_cast h1
      omega
    have hb := hN (t / 2) hNt
    show L₀ / Real.sqrt ((t / 2 : ℕ) : ℝ) +
      Dm * Real.exp (-c₂ * (((t / 2 : ℕ) : ℝ) - 2) / Dm ^ 2) ≤ _
    have e2 : 2 * L₀ * (Real.sqrt ((t / 2 : ℕ) : ℝ))⁻¹ =
        L₀ / Real.sqrt ((t / 2 : ℕ) : ℝ) + L₀ / Real.sqrt ((t / 2 : ℕ) : ℝ) := by ring
    rw [e2]
    linarith
  -- the densities of the joint stopping measures
  set kern : ℕ → ℝ → ℝ := fun t a =>
    C₁ / t * F (t / 2) * Real.exp (-γ₁ * (eps ^ 2 / t + t / eps ^ 2 + qdev t a)) +
      C₂ / t * F (t / 2) * Real.sqrt (t * (Kd / eps ^ 2) / eps ^ 2) *
        Real.exp (-γ₂ * (t / eps ^ 2 + qdev t a)) with hkern
  set dens : ℕ → ℝ → ℝ≥0∞ := fun t a =>
    if 2 * eps < (t : ℝ) then ENNReal.ofReal (kern t a) else 0 with hdens
  have hmd : ∀ t, Measurable (dens t) := by
    intro t
    have hq : Measurable fun x : ℝ => qdev t x :=
      Continuous.measurable (by unfold qdev; fun_prop)
    by_cases ht : 2 * eps < (t : ℝ)
    · simp only [hdens, if_pos ht, hkern]
      fun_prop
    · simp only [hdens, if_neg ht]
      exact measurable_const
  have hν : ∀ t, pStopMeas eps P V t ≤ volume.withDensity (dens t) := by
    intro t
    by_cases ht : 2 * eps < (t : ℝ)
    · refine (h.pStopMeas_le_kernel hθ₁ hAt haT heps8 hρ hexp hF hFa ht).trans
        (withDensity_mono (ae_of_all _ fun a => ?_))
      simp only [hdens, if_pos ht, hkern]
      exact le_rfl
    · rw [pStopMeas_eq_zero heps0 V (not_lt.1 ht)]
      exact Measure.zero_le _
  have hν' : ∀ t A, MeasurableSet A →
      pStopMeas eps P V t A ≤ ∫⁻ x in A, (Ioi 0).indicator (dens t) x := by
    intro t A hA
    rw [setLIntegral_indicator measurableSet_Ioi]
    calc pStopMeas eps P V t A ≤ pStopMeas eps P V t (Ioi 0 ∩ A ∪ Iic 0) := by
          refine measure_mono fun x hx => ?_
          by_cases h0 : 0 < x
          · exact Or.inl ⟨h0, hx⟩
          · exact Or.inr (not_lt.1 h0)
      _ ≤ pStopMeas eps P V t (Ioi 0 ∩ A) + pStopMeas eps P V t (Iic 0) := measure_union_le _ _
      _ = pStopMeas eps P V t (Ioi 0 ∩ A) := by
          rw [h.pStopMeas_Iic hρ.pos heps0 t, add_zero]
      _ ≤ volume.withDensity (dens t) (Ioi 0 ∩ A) := hν t _
      _ = ∫⁻ x in Ioi 0 ∩ A, dens t x := withDensity_apply _ (measurableSet_Ioi.inter hA)
  -- the pointwise bound of each term
  have hterm : ∀ t : ℕ, ∀ x : ℝ, dens t x ≤
      ENNReal.ofReal A₁ * ENNReal.ofReal (((t : ℝ) * Real.sqrt t)⁻¹ *
          Real.exp (-γ₁ * (eps ^ 2 / t + t / eps ^ 2 + qdev t x))) +
        ENNReal.ofReal (A₂ / eps ^ 2) * ENNReal.ofReal ((t : ℝ)⁻¹ *
          Real.exp (-γ₂ * (t / eps ^ 2 + qdev t x))) := by
    intro t x
    by_cases ht : 2 * eps < (t : ℝ)
    · simp only [hdens, if_pos ht]
      rw [← ENNReal.ofReal_mul hA₁0.le, ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have htpos : (0 : ℝ) < t := by linarith
      have hFt' := hFt t ht
      have hr := inv_mul_inv_sqrt_half_le' t
      have hF0 : 0 ≤ F (t / 2) := by simp only [hFdef]; positivity
      set e1 := Real.exp (-γ₁ * (eps ^ 2 / t + t / eps ^ 2 + qdev t x)) with he1
      set e2 := Real.exp (-γ₂ * (t / eps ^ 2 + qdev t x)) with he2
      have he10 : 0 ≤ e1 := (Real.exp_pos _).le
      have he20 : 0 ≤ e2 := (Real.exp_pos _).le
      have hsqrt : Real.sqrt (t * (Kd / eps ^ 2) / eps ^ 2) =
          Real.sqrt t * Real.sqrt Kd / eps ^ 2 := by
        have e : (t : ℝ) * (Kd / eps ^ 2) / eps ^ 2 =
            (Real.sqrt t * Real.sqrt Kd / eps ^ 2) ^ 2 := by
          rw [div_pow, mul_pow, Real.sq_sqrt htpos.le, Real.sq_sqrt hKd]
          ring
        rw [e, Real.sqrt_sq (by positivity)]
      have hst : ((t : ℝ) * Real.sqrt t)⁻¹ * Real.sqrt t = (t : ℝ)⁻¹ := by
        have : 0 < Real.sqrt t := Real.sqrt_pos.2 htpos
        field_simp
      have hsr0 : 0 ≤ (Real.sqrt ((t / 2 : ℕ) : ℝ))⁻¹ := by positivity
      have key : (t : ℝ)⁻¹ * F (t / 2) ≤ 2 * L₀ * Real.sqrt 3 * ((t : ℝ) * Real.sqrt t)⁻¹ := by
        calc (t : ℝ)⁻¹ * F (t / 2) ≤ (t : ℝ)⁻¹ * (2 * L₀ * (Real.sqrt ((t / 2 : ℕ) : ℝ))⁻¹) :=
              mul_le_mul_of_nonneg_left hFt' (by positivity)
          _ = 2 * L₀ * ((t : ℝ)⁻¹ * (Real.sqrt ((t / 2 : ℕ) : ℝ))⁻¹) := by ring
          _ ≤ 2 * L₀ * (Real.sqrt 3 * ((t : ℝ) * Real.sqrt t)⁻¹) :=
              mul_le_mul_of_nonneg_left hr (by positivity)
          _ = 2 * L₀ * Real.sqrt 3 * ((t : ℝ) * Real.sqrt t)⁻¹ := by ring
      show C₁ / t * F (t / 2) * e1 + C₂ / t * F (t / 2) *
          Real.sqrt (t * (Kd / eps ^ 2) / eps ^ 2) * e2 ≤ _
      rw [hsqrt]
      have k1 : C₁ / t * F (t / 2) * e1 ≤ A₁ * (((t : ℝ) * Real.sqrt t)⁻¹ * e1) := by
        calc C₁ / t * F (t / 2) * e1 = C₁ * ((t : ℝ)⁻¹ * F (t / 2)) * e1 := by ring
          _ ≤ C₁ * (2 * L₀ * Real.sqrt 3 * ((t : ℝ) * Real.sqrt t)⁻¹) * e1 := by gcongr
          _ = A₁ * (((t : ℝ) * Real.sqrt t)⁻¹ * e1) := by rw [hA₁]; ring
      have k2 : C₂ / t * F (t / 2) * (Real.sqrt t * Real.sqrt Kd / eps ^ 2) * e2 ≤
          A₂ / eps ^ 2 * ((t : ℝ)⁻¹ * e2) := by
        calc C₂ / t * F (t / 2) * (Real.sqrt t * Real.sqrt Kd / eps ^ 2) * e2
            = C₂ * ((t : ℝ)⁻¹ * F (t / 2)) * Real.sqrt t * Real.sqrt Kd / eps ^ 2 * e2 := by
              ring
          _ ≤ C₂ * (2 * L₀ * Real.sqrt 3 * ((t : ℝ) * Real.sqrt t)⁻¹) * Real.sqrt t *
                Real.sqrt Kd / eps ^ 2 * e2 := by gcongr
          _ = A₂ / eps ^ 2 * ((((t : ℝ) * Real.sqrt t)⁻¹ * Real.sqrt t) * e2) := by
              rw [hA₂]; ring
          _ = A₂ / eps ^ 2 * ((t : ℝ)⁻¹ * e2) := by rw [hst]
      linarith
    · simp only [hdens, if_neg ht]
      exact zero_le
  have hpt : ∀ x : ℝ, ∑' t, (Ioi 0).indicator (dens t) x ≤
      ENNReal.ofReal ((Ioi (0 : ℝ)).indicator (fun a => (A₁ * K₁ + A₂ * K₂) / eps ^ 2 *
        Real.exp (-(min γ₁ γ₂ / 4) * a / eps ^ 2)) x) := by
    intro x
    by_cases hx : x ∈ Ioi (0 : ℝ)
    · simp_rw [Set.indicator_of_mem hx]
      have hx0 : 0 ≤ x := le_of_lt hx
      have hm1 : Real.exp (-(γ₁ / 4) * x / eps ^ 2) ≤
          Real.exp (-(min γ₁ γ₂ / 4) * x / eps ^ 2) := by
        refine Real.exp_le_exp.2 ?_
        rw [neg_mul, neg_mul, neg_div, neg_div, neg_le_neg_iff]
        have := min_le_left γ₁ γ₂
        gcongr
      have hm2 : Real.exp (-(γ₂ / 4) * x / eps ^ 2) ≤
          Real.exp (-(min γ₁ γ₂ / 4) * x / eps ^ 2) := by
        refine Real.exp_le_exp.2 ?_
        rw [neg_mul, neg_mul, neg_div, neg_div, neg_le_neg_iff]
        have := min_le_right γ₁ γ₂
        gcongr
      calc ∑' t, dens t x
          ≤ ∑' t : ℕ, (ENNReal.ofReal A₁ * ENNReal.ofReal (((t : ℝ) * Real.sqrt t)⁻¹ *
                Real.exp (-γ₁ * (eps ^ 2 / t + t / eps ^ 2 + qdev t x))) +
              ENNReal.ofReal (A₂ / eps ^ 2) * ENNReal.ofReal ((t : ℝ)⁻¹ *
                Real.exp (-γ₂ * (t / eps ^ 2 + qdev t x)))) :=
            ENNReal.tsum_le_tsum fun t => hterm t x
        _ = ENNReal.ofReal A₁ * ∑' t : ℕ, ENNReal.ofReal (((t : ℝ) * Real.sqrt t)⁻¹ *
                Real.exp (-γ₁ * (eps ^ 2 / t + t / eps ^ 2 + qdev t x))) +
              ENNReal.ofReal (A₂ / eps ^ 2) * ∑' t : ℕ, ENNReal.ofReal ((t : ℝ)⁻¹ *
                Real.exp (-γ₂ * (t / eps ^ 2 + qdev t x))) := by
            rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
        _ ≤ ENNReal.ofReal A₁ *
              ENNReal.ofReal (K₁ / eps ^ 2 * Real.exp (-(γ₁ / 4) * x / eps ^ 2)) +
            ENNReal.ofReal (A₂ / eps ^ 2) *
              ENNReal.ofReal (K₂ * Real.exp (-(γ₂ / 4) * x / eps ^ 2)) := by
            gcongr
            · exact hsumk _ hE1 x hx0
            · exact hsum2 _ hE1 x hx0
        _ = ENNReal.ofReal (A₁ * (K₁ / eps ^ 2 * Real.exp (-(γ₁ / 4) * x / eps ^ 2)) +
              A₂ / eps ^ 2 * (K₂ * Real.exp (-(γ₂ / 4) * x / eps ^ 2))) := by
            rw [← ENNReal.ofReal_mul hA₁0.le, ← ENNReal.ofReal_mul (by positivity),
              ← ENNReal.ofReal_add (by positivity) (by positivity)]
        _ ≤ ENNReal.ofReal ((A₁ * K₁ + A₂ * K₂) / eps ^ 2 *
              Real.exp (-(min γ₁ γ₂ / 4) * x / eps ^ 2)) := by
            refine ENNReal.ofReal_le_ofReal ?_
            have i1 : A₁ * (K₁ / eps ^ 2 * Real.exp (-(γ₁ / 4) * x / eps ^ 2)) ≤
                A₁ * K₁ / eps ^ 2 * Real.exp (-(min γ₁ γ₂ / 4) * x / eps ^ 2) := by
              calc A₁ * (K₁ / eps ^ 2 * Real.exp (-(γ₁ / 4) * x / eps ^ 2))
                  = A₁ * K₁ / eps ^ 2 * Real.exp (-(γ₁ / 4) * x / eps ^ 2) := by ring
                _ ≤ _ := by gcongr
            have i2 : A₂ / eps ^ 2 * (K₂ * Real.exp (-(γ₂ / 4) * x / eps ^ 2)) ≤
                A₂ * K₂ / eps ^ 2 * Real.exp (-(min γ₁ γ₂ / 4) * x / eps ^ 2) := by
              calc A₂ / eps ^ 2 * (K₂ * Real.exp (-(γ₂ / 4) * x / eps ^ 2))
                  = A₂ * K₂ / eps ^ 2 * Real.exp (-(γ₂ / 4) * x / eps ^ 2) := by ring
                _ ≤ _ := by gcongr
            have e : (A₁ * K₁ + A₂ * K₂) / eps ^ 2 * Real.exp (-(min γ₁ γ₂ / 4) * x / eps ^ 2) =
                A₁ * K₁ / eps ^ 2 * Real.exp (-(min γ₁ γ₂ / 4) * x / eps ^ 2) +
                  A₂ * K₂ / eps ^ 2 * Real.exp (-(min γ₁ γ₂ / 4) * x / eps ^ 2) := by ring
            rw [e]
            exact add_le_add i1 i2
    · simp_rw [Set.indicator_of_notMem hx]
      simp
  rw [map_actSum_eq_sum h.iid.measurable h.fin, Measure.le_iff]
  intro A hA
  rw [Measure.sum_apply _ hA, withDensity_apply _ hA]
  calc ∑' t, pStopMeas eps P V t A ≤ ∑' t, ∫⁻ x in A, (Ioi 0).indicator (dens t) x :=
        ENNReal.tsum_le_tsum fun t => hν' t A hA
    _ = ∫⁻ x in A, ∑' t, (Ioi 0).indicator (dens t) x :=
        (lintegral_tsum fun t => ((hmd t).indicator measurableSet_Ioi).aemeasurable).symm
    _ ≤ _ := lintegral_mono fun x => hpt x


/-- **The paired one-layer envelope.**  `K` and `c` do not depend on the passive density bound
`Dm`; only the threshold does. -/
theorem pairedLaw_envelope {b β vmin θ₁ B₁ At aT Kd cm cp : ℝ} (hvmin0 : 0 < vmin)
    (hvb : vmin ≤ b) (hβ1 : 1 ≤ β) (hθ₁ : 0 < θ₁) (hB₁ : 0 < B₁) (hAt : 0 ≤ At) (haT : 0 < aT)
    (hKd : 0 ≤ Kd) (hcm : 0 < cm) (hcp : cm ≤ cp) :
    ∃ K c : ℝ, 0 < K ∧ 0 < c ∧ ∀ Dm : ℝ, 0 < Dm → ∃ e₁ : ℝ, ∀ eps, e₁ ≤ eps →
      ∀ (P : Measure Ω) [IsProbabilityMeasure P] (V : ℕ → Ω → ℝ × ℝ)
        (ρ : ProbabilityMeasure ℝ), PairedHyp P V ρ eps At aT (Kd / eps ^ 2) →
        MomClass b β vmin ρ → ExpMom θ₁ B₁ ρ → LocBd Dm (ρ : Measure ℝ) →
        cm * eps ^ 2 ≤ actMean eps P V → actMean eps P V ≤ cp * eps ^ 2 →
        EnvBd K c (P.map fun ω => actSum eps V ω / actMean eps P V) := by
  obtain ⟨K', γ, hK', hγ, hstop⟩ :=
    pairedStopLaw_le (Ω := Ω) hvmin0 hvb hβ1 hθ₁ hB₁ hAt haT hKd
  have hcp0 : 0 < cp := hcm.trans_le hcp
  refine ⟨cp * K', γ * cm, by positivity, by positivity, fun Dm hDm => ?_⟩
  obtain ⟨e, he⟩ := hstop Dm hDm
  refine ⟨max e 1, fun eps heps P _ V ρ h hρ hexp hρD hCm hCp => ?_⟩
  have he' : e ≤ eps := le_trans (le_max_left _ _) heps
  have heps1 : 1 ≤ eps := le_trans (le_max_right _ _) heps
  set C := actMean eps P V with hCdef
  have hE : 0 < eps ^ 2 := by positivity
  have hC : 0 < C := lt_of_lt_of_le (by positivity) hCm
  have hmap := map_div_const_le (he eps he' P V ρ h hρ hexp hρD) hC
  have hlaw : (P.map fun ω => actSum eps V ω / C) =
      (P.map (actSum eps V)).map (fun x => x / C) := by
    have hdiv : Measurable fun x : ℝ => x / C := measurable_id.div_const C
    rw [Measure.map_map hdiv (measurable_actSum h.iid.measurable eps)]
    rfl
  unfold EnvBd
  rw [hlaw]
  refine hmap.trans (withDensity_mono (Filter.Eventually.of_forall fun z => ?_))
  refine ENNReal.ofReal_le_ofReal ?_
  simp only [envFun, Set.indicator_apply, Set.mem_Ioi]
  by_cases hz : 0 < z
  · have hCz : 0 < C * z := mul_pos hC hz
    rw [if_pos hCz, if_pos hz]
    have h1 : C / eps ^ 2 ≤ cp := by rw [div_le_iff₀ hE]; exact hCp
    have h2 : cm ≤ C / eps ^ 2 := by rw [le_div_iff₀ hE]; exact hCm
    have hex : Real.exp (-γ * (C * z) / eps ^ 2) ≤ Real.exp (-(γ * cm) * z) := by
      refine Real.exp_le_exp.2 ?_
      have : γ * cm * z ≤ γ * (C * z) / eps ^ 2 := by
        calc γ * cm * z = γ * z * cm := by ring
          _ ≤ γ * z * (C / eps ^ 2) := mul_le_mul_of_nonneg_left h2 (by positivity)
          _ = γ * (C * z) / eps ^ 2 := by ring
      rw [neg_mul, neg_mul, neg_div]
      exact neg_le_neg this
    calc C * (K' / eps ^ 2 * Real.exp (-γ * (C * z) / eps ^ 2))
        = C / eps ^ 2 * K' * Real.exp (-γ * (C * z) / eps ^ 2) := by ring
      _ ≤ cp * K' * Real.exp (-(γ * cm) * z) := by gcongr
  · have hCz : ¬ 0 < C * z := not_lt.2 (mul_nonpos_of_nonneg_of_nonpos hC.le (not_lt.1 hz))
    rw [if_neg hCz, if_neg hz, mul_zero]


end

end PGM
