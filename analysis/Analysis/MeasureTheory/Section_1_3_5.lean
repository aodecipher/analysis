import Analysis.MeasureTheory.Section_1_3_4

/-!
# Introduction to Measure Theory, Section 1.3.5: Littlewood's three principles

A companion to (the introduction to) Section 1.3.5 of the book "An introduction to Measure Theory".

-/

/-! ### Helper lemmas for Theorem 1.3.20(i)

The proof follows the book's argument:
1. For unsigned f, use the definition of lower Lebesgue integral as a supremum to extract
   an approximating simple function g ≤ f with ∫g ≥ ∫f - ε.
2. For real f, split into positive and negative parts f = f⁺ - f⁻, approximate each.
3. For complex f, split into real and imaginary parts, approximate each.
-/

/-- For unsigned absolutely integrable f, there exists an unsigned simple function g ≤ f
    with integral close to f's integral. This is the key step from the informal proof:
    "from the definition of the lower Lebesgue integral, there exists an unsigned simple
    function g such that g ≤ f and ∫g ≥ ∫f - ε" -/
theorem UnsignedAbsolutelyIntegrable.approx_by_simple_le {d:ℕ} {f: EuclideanSpace' d → EReal}
    (hf : UnsignedAbsolutelyIntegrable f) (ε : ℝ) (hε : 0 < ε) :
    ∃ (g : EuclideanSpace' d → EReal), UnsignedSimpleFunction g ∧
      (∀ x, g x ≤ f x) ∧
      UnsignedLebesgueIntegral f - ε ≤ UnsignedLebesgueIntegral g := by
  -- The lower integral is defined as sSup { hg.integ | g simple, g ≤ f }
  -- Since f is absolutely integrable, ∫f < ⊤, so ∫f - ε < ∫f
  -- By lt_sSup_iff, there exists a simple g ≤ f with ∫g > ∫f - ε
  have hf_finite : UnsignedLebesgueIntegral f < ⊤ := hf.2
  have hf_nn := UnsignedLebesgueIntegral.nonneg hf.1
  by_cases hzero : UnsignedLebesgueIntegral f ≤ ε
  · -- Case 1: ∫f ≤ ε, take g = 0; then ∫f - ε ≤ 0 = ∫g
    use 0
    have h_simple : UnsignedSimpleFunction (0 : EuclideanSpace' d → EReal) := by
      use 0, fun i => Fin.elim0 i, fun i => Fin.elim0 i
      constructor
      · intro i; exact Fin.elim0 i
      · funext x; simp only [Pi.zero_apply, Finset.univ_eq_empty, Finset.sum_empty]
    refine ⟨h_simple, ?_, ?_⟩
    · -- 0 ≤ f pointwise
      exact hf.1.1
    · -- ∫f - ε ≤ ∫0 = 0
      have h0 : UnsignedLebesgueIntegral (0 : EuclideanSpace' d → EReal) = 0 := by
        rw [UnsignedLebesgueIntegral, LowerUnsignedLebesgueIntegral.eq_simpleIntegral h_simple]
        exact UnsignedSimpleFunction.integ_zero
      rw [h0]
      calc UnsignedLebesgueIntegral f - ↑ε
          ≤ ↑ε - ↑ε := EReal.sub_le_sub hzero le_rfl
        _ = 0 := EReal.sub_self (EReal.coe_ne_top ε) (EReal.coe_ne_bot ε)
  · -- Case 2: ∫f > ε, extract approximating function from supremum
    push_neg at hzero
    -- Convert integral to real value
    have h_ne_top : UnsignedLebesgueIntegral f ≠ ⊤ := ne_of_lt hf_finite
    have h_ne_bot : UnsignedLebesgueIntegral f ≠ ⊥ := ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero hf_nn)
    set r := (UnsignedLebesgueIntegral f).toReal with hr_def
    have hr : UnsignedLebesgueIntegral f = r.toEReal := (EReal.coe_toReal h_ne_top h_ne_bot).symm
    have hrnn : 0 ≤ r := by
      rw [← EReal.coe_le_coe_iff, ← hr]
      exact hf_nn
    have hr_gt : r > ε := by rw [hr] at hzero; exact EReal.coe_lt_coe_iff.mp hzero
    -- The lower integral is a sSup, so (r - ε) < r = ∫f implies existence
    have hlt : (r - ε).toEReal < LowerUnsignedLebesgueIntegral f := by
      rw [← UnsignedLebesgueIntegral, hr]; exact EReal.coe_lt_coe_iff.mpr (by linarith)
    -- By lt_sSup_iff applied to the definition of LowerUnsignedLebesgueIntegral
    rw [LowerUnsignedLebesgueIntegral, lt_sSup_iff] at hlt
    obtain ⟨R, hR_mem, hR_gt⟩ := hlt
    -- Extract the simple function from membership
    simp only [Set.mem_setOf_eq] at hR_mem
    obtain ⟨g, hg_simple, hg_cond⟩ := hR_mem
    -- The condition is ∀ x, g x ≤ f x ∧ R = hg_simple.integ
    -- This is an unusual format, extract both parts
    have hg_le : ∀ x, g x ≤ f x := fun x => (hg_cond x).1
    have hR_eq : R = hg_simple.integ := by
      haveI : Nonempty (EuclideanSpace' d) := inferInstance
      exact (hg_cond (Classical.arbitrary _)).2
    use g
    refine ⟨hg_simple, hg_le, ?_⟩
    -- Need: ∫f - ε ≤ ∫g
    have hg_int : UnsignedLebesgueIntegral g = hg_simple.integ :=
      LowerUnsignedLebesgueIntegral.eq_simpleIntegral hg_simple
    calc UnsignedLebesgueIntegral f - ↑ε
        = ↑r - ↑ε := by rw [hr]
      _ ≤ R := le_of_lt hR_gt
      _ = hg_simple.integ := hR_eq
      _ = UnsignedLebesgueIntegral g := hg_int.symm

/-! ### Conversion from UnsignedSimpleFunction to RealSimpleFunction

When an unsigned simple function is bounded by a finite-valued real function (like pos_fun f),
it can be converted to a real-valued simple function. This is needed to construct
real simple approximations from the EReal-valued ones obtained from approx_by_simple_le.
-/

/-- Convert an unsigned simple function to real by taking toReal of coefficients -/
noncomputable def UnsignedSimpleFunction.toRealFun {d:ℕ}
    {f: EuclideanSpace' d → EReal} (hf : UnsignedSimpleFunction f) :
    EuclideanSpace' d → ℝ :=
  let k := hf.choose
  let c := hf.choose_spec.choose
  let E := hf.choose_spec.choose_spec.choose
  fun x => ∑ i : Fin k, (c i).toReal * (E i).indicator' x

/-- EReal bounded by a finite real is finite -/
lemma EReal.ne_top_of_le_coe {x : EReal} {r : ℝ} (h : x ≤ (r : EReal)) : x ≠ ⊤ :=
  ne_top_of_le_ne_top (EReal.coe_ne_top r) h

/-! #### EReal arithmetic lemmas -/

/-- a + (b - a) = b when a ≤ b and a ≠ ⊥ and b ≠ ⊤ -/
lemma EReal.add_sub_cancel' {a b : EReal} (h_le : a ≤ b) (ha_ne_bot : a ≠ ⊥) (hb_ne_top : b ≠ ⊤) :
    a + (b - a) = b := by
  by_cases ha_top : a = ⊤
  · exact (hb_ne_top (top_unique (ha_top ▸ h_le))).elim
  · have ha_finite : a = (a.toReal : EReal) := (EReal.coe_toReal ha_top ha_ne_bot).symm
    by_cases hb_bot : b = ⊥
    · rw [hb_bot] at h_le
      exact (ha_ne_bot (le_bot_iff.mp h_le)).elim
    · have hb_finite : b = (b.toReal : EReal) := (EReal.coe_toReal hb_ne_top hb_bot).symm
      rw [ha_finite, hb_finite]
      rw [← EReal.coe_sub, ← EReal.coe_add]
      congr 1
      ring

/-- a - (a - b) = b when a ≠ ⊤ and a ≠ ⊥ -/
lemma EReal.sub_sub_cancel' {a : EReal} {b : ℝ} (ha_ne_top : a ≠ ⊤) (ha_ne_bot : a ≠ ⊥) :
    a - (a - b) = b := by
  have ha_finite : a = (a.toReal : EReal) := (EReal.coe_toReal ha_ne_top ha_ne_bot).symm
  rw [ha_finite]
  rw [← EReal.coe_sub, ← EReal.coe_sub]
  congr 1
  ring

/-- Subtraction is antitone in second argument: x - y ≤ x - z when z ≤ y -/
lemma EReal.sub_le_sub_left' {x y z : EReal} (h : z ≤ y) : x - y ≤ x - z :=
  EReal.sub_le_sub (le_refl x) h

/-! #### Helper lemmas for UnsignedSimpleFunction conversion -/

/-- Unsigned function bounded by pos_fun of a real function has finite values -/
lemma UnsignedSimpleFunction.finite_of_le_pos_fun {d:ℕ}
    {g: EuclideanSpace' d → EReal} (_hg : UnsignedSimpleFunction g)
    {f: EuclideanSpace' d → ℝ} (hle : ∀ x, g x ≤ EReal.pos_fun f x)
    (x : EuclideanSpace' d) : g x ≠ ⊤ := by
  apply EReal.ne_top_of_le_coe (r := max (f x) 0)
  simp only [EReal.pos_fun] at hle ⊢
  exact hle x

/-- toRealFun of an unsigned simple function is a real simple function -/
lemma UnsignedSimpleFunction.toRealFun_isSimple {d:ℕ}
    {f: EuclideanSpace' d → EReal} (hf : UnsignedSimpleFunction f) :
    RealSimpleFunction hf.toRealFun := by
  unfold UnsignedSimpleFunction.toRealFun
  use hf.choose, fun i => (hf.choose_spec.choose i).toReal, hf.choose_spec.choose_spec.choose
  constructor
  · intro i
    exact (hf.choose_spec.choose_spec.choose_spec.1 i).1
  · funext x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

/-- Unsigned simple function has non-negative values -/
lemma UnsignedSimpleFunction.nonneg {d:ℕ}
    {f: EuclideanSpace' d → EReal} (hf : UnsignedSimpleFunction f)
    (x : EuclideanSpace' d) : f x ≥ 0 := by
  obtain ⟨k, c, E, hE, heq⟩ := hf
  rw [heq]; clear heq
  simp only [Finset.sum_apply, Pi.smul_apply]
  apply Finset.sum_nonneg
  intro i _
  simp only [smul_eq_mul]
  by_cases hx : x ∈ E i
  · simp only [EReal.indicator, Real.EReal_fun, Set.indicator'_of_mem hx, EReal.coe_one, mul_one]
    exact (hE i).2
  · simp only [EReal.indicator, Real.EReal_fun, Set.indicator'_of_notMem hx, EReal.coe_zero, mul_zero, le_refl]

/-- Nonneg EReal is not bot -/
lemma EReal.ne_bot_of_nonneg {x : EReal} (h : x ≥ 0) : x ≠ ⊥ := by
  intro hbot
  rw [hbot] at h
  exact (not_le.mpr EReal.bot_lt_zero) h

/-- EReal.toReal of nonneg value is ≤ the value (in EReal) -/
lemma EReal.coe_toReal_le_self {x : EReal} (hx : x ≥ 0) : (x.toReal : EReal) ≤ x := by
  by_cases hx_top : x = ⊤
  · simp only [hx_top, EReal.toReal_top, EReal.coe_zero, le_top]
  · by_cases hx_bot : x = ⊥
    · simp only [hx_bot] at hx
      exact (not_le.mpr EReal.bot_lt_zero hx).elim
    · rw [EReal.coe_toReal hx_top hx_bot]

/-- toRealFun is bounded by the original function (in EReal) -/
lemma UnsignedSimpleFunction.coe_toRealFun_le {d:ℕ}
    {g: EuclideanSpace' d → EReal} (hg : UnsignedSimpleFunction g)
    (x : EuclideanSpace' d) : (hg.toRealFun x : EReal) ≤ g x := by
  unfold UnsignedSimpleFunction.toRealFun
  have hspec := hg.choose_spec.choose_spec.choose_spec
  have hE : ∀ i, LebesgueMeasurable (hg.choose_spec.choose_spec.choose i) ∧
                 hg.choose_spec.choose i ≥ 0 := hspec.1
  have heq : g = ∑ i, (hg.choose_spec.choose i) • (EReal.indicator (hg.choose_spec.choose_spec.choose i)) := hspec.2
  conv_rhs => rw [heq]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have h_nonneg : ∀ a ∈ Finset.univ, 0 ≤ (hg.choose_spec.choose a).toReal * (hg.choose_spec.choose_spec.choose a).indicator' x := by
    intro a _
    apply mul_nonneg
    · exact EReal.toReal_nonneg (hE a).2
    · by_cases hx : x ∈ hg.choose_spec.choose_spec.choose a
      · simp only [Set.indicator'_of_mem hx]; norm_num
      · simp only [Set.indicator'_of_notMem hx]; norm_num
  rw [EReal.coe_finset_sum h_nonneg]
  apply Finset.sum_le_sum
  intro i _
  simp only [EReal.coe_mul]
  by_cases hx : x ∈ hg.choose_spec.choose_spec.choose i
  · simp only [Set.indicator'_of_mem hx, EReal.indicator, Real.EReal_fun,
      EReal.coe_one, mul_one]
    exact EReal.coe_toReal_le_self (hE i).2
  · simp only [Set.indicator'_of_notMem hx, EReal.indicator, Real.EReal_fun,
      EReal.coe_zero, mul_zero, le_refl]

/-- If a nonneg term in a finset sum is ⊤, the sum is ⊤ -/
lemma EReal.finset_sum_eq_top_of_mem_top {ι : Type*} {s : Finset ι} {f : ι → EReal}
    (h_nonneg : ∀ i ∈ s, f i ≥ 0) {i : ι} (hi : i ∈ s) (hfi : f i = ⊤) :
    ∑ j ∈ s, f j = ⊤ := by
  have h1 : f i ≤ ∑ j ∈ s, f j := Finset.single_le_sum h_nonneg hi
  rw [hfi] at h1
  exact top_unique h1

/-- When g is bounded by a finite function, toRealFun equals g -/
lemma UnsignedSimpleFunction.coe_toRealFun_eq {d:ℕ}
    {g: EuclideanSpace' d → EReal} (hg : UnsignedSimpleFunction g)
    {f: EuclideanSpace' d → ℝ} (hle : ∀ x, g x ≤ EReal.pos_fun f x)
    (x : EuclideanSpace' d) : (hg.toRealFun x : EReal) = g x := by
  have hg_finite : g x ≠ ⊤ := hg.finite_of_le_pos_fun hle x
  have hg_nonneg : g x ≥ 0 := hg.nonneg x
  have hcoeff_finite : ∀ i : Fin hg.choose,
      x ∈ hg.choose_spec.choose_spec.choose i →
      hg.choose_spec.choose i ≠ ⊤ := by
    intro i hx_mem
    intro hci_top
    have heq := hg.choose_spec.choose_spec.choose_spec.2
    have hgx_top : g x = ⊤ := by
      rw [heq]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      have h_term : hg.choose_spec.choose i * EReal.indicator (hg.choose_spec.choose_spec.choose i) x = ⊤ := by
        simp only [EReal.indicator, Real.EReal_fun, Set.indicator'_of_mem hx_mem, EReal.coe_one, hci_top]
        exact EReal.top_mul_of_pos (by norm_num : (0 : EReal) < 1)
      have hE := hg.choose_spec.choose_spec.choose_spec.1
      have h_nonneg : ∀ j ∈ Finset.univ, hg.choose_spec.choose j * EReal.indicator (hg.choose_spec.choose_spec.choose j) x ≥ 0 := by
        intro j _
        by_cases hxj : x ∈ hg.choose_spec.choose_spec.choose j
        · simp only [EReal.indicator, Real.EReal_fun, Set.indicator'_of_mem hxj, EReal.coe_one, mul_one]
          exact (hE j).2
        · simp only [EReal.indicator, Real.EReal_fun, Set.indicator'_of_notMem hxj, EReal.coe_zero, mul_zero, le_refl]
      exact EReal.finset_sum_eq_top_of_mem_top h_nonneg (Finset.mem_univ i) h_term
    exact hg_finite hgx_top
  apply le_antisymm
  · exact hg.coe_toRealFun_le x
  · unfold UnsignedSimpleFunction.toRealFun
    have heq := hg.choose_spec.choose_spec.choose_spec.2
    conv_lhs => rw [heq]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    have hE := hg.choose_spec.choose_spec.choose_spec.1
    have h_nonneg : ∀ a ∈ Finset.univ, 0 ≤ (hg.choose_spec.choose a).toReal * (hg.choose_spec.choose_spec.choose a).indicator' x := by
      intro a _
      apply mul_nonneg
      · exact EReal.toReal_nonneg (hE a).2
      · by_cases hx : x ∈ hg.choose_spec.choose_spec.choose a
        · simp only [Set.indicator'_of_mem hx]; norm_num
        · simp only [Set.indicator'_of_notMem hx]; norm_num
    rw [EReal.coe_finset_sum h_nonneg]
    apply Finset.sum_le_sum
    intro i _
    by_cases hx : x ∈ hg.choose_spec.choose_spec.choose i
    · simp only [Set.indicator'_of_mem hx, EReal.indicator, Real.EReal_fun, EReal.coe_one, mul_one]
      have hci_ne_top : hg.choose_spec.choose i ≠ ⊤ := hcoeff_finite i hx
      have hci_ne_bot : hg.choose_spec.choose i ≠ ⊥ := EReal.ne_bot_of_nonneg (hE i).2
      rw [EReal.coe_toReal hci_ne_top hci_ne_bot]
    · simp only [Set.indicator'_of_notMem hx, EReal.indicator, Real.EReal_fun, EReal.coe_zero, mul_zero, le_refl]

/-- toRealFun of unsigned simple function is non-negative -/
lemma UnsignedSimpleFunction.toRealFun_nonneg {d:ℕ}
    {g: EuclideanSpace' d → EReal} (hg : UnsignedSimpleFunction g)
    (x : EuclideanSpace' d) : 0 ≤ hg.toRealFun x := by
  unfold UnsignedSimpleFunction.toRealFun
  have hE := hg.choose_spec.choose_spec.choose_spec.1
  apply Finset.sum_nonneg
  intro i _
  apply mul_nonneg
  · exact EReal.toReal_nonneg (hE i).2
  · by_cases hx : x ∈ hg.choose_spec.choose_spec.choose i
    · simp only [Set.indicator'_of_mem hx]; norm_num
    · simp only [Set.indicator'_of_notMem hx]; norm_num

/-- toReal preserves order when values are finite -/
lemma UnsignedSimpleFunction.toRealFun_le {d:ℕ}
    {g: EuclideanSpace' d → EReal} (hg : UnsignedSimpleFunction g)
    {f: EuclideanSpace' d → ℝ} (hle : ∀ x, g x ≤ EReal.pos_fun f x)
    (x : EuclideanSpace' d) : hg.toRealFun x ≤ max (f x) 0 := by
  have h1 : (hg.toRealFun x : EReal) ≤ g x := hg.coe_toRealFun_le x
  have h2 : g x ≤ (max (f x) 0 : EReal) := by
    simp only [EReal.pos_fun] at hle
    exact hle x
  have h3 : (hg.toRealFun x : EReal) ≤ (max (f x) 0 : EReal) := le_trans h1 h2
  exact EReal.coe_le_coe_iff.mp h3

/-- The main approximation lemma for unsigned functions bounded by a real function.
    If g_E ≤ f⁺ and ∫f⁺ - ε ≤ ∫g_E, then ∫(f⁺ - g_R) ≤ ε where g_R = toRealFun g_E -/
lemma approx_unsigned_by_real {d:ℕ} {f: EuclideanSpace' d → ℝ}
    (hf_pos : UnsignedAbsolutelyIntegrable (EReal.pos_fun f))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (g : EuclideanSpace' d → ℝ), RealSimpleFunction g ∧
      (∀ x, 0 ≤ g x) ∧ (∀ x, g x ≤ max (f x) 0) ∧
      UnsignedLebesgueIntegral (fun x => (max (f x) 0 - g x : EReal)) ≤ ε := by
  obtain ⟨g_E, hg_E_simple, hg_E_le, hg_E_approx⟩ :=
    UnsignedAbsolutelyIntegrable.approx_by_simple_le hf_pos ε hε
  use hg_E_simple.toRealFun
  constructor
  · exact hg_E_simple.toRealFun_isSimple
  constructor
  · intro x
    exact hg_E_simple.toRealFun_nonneg x
  constructor
  · intro x
    exact hg_E_simple.toRealFun_le hg_E_le x
  · have h_eq : (fun x => (max (f x) 0 - hg_E_simple.toRealFun x : EReal)) =
                (fun x => EReal.pos_fun f x - g_E x) := by
      funext x
      simp only [EReal.pos_fun]
      rw [← hg_E_simple.coe_toRealFun_eq hg_E_le x]
    rw [h_eq]
    have h_posf_finite : UnsignedLebesgueIntegral (EReal.pos_fun f) < ⊤ := hf_pos.2
    have h_gE_le_posf : UnsignedLebesgueIntegral g_E ≤ UnsignedLebesgueIntegral (EReal.pos_fun f) := by
      apply LowerUnsignedLebesgueIntegral.mono hg_E_simple.unsignedMeasurable hf_pos.1
      exact AlmostAlways.ofAlways hg_E_le
    have h_gE_finite : UnsignedLebesgueIntegral g_E < ⊤ := lt_of_le_of_lt h_gE_le_posf h_posf_finite
    have h_int_posf_ne_top : UnsignedLebesgueIntegral (EReal.pos_fun f) ≠ ⊤ :=
      ne_top_of_lt h_posf_finite
    have h_int_gE_ne_top : UnsignedLebesgueIntegral g_E ≠ ⊤ := ne_top_of_lt h_gE_finite
    have h_int_posf_nonneg : 0 ≤ UnsignedLebesgueIntegral (EReal.pos_fun f) :=
      UnsignedLebesgueIntegral.nonneg hf_pos.1
    have h_int_gE_nonneg : 0 ≤ UnsignedLebesgueIntegral g_E :=
      UnsignedLebesgueIntegral.nonneg hg_E_simple.unsignedMeasurable
    have h_int_posf_ne_bot : UnsignedLebesgueIntegral (EReal.pos_fun f) ≠ ⊥ :=
      EReal.ne_bot_of_nonneg h_int_posf_nonneg
    have h_int_gE_ne_bot : UnsignedLebesgueIntegral g_E ≠ ⊥ :=
      EReal.ne_bot_of_nonneg h_int_gE_nonneg
    have h_bound : UnsignedLebesgueIntegral (EReal.pos_fun f) - UnsignedLebesgueIntegral g_E ≤ ε := by
      calc UnsignedLebesgueIntegral (EReal.pos_fun f) - UnsignedLebesgueIntegral g_E
          ≤ UnsignedLebesgueIntegral (EReal.pos_fun f) -
            (UnsignedLebesgueIntegral (EReal.pos_fun f) - ε) := by
              apply EReal.sub_le_sub_left' hg_E_approx
        _ = ε := EReal.sub_sub_cancel' h_int_posf_ne_top h_int_posf_ne_bot
    have h_decomp : EReal.pos_fun f = g_E + (fun x => EReal.pos_fun f x - g_E x) := by
      funext x
      have h_gE_finite_x : g_E x ≠ ⊤ := hg_E_simple.finite_of_le_pos_fun hg_E_le x
      have h_gE_nonneg_x : 0 ≤ g_E x := hg_E_simple.nonneg x
      have h_gE_ne_bot : g_E x ≠ ⊥ := EReal.ne_bot_of_nonneg h_gE_nonneg_x
      have h_posf_ne_top : EReal.pos_fun f x ≠ ⊤ := by
        simp only [EReal.pos_fun]
        exact EReal.coe_ne_top (max (f x) 0)
      have h_eq : g_E x + (EReal.pos_fun f x - g_E x) = EReal.pos_fun f x :=
        EReal.add_sub_cancel' (hg_E_le x) h_gE_ne_bot h_posf_ne_top
      exact h_eq.symm
    have h_meas_posf : UnsignedMeasurable (EReal.pos_fun f) := hf_pos.1
    have h_meas_gE : UnsignedMeasurable g_E := hg_E_simple.unsignedMeasurable
    let diff := fun x => EReal.pos_fun f x - g_E x
    have h_diff_nonneg : ∀ x, 0 ≤ diff x := by
      intro x
      simp only [diff]
      have h_le := hg_E_le x
      have h_posf_ne_top : EReal.pos_fun f x ≠ ⊤ := EReal.coe_ne_top (max (f x) 0)
      have h_gE_ne_bot : g_E x ≠ ⊥ := EReal.ne_bot_of_nonneg (hg_E_simple.nonneg x)
      rw [EReal.sub_nonneg (Or.inl h_posf_ne_top) (Or.inr h_gE_ne_bot)]
      exact h_le
    have h_int_eq : UnsignedLebesgueIntegral diff =
                    UnsignedLebesgueIntegral (EReal.pos_fun f) - UnsignedLebesgueIntegral g_E := by
      have h_meas_diff : UnsignedMeasurable diff := by
        have h_diff_unsigned : Unsigned diff := h_diff_nonneg
        have h_tfae := UnsignedMeasurable.TFAE h_diff_unsigned
        have h_iff : UnsignedMeasurable diff ↔ (∀ t, LebesgueMeasurable {x | diff x > t}) :=
          List.TFAE.out h_tfae 0 4
        apply h_iff.mpr
        intro t
        by_cases ht : t < 0
        · have h_full : {x | diff x > t} = Set.univ := by
            ext x
            simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
            exact lt_of_lt_of_le ht (h_diff_nonneg x)
          rw [h_full]
          have h_univ_meas : LebesgueMeasurable (Set.univ : Set (EuclideanSpace' d)) := by
            have h_compl : (Set.univ : Set (EuclideanSpace' d)) = (∅ : Set (EuclideanSpace' d))ᶜ := by
              ext; simp
            rw [h_compl]
            exact LebesgueMeasurable.complement LebesgueMeasurable.empty
          exact h_univ_meas
        · push_neg at ht
          have h_gE_meas : UnsignedMeasurable g_E := hg_E_simple.unsignedMeasurable
          have h_posf_meas : UnsignedMeasurable (EReal.pos_fun f) := h_meas_posf
          have h_posf_level : ∀ s, LebesgueMeasurable {x | EReal.pos_fun f x > s} := by
            have h_tfae_posf := UnsignedMeasurable.TFAE h_posf_meas.1
            exact (List.TFAE.out h_tfae_posf 0 4).mp h_posf_meas
          obtain ⟨k, c, E, hE, heq⟩ := hg_E_simple
          open UnsignedSimpleFunction.IntegralWellDef in
          have h_atom_meas : ∀ n : Fin (2^k), LebesgueMeasurable (singleAtom E n) :=
            fun n => RealSimpleFunction.DisjointRepr.singleAtom_measurable (fun i => (hE i).1) n
          let atomValueE : Fin (2^k) → EReal :=
            fun n => ∑ i : Fin k, if n.val.testBit i.val then c i else 0
          have h_gE_on_atom : ∀ n : Fin (2^k), ∀ x : EuclideanSpace' d,
              x ∈ singleAtom E n → g_E x = atomValueE n := by
            intro n x hx
            rw [heq]
            simp only [Finset.sum_apply, Pi.smul_apply, atomValueE]
            apply Finset.sum_congr rfl
            intro i _
            rw [mem_singleAtom_iff] at hx
            specialize hx i
            by_cases hbit : n.val.testBit i.val
            · simp only [hbit, ↓reduceIte]
              have hx_in : x ∈ E i := hx.mp hbit
              simp only [smul_eq_mul, EReal.indicator, Real.EReal_fun,
                         Set.indicator'_of_mem hx_in, EReal.coe_one, mul_one]
            · have hbit_false : n.val.testBit i.val = false := Bool.eq_false_iff.mpr hbit
              have hx_out : x ∉ E i := fun h => hbit (hx.mpr h)
              simp only [hbit_false, Bool.false_eq_true, ↓reduceIte, smul_eq_mul,
                         EReal.indicator, Real.EReal_fun, Set.indicator'_of_notMem hx_out,
                         EReal.coe_zero, mul_zero]
          have h_set_eq : {x | diff x > t} =
              ⋃ n : Fin (2^k), (singleAtom E n ∩ {x | EReal.pos_fun f x > atomValueE n + t}) := by
            ext x
            simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff, diff]
            have ⟨n, hn_mem, hn_unique⟩ := exists_unique_singleAtom E x
            constructor
            · intro h_diff_gt
              use n, hn_mem
              rw [h_gE_on_atom n x hn_mem] at h_diff_gt
              have h_atomVal_nonneg : atomValueE n ≥ 0 := by
                simp only [atomValueE, ge_iff_le]
                apply Finset.sum_nonneg
                intro i _
                split_ifs with h
                · exact (hE i).2
                · rfl
              have h_atomVal_ne_bot : atomValueE n ≠ ⊥ := ne_bot_of_le_ne_bot (by simp) h_atomVal_nonneg
              have h_t_ne_bot : t ≠ ⊥ := ne_bot_of_le_ne_bot (by simp) ht
              rw [add_comm]
              exact (EReal.lt_sub_iff_add_lt (Or.inl h_atomVal_ne_bot) (Or.inr h_t_ne_bot)).mp h_diff_gt
            · intro ⟨m, hm_mem, hm_posf⟩
              have hm_eq_n : m = n := hn_unique m hm_mem
              rw [hm_eq_n] at hm_posf
              rw [h_gE_on_atom n x hn_mem]
              have h_atomVal_nonneg : atomValueE n ≥ 0 := by
                simp only [atomValueE, ge_iff_le]
                apply Finset.sum_nonneg
                intro i _
                split_ifs with h
                · exact (hE i).2
                · rfl
              have h_atomVal_ne_bot : atomValueE n ≠ ⊥ := ne_bot_of_le_ne_bot (by simp) h_atomVal_nonneg
              have h_t_ne_bot : t ≠ ⊥ := ne_bot_of_le_ne_bot (by simp) ht
              rw [add_comm] at hm_posf
              exact (EReal.lt_sub_iff_add_lt (Or.inl h_atomVal_ne_bot) (Or.inr h_t_ne_bot)).mpr hm_posf
          rw [h_set_eq]
          apply LebesgueMeasurable.finite_union
          intro n
          exact LebesgueMeasurable.inter (h_atom_meas n) (h_posf_level (atomValueE n + t))
      have h_add_eq : UnsignedLebesgueIntegral (EReal.pos_fun f) =
                      UnsignedLebesgueIntegral g_E + UnsignedLebesgueIntegral diff := by
        simp only [UnsignedLebesgueIntegral]
        rw [h_decomp]
        exact LowerUnsignedLebesgueIntegral.add h_meas_gE h_meas_diff (by rw [← h_decomp]; exact h_meas_posf)
      have h1 : UnsignedLebesgueIntegral g_E + UnsignedLebesgueIntegral diff =
                UnsignedLebesgueIntegral (EReal.pos_fun f) := h_add_eq.symm
      symm
      calc UnsignedLebesgueIntegral (EReal.pos_fun f) - UnsignedLebesgueIntegral g_E
          = (UnsignedLebesgueIntegral g_E + UnsignedLebesgueIntegral diff) - UnsignedLebesgueIntegral g_E := by
              rw [h_add_eq]
        _ = UnsignedLebesgueIntegral diff := by
              have h_gE_real : UnsignedLebesgueIntegral g_E =
                              (UnsignedLebesgueIntegral g_E).toReal := by
                exact (EReal.coe_toReal h_int_gE_ne_top h_int_gE_ne_bot).symm
              rw [h_gE_real]
              exact EReal.add_sub_cancel_left
    calc UnsignedLebesgueIntegral (fun x => EReal.pos_fun f x - g_E x)
        = UnsignedLebesgueIntegral diff := rfl
      _ = UnsignedLebesgueIntegral (EReal.pos_fun f) - UnsignedLebesgueIntegral g_E := h_int_eq
      _ ≤ ε := h_bound

/-! ### Main approximation theorems -/

/-- Theorem 1.3.20(i) Approximation of $L^1$ functions by simple functions -/
theorem ComplexAbsolutelyIntegrable.approx_by_simple {d:ℕ} {f: EuclideanSpace' d → ℂ} (hf : ComplexAbsolutelyIntegrable f)
  (ε : ℝ) (hε : 0 < ε) :
  ∃ (g : EuclideanSpace' d → ℂ), ComplexSimpleFunction g ∧ ComplexAbsolutelyIntegrable g ∧
    PreL1.norm (f - g) ≤ ε := by
  -- Strategy: Use RealAbsolutelyIntegrable.approx_by_simple on Re(f) and Im(f)
  -- 1. hf.re : RealAbsolutelyIntegrable (Complex.re_fun f)
  -- 2. hf.im : RealAbsolutelyIntegrable (Complex.im_fun f)
  -- 3. Apply approx_by_simple to each with ε/2
  -- 4. Construct complex simple g = g_re + i * g_im
  -- 5. Show PreL1.norm (f - g) ≤ ε using |z| ≤ |Re z| + |Im z|
  sorry

theorem RealAbsolutelyIntegrable.approx_by_simple {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf : RealAbsolutelyIntegrable f)
  (ε : ℝ) (hε : 0 < ε) :
  ∃ (g : EuclideanSpace' d → ℝ), RealSimpleFunction g ∧ RealAbsolutelyIntegrable g ∧
    PreL1.norm (f - g) ≤ ε := by
  -- Strategy: Split f = f⁺ - f⁻, approximate each unsigned part, combine
  -- 1. hf.pos : UnsignedAbsolutelyIntegrable (EReal.pos_fun f)
  -- 2. hf.neg : UnsignedAbsolutelyIntegrable (EReal.neg_fun f)
  -- 3. Use approx_by_simple_le on f⁺ and f⁻ with ε/2 to get EReal simple g⁺, g⁻
  -- 4. Convert g⁺, g⁻ to Real (they have finite values since bounded by integrable f⁺, f⁻)
  -- 5. Construct g = g⁺ - g⁻ as a RealSimpleFunction
  -- 6. Show PreL1.norm (f - g) ≤ ε using monotonicity and triangle inequality
  sorry

def ComplexStepFunction {d:ℕ} (f: EuclideanSpace' d → ℂ) : Prop :=
  ∃ (S: Finset (Box d)) (c: S → ℂ), f = ∑ B, (c B • Complex.indicator (B.val.toSet))

def RealStepFunction {d:ℕ} (f: EuclideanSpace' d → ℝ) : Prop :=
  ∃ (S: Finset (Box d)) (c: S → ℝ), f = ∑ B, (c B • (B.val.toSet).indicator')

/-- Theorem 1.3.20(ii) Approximation of $L^1$ functions by step functions -/
theorem ComplexAbsolutelyIntegrable.approx_by_step {d:ℕ} {f: EuclideanSpace' d → ℂ} (hf : ComplexAbsolutelyIntegrable f)
  (ε : ℝ) (hε : 0 < ε) :
  ∃ (g : EuclideanSpace' d → ℂ), ComplexStepFunction g ∧ ComplexAbsolutelyIntegrable g ∧
    PreL1.norm (f - g) ≤ ε := by sorry

theorem RealAbsolutelyIntegrable.approx_by_step {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf : RealAbsolutelyIntegrable f)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (g : EuclideanSpace' d → ℝ), RealStepFunction g ∧ RealAbsolutelyIntegrable g ∧
        PreL1.norm (f - g) ≤ ε := by sorry

def CompactlySupported {X Y:Type*} [TopologicalSpace X] [Zero Y] (f: X → Y) : Prop :=
  ∃ (K: Set X), IsCompact K ∧ ∀ x, x ∉ K → f x = 0

/-- Theorem 1.3.20(iii) Approximation of $L^1$ functions by continuous compactly supported functions -/
theorem ComplexAbsolutelyIntegrable.approx_by_continuous_compact {d:ℕ} {f: EuclideanSpace' d → ℂ} (hf : ComplexAbsolutelyIntegrable f)
  (ε : ℝ) (hε : 0 < ε) :
  ∃ (g : EuclideanSpace' d → ℂ), Continuous g ∧ CompactlySupported g ∧
    PreL1.norm (f - g) ≤ ε := by sorry

theorem RealAbsolutelyIntegrable.approx_by_continuous_compact {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf : RealAbsolutelyIntegrable f)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (g : EuclideanSpace' d → ℝ), Continuous g ∧ CompactlySupported g ∧
        PreL1.norm (f - g) ≤ ε := by sorry

def UniformlyConvergesTo {X Y:Type*} [PseudoMetricSpace Y] (f: ℕ → X → Y) (g: X → Y) : Prop := ∀ ε>0, ∃ N, ∀ n ≥ N, ∀ x, dist (f n x) (g x) ≤ ε

def UniformlyConvergesToOn {X Y:Type*} [PseudoMetricSpace Y] (f: ℕ → X → Y) (g: X → Y) (S: Set X): Prop := UniformlyConvergesTo (fun n (x:S) ↦ f n x.val) (fun x ↦ g x.val)

/-- Definition 1.3.21 (Locally uniform convergence) -/
def LocallyUniformlyConvergesTo {X Y:Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y] (f: ℕ → X → Y) (g: X → Y) : Prop :=
  ∀ (K: Set X), Bornology.IsBounded K → UniformlyConvergesToOn f g K

/-- Remark 1.3.22 -/
theorem LocallyUniformlyConvergesTo.iff {d:ℕ} {Y:Type*} [PseudoMetricSpace Y] (f: ℕ → EuclideanSpace' d → Y) (g: EuclideanSpace' d → Y) :
  LocallyUniformlyConvergesTo f g ↔
  ∀ x₀, ∃ U: Set (EuclideanSpace' d), x₀ ∈ U ∧ IsOpen U → UniformlyConvergesToOn f g U := by sorry

def LocallyUniformlyConvergesToOn {X Y:Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y] (f: ℕ → X → Y) (g: X → Y) (S: Set X): Prop :=
  LocallyUniformlyConvergesTo (fun n (x:S) ↦ f n x.val) (fun x ↦ g x.val)

/-- Example 1.3.23 -/
example : LocallyUniformlyConvergesTo (fun n (x:EuclideanSpace' 1) ↦ x.toReal / n) (fun x ↦ 0) := by sorry

example : ¬ UniformlyConvergesTo (fun n (x:EuclideanSpace' 1) ↦ x.toReal / n) (fun x ↦ 0) := by sorry

/-- Example 1.3.24 -/
example : LocallyUniformlyConvergesTo (fun N (x:EuclideanSpace' 1) ↦ ∑ n ∈ Finset.range N, x.toReal^n / n.factorial) (fun x ↦ x.toReal.exp) := by sorry

example : PointwiseConvergesTo (fun N (x:EuclideanSpace' 1) ↦ ∑ n ∈ Finset.range N, x.toReal^n / n.factorial) (fun x ↦ x.toReal.exp) := by sorry

example : ¬ UniformlyConvergesTo (fun N (x:EuclideanSpace' 1) ↦ ∑ n ∈ Finset.range N, x.toReal^n / n.factorial) (fun x ↦ x.toReal.exp) := by sorry

/-- Example 1.3.25 -/
example : PointwiseConvergesTo (fun n (x:EuclideanSpace' 1) ↦ if x.toReal > 0 then 1 / (n * x.toReal) else 0) (fun x ↦ 0) := by sorry

example : ¬ LocallyUniformlyConvergesTo (fun n (x:EuclideanSpace' 1) ↦ if x.toReal > 0 then 1 / (n * x.toReal) else 0) (fun x ↦ 0) := by sorry

/-- Theorem 1.3.26 (Egorov's theorem)-/
theorem PointwiseAeConvergesTo.locallyUniformlyConverges_outside_small {d:ℕ} {f : ℕ → EuclideanSpace' d → ℂ} {g : EuclideanSpace' d → ℂ}
  (hf: ∀ n, ComplexMeasurable (f n))
  (hfg: PointwiseAeConvergesTo f g)
  (ε : ℝ) (hε : 0 < ε) :
  ∃ (E: Set (EuclideanSpace' d)), MeasurableSet E ∧
    Lebesgue_measure E ≤ ε ∧
    LocallyUniformlyConvergesToOn f g Eᶜ := by sorry

/-- The exceptional set in Egorov's theorem cannot be taken to be null -/
example : ∃ (d:ℕ) (f : ℕ → EuclideanSpace' d → ℝ) (g : EuclideanSpace' d → ℝ),
    (∀ n, RealMeasurable (f n)) ∧
    PointwiseAeConvergesTo f g ∧
    ∀ (E: Set (EuclideanSpace' d)), MeasurableSet E ∧
      Lebesgue_measure E = 0 →
      ¬ LocallyUniformlyConvergesToOn f g Eᶜ := by sorry

/-- Remark 1.3.27: Local uniform convergence in Egorov's theorem cannot be upgraded to uniform convergence -/
example : ∃ (d:ℕ) (f : ℕ → EuclideanSpace' d → ℝ) (g : EuclideanSpace' d → ℝ),
    (∀ n, RealMeasurable (f n)) ∧
    PointwiseAeConvergesTo f g ∧
    ∃ (ε : ℝ) (hε : 0 < ε),
      ∀ (E: Set (EuclideanSpace' d)), MeasurableSet E ∧
        Lebesgue_measure E ≤ ε →
        ¬ UniformlyConvergesToOn f g Eᶜ := by sorry

/-- But uniform convergence can be recovered on a fixed set of finite measure -/
theorem PointwiseAeConvergesTo.uniformlyConverges_outside_small {d:ℕ} {f : ℕ → EuclideanSpace' d → ℂ} {g : EuclideanSpace' d → ℂ}
  (hf: ∀ n, ComplexMeasurable (f n))
  (hfg: PointwiseAeConvergesTo f g)
  (S: Set (EuclideanSpace' d))
  (hS: Lebesgue_measure S < ⊤)
  (ε : ℝ) (hε : 0 < ε) :
  ∃ (E: Set (EuclideanSpace' d)), MeasurableSet E ∧
    Lebesgue_measure E ≤ ε ∧
    UniformlyConvergesToOn f g (Sᶜ ∪ E) := by sorry

/-- Theorem 1.3.28 (Lusin's theorem) -/
theorem ComplexAbsolutelyIntegrable.approx_by_continuous_outside_small {d:ℕ} {f : EuclideanSpace' d → ℂ}
  (hf: ComplexAbsolutelyIntegrable f)
  (ε : ℝ) (hε : 0 < ε) :
  ∃ (g : EuclideanSpace' d → ℂ) (E: Set (EuclideanSpace' d)), ContinuousOn g Eᶜ ∧ MeasurableSet E ∧
      Lebesgue_measure E ≤ ε ∧
      ∀ x ∉ E, g x = f x := by sorry

/-- Lusin's theorem does not make the original function continuous outside of E -/
example : ∃ (d:ℕ) (f : EuclideanSpace' d → ℝ),
    RealMeasurable f ∧
    ∀ (E: Set (EuclideanSpace' d)), MeasurableSet E → Lebesgue_measure E ≤ 1 → ¬ ContinuousOn f Eᶜ := by sorry

def LocallyComplexAbsolutelyIntegrable {d:ℕ} (f: EuclideanSpace' d → ℂ) : Prop :=
  ∀ (S: Set (EuclideanSpace' d)), MeasurableSet S ∧ Bornology.IsBounded S → ComplexAbsolutelyIntegrableOn f S

/-- Exercise 1.3.23 (Lusin's theorem only requires local absolute integrability )-/
theorem LocallyComplexAbsolutelyIntegrable.approx_by_continuous_outside_small {d:ℕ} {f : EuclideanSpace' d → ℂ}
  (hf: LocallyComplexAbsolutelyIntegrable f)
  (ε : ℝ) (hε : 0 < ε) :
  ∃ (g : EuclideanSpace' d → ℂ) (E: Set (EuclideanSpace' d)), ContinuousOn g Eᶜ ∧ MeasurableSet E ∧
      Lebesgue_measure E ≤ ε ∧
      ∀ x ∉ E, g x = f x := by sorry

theorem ComplexMeasurable.approx_by_continuous_outside_small {d:ℕ} {f : EuclideanSpace' d → ℂ}
  (hf: ComplexMeasurable f)
  (ε : ℝ) (hε : 0 < ε) :
  ∃ (g : EuclideanSpace' d → ℂ) (E: Set (EuclideanSpace' d)), ContinuousOn g Eᶜ ∧ MeasurableSet E ∧
      Lebesgue_measure E ≤ ε ∧
      ∀ x ∉ E, g x = f x := by sorry

/-- Exercise 1.3.24 -/
theorem ComplexMeasurable.iff_pointwiseae_of_continuous {d:ℕ} {f : EuclideanSpace' d → ℂ} :
  ComplexMeasurable f ↔
  ∃ (g : ℕ → EuclideanSpace' d → ℂ), (∀ n, Continuous (g n)) ∧ PointwiseAeConvergesTo g f := by sorry

/-- Remark 1.3.29 -/
theorem UnsignedMeasurable.approx_by_continuous_outside_small {d:ℕ} {f : EuclideanSpace' d → EReal}
  (hf: UnsignedMeasurable f) (hfin: AlmostAlways (fun x ↦ f x < ⊤))
  (ε : ℝ) (hε : 0 < ε) :
  ∃ (g : EuclideanSpace' d → ℝ) (E: Set (EuclideanSpace' d)), ContinuousOn g Eᶜ ∧ MeasurableSet E ∧
      Lebesgue_measure E ≤ ε ∧
      ∀ x ∉ E, g x = f x := by sorry

/-- Exercise 1.3.25 (a) (Littlewood-like principle) -/
theorem ComplexAbsolutelyIntegrable.almost_bounded_support {d:ℕ} {f : EuclideanSpace' d → ℂ}
  (hf: ComplexAbsolutelyIntegrable f)
  (ε : ℝ) (hε : 0 < ε) :
  ∃ (R: ℝ), PreL1.norm (f * Complex.indicator (Metric.ball 0 R)ᶜ) ≤ ε := by sorry

def BoundedOn {X Y:Type*} [PseudoMetricSpace Y] (f: X → Y) (S: Set X) : Prop := Bornology.IsBounded (f '' S)

/-- Exercise 1.3.25 (b) (Littlewood-like principle) -/
theorem ComplexAbsolutelyIntegrable.almost_bounded {d:ℕ} {f : EuclideanSpace' d → ℂ}
  (hf: ComplexAbsolutelyIntegrable f)
  (ε : ℝ) (hε : 0 < ε) :
  ∃ (E: Set (EuclideanSpace' d)), MeasurableSet E ∧
    Lebesgue_measure E ≤ ε ∧
    BoundedOn f Eᶜ := by sorry
