import TokenAuctions.Defs

set_option maxHeartbeats 4000000

/-!
# Robust Token Auctions: Partial Preferences & Revelation Principle

This module formalizes Section 4 (Definitions 4.1–4.4, Theorem 4.5, Lemma 4.6, Lemma 4.7) and
Appendix C (Lemma C.1, Remark C.2) of *Mechanism Design for Large Language Models: Token Auctions
with Proxy Bidders*.

## Main Results
- `sec_4_multiUtility_closed_preorder`: Multi-utility preferences `⪰_V` induced by continuous
  valuation functions form a topologically closed preorder on `Δ(T)` (Section 4).
- `def_4_1_equal_outcome_equal_payment`: Under payment monotonicity and reflexive preferences,
  bids inducing identical outcomes incur identical expected payments (Definition 4.1).
- `lem_C_1_debreu_countable_utility`: Every complete, transitive preference relation on a countable
  set `X` admits a strictly positive rational utility representation `f : X → ℚ₊` (Lemma C.1).
- `rem_C_2_lexicographic_no_utility`: The lexicographic order on `ℝ × ℝ` is a complete antisymmetric
  transitive order that admits no real-valued utility representation (Remark C.2).
- `lem_4_6_payment_monotone_iff_total_order`: Existence of an admissible payment-monotone payment
  rule is equivalent to total comparability on achievable menus `Q_i(b_{-i}, p)` with the zero-bid
  outcome weakly least (Lemma 4.6).
- `lem_4_7_consistent_realignment`: Any consistent aggregation rule generating totally ordered menus
  with `0` weakly least can be realigned via strategy maps `π_i : ℚ₊ → ℚ₊` into a monotone
  aggregation rule `q̃` (Lemma 4.7).
- `thm_4_5_revelation_principle`: Revelation principle for robust token auctions — every
  payment-monotone, consistent mechanism `𝓜 = ⟨q, z⟩` is strategically and deviation-equivalent to
  a monotone, payment-monotone, admissible mechanism `𝓜̃ = ⟨q̃, z̃⟩` (Theorem 4.5).
-/

namespace TokenAuctions

open scoped BigOperators
open Classical MeasureTheory

noncomputable section

/-- Lexicographic weak order on `ℝ × ℝ` from Remark C.2 (`appendix:proof-mono`). -/
def lexPlaneLE (x y : ℝ × ℝ) : Prop :=
  x.1 < y.1 ∨ (x.1 = y.1 ∧ x.2 ≤ y.2)

/-! ## Internal Order-Separation & Back-and-Forth Helpers -/

private def gapBid (L U : Finset Bid) : Bid :=
  if hL : L.Nonempty then
    if hU : U.Nonempty then (L.max' hL + U.min' hU) / 2
    else L.max' hL + 1
  else
    if hU : U.Nonempty then U.min' hU / 2
    else 1

private lemma gapBid_spec (L U : Finset Bid)
    (hU_pos : ∀ u ∈ U, 0 < u)
    (hLU : ∀ l ∈ L, ∀ u ∈ U, l < u) :
    0 < gapBid L U ∧ (∀ l ∈ L, l < gapBid L U) ∧ (∀ u ∈ U, gapBid L U < u) := by
  dsimp only [gapBid]
  split_ifs with hL hU hU'
  · have ha_mem : L.max' hL ∈ L := Finset.max'_mem L hL
    have hb_mem : U.min' hU ∈ U := Finset.min'_mem U hU
    have hab : L.max' hL < U.min' hU := hLU _ ha_mem _ hb_mem
    have hb_pos : 0 < U.min' hU := hU_pos _ hb_mem
    have ha_nonneg : (0 : ℚ) ≤ (L.max' hL : ℚ) := by positivity
    have hab_q : (L.max' hL : ℚ) < (U.min' hU : ℚ) := by exact_mod_cast hab
    have hb_pos_q : (0 : ℚ) < (U.min' hU : ℚ) := by exact_mod_cast hb_pos
    refine ⟨?_, ?_, ?_⟩
    · rw [← NNRat.cast_lt (K := ℚ)]; push_cast; linarith
    · intro l hl
      have hle : (l : ℚ) ≤ (L.max' hL : ℚ) := by exact_mod_cast Finset.le_max' L l hl
      rw [← NNRat.cast_lt (K := ℚ)]; push_cast; linarith
    · intro u hu
      have hle : (U.min' hU : ℚ) ≤ (u : ℚ) := by exact_mod_cast Finset.min'_le U u hu
      rw [← NNRat.cast_lt (K := ℚ)]; push_cast; linarith
  · have ha_nonneg : (0 : ℚ) ≤ (L.max' hL : ℚ) := by positivity
    refine ⟨?_, ?_, ?_⟩
    · rw [← NNRat.cast_lt (K := ℚ)]; push_cast; linarith
    · intro l hl
      have hle : (l : ℚ) ≤ (L.max' hL : ℚ) := by exact_mod_cast Finset.le_max' L l hl
      rw [← NNRat.cast_lt (K := ℚ)]; push_cast; linarith
    · intro u hu; exact False.elim (hU ⟨u, hu⟩)
  · have hb_mem : U.min' hU' ∈ U := Finset.min'_mem U hU'
    have hb_pos : (0 : ℚ) < (U.min' hU' : ℚ) := by exact_mod_cast hU_pos _ hb_mem
    refine ⟨?_, ?_, ?_⟩
    · rw [← NNRat.cast_lt (K := ℚ)]; push_cast; linarith
    · intro l hl; exact False.elim (hL ⟨l, hl⟩)
    · intro u hu
      have hle : (U.min' hU' : ℚ) ≤ (u : ℚ) := by exact_mod_cast Finset.min'_le U u hu
      rw [← NNRat.cast_lt (K := ℚ)]; push_cast; linarith
  · refine ⟨zero_lt_one, ?_, ?_⟩
    · intro l hl; exact False.elim (hL ⟨l, hl⟩)
    · intro u hu; exact False.elim (hU' ⟨u, hu⟩)

private lemma countable_bid : Countable Bid := NNRat.coe_injective.countable

/-! ## Section 4 Basic Structural Properties -/

/-- Section 4: Multi-utility preference relation `multiUtilityPref V` induced by a family `V` of
    continuous valuation functions is reflexive, transitive, and topologically closed. -/
theorem sec_4_multiUtility_closed_preorder (T : Type) [Fintype T] [DecidableEq T]
    (V : Set (TokenDist T → ℝ)) (hcont : ∀ v ∈ V, Continuous v) :
    (∀ q : TokenDist T, multiUtilityPref V q q) ∧
    (∀ q₁ q₂ q₃ : TokenDist T,
      multiUtilityPref V q₁ q₂ → multiUtilityPref V q₂ q₃ → multiUtilityPref V q₁ q₃) ∧
    IsClosed {pair : TokenDist T × TokenDist T | multiUtilityPref V pair.1 pair.2} := by
  refine ⟨fun q v _ => le_rfl, fun q₁ q₂ q₃ h₁₂ h₂₃ v hv => le_trans (h₂₃ v hv) (h₁₂ v hv), ?_⟩
  have hset : {pair : TokenDist T × TokenDist T | multiUtilityPref V pair.1 pair.2} =
      ⋂ v ∈ V, {pair : TokenDist T × TokenDist T | v pair.2 ≤ v pair.1} := by
    ext pair
    simp [multiUtilityPref]
  rw [hset]
  exact isClosed_biInter (fun v hv =>
    isClosed_le ((hcont v hv).comp continuous_snd) ((hcont v hv).comp continuous_fst))

/-- Definition 4.1 consequence: Under reflexive preferences and payment monotonicity, two bids that
    produce identical output distributions must incur equal expected payments. -/
theorem def_4_1_equal_outcome_equal_payment (n : ℕ) (T : Type) [Fintype T] [DecidableEq T]
    (pref : AgentPrefs n T) (M : TokenMechanism n T)
    (hpre : IsPreorderPrefs pref) (hmono : IsPaymentMonotone pref M)
    (i : Fin n) (p : DistProfile n T) (bOthers : OpposingBids n i) (b_i b'_i : Bid)
    (hq : M.q (joinBid i b_i bOthers) p = M.q (joinBid i b'_i bOthers) p) :
    M.z i (joinBid i b_i bOthers) p = M.z i (joinBid i b'_i bOthers) p := by
  have hrefl := (hpre i p).1
  have h1 : M.z i (joinBid i b'_i bOthers) p ≤ M.z i (joinBid i b_i bOthers) p := by
    apply (hmono i p bOthers b_i b'_i).mpr
    rw [hq]; exact hrefl _
  have h2 : M.z i (joinBid i b_i bOthers) p ≤ M.z i (joinBid i b'_i bOthers) p := by
    apply (hmono i p bOthers b'_i b_i).mpr
    rw [hq]; exact hrefl _
  exact le_antisymm h2 h1

/-! ## Appendix C: Countable Rational Utility Representation & Uncountable Counterexample -/

/-- Lemma C.1 (`lemma:debreu`): Let `X` be a countable type equipped with a complete, transitive
    relation `r`. Then there exists a strictly positive rational utility function `f : X → ℚ₊`
    such that `r x y ↔ f x ≤ f y` for all `x, y ∈ X`. -/
theorem lem_C_1_debreu_countable_utility (X : Type) [Countable X] (r : X → X → Prop)
    (htot : ∀ x y : X, r x y ∨ r y x)
    (htrans : ∀ x y z : X, r x y → r y z → r x z) :
    ∃ f : X → Bid, (∀ x : X, 0 < f x) ∧ (∀ x y : X, r x y ↔ f x ≤ f y) := by
  obtain ⟨enc, henc⟩ := Countable.exists_injective_nat X
  have hrefl : ∀ x : X, r x x := fun x => (htot x x).elim id id
  let stepVal : (ℕ → Bid) → ℕ → Bid := fun g k =>
    if hx : ∃ x : X, enc x = k then
      let x₀ := Classical.choose hx
      let I := (Finset.range k).filter (fun m => ∃ y : X, enc y = m ∧ r x₀ y ∧ r y x₀)
      if hI : I.Nonempty then
        g (I.min' hI)
      else
        let L := ((Finset.range k).filter (fun m => ∃ y : X, enc y = m ∧ r y x₀ ∧ ¬ r x₀ y)).image g
        let U := ((Finset.range k).filter (fun m => ∃ y : X, enc y = m ∧ r x₀ y ∧ ¬ r y x₀)).image g
        gapBid L U
    else 1
  let G : ℕ → ℕ → Bid := fun k =>
    Nat.rec (fun _ => 1) (fun j gj m => if m = j then stepVal gj j else gj m) k
  have hG_step : ∀ k m, G (k + 1) m = if m = k then stepVal (G k) k else G k m :=
    fun _ _ => rfl
  have hG_lt : ∀ {m k k'}, m < k → k ≤ k' → G k' m = G k m := by
    intro m k k' hmk hkk'
    induction k' with
    | zero => omega
    | succ j ih =>
      rcases Nat.eq_or_lt_of_le hkk' with rfl | hlt
      · rfl
      · have hmj : m ≠ j := by omega
        rw [hG_step, if_neg hmj, ih (Nat.le_of_lt_succ hlt)]
  have hG_inv : ∀ k : ℕ,
      (∀ m < k, 0 < G k m) ∧
      (∀ x y : X, enc x < k → enc y < k → (r x y ↔ G k (enc x) ≤ G k (enc y))) := by
    intro k
    induction k with
    | zero =>
      exact ⟨fun m hm => by omega, fun x y hx _ => by omega⟩
    | succ k ih =>
      rcases ih with ⟨ih_pos, ih_ord⟩
      have hv_pos : 0 < stepVal (G k) k := by
        dsimp only [stepVal]
        split_ifs with hx hI
        · have hm_mem : _ ∈ Finset.range k := (Finset.mem_filter.mp (Finset.min'_mem _ hI)).1
          exact ih_pos _ (Finset.mem_range.mp hm_mem)
        · apply (gapBid_spec _ _ ?_ ?_).1
          · intro u hu
            rcases Finset.mem_image.mp hu with ⟨m, hm, rfl⟩
            exact ih_pos m (Finset.mem_range.mp (Finset.mem_filter.mp hm).1)
          · intro l hl u hu
            rcases Finset.mem_image.mp hl with ⟨m₁, hm₁, rfl⟩
            rcases Finset.mem_image.mp hu with ⟨m₂, hm₂, rfl⟩
            rcases (Finset.mem_filter.mp hm₁) with ⟨hm₁_lt, y₁, rfl, _, hy₁_not⟩
            rcases (Finset.mem_filter.mp hm₂) with ⟨hm₂_lt, y₂, rfl, hy₂_ge, _⟩
            have hnot : ¬ r y₂ y₁ := fun h => hy₁_not (htrans _ _ _ hy₂_ge h)
            exact lt_of_not_ge (fun hle =>
              hnot ((ih_ord y₂ y₁ (Finset.mem_range.mp hm₂_lt) (Finset.mem_range.mp hm₁_lt)).mpr hle))
        · exact zero_lt_one
      have h_pos_succ : ∀ m < k + 1, 0 < G (k + 1) m := by
        intro m hm
        rw [hG_step]
        split_ifs with hmk
        · exact hv_pos
        · exact ih_pos m (by omega)
      have h_cmp : ∀ (hx : ∃ z : X, enc z = k) (y : X), enc y < k →
          (r (Classical.choose hx) y ↔ stepVal (G k) k ≤ G k (enc y)) ∧
          (r y (Classical.choose hx) ↔ G k (enc y) ≤ stepVal (G k) k) := by
        intro hx y hy
        set x₀ := Classical.choose hx
        have hv_eq : stepVal (G k) k =
            (let I := (Finset.range k).filter (fun m => ∃ y' : X, enc y' = m ∧ r x₀ y' ∧ r y' x₀)
             if hI : I.Nonempty then G k (I.min' hI)
             else
               let L := ((Finset.range k).filter (fun m => ∃ y' : X, enc y' = m ∧ r y' x₀ ∧ ¬ r x₀ y')).image (G k)
               let U := ((Finset.range k).filter (fun m => ∃ y' : X, enc y' = m ∧ r x₀ y' ∧ ¬ r y' x₀)).image (G k)
               gapBid L U) := dif_pos hx
        rw [hv_eq]
        dsimp only []
        split_ifs with hI
        · have hm₀ := Finset.mem_filter.mp (Finset.min'_mem _ hI)
          rcases hm₀ with ⟨hm₀_lt, y₀, hy₀_enc, hx₀y₀, hy₀x₀⟩
          rw [← hy₀_enc] at hm₀_lt ⊢
          have hy₀_lt : enc y₀ < k := Finset.mem_range.mp hm₀_lt
          constructor
          · calc r x₀ y ↔ r y₀ y := ⟨htrans _ _ _ hy₀x₀, htrans _ _ _ hx₀y₀⟩
              _ ↔ G k (enc y₀) ≤ G k (enc y) := ih_ord y₀ y hy₀_lt hy
          · calc r y x₀ ↔ r y y₀ := ⟨fun h => htrans _ _ _ h hx₀y₀, fun h => htrans _ _ _ h hy₀x₀⟩
              _ ↔ G k (enc y) ≤ G k (enc y₀) := ih_ord y y₀ hy hy₀_lt
        · set L := ((Finset.range k).filter (fun m => ∃ y' : X, enc y' = m ∧ r y' x₀ ∧ ¬ r x₀ y')).image (G k)
          set U := ((Finset.range k).filter (fun m => ∃ y' : X, enc y' = m ∧ r x₀ y' ∧ ¬ r y' x₀)).image (G k)
          have hgap := gapBid_spec L U
            (by
              intro u hu
              rcases Finset.mem_image.mp hu with ⟨m, hm, rfl⟩
              exact ih_pos m (Finset.mem_range.mp (Finset.mem_filter.mp hm).1))
            (by
              intro l hl u hu
              rcases Finset.mem_image.mp hl with ⟨m₁, hm₁, rfl⟩
              rcases Finset.mem_image.mp hu with ⟨m₂, hm₂, rfl⟩
              rcases Finset.mem_filter.mp hm₁ with ⟨hm₁_lt, y₁, rfl, _, hy₁_not⟩
              rcases Finset.mem_filter.mp hm₂ with ⟨hm₂_lt, y₂, rfl, hy₂_ge, _⟩
              have hnot : ¬ r y₂ y₁ := fun h => hy₁_not (htrans _ _ _ hy₂_ge h)
              exact lt_of_not_ge (fun hle =>
                hnot ((ih_ord y₂ y₁ (Finset.mem_range.mp hm₂_lt) (Finset.mem_range.mp hm₁_lt)).mpr hle)))
          have hnot_both : ¬ (r x₀ y ∧ r y x₀) := by
            intro hboth
            apply hI
            exact ⟨enc y, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hy, y, rfl, hboth.1, hboth.2⟩⟩
          rcases htot x₀ y with hxy | hyx
          · have hnyx : ¬ r y x₀ := fun hyx => hnot_both ⟨hxy, hyx⟩
            have hmemU : G k (enc y) ∈ U :=
              Finset.mem_image.mpr ⟨enc y, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hy, y, rfl, hxy, hnyx⟩, rfl⟩
            have hlt : gapBid L U < G k (enc y) := hgap.2.2 _ hmemU
            exact ⟨⟨fun _ => le_of_lt hlt, fun _ => hxy⟩,
                   ⟨fun h => False.elim (hnyx h), fun hle => False.elim (not_le_of_gt hlt hle)⟩⟩
          · have hnxy : ¬ r x₀ y := fun hxy => hnot_both ⟨hxy, hyx⟩
            have hmemL : G k (enc y) ∈ L :=
              Finset.mem_image.mpr ⟨enc y, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hy, y, rfl, hyx, hnxy⟩, rfl⟩
            have hlt : G k (enc y) < gapBid L U := hgap.2.1 _ hmemL
            exact ⟨⟨fun h => False.elim (hnxy h), fun hle => False.elim (not_le_of_gt hlt hle)⟩,
                   ⟨fun _ => le_of_lt hlt, fun _ => hyx⟩⟩
      refine ⟨h_pos_succ, ?_⟩
      intro x y hx_lt hy_lt
      rw [hG_step k (enc x), hG_step k (enc y)]
      split_ifs with hxk hyk hyk'
      · have hxy_eq : x = y := henc (hxk.trans hyk.symm)
        subst hxy_eq
        exact ⟨fun _ => le_rfl, fun _ => hrefl x⟩
      · have hx_ex : ∃ z : X, enc z = k := ⟨x, hxk⟩
        have hx_eq : x = Classical.choose hx_ex := henc (hxk.trans (Classical.choose_spec hx_ex).symm)
        rw [hx_eq]
        exact (h_cmp hx_ex y (by omega)).1
      · have hy_ex : ∃ z : X, enc z = k := ⟨y, hyk'⟩
        have hy_eq : y = Classical.choose hy_ex := henc (hyk'.trans (Classical.choose_spec hy_ex).symm)
        rw [hy_eq]
        exact (h_cmp hy_ex x (by omega)).2
      · exact ih_ord x y (by omega) (by omega)
  refine ⟨fun x => G (enc x + 1) (enc x), ?_, ?_⟩
  · intro x
    exact (hG_inv (enc x + 1)).1 (enc x) (Nat.lt_succ_self _)
  · intro x y
    let K := max (enc x) (enc y) + 1
    have hxK : G K (enc x) = G (enc x + 1) (enc x) :=
      hG_lt (Nat.lt_succ_self _) (Nat.succ_le_succ (le_max_left _ _))
    have hyK : G K (enc y) = G (enc y + 1) (enc y) :=
      hG_lt (Nat.lt_succ_self _) (Nat.succ_le_succ (le_max_right _ _))
    dsimp only []
    rw [← hxK, ← hyK]
    exact (hG_inv K).2 x y
      (Nat.lt_succ_of_le (le_max_left _ _))
      (Nat.lt_succ_of_le (le_max_right _ _))

/-- Remark C.2: The lexicographic order on `ℝ × ℝ` is complete, transitive, and antisymmetric, yet
    admits no real-valued utility representation `f : ℝ × ℝ → ℝ` (justifying rational bids `ℚ₊`). -/
theorem rem_C_2_lexicographic_no_utility :
    (∀ x y : ℝ × ℝ, lexPlaneLE x y ∨ lexPlaneLE y x) ∧
    (∀ x y z : ℝ × ℝ, lexPlaneLE x y → lexPlaneLE y z → lexPlaneLE x z) ∧
    (∀ x y : ℝ × ℝ, lexPlaneLE x y → lexPlaneLE y x → x = y) ∧
    ¬ (∃ f : ℝ × ℝ → ℝ, ∀ x y : ℝ × ℝ, lexPlaneLE x y ↔ f x ≤ f y) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y
    rcases lt_trichotomy x.1 y.1 with hlt | heq | hgt
    · exact Or.inl (Or.inl hlt)
    · rcases le_total x.2 y.2 with hle | hge
      · exact Or.inl (Or.inr ⟨heq, hle⟩)
      · exact Or.inr (Or.inr ⟨heq.symm, hge⟩)
    · exact Or.inr (Or.inl hgt)
  · intro x y z hxy hyz
    rcases hxy with hxy1 | ⟨hxy1, hxy2⟩ <;> rcases hyz with hyz1 | ⟨hyz1, hyz2⟩
    · exact Or.inl (lt_trans hxy1 hyz1)
    · exact Or.inl (hyz1 ▸ hxy1)
    · exact Or.inl (hxy1 ▸ hyz1)
    · exact Or.inr ⟨hxy1.trans hyz1, le_trans hxy2 hyz2⟩
  · intro x y hxy hyx
    rcases hxy with hxy1 | ⟨hxy1, hxy2⟩ <;> rcases hyx with hyx1 | ⟨hyx1, hyx2⟩
    · linarith
    · linarith
    · linarith
    · exact Prod.ext hxy1 (le_antisymm hxy2 hyx2)
  · rintro ⟨f, hf⟩
    have hstep : ∀ a : ℝ, f (a, 0) < f (a, 1) := by
      intro a
      apply lt_of_not_ge
      intro hle
      have hlex : lexPlaneLE (a, 1) (a, 0) := (hf (a, 1) (a, 0)).mpr hle
      rcases hlex with hlt | ⟨_, hle2⟩ <;> linarith
    let g : ℝ → ℚ := fun a => Classical.choose (exists_rat_btwn (hstep a))
    have hg : ∀ a : ℝ, f (a, 0) < (g a : ℝ) ∧ (g a : ℝ) < f (a, 1) :=
      fun a => Classical.choose_spec (exists_rat_btwn (hstep a))
    have hg_mono : ∀ {a b : ℝ}, a < b → (g a : ℝ) < (g b : ℝ) := by
      intro a b hab
      have hlex : lexPlaneLE (a, 1) (b, 0) := Or.inl hab
      have hfle : f (a, 1) ≤ f (b, 0) := (hf (a, 1) (b, 0)).mp hlex
      exact lt_trans (lt_of_lt_of_le (hg a).2 hfle) (hg b).1
    have hg_inj : Function.Injective g := by
      intro a b hgab
      have hgab_r : (g a : ℝ) = (g b : ℝ) := congrArg Rat.cast hgab
      rcases lt_trichotomy a b with hlt | rfl | hgt
      · linarith [hg_mono hlt]
      · rfl
      · linarith [hg_mono hgt]
    have hc : Countable ℝ := hg_inj.countable
    exact not_countable hc

/-! ## Section 4: Lemma 4.6, Lemma 4.7 & Theorem 4.5 (Revelation Principle) -/

/-- Lemma 4.6 (`lemma:full-order`): An aggregation rule `q` admits an admissible payment rule `z`
    making `⟨q, z⟩` payment-monotone if and only if each agent's preference `⪰_i` is complete on
    every achievable menu `Q_i(b_{-i}, p)` with the zero-bid outcome `q(0, b_{-i}, p)` weakly least. -/
theorem lem_4_6_payment_monotone_iff_total_order (n : ℕ) (T : Type) [Fintype T] [DecidableEq T]
    (pref : AgentPrefs n T) (q : AggRule n T) (hpre : IsPreorderPrefs pref) :
    (∃ z : PaymentRule n T, IsAdmissiblePayment z ∧ IsPaymentMonotone pref ⟨q, z⟩) ↔
      MenuTotallyOrderedFromZero pref q := by
  constructor
  · rintro ⟨z, ⟨hz_nonneg, hz_zero⟩, hz_mono⟩ i p bOthers
    refine ⟨?_, ?_⟩
    · rintro q₁ ⟨b₁, rfl⟩ q₂ ⟨b₂, rfl⟩
      rcases le_total (z i (joinBid i b₂ bOthers) p) (z i (joinBid i b₁ bOthers) p) with hle | hge
      · exact Or.inl ((hz_mono i p bOthers b₁ b₂).mp hle)
      · exact Or.inr ((hz_mono i p bOthers b₂ b₁).mp hge)
    · intro b_i
      have h0le : z i (joinBid i 0 bOthers) p ≤ z i (joinBid i b_i bOthers) p := by
        rw [hz_zero i bOthers p]
        exact hz_nonneg i (joinBid i b_i bOthers) p
      exact (hz_mono i p bOthers b_i 0).mp h0le
  · intro hmenu
    haveI : Countable Bid := countable_bid
    have h_u_ex : ∀ (i : Fin n) (p : DistProfile n T) (bOthers : OpposingBids n i),
        ∃ u : Bid → Bid, ∀ b₁ b₂ : Bid,
          pref i p (q (joinBid i b₂ bOthers) p) (q (joinBid i b₁ bOthers) p) ↔ u b₁ ≤ u b₂ := by
      intro i p bOthers
      obtain ⟨u, _, hu⟩ := lem_C_1_debreu_countable_utility Bid
        (fun b₁ b₂ => pref i p (q (joinBid i b₂ bOthers) p) (q (joinBid i b₁ bOthers) p))
        (fun b₁ b₂ => (hmenu i p bOthers).1 _ ⟨b₂, rfl⟩ _ ⟨b₁, rfl⟩)
        (fun b₁ b₂ b₃ h₁₂ h₂₃ => (hpre i p).2 _ _ _ h₂₃ h₁₂)
      exact ⟨u, hu⟩
    let u : ∀ (i : Fin n), DistProfile n T → OpposingBids n i → Bid → Bid :=
      fun i p bOthers => Classical.choose (h_u_ex i p bOthers)
    have hu : ∀ (i : Fin n) (p : DistProfile n T) (bOthers : OpposingBids n i) (b₁ b₂ : Bid),
        pref i p (q (joinBid i b₂ bOthers) p) (q (joinBid i b₁ bOthers) p) ↔
          u i p bOthers b₁ ≤ u i p bOthers b₂ :=
      fun i p bOthers => Classical.choose_spec (h_u_ex i p bOthers)
    let z : PaymentRule n T := fun i b p =>
      (u i p (restrictBids i b) (b i) : ℝ) - (u i p (restrictBids i b) 0 : ℝ)
    refine ⟨z, ⟨?_, ?_⟩, ?_⟩
    · intro i b p
      have hzero : pref i p (q (joinBid i (b i) (restrictBids i b)) p)
          (q (joinBid i 0 (restrictBids i b)) p) :=
        (hmenu i p (restrictBids i b)).2 (b i)
      have hule : u i p (restrictBids i b) 0 ≤ u i p (restrictBids i b) (b i) :=
        (hu i p (restrictBids i b) 0 (b i)).mp hzero
      have hule_r : (u i p (restrictBids i b) 0 : ℝ) ≤ (u i p (restrictBids i b) (b i) : ℝ) := by
        exact_mod_cast hule
      dsimp only [z]
      linarith
    · intro i bOthers p
      simp [z]
    · intro i p bOthers b_i b'_i
      dsimp only [z]
      simp only [restrictBids_joinBid, joinBid_self, sub_le_sub_iff_right]
      calc ((u i p bOthers b'_i : Bid) : ℝ) ≤ ((u i p bOthers b_i : Bid) : ℝ) ↔
          u i p bOthers b'_i ≤ u i p bOthers b_i := by exact_mod_cast Iff.rfl
        _ ↔ pref i p (q (joinBid i b_i bOthers) p) (q (joinBid i b'_i bOthers) p) :=
          (hu i p bOthers b'_i b_i).symm

private lemma realign_complete_preorder_on_bids (R : Bid → Bid → Prop)
    (htot : ∀ x y : Bid, R x y ∨ R y x)
    (htrans : ∀ x y z : Bid, R x y → R y z → R x z)
    (h0 : ∀ x : Bid, R 0 x) :
    ∃ (π ρ : Bid → Bid),
      π 0 = 0 ∧
      ρ 0 = 0 ∧
      (∀ b : Bid, ρ (π b) = b) ∧
      (∀ b₁ b₂ : Bid, b₁ ≤ b₂ → R (ρ b₁) (ρ b₂)) := by
  have hrefl : ∀ x : Bid, R x x := fun x => (htot x x).elim id id
  let ltOrig : Bid → Bid → Prop := fun x y =>
    (R x y ∧ ¬ R y x) ∨ (R x y ∧ R y x ∧ x < y)
  let leOrig : Bid → Bid → Prop := fun x y => x = y ∨ ltOrig x y
  have hlt_irrefl : ∀ x : Bid, ¬ ltOrig x x := by
    rintro x (⟨h1, h2⟩ | ⟨_, _, h3⟩)
    · exact h2 h1
    · exact lt_irrefl x h3
  have hlt_trans : ∀ {x y z : Bid}, ltOrig x y → ltOrig y z → ltOrig x z := by
    rintro x y z (⟨hxy, hnyx⟩ | ⟨hxy, hyx, hxylt⟩) (⟨hyz, hnzy⟩ | ⟨hyz, hzy, hyzlt⟩)
    · exact Or.inl ⟨htrans x y z hxy hyz, fun hzx => hnyx (htrans y z x hyz hzx)⟩
    · exact Or.inl ⟨htrans x y z hxy hyz, fun hzx => hnyx (htrans y z x hyz hzx)⟩
    · exact Or.inl ⟨htrans x y z hxy hyz, fun hzx => hnzy (htrans z x y hzx hxy)⟩
    · exact Or.inr ⟨htrans x y z hxy hyz, htrans z y x hzy hyx, lt_trans hxylt hyzlt⟩
  have hlt_trich : ∀ x y : Bid, ltOrig x y ∨ x = y ∨ ltOrig y x := by
    intro x y
    by_cases hxy : R x y
    · by_cases hyx : R y x
      · rcases lt_trichotomy x y with hlt | rfl | hgt
        · exact Or.inl (Or.inr ⟨hxy, hyx, hlt⟩)
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr (Or.inr ⟨hyx, hxy, hgt⟩))
      · exact Or.inl (Or.inl ⟨hxy, hyx⟩)
    · rcases htot x y with h | hyx
      · exact False.elim (hxy h)
      · exact Or.inr (Or.inr (Or.inl ⟨hyx, hxy⟩))
  have hlt_not_le : ∀ {x y : Bid}, ltOrig x y → ¬ leOrig y x := by
    rintro x y hxy (rfl | hyx)
    · exact hlt_irrefl _ hxy
    · exact hlt_irrefl _ (hlt_trans hxy hyx)
  have hle_R : ∀ {x y : Bid}, leOrig x y → R x y := by
    rintro x y (rfl | ⟨hxy, _⟩ | ⟨hxy, _, _⟩)
    · exact hrefl x
    · exact hxy
    · exact hxy
  let Inv : Finset (Bid × Bid) → Prop := fun P =>
    (∀ p ∈ P, 0 < p.1 ∧ 0 < p.2) ∧
    (∀ p₁ ∈ P, ∀ p₂ ∈ P, p₁.1 = p₂.1 → p₁.2 = p₂.2) ∧
    (∀ p₁ ∈ P, ∀ p₂ ∈ P, p₁.1 < p₂.1 → leOrig p₁.2 p₂.2)
  have hInv_le : ∀ {P : Finset (Bid × Bid)} {p₁ p₂ : Bid × Bid},
      Inv P → p₁ ∈ P → p₂ ∈ P → p₁.1 ≤ p₂.1 → leOrig p₁.2 p₂.2 := by
    intro P p₁ p₂ hP hp₁ hp₂ hle
    rcases eq_or_lt_of_le hle with heq | hlt
    · exact Or.inl (hP.2.1 p₁ hp₁ p₂ hp₂ heq)
    · exact hP.2.2 p₁ hp₁ p₂ hp₂ hlt
  let insertOrig : Finset (Bid × Bid) → Bid → Finset (Bid × Bid) := fun P b =>
    if ∃ p ∈ P, p.2 = b then P
    else
      let L := (P.filter (fun p => ltOrig p.2 b)).image Prod.fst
      let U := (P.filter (fun p => ltOrig b p.2)).image Prod.fst
      insert (gapBid L U, b) P
  have h_insertOrig : ∀ (P : Finset (Bid × Bid)) (b : Bid),
      Inv P → 0 < b →
      Inv (insertOrig P b) ∧ P ⊆ insertOrig P b ∧ (insertOrig P b).Nonempty ∧
      (∃ l : Bid, (l, b) ∈ insertOrig P b) := by
    intro P b hP hb
    dsimp only [insertOrig]
    split_ifs with hex
    · rcases hex with ⟨p, hp, rfl⟩
      exact ⟨hP, Finset.Subset.refl P, ⟨p, hp⟩, ⟨p.1, by rwa [Prod.mk.eta]⟩⟩
    · set L := (P.filter (fun p => ltOrig p.2 b)).image Prod.fst
      set U := (P.filter (fun p => ltOrig b p.2)).image Prod.fst
      set l_new := gapBid L U
      have hgap := gapBid_spec L U
        (by
          intro u hu
          rcases Finset.mem_image.mp hu with ⟨p, hp, rfl⟩
          exact (hP.1 p (Finset.mem_filter.mp hp).1).1)
        (by
          intro l hl u hu
          rcases Finset.mem_image.mp hl with ⟨p₁, hp₁, rfl⟩
          rcases Finset.mem_image.mp hu with ⟨p₂, hp₂, rfl⟩
          have hp₁P := (Finset.mem_filter.mp hp₁).1
          have hlt₁ := (Finset.mem_filter.mp hp₁).2
          have hp₂P := (Finset.mem_filter.mp hp₂).1
          have hlt₂ := (Finset.mem_filter.mp hp₂).2
          exact lt_of_not_ge (fun hge =>
            hlt_not_le (hlt_trans hlt₁ hlt₂) (hInv_le hP hp₂P hp₁P hge)))
      have hp_sep : ∀ p ∈ P, (p.1 < l_new ∧ ltOrig p.2 b) ∨ (l_new < p.1 ∧ ltOrig b p.2) := by
        intro p hp
        rcases hlt_trich p.2 b with hlt | heq | hgt
        · have hmem : p.1 ∈ L := Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr ⟨hp, hlt⟩, rfl⟩
          exact Or.inl ⟨hgap.2.1 _ hmem, hlt⟩
        · exact False.elim (hex ⟨p, hp, heq⟩)
        · have hmem : p.1 ∈ U := Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr ⟨hp, hgt⟩, rfl⟩
          exact Or.inr ⟨hgap.2.2 _ hmem, hgt⟩
      refine ⟨⟨?_, ?_, ?_⟩, Finset.subset_insert _ _, Finset.insert_nonempty _ _,
        ⟨l_new, Finset.mem_insert_self _ _⟩⟩
      · intro p hp
        rcases Finset.mem_insert.mp hp with rfl | hpP
        · exact ⟨hgap.1, hb⟩
        · exact hP.1 p hpP
      · intro p₁ hp₁ p₂ hp₂ heq
        rcases Finset.mem_insert.mp hp₁ with rfl | hp₁P <;>
          rcases Finset.mem_insert.mp hp₂ with rfl | hp₂P
        · rfl
        · have heq' : l_new = p₂.1 := heq
          rcases hp_sep p₂ hp₂P with ⟨hlt, _⟩ | ⟨hgt, _⟩
          · exact False.elim ((ne_of_lt hlt) heq'.symm)
          · exact False.elim ((ne_of_gt hgt) heq'.symm)
        · have heq' : p₁.1 = l_new := heq
          rcases hp_sep p₁ hp₁P with ⟨hlt, _⟩ | ⟨hgt, _⟩
          · exact False.elim ((ne_of_lt hlt) heq')
          · exact False.elim ((ne_of_gt hgt) heq')
        · exact hP.2.1 p₁ hp₁P p₂ hp₂P heq
      · intro p₁ hp₁ p₂ hp₂ hlt
        rcases Finset.mem_insert.mp hp₁ with rfl | hp₁P <;>
          rcases Finset.mem_insert.mp hp₂ with rfl | hp₂P
        · exact False.elim (lt_irrefl _ hlt)
        · rcases hp_sep p₂ hp₂P with ⟨h1, _⟩ | ⟨_, h2⟩
          · exact False.elim (lt_asymm hlt h1)
          · exact Or.inr h2
        · rcases hp_sep p₁ hp₁P with ⟨_, h1⟩ | ⟨h2, _⟩
          · exact Or.inr h1
          · exact False.elim (lt_asymm hlt h2)
        · exact hP.2.2 p₁ hp₁P p₂ hp₂P hlt
  let insertLabel : Finset (Bid × Bid) → Bid → Finset (Bid × Bid) := fun P l =>
    if ∃ p ∈ P, p.1 = l then P
    else if hne : P.Nonempty then
      let B := (P.filter (fun p => p.1 < l)).image Prod.fst
      if hB : B.Nonempty then
        let o_new := (Classical.choose (Finset.mem_image.mp (Finset.max'_mem B hB))).2
        insert (l, o_new) P
      else
        let A := P.image Prod.fst
        let o_new := (Classical.choose (Finset.mem_image.mp (Finset.min'_mem A (hne.image Prod.fst)))).2
        insert (l, o_new) P
    else P
  have h_insertLabel : ∀ (P : Finset (Bid × Bid)) (l : Bid),
      Inv P → P.Nonempty → 0 < l →
      Inv (insertLabel P l) ∧ P ⊆ insertLabel P l ∧ (∃ o : Bid, (l, o) ∈ insertLabel P l) := by
    intro P l hP hne hl
    dsimp only [insertLabel]
    by_cases hex : ∃ p ∈ P, p.1 = l
    · rw [if_pos hex]
      rcases hex with ⟨p, hp, rfl⟩
      exact ⟨hP, Finset.Subset.refl P, ⟨p.2, by rwa [Prod.mk.eta]⟩⟩
    · rw [if_neg hex, dif_pos hne]
      set B := (P.filter (fun p => p.1 < l)).image Prod.fst
      by_cases hB : B.Nonempty
      · rw [dif_pos hB]
        set p_max := Classical.choose (Finset.mem_image.mp (Finset.max'_mem B hB))
        have hp_max_spec := Classical.choose_spec (Finset.mem_image.mp (Finset.max'_mem B hB))
        have hp_max_P : p_max ∈ P := (Finset.mem_filter.mp hp_max_spec.1).1
        have hp_max_lt : p_max.1 < l := (Finset.mem_filter.mp hp_max_spec.1).2
        have ho_pos : 0 < p_max.2 := (hP.1 p_max hp_max_P).2
        refine ⟨⟨?_, ?_, ?_⟩, Finset.subset_insert _ _, ⟨p_max.2, Finset.mem_insert_self _ _⟩⟩
        · intro p hp
          rcases Finset.mem_insert.mp hp with rfl | hpP
          · exact ⟨hl, ho_pos⟩
          · exact hP.1 p hpP
        · intro p₁ hp₁ p₂ hp₂ heq
          rcases Finset.mem_insert.mp hp₁ with rfl | hp₁P <;>
            rcases Finset.mem_insert.mp hp₂ with rfl | hp₂P
          · rfl
          · exact False.elim (hex ⟨p₂, hp₂P, heq.symm⟩)
          · exact False.elim (hex ⟨p₁, hp₁P, heq⟩)
          · exact hP.2.1 p₁ hp₁P p₂ hp₂P heq
        · intro p₁ hp₁ p₂ hp₂ hlt
          rcases Finset.mem_insert.mp hp₁ with rfl | hp₁P <;>
            rcases Finset.mem_insert.mp hp₂ with rfl | hp₂P
          · exact False.elim (lt_irrefl _ hlt)
          · change leOrig p_max.2 p₂.2
            exact hP.2.2 p_max hp_max_P p₂ hp₂P (lt_trans hp_max_lt hlt)
          · have hmemB : p₁.1 ∈ B :=
              Finset.mem_image.mpr ⟨p₁, Finset.mem_filter.mpr ⟨hp₁P, hlt⟩, rfl⟩
            have hle_max : p₁.1 ≤ p_max.1 := hp_max_spec.2.symm ▸ Finset.le_max' B p₁.1 hmemB
            change leOrig p₁.2 p_max.2
            exact hInv_le hP hp₁P hp_max_P hle_max
          · exact hP.2.2 p₁ hp₁P p₂ hp₂P hlt
      · rw [dif_neg hB]
        set A := P.image Prod.fst
        have hA : A.Nonempty := hne.image Prod.fst
        set p_min := Classical.choose (Finset.mem_image.mp (Finset.min'_mem A hA))
        have hp_min_spec := Classical.choose_spec (Finset.mem_image.mp (Finset.min'_mem A hA))
        have hp_min_P : p_min ∈ P := hp_min_spec.1
        have ho_pos : 0 < p_min.2 := (hP.1 p_min hp_min_P).2
        refine ⟨⟨?_, ?_, ?_⟩, Finset.subset_insert _ _, ⟨p_min.2, Finset.mem_insert_self _ _⟩⟩
        · intro p hp
          rcases Finset.mem_insert.mp hp with rfl | hpP
          · exact ⟨hl, ho_pos⟩
          · exact hP.1 p hpP
        · intro p₁ hp₁ p₂ hp₂ heq
          rcases Finset.mem_insert.mp hp₁ with rfl | hp₁P <;>
            rcases Finset.mem_insert.mp hp₂ with rfl | hp₂P
          · rfl
          · exact False.elim (hex ⟨p₂, hp₂P, heq.symm⟩)
          · exact False.elim (hex ⟨p₁, hp₁P, heq⟩)
          · exact hP.2.1 p₁ hp₁P p₂ hp₂P heq
        · intro p₁ hp₁ p₂ hp₂ hlt
          rcases Finset.mem_insert.mp hp₁ with rfl | hp₁P <;>
            rcases Finset.mem_insert.mp hp₂ with rfl | hp₂P
          · exact False.elim (lt_irrefl _ hlt)
          · have hmemA : p₂.1 ∈ A := Finset.mem_image.mpr ⟨p₂, hp₂P, rfl⟩
            have hmin_le : p_min.1 ≤ p₂.1 := hp_min_spec.2.symm ▸ Finset.min'_le A p₂.1 hmemA
            change leOrig p_min.2 p₂.2
            exact hInv_le hP hp_min_P hp₂P hmin_le
          · exact False.elim (hB ⟨p₁.1, Finset.mem_image.mpr ⟨p₁, Finset.mem_filter.mpr ⟨hp₁P, hlt⟩, rfl⟩⟩)
          · exact hP.2.2 p₁ hp₁P p₂ hp₂P hlt
  haveI : Countable Bid := countable_bid
  let PosBid := {b : Bid // 0 < b}
  haveI : Countable PosBid := Subtype.val_injective.countable
  haveI : Nonempty PosBid := ⟨⟨1, zero_lt_one⟩⟩
  obtain ⟨enum, henum⟩ := exists_surjective_nat PosBid
  let P : ℕ → Finset (Bid × Bid) := fun k =>
    Nat.rec ∅ (fun j pj => insertLabel (insertOrig pj (enum j).1) (enum j).1) k
  have hP_step : ∀ k, P (k + 1) = insertLabel (insertOrig (P k) (enum k).1) (enum k).1 :=
    fun _ => rfl
  have hP_inv_sub : ∀ k, Inv (P k) ∧ P k ⊆ P (k + 1) := by
    intro k
    induction k with
    | zero =>
      have h_inv0 : Inv (P 0) := ⟨by simp [P], by simp [P], by simp [P]⟩
      exact ⟨h_inv0, Finset.empty_subset _⟩
    | succ k ih =>
      have h1 := h_insertOrig (P k) (enum k).1 ih.1 (enum k).2
      have h2 := h_insertLabel (insertOrig (P k) (enum k).1) (enum k).1 h1.1 h1.2.2.1 (enum k).2
      have h_inv_k1 : Inv (P (k + 1)) := by rw [hP_step]; exact h2.1
      have h1' := h_insertOrig (P (k + 1)) (enum (k + 1)).1 h_inv_k1 (enum (k + 1)).2
      have h2' := h_insertLabel (insertOrig (P (k + 1)) (enum (k + 1)).1) (enum (k + 1)).1
        h1'.1 h1'.2.2.1 (enum (k + 1)).2
      exact ⟨h_inv_k1, by rw [hP_step (k + 1)]; exact Finset.Subset.trans h1'.2.1 h2'.2.1⟩
  have hP_sub : ∀ {k₁ k₂ : ℕ}, k₁ ≤ k₂ → P k₁ ⊆ P k₂ := by
    intro k₁ k₂ hle
    induction k₂ with
    | zero =>
      have hk₁ : k₁ = 0 := by omega
      subst hk₁; exact Finset.Subset.refl _
    | succ j ih =>
      rcases Nat.eq_or_lt_of_le hle with rfl | hlt
      · exact Finset.Subset.refl _
      · exact Finset.Subset.trans (ih (Nat.le_of_lt_succ hlt)) (hP_inv_sub j).2
  have h_orig_ex : ∀ {b : Bid}, 0 < b → ∃ k : ℕ, ∃ l : Bid, (l, b) ∈ P k := by
    intro b hb
    obtain ⟨k, hk⟩ := henum ⟨b, hb⟩
    have hk_val : (enum k).1 = b := congrArg Subtype.val hk
    have h1 := h_insertOrig (P k) (enum k).1 (hP_inv_sub k).1 (enum k).2
    have h2 := h_insertLabel (insertOrig (P k) (enum k).1) (enum k).1 h1.1 h1.2.2.1 (enum k).2
    rcases h1.2.2.2 with ⟨l, hl⟩
    refine ⟨k + 1, l, ?_⟩
    rw [hP_step, ← hk_val]
    exact h2.2.1 hl
  have h_lbl_ex : ∀ {l : Bid}, 0 < l → ∃ k : ℕ, ∃ o : Bid, (l, o) ∈ P k := by
    intro l hl
    obtain ⟨k, hk⟩ := henum ⟨l, hl⟩
    have hk_val : (enum k).1 = l := congrArg Subtype.val hk
    have h1 := h_insertOrig (P k) (enum k).1 (hP_inv_sub k).1 (enum k).2
    have h2 := h_insertLabel (insertOrig (P k) (enum k).1) (enum k).1 h1.1 h1.2.2.1 (enum k).2
    rcases h2.2.2 with ⟨o, ho⟩
    refine ⟨k + 1, o, ?_⟩
    rw [hP_step, ← hk_val]
    exact ho
  let π : Bid → Bid := fun b =>
    if hb : 0 < b then Classical.choose (Classical.choose_spec (h_orig_ex hb)) else 0
  let ρ : Bid → Bid := fun l =>
    if hl : 0 < l then Classical.choose (Classical.choose_spec (h_lbl_ex hl)) else 0
  refine ⟨π, ρ, by simp [π], by simp [ρ], ?_, ?_⟩
  · intro b
    by_cases hb : 0 < b
    · set k₁ := Classical.choose (h_orig_ex hb)
      have hk₁ : (π b, b) ∈ P k₁ := by
        dsimp only [π]; rw [dif_pos hb]
        exact Classical.choose_spec (Classical.choose_spec (h_orig_ex hb))
      have hπ_pos : 0 < π b := ((hP_inv_sub k₁).1.1 _ hk₁).1
      set k₂ := Classical.choose (h_lbl_ex hπ_pos)
      have hk₂ : (π b, ρ (π b)) ∈ P k₂ := by
        dsimp only [ρ]; rw [dif_pos hπ_pos]
        exact Classical.choose_spec (Classical.choose_spec (h_lbl_ex hπ_pos))
      let M := max k₁ k₂
      exact (hP_inv_sub M).1.2.1 _ (hP_sub (le_max_right k₁ k₂) hk₂) _
        (hP_sub (le_max_left k₁ k₂) hk₁) rfl
    · have hb0 : b = 0 := le_antisymm (not_lt.mp hb) (zero_le b)
      subst hb0; simp [π, ρ]
  · intro b₁ b₂ hle
    by_cases hb₁ : 0 < b₁
    · have hb₂ : 0 < b₂ := lt_of_lt_of_le hb₁ hle
      set k₁ := Classical.choose (h_lbl_ex hb₁)
      have hk₁ : (b₁, ρ b₁) ∈ P k₁ := by
        dsimp only [ρ]; rw [dif_pos hb₁]
        exact Classical.choose_spec (Classical.choose_spec (h_lbl_ex hb₁))
      set k₂ := Classical.choose (h_lbl_ex hb₂)
      have hk₂ : (b₂, ρ b₂) ∈ P k₂ := by
        dsimp only [ρ]; rw [dif_pos hb₂]
        exact Classical.choose_spec (Classical.choose_spec (h_lbl_ex hb₂))
      let M := max k₁ k₂
      exact hle_R (hInv_le (hP_inv_sub M).1
        (hP_sub (le_max_left k₁ k₂) hk₁)
        (hP_sub (le_max_right k₁ k₂) hk₂) hle)
    · dsimp only [ρ]
      rw [dif_neg hb₁]
      exact h0 _

private lemma realign_mechanism_master (n : ℕ) (T : Type) [Fintype T] [DecidableEq T]
    (pref : AgentPrefs n T) (q : AggRule n T)
    (hpre : IsPreorderPrefs pref)
    (hcons : IsConsistentAgg pref q)
    (hmenu : MenuTotallyOrderedFromZero pref q) :
    ∃ (π ρ : DistProfile n T → Fin n → Bid → Bid),
      (∀ p i, π p i 0 = 0 ∧ ρ p i 0 = 0 ∧ ∀ b_i : Bid, ρ p i (π p i b_i) = b_i) ∧
      IsMonotoneAgg pref (fun b' p => q (applyStrategyProfile (ρ p) b') p) ∧
      (∀ p b, applyStrategyProfile (ρ p) (applyStrategyProfile (π p) b) = b) ∧
      (∀ z : PaymentRule n T, IsAdmissiblePayment z →
        IsAdmissiblePayment (fun i b' p => z i (applyStrategyProfile (ρ p) b') p)) ∧
      (∀ z : PaymentRule n T, IsPaymentMonotone pref ⟨q, z⟩ →
        IsPaymentMonotone pref
          ⟨fun b' p => q (applyStrategyProfile (ρ p) b') p,
           fun i b' p => z i (applyStrategyProfile (ρ p) b') p⟩) := by
  have h_ex : ∀ (p : DistProfile n T) (i : Fin n),
      ∃ (π_i ρ_i : Bid → Bid),
        π_i 0 = 0 ∧ ρ_i 0 = 0 ∧ (∀ b_i : Bid, ρ_i (π_i b_i) = b_i) ∧
        (∀ b₁ b₂ : Bid, b₁ ≤ b₂ → ∀ bOthers : OpposingBids n i,
          pref i p (q (joinBid i (ρ_i b₂) bOthers) p) (q (joinBid i (ρ_i b₁) bOthers) p)) := by
    intro p i
    apply realign_complete_preorder_on_bids
      (fun b₁ b₂ => ∀ bOthers : OpposingBids n i,
        pref i p (q (joinBid i b₂ bOthers) p) (q (joinBid i b₁ bOthers) p))
    · intro b₁ b₂
      by_cases h : ∀ bOthers : OpposingBids n i,
          pref i p (q (joinBid i b₂ bOthers) p) (q (joinBid i b₁ bOthers) p)
      · exact Or.inl h
      · push_neg at h
        rcases h with ⟨bOthers, hnot⟩
        have hyes : pref i p (q (joinBid i b₁ bOthers) p) (q (joinBid i b₂ bOthers) p) := by
          rcases (hmenu i p bOthers).1 _ ⟨b₁, rfl⟩ _ ⟨b₂, rfl⟩ with h1 | h2
          · exact h1
          · exact False.elim (hnot h2)
        exact Or.inr (hcons i p b₁ b₂ ⟨bOthers, ⟨hyes, hnot⟩⟩)
    · intro b₁ b₂ b₃ h₁₂ h₂₃ bOthers
      exact (hpre i p).2 _ _ _ (h₂₃ bOthers) (h₁₂ bOthers)
    · intro x bOthers
      exact (hmenu i p bOthers).2 x
  let π : DistProfile n T → Fin n → Bid → Bid :=
    fun p i => Classical.choose (h_ex p i)
  let ρ : DistProfile n T → Fin n → Bid → Bid :=
    fun p i => Classical.choose (Classical.choose_spec (h_ex p i))
  have hspec : ∀ (p : DistProfile n T) (i : Fin n),
      π p i 0 = 0 ∧ ρ p i 0 = 0 ∧ (∀ b_i : Bid, ρ p i (π p i b_i) = b_i) ∧
      (∀ b₁ b₂ : Bid, b₁ ≤ b₂ → ∀ bOthers : OpposingBids n i,
        pref i p (q (joinBid i (ρ p i b₂) bOthers) p) (q (joinBid i (ρ p i b₁) bOthers) p)) :=
    fun p i => Classical.choose_spec (Classical.choose_spec (h_ex p i))
  have h_conj : ∀ (σ : Fin n → Bid → Bid) (i : Fin n) (b_i : Bid) (bOthers : OpposingBids n i),
      applyStrategyProfile σ (joinBid i b_i bOthers) =
        joinBid i (σ i b_i) (fun j => σ j.1 (bOthers j)) := by
    intro σ i b_i bOthers
    funext j
    by_cases hj : j = i
    · subst hj; simp [applyStrategyProfile, joinBid]
    · simp [applyStrategyProfile, joinBid, hj]
  have h_inv_prof : ∀ p b, applyStrategyProfile (ρ p) (applyStrategyProfile (π p) b) = b := by
    intro p b
    funext i
    exact (hspec p i).2.2.1 (b i)
  refine ⟨π, ρ, ?_, ?_, h_inv_prof, ?_, ?_⟩
  · intro p i
    exact ⟨(hspec p i).1, (hspec p i).2.1, (hspec p i).2.2.1⟩
  · intro i p bOthers b_i b'_i hle
    dsimp only []
    rw [h_conj (ρ p) i b_i bOthers, h_conj (ρ p) i b'_i bOthers]
    exact (hspec p i).2.2.2 b'_i b_i hle (fun j => ρ p j.1 (bOthers j))
  · intro z hz
    refine ⟨fun i b' p => hz.1 i (applyStrategyProfile (ρ p) b') p, ?_⟩
    intro i bOthers p
    dsimp only []
    rw [h_conj (ρ p) i 0 bOthers, (hspec p i).2.1]
    exact hz.2 i (fun j => ρ p j.1 (bOthers j)) p
  · intro z hz_mono i p bOthers b_i b'_i
    dsimp only []
    rw [h_conj (ρ p) i b_i bOthers, h_conj (ρ p) i b'_i bOthers]
    exact hz_mono i p (fun j => ρ p j.1 (bOthers j)) (ρ p i b_i) (ρ p i b'_i)

/-- Lemma 4.7 (`lemma:consistent`): Any consistent aggregation rule `q` whose achievable menus are
    totally ordered with zero-bid outcome weakly least can be realigned via strategy mappings
    `π_i : ℚ₊ → ℚ₊` into a monotone aggregation rule `q̃`. -/
theorem lem_4_7_consistent_realignment (n : ℕ) (T : Type) [Fintype T] [DecidableEq T]
    (pref : AgentPrefs n T) (q : AggRule n T)
    (hpre : IsPreorderPrefs pref) (hcons : IsConsistentAgg pref q)
    (hmenu : MenuTotallyOrderedFromZero pref q) :
    ∃ qtilde : AggRule n T,
      IsMonotoneAgg pref qtilde ∧
      ∀ p : DistProfile n T, ∃ π : Fin n → Bid → Bid,
        ∀ b : BidProfile n, q b p = qtilde (applyStrategyProfile π b) p := by
  obtain ⟨π, ρ, _, hmono, hinv, _, _⟩ := realign_mechanism_master n T pref q hpre hcons hmenu
  refine ⟨fun b' p => q (applyStrategyProfile (ρ p) b') p, hmono, ?_⟩
  intro p
  refine ⟨π p, fun b => ?_⟩
  dsimp only []
  rw [hinv p b]

/-- Theorem 4.5 (`thm:monotone`, Revelation Principle): Every payment-monotone, consistent,
    admissible token auction mechanism `𝓜 = ⟨q, z⟩` is strategically and deviation-equivalent to a
    monotone, payment-monotone, admissible mechanism `𝓜̃ = ⟨q̃, z̃⟩`. -/
theorem thm_4_5_revelation_principle (n : ℕ) (T : Type) [Fintype T] [DecidableEq T]
    (pref : AgentPrefs n T) (M : TokenMechanism n T)
    (hpre : IsPreorderPrefs pref)
    (hcons : IsConsistentAgg pref M.q)
    (hadm : IsAdmissiblePayment M.z)
    (hpmono : IsPaymentMonotone pref M) :
    ∃ Mtilde : TokenMechanism n T,
      IsMonotoneAgg pref Mtilde.q ∧
      IsAdmissiblePayment Mtilde.z ∧
      IsPaymentMonotone pref Mtilde ∧
      StrategicallyEquivalent M Mtilde ∧
      (∀ p : DistProfile n T, ∃ (π ρ : Fin n → Bid → Bid),
        (∀ i : Fin n, π i 0 = 0 ∧ ρ i 0 = 0 ∧ ∀ b_i : Bid, ρ i (π i b_i) = b_i) ∧
        (∀ b' : BidProfile n,
          Mtilde.q b' p = M.q (applyStrategyProfile ρ b') p ∧
          ∀ i : Fin n, Mtilde.z i b' p = M.z i (applyStrategyProfile ρ b') p) ∧
        (∀ b : BidProfile n,
          M.q b p = Mtilde.q (applyStrategyProfile π b) p ∧
          ∀ i : Fin n, M.z i b p = Mtilde.z i (applyStrategyProfile π b) p)) := by
  have hmenu : MenuTotallyOrderedFromZero pref M.q :=
    (lem_4_6_payment_monotone_iff_total_order n T pref M.q hpre).mp ⟨M.z, hadm, hpmono⟩
  obtain ⟨π, ρ, h0, hmono, hinv, hadm_tilde, hpmono_tilde⟩ :=
    realign_mechanism_master n T pref M.q hpre hcons hmenu
  let Mtilde : TokenMechanism n T :=
    { q := fun b' p => M.q (applyStrategyProfile (ρ p) b') p
      z := fun i b' p => M.z i (applyStrategyProfile (ρ p) b') p }
  refine ⟨Mtilde, hmono, hadm_tilde M.z hadm, hpmono_tilde M.z hpmono, ?_, ?_⟩
  · intro p
    refine ⟨π p, fun b => ?_⟩
    dsimp only [Mtilde]
    rw [hinv p b]
    exact ⟨rfl, fun _ => rfl⟩
  · intro p
    refine ⟨π p, ρ p, h0 p, fun _ => ⟨rfl, fun _ => rfl⟩, fun b => ?_⟩
    dsimp only [Mtilde]
    rw [hinv p b]
    exact ⟨rfl, fun _ => rfl⟩

end

end TokenAuctions
