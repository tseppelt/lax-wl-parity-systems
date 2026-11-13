import Mathlib
import Lax119563.MatrixCompiler

/-!
# The checksum code

Vectors over the coordinates `𝔠 = [k] × 𝔽₂^ℓ`, the code `C = ker B` of the check matrix,
addresses as codewords, and the action of block-induced permutations.
-/

open Lax119563.ImplicitParitySystems Lax119563.MatrixCompiler

namespace Lax119563Proofs.Matrix

variable {k ℓ : ℕ}

/-- Vectors indexed by the coordinates. -/
abbrev Vec (k ℓ : ℕ) := Coord k ℓ → ZMod 2

/-- The rows of the check matrix. -/
abbrev Row (k ℓ : ℕ) := Fin (k - 1) ⊕ Fin ℓ

/-- The dot product of two vectors. -/
def dot (y z : Vec k ℓ) : ZMod 2 := ∑ c, y c * z c

/-- `y` is a codeword: `B y = 0`. -/
def IsCode (y : Vec k ℓ) : Prop := ∀ j : Row k ℓ, ∑ c, checkMatrix k ℓ j c * y c = 0

/-- The sum of the entries of `y` in block `i`. -/
def blockSum (y : Vec k ℓ) (i : Fin k) : ZMod 2 := ∑ b, y (i, b)

/-- `y` vanishes outside `J`. -/
def SuppIn (y : Vec k ℓ) (J : Finset (Coord k ℓ)) : Prop := ∀ c, c ∉ J → y c = 0

/-- The indicator vector of the support of an address array. -/
def ind (a : Fin k → BlockCoord ℓ) : Vec k ℓ := fun c => if c.2 = a c.1 then 1 else 0

lemma zmod2_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma zmod2_ne_zero_iff (x : ZMod 2) : x ≠ 0 ↔ x = 1 := by
  rcases zmod2_eq_zero_or_one x with h | h <;> simp [h]

lemma zmod2_add_self (x : ZMod 2) : x + x = 0 := by
  rcases zmod2_eq_zero_or_one x with h | h <;> subst h <;> decide

lemma zmod2_neg (x : ZMod 2) : -x = x := by
  rcases zmod2_eq_zero_or_one x with h | h <;> subst h <;> decide

lemma zmod2_sub (x y : ZMod 2) : x - y = x + y := by
  rw [sub_eq_add_neg, zmod2_neg]

lemma zmod2_eq_of_add_eq_zero {x y : ZMod 2} (h : x + y = 0) : x = y := by
  have := congrArg (· + y) h
  simpa [add_assoc, zmod2_add_self] using this

lemma zmod2_add_eq_zero_iff {x y : ZMod 2} : x + y = 0 ↔ x = y :=
  ⟨zmod2_eq_of_add_eq_zero, fun h => h ▸ zmod2_add_self x⟩

lemma mem_supp_iff {a : Fin k → BlockCoord ℓ} {c : Coord k ℓ} : c ∈ supp a ↔ a c.1 = c.2 := by
  constructor
  · intro h
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp h
    rw [← hi]
  · intro h
    exact Finset.mem_image.mpr ⟨c.1, Finset.mem_univ _, by rw [h]⟩

lemma card_supp (a : Fin k → BlockCoord ℓ) : (supp a).card = k := by
  rw [supp, Finset.card_image_of_injective _ (fun i j h => congrArg Prod.fst h)]
  simp

lemma ind_apply_eq_one {a : Fin k → BlockCoord ℓ} {c : Coord k ℓ} :
    ind a c = 1 ↔ c ∈ supp a := by
  rw [mem_supp_iff, ind]
  constructor
  · intro h
    by_contra h'
    rw [if_neg (Ne.symm h')] at h
    exact zero_ne_one h
  · intro h; rw [if_pos h.symm]

lemma ind_apply_eq_zero {a : Fin k → BlockCoord ℓ} {c : Coord k ℓ} :
    ind a c = 0 ↔ c ∉ supp a := by
  rw [← ind_apply_eq_one, ← zmod2_ne_zero_iff, not_not]

lemma suppIn_ind {a : Fin k → BlockCoord ℓ} {J : Finset (Coord k ℓ)} :
    SuppIn (ind a) J ↔ supp a ⊆ J := by
  constructor
  · intro h c hc
    by_contra hJ
    have := h c hJ
    rw [ind_apply_eq_zero] at this
    exact this hc
  · intro h c hc
    rw [ind_apply_eq_zero]
    exact fun h' => hc (h h')

/-- Sum over coordinates, block by block. -/
lemma sum_coord (f : Coord k ℓ → ZMod 2) : ∑ c, f c = ∑ i, ∑ b, f (i, b) :=
  Fintype.sum_prod_type f

lemma dot_ind_left (a : Fin k → BlockCoord ℓ) (z : Vec k ℓ) :
    dot (ind a) z = ∑ i, z (i, a i) := by
  rw [dot, sum_coord]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single (a i)]
  · simp [ind]
  · intro b _ hb; simp [ind, hb]
  · simp

lemma dot_ind_eq_sum_supp (a : Fin k → BlockCoord ℓ) (z : Vec k ℓ) :
    dot (ind a) z = ∑ c ∈ supp a, z c := by
  rw [dot_ind_left, supp, Finset.sum_image (fun i _ j _ h => congrArg Prod.fst h)]

lemma dot_comm (y z : Vec k ℓ) : dot y z = dot z y := by
  simp [dot, mul_comm]

lemma dot_add_left (y y' z : Vec k ℓ) : dot (y + y') z = dot y z + dot y' z := by
  simp [dot, add_mul, Finset.sum_add_distrib]

lemma dot_add_right (y z z' : Vec k ℓ) : dot y (z + z') = dot y z + dot y z' := by
  simp [dot, mul_add, Finset.sum_add_distrib]

lemma dot_congr_suppIn {y z z' : Vec k ℓ} {J : Finset (Coord k ℓ)} (hy : SuppIn y J)
    (h : ∀ c ∈ J, z c = z' c) : dot y z = dot y z' := by
  refine Finset.sum_congr rfl fun c _ => ?_
  by_cases hc : c ∈ J
  · rw [h c hc]
  · rw [hy c hc]; simp

/-! ### Rows of the check matrix -/

/-- The block `k - 1`. -/
def lastBlock (hk : 0 < k) : Fin k := ⟨k - 1, by omega⟩

/-- The block `i` of a block-parity row. -/
def rowBlock (i : Fin (k - 1)) : Fin k := ⟨i, by omega⟩

lemma rowBlock_ne_last (hk : 0 < k) (i : Fin (k - 1)) : rowBlock i ≠ lastBlock hk := by
  intro h
  have := congrArg Fin.val h
  simp [rowBlock, lastBlock] at this
  omega

lemma checkMatrix_inl (i : Fin (k - 1)) (c : Coord k ℓ) :
    checkMatrix k ℓ (.inl i) c = if (c.1 : ℕ) = i ∨ (c.1 : ℕ) = k - 1 then 1 else 0 := rfl

lemma checkMatrix_inr (t : Fin ℓ) (c : Coord k ℓ) :
    checkMatrix k ℓ (.inr t) c = c.2 t := rfl

lemma row_inl_sum (hk : 0 < k) (i : Fin (k - 1)) (y : Vec k ℓ) :
    ∑ c, checkMatrix k ℓ (.inl i) c * y c =
      blockSum y (rowBlock i) + blockSum y (lastBlock hk) := by
  rw [sum_coord]
  have h : ∀ i' : Fin k, (∑ b, checkMatrix k ℓ (.inl i) (i', b) * y (i', b)) =
      if i' = rowBlock i ∨ i' = lastBlock hk then blockSum y i' else 0 := by
    intro i'
    have e : ((i' : ℕ) = i ∨ (i' : ℕ) = k - 1) ↔ (i' = rowBlock i ∨ i' = lastBlock hk) := by
      simp [rowBlock, lastBlock, Fin.ext_iff]
    by_cases hc : (i' : ℕ) = i ∨ (i' : ℕ) = k - 1
    · rw [if_pos (e.mp hc), blockSum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [checkMatrix_inl, if_pos hc, one_mul]
    · rw [if_neg (fun h => hc (e.mpr h))]
      refine Finset.sum_eq_zero fun b _ => ?_
      rw [checkMatrix_inl, if_neg hc, zero_mul]
  simp_rw [h]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  have : Finset.univ.filter (fun i' : Fin k => i' = rowBlock i ∨ i' = lastBlock hk) =
      {rowBlock i, lastBlock hk} := by
    ext x; simp
  rw [this, Finset.sum_pair (rowBlock_ne_last hk i)]

lemma row_inr_sum (t : Fin ℓ) (y : Vec k ℓ) :
    ∑ c, checkMatrix k ℓ (.inr t) c * y c = ∑ c, y c * c.2 t := by
  simp [checkMatrix_inr, mul_comm]

/-- Codewords: all block sums agree and the checksum vanishes. -/
lemma isCode_iff (hk : 0 < k) (y : Vec k ℓ) :
    IsCode y ↔ (∀ i, blockSum y i = blockSum y (lastBlock hk)) ∧
      ∀ t : Fin ℓ, ∑ c, y c * c.2 t = 0 := by
  constructor
  · intro h
    refine ⟨fun i => ?_, fun t => by rw [← row_inr_sum]; exact h (.inr t)⟩
    by_cases hi : (i : ℕ) = k - 1
    · congr 1; exact Fin.ext hi
    · have := h (.inl ⟨i, by omega⟩)
      rw [row_inl_sum hk] at this
      have e : rowBlock (⟨i, by omega⟩ : Fin (k - 1)) = i := Fin.ext rfl
      rw [e] at this
      exact zmod2_eq_of_add_eq_zero this
  · rintro ⟨h1, h2⟩ (i | t)
    · rw [row_inl_sum hk, h1, zmod2_add_self]
    · rw [row_inr_sum]; exact h2 t

lemma IsCode.add {y y' : Vec k ℓ} (h : IsCode y) (h' : IsCode y') : IsCode (y + y') := by
  intro j
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, h j, h' j, add_zero]

lemma IsCode.blockSum_eq (hk : 0 < k) {y : Vec k ℓ} (h : IsCode y) (i i' : Fin k) :
    blockSum y i = blockSum y i' := by
  have := (isCode_iff hk y).mp h
  rw [this.1 i, this.1 i']

lemma blockSum_add (y y' : Vec k ℓ) (i : Fin k) :
    blockSum (y + y') i = blockSum y i + blockSum y' i := by
  simp [blockSum, Finset.sum_add_distrib]

lemma blockSum_ind (a : Fin k → BlockCoord ℓ) (i : Fin k) : blockSum (ind a) i = 1 := by
  rw [blockSum, Finset.sum_eq_single (a i)]
  · simp [ind]
  · intro b _ hb; simp [ind, hb]
  · simp

lemma isCode_ind (hk : 0 < k) {a : Fin k → BlockCoord ℓ} (ha : IsAddress a) :
    IsCode (ind a) := by
  rw [isCode_iff hk]
  refine ⟨fun i => by rw [blockSum_ind, blockSum_ind], fun t => ?_⟩
  have : ∑ c, ind a c * c.2 t = dot (ind a) (fun c => c.2 t) := rfl
  rw [this, dot_ind_left]
  have := congrFun ha t
  simpa [Finset.sum_apply] using this

/-- Each row of `B` meets every address in an even number of coordinates. -/
lemma sum_row_supp (hk : 0 < k) {a : Fin k → BlockCoord ℓ} (ha : IsAddress a) (j : Row k ℓ) :
    ∑ i, checkMatrix k ℓ j (i, a i) = 0 := by
  have := isCode_ind hk ha j
  have e : ∑ c, checkMatrix k ℓ j c * ind a c = dot (ind a) (fun c => checkMatrix k ℓ j c) := by
    rw [dot]; simp [mul_comm]
  rw [e, dot_ind_left] at this
  exact this

/-! ### Short codewords -/

/-- The support of a vector as a finset. -/
def vsupp (y : Vec k ℓ) : Finset (Coord k ℓ) := Finset.univ.filter fun c => y c ≠ 0

lemma vsupp_subset {y : Vec k ℓ} {J : Finset (Coord k ℓ)} (h : SuppIn y J) : vsupp y ⊆ J := by
  intro c hc
  by_contra h'
  exact (Finset.mem_filter.mp hc).2 (h c h')

lemma blockSum_eq_card (y : Vec k ℓ) (i : Fin k) :
    blockSum y i = ((Finset.univ.filter fun b => y (i, b) ≠ 0).card : ZMod 2) := by
  rw [blockSum, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun b _ => ?_
  rcases zmod2_eq_zero_or_one (y (i, b)) with h | h <;> simp [h]

lemma card_vsupp (y : Vec k ℓ) :
    (vsupp y).card = ∑ i, (Finset.univ.filter fun b => y (i, b) ≠ 0).card := by
  rw [vsupp, ← Finset.card_sigma]
  refine Finset.card_bij (fun c _ => ⟨c.1, c.2⟩) ?_ ?_ ?_
  · intro c hc; simpa using hc
  · intro c _ c' _ h
    simp only [Sigma.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    exact Prod.ext h1 (eq_of_heq h2)
  · rintro ⟨i, b⟩ hb
    exact ⟨(i, b), by simpa using hb, rfl⟩

lemma card_odd_of_zmod (n : ℕ) (h : (n : ZMod 2) = 1) : n % 2 = 1 := by
  rcases Nat.mod_two_eq_zero_or_one n with h' | h'
  · exfalso
    have : (n : ZMod 2) = 0 := by
      rw [ZMod.natCast_eq_zero_iff_even]; exact Nat.even_iff.mpr h'
    rw [this] at h; exact zero_ne_one h
  · exact h'

/-- A block-odd codeword supported in at most `k + 1` coordinates is an address. -/
lemma exists_address_of_odd (hk : 0 < k) {y : Vec k ℓ} {J : Finset (Coord k ℓ)}
    (hy : IsCode y) (hodd : ∀ i, blockSum y i = 1) (hJ : SuppIn y J) (hcard : J.card ≤ k + 1) :
    ∃ a, IsAddress a ∧ y = ind a := by
  set S : Fin k → Finset (BlockCoord ℓ) := fun i => Finset.univ.filter fun b => y (i, b) ≠ 0
  have hS : ∀ i, (S i).card % 2 = 1 := fun i =>
    card_odd_of_zmod _ (by rw [← blockSum_eq_card]; exact hodd i)
  have hsum : ∑ i, (S i).card ≤ k + 1 := by
    rw [← card_vsupp]; exact (Finset.card_le_card (vsupp_subset hJ)).trans hcard
  have hone : ∀ i, (S i).card = 1 := by
    by_contra hne
    push Not at hne
    obtain ⟨i₀, hi₀⟩ := hne
    have h3 : 3 ≤ (S i₀).card := by
      have := hS i₀; have : (S i₀).card ≠ 0 := by omega
      omega
    have : ∑ i, (S i).card ≥ 3 + (k - 1) := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)]
      have : ∑ i ∈ Finset.univ.erase i₀, (S i).card ≥ ∑ i ∈ Finset.univ.erase i₀, 1 :=
        Finset.sum_le_sum fun i _ => by have := hS i; omega
      simp only [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_erase_of_mem
        (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at this
      omega
    omega
  choose a ha using fun i => Finset.card_eq_one.mp (hone i)
  have hy1 : ∀ i b, y (i, b) ≠ 0 ↔ b = a i := by
    intro i b
    have := ha i
    have hmem : b ∈ S i ↔ b = a i := by rw [this]; simp
    simpa [S] using hmem
  have hyeq : y = ind a := by
    funext c
    obtain ⟨i, b⟩ := c
    simp only [ind]
    by_cases hb : b = a i
    · rw [if_pos hb]; exact (zmod2_ne_zero_iff _).mp ((hy1 i b).mpr hb)
    · rw [if_neg hb]; by_contra h; exact hb ((hy1 i b).mp h)
  refine ⟨a, ?_, hyeq⟩
  funext t
  have := ((isCode_iff hk y).mp hy).2 t
  have e : ∑ c, y c * c.2 t = dot (ind a) (fun c => c.2 t) := by rw [hyeq]; rfl
  rw [e, dot_ind_left] at this
  simpa [Finset.sum_apply] using this

/-- At most one address is supported in a set of at most `k + 1` coordinates. -/
lemma address_unique {a a' : Fin k → BlockCoord ℓ} (ha : IsAddress a) (ha' : IsAddress a')
    {J : Finset (Coord k ℓ)} (hJ : J.card ≤ k + 1) (h : supp a ⊆ J) (h' : supp a' ⊆ J) :
    a = a' := by
  classical
  set D := Finset.univ.filter fun i => a i ≠ a' i
  have hunion : (supp a ∪ supp a').card = k + D.card := by
    have hdisj : supp a ∪ supp a' = supp a ∪ D.image (fun i => (i, a' i)) := by
      ext c
      simp only [Finset.mem_union, mem_supp_iff, Finset.mem_image, D, Finset.mem_filter,
        Finset.mem_univ, true_and]
      constructor
      · rintro (h | h)
        · exact Or.inl h
        · by_cases hc : a c.1 = c.2
          · exact Or.inl hc
          · exact Or.inr ⟨c.1, by rw [h]; exact hc, by rw [h]⟩
      · rintro (h | ⟨i, _, rfl⟩)
        · exact Or.inl h
        · exact Or.inr rfl
    rw [hdisj, Finset.card_union_of_disjoint, card_supp,
      Finset.card_image_of_injective _ (fun i j h => congrArg Prod.fst h)]
    rw [Finset.disjoint_left]
    intro c hc hc'
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hc'
    rw [mem_supp_iff] at hc
    exact (Finset.mem_filter.mp hi).2 hc
  have hD : D.card ≤ 1 := by
    have := Finset.card_le_card (Finset.union_subset h h')
    omega
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hD with h0 | h1
  · funext i
    by_contra hi
    have : i ∈ D := by simp [D, hi]
    rw [Finset.card_eq_zero] at h0
    simp [h0] at this
  · obtain ⟨i₀, hi₀⟩ := Finset.card_eq_one.mp h1
    have hoth : ∀ i, i ≠ i₀ → a i = a' i := by
      intro i hi
      by_contra hne
      have : i ∈ D := by simp [D, hne]
      rw [hi₀] at this
      exact hi (Finset.mem_singleton.mp this)
    exfalso
    have hs : a i₀ = a' i₀ := by
      have e1 := ha
      have e2 := ha'
      rw [IsAddress, ← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)] at e1 e2
      have : ∑ i ∈ Finset.univ.erase i₀, a i = ∑ i ∈ Finset.univ.erase i₀, a' i :=
        Finset.sum_congr rfl fun i hi => hoth i (Finset.ne_of_mem_erase hi)
      rw [this] at e1
      have := e1.trans e2.symm
      exact add_right_cancel this
    have : i₀ ∈ D := by rw [hi₀]; exact Finset.mem_singleton_self _
    exact (Finset.mem_filter.mp this).2 hs

end Lax119563Proofs.Matrix
