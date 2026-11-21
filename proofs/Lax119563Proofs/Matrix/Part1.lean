import Lax119563.MatrixCompiler
import Lax119563.PebbleGame
import Mathlib

/-! ### Formerly `Lax119563Proofs.Matrix.Codes` -/

section Matrix_Codes

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

lemma zmod2_eq_of_add_eq_zero {x y : ZMod 2} (h : x + y = 0) : x = y := by
  have := congrArg (· + y) h
  simpa [add_assoc, zmod2_add_self] using this

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

lemma dot_add_left (y y' z : Vec k ℓ) : dot (y + y') z = dot y z + dot y' z := by
  simp [dot, add_mul, Finset.sum_add_distrib]

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

end Matrix_Codes

/-! ### Formerly `Lax119563Proofs.Matrix.GameLemmas` -/

section Matrix_GameLemmas

/-!
# Generic facts about the bijective pebble game

* survival is antitone in the number of rounds;
* `Forces c S P`: from `S`, Spoiler can force within `c` rounds a state satisfying `P`
  (unless he wins earlier); this composes like a monad and turns into Spoiler wins;
* the basic Spoiler move: lift a pebble and place it on a chosen vertex of `G`.
-/

open Lax119563.ColoredGraphs Lax119563.PebbleGame

namespace Lax119563Proofs.Matrix

variable {m : ℕ} {G H : ColoredGraph}

lemma survivesFrom_succ {r : ℕ} {S : GameState m G H} (h : SurvivesFrom G H (r + 1) S) :
    SurvivesFrom G H r S := by
  induction r generalizing S with
  | zero => trivial
  | succ r ih =>
    intro i
    obtain ⟨f, hf⟩ := h i
    exact ⟨f, fun p => ⟨(hf p).1, ih (hf p).2⟩⟩

lemma survivesFrom_mono {r r' : ℕ} (hr : r ≤ r') {S : GameState m G H}
    (h : SurvivesFrom G H r' S) : SurvivesFrom G H r S := by
  induction hr with
  | refl => exact h
  | step _ ih => exact ih (survivesFrom_succ h)

/-- Spoiler wins from `S` within `r` rounds. -/
def SWins (r : ℕ) (S : GameState m G H) : Prop := ¬ SurvivesFrom G H r S

lemma SWins.mono {r r' : ℕ} (hr : r ≤ r') {S : GameState m G H} (h : SWins r S) :
    SWins r' S := fun h' => h (survivesFrom_mono hr h')

/-- From `S`, Spoiler can force within `c` rounds a state satisfying `P`, or win. -/
def Forces (c : ℕ) (S : GameState m G H) (P : GameState m G H → Prop) : Prop :=
  ∀ r, (∀ S', P S' → SWins r S') → SWins (r + c) S

lemma Forces.ret {S : GameState m G H} {P : GameState m G H → Prop} (h : P S) : Forces 0 S P :=
  fun _ hr => hr S h

lemma Forces.bind {c d : ℕ} {S : GameState m G H} {P Q : GameState m G H → Prop}
    (h : Forces c S P) (h' : ∀ S', P S' → Forces d S' Q) : Forces (c + d) S Q := by
  intro r hr
  have := h (r + d) fun S' hS' => h' S' hS' r hr
  rwa [Nat.add_comm c d, ← Nat.add_assoc]

lemma Forces.mono {c c' : ℕ} (hc : c ≤ c') {S : GameState m G H} {P : GameState m G H → Prop}
    (h : Forces c S P) : Forces c' S P :=
  fun r hr => (h r hr).mono (Nat.add_le_add_left hc r)

lemma Forces.weaken {c : ℕ} {S : GameState m G H} {P Q : GameState m G H → Prop}
    (h : Forces c S P) (hPQ : ∀ S', P S' → Q S') : Forces c S Q :=
  fun r hr => h r fun S' hS' => hr S' (hPQ S' hS')

/-- Spoiler lifts pebble `i` and places it on `p`; Duplicator answers with some `q`, and
unless the result is not a partial isomorphism (a win), the game continues from there. -/
lemma Forces.place (S : GameState m G H) (i : Fin m) (p : Fin G.n) :
    Forces 1 S fun S' => ∃ q, S' = Function.update S i (some (p, q)) ∧ IsPartialIso G H S' := by
  intro r hr hS
  obtain ⟨f, hf⟩ := hS i
  by_cases hpi : IsPartialIso G H (Function.update S i (some (p, f p)))
  · exact hr _ ⟨f p, rfl, hpi⟩ (hf p).2
  · exact hpi (hf p).1

end Lax119563Proofs.Matrix

end Matrix_GameLemmas

/-! ### Formerly `Lax119563Proofs.Matrix.ListGraph` -/

section Matrix_ListGraph

/-!
# Colored graphs given by a list of vertex names

A colored graph whose vertices are the entries of a duplicate-free list of names: vertex `i`
is the `i`-th name, adjacency is a relation on names, and the color of a vertex is the
position of the first name of its class in the list. In particular colors are bounded by the
number of vertices, and two vertices have the same color iff their names have the same class.
-/

open Lax119563.ColoredGraphs

namespace Lax119563Proofs.Matrix

variable {α β : Type*} [DecidableEq β]

/-- The colored graph on the names of `L`. -/
@[reducible] def listGraph (L : List α) (adj : α → α → Prop) [DecidableRel adj] (hsymm : ∀ x y, adj x y → adj y x)
    (hirr : ∀ x, ¬ adj x x) (cls : α → β) : ColoredGraph where
  n := L.length
  graph :=
    { Adj := fun i j => adj L[i] L[j]
      symm := ⟨fun _ _ h => hsymm _ _ h⟩
      loopless := ⟨fun _ h => hirr _ h⟩ }
  color := fun i => L.findIdx fun x => decide (cls x = cls L[i])

variable (L : List α) (adj : α → α → Prop) [DecidableRel adj]
  (hsymm : ∀ x y, adj x y → adj y x) (hirr : ∀ x, ¬ adj x x) (cls : α → β)

@[simp] lemma listGraph_n : (listGraph L adj hsymm hirr cls).n = L.length := rfl

lemma listGraph_color_eq_iff (i j : Fin (listGraph L adj hsymm hirr cls).n) :
    (listGraph L adj hsymm hirr cls).color i = (listGraph L adj hsymm hirr cls).color j ↔
      cls (L[(i : ℕ)]'i.2) = cls (L[(j : ℕ)]'j.2) := by
  constructor
  · intro h
    change List.findIdx _ L = List.findIdx _ L at h
    have hi := List.findIdx_lt_length_of_exists
      (p := fun x => decide (cls x = cls (L[(i : ℕ)]'i.2)))
      ⟨L[(i : ℕ)]'i.2, List.getElem_mem _, by simp⟩
    have h1 := List.findIdx_getElem (w := hi)
    have h2 := List.findIdx_getElem (p := fun x => decide (cls x = cls (L[(j : ℕ)]'j.2)))
      (w := h ▸ hi)
    simp only [decide_eq_true_eq] at h1 h2
    have : L[L.findIdx fun x => decide (cls x = cls (L[(i : ℕ)]'i.2))]'hi =
        L[L.findIdx fun x => decide (cls x = cls (L[(j : ℕ)]'j.2))]'(h ▸ hi) := by
      congr 1
    rw [← h1, ← h2, this]
  · intro h
    simp only [listGraph, Fin.getElem_fin]
    exact congrArg (fun b => L.findIdx fun x => decide (cls x = b)) h

end Lax119563Proofs.Matrix

end Matrix_ListGraph

/-! ### Formerly `Lax119563Proofs.Matrix.Seeds` -/

section Matrix_Seeds

/-!
# Block-induced permutations, partial seeds and row-space duality

* the action of block-induced permutations on vectors and addresses,
* the extension of partial seeds (Lemma "Extending partial seeds"),
* the duality between the row space of the check matrix and short codewords.
-/

open Lax119563.ImplicitParitySystems Lax119563.MatrixCompiler

namespace Lax119563Proofs.Matrix

variable {k ℓ : ℕ}

/-! ### Block-induced permutations -/

/-- A block-induced permutation as an equivalence of coordinates. -/
def bpEquiv (P : BlockPerm k ℓ) : Coord k ℓ ≃ Coord k ℓ where
  toFun := P.apply
  invFun c := (P.perm.symm c.1, c.2 - P.shift (P.perm.symm c.1))
  left_inv c := by simp [BlockPerm.apply]
  right_inv c := by simp [BlockPerm.apply]

@[simp] lemma bpEquiv_apply (P : BlockPerm k ℓ) (c : Coord k ℓ) :
    bpEquiv P c = P.apply c := rfl

lemma bp_apply_injective (P : BlockPerm k ℓ) : Function.Injective P.apply :=
  (bpEquiv P).injective

/-- The image `P y` of a vector, `(P y)(P c) = y c`. -/
def permVec (P : BlockPerm k ℓ) (y : Vec k ℓ) : Vec k ℓ := fun c => y ((bpEquiv P).symm c)

lemma dot_permVec (P : BlockPerm k ℓ) (y z : Vec k ℓ) :
    dot (permVec P y) z = ∑ c, y c * z (P.apply c) := by
  rw [dot, ← Equiv.sum_comp (bpEquiv P)]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [permVec, bpEquiv_apply]
  rw [← bpEquiv_apply, Equiv.symm_apply_apply]

lemma blockSum_permVec (P : BlockPerm k ℓ) (y : Vec k ℓ) (i : Fin k) :
    blockSum (permVec P y) (P.perm i) = blockSum y i := by
  simp only [blockSum, permVec, bpEquiv, Equiv.coe_fn_symm_mk, Equiv.symm_apply_apply]
  exact Fintype.sum_equiv (Equiv.subRight (P.shift i)) _ _ (fun b => rfl)

lemma blockSum_permVec' (P : BlockPerm k ℓ) (y : Vec k ℓ) (i : Fin k) :
    blockSum (permVec P y) i = blockSum y (P.perm.symm i) := by
  rw [← blockSum_permVec P y (P.perm.symm i), Equiv.apply_symm_apply]

lemma isCode_permVec (hk : 0 < k) (P : BlockPerm k ℓ) {y : Vec k ℓ} (hy : IsCode y) :
    IsCode (permVec P y) := by
  rw [isCode_iff hk] at hy ⊢
  obtain ⟨h1, h2⟩ := hy
  refine ⟨fun i => by rw [blockSum_permVec', blockSum_permVec', h1 (P.perm.symm i), h1 (P.perm.symm _)], fun t => ?_⟩
  have e : ∑ c, permVec P y c * c.2 t = dot (permVec P y) (fun c => c.2 t) := rfl
  rw [e, dot_permVec]
  simp only [BlockPerm.apply, Pi.add_apply, mul_add, Finset.sum_add_distrib, h2 t, zero_add]
  rw [sum_coord]
  have : ∀ i, ∑ b, y (i, b) * P.shift i t = blockSum y i * P.shift i t := by
    intro i; rw [blockSum, Finset.sum_mul]
  simp_rw [this, h1]
  rw [← Finset.mul_sum]
  have := congrFun P.sum_shift t
  simp only [Finset.sum_apply, Pi.zero_apply] at this
  rw [this, mul_zero]

lemma suppIn_permVec (P : BlockPerm k ℓ) {y : Vec k ℓ} {J : Finset (Coord k ℓ)}
    (hy : SuppIn y J) : SuppIn (permVec P y) (J.image P.apply) := by
  intro c hc
  apply hy
  intro hJ
  apply hc
  exact Finset.mem_image.mpr ⟨_, hJ, by simp [← bpEquiv_apply]⟩

lemma isAddress_act (P : BlockPerm k ℓ) {a : Fin k → BlockCoord ℓ} (ha : IsAddress a) :
    IsAddress (P.act a) := by
  unfold IsAddress BlockPerm.act
  rw [Finset.sum_add_distrib]
  rw [Equiv.sum_comp P.perm.symm a, Equiv.sum_comp P.perm.symm P.shift, ha, P.sum_shift,
    add_zero]

lemma supp_act (P : BlockPerm k ℓ) (a : Fin k → BlockCoord ℓ) :
    supp (P.act a) = (supp a).image P.apply := by
  ext c
  simp only [mem_supp_iff, Finset.mem_image, BlockPerm.act, BlockPerm.apply]
  constructor
  · intro h
    refine ⟨(P.perm.symm c.1, a (P.perm.symm c.1)), rfl, ?_⟩
    ext <;> simp [← h]
  · rintro ⟨d, hd, rfl⟩
    simp [hd]

lemma ind_act (P : BlockPerm k ℓ) (a : Fin k → BlockCoord ℓ) :
    ind (P.act a) = permVec P (ind a) := by
  funext c
  simp only [ind, permVec, bpEquiv, Equiv.coe_fn_symm_mk, BlockPerm.act]
  congr 1
  apply propext
  constructor
  · intro h; rw [h]; simp
  · intro h; rw [← h]; simp

/-- The value `(P a) · z` of a permuted address as a sum over the support of `a`. -/
lemma dot_ind_act (P : BlockPerm k ℓ) (a : Fin k → BlockCoord ℓ) (z : Vec k ℓ) :
    dot (ind (P.act a)) z = ∑ i, z (P.apply (i, a i)) := by
  rw [ind_act, dot_permVec, sum_coord]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single (a i)]
  · simp [ind]
  · intro b _ hb; simp [ind, hb]
  · simp

/-! ### Partial seeds -/

/-- The seed `z` annihilates every block-even codeword supported in `J`. -/
def EvenKills (z : Vec k ℓ) (J : Finset (Coord k ℓ)) : Prop :=
  ∀ y, IsCode y → (∀ i, blockSum y i = 0) → SuppIn y J → dot y z = 0

lemma EvenKills.mono {z : Vec k ℓ} {J J' : Finset (Coord k ℓ)} (h : EvenKills z J)
    (hJ : J' ⊆ J) : EvenKills z J' :=
  fun y hy he hs => h y hy he fun c hc => hs c fun h' => hc (hJ h')

lemma dot_update (y z : Vec k ℓ) (c : Coord k ℓ) (β : ZMod 2) :
    dot y (Function.update z c β) = dot y (Function.update z c 0) + y c * β := by
  simp only [dot]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ c), ← Finset.add_sum_erase _ _
    (Finset.mem_univ c)]
  simp only [Function.update_self]
  have : ∑ x ∈ Finset.univ.erase c, y x * Function.update z c β x =
      ∑ x ∈ Finset.univ.erase c, y x * Function.update z c 0 x :=
    Finset.sum_congr rfl fun x hx => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hx),
        Function.update_of_ne (Finset.ne_of_mem_erase hx)]
  rw [this]; ring

lemma suppIn_insert_of_zero {y : Vec k ℓ} {J : Finset (Coord k ℓ)} {c : Coord k ℓ}
    (h : SuppIn y (insert c J)) (hc : y c = 0) : SuppIn y J := by
  intro d hd
  by_cases hdc : d = c
  · rw [hdc]; exact hc
  · exact h d (by simp [hdc, hd])

/-- **Extending partial seeds.** A seed on `J` annihilating block-even codewords extends to
`J ∪ {c}`, with any prescribed value on the address supported there that uses `c`. -/
lemma extend_seed (hk : 0 < k) {J : Finset (Coord k ℓ)} {c : Coord k ℓ} (hcJ : c ∉ J)
    (hcard : (insert c J).card ≤ k + 1) {z : Vec k ℓ} (hz : EvenKills z J) (p : ZMod 2) :
    ∃ β : ZMod 2, EvenKills (Function.update z c β) (insert c J) ∧
      ∀ a, IsAddress a → supp a ⊆ insert c J → c ∈ supp a →
        dot (ind a) (Function.update z c β) = p := by
  classical
  -- block-even codewords not using `c` are handled by `hz`
  have hold : ∀ β : ZMod 2, ∀ y, IsCode y → (∀ i, blockSum y i = 0) →
      SuppIn y (insert c J) → y c = 0 → dot y (Function.update z c β) = 0 := by
    intro β y hy he hs hc
    rw [dot_update, hc, zero_mul, add_zero]
    have hs' := suppIn_insert_of_zero hs hc
    rw [dot_congr_suppIn hs' (z' := z) fun d hd =>
      Function.update_of_ne (fun h => hcJ (by rw [← h]; exact hd)) _ _]
    exact hz y hy he hs'
  by_cases h0 : ∃ y0, IsCode y0 ∧ (∀ i, blockSum y0 i = 0) ∧ SuppIn y0 (insert c J) ∧ y0 c = 1
  · obtain ⟨y0, hy0, he0, hs0, hc0⟩ := h0
    refine ⟨dot y0 (Function.update z c 0), fun y hy he hs => ?_, fun a ha hsa hca => ?_⟩
    · rcases zmod2_eq_zero_or_one (y c) with hc | hc
      · exact hold _ y hy he hs hc
      · have hsum := hold (dot y0 (Function.update z c 0)) (y + y0) (hy.add hy0)
          (fun i => by rw [blockSum_add, he, he0, add_zero])
          (fun d hd => by simp [hs d hd, hs0 d hd]) (by simp [hc, hc0, zmod2_add_self])
        rw [dot_add_left] at hsum
        have h2 : dot y0 (Function.update z c (dot y0 (Function.update z c 0))) = 0 := by
          rw [dot_update, hc0, one_mul, zmod2_add_self]
        rw [h2, add_zero] at hsum
        exact hsum
    · exfalso
      obtain ⟨a', ha', he'⟩ := exists_address_of_odd hk (y := ind a + y0) (J := insert c J)
        ((isCode_ind hk ha).add hy0) (fun i => by rw [blockSum_add, blockSum_ind, he0, add_zero])
        (fun d hd => by
          have : ind a d = 0 := ind_apply_eq_zero.mpr fun h => hd (hsa h)
          simp [this, hs0 d hd]) hcard
      have hsa' : supp a' ⊆ insert c J := by
        rw [← suppIn_ind, ← he']
        intro d hd
        have : ind a d = 0 := ind_apply_eq_zero.mpr fun h => hd (hsa h)
        simp [this, hs0 d hd]
      have := address_unique ha ha' hcard hsa hsa'
      subst this
      have := congrFun he' c
      simp only [Pi.add_apply, hc0] at this
      have h' : ind a c + 1 = ind a c + 0 := by rw [this, add_zero]
      exact one_ne_zero (add_left_cancel h')
  · push Not at h0
    have heven : EvenKills (Function.update z c 0) (insert c J) ∧
        ∀ β, EvenKills (Function.update z c β) (insert c J) := by
      refine ⟨fun y hy he hs => hold 0 y hy he hs ?_, fun β y hy he hs => hold β y hy he hs ?_⟩
      · rcases zmod2_eq_zero_or_one (y c) with hc | hc
        · exact hc
        · exact absurd hc (h0 y hy he hs)
      · rcases zmod2_eq_zero_or_one (y c) with hc | hc
        · exact hc
        · exact absurd hc (h0 y hy he hs)
    by_cases h1 : ∃ a, IsAddress a ∧ supp a ⊆ insert c J ∧ c ∈ supp a
    · obtain ⟨a, ha, hsa, hca⟩ := h1
      refine ⟨p + dot (ind a) (Function.update z c 0), heven.2 _, fun a' ha' hsa' hca' => ?_⟩
      have := address_unique ha ha' hcard hsa hsa'
      subst this
      rw [dot_update, ind_apply_eq_one.mpr hca, one_mul, add_comm p, ← add_assoc,
        zmod2_add_self, zero_add]
    · push Not at h1
      exact ⟨0, heven.2 0, fun a ha hsa hca => absurd hca (h1 a ha hsa)⟩

/-! ### Duality between the row space and short codewords -/

/-- A vector orthogonal to all codewords supported in `J` agrees on `J` with a sum of rows of
the check matrix. -/
lemma exists_rowComb (J : Finset (Coord k ℓ)) (t : Vec k ℓ)
    (h : ∀ y, IsCode y → SuppIn y J → dot y t = 0) :
    ∃ μ : Row k ℓ → ZMod 2, ∀ c ∈ J, ∑ j, μ j * checkMatrix k ℓ j c = t c := by
  classical
  let f : (J → ZMod 2) →ₗ[ZMod 2] (Row k ℓ → ZMod 2) :=
    { toFun := fun x j => ∑ c : J, checkMatrix k ℓ j c * x c
      map_add' := fun x x' => by
        funext j; simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun r x => by
        funext j; simp [Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => by ring }
  let φ : Module.Dual (ZMod 2) (J → ZMod 2) :=
    { toFun := fun x => ∑ c : J, t c * x c
      map_add' := fun x x' => by simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun r x => by
        simp [Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => by ring }
  let ext : (J → ZMod 2) → Vec k ℓ := fun x c => if hc : c ∈ J then x ⟨c, hc⟩ else 0
  have hext_supp : ∀ x, SuppIn (ext x) J := fun x c hc => by simp [ext, hc]
  have hext_sum : ∀ (x : J → ZMod 2) (g : Coord k ℓ → ZMod 2),
      ∑ c : J, g c * x c = ∑ c, g c * ext x c := by
    intro x g
    rw [← Finset.sum_subset (Finset.subset_univ J) (fun c _ hc => by simp [ext, hc])]
    rw [← Finset.sum_coe_sort J]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp [ext]
  have hφ : φ ∈ (LinearMap.ker f).dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    intro x hx
    have hcode : IsCode (ext x) := by
      intro j
      have := congrFun (LinearMap.mem_ker.mp hx) j
      simp only [f, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at this
      rw [hext_sum x (fun c => checkMatrix k ℓ j c)] at this
      exact this
    have := h _ hcode (hext_supp x)
    show ∑ c : J, t c * x c = 0
    rw [hext_sum x (fun c => t c)]
    rw [← this, dot]
    simp [mul_comm]
  rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at hφ
  obtain ⟨ψ, hψ⟩ := hφ
  refine ⟨fun j => ψ (fun j' => if j = j' then 1 else 0), fun c hc => ?_⟩
  have h1 := LinearMap.congr_fun hψ (fun c' => if c' = ⟨c, hc⟩ then 1 else 0)
  rw [LinearMap.dualMap_apply] at h1
  have h2 : f (fun c' => if c' = ⟨c, hc⟩ then 1 else 0) = fun j => checkMatrix k ℓ j c := by
    funext j
    simp only [f, LinearMap.coe_mk, AddHom.coe_mk, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [h2, LinearMap.pi_apply_eq_sum_univ] at h1
  change _ = ∑ c' : J, t c' * (if c' = ⟨c, hc⟩ then 1 else 0) at h1
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h1
  rw [← h1]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_eq_mul, mul_comm]

end Lax119563Proofs.Matrix

end Matrix_Seeds

/-! ### Formerly `Lax119563Proofs.Matrix.Construction` -/

section Matrix_Construction

/-!
# The matrix construction

The explicit graph pair `matrixGraph I 0, matrixGraph I 1` of the matrix compiler.

## Parameters

* `M = k - 1 + ℓ` check rows; row `j < k - 1` is the block-parity check comparing block `j`
  with block `k - 1`, row `k - 1 + t` is the checksum check of bit `t`
  (`finSumFinEquiv` order of `Fin (k - 1) ⊕ Fin ℓ`).
* `R = k + 1` repetitions, hence `N = R * M` *steps*; step `σ < N` processes row `σ % M`.
  `ent σ c` is the entry of that row at the coordinate `c`.

## Vertex classes and names

A vertex name is a pair `(X, (s, t))` of a class `X : Cls` and a label `(s, t)`; classes with
one bit use labels `(s, 0)`.

* `coord v c` (`c ∈ 𝔠_v`): labels `(0,0), (1,0)`; only `(0,0)` if `v` is initialized.
* `sum e c`, `junc e c` (`e` ternary, `c ∈ 𝔠_e`): one and two bits; `junc e c` with label
  `(s, t)` is the junction vertex `(s, t, s + t)`.
* `link e c` (`c ∈ 𝔠_e`): one bit.
* `track e σ c`, `upd e σ c` (`σ < N`, `c ∈ 𝔠_e`, `ent σ c = 1`): one and two bits; the update
  with label `(s, t)` is the update vertex `(s, t, s + t)`, and `track e σ c` is the track
  leaving it.
* `coef e σ` (`σ < N`, row of `σ` nonzero on `𝔠_e`): one bit.

The track of column `c` at stage `σ` (`trackAt`) is `track e σ' c` for the last step
`σ' < σ` with `ent σ' c = 1`, and the start class (`coord u (σ_e c)` for binary `e`,
`sum e c` for ternary `e`) if there is none.

## Edges

Every edge joins a *hub* (update, junction, link) with a vertex of one of its neighbor
classes whose label is prescribed:
* `upd e σ c` `(s, t)`: `trackAt e c σ` with label `s`, `track e σ c` with label `t`,
  `coef e σ` with label `s + t`;
* `junc e c` `(s, t)`: `coord u (σ_e c)` with label `s`, `coord v (τ_e c)` with label `t`,
  `sum e c` with label `s + t`;
* `link e c` `(s)`: `trackAt e c N` and the end class `coord w (π_e c)` (resp.
  `coord v (τ_e c)` for binary `e`), both with label `s`.

Labels are compared as *effective labels*: in `G_ε`, the single vertex of an initialized
coordinate class `coord v c` has effective label `ε · ι(v)` if `c` lies in block `0` and `0`
otherwise.

## Numbering

The vertices of both graphs are the entries of `vertexList I`, in this order:
1. for each location `v` and each `c ∈ 𝔠_v` (in the order of `coordList`): its coordinate
   vertices;
2. for each schema `e` (in list order): for each `c ∈ 𝔠_e`: `sum`, `junc` (ternary only) and
   `link` vertices; then for each step `σ < N`: the `coef` vertices (if present), and for each
   `c ∈ 𝔠_e` with `ent σ c = 1` the `track` and the `upd` vertices.
Labels are listed as `(0,0), (1,0)` resp. `(0,0), (0,1), (1,0), (1,1)`. The color of a vertex
is the position in this list of the first vertex of its class.
-/

open Lax119563.ImplicitParitySystems Lax119563.MatrixCompiler Lax119563.ColoredGraphs

namespace Lax119563Proofs.Matrix

variable {k ℓ w : ℕ}

/-! ### Schema accessors -/

/-- Whether a schema is ternary. -/
def isTern : Schema k ℓ w → Bool
  | .binary .. => false
  | .ternary .. => true

/-- The first argument location. -/
def locU : Schema k ℓ w → Fin w
  | .binary u .. => u
  | .ternary u .. => u

/-- The first argument permutation. -/
def permU : Schema k ℓ w → BlockPerm k ℓ
  | .binary _ _ _ σ _ => σ
  | .ternary _ _ _ _ σ _ _ => σ

/-- The second argument location. -/
def locV : Schema k ℓ w → Fin w
  | .binary _ v .. => v
  | .ternary _ v .. => v

/-- The second argument permutation. -/
def permV : Schema k ℓ w → BlockPerm k ℓ
  | .binary _ _ _ _ τ => τ
  | .ternary _ _ _ _ _ τ _ => τ

/-- The location at the end of the strip: the second argument of a binary schema, the third
argument of a ternary schema. -/
def locEnd : Schema k ℓ w → Fin w
  | .binary _ v .. => v
  | .ternary _ _ w' .. => w'

/-- The permutation at the end of the strip. -/
def permEnd : Schema k ℓ w → BlockPerm k ℓ
  | .binary _ _ _ _ τ => τ
  | .ternary _ _ _ _ _ _ π => π

/-! ### Steps and check rows -/

/-- The number `N = (k + 1)(k - 1 + ℓ)` of steps of a strip. -/
def numSteps (k ℓ : ℕ) : ℕ := (k + 1) * (k - 1 + ℓ)

/-- The check row processed by step `σ` (as an element of `Fin (k - 1) ⊕ Fin ℓ`). -/
def stepRow (h : 0 < k - 1 + ℓ) (σ : ℕ) : Fin (k - 1) ⊕ Fin ℓ :=
  finSumFinEquiv.symm ⟨σ % (k - 1 + ℓ), Nat.mod_lt _ h⟩

/-- The entry of the row of step `σ` at the coordinate `c`. -/
def ent (σ : ℕ) (c : Coord k ℓ) : ZMod 2 :=
  if h : 0 < k - 1 + ℓ then checkMatrix k ℓ (stepRow h σ) c else 0

/-- The last step before `σ` whose row is nonzero at `c`. -/
def prevStep (c : Coord k ℓ) : ℕ → Option ℕ
  | 0 => none
  | σ + 1 => if ent σ c ≠ 0 then some σ else prevStep c σ

/-! ### Classes and names -/

/-- Vertex classes. -/
inductive Cls (k ℓ w E : ℕ)
  | coord (v : Fin w) (c : Coord k ℓ)
  | sum (e : Fin E) (c : Coord k ℓ)
  | junc (e : Fin E) (c : Coord k ℓ)
  | link (e : Fin E) (c : Coord k ℓ)
  | track (e : Fin E) (σ : ℕ) (c : Coord k ℓ)
  | upd (e : Fin E) (σ : ℕ) (c : Coord k ℓ)
  | coef (e : Fin E) (σ : ℕ)
  deriving DecidableEq

variable (I : ImplicitParitySystem k ℓ)

/-- The classes of `I`. -/
abbrev ICls := Cls k ℓ I.numLocations I.schemas.length

/-- Labels. -/
abbrev Lab := ZMod 2 × ZMod 2

/-- Vertex names: a class and a label. -/
abbrev VName := ICls I × Lab

/-- The schema with index `e`. -/
def sch (e : Fin I.schemas.length) : Schema k ℓ I.numLocations := I.schemas.get e

/-- The coordinate domain of schema `e`. -/
def dom (e : Fin I.schemas.length) : Finset (Coord k ℓ) := (sch I e).domain

/-- The class at which the strip of column `c` starts. -/
def startCls (e : Fin I.schemas.length) (c : Coord k ℓ) : ICls I :=
  if isTern (sch I e) then .sum e c else .coord (locU (sch I e)) ((permU (sch I e)).apply c)

/-- The class at which the strip of column `c` ends. -/
def endCls (e : Fin I.schemas.length) (c : Coord k ℓ) : ICls I :=
  .coord (locEnd (sch I e)) ((permEnd (sch I e)).apply c)

/-- The track class of column `c` at stage `σ`. -/
def trackAt (e : Fin I.schemas.length) (c : Coord k ℓ) (σ : ℕ) : ICls I :=
  match prevStep c σ with
  | none => startCls I e c
  | some σ' => .track e σ' c

/-- The initial seed: `ι(v)` on block `0` and `0` elsewhere (and `0` if `v` is
uninitialized). -/
def initSeed (v : Fin I.numLocations) (c : Coord k ℓ) : ZMod 2 :=
  match I.init v with
  | some b => if (c.1 : ℕ) = 0 then b else 0
  | none => 0

/-- The label offset of a class in `G₁`. -/
def initBit : ICls I → ZMod 2
  | .coord v c => initSeed I v c
  | _ => 0

/-- The effective label of a name in `G_ε`. -/
def eff (ε : ZMod 2) (x : VName I) : Lab := (x.2.1 + ε * initBit I x.1, x.2.2)

/-- The neighbor relation of hubs: `hubB X l Y m` says that a hub of class `X` with effective
label `l` is adjacent to a vertex of class `Y` with effective label `m`. -/
def hubB (X : ICls I) (l : Lab) (Y : ICls I) (m : Lab) : Bool :=
  match X with
  | .upd e σ c =>
      (decide (Y = trackAt I e c σ) && decide (m.1 = l.1)) ||
      (decide (Y = .track e σ c) && decide (m.1 = l.2)) ||
      (decide (Y = .coef e σ) && decide (m.1 = l.1 + l.2))
  | .junc e c =>
      (decide (Y = .coord (locU (sch I e)) ((permU (sch I e)).apply c)) && decide (m.1 = l.1)) ||
      (decide (Y = .coord (locV (sch I e)) ((permV (sch I e)).apply c)) && decide (m.1 = l.2)) ||
      (decide (Y = .sum e c) && decide (m.1 = l.1 + l.2))
  | .link e c =>
      (decide (Y = trackAt I e c (numSteps k ℓ)) && decide (m.1 = l.1)) ||
      (decide (Y = endCls I e c) && decide (m.1 = l.1))
  | _ => false

/-- Adjacency in `G_ε`. -/
def adjN (ε : ZMod 2) (x y : VName I) : Prop :=
  hubB I x.1 (eff I ε x) y.1 (eff I ε y) = true ∨ hubB I y.1 (eff I ε y) x.1 (eff I ε x) = true

instance (ε : ZMod 2) : DecidableRel (adjN I ε) := fun _ _ => by
  unfold adjN; infer_instance

/-- Hubs. -/
def isHub : ICls I → Bool
  | .upd .. => true
  | .junc .. => true
  | .link .. => true
  | _ => false

lemma isHub_startCls (e : Fin I.schemas.length) (c : Coord k ℓ) :
    isHub I (startCls I e c) = false := by
  unfold startCls; split <;> rfl

lemma isHub_trackAt (e : Fin I.schemas.length) (c : Coord k ℓ) (σ : ℕ) :
    isHub I (trackAt I e c σ) = false := by
  unfold trackAt; split
  · exact isHub_startCls I e c
  · rfl

/-- Only hubs have neighbors through `hubB`, and these are not hubs. -/
lemma hubB_hub {X Y : ICls I} {l m : Lab} (h : hubB I X l Y m = true) :
    isHub I X = true ∧ isHub I Y = false := by
  cases X with
  | upd e σ c =>
    refine ⟨rfl, ?_⟩
    simp only [hubB, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ((⟨rfl, -⟩ | ⟨rfl, -⟩) | ⟨rfl, -⟩)
    · exact isHub_trackAt I e c σ
    · rfl
    · rfl
  | junc e c =>
    refine ⟨rfl, ?_⟩
    simp only [hubB, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ((⟨rfl, -⟩ | ⟨rfl, -⟩) | ⟨rfl, -⟩) <;> rfl
  | link e c =>
    refine ⟨rfl, ?_⟩
    simp only [hubB, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with (⟨rfl, -⟩ | ⟨rfl, -⟩)
    · exact isHub_trackAt I e c _
    · rfl
  | coord => simp [hubB] at h
  | sum => simp [hubB] at h
  | track => simp [hubB] at h
  | coef => simp [hubB] at h

lemma adjN_symm (ε : ZMod 2) (x y : VName I) (h : adjN I ε x y) : adjN I ε y x :=
  h.symm

lemma adjN_irrefl (ε : ZMod 2) (x : VName I) : ¬ adjN I ε x x := by
  rintro (h | h) <;>
  · have := hubB_hub I h
    rw [this.1] at this
    exact absurd this.2 (by decide)

/-! ### Valid names -/

/-- The classes present in the graphs. -/
def ClsValid : ICls I → Prop
  | .coord v c => c ∈ I.domain v
  | .sum e c => isTern (sch I e) = true ∧ c ∈ dom I e
  | .junc e c => isTern (sch I e) = true ∧ c ∈ dom I e
  | .link e c => c ∈ dom I e
  | .track e σ c => σ < numSteps k ℓ ∧ c ∈ dom I e ∧ ent σ c ≠ 0
  | .upd e σ c => σ < numSteps k ℓ ∧ c ∈ dom I e ∧ ent σ c ≠ 0
  | .coef e σ => σ < numSteps k ℓ ∧ ∃ c ∈ dom I e, ent σ c ≠ 0

/-- Classes with two label bits. -/
def twoBit : ICls I → Bool
  | .junc .. => true
  | .upd .. => true
  | _ => false

/-- Singleton classes: coordinate classes at initialized locations. -/
def isSingleton : ICls I → Bool
  | .coord v _ => (I.init v).isSome
  | _ => false

/-- The labels present in a class. -/
def LabelOK (X : ICls I) (l : Lab) : Prop :=
  (twoBit I X = false → l.2 = 0) ∧ (isSingleton I X = true → l.1 = 0)

/-- Valid vertex names. -/
def Valid (x : VName I) : Prop := ClsValid I x.1 ∧ LabelOK I x.1 x.2

/-! ### Enumerations -/

/-- All block coordinates. -/
def allBlockCoords : (ℓ : ℕ) → List (BlockCoord ℓ)
  | 0 => [fun i => i.elim0]
  | ℓ + 1 => (allBlockCoords ℓ).flatMap fun b => [Fin.cons 0 b, Fin.cons 1 b]

/-- All coordinates, block by block. -/
def allCoords (k ℓ : ℕ) : List (Coord k ℓ) :=
  (List.finRange k).flatMap fun i => (allBlockCoords ℓ).map fun b => (i, b)

/-- The coordinates of a domain, in the order of `allCoords`. -/
def coordList (D : Finset (Coord k ℓ)) : List (Coord k ℓ) := (allCoords k ℓ).filter (· ∈ D)

/-- One-bit labels. -/
def bits1 : List Lab := [(0, 0), (1, 0)]

/-- Two-bit labels. -/
def bits2 : List Lab := [(0, 0), (0, 1), (1, 0), (1, 1)]

/-- The vertices of the coordinate classes of location `v`. -/
def coordVerts (v : Fin I.numLocations) : List (VName I) :=
  (coordList (I.domain v)).flatMap fun c =>
    (if (I.init v).isSome then [((0 : ZMod 2), (0 : ZMod 2))] else bits1).map fun l =>
      (Cls.coord v c, l)

/-- The `sum`, `junc` and `link` vertices of column `c` of schema `e`. -/
def columnVerts (e : Fin I.schemas.length) (c : Coord k ℓ) : List (VName I) :=
  (if isTern (sch I e) then bits1.map (fun l => (Cls.sum e c, l)) ++
      bits2.map (fun l => (Cls.junc e c, l)) else []) ++
    bits1.map fun l => (Cls.link e c, l)

/-- The vertices of step `σ` of schema `e`. -/
def stepVerts (e : Fin I.schemas.length) (σ : ℕ) : List (VName I) :=
  (if ∃ c ∈ dom I e, ent σ c ≠ 0 then bits1.map fun l => (Cls.coef e σ, l) else []) ++
    ((coordList (dom I e)).filter fun c => ent σ c ≠ 0).flatMap fun c =>
      bits1.map (fun l => (Cls.track e σ c, l)) ++ bits2.map fun l => (Cls.upd e σ c, l)

/-- The vertices of the gadget of schema `e`. -/
def schemaVerts (e : Fin I.schemas.length) : List (VName I) :=
  (coordList (dom I e)).flatMap (columnVerts I e) ++
    (List.range (numSteps k ℓ)).flatMap (stepVerts I e)

/-- The vertex list shared by both graphs. -/
def vertexList : List (VName I) :=
  (List.finRange I.numLocations).flatMap (coordVerts I) ++
    (List.finRange I.schemas.length).flatMap (schemaVerts I)

/-- **The matrix compiler graph** `G_ε`. -/
abbrev matrixGraph (ε : ZMod 2) : ColoredGraph :=
  listGraph (vertexList I) (adjN I ε) (adjN_symm I ε) (adjN_irrefl I ε) Prod.fst

end Lax119563Proofs.Matrix

end Matrix_Construction

/-! ### Formerly `Lax119563Proofs.Matrix.Semantics` -/

section Matrix_Semantics

/-!
# Schemas, equations and unit propagation

Uniform access to the two or three arguments of a schema, and the facts about unit
propagation used by both players.
-/

open Lax119563.ImplicitParitySystems Lax119563.MatrixCompiler Lax119563.ParitySystems

namespace Lax119563Proofs.Matrix

variable {k ℓ w : ℕ}

/-! ### Arguments of a schema -/

/-- The number of arguments of a schema. -/
@[reducible] def arity : Schema k ℓ w → ℕ
  | .binary .. => 2
  | .ternary .. => 3

/-- The argument locations. -/
def argLoc : (s : Schema k ℓ w) → Fin (arity s) → Fin w
  | .binary u v _ _ _ => ![u, v]
  | .ternary u v w' _ _ _ _ => ![u, v, w']

/-- The argument permutations. -/
def argPerm : (s : Schema k ℓ w) → Fin (arity s) → BlockPerm k ℓ
  | .binary _ _ _ σ τ => ![σ, τ]
  | .ternary _ _ _ _ σ τ π => ![σ, τ, π]

lemma equation_eq (s : Schema k ℓ w) (a : Fin k → BlockCoord ℓ) :
    s.equation a = Finset.univ.image fun i => (argLoc s i, (argPerm s i).act a) := by
  cases s with
  | binary u v D σ τ =>
    show _ = (Finset.univ : Finset (Fin 2)).image fun i => (![u, v] i, (![σ, τ] i).act a)
    ext x; simp [Schema.equation, Fin.exists_fin_two, eq_comm]
  | ternary u v w' D σ τ π =>
    show _ = (Finset.univ : Finset (Fin 3)).image fun i => (![u, v, w'] i, (![σ, τ, π] i).act a)
    ext x; simp [Schema.equation, Fin.exists_fin_succ, eq_comm]

lemma locations_eq (s : Schema k ℓ w) : s.locations = Finset.univ.image (argLoc s) := by
  cases s with
  | binary u v D σ τ =>
    show _ = (Finset.univ : Finset (Fin 2)).image ![u, v]
    ext x; simp [Schema.locations, Fin.exists_fin_two, eq_comm]
  | ternary u v w' D σ τ π =>
    show _ = (Finset.univ : Finset (Fin 3)).image ![u, v, w']
    ext x; simp [Schema.locations, Fin.exists_fin_succ, eq_comm]

lemma argLoc_injective {dom : Fin w → Finset (Coord k ℓ)} {s : Schema k ℓ w}
    (h : s.WellFormed dom) : Function.Injective (argLoc s) := by
  cases s with
  | binary u v D σ τ =>
    obtain ⟨huv, -⟩ := h
    show Function.Injective (![u, v] : Fin 2 → Fin w)
    intro i j hij
    fin_cases i <;> fin_cases j <;> first
      | rfl
      | (exfalso; simp at hij; subst hij; simp_all)
  | ternary u v w' D σ τ π =>
    obtain ⟨huv, huw, hvw, -⟩ := h
    show Function.Injective (![u, v, w'] : Fin 3 → Fin w)
    intro i j hij
    fin_cases i <;> fin_cases j <;> first
      | rfl
      | (exfalso; simp at hij; subst hij; simp_all)

lemma argPerm_mem {dom : Fin w → Finset (Coord k ℓ)} {s : Schema k ℓ w}
    (h : s.WellFormed dom) {c : Coord k ℓ} (hc : c ∈ s.domain) (i : Fin (arity s)) :
    (argPerm s i).apply c ∈ dom (argLoc s i) := by
  cases s with
  | binary u v D σ τ =>
    obtain ⟨-, h1, h2⟩ := h
    fin_cases i
    · exact h1 (Finset.mem_image_of_mem _ hc)
    · exact h2 (Finset.mem_image_of_mem _ hc)
  | ternary u v w' D σ τ π =>
    obtain ⟨-, -, -, h1, h2, h3⟩ := h
    fin_cases i
    · exact h1 (Finset.mem_image_of_mem _ hc)
    · exact h2 (Finset.mem_image_of_mem _ hc)
    · exact h3 (Finset.mem_image_of_mem _ hc)

/-- The sum of a function over the arguments: the start terms plus the end term. -/
lemma sum_args (s : Schema k ℓ w) (f : Fin w → BlockPerm k ℓ → ZMod 2) :
    ∑ i, f (argLoc s i) (argPerm s i) =
      f (locU s) (permU s) + (if isTern s then f (locV s) (permV s) else 0) +
        f (locEnd s) (permEnd s) := by
  cases s with
  | binary u v D σ τ =>
    show ∑ i : Fin 2, f (![u, v] i) (![σ, τ] i) = _
    simp [Fin.sum_univ_two, isTern, locU, permU, locEnd, permEnd]
  | ternary u v w' D σ τ π =>
    show ∑ i : Fin 3, f (![u, v, w'] i) (![σ, τ, π] i) = _
    simp [Fin.sum_univ_three, isTern, locU, permU, locV, permV, locEnd, permEnd]

/-! ### Schemas of an implicit parity system -/

variable (I : ImplicitParitySystem k ℓ)

lemma sch_mem (e : Fin I.schemas.length) : sch I e ∈ I.schemas := List.get_mem _ _

lemma sch_wf (e : Fin I.schemas.length) : (sch I e).WellFormed I.domain :=
  I.schema_wellFormed _ (sch_mem I e)

lemma exists_sch {s : Schema k ℓ I.numLocations} (hs : s ∈ I.schemas) :
    ∃ e, sch I e = s := List.mem_iff_get.mp hs

/-- Distinct schemas share at most one location. -/
lemma sch_meet {e e' : Fin I.schemas.length} (h : e ≠ e') :
    ((sch I e).locations ∩ (sch I e').locations).card ≤ 1 := by
  have hp := List.pairwise_iff_getElem.mp I.schemas_meet
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne h) with hlt | hlt
  · exact hp e e' e.2 e'.2 hlt
  · rw [Finset.inter_comm]; exact hp e' e e'.2 e.2 hlt

lemma sch_meet' {e e' : Fin I.schemas.length} (h : e ≠ e') {v v' : Fin I.numLocations}
    (hvv' : v ≠ v') (hv : v ∈ (sch I e).locations) (hv' : v' ∈ (sch I e).locations)
    (hv2 : v ∈ (sch I e').locations) (hv2' : v' ∈ (sch I e').locations) : False := by
  have := sch_meet I h
  have h2 : ({v, v'} : Finset _) ⊆ (sch I e).locations ∩ (sch I e').locations := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> simp_all
  have := (Finset.card_le_card h2).trans this
  rw [Finset.card_pair hvv'] at this
  omega

/-! ### Unit propagation -/

/-- The variable of argument `i` of schema `e` at address `a`. -/
def argVar (e : Fin I.schemas.length) (i : Fin (arity (sch I e))) (a : Fin k → BlockCoord ℓ) :
    Fin I.numLocations × (Fin k → BlockCoord ℓ) :=
  (argLoc (sch I e) i, (argPerm (sch I e) i).act a)

lemma argVar_injective (e : Fin I.schemas.length) (a : Fin k → BlockCoord ℓ) :
    Function.Injective fun i => argVar I e i a :=
  fun _ _ h => argLoc_injective (sch_wf I e) (congrArg Prod.fst h)

lemma known_mono {r r' : ℕ} (h : r ≤ r') : I.toParitySystem.known r ⊆ I.toParitySystem.known r' := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans Set.subset_union_left

lemma hasConflict_mono {r r' : ℕ} (h : r ≤ r') (hc : I.toParitySystem.HasConflict r) :
    I.toParitySystem.HasConflict r' := by
  obtain ⟨X, h0, h1⟩ := hc
  exact ⟨X, known_mono I h h0, known_mono I h h1⟩

lemma hasConflict_of_conflictRound {τ : ℕ} (h : I.conflictRound = τ) :
    I.toParitySystem.HasConflict τ := by
  classical
  by_contra hne
  have hex : ∃ r, I.toParitySystem.HasConflict r := by
    by_contra hno
    push Not at hno
    have : I.conflictRound = ⊤ := by
      simp [ImplicitParitySystem.conflictRound, ParitySystem.conflictRound, hno]
    rw [this] at h
    exact ENat.top_ne_natCast τ h
  let r₀ := Nat.find hex
  have hle : I.conflictRound ≤ r₀ := iInf₂_le r₀ (Nat.find_spec hex)
  have hge : (r₀ : ℕ∞) ≤ I.conflictRound := le_iInf₂ fun r hr => by
    exact_mod_cast Nat.find_min' hex hr
  have : (r₀ : ℕ∞) = τ := le_antisymm hge hle |>.symm ▸ h
  have hτ : r₀ = τ := by exact_mod_cast this
  exact hne (hτ ▸ Nat.find_spec hex)

lemma not_hasConflict_of_lt {r : ℕ} (h : (r : ℕ∞) + 1 ≤ I.conflictRound) :
    ¬ I.toParitySystem.HasConflict r := by
  intro hc
  have h1 : I.conflictRound ≤ r := iInf₂_le r hc
  have h2 : (r : ℕ∞) < r + 1 := by exact_mod_cast Nat.lt_succ_self r
  exact absurd (h.trans h1) (not_le.mpr h2)

/-- The equation of schema `e` at an allowed address is an equation of the parity system. -/
lemma equation_mem (e : Fin I.schemas.length) {a : Fin k → BlockCoord ℓ} (ha : IsAddress a)
    (hs : supp a ⊆ dom I e) : (sch I e).equation a ∈ I.toParitySystem.equations :=
  ⟨sch I e, sch_mem I e, a, ha, hs, rfl⟩

/-- One round of unit propagation along an equation of schema `e`. -/
lemma infer (e : Fin I.schemas.length) {a : Fin k → BlockCoord ℓ} (ha : IsAddress a)
    (hs : supp a ⊆ dom I e) (i₀ : Fin (arity (sch I e))) (b : Fin (arity (sch I e)) → ZMod 2)
    {r : ℕ} (hb : ∀ i, i ≠ i₀ → (argVar I e i a, b i) ∈ I.toParitySystem.known r) :
    (argVar I e i₀ a, ∑ i ∈ Finset.univ.erase i₀, b i) ∈ I.toParitySystem.known (r + 1) := by
  classical
  right
  refine ⟨_, equation_mem I e ha hs, ?_, ?_⟩
  · rw [equation_eq]; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
  · let bF : Fin I.numLocations × (Fin k → BlockCoord ℓ) → ZMod 2 := fun X =>
      if h : ∃ i, argVar I e i a = X then b h.choose else 0
    have hbF : ∀ i, bF (argVar I e i a) = b i := by
      intro i
      have h : ∃ i', argVar I e i' a = argVar I e i a := ⟨i, rfl⟩
      simp only [bF, dif_pos h]
      rw [argVar_injective I e a h.choose_spec]
    refine ⟨bF, fun Y hY hne => ?_, ?_⟩
    · rw [equation_eq] at hY
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hY
      rw [show (argLoc (sch I e) i, (argPerm (sch I e) i).act a) = argVar I e i a from rfl, hbF]
      exact hb i fun h => hne (by rw [h]; rfl)
    · rw [equation_eq]
      have : (Finset.univ.image fun i => argVar I e i a).erase (argVar I e i₀ a) =
          (Finset.univ.erase i₀).image fun i => argVar I e i a := by
        rw [Finset.image_erase (argVar_injective I e a)]
      simp only [show (fun i => (argLoc (sch I e) i, (argPerm (sch I e) i).act a)) =
        fun i => argVar I e i a from rfl]
      rw [this, Finset.sum_image fun x _ y _ h => argVar_injective I e a h]
      exact Finset.sum_congr rfl fun i _ => (hbF i).symm

/-- A fact derived in round `r + 1` was known before or is inferred along a schema equation
from facts of round `r`. -/
lemma known_succ_cases {r : ℕ} {X : Fin I.numLocations × (Fin k → BlockCoord ℓ)} {b : ZMod 2}
    (h : (X, b) ∈ I.toParitySystem.known (r + 1)) :
    (X, b) ∈ I.toParitySystem.known r ∨
      ∃ e a, IsAddress a ∧ supp a ⊆ dom I e ∧ ∃ i₀, X = argVar I e i₀ a ∧
        ∃ bf : Fin (arity (sch I e)) → ZMod 2,
          (∀ i, i ≠ i₀ → (argVar I e i a, bf i) ∈ I.toParitySystem.known r) ∧
          b = ∑ i ∈ Finset.univ.erase i₀, bf i := by
  classical
  rcases h with h | ⟨h, ⟨s, hs, a, ha, hsa, rfl⟩, hXh, bF, hbF, hsum⟩
  · exact Or.inl h
  right
  obtain ⟨e, rfl⟩ := exists_sch I hs
  change X ∈ (sch I e).equation a at hXh
  change ∀ Y ∈ (sch I e).equation a, Y ≠ X → (Y, bF Y) ∈ I.toParitySystem.known r at hbF
  rw [equation_eq] at hXh
  obtain ⟨i₀, -, hX⟩ := Finset.mem_image.mp hXh
  refine ⟨e, a, ha, hsa, i₀, hX.symm, fun i => bF (argVar I e i a), fun i hi => ?_, ?_⟩
  · apply hbF
    · rw [equation_eq]; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
    · intro h; apply hi
      exact argVar_injective I e a (h.trans hX.symm)
  · simp only at hsum
    rw [hsum, equation_eq]
    have : (Finset.univ.image fun i => argVar I e i a).erase (X) =
        (Finset.univ.erase i₀).image fun i => argVar I e i a := by
      rw [← hX]
      exact (Finset.image_erase (argVar_injective I e a) _ _).symm
    simp only [show (fun i => (argLoc (sch I e) i, (argPerm (sch I e) i).act a)) =
      fun i => argVar I e i a from rfl]
    rw [this, Finset.sum_image fun x _ y _ h => argVar_injective I e a h]

/-- Known facts concern addresses supported in the coordinate domain of their location. -/
lemma known_valid {r : ℕ} {X : Fin I.numLocations × (Fin k → BlockCoord ℓ)} {b : ZMod 2}
    (h : (X, b) ∈ I.toParitySystem.known r) : IsAddress X.2 ∧ supp X.2 ⊆ I.domain X.1 := by
  induction r generalizing X b with
  | zero =>
    obtain ⟨_, -, -, h1, h2⟩ := h
    exact ⟨h1, h2⟩
  | succ r ih =>
    rcases known_succ_cases I h with h | ⟨e, a, ha, hsa, i₀, rfl, -⟩
    · exact ih h
    · refine ⟨isAddress_act _ ha, ?_⟩
      simp only [argVar]
      rw [supp_act]
      intro c hc
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hc
      exact argPerm_mem (sch_wf I e) (hsa hd) i₀

end Lax119563Proofs.Matrix

end Matrix_Semantics

/-! ### Formerly `Lax119563Proofs.Matrix.VertexList` -/

section Matrix_VertexList

/-!
# The vertex list

`vertexList I` lists every valid vertex name exactly once.
-/

open Lax119563.ImplicitParitySystems Lax119563.MatrixCompiler

namespace Lax119563Proofs.Matrix

variable {k ℓ : ℕ}

/-! ### Generic list facts -/

lemma nodup_flatMap_of_key {γ α : Type*} {l : List γ} {f : γ → List α} (key : α → Option γ)
    (hl : l.Nodup) (hf : ∀ a ∈ l, (f a).Nodup) (hk : ∀ a ∈ l, ∀ x ∈ f a, key x = some a) :
    (l.flatMap f).Nodup := by
  refine List.nodup_flatMap.mpr ⟨hf, hl.imp_of_mem fun ha hb hab => ?_⟩
  intro x hxa hxb
  exact hab (Option.some.inj ((hk _ ha x hxa).symm.trans (hk _ hb x hxb)))

lemma nodup_append_of_key {α : Type*} {l₁ l₂ : List α} (key : α → Prop) (h₁ : l₁.Nodup)
    (h₂ : l₂.Nodup) (hk₁ : ∀ x ∈ l₁, key x) (hk₂ : ∀ x ∈ l₂, ¬ key x) : (l₁ ++ l₂).Nodup :=
  List.nodup_append.mpr ⟨h₁, h₂, fun a ha b hb hab => hk₂ b hb (hab ▸ hk₁ a ha)⟩

/-! ### Coordinates -/

lemma mem_allBlockCoords : ∀ {ℓ : ℕ} (b : BlockCoord ℓ), b ∈ allBlockCoords ℓ
  | 0, b => by
    simp only [allBlockCoords, List.mem_singleton]
    funext i; exact i.elim0
  | ℓ + 1, b => by
    simp only [allBlockCoords, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
    refine ⟨Fin.tail b, mem_allBlockCoords _, ?_⟩
    rcases zmod2_eq_zero_or_one (b 0) with h | h
    · left; rw [← h]; exact (Fin.cons_self_tail b).symm
    · right; rw [← h]; exact (Fin.cons_self_tail b).symm

lemma nodup_allBlockCoords : ∀ ℓ : ℕ, (allBlockCoords ℓ).Nodup
  | 0 => List.nodup_singleton _
  | ℓ + 1 => by
    refine nodup_flatMap_of_key (fun b => some (Fin.tail b)) (nodup_allBlockCoords ℓ)
      (fun b _ => ?_) (fun b _ x hx => ?_)
    · refine List.nodup_cons.mpr ⟨?_, List.nodup_singleton _⟩
      simp only [List.mem_singleton]
      intro h
      have := congrFun h 0
      simp at this
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> simp

lemma mem_allCoords (c : Coord k ℓ) : c ∈ allCoords k ℓ := by
  simp only [allCoords, List.mem_flatMap, List.mem_finRange, List.mem_map, true_and]
  exact ⟨c.1, c.2, mem_allBlockCoords _, rfl⟩

lemma nodup_allCoords : (allCoords k ℓ).Nodup := by
  refine nodup_flatMap_of_key (fun c => some c.1) (List.nodup_finRange k)
    (fun i _ => (nodup_allBlockCoords ℓ).map fun b b' h => congrArg Prod.snd h) ?_
  intro i _ x hx
  obtain ⟨b, -, rfl⟩ := List.mem_map.mp hx
  rfl

@[simp] lemma mem_coordList {D : Finset (Coord k ℓ)} {c : Coord k ℓ} :
    c ∈ coordList D ↔ c ∈ D := by
  simp [coordList, mem_allCoords]

lemma nodup_coordList (D : Finset (Coord k ℓ)) : (coordList D).Nodup :=
  nodup_allCoords.filter _

/-! ### Labels -/

@[simp] lemma mem_bits1 (l : Lab) : l ∈ bits1 ↔ l.2 = 0 := by
  obtain ⟨a, b⟩ := l
  simp only [bits1, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq]
  rcases zmod2_eq_zero_or_one a with rfl | rfl <;> simp

@[simp] lemma mem_bits2 (l : Lab) : l ∈ bits2 := by
  obtain ⟨a, b⟩ := l
  simp only [bits2, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq]
  rcases zmod2_eq_zero_or_one a with rfl | rfl <;>
    rcases zmod2_eq_zero_or_one b with rfl | rfl <;> simp

lemma nodup_bits1 : bits1.Nodup := by decide

lemma nodup_bits2 : bits2.Nodup := by decide

/-! ### Membership -/

variable (I : ImplicitParitySystem k ℓ)

lemma mem_coordVerts (v : Fin I.numLocations) (x : VName I) :
    x ∈ coordVerts I v ↔ (∃ c, x.1 = .coord v c) ∧ Valid I x := by
  obtain ⟨X, l⟩ := x
  constructor
  · simp only [coordVerts, List.mem_flatMap, mem_coordList, List.mem_map]
    rintro ⟨c, hc, l', hl', he⟩
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    refine ⟨⟨c, rfl⟩, hc, fun _ => ?_, fun h => ?_⟩
    · split at hl'
      · simp at hl'; rw [hl']
      · exact (mem_bits1 _).mp hl'
    · simp only [isSingleton] at h
      rw [if_pos h] at hl'
      simp at hl'; rw [hl']
  · rintro ⟨⟨c, rfl⟩, hc, hl1, hl2⟩
    simp only [coordVerts, List.mem_flatMap, mem_coordList, List.mem_map]
    refine ⟨c, hc, l, ?_, rfl⟩
    have h2 : l.2 = 0 := hl1 rfl
    split
    · next h =>
      have h1 : l.1 = 0 := hl2 (by simpa [isSingleton] using h)
      simp [Prod.ext_iff, h1, h2]
    · exact (mem_bits1 _).mpr h2

lemma mem_columnVerts (e : Fin I.schemas.length) (c : Coord k ℓ) (x : VName I) :
    x ∈ columnVerts I e c ↔ (x.1 = .sum e c ∨ x.1 = .junc e c ∨ x.1 = .link e c) ∧
      (x.1 = .link e c ∨ isTern (sch I e) = true) ∧ LabelOK I x.1 x.2 := by
  obtain ⟨X, l⟩ := x
  by_cases ht : isTern (sch I e) = true
  · simp only [columnVerts, ht, if_true, List.mem_append, List.mem_map, mem_bits1, mem_bits2,
      Prod.mk.injEq, or_true]
    constructor
    · rintro ((⟨l', hl', rfl, rfl⟩ | ⟨l', -, rfl, rfl⟩) | ⟨l', hl', rfl, rfl⟩)
      · exact ⟨Or.inl rfl, trivial, fun _ => hl', fun h => by simp [isSingleton] at h⟩
      · exact ⟨Or.inr (Or.inl rfl), trivial, fun h => by simp [twoBit] at h,
          fun h => by simp [isSingleton] at h⟩
      · exact ⟨Or.inr (Or.inr rfl), trivial, fun _ => hl', fun h => by simp [isSingleton] at h⟩
    · rintro ⟨hX | hX | hX, -, hl1, -⟩ <;> subst hX
      · exact Or.inl (Or.inl ⟨l, hl1 rfl, rfl, rfl⟩)
      · exact Or.inl (Or.inr ⟨l, trivial, rfl, rfl⟩)
      · exact Or.inr ⟨l, hl1 rfl, rfl, rfl⟩
  · simp only [columnVerts, ht, Bool.false_eq_true, if_false, List.nil_append,
      List.mem_map, mem_bits1, Prod.mk.injEq, or_false]
    constructor
    · rintro ⟨l', hl', rfl, rfl⟩
      exact ⟨Or.inr (Or.inr rfl), rfl, fun _ => hl', fun h => by simp [isSingleton] at h⟩
    · rintro ⟨-, rfl, hl1, -⟩
      exact ⟨l, hl1 rfl, rfl, rfl⟩

lemma mem_stepVerts (e : Fin I.schemas.length) (σ : ℕ) (x : VName I) :
    x ∈ stepVerts I e σ ↔
      ((x.1 = .coef e σ ∧ ∃ c ∈ dom I e, ent σ c ≠ 0) ∨
        ∃ c ∈ dom I e, ent σ c ≠ 0 ∧ (x.1 = .track e σ c ∨ x.1 = .upd e σ c)) ∧
      LabelOK I x.1 x.2 := by
  obtain ⟨X, l⟩ := x
  simp only [stepVerts, List.mem_append, List.mem_flatMap, List.mem_filter, mem_coordList,
    List.mem_map, Prod.mk.injEq, decide_eq_true_eq]
  constructor
  · rintro (h | ⟨c, ⟨hc, hent⟩, h⟩)
    · split at h
      · next hex =>
        obtain ⟨l', hl', rfl, rfl⟩ := List.mem_map.mp h
        exact ⟨Or.inl ⟨rfl, hex⟩, fun _ => (mem_bits1 _).mp hl', fun h => by
          simp [isSingleton] at h⟩
      · simp at h
    · rcases h with ⟨l', hl', rfl, rfl⟩ | ⟨l', hl', rfl, rfl⟩
      · exact ⟨Or.inr ⟨c, hc, hent, Or.inl rfl⟩, fun _ => (mem_bits1 _).mp hl', fun h => by
          simp [isSingleton] at h⟩
      · exact ⟨Or.inr ⟨c, hc, hent, Or.inr rfl⟩, fun h => by simp [twoBit] at h, fun h => by
          simp [isSingleton] at h⟩
  · rintro ⟨⟨rfl, hex⟩ | ⟨c, hc, hent, rfl | rfl⟩, hl1, -⟩
    · left
      rw [if_pos hex]
      exact List.mem_map.mpr ⟨l, (mem_bits1 _).mpr (hl1 rfl), rfl⟩
    · exact Or.inr ⟨c, ⟨hc, hent⟩, Or.inl ⟨l, (mem_bits1 _).mpr (hl1 rfl), rfl, rfl⟩⟩
    · exact Or.inr ⟨c, ⟨hc, hent⟩, Or.inr ⟨l, mem_bits2 _, rfl, rfl⟩⟩

/-- The vertex list consists of the valid names. -/
theorem mem_vertexList (x : VName I) : x ∈ vertexList I ↔ Valid I x := by
  obtain ⟨X, l⟩ := x
  simp only [vertexList, List.mem_append, List.mem_flatMap, List.mem_finRange, true_and,
    mem_coordVerts, schemaVerts, mem_columnVerts, mem_coordList, List.mem_range,
    mem_stepVerts]
  constructor
  · rintro (⟨v, -, hv⟩ | ⟨e, ⟨c, hc, hX, ht, hl⟩ | ⟨σ, hσ, hX, hl⟩⟩)
    · exact hv
    · refine ⟨?_, hl⟩
      rcases hX with rfl | rfl | rfl
      · exact ⟨ht.resolve_left (by simp), hc⟩
      · exact ⟨ht.resolve_left (by simp), hc⟩
      · exact hc
    · refine ⟨?_, hl⟩
      rcases hX with ⟨rfl, hex⟩ | ⟨c, hc, hent, rfl | rfl⟩
      · exact ⟨hσ, hex⟩
      · exact ⟨hσ, hc, hent⟩
      · exact ⟨hσ, hc, hent⟩
  · rintro ⟨hX, hl⟩
    cases X with
    | coord v c => exact Or.inl ⟨v, ⟨c, rfl⟩, hX, hl⟩
    | sum e c => exact Or.inr ⟨e, Or.inl ⟨c, hX.2, Or.inl rfl, Or.inr hX.1, hl⟩⟩
    | junc e c => exact Or.inr ⟨e, Or.inl ⟨c, hX.2, Or.inr (Or.inl rfl), Or.inr hX.1, hl⟩⟩
    | link e c => exact Or.inr ⟨e, Or.inl ⟨c, hX, Or.inr (Or.inr rfl), Or.inl rfl, hl⟩⟩
    | track e σ c => exact Or.inr ⟨e, Or.inr ⟨σ, hX.1, Or.inr ⟨c, hX.2.1, hX.2.2, Or.inl rfl⟩, hl⟩⟩
    | upd e σ c => exact Or.inr ⟨e, Or.inr ⟨σ, hX.1, Or.inr ⟨c, hX.2.1, hX.2.2, Or.inr rfl⟩, hl⟩⟩
    | coef e σ => exact Or.inr ⟨e, Or.inr ⟨σ, hX.1, Or.inl ⟨rfl, hX.2⟩, hl⟩⟩

/-! ### No duplicates -/

/-- The location of a coordinate class. -/
def keyLoc : ICls I → Option (Fin I.numLocations)
  | .coord v _ => some v
  | _ => none

/-- The coordinate of a class. -/
def keyCoord : ICls I → Option (Coord k ℓ)
  | .coord _ c => some c
  | .sum _ c => some c
  | .junc _ c => some c
  | .link _ c => some c
  | .track _ _ c => some c
  | .upd _ _ c => some c
  | .coef _ _ => none

/-- The schema of a class. -/
def keySchema : ICls I → Option (Fin I.schemas.length)
  | .coord .. => none
  | .sum e _ => some e
  | .junc e _ => some e
  | .link e _ => some e
  | .track e _ _ => some e
  | .upd e _ _ => some e
  | .coef e _ => some e

/-- The step of a class. -/
def keyStep : ICls I → Option ℕ
  | .track _ σ _ => some σ
  | .upd _ σ _ => some σ
  | .coef _ σ => some σ
  | _ => none

/-- The constructor of a class. -/
def tag : ICls I → ℕ
  | .coord .. => 0
  | .sum .. => 1
  | .junc .. => 2
  | .link .. => 3
  | .track .. => 4
  | .upd .. => 5
  | .coef .. => 6

lemma nodup_map_label (X : ICls I) {L : List Lab} (h : L.Nodup) :
    (L.map fun l => (X, l)).Nodup :=
  h.map fun _ _ h => congrArg Prod.snd h

lemma nodup_coordVerts (v : Fin I.numLocations) : (coordVerts I v).Nodup := by
  refine nodup_flatMap_of_key (fun x => keyCoord I x.1) (nodup_coordList _) (fun c _ => ?_)
    (fun c _ x hx => ?_)
  · apply nodup_map_label
    split
    · exact List.nodup_singleton _
    · exact nodup_bits1
  · obtain ⟨l, -, rfl⟩ := List.mem_map.mp hx
    rfl

lemma nodup_columnVerts (e : Fin I.schemas.length) (c : Coord k ℓ) :
    (columnVerts I e c).Nodup := by
  refine nodup_append_of_key (fun x => tag I x.1 ≠ 3) ?_ (nodup_map_label I _ nodup_bits1)
    ?_ ?_
  · split
    · exact nodup_append_of_key (fun x => tag I x.1 = 1) (nodup_map_label I _ nodup_bits1)
        (nodup_map_label I _ nodup_bits2) (fun x hx => by
          obtain ⟨l, -, rfl⟩ := List.mem_map.mp hx; rfl) (fun x hx => by
          obtain ⟨l, -, rfl⟩ := List.mem_map.mp hx; simp [tag])
    · exact List.nodup_nil
  · intro x hx
    split at hx
    · rcases List.mem_append.mp hx with hx | hx <;>
      · obtain ⟨l, -, rfl⟩ := List.mem_map.mp hx; simp [tag]
    · simp at hx
  · intro x hx
    obtain ⟨l, -, rfl⟩ := List.mem_map.mp hx; simp [tag]

lemma nodup_stepVerts (e : Fin I.schemas.length) (σ : ℕ) : (stepVerts I e σ).Nodup := by
  refine nodup_append_of_key (fun x => tag I x.1 = 6) ?_ ?_ ?_ ?_
  · split
    · exact nodup_map_label I _ nodup_bits1
    · exact List.nodup_nil
  · refine nodup_flatMap_of_key (fun x => keyCoord I x.1) ((nodup_coordList _).filter _)
      (fun c _ => ?_) (fun c _ x hx => ?_)
    · exact nodup_append_of_key (fun x => tag I x.1 = 4) (nodup_map_label I _ nodup_bits1)
        (nodup_map_label I _ nodup_bits2) (fun x hx => by
          obtain ⟨l, -, rfl⟩ := List.mem_map.mp hx; rfl) (fun x hx => by
          obtain ⟨l, -, rfl⟩ := List.mem_map.mp hx; simp [tag])
    · rcases List.mem_append.mp hx with hx | hx <;>
      · obtain ⟨l, -, rfl⟩ := List.mem_map.mp hx; rfl
  · intro x hx
    split at hx
    · obtain ⟨l, -, rfl⟩ := List.mem_map.mp hx; rfl
    · simp at hx
  · intro x hx
    obtain ⟨c, -, hx⟩ := List.mem_flatMap.mp hx
    rcases List.mem_append.mp hx with hx | hx <;>
    · obtain ⟨l, -, rfl⟩ := List.mem_map.mp hx; simp [tag]

lemma nodup_schemaVerts (e : Fin I.schemas.length) : (schemaVerts I e).Nodup := by
  refine nodup_append_of_key (fun x => tag I x.1 = 1 ∨ tag I x.1 = 2 ∨ tag I x.1 = 3) ?_ ?_ ?_ ?_
  · refine nodup_flatMap_of_key (fun x => keyCoord I x.1) (nodup_coordList _)
      (fun c _ => nodup_columnVerts I e c) (fun c _ x hx => ?_)
    rcases ((mem_columnVerts I e c x).mp hx).1 with h | h | h <;> rw [h] <;> rfl
  · refine nodup_flatMap_of_key (fun x => keyStep I x.1) List.nodup_range
      (fun σ _ => nodup_stepVerts I e σ) (fun σ _ x hx => ?_)
    rcases ((mem_stepVerts I e σ x).mp hx).1 with ⟨h, -⟩ | ⟨c, -, -, h | h⟩ <;> rw [h] <;> rfl
  · intro x hx
    obtain ⟨c, -, hx⟩ := List.mem_flatMap.mp hx
    rcases ((mem_columnVerts I e c x).mp hx).1 with h | h | h <;> rw [h] <;> simp [tag]
  · intro x hx
    obtain ⟨σ, -, hx⟩ := List.mem_flatMap.mp hx
    rcases ((mem_stepVerts I e σ x).mp hx).1 with ⟨h, -⟩ | ⟨c, -, -, h | h⟩ <;> rw [h] <;>
      simp [tag]

/-- Every valid name occurs exactly once in the vertex list. -/
theorem nodup_vertexList : (vertexList I).Nodup := by
  refine nodup_append_of_key (fun x => tag I x.1 = 0) ?_ ?_ ?_ ?_
  · refine nodup_flatMap_of_key (fun x => keyLoc I x.1) (List.nodup_finRange _)
      (fun v _ => nodup_coordVerts I v) (fun v _ x hx => ?_)
    obtain ⟨⟨c, h⟩, -⟩ := (mem_coordVerts I v x).mp hx
    rw [h]; rfl
  · refine nodup_flatMap_of_key (fun x => keySchema I x.1) (List.nodup_finRange _)
      (fun e _ => nodup_schemaVerts I e) (fun e _ x hx => ?_)
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨c, -, hx⟩ := List.mem_flatMap.mp hx
      rcases ((mem_columnVerts I e c x).mp hx).1 with h | h | h <;> rw [h] <;> rfl
    · obtain ⟨σ, -, hx⟩ := List.mem_flatMap.mp hx
      rcases ((mem_stepVerts I e σ x).mp hx).1 with ⟨h, -⟩ | ⟨c, -, -, h | h⟩ <;> rw [h] <;> rfl
  · intro x hx
    obtain ⟨v, -, hx⟩ := List.mem_flatMap.mp hx
    obtain ⟨⟨c, h⟩, -⟩ := (mem_coordVerts I v x).mp hx
    rw [h]; rfl
  · intro x hx
    obtain ⟨e, -, hx⟩ := List.mem_flatMap.mp hx
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨c, -, hx⟩ := List.mem_flatMap.mp hx
      rcases ((mem_columnVerts I e c x).mp hx).1 with h | h | h <;> rw [h] <;> simp [tag]
    · obtain ⟨σ, -, hx⟩ := List.mem_flatMap.mp hx
      rcases ((mem_stepVerts I e σ x).mp hx).1 with ⟨h, -⟩ | ⟨c, -, -, h | h⟩ <;> rw [h] <;>
        simp [tag]

end Lax119563Proofs.Matrix

end Matrix_VertexList

/-! ### Formerly `Lax119563Proofs.Matrix.Shifts` -/

section Matrix_Shifts

/-!
# Descriptions and the induced translations

A *description* consists of total seeds `z_v` and coefficient bits `λ_{e,σ}`. It translates
the labels of every class; the translation `phi` is a class-preserving involution on names,
and it is an isomorphism between the graphs on every set of classes on which it is
*consistent* (initialized seeds and the mask-sum condition at the links).
-/

open Lax119563.ImplicitParitySystems Lax119563.MatrixCompiler

namespace Lax119563Proofs.Matrix

variable {k ℓ : ℕ}

/-! ### Steps -/

lemma ent_eq_one {σ : ℕ} {c : Coord k ℓ} (h : ent σ c ≠ 0) : ent σ c = 1 :=
  (zmod2_ne_zero_iff _).mp h

lemma prevStep_none {c : Coord k ℓ} {σ : ℕ} (h : prevStep c σ = none) :
    ∀ σ' < σ, ent σ' c = 0 := by
  induction σ with
  | zero => intro σ' h'; omega
  | succ σ ih =>
    simp only [prevStep] at h
    split at h
    · simp at h
    · next hne =>
      intro σ' hσ'
      rcases Nat.lt_succ_iff_lt_or_eq.mp hσ' with h' | rfl
      · exact ih h σ' h'
      · exact not_not.mp hne

lemma prevStep_some {c : Coord k ℓ} {σ σ' : ℕ} (h : prevStep c σ = some σ') :
    σ' < σ ∧ ent σ' c ≠ 0 ∧ ∀ σ'', σ' < σ'' → σ'' < σ → ent σ'' c = 0 := by
  induction σ with
  | zero => simp [prevStep] at h
  | succ σ ih =>
    simp only [prevStep] at h
    split at h
    · next hne =>
      cases h
      exact ⟨Nat.lt_succ_self _, hne, fun σ'' h1 h2 => by omega⟩
    · next hne =>
      obtain ⟨h1, h2, h3⟩ := ih h
      refine ⟨by omega, h2, fun σ'' h4 h5 => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp h5 with h6 | rfl
      · exact h3 σ'' h4 h6
      · exact not_not.mp hne

lemma trackAt_succ (I : ImplicitParitySystem k ℓ) (e : Fin I.schemas.length) (c : Coord k ℓ)
    (σ : ℕ) : trackAt I e c (σ + 1) = if ent σ c ≠ 0 then .track e σ c else trackAt I e c σ := by
  by_cases h : ent σ c = 0 <;> simp [trackAt, prevStep, h]

/-! ### Descriptions -/

variable (I : ImplicitParitySystem k ℓ)

/-- A description: total seeds and coefficient bits. -/
structure Desc where
  /-- The seed of each location. -/
  z : Fin I.numLocations → Vec k ℓ
  /-- The coefficient bit of each step of each schema. -/
  lam : Fin I.schemas.length → ℕ → ZMod 2

variable {I}

/-- The initial track bit `t_{e,0}(c)`. -/
def t0 (D : Desc I) (e : Fin I.schemas.length) (c : Coord k ℓ) : ZMod 2 :=
  D.z (locU (sch I e)) ((permU (sch I e)).apply c) +
    if isTern (sch I e) then D.z (locV (sch I e)) ((permV (sch I e)).apply c) else 0

/-- The track bit of column `c` at stage `σ`. -/
def T (D : Desc I) (e : Fin I.schemas.length) (c : Coord k ℓ) (σ : ℕ) : ZMod 2 :=
  t0 D e c + ∑ σ' ∈ Finset.range σ, D.lam e σ' * ent σ' c

/-- The translation of each class. -/
def shift (D : Desc I) : ICls I → Lab
  | .coord v c => (D.z v c, 0)
  | .sum e c => (t0 D e c, 0)
  | .junc e c => (D.z (locU (sch I e)) ((permU (sch I e)).apply c),
      D.z (locV (sch I e)) ((permV (sch I e)).apply c))
  | .link e c => (T D e c (numSteps k ℓ), 0)
  | .track e σ c => (T D e c (σ + 1), 0)
  | .upd e σ c => (T D e c σ, T D e c (σ + 1))
  | .coef e σ => (D.lam e σ, 0)

/-- The map induced by a description on vertex names. -/
def phi (D : Desc I) (x : VName I) : VName I :=
  if isSingleton I x.1 then x else (x.1, x.2 + shift D x.1)

/-- The seeds of initialized locations are the initial seeds. -/
def InitOK (D : Desc I) : Prop := ∀ v, (I.init v).isSome → D.z v = initSeed I v

/-- The mask-sum condition at column `c` of schema `e`. -/
def MS (D : Desc I) (e : Fin I.schemas.length) (c : Coord k ℓ) : Prop :=
  T D e c (numSteps k ℓ) = D.z (locEnd (sch I e)) ((permEnd (sch I e)).apply c)

lemma T_succ (D : Desc I) (e : Fin I.schemas.length) (c : Coord k ℓ) (σ : ℕ) :
    T D e c (σ + 1) = T D e c σ + D.lam e σ * ent σ c := by
  simp [T, Finset.sum_range_succ, add_assoc]

lemma T_zero (D : Desc I) (e : Fin I.schemas.length) (c : Coord k ℓ) : T D e c 0 = t0 D e c := by
  simp [T]

lemma shift_startCls (D : Desc I) (e : Fin I.schemas.length) (c : Coord k ℓ) :
    (shift D (startCls I e c)).1 = t0 D e c := by
  unfold startCls t0
  split
  · next h => simp [shift, t0, h]
  · simp [shift]

lemma T_eq_of_zero (D : Desc I) (e : Fin I.schemas.length) (c : Coord k ℓ) {σ σ' : ℕ}
    (hle : σ ≤ σ') (h : ∀ σ'', σ ≤ σ'' → σ'' < σ' → ent σ'' c = 0) : T D e c σ' = T D e c σ := by
  induction hle with
  | refl => rfl
  | step hle ih =>
    rw [T_succ, h _ hle (Nat.lt_succ_self _), mul_zero, add_zero]
    exact ih fun σ'' h1 h2 => h σ'' h1 (Nat.lt_succ_of_lt h2)

lemma shift_trackAt (D : Desc I) (e : Fin I.schemas.length) (c : Coord k ℓ) (σ : ℕ) :
    (shift D (trackAt I e c σ)).1 = T D e c σ := by
  unfold trackAt
  split
  · next h =>
    rw [shift_startCls, T_eq_of_zero D e c (Nat.zero_le σ) fun σ'' _ h2 => prevStep_none h σ'' h2,
      T_zero]
  · next σ' h =>
    obtain ⟨h1, -, h3⟩ := prevStep_some h
    exact (T_eq_of_zero D e c h1 fun σ'' h4 h5 => h3 σ'' h4 h5).symm

/-! ### `phi` -/

@[simp] lemma phi_fst (D : Desc I) (x : VName I) : (phi D x).1 = x.1 := by
  unfold phi; split <;> rfl

lemma phi_phi (D : Desc I) (x : VName I) : phi D (phi D x) = x := by
  by_cases h : isSingleton I x.1 = true
  · simp [phi, h]
  · obtain ⟨X, l⟩ := x
    simp only at h
    simp only [phi, h, Bool.false_eq_true, if_false]
    ext <;> simp [add_assoc, zmod2_add_self]

lemma shift_snd (D : Desc I) {X : ICls I} (h : twoBit I X = false) : (shift D X).2 = 0 := by
  cases X <;> simp_all [twoBit, shift]

lemma valid_phi (D : Desc I) {x : VName I} (hx : Valid I x) : Valid I (phi D x) := by
  unfold phi
  split
  · exact hx
  · next hs =>
    refine ⟨hx.1, fun h2 => ?_, fun h => absurd h hs⟩
    simp only [Prod.snd_add, hx.2.1 h2, shift_snd D h2, add_zero]

lemma initBit_eq_zero_of_not_singleton {X : ICls I} (h : ¬ isSingleton I X = true) :
    initBit I X = 0 := by
  cases X with
  | coord v c =>
    simp only [isSingleton, Option.isSome_iff_ne_none, ne_eq, not_not] at h
    simp [initBit, initSeed, h]
  | _ => rfl

lemma eff_phi (D : Desc I) (hD : InitOK D) {x : VName I} (hx : Valid I x) :
    eff I 1 (phi D x) = eff I 0 x + shift D x.1 := by
  obtain ⟨X, l⟩ := x
  unfold phi eff
  split
  · next hs =>
    cases X with
    | coord v c =>
      have h1 : l.1 = 0 := hx.2.2 hs
      have h2 : l.2 = 0 := hx.2.1 rfl
      simp only [isSingleton] at hs
      simp [shift, initBit, hD v hs, h1, h2]
    | _ => simp [isSingleton] at hs
  · next hs =>
    simp [initBit_eq_zero_of_not_singleton hs]
    rfl

/-! ### Invariance of the hub relation -/

lemma and_decide_congr {Y A : ICls I} {P Q : Prop} [Decidable P] [Decidable Q]
    (h : Y = A → (P ↔ Q)) : (decide (Y = A) && decide P) = (decide (Y = A) && decide Q) := by
  by_cases hY : Y = A
  · simp [hY, h hY]
  · simp [hY]

/-- The hub relation is invariant under the translation, provided the mask-sum condition holds
at links and updates are valid. -/
lemma hubB_shift (D : Desc I) {X : ICls I} (hX : ClsValid I X)
    (hms : ∀ e c, X = .link e c → MS D e c) (l m : Lab) (Y : ICls I) :
    hubB I X (l + shift D X) Y (m + shift D Y) = hubB I X l Y m := by
  cases X with
  | upd e σ c =>
    have hent : ent σ c = 1 := ent_eq_one hX.2.2
    simp only [hubB]
    congr 1
    · congr 1
      · refine and_decide_congr fun hY => ?_
        subst hY
        rw [Prod.fst_add, Prod.fst_add, shift_trackAt]
        exact add_left_inj (T D e c σ)
      · refine and_decide_congr fun hY => ?_
        subst hY
        rw [Prod.fst_add, Prod.snd_add]
        exact add_left_inj (T D e c (σ + 1))
    · refine and_decide_congr fun hY => ?_
      subst hY
      simp only [Prod.fst_add, Prod.snd_add, shift, T_succ, hent, mul_one]
      constructor
      · intro h
        have : m.1 + D.lam e σ = l.1 + l.2 + D.lam e σ := by
          rw [h]; ring_nf; rw [show (2 : ZMod 2) = 0 from rfl]; ring
        exact add_right_cancel this
      · intro h
        rw [h]; ring_nf; rw [show (2 : ZMod 2) = 0 from rfl]; ring
  | junc e c =>
    simp only [hubB]
    congr 1
    · congr 1
      · refine and_decide_congr fun hY => ?_
        subst hY
        rw [Prod.fst_add, Prod.fst_add]
        exact add_left_inj (D.z (locU (sch I e)) ((permU (sch I e)).apply c))
      · refine and_decide_congr fun hY => ?_
        subst hY
        rw [Prod.fst_add, Prod.snd_add]
        exact add_left_inj (D.z (locV (sch I e)) ((permV (sch I e)).apply c))
    · refine and_decide_congr fun hY => ?_
      subst hY
      have ht : isTern (sch I e) = true := hX.1
      simp only [Prod.fst_add, Prod.snd_add, shift, t0, ht, if_true]
      constructor
      · intro h
        have := h
        refine add_right_cancel (b := D.z (locU (sch I e)) ((permU (sch I e)).apply c) +
          D.z (locV (sch I e)) ((permV (sch I e)).apply c)) ?_
        rw [this]; ring
      · intro h; rw [h]; ring
  | link e c =>
    have hm := hms e c rfl
    simp only [hubB]
    congr 1
    · refine and_decide_congr fun hY => ?_
      subst hY
      rw [Prod.fst_add, Prod.fst_add, shift_trackAt]
      exact add_left_inj (T D e c (numSteps k ℓ))
    · refine and_decide_congr fun hY => ?_
      subst hY
      rw [Prod.fst_add, Prod.fst_add]
      rw [MS] at hm
      show m.1 + D.z (locEnd (sch I e)) ((permEnd (sch I e)).apply c) =
        l.1 + T D e c (numSteps k ℓ) ↔ _
      rw [hm]
      exact add_left_inj _
  | coord => rfl
  | sum => rfl
  | track => rfl
  | coef => rfl

/-- The translation preserves adjacency between valid names whose classes satisfy the
consistency conditions. -/
lemma adjN_phi (D : Desc I) (hD : InitOK D) {x y : VName I} (hx : Valid I x) (hy : Valid I y)
    (hmsx : ∀ e c, x.1 = .link e c → MS D e c) (hmsy : ∀ e c, y.1 = .link e c → MS D e c) :
    adjN I 0 x y ↔ adjN I 1 (phi D x) (phi D y) := by
  unfold adjN
  rw [eff_phi D hD hx, eff_phi D hD hy, phi_fst, phi_fst, hubB_shift D hx.1 hmsx,
    hubB_shift D hy.1 hmsy]

end Lax119563Proofs.Matrix

end Matrix_Shifts

/-! ### Formerly `Lax119563Proofs.Matrix.Exposure` -/

section Matrix_Exposure

/-!
# Pebbled coordinate sets and exposure

For a set `A` of classes, `Iloc A v` and `Isch A e` are the coordinate sets
`𝔍_v(A)` and `𝔍_e(A)` of the paper. Each class contributes at most one coordinate to each of
them. The geometry lemma: an equation that becomes exposed has at most one variable that
was exposed before.
-/

open Lax119563.ImplicitParitySystems Lax119563.MatrixCompiler

namespace Lax119563Proofs.Matrix

variable {k ℓ : ℕ} {I : ImplicitParitySystem k ℓ}

variable (I) in
/-- The coordinates contributed to location `v` by an internal class of schema `e` at `c`. -/
def argContrib (e : Fin I.schemas.length) (c : Coord k ℓ) (v : Fin I.numLocations) :
    Finset (Coord k ℓ) :=
  (Finset.univ.filter fun i => argLoc (sch I e) i = v).image fun i => (argPerm (sch I e) i).apply c

/-- The schema and coordinate of an internal class. -/
def inner : ICls I → Option (Fin I.schemas.length × Coord k ℓ)
  | .sum e c => some (e, c)
  | .junc e c => some (e, c)
  | .link e c => some (e, c)
  | .track e _ c => some (e, c)
  | .upd e _ c => some (e, c)
  | _ => none

/-- The coordinates contributed by a class to location `v`. -/
def locContrib (X : ICls I) (v : Fin I.numLocations) : Finset (Coord k ℓ) :=
  match X with
  | .coord v' c => if v' = v then {c} else ∅
  | .coef _ _ => ∅
  | X => match inner X with
    | some (e, c) => argContrib I e c v
    | none => ∅

/-- The coordinates contributed by a class to schema `e`. -/
def schContrib (X : ICls I) (e : Fin I.schemas.length) : Finset (Coord k ℓ) :=
  match inner X with
  | some (e', c) => if e' = e then {c} else ∅
  | none => ∅

/-- The pebbled coordinate set `𝔍_v(A)`. -/
def Iloc (A : Finset (ICls I)) (v : Fin I.numLocations) : Finset (Coord k ℓ) :=
  A.biUnion fun X => locContrib X v

/-- The pebbled coordinate set `𝔍_e(A)`. -/
def Isch (A : Finset (ICls I)) (e : Fin I.schemas.length) : Finset (Coord k ℓ) :=
  A.biUnion fun X => schContrib X e

lemma locContrib_of_inner {X : ICls I} {e : Fin I.schemas.length} {c : Coord k ℓ}
    (h : inner X = some (e, c)) (v : Fin I.numLocations) :
    locContrib X v = argContrib I e c v := by
  cases X <;> simp_all [inner, locContrib]

lemma inner_none {X : ICls I} (h : inner X = none) :
    (∃ v c, X = .coord v c) ∨ ∃ e σ, X = .coef e σ := by
  cases X <;> simp_all [inner]

lemma mem_argContrib {e : Fin I.schemas.length} {c d : Coord k ℓ} {v : Fin I.numLocations} :
    d ∈ argContrib I e c v ↔ ∃ i, argLoc (sch I e) i = v ∧ (argPerm (sch I e) i).apply c = d := by
  simp [argContrib]

lemma card_argContrib_le (e : Fin I.schemas.length) (c : Coord k ℓ) (v : Fin I.numLocations) :
    (argContrib I e c v).card ≤ 1 := by
  refine Finset.card_le_one.mpr fun d hd d' hd' => ?_
  obtain ⟨i, hi, rfl⟩ := mem_argContrib.mp hd
  obtain ⟨j, hj, rfl⟩ := mem_argContrib.mp hd'
  rw [argLoc_injective (sch_wf I e) (hi.trans hj.symm)]

lemma argContrib_self (e : Fin I.schemas.length) (c : Coord k ℓ) (i : Fin (arity (sch I e))) :
    argContrib I e c (argLoc (sch I e) i) = {(argPerm (sch I e) i).apply c} := by
  refine Finset.eq_singleton_iff_unique_mem.mpr ⟨mem_argContrib.mpr ⟨i, rfl, rfl⟩, ?_⟩
  intro d hd
  obtain ⟨j, hj, rfl⟩ := mem_argContrib.mp hd
  rw [argLoc_injective (sch_wf I e) hj]

lemma argContrib_nonempty {e : Fin I.schemas.length} {c : Coord k ℓ} {v : Fin I.numLocations}
    (h : (argContrib I e c v).Nonempty) : v ∈ (sch I e).locations := by
  obtain ⟨d, hd⟩ := h
  obtain ⟨i, rfl, -⟩ := mem_argContrib.mp hd
  rw [locations_eq]; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)

lemma card_locContrib_le (X : ICls I) (v : Fin I.numLocations) : (locContrib X v).card ≤ 1 := by
  cases X with
  | coord v' c => simp only [locContrib]; split <;> simp
  | coef => simp [locContrib]
  | _ => exact card_argContrib_le _ _ _

lemma card_schContrib_le (X : ICls I) (e : Fin I.schemas.length) : (schContrib X e).card ≤ 1 := by
  unfold schContrib
  split
  · split <;> simp
  · simp

lemma card_biUnion_le_card {A : Finset (ICls I)} {f : ICls I → Finset (Coord k ℓ)}
    (h : ∀ X, (f X).card ≤ 1) : (A.biUnion f).card ≤ A.card :=
  (Finset.card_biUnion_le).trans (by simpa using Finset.sum_le_sum fun X (_ : X ∈ A) => h X)

lemma card_Iloc_le (A : Finset (ICls I)) (v : Fin I.numLocations) : (Iloc A v).card ≤ A.card :=
  card_biUnion_le_card fun X => card_locContrib_le X v

lemma card_Isch_le (A : Finset (ICls I)) (e : Fin I.schemas.length) : (Isch A e).card ≤ A.card :=
  card_biUnion_le_card fun X => card_schContrib_le X e

lemma Iloc_mono {A B : Finset (ICls I)} (h : A ⊆ B) (v : Fin I.numLocations) :
    Iloc A v ⊆ Iloc B v := Finset.biUnion_subset_biUnion_of_subset_left _ h

lemma Isch_mono {A B : Finset (ICls I)} (h : A ⊆ B) (e : Fin I.schemas.length) :
    Isch A e ⊆ Isch B e := Finset.biUnion_subset_biUnion_of_subset_left _ h

lemma Iloc_insert (X : ICls I) (A : Finset (ICls I)) (v : Fin I.numLocations) :
    Iloc (insert X A) v = locContrib X v ∪ Iloc A v := Finset.biUnion_insert

lemma Isch_insert (X : ICls I) (A : Finset (ICls I)) (e : Fin I.schemas.length) :
    Isch (insert X A) e = schContrib X e ∪ Isch A e := Finset.biUnion_insert

lemma mem_Isch {A : Finset (ICls I)} {e : Fin I.schemas.length} {c : Coord k ℓ} :
    c ∈ Isch A e ↔ ∃ X ∈ A, inner X = some (e, c) := by
  simp only [Isch, Finset.mem_biUnion, schContrib]
  constructor
  · rintro ⟨X, hX, hc⟩
    split at hc
    · next e' c' h =>
      split at hc
      · next he => simp at hc; subst hc; subst he; exact ⟨X, hX, h⟩
      · simp at hc
    · simp at hc
  · rintro ⟨X, hX, h⟩
    exact ⟨X, hX, by simp [h]⟩

lemma schContrib_of_inner {X : ICls I} {e : Fin I.schemas.length} {c : Coord k ℓ}
    (h : inner X = some (e, c)) (e' : Fin I.schemas.length) :
    schContrib X e' = if e = e' then {c} else ∅ := by
  simp [schContrib, h]

lemma schContrib_of_inner_none {X : ICls I} (h : inner X = none) (e' : Fin I.schemas.length) :
    schContrib X e' = ∅ := by
  simp [schContrib, h]

/-- The argument coordinates of a pebbled schema coordinate are pebbled. -/
lemma Isch_args {A : Finset (ICls I)} {e : Fin I.schemas.length} {c : Coord k ℓ}
    (hc : c ∈ Isch A e) (i : Fin (arity (sch I e))) :
    (argPerm (sch I e) i).apply c ∈ Iloc A (argLoc (sch I e) i) := by
  obtain ⟨X, hX, h⟩ := mem_Isch.mp hc
  refine Finset.mem_biUnion.mpr ⟨X, hX, ?_⟩
  rw [locContrib_of_inner h, argContrib_self]
  exact Finset.mem_singleton_self _

/-- Valid classes. -/
def AllValid (A : Finset (ICls I)) : Prop := ∀ X ∈ A, ClsValid I X

lemma ClsValid.inner_dom {X : ICls I} (hX : ClsValid I X) {e : Fin I.schemas.length}
    {c : Coord k ℓ} (h : inner X = some (e, c)) : c ∈ dom I e := by
  cases X <;> simp only [inner, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h <;>
    obtain ⟨rfl, rfl⟩ := h <;> simp_all [ClsValid]

lemma Iloc_subset {A : Finset (ICls I)} (hA : AllValid A) (v : Fin I.numLocations) :
    Iloc A v ⊆ I.domain v := by
  intro d hd0
  obtain ⟨X, hX, hd⟩ := Finset.mem_biUnion.mp hd0
  cases hi : inner X with
  | some p =>
    obtain ⟨e, c⟩ := p
    rw [locContrib_of_inner hi] at hd
    obtain ⟨i, rfl, rfl⟩ := mem_argContrib.mp hd
    exact argPerm_mem (sch_wf I e) ((hA X hX).inner_dom hi) i
  | none =>
    rcases inner_none hi with ⟨v', c, rfl⟩ | ⟨e, σ, rfl⟩
    · simp only [locContrib] at hd
      split at hd
      · next h => subst h; rw [Finset.mem_singleton] at hd; subst hd; exact hA _ hX
      · simp at hd
    · simp [locContrib] at hd

lemma Isch_subset {A : Finset (ICls I)} (hA : AllValid A) (e : Fin I.schemas.length) :
    Isch A e ⊆ dom I e := by
  intro c hc
  obtain ⟨X, hX, h⟩ := mem_Isch.mp hc
  exact (hA X hX).inner_dom h

/-! ### Geometry -/

/-- If an address is covered at location `v` by at most `k` classes, every class contributes
to `v`. -/
lemma cover_all {A : Finset (ICls I)} (hA : A.card ≤ k) {v : Fin I.numLocations}
    {b : Fin k → BlockCoord ℓ} (hb : supp b ⊆ Iloc A v) :
    ∀ X ∈ A, (locContrib X v ∩ supp b).Nonempty := by
  classical
  set F := A.filter fun X => (locContrib X v ∩ supp b).Nonempty
  have hcov : supp b ⊆ F.biUnion fun X => locContrib X v ∩ supp b := by
    intro d hd
    obtain ⟨X, hX, hdX⟩ := Finset.mem_biUnion.mp (hb hd)
    have hne : (locContrib X v ∩ supp b).Nonempty := ⟨d, Finset.mem_inter.mpr ⟨hdX, hd⟩⟩
    exact Finset.mem_biUnion.mpr ⟨X, Finset.mem_filter.mpr ⟨hX, hne⟩,
      Finset.mem_inter.mpr ⟨hdX, hd⟩⟩
  have hk : k ≤ F.card := by
    have := (Finset.card_le_card hcov).trans (card_biUnion_le_card (A := F)
      fun X => (Finset.card_le_card Finset.inter_subset_left).trans (card_locContrib_le X v))
    rwa [card_supp] at this
  have hF : F = A := Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (hA.trans hk)
  intro X hX
  rw [← hF] at hX
  exact (Finset.mem_filter.mp hX).2

/-- **Exposure.** If two variables of the equation of schema `e` at address `a` are exposed
for a set of at most `k` classes, the equation itself is exposed. -/
lemma geometry {A : Finset (ICls I)} (hA : A.card ≤ k) (e : Fin I.schemas.length)
    {a : Fin k → BlockCoord ℓ} {i j : Fin (arity (sch I e))} (hij : i ≠ j)
    (hi : supp ((argPerm (sch I e) i).act a) ⊆ Iloc A (argLoc (sch I e) i))
    (hj : supp ((argPerm (sch I e) j).act a) ⊆ Iloc A (argLoc (sch I e) j)) :
    supp a ⊆ Isch A e := by
  have hvv : argLoc (sch I e) i ≠ argLoc (sch I e) j :=
    fun h => hij (argLoc_injective (sch_wf I e) h)
  have hci := cover_all hA hi
  have hcj := cover_all hA hj
  -- every class of `A` is internal to `e`
  have hint : ∀ X ∈ A, ∃ c', inner X = some (e, c') := by
    intro X hX
    obtain ⟨d, hd⟩ := hci X hX
    obtain ⟨d', hd'⟩ := hcj X hX
    have hd1 := (Finset.mem_inter.mp hd).1
    have hd1' := (Finset.mem_inter.mp hd').1
    cases hin : inner X with
    | none =>
      exfalso
      rcases inner_none hin with ⟨v', c, rfl⟩ | ⟨e', σ, rfl⟩
      · simp only [locContrib] at hd1 hd1'
        split at hd1
        · split at hd1'
          · next h1 h2 => exact hvv (h1.symm.trans h2)
          · simp at hd1'
        · simp at hd1
      · simp [locContrib] at hd1
    | some p =>
      obtain ⟨e', c'⟩ := p
      rw [locContrib_of_inner hin] at hd1 hd1'
      by_cases he : e' = e
      · exact ⟨c', he ▸ rfl⟩
      · exfalso
        have l1 := argContrib_nonempty ⟨d, hd1⟩
        have l2 := argContrib_nonempty ⟨d', hd1'⟩
        have m1 : argLoc (sch I e) i ∈ (sch I e).locations := by
          rw [locations_eq]; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
        have m2 : argLoc (sch I e) j ∈ (sch I e).locations := by
          rw [locations_eq]; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
        exact sch_meet' I he hvv l1 l2 m1 m2
  intro c hc
  have hd : (argPerm (sch I e) i).apply c ∈ supp ((argPerm (sch I e) i).act a) := by
    rw [supp_act]; exact Finset.mem_image_of_mem _ hc
  obtain ⟨X, hX, hdX⟩ := Finset.mem_biUnion.mp (hi hd)
  obtain ⟨c', hc'⟩ := hint X hX
  rw [locContrib_of_inner hc', argContrib_self] at hdX
  have : c = c' := bp_apply_injective _ (Finset.mem_singleton.mp hdX)
  subst this
  exact mem_Isch.mpr ⟨X, hX, hc'⟩

end Lax119563Proofs.Matrix

end Matrix_Exposure

/-! ### Formerly `Lax119563Proofs.Matrix.Invariant` -/

section Matrix_Invariant

/-!
# Duplicator's invariant

`Good r A D`: the description `D` is consistent on the pebbled classes `A`, its partial seeds
annihilate block-even codewords, the exposed values agree with `K_r`, and `K_r` is
conflict-free. This file proves the basic properties of the invariant and the extension of a
single location seed.
-/

open Lax119563.ImplicitParitySystems Lax119563.MatrixCompiler Lax119563.ParitySystems

namespace Lax119563Proofs.Matrix

variable {k ℓ : ℕ} {I : ImplicitParitySystem k ℓ}

/-- Duplicator's invariant with `r` rounds remaining. -/
structure Good (r : ℕ) (A : Finset (ICls I)) (D : Desc I) : Prop where
  init : InitOK D
  ms : ∀ e, ∀ c ∈ Isch A e, MS D e c
  even : ∀ v, EvenKills (D.z v) (Iloc A v)
  agree : ∀ v a b, IsAddress a → supp a ⊆ Iloc A v →
    ((v, a), b) ∈ I.toParitySystem.known r → dot (ind a) (D.z v) = b
  noConflict : ¬ I.toParitySystem.HasConflict r

lemma Good.mono {r r' : ℕ} {A B : Finset (ICls I)} {D : Desc I} (h : Good r A D) (hr : r' ≤ r)
    (hB : B ⊆ A) : Good r' B D where
  init := h.init
  ms e c hc := h.ms e c (Isch_mono hB e hc)
  even v := (h.even v).mono (Iloc_mono hB v)
  agree v a b ha hs hb := h.agree v a b ha (hs.trans (Iloc_mono hB v)) (known_mono I hr hb)
  noConflict hc := h.noConflict (hasConflict_mono I hr hc)

lemma Good.ms_link {r : ℕ} {A : Finset (ICls I)} {D : Desc I} (h : Good r A D) {X : ICls I}
    (hX : X ∈ A) : ∀ e c, X = .link e c → MS D e c := by
  rintro e c rfl
  exact h.ms e c (mem_Isch.mpr ⟨_, hX, rfl⟩)

/-! ### Facts -/

lemma fact_unique {r : ℕ} (hnc : ¬ I.toParitySystem.HasConflict r)
    {X : Fin I.numLocations × (Fin k → BlockCoord ℓ)} {b b' : ZMod 2}
    (h : (X, b) ∈ I.toParitySystem.known r) (h' : (X, b') ∈ I.toParitySystem.known r) :
    b = b' := by
  by_contra hne
  apply hnc
  rcases zmod2_eq_zero_or_one b with rfl | rfl <;> rcases zmod2_eq_zero_or_one b' with rfl | rfl
  · exact absurd rfl hne
  · exact ⟨X, h, h'⟩
  · exact ⟨X, h', h⟩
  · exact absurd rfl hne

lemma initSeed_evenKills (v : Fin I.numLocations) (J : Finset (Coord k ℓ)) :
    EvenKills (initSeed I v) J := by
  intro y hy he _
  rw [dot, sum_coord]
  unfold initSeed
  split
  · next b _ =>
    have : ∀ i : Fin k, ∑ b', y (i, b') * (if ((i, b') : Coord k ℓ).1.val = 0 then b else 0) =
        if i.val = 0 then blockSum y i * b else 0 := by
      intro i
      split
      · simp [blockSum, Finset.sum_mul]
      · simp
    simp_rw [this, he, zero_mul]
    simp
  · simp

lemma dot_initSeed {v : Fin I.numLocations} {b : ZMod 2} (hv : I.init v = some b) (hk : 0 < k)
    (a : Fin k → BlockCoord ℓ) : dot (ind a) (initSeed I v) = b := by
  rw [dot_ind_left]
  simp only [initSeed, hv]
  rw [Finset.sum_eq_single (⟨0, hk⟩ : Fin k)]
  · simp
  · intro i _ hi
    rw [if_neg]
    intro h; exact hi (Fin.ext h)
  · simp

/-- At an initialized location, all facts of a conflict-free round agree with the
initialization. -/
lemma fact_init {r : ℕ} (hnc : ¬ I.toParitySystem.HasConflict r) {v : Fin I.numLocations}
    {b ι : ZMod 2} (hv : I.init v = some ι) {a : Fin k → BlockCoord ℓ} (ha : IsAddress a)
    (hs : supp a ⊆ I.domain v) (h : ((v, a), b) ∈ I.toParitySystem.known r) : b = ι := by
  have h0 : ((v, a), ι) ∈ I.toParitySystem.known r :=
    known_mono I (Nat.zero_le r) ⟨ι, hv, rfl, ha, hs⟩
  exact fact_unique hnc h h0

/-- The initial description. -/
def desc0 (I : ImplicitParitySystem k ℓ) : Desc I where
  z v := initSeed I v
  lam _ _ := 0

lemma good_empty (hk : 0 < k) {r : ℕ} (hnc : ¬ I.toParitySystem.HasConflict r) :
    Good r ∅ (desc0 I) where
  init _ _ := rfl
  ms e c hc := by simp [Isch] at hc
  even v := initSeed_evenKills v _
  agree v a b ha hs _ := by
    exfalso
    have : (supp a).card = 0 := by
      rw [Finset.card_eq_zero]; simpa [Iloc] using hs
    rw [card_supp] at this; omega
  noConflict := hnc

/-! ### Extending the seed of one location -/

/-- Extending the seed of location `v` by the coordinate `d`, with prescribed value `p` on the
new address. -/
lemma extend_loc (hk : 0 < k) {r : ℕ} {A : Finset (ICls I)} {D : Desc I}
    (hG : Good (r + 1) A D) (v : Fin I.numLocations) (d : Coord k ℓ)
    (hcard : (insert d (Iloc A v)).card ≤ k + 1) (hdom : insert d (Iloc A v) ⊆ I.domain v)
    (p : ZMod 2)
    (hp : ∀ a b, IsAddress a → supp a ⊆ insert d (Iloc A v) → d ∈ supp a → d ∉ Iloc A v →
      ((v, a), b) ∈ I.toParitySystem.known r → p = b) :
    ∃ zv : Vec k ℓ, (∀ d' ∈ Iloc A v, zv d' = D.z v d') ∧
      ((I.init v).isSome → zv = initSeed I v) ∧
      EvenKills zv (insert d (Iloc A v)) ∧
      (∀ a, IsAddress a → supp a ⊆ insert d (Iloc A v) → d ∈ supp a → d ∉ Iloc A v →
        dot (ind a) zv = p) ∧
      (∀ a b, IsAddress a → supp a ⊆ insert d (Iloc A v) →
        ((v, a), b) ∈ I.toParitySystem.known r → dot (ind a) zv = b) := by
  have hnc : ¬ I.toParitySystem.HasConflict r :=
    fun h => hG.noConflict (hasConflict_mono I (Nat.le_succ r) h)
  -- old addresses keep their values
  have hold : ∀ zv : Vec k ℓ, (∀ d' ∈ Iloc A v, zv d' = D.z v d') →
      ∀ a b, IsAddress a → supp a ⊆ Iloc A v →
        ((v, a), b) ∈ I.toParitySystem.known r → dot (ind a) zv = b := by
    intro zv hzv a b ha hs hb
    rw [dot_congr_suppIn (suppIn_ind.mpr hs) (z' := D.z v) hzv]
    exact hG.agree v a b ha hs (known_mono I (Nat.le_succ r) hb)
  by_cases hd : d ∈ Iloc A v
  · rw [Finset.insert_eq_of_mem hd]
    exact ⟨D.z v, fun _ _ => rfl, hG.init v, hG.even v, fun _ _ _ _ h => absurd hd h,
      hold _ fun _ _ => rfl⟩
  · cases hv : I.init v with
    | some ι =>
      have hz := hG.init v (by simp [hv])
      refine ⟨D.z v, fun _ _ => rfl, fun _ => hz, hz ▸ initSeed_evenKills v _,
        fun a ha hs hda _ => ?_, fun a b ha hs hb => ?_⟩
      · have h0 : ((v, a), ι) ∈ I.toParitySystem.known r :=
          known_mono I (Nat.zero_le r) ⟨ι, hv, rfl, ha, hs.trans hdom⟩
        rw [hz, dot_initSeed hv hk, hp a ι ha hs hda hd h0]
      · rw [hz, dot_initSeed hv hk, fact_init hnc hv ha (hs.trans hdom) hb]
    | none =>
      obtain ⟨β, hβ1, hβ2⟩ := extend_seed hk hd hcard (hG.even v) p
      have hagree : ∀ d' ∈ Iloc A v, Function.update (D.z v) d β d' = D.z v d' :=
        fun d' hd' => Function.update_of_ne (fun h => hd (by rw [← h]; exact hd')) _ _
      refine ⟨Function.update (D.z v) d β, hagree, fun h => by simp at h, hβ1,
        fun a ha hs hda _ => hβ2 a ha hs hda, fun a b ha hs hb => ?_⟩
      by_cases hda : d ∈ supp a
      · rw [hβ2 a ha hs hda, hp a b ha hs hda hd hb]
      · refine hold _ hagree a b ha ?_ hb
        intro x hx
        rcases Finset.mem_insert.mp (hs hx) with rfl | h
        · exact absurd hx hda
        · exact h

end Lax119563Proofs.Matrix

end Matrix_Invariant

/-! ### Formerly `Lax119563Proofs.Matrix.ExtendSeeds` -/

section Matrix_ExtendSeeds

/-!
# Extending exposed values and argument seeds

When a new internal coordinate `c` of schema `e` is pebbled, the argument locations gain at
most one coordinate each. We choose values for the newly exposed variables (Lemma
"Extending exposed values") and extend the argument seeds accordingly.
-/

open Lax119563.ImplicitParitySystems Lax119563.MatrixCompiler Lax119563.ParitySystems

namespace Lax119563Proofs.Matrix

variable {k ℓ w : ℕ}

/-! ### Arguments and track bits -/

lemma exists_arg_U (s : Schema k ℓ w) : ∃ i, argLoc s i = locU s ∧ argPerm s i = permU s := by
  cases s
  · exact ⟨(0 : Fin 2), rfl, rfl⟩
  · exact ⟨(0 : Fin 3), rfl, rfl⟩

lemma exists_arg_V (s : Schema k ℓ w) : ∃ i, argLoc s i = locV s ∧ argPerm s i = permV s := by
  cases s
  · exact ⟨(1 : Fin 2), rfl, rfl⟩
  · exact ⟨(1 : Fin 3), rfl, rfl⟩

lemma exists_arg_End (s : Schema k ℓ w) :
    ∃ i, argLoc s i = locEnd s ∧ argPerm s i = permEnd s := by
  cases s
  · exact ⟨(1 : Fin 2), rfl, rfl⟩
  · exact ⟨(2 : Fin 3), rfl, rfl⟩

lemma arity_pos (s : Schema k ℓ w) : 0 < arity s := by
  cases s <;> simp [arity]

variable {I : ImplicitParitySystem k ℓ}

lemma t0_add_end (D : Desc I) (e : Fin I.schemas.length) (c : Coord k ℓ) :
    t0 D e c + D.z (locEnd (sch I e)) ((permEnd (sch I e)).apply c) =
      ∑ i, D.z (argLoc (sch I e) i) ((argPerm (sch I e) i).apply c) := by
  rw [sum_args (sch I e) fun v P => D.z v (P.apply c), t0]

/-- Agreement of two descriptions at the argument coordinates of `c`. -/
def ArgsAgree (D D' : Desc I) (e : Fin I.schemas.length) (c : Coord k ℓ) : Prop :=
  ∀ i, D'.z (argLoc (sch I e) i) ((argPerm (sch I e) i).apply c) =
    D.z (argLoc (sch I e) i) ((argPerm (sch I e) i).apply c)

lemma ArgsAgree.U {D D' : Desc I} {e : Fin I.schemas.length} {c : Coord k ℓ}
    (h : ArgsAgree D D' e c) :
    D'.z (locU (sch I e)) ((permU (sch I e)).apply c) =
      D.z (locU (sch I e)) ((permU (sch I e)).apply c) := by
  obtain ⟨i, h1, h2⟩ := exists_arg_U (sch I e)
  rw [← h1, ← h2]; exact h i

lemma ArgsAgree.V {D D' : Desc I} {e : Fin I.schemas.length} {c : Coord k ℓ}
    (h : ArgsAgree D D' e c) :
    D'.z (locV (sch I e)) ((permV (sch I e)).apply c) =
      D.z (locV (sch I e)) ((permV (sch I e)).apply c) := by
  obtain ⟨i, h1, h2⟩ := exists_arg_V (sch I e)
  rw [← h1, ← h2]; exact h i

lemma ArgsAgree.End {D D' : Desc I} {e : Fin I.schemas.length} {c : Coord k ℓ}
    (h : ArgsAgree D D' e c) :
    D'.z (locEnd (sch I e)) ((permEnd (sch I e)).apply c) =
      D.z (locEnd (sch I e)) ((permEnd (sch I e)).apply c) := by
  obtain ⟨i, h1, h2⟩ := exists_arg_End (sch I e)
  rw [← h1, ← h2]; exact h i

lemma ArgsAgree.t0 {D D' : Desc I} {e : Fin I.schemas.length} {c : Coord k ℓ}
    (h : ArgsAgree D D' e c) : t0 D' e c = t0 D e c := by
  simp only [Matrix.t0, h.U, h.V]

lemma T_congr {D D' : Desc I} {e : Fin I.schemas.length} {c : Coord k ℓ} (h : ArgsAgree D D' e c)
    {σ : ℕ} (hlam : ∀ σ' < σ, D'.lam e σ' = D.lam e σ') : T D' e c σ = T D e c σ := by
  simp only [T, h.t0]
  congr 1
  exact Finset.sum_congr rfl fun σ' hσ' => by rw [hlam σ' (Finset.mem_range.mp hσ')]

lemma argsAgree_of {D D' : Desc I} {Y : ICls I} {e : Fin I.schemas.length} {c : Coord k ℓ}
    (hY : inner Y = some (e, c)) (hz : ∀ v, ∀ d ∈ locContrib Y v, D'.z v d = D.z v d) :
    ArgsAgree D D' e c := by
  intro i
  apply hz
  rw [locContrib_of_inner hY, argContrib_self]
  exact Finset.mem_singleton_self _

/-- Shifts only depend on the seeds at the contributed coordinates and on the coefficients. -/
lemma shift_eq_of_z {D D' : Desc I} (Y : ICls I)
    (hz : ∀ v, ∀ d ∈ locContrib Y v, D'.z v d = D.z v d) (hlam : D'.lam = D.lam) :
    shift D' Y = shift D Y := by
  cases Y with
  | coord v c =>
    have := hz v c (by simp [locContrib])
    simp [shift, this]
  | sum e c =>
    have h := argsAgree_of (rfl : inner (Cls.sum e c : ICls I) = _) hz
    simp [shift, h.t0]
  | junc e c =>
    have h := argsAgree_of (rfl : inner (Cls.junc e c : ICls I) = _) hz
    simp [shift, h.U, h.V]
  | link e c =>
    have h := argsAgree_of (rfl : inner (Cls.link e c : ICls I) = _) hz
    simp [shift, T_congr h fun σ' _ => by rw [hlam]]
  | track e σ c =>
    have h := argsAgree_of (rfl : inner (Cls.track e σ c : ICls I) = _) hz
    simp [shift, T_congr h fun σ' _ => by rw [hlam]]
  | upd e σ c =>
    have h := argsAgree_of (rfl : inner (Cls.upd e σ c : ICls I) = _) hz
    simp [shift, T_congr h fun σ' _ => by rw [hlam]]
  | coef e σ => simp [shift, hlam]

/-! ### Rows and addresses -/

lemma ent_eq (hk : 2 ≤ k) (σ : ℕ) (c : Coord k ℓ) :
    ent σ c = checkMatrix k ℓ (stepRow (by omega) σ) c := by
  simp only [ent, dif_pos (show 0 < k - 1 + ℓ by omega)]

lemma sum_ent_supp (hk : 2 ≤ k) {a : Fin k → BlockCoord ℓ} (ha : IsAddress a) (σ : ℕ) :
    ∑ i, ent σ (i, a i) = 0 := by
  simp only [ent_eq hk]
  exact sum_row_supp (by omega) ha _

lemma sum_ent_code (hk : 2 ≤ k) {y : Vec k ℓ} (hy : IsCode y) (σ : ℕ) :
    ∑ c, y c * ent σ c = 0 := by
  have := hy (stepRow (by omega) σ)
  simp only [ent_eq hk]
  rw [← this]
  exact Finset.sum_congr rfl fun c _ => mul_comm _ _

/-- The equation of an address all of whose coordinates satisfy the mask-sum condition holds
for the seeds. -/
lemma eq_of_ms (hk : 2 ≤ k) (D : Desc I) (e : Fin I.schemas.length) {a : Fin k → BlockCoord ℓ}
    (ha : IsAddress a) (hms : ∀ c ∈ supp a, MS D e c) :
    ∑ i, dot (ind ((argPerm (sch I e) i).act a)) (D.z (argLoc (sch I e) i)) = 0 := by
  simp_rw [dot_ind_act]
  rw [Finset.sum_comm]
  have h : ∀ i', ∑ i, D.z (argLoc (sch I e) i) ((argPerm (sch I e) i).apply (i', a i')) =
      ∑ σ ∈ Finset.range (numSteps k ℓ), D.lam e σ * ent σ (i', a i') := by
    intro i'
    rw [← t0_add_end]
    have hm := hms (i', a i') (mem_supp_iff.mpr rfl)
    rw [MS, T] at hm
    rw [← hm]
    ring_nf
    rw [show (2 : ZMod 2) = 0 from rfl]
    ring
  simp_rw [h]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun σ _ => ?_
  rw [← Finset.mul_sum, sum_ent_supp hk ha, mul_zero]

/-! ### Choosing the values of new variables -/

variable {r : ℕ} {A : Finset (ICls I)} {D : Desc I}

lemma card_insert_Iloc (hcard : A.card ≤ k) (v : Fin I.numLocations) (d : Coord k ℓ) :
    (insert d (Iloc A v)).card ≤ k + 1 :=
  (Finset.card_insert_le _ _).trans (by have := card_Iloc_le A v; omega)

lemma card_insert_Isch (hcard : A.card ≤ k) (e : Fin I.schemas.length) (c : Coord k ℓ) :
    (insert c (Isch A e)).card ≤ k + 1 :=
  (Finset.card_insert_le _ _).trans (by have := card_Isch_le A e; omega)

/-- The address of the equation, as seen at an argument location. -/
lemma supp_arg_subset {e : Fin I.schemas.length} {c : Coord k ℓ} {a : Fin k → BlockCoord ℓ}
    (hs : supp a ⊆ insert c (Isch A e)) (i : Fin (arity (sch I e))) :
    supp ((argPerm (sch I e) i).act a) ⊆
      insert ((argPerm (sch I e) i).apply c) (Iloc A (argLoc (sch I e) i)) := by
  rw [supp_act]
  intro d hd
  obtain ⟨c', hc', rfl⟩ := Finset.mem_image.mp hd
  rcases Finset.mem_insert.mp (hs hc') with rfl | h
  · exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem (Isch_args h i)

lemma mem_supp_arg {e : Fin I.schemas.length} {c : Coord k ℓ} {a : Fin k → BlockCoord ℓ}
    (hc : c ∈ supp a) (i : Fin (arity (sch I e))) :
    (argPerm (sch I e) i).apply c ∈ supp ((argPerm (sch I e) i).act a) := by
  rw [supp_act]; exact Finset.mem_image_of_mem _ hc

/-- **Extending exposed values.** Values for the variables newly exposed at the argument
locations, consistent with `K_r` and with the newly exposed equation. -/
lemma choose_values (hG : Good (r + 1) A D) (hA : AllValid A)
    (hcard : A.card ≤ k) (e : Fin I.schemas.length) {c : Coord k ℓ} (hc : c ∉ Isch A e)
    (hcd : c ∈ dom I e) :
    ∃ p : Fin (arity (sch I e)) → ZMod 2,
      (∀ i a b, IsAddress a →
        supp a ⊆ insert ((argPerm (sch I e) i).apply c) (Iloc A (argLoc (sch I e) i)) →
        (argPerm (sch I e) i).apply c ∈ supp a →
        (argPerm (sch I e) i).apply c ∉ Iloc A (argLoc (sch I e) i) →
        ((argLoc (sch I e) i, a), b) ∈ I.toParitySystem.known r → p i = b) ∧
      (∀ a, IsAddress a → supp a ⊆ insert c (Isch A e) → c ∈ supp a →
        ∑ i, (if (argPerm (sch I e) i).apply c ∈ Iloc A (argLoc (sch I e) i) then
          dot (ind ((argPerm (sch I e) i).act a)) (D.z (argLoc (sch I e) i)) else p i) = 0) := by
  classical
  set s := sch I e
  set L := argLoc s
  set P := argPerm s
  set d : Fin (arity s) → Coord k ℓ := fun i => (P i).apply c
  set J : Fin (arity s) → Finset (Coord k ℓ) := fun i => Iloc A (L i)
  have hnc : ¬ I.toParitySystem.HasConflict r :=
    fun h => hG.noConflict (hasConflict_mono I (Nat.le_succ r) h)
  -- facts about new addresses
  let NewFact : Fin (arity s) → ZMod 2 → Prop := fun i b => ∃ a, IsAddress a ∧
    supp a ⊆ insert (d i) (J i) ∧ d i ∈ supp a ∧ ((L i, a), b) ∈ I.toParitySystem.known r
  have hnf_unique : ∀ i b b', NewFact i b → NewFact i b' → b = b' := by
    rintro i b b' ⟨a, ha, hs, -, hb⟩ ⟨a', ha', hs', -, hb'⟩
    have := address_unique ha ha' (card_insert_Iloc hcard _ _) hs hs'
    subst this
    exact fact_unique hnc hb hb'
  let p0 : Fin (arity s) → ZMod 2 := fun i => if h : ∃ b, NewFact i b then h.choose else 0
  have hp0 : ∀ i b, NewFact i b → p0 i = b := by
    intro i b hb
    have h : ∃ b, NewFact i b := ⟨b, hb⟩
    simp only [p0, dif_pos h]
    exact hnf_unique i _ _ h.choose_spec hb
  have hP1 : ∀ p : Fin (arity s) → ZMod 2, (∀ i, (∃ b, NewFact i b) → p i = p0 i) →
      ∀ i a b, IsAddress a → supp a ⊆ insert (d i) (J i) → d i ∈ supp a → d i ∉ J i →
        ((L i, a), b) ∈ I.toParitySystem.known r → p i = b := by
    intro p hp i a b ha hs hda _ hb
    have hnf : NewFact i b := ⟨a, ha, hs, hda, hb⟩
    rw [hp i ⟨b, hnf⟩, hp0 i b hnf]
  by_cases hex : ∃ a, IsAddress a ∧ supp a ⊆ insert c (Isch A e) ∧ c ∈ supp a
  swap
  · push Not at hex
    exact ⟨p0, hP1 p0 fun _ _ => rfl, fun a ha hs hca => absurd hca (hex a ha hs)⟩
  obtain ⟨a, ha, hsa, hca⟩ := hex
  have hJcard := card_insert_Isch hcard e c
  have hdom : insert c (Isch A e) ⊆ dom I e :=
    Finset.insert_subset hcd (Isch_subset hA e)
  -- the only address of the newly exposed equation
  have huniq : ∀ a', IsAddress a' → supp a' ⊆ insert c (Isch A e) → a' = a :=
    fun a' ha' hs' => address_unique ha' ha hJcard hs' hsa
  have hsi : ∀ i, supp ((P i).act a) ⊆ insert (d i) (J i) := fun i => supp_arg_subset hsa i
  have hdi : ∀ i, d i ∈ supp ((P i).act a) := fun i => mem_supp_arg hca i
  have hai : ∀ i, IsAddress ((P i).act a) := fun i => isAddress_act _ ha
  -- old variables are covered by the old coordinate set
  have hold_supp : ∀ i, d i ∈ J i → supp ((P i).act a) ⊆ J i := by
    intro i hi
    have := hsi i
    rwa [Finset.insert_eq_of_mem hi] at this
  -- at most one argument variable was exposed before
  have hone : ∀ i j, i ≠ j → d i ∈ J i → d j ∈ J j → False := by
    intro i j hij hi hj
    exact hc (geometry hcard e hij (hold_supp i hi) (hold_supp j hj) hca)
  -- a fact at a new location is a fact about the equation's variable
  have hnf_eq : ∀ i b, NewFact i b → ((L i, (P i).act a), b) ∈ I.toParitySystem.known r := by
    rintro i b ⟨a', ha', hs', -, hb⟩
    have := address_unique ha' (hai i) (card_insert_Iloc hcard _ _) hs' (hsi i)
    rwa [this] at hb
  let val : (Fin (arity s) → ZMod 2) → Fin (arity s) → ZMod 2 := fun p i =>
    if d i ∈ J i then dot (ind ((P i).act a)) (D.z (L i)) else p i
  have hP2 : ∀ p : Fin (arity s) → ZMod 2, ∑ i, val p i = 0 →
      ∀ a', IsAddress a' → supp a' ⊆ insert c (Isch A e) → c ∈ supp a' →
        ∑ i, (if d i ∈ J i then dot (ind ((P i).act a')) (D.z (L i)) else p i) = 0 := by
    intro p hp a' ha' hs' _
    rw [huniq a' ha' hs']
    exact hp
  by_cases hfree : ∃ i₀, d i₀ ∉ J i₀ ∧ ¬ ∃ b, NewFact i₀ b
  · obtain ⟨i₀, hi₀, hnf₀⟩ := hfree
    let p := Function.update p0 i₀ (∑ i ∈ Finset.univ.erase i₀, val p0 i)
    refine ⟨p, hP1 p fun i hi => ?_, hP2 p ?_⟩
    · have : i ≠ i₀ := by rintro rfl; exact hnf₀ hi
      simp [p, Function.update_of_ne this]
    · rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)]
      have h1 : val p i₀ = ∑ i ∈ Finset.univ.erase i₀, val p0 i := by
        simp [val, hi₀, p]
      have h2 : ∑ i ∈ Finset.univ.erase i₀, val p i = ∑ i ∈ Finset.univ.erase i₀, val p0 i :=
        Finset.sum_congr rfl fun i hi => by
          simp [val, p, Function.update_of_ne (Finset.ne_of_mem_erase hi)]
      rw [h1, h2, zmod2_add_self]
  · push Not at hfree
    refine ⟨p0, hP1 p0 fun _ _ => rfl, hP2 p0 ?_⟩
    -- every new variable has a fact in `K_r`
    have hfacts : ∀ i, d i ∉ J i → ((L i, (P i).act a), p0 i) ∈ I.toParitySystem.known r := by
      intro i hi
      obtain ⟨b, hb⟩ := hfree i hi
      rw [hp0 i b hb]
      exact hnf_eq i b hb
    by_cases hold : ∃ i₁, d i₁ ∈ J i₁
    · obtain ⟨i₁, hi₁⟩ := hold
      have hnew : ∀ i, i ≠ i₁ → d i ∉ J i := fun i hi h => hone i i₁ hi h hi₁
      have hinf := infer I e ha (hsa.trans hdom) i₁ (val p0)
        (r := r) fun i hi => by
          simp only [val, if_neg (hnew i hi)]
          exact hfacts i (hnew i hi)
      have hval := hG.agree (L i₁) _ _ (hai i₁) (hold_supp i₁ hi₁) hinf
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₁)]
      have : val p0 i₁ = dot (ind ((P i₁).act a)) (D.z (L i₁)) := by simp [val, hi₁]
      rw [this, hval, zmod2_add_self]
    · push Not at hold
      let i₀ : Fin (arity s) := ⟨0, arity_pos s⟩
      have hinf := infer I e ha (hsa.trans hdom) i₀ (val p0) (r := r) fun i _ => by
        simp only [val, if_neg (hold i)]
        exact hfacts i (hold i)
      have h0 : ((L i₀, (P i₀).act a), val p0 i₀) ∈ I.toParitySystem.known (r + 1) := by
        simp only [val, if_neg (hold i₀)]
        exact known_mono I (Nat.le_succ r) (hfacts i₀ (hold i₀))
      have := fact_unique hG.noConflict hinf h0
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀), ← this, zmod2_add_self]

lemma Iloc_insert_inner {X : ICls I} {e : Fin I.schemas.length} {c : Coord k ℓ}
    (hX : inner X = some (e, c)) (v : Fin I.numLocations) :
    Iloc (insert X A) v = argContrib I e c v ∪ Iloc A v := by
  rw [Iloc_insert, locContrib_of_inner hX]

lemma argContrib_of_not_loc {e : Fin I.schemas.length} {c : Coord k ℓ} {v : Fin I.numLocations}
    (h : ∀ i, argLoc (sch I e) i ≠ v) : argContrib I e c v = ∅ := by
  ext d
  simp only [Finset.notMem_empty, iff_false]
  intro hd
  obtain ⟨i, hi, -⟩ := mem_argContrib.mp hd
  exact h i hi

lemma argContrib_union_loc (e : Fin I.schemas.length) (c : Coord k ℓ) (i : Fin (arity (sch I e))) :
    argContrib I e c (argLoc (sch I e) i) ∪ Iloc A (argLoc (sch I e) i) =
      insert ((argPerm (sch I e) i).apply c) (Iloc A (argLoc (sch I e) i)) := by
  rw [argContrib_self, Finset.insert_eq]

/-- Extension of the argument seeds for a new internal coordinate `c` of schema `e`. -/
lemma extend_seeds (hk : 2 ≤ k) (hG : Good (r + 1) A D) (hA : AllValid A) (hcard : A.card ≤ k)
    (e : Fin I.schemas.length) {c : Coord k ℓ} (hc : c ∉ Isch A e) (hcd : c ∈ dom I e) :
    ∃ z' : Fin I.numLocations → Vec k ℓ,
      (∀ v, ∀ d ∈ Iloc A v, z' v d = D.z v d) ∧
      (∀ v, (I.init v).isSome → z' v = initSeed I v) ∧
      (∀ v, EvenKills (z' v) (argContrib I e c v ∪ Iloc A v)) ∧
      (∀ v a b, IsAddress a → supp a ⊆ argContrib I e c v ∪ Iloc A v →
        ((v, a), b) ∈ I.toParitySystem.known r → dot (ind a) (z' v) = b) ∧
      (∀ a, IsAddress a → supp a ⊆ insert c (Isch A e) →
        ∑ i, dot (ind ((argPerm (sch I e) i).act a)) (z' (argLoc (sch I e) i)) = 0) := by
  classical
  set s := sch I e
  set L := argLoc s
  set P := argPerm s
  obtain ⟨p, hp1, hp2⟩ := choose_values hG hA hcard e hc hcd
  have hext : ∀ i, ∃ zv : Vec k ℓ, (∀ d' ∈ Iloc A (L i), zv d' = D.z (L i) d') ∧
      ((I.init (L i)).isSome → zv = initSeed I (L i)) ∧
      EvenKills zv (insert ((P i).apply c) (Iloc A (L i))) ∧
      (∀ a, IsAddress a → supp a ⊆ insert ((P i).apply c) (Iloc A (L i)) →
        (P i).apply c ∈ supp a → (P i).apply c ∉ Iloc A (L i) → dot (ind a) zv = p i) ∧
      (∀ a b, IsAddress a → supp a ⊆ insert ((P i).apply c) (Iloc A (L i)) →
        ((L i, a), b) ∈ I.toParitySystem.known r → dot (ind a) zv = b) := fun i =>
    extend_loc (by omega) hG (L i) ((P i).apply c) (card_insert_Iloc hcard _ _)
      (Finset.insert_subset (argPerm_mem (sch_wf I e) hcd i) (Iloc_subset hA _)) (p i)
      (fun a b ha hs hda hdn hb => hp1 i a b ha hs hda hdn hb)
  choose zv hzv1 hzv2 hzv3 hzv4 hzv5 using hext
  let z' : Fin I.numLocations → Vec k ℓ := fun v => if h : ∃ i, L i = v then zv h.choose else D.z v
  have hz'L : ∀ i, z' (L i) = zv i := by
    intro i
    have h : ∃ i', L i' = L i := ⟨i, rfl⟩
    simp only [z', dif_pos h]
    rw [argLoc_injective (sch_wf I e) h.choose_spec]
  have hz'N : ∀ v, (¬ ∃ i, L i = v) → z' v = D.z v := fun v h => by simp only [z', dif_neg h]
  refine ⟨z', fun v d hd => ?_, fun v hv => ?_, fun v => ?_, fun v a b ha hs hb => ?_,
    fun a ha hs => ?_⟩
  · by_cases h : ∃ i, L i = v
    · obtain ⟨i, rfl⟩ := h; rw [hz'L]; exact hzv1 i d hd
    · rw [hz'N v h]
  · by_cases h : ∃ i, L i = v
    · obtain ⟨i, rfl⟩ := h; rw [hz'L]; exact hzv2 i hv
    · rw [hz'N v h]; exact hG.init v hv
  · by_cases h : ∃ i, L i = v
    · obtain ⟨i, rfl⟩ := h; rw [hz'L, argContrib_union_loc]; exact hzv3 i
    · push Not at h
      rw [hz'N v (by push Not; exact h), argContrib_of_not_loc h, Finset.empty_union]
      exact hG.even v
  · by_cases h : ∃ i, L i = v
    · obtain ⟨i, rfl⟩ := h
      rw [hz'L]; rw [argContrib_union_loc] at hs; exact hzv5 i a b ha hs hb
    · push Not at h
      rw [hz'N v (by push Not; exact h)]
      rw [argContrib_of_not_loc h, Finset.empty_union] at hs
      exact hG.agree v a b ha hs (known_mono I (Nat.le_succ r) hb)
  · simp_rw [hz'L]
    by_cases hca : c ∈ supp a
    · rw [← hp2 a ha hs hca]
      refine Finset.sum_congr rfl fun i _ => ?_
      split
      · next hi =>
        have hsub : supp ((P i).act a) ⊆ Iloc A (L i) := by
          have := supp_arg_subset hs i
          rwa [Finset.insert_eq_of_mem hi] at this
        exact dot_congr_suppIn (suppIn_ind.mpr hsub) (hzv1 i)
      · next hi =>
        exact hzv4 i _ (isAddress_act _ ha) (supp_arg_subset hs i) (mem_supp_arg hca i) hi
    · have hsub : supp a ⊆ Isch A e := by
        intro x hx
        rcases Finset.mem_insert.mp (hs hx) with rfl | h
        · exact absurd hx hca
        · exact h
      rw [← eq_of_ms hk D e ha fun c' hc' => hG.ms e c' (hsub hc')]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hsub' : supp ((P i).act a) ⊆ Iloc A (L i) := by
        rw [supp_act]
        intro d hd
        obtain ⟨c', hc', rfl⟩ := Finset.mem_image.mp hd
        exact Isch_args (hsub hc') i
      exact dot_congr_suppIn (suppIn_ind.mpr hsub') (hzv1 i)

end Lax119563Proofs.Matrix

end Matrix_ExtendSeeds

/-! ### Formerly `Lax119563Proofs.Matrix.Extension` -/

section Matrix_Extension

/-!
# The local extension lemma

From a description satisfying the invariant for the retained classes `A` (`|A| ≤ k`) and an
announced class `X`, we construct a description satisfying the invariant for `A ∪ {X}` with
one round less, without changing the translation of any retained class. For a new internal
coordinate the coefficients are repaired in a repetition untouched by `A`.
-/

open Lax119563.ImplicitParitySystems Lax119563.MatrixCompiler Lax119563.ParitySystems

namespace Lax119563Proofs.Matrix

variable {k ℓ : ℕ} {I : ImplicitParitySystem k ℓ}

/-! ### Corrections of the coefficients in one repetition -/

/-- The correction of the coefficients: `μ` in repetition `h` of schema `e`. -/
def corrLam (hM : 0 < k - 1 + ℓ) (e : Fin I.schemas.length) (h : ℕ)
    (μ : Fin (k - 1) ⊕ Fin ℓ → ZMod 2) (e' : Fin I.schemas.length) (σ : ℕ) : ZMod 2 :=
  if e' = e ∧ σ / (k - 1 + ℓ) = h then μ (stepRow hM σ) else 0

lemma stepRow_add (hM : 0 < k - 1 + ℓ) (h j : ℕ) (hj : j < k - 1 + ℓ) :
    stepRow hM (h * (k - 1 + ℓ) + j) = finSumFinEquiv.symm ⟨j, hj⟩ := by
  simp only [stepRow]
  congr 2
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]

/-- The accumulated correction of column `c` up to stage `σ`. -/
lemma sum_corr (hk : 2 ≤ k) (e : Fin I.schemas.length) (h : ℕ)
    (μ : Fin (k - 1) ⊕ Fin ℓ → ZMod 2) (c : Coord k ℓ) (σ : ℕ) :
    (σ ≤ h * (k - 1 + ℓ) →
      ∑ σ' ∈ Finset.range σ, corrLam (I := I) (by omega) e h μ e σ' * ent σ' c = 0) ∧
    ((h + 1) * (k - 1 + ℓ) ≤ σ →
      ∑ σ' ∈ Finset.range σ, corrLam (I := I) (by omega) e h μ e σ' * ent σ' c =
        ∑ j, μ j * checkMatrix k ℓ j c) := by
  have hM : 0 < k - 1 + ℓ := by omega
  have hlow : ∀ σ' < h * (k - 1 + ℓ), corrLam (I := I) hM e h μ e σ' = 0 := by
    intro σ' hσ'
    simp only [corrLam, true_and]
    rw [if_neg]
    exact ((Nat.div_lt_iff_lt_mul hM).mpr hσ').ne
  have hhigh : ∀ σ', (h + 1) * (k - 1 + ℓ) ≤ σ' → corrLam (I := I) hM e h μ e σ' = 0 := by
    intro σ' hσ'
    simp only [corrLam, true_and]
    rw [if_neg]
    exact (Nat.lt_of_lt_of_le (Nat.lt_succ_self h) ((Nat.le_div_iff_mul_le hM).mpr hσ')).ne'
  constructor
  · intro hσ
    exact Finset.sum_eq_zero fun σ' hσ' => by
      rw [hlow σ' (lt_of_lt_of_le (Finset.mem_range.mp hσ') hσ), zero_mul]
  · intro hσ
    obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hσ
    rw [Finset.sum_range_add, Finset.sum_eq_zero (s := Finset.range t) fun x _ => by
      rw [hhigh _ (Nat.le_add_right _ _), zero_mul], add_zero]
    rw [show (h + 1) * (k - 1 + ℓ) = h * (k - 1 + ℓ) + (k - 1 + ℓ) by ring, Finset.sum_range_add,
      Finset.sum_eq_zero (s := Finset.range (h * (k - 1 + ℓ))) fun x hx => by
        rw [hlow _ (Finset.mem_range.mp hx), zero_mul], zero_add]
    rw [Finset.sum_range]
    have : ∀ j : Fin (k - 1 + ℓ),
        corrLam (I := I) hM e h μ e (h * (k - 1 + ℓ) + j) * ent (h * (k - 1 + ℓ) + j) c =
          μ (finSumFinEquiv.symm j) * checkMatrix k ℓ (finSumFinEquiv.symm j) c := by
      intro j
      have hdiv : (h * (k - 1 + ℓ) + j) / (k - 1 + ℓ) = h := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ hM, Nat.div_eq_of_lt j.2, zero_add]
      simp only [corrLam, true_and, ent_eq hk]
      rw [if_pos hdiv, stepRow_add hM h j j.2]
    simp_rw [this]
    exact Equiv.sum_comp finSumFinEquiv.symm fun j => μ j * checkMatrix k ℓ j c

/-! ### Untouched repetitions -/

/-- The schema and repetition touched by a class. -/
def touch : ICls I → Option (Fin I.schemas.length × ℕ)
  | .track e σ _ => some (e, σ / (k - 1 + ℓ))
  | .upd e σ _ => some (e, σ / (k - 1 + ℓ))
  | .coef e σ => some (e, σ / (k - 1 + ℓ))
  | _ => none

/-- The repetitions of schema `e` touched by a class. -/
def touchSet (e : Fin I.schemas.length) (Y : ICls I) : Finset ℕ :=
  match touch Y with
  | some (e', h) => if e' = e then {h} else ∅
  | none => ∅

lemma card_touchSet_le (e : Fin I.schemas.length) (Y : ICls I) : (touchSet e Y).card ≤ 1 := by
  unfold touchSet
  split
  · split <;> simp
  · simp

lemma exists_untouched {A : Finset (ICls I)} (hcard : A.card ≤ k) (e : Fin I.schemas.length) :
    ∃ h < k + 1, ∀ Y ∈ A, touch Y ≠ some (e, h) := by
  classical
  let S := A.biUnion (touchSet e)
  have hS : S.card ≤ k := by
    refine (Finset.card_biUnion_le).trans (le_trans ?_ hcard)
    simpa using Finset.sum_le_sum fun Y (_ : Y ∈ A) => card_touchSet_le e Y
  obtain ⟨h, hh, hnot⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := S) (t := Finset.range (k + 1)) (by simp; omega)
  refine ⟨h, Finset.mem_range.mp hh, fun Y hY hYt => hnot ?_⟩
  exact Finset.mem_biUnion.mpr ⟨Y, hY, by simp [touchSet, hYt]⟩

lemma lt_or_ge_of_div_ne {σ h M : ℕ} (hM : 0 < M) (hne : σ / M ≠ h) :
    σ + 1 ≤ h * M ∨ (h + 1) * M ≤ σ := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · left
    have := (Nat.div_lt_iff_lt_mul hM).mp hlt
    omega
  · right
    exact (Nat.le_div_iff_mul_le hM).mp hgt

/-! ### The extension lemma -/

variable {r : ℕ} {A : Finset (ICls I)} {D : Desc I}

lemma good_of_contrib (hG : Good (r + 1) A D) {X : ICls I}
    (hloc : ∀ v, locContrib X v ⊆ Iloc A v) (hsch : ∀ e, schContrib X e ⊆ Isch A e) :
    Good r (insert X A) D := by
  have h1 : ∀ v, Iloc (insert X A) v = Iloc A v := fun v => by
    rw [Iloc_insert, Finset.union_eq_right.mpr (hloc v)]
  have h2 : ∀ e, Isch (insert X A) e = Isch A e := fun e => by
    rw [Isch_insert, Finset.union_eq_right.mpr (hsch e)]
  have hG' := hG.mono (Nat.le_succ r) le_rfl
  exact ⟨hG'.init, fun e c hc => hG'.ms e c (h2 e ▸ hc), fun v => (h1 v).symm ▸ hG'.even v,
    fun v a b ha hs hb => hG'.agree v a b ha ((h1 v) ▸ hs) hb, hG'.noConflict⟩

/-- **Local extension.** -/
theorem extend (hk : 2 ≤ k) (hG : Good (r + 1) A D) (hA : AllValid A) (hcard : A.card ≤ k)
    {X : ICls I} (hX : ClsValid I X) :
    ∃ D' : Desc I, Good r (insert X A) D' ∧ ∀ Y ∈ A, shift D' Y = shift D Y := by
  classical
  have hM : 0 < k - 1 + ℓ := by omega
  have hnc : ¬ I.toParitySystem.HasConflict r :=
    fun h => hG.noConflict (hasConflict_mono I (Nat.le_succ r) h)
  cases hin : inner X with
  | none =>
    rcases inner_none hin with ⟨v, d, rfl⟩ | ⟨e, σ, rfl⟩
    swap
    · -- a coefficient class
      exact ⟨D, good_of_contrib hG (fun v => by simp [locContrib])
        (fun e => by simp [schContrib, inner]), fun _ _ => rfl⟩
    -- a coordinate class
    by_cases hd : d ∈ Iloc A v
    · refine ⟨D, good_of_contrib hG (fun v' => ?_) (fun e => by simp [schContrib, inner]),
        fun _ _ => rfl⟩
      simp only [locContrib]
      split
      · next h => subst h; simpa using hd
      · simp
    let NewFact : ZMod 2 → Prop := fun b => ∃ a, IsAddress a ∧
      supp a ⊆ insert d (Iloc A v) ∧ d ∈ supp a ∧ ((v, a), b) ∈ I.toParitySystem.known r
    let p : ZMod 2 := if h : ∃ b, NewFact b then h.choose else 0
    have hp : ∀ a b, IsAddress a → supp a ⊆ insert d (Iloc A v) → d ∈ supp a → d ∉ Iloc A v →
        ((v, a), b) ∈ I.toParitySystem.known r → p = b := by
      intro a b ha hs hda _ hb
      have h : ∃ b, NewFact b := ⟨b, a, ha, hs, hda, hb⟩
      simp only [p, dif_pos h]
      obtain ⟨a', ha', hs', -, hb'⟩ := h.choose_spec
      have := address_unique ha' ha (card_insert_Iloc hcard v d) hs' hs
      subst this
      exact fact_unique hnc hb' hb
    obtain ⟨zv, hz1, hz2, hz3, -, hz5⟩ := extend_loc (by omega) hG v d (card_insert_Iloc hcard v d)
      (Finset.insert_subset hX (Iloc_subset hA v)) p hp
    let D' : Desc I := ⟨Function.update D.z v zv, D.lam⟩
    have hIloc : ∀ v', Iloc (insert (Cls.coord v d) A) v' =
        if v = v' then insert d (Iloc A v') else Iloc A v' := by
      intro v'
      rw [Iloc_insert]
      simp only [locContrib]
      split
      · next h => subst h; rw [Finset.insert_eq]
      · simp
    have hzA : ∀ v', ∀ d' ∈ Iloc A v', D'.z v' d' = D.z v' d' := by
      intro v' d' hd'
      by_cases h : v' = v
      · subst h; simp [D', hz1 d' hd']
      · simp [D', Function.update_of_ne h]
    have hshift : ∀ Y ∈ A, shift D' Y = shift D Y := fun Y hY =>
      shift_eq_of_z Y (fun v' d' hd' => hzA v' d' (Finset.mem_biUnion.mpr ⟨Y, hY, hd'⟩)) rfl
    refine ⟨D', ⟨fun v' hv' => ?_, fun e c hc => ?_, fun v' => ?_, fun v' a b ha hs hb => ?_,
      hnc⟩, hshift⟩
    · by_cases h : v' = v
      · subst h; simp [D', hz2 hv']
      · simp [D', Function.update_of_ne h, hG.init v' hv']
    · have hc' : c ∈ Isch A e := by
        rw [Isch_insert] at hc
        simpa [schContrib, inner] using hc
      have hagree : ArgsAgree D D' e c := fun i => hzA _ _ (Isch_args hc' i)
      rw [MS, T_congr hagree fun _ _ => rfl, hagree.End]
      exact hG.ms e c hc'
    · rw [hIloc]
      split
      · next h => subst h; simpa [D'] using hz3
      · next h => simpa [D', Function.update_of_ne (Ne.symm h)] using hG.even v'
    · rw [hIloc] at hs
      split at hs
      · next h => subst h; simpa [D'] using hz5 a b ha hs hb
      · next h =>
        simp only [D', Function.update_of_ne (Ne.symm h)]
        exact hG.agree v' a b ha hs (known_mono I (Nat.le_succ r) hb)
  | some p =>
    obtain ⟨e, c⟩ := p
    by_cases hc : c ∈ Isch A e
    · -- the coordinate is already pebbled
      refine ⟨D, good_of_contrib hG (fun v => ?_) (fun e' => ?_), fun _ _ => rfl⟩
      · rw [locContrib_of_inner hin]
        intro d hd
        obtain ⟨i, rfl, rfl⟩ := mem_argContrib.mp hd
        exact Isch_args hc i
      · rw [schContrib_of_inner hin]
        split
        · next h => subst h; simpa using hc
        · simp
    have hcd : c ∈ dom I e := hX.inner_dom hin
    obtain ⟨z', hz1, hz2, hz3, hz4, hz5⟩ := extend_seeds hk hG hA hcard e hc hcd
    set s := sch I e
    set L := argLoc s
    set P := argPerm s
    let D1 : Desc I := ⟨z', D.lam⟩
    -- the new seeds agree with the old ones at all retained argument coordinates
    have hagree : ∀ c' ∈ Isch A e, ArgsAgree D D1 e c' := fun c' hc' i =>
      hz1 _ _ (Isch_args hc' i)
    let bsum : Coord k ℓ → ZMod 2 := fun c' => ∑ i, z' (L i) ((P i).apply c')
    let Λ : Coord k ℓ → ZMod 2 := fun c' =>
      ∑ σ ∈ Finset.range (numSteps k ℓ), D.lam e σ * ent σ c'
    have hbΛ : ∀ c' ∈ Isch A e, bsum c' + Λ c' = 0 := by
      intro c' hc'
      have hms := hG.ms e c' hc'
      rw [MS, T] at hms
      have h1 : bsum c' = t0 D e c' + D.z (locEnd s) ((permEnd s).apply c') := by
        rw [t0_add_end]
        exact Finset.sum_congr rfl fun i _ => hagree c' hc' i
      rw [h1, ← hms]
      simp only [Λ]
      rw [← add_assoc (t0 D e c'), zmod2_add_self, zero_add, zmod2_add_self]
    set J := insert c (Isch A e)
    let t : Vec k ℓ := fun c' => if c' = c then bsum c + Λ c else 0
    have ht : ∀ y, IsCode y → SuppIn y J → dot y t = 0 := by
      intro y hy hyJ
      have e1 : dot y t = ∑ c', y c' * (bsum c' + Λ c') := by
        refine Finset.sum_congr rfl fun c' _ => ?_
        by_cases h1 : c' = c
        · subst h1; simp [t]
        · by_cases h2 : c' ∈ Isch A e
          · simp [t, h1, hbΛ c' h2]
          · have : y c' = 0 := hyJ c' (by simp [J, h1, h2])
            simp [t, h1, this]
      rw [e1]
      simp only [mul_add, Finset.sum_add_distrib]
      have hΛ : ∑ c', y c' * Λ c' = 0 := by
        simp only [Λ, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_eq_zero fun σ _ => ?_
        have := sum_ent_code hk hy σ
        rw [← mul_zero (D.lam e σ), ← this, Finset.mul_sum]
        exact Finset.sum_congr rfl fun c' _ => by ring
      rw [hΛ, add_zero]
      have hb : ∑ c', y c' * bsum c' = ∑ i, dot (permVec (P i) y) (z' (L i)) := by
        simp only [bsum, Finset.mul_sum, dot_permVec]
        exact Finset.sum_comm
      rw [hb]
      have hpar := hy.blockSum_eq (by omega)
      rcases zmod2_eq_zero_or_one (blockSum y ⟨0, by omega⟩) with h0 | h1
      · refine Finset.sum_eq_zero fun i _ => hz3 (L i) _ (isCode_permVec (by omega) _ hy)
          (fun i' => by rw [blockSum_permVec', hpar _ ⟨0, by omega⟩, h0]) ?_
        intro d hd
        apply suppIn_permVec (P i) hyJ d
        intro hd'
        apply hd
        obtain ⟨c', hc', rfl⟩ := Finset.mem_image.mp hd'
        rcases Finset.mem_insert.mp hc' with rfl | h
        · exact Finset.mem_union_left _ (by rw [argContrib_self]; exact Finset.mem_singleton_self _)
        · exact Finset.mem_union_right _ (Isch_args h i)
      · obtain ⟨a, ha, rfl⟩ := exists_address_of_odd (by omega) hy
          (fun i' => by rw [hpar i' ⟨0, by omega⟩, h1]) hyJ (card_insert_Isch hcard e c)
        simp_rw [← ind_act]
        exact hz5 a ha (suppIn_ind.mp hyJ)
    obtain ⟨μ, hμ⟩ := exists_rowComb J t ht
    obtain ⟨h, hh, huntouched⟩ := exists_untouched hcard e
    let D' : Desc I := ⟨z', fun e' σ => D.lam e' σ + corrLam (I := I) hM e h μ e' σ⟩
    have hT_other : ∀ e', e' ≠ e → ∀ c' σ, T D' e' c' σ = T D1 e' c' σ := by
      intro e' he' c' σ
      simp [T, D', D1, corrLam, he', Matrix.t0]
    have hT_e : ∀ c' σ, T D' e c' σ =
        T D1 e c' σ + ∑ σ' ∈ Finset.range σ, corrLam (I := I) hM e h μ e σ' * ent σ' c' := by
      intro c' σ
      simp only [T, D', D1, Matrix.t0, add_mul, Finset.sum_add_distrib, add_assoc]
    have hγ : ∀ c' ∈ J, ∑ j, μ j * checkMatrix k ℓ j c' = t c' := hμ
    have hN : (h + 1) * (k - 1 + ℓ) ≤ numSteps k ℓ := by
      unfold numSteps; exact Nat.mul_le_mul_right _ hh
    -- retained columns are unchanged at stages outside the repaired repetition
    have hT_keep : ∀ c' ∈ Isch A e, ∀ σ, (σ ≤ h * (k - 1 + ℓ) ∨ (h + 1) * (k - 1 + ℓ) ≤ σ) →
        T D' e c' σ = T D e c' σ := by
      intro c' hc' σ hσ
      rw [hT_e, T_congr (hagree c' hc') fun _ _ => rfl]
      rcases hσ with hσ | hσ
      · rw [(sum_corr hk e h μ c' σ).1 hσ, add_zero]
      · rw [(sum_corr hk e h μ c' σ).2 hσ, hγ c' (Finset.mem_insert_of_mem hc')]
        simp [t, show c' ≠ c from fun h' => hc (h' ▸ hc')]
    have hIloc : ∀ v, Iloc (insert X A) v = argContrib I e c v ∪ Iloc A v :=
      Iloc_insert_inner hin
    have hIsch : ∀ e', Isch (insert X A) e' = (if e = e' then {c} else ∅) ∪ Isch A e' := by
      intro e'; rw [Isch_insert, schContrib_of_inner hin]
    refine ⟨D', ⟨fun v hv => hz2 v hv, fun e' c' hc' => ?_, fun v => (hIloc v).symm ▸ hz3 v,
      fun v a b ha hs hb => hz4 v a b ha ((hIloc v) ▸ hs) hb, hnc⟩, fun Y hY => ?_⟩
    · -- the mask-sum conditions
      rw [hIsch] at hc'
      by_cases he : e = e'
      · subst he
        rcases Finset.mem_union.mp hc' with h1 | h1
        · rw [if_pos rfl, Finset.mem_singleton] at h1
          subst h1
          rw [MS, hT_e, (sum_corr hk e h μ c' _).2 hN, hγ c' (Finset.mem_insert_self _ _)]
          simp only [t, if_true]
          have hb : bsum c' = t0 D1 e c' + z' (locEnd s) ((permEnd s).apply c') := by
            rw [t0_add_end]
          rw [T, hb]
          show t0 D1 e c' + Λ c' + (t0 D1 e c' + z' (locEnd s) ((permEnd s).apply c') +
            Λ c') = _
          ring_nf
          rw [show (2 : ZMod 2) = 0 from rfl]
          ring
        · rw [MS, hT_keep c' h1 _ (Or.inr hN)]
          have := hG.ms e c' h1
          rw [MS] at this
          rw [this]
          exact ((hagree c' h1).End).symm
      · rw [if_neg he, Finset.empty_union] at hc'
        have ha' : ArgsAgree D D1 e' c' := fun i => hz1 _ _ (Isch_args hc' i)
        rw [MS, hT_other e' (Ne.symm he), T_congr ha' fun _ _ => rfl]
        have := hG.ms e' c' hc'
        rw [MS] at this
        rw [this]
        exact ha'.End.symm
    · -- retained translations
      have hzY : ∀ v, ∀ d ∈ locContrib Y v, z' v d = D.z v d :=
        fun v d hd => hz1 v d (Finset.mem_biUnion.mpr ⟨Y, hY, hd⟩)
      have hT : ∀ e' c' σ, inner Y = some (e', c') →
          (e' = e → σ ≤ h * (k - 1 + ℓ) ∨ (h + 1) * (k - 1 + ℓ) ≤ σ) →
          T D' e' c' σ = T D e' c' σ := by
        intro e' c' σ hY' hσ
        have ha := argsAgree_of (D := D) (D' := D1) hY' hzY
        by_cases he : e' = e
        · subst he
          exact hT_keep c' (mem_Isch.mpr ⟨Y, hY, hY'⟩) σ (hσ rfl)
        · rw [hT_other e' he, T_congr ha fun _ _ => rfl]
      have hrep : ∀ e' σ, touch Y = some (e', σ / (k - 1 + ℓ)) → e' = e →
          (σ + 1 ≤ h * (k - 1 + ℓ) ∨ (h + 1) * (k - 1 + ℓ) ≤ σ) := by
        rintro e' σ hYt rfl
        exact lt_or_ge_of_div_ne hM fun h' => huntouched Y hY (h' ▸ hYt)
      cases Y with
      | coord v d =>
        simp [shift, D', hzY v d (by simp [locContrib])]
      | sum e' c' =>
        have ha := argsAgree_of (D := D) (D' := D1) (rfl : inner (Cls.sum e' c' : ICls I) = _) hzY
        simp only [shift]
        rw [show t0 D' e' c' = t0 D1 e' c' from rfl, ha.t0]
      | junc e' c' =>
        have ha := argsAgree_of (D := D) (D' := D1) (rfl : inner (Cls.junc e' c' : ICls I) = _) hzY
        simp only [shift]
        exact Prod.ext ha.U ha.V
      | link e' c' =>
        simp only [shift]
        rw [hT e' c' _ rfl fun _ => Or.inr hN]
      | track e' σ c' =>
        simp only [shift]
        rw [hT e' c' _ rfl fun he => ?_]
        rcases hrep e' σ rfl he with h1 | h1
        · left; omega
        · right; omega
      | upd e' σ c' =>
        simp only [shift]
        rw [hT e' c' σ rfl fun he => ?_, hT e' c' (σ + 1) rfl fun he => ?_]
        · rcases hrep e' σ rfl he with h1 | h1
          · left; omega
          · right; omega
        · rcases hrep e' σ rfl he with h1 | h1
          · left; omega
          · right; omega
      | coef e' σ =>
        simp only [shift, D', corrLam]
        rw [if_neg, add_zero]
        rintro ⟨rfl, h'⟩
        exact huntouched _ hY (by simp [touch, h'])

end Lax119563Proofs.Matrix

end Matrix_Extension

/-! ### Formerly `Lax119563Proofs.Matrix.Duplicator` -/

section Matrix_Duplicator

/-!
# Duplicator's strategy

Duplicator survives `r` rounds of the bijective `(k + 1)`-pebble game on
`(matrixGraph I 0, matrixGraph I 1)` whenever `K_r` is conflict-free (Theorem
"Matrix compiler", part (II)).
-/

open Lax119563.ImplicitParitySystems Lax119563.MatrixCompiler Lax119563.ParitySystems
open Lax119563.ColoredGraphs Lax119563.PebbleGame

namespace Lax119563Proofs.Matrix

variable {k ℓ : ℕ} (I : ImplicitParitySystem k ℓ)

/-! ### Vertices and names -/

/-- The number of vertices of both graphs. -/
abbrev nV : ℕ := (vertexList I).length

variable {I}

/-- The name of a vertex. -/
def nm (i : Fin (nV I)) : VName I := (vertexList I)[(i : ℕ)]

/-- The vertex of a name in the list. -/
def idx (x : VName I) (hx : x ∈ vertexList I) : Fin (nV I) :=
  ⟨(vertexList I).idxOf x, List.idxOf_lt_length_of_mem hx⟩

lemma nm_mem (i : Fin (nV I)) : nm i ∈ vertexList I := List.getElem_mem _

lemma nm_valid (i : Fin (nV I)) : Valid I (nm i) := (mem_vertexList I _).mp (nm_mem i)

@[simp] lemma nm_idx (x : VName I) (hx : x ∈ vertexList I) : nm (idx x hx) = x :=
  List.getElem_idxOf _

@[simp] lemma idx_nm (i : Fin (nV I)) : idx (nm i) (nm_mem i) = i :=
  Fin.ext ((nodup_vertexList I).idxOf_getElem i i.2)

lemma nm_injective : Function.Injective (nm (I := I)) := by
  intro i j h
  rw [← idx_nm i, ← idx_nm j]
  simp only [idx, h]

lemma matrixGraph_color (ε ε' : ZMod 2) (i j : Fin (nV I)) :
    (matrixGraph I ε).color i = (matrixGraph I ε').color j ↔ (nm i).1 = (nm j).1 :=
  listGraph_color_eq_iff (vertexList I) (adjN I ε) (adjN_symm I ε) (adjN_irrefl I ε) Prod.fst i j

/-! ### The translation on vertices -/

/-- The bijection of a description on vertices. -/
def phiV (D : Desc I) (i : Fin (nV I)) : Fin (nV I) :=
  idx (phi D (nm i)) ((mem_vertexList I _).mpr (valid_phi D (nm_valid i)))

@[simp] lemma nm_phiV (D : Desc I) (i : Fin (nV I)) : nm (phiV D i) = phi D (nm i) := nm_idx _ _

lemma phiV_phiV (D : Desc I) (i : Fin (nV I)) : phiV D (phiV D i) = i :=
  nm_injective (by rw [nm_phiV, nm_phiV, phi_phi])

lemma phi_congr {D D' : Desc I} {x : VName I} (h : shift D' x.1 = shift D x.1) :
    phi D' x = phi D x := by
  simp only [phi, h]

/-! ### Game states -/

local notation "G₀" => matrixGraph I 0
local notation "G₁" => matrixGraph I 1

/-- The classes of the vertices of `G₀` carrying a pebble. -/
def clsOf {m : ℕ} (S : GameState m G₀ G₁) : Finset (ICls I) :=
  Finset.univ.biUnion fun j => match S j with
    | some (p, _) => {(nm p).1}
    | none => ∅

lemma mem_clsOf {m : ℕ} {S : GameState m G₀ G₁} {X : ICls I} :
    X ∈ clsOf S ↔ ∃ j p q, S j = some (p, q) ∧ (nm p).1 = X := by
  simp only [clsOf, Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, hj⟩
    split at hj
    · next p q h => exact ⟨j, p, q, h, (Finset.mem_singleton.mp hj).symm⟩
    · simp at hj
  · rintro ⟨j, p, q, h, rfl⟩
    exact ⟨j, by simp [h]⟩

lemma clsOf_valid {m : ℕ} (S : GameState m G₀ G₁) : AllValid (clsOf S) := by
  intro X hX
  obtain ⟨j, p, q, -, rfl⟩ := mem_clsOf.mp hX
  exact (nm_valid p).1

lemma card_clsOf_lift {m : ℕ} (S : GameState (m + 1) G₀ G₁) (i : Fin (m + 1)) :
    (clsOf (Function.update S i none)).card ≤ m := by
  classical
  refine (Finset.card_biUnion_le).trans ?_
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  simp only [Function.update_self, Finset.card_empty, zero_add]
  calc _ ≤ ∑ j ∈ Finset.univ.erase i, 1 := Finset.sum_le_sum fun j _ => by
          split <;> simp
    _ = m := by simp

lemma clsOf_lift_subset {m : ℕ} (S : GameState m G₀ G₁) (i : Fin m) :
    clsOf (Function.update S i none) ⊆ clsOf S := by
  intro X hX
  obtain ⟨j, p, q, h, rfl⟩ := mem_clsOf.mp hX
  by_cases hji : j = i
  · subst hji; simp at h
  · rw [Function.update_of_ne hji] at h
    exact mem_clsOf.mpr ⟨j, p, q, h, rfl⟩

lemma clsOf_place {m : ℕ} (S : GameState m G₀ G₁) (i : Fin m) (p q : Fin (nV I)) :
    clsOf (Function.update S i (some (p, q))) = insert (nm p).1 (clsOf (Function.update S i none)) := by
  ext X
  simp only [mem_clsOf, Finset.mem_insert]
  constructor
  · rintro ⟨j, p', q', h, rfl⟩
    by_cases hji : j = i
    · subst hji; simp at h; obtain ⟨rfl, rfl⟩ := h; exact Or.inl rfl
    · rw [Function.update_of_ne hji] at h
      exact Or.inr ⟨j, p', q', by rw [Function.update_of_ne hji]; exact h, rfl⟩
  · rintro (rfl | ⟨j, p', q', h, rfl⟩)
    · exact ⟨i, p, q, by simp, rfl⟩
    · by_cases hji : j = i
      · subst hji; simp at h
      · exact ⟨j, p', q', by rw [Function.update_of_ne hji] at h ⊢; exact h, rfl⟩

/-- The pebble pairs follow the translation of `D`. -/
def Matches {m : ℕ} (D : Desc I) (S : GameState m G₀ G₁) : Prop :=
  ∀ j p q, S j = some (p, q) → q = phiV D p

/-- Consistent descriptions give partial isomorphisms. -/
lemma partialIso_of_good {m r : ℕ} {D : Desc I} {S : GameState m G₀ G₁}
    (hG : Good r (clsOf S) D) (hM : Matches D S) : IsPartialIso G₀ G₁ S := by
  intro i j p q p' q' hi hj
  have hpA : (nm p).1 ∈ clsOf S := mem_clsOf.mpr ⟨i, p, q, hi, rfl⟩
  have hp'A : (nm p').1 ∈ clsOf S := mem_clsOf.mpr ⟨j, p', q', hj, rfl⟩
  have e1 := hM i p q hi
  have e2 := hM j p' q' hj
  subst e1 e2
  refine ⟨⟨fun h => h ▸ rfl, fun h => ?_⟩, ?_, ?_⟩
  · have := congrArg (phiV D) h
    erw [phiV_phiV, phiV_phiV] at this
    exact this
  · show adjN I 0 (nm p) (nm p') ↔ adjN I 1 (nm (phiV D p)) (nm (phiV D p'))
    erw [nm_phiV, nm_phiV]
    exact adjN_phi D hG.init (nm_valid p) (nm_valid p') (hG.ms_link hpA) (hG.ms_link hp'A)
  · exact (matrixGraph_color 0 1 p (phiV D p)).mpr (by erw [nm_phiV, phi_fst])

/-- Duplicator's invariant on game states. -/
def DupInv {m : ℕ} (r : ℕ) (S : GameState m G₀ G₁) : Prop :=
  ∃ D : Desc I, Good r (clsOf S) D ∧ Matches D S

/-- **Duplicator's strategy.** -/
theorem survivesFrom_of_inv (hk : 2 ≤ k) :
    ∀ (r : ℕ) (S : GameState (k + 1) G₀ G₁), DupInv r S → SurvivesFrom G₀ G₁ r S
  | 0, _, _ => trivial
  | r + 1, S, ⟨D, hG, hM⟩ => by
    classical
    intro i
    set A₀ := clsOf (Function.update S i none)
    have hG₀ : Good (r + 1) A₀ D := hG.mono le_rfl (clsOf_lift_subset S i)
    have hA₀ := clsOf_valid (Function.update S i none)
    have hcard := card_clsOf_lift S i
    have hext : ∀ X : ICls I, ∃ D' : Desc I, ClsValid I X →
        Good r (insert X A₀) D' ∧ ∀ Y ∈ A₀, shift D' Y = shift D Y := by
      intro X
      by_cases hX : ClsValid I X
      · obtain ⟨D', h1, h2⟩ := extend hk hG₀ hA₀ hcard hX
        exact ⟨D', fun _ => ⟨h1, h2⟩⟩
      · exact ⟨D, fun h => absurd h hX⟩
    choose DX hDX using hext
    let f : Fin (nV I) → Fin (nV I) := fun p => phiV (DX (nm p).1) p
    have hf : Function.Involutive f := by
      intro p
      have : (nm (f p)).1 = (nm p).1 := by simp [f]
      simp only [f, this, phiV_phiV]
    refine ⟨hf.toPerm f, fun p => ?_⟩
    have hp := hDX (nm p).1 (nm_valid p).1
    set S' := Function.update S i (some (p, (hf.toPerm f) p))
    have hcls : clsOf S' = insert (nm p).1 A₀ := clsOf_place S i p _
    have hM' : Matches (DX (nm p).1) S' := by
      intro j p' q' hj
      by_cases hji : j = i
      · subst hji
        simp only [S', Function.update_self, Option.some.injEq] at hj
        obtain ⟨rfl, rfl⟩ := hj
        rfl
      · rw [show S' j = S j from Function.update_of_ne hji _ _] at hj
        rw [hM j p' q' hj]
        have hY : (nm p').1 ∈ A₀ :=
          mem_clsOf.mpr ⟨j, p', q', by rw [Function.update_of_ne hji]; exact hj, rfl⟩
        apply nm_injective
        erw [nm_phiV, nm_phiV, phi_congr (hp.2 _ hY)]
    have hG' : Good r (clsOf S') (DX (nm p).1) := hcls ▸ hp.1
    exact ⟨partialIso_of_good hG' hM', survivesFrom_of_inv hk r S' ⟨_, hG', hM'⟩⟩

/-- **Part (II) of the matrix compiler.** Duplicator survives `r` rounds as long as `K_r` is
conflict-free. -/
theorem duplicatorSurvives (hk : 2 ≤ k) {r : ℕ} (hnc : ¬ I.toParitySystem.HasConflict r) :
    DuplicatorSurvives (k + 1) r (matrixGraph I 0) (matrixGraph I 1) := by
  refine ⟨rfl, survivesFrom_of_inv hk r _ ⟨desc0 I, ?_, fun _ _ _ h => by simp at h⟩⟩
  have : clsOf (I := I) (fun _ : Fin (k + 1) => none) = ∅ := by
    ext X; simp [mem_clsOf]
  rw [this]
  exact good_empty (by omega) hnc

end Lax119563Proofs.Matrix

end Matrix_Duplicator

/-! ### Formerly `Lax119563Proofs.Matrix.SpoilerBasics` -/

section Matrix_SpoilerBasics

/-!
# Spoiler's moves

Spoiler always places pebbles on zero vertices of `G₀` (label `(0, 0)`). Pebbles
`0, …, k - 1` hold *representatives*; pebble `k` is the spare. Replacing a representative
costs two rounds: the spare is placed on the new vertex, then the representative is moved
onto the same vertex, where Duplicator has to answer with the same image.
-/

open Lax119563.ImplicitParitySystems Lax119563.MatrixCompiler Lax119563.ParitySystems
open Lax119563.ColoredGraphs Lax119563.PebbleGame

namespace Lax119563Proofs.Matrix

variable {k ℓ : ℕ} {I : ImplicitParitySystem k ℓ}

local notation "G₀" => matrixGraph I 0
local notation "G₁" => matrixGraph I 1

/-- Game states of the `(k + 1)`-pebble game on the matrix graphs. -/
abbrev St (I : ImplicitParitySystem k ℓ) := GameState (k + 1) (matrixGraph I 0) (matrixGraph I 1)

/-- The spare pebble. -/
abbrev spare : Fin (k + 1) := Fin.last k

lemma valid_zero {X : ICls I} (hX : ClsValid I X) : Valid I (X, ((0 : ZMod 2), (0 : ZMod 2))) :=
  ⟨hX, fun _ => rfl, fun _ => rfl⟩

/-- The zero vertex of a class. -/
def zv (X : ICls I) (hX : ClsValid I X) : Fin (nV I) :=
  idx (X, (0, 0)) ((mem_vertexList I _).mpr (valid_zero hX))

@[simp] lemma nm_zv (X : ICls I) (hX : ClsValid I X) : nm (zv X hX) = (X, (0, 0)) := nm_idx _ _

lemma eff_zero (X : ICls I) : eff I 0 (X, ((0 : ZMod 2), (0 : ZMod 2))) = (0, 0) := by
  simp [eff]

/-- Pebble `j` holds the zero vertex of class `X`, matched with a vertex of `G₁` of effective
label `l`. -/
def HoldsAt (S : St I) (j : Fin (k + 1)) (X : ICls I) (l : Lab) : Prop :=
  ∃ p q, S j = some (p, q) ∧ nm p = (X, (0, 0)) ∧ (nm q).1 = X ∧ eff I 1 (nm q) = l

/-- The representatives hold the classes `cls` with labels `lab`. -/
def Holds (S : St I) (cls : Fin k → ICls I) (lab : Fin k → Lab) : Prop :=
  ∀ i, HoldsAt S i.castSucc (cls i) (lab i)

lemma castSucc_ne_spare (i : Fin k) : (i.castSucc : Fin (k + 1)) ≠ spare :=
  Fin.castSucc_ne_last i

lemma HoldsAt.update_ne {S : St I} {j j' : Fin (k + 1)} {X : ICls I} {l : Lab}
    (h : HoldsAt S j X l) (hj : j ≠ j') (v : Option (Fin (nV I) × Fin (nV I))) :
    HoldsAt (Function.update S j' v) j X l := by
  obtain ⟨p, q, h1, h2⟩ := h
  exact ⟨p, q, by rw [Function.update_of_ne hj]; exact h1, h2⟩

lemma Holds.update_spare {S : St I} {cls : Fin k → ICls I} {lab : Fin k → Lab}
    (h : Holds S cls lab) (v : Option (Fin (nV I) × Fin (nV I))) :
    Holds (Function.update S spare v) cls lab :=
  fun i => (h i).update_ne (castSucc_ne_spare i) v

/-! ### Partial isomorphisms -/

lemma pi_adj {S : St I} (hPI : IsPartialIso G₀ G₁ S) {j j' : Fin (k + 1)} {p q p' q' : Fin (nV I)}
    (hj : S j = some (p, q)) (hj' : S j' = some (p', q')) :
    adjN I 0 (nm p) (nm p') ↔ adjN I 1 (nm q) (nm q') :=
  (hPI j j' p q p' q' hj hj').2.1

lemma pi_cls {S : St I} (hPI : IsPartialIso G₀ G₁ S) {j : Fin (k + 1)} {p q : Fin (nV I)}
    (hj : S j = some (p, q)) : (nm q).1 = (nm p).1 :=
  ((matrixGraph_color 0 1 p q).mp (hPI j j p q p q hj hj).2.2).symm

lemma pi_eq {S : St I} (hPI : IsPartialIso G₀ G₁ S) {j j' : Fin (k + 1)} {p q q' : Fin (nV I)}
    (hj : S j = some (p, q)) (hj' : S j' = some (p, q')) : q = q' :=
  (hPI j j' p q p q' hj hj').1.mp rfl

lemma adjN_iff_hub (ε : ZMod 2) {x y : VName I} (hx : isHub I x.1 = true) :
    adjN I ε x y ↔ hubB I x.1 (eff I ε x) y.1 (eff I ε y) = true := by
  unfold adjN
  constructor
  · rintro (h | h)
    · exact h
    · have := (hubB_hub I h).2
      rw [hx] at this
      exact absurd this (by decide)
  · exact Or.inl

/-- What Duplicator's answer `q` on the spare reveals about a representative, for a hub class
`Y` placed next to a held class `X`. -/
lemma forced_hub {S : St I} (hPI : IsPartialIso G₀ G₁ S) {j : Fin (k + 1)} {X : ICls I} {l : Lab}
    (hj : HoldsAt S j X l) {Y : ICls I} (hY : ClsValid I Y) {q : Fin (nV I)}
    (hs : S spare = some (zv Y hY, q)) (hYhub : isHub I Y = true) :
    hubB I Y (0, 0) X (0, 0) = true ↔ hubB I Y (eff I 1 (nm q)) X l = true := by
  obtain ⟨p, q', h1, h2, h3, h4⟩ := hj
  have := pi_adj hPI hs h1
  have hq : (nm q).1 = Y := by rw [pi_cls hPI hs, nm_zv]
  rw [nm_zv, h2, adjN_iff_hub 0 hYhub, adjN_iff_hub 1 (by rw [hq]; exact hYhub), eff_zero,
    eff_zero, h4, hq, h3] at this
  exact this

/-- The same, for a hub `X` held by a representative and a non-hub class `Y` on the spare. -/
lemma forced_nonhub {S : St I} (hPI : IsPartialIso G₀ G₁ S) {j : Fin (k + 1)} {X : ICls I}
    {l : Lab} (hj : HoldsAt S j X l) {Y : ICls I} (hY : ClsValid I Y) {q : Fin (nV I)}
    (hs : S spare = some (zv Y hY, q)) (hXhub : isHub I X = true) :
    hubB I X (0, 0) Y (0, 0) = true ↔ hubB I X l Y (eff I 1 (nm q)) = true := by
  obtain ⟨p, q', h1, h2, h3, h4⟩ := hj
  have := pi_adj hPI h1 hs
  have hq : (nm q).1 = Y := by rw [pi_cls hPI hs, nm_zv]
  rw [nm_zv, h2, adjN_iff_hub 0 hXhub, adjN_iff_hub 1 (by rw [h3]; exact hXhub), eff_zero,
    eff_zero, h4, hq, h3] at this
  exact this

lemma spare_cls {S : St I} (hPI : IsPartialIso G₀ G₁ S) {Y : ICls I} (hY : ClsValid I Y)
    {q : Fin (nV I)} (hs : S spare = some (zv Y hY, q)) : (nm q).1 = Y := by
  rw [pi_cls hPI hs, nm_zv]

/-! ### Moves -/

/-- Placing the spare on the zero vertex of `Y`. -/
lemma forces_spare (S : St I) (Y : ICls I) (hY : ClsValid I Y) :
    Forces 1 S fun S' => ∃ q, S' = Function.update S spare (some (zv Y hY, q)) ∧
      IsPartialIso G₀ G₁ S' :=
  Forces.place S spare (zv Y hY)

/-- Replacing representative `i` by the zero vertex of `Y`. -/
lemma forces_replace (S : St I) (i : Fin k) (Y : ICls I) (hY : ClsValid I Y) :
    Forces 2 S fun S' => ∃ q, IsPartialIso G₀ G₁ (Function.update S spare (some (zv Y hY, q))) ∧
      S' = Function.update (Function.update S spare (some (zv Y hY, q))) i.castSucc
        (some (zv Y hY, q)) ∧ IsPartialIso G₀ G₁ S' := by
  refine Forces.mono (le_refl (1 + 1)) ((forces_spare S Y hY).bind fun S1 ⟨q, hS1, hPI1⟩ => ?_)
  refine (Forces.place S1 i.castSucc (zv Y hY)).weaken fun S2 ⟨q2, hS2, hPI2⟩ => ?_
  have hq : q2 = q := by
    refine pi_eq hPI2 (p := zv Y hY) (j := i.castSucc) (j' := spare) ?_ ?_
    · rw [hS2]; simp
    · rw [hS2, Function.update_of_ne (castSucc_ne_spare i).symm, hS1]; simp
  subst hq hS1
  exact ⟨q2, hPI1, hS2, hPI2⟩

/-- Replacing representative `i` by class `Y`, where the answer satisfies `R`. -/
lemma forces_step {S : St I} {cls : Fin k → ICls I} {lab : Fin k → Lab} (hH : Holds S cls lab)
    (i : Fin k) (Y : ICls I) (hY : ClsValid I Y) (R : Lab → Prop)
    (hR : ∀ q, IsPartialIso G₀ G₁ (Function.update S spare (some (zv Y hY, q))) →
      R (eff I 1 (nm q))) :
    Forces 2 S fun S' => ∃ l, R l ∧ Holds S' (Function.update cls i Y)
      (Function.update lab i l) ∧ IsPartialIso G₀ G₁ S' := by
  refine (forces_replace S i Y hY).weaken fun S' ⟨q, hPI1, hS', hPI'⟩ => ?_
  refine ⟨eff I 1 (nm q), hR q hPI1, fun j => ?_, hPI'⟩
  by_cases hji : j = i
  · subst hji
    refine ⟨zv Y hY, q, by rw [hS']; simp, by simp, ?_, by simp⟩
    rw [Function.update_self]
    exact spare_cls (hY := hY) hPI1 (Function.update_self _ _ _)
  · rw [Function.update_of_ne hji, Function.update_of_ne hji, hS']
    exact ((hH j).update_ne (castSucc_ne_spare j) _).update_ne
      (fun h => hji (Fin.castSucc_injective _ h)) _

/-- Replacing the representatives in the list `T` one after the other. -/
lemma forces_replaceAll (T : List (Fin k)) (hT : T.Nodup) {S : St I} {cls : Fin k → ICls I}
    {lab : Fin k → Lab} (hH : Holds S cls lab) (hPI : IsPartialIso G₀ G₁ S) (newCls : Fin k → ICls I)
    (hval : ∀ i ∈ T, ClsValid I (newCls i)) (R : Fin k → Lab → Lab → Prop)
    (hR : ∀ (S1 : St I) i q (hi : i ∈ T), HoldsAt S1 i.castSucc (cls i) (lab i) →
      S1 spare = some (zv (newCls i) (hval i hi), q) → IsPartialIso G₀ G₁ S1 →
      R i (lab i) (eff I 1 (nm q))) :
    Forces (2 * T.length) S fun S' => ∃ lab' : Fin k → Lab,
      (∀ i ∈ T, R i (lab i) (lab' i)) ∧ (∀ i, i ∉ T → lab' i = lab i) ∧
      Holds S' (fun i => if i ∈ T then newCls i else cls i) lab' ∧ IsPartialIso G₀ G₁ S' := by
  induction T generalizing S cls lab with
  | nil =>
    refine Forces.ret ⟨lab, by simp, fun _ _ => rfl, by simpa using hH, hPI⟩
  | cons i T ih =>
    obtain ⟨hiT, hT'⟩ := List.nodup_cons.mp hT
    have hstep := forces_step hH i (newCls i) (hval i List.mem_cons_self) (R i (lab i))
      fun q hPI => hR _ i q List.mem_cons_self ((hH i).update_ne (castSucc_ne_spare i) _)
        (Function.update_self ..) hPI
    refine Forces.mono (show 2 + 2 * T.length ≤ 2 * (i :: T).length by simp; omega)
      (hstep.bind fun S1 ⟨l, hl, hH1, hPI1⟩ => ?_)
    refine (ih hT' hH1 hPI1 (fun j hj => hval j (List.mem_cons_of_mem _ hj))
      fun S2 j q hj hj2 hs hPI2 => ?_).weaken
      fun S' ⟨lab', h1, h2, h3, h4⟩ => ?_
    · have hji : j ≠ i := fun h => hiT (h ▸ hj)
      rw [Function.update_of_ne hji] at hj2 ⊢
      rw [Function.update_of_ne hji] at hj2
      exact hR S2 j q (List.mem_cons_of_mem _ hj) hj2 hs hPI2
    · refine ⟨lab', fun j hj => ?_, fun j hj => ?_, ?_, h4⟩
      · rcases List.mem_cons.mp hj with rfl | hj
        · rw [h2 j hiT]; simpa using hl
        · have hji : j ≠ i := fun h => hiT (h ▸ hj)
          have := h1 j hj
          rwa [Function.update_of_ne hji] at this
      · have hji : j ≠ i := fun h => hj (h ▸ List.mem_cons_self)
        rw [h2 j fun h => hj (List.mem_cons_of_mem _ h), Function.update_of_ne hji]
      · convert h3 using 2 with j
        by_cases hji : j = i
        · subst hji; simp [hiT]
        · simp [hji]

end Lax119563Proofs.Matrix

end Matrix_SpoilerBasics

/-! ### Formerly `Lax119563Proofs.Matrix.SpoilerStrip` -/

section Matrix_SpoilerStrip

/-!
# Spoiler's moves through a strip

Sweeping one check row (Lemma "Sweeping one check row"), the whole strip, the link to the end
coordinate class, and the junction moves of ternary schemas. Representatives follow the
columns `g i` of an allowed address; observed values are preserved.
-/

open Lax119563.ImplicitParitySystems Lax119563.MatrixCompiler Lax119563.ParitySystems
open Lax119563.ColoredGraphs Lax119563.PebbleGame

namespace Lax119563Proofs.Matrix

variable {k ℓ : ℕ} {I : ImplicitParitySystem k ℓ}

local notation "G₀" => matrixGraph I 0
local notation "G₁" => matrixGraph I 1

/-! ### The hub relation, slot by slot -/

lemma hubB_upd {e : Fin I.schemas.length} {σ : ℕ} {c : Coord k ℓ} {l m : Lab} {Y : ICls I} :
    hubB I (.upd e σ c) l Y m = true ↔ (Y = trackAt I e c σ ∧ m.1 = l.1) ∨
      (Y = .track e σ c ∧ m.1 = l.2) ∨ (Y = .coef e σ ∧ m.1 = l.1 + l.2) := by
  simp [hubB, or_assoc]

lemma hubB_junc {e : Fin I.schemas.length} {c : Coord k ℓ} {l m : Lab} {Y : ICls I} :
    hubB I (.junc e c) l Y m = true ↔
      (Y = .coord (locU (sch I e)) ((permU (sch I e)).apply c) ∧ m.1 = l.1) ∨
      (Y = .coord (locV (sch I e)) ((permV (sch I e)).apply c) ∧ m.1 = l.2) ∨
      (Y = .sum e c ∧ m.1 = l.1 + l.2) := by
  simp [hubB, or_assoc]

lemma hubB_link {e : Fin I.schemas.length} {c : Coord k ℓ} {l m : Lab} {Y : ICls I} :
    hubB I (.link e c) l Y m = true ↔
      (Y = trackAt I e c (numSteps k ℓ) ∧ m.1 = l.1) ∨ (Y = endCls I e c ∧ m.1 = l.1) := by
  simp [hubB]

/-! ### Distinct classes -/

lemma trackAt_cases (e : Fin I.schemas.length) (c : Coord k ℓ) (σ : ℕ) :
    trackAt I e c σ = startCls I e c ∨ ∃ σ' < σ, trackAt I e c σ = .track e σ' c := by
  unfold trackAt
  split
  · exact Or.inl rfl
  · next σ' h => exact Or.inr ⟨σ', (prevStep_some h).1, rfl⟩

lemma startCls_cases (e : Fin I.schemas.length) (c : Coord k ℓ) :
    startCls I e c = .sum e c ∨
      startCls I e c = .coord (locU (sch I e)) ((permU (sch I e)).apply c) := by
  unfold startCls; split <;> simp

lemma trackAt_ne_track (e : Fin I.schemas.length) (c : Coord k ℓ) (σ : ℕ) :
    trackAt I e c σ ≠ .track e σ c := by
  rcases trackAt_cases e c σ with h | ⟨σ', hσ', h⟩ <;> rw [h]
  · rcases startCls_cases e c with h' | h' <;> rw [h'] <;> simp
  · simp; omega

lemma trackAt_ne_coef (e : Fin I.schemas.length) (c : Coord k ℓ) (σ σ' : ℕ) :
    trackAt I e c σ ≠ .coef e σ' := by
  rcases trackAt_cases e c σ with h | ⟨σ'', -, h⟩ <;> rw [h]
  · rcases startCls_cases e c with h' | h' <;> rw [h'] <;> simp
  · simp

lemma locU_ne_locEnd (e : Fin I.schemas.length) : locU (sch I e) ≠ locEnd (sch I e) := by
  have h := sch_wf I e
  revert h
  cases sch I e <;> simp [Schema.WellFormed, locU, locEnd] <;> tauto

lemma locU_ne_locV (e : Fin I.schemas.length) (ht : isTern (sch I e) = true) :
    locU (sch I e) ≠ locV (sch I e) := by
  have h := sch_wf I e
  revert h ht
  cases sch I e <;> simp [Schema.WellFormed, locU, locV, isTern]
  tauto

lemma trackAt_ne_endCls (e : Fin I.schemas.length) (c : Coord k ℓ) (σ : ℕ) :
    trackAt I e c σ ≠ endCls I e c := by
  rcases trackAt_cases e c σ with h | ⟨σ', -, h⟩ <;> rw [h]
  · rcases startCls_cases e c with h' | h' <;> rw [h']
    · simp [endCls]
    · simp only [endCls, ne_eq, Cls.coord.injEq, not_and]
      exact fun h => absurd h (locU_ne_locEnd e)
  · simp [endCls]

/-! ### Valid classes -/

variable (e : Fin I.schemas.length)

lemma valid_startCls {c : Coord k ℓ} (hc : c ∈ dom I e) : ClsValid I (startCls I e c) := by
  unfold startCls
  split
  · next h => exact ⟨h, hc⟩
  · obtain ⟨i, h1, h2⟩ := exists_arg_U (sch I e)
    show (permU (sch I e)).apply c ∈ I.domain (locU (sch I e))
    rw [← h1, ← h2]
    exact argPerm_mem (sch_wf I e) hc i

lemma valid_endCls {c : Coord k ℓ} (hc : c ∈ dom I e) : ClsValid I (endCls I e c) := by
  obtain ⟨i, h1, h2⟩ := exists_arg_End (sch I e)
  show (permEnd (sch I e)).apply c ∈ I.domain (locEnd (sch I e))
  rw [← h1, ← h2]
  exact argPerm_mem (sch_wf I e) hc i

lemma valid_coordU {c : Coord k ℓ} (hc : c ∈ dom I e) :
    ClsValid I (.coord (locU (sch I e)) ((permU (sch I e)).apply c)) := by
  obtain ⟨i, h1, h2⟩ := exists_arg_U (sch I e)
  show (permU (sch I e)).apply c ∈ I.domain (locU (sch I e))
  rw [← h1, ← h2]
  exact argPerm_mem (sch_wf I e) hc i

lemma valid_coordV {c : Coord k ℓ} (hc : c ∈ dom I e) :
    ClsValid I (.coord (locV (sch I e)) ((permV (sch I e)).apply c)) := by
  obtain ⟨i, h1, h2⟩ := exists_arg_V (sch I e)
  show (permV (sch I e)).apply c ∈ I.domain (locV (sch I e))
  rw [← h1, ← h2]
  exact argPerm_mem (sch_wf I e) hc i

lemma valid_trackAt {c : Coord k ℓ} (hc : c ∈ dom I e) {σ : ℕ} (hσ : σ ≤ numSteps k ℓ) :
    ClsValid I (trackAt I e c σ) := by
  unfold trackAt
  split
  · exact valid_startCls e hc
  · next σ' h =>
    obtain ⟨h1, h2, -⟩ := prevStep_some h
    exact ⟨by omega, hc, h2⟩

/-! ### Sweeping one check row -/

/-- The steps whose row is nonzero on the domain of `e`. -/
def hit (σ : ℕ) : ℕ := if ∃ c ∈ dom I e, ent σ c ≠ 0 then 1 else 0

variable {e}

/-- Columns of an allowed address. -/
structure Cols (e : Fin I.schemas.length) (g : Fin k → Coord k ℓ) : Prop where
  addr : ∃ a, IsAddress a ∧ supp a ⊆ dom I e ∧ Finset.univ.image g = supp a
  inj : Function.Injective g

lemma Cols.mem {g : Fin k → Coord k ℓ} (h : Cols e g) (i : Fin k) : g i ∈ dom I e := by
  obtain ⟨a, -, hs, himg⟩ := h.addr
  exact hs (himg ▸ Finset.mem_image_of_mem g (Finset.mem_univ i))

lemma Cols.sum_ent (hk : 2 ≤ k) {g : Fin k → Coord k ℓ} (h : Cols e g) (σ : ℕ) :
    ∑ i, ent σ (g i) = 0 := by
  obtain ⟨a, ha, -, himg⟩ := h.addr
  rw [← Finset.sum_image (f := fun c => ent σ c) fun x _ y _ hxy => h.inj hxy, himg, supp,
    Finset.sum_image fun x _ y _ hxy => congrArg Prod.fst hxy]
  exact sum_ent_supp hk ha σ

lemma Holds.congr_cls {S : St I} {cls cls' : Fin k → ICls I} {lab : Fin k → Lab}
    (h : Holds S cls lab) (hc : ∀ i, cls i = cls' i) : Holds S cls' lab := by
  rwa [show cls = cls' from funext hc] at h

/-- The representatives in the support of the row of step `σ`. -/
def rowList (g : Fin k → Coord k ℓ) (σ : ℕ) : List (Fin k) :=
  (List.finRange k).filter fun i => ent σ (g i) ≠ 0

lemma mem_rowList {g : Fin k → Coord k ℓ} {σ : ℕ} {i : Fin k} :
    i ∈ rowList g σ ↔ ent σ (g i) ≠ 0 := by
  simp [rowList]

lemma nodup_rowList (g : Fin k → Coord k ℓ) (σ : ℕ) : (rowList g σ).Nodup :=
  (List.nodup_finRange k).filter _

lemma length_rowList_le (g : Fin k → Coord k ℓ) (σ : ℕ) : (rowList g σ).length ≤ k :=
  (List.length_filter_le _ _).trans (by simp)

/-- **Sweeping one check row**, forwards (`dir = true`) or backwards. -/
lemma sweep (hk : 2 ≤ k) {g : Fin k → Coord k ℓ} (hg : Cols e g) {σ : ℕ}
    (hσ : σ < numSteps k ℓ) (dir : Bool) {S : St I} {lab : Fin k → Lab}
    (hH : Holds S (fun i => trackAt I e (g i) (if dir then σ else σ + 1)) lab)
    (hPI : IsPartialIso G₀ G₁ S) :
    Forces ((4 * k + 1) * hit e σ) S fun S' => ∃ lab' : Fin k → Lab,
      Holds S' (fun i => trackAt I e (g i) (if dir then σ + 1 else σ)) lab' ∧
      ∑ i, (lab' i).1 = ∑ i, (lab i).1 ∧ IsPartialIso G₀ G₁ S' := by
  classical
  set T := rowList g σ
  have hstay : ∀ i, i ∉ T → trackAt I e (g i) (σ + 1) = trackAt I e (g i) σ := by
    intro i hi
    rw [trackAt_succ, if_neg (by rwa [mem_rowList] at hi)]
  have hmove : ∀ i, i ∈ T → trackAt I e (g i) (σ + 1) = .track e σ (g i) := by
    intro i hi
    rw [trackAt_succ, if_pos (mem_rowList.mp hi)]
  by_cases hT : T = []
  · refine Forces.mono (Nat.zero_le _) (Forces.ret ⟨lab, hH.congr_cls fun i => ?_, rfl, hPI⟩)
    have := hstay i (by rw [hT]; simp)
    cases dir <;> simp [this]
  obtain ⟨i₀, hi₀⟩ := List.exists_mem_of_ne_nil T hT
  have hhit : hit e σ = 1 := by
    simp only [hit]
    rw [if_pos ⟨g i₀, hg.mem i₀, mem_rowList.mp hi₀⟩]
  rw [hhit, mul_one]
  have hvalU : ∀ i ∈ T, ClsValid I (.upd e σ (g i)) := fun i hi =>
    ⟨hσ, hg.mem i, mem_rowList.mp hi⟩
  have hvalC : ClsValid I (.coef e σ : ICls I) := ⟨hσ, g i₀, hg.mem i₀, mem_rowList.mp hi₀⟩
  set old := fun i => trackAt I e (g i) (if dir then σ else σ + 1)
  have hold_ne_upd : ∀ i, i ∈ T → hubB I (.upd e σ (g i)) (0, 0) (old i) (0, 0) = true := by
    intro i hi
    rw [hubB_upd]
    cases dir
    · refine Or.inr (Or.inl ⟨?_, rfl⟩)
      simp only [old, Bool.false_eq_true, if_false, hmove i hi]
    · exact Or.inl ⟨by simp [old], rfl⟩
  -- the label of the update recorded in the old track
  let Rin : Fin k → Lab → Lab → Prop := fun _ l l' => (if dir then l'.1 else l'.2) = l.1
  have hA := forces_replaceAll T (nodup_rowList g σ) hH hPI (fun i => .upd e σ (g i)) hvalU Rin
    fun S1 i q hi hHi hs hPI1 => by
      have := (forced_hub hPI1 hHi (hvalU i hi) hs rfl).mp (hold_ne_upd i hi)
      rw [hubB_upd] at this
      cases dir
      · simp only [old, Bool.false_eq_true, if_false, hmove i hi] at this
        simp only [Rin, Bool.false_eq_true, if_false]
        rcases this with ⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩
        · exact absurd h.symm (trackAt_ne_track e (g i) σ)
        · exact h.symm
        · exact absurd h (by simp)
      · simp only [old, if_true] at this
        simp only [Rin, if_true]
        rcases this with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩
        · exact h.symm
        · exact absurd h (trackAt_ne_track e (g i) σ)
        · exact absurd h (trackAt_ne_coef e (g i) σ σ)
  have hTl : T.length ≤ k := length_rowList_le g σ
  refine Forces.mono (show 2 * T.length + (1 + 2 * T.length) ≤ 4 * k + 1 by omega) (hA.bind fun S1 ⟨lab1, hR1, hN1, hH1, hPI1⟩ => ?_)
  -- check the coefficient
  refine (forces_spare S1 (.coef e σ) hvalC).bind fun S2 ⟨η', hS2, hPI2⟩ => ?_
  set η := (eff I 1 (nm η')).1
  have hH2 : Holds S2 (fun i => if i ∈ T then .upd e σ (g i) else old i) lab1 := by
    rw [hS2]; exact hH1.update_spare _
  have hη : ∀ i ∈ T, η = (lab1 i).1 + (lab1 i).2 := by
    intro i hi
    have hHi := hH2 i
    simp only [if_pos hi] at hHi
    have := (forced_nonhub hPI2 hHi hvalC (q := η') (by rw [hS2]; exact Function.update_self ..)
      rfl).mp
      (by rw [hubB_upd]; exact Or.inr (Or.inr ⟨rfl, by simp⟩))
    rw [hubB_upd] at this
    rcases this with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩
    · exact absurd h.symm (trackAt_ne_coef e (g i) σ σ)
    · exact absurd h (by simp)
    · exact h
  -- move to the new tracks
  set new := fun i => trackAt I e (g i) (if dir then σ + 1 else σ)
  have hvalN : ∀ i ∈ T, ClsValid I (new i) := fun i _ => by
    simp only [new]
    exact valid_trackAt e (hg.mem i) (by split <;> omega)
  let Rout : Fin k → Lab → Lab → Prop := fun _ l l' => l'.1 = if dir then l.2 else l.1
  have hC := forces_replaceAll T (nodup_rowList g σ) hH2 hPI2 new hvalN Rout
    fun S3 i q hi hHi hs hPI3 => by
      simp only [if_pos hi] at hHi
      have := (forced_nonhub hPI3 hHi (hvalN i hi) hs rfl).mp (by
        rw [hubB_upd]
        cases dir
        · exact Or.inl ⟨by simp [new], rfl⟩
        · exact Or.inr (Or.inl ⟨by simp [new, hmove i hi], rfl⟩))
      rw [hubB_upd] at this
      cases dir
      · simp only [new, Bool.false_eq_true, if_false] at this
        simp only [Rout, Bool.false_eq_true, if_false]
        rcases this with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩
        · exact h
        · exact absurd h (trackAt_ne_track e (g i) σ)
        · exact absurd h (trackAt_ne_coef e (g i) σ σ)
      · simp only [new, if_true, hmove i hi] at this
        simp only [Rout, if_true]
        rcases this with ⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩
        · exact absurd h.symm (trackAt_ne_track e (g i) σ)
        · exact h
        · exact absurd h (by simp)
  refine hC.weaken fun S3 ⟨lab3, hR3, hN3, hH3, hPI3⟩ => ⟨lab3, hH3.congr_cls fun i => ?_, ?_, hPI3⟩
  · by_cases hi : i ∈ T
    · simp [hi, new]
    · simp only [hi, if_false, old, new]
      cases dir <;> simp [hstay i hi]
  · -- the observed value is preserved
    have hlab : ∀ i, (lab3 i).1 = (lab i).1 + ent σ (g i) * η := by
      intro i
      by_cases hi : i ∈ T
      · have h1 := hR1 i hi
        have h3 := hR3 i hi
        have h2 := hη i hi
        rw [ent_eq_one (mem_rowList.mp hi), one_mul]
        simp only [Rin, Rout] at h1 h3
        cases dir
        · simp only [Bool.false_eq_true, if_false] at h1 h3
          rw [h3, h2, ← h1]
          ring_nf; rw [show (2 : ZMod 2) = 0 from rfl]; ring
        · simp only [if_true] at h1 h3
          rw [h3, h2, ← h1]
          ring_nf; rw [show (2 : ZMod 2) = 0 from rfl]; ring
      · rw [hN3 i hi, hN1 i hi]
        have : ent σ (g i) = 0 := by
          by_contra h; exact hi (mem_rowList.mpr h)
        rw [this, zero_mul, add_zero]
    simp_rw [hlab]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, hg.sum_ent hk, zero_mul, add_zero]

end Lax119563Proofs.Matrix

end Matrix_SpoilerStrip

/-! ### Formerly `Lax119563Proofs.Matrix.SpoilerGadget` -/

section Matrix_SpoilerGadget

/-!
# Spoiler's moves through a schema gadget

The whole strip, the link to the end coordinate class, the junction moves, and the five ways
of following an inference backwards through the gadget of a schema (Lemma "Following an
inference" with row sweeps).
-/

open Lax119563.ImplicitParitySystems Lax119563.MatrixCompiler Lax119563.ParitySystems
open Lax119563.ColoredGraphs Lax119563.PebbleGame

namespace Lax119563Proofs.Matrix

variable {k ℓ : ℕ} {I : ImplicitParitySystem k ℓ}

local notation "G₀" => matrixGraph I 0
local notation "G₁" => matrixGraph I 1

/-- Replacing every representative. -/
lemma forces_replaceEvery {S : St I} {cls : Fin k → ICls I} {lab : Fin k → Lab}
    (hH : Holds S cls lab) (hPI : IsPartialIso G₀ G₁ S) (newCls : Fin k → ICls I)
    (hval : ∀ i, ClsValid I (newCls i)) (R : Fin k → Lab → Lab → Prop)
    (hR : ∀ (S1 : St I) i q, HoldsAt S1 i.castSucc (cls i) (lab i) →
      S1 spare = some (zv (newCls i) (hval i), q) → IsPartialIso G₀ G₁ S1 →
      R i (lab i) (eff I 1 (nm q))) :
    Forces (2 * k) S fun S' => ∃ lab' : Fin k → Lab, (∀ i, R i (lab i) (lab' i)) ∧
      Holds S' newCls lab' ∧ IsPartialIso G₀ G₁ S' := by
  have := forces_replaceAll (List.finRange k) (List.nodup_finRange k) hH hPI newCls
    (fun i _ => hval i) R fun S1 i q _ h1 h2 h3 => hR S1 i q h1 h2 h3
  rw [List.length_finRange] at this
  exact this.weaken fun S' ⟨lab', h1, _, h3, h4⟩ =>
    ⟨lab', fun i => h1 i (List.mem_finRange i), h3.congr_cls fun i => by simp, h4⟩

variable {e : Fin I.schemas.length} {g : Fin k → Coord k ℓ}

/-! ### The strip -/

/-- The cost of sweeping a strip. -/
def stripCost (e : Fin I.schemas.length) : ℕ :=
  ∑ σ ∈ Finset.range (numSteps k ℓ), (4 * k + 1) * hit e σ

/-- Sweeping the strip forwards, from stage `0` to stage `n`. -/
lemma strip_fwd (hk : 2 ≤ k) (hg : Cols e g) :
    ∀ n ≤ numSteps k ℓ, ∀ (S : St I) (lab : Fin k → Lab),
      Holds S (fun i => trackAt I e (g i) 0) lab → IsPartialIso G₀ G₁ S →
      Forces (∑ σ ∈ Finset.range n, (4 * k + 1) * hit e σ) S fun S' => ∃ lab' : Fin k → Lab,
        Holds S' (fun i => trackAt I e (g i) n) lab' ∧ ∑ i, (lab' i).1 = ∑ i, (lab i).1 ∧
        IsPartialIso G₀ G₁ S'
  | 0, _, S, lab, hH, hPI => Forces.ret ⟨lab, hH, rfl, hPI⟩
  | n + 1, hn, S, lab, hH, hPI => by
    rw [Finset.sum_range_succ]
    refine (strip_fwd hk hg n (by omega) S lab hH hPI).bind fun S1 ⟨lab1, hH1, hs1, hPI1⟩ => ?_
    refine (sweep hk hg (σ := n) (by omega) true (hH1.congr_cls fun i => by simp) hPI1).weaken
      fun S2 ⟨lab2, hH2, hs2, hPI2⟩ => ⟨lab2, hH2.congr_cls fun i => by simp, hs2.trans hs1, hPI2⟩

/-- Sweeping the strip backwards, from stage `n` to stage `0`. -/
lemma strip_bwd (hk : 2 ≤ k) (hg : Cols e g) :
    ∀ n ≤ numSteps k ℓ, ∀ (S : St I) (lab : Fin k → Lab),
      Holds S (fun i => trackAt I e (g i) n) lab → IsPartialIso G₀ G₁ S →
      Forces (∑ σ ∈ Finset.range n, (4 * k + 1) * hit e σ) S fun S' => ∃ lab' : Fin k → Lab,
        Holds S' (fun i => trackAt I e (g i) 0) lab' ∧ ∑ i, (lab' i).1 = ∑ i, (lab i).1 ∧
        IsPartialIso G₀ G₁ S'
  | 0, _, S, lab, hH, hPI => Forces.ret ⟨lab, hH, rfl, hPI⟩
  | n + 1, hn, S, lab, hH, hPI => by
    have h1 := sweep hk hg (σ := n) (by omega) false (hH.congr_cls fun i => by simp) hPI
    have hc : ∑ σ ∈ Finset.range (n + 1), (4 * k + 1) * hit e σ =
        (4 * k + 1) * hit e n + ∑ σ ∈ Finset.range n, (4 * k + 1) * hit e σ := by
      rw [Finset.sum_range_succ, Nat.add_comm]
    rw [hc]
    refine h1.bind fun S1 ⟨lab1, hH1, hs1, hPI1⟩ =>
      (strip_bwd hk hg n (by omega) S1 lab1 (hH1.congr_cls fun i => by simp) hPI1).weaken
        fun S2 ⟨lab2, hH2, hs2, hPI2⟩ => ⟨lab2, hH2, hs2.trans hs1, hPI2⟩

/-! ### The link -/

/-- From the last tracks through the links to the end coordinate classes. -/
lemma link_fwd (hg : Cols e g) {S : St I} {lab : Fin k → Lab}
    (hH : Holds S (fun i => trackAt I e (g i) (numSteps k ℓ)) lab)
    (hPI : IsPartialIso G₀ G₁ S) :
    Forces (2 * k + 2 * k) S fun S' => ∃ lab' : Fin k → Lab,
      Holds S' (fun i => endCls I e (g i)) lab' ∧ ∑ i, (lab' i).1 = ∑ i, (lab i).1 ∧
      IsPartialIso G₀ G₁ S' := by
  have hvL : ∀ i, ClsValid I (Cls.link e (g i) : ICls I) := fun i => hg.mem i
  refine (forces_replaceEvery hH hPI _ hvL (fun _ l l' => l'.1 = l.1)
    fun S1 i q hHi hs hPI1 => ?_).bind fun S1 ⟨lab1, hR1, hH1, hPI1⟩ => ?_
  · have := (forced_hub hPI1 hHi (hvL i) hs rfl).mp (by rw [hubB_link]; exact Or.inl ⟨rfl, rfl⟩)
    rw [hubB_link] at this
    rcases this with ⟨-, h⟩ | ⟨h, -⟩
    · exact h.symm
    · exact absurd h (trackAt_ne_endCls e (g i) _)
  · refine (forces_replaceEvery hH1 hPI1 _ (fun i => valid_endCls e (hg.mem i))
      (fun _ l l' => l'.1 = l.1) fun S2 i q hHi hs hPI2 => ?_).weaken
      fun S2 ⟨lab2, hR2, hH2, hPI2⟩ => ⟨lab2, hH2, ?_, hPI2⟩
    · have := (forced_nonhub hPI2 hHi (valid_endCls e (hg.mem i)) hs rfl).mp
        (by rw [hubB_link]; exact Or.inr ⟨rfl, rfl⟩)
      rw [hubB_link] at this
      rcases this with ⟨h, -⟩ | ⟨-, h⟩
      · exact absurd h.symm (trackAt_ne_endCls e (g i) _)
      · exact h
    · exact Finset.sum_congr rfl fun i _ => (hR2 i).trans (hR1 i)

/-- From the end coordinate classes through the links to the last tracks. -/
lemma link_bwd (hg : Cols e g) {S : St I} {lab : Fin k → Lab}
    (hH : Holds S (fun i => endCls I e (g i)) lab) (hPI : IsPartialIso G₀ G₁ S) :
    Forces (2 * k + 2 * k) S fun S' => ∃ lab' : Fin k → Lab,
      Holds S' (fun i => trackAt I e (g i) (numSteps k ℓ)) lab' ∧
      ∑ i, (lab' i).1 = ∑ i, (lab i).1 ∧ IsPartialIso G₀ G₁ S' := by
  have hvL : ∀ i, ClsValid I (Cls.link e (g i) : ICls I) := fun i => hg.mem i
  refine (forces_replaceEvery hH hPI _ hvL (fun _ l l' => l'.1 = l.1)
    fun S1 i q hHi hs hPI1 => ?_).bind fun S1 ⟨lab1, hR1, hH1, hPI1⟩ => ?_
  · have := (forced_hub hPI1 hHi (hvL i) hs rfl).mp (by rw [hubB_link]; exact Or.inr ⟨rfl, rfl⟩)
    rw [hubB_link] at this
    rcases this with ⟨h, -⟩ | ⟨-, h⟩
    · exact absurd h.symm (trackAt_ne_endCls e (g i) _)
    · exact h.symm
  · refine (forces_replaceEvery hH1 hPI1 _
      (fun i => valid_trackAt e (hg.mem i) le_rfl)
      (fun _ l l' => l'.1 = l.1) fun S2 i q hHi hs hPI2 => ?_).weaken
      fun S2 ⟨lab2, hR2, hH2, hPI2⟩ => ⟨lab2, hH2, ?_, hPI2⟩
    · have := (forced_nonhub hPI2 hHi (valid_trackAt e (hg.mem i) le_rfl) hs rfl).mp
        (by rw [hubB_link]; exact Or.inl ⟨rfl, rfl⟩)
      rw [hubB_link] at this
      rcases this with ⟨-, h⟩ | ⟨h, -⟩
      · exact h
      · exact absurd h (trackAt_ne_endCls e (g i) _)
    · exact Finset.sum_congr rfl fun i _ => (hR2 i).trans (hR1 i)

/-! ### Junctions -/

/-- The neighbor classes of a junction. -/
def coordU (e : Fin I.schemas.length) (c : Coord k ℓ) : ICls I :=
  .coord (locU (sch I e)) ((permU (sch I e)).apply c)

/-- The neighbor classes of a junction. -/
def coordV (e : Fin I.schemas.length) (c : Coord k ℓ) : ICls I :=
  .coord (locV (sch I e)) ((permV (sch I e)).apply c)

lemma coordU_ne_coordV (ht : isTern (sch I e) = true) (c : Coord k ℓ) :
    coordU e c ≠ coordV e c := by
  simp only [coordU, coordV, ne_eq, Cls.coord.injEq, not_and]
  exact fun h => absurd h (locU_ne_locV e ht)

lemma hubB_junc' {c : Coord k ℓ} {l m : Lab} {Y : ICls I} :
    hubB I (.junc e c) l Y m = true ↔ (Y = coordU e c ∧ m.1 = l.1) ∨
      (Y = coordV e c ∧ m.1 = l.2) ∨ (Y = .sum e c ∧ m.1 = l.1 + l.2) :=
  hubB_junc

/-- A junction move: all representatives move between a junction class and one of its
neighbor classes. -/
lemma junc_move (ht : isTern (sch I e) = true) (hg : Cols e g) (toJunc : Bool)
    (nb : Fin k → ICls I) (hnb : ∀ i, nb i = coordU e (g i) ∨ nb i = coordV e (g i) ∨
      nb i = .sum e (g i))
    (hval : ∀ i, ClsValid I (nb i)) (f : Lab → ZMod 2)
    (hf : ∀ i l, (nb i = coordU e (g i) → f l = l.1) ∧ (nb i = coordV e (g i) → f l = l.2) ∧
      (nb i = .sum e (g i) → f l = l.1 + l.2))
    {S : St I} {lab : Fin k → Lab}
    (hH : Holds S (fun i => if toJunc then nb i else .junc e (g i)) lab)
    (hPI : IsPartialIso G₀ G₁ S) :
    Forces (2 * k) S fun S' => ∃ lab' : Fin k → Lab,
      (∀ i, if toJunc then f (lab' i) = (lab i).1 else (lab' i).1 = f (lab i)) ∧
      Holds S' (fun i => if toJunc then .junc e (g i) else nb i) lab' ∧
      IsPartialIso G₀ G₁ S' := by
  have hvJ : ∀ i, ClsValid I (Cls.junc e (g i) : ICls I) := fun i => ⟨ht, hg.mem i⟩
  have hvN : ∀ i, ClsValid I (if toJunc then Cls.junc e (g i) else nb i) := by
    intro i; split
    · exact hvJ i
    · exact hval i
  have hz : ∀ i, hubB I (.junc e (g i)) (0, 0) (nb i) (0, 0) = true := by
    intro i
    rw [hubB_junc']
    rcases hnb i with h | h | h
    · exact Or.inl ⟨h, rfl⟩
    · exact Or.inr (Or.inl ⟨h, rfl⟩)
    · exact Or.inr (Or.inr ⟨h, by simp⟩)
  -- the label relation at a junction with label `l` and its neighbor with label `m`
  have hrel : ∀ i l m, hubB I (.junc e (g i)) l (nb i) m = true → m.1 = f l := by
    intro i l m h
    rw [hubB_junc'] at h
    have hU := (hf i l).1
    have hV := (hf i l).2.1
    have hS := (hf i l).2.2
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h2, hU h1]
    · rw [h2, hV h1]
    · rw [h2, hS h1]
  refine (forces_replaceEvery hH hPI _ hvN
    (fun _ l l' => if toJunc then f l' = l.1 else l'.1 = f l) fun S1 i q hHi hs hPI1 => ?_).weaken
    fun S' ⟨lab', h1, h2, h3⟩ => ⟨lab', h1, h2, h3⟩
  cases toJunc
  · simp only [Bool.false_eq_true, if_false] at hHi hs ⊢
    exact hrel i _ _ ((forced_nonhub hPI1 hHi (hval i) hs rfl).mp (hz i))
  · simp only [if_true] at hHi hs ⊢
    exact (hrel i _ _ ((forced_hub hPI1 hHi (hvJ i) hs rfl).mp (hz i))).symm

end Lax119563Proofs.Matrix

end Matrix_SpoilerGadget

/-! ### Formerly `Lax119563Proofs.Matrix.SpoilerWalk` -/

section Matrix_SpoilerWalk

/-!
# Spoiler's strategy

Spoiler follows a derivation of a conflict backwards: from a discrepant fact he moves
through the gadget of an inference to a discrepant premise derived in an earlier round, until
an initial fact contradicts the singleton coordinate classes (Theorem "Matrix compiler",
part (I)).
-/

open Lax119563.ImplicitParitySystems Lax119563.MatrixCompiler Lax119563.ParitySystems
open Lax119563.ColoredGraphs Lax119563.PebbleGame

namespace Lax119563Proofs.Matrix

variable {k ℓ : ℕ} {I : ImplicitParitySystem k ℓ}

local notation "G₀" => matrixGraph I 0
local notation "G₁" => matrixGraph I 1

/-! ### Discrepant facts -/

/-- The representatives hold the coordinate classes of the variable `X`, and the observed
value disagrees with `b`. -/
def Disc (S : St I) (X : Fin I.numLocations × (Fin k → BlockCoord ℓ)) (b : ZMod 2) : Prop :=
  ∃ g : Fin k → Coord k ℓ, Function.Injective g ∧ Finset.univ.image g = supp X.2 ∧
    ∃ lab : Fin k → Lab, Holds S (fun i => .coord X.1 (g i)) lab ∧ ∑ i, (lab i).1 = b + 1 ∧
      IsPartialIso G₀ G₁ S

variable {e : Fin I.schemas.length} {a : Fin k → BlockCoord ℓ}

lemma disc_to_cols (ha : IsAddress a) (hsa : supp a ⊆ dom I e) {S : St I}
    {x : Fin I.numLocations} {P : BlockPerm k ℓ} {b : ZMod 2} (hD : Disc S (x, P.act a) b) :
    ∃ g, Cols e g ∧ Finset.univ.image g = supp a ∧ ∃ lab : Fin k → Lab,
      Holds S (fun i => .coord x (P.apply (g i))) lab ∧ ∑ i, (lab i).1 = b + 1 ∧
      IsPartialIso G₀ G₁ S := by
  obtain ⟨g, hg, himg, lab, hH, hs, hPI⟩ := hD
  simp only at himg hH
  have himg' : Finset.univ.image (fun i => (bpEquiv P).symm (g i)) = supp a := by
    ext c
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩
      have : g i ∈ supp (P.act a) := himg ▸ Finset.mem_image_of_mem g (Finset.mem_univ i)
      rw [supp_act] at this
      obtain ⟨c, hc, hci⟩ := Finset.mem_image.mp this
      rw [← hci, ← bpEquiv_apply, Equiv.symm_apply_apply]
      exact hc
    · intro hc
      have : P.apply c ∈ supp (P.act a) := by
        rw [supp_act]; exact Finset.mem_image_of_mem _ hc
      rw [← himg] at this
      obtain ⟨i, -, hi⟩ := Finset.mem_image.mp this
      exact ⟨i, by rw [hi, ← bpEquiv_apply, Equiv.symm_apply_apply]⟩
  refine ⟨fun i => (bpEquiv P).symm (g i), ⟨⟨a, ha, hsa, himg'⟩,
    fun i j h => hg ((bpEquiv P).symm.injective h)⟩, himg', lab, hH.congr_cls fun i => ?_, hs,
    hPI⟩
  simp [← bpEquiv_apply]

lemma cols_to_disc {S : St I} {x : Fin I.numLocations} {P : BlockPerm k ℓ} {b : ZMod 2}
    {g : Fin k → Coord k ℓ} (hg : Function.Injective g) (himg : Finset.univ.image g = supp a)
    {lab : Fin k → Lab} (hH : Holds S (fun i => .coord x (P.apply (g i))) lab)
    (hs : ∑ i, (lab i).1 = b + 1) (hPI : IsPartialIso G₀ G₁ S) : Disc S (x, P.act a) b := by
  refine ⟨fun i => P.apply (g i), fun i j h => hg (bp_apply_injective P h), ?_, lab, hH, hs, hPI⟩
  simp only
  rw [supp_act, ← himg, Finset.image_image]
  rfl

/-! ### Following an inference through a gadget -/

variable {g : Fin k → Coord k ℓ}

lemma trackAt_zero (e : Fin I.schemas.length) (c : Coord k ℓ) : trackAt I e c 0 = startCls I e c :=
  rfl

lemma startCls_bin (ht : isTern (sch I e) = false) (c : Coord k ℓ) :
    startCls I e c = coordU e c := by
  simp [startCls, ht, coordU]

lemma startCls_tern (ht : isTern (sch I e) = true) (c : Coord k ℓ) :
    startCls I e c = .sum e c := by
  simp [startCls, ht]

/-- The cost of one inference step. -/
def stepCost (e : Fin I.schemas.length) : ℕ := stripCost e + 8 * k

lemma bin_fwd (hk : 2 ≤ k) (ht : isTern (sch I e) = false) (hg : Cols e g) {S : St I}
    {lab : Fin k → Lab} (hH : Holds S (fun i => coordU e (g i)) lab)
    (hPI : IsPartialIso G₀ G₁ S) :
    Forces (stepCost e) S fun S' => ∃ lab' : Fin k → Lab,
      Holds S' (fun i => endCls I e (g i)) lab' ∧ ∑ i, (lab' i).1 = ∑ i, (lab i).1 ∧
      IsPartialIso G₀ G₁ S' := by
  have h1 := strip_fwd hk hg (numSteps k ℓ) le_rfl S lab
    (hH.congr_cls fun i => by rw [trackAt_zero, startCls_bin ht]) hPI
  refine Forces.mono (by unfold stepCost stripCost; omega) (h1.bind fun S1 ⟨lab1, hH1, hs1, hPI1⟩ =>
    (link_fwd hg hH1 hPI1).weaken fun S2 ⟨lab2, hH2, hs2, hPI2⟩ =>
      ⟨lab2, hH2, hs2.trans hs1, hPI2⟩)

lemma bin_bwd (hk : 2 ≤ k) (ht : isTern (sch I e) = false) (hg : Cols e g) {S : St I}
    {lab : Fin k → Lab} (hH : Holds S (fun i => endCls I e (g i)) lab)
    (hPI : IsPartialIso G₀ G₁ S) :
    Forces (stepCost e) S fun S' => ∃ lab' : Fin k → Lab,
      Holds S' (fun i => coordU e (g i)) lab' ∧ ∑ i, (lab' i).1 = ∑ i, (lab i).1 ∧
      IsPartialIso G₀ G₁ S' := by
  refine Forces.mono (by unfold stepCost stripCost; omega) ((link_bwd hg hH hPI).bind
    fun S1 ⟨lab1, hH1, hs1, hPI1⟩ => (strip_bwd hk hg (numSteps k ℓ) le_rfl S1 lab1 hH1
      hPI1).weaken fun S2 ⟨lab2, hH2, hs2, hPI2⟩ => ⟨lab2, hH2.congr_cls fun i => by
        rw [trackAt_zero, startCls_bin ht], hs2.trans hs1, hPI2⟩)

lemma sum_eq_or (x b : ZMod 2) (h : x ≠ b) : x = b + 1 := by
  rcases zmod2_eq_zero_or_one x with rfl | rfl <;> rcases zmod2_eq_zero_or_one b with rfl | rfl <;>
    first | exact absurd rfl h | rfl

/-- From the end coordinate classes of a ternary schema to a discrepant first or second
argument. -/
lemma tern_end (hk : 2 ≤ k) (ht : isTern (sch I e) = true) (hg : Cols e g) (b₁ : ZMod 2)
    {S : St I} {lab : Fin k → Lab} (hH : Holds S (fun i => endCls I e (g i)) lab)
    (hPI : IsPartialIso G₀ G₁ S) :
    Forces (stepCost e) S fun S' =>
      (∃ lab' : Fin k → Lab, Holds S' (fun i => coordU e (g i)) lab' ∧
        ∑ i, (lab' i).1 = b₁ + 1 ∧ IsPartialIso G₀ G₁ S') ∨
      (∃ lab' : Fin k → Lab, Holds S' (fun i => coordV e (g i)) lab' ∧
        ∑ i, (lab' i).1 = ∑ i, (lab i).1 + b₁ ∧ IsPartialIso G₀ G₁ S') := by
  have hvS : ∀ i, ClsValid I (Cls.sum e (g i) : ICls I) := fun i => ⟨ht, hg.mem i⟩
  refine Forces.mono (show 2 * k + 2 * k + (stripCost e + (2 * k + 2 * k)) ≤ stepCost e by
    unfold stepCost; omega) ((link_bwd hg hH hPI).bind fun S1 ⟨lab1, hH1, hs1, hPI1⟩ =>
      (strip_bwd hk hg (numSteps k ℓ) le_rfl S1 lab1 hH1 hPI1).bind
        fun S2 ⟨lab2, hH2, hs2, hPI2⟩ => ?_)
  have hH2' : Holds S2 (fun i => if true then Cls.sum e (g i) else Cls.junc e (g i)) lab2 :=
    hH2.congr_cls fun i => by rw [trackAt_zero, startCls_tern ht]; rfl
  refine (junc_move ht hg true _ (fun i => Or.inr (Or.inr rfl)) hvS (fun l => l.1 + l.2)
    (fun i l => ⟨fun h => by simp [coordU] at h, fun h => by simp [coordV] at h, fun _ => rfl⟩)
    hH2' hPI2).bind fun S3 ⟨lab3, hR3, hH3, hPI3⟩ => ?_
  simp only [if_true] at hR3 hH3
  by_cases hb : ∑ i, (lab3 i).1 = b₁
  · refine (junc_move ht hg false (fun i => coordV e (g i)) (fun i => Or.inr (Or.inl rfl))
      (fun i => valid_coordV e (hg.mem i)) (fun l => l.2)
      (fun i l => ⟨fun h => absurd h.symm (coordU_ne_coordV ht _), fun _ => rfl,
        fun h => by simp [coordV] at h⟩) (hH3.congr_cls fun i => by simp) hPI3).weaken
      fun S4 ⟨lab4, hR4, hH4, hPI4⟩ => Or.inr ⟨lab4, hH4.congr_cls fun i => by simp, ?_, hPI4⟩
    simp only [Bool.false_eq_true, if_false] at hR4
    have : ∀ i, (lab4 i).1 = (lab3 i).1 + (lab2 i).1 := by
      intro i
      rw [hR4 i, ← hR3 i]
      ring_nf; rw [show (2 : ZMod 2) = 0 from rfl]; ring
    simp_rw [this]
    rw [Finset.sum_add_distrib, hb, hs2, hs1, add_comm]
  · refine (junc_move ht hg false (fun i => coordU e (g i)) (fun i => Or.inl rfl)
      (fun i => valid_coordU e (hg.mem i)) (fun l => l.1)
      (fun i l => ⟨fun _ => rfl, fun h => absurd h (coordU_ne_coordV ht _),
        fun h => by simp [coordU] at h⟩) (hH3.congr_cls fun i => by simp) hPI3).weaken
      fun S4 ⟨lab4, hR4, hH4, hPI4⟩ => Or.inl ⟨lab4, hH4.congr_cls fun i => by simp, ?_, hPI4⟩
    simp only [Bool.false_eq_true, if_false] at hR4
    simp_rw [hR4]
    exact sum_eq_or _ _ hb

/-- From the coordinate classes of an argument next to the junctions (`first = true`: the
first argument, otherwise the second) to the other one or the end of the strip. -/
lemma tern_side (hk : 2 ≤ k) (ht : isTern (sch I e) = true) (hg : Cols e g) (first : Bool)
    (b' : ZMod 2) {S : St I} {lab : Fin k → Lab}
    (hH : Holds S (fun i => if first then coordU e (g i) else coordV e (g i)) lab)
    (hPI : IsPartialIso G₀ G₁ S) :
    Forces (stepCost e) S fun S' =>
      (∃ lab' : Fin k → Lab, Holds S' (fun i => if first then coordV e (g i) else coordU e (g i))
        lab' ∧ ∑ i, (lab' i).1 = b' + 1 ∧ IsPartialIso G₀ G₁ S') ∨
      (∃ lab' : Fin k → Lab, Holds S' (fun i => endCls I e (g i)) lab' ∧
        ∑ i, (lab' i).1 = ∑ i, (lab i).1 + b' ∧ IsPartialIso G₀ G₁ S') := by
  have hvS : ∀ i, ClsValid I (Cls.sum e (g i) : ICls I) := fun i => ⟨ht, hg.mem i⟩
  -- the neighbor classes in the order (held, other)
  let own : Lab → ZMod 2 := fun l => if first then l.1 else l.2
  let oth : Lab → ZMod 2 := fun l => if first then l.2 else l.1
  have hvOwn : ∀ i, ClsValid I (if first then coordU e (g i) else coordV e (g i)) := fun i => by
    split
    · exact valid_coordU e (hg.mem i)
    · exact valid_coordV e (hg.mem i)
  have hvOth : ∀ i, ClsValid I (if first then coordV e (g i) else coordU e (g i)) := fun i => by
    split
    · exact valid_coordV e (hg.mem i)
    · exact valid_coordU e (hg.mem i)
  have hH' : Holds S (fun i => if true then (if first then coordU e (g i) else coordV e (g i))
      else Cls.junc e (g i)) lab := hH.congr_cls fun i => rfl
  refine Forces.mono (show 2 * k + (2 * k + (stripCost e + (2 * k + 2 * k))) ≤ stepCost e by
    unfold stepCost; omega) ((junc_move ht hg true _ (fun i => by cases first <;> simp)
    hvOwn own (fun i l => by
      cases first <;> refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩ <;>
        simp only [if_true, Bool.false_eq_true, if_false, own] at h ⊢ <;>
        first | rfl | exact absurd h (coordU_ne_coordV ht _) |
          exact absurd h.symm (coordU_ne_coordV ht _) | simp [coordU, coordV] at h) hH' hPI).bind
    fun S1 ⟨lab1, hR1, hH1, hPI1⟩ => ?_)
  simp only [if_true] at hR1 hH1
  by_cases hb : ∑ i, oth (lab1 i) = b'
  · -- go to the sums and sweep the strip
    refine (junc_move ht hg false (fun i => Cls.sum e (g i)) (fun i => Or.inr (Or.inr rfl)) hvS
      (fun l => l.1 + l.2) (fun i l => ⟨fun h => by simp [coordU] at h,
        fun h => by simp [coordV] at h, fun _ => rfl⟩) (hH1.congr_cls fun i => by simp)
      hPI1).bind fun S2 ⟨lab2, hR2, hH2, hPI2⟩ => ?_
    simp only [Bool.false_eq_true, if_false] at hR2 hH2
    have hsum2 : ∑ i, (lab2 i).1 = ∑ i, (lab i).1 + b' := by
      have : ∀ i, (lab2 i).1 = own (lab1 i) + oth (lab1 i) := by
        intro i; rw [hR2 i]; simp only [own, oth]; cases first <;> simp [add_comm]
      simp_rw [this]
      rw [Finset.sum_add_distrib, hb]
      congr 1
      exact Finset.sum_congr rfl fun i _ => hR1 i
    refine (strip_fwd hk hg (numSteps k ℓ) le_rfl S2 lab2
      (hH2.congr_cls fun i => by rw [trackAt_zero, startCls_tern ht]) hPI2).bind
      fun S3 ⟨lab3, hH3, hs3, hPI3⟩ => (link_fwd hg hH3 hPI3).weaken
        fun S4 ⟨lab4, hH4, hs4, hPI4⟩ => Or.inr ⟨lab4, hH4, by rw [hs4, hs3, hsum2], hPI4⟩
  · -- go to the other argument
    refine Forces.mono (Nat.le_add_right _ _) ((junc_move ht hg false
      (fun i => if first then coordV e (g i) else coordU e (g i))
      (fun i => by cases first <;> simp) hvOth oth (fun i l => by
      cases first <;> refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩ <;>
        simp only [if_true, Bool.false_eq_true, if_false, oth] at h ⊢ <;>
        first | rfl | exact absurd h (coordU_ne_coordV ht _) |
          exact absurd h.symm (coordU_ne_coordV ht _) | simp [coordU, coordV] at h) (hH1.congr_cls fun i => by simp)
      hPI1).weaken fun S2 ⟨lab2, hR2, hH2, hPI2⟩ =>
        Or.inl ⟨lab2, hH2.congr_cls fun i => by simp, ?_, hPI2⟩)
    simp only [Bool.false_eq_true, if_false] at hR2
    simp_rw [hR2]
    exact sum_eq_or _ _ hb

end Lax119563Proofs.Matrix

end Matrix_SpoilerWalk
