import Lax119563Proofs.Hierarchy.UnivKey

/-!
# Looking up the key in the table

A table is a list of entries `(key, ins)`, laid out as `key ++ [M] ++ ins.reverse ++ [E]`.
`lookup` finds the first entry whose key equals `KEY` and leaves its instruction on `INS`.
-/

namespace Lax119563Proofs.Hierarchy.Universal

open Prog Function

/-- The layout of a table entry. -/
def entryToks (e : List Tok × List Tok) : List Tok := e.1 ++ tM :: e.2.reverse ++ [tE]

/-- The layout of a table. -/
def tableToks (es : List (List Tok × List Tok)) : List Tok := es.flatMap entryToks

/-- Keys use only the tokens `U` and `S`; instructions do not use `E`. -/
def WellFormed (e : List Tok × List Tok) : Prop :=
  (∀ t ∈ e.1, t = tU ∨ t = tS) ∧ tE ∉ e.2

lemma dupWhileNot_runs {i j k : Stk} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (a : Tok)
    (l₂ : List Tok) (hl₂ : l₂.head? = some a) :
    ∀ (l : List Tok) (s : Stacks 16 13), a ∉ l → s i = l ++ l₂ →
      (dupWhileNot i j k a).RunsLe s
        (update (update (update s i l₂) j (l.reverse ++ s j)) k (l.reverse ++ s k))
        (40 * l.length + 1)
  | [], s, _, hs =>
    (RunsLe.loopF (c := fun r => (r i).isSome && r i != some a) (s := s)
      (p := seq (pushTopOf i j (List.finRange 15)) (seq (pushTopOf i k (List.finRange 15)) (pop i)))
      (by simp [tops, hs, hl₂])).of_eq (by simp at hs; stacks_eq) (by simp)
  | b :: l, s, ha, hs => by
    have hb : b ≠ a := fun h => ha (by simp [h])
    set s₁ := update (update (update s i (l ++ l₂)) j (b :: s j)) k (b :: s k)
    have hbody : (seq (pushTopOf i j (List.finRange 15)) (seq (pushTopOf i k (List.finRange 15))
        (pop i)) : SProg).RunsLe s s₁ 39 := by
      have h1 := pushTopOf_runs i j (s := s) (by simp [tops, hs]) (List.finRange 15)
        (List.mem_finRange b)
      have h2 := pushTopOf_runs i k (s := update s j (b :: s j))
        (by simp [tops, update_of_ne hij, hs]) (List.finRange 15) (List.mem_finRange b)
      have h3 := RunsLe.pop i (update (update s j (b :: s j)) k (b :: update s j (b :: s j) k))
      refine (h1.seq (h2.seq h3)).of_eq ?_ (by simp)
      funext x
      simp only [s₁, update_apply]
      split_ifs <;> simp_all
    have h2 := dupWhileNot_runs hij hik hjk a l₂ hl₂ l s₁ (fun h => ha (by simp [h]))
      (by simp [s₁, update_of_ne hij, update_of_ne hik])
    refine (RunsLe.loopT (c := fun r => (r i).isSome && r i != some a) (by simp [tops, hs, hb])
      hbody h2).of_eq ?_ (le_of_eq (by simp only [List.length_cons]; ring))
    funext x
    simp only [s₁, update_apply]
    split_ifs <;> simp_all

lemma compare_runs :
    ∀ (c a b : List Tok) (s : Stacks 16 13), s KEY = c ++ a → s TBL = c ++ b →
      (a = [] ∨ a.head? ≠ b.head?) →
      compare.RunsLe s (update (update (update (update s KEY a) KEY2 (c.reverse ++ s KEY2)) TBL b)
        TBL2 (c.reverse ++ s TBL2)) (40 * c.length + 1)
  | [], a, b, s, hK, hT, hab =>
    (RunsLe.loopF (c := fun r => (r KEY).isSome && r KEY == r TBL) (s := s)
      (p := seq (moveOne KEY KEY2) (moveOne TBL TBL2)) (by
        rcases hab with rfl | h
        · simp [tops, hK]
        · simp only [List.nil_append] at hK hT
          simp [tops, hK, hT, h])).of_eq (by simp at hK hT; sim_eq) (by simp)
  | x :: c, a, b, s, hK, hT, hab => by
    set s₁ := update (update (update (update s KEY (c ++ a)) KEY2 (x :: s KEY2)) TBL (c ++ b))
      TBL2 (x :: s TBL2)
    have h1 := moveOne_runs (i := KEY) (j := KEY2) (by decide) (s := s) (a := x) (l := c ++ a)
      (by simp [hK])
    have h2 := moveOne_runs (i := TBL) (j := TBL2) (by decide) (a := x) (l := c ++ b)
      (s := update (update s KEY (c ++ a)) KEY2 (x :: s KEY2)) (by simp [hT])
    have hbody : (seq (moveOne KEY KEY2) (moveOne TBL TBL2) : SProg).RunsLe s s₁ 36 :=
      (h1.seq h2).of_eq (by simp only [s₁]; sim_eq) (by simp)
    have h3 := compare_runs c a b s₁ (by simp [s₁]) (by simp [s₁]) hab
    refine (RunsLe.loopT (c := fun r => (r KEY).isSome && r KEY == r TBL) (by simp [tops, hK, hT])
      hbody h3).of_eq ?_ (by simp only [List.length_cons]; omega)
    simp only [s₁]
    sim_eq

/-- The longest common prefix decomposition. -/
lemma exists_lcp {α : Type} [DecidableEq α] :
    ∀ x y : List α, ∃ c a b, x = c ++ a ∧ y = c ++ b ∧ (a = [] ∨ a.head? ≠ b.head?)
  | [], y => ⟨[], [], y, rfl, rfl, .inl rfl⟩
  | h :: x, [] => ⟨[], h :: x, [], rfl, rfl, .inr (by simp)⟩
  | h :: x, h' :: y => by
    by_cases hh : h = h'
    · subst hh
      obtain ⟨c, a, b, rfl, rfl, hab⟩ := exists_lcp x y
      exact ⟨h :: c, a, b, rfl, rfl, hab⟩
    · exact ⟨[], h :: x, h' :: y, rfl, rfl, .inr (by simp [hh])⟩

lemma append_cons_cancel {α : Type} {x : α} :
    ∀ {l₁ l₂ r₁ r₂ : List α}, x ∉ l₁ → x ∉ l₂ → l₁ ++ x :: r₁ = l₂ ++ x :: r₂ → l₁ = l₂ ∧ r₁ = r₂
  | [], [], _, _, _, _, h => by simpa using h
  | [], y :: l₂, _, _, _, h₂, h => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    exact absurd (h.1 ▸ List.mem_cons_self) h₂
  | y :: l₁, [], _, _, h₁, _, h => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    exact absurd (h.1 ▸ List.mem_cons_self) h₁
  | y :: l₁, y' :: l₂, _, _, h₁, h₂, h => by
    simp only [List.cons_append, List.cons.injEq] at h
    obtain ⟨rfl, h⟩ := h
    obtain ⟨rfl, rfl⟩ := append_cons_cancel (fun hm => h₁ (List.mem_cons_of_mem _ hm))
      (fun hm => h₂ (List.mem_cons_of_mem _ hm)) h
    exact ⟨rfl, rfl⟩

lemma key_no_M {key : List Tok} (hk : ∀ t ∈ key, t = tU ∨ t = tS) : tM ∉ key := by
  intro h; rcases hk _ h with h | h <;> exact absurd h (by decide)

lemma key_no_E {key : List Tok} (hk : ∀ t ∈ key, t = tU ∨ t = tS) : tE ∉ key := by
  intro h; rcases hk _ h with h | h <;> exact absurd h (by decide)

/-- An entry whose key matches. -/
lemma examine_match {key ins rest : List Tok} (hk : ∀ t ∈ key, t = tU ∨ t = tS) (hi : tE ∉ ins)
    (s : Stacks 16 13) (hK : s KEY = key) (hT : s TBL = entryToks (key, ins) ++ rest)
    (hK2 : s KEY2 = []) :
    examine.RunsLe s (update (update (update (update s FLG (0 :: s FLG)) TBL (tE :: rest)) TBL2
      (ins ++ tM :: (key.reverse ++ s TBL2))) INS (ins ++ s INS))
      (100 * ((entryToks (key, ins)).length + 1)) := by
  have hT' : s TBL = key ++ (tM :: (ins.reverse ++ tE :: rest)) := by
    rw [hT]; simp [entryToks]
  have h1 := compare_runs key [] _ s (by simp [hK]) hT' (.inl rfl)
  set s₁ := update (update (update (update s KEY []) KEY2 (key.reverse ++ s KEY2)) TBL
    (tM :: (ins.reverse ++ tE :: rest))) TBL2 (key.reverse ++ s TBL2)
  have hc : (fun r : Stk → Option Tok => (r KEY).isNone && r TBL == some tM) (tops s₁) = true := by
    simp [tops, s₁]
  have h2 := RunsLe.push FLG 0 s₁
  set s₂ := update s₁ FLG (0 :: s₁ FLG)
  have h3 := moveOne_runs (i := TBL) (j := TBL2) (by decide) (s := s₂) (a := tM)
    (l := ins.reverse ++ tE :: rest) (by simp [s₂, s₁])
  set s₃ := update (update s₂ TBL (ins.reverse ++ tE :: rest)) TBL2 (tM :: s₂ TBL2)
  have h4 := dupWhileNot_runs (i := TBL) (j := TBL2) (k := INS) (by decide) (by decide)
    (by decide) tE (tE :: rest) (by simp) ins.reverse s₃ (by simpa using hi) (by simp [s₃])
  set s₄ := update (update (update s₃ TBL (tE :: rest)) TBL2 (ins.reverse.reverse ++ s₃ TBL2)) INS
    (ins.reverse.reverse ++ s₃ INS)
  have h5 := moveAll_runs (i := KEY2) (j := KEY) (by decide) key.reverse s₄
    (by simp [s₄, s₃, s₂, s₁, hK2])
  refine (h1.seq (((h2.seq (h3.seq h4)).iteT hc).seq h5)).of_eq ?_ ?_
  · simp only [s₄, s₃, s₂, s₁, List.reverse_reverse]
    sim_eq
  · simp only [entryToks, List.length_append, List.length_cons, List.length_reverse,
      List.length_nil]
    nlinarith

/-- An entry whose key does not match. -/
lemma examine_mismatch {key rest : List Tok} {e : List Tok × List Tok}
    (hk : ∀ t ∈ key, t = tU ∨ t = tS) (he : WellFormed e) (hne : e.1 ≠ key)
    (s : Stacks 16 13) (hK : s KEY = key) (hT : s TBL = entryToks e ++ rest)
    (hK2 : s KEY2 = []) :
    examine.RunsLe s (update (update s TBL rest) TBL2 ((entryToks e).reverse ++ s TBL2))
      (100 * ((entryToks e).length + key.length + 1)) := by
  set u := e.1 ++ tM :: e.2.reverse with hu
  have hEu : tE ∉ u := by
    simp only [u, List.mem_append, List.mem_cons, List.mem_reverse, not_or]
    exact ⟨key_no_E he.1, by decide, he.2⟩
  have hT' : s TBL = u ++ tE :: rest := by rw [hT]; simp [entryToks, u]
  obtain ⟨c, a, b, hka, hcb, hab⟩ := exists_lcp key (u ++ tE :: rest)
  have hEc : tE ∉ c := fun h => key_no_E hk (hka ▸ List.mem_append_left _ h)
  -- `c` is a prefix of `u`
  obtain ⟨b₀, hub, hb⟩ : ∃ b₀, u = c ++ b₀ ∧ b = b₀ ++ tE :: rest := by
    rcases List.append_eq_append_iff.mp hcb.symm with ⟨a', h1, h2⟩ | ⟨c', h1, h2⟩
    · exact ⟨a', h1, h2⟩
    · cases c' with
      | nil => exact ⟨[], by simpa using h1.symm, by simpa using h2.symm⟩
      | cons t c' =>
        simp only [List.cons_append, List.cons.injEq] at h2
        exact absurd (h1 ▸ h2.1 ▸ List.mem_append_right _ List.mem_cons_self) hEc
  have h1 := compare_runs c a b s (by rw [hK, hka]) (by rw [hT', hcb]) hab
  set s₁ := update (update (update (update s KEY a) KEY2 (c.reverse ++ s KEY2)) TBL b) TBL2
    (c.reverse ++ s TBL2)
  have hc : (fun r : Stk → Option Tok => (r KEY).isNone && r TBL == some tM) (tops s₁) = false := by
    simp only [tops, s₁]
    rcases a with _ | ⟨t, a⟩
    · -- the key is a prefix of the entry; it must not be followed by `M`
      simp only [List.append_nil] at hka
      subst hka
      cases b with
      | nil => simp
      | cons t b =>
        by_cases ht : t = tM
        · subst ht
          exfalso
          have := hcb
          rw [show u ++ tE :: rest = e.1 ++ tM :: (e.2.reverse ++ tE :: rest) by simp [u]] at this
          exact hne (append_cons_cancel (key_no_M he.1) (key_no_M hk) this).1
        · simp [ht]
    · simp
  have h2 := moveThrough_runs (i := TBL) (j := TBL2) (by decide) (s := s₁) (l₁ := b₀) (l₂ := rest)
    (fun h => hEu (hub ▸ List.mem_append_right _ h)) (by simp [s₁, hb])
  set s₂ := update (update s₁ TBL rest) TBL2 (tE :: (b₀.reverse ++ s₁ TBL2))
  have h3 := moveAll_runs (i := KEY2) (j := KEY) (by decide) c.reverse s₂ (by simp [s₂, s₁, hK2])
  refine (h1.seq ((h2.iteF hc).seq h3)).of_eq ?_ ?_
  · have hent : (entryToks e).reverse = tE :: (b₀.reverse ++ c.reverse) := by
      simp [entryToks, ← hu, hub]
    simp only [s₂, s₁, List.reverse_reverse, hent]
    funext k; fin_cases k <;> simp (config := {decide := true}) [update_apply, hK, hka, hK2]
  · have hcl : c.length ≤ key.length := by rw [hka]; simp
    have hcl' : (entryToks e).length = c.length + b₀.length + 1 := by
      have : entryToks e = u ++ [tE] := by simp [entryToks, u]
      rw [this, hub, List.length_append, List.length_append]; rfl
    simp only [List.length_reverse]
    nlinarith

end Lax119563Proofs.Hierarchy.Universal
