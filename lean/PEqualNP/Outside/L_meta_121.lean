import Mathlib
import PEqualNP.Defs

/-!
# The exact formula size of `two consecutive inputs are both true`

The statement below is the one recorded for the desk gap `L-meta-121`, byte for byte.

On `n` inputs in a row let `f n` be the OR, over the `n - 1` edges `(i, i + 1)`, of
`x i AND x (i + 1)`. The claim is that the smallest de Morgan formula for `f n` has exactly
`(n - 1) + n / 2` leaves, that is `n + n / 2 ≤ s + 1`.

The construction is the one of the sibling circuit result `L-meta-102`: three leaves per two
edges, `x (j + 1) AND (x j OR x (j + 2))`, plus one edge at the end;

`f (n + 2) = f n OR (x 1 AND (x 0 OR x 2))`.

The lower bound runs over the class `G N k` of `L-meta-102`: `k` free inputs, then a path on
the inputs `k .. N - 1`, with `d = N - k` path vertices. A formula for `G N k` has at least
`N + d / 2 - 1` leaves. Two facts drive the induction on `d`.

* Restricting the first path vertex `k` loses at least two leaves: one is the leaf on the
  vertex itself, and the other is the sibling of that leaf, which the restriction absorbs.
  This is where the leaf count matters: a surviving constant is not free here, it costs two
  leaves, so a formula that collapsed to a constant would have lost at least two leaves.
* After the restriction the first path vertex is deleted and the two cases are the class
  `G n k` on `d - 1` vertices and the class `G n (k + 1)` on `d - 2` vertices.

For `d < 4` the bound is the dependency bound: every one of the `N` inputs is read at least
once, so a formula has at least `N` leaves.
-/

namespace PEqualNP.Outside.L_meta_121_aux

open PEqualNP.MetaComplexity

/-! ## The class: `k` free OR inputs, then a path on the inputs `k .. N - 1` -/

/-- The class: `k` free OR inputs, then a path on the inputs `k .. N - 1`. -/
def G (N k : ℕ) (x : Fin N → Bool) : Bool :=
  decide ((∃ i : Fin N, i.val < k ∧ x i = true) ∨
    (∃ i j : Fin N, k ≤ i.val ∧ i.val + 1 = j.val ∧ x i = true ∧ x j = true))

/-- An input read at a natural index, `false` past the end. -/
def ext {N : ℕ} (x : Fin N → Bool) (j : ℕ) : Bool := if h : j < N then x ⟨j, h⟩ else false

theorem ext_fin {N : ℕ} (x : Fin N → Bool) (i : Fin N) : ext x i.val = x i := by
  simp [ext]

theorem ext_lt {N : ℕ} {x : Fin N → Bool} {j : ℕ} (h : ext x j = true) : j < N := by
  unfold ext at h
  split at h
  · assumption
  · simp at h

theorem ext_fn {N : ℕ} (Q : ℕ → Bool) (j : ℕ) :
    ext (fun i : Fin N => Q i.val) j = (decide (j < N) && Q j) := by
  unfold ext
  by_cases hj : j < N <;> simp [hj]

theorem ext_of_val {N : ℕ} (x : Fin N → Bool) (i : Fin N) (h : ext x i.val = true) :
    x i = true := by
  rwa [ext_fin] at h

theorem val_of_ext {N : ℕ} (x : Fin N → Bool) (i : Fin N) (h : x i = true) :
    ext x i.val = true := by
  rwa [ext_fin]

theorem ext_update {N : ℕ} (x : Fin N → Bool) (p : Fin N) (b : Bool) (j : ℕ) :
    ext (Function.update x p b) j = if j = p.val then b else ext x j := by
  unfold ext
  by_cases hj : j < N
  · simp [hj, Function.update_apply, Fin.ext_iff]
  · have : j ≠ p.val := by have := p.2; omega
    simp [hj, this]

theorem G_iff (N k : ℕ) (x : Fin N → Bool) : G N k x = true ↔
    ((∃ i, i < k ∧ ext x i = true) ∨ (∃ i, k ≤ i ∧ ext x i = true ∧ ext x (i + 1) = true)) := by
  unfold G
  rw [decide_eq_true_iff]
  constructor
  · rintro (⟨i, hi, hx⟩ | ⟨i, j, hi, hij, hx, hy⟩)
    · exact Or.inl ⟨i, hi, by rw [ext_fin]; exact hx⟩
    · refine Or.inr ⟨i, hi, by rw [ext_fin]; exact hx, ?_⟩
      rw [hij, ext_fin]; exact hy
  · rintro (⟨i, hi, hx⟩ | ⟨i, hi, hx, hy⟩)
    · have hl := ext_lt hx
      refine Or.inl ⟨⟨i, hl⟩, hi, ?_⟩
      rw [← ext_fin x ⟨i, hl⟩]; exact hx
    · have hl := ext_lt hy
      refine Or.inr ⟨⟨i, by omega⟩, ⟨i + 1, hl⟩, hi, rfl, ?_, ?_⟩
      · rw [← ext_fin x ⟨i, by omega⟩]; exact hx
      · rw [← ext_fin x ⟨i + 1, hl⟩]; exact hy

/-- The renaming that skips index `k`: `i ↦ i` for `i ≤ k`, `i ↦ i - 1` for `i > k`. -/
def del (n k : ℕ) (hk : k < n) : Fin (n + 1) → Fin n :=
  fun i => ⟨if i.val ≤ k then i.val else i.val - 1, by have := i.2; split <;> omega⟩

theorem ext_del (n k : ℕ) (hk : k < n) (y : Fin n → Bool) (b : Bool) (j : ℕ) :
    ext (Function.update (y ∘ del n k hk) ⟨k, by omega⟩ b) j
      = if j = k then b else if j < k then ext y j else ext y (j - 1) := by
  rw [ext_update]
  by_cases hjk : j = k
  · simp [hjk]
  · rw [if_neg hjk, if_neg hjk]
    unfold ext
    by_cases hj : j < n + 1
    · rw [dif_pos hj]
      by_cases hjk' : j < k
      · rw [if_pos hjk', dif_pos (by omega)]
        simp [del, show j ≤ k by omega]
      · rw [if_neg hjk', dif_pos (by omega)]
        simp [del, show ¬ j ≤ k by omega]
    · rw [dif_neg hj, if_neg (by omega), dif_neg (by omega)]

theorem G_del_false (n k : ℕ) (hk : k < n) (y : Fin n → Bool) :
    G (n + 1) k (Function.update (y ∘ del n k hk) ⟨k, by omega⟩ false) = G n k y := by
  rw [Bool.eq_iff_iff, G_iff, G_iff]
  simp only [ext_del]
  constructor
  · rintro (⟨i, hi, hx⟩ | ⟨i, hi, hx, hy⟩)
    · rw [if_neg (by omega), if_pos hi] at hx
      exact Or.inl ⟨i, hi, hx⟩
    · by_cases hik : i = k
      · rw [if_pos hik] at hx; exact absurd hx (by simp)
      · rw [if_neg hik, if_neg (by omega)] at hx
        rw [if_neg (by omega), if_neg (by omega)] at hy
        refine Or.inr ⟨i - 1, by omega, hx, ?_⟩
        rwa [show i - 1 + 1 = i + 1 - 1 by omega]
  · rintro (⟨i, hi, hx⟩ | ⟨i, hi, hx, hy⟩)
    · refine Or.inl ⟨i, hi, ?_⟩
      rw [if_neg (by omega), if_pos hi]; exact hx
    · refine Or.inr ⟨i + 1, by omega, ?_, ?_⟩
      · rw [if_neg (by omega), if_neg (by omega)]; simpa using hx
      · rw [if_neg (by omega), if_neg (by omega)]; simpa using hy

theorem G_del_true (n k : ℕ) (hk : k < n) (y : Fin n → Bool) :
    G (n + 1) k (Function.update (y ∘ del n k hk) ⟨k, by omega⟩ true) = G n (k + 1) y := by
  rw [Bool.eq_iff_iff, G_iff, G_iff]
  simp only [ext_del]
  constructor
  · rintro (⟨i, hi, hx⟩ | ⟨i, hi, hx, hy⟩)
    · rw [if_neg (by omega), if_pos hi] at hx
      exact Or.inl ⟨i, by omega, hx⟩
    · by_cases hik : i = k
      · rw [if_neg (by omega), if_neg (by omega)] at hy
        refine Or.inl ⟨k, by omega, ?_⟩
        rwa [show k = i + 1 - 1 by omega]
      · by_cases hik1 : i = k + 1
        · rw [if_neg (by omega), if_neg (by omega)] at hx
          refine Or.inl ⟨k, by omega, ?_⟩
          rwa [show k = i - 1 by omega]
        · rw [if_neg hik, if_neg (by omega)] at hx
          rw [if_neg (by omega), if_neg (by omega)] at hy
          refine Or.inr ⟨i - 1, by omega, hx, ?_⟩
          rwa [show i - 1 + 1 = i + 1 - 1 by omega]
  · rintro (⟨i, hi, hx⟩ | ⟨i, hi, hx, hy⟩)
    · by_cases hik : i < k
      · refine Or.inl ⟨i, hik, ?_⟩
        rw [if_neg (by omega), if_pos hik]; exact hx
      · have e : i = k := by omega
        subst e
        refine Or.inr ⟨i, le_rfl, by simp, ?_⟩
        rw [if_neg (by omega), if_neg (by omega)]; simpa using hx
    · refine Or.inr ⟨i + 1, by omega, ?_, ?_⟩
      · rw [if_neg (by omega), if_neg (by omega)]; simpa using hx
      · rw [if_neg (by omega), if_neg (by omega)]; simpa using hy

/-- `G N k` depends on every input once the path has at least two vertices. -/
theorem G_dep (N k : ℕ) (hd : k + 2 ≤ N) (p : Fin N) :
    ∃ x : Fin N → Bool, G N k (Function.update x p (!x p)) ≠ G N k x := by
  by_cases hp : p.val < k
  · refine ⟨fun _ => false, ?_⟩
    have h1 : G N k (Function.update (fun _ => false) p (!false)) = true := by
      rw [G_iff]
      refine Or.inl ⟨p.val, hp, ?_⟩
      rw [ext_update]; simp
    have h0 : G N k (fun _ => false) = false := by
      rw [← Bool.not_eq_true, G_iff]
      rintro (⟨i, _, hx⟩ | ⟨i, _, hx, _⟩) <;> simp [ext] at hx
    rw [h1, h0]; simp
  · set q : ℕ := if p.val + 1 < N then p.val + 1 else p.val - 1 with hq
    have hqN : q < N := by rw [hq]; split <;> omega
    have hqk : k ≤ q := by have := p.2; rw [hq]; split <;> omega
    have hpq : p.val ≠ q := by rw [hq]; split <;> omega
    refine ⟨fun i : Fin N => decide (i.val = q), ?_⟩
    have hxp : (fun i : Fin N => decide (i.val = q)) p = false := by simp [hpq]
    rw [hxp]
    have h1 : G N k (Function.update (fun i : Fin N => decide (i.val = q)) p (!false)) = true := by
      rw [G_iff]
      right
      by_cases hc : p.val + 1 < N
      · have hqv : q = p.val + 1 := by rw [hq, if_pos hc]
        refine ⟨p.val, by omega, ?_, ?_⟩
        · rw [ext_update]; simp
        · rw [ext_update, if_neg (by omega), ext_fn (fun j => decide (j = q))]; simp [hqv, hc]
      · have hqv : q = p.val - 1 := by rw [hq, if_neg hc]
        refine ⟨q, hqk, ?_, ?_⟩
        · rw [ext_update, if_neg (by omega), ext_fn (fun j => decide (j = q))]; simp [hqN]
        · rw [ext_update, if_pos (by omega)]; rfl
    have h0 : G N k (fun i : Fin N => decide (i.val = q)) = false := by
      rw [← Bool.not_eq_true, G_iff]
      rintro (⟨i, hi, hx⟩ | ⟨i, _, hx, hy⟩)
      · rw [ext_fn (fun j => decide (j = q))] at hx
        simp at hx; omega
      · rw [ext_fn (fun j => decide (j = q))] at hx hy
        simp at hx hy; omega
    rw [h1, h0]; simp

/-- `G N k` is not constant once the path has at least two vertices. -/
theorem G_nonconst (N k : ℕ) (hd : k + 2 ≤ N) :
    ∃ x y : Fin N → Bool, G N k x ≠ G N k y := by
  have h0 : G N k (fun _ => false) = false := by
    rw [← Bool.not_eq_true, G_iff]
    rintro (⟨i, _, hx⟩ | ⟨i, _, hx, _⟩) <;> simp [ext] at hx
  have h1 : G N k (fun i : Fin N => decide (i.val = k ∨ i.val = k + 1)) = true := by
    rw [G_iff]
    right
    refine ⟨k, le_rfl, ?_, ?_⟩
    · rw [ext, dif_pos (by omega)]; simp
    · rw [ext, dif_pos (by omega)]; simp
  refine ⟨fun i : Fin N => decide (i.val = k ∨ i.val = k + 1), fun _ => false, ?_⟩
  rw [h1, h0]; simp

/-! ## Leaves and occurrences -/

/-- The number of occurrences of the input `k` in a formula. -/
def occ {n : ℕ} : DMFormula n → Fin n → ℕ
  | DMFormula.lit i _, k => if i = k then 1 else 0
  | DMFormula.and a b, k => occ a k + occ b k
  | DMFormula.or a b, k => occ a k + occ b k

theorem leaves_eq {n : ℕ} (φ : DMFormula n) : φ.leaves = ∑ k, occ φ k := by
  induction φ with
  | lit i b =>
    show 1 = ∑ k : Fin n, (if i = k then 1 else 0)
    rw [Finset.sum_eq_single i]
    · simp
    · intro k _ hk; simp [Ne.symm hk]
    · intro h; simp at h
  | and a b iha ihb =>
    show a.leaves + b.leaves = ∑ k, (occ a k + occ b k)
    rw [iha, ihb, Finset.sum_add_distrib]
  | or a b iha ihb =>
    show a.leaves + b.leaves = ∑ k, (occ a k + occ b k)
    rw [iha, ihb, Finset.sum_add_distrib]

theorem leaves_pos {n : ℕ} (φ : DMFormula n) : 1 ≤ φ.leaves := by
  induction φ with
  | lit i b => show 1 ≤ 1; omega
  | and a b iha ihb => show 1 ≤ a.leaves + b.leaves; omega
  | or a b iha ihb => show 1 ≤ a.leaves + b.leaves; omega

/-- A formula that does not read the input `p` does not depend on it. -/
theorem eval_update_of_zero {n : ℕ} (φ : DMFormula n) (p : Fin n) (h : occ φ p = 0)
    (x : Fin n → Bool) (c : Bool) :
    φ.eval (Function.update x p c) = φ.eval x := by
  induction φ with
  | lit i b =>
    by_cases hip : i = p
    · rw [hip] at h; simp [occ] at h
    · simp only [DMFormula.eval]
      rw [show Function.update x p c i = x i by simp [Function.update_apply, hip]]
  | and a b iha ihb =>
    have h1 : occ a p = 0 := by simp only [occ] at h; omega
    have h2 : occ b p = 0 := by simp only [occ] at h; omega
    show (a.eval (Function.update x p c) && b.eval (Function.update x p c))
      = (a.eval x && b.eval x)
    rw [iha h1, ihb h2]
  | or a b iha ihb =>
    have h1 : occ a p = 0 := by simp only [occ] at h; omega
    have h2 : occ b p = 0 := by simp only [occ] at h; omega
    show (a.eval (Function.update x p c) || b.eval (Function.update x p c))
      = (a.eval x || b.eval x)
    rw [iha h1, ihb h2]

/-- A dependent input occurs at least once. -/
theorem occ_pos_of_dep {n : ℕ} (φ : DMFormula n) (p : Fin n)
    (h : ∃ x : Fin n → Bool, φ.eval (Function.update x p (!x p)) ≠ φ.eval x) : 1 ≤ occ φ p := by
  by_contra hc
  have h0 : occ φ p = 0 := by omega
  obtain ⟨x, hx⟩ := h
  exact hx (eval_update_of_zero φ p h0 x (!x p))

/-! ## Restriction of one input, with the constants simplified away -/

/-- A restricted subformula: a formula, or a constant. -/
abbrev Simp (n : ℕ) := Bool ⊕ DMFormula n

/-- The value of a restricted formula. -/
def sval {n : ℕ} : Simp n → (Fin n → Bool) → Bool
  | Sum.inl b, _ => b
  | Sum.inr φ, x => φ.eval x

/-- The leaves of a restricted formula; a surviving constant costs nothing. -/
def sleaves {n : ℕ} : Simp n → ℕ
  | Sum.inl _ => 0
  | Sum.inr φ => φ.leaves

/-- The AND of two restricted formulas, with the constants simplified: the first argument is
matched first, so that a constant left child reduces by computation. -/
def mkAnd {n : ℕ} (s t : Simp n) : Simp n :=
  match s, t with
  | Sum.inl true, u => u
  | Sum.inl false, _ => Sum.inl false
  | Sum.inr a, Sum.inl true => Sum.inr a
  | Sum.inr a, Sum.inl false => Sum.inl false
  | Sum.inr a, Sum.inr b => Sum.inr (DMFormula.and a b)

/-- The OR of two restricted formulas, with the constants simplified. -/
def mkOr {n : ℕ} (s t : Simp n) : Simp n :=
  match s, t with
  | Sum.inl false, u => u
  | Sum.inl true, _ => Sum.inl true
  | Sum.inr a, Sum.inl false => Sum.inr a
  | Sum.inr a, Sum.inl true => Sum.inl true
  | Sum.inr a, Sum.inr b => Sum.inr (DMFormula.or a b)

/-- Substituting `v` for the input `p`. -/
def rsubst {n : ℕ} : DMFormula n → Fin n → Bool → Simp n
  | DMFormula.lit i c, p, v => if i = p then Sum.inl (c == v) else Sum.inr (DMFormula.lit i c)
  | DMFormula.and a b, p, v => mkAnd (rsubst a p v) (rsubst b p v)
  | DMFormula.or a b, p, v => mkOr (rsubst a p v) (rsubst b p v)

theorem mkAnd_eval {n : ℕ} (s t : Simp n) (x : Fin n → Bool) :
    sval (mkAnd s t) x = (sval s x && sval t x) := by
  rcases s with b | a
  · cases b
    · rcases t with c | d
      · cases c <;> rfl
      · rfl
    · rcases t with c | d
      · cases c <;> rfl
      · rfl
  · rcases t with c | d
    · cases c <;> simp [mkAnd, sval]
    · rfl

theorem mkOr_eval {n : ℕ} (s t : Simp n) (x : Fin n → Bool) :
    sval (mkOr s t) x = (sval s x || sval t x) := by
  rcases s with b | a
  · cases b
    · rcases t with c | d
      · cases c <;> rfl
      · rfl
    · rcases t with c | d
      · cases c <;> rfl
      · rfl
  · rcases t with c | d
    · cases c <;> simp [mkOr, sval]
    · rfl

theorem mkAnd_leaves {n : ℕ} (s t : Simp n) :
    sleaves (mkAnd s t) ≤ sleaves s + sleaves t := by
  rcases s with b | a
  · cases b
    · rcases t with c | d
      · cases c <;> simp [mkAnd, sleaves]
      · simp [mkAnd, sleaves]
    · rcases t with c | d
      · cases c <;> simp [mkAnd, sleaves]
      · simp [mkAnd, sleaves]
  · rcases t with c | d
    · cases c <;> simp [mkAnd, sleaves]
    · show a.leaves + d.leaves ≤ a.leaves + d.leaves
      omega

theorem mkOr_leaves {n : ℕ} (s t : Simp n) :
    sleaves (mkOr s t) ≤ sleaves s + sleaves t := by
  rcases s with b | a
  · cases b
    · rcases t with c | d
      · cases c <;> simp [mkOr, sleaves]
      · simp [mkOr, sleaves]
    · rcases t with c | d
      · cases c <;> simp [mkOr, sleaves]
      · simp [mkOr, sleaves]
  · rcases t with c | d
    · cases c <;> simp [mkOr, sleaves]
    · show a.leaves + d.leaves ≤ a.leaves + d.leaves
      omega

theorem rsubst_lit_self {n : ℕ} (p : Fin n) (c v : Bool) :
    rsubst (DMFormula.lit p c) p v = Sum.inl (c == v) := by
  simp [rsubst]

theorem rsubst_lit_other {n : ℕ} (i p : Fin n) (c v : Bool) (h : i ≠ p) :
    rsubst (DMFormula.lit i c) p v = Sum.inr (DMFormula.lit i c) := by
  simp [rsubst, h]

theorem eq_beq (c v : Bool) : (c == v) = if c then v else !v := by
  cases c <;> cases v <;> rfl

theorem rsubst_eval {n : ℕ} (φ : DMFormula n) (p : Fin n) (v : Bool) (x : Fin n → Bool) :
    sval (rsubst φ p v) x = φ.eval (Function.update x p v) := by
  induction φ with
  | lit i c =>
    by_cases hip : i = p
    · rw [hip]
      rw [rsubst_lit_self, eq_beq]
      show (if c then v else !v)
        = (if c then (Function.update x p v) p else !((Function.update x p v) p))
      rw [show (Function.update x p v) p = v by simp [Function.update_apply]]
    · rw [rsubst_lit_other i p c v hip]
      show (DMFormula.lit i c).eval x = (DMFormula.lit i c).eval (Function.update x p v)
      simp only [DMFormula.eval]
      rw [show Function.update x p v i = x i by simp [Function.update_apply, hip]]
  | and a b iha ihb =>
    show sval (mkAnd (rsubst a p v) (rsubst b p v)) x
      = (a.eval (Function.update x p v) && b.eval (Function.update x p v))
    rw [mkAnd_eval, iha, ihb]
  | or a b iha ihb =>
    show sval (mkOr (rsubst a p v) (rsubst b p v)) x
      = (a.eval (Function.update x p v) || b.eval (Function.update x p v))
    rw [mkOr_eval, iha, ihb]

theorem rsubst_leaves_le {n : ℕ} (φ : DMFormula n) (p : Fin n) (v : Bool) :
    sleaves (rsubst φ p v) ≤ φ.leaves := by
  induction φ with
  | lit i c =>
    by_cases hip : i = p
    · rw [hip, rsubst_lit_self]
      show 0 ≤ 1
      omega
    · rw [rsubst_lit_other i p c v hip]
      show 1 ≤ 1
      omega
  | and a b iha ihb =>
    show sleaves (mkAnd (rsubst a p v) (rsubst b p v)) ≤ a.leaves + b.leaves
    have h := mkAnd_leaves (rsubst a p v) (rsubst b p v)
    omega
  | or a b iha ihb =>
    show sleaves (mkOr (rsubst a p v) (rsubst b p v)) ≤ a.leaves + b.leaves
    have h := mkOr_leaves (rsubst a p v) (rsubst b p v)
    omega

/-! ### The four absorbing shapes

A literal whose parent is an `AND` is absorbed when the literal is set to `false`, and a
literal under an `OR` is absorbed when it is set to `true`. In each case the sibling of the
literal disappears with it, which is the second of the two leaves. -/

theorem absorb_and_left {n : ℕ} (p : Fin n) (c : Bool) (ψ : DMFormula n) :
    ∃ v : Bool, sleaves (mkAnd (rsubst (DMFormula.lit p c) p v) (rsubst ψ p v)) + 2
      ≤ 1 + ψ.leaves := by
  refine ⟨!c, ?_⟩
  have hcv : (c == !c) = false := by cases c <;> rfl
  rw [rsubst_lit_self, hcv]
  have hm : mkAnd (Sum.inl false) (rsubst ψ p (!c)) = Sum.inl false := rfl
  rw [hm]
  have := leaves_pos ψ
  show 0 + 2 ≤ 1 + ψ.leaves
  omega

theorem absorb_and_right {n : ℕ} (p : Fin n) (c : Bool) (ψ : DMFormula n) :
    ∃ v : Bool, sleaves (mkAnd (rsubst ψ p v) (rsubst (DMFormula.lit p c) p v)) + 2
      ≤ ψ.leaves + 1 := by
  refine ⟨!c, ?_⟩
  have hcv : (c == !c) = false := by cases c <;> rfl
  rw [rsubst_lit_self, hcv]
  have hm : mkAnd (rsubst ψ p (!c)) (Sum.inl false) = Sum.inl false := by
    cases h : rsubst ψ p (!c) with
    | inl b => cases b <;> rfl
    | inr a => rfl
  rw [hm]
  have := leaves_pos ψ
  show 0 + 2 ≤ ψ.leaves + 1
  omega

theorem absorb_or_left {n : ℕ} (p : Fin n) (c : Bool) (ψ : DMFormula n) :
    ∃ v : Bool, sleaves (mkOr (rsubst (DMFormula.lit p c) p v) (rsubst ψ p v)) + 2
      ≤ 1 + ψ.leaves := by
  refine ⟨c, ?_⟩
  have hcv : (c == c) = true := by cases c <;> rfl
  rw [rsubst_lit_self, hcv]
  have hm : mkOr (Sum.inl true) (rsubst ψ p c) = Sum.inl true := rfl
  rw [hm]
  have := leaves_pos ψ
  show 0 + 2 ≤ 1 + ψ.leaves
  omega

theorem absorb_or_right {n : ℕ} (p : Fin n) (c : Bool) (ψ : DMFormula n) :
    ∃ v : Bool, sleaves (mkOr (rsubst ψ p v) (rsubst (DMFormula.lit p c) p v)) + 2
      ≤ ψ.leaves + 1 := by
  refine ⟨c, ?_⟩
  have hcv : (c == c) = true := by cases c <;> rfl
  rw [rsubst_lit_self, hcv]
  have hm : mkOr (rsubst ψ p c) (Sum.inl true) = Sum.inl true := by
    cases h : rsubst ψ p c with
    | inl b => cases b <;> rfl
    | inr a => rfl
  rw [hm]
  have := leaves_pos ψ
  show 0 + 2 ≤ ψ.leaves + 1
  omega

/-- **Restricting a non-literal formula loses at least two leaves**: the leaf on the input
itself, and the sibling of that leaf, which the restriction absorbs. -/
theorem restrict_loses_two {n : ℕ} (φ : DMFormula n) (p : Fin n) (h1 : 1 ≤ occ φ p)
    (h2 : ∀ c : Bool, φ ≠ DMFormula.lit p c) :
    ∃ v : Bool, sleaves (rsubst φ p v) + 2 ≤ φ.leaves := by
  induction φ with
  | lit i c =>
    by_cases hip : i = p
    · rw [hip] at h2; exact absurd rfl (h2 c)
    · simp only [occ, if_neg hip] at h1; omega
  | and a b iha ihb =>
    have hsum : 1 ≤ occ a p + occ b p := by simpa only [occ] using h1
    by_cases ha : 1 ≤ occ a p
    · cases a with
      | lit i c =>
        have hip : i = p := by
          by_contra hne
          simp only [occ, if_neg hne] at ha
          omega
        rw [hip]
        exact absorb_and_left p c b
      | and a1 a2 =>
        obtain ⟨v, hv⟩ := iha ha (fun c hc => nomatch hc)
        refine ⟨v, ?_⟩
        have hv' : sleaves (rsubst (DMFormula.and a1 a2) p v) + 2 ≤ a1.leaves + a2.leaves := hv
        have h1' := mkAnd_leaves (rsubst (DMFormula.and a1 a2) p v) (rsubst b p v)
        have h2' := rsubst_leaves_le b p v
        show sleaves (mkAnd (rsubst (DMFormula.and a1 a2) p v) (rsubst b p v)) + 2
          ≤ (a1.leaves + a2.leaves) + b.leaves
        omega
      | or a1 a2 =>
        obtain ⟨v, hv⟩ := iha ha (fun c hc => nomatch hc)
        refine ⟨v, ?_⟩
        have hv' : sleaves (rsubst (DMFormula.or a1 a2) p v) + 2 ≤ a1.leaves + a2.leaves := hv
        have h1' := mkAnd_leaves (rsubst (DMFormula.or a1 a2) p v) (rsubst b p v)
        have h2' := rsubst_leaves_le b p v
        show sleaves (mkAnd (rsubst (DMFormula.or a1 a2) p v) (rsubst b p v)) + 2
          ≤ (a1.leaves + a2.leaves) + b.leaves
        omega
    · have hb : 1 ≤ occ b p := by omega
      cases b with
      | lit i c =>
        have hip : i = p := by
          by_contra hne
          simp only [occ, if_neg hne] at hb
          omega
        rw [hip]
        exact absorb_and_right p c a
      | and b1 b2 =>
        obtain ⟨v, hv⟩ := ihb hb (fun c hc => nomatch hc)
        refine ⟨v, ?_⟩
        have hv' : sleaves (rsubst (DMFormula.and b1 b2) p v) + 2 ≤ b1.leaves + b2.leaves := hv
        have h1' := mkAnd_leaves (rsubst a p v) (rsubst (DMFormula.and b1 b2) p v)
        have h2' := rsubst_leaves_le a p v
        show sleaves (mkAnd (rsubst a p v) (rsubst (DMFormula.and b1 b2) p v)) + 2
          ≤ a.leaves + (b1.leaves + b2.leaves)
        omega
      | or b1 b2 =>
        obtain ⟨v, hv⟩ := ihb hb (fun c hc => nomatch hc)
        refine ⟨v, ?_⟩
        have hv' : sleaves (rsubst (DMFormula.or b1 b2) p v) + 2 ≤ b1.leaves + b2.leaves := hv
        have h1' := mkAnd_leaves (rsubst a p v) (rsubst (DMFormula.or b1 b2) p v)
        have h2' := rsubst_leaves_le a p v
        show sleaves (mkAnd (rsubst a p v) (rsubst (DMFormula.or b1 b2) p v)) + 2
          ≤ a.leaves + (b1.leaves + b2.leaves)
        omega
  | or a b iha ihb =>
    have hsum : 1 ≤ occ a p + occ b p := by simpa only [occ] using h1
    by_cases ha : 1 ≤ occ a p
    · cases a with
      | lit i c =>
        have hip : i = p := by
          by_contra hne
          simp only [occ, if_neg hne] at ha
          omega
        rw [hip]
        exact absorb_or_left p c b
      | and a1 a2 =>
        obtain ⟨v, hv⟩ := iha ha (fun c hc => nomatch hc)
        refine ⟨v, ?_⟩
        have hv' : sleaves (rsubst (DMFormula.and a1 a2) p v) + 2 ≤ a1.leaves + a2.leaves := hv
        have h1' := mkOr_leaves (rsubst (DMFormula.and a1 a2) p v) (rsubst b p v)
        have h2' := rsubst_leaves_le b p v
        show sleaves (mkOr (rsubst (DMFormula.and a1 a2) p v) (rsubst b p v)) + 2
          ≤ (a1.leaves + a2.leaves) + b.leaves
        omega
      | or a1 a2 =>
        obtain ⟨v, hv⟩ := iha ha (fun c hc => nomatch hc)
        refine ⟨v, ?_⟩
        have hv' : sleaves (rsubst (DMFormula.or a1 a2) p v) + 2 ≤ a1.leaves + a2.leaves := hv
        have h1' := mkOr_leaves (rsubst (DMFormula.or a1 a2) p v) (rsubst b p v)
        have h2' := rsubst_leaves_le b p v
        show sleaves (mkOr (rsubst (DMFormula.or a1 a2) p v) (rsubst b p v)) + 2
          ≤ (a1.leaves + a2.leaves) + b.leaves
        omega
    · have hb : 1 ≤ occ b p := by omega
      cases b with
      | lit i c =>
        have hip : i = p := by
          by_contra hne
          simp only [occ, if_neg hne] at hb
          omega
        rw [hip]
        exact absorb_or_right p c a
      | and b1 b2 =>
        obtain ⟨v, hv⟩ := ihb hb (fun c hc => nomatch hc)
        refine ⟨v, ?_⟩
        have hv' : sleaves (rsubst (DMFormula.and b1 b2) p v) + 2 ≤ b1.leaves + b2.leaves := hv
        have h1' := mkOr_leaves (rsubst a p v) (rsubst (DMFormula.and b1 b2) p v)
        have h2' := rsubst_leaves_le a p v
        show sleaves (mkOr (rsubst a p v) (rsubst (DMFormula.and b1 b2) p v)) + 2
          ≤ a.leaves + (b1.leaves + b2.leaves)
        omega
      | or b1 b2 =>
        obtain ⟨v, hv⟩ := ihb hb (fun c hc => nomatch hc)
        refine ⟨v, ?_⟩
        have hv' : sleaves (rsubst (DMFormula.or b1 b2) p v) + 2 ≤ b1.leaves + b2.leaves := hv
        have h1' := mkOr_leaves (rsubst a p v) (rsubst (DMFormula.or b1 b2) p v)
        have h2' := rsubst_leaves_le a p v
        show sleaves (mkOr (rsubst a p v) (rsubst (DMFormula.or b1 b2) p v)) + 2
          ≤ a.leaves + (b1.leaves + b2.leaves)
        omega

/-! ## Renaming the inputs of a formula -/

/-- Renaming the inputs along `π`: `lit i c` becomes `lit (π i) c`. -/
def relabel {m n : ℕ} (π : Fin m → Fin n) : DMFormula m → DMFormula n
  | DMFormula.lit i c => DMFormula.lit (π i) c
  | DMFormula.and a b => DMFormula.and (relabel π a) (relabel π b)
  | DMFormula.or a b => DMFormula.or (relabel π a) (relabel π b)

theorem relabel_eval {m n : ℕ} (π : Fin m → Fin n) (φ : DMFormula m) (y : Fin n → Bool) :
    (relabel π φ).eval y = φ.eval (fun i => y (π i)) := by
  induction φ with
  | lit i c => simp only [relabel, DMFormula.eval]
  | and a b iha ihb =>
    show ((relabel π a).eval y && (relabel π b).eval y) = (a.eval _ && b.eval _)
    rw [iha, ihb]
  | or a b iha ihb =>
    show ((relabel π a).eval y || (relabel π b).eval y) = (a.eval _ || b.eval _)
    rw [iha, ihb]

theorem relabel_leaves {m n : ℕ} (π : Fin m → Fin n) (φ : DMFormula m) :
    (relabel π φ).leaves = φ.leaves := by
  induction φ with
  | lit i c => rfl
  | and a b iha ihb =>
    show (relabel π a).leaves + (relabel π b).leaves = a.leaves + b.leaves
    rw [iha, ihb]
  | or a b iha ihb =>
    show (relabel π a).leaves + (relabel π b).leaves = a.leaves + b.leaves
    rw [iha, ihb]

/-! ## The lower bound for the class -/

theorem G_lower : ∀ d : ℕ, 2 ≤ d → ∀ k N s : ℕ, N = k + d →
    HasLeafSize N (G N k) s → N + d / 2 ≤ s + 1 := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro hd k N s hN h
    obtain ⟨φ, hle, hev⟩ := h
    by_cases hd4 : d < 4
    · -- every input is read at least once
      have hdep : ∀ p : Fin N, 1 ≤ occ φ p := by
        intro p
        obtain ⟨x, hx⟩ := G_dep N k (by omega) p
        exact occ_pos_of_dep φ p ⟨x, by rw [hev, hev]; exact hx⟩
      have hNle : N ≤ φ.leaves := by
        rw [leaves_eq]
        calc N = ∑ _p : Fin N, 1 := by simp
          _ ≤ ∑ p : Fin N, occ φ p := Finset.sum_le_sum (fun p _ => hdep p)
      have : d / 2 ≤ 1 := by omega
      omega
    · have hkN : k < N := by omega
      have hdep := G_dep N k (by omega) ⟨k, hkN⟩
      have hoc : 1 ≤ occ φ ⟨k, hkN⟩ :=
        occ_pos_of_dep φ ⟨k, hkN⟩ ⟨hdep.choose, by rw [hev, hev]; exact hdep.choose_spec⟩
      -- the formula is not a single literal
      have hnotlit : ∀ c : Bool, φ ≠ DMFormula.lit ⟨k, hkN⟩ c := by
        intro c hc
        have hqp : (⟨k + 1, by omega⟩ : Fin N) ≠ ⟨k, hkN⟩ := by
          intro hEq
          have hv' := congrArg Fin.val hEq
          simp at hv'
        obtain ⟨x, hx⟩ := G_dep N k (by omega) (⟨k + 1, by omega⟩ : Fin N)
        have hq1 : 1 ≤ occ φ ⟨k + 1, by omega⟩ :=
          occ_pos_of_dep φ ⟨k + 1, by omega⟩ ⟨x, by rw [hev, hev]; exact hx⟩
        rw [hc] at hq1
        simp only [occ] at hq1
        rw [if_neg (Ne.symm hqp)] at hq1
        omega
      obtain ⟨v, hv⟩ := restrict_loses_two φ ⟨k, hkN⟩ hoc hnotlit
      obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
      have hk : k < n := by omega
      cases v with
      | false =>
        -- the class `G n k` on `d - 1` path vertices
        have hnc : ∃ x y : Fin (n + 1) → Bool,
            sval (rsubst φ ⟨k, hkN⟩ false) x ≠ sval (rsubst φ ⟨k, hkN⟩ false) y := by
          obtain ⟨a, b, hab⟩ := G_nonconst n k (by omega)
          refine ⟨fun i => a (del n k hk i), fun i => b (del n k hk i), ?_⟩
          have e1 : sval (rsubst φ ⟨k, hkN⟩ false) (fun i => a (del n k hk i)) = G n k a := by
            rw [rsubst_eval, hev]; exact G_del_false n k hk a
          have e2 : sval (rsubst φ ⟨k, hkN⟩ false) (fun i => b (del n k hk i)) = G n k b := by
            rw [rsubst_eval, hev]; exact G_del_false n k hk b
          rw [e1, e2]; exact hab
        cases hrs : rsubst φ ⟨k, hkN⟩ false with
        | inl b0 =>
          exfalso
          obtain ⟨x, y, hxy⟩ := hnc
          rw [hrs] at hxy
          simp only [sval] at hxy
          exact hxy rfl
        | inr ψ =>
          have hψle : ψ.leaves + 2 ≤ s := by
            have h2 := hv
            rw [hrs] at h2
            simp only [sleaves] at h2
            omega
          have hev' : ∀ y : Fin n → Bool, (relabel (del n k hk) ψ).eval y = G n k y := by
            intro y
            rw [relabel_eval]
            have h1 : ψ.eval (fun i => y (del n k hk i))
                = sval (rsubst φ ⟨k, hkN⟩ false) (fun i => y (del n k hk i)) := by
              rw [hrs]; rfl
            rw [h1, rsubst_eval, hev]
            exact G_del_false n k hk y
          have hinst := ih (d - 1) (by omega) (by omega) k n
            (relabel (del n k hk) ψ).leaves (by omega) ⟨_, le_rfl, hev'⟩
          have hle2 : (relabel (del n k hk) ψ).leaves + 2 ≤ s := by
            rw [relabel_leaves]; omega
          have hdiv : d / 2 ≤ (d - 1) / 2 + 1 := by omega
          omega
      | true =>
        -- the class `G n (k + 1)` on `d - 2` path vertices
        have hnc : ∃ x y : Fin (n + 1) → Bool,
            sval (rsubst φ ⟨k, hkN⟩ true) x ≠ sval (rsubst φ ⟨k, hkN⟩ true) y := by
          obtain ⟨a, b, hab⟩ := G_nonconst n (k + 1) (by omega)
          refine ⟨fun i => a (del n k hk i), fun i => b (del n k hk i), ?_⟩
          have e1 : sval (rsubst φ ⟨k, hkN⟩ true) (fun i => a (del n k hk i))
              = G n (k + 1) a := by
            rw [rsubst_eval, hev]; exact G_del_true n k hk a
          have e2 : sval (rsubst φ ⟨k, hkN⟩ true) (fun i => b (del n k hk i))
              = G n (k + 1) b := by
            rw [rsubst_eval, hev]; exact G_del_true n k hk b
          rw [e1, e2]; exact hab
        cases hrs : rsubst φ ⟨k, hkN⟩ true with
        | inl b0 =>
          exfalso
          obtain ⟨x, y, hxy⟩ := hnc
          rw [hrs] at hxy
          simp only [sval] at hxy
          exact hxy rfl
        | inr ψ =>
          have hψle : ψ.leaves + 2 ≤ s := by
            have h2 := hv
            rw [hrs] at h2
            simp only [sleaves] at h2
            omega
          have hev' : ∀ y : Fin n → Bool, (relabel (del n k hk) ψ).eval y = G n (k + 1) y := by
            intro y
            rw [relabel_eval]
            have h1 : ψ.eval (fun i => y (del n k hk i))
                = sval (rsubst φ ⟨k, hkN⟩ true) (fun i => y (del n k hk i)) := by
              rw [hrs]; rfl
            rw [h1, rsubst_eval, hev]
            exact G_del_true n k hk y
          have hinst := ih (d - 2) (by omega) (by omega) (k + 1) n
            (relabel (del n k hk) ψ).leaves (by omega) ⟨_, le_rfl, hev'⟩
          have hle2 : (relabel (del n k hk) ψ).leaves + 2 ≤ s := by
            rw [relabel_leaves]; omega
          have hdiv : d / 2 ≤ (d - 2) / 2 + 1 := by omega
          omega

/-! ## The upper bound: three leaves per two edges -/

theorem ext_shift (n : ℕ) (x : Fin (n + 2) → Bool) (j : ℕ) :
    ext (fun i : Fin n => x ⟨i.val + 2, by omega⟩) j = (decide (j < n) && ext x (j + 2)) := by
  by_cases hj : j < n
  · have h2 : j + 2 < n + 2 := by omega
    simp [ext, hj, h2]
  · simp [ext, hj]

theorem ext_shift_iff (n : ℕ) (x : Fin (n + 2) → Bool) (j : ℕ) :
    ext (fun i : Fin n => x ⟨i.val + 2, by omega⟩) j = true ↔
      (j < n ∧ ext x (j + 2) = true) := by
  rw [ext_shift, Bool.and_eq_true, decide_eq_true_eq]

/-- Peeling the first two edges off the path: `f (n + 2) = f n OR (x 1 AND (x 0 OR x 2))`. -/
theorem G_succ (n : ℕ) (hn : 2 ≤ n) (x : Fin (n + 2) → Bool) :
    G (n + 2) 0 x = (G n 0 (fun i : Fin n => x ⟨i.val + 2, by omega⟩) ||
      (x ⟨1, by omega⟩ && (x ⟨0, by omega⟩ || x ⟨2, by omega⟩))) := by
  have hL : (G (n + 2) 0 x = true) ↔
      (∃ i, i < n + 2 ∧ ext x i = true ∧ ext x (i + 1) = true) := by
    rw [G_iff]
    constructor
    · rintro (⟨i, hi, _⟩ | ⟨i, hi, hx, hy⟩)
      · omega
      · exact ⟨i, ext_lt hx, hx, hy⟩
    · rintro ⟨i, hi, hx, hy⟩
      exact Or.inr ⟨i, Nat.zero_le _, hx, hy⟩
  have hR : (G n 0 (fun i : Fin n => x ⟨i.val + 2, by omega⟩) = true) ↔
      (∃ i, i < n ∧ ext x (i + 2) = true ∧ ext x (i + 1 + 2) = true) := by
    rw [G_iff]
    constructor
    · rintro (⟨i, hi, _⟩ | ⟨i, hi, hx, hy⟩)
      · omega
      · obtain ⟨h1, h2⟩ := (ext_shift_iff n x i).1 hx
        obtain ⟨h3, h4⟩ := (ext_shift_iff n x (i + 1)).1 hy
        exact ⟨i, h1, h2, h4⟩
    · rintro ⟨i, hi, hx, hy⟩
      refine Or.inr ⟨i, Nat.zero_le _, ?_, ?_⟩
      · exact (ext_shift_iff n x i).2 ⟨hi, hx⟩
      · refine (ext_shift_iff n x (i + 1)).2 ⟨?_, hy⟩
        have := ext_lt hy
        omega
  rw [Bool.eq_iff_iff, Bool.or_eq_true, Bool.and_eq_true, Bool.or_eq_true, hL, hR]
  constructor
  · rintro ⟨i, hi, hx, hy⟩
    rcases Nat.lt_or_ge i 2 with h2 | h2
    · have hcase : i = 0 ∨ i = 1 := by omega
      rcases hcase with h0 | h1
      · right
        rw [h0] at hx hy
        have hx0 : x ⟨0, by omega⟩ = true := ext_of_val x ⟨0, by omega⟩ (by simpa using hx)
        have hy1 : x ⟨1, by omega⟩ = true := ext_of_val x ⟨1, by omega⟩ (by simpa using hy)
        exact ⟨hy1, Or.inl hx0⟩
      · right
        rw [h1] at hx hy
        have hx1 : x ⟨1, by omega⟩ = true := ext_of_val x ⟨1, by omega⟩ (by simpa using hx)
        have hy2 : x ⟨2, by omega⟩ = true := ext_of_val x ⟨2, by omega⟩ (by simpa using hy)
        exact ⟨hx1, Or.inr hy2⟩
    · left
      refine ⟨i - 2, by omega, ?_, ?_⟩
      · rwa [show i - 2 + 2 = i by omega]
      · rwa [show i - 2 + 1 + 2 = i + 1 by omega]
  · rintro (⟨i, hi, hx, hy⟩ | ⟨h1, h0 | h2⟩)
    · refine ⟨i + 2, by omega, hx, ?_⟩
      rw [show i + 2 + 1 = i + 1 + 2 by omega]
      exact hy
    · have h0' : ext x 0 = true := val_of_ext x ⟨0, by omega⟩ h0
      have h1' : ext x 1 = true := val_of_ext x ⟨1, by omega⟩ h1
      exact ⟨0, by omega, h0', by simpa using h1'⟩
    · have h1' : ext x 1 = true := val_of_ext x ⟨1, by omega⟩ h1
      have h2' : ext x 2 = true := val_of_ext x ⟨2, by omega⟩ h2
      exact ⟨1, by omega, h1', by simpa using h2'⟩


theorem G_path (n : ℕ) :
    G n 0 = fun x : Fin n → Bool =>
      decide (∃ i j : Fin n, i.val + 1 = j.val ∧ x i = true ∧ x j = true) := by
  funext x
  simp [G]

theorem leaf_up_step (m b : ℕ) (h : b ≤ (m + 2) + (m + 2) / 2 - 1) :
    b + 3 ≤ (m + 4) + (m + 4) / 2 - 1 := by omega

theorem G_up : ∀ n : ℕ, 2 ≤ n → ∃ φ : DMFormula n, φ.leaves ≤ n + n / 2 - 1 ∧
    ∀ x : Fin n → Bool, φ.eval x = G n 0 x := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    by_cases h2 : n = 2
    · subst h2
      refine ⟨DMFormula.and (DMFormula.lit (⟨0, by omega⟩ : Fin 2) true)
        (DMFormula.lit ⟨1, by omega⟩ true), ?_, ?_⟩
      · show 1 + 1 ≤ 2 + 2 / 2 - 1
        omega
      · show ∀ x : Fin 2 → Bool,
          (DMFormula.and (DMFormula.lit (⟨0, by omega⟩ : Fin 2) true)
            (DMFormula.lit ⟨1, by omega⟩ true)).eval x = G 2 0 x
        decide
    by_cases h3 : n = 3
    · subst h3
      refine ⟨DMFormula.and (DMFormula.lit (⟨1, by omega⟩ : Fin 3) true)
        (DMFormula.or (DMFormula.lit ⟨0, by omega⟩ true)
          (DMFormula.lit ⟨2, by omega⟩ true)), ?_, ?_⟩
      · show 1 + (1 + 1) ≤ 3 + 3 / 2 - 1
        omega
      · show ∀ x : Fin 3 → Bool,
          (DMFormula.and (DMFormula.lit (⟨1, by omega⟩ : Fin 3) true)
            (DMFormula.or (DMFormula.lit ⟨0, by omega⟩ true)
              (DMFormula.lit ⟨2, by omega⟩ true))).eval x = G 3 0 x
        decide
    · obtain ⟨m, hm⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
      subst hm
      obtain ⟨φ, hle, hev⟩ := ih (m + 2) (by omega) (by omega)
      refine ⟨DMFormula.or (relabel (fun i : Fin (m + 2) => ⟨i.val + 2, by omega⟩) φ)
        (DMFormula.and (DMFormula.lit (⟨1, by omega⟩ : Fin (m + 4)) true)
          (DMFormula.or (DMFormula.lit ⟨0, by omega⟩ true)
            (DMFormula.lit ⟨2, by omega⟩ true))), ?_, ?_⟩
      · show (relabel (fun i : Fin (m + 2) => ⟨i.val + 2, by omega⟩) φ).leaves
          + (1 + (1 + 1)) ≤ (m + 4) + (m + 4) / 2 - 1
        rw [relabel_leaves]
        exact leaf_up_step m φ.leaves hle
      · intro x
        have e : (DMFormula.or (relabel (fun i : Fin (m + 2) => ⟨i.val + 2, by omega⟩) φ)
            (DMFormula.and (DMFormula.lit (⟨1, by omega⟩ : Fin (m + 4)) true)
              (DMFormula.or (DMFormula.lit ⟨0, by omega⟩ true)
                (DMFormula.lit ⟨2, by omega⟩ true)))).eval x
            = ((relabel (fun i : Fin (m + 2) => ⟨i.val + 2, by omega⟩) φ).eval x
              || (x ⟨1, by omega⟩ && (x ⟨0, by omega⟩ || x ⟨2, by omega⟩))) := rfl
        rw [e, relabel_eval]
        have h1 : φ.eval (fun i : Fin (m + 2) => x ⟨i.val + 2, by omega⟩)
            = G (m + 2) 0 (fun i : Fin (m + 2) => x ⟨i.val + 2, by omega⟩) := hev _
        rw [h1]
        exact (G_succ (m + 2) (by omega) x).symm


end PEqualNP.Outside.L_meta_121_aux

theorem PEqualNP.Outside.L_meta_121 :
    ∀ n s : ℕ, 2 ≤ n → (PEqualNP.MetaComplexity.HasLeafSize n (fun x : Fin n → Bool => decide (∃ i j : Fin n, i.val + 1 = j.val ∧ x i = true ∧ x j = true)) s ↔ n + n / 2 ≤ s + 1) := by
  intro n s hn
  rw [← PEqualNP.Outside.L_meta_121_aux.G_path n]
  constructor
  · intro h
    exact PEqualNP.Outside.L_meta_121_aux.G_lower n hn 0 n s (by omega) h
  · intro h
    obtain ⟨φ, hle, hev⟩ := PEqualNP.Outside.L_meta_121_aux.G_up n hn
    exact ⟨φ, by omega, hev⟩
