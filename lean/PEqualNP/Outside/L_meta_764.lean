import Mathlib
import PEqualNP.Defs

/-!
# L-meta-764: a triangle plus a disjoint edge has circuits with `s` gates exactly when `6 ≤ s`

The recorded function is `(x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 2 && x 4)`: the edge
function of the triangle `2-3-4` with a rigid AND term on the two fresh inputs `x 0`, `x 1` ORed
over it.  Write it as `(x 0 && x 1) || g (x 2, x 3, x 4)` with `g` the triangle's edge function.

* Upper bound: `g` has a four-gate circuit (`L-meta-100`, `maj3_size`); the two gates of the AND
  term and its OR (`L-meta-153`, `rigid_up`) give `f` a six-gate circuit at `6 ≤ s`.
* Lower bound: `L-meta-153`'s `rigid_down` says a circuit for `f` with `s + 2` gates gives one for
  `g` with `s` gates — the rigid AND term costs at least two gates; `L-meta-100` says `g` needs
  four.  So five gates are impossible: `HasCircuitSize 5 f s` with `s ≤ 5` would give
  `HasCircuitSize 3 g 3`, hence `4 ≤ 3`.

`|E| + tau - 1 = 4 + 3 - 1 = 6` for that graph, so six is also the cover bound, reached here.

`Outside` files may import only `Mathlib` and `PEqualNP.Defs`, so Part 1 is the merged proofs of
`L-meta-100` and `L-meta-153` (`ExactMaj3`/`maj3_size` and `RigidAnd`/`rigid_and` with the chain
`TableSearch`, `Elim`, `Parity`, `PermInputs`, `Forest`, `PadOr`, `Shannon`, `Support` they rest
on) ported inline, with every namespace moved under `PEqualNP.Outside.L_meta_764_aux`.  Part 2 is
the instance data, Part 3 the recorded statement.
-/

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-! ## Part 1 — `L-meta-100` and `L-meta-153` with their chain, ported inline -/

/-! ---- ported from PEqualNP.MetaComplexity.Helpers.Shannon ---- -/

/-!
# Shannon expansion as a straight-line program

Helper for `L-meta-001`. The construction is made at an arbitrary wire offset: the function
reads the first `k` wires of a wire list of length `m`, and the new gates are appended after
wire `m - 1`. So two subcircuits are put one after the other without renumbering any gate.
-/

namespace PEqualNP.Outside.L_meta_764_aux

open PEqualNP.CircuitLowerBounds

/-- Run gates on a wire list: the fold inside `Circuit.wires`. -/
def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

/-- The four gates that close one Shannon expansion step, appended to the wires `v`: with
`a = v[k]`, `p = v[o0]`, `q = v[o1]` they produce `(¬a ∧ p) ∨ (a ∧ q)` on the last wire. -/
theorem final_gates (v : List Bool) (k o0 o1 : ℕ) (hk : k < v.length) (h0 : o0 < v.length)
    (h1 : o1 < v.length) :
    (wiresFrom [⟨GateOp.not, [k]⟩, ⟨GateOp.and, [v.length, o0]⟩, ⟨GateOp.and, [k, o1]⟩,
      ⟨GateOp.or, [v.length + 1, v.length + 2]⟩] v).getD (v.length + 3) false
      = ((!(v.getD k false) && v.getD o0 false) || (v.getD k false && v.getD o1 false)) := by
  have A : ∀ (t : List Bool) (i : ℕ), i < v.length → (v ++ t)[i]?.getD false = v[i]?.getD false := by
    intro t i h; rw [List.getElem?_append_left h]
  simp [wiresFrom, GateOp.eval, A _ _ hk, A _ _ h0, A _ _ h1]

/-- The allowed gates: AND, OR, NOT reading at most two wires. -/
def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem shannon (k : ℕ) : ∀ (f : (Fin k → Bool) → Bool) (m : ℕ), k ≤ m →
    ∃ (gs : List Gate) (out : ℕ), (∀ g ∈ gs, Ok g) ∧ gs.length + 4 ≤ 5 * 2 ^ k ∧
      out < m + gs.length ∧
      ∀ w : List Bool, w.length = m →
        (wiresFrom gs w).getD out false = f (fun i : Fin k => w.getD i false) := by
  induction k with
  | zero =>
    intro f m _
    refine ⟨[⟨if f (fun i => i.elim0) = true then GateOp.and else GateOp.or, []⟩], m, ?_, by simp,
      by simp, ?_⟩
    · intro g hg
      simp only [List.mem_singleton] at hg
      subst hg
      refine ⟨?_, by simp⟩
      by_cases h : f (fun i => i.elim0) = true <;> simp [h]
    · intro w hw
      have hf : (fun i : Fin 0 => w.getD i false) = (fun i => i.elim0) := Subsingleton.elim _ _
      rw [hf]
      by_cases h : f (fun i => i.elim0) = true <;>
        simp [wiresFrom, h, ← hw, GateOp.eval]
  | succ k ih =>
    intro f m hm
    obtain ⟨gs0, o0, ok0, len0, ho0, ev0⟩ :=
      ih (fun y => f (Fin.snoc y false)) m (by omega)
    obtain ⟨gs1, o1, ok1, len1, ho1, ev1⟩ :=
      ih (fun y => f (Fin.snoc y true)) (m + gs0.length) (by omega)
    let M := m + gs0.length + gs1.length
    refine ⟨gs0 ++ gs1 ++ [⟨GateOp.not, [k]⟩, ⟨GateOp.and, [M, o0]⟩, ⟨GateOp.and, [k, o1]⟩,
      ⟨GateOp.or, [M + 1, M + 2]⟩], M + 3, ?_, ?_, ?_, ?_⟩
    · intro g hg
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with (hg | hg) | hg | hg | hg | hg
      · exact ok0 g hg
      · exact ok1 g hg
      all_goals (subst hg; simp [Ok])
    · simp only [List.length_append, List.length_cons, List.length_nil]
      rw [pow_succ]; omega
    · simp only [List.length_append, List.length_cons, List.length_nil]; omega
    · intro w hw
      rw [wiresFrom_append, wiresFrom_append]
      set w1 := wiresFrom gs0 w with hw1
      set w2 := wiresFrom gs1 w1 with hw2
      have l1 : w1.length = m + gs0.length := by rw [hw1, length_wiresFrom, hw]
      have l2 : w2.length = M := by rw [hw2, length_wiresFrom, l1]
      have e0 : w2.getD o0 false = f (Fin.snoc (fun i : Fin k => w.getD i false) false) := by
        rw [hw2, getD_wiresFrom _ _ _ (by omega)]; exact ev0 w hw
      have e1 : w2.getD o1 false = f (Fin.snoc (fun i : Fin k => w.getD i false) true) := by
        rw [ev1 w1 l1]
        congr 2; funext i
        exact getD_wiresFrom _ _ _ (by have := i.isLt; omega)
      have ek : w2.getD k false = w.getD k false := by
        rw [hw2, getD_wiresFrom _ _ _ (by omega), hw1, getD_wiresFrom _ _ _ (by omega)]
      have hx : (fun i : Fin (k + 1) => w.getD i false)
          = Fin.snoc (fun i : Fin k => w.getD i false) (w.getD k false) := by
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
      rw [hx]
      have hk2 : k < w2.length := by omega
      have h02 : o0 < w2.length := by omega
      have h12 : o1 < w2.length := by omega
      rw [show M = w2.length from l2.symm, final_gates w2 k o0 o1 hk2 h02 h12, ek, e0, e1]
      cases w.getD k false <;> simp

end PEqualNP.Outside.L_meta_764_aux

/-! ---- ported from PEqualNP.MetaComplexity.Helpers.Support ---- -/

/-!
# Supports of wires

Helper for `L-meta-011`. Every wire gets a support: the set of inputs it can depend on, read
off the gates. Two facts: the value of a wire depends only on the inputs in its support, and
any set `W` of wires has a joint support of size at most (number of gates) + `|W|`, because a
gate of fan-in two replaces itself by at most two earlier wires.
-/

namespace PEqualNP.Outside.L_meta_764_aux

open PEqualNP.CircuitLowerBounds

variable {n : ℕ}

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

/-- The support of a gate: the union of the supports of the wires it reads. -/
def gateSupp (L : List (Finset (Fin n))) (g : Gate) : Finset (Fin n) :=
  (g.inputs.map fun a => L.getD a ∅).foldr (· ∪ ·) ∅

theorem mem_foldr_union (l : List ℕ) (F : ℕ → Finset (Fin n)) (i : Fin n) :
    i ∈ (l.map F).foldr (· ∪ ·) ∅ ↔ ∃ a ∈ l, i ∈ F a := by
  induction l with
  | nil => simp
  | cons b l ih => simp [ih]

theorem mem_gateSupp (L : List (Finset (Fin n))) (g : Gate) (i : Fin n) :
    i ∈ gateSupp L g ↔ ∃ a ∈ g.inputs, i ∈ L.getD a ∅ :=
  mem_foldr_union _ _ _

/-- The supports of all wires, starting from the supports `L` of the wires present. -/
def suppsFrom (gs : List Gate) (L : List (Finset (Fin n))) : List (Finset (Fin n)) :=
  gs.foldl (fun L g => L ++ [gateSupp L g]) L

/-- The supports of the input wires: input `i` has support `{i}`. -/
def inputSupps (n : ℕ) : List (Finset (Fin n)) := List.ofFn fun i : Fin n => {i}

/-- Wire lists `w`, `w'` (for the inputs `x`, `y`) agree on every wire whose support `x` and
`y` agree on. -/
def Agree (x y : Fin n → Bool) (L : List (Finset (Fin n))) (w w' : List Bool) : Prop :=
  L.length = w.length ∧ w.length = w'.length ∧
    ∀ j : ℕ, (∀ i ∈ L.getD j ∅, x i = y i) → w.getD j false = w'.getD j false

theorem agree_wiresFrom (x y : Fin n → Bool) (gs : List Gate) :
    ∀ (L : List (Finset (Fin n))) (w w' : List Bool), Agree x y L w w' →
      Agree x y (suppsFrom gs L) (wiresFrom gs w) (wiresFrom gs w') := by
  induction gs with
  | nil => intro L w w' h; exact h
  | cons g gs ih =>
    intro L w w' h
    obtain ⟨h1, h2, h3⟩ := h
    apply ih (L ++ [gateSupp L g])
      (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
    refine ⟨by simp [h1], by simp [h2], ?_⟩
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq] at hj
      rw [h1, getD_snoc_eq, h2, getD_snoc_eq]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact h3 a (fun i hi => hj i ((mem_gateSupp L g i).2 ⟨a, ha, hi⟩))
    · rw [getD_snoc_ne _ _ _ _ hjl] at hj
      rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
      exact h3 j hj

theorem agree_inputs (x y : Fin n → Bool) :
    Agree x y (inputSupps n) (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp [inputSupps], by simp, ?_⟩
  intro j hj
  by_cases hjn : j < n
  · have hx : x ⟨j, hjn⟩ = y ⟨j, hjn⟩ := hj _ (by simp [inputSupps, hjn])
    simp [hjn, hx]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

/-- Any set `W` of wires has a joint support of size at most `t + |W|`. -/
def Cnt (t : ℕ) (L : List (Finset (Fin n))) : Prop :=
  ∀ W : Finset ℕ, (W.biUnion fun j => L.getD j ∅).card ≤ t + W.card

theorem cnt_inputs : Cnt 0 (inputSupps n) := by
  intro W
  refine le_trans Finset.card_biUnion_le ?_
  rw [zero_add, Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro j _
  by_cases hjn : j < n
  · simp [inputSupps, hjn]
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

theorem cnt_step (t : ℕ) (L : List (Finset (Fin n))) (g : Gate) (hg : g.inputs.length ≤ 2)
    (h : Cnt t L) : Cnt (t + 1) (L ++ [gateSupp L g]) := by
  intro W
  by_cases hW : L.length ∈ W
  · have hsub : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        ⊆ ((W.erase L.length ∪ g.inputs.toFinset).biUnion fun j => L.getD j ∅) := by
      intro i hi
      rw [Finset.mem_biUnion] at hi ⊢
      obtain ⟨j, hjW, hij⟩ := hi
      by_cases hjl : j = L.length
      · subst hjl
        rw [getD_snoc_eq] at hij
        obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g i).1 hij
        exact ⟨a, Finset.mem_union_right _ (List.mem_toFinset.2 ha), hia⟩
      · rw [getD_snoc_ne _ _ _ _ hjl] at hij
        exact ⟨j, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hjl, hjW⟩), hij⟩
    have hc1 : (W.erase L.length ∪ g.inputs.toFinset).card ≤ (W.card - 1) + 2 := by
      refine le_trans (Finset.card_union_le _ _) ?_
      rw [Finset.card_erase_of_mem hW]
      exact Nat.add_le_add_left (le_trans (List.toFinset_card_le _) hg) _
    have hWpos : 1 ≤ W.card := Finset.card_pos.2 ⟨_, hW⟩
    have := h (W.erase L.length ∪ g.inputs.toFinset)
    have := Finset.card_le_card hsub
    omega
  · have heq : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        = (W.biUnion fun j => L.getD j ∅) := by
      apply Finset.biUnion_congr rfl
      intro j hj
      exact getD_snoc_ne _ _ _ _ (fun e => hW (e ▸ hj))
    rw [heq]
    have := h W
    omega

theorem cnt_suppsFrom (gs : List Gate) : ∀ (t : ℕ) (L : List (Finset (Fin n))),
    (∀ g ∈ gs, Ok g) → Cnt t L → Cnt (t + gs.length) (suppsFrom gs L) := by
  induction gs with
  | nil => intro t L _ h; exact h
  | cons g gs ih =>
    intro t L hok h
    have := ih (t + 1) (L ++ [gateSupp L g]) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (cnt_step t L g (hok g List.mem_cons_self).2 h)
    rw [List.length_cons, show t + (gs.length + 1) = t + 1 + gs.length by omega]
    exact this

/-- A function that depends on each of its `n` inputs has no circuit with fewer than `n - 1`
gates. -/
theorem dep_lower (n : ℕ) (f : (Fin n → Bool) → Bool)
    (hdep : ∀ i : Fin n, ∃ x : Fin n → Bool, f (Function.update x i (!x i)) ≠ f x)
    (s : ℕ) (h : HasCircuitSize n f s) : n ≤ s + 1 := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set S := (suppsFrom C.gates (inputSupps n)).getD C.output ∅ with hS
  have hall : ∀ i : Fin n, i ∈ S := by
    intro i
    by_contra hi
    obtain ⟨x, hx⟩ := hdep i
    apply hx
    have hag := (agree_wiresFrom (Function.update x i (!x i)) x C.gates _ _ _
      (agree_inputs _ _)).2.2 C.output (by
        intro k hk
        have : k ≠ i := fun e => hi (e ▸ hk)
        simp [Function.update_of_ne this])
    rw [← hev, ← hev]
    exact hag
  have hcard : S.card = n := by
    rw [Finset.eq_univ_of_forall hall]; simp
  have hc := cnt_suppsFrom C.gates 0 (inputSupps n) ok cnt_inputs {C.output}
  simp only [Finset.singleton_biUnion, Finset.card_singleton, zero_add] at hc
  rw [← hS, hcard] at hc
  omega

end PEqualNP.Outside.L_meta_764_aux

/-! ---- ported from PEqualNP.MetaComplexity.Helpers.Elim ---- -/

/-!
# Gate elimination

Helper for `L-meta-014`. The last input of a circuit on `n + 1` inputs is fixed to `b`. One
pass over the gates gives every old wire a status: a constant, or an alias of a wire of the
new circuit on `n` inputs. A gate that reads a constant becomes a constant or an alias and is
not emitted, so if some gate reads the fixed input the new circuit is smaller. If no gate
reads it, the supports of `Support.lean` show the function does not depend on it.
-/

namespace PEqualNP.Outside.L_meta_764_aux

open PEqualNP.CircuitLowerBounds

/-- A NOT gate reads only its first wire: drop the others. -/
def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

theorem normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

/-- An allowed gate whose NOT gates read at most one wire. -/
def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

theorem normGate_nok (g : Gate) (h : Ok g) : NOk (normGate g) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := h
  rcases hop with h | h | h
  · have : op = GateOp.and := h
    subst this; exact ⟨⟨Or.inl rfl, hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.or := h
    subst this; exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.not := h
    subst this
    refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩ <;> simp [normGate] <;> omega

theorem wiresFrom_norm (gs : List Gate) : ∀ w : List Bool,
    wiresFrom (gs.map normGate) w = wiresFrom gs w := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    have s1 : wiresFrom ((g :: gs).map normGate) w = wiresFrom (gs.map normGate)
        (w ++ [(normGate g).op.eval ((normGate g).inputs.map fun i => w.getD i false)]) := rfl
    have s2 : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [s1, s2, normGate_eval, ih]

/-- The status of an old wire: a constant, or the wire `j` of the new circuit. -/
inductive Stat : Type
  | const (c : Bool)
  | wire (j : ℕ)

def Stat.val (w : List Bool) : Stat → Bool
  | Stat.const c => c
  | Stat.wire j => w.getD j false

def Stat.Valid (m : ℕ) : Stat → Prop
  | Stat.const _ => True
  | Stat.wire j => j < m

def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const true)
  | Stat.const c :: _ => (none, Stat.const (!c))
  | Stat.wire j :: _ => (some ⟨GateOp.not, [j]⟩, Stat.wire m)

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const true)
  | [Stat.const c] => (none, Stat.const c)
  | [Stat.wire j] => (none, Stat.wire j)
  | [Stat.const c, Stat.const d] => (none, Stat.const (c && d))
  | [Stat.const c, Stat.wire j] => (none, bif c then Stat.wire j else Stat.const false)
  | [Stat.wire j, Stat.const c] => (none, bif c then Stat.wire j else Stat.const false)
  | [Stat.wire j, Stat.wire k] => (some ⟨GateOp.and, [j, k]⟩, Stat.wire m)
  | _ => (none, Stat.const false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const false)
  | [Stat.const c] => (none, Stat.const c)
  | [Stat.wire j] => (none, Stat.wire j)
  | [Stat.const c, Stat.const d] => (none, Stat.const (c || d))
  | [Stat.const c, Stat.wire j] => (none, bif c then Stat.const true else Stat.wire j)
  | [Stat.wire j, Stat.const c] => (none, bif c then Stat.const true else Stat.wire j)
  | [Stat.wire j, Stat.wire k] => (some ⟨GateOp.or, [j, k]⟩, Stat.wire m)
  | _ => (none, Stat.const false)

/-- What a gate becomes, given the statuses of the wires it reads; `m` is the number of the
next new wire. The result is the gate to emit, if any, and the status of the gate's wire. -/
def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Stat.const false)

theorem simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, Ok g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; simp [Ok])
  · simp at hg
  · simp at hg

theorem simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Stat.const c ∈ ins) :
    (simplify op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

theorem simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, s.Valid w.length) :
    ((simplify op w.length ins).2).Valid (w.length + (simplify op w.length ins).1.toList.length) ∧
    ((simplify op w.length ins).2).val (wiresFrom (simplify op w.length ins).1.toList w)
      = op.eval (ins.map (Stat.val w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]

/-- One step of the pass: `acc.1` holds the statuses of the old wires, `acc.2` the new gates. -/
def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

theorem elim_getD (n k : ℕ) (d : Stat) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    k < acc.1.length → (elim n gs acc).1.getD k d = acc.1.getD k d := by
  induction gs with
  | nil => intro acc _; rfl
  | cons g gs ih =>
    intro acc hk
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, ih (elimStep n acc g) (by simp [elimStep]; omega)]
    exact getD_snoc_ne _ _ _ _ (by omega)

theorem toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

theorem elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ acc.2, Ok g) → ∀ g ∈ (elim n gs acc).2, Ok g := by
  induction gs with
  | nil => intro acc h; exact h
  | cons g gs ih =>
    intro acc h
    apply ih (elimStep n acc g)
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplify_ok _ _ _ g' (by simpa using h1)

theorem elim_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc
    have h1 := ih (elimStep n acc g)
    have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      have := toList_length_le (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1
      omega
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]; omega

/-- If the status of old wire `k` is a constant and some gate reads wire `k`, one gate is
saved. -/
theorem elim_len_lt (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, NOk g) → k < acc.1.length → (∃ c, acc.1.getD k (Stat.const false) = Stat.const c) →
    (∃ g ∈ gs, k ∈ g.inputs) → (elim n gs acc).2.length + 1 ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _ h; obtain ⟨g, hg, _⟩ := h; simp at hg
  | cons g gs ih =>
    intro acc hok hk hc hex
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]
    by_cases hkg : k ∈ g.inputs
    · obtain ⟨c, hc⟩ := hc
      have hnok := hok g List.mem_cons_self
      have hnone : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1 = none := by
        apply simplify_count
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep n acc g).2.length = acc.2.length := by
        show (acc.2 ++ (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList).length = _
        rw [hnone]; simp
      have := elim_len n gs (elimStep n acc g)
      omega
    · have hex' : ∃ g' ∈ gs, k ∈ g'.inputs := by
        obtain ⟨g', hg', hk'⟩ := hex
        rcases List.mem_cons.1 hg' with rfl | h
        · exact absurd hk' hkg
        · exact ⟨g', h, hk'⟩
      have h1 := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (by simp [elimStep]; omega)
        (by
          obtain ⟨c, hc⟩ := hc
          refine ⟨c, ?_⟩
          simp only [elimStep]
          rw [getD_snoc_ne _ _ _ _ (by omega)]; exact hc)
        hex'
      have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1
        omega
      omega

theorem Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Stat.const _, _ => trivial
  | Stat.wire _, hj => lt_of_lt_of_le hj h

theorem Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Stat.const _, _ => rfl
  | Stat.wire _, hj => List.getD_append _ _ _ _ hj

/-- The invariant of the pass, for one input `y` of the new circuit: `w` are the old wires,
and every old wire has a valid status whose value on the new wires is the old value. -/
def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (Stat.const false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Stat.const false)).val (wiresFrom acc.2 y) = w.getD i false

theorem inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      Inv n y (wiresFrom gs w) (elim n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi⟩ := h
    set w' := wiresFrom acc.2 y with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hy]
    set ins := g.inputs.map fun i => acc.1.getD i (Stat.const false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (Stat.val w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, htl⟩ := wiresFrom_prefix r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show ((acc.1 ++ [r.2]).getD i (Stat.const false)).Valid (n + (acc.2 ++ r.1.toList).length) ∧
      ((acc.1 ++ [r.2]).getD i (Stat.const false)).val (wiresFrom (acc.2 ++ r.1.toList) y) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨Stat.valid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, Stat.val_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

/-- The statuses at the start: the first `n` old wires are the new input wires, and the last
input is the constant `b`. -/
def initStats (n : ℕ) (b : Bool) : List Stat :=
  List.ofFn (fun i : Fin n => Stat.wire i) ++ [Stat.const b]

theorem inv_init (n : ℕ) (b : Bool) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y ++ [b]) (initStats n b, []) := by
  refine ⟨by simp [initStats], ?_⟩
  intro i
  have l1 : (List.ofFn (fun i : Fin n => Stat.wire i)).length = n := by simp
  have l2 : (List.ofFn y).length = n := by simp
  by_cases hin : i = n
  · subst hin
    simp only [initStats]
    rw [getD_snoc_len _ _ _ _ l1, getD_snoc_len _ _ _ _ l2]
    exact ⟨trivial, rfl⟩
  · simp only [initStats]
    rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
    by_cases hlt : i < n
    · simp [hlt, Stat.Valid, Stat.val, wiresFrom]
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      exact ⟨trivial, rfl⟩

theorem ofFn_snoc (n : ℕ) (y : Fin n → Bool) (b : Bool) :
    List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool) = List.ofFn y ++ [b] := by
  rw [List.ofFn_succ']
  simp

/-- If no gate reads wire `n`, no other wire has the last input in its support. -/
theorem supp_noread (n : ℕ) (gs : List Gate) : ∀ L : List (Finset (Fin (n + 1))),
    (∀ g ∈ gs, n ∉ g.inputs) → (∀ j : ℕ, j ≠ n → Fin.last n ∉ L.getD j ∅) →
    ∀ j : ℕ, j ≠ n → Fin.last n ∉ (suppsFrom gs L).getD j ∅ := by
  induction gs with
  | nil => intro L _ h; exact h
  | cons g gs ih =>
    intro L hno h
    apply ih (L ++ [gateSupp L g]) (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq]
      intro hmem
      obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g _).1 hmem
      exact h a (fun e => hno g List.mem_cons_self (e ▸ ha)) hia
    · rw [getD_snoc_ne _ _ _ _ hjl]; exact h j hj

theorem inputSupps_getD (m j : ℕ) (h : j < m) :
    (inputSupps m).getD j ∅ = {⟨j, h⟩} := by
  simp [inputSupps, h]

theorem inputSupps_noread (n : ℕ) : ∀ j : ℕ, j ≠ n →
    Fin.last n ∉ (inputSupps (n + 1)).getD j ∅ := by
  intro j hj
  by_cases hlt : j < n + 1
  · have e : (inputSupps (n + 1)).getD j ∅ = {⟨j, hlt⟩} := inputSupps_getD (n + 1) j hlt
    rw [e, Finset.mem_singleton]
    intro e'
    exact hj (by have := congrArg Fin.val e'; simpa using this.symm)
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

/-- Gate elimination: fix the last input of `f` to `b`. If `f` depends on that input and the
restriction is not constant, a circuit of size `s + 1` for `f` gives one of size `s` for the
restriction. -/
theorem gate_elim (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (b : Bool) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ f x)
    (hnc : ∃ y y' : Fin n → Bool, f (Fin.snoc y b) ≠ f (Fin.snoc y' b))
    (h : HasCircuitSize (n + 1) f (s + 1)) :
    HasCircuitSize n (fun y : Fin n → Bool => f (Fin.snoc y b)) s := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s + 1 := hsz
  set gs := C.gates.map normGate with hgs
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (ok g0 hg0)
  have hevg : ∀ x : Fin (n + 1) → Bool, (wiresFrom gs (List.ofFn x)).getD C.output false = f x := by
    intro x
    rw [hgs, wiresFrom_norm, ← hev x]; rfl
  set acc := elim n gs (initStats n b, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool))) acc := by
    intro y
    rw [ofFn_snoc]
    exact inv_elim n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (inv_init n b y)
  have hval : ∀ y : Fin n → Bool,
      (acc.1.getD C.output (Stat.const false)).val (wiresFrom acc.2 (List.ofFn y))
        = f (Fin.snoc y b) := by
    intro y
    rw [((hinv y).2 C.output).2, hevg]
  have hvalid : (acc.1.getD C.output (Stat.const false)).Valid (n + acc.2.length) := by
    obtain ⟨y, _, _⟩ := hnc
    exact ((hinv y).2 C.output).1
  cases hst : acc.1.getD C.output (Stat.const false) with
  | const c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]; rfl
  | wire j =>
    have hlen : acc.2.length ≤ s := by
      by_cases hread : ∃ g ∈ gs, n ∈ g.inputs
      · have := elim_len_lt n n gs (initStats n b, []) hnok (by simp [initStats])
          ⟨b, getD_snoc_len _ _ _ _ (by simp)⟩ hread
        rw [← hacc] at this
        have hl : gs.length = C.gates.length := by simp [hgs]
        simp only [List.length_nil, zero_add] at this
        omega
      · exfalso
        push Not at hread
        have hout : C.output ≠ n := by
          intro e
          rw [e, hacc, elim_getD n n _ gs _ (by simp [initStats])] at hst
          have hb : (initStats n b).getD n (Stat.const false) = Stat.const b :=
            getD_snoc_len _ _ _ _ (by simp)
          rw [show ((initStats n b, ([] : List Gate))).1 = initStats n b from rfl, hb] at hst
          cases hst
        obtain ⟨x, hx⟩ := hdep
        apply hx
        have hns := supp_noread n gs (inputSupps (n + 1)) hread (inputSupps_noread n) C.output hout
        have hag := (agree_wiresFrom (Function.update x (Fin.last n) (!x (Fin.last n))) x gs _ _ _
          (agree_inputs _ _)).2.2 C.output (by
            intro k hk
            have : k ≠ Fin.last n := fun e => hns (e ▸ hk)
            simp [Function.update_of_ne this])
        rw [← hevg, ← hevg]
        exact hag
    refine ⟨⟨acc.2, j⟩, elim_ok n gs _ (by simp), hlen, ?_⟩
    intro y
    have := hval y
    rw [hst] at this
    exact this

end PEqualNP.Outside.L_meta_764_aux

/-! ---- ported from PEqualNP.MetaComplexity.Helpers.Parity ---- -/

/-!
# Parity needs `2 (n - 1)` gates

Helper for `L-meta-020`. The pass of `Elim.lean` fixes the last input of a circuit to a
constant `b`. Here it is shown to save two gates for a suitable `b`, when the function depends
on the last input and both restrictions are non-constant. Either two gates read the fixed
input, or the only gate reading it becomes a constant for a suitable `b` and a later gate
reads that constant, or the output does not depend on the last input. Parity and its
complement satisfy the hypotheses, and their restrictions are again parity or its complement.
-/

namespace PEqualNP.Outside.L_meta_764_aux

open PEqualNP.CircuitLowerBounds

/-! ## The pass, cut at one gate -/

theorem elim_cons (n : ℕ) (g : Gate) (gs : List Gate) (acc : List Stat × List Gate) :
    elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl

theorem elim_append (n : ℕ) (pre post : List Gate) (acc : List Stat × List Gate) :
    elim n (pre ++ post) acc = elim n post (elim n pre acc) := by
  simp [elim, List.foldl_append]

theorem elim_fst_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).1.length = acc.1.length + gs.length := by
  induction gs with
  | nil => intro acc; rfl
  | cons g gs ih =>
    intro acc
    rw [elim_cons, ih]
    simp only [elimStep, List.length_append, List.length_cons, List.length_nil]
    omega

theorem initStats_last (n : ℕ) (b : Bool) :
    (initStats n b).getD n (Stat.const false) = Stat.const b :=
  getD_snoc_len _ _ _ _ (by simp)

/-- A normalized allowed gate that reads a constant `b`, where `b` is `false` for an AND gate
and `true` for an OR gate, becomes a constant. -/
theorem simplify_const (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (b : Bool)
    (hand : op = GateOp.and → b = false) (hor : op = GateOp.or → b = true)
    (hc : Stat.const b ∈ ins) : ∃ c, (simplify op m ins).2 = Stat.const c := by
  rcases hop with rfl | rfl | rfl
  · have := hand rfl
    subst this
    rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
      simp_all [simplify, simpAnd]
  · have := hor rfl
    subst this
    rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨d, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

/-- A normalized allowed gate that reads a wire of constant status emits no gate. -/
theorem elimStep_none (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (c : Bool) (hc : acc.1.getD k (Stat.const false) = Stat.const c) :
    (elimStep n acc g).2.length = acc.2.length := by
  have hnone : (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1 = none := by
    apply simplify_count
    · exact hg.1.1
    · simpa using hg.1.2
    · intro h; simpa using hg.2 h
    · exact ⟨c, List.mem_map.2 ⟨k, hk, hc⟩⟩
  show (acc.2 ++ (simplify g.op (n + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList).length = _
  rw [hnone]; simp

/-- The value to give the fixed input so that a gate reading it becomes a constant. -/
def fixBit (g : Gate) : Bool :=
  match g.op with
  | GateOp.or => true
  | _ => false

theorem elimStep_const (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (hc : acc.1.getD k (Stat.const false) = Stat.const (fixBit g)) :
    ∃ c, (elimStep n acc g).1.getD acc.1.length (Stat.const false) = Stat.const c := by
  have e : (elimStep n acc g).1.getD acc.1.length (Stat.const false)
      = (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Stat.const false))).2 := getD_snoc_eq _ _ _
  rw [e]
  apply simplify_const _ _ _ hg.1.1 (by simpa using hg.1.2) (fun h => by simpa using hg.2 h)
    (fixBit g)
  · intro h; simp [fixBit, h]
  · intro h; simp [fixBit, h]
  · exact List.mem_map.2 ⟨k, hk, hc⟩

/-! ## Supports -/

theorem suppsFrom_append {n : ℕ} (pre post : List Gate) (L : List (Finset (Fin n))) :
    suppsFrom (pre ++ post) L = suppsFrom post (suppsFrom pre L) := by
  simp [suppsFrom, List.foldl_append]

theorem length_suppsFrom {n : ℕ} (gs : List Gate) : ∀ L : List (Finset (Fin n)),
    (suppsFrom gs L).length = L.length + gs.length := by
  induction gs with
  | nil => intro L; rfl
  | cons g gs ih =>
    intro L
    have h : suppsFrom (g :: gs) L = suppsFrom gs (L ++ [gateSupp L g]) := rfl
    rw [h, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

/-- If no gate reads a wire of the set `D`, no wire outside `D` gets the last input in its
support. -/
theorem supp_noreadD (n : ℕ) (D : ℕ → Prop) (gs : List Gate) :
    ∀ L : List (Finset (Fin (n + 1))),
    (∀ g ∈ gs, ∀ a ∈ g.inputs, ¬ D a) → (∀ j : ℕ, ¬ D j → Fin.last n ∉ L.getD j ∅) →
    ∀ j : ℕ, ¬ D j → Fin.last n ∉ (suppsFrom gs L).getD j ∅ := by
  induction gs with
  | nil => intro L _ h; exact h
  | cons g gs ih =>
    intro L hno h
    apply ih (L ++ [gateSupp L g]) (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq]
      intro hmem
      obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g _).1 hmem
      exact h a (hno g List.mem_cons_self a ha) hia
    · rw [getD_snoc_ne _ _ _ _ hjl]; exact h j hj

/-! ## Two gates saved -/

/-- If the output wire has the last input in its support and its status is never a constant,
then for some value of the last input the pass emits two gates fewer than it reads. -/
theorem two_saved (n : ℕ) (gs : List Gate) (hnok : ∀ g ∈ gs, NOk g) (o : ℕ)
    (hdep : Fin.last n ∈ (suppsFrom gs (inputSupps (n + 1))).getD o ∅)
    (hout : ∀ b c, (elim n gs (initStats n b, [])).1.getD o (Stat.const false) ≠ Stat.const c) :
    ∃ b, (elim n gs (initStats n b, [])).2.length + 2 ≤ gs.length := by
  have hon : o ≠ n := by
    intro e
    apply hout false false
    rw [e, elim_getD n n _ gs _ (by simp [initStats])]
    exact initStats_last n false
  by_cases hread : ∃ g ∈ gs, n ∈ g.inputs
  swap
  · exfalso
    push Not at hread
    exact supp_noread n gs (inputSupps (n + 1)) hread (inputSupps_noread n) o hon hdep
  obtain ⟨g, hg, hng⟩ := hread
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem hg
  have hgn : NOk g := hnok g hg
  have hpren : ∀ g' ∈ pre, NOk g' := fun g' h => hnok g' (List.mem_append_left _ h)
  have hpostn : ∀ g' ∈ post, NOk g' :=
    fun g' h => hnok g' (List.mem_append_right _ (List.mem_cons_of_mem _ h))
  have hsplit : ∀ b, elim n (pre ++ g :: post) (initStats n b, [])
      = elim n post (elimStep n (elim n pre (initStats n b, [])) g) :=
    fun b => by rw [elim_append, elim_cons]
  have hAn : ∀ b, (elim n pre (initStats n b, [])).1.getD n (Stat.const false) = Stat.const b := by
    intro b
    rw [elim_getD n n _ pre _ (by simp [initStats])]
    exact initStats_last n b
  have hAl : ∀ b, (elim n pre (initStats n b, [])).1.length = n + 1 + pre.length := by
    intro b
    rw [elim_fst_len]
    simp [initStats]
  have hA2 : ∀ b, (elim n pre (initStats n b, [])).2.length ≤ 0 + pre.length :=
    fun b => elim_len n pre (initStats n b, [])
  have hB2 := fun b => elimStep_none n (elim n pre (initStats n b, [])) g hgn n hng b (hAn b)
  have hBl : ∀ b, (elimStep n (elim n pre (initStats n b, [])) g).1.length
      = n + 1 + pre.length + 1 := by
    intro b
    simp [elimStep, hAl b]
  have hBn : ∀ b, (elimStep n (elim n pre (initStats n b, [])) g).1.getD n (Stat.const false)
      = Stat.const b := by
    intro b
    show ((elim n pre (initStats n b, [])).1 ++ [_]).getD n _ = _
    rw [getD_snoc_ne _ _ _ _ (by rw [hAl b]; omega)]
    exact hAn b
  have hF := fun b => elim_len n post (elimStep n (elim n pre (initStats n b, [])) g)
  have hlen : (pre ++ g :: post).length = pre.length + post.length + 1 := by
    simp only [List.length_append, List.length_cons]; omega
  by_cases h1 : ∃ g' ∈ pre, n ∈ g'.inputs
  · refine ⟨false, ?_⟩
    have a1 : (elim n pre (initStats n false, [])).2.length + 1 ≤ 0 + pre.length :=
      elim_len_lt n n pre (initStats n false, []) hpren (by simp [initStats])
        ⟨false, initStats_last n false⟩ h1
    have := hF false
    have := hB2 false
    rw [hsplit, hlen]
    omega
  by_cases h2 : ∃ g' ∈ post, n ∈ g'.inputs
  · refine ⟨false, ?_⟩
    have a1 := elim_len_lt n n post (elimStep n (elim n pre (initStats n false, [])) g) hpostn
      (by rw [hBl]; omega) ⟨false, hBn false⟩ h2
    have := hA2 false
    have := hB2 false
    rw [hsplit, hlen]
    omega
  obtain ⟨c, hc⟩ := elimStep_const n (elim n pre (initStats n (fixBit g), [])) g hgn n hng
    (hAn (fixBit g))
  rw [hAl (fixBit g)] at hc
  refine ⟨fixBit g, ?_⟩
  by_cases h3 : ∃ g' ∈ post, (n + 1 + pre.length) ∈ g'.inputs
  · have a1 := elim_len_lt n (n + 1 + pre.length) post
      (elimStep n (elim n pre (initStats n (fixBit g), [])) g) hpostn
      (by rw [hBl]; omega) ⟨c, hc⟩ h3
    have := hA2 (fixBit g)
    have := hB2 (fixBit g)
    rw [hsplit, hlen]
    omega
  · exfalso
    have hom : o ≠ n + 1 + pre.length := by
      intro e
      apply hout (fixBit g) c
      rw [hsplit, e, elim_getD n _ _ post _ (by rw [hBl]; omega)]
      exact hc
    push Not at h1 h2 h3
    have hs : suppsFrom (pre ++ g :: post) (inputSupps (n + 1))
        = suppsFrom post (suppsFrom pre (inputSupps (n + 1))
          ++ [gateSupp (suppsFrom pre (inputSupps (n + 1))) g]) := by
      rw [suppsFrom_append]; rfl
    rw [hs] at hdep
    have hL := supp_noread n pre (inputSupps (n + 1)) h1 (inputSupps_noread n)
    have hLl : (suppsFrom pre (inputSupps (n + 1))).length = n + 1 + pre.length := by
      rw [length_suppsFrom]
      simp [inputSupps]
    refine supp_noreadD n (fun j => j = n ∨ j = n + 1 + pre.length) post _ ?_ ?_ o
      (by simp [hon, hom]) hdep
    · intro g' hg' a ha hD
      rcases hD with rfl | rfl
      · exact h2 g' hg' ha
      · exact h3 g' hg' ha
    · intro j hj
      have hj' : j ≠ n ∧ j ≠ n + 1 + pre.length := by
        constructor
        · exact fun e => hj (Or.inl e)
        · exact fun e => hj (Or.inr e)
      rw [getD_snoc_ne _ _ _ _ (by rw [hLl]; exact hj'.2)]
      exact hL j hj'.1

/-- Gate elimination saving two gates: if `f` depends on its last input and stays non-constant
whichever value that input is fixed to, then for some value `b` the restriction has a circuit
with two gates fewer. -/
theorem gate_elim_two (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ f x)
    (hnc : ∀ b : Bool, ∃ y y' : Fin n → Bool, f (Fin.snoc y b) ≠ f (Fin.snoc y' b))
    (h : HasCircuitSize (n + 1) f s) :
    ∃ (b : Bool) (s' : ℕ), s' + 2 ≤ s ∧
      HasCircuitSize n (fun y : Fin n → Bool => f (Fin.snoc y b)) s' := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set gs := C.gates.map normGate with hgs
  have hl : gs.length = C.gates.length := by simp [hgs]
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (ok g0 hg0)
  have hevg : ∀ x : Fin (n + 1) → Bool, (wiresFrom gs (List.ofFn x)).getD C.output false = f x := by
    intro x
    rw [hgs, wiresFrom_norm, ← hev x]; rfl
  have hinv : ∀ (b : Bool) (y : Fin n → Bool),
      Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool)))
        (elim n gs (initStats n b, [])) := by
    intro b y
    rw [ofFn_snoc]
    exact inv_elim n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (inv_init n b y)
  have hval : ∀ (b : Bool) (y : Fin n → Bool),
      ((elim n gs (initStats n b, [])).1.getD C.output (Stat.const false)).val
        (wiresFrom (elim n gs (initStats n b, [])).2 (List.ofFn y)) = f (Fin.snoc y b) := by
    intro b y
    rw [((hinv b y).2 C.output).2, hevg]
  have hout : ∀ b c,
      (elim n gs (initStats n b, [])).1.getD C.output (Stat.const false) ≠ Stat.const c := by
    intro b c hst
    obtain ⟨y, y', hne⟩ := hnc b
    apply hne
    rw [← hval b y, ← hval b y', hst]; rfl
  have hsupp : Fin.last n ∈ (suppsFrom gs (inputSupps (n + 1))).getD C.output ∅ := by
    by_contra hns
    obtain ⟨x, hx⟩ := hdep
    apply hx
    have hag := (agree_wiresFrom (Function.update x (Fin.last n) (!x (Fin.last n))) x gs _ _ _
      (agree_inputs _ _)).2.2 C.output (by
        intro k hk
        have : k ≠ Fin.last n := fun e => hns (e ▸ hk)
        simp [Function.update_of_ne this])
    rw [← hevg, ← hevg]
    exact hag
  obtain ⟨b, hb⟩ := two_saved n gs hnok C.output hsupp hout
  cases hst : (elim n gs (initStats n b, [])).1.getD C.output (Stat.const false) with
  | const c => exact absurd hst (hout b c)
  | wire j =>
    refine ⟨b, (elim n gs (initStats n b, [])).2.length, by omega,
      ⟨(elim n gs (initStats n b, [])).2, j⟩, elim_ok n gs _ (by simp), le_refl _, ?_⟩
    intro y
    have := hval b y
    rw [hst] at this
    exact this

/-! ## Parity -/

/-- Parity of `n` bits: the number of true bits is odd. -/
def par (n : ℕ) (x : Fin n → Bool) : Bool :=
  decide ((Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1)

theorem par_snoc (n : ℕ) (y : Fin n → Bool) (b : Bool) :
    par (n + 1) (Fin.snoc y b) = xor (par n y) b := by
  unfold par
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  generalize (∑ i : Fin n, if y i = true then 1 else 0) = S
  have h := Nat.mod_two_eq_zero_or_one S
  cases b <;> rcases h with h | h <;> simp [Nat.add_mod, h]

/-- Parity or its complement on `n + 1` inputs needs `2 n` gates. -/
theorem par_lower : ∀ (n : ℕ) (c : Bool) (s : ℕ),
    HasCircuitSize (n + 1) (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) c) s →
      2 * n ≤ s := by
  intro n
  induction n with
  | zero => intro c s _; omega
  | succ n ih =>
    intro c s h
    have hdep : ∃ x : Fin (n + 1 + 1) → Bool,
        (fun x : Fin (n + 1 + 1) → Bool => xor (par (n + 1 + 1) x) c)
          (Function.update x (Fin.last (n + 1)) (!x (Fin.last (n + 1))))
        ≠ (fun x : Fin (n + 1 + 1) → Bool => xor (par (n + 1 + 1) x) c) x := by
      refine ⟨Fin.snoc (fun _ => false) false, ?_⟩
      simp only [Fin.snoc_last, Fin.update_snoc_last, par_snoc]
      simp
    have hnc : ∀ b : Bool, ∃ y y' : Fin (n + 1) → Bool,
        (fun x : Fin (n + 1 + 1) → Bool => xor (par (n + 1 + 1) x) c) (Fin.snoc y b)
        ≠ (fun x : Fin (n + 1 + 1) → Bool => xor (par (n + 1 + 1) x) c) (Fin.snoc y' b) := by
      intro b
      refine ⟨Fin.snoc (fun _ => false) false, Fin.snoc (fun _ => false) true, ?_⟩
      simp only [par_snoc]
      simp
    obtain ⟨b, s', hs, h'⟩ := gate_elim_two (n + 1) _ s hdep hnc h
    have e : (fun y : Fin (n + 1) → Bool =>
          (fun x : Fin (n + 1 + 1) → Bool => xor (par (n + 1 + 1) x) c) (Fin.snoc y b))
        = fun y : Fin (n + 1) → Bool => xor (par (n + 1) y) (xor b c) := by
      funext y
      show xor (par (n + 1 + 1) (Fin.snoc y b)) c = _
      rw [par_snoc]
      cases par (n + 1) y <;> cases b <;> cases c <;> rfl
    rw [e] at h'
    have := ih _ _ h'
    omega

/-- Parity of `n` inputs needs at least `2 (n - 1)` gates. -/
theorem parity_lower : ∀ (n s : ℕ),
    HasCircuitSize n (fun x : Fin n → Bool =>
      decide ((Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1)) s →
    2 * (n - 1) ≤ s := by
  intro n s h
  cases n with
  | zero => omega
  | succ n =>
    have e : (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) false)
        = fun x : Fin (n + 1) → Bool =>
          decide ((Finset.univ.filter fun i : Fin (n + 1) => x i = true).card % 2 = 1) := by
      funext x
      simp [par]
    have h' : HasCircuitSize (n + 1)
        (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) false) s := by
      rw [e]; exact h
    have := par_lower n false s h'
    omega

end PEqualNP.Outside.L_meta_764_aux

/-! ---- ported from PEqualNP.MetaComplexity.Helpers.PermInputs ---- -/

/-!
# Relabelling the inputs of a circuit, and fixing many inputs with two-gate savings

Helper module (proofs only, no statement may use it).

* `relabel_size`: if `h` on `n` inputs has a circuit with at most `s` gates, then for every map
  `π : Fin n → Fin m` the function `x ↦ h (x ∘ π)` on `m` inputs has one too. The input wires
  of the circuit are renamed along `π` and the gate wires are shifted by `m - n`; a wire that
  does not exist stays one that does not exist, so every wire keeps its value.
* `dep_lower_set`: a function that depends on every input of a set `T` has no circuit with
  fewer than `|T| - 1` gates (L-meta-011 for a set of inputs).
* `gate_elim_at`: the two-gate elimination `gate_elim_two` at any input position, the arity
  kept: the restriction is `x ↦ f (update x p b)`.
* `fix_many`: fixing the inputs of a list `L` one at a time, each saving two gates, then the
  inputs of `T` all matter: at least `|T| + 2 |L| - 1` gates.
-/

namespace PEqualNP.Outside.L_meta_764_aux.PermInputs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- The renaming of wires: input wire `w < n` goes to `π w`, gate wire `w ≥ n` to
`w - n + m`. -/
def wmap (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
  if h : w < n then (π ⟨w, h⟩ : ℕ) else w - n + m

/-- A gate with its wires renamed. -/
def relGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wmap n m π)⟩

/-- A circuit with its wires renamed. -/
def relabel (n m : ℕ) (π : Fin n → Fin m) (C : Circuit) : Circuit :=
  ⟨C.gates.map (relGate n m π), wmap n m π C.output⟩

/-- One gate evaluated on a wire list. -/
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

/-- The invariant: the wire lists match along the renaming. -/
def Rel (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) : Prop :=
  n ≤ W.length ∧ W'.length + n = W.length + m ∧
    ∀ w : ℕ, W'.getD (wmap n m π w) false = W.getD w false

theorem rel_step (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) (g : Gate)
    (h : Rel n m π W W') : Rel n m π (step W g) (step W' (relGate n m π g)) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hv : (relGate n m π g).op.eval
      ((relGate n m π g).inputs.map fun i => W'.getD i false)
      = g.op.eval (g.inputs.map fun i => W.getD i false) := by
    simp only [relGate, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a _
    exact h3 a
  refine ⟨by simp [step]; omega, by simp [step]; omega, ?_⟩
  intro w
  simp only [step, hv]
  rcases Nat.lt_trichotomy w W.length with hw | hw | hw
  · have hlt : wmap n m π w < W'.length := by
      unfold wmap
      split
      · have := (π ⟨w, by assumption⟩).2; omega
      · omega
    rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hw]
    exact h3 w
  · have he : wmap n m π w = W'.length := by
      unfold wmap
      split
      · omega
      · omega
    rw [he, hw, getD_snoc_eq, getD_snoc_eq]
  · have hge : W'.length + 1 ≤ wmap n m π w := by
      unfold wmap
      split
      · omega
      · omega
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

theorem rel_fold (n m : ℕ) (π : Fin n → Fin m) (gs : List Gate) :
    ∀ W W' : List Bool, Rel n m π W W' →
      Rel n m π (gs.foldl step W) ((gs.map (relGate n m π)).foldl step W') := by
  induction gs with
  | nil => intro W W' h; exact h
  | cons g gs ih =>
    intro W W' h
    exact ih _ _ (rel_step n m π W W' g h)

theorem rel_init (n m : ℕ) (π : Fin n → Fin m) (x : Fin m → Bool) :
    Rel n m π (List.ofFn (x ∘ π)) (List.ofFn x) := by
  refine ⟨by simp, by simp; omega, ?_⟩
  intro w
  unfold wmap
  split
  · rename_i hw
    rw [List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simpa using hw)]
    simp
  · rename_i hw
    rw [List.getD_eq_default _ _ (by simp), List.getD_eq_default _ _ (by simp; omega)]

/-- Renaming inputs along any map keeps the circuit size. -/
theorem relabel_size {n m : ℕ} (π : Fin n → Fin m) (h : (Fin n → Bool) → Bool) (s : ℕ)
    (hc : HasCircuitSize n h s) : HasCircuitSize m (fun x => h (x ∘ π)) s := by
  obtain ⟨C, ok, hsz, hev⟩ := hc
  refine ⟨relabel n m π C, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact ⟨(ok g0 hg0).1, by simpa [relGate] using (ok g0 hg0).2⟩
  · simpa [relabel, Circuit.size] using hsz
  · intro x
    show _ = h (x ∘ π)
    rw [← hev (x ∘ π)]
    have := (rel_fold n m π C.gates _ _ (rel_init n m π x)).2.2 C.output
    exact this

/-- L-meta-011 for a set of inputs. -/
theorem dep_lower_set (n : ℕ) (f : (Fin n → Bool) → Bool) (T : Finset (Fin n))
    (hdep : ∀ i ∈ T, ∃ x : Fin n → Bool, f (Function.update x i (!x i)) ≠ f x)
    (s : ℕ) (h : HasCircuitSize n f s) : T.card ≤ s + 1 := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set S := (suppsFrom C.gates (inputSupps n)).getD C.output ∅ with hS
  have hall : T ⊆ S := by
    intro i hiT
    by_contra hi
    obtain ⟨x, hx⟩ := hdep i hiT
    apply hx
    have hag := (agree_wiresFrom (Function.update x i (!x i)) x C.gates _ _ _
      (agree_inputs _ _)).2.2 C.output (by
        intro k hk
        have : k ≠ i := fun e => hi (e ▸ hk)
        simp [Function.update_of_ne this])
    rw [← hev, ← hev]
    exact hag
  have hc := cnt_suppsFrom C.gates 0 (inputSupps n) ok cnt_inputs {C.output}
  simp only [Finset.singleton_biUnion, Finset.card_singleton, zero_add] at hc
  rw [← hS] at hc
  have := Finset.card_le_card hall
  omega

theorem snoc_swap (n : ℕ) (p : Fin (n + 1)) (x : Fin (n + 1) → Bool) (b : Bool) :
    (Fin.snoc (fun j : Fin n => x (Equiv.swap p (Fin.last n) j.castSucc)) b :
        Fin (n + 1) → Bool) ∘ (Equiv.swap p (Fin.last n))
      = Function.update x p b := by
  funext j
  simp only [Function.comp_apply]
  by_cases hj : j = p
  · subst hj
    rw [Equiv.swap_apply_left, Fin.snoc_last, Function.update_self]
  · have hl : Equiv.swap p (Fin.last n) j ≠ Fin.last n := by
      intro e
      apply hj
      have := congrArg (Equiv.swap p (Fin.last n)) e
      rwa [Equiv.swap_apply_self, Equiv.swap_apply_right] at this
    obtain ⟨t, ht⟩ := Fin.exists_castSucc_eq.2 hl
    rw [← ht, Fin.snoc_castSucc, ht, Equiv.swap_apply_self, Function.update_of_ne hj]

/-- Two-gate elimination at any input position, the arity kept. -/
theorem gate_elim_at (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (p : Fin (n + 1)) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x p (!x p)) ≠ f x)
    (hnc : ∀ b : Bool, ∃ x y : Fin (n + 1) → Bool,
      f (Function.update x p b) ≠ f (Function.update y p b))
    (h : HasCircuitSize (n + 1) f s) :
    ∃ (b : Bool) (s' : ℕ), s' + 2 ≤ s ∧
      HasCircuitSize (n + 1) (fun x => f (Function.update x p b)) s' := by
  set σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap p (Fin.last n) with hσ
  have hg : HasCircuitSize (n + 1) (fun x => f (x ∘ σ)) s := relabel_size (⇑σ) f s h
  have hss : ∀ x : Fin (n + 1) → Bool, (x ∘ σ) ∘ σ = x := by
    intro x; funext j; simp [hσ, Equiv.swap_apply_self]
  have hsl : σ.symm (Fin.last n) = p := by
    rw [hσ, Equiv.symm_swap, Equiv.swap_apply_right]
  have hdep' : ∃ x : Fin (n + 1) → Bool,
      (fun x => f (x ∘ σ)) (Function.update x (Fin.last n) (!x (Fin.last n)))
        ≠ (fun x => f (x ∘ σ)) x := by
    obtain ⟨x0, hx0⟩ := hdep
    refine ⟨x0 ∘ σ, ?_⟩
    simp only
    rw [Function.update_comp_equiv, hsl, hss]
    have : (x0 ∘ ⇑σ) (Fin.last n) = x0 p := by
      simp [hσ, Equiv.swap_apply_right]
    rw [this]
    exact hx0
  have hnc' : ∀ b : Bool, ∃ y y' : Fin n → Bool,
      (fun x => f (x ∘ σ)) (Fin.snoc y b) ≠ (fun x => f (x ∘ σ)) (Fin.snoc y' b) := by
    intro b
    obtain ⟨x, y, hxy⟩ := hnc b
    refine ⟨fun j => x (σ j.castSucc), fun j => y (σ j.castSucc), ?_⟩
    simp only
    rw [snoc_swap, snoc_swap]
    exact hxy
  obtain ⟨b, s', hs, h'⟩ := gate_elim_two n _ s hdep' hnc' hg
  refine ⟨b, s', hs, ?_⟩
  have h'' := relabel_size (fun j : Fin n => σ j.castSucc) _ s' h'
  have e : (fun x : Fin (n + 1) → Bool =>
      (fun y : Fin n → Bool => (fun x => f (x ∘ σ)) (Fin.snoc y b))
        (x ∘ fun j : Fin n => σ j.castSucc))
      = fun x => f (Function.update x p b) := by
    funext x
    simp only
    exact congrArg f (snoc_swap n p x b)
  rw [e] at h''
  exact h''

/-- Fixing the inputs of `L` in order, each with a two-gate saving, then every input of `T`
matters. Condition on `L`: for every assignment `a` and every split `L = pre ++ p :: post`,
the function depends on `p` among the inputs agreeing with `a` on `pre`. Condition on `T`: for
every `a` and `i ∈ T`, the function depends on `i` among the inputs agreeing with `a` on `L`. -/
theorem fix_many {N : ℕ} (T : Finset (Fin N)) (hT : T.Nonempty) :
    ∀ (L : List (Fin N)) (f : (Fin N → Bool) → Bool), L.Nodup → (∀ p ∈ L, p ∉ T) →
    (∀ (a : Fin N → Bool) (pre post : List (Fin N)) (p : Fin N), L = pre ++ p :: post →
      ∃ x : Fin N → Bool, (∀ q ∈ pre, x q = a q) ∧ f (Function.update x p (!x p)) ≠ f x) →
    (∀ (a : Fin N → Bool), ∀ i ∈ T, ∃ x : Fin N → Bool, (∀ q ∈ L, x q = a q) ∧
      f (Function.update x i (!x i)) ≠ f x) →
    ∀ s : ℕ, HasCircuitSize N f s → T.card + 2 * L.length ≤ s + 1 := by
  obtain ⟨i0, hi0⟩ := hT
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by have := i0.2; omega⟩
  intro L
  induction L with
  | nil =>
    intro f _ _ _ hC s h
    have := dep_lower_set (n + 1) f T (fun i hi => by
      obtain ⟨x, _, hx⟩ := hC (fun _ => false) i hi
      exact ⟨x, hx⟩) s h
    simpa using this
  | cons p L ih =>
    intro f hnd hdis hA hC s h
    have hpL : p ∉ L := (List.nodup_cons.1 hnd).1
    have hpT : p ∉ T := hdis p List.mem_cons_self
    have hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x p (!x p)) ≠ f x := by
      obtain ⟨x, _, hx⟩ := hA (fun _ => false) [] L p rfl
      exact ⟨x, hx⟩
    have hnc : ∀ b : Bool, ∃ x y : Fin (n + 1) → Bool,
        f (Function.update x p b) ≠ f (Function.update y p b) := by
      intro b
      obtain ⟨x, hxa, hx⟩ := hC (fun _ => b) i0 hi0
      have hxp : x p = b := hxa p List.mem_cons_self
      have hi0p : i0 ≠ p := fun e => hpT (e ▸ hi0)
      refine ⟨Function.update x i0 (!x i0), x, ?_⟩
      have e1 : Function.update (Function.update x i0 (!x i0)) p b
          = Function.update x i0 (!x i0) :=
        Function.update_eq_self_iff.2 (by rw [Function.update_of_ne (Ne.symm hi0p), hxp])
      have e2 : Function.update x p b = x := Function.update_eq_self_iff.2 hxp.symm
      rw [e1, e2]
      exact hx
    obtain ⟨b, s', hs, h'⟩ := gate_elim_at n f p s hdep hnc h
    have := ih (fun x => f (Function.update x p b)) (List.nodup_cons.1 hnd).2
      (fun q hq => hdis q (List.mem_cons_of_mem _ hq)) ?_ ?_ s' h'
    · simp only [List.length_cons]; omega
    · intro a pre post p' hL
      obtain ⟨x, hxa, hx⟩ := hA (Function.update a p b) (p :: pre) post p' (by rw [hL]; rfl)
      have hxp : x p = b := by
        rw [hxa p List.mem_cons_self, Function.update_self]
      have hp' : p' ≠ p := by
        intro e; apply hpL; rw [← e, hL]; simp
      refine ⟨x, fun q hq => ?_, ?_⟩
      · have hqp : q ≠ p := by
          intro e; apply hpL; rw [← e, hL]; simp [hq]
        rw [hxa q (List.mem_cons_of_mem _ hq), Function.update_of_ne hqp]
      · have e1 : Function.update (Function.update x p' (!x p')) p b
            = Function.update x p' (!x p') :=
          Function.update_eq_self_iff.2 (by rw [Function.update_of_ne (Ne.symm hp'), hxp])
        have e2 : Function.update x p b = x := Function.update_eq_self_iff.2 hxp.symm
        show f _ ≠ f _
        rw [e1, e2]
        exact hx
    · intro a i hi
      obtain ⟨x, hxa, hx⟩ := hC (Function.update a p b) i hi
      have hxp : x p = b := by
        rw [hxa p List.mem_cons_self, Function.update_self]
      have hip : i ≠ p := fun e => hpT (e ▸ hi)
      refine ⟨x, fun q hq => ?_, ?_⟩
      · have hqp : q ≠ p := fun e => hpL (e ▸ hq)
        rw [hxa q (List.mem_cons_of_mem _ hq), Function.update_of_ne hqp]
      · have e1 : Function.update (Function.update x i (!x i)) p b
            = Function.update x i (!x i) :=
          Function.update_eq_self_iff.2 (by rw [Function.update_of_ne (Ne.symm hip), hxp])
        have e2 : Function.update x p b = x := Function.update_eq_self_iff.2 hxp.symm
        show f _ ≠ f _
        rw [e1, e2]
        exact hx

end PEqualNP.Outside.L_meta_764_aux.PermInputs

/-! ---- ported from PEqualNP.MetaComplexity.Helpers.ForestElim ---- -/

/-!
# One-gate elimination at any input, the arity kept

Helper for `L-meta-104` (proofs only, no statement may use it). The one-gate elimination
`gate_elim` of `Elim.lean` fixes the last input; renaming the inputs by a transposition moves
any input to the last place, as `gate_elim_at` of `PermInputs.lean` does for two gates.
-/

namespace PEqualNP.Outside.L_meta_764_aux.Forest

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_764_aux.PermInputs

/-- One-gate elimination at input `p` with the chosen value `b`, the arity kept. -/
theorem one_gate_at (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (p : Fin (n + 1)) (b : Bool)
    (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x p (!x p)) ≠ f x)
    (hnc : ∃ x y : Fin (n + 1) → Bool,
      f (Function.update x p b) ≠ f (Function.update y p b))
    (h : HasCircuitSize (n + 1) f (s + 1)) :
    HasCircuitSize (n + 1) (fun x => f (Function.update x p b)) s := by
  set σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap p (Fin.last n) with hσ
  have hg : HasCircuitSize (n + 1) (fun x => f (x ∘ σ)) (s + 1) := relabel_size (⇑σ) f _ h
  have hss : ∀ x : Fin (n + 1) → Bool, (x ∘ σ) ∘ σ = x := by
    intro x; funext j; simp [hσ, Equiv.swap_apply_self]
  have hsl : σ.symm (Fin.last n) = p := by
    rw [hσ, Equiv.symm_swap, Equiv.swap_apply_right]
  have hdep' : ∃ x : Fin (n + 1) → Bool,
      (fun x => f (x ∘ σ)) (Function.update x (Fin.last n) (!x (Fin.last n)))
        ≠ (fun x => f (x ∘ σ)) x := by
    obtain ⟨x0, hx0⟩ := hdep
    refine ⟨x0 ∘ σ, ?_⟩
    simp only
    rw [Function.update_comp_equiv, hsl, hss]
    have : (x0 ∘ ⇑σ) (Fin.last n) = x0 p := by
      simp [hσ, Equiv.swap_apply_right]
    rw [this]
    exact hx0
  have hnc' : ∃ y y' : Fin n → Bool,
      (fun x => f (x ∘ σ)) (Fin.snoc y b) ≠ (fun x => f (x ∘ σ)) (Fin.snoc y' b) := by
    obtain ⟨x, y, hxy⟩ := hnc
    refine ⟨fun j => x (σ j.castSucc), fun j => y (σ j.castSucc), ?_⟩
    simp only
    rw [snoc_swap, snoc_swap]
    exact hxy
  have h' := PEqualNP.Outside.L_meta_764_aux.gate_elim n _ b s hdep' hnc' hg
  have h'' := relabel_size (fun j : Fin n => σ j.castSucc) _ s h'
  have e : (fun x : Fin (n + 1) → Bool =>
      (fun y : Fin n → Bool => (fun x => f (x ∘ σ)) (Fin.snoc y b))
        (x ∘ fun j : Fin n => σ j.castSucc))
      = fun x => f (Function.update x p b) := by
    funext x
    simp only
    exact congrArg f (snoc_swap n p x b)
  rw [e] at h''
  exact h''

end PEqualNP.Outside.L_meta_764_aux.Forest

/-! ---- ported from PEqualNP.MetaComplexity.Helpers.PadOr ---- -/

/-!
# Padding by a fresh OR variable costs exactly one gate

Helper for `L-meta-128` (proofs only, no statement may use it). For a non-constant `f` on `n`
inputs, `g x = x last || f (first n of x)` has a circuit with at most `s + 1` gates exactly
when `f` has one with at most `s`.

* Upward: rename the inputs of a circuit for `f` along `Fin.castSucc` (`relabel_size`), then
  add one OR gate reading the new input and the old output.
* Downward: one-gate elimination at the last input with value `false` (`one_gate_at`), then
  drop the unread last input by renaming along a map `Fin (n + 1) → Fin n` (`relabel_size`).
-/

namespace PEqualNP.Outside.L_meta_764_aux.PadOr

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_764_aux.PermInputs

/-- Evaluating gates only appends wires, one per gate. -/
theorem fold_prefix (gs : List Gate) : ∀ w : List Bool, ∃ t : List Bool,
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w = w ++ t ∧
      t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp, rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨[g.op.eval (g.inputs.map fun i => w.getD i false)] ++ t, ?_, ?_⟩
    · simp only [List.foldl_cons]; rw [ht]; simp
    · simp [hl]

/-- Add one OR gate reading wire `a` and the old output. -/
def addOr (C : Circuit) (n a : ℕ) : Circuit :=
  ⟨C.gates ++ [⟨GateOp.or, [a, C.output]⟩], n + C.gates.length⟩

theorem addOr_eval (C : Circuit) (x : List Bool) (a : ℕ) (ha : a < x.length) :
    (addOr C x.length a).eval x = (x.getD a false || C.eval x) := by
  obtain ⟨t, ht, hl⟩ := fold_prefix C.gates x
  have hw : C.wires x = x ++ t := ht
  have hw2 : (addOr C x.length a).wires x =
      C.wires x ++ [GateOp.or.eval ([a, C.output].map fun i => (C.wires x).getD i false)] := by
    simp [addOr, Circuit.wires, List.foldl_append]
  have hlen : (C.wires x).length = x.length + C.gates.length := by
    rw [hw, List.length_append, hl]
  unfold Circuit.eval
  rw [hw2]
  have hout : (addOr C x.length a).output = (C.wires x).length := by
    simp [addOr, hlen]
  rw [hout, List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self]
  have hxa : (C.wires x).getD a false = x.getD a false := by
    rw [hw, List.getD_append _ _ _ _ ha]
  simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id, hxa,
    Bool.or_false]
  rfl

/-- Upward: one more gate pays for the fresh OR variable. -/
theorem pad_up (n s : ℕ) (f : (Fin n → Bool) → Bool) (h : HasCircuitSize n f s) :
    HasCircuitSize (n + 1)
      (fun x : Fin (n + 1) → Bool => x (Fin.last n) || f (fun i : Fin n => x i.castSucc))
      (s + 1) := by
  obtain ⟨C, ok, hsz, hev⟩ := relabel_size (Fin.castSucc : Fin n → Fin (n + 1)) f s h
  refine ⟨addOr C (n + 1) n, ?_, ?_, ?_⟩
  · intro g hg
    simp only [addOr, List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | hg
    · exact ok g hg
    · subst hg; simp
  · have : C.gates.length ≤ s := hsz
    simp [addOr, Circuit.size]; omega
  · intro x
    have hl : (List.ofFn x).length = n + 1 := List.length_ofFn
    have e := addOr_eval C (List.ofFn x) n (by rw [hl]; omega)
    rw [hl] at e
    rw [e, hev x]
    have : (List.ofFn x).getD n false = x (Fin.last n) := by
      rw [List.getD_eq_getElem _ _ (by rw [hl]; omega), List.getElem_ofFn]; rfl
    rw [this]; rfl

/-- Downward: the fresh OR variable costs at least one gate. -/
theorem pad_down (n s : ℕ) (f : (Fin n → Bool) → Bool) (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y')
    (h : HasCircuitSize (n + 1)
      (fun x : Fin (n + 1) → Bool => x (Fin.last n) || f (fun i : Fin n => x i.castSucc))
      (s + 1)) : HasCircuitSize n f s := by
  obtain ⟨y, y', hyy⟩ := hnc
  set g : (Fin (n + 1) → Bool) → Bool :=
    fun x => x (Fin.last n) || f (fun i : Fin n => x i.castSucc) with hg
  have hupd : ∀ (x : Fin (n + 1) → Bool) (b : Bool),
      (fun i : Fin n => Function.update x (Fin.last n) b i.castSucc) = fun i => x i.castSucc := by
    intro x b; funext i
    exact Function.update_of_ne (Fin.castSucc_lt_last i).ne _ _
  have hres : ∀ x : Fin (n + 1) → Bool,
      g (Function.update x (Fin.last n) false) = f (fun i : Fin n => x i.castSucc) := by
    intro x; simp only [hg]; rw [hupd]; simp
  have hsn : ∀ z : Fin n → Bool, ∀ b : Bool, (fun i : Fin n => (Fin.snoc z b : Fin (n + 1) → Bool) i.castSucc) = z := by
    intro z b; funext i; exact Fin.snoc_castSucc (α := fun _ => Bool) ..
  -- some point where f is false
  obtain ⟨z, hz⟩ : ∃ z : Fin n → Bool, f z = false := by
    cases h1 : f y
    · exact ⟨y, h1⟩
    · cases h2 : f y'
      · exact ⟨y', h2⟩
      · exact absurd (h1.trans h2.symm) hyy
  have hdep : ∃ x : Fin (n + 1) → Bool,
      g (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ g x := by
    refine ⟨Fin.snoc z false, ?_⟩
    simp only [hg, Function.update_self, Fin.snoc_last]
    rw [hupd, hsn, hz]; simp
  have hnc' : ∃ x x' : Fin (n + 1) → Bool,
      g (Function.update x (Fin.last n) false) ≠ g (Function.update x' (Fin.last n) false) := by
    refine ⟨Fin.snoc y false, Fin.snoc y' false, ?_⟩
    rw [hres, hres, hsn, hsn]; exact hyy
  have h1 := PEqualNP.Outside.L_meta_764_aux.Forest.one_gate_at n g (Fin.last n) false s hdep hnc' h
  have h1' : HasCircuitSize (n + 1) (fun x : Fin (n + 1) → Bool => f (fun i : Fin n => x i.castSucc)) s := by
    have e : (fun x => g (Function.update x (Fin.last n) false))
        = (fun x : Fin (n + 1) → Bool => f (fun i : Fin n => x i.castSucc)) := by
      funext x; exact hres x
    rw [← e]; exact h1
  -- n is positive: f is non-constant
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := by
    cases n with
    | zero => exact absurd (congrArg f (Subsingleton.elim y y')) hyy
    | succ m => exact ⟨m, rfl⟩
  let π : Fin (m + 1 + 1) → Fin (m + 1) := Fin.lastCases 0 id
  have h2 := relabel_size π _ s h1'
  have e : (fun x : Fin (m + 1) → Bool => f (fun i : Fin (m + 1) => (x ∘ π) i.castSucc)) = f := by
    funext x; congr 1; funext i; simp [π, Fin.lastCases_castSucc]
  rw [e] at h2; exact h2

theorem pad_or (n s : ℕ) (f : (Fin n → Bool) → Bool) (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') :
    HasCircuitSize (n + 1)
      (fun x : Fin (n + 1) → Bool => x (Fin.last n) || f (fun i : Fin n => x i.castSucc))
      (s + 1) ↔ HasCircuitSize n f s :=
  ⟨pad_down n s f hnc, pad_up n s f⟩

end PEqualNP.Outside.L_meta_764_aux.PadOr

/-! ---- ported from PEqualNP.MetaComplexity.Helpers.RigidAnd ---- -/

/-!
# A rigid AND term: `(x AND y) OR g` costs exactly two gates more than `g`

Helper for `L-meta-153` (proofs only, no statement may use it). For a non-constant `g` on `k`
inputs, `(x 0 && x 1) || g (inputs 2 ..)` on `2 + k` inputs has a circuit with at most `s + 2`
gates exactly when `g` has one with at most `s`.

* Upward: rename the inputs of a circuit for `g` along `Fin.natAdd 2`, then add an AND gate on
  wires `0, 1` and an OR gate on that AND and the old output.
* Downward: rename to arity `k + 1 + 1`, one-gate elimination at input `0` with value `true`
  (`one_gate_at`), rename down to `x last || g` on `k + 1` inputs, then `pad_down`.
-/

namespace PEqualNP.Outside.L_meta_764_aux.RigidAnd

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_764_aux.PermInputs PEqualNP.Outside.L_meta_764_aux.PadOr

/-- Add an AND gate on wires `0, 1` and an OR gate reading it and the old output. -/
def addAndOr (C : Circuit) (m : ℕ) : Circuit :=
  ⟨C.gates ++ [⟨GateOp.and, [0, 1]⟩, ⟨GateOp.or, [m + C.gates.length, C.output]⟩],
    m + C.gates.length + 1⟩

theorem addAndOr_eval (C : Circuit) (x : List Bool) (h2 : 2 ≤ x.length)
    (hout : C.output < x.length + C.gates.length) :
    (addAndOr C x.length).eval x = ((x.getD 0 false && x.getD 1 false) || C.eval x) := by
  obtain ⟨t, ht, hl⟩ := fold_prefix C.gates x
  have hw : C.wires x = x ++ t := ht
  have hlen : (C.wires x).length = x.length + C.gates.length := by
    rw [hw, List.length_append, hl]
  set a := GateOp.and.eval ([0, 1].map fun i => (C.wires x).getD i false) with ha
  have hw2 : (addAndOr C x.length).wires x =
      (C.wires x ++ [a]) ++ [GateOp.or.eval ([x.length + C.gates.length, C.output].map
        fun i => (C.wires x ++ [a]).getD i false)] := by
    simp [addAndOr, Circuit.wires, List.foldl_append, ha]
  unfold Circuit.eval
  rw [hw2]
  have hl2 : (C.wires x ++ [a]).length = x.length + C.gates.length + 1 := by
    simp [hlen]
  have ho : (addAndOr C x.length).output = (C.wires x ++ [a]).length := by
    simp [addAndOr, hl2]
  rw [ho, List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self]
  have hA : (C.wires x ++ [a]).getD (x.length + C.gates.length) false = a := by
    rw [← hlen]; exact getD_snoc_eq _ _ _
  have hB : (C.wires x ++ [a]).getD C.output false = (C.wires x).getD C.output false := by
    rw [List.getD_append _ _ _ _ (by rw [hlen]; exact hout)]
  have h0 : (C.wires x).getD 0 false = x.getD 0 false := by
    rw [hw, List.getD_append _ _ _ _ (by omega)]
  have h1 : (C.wires x).getD 1 false = x.getD 1 false := by
    rw [hw, List.getD_append _ _ _ _ (by omega)]
  simp only [List.map_cons, List.map_nil, hA, hB]
  simp only [ha, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
    List.all_cons, List.all_nil, id, h0, h1, Bool.or_false, Bool.and_true, List.getD_cons_zero]

/-- The target function: `(x 0 && x 1) || g (inputs 2 ..)`. -/
def andOr (k : ℕ) (g : (Fin k → Bool) → Bool) : (Fin (2 + k) → Bool) → Bool :=
  fun x => (x (Fin.castAdd k 0) && x (Fin.castAdd k 1)) || g (fun j : Fin k => x (Fin.natAdd 2 j))

/-- Upward: two more gates pay for the AND term. -/
theorem rigid_up (k s : ℕ) (g : (Fin k → Bool) → Bool) (hnc : ∃ y y' : Fin k → Bool, g y ≠ g y')
    (h : HasCircuitSize k g s) : HasCircuitSize (2 + k) (andOr k g) (s + 2) := by
  obtain ⟨C, ok, hsz, hev⟩ := relabel_size (Fin.natAdd 2 : Fin k → Fin (2 + k)) g s h
  have hsz' : C.gates.length ≤ s := hsz
  have happ : ∀ y : Fin k → Bool,
      (Fin.append (fun _ : Fin 2 => false) y : Fin (2 + k) → Bool) ∘ Fin.natAdd 2 = y := by
    intro y; funext j; simp [Fin.append_right]
  have hout : C.output < 2 + k + C.gates.length := by
    by_contra hc
    obtain ⟨y, y', hyy⟩ := hnc
    have hfalse : ∀ x : Fin (2 + k) → Bool, C.eval (List.ofFn x) = false := by
      intro x
      obtain ⟨t, ht, hl⟩ := fold_prefix C.gates (List.ofFn x)
      unfold Circuit.eval
      apply List.getD_eq_default
      have : (C.wires (List.ofFn x)).length = 2 + k + C.gates.length := by
        have hw : C.wires (List.ofFn x) = List.ofFn x ++ t := ht
        rw [hw, List.length_append, hl, List.length_ofFn]
      omega
    apply hyy
    have e1 := hev (Fin.append (fun _ : Fin 2 => false) y)
    have e2 := hev (Fin.append (fun _ : Fin 2 => false) y')
    rw [hfalse] at e1 e2
    beta_reduce at e1 e2
    rw [happ] at e1 e2
    rw [← e1, ← e2]
  refine ⟨addAndOr C (2 + k), ?_, ?_, ?_⟩
  · intro gt hg
    simp only [addAndOr, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with hg | hg | hg
    · exact ok gt hg
    · subst hg; simp
    · subst hg; simp
  · simp [addAndOr, Circuit.size]; omega
  · intro x
    have hl : (List.ofFn x).length = 2 + k := List.length_ofFn
    have e := addAndOr_eval C (List.ofFn x) (by rw [hl]; omega) (by rw [hl]; exact hout)
    rw [hl] at e
    rw [e, hev x]
    have h0 : (List.ofFn x).getD 0 false = x (Fin.castAdd k 0) := by
      rw [List.getD_eq_getElem _ _ (by rw [hl]; omega), List.getElem_ofFn]; rfl
    have h1 : (List.ofFn x).getD 1 false = x (Fin.castAdd k 1) := by
      rw [List.getD_eq_getElem _ _ (by rw [hl]; omega), List.getElem_ofFn]; rfl
    rw [h0, h1]; rfl

/-- Downward: the AND term costs at least two gates. -/
theorem rigid_down (k s : ℕ) (g : (Fin k → Bool) → Bool) (hnc : ∃ y y' : Fin k → Bool, g y ≠ g y')
    (h : HasCircuitSize (2 + k) (andOr k g) (s + 2)) : HasCircuitSize k g s := by
  have hk : k + 1 + 1 = 2 + k := by omega
  have hH := relabel_size (Fin.cast hk.symm : Fin (2 + k) → Fin (k + 1 + 1)) (andOr k g) _ h
  set H : (Fin (k + 1 + 1) → Bool) → Bool :=
    fun z => andOr k g (z ∘ Fin.cast hk.symm) with hHdef
  set p : Fin (k + 1 + 1) := ⟨0, by omega⟩ with hp
  set q : Fin (k + 1 + 1) := ⟨1, by omega⟩ with hq
  set r : Fin k → Fin (k + 1 + 1) := fun j => ⟨2 + j, by omega⟩ with hr
  have hHval : ∀ z, H z = ((z p && z q) || g (fun j => z (r j))) := by
    intro z; rfl
  obtain ⟨y, y', hyy⟩ := hnc
  obtain ⟨w, hw⟩ : ∃ w : Fin k → Bool, g w = false := by
    cases h1 : g y
    · exact ⟨y, h1⟩
    · cases h2 : g y'
      · exact ⟨y', h2⟩
      · exact absurd (h1.trans h2.symm) hyy
  -- a point built from the values at p, q and the rest
  let mk : Bool → Bool → (Fin k → Bool) → Fin (k + 1 + 1) → Bool :=
    fun a b v i => if i.val = 0 then a else if i.val = 1 then b else
      if hi : i.val - 2 < k then v ⟨i.val - 2, hi⟩ else false
  have mk_p : ∀ a b v, mk a b v p = a := by intro a b v; simp [mk, hp]
  have mk_q : ∀ a b v, mk a b v q = b := by intro a b v; simp [mk, hq]
  have mk_r : ∀ a b v, (fun j => mk a b v (r j)) = v := by
    intro a b v; funext j; simp [mk, hr]; omega
  have up_p : ∀ (z : Fin (k + 1 + 1) → Bool) (c : Bool), Function.update z p c p = c := by
    intro z c; simp
  have up_q : ∀ (z : Fin (k + 1 + 1) → Bool) (c : Bool), Function.update z p c q = z q := by
    intro z c; apply Function.update_of_ne; simp [hp, hq, Fin.ext_iff]
  have up_r : ∀ (z : Fin (k + 1 + 1) → Bool) (c : Bool),
      (fun j => Function.update z p c (r j)) = fun j => z (r j) := by
    intro z c; funext j; apply Function.update_of_ne; simp [hp, hr, Fin.ext_iff]
  have hdep : ∃ x : Fin (k + 1 + 1) → Bool, H (Function.update x p (!x p)) ≠ H x := by
    refine ⟨mk false true w, ?_⟩
    rw [hHval, hHval, up_p, up_q, up_r, mk_p, mk_q, mk_r, hw]; simp
  have hnc' : ∃ x x' : Fin (k + 1 + 1) → Bool,
      H (Function.update x p true) ≠ H (Function.update x' p true) := by
    refine ⟨mk false true w, mk false false w, ?_⟩
    rw [hHval, hHval, up_p, up_p, up_q, up_q, up_r, up_r, mk_q, mk_q, mk_r, mk_r, hw]; simp
  have h1 := PEqualNP.Outside.L_meta_764_aux.Forest.one_gate_at (k + 1) H p true (s + 1) hdep hnc' hH
  let π : Fin (k + 1 + 1) → Fin (k + 1) :=
    fun i => if hi : 2 ≤ i.val then ⟨i.val - 2, by omega⟩ else Fin.last k
  have h2 := relabel_size π _ (s + 1) h1
  have e : (fun x : Fin (k + 1) → Bool => H (Function.update (x ∘ π) p true))
      = fun x : Fin (k + 1) → Bool => x (Fin.last k) || g (fun i : Fin k => x i.castSucc) := by
    funext x
    rw [hHval, up_p, up_q, up_r]
    have hq' : (x ∘ π) q = x (Fin.last k) := by simp [π, hq]
    have hr' : (fun j => (x ∘ π) (r j)) = fun i : Fin k => x i.castSucc := by
      funext j; simp only [Function.comp, π, hr]
      rw [dif_pos (by omega)]; congr 1; ext; simp
    rw [hq', hr']; simp
  rw [e] at h2
  exact pad_down k s g ⟨y, y', hyy⟩ h2

theorem rigid_and (k s : ℕ) (g : (Fin k → Bool) → Bool) (hnc : ∃ y y' : Fin k → Bool, g y ≠ g y') :
    HasCircuitSize (2 + k) (andOr k g) (s + 2) ↔ HasCircuitSize k g s :=
  ⟨rigid_down k s g hnc, rigid_up k s g hnc⟩

end PEqualNP.Outside.L_meta_764_aux.RigidAnd

/-! ---- ported from PEqualNP.MetaComplexity.Helpers.TableSearch ---- -/

/-!
# Circuits as truth tables, and a bounded search over tables

A truth table on `n` inputs is a natural number read as a bitmask: bit `p` is the value at the
point `p`. `M` is the table that is true everywhere (`2 ^ (2 ^ n) - 1` for `n` inputs; any `M`
with bit `p` set works at the point `p`).

* `gt M op l`: the table of one gate whose inputs have the tables `l`;
* `tabs M T0 gs`: the tables of all wires, mirroring `Circuit.wires`;
* `wires_tabs` (the abstraction lemma): at a point `p` where `M` is true, the wire values are
  the bits `p` of the wire tables, for circuits of AND, OR and NOT gates of fan-in two;
* `reach M good k S`: a search over the tables that `k` more gates can add to the wire tables
  `S`, asking whether some wire table is `good`;
* `reach_sound`: a circuit of at most `k` gates whose output table is good makes the search
  succeed. So a failed search, checked by `decide`, is a circuit lower bound.
-/

namespace PEqualNP.Outside.L_meta_764_aux.TableSearch

open PEqualNP.CircuitLowerBounds

/-- The table of one gate, from the tables of the wires it reads. Meant for AND, OR and NOT
gates reading at most two wires. -/
def gt (M : ℕ) : GateOp → List ℕ → ℕ
  | GateOp.and, [] => M
  | GateOp.and, [a] => a
  | GateOp.and, a :: b :: _ => a &&& b
  | GateOp.or, [] => 0
  | GateOp.or, [a] => a
  | GateOp.or, a :: b :: _ => a ||| b
  | GateOp.not, [] => M
  | GateOp.not, a :: _ => M ^^^ a
  | _, _ => 0

/-- One step of `tabs`. -/
def tstep (M : ℕ) (T : List ℕ) (g : Gate) : List ℕ :=
  T ++ [gt M g.op (g.inputs.map fun i => T.getD i 0)]

/-- The tables of all wires: the tables `T0` of the inputs, then one table per gate. -/
def tabs (M : ℕ) (T0 : List ℕ) (gs : List Gate) : List ℕ :=
  gs.foldl (tstep M) T0

/-- The gate is AND, OR or NOT and reads at most two wires. -/
def GOk (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2

theorem gt_testBit (M p : ℕ) (hM : M.testBit p = true) (op : GateOp)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (l : List ℕ)
    (hl : l.length ≤ 2) :
    (gt M op l).testBit p = op.eval (l.map fun t => t.testBit p) := by
  match l, hl with
  | [], _ => rcases hop with h | h | h <;> subst h <;> simp [gt, GateOp.eval, hM]
  | [a], _ => rcases hop with h | h | h <;> subst h <;> simp [gt, GateOp.eval, Nat.testBit_xor, hM]
  | [a, b], _ =>
    rcases hop with h | h | h <;> subst h <;>
      simp [gt, GateOp.eval, Nat.testBit_xor, Nat.testBit_land, Nat.testBit_lor, hM]

theorem getD_map_testBit (T : List ℕ) (p i : ℕ) :
    (T.map fun t => t.testBit p).getD i false = (T.getD i 0).testBit p := by
  rw [show false = (0 : ℕ).testBit p by simp, List.getD_map]

/-- The abstraction lemma: wire values at the point `p` are bits of the wire tables. -/
theorem wires_tabs (M p : ℕ) (hM : M.testBit p = true) :
    ∀ (gs : List Gate) (T0 : List ℕ), (∀ g ∈ gs, GOk g) →
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
          (T0.map fun t => t.testBit p)
        = (tabs M T0 gs).map fun t => t.testBit p := by
  intro gs
  induction gs with
  | nil => intro T0 _; rfl
  | cons g gs ih =>
    intro T0 hok
    have hg := hok g (by simp)
    have e : (T0.map fun t => t.testBit p) ++
        [g.op.eval (g.inputs.map fun i => (T0.map fun t => t.testBit p).getD i false)]
        = (tstep M T0 g).map fun t => t.testBit p := by
      simp only [tstep, List.map_append, List.map_cons, List.map_nil]
      congr 2
      rw [gt_testBit M p hM g.op hg.1 _ (by simpa using hg.2), List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      exact getD_map_testBit T0 p i
    simp only [List.foldl_cons]
    rw [e]
    exact ih _ (fun g' hg' => hok g' (by simp [hg']))

/-- Every table one gate can add to the wire tables `S` (a missing wire reads `0`). -/
def cands (M : ℕ) (S : List ℕ) : List ℕ :=
  M :: 0 :: ((0 :: S).map (fun a => M ^^^ a) ++ (0 :: S) ++
    ((0 :: S).flatMap fun a => (0 :: S).map fun b => a &&& b) ++
    ((0 :: S).flatMap fun a => (0 :: S).map fun b => a ||| b))

/-- A list without repetitions, with the same members. -/
def nub : List ℕ → List ℕ
  | [] => []
  | a :: l => if (nub l).contains a then nub l else a :: nub l

theorem mem_nub (x : ℕ) : ∀ l : List ℕ, x ∈ nub l ↔ x ∈ l := by
  intro l
  induction l with
  | nil => simp [nub]
  | cons a l ih =>
    simp only [nub]
    split
    · rename_i h
      simp only [List.contains_iff_mem] at h
      rw [ih, List.mem_cons]
      constructor
      · exact Or.inr
      · rintro (rfl | h') <;> [exact (ih.1 h); exact h']
    · simp [ih]

/-- The new tables one gate can add to `S`, without repetitions. -/
def next (M : ℕ) (S : List ℕ) : List ℕ :=
  nub ((cands M S).filter fun t => !(S.contains t))

/-- Some wire table of `S`, or the missing-wire table `0`, is good, using at most `k` more
gates. -/
def reach (M : ℕ) (good : ℕ → Bool) : ℕ → List ℕ → Bool
  | 0, S => (0 :: S).any good
  | k + 1, S => (0 :: S).any good || (next M S).any fun t => reach M good k (S ++ [t])

theorem cands_mono (M : ℕ) (S S' : List ℕ) (h : ∀ x, x ∈ S → x ∈ S') (t : ℕ)
    (ht : t ∈ cands M S) : t ∈ cands M S' := by
  have h0 : ∀ x, x ∈ (0 :: S) → x ∈ (0 :: S') := by
    intro x hx
    rcases List.mem_cons.1 hx with hx | hx
    · simp [hx]
    · exact List.mem_cons_of_mem _ (h x hx)
  simp only [cands, List.mem_cons, List.mem_append, List.mem_map, List.mem_flatMap] at ht
  simp only [cands, List.mem_cons, List.mem_append, List.mem_map, List.mem_flatMap]
  rcases ht with ht | ht | ((⟨a, ha, e⟩ | ht) | ⟨a, ha, b, hb, e⟩) | ⟨a, ha, b, hb, e⟩
  · exact Or.inl ht
  · exact Or.inr (Or.inl ht)
  · refine Or.inr (Or.inr (Or.inl (Or.inl (Or.inl ⟨a, ?_, e⟩))))
    have := h0 a (by simpa using ha); simpa using this
  · refine Or.inr (Or.inr (Or.inl (Or.inl (Or.inr ?_))))
    have := h0 t (by simpa using ht); simpa using this
  · refine Or.inr (Or.inr (Or.inl (Or.inr ⟨a, ?_, b, ?_, e⟩)))
    · have := h0 a (by simpa using ha); simpa using this
    · have := h0 b (by simpa using hb); simpa using this
  · refine Or.inr (Or.inr (Or.inr ⟨a, ?_, b, ?_, e⟩))
    · have := h0 a (by simpa using ha); simpa using this
    · have := h0 b (by simpa using hb); simpa using this

theorem mem_next (M : ℕ) (S : List ℕ) (t : ℕ) : t ∈ next M S ↔ t ∈ cands M S ∧ t ∉ S := by
  simp [next, mem_nub]

theorem any_congr_mem (l l' : List ℕ) (f f' : ℕ → Bool) (hl : ∀ x, x ∈ l ↔ x ∈ l')
    (hf : ∀ x, f x = f' x) : l.any f = l'.any f' := by
  rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
  constructor
  · rintro ⟨x, hx, e⟩; exact ⟨x, (hl x).1 hx, by rw [← hf]; exact e⟩
  · rintro ⟨x, hx, e⟩; exact ⟨x, (hl x).2 hx, by rw [hf]; exact e⟩

/-- The search depends on the wire tables only through which tables are present. -/
theorem reach_congr (M : ℕ) (good : ℕ → Bool) : ∀ (k : ℕ) (S S' : List ℕ),
    (∀ x, x ∈ S ↔ x ∈ S') → reach M good k S = reach M good k S' := by
  intro k
  induction k with
  | zero =>
    intro S S' h
    simp only [reach]
    exact any_congr_mem _ _ _ _ (by intro x; simp [h]) (fun _ => rfl)
  | succ k ih =>
    intro S S' h
    simp only [reach]
    congr 1
    · exact any_congr_mem _ _ _ _ (by intro x; simp [h]) (fun _ => rfl)
    · apply any_congr_mem
      · intro x
        rw [mem_next, mem_next]
        exact ⟨fun ⟨a, b⟩ => ⟨cands_mono M S S' (fun y => (h y).1) x a, by rwa [← h]⟩,
          fun ⟨a, b⟩ => ⟨cands_mono M S' S (fun y => (h y).2) x a, by rwa [h]⟩⟩
      · intro t
        exact ih _ _ (by intro x; simp [h])

theorem reach_of_zero (M : ℕ) (good : ℕ → Bool) (S : List ℕ) (h : reach M good 0 S = true) :
    ∀ k, reach M good k S = true := by
  intro k
  cases k with
  | zero => exact h
  | succ k => simp only [reach] at h ⊢; simp [h]

theorem reach_succ (M : ℕ) (good : ℕ → Bool) (k : ℕ) (S : List ℕ) :
    reach M good (k + 1) S
      = ((0 :: S).any good || (next M S).any fun t => reach M good k (S ++ [t])) := rfl

theorem reach_mono (M : ℕ) (good : ℕ → Bool) : ∀ (k : ℕ) (S : List ℕ),
    reach M good k S = true → reach M good (k + 1) S = true := by
  intro k
  induction k with
  | zero => intro S h; exact reach_of_zero M good S h 1
  | succ k ih =>
    intro S h
    rw [reach_succ M good k S] at h
    rw [reach_succ M good (k + 1) S]
    simp only [Bool.or_eq_true, List.any_eq_true] at h ⊢
    rcases h with h | ⟨t, ht, e⟩
    · exact Or.inl h
    · exact Or.inr ⟨t, ht, ih _ e⟩

theorem getD_mem_zero (S : List ℕ) (o : ℕ) : S.getD o 0 ∈ (0 :: S) := by
  rw [List.getD_eq_getElem?_getD]
  cases hs : S[o]? with
  | none => simp
  | some v => exact List.mem_cons_of_mem _ (List.mem_of_getElem? hs)

theorem mem_cands_not (M : ℕ) (S : List ℕ) (a : ℕ) (ha : a ∈ (0 :: S)) :
    M ^^^ a ∈ cands M S :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem ha)))))

theorem mem_cands_copy (M : ℕ) (S : List ℕ) (a : ℕ) (ha : a ∈ (0 :: S)) : a ∈ cands M S :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_append_right _ ha))))

theorem mem_cands_and (M : ℕ) (S : List ℕ) (a b : ℕ) (ha : a ∈ (0 :: S)) (hb : b ∈ (0 :: S)) :
    a &&& b ∈ cands M S :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _
    (List.mem_append_right _ (List.mem_flatMap.2 ⟨a, ha, List.mem_map_of_mem hb⟩))))

theorem mem_cands_or (M : ℕ) (S : List ℕ) (a b : ℕ) (ha : a ∈ (0 :: S)) (hb : b ∈ (0 :: S)) :
    a ||| b ∈ cands M S :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_right _
    (List.mem_flatMap.2 ⟨a, ha, List.mem_map_of_mem hb⟩)))

theorem gt_mem (M : ℕ) (S : List ℕ) (g : Gate) (hg : GOk g) :
    gt M g.op (g.inputs.map fun i => S.getD i 0) ∈ cands M S := by
  obtain ⟨hop, hl⟩ := hg
  have hm : ∀ i, S.getD i 0 ∈ (0 :: S) := getD_mem_zero S
  generalize g.inputs = ins at hl ⊢
  match ins, hl with
  | [], _ =>
    rcases hop with h | h | h <;> rw [h] <;> simp [gt, cands]
  | [i], _ =>
    rcases hop with h | h | h <;> rw [h] <;> simp only [gt, List.map_cons, List.map_nil]
    · exact mem_cands_copy M S _ (hm i)
    · exact mem_cands_copy M S _ (hm i)
    · exact mem_cands_not M S _ (hm i)
  | [i, j], _ =>
    rcases hop with h | h | h <;> rw [h] <;> simp only [gt, List.map_cons, List.map_nil]
    · exact mem_cands_and M S _ _ (hm i) (hm j)
    · exact mem_cands_or M S _ _ (hm i) (hm j)
    · exact mem_cands_not M S _ (hm i)

/-- Soundness of the search: a circuit with at most `k` gates whose output table is good. -/
theorem reach_sound (M : ℕ) (good : ℕ → Bool) : ∀ (gs : List Gate) (k : ℕ) (S : List ℕ)
    (o : ℕ), gs.length ≤ k → (∀ g ∈ gs, GOk g) → good ((tabs M S gs).getD o 0) = true →
    reach M good k S = true := by
  intro gs
  induction gs with
  | nil =>
    intro k S o _ _ hgood
    apply reach_of_zero
    simp only [reach, List.any_eq_true]
    exact ⟨_, getD_mem_zero S o, hgood⟩
  | cons g gs ih =>
    intro k S o hk hok hgood
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by simp at hk; omega⟩
    have hg := hok g (by simp)
    set t := gt M g.op (g.inputs.map fun i => S.getD i 0) with ht
    have h1 : reach M good k' (S ++ [t]) = true :=
      ih k' (S ++ [t]) o (by simpa using hk) (fun g' hg' => hok g' (by simp [hg'])) hgood
    by_cases hin : t ∈ S
    · have e : reach M good k' (S ++ [t]) = reach M good k' S :=
        reach_congr M good k' _ _ (by intro x; simp only [List.mem_append, List.mem_singleton]
                                      constructor
                                      · rintro (h | rfl) <;> assumption
                                      · exact Or.inl)
      exact reach_mono M good k' S (e ▸ h1)
    · simp only [reach, Bool.or_eq_true, List.any_eq_true]
      exact Or.inr ⟨t, (mem_next M S t).2 ⟨gt_mem M S g hg, hin⟩, h1⟩

/-- A table equal to `tgt` on the points below `B`, with `tgt < 2 ^ B`. -/
theorem mod_eq_of_testBit (B t tgt : ℕ) (htgt : tgt < 2 ^ B)
    (h : ∀ p, p < B → t.testBit p = tgt.testBit p) : t % 2 ^ B = tgt := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow]
  by_cases hi : i < B
  · simp [hi, h i hi]
  · simp only [hi, decide_false, Bool.false_and]
    symm
    apply Nat.testBit_eq_false_of_lt
    exact lt_of_lt_of_le htgt (Nat.pow_le_pow_right (by norm_num) (by omega))

/-- The lower bound from a failed search. The wire tables `T0` of the inputs must give, at
each point `p < B`, the input `pt p`; `f` must take the value `tgt.testBit p` there, and every
input on which `f` is checked must be some `pt p`. -/
theorem lower_of_search (n B : ℕ) (f : (Fin n → Bool) → Bool) (T0 : List ℕ) (tgt k : ℕ)
    (htgt : tgt < 2 ^ B)
    (hpt : ∀ p, p < B → ∃ x : Fin n → Bool, List.ofFn x = T0.map (fun t => t.testBit p) ∧
      f x = tgt.testBit p)
    (hsearch : reach (2 ^ B - 1) (fun t => t % 2 ^ B == tgt) k T0 = false) :
    ¬ HasCircuitSize n f k := by
  rintro ⟨C, hC, hsize, hev⟩
  have hok : ∀ g ∈ C.gates, GOk g := by
    intro g hg
    obtain ⟨h1, h2⟩ := hC g hg
    refine ⟨?_, h2⟩
    simpa [Set.mem_insert_iff] using h1
  have hgood : (fun t => t % 2 ^ B == tgt) ((tabs (2 ^ B - 1) T0 C.gates).getD C.output 0)
      = true := by
    simp only [beq_iff_eq]
    apply mod_eq_of_testBit B _ tgt htgt
    intro p hp
    obtain ⟨x, hx, hfx⟩ := hpt p hp
    have hM : (2 ^ B - 1).testBit p = true := by
      rw [Nat.testBit_two_pow_sub_one]; simpa using hp
    have := hev x
    rw [hfx] at this
    rw [← this, Circuit.eval, Circuit.wires, hx, wires_tabs _ p hM _ _ hok,
      getD_map_testBit]
  have := reach_sound (2 ^ B - 1) (fun t => t % 2 ^ B == tgt) C.gates k T0 C.output hsize hok hgood
  rw [hsearch] at this
  exact absurd this (by decide)

end PEqualNP.Outside.L_meta_764_aux.TableSearch

/-! ---- ported from PEqualNP.MetaComplexity.Helpers.ExactMaj3 ---- -/

/-!
# Majority of three inputs has circuit size exactly four

Helper for `L100`. Upper bound: the circuit AND(x0, x1), OR(x0, x1), AND(that, x2), OR of the
two. Lower bound: the truth-table search of `Helpers.TableSearch`, run to depth three from the
tables of the three inputs (`170`, `204`, `240`), never meets the table of majority (`232`).
-/

namespace PEqualNP.Outside.L_meta_764_aux.ExactMaj3

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_764_aux.TableSearch

/-- Majority of three inputs. -/
def maj3 : (Fin 3 → Bool) → Bool :=
  fun x : Fin 3 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 0 && x 2)

/-- The four-gate circuit. -/
def maj3Circuit : Circuit :=
  ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.and, [4, 2]⟩, ⟨GateOp.or, [3, 5]⟩], 6⟩

theorem maj3_upper : HasCircuitSize 3 maj3 4 := by
  refine ⟨maj3Circuit, ?_, by decide, ?_⟩
  · intro g hg
    simp only [maj3Circuit, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl <;> simp
  · decide

/-- The search fails at depth three. -/
theorem maj3_search : reach (2 ^ 8 - 1) (fun t => t % 2 ^ 8 == 232) 3 [170, 204, 240] = false := by
  decide +kernel

theorem maj3_lower : ¬ HasCircuitSize 3 maj3 3 := by
  apply lower_of_search 3 8 maj3 [170, 204, 240] 232 3 (by norm_num) _ maj3_search
  have key : ∀ p, p < 8 → (List.ofFn fun i : Fin 3 => p.testBit i)
      = [170, 204, 240].map (fun t : ℕ => t.testBit p) ∧
      maj3 (fun i => p.testBit i) = Nat.testBit 232 p := by decide
  exact fun p hp => ⟨_, key p hp⟩

theorem hasCircuitSize_mono {n : ℕ} {f : (Fin n → Bool) → Bool} {s t : ℕ} (hst : s ≤ t)
    (h : HasCircuitSize n f s) : HasCircuitSize n f t := by
  obtain ⟨C, h1, h2, h3⟩ := h
  exact ⟨C, h1, le_trans h2 hst, h3⟩

theorem maj3_size (s : ℕ) : HasCircuitSize 3 maj3 s ↔ 4 ≤ s := by
  constructor
  · intro h
    by_contra hs
    exact maj3_lower (hasCircuitSize_mono (by omega) h)
  · intro h
    exact hasCircuitSize_mono h maj3_upper

end PEqualNP.Outside.L_meta_764_aux.ExactMaj3


/-! ## Part 2 — the instance data: a triangle plus a disjoint edge -/
namespace PEqualNP.Outside.L_meta_764_glue

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- The triangle's edge function on three inputs. -/
def tri : (Fin 3 → Bool) → Bool :=
  fun y : Fin 3 → Bool => (y 0 && y 1) || (y 1 && y 2) || (y 0 && y 2)

/-- The recorded function on five inputs. -/
def f5 : (Fin 5 → Bool) → Bool :=
  fun x : Fin 5 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 2 && x 4)

/-- `tri` is `L-meta-100`'s majority of three, verbatim. -/
theorem tri_eq_maj3 : tri = PEqualNP.Outside.L_meta_764_aux.ExactMaj3.maj3 := rfl

/-- **`L-meta-100` at the triangle**: exactly four gates, at every bound. -/
theorem tri_size (s : ℕ) : HasCircuitSize 3 tri s ↔ 4 ≤ s := by
  have h := PEqualNP.Outside.L_meta_764_aux.ExactMaj3.maj3_size s
  rw [← tri_eq_maj3] at h
  exact h

/-- The triangle's edge function is not constant: `L-meta-153`'s hypothesis. -/
theorem tri_nc : ∃ y y' : Fin 3 → Bool, tri y ≠ tri y' := by
  refine ⟨fun _ => false, fun _ => true, ?_⟩
  decide

/-- The recorded function is `L-meta-153`'s `(x 0 && x 1) || g (inputs 2 ..)` at `k = 3`. -/
theorem f5_pt : ∀ x : Fin 5 → Bool,
    f5 x = PEqualNP.Outside.L_meta_764_aux.RigidAnd.andOr 3 tri x := by
  decide

theorem f5_eq_andOr : f5 = PEqualNP.Outside.L_meta_764_aux.RigidAnd.andOr 3 tri :=
  funext f5_pt

/-- **The exact size is six**: `L-meta-153` at `k = 3` on top of `L-meta-100`. -/
theorem f5_exact (s : ℕ) : HasCircuitSize 5 f5 s ↔ 6 ≤ s := by
  have hrig := PEqualNP.Outside.L_meta_764_aux.RigidAnd.rigid_and 3 3 tri tri_nc
  constructor
  · intro h
    by_contra hs
    have hs5 : s ≤ 5 := by omega
    have h5 : HasCircuitSize 5 f5 5 :=
      PEqualNP.Outside.L_meta_764_aux.ExactMaj3.hasCircuitSize_mono hs5 h
    rw [f5_eq_andOr] at h5
    have h3 : HasCircuitSize 3 tri 3 := hrig.1 h5
    have h4 := (tri_size 3).1 h3
    omega
  · intro h
    have h4 : HasCircuitSize 3 tri 4 := (tri_size 4).2 (le_refl 4)
    have hu : HasCircuitSize (2 + 3) (PEqualNP.Outside.L_meta_764_aux.RigidAnd.andOr 3 tri)
        (4 + 2) := PEqualNP.Outside.L_meta_764_aux.RigidAnd.rigid_up 3 4 tri tri_nc h4
    rw [← f5_eq_andOr] at hu
    exact PEqualNP.Outside.L_meta_764_aux.ExactMaj3.hasCircuitSize_mono (by omega) hu

end PEqualNP.Outside.L_meta_764_glue

/-! ## Part 3 — the recorded statement -/

namespace PEqualNP.Outside

/-- **L-meta-764**: the edge function of a triangle and a disjoint edge has circuits with `s`
gates exactly when `6 ≤ s`. -/
theorem L_meta_764 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 2 && x 4)) s ↔ 6 ≤ s :=
  fun s => PEqualNP.Outside.L_meta_764_glue.f5_exact s

end PEqualNP.Outside
