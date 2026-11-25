import Mathlib
import PEqualNP.Defs

/-!
# The 6-by-4 bipartite graph with mask 13124385 needs at least eleven AND/OR gates

Two disjoint five-vertex paths, ends on the same side: the six left vertices `0 1 2` and `3 4 5`
carry the paths `0 - v0 - 2 - v1 - 1` and `3 - v2 - 5 - v3 - 4`, i.e. the eight joined pairs
`(0,0) (2,0) (2,1) (1,1)` and `(3,2) (5,2) (5,3) (4,3)`.

The lower half is a closure-and-compression argument: a representing circuit turns into a `build`
chain over the packed truth tables, `compress` shrinks the chain to a `live` set inside the ten
input wires, and no `live` set of at most eleven wires survives ten steps.

Truth tables are packed into a `BitVec 256`: one hundred and twenty-eight cut pairs of two halves,
bits 0-127 the sixteen false cells and bits 128-255 the eight true cells, each position a
(negative, positive) pair.  Sixteen times eight is exactly one hundred and twenty-eight, so no
position repeats.  The goal is `(-1) ++ (0)`.
-/

namespace PEqualNP.Outside.L_meta_8299

section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

theorem compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero =>
    exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

theorem live_card {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : s.card ≤ k + 1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

theorem live_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩

theorem first_live {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal (k + 1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, tail⟩
      · exact .inl done
      · exact .inr ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, Or.inl tail⟩
    · exact .inr step

end Live

abbrev W := BitVec 256

def ops (x y : W) : List W := [x &&& y, x ||| y]

def sep (x : W) : BitVec 128 := ((x >>> 128) &&& ~~~x).setWidth 128

def cuts (ws : List W) : BitVec 128 := ws.foldr (fun w v => sep w ||| v) 0

def goal : W := (-1 : BitVec 128) ++ (0 : BitVec 128)

def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

def rawInputs : List W :=
  [0x0000000000000000000000000000ffff00070007000700070007000700070007, 0x000000000000000000000000ffff000000380038003800380038003800380038, 0x0000000000000000ffffffff0000000000c000c000c000c000c000c000c000c0, 0x000000000000ffff000000000000000007000700070007000700070007000700, 0x00000000ffff0000000000000000000038003800380038003800380038003800, 0xffffffff000000000000000000000000c000c000c000c000c000c000c000c000, 0x00000000000000000000ffff0000ffff49084908490849084908490849084908, 0x0000000000000000ffff0000ffff000092019201920192019201920192019201, 0x0000ffff0000ffff000000000000000020522052205220522052205220522052, 0xffff0000ffff0000000000000000000004a404a404a404a404a404a404a404a4]

def inputs : List W := rawInputs

theorem pick_one {α : Type} {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a, rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, rest), hm, rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

theorem pick_two {α : Type} {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b, r), hm, rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r, .inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_,
          (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b, r), hm, rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b, a, r), hm, rfl⟩))

abbrev basicOps (a b : W) : Finset W := (ops a b).toFinset

def differs (i : Fin 128) (w : W) : Prop :=
  w.getLsbD (128 + i.val) = true ∧ w.getLsbD i.val = false

theorem ops_differs (i : Fin 128) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  unfold differs at hd ⊢
  rcases hz with rfl | rfl <;> revert hd <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or] <;>
    cases a.getLsbD (128 + i.val) <;> cases a.getLsbD i.val <;>
    cases b.getLsbD (128 + i.val) <;> cases b.getLsbD i.val <;> simp

theorem goal_differs : ∀ i : Fin 128, differs i goal := by
  unfold differs
  decide

theorem cuts_spec (ws : List W) (i : Fin 128) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have hi : i.val < 256 := by omega
    simp [sep, i.isLt, differs, hi, Nat.add_comm]

theorem cuts_full {k : ℕ} {ws : List W} (h : live basicOps goal k ws.toFinset) :
    cuts ws = -1 := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (goal_differs ⟨j, hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 128)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp [basicOps, ops, BitVec.and_comm, BitVec.or_comm]

def keepChoices (a b : W) (r : List W) : List (List W) := [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept {ws r : List W} {a b : W} {needed : Finset W}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

theorem singleton_list {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def possible (w : List W) (z : W) : Bool :=
  z == 0 || z == BitVec.allOnes 256 || w.any (fun u => z == u ||
    w.any (fun v => z == (u &&& v) || z == (u ||| v)))

private def bit (k : Fin 256) (z : W) : Bool := z[k.val]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 256) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

private theorem read_wire (w : List W) (i : ℕ) : w.getD i 0 = 0 ∨ w.getD i 0 ∈ w := by
  by_cases h : i < w.length
  · exact Or.inr (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_gt h)]

private theorem atom {ws : List W} {x : W} (hx : x = 0 ∨ x ∈ ws) : possible ws x := by
  rcases hx with rfl | hx
  · simp [possible]
  · simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    exact .inr ⟨x, hx, .inl rfl⟩

private theorem pair {ws : List W} {x y : W} (hx : x = 0 ∨ x ∈ ws) (hy : y = 0 ∨ y ∈ ws) :
    possible ws (x &&& y) ∧ possible ws (x ||| y) := by
  rcases hx with rfl | hx
  · simpa [possible] using atom hy
  rcases hy with rfl | hy
  · simpa [possible] using atom (.inr hx)
  · simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    constructor
    · exact .inr ⟨x, hx, .inr ⟨y, hy, .inl rfl⟩⟩
    · exact .inr ⟨x, hx, .inr ⟨y, hy, .inr rfl⟩⟩

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def legal (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

set_option maxRecDepth 2000 in
private theorem gate_table (w ws : List W) (hw : w ⊆ ws) (g : Gate) (hg : legal g) :
    ∃ z, possible ws z ∧ ∀ k, step (w.map (bit k)) g = (w ++ [z]).map (bit k) := by
  have mem (i : ℕ) : w.getD i 0 = 0 ∨ w.getD i 0 ∈ ws :=
    (read_wire w i).imp_right (fun h => hw h)
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  change op = .and ∨ op = .or at hop
  change args.length ≤ 2 at hlen
  cases args with
  | nil =>
    rcases hop with rfl | rfl
    · exact ⟨BitVec.allOnes 256, by simp [possible], by simp [step, GateOp.eval, bit]; decide⟩
    · exact ⟨0, by simp [possible], by simp [step, GateOp.eval, bit]⟩
  | cons i tail =>
    cases tail with
    | nil =>
      rcases hop with rfl | rfl
      · exact ⟨_, atom (mem i),
          by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval]⟩
      · exact ⟨_, atom (mem i),
          by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval]⟩
    | cons j tail =>
      cases tail with
      | cons => simp at hlen
      | nil =>
        rcases hop with rfl | rfl
        · exact ⟨_, (pair (mem i) (mem j)).1,
            by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit]⟩
        · exact ⟨_, (pair (mem i) (mem j)).2,
            by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit]⟩

def represents (available : Finset W) (w : List W) : Prop :=
  ∀ u ∈ w, u = 0 ∨ u = BitVec.allOnes 256 ∨ u ∈ available

theorem classify {available : Finset W} {ws : List W} (hw : represents available ws)
    {z : W} (hz : possible ws z) :
    z = 0 ∨ z = BitVec.allOnes 256 ∨ z ∈ available ∨
      ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧ z ∈ basicOps a b := by
  have lift {t : W} (h : t = 0 ∨ t = BitVec.allOnes 256 ∨ t ∈ available) :
      t = 0 ∨ t = BitVec.allOnes 256 ∨ t ∈ available ∨
        ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧ t ∈ basicOps a b :=
    h.imp_right (Or.imp_right Or.inl)
  simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at hz
  rcases hz with ((h | h) | ⟨x, hx, h | ⟨y, hy, h | h⟩⟩)
  · exact .inl h
  · exact .inr (.inl h)
  · subst z; exact lift (hw _ hx)
  · subst z
    rcases hw _ hx with rfl | rfl | hu
    · left; simp
    · rw [BitVec.allOnes_and]; exact lift (hw _ hy)
    rcases hw _ hy with rfl | rfl | hv
    · left; simp
    · rw [BitVec.and_allOnes]; exact .inr (.inr (.inl hu))
    by_cases h : x = y
    · subst h; rw [BitVec.and_self]; exact .inr (.inr (.inl hu))
    · exact .inr (.inr (.inr ⟨x, hu, y, hv, h, by simp [basicOps, ops]⟩))
  · subst z
    rcases hw _ hx with rfl | rfl | hu
    · rw [show (0 : W) ||| y = y by ext i hi; simp]; exact lift (hw _ hy)
    · right; left; exact BitVec.allOnes_or
    rcases hw _ hy with rfl | rfl | hv
    · rw [show x ||| (0 : W) = x by ext i hi; simp]; exact .inr (.inr (.inl hu))
    · right; left; exact BitVec.or_allOnes
    by_cases h : x = y
    · subst h; rw [BitVec.or_self]; exact .inr (.inr (.inl hu))
    · exact .inr (.inr (.inr ⟨x, hu, y, hv, h, by simp [basicOps, ops]⟩))

private theorem compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W) (av : Finset W) (hw : represents av w)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k goal) :
    build basicOps goal gs.length av := by
  induction gs generalizing w av with
  | nil =>
    have hval : w.getD out 0 = goal := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i, hi⟩
    have hr := read_wire w out
    rw [hval] at hr
    rcases hr with hz | hm
    · exact False.elim ((by decide : goal ≠ (0 : W)) hz)
    · rcases hw _ hm with h | h | h
      · exact False.elim ((by decide : goal ≠ (0 : W)) h)
      · exact False.elim ((by decide : goal ≠ BitVec.allOnes 256) h)
      · exact h
  | cons g gs ih =>
    obtain ⟨z, hz, hstep⟩ := gate_table w w (fun _ h => h) g (hg g (by simp))
    have fn := ih (fun g' h => hg g' (by simp [h])) (w ++ [z])
    have he' : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k goal := by
      intro k; simpa only [List.foldl_cons, hstep] using he k
    have appendOK (h : z = 0 ∨ z = BitVec.allOnes 256 ∨ z ∈ av) : represents av (w ++ [z]) := by
      intro u hu
      rcases List.mem_append.mp hu with old | fresh
      · exact hw _ old
      · have eq : u = z := List.mem_singleton.mp fresh
        exact eq ▸ h
    rcases classify hw hz with h | h | h | ⟨a, ha, b, hb, hab, hop⟩
    · exact Or.inl (fn av (appendOK (.inl h)) he')
    · exact Or.inl (fn av (appendOK (.inr (.inl h))) he')
    · exact Or.inl (fn av (appendOK (.inr (.inr h))) he')
    · refine Or.inr ⟨a, ha, b, hb, hab, z, hop, fn (insert z av) ?_ he'⟩
      intro u hu
      rcases List.mem_append.mp hu with hu | hu
      · exact (hw _ hu).imp_right (Or.imp_right (Finset.mem_insert_of_mem ·))
      · simp_all

def dispatch (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) : Bool :=
  let base := cuts r
  (ops a b).any fun w =>
    let v := sep w ||| base
    ((v == -1) && next extra (w :: r)) ||
    ((extra != 0) && (((v ||| sep a == -1) && next (extra - 1) (w :: a :: r)) ||
                       ((v ||| sep b == -1) && next (extra - 1) (w :: b :: r)))) ||
    ((extra ≥ 2) && (v ||| sep a ||| sep b == -1) && next (extra - 2) (w :: a :: b :: r))

def optimized : ℕ → ℕ → List W → Bool
  | 0, _, ws => ws == [goal]
  | k + 1, extra, ws => ws == [goal] ||
    (pairs ws).any (fun (a, b, r) => dispatch extra (optimized k) a b r)

theorem dispatch_complete {k extra : ℕ} {a b z : W} {r kept : List W}
    (next : ℕ → List W → Bool)
    (hz : z ∈ basicOps a b) (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts (z :: kept) = -1) (ht : next (k - kept.length) (z :: kept) = true) :
    dispatch extra next a b r = true := by
  apply List.any_eq_true.mpr
  refine ⟨z, List.mem_toFinset.mp hz, ?_⟩
  simp [keepChoices] at hk
  rcases hk with rfl | rfl | rfl | rfl <;>
    simp only [cuts, List.foldr_cons] at hc ⊢ <;>
    (try simp only [List.length_cons] at *) <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne]
  · left; left; exact ⟨hc, by convert ht using 2; omega⟩
  · left; right; exact ⟨by omega, .inl ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · left; right; exact ⟨by omega, .inr ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · right; exact ⟨⟨by omega, by convert hc using 1; ac_rfl⟩, by convert ht using 2; omega⟩

theorem optimized_complete (n : ℕ) (ws : List W) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n + 1) (h : live basicOps goal n ws.toFinset) :
    optimized n extra ws = true := by
  induction n generalizing ws extra with
  | zero => simp [optimized, singleton_list hn h]
  | succ k ih =>
    rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · simp [optimized, singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : W} (perm : ws.Perm (a :: b :: r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          dispatch extra (optimized k) a b r = true := by
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live basicOps goal k (z :: kept).toFinset := by
          simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        apply dispatch_complete (k := k) (extra := extra) (optimized k) hop hk (by omega) (by omega) (cuts_full hl)
        apply ih _ _ hnd _ hl
        simp; omega
      simp only [optimized, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs hz⟩
      · exact ⟨(b, a, r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩
def A : Fin 6 → Fin 4 → Bool := fun (u : Fin 6) (v : Fin 4) => (13124385 : ℕ).testBit (4 * u.val + v.val)

def posL : List (Fin 6 × Fin 4) :=
  [(0, 0), (1, 1), (2, 0), (2, 1), (3, 2), (4, 3), (5, 2), (5, 3)]

def negL : List (Fin 6 × Fin 4) :=
  [(0, 1), (0, 2), (0, 3), (1, 0), (1, 2), (1, 3), (2, 2), (2, 3), (3, 0), (3, 1), (3, 3), (4, 0), (4, 1), (4, 2), (5, 0), (5, 1)]

def samp (k : Fin 256) : Fin 6 × Fin 4 :=
  if k.val < 128 then negL.getD (k.val % 16) (0, 0)
  else posL.getD ((k.val - 128) / 16) (0, 0)

theorem input_rows : ∀ k : Fin 256,
    rawInputs.map (bit k) = PEqualNP.Represents.oneEach (samp k).1 (samp k).2 := by
  decide +kernel

theorem goal_rows : ∀ k : Fin 256, bit k goal = A (samp k).1 (samp k).2 := by
  decide +kernel

theorem rows_eval (C : Circuit) (hr : PEqualNP.Represents.Represents A C) (k : Fin 256) :
    (C.gates.foldl step (rawInputs.map (bit k))).getD C.output false = bit k goal := by
  rw [input_rows k, goal_rows k]
  exact hr (samp k).1 (samp k).2

theorem initial_rep : represents inputs.toFinset rawInputs := by
  intro u hu
  exact .inr (.inr (List.mem_toFinset.mpr hu))

theorem get_build (C : Circuit) (hg : Monotone2 C) (hr : PEqualNP.Represents.Represents A C) :
    build basicOps goal C.gates.length inputs.toFinset :=
  compile C.gates C.output hg rawInputs inputs.toFinset initial_rep (rows_eval C hr)

theorem extend_live {m n : ℕ} {s : Finset W} (le : m ≤ n) (h : live basicOps goal m s) :
    live basicOps goal n s := by
  induction le with
  | refl => exact h
  | step _ ih => exact Or.inl ih

theorem inputs_nodup : inputs.Nodup := by decide +kernel

def frontOK (l : List W) : Bool :=
  decide (11 < l.length) || decide (l = inputs) || !(optimized 10 (11 - l.length) l)
theorem all_of_chunks {β : Type} (F : β → Bool) (n : ℕ) : ∀ (m : ℕ) (L : List β), L.length ≤ n * m →
    (∀ j < m, ((L.drop (n * j)).take n).all F = true) → L.all F = true := by
  intro m
  induction m with
  | zero =>
    intro L hl _
    have h0 : L = [] := List.eq_nil_of_length_eq_zero (by simpa using hl)
    simp [h0]
  | succ m ih =>
    intro L hl h
    rw [← List.take_append_drop n L, List.all_append, Bool.and_eq_true]
    refine ⟨by simpa using h 0 (by omega), ih (L.drop n) ?_ ?_⟩
    · rw [List.length_drop]
      rw [Nat.mul_succ] at hl
      generalize n * m = t at *
      omega
    · intro j hj
      have e : List.drop (n * j) (List.drop n L) = List.drop (n * (j + 1)) L := by
        rw [List.drop_drop]
        congr 1
        ring
      rw [e]
      exact h (j + 1) (by omega)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem chunk_0 : (((inputs.sublists).drop (16 * 0)).take 16).all frontOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem chunk_1 : (((inputs.sublists).drop (16 * 1)).take 16).all frontOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem chunk_2 : (((inputs.sublists).drop (16 * 2)).take 16).all frontOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem chunk_3 : (((inputs.sublists).drop (16 * 3)).take 16).all frontOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem chunk_4 : (((inputs.sublists).drop (16 * 4)).take 16).all frontOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem chunk_5 : (((inputs.sublists).drop (16 * 5)).take 16).all frontOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem chunk_6 : (((inputs.sublists).drop (16 * 6)).take 16).all frontOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem chunk_7 : (((inputs.sublists).drop (16 * 7)).take 16).all frontOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem chunk_8 : (((inputs.sublists).drop (16 * 8)).take 16).all frontOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem chunk_9 : (((inputs.sublists).drop (16 * 9)).take 16).all frontOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem chunk_10 : (((inputs.sublists).drop (16 * 10)).take 16).all frontOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem chunk_11 : (((inputs.sublists).drop (16 * 11)).take 16).all frontOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem chunk_12 : (((inputs.sublists).drop (16 * 12)).take 16).all frontOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem chunk_13 : (((inputs.sublists).drop (16 * 13)).take 16).all frontOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem chunk_14 : (((inputs.sublists).drop (16 * 14)).take 16).all frontOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem chunk_15 : (((inputs.sublists).drop (16 * 15)).take 16).all frontOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem chunk_16 : (((inputs.sublists).drop (16 * 16)).take 16).all frontOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem chunk_17 : (((inputs.sublists).drop (16 * 17)).take 16).all frontOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem chunk_18 : (((inputs.sublists).drop (16 * 18)).take 16).all frontOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem chunk_19 : (((inputs.sublists).drop (16 * 19)).take 16).all frontOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem chunk_20 : (((inputs.sublists).drop (16 * 20)).take 16).all frontOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem chunk_21 : (((inputs.sublists).drop (16 * 21)).take 16).all frontOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem chunk_22 : (((inputs.sublists).drop (16 * 22)).take 16).all frontOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem chunk_23 : (((inputs.sublists).drop (16 * 23)).take 16).all frontOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem chunk_24 : (((inputs.sublists).drop (16 * 24)).take 16).all frontOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem chunk_25 : (((inputs.sublists).drop (16 * 25)).take 16).all frontOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem chunk_26 : (((inputs.sublists).drop (16 * 26)).take 16).all frontOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem chunk_27 : (((inputs.sublists).drop (16 * 27)).take 16).all frontOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem chunk_28 : (((inputs.sublists).drop (16 * 28)).take 16).all frontOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem chunk_29 : (((inputs.sublists).drop (16 * 29)).take 16).all frontOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem chunk_30 : (((inputs.sublists).drop (16 * 30)).take 16).all frontOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem chunk_31 : (((inputs.sublists).drop (16 * 31)).take 16).all frontOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem chunk_32 : (((inputs.sublists).drop (16 * 32)).take 16).all frontOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem chunk_33 : (((inputs.sublists).drop (16 * 33)).take 16).all frontOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem chunk_34 : (((inputs.sublists).drop (16 * 34)).take 16).all frontOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem chunk_35 : (((inputs.sublists).drop (16 * 35)).take 16).all frontOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem chunk_36 : (((inputs.sublists).drop (16 * 36)).take 16).all frontOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem chunk_37 : (((inputs.sublists).drop (16 * 37)).take 16).all frontOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem chunk_38 : (((inputs.sublists).drop (16 * 38)).take 16).all frontOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem chunk_39 : (((inputs.sublists).drop (16 * 39)).take 16).all frontOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem chunk_40 : (((inputs.sublists).drop (16 * 40)).take 16).all frontOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem chunk_41 : (((inputs.sublists).drop (16 * 41)).take 16).all frontOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem chunk_42 : (((inputs.sublists).drop (16 * 42)).take 16).all frontOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem chunk_43 : (((inputs.sublists).drop (16 * 43)).take 16).all frontOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem chunk_44 : (((inputs.sublists).drop (16 * 44)).take 16).all frontOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem chunk_45 : (((inputs.sublists).drop (16 * 45)).take 16).all frontOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem chunk_46 : (((inputs.sublists).drop (16 * 46)).take 16).all frontOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem chunk_47 : (((inputs.sublists).drop (16 * 47)).take 16).all frontOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem chunk_48 : (((inputs.sublists).drop (16 * 48)).take 16).all frontOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem chunk_49 : (((inputs.sublists).drop (16 * 49)).take 16).all frontOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem chunk_50 : (((inputs.sublists).drop (16 * 50)).take 16).all frontOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem chunk_51 : (((inputs.sublists).drop (16 * 51)).take 16).all frontOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem chunk_52 : (((inputs.sublists).drop (16 * 52)).take 16).all frontOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem chunk_53 : (((inputs.sublists).drop (16 * 53)).take 16).all frontOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem chunk_54 : (((inputs.sublists).drop (16 * 54)).take 16).all frontOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem chunk_55 : (((inputs.sublists).drop (16 * 55)).take 16).all frontOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem chunk_56 : (((inputs.sublists).drop (16 * 56)).take 16).all frontOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem chunk_57 : (((inputs.sublists).drop (16 * 57)).take 16).all frontOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem chunk_58 : (((inputs.sublists).drop (16 * 58)).take 16).all frontOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem chunk_59 : (((inputs.sublists).drop (16 * 59)).take 16).all frontOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem chunk_60 : (((inputs.sublists).drop (16 * 60)).take 16).all frontOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem chunk_61 : (((inputs.sublists).drop (16 * 61)).take 16).all frontOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem chunk_62 : (((inputs.sublists).drop (16 * 62)).take 16).all frontOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem chunk_63 : (((inputs.sublists).drop (16 * 63)).take 16).all frontOK = true := by
  decide +kernel
theorem sublists_ok : inputs.sublists.all frontOK = true :=
  all_of_chunks frontOK 16 64 inputs.sublists (by decide +kernel) (fun j hj => by
    interval_cases j
    exacts [chunk_0, chunk_1, chunk_2, chunk_3, chunk_4, chunk_5, chunk_6, chunk_7, chunk_8, chunk_9, chunk_10, chunk_11, chunk_12, chunk_13, chunk_14, chunk_15, chunk_16, chunk_17, chunk_18, chunk_19, chunk_20, chunk_21, chunk_22, chunk_23, chunk_24, chunk_25, chunk_26, chunk_27, chunk_28, chunk_29, chunk_30, chunk_31, chunk_32, chunk_33, chunk_34, chunk_35, chunk_36, chunk_37, chunk_38, chunk_39, chunk_40, chunk_41, chunk_42, chunk_43, chunk_44, chunk_45, chunk_46, chunk_47, chunk_48, chunk_49, chunk_50, chunk_51, chunk_52, chunk_53, chunk_54, chunk_55, chunk_56, chunk_57, chunk_58, chunk_59, chunk_60, chunk_61, chunk_62, chunk_63])

def pairOK (p : W × W × List W) : Bool := !(dispatch 1 (optimized 9) p.1 p.2.1 p.2.2)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem pairchunk_0 : (((pairs inputs).drop (1 * 0)).take 1).all pairOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem pairchunk_1 : (((pairs inputs).drop (1 * 1)).take 1).all pairOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem pairchunk_2 : (((pairs inputs).drop (1 * 2)).take 1).all pairOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem pairchunk_3 : (((pairs inputs).drop (1 * 3)).take 1).all pairOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem pairchunk_4 : (((pairs inputs).drop (1 * 4)).take 1).all pairOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem pairchunk_5 : (((pairs inputs).drop (1 * 5)).take 1).all pairOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem pairchunk_6 : (((pairs inputs).drop (1 * 6)).take 1).all pairOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem pairchunk_7 : (((pairs inputs).drop (1 * 7)).take 1).all pairOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem pairchunk_8 : (((pairs inputs).drop (1 * 8)).take 1).all pairOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem pairchunk_9 : (((pairs inputs).drop (1 * 9)).take 1).all pairOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem pairchunk_10 : (((pairs inputs).drop (1 * 10)).take 1).all pairOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem pairchunk_11 : (((pairs inputs).drop (1 * 11)).take 1).all pairOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem pairchunk_12 : (((pairs inputs).drop (1 * 12)).take 1).all pairOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem pairchunk_13 : (((pairs inputs).drop (1 * 13)).take 1).all pairOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem pairchunk_14 : (((pairs inputs).drop (1 * 14)).take 1).all pairOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem pairchunk_15 : (((pairs inputs).drop (1 * 15)).take 1).all pairOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem pairchunk_16 : (((pairs inputs).drop (1 * 16)).take 1).all pairOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem pairchunk_17 : (((pairs inputs).drop (1 * 17)).take 1).all pairOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem pairchunk_18 : (((pairs inputs).drop (1 * 18)).take 1).all pairOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem pairchunk_19 : (((pairs inputs).drop (1 * 19)).take 1).all pairOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem pairchunk_20 : (((pairs inputs).drop (1 * 20)).take 1).all pairOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem pairchunk_21 : (((pairs inputs).drop (1 * 21)).take 1).all pairOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem pairchunk_22 : (((pairs inputs).drop (1 * 22)).take 1).all pairOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem pairchunk_23 : (((pairs inputs).drop (1 * 23)).take 1).all pairOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem pairchunk_24 : (((pairs inputs).drop (1 * 24)).take 1).all pairOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem pairchunk_25 : (((pairs inputs).drop (1 * 25)).take 1).all pairOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem pairchunk_26 : (((pairs inputs).drop (1 * 26)).take 1).all pairOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem pairchunk_27 : (((pairs inputs).drop (1 * 27)).take 1).all pairOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem pairchunk_28 : (((pairs inputs).drop (1 * 28)).take 1).all pairOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem pairchunk_29 : (((pairs inputs).drop (1 * 29)).take 1).all pairOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem pairchunk_30 : (((pairs inputs).drop (1 * 30)).take 1).all pairOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem pairchunk_31 : (((pairs inputs).drop (1 * 31)).take 1).all pairOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem pairchunk_32 : (((pairs inputs).drop (1 * 32)).take 1).all pairOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem pairchunk_33 : (((pairs inputs).drop (1 * 33)).take 1).all pairOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem pairchunk_34 : (((pairs inputs).drop (1 * 34)).take 1).all pairOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem pairchunk_35 : (((pairs inputs).drop (1 * 35)).take 1).all pairOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem pairchunk_36 : (((pairs inputs).drop (1 * 36)).take 1).all pairOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem pairchunk_37 : (((pairs inputs).drop (1 * 37)).take 1).all pairOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem pairchunk_38 : (((pairs inputs).drop (1 * 38)).take 1).all pairOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem pairchunk_39 : (((pairs inputs).drop (1 * 39)).take 1).all pairOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem pairchunk_40 : (((pairs inputs).drop (1 * 40)).take 1).all pairOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem pairchunk_41 : (((pairs inputs).drop (1 * 41)).take 1).all pairOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem pairchunk_42 : (((pairs inputs).drop (1 * 42)).take 1).all pairOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem pairchunk_43 : (((pairs inputs).drop (1 * 43)).take 1).all pairOK = true := by
  decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem pairchunk_44 : (((pairs inputs).drop (1 * 44)).take 1).all pairOK = true := by
  decide +kernel
theorem pairs_ok : (pairs inputs).all pairOK = true :=
  all_of_chunks pairOK 1 45 (pairs inputs) (by decide +kernel) (fun j hj => by
    interval_cases j
    exacts [pairchunk_0, pairchunk_1, pairchunk_2, pairchunk_3, pairchunk_4, pairchunk_5, pairchunk_6, pairchunk_7, pairchunk_8, pairchunk_9, pairchunk_10, pairchunk_11, pairchunk_12, pairchunk_13, pairchunk_14, pairchunk_15, pairchunk_16, pairchunk_17, pairchunk_18, pairchunk_19, pairchunk_20, pairchunk_21, pairchunk_22, pairchunk_23, pairchunk_24, pairchunk_25, pairchunk_26, pairchunk_27, pairchunk_28, pairchunk_29, pairchunk_30, pairchunk_31, pairchunk_32, pairchunk_33, pairchunk_34, pairchunk_35, pairchunk_36, pairchunk_37, pairchunk_38, pairchunk_39, pairchunk_40, pairchunk_41, pairchunk_42, pairchunk_43, pairchunk_44])

theorem full_search : optimized 10 1 inputs = false := by
  have hp := List.all_eq_true.mp pairs_ok
  show (inputs == [goal] || (pairs inputs).any (fun (a, b, r) => dispatch 1 (optimized 9) a b r)) = false
  rw [Bool.or_eq_false_iff]
  refine ⟨by decide +kernel, ?_⟩
  rw [List.any_eq_false]
  rintro ⟨a, b, r⟩ hm
  have hx := hp _ hm
  simpa [pairOK] using hx

theorem len_one : 11 - inputs.length = 1 := by decide +kernel

theorem no_small (C : Circuit) (hm : Monotone2 C) (hs : C.size ≤ 10)
    (hr : PEqualNP.Represents.Represents A C) : False := by
  obtain ⟨S, hsub, hl⟩ := compress (get_build C hm hr)
  have hl3 : live basicOps goal 10 S := extend_live hs hl
  let l := inputs.filter (fun w => decide (w ∈ S))
  have hlS : l.toFinset = S := by
    ext v
    simp only [l, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨List.mem_toFinset.mp (hsub h), h⟩
  have hnd : l.Nodup := inputs_nodup.filter _
  have hcard := live_card hl3
  rw [← hlS, List.toFinset_card_of_nodup hnd] at hcard
  have hsearch := optimized_complete 10 l (11 - l.length) hnd (by omega) (hlS ▸ hl3)
  have hmem : l ∈ inputs.sublists := List.mem_sublists.mpr List.filter_sublist
  have hrow := List.all_eq_true.mp sublists_ok l hmem
  simp only [frontOK] at hrow
  have h4 : decide (11 < l.length) = false := by simp; omega
  rw [h4, hsearch] at hrow
  have hli : l = inputs := by simpa using hrow
  rw [hli, len_one, full_search] at hsearch
  exact Bool.noConfusion hsearch

end PEqualNP.Outside.L_meta_8299

theorem PEqualNP.Outside.L_meta_8299 :
    ¬ PEqualNP.Represents.RepSizeAtMost
      (fun (u : Fin 6) (v : Fin 4) => (13124385 : ℕ).testBit (4 * u.val + v.val)) 10 := by
  rintro ⟨C, hm, hs, hr⟩
  exact PEqualNP.Outside.L_meta_8299.no_small C hm hs hr
