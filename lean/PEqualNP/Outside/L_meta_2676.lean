import PEqualNP.Defs

/-!
# L-meta-2676 — the implicant lift never raises read

The lift replaces the OR gate `j` (reading `u` and `t`) by a copy of `u`, and ORs the circuit's
output with the wire `t` at the top.  Read vectors only shrink under the replacement; the vectors
lost are exactly those whose proof tree enters gate `j` through `t`, and such a tree's `t`-subtree
has a count vector below the lost one and is still available at wire `t`, which the new top gate
reads.  Hence a good vector survives.

The invariant (`Rel`): at every wire `w`, every vector available before the change either is
available at `w` after it, or dominates a vector available at `t` before the change.
-/

namespace PEqualNP.Outside.ReadK2676

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadK

variable {S : List ℕ} {k : ℕ}

/-! ## §1 Entrywise order on count vectors -/

/-- `VecLe v u`: `v` is entrywise at most `u` (positions past the end read `0`). -/
def VecLe (v u : List ℕ) : Prop := ∀ i, v.getD i 0 ≤ u.getD i 0

theorem VecLe.refl (v : List ℕ) : VecLe v v := fun _ => le_rfl

theorem VecLe.trans {a b c : List ℕ} (h1 : VecLe a b) (h2 : VecLe b c) : VecLe a c :=
  fun i => le_trans (h1 i) (h2 i)

/-! ## §2 `capAdd`: length, entries, and domination -/

theorem capAdd_length {u v : List ℕ} {m : ℕ} (hu : u.length = m) (hv : v.length = m) :
    (capAdd k u v).length = m := by
  simp only [capAdd, List.length_zipWith, hu, hv, Nat.min_self]

theorem capAdd_getD {u v : List ℕ} {m : ℕ} (hu : u.length = m) (hv : v.length = m) (i : ℕ) :
    (capAdd k u v).getD i 0 = min (u.getD i 0 + v.getD i 0) (k + 1) := by
  rcases lt_or_ge i m with hi | hi
  · have h1 : i < u.length := hu ▸ hi
    have h2 : i < v.length := hv ▸ hi
    have h3 : i < (capAdd k u v).length := by rw [capAdd_length hu hv]; exact hi
    rw [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2,
      List.getD_eq_getElem _ _ h3]
    simp only [capAdd, List.getElem_zipWith]
  · have h1 : u.length ≤ i := hu ▸ hi
    have h2 : v.length ≤ i := hv ▸ hi
    have h3 : (capAdd k u v).length ≤ i := by rw [capAdd_length hu hv]; exact hi
    rw [List.getD_eq_default _ _ h1, List.getD_eq_default _ _ h2,
      List.getD_eq_default _ _ h3]
    simp

/-- Every entry of `capAdd k u v` is at most `k + 1`. -/
theorem mem_capAdd_bound {u v : List ℕ} {a : ℕ} (ha : a ∈ capAdd k u v) : a ≤ k + 1 := by
  rw [List.mem_iff_getElem?] at ha
  obtain ⟨i, hi⟩ := ha
  rw [capAdd, List.getElem?_zipWith] at hi
  cases h1 : u[i]? with
  | none => rw [h1] at hi; simp at hi
  | some b =>
      cases h2 : v[i]? with
      | none => rw [h1, h2] at hi; simp at hi
      | some c =>
          rw [h1, h2] at hi
          simp only [Option.some.injEq] at hi
          rw [← hi]
          exact Nat.min_le_right _ _

/-! ## §3 The invariant on one vector and on a set -/

/-- The invariant on one count vector: right length, every entry capped at `k + 1`. -/
def OkVec (S : List ℕ) (k : ℕ) (v : List ℕ) : Prop := v.length = S.length ∧ ∀ a ∈ v, a ≤ k + 1

/-- The invariant on a set of vectors. -/
def OkSet (S : List ℕ) (k : ℕ) (A : List (List ℕ)) : Prop := ∀ v ∈ A, OkVec S k v

theorem OkVec.getD_le {v : List ℕ} (h : OkVec S k v) (i : ℕ) : v.getD i 0 ≤ k + 1 := by
  rcases lt_or_ge i v.length with hi | hi
  · rw [List.getD_eq_getElem _ _ hi]
    exact h.2 _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ hi]
    exact Nat.zero_le _

theorem okVec_capAdd {u v : List ℕ} (hu : OkVec S k u) (hv : OkVec S k v) :
    OkVec S k (capAdd k u v) :=
  ⟨capAdd_length hu.1 hv.1, fun _ ha => mem_capAdd_bound ha⟩

theorem okVec_zero : OkVec S k (S.map fun _ => 0) := by
  refine ⟨by simp, ?_⟩
  intro a ha
  obtain ⟨j, _, hj⟩ := List.getElem_of_mem ha
  rw [← hj, List.getElem_map]
  exact Nat.zero_le _

theorem okSet_leafVectors (i : ℕ) : OkSet S k (leafVectors S k i) := by
  intro v hv
  unfold leafVectors at hv
  by_cases h : i ∈ S
  · rw [if_pos h, List.mem_singleton] at hv
    rw [hv]
    refine ⟨by simp, ?_⟩
    intro a ha
    obtain ⟨j, _, hj⟩ := List.getElem_of_mem ha
    rw [← hj, List.getElem_map]
    split
    · exact Nat.min_le_right _ _
    · exact Nat.zero_le _
  · rw [if_neg h] at hv
    exact absurd hv (List.not_mem_nil)

theorem okSet_nil : OkSet S k [] := by intro v hv; exact absurd hv (List.not_mem_nil)

theorem okVec_fold_capAdd {vs : List (List ℕ)} (hvs : ∀ u ∈ vs, OkVec S k u) (z : List ℕ)
    (hz : OkVec S k z) : OkVec S k (vs.foldl (capAdd k) z) := by
  induction vs generalizing z with
  | nil => exact hz
  | cons w rest ih =>
      rw [List.foldl_cons]
      exact ih (fun u hu => hvs u (List.mem_cons_of_mem _ hu)) (capAdd k z w)
        (okVec_capAdd hz (hvs w List.mem_cons_self))

theorem VecLe_capAdd_left {u v : List ℕ} (hu : OkVec S k u) (hv : OkVec S k v) :
    VecLe u (capAdd k u v) := by
  intro i
  rcases lt_or_ge i u.length with hi | hi
  · rw [capAdd_getD hu.1 hv.1]
    exact (Nat.le_min).mpr ⟨Nat.le_add_right _ _, hu.getD_le i⟩
  · rw [List.getD_eq_default _ _ hi]
    exact Nat.zero_le _

theorem VecLe_capAdd_right {u v : List ℕ} (hu : OkVec S k u) (hv : OkVec S k v) :
    VecLe v (capAdd k u v) := by
  intro i
  rcases lt_or_ge i v.length with hi | hi
  · rw [capAdd_getD hu.1 hv.1]
    exact (Nat.le_min).mpr ⟨Nat.le_add_left _ _, hv.getD_le i⟩
  · rw [List.getD_eq_default _ _ hi]
    exact Nat.zero_le _

/-- The chain of `capAdd`s started at `z` dominates `z` and every element of `vs`. -/
theorem VecLe_fold_capAdd {vs : List (List ℕ)} (hvs : ∀ u ∈ vs, OkVec S k u) (z : List ℕ)
    (hz : OkVec S k z) :
    (∀ u ∈ vs, VecLe u (vs.foldl (capAdd k) z)) ∧ VecLe z (vs.foldl (capAdd k) z) := by
  induction vs generalizing z with
  | nil => exact ⟨by simp, VecLe.refl z⟩
  | cons w rest ih =>
      rw [List.foldl_cons]
      have hw : OkVec S k w := hvs w List.mem_cons_self
      have hrest : ∀ u ∈ rest, OkVec S k u := fun u hu => hvs u (List.mem_cons_of_mem _ hu)
      obtain ⟨ih1, ih2⟩ := ih hrest (capAdd k z w) (okVec_capAdd hz hw)
      refine ⟨?_, ?_⟩
      · intro u hu
        rcases List.mem_cons.mp hu with rfl | hu
        · exact VecLe.trans (VecLe_capAdd_right hz hw) ih2
        · exact ih1 u hu
      · exact VecLe.trans (VecLe_capAdd_left hz hw) ih2

/-! ## §4 Membership in the union and in the AND fold -/

theorem mem_foldl_insertNew {A : List (List ℕ)} {l : List (List ℕ)} {v : List ℕ} :
    v ∈ l.foldl insertNew A ↔ v ∈ A ∨ v ∈ l := by
  induction l generalizing A with
  | nil => simp
  | cons x xs ih =>
      rw [List.foldl_cons, ih (A := insertNew A x), List.mem_cons]
      unfold insertNew
      by_cases h : x ∈ A
      · rw [if_pos h]
        constructor
        · rintro (h1 | h1)
          · exact Or.inl h1
          · exact Or.inr (Or.inr h1)
        · rintro (h1 | h1 | h1)
          · exact Or.inl h1
          · rw [h1]; exact Or.inl h
          · exact Or.inr h1
      · rw [if_neg h, List.mem_append, List.mem_singleton]
        tauto

theorem mem_orFold (l : List (List (List ℕ))) (A0 : List (List ℕ)) {v : List ℕ} :
    v ∈ l.foldl (fun acc A => A.foldl insertNew acc) A0 ↔ v ∈ A0 ∨ ∃ A ∈ l, v ∈ A := by
  induction l generalizing A0 with
  | nil => simp
  | cons A l ih =>
      rw [List.foldl_cons, ih (A0 := A.foldl insertNew A0), mem_foldl_insertNew]
      constructor
      · rintro ((h | h) | ⟨B, hB, hv⟩)
        · exact Or.inl h
        · exact Or.inr ⟨A, List.mem_cons_self, h⟩
        · exact Or.inr ⟨B, List.mem_cons_of_mem _ hB, hv⟩
      · rintro (h | ⟨B, hB, hv⟩)
        · exact Or.inl (Or.inl h)
        · rcases List.mem_cons.mp hB with rfl | hB
          · exact Or.inl (Or.inr hv)
          · exact Or.inr ⟨B, hB, hv⟩

theorem mem_andStep {A B : List (List ℕ)} {v : List ℕ} :
    v ∈ andStep k A B ↔ ∃ u ∈ A, ∃ w ∈ B, v = capAdd k u w := by
  unfold andStep
  rw [mem_foldl_insertNew, List.mem_nil_iff, false_or, List.mem_flatMap]
  constructor
  · rintro ⟨u, hu, hw'⟩
    obtain ⟨w, hw, hvw⟩ := List.mem_map.mp hw'
    exact ⟨u, hu, w, hw, hvw.symm⟩
  · rintro ⟨u, hu, w, hw, rfl⟩
    exact ⟨u, hu, List.mem_map.mpr ⟨w, hw, rfl⟩⟩

/-- The AND fold: every vector in it is the `capAdd` chain of one vector per input set. -/
theorem mem_andFold_aux (As : List (List (List ℕ))) (Z : List (List ℕ)) :
    ∀ {v : List ℕ}, v ∈ As.foldl (andStep k) Z →
      ∃ z ∈ Z, ∃ vs : List (List ℕ),
        List.Forall₂ (fun (A : List (List ℕ)) (u : List ℕ) => u ∈ A) As vs ∧
          v = vs.foldl (capAdd k) z := by
  induction As generalizing Z with
  | nil =>
      intro v hv
      exact ⟨v, hv, [], List.Forall₂.nil, by simp⟩
  | cons A As ih =>
      intro v hv
      rw [List.foldl_cons] at hv
      obtain ⟨z', hz', vs, hvs, hvz⟩ := ih (Z := andStep k Z A) hv
      obtain ⟨u, hu, w, hw, rfl⟩ := mem_andStep.mp hz'
      exact ⟨u, hu, w :: vs, List.Forall₂.cons hw hvs, by
        rw [List.foldl_cons]; exact hvz⟩

/-- The other direction: a `capAdd` chain of available input vectors is in the AND fold. -/
theorem andFold_mem {As : List (List (List ℕ))} {vs : List (List ℕ)}
    (hvs : List.Forall₂ (fun (A : List (List ℕ)) (u : List ℕ) => u ∈ A) As vs) :
    ∀ (Z : List (List ℕ)) (z : List ℕ), z ∈ Z →
      vs.foldl (capAdd k) z ∈ As.foldl (andStep k) Z := by
  induction hvs with
  | nil => intro Z z hz; simpa using hz
  | cons hmem htail ih =>
      intro Z z hz
      rw [List.foldl_cons, List.foldl_cons]
      exact ih _ _ (mem_andStep.mpr ⟨z, hz, _, hmem, rfl⟩)

/-! ## §5 The gate sets, and the state invariant -/

/-- The set of count vectors one gate contributes, from the state `R`. -/
def gateSet (S : List ℕ) (k : ℕ) (R : List (List (List ℕ))) (g : Gate) : List (List ℕ) :=
  let ins := g.inputs.map fun i => R.getD i []
  match g.op with
  | GateOp.or => ins.foldl (fun acc A => A.foldl insertNew acc) []
  | GateOp.and => ins.foldl (andStep k) [S.map fun _ => 0]
  | _ => []

/-- One step of the fold inside `readVectors`: append the gate's set. -/
def stepR (S : List ℕ) (k : ℕ) (R : List (List (List ℕ))) (g : Gate) : List (List (List ℕ)) :=
  R ++ [gateSet S k R g]

theorem readVectors_eq (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ) :
    readVectors C n S k = C.gates.foldl (stepR S k) ((List.range n).map (leafVectors S k)) := rfl

theorem mem_gateSet_or {R : List (List (List ℕ))} {ins : List ℕ} {v : List ℕ} :
    v ∈ gateSet S k R { op := GateOp.or, inputs := ins } ↔ ∃ i ∈ ins, v ∈ R.getD i [] := by
  have h : gateSet S k R { op := GateOp.or, inputs := ins }
      = (ins.map fun i => R.getD i []).foldl (fun acc A => A.foldl insertNew acc) [] := rfl
  rw [h, mem_orFold]
  constructor
  · rintro (h0 | ⟨A, hA, hv⟩)
    · exact absurd h0 (List.not_mem_nil)
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hA
      exact ⟨i, hi, hv⟩
  · rintro ⟨i, hi, hv⟩
    exact Or.inr ⟨R.getD i [], List.mem_map.mpr ⟨i, hi, rfl⟩, hv⟩

theorem mem_gateSet_and {R : List (List (List ℕ))} {ins : List ℕ} {v : List ℕ} :
    v ∈ gateSet S k R { op := GateOp.and, inputs := ins } →
      ∃ vs : List (List ℕ), List.Forall₂ (fun i u => u ∈ R.getD i []) ins vs ∧
        v = vs.foldl (capAdd k) (S.map fun _ => 0) := by
  intro hv
  obtain ⟨z, hz, vs, hvs, hvz⟩ :=
    mem_andFold_aux (ins.map fun i => R.getD i []) [S.map fun _ => 0] hv
  rw [List.mem_singleton] at hz
  subst hz
  obtain ⟨hlen, hget⟩ := List.forall₂_iff_get.mp hvs
  refine ⟨vs, ?_, hvz⟩
  rw [List.forall₂_iff_get]
  refine ⟨by simpa using hlen, ?_⟩
  intro i h1 h2
  have := hget i (by simpa using h1) h2
  simpa using this

theorem gateSet_and_mem {R : List (List (List ℕ))} {ins : List ℕ} {vs : List (List ℕ)}
    (hvs : List.Forall₂ (fun i u => u ∈ R.getD i []) ins vs) :
    vs.foldl (capAdd k) (S.map fun _ => 0)
      ∈ gateSet S k R { op := GateOp.and, inputs := ins } := by
  have h : gateSet S k R { op := GateOp.and, inputs := ins }
      = (ins.map fun i => R.getD i []).foldl (andStep k) [S.map fun _ => 0] := rfl
  rw [h]
  rw [List.forall₂_iff_get] at hvs
  obtain ⟨hlen, hget⟩ := hvs
  have hvs' : List.Forall₂ (fun (A : List (List ℕ)) (u : List ℕ) => u ∈ A)
      (ins.map fun i => R.getD i []) vs := by
    rw [List.forall₂_iff_get]
    refine ⟨by simpa using hlen, ?_⟩
    intro i h1 h2
    have := hget i (by simpa using h1) h2
    simpa using this
  exact andFold_mem hvs' _ _ (by simp)

theorem okSet_orFold {l : List (List (List ℕ))} (h : ∀ A ∈ l, OkSet S k A) (A0 : List (List ℕ))
    (h0 : OkSet S k A0) : OkSet S k (l.foldl (fun acc A => A.foldl insertNew acc) A0) := by
  induction l generalizing A0 with
  | nil => exact h0
  | cons A l ih =>
      rw [List.foldl_cons]
      refine ih (fun B hB => h B (List.mem_cons_of_mem _ hB)) (A.foldl insertNew A0) ?_
      intro v hv
      rw [mem_foldl_insertNew] at hv
      rcases hv with hv | hv
      · exact h0 v hv
      · exact h A List.mem_cons_self v hv

theorem okSet_andFold {l : List (List (List ℕ))} (h : ∀ A ∈ l, OkSet S k A) :
    ∀ (Z : List (List ℕ)), OkSet S k Z → OkSet S k (l.foldl (andStep k) Z) := by
  induction l with
  | nil => intro Z hZ; simpa using hZ
  | cons A l ih =>
      intro Z hZ
      rw [List.foldl_cons]
      refine ih (fun B hB => h B (List.mem_cons_of_mem _ hB)) _ ?_
      intro v hv
      rw [mem_andStep] at hv
      obtain ⟨u, hu, w, hw, rfl⟩ := hv
      exact okVec_capAdd (hZ u hu) (h A List.mem_cons_self w hw)

/-- Every count vector of every set of a `readVectors` state is `OkVec`. -/
def OkState (S : List ℕ) (k : ℕ) (R : List (List (List ℕ))) : Prop := ∀ w, OkSet S k (R.getD w [])

theorem okSet_gateSet {R : List (List (List ℕ))} (h : OkState S k R) (g : Gate) :
    OkSet S k (gateSet S k R g) := by
  intro v hv
  obtain ⟨op, ins⟩ := g
  cases op with
  | or =>
      rw [mem_gateSet_or] at hv
      obtain ⟨i, _, hvi⟩ := hv
      exact h i v hvi
  | and =>
      obtain ⟨vs, hvs, rfl⟩ := mem_gateSet_and hv
      refine okVec_fold_capAdd ?_ _ okVec_zero
      intro u hu
      obtain ⟨i, hi2, hiu⟩ := List.getElem_of_mem hu
      obtain ⟨hlen, hget⟩ := List.forall₂_iff_get.mp hvs
      rw [← hiu]
      exact h ins[i] vs[i] (by simpa using hget i (hlen ▸ hi2) hi2)
  | not => rw [show gateSet S k R { op := GateOp.not, inputs := ins } = [] from rfl] at hv
           exact absurd hv (List.not_mem_nil)
  | mod m => rw [show gateSet S k R { op := GateOp.mod m, inputs := ins } = [] from rfl] at hv
             exact absurd hv (List.not_mem_nil)
  | maj => rw [show gateSet S k R { op := GateOp.maj, inputs := ins } = [] from rfl] at hv
           exact absurd hv (List.not_mem_nil)

theorem okState_step {R : List (List (List ℕ))} (h : OkState S k R) (g : Gate) :
    OkState S k (stepR S k R g) := by
  intro w
  rw [stepR]
  rcases lt_or_ge w R.length with hw | hw
  · rw [List.getD_append R [gateSet S k R g] [] w hw]; exact h w
  · rw [List.getD_append_right R [gateSet S k R g] [] w hw]
    rcases Nat.eq_or_lt_of_le hw with heq | hlt
    · subst heq; simpa using okSet_gateSet h g
    · have hge : [gateSet S k R g].length ≤ w - R.length := by
        simp only [List.length_singleton]; omega
      rw [List.getD_eq_default _ _ hge]
      exact okSet_nil

theorem okState_fold (gs : List Gate) {R : List (List (List ℕ))} (h : OkState S k R) :
    OkState S k (gs.foldl (stepR S k) R) := by
  induction gs generalizing R with
  | nil => exact h
  | cons g gs ih => rw [List.foldl_cons]; exact ih (okState_step h g)

theorem okState_init (n : ℕ) : OkState S k ((List.range n).map (leafVectors S k)) := by
  intro w
  rcases lt_or_ge w n with hw | hw
  · intro v hv
    rw [List.getD_eq_getElem _ _ (by simpa using hw)] at hv
    simp only [List.getElem_map, List.getElem_range] at hv
    exact okSet_leafVectors w v hv
  · rw [List.getD_eq_default _ _ (by simpa using hw)]
    exact okSet_nil

/-! ## §6 Lengths of the fold -/

theorem stepR_length (R : List (List (List ℕ))) (g : Gate) :
    (stepR S k R g).length = R.length + 1 := by
  simp [stepR]

theorem foldl_stepR_length (gs : List Gate) (R : List (List (List ℕ))) :
    (gs.foldl (stepR S k) R).length = R.length + gs.length := by
  induction gs generalizing R with
  | nil => simp
  | cons g gs ih => rw [List.foldl_cons, ih, stepR_length, List.length_cons]; omega

theorem getD_stepR_lt (R : List (List (List ℕ))) (g : Gate) {w : ℕ} (hw : w < R.length) :
    (stepR S k R g).getD w [] = R.getD w [] :=
  List.getD_append R [gateSet S k R g] [] w hw

theorem getD_foldl_stepR_lt (gs : List Gate) (R : List (List (List ℕ))) {w : ℕ} (hw : w < R.length) :
    (gs.foldl (stepR S k) R).getD w [] = R.getD w [] := by
  induction gs generalizing R with
  | nil => rfl
  | cons g gs ih =>
      rw [List.foldl_cons, ih (R := stepR S k R g) (by rw [stepR_length]; omega),
        getD_stepR_lt R g hw]

theorem getD_stepR_last (R : List (List (List ℕ))) (g : Gate) :
    (stepR S k R g).getD R.length [] = gateSet S k R g := by
  rw [stepR, List.getD_append_right R [gateSet S k R g] [] R.length (le_rfl)]
  simp

/-! ## §7 The relation between the state before and after the change -/

/-- `Rel R0 R1 Rt`: every vector at a wire of `R0` either is at that wire of `R1`, or dominates a
vector available at the untouched wire `t` (whose set is `Rt`). -/
def Rel (R0 R1 : List (List (List ℕ))) (Rt : List (List ℕ)) : Prop :=
  ∀ (w : ℕ) (v : List ℕ), v ∈ R0.getD w [] → v ∈ R1.getD w [] ∨ ∃ v' ∈ Rt, VecLe v' v

/-- One step of the fold, with the same gate on both sides. -/
theorem Rel_step {R0 R1 : List (List (List ℕ))} {Rt : List (List ℕ)} {g : Gate}
    (hlen : R0.length = R1.length) (h : Rel R0 R1 Rt) (hok : OkState S k R0) :
    Rel (stepR S k R0 g) (stepR S k R1 g) Rt := by
  intro w v hv
  rcases lt_or_ge w R0.length with hw | hw
  · rw [getD_stepR_lt _ _ hw] at hv
    rw [getD_stepR_lt _ _ (hlen ▸ hw)]
    exact h w v hv
  · have hlt : w < (stepR S k R0 g).length := by
      by_contra hc
      have hge : (stepR S k R0 g).length ≤ w := le_of_not_gt hc
      rw [List.getD_eq_default _ _ hge] at hv
      exact List.not_mem_nil hv
    have hlast : w = R0.length := by rw [stepR_length] at hlt; omega
    subst hlast
    rw [getD_stepR_last] at hv
    rw [hlen, getD_stepR_last]
    obtain ⟨op, ins⟩ := g
    cases op with
    | or =>
        rw [mem_gateSet_or] at hv
        obtain ⟨i, hi, hvi⟩ := hv
        rcases h i v hvi with h1 | h2
        · exact Or.inl (mem_gateSet_or.mpr ⟨i, hi, h1⟩)
        · exact Or.inr h2
    | and =>
        obtain ⟨vs, hvs, rfl⟩ := mem_gateSet_and hv
        obtain ⟨hvslen, hvsget⟩ := List.forall₂_iff_get.mp hvs
        have hvsok : ∀ u ∈ vs, OkVec S k u := by
          intro u hu
          obtain ⟨i, hi2, hiu⟩ := List.getElem_of_mem hu
          rw [← hiu]
          exact hok ins[i] vs[i] (by simpa using hvsget i (hvslen ▸ hi2) hi2)
        by_cases hall : List.Forall₂ (fun i u => u ∈ R1.getD i []) ins vs
        · exact Or.inl (gateSet_and_mem hall)
        · have hnot : ∃ (i : ℕ) (h1 : i < ins.length) (h2 : i < vs.length),
              ¬ (vs[i] ∈ R1.getD ins[i] []) := by
            by_contra hc
            apply hall
            rw [List.forall₂_iff_get]
            refine ⟨hvslen, ?_⟩
            intro i h1 h2
            by_contra hlt
            exact hc ⟨i, h1, h2, hlt⟩
          obtain ⟨i, h1, h2, hlt⟩ := hnot
          have hmem0 : vs[i] ∈ R0.getD ins[i] [] := by
            have := hvsget i h1 h2
            simpa using this
          rcases h ins[i] vs[i] hmem0 with hcontra | ⟨v', hv', hle⟩
          · exact absurd hcontra hlt
          · refine Or.inr ⟨v', hv', VecLe.trans hle ?_⟩
            exact (VecLe_fold_capAdd hvsok (S.map fun _ => 0) okVec_zero).1 vs[i]
              (List.getElem_mem h2)
    | not => rw [show gateSet S k R0 { op := GateOp.not, inputs := ins } = [] from rfl] at hv
             exact absurd hv (List.not_mem_nil)
    | mod m => rw [show gateSet S k R0 { op := GateOp.mod m, inputs := ins } = [] from rfl] at hv
               exact absurd hv (List.not_mem_nil)
    | maj => rw [show gateSet S k R0 { op := GateOp.maj, inputs := ins } = [] from rfl] at hv
             exact absurd hv (List.not_mem_nil)

/-- The change at gate `j` itself: `OR(u, t) → OR(u)`, with `t` available on both sides. -/
theorem Rel_orJK {A : List (List (List ℕ))} {u t : ℕ} (htA : t < A.length) :
    Rel (stepR S k A { op := GateOp.or, inputs := [u, t] })
      (stepR S k A { op := GateOp.or, inputs := [u] }) (A.getD t []) := by
  intro w v hv
  rcases lt_or_ge w A.length with hw | hw
  · rw [getD_stepR_lt _ _ hw] at hv
    rw [getD_stepR_lt _ _ hw]
    exact Or.inl hv
  · have hlt : w < (stepR S k A { op := GateOp.or, inputs := [u, t] }).length := by
      by_contra hc
      have hge : (stepR S k A { op := GateOp.or, inputs := [u, t] }).length ≤ w := le_of_not_gt hc
      rw [List.getD_eq_default _ _ hge] at hv
      exact List.not_mem_nil hv
    have hlast : w = A.length := by rw [stepR_length] at hlt; omega
    subst hlast
    rw [getD_stepR_last, mem_gateSet_or] at hv
    rw [getD_stepR_last]
    obtain ⟨i, hi, hvi⟩ := hv
    have hi' : i = u ∨ i = t := by simpa using hi
    rcases hi' with h | h
    · refine Or.inl ?_
      rw [h] at hvi
      rw [mem_gateSet_or]
      by_cases hu : u < A.length
      · exact ⟨u, by simp, hvi⟩
      · rw [List.getD_eq_default _ _ (le_of_not_gt hu)] at hvi
        exact absurd hvi (List.not_mem_nil)
    · rw [h] at hvi
      exact Or.inr ⟨v, hvi, VecLe.refl v⟩

/-- The relation propagates along a list of gates. -/
theorem Rel_fold (gs : List Gate) {R0 R1 : List (List (List ℕ))} {Rt : List (List ℕ)}
    (hlen : R0.length = R1.length) (h : Rel R0 R1 Rt) (hok : OkState S k R0) :
    Rel (gs.foldl (stepR S k) R0) (gs.foldl (stepR S k) R1) Rt := by
  induction gs generalizing R0 R1 with
  | nil => exact h
  | cons g gs ih =>
      rw [List.foldl_cons, List.foldl_cons]
      exact ih (R0 := stepR S k R0 g) (R1 := stepR S k R1 g)
        (by rw [stepR_length, stepR_length, hlen]) (Rel_step hlen h hok) (okState_step hok g)

/-! ## §8 The statement, and its proof -/

/-- A good vector's sub-vector is good. -/
theorem all_of_VecLe {v v' : List ℕ} (h : VecLe v' v) (hv : v.length = S.length)
    (hv' : v'.length = S.length) (hgood : v.all (fun a => decide (a ≤ k)) = true) :
    v'.all (fun a => decide (a ≤ k)) = true := by
  rw [List.all_eq_true] at hgood ⊢
  intro a ha
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
  have hi2 : i < v.length := (hv'.trans hv.symm) ▸ hi
  have h1 : v'.getD i 0 ≤ v.getD i 0 := h i
  rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hi2] at h1
  have h2 : v[i]'(hi2) ≤ k := by
    have := hgood _ (List.getElem_mem hi2)
    simpa using this
  exact decide_eq_true (le_trans h1 h2)

/-- **L-meta-2676**, transcribed from the registry (byte for byte). -/
theorem statement :
    ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (j u t : ℕ),
    PEqualNP.MetaComplexity.Monotone2 C →
    j < C.gates.length →
    C.gates[j]? = some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [u, t] } →
    t < n + j →
    (∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD t false = true →
      PEqualNP.MetaComplexity.circuitFun n C x = true) →
    ∀ (S : List ℕ) (k : ℕ), PEqualNP.ReadK.readsAtMost C n S k = true →
      PEqualNP.ReadK.readsAtMost
        { gates := C.gates.set j
            { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [u] } ++
            [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [C.output, t] }],
          output := n + C.gates.length } n S k = true := by
  intro n C j u t hmono hj hget ht himp S k hread
  -- the gate at `j`, and the two decompositions of the gate list
  have hg : C.gates[j]'(hj) = { op := GateOp.or, inputs := [u, t] } := by
    have h1 := List.getElem?_eq_getElem hj
    rw [h1] at hget
    exact Option.some.inj hget
  have hdecomp : C.gates
      = C.gates.take j ++ { op := GateOp.or, inputs := [u, t] } :: C.gates.drop (j + 1) := by
    calc C.gates = C.gates.take j ++ C.gates.drop j := (List.take_append_drop j C.gates).symm
      _ = C.gates.take j ++ (C.gates[j]'(hj) :: C.gates.drop (j + 1)) := by
            rw [List.drop_eq_getElem_cons hj]
      _ = C.gates.take j ++ ({ op := GateOp.or, inputs := [u, t] } :: C.gates.drop (j + 1)) := by
            rw [hg]
  have hset : C.gates.set j { op := GateOp.or, inputs := [u] }
      = C.gates.take j ++ { op := GateOp.or, inputs := [u] } :: C.gates.drop (j + 1) :=
    List.set_eq_take_cons_drop _ hj
  -- the common prefix state
  set A : List (List (List ℕ)) :=
    (C.gates.take j).foldl (stepR S k) ((List.range n).map (leafVectors S k)) with hA
  have hAlen : A.length = n + j := by
    rw [hA, foldl_stepR_length, List.length_take, Nat.min_eq_left (le_of_lt hj)]
    simp
  -- the two full states
  have hR0 : readVectors C n S k = (C.gates.drop (j + 1)).foldl (stepR S k)
      (stepR S k A { op := GateOp.or, inputs := [u, t] }) := by
    rw [readVectors_eq]
    conv_lhs => rw [hdecomp]
    rw [List.foldl_append, List.foldl_cons, hA]
  set R1f : List (List (List ℕ)) := (C.gates.drop (j + 1)).foldl (stepR S k)
    (stepR S k A { op := GateOp.or, inputs := [u] }) with hR1f
  have hR1 : readVectors
      { gates := C.gates.set j { op := GateOp.or, inputs := [u] } ++
          [{ op := GateOp.or, inputs := [C.output, t] }],
        output := n + C.gates.length } n S k
      = stepR S k R1f { op := GateOp.or, inputs := [C.output, t] } := by
    rw [readVectors_eq]
    conv_lhs => rw [hset]
    rw [hR1f]
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [hA]
  have hR1flen : R1f.length = n + C.gates.length := by
    rw [hR1f, foldl_stepR_length, stepR_length, List.length_drop]
    omega
  -- a good vector at the old output
  have hread' : ((readVectors C n S k).getD C.output []).any
      (fun v => v.all fun a => decide (a ≤ k)) = true := by
    simpa [readsAtMost] using hread
  obtain ⟨v, hvmem, hvgood⟩ := List.any_eq_true.mp hread'
  have hvmem' : v ∈ ((C.gates.drop (j + 1)).foldl (stepR S k)
      (stepR S k A { op := GateOp.or, inputs := [u, t] })).getD C.output [] := by
    rw [← hR0]; exact hvmem
  -- the relation, along `drop (j+1)`
  have hokA : OkState S k A := by
    rw [hA]
    exact okState_fold _ (okState_init n)
  have hRelJ : Rel (stepR S k A { op := GateOp.or, inputs := [u, t] })
      (stepR S k A { op := GateOp.or, inputs := [u] }) (A.getD t []) :=
    Rel_orJK (by rw [hAlen]; exact ht)
  have hRelEnd := Rel_fold (S := S) (k := k) (gs := C.gates.drop (j + 1)) (Rt := A.getD t [])
    (by rw [stepR_length, stepR_length]) hRelJ (okState_step hokA _)
  -- `t` reads the same in both
  have hRt : R1f.getD t [] = A.getD t [] := by
    rw [hR1f,
      getD_foldl_stepR_lt (gs := C.gates.drop (j + 1))
        (R := stepR S k A { op := GateOp.or, inputs := [u] }) (w := t)
        (by rw [stepR_length]; omega),
      getD_stepR_lt A _ (by rw [hAlen]; exact ht)]
  -- the top wire is the new gate, and it reads `out` and `t`
  have htop : (readVectors
      { gates := C.gates.set j { op := GateOp.or, inputs := [u] } ++
          [{ op := GateOp.or, inputs := [C.output, t] }],
        output := n + C.gates.length } n S k).getD (n + C.gates.length) []
      = gateSet S k R1f { op := GateOp.or, inputs := [C.output, t] } := by
    rw [hR1, ← hR1flen, getD_stepR_last]
  -- assemble
  have hok0 : OkState S k ((C.gates.drop (j + 1)).foldl (stepR S k)
      (stepR S k A { op := GateOp.or, inputs := [u, t] })) :=
    okState_fold _ (okState_step hokA _)
  have hlen0 : v.length = S.length := (hok0 C.output v hvmem').1
  rw [readsAtMost, htop, List.any_eq_true]
  rcases hRelEnd C.output v hvmem' with hin | ⟨v', hv', hle⟩
  · exact ⟨v, mem_gateSet_or.mpr ⟨C.output, by simp, hin⟩, hvgood⟩
  · have hv'mem : v' ∈ R1f.getD t [] := by rw [hRt]; exact hv'
    have hv'len : v'.length = S.length := (hokA t v' hv').1
    have hv'good : v'.all (fun a => decide (a ≤ k)) = true :=
      all_of_VecLe hle hlen0 hv'len hvgood
    exact ⟨v', mem_gateSet_or.mpr ⟨t, by simp, hv'mem⟩, hv'good⟩

end PEqualNP.Outside.ReadK2676
