import PEqualNP.Defs

set_option autoImplicit false

/-!
# L-meta-3657: the normal-form top lemma

In a lift-fixed live fan-in-two AND/OR edge circuit with no AND reading a below-`F` wire, an AND
gate is below `F` iff only OR gates lie above it (strictly in its cone).

The setting is that of `PEqualNP.Defs.TopForm`, `PEqualNP.Defs.Core` and
`PEqualNP.Defs.EdgeOwnership`: `C` is a circuit of the root model on the inputs `Fin n`, wire `i < n`
is the input `x_i`, gate number `j` is wire `n + j`, `F = graphFun G ∅` is the edge function of the
graph `G`, `BelowF G C j` says gate `j` is true only where `F` is true, `InCone n C i j` says gate
`i` lies strictly inside the cone of gate `j`, and `IsLiftFixedPoint G C` says the implicant lift
applies nowhere.

The proof, in words.

* A gate wire `n + j` is an IMPLICANT WIRE when gate `j` is below `F` and true somewhere
  (`liveness`).
* THE LIFT ARGUMENT. Let `g` be an OR gate of the output cone reading an implicant wire `w`. If `g`
  were not below `F`, the lift would apply at `g` at the operand position of `w` (fan-in two names
  that position): `LiftAt g b` holds, against `IsLiftFixedPoint`. Hence `g` is below `F`.
* CLIMBING. Let `h` be below `F`. Every gate strictly above `h` reads, by `inCone_iff`, a gate wire
  `n + m` with `m = h` or `m` strictly above `h`; inducting downwards gives `BelowF m`, so that
  wire is below `F`. An AND gate above `h` would read a below-`F` wire, which the hypothesis
  forbids; an OR gate above `h` reads that implicant wire, so the lift argument makes it below `F`.
  Hence: every gate above a below-`F` gate is an OR gate below `F`.
* DOWNWARD VALUE. Conversely, if every gate above the AND gate `h` is an OR, then the value of `h`
  climbs the cone: each OR gate above `h` reads, through `inCone_iff`, a gate wire whose value is
  already true, so (`val_or`) its own value is true. The output lies in the cone of `h` (the
  output-cone hypothesis), so the output is true wherever `h` is true; the circuit computes `F`,
  so `h` is below `F`.

No `sorry`, no new axiom: every declaration lives in `PEqualNP.Outside.L_meta_3657`.
-/

namespace PEqualNP.Outside.L_meta_3657

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.Core PEqualNP.ReadTwo

attribute [local instance] gateOpDecEq

/-! ## 1. The values of the wires of a circuit -/

/-- One step of the wire computation. -/
def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [ite_eq_left hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

/-- The value of wire `u` of `C` on the input `x` (`false` past the last wire). -/
def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

lemma eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj

lemma val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
    val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨i, hi, h⟩
    by_cases hlt : i < n + r
    · rw [ite_eq_left hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [ite_eq_right hlt] at h; cases h
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨i, hi, by rw [ite_eq_left hlt]; exact h⟩

lemma val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
    val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  constructor
  · intro h i hi
    have h' := h i hi
    by_cases hlt : i < n + r
    · rw [ite_eq_left hlt] at h'; exact ⟨hlt, h'⟩
    · rw [ite_eq_right hlt] at h'; cases h'
  · intro h i hi
    rw [ite_eq_left (h i hi).1]; exact (h i hi).2

/-- `gateVal` is the wire value of the gate's wire. -/
lemma gateVal_eq_val (n : ℕ) (C : Circuit) (j : ℕ) (x : Fin n → Bool) :
    gateVal n C j x = val C (List.ofFn x) (n + j) := rfl

/-- `wval` is the wire value. -/
lemma wval_eq_val (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) :
    wval C x w = val C (List.ofFn x) w := rfl

/-- The value of the circuit `⟨C.gates, t⟩` is the wire value of wire `t`. -/
lemma eval_gates_eq_val (n : ℕ) (C : Circuit) (t : ℕ) (x : Fin n → Bool) :
    Circuit.eval ⟨C.gates, t⟩ (List.ofFn x) = val C (List.ofFn x) t := rfl

/-! ## 2. The strict cone, gate by gate -/

lemma cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

lemma cones_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
      j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
        (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) []) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (coneStep n) []).length = gs.length := by
      rw [cones_len]; simp
    have key : ∀ k, k < gs.length →
        (coneStep n (gs.foldl (coneStep n) []) g).getD k [] =
          (gs.foldl (coneStep n) []).getD k [] := by
      intro k hk
      simp only [coneStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨h, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)] at h3
        exact h3
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      have e2 : (coneStep n (gs.foldl (coneStep n) []) g).getD gs.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
            (fun w => (w - n) :: (gs.foldl (coneStep n) []).getD (w - n) []) := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2, e1]
      simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
      constructor
      · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
        refine ⟨by simp, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        rw [key (w - n) (by omega)] at h3
        exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
    · have e0 : (coneStep n (gs.foldl (coneStep n) []) g).getD j [] = [] := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

/-- THE STEP FORM OF THE CONE: `i` is strictly inside the cone of `j` iff `j` is a real gate reading
a gate wire `n + k` with `k < j` and `i = k` or `i` strictly inside the cone of `k`. -/
lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
    InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧ n + k ∈ (gateAt C j).inputs ∧
      (i = k ∨ InCone n C i k) := by
  have h := cones_char n C.gates i j
  unfold InCone cones gateAt
  rw [h]
  constructor
  · rintro ⟨h0, w, hw, h1, h2, h3⟩
    refine ⟨h0, w - n, by omega, ?_, h3⟩
    have : n + (w - n) = w := by omega
    rw [this]
    exact hw
  · rintro ⟨h0, k, hk, hw, h3⟩
    refine ⟨h0, n + k, hw, by omega, by omega, ?_⟩
    have : n + k - n = k := by omega
    rw [this]
    exact h3

/-- Everything strictly inside the cone of a gate has a smaller index. -/
lemma inCone_lt (n : ℕ) (C : Circuit) : ∀ k, k < C.gates.length → ∀ i, InCone n C i k → i < k := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro hk i h
    obtain ⟨_, m, hm, hin, h | h⟩ := (inCone_iff n C i k).1 h
    · omega
    · have h2 := ih m hm (by omega) i h
      omega

/-! ## 3. The lift argument, the climb, and the downward value -/

/-- A fan-in-two gate that reads `w` reads it at one of its two operand positions. -/
lemma exists_getD_eq_of_mem_length_two {l : List ℕ} (hlen : l.length = 2) {w : ℕ} (hw : w ∈ l) :
    ∃ b : Fin 2, l.getD (b : ℕ) 0 = w := by
  obtain ⟨a, c, rfl⟩ : ∃ a c : ℕ, l = [a, c] := by
    match l with
    | [] => simp at hlen
    | [_] => simp at hlen
    | [a, c] => exact ⟨a, c, rfl⟩
    | _ :: _ :: _ :: _ => simp at hlen
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩

/-- The wire of a below-`F` gate that is true somewhere is an implicant wire. -/
lemma isImpWire_of_belowF {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (j : ℕ) (hbelow : BelowF G C j)
    (hlive : ∃ x : Fin n → Bool, gateVal n C j x = true) : IsImpWire G C (n + j) := by
  refine ⟨?_, hlive⟩
  intro x hx
  exact hbelow x hx

/-- THE LIFT ARGUMENT: an OR gate of the output cone reading an implicant wire is below `F`.
Otherwise the implicant lift would apply at it, at the operand position of that wire. -/
lemma belowF_of_or_reads_impWire {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (g w : ℕ) (hg : g < C.gates.length) (hAO2 : IsAO2 n C)
    (hout : InOutputCone n C g) (hfix : IsLiftFixedPoint G C)
    (hor : (gateAt C g).op = GateOp.or) (hw : w ∈ (gateAt C g).inputs)
    (himp : IsImpWire G C w) : BelowF G C g := by
  by_contra hnb
  have hlen2 : (gateAt C g).inputs.length = 2 := hAO2.2.2 _ (gateAt_mem hg)
  obtain ⟨b, hb⟩ := exists_getD_eq_of_mem_length_two hlen2 hw
  have hLift : LiftAt G C g b := by
    refine ⟨hout, hor, hnb, ?_⟩
    show IsImpWire G C (opnd C g b)
    rw [opnd, hb]
    exact himp
  exact hfix ⟨g, hg, b, hLift⟩

/-- THE CLIMB: strictly above a below-`F` gate, every gate is below `F`. Every gate above `h` reads
a gate wire `n + m` with `m` at or above `h`; an AND reader would read a below-`F` wire (forbidden),
an OR reader then is below `F` by the lift argument. -/
lemma belowF_of_inCone {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (h : ℕ) (hb : BelowF G C h) (hAO2 : IsAO2 n C)
    (hout : ∀ k < C.gates.length, InOutputCone n C k) (hfix : IsLiftFixedPoint G C)
    (hno : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → ∀ t ∈ (gateAt C k).inputs,
      ¬ (∀ x : Fin n → Bool, Circuit.eval ⟨C.gates, t⟩ (List.ofFn x) = true →
        graphFun G ∅ x = true))
    (hlive : ∀ k < C.gates.length, ∃ x : Fin n → Bool, gateVal n C k x = true) :
    ∀ k, InCone n C h k → BelowF G C k := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro hc
    obtain ⟨hk, m, hm, hin, hcase⟩ := (inCone_iff n C h k).1 hc
    have hmlen : m < C.gates.length := by omega
    have hbm : BelowF G C m := by
      rcases hcase with rfl | hc2
      · exact hb
      · exact ih m hm hc2
    have himp : IsImpWire G C (n + m) :=
      isImpWire_of_belowF m hbm (hlive m hmlen)
    by_cases hand : (gateAt C k).op = GateOp.and
    · refine absurd (fun x hx => hbm x ?_) (hno k hk hand (n + m) hin)
      rw [eval_gates_eq_val] at hx
      rw [gateVal_eq_val]
      exact hx
    · have hor : (gateAt C k).op = GateOp.or := by
        rcases hAO2.1 _ (gateAt_mem hk) with h' | h'
        · exact absurd h' hand
        · exact h'
      exact belowF_of_or_reads_impWire k (n + m) hk hAO2 (hout k hk) hfix hor hin himp

/-- THE DOWNWARD VALUE: if every gate strictly above `h` is an OR gate, the value of `h` climbs the
cone: each OR gate above `h` reads a gate wire already carrying `true`. -/
lemma val_of_or_cone {n : ℕ} {C : Circuit} (h : ℕ) (hh : h < C.gates.length)
    (horcone : ∀ k < C.gates.length, InCone n C h k → (gateAt C k).op = GateOp.or)
    (x : Fin n → Bool) (hx : val C (List.ofFn x) (n + h) = true) :
    ∀ k, (k = h ∨ InCone n C h k) → val C (List.ofFn x) (n + k) = true := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro hk
    rcases hk with rfl | hc
    · exact hx
    · obtain ⟨hklen, m, hm, hin, hcase⟩ := (inCone_iff n C h k).1 hc
      have hvm : val C (List.ofFn x) (n + m) = true := by
        rcases hcase with rfl | hc2
        · exact hx
        · exact ih m hm (Or.inr hc2)
      have hor : (gateAt C k).op = GateOp.or := horcone k hklen hc
      refine (val_or (n := n) (C := C) (x := List.ofFn x) (by simp) hklen hor).mpr
        ⟨n + m, hin, by omega, hvm⟩

/-! ## 4. The normal-form top lemma -/

/-- THE NORMAL-FORM DICHOTOMY, strong form: for an ARBITRARY gate `h` — being an AND gate is not
used — `h` is below `F` iff only OR gates lie strictly above it. -/
lemma normalForm_iff {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (hAO2 : IsAO2 n C) (hfun : circuitFun n C = graphFun G ∅)
    (hout : ∀ k < C.gates.length, InOutputCone n C k) (hfix : IsLiftFixedPoint G C)
    (hno : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → ∀ t ∈ (gateAt C k).inputs,
      ¬ (∀ x : Fin n → Bool, Circuit.eval ⟨C.gates, t⟩ (List.ofFn x) = true →
        graphFun G ∅ x = true))
    (hlive : ∀ k < C.gates.length, ∃ x : Fin n → Bool, gateVal n C k x = true) :
    ∀ h < C.gates.length,
      (BelowF G C h ↔
        ∀ k < C.gates.length, InCone n C h k → (gateAt C k).op = GateOp.or) := by
  intro h hh
  constructor
  · intro hb k hk hc
    have hclimb := belowF_of_inCone (G := G) (C := C) h hb hAO2 hout hfix hno hlive
    obtain ⟨_, m, hm, hin, hcase⟩ := (inCone_iff n C h k).1 hc
    have hmlen : m < C.gates.length := by omega
    have hbm : BelowF G C m := by
      rcases hcase with rfl | hc2
      · exact hb
      · exact hclimb m hc2
    by_cases handk : (gateAt C k).op = GateOp.and
    · refine absurd (fun x hx => hbm x ?_) (hno k hk handk (n + m) hin)
      rw [eval_gates_eq_val] at hx
      rw [gateVal_eq_val]
      exact hx
    · rcases hAO2.1 _ (gateAt_mem hk) with h' | h'
      · exact absurd h' handk
      · exact h'
  · intro hcone x hx
    have hout_h := hout h hh
    have hval : val C (List.ofFn x) C.output = true := by
      rcases hout_h.2 with heq | ⟨hnle, hcin⟩
      · rw [heq]
        exact hx
      · have hprop := val_of_or_cone (n := n) (C := C) h hh hcone x hx
        have h1 := hprop (C.output - n) (Or.inr hcin)
        have en : n + (C.output - n) = C.output := by omega
        rwa [en] at h1
    have hfunx : circuitFun n C x = graphFun G ∅ x := congrFun hfun x
    rw [← hfunx]
    show C.eval (List.ofFn x) = true
    rw [eval_eq_val]
    exact hval

end PEqualNP.Outside.L_meta_3657

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.Core

attribute [local instance] PEqualNP.MetaComplexity.NestedCover.gateOpDecEq

/-- L-meta-3657: in a lift-fixed live fan-in-two AND/OR edge circuit with no AND reading a below-`F`
wire, an AND gate is below `F` iff only OR gates lie strictly above it. -/
theorem PEqualNP.Outside.L_meta_3657 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit), IsAO2 n C → circuitFun n C = graphFun G ∅ →
    (∀ k < C.gates.length, InOutputCone n C k) → IsLiftFixedPoint G C →
    (∀ k < C.gates.length, (gateAt C k).op = GateOp.and → ∀ t ∈ (gateAt C k).inputs,
      ¬ (∀ x : Fin n → Bool, Circuit.eval ⟨C.gates, t⟩ (List.ofFn x) = true →
        graphFun G ∅ x = true)) →
    (∀ k < C.gates.length, ∃ x : Fin n → Bool, gateVal n C k x = true) →
    ∀ h < C.gates.length, (gateAt C h).op = GateOp.and →
      (BelowF G C h ↔
        ∀ k < C.gates.length, InCone n C h k → (gateAt C k).op = GateOp.or) := by
  intro n G _ C hAO2 hfun hout hfix hno hlive h hh _hand
  exact PEqualNP.Outside.L_meta_3657.normalForm_iff hAO2 hfun hout hfix hno hlive h hh
