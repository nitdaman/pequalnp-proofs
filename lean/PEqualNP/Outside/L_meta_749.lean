import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_749

open PEqualNP.CircuitLowerBounds

def readAt {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) : Bool :=
  (g.inputs.map fun i => (Circuit.wires ⟨gs, 0⟩ (List.ofFn x)).getD i false).headD false

def andOr (g : Gate) : Prop :=
  g.op = GateOp.and ∨ g.op = GateOp.or

def above {n : ℕ} (y x : Fin n → Bool) : Prop :=
  ∀ p : Fin n, y p = true → x p = true

lemma eval_const_or : GateOp.or.eval ([] : List Bool) = false := by
  simp [GateOp.eval]

lemma eval_const_and : GateOp.and.eval ([] : List Bool) = true := by
  simp [GateOp.eval]

lemma wires_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    Circuit.wires ⟨gs ++ [g], 0⟩ x =
      (Circuit.wires ⟨gs, 0⟩ x) ++
        [g.op.eval (g.inputs.map fun i => (Circuit.wires ⟨gs, 0⟩ x).getD i false)] := by
  simp [Circuit.wires, List.foldl_append]

lemma eval_andOr_mono {op : GateOp} {ins : List ℕ} {w w' : List Bool}
    (hop : op = GateOp.and ∨ op = GateOp.or)
    (hm : ∀ i ∈ ins, w.getD i false = true → w'.getD i false = true) :
    op.eval (ins.map fun i => w.getD i false) = true →
      op.eval (ins.map fun i => w'.getD i false) = true := by
  intro h
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, List.mem_map] at h ⊢
    intro b hb
    rcases hb with ⟨i, hi, rfl⟩
    exact hm i hi (h (w.getD i false) ⟨i, hi, rfl⟩)
  · simp only [GateOp.eval, List.any_eq_true, List.mem_map] at h ⊢
    rcases h with ⟨b, ⟨i, hi, rfl⟩, hb⟩
    exact ⟨w'.getD i false, ⟨i, hi, rfl⟩, hm i hi hb⟩

lemma getD_snoc_left : ∀ (l : List Bool) (b : Bool) (i : ℕ), i < l.length →
    (l ++ [b]).getD i false = l.getD i false
  | [], _, _, h => by simp at h
  | _ :: tl, b, 0, _ => by simp
  | _ :: tl, b, i + 1, h => by
      simp [List.getD]
      exact getD_snoc_left tl b i (by simp at h; omega)

lemma getD_snoc_at : ∀ (l : List Bool) (b : Bool), (l ++ [b]).getD l.length false = b
  | [], b => by simp
  | _ :: tl, b => by
      simp [List.getD, getD_snoc_at tl b]

lemma getD_snoc_high : ∀ (l : List Bool) (b : Bool) (i : ℕ), l.length < i →
    (l ++ [b]).getD i false = false
  | [], _, 0, h => by simp at h
  | [], b, i + 1, _ => by simp
  | _ :: tl, b, 0, h => by simp at h
  | _ :: tl, b, i + 1, h => by
      simp [List.getD]
      exact getD_snoc_high tl b i (by simp at h; omega)

lemma fold_mono (ts : List Gate) (hts : ∀ g ∈ ts, andOr g)
    (a b : List Bool) (hlen : a.length = b.length)
    (hm : ∀ i, a.getD i false = true → b.getD i false = true) :
    ∀ i, (ts.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]) a).getD i false = true →
      (ts.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]) b).getD i false = true := by
  induction ts generalizing a b with
  | nil =>
      intro i hi
      exact hm i hi
  | cons g ts ih =>
      intro i hi
      have hg : andOr g := hts g (by simp)
      have hts' : ∀ a ∈ ts, andOr a := fun a ha => hts a (List.mem_cons_of_mem g ha)
      let aval := g.op.eval (g.inputs.map fun j => a.getD j false)
      let bval := g.op.eval (g.inputs.map fun j => b.getD j false)
      have hm1 : ∀ j, (a ++ [aval]).getD j false = true → (b ++ [bval]).getD j false = true := by
        intro j hj
        by_cases hlt : j < a.length
        · have haj : a.getD j false = true := by
            rw [getD_snoc_left a aval j hlt] at hj
            exact hj
          have hbj := hm j haj
          rw [getD_snoc_left b bval j (by omega)]
          exact hbj
        · have hge : a.length ≤ j := not_lt.mp hlt
          rcases Nat.eq_or_lt_of_le hge with hidx | hhi
          · have haval : aval = true := by
              rw [← hidx] at hj
              rw [getD_snoc_at] at hj
              exact hj
            have hin : ∀ t ∈ g.inputs, a.getD t false = true → b.getD t false = true :=
              fun t _ ht => hm t ht
            have hbval : bval = true := eval_andOr_mono hg hin haval
            rw [← hidx, hlen, getD_snoc_at]
            exact hbval
          · rw [getD_snoc_high a aval j hhi] at hj
            cases hj
      have hlen1 : (a ++ [aval]).length = (b ++ [bval]).length := by simp [hlen]
      exact ih hts' (a ++ [aval]) (b ++ [bval]) hlen1 hm1 i hi

lemma wires_mono {n : ℕ} (gs : List Gate) (hgs : ∀ g ∈ gs, andOr g)
    {y x : Fin n → Bool} (hle : above y x) :
    ∀ w : ℕ, (Circuit.wires ⟨gs, 0⟩ (List.ofFn y)).getD w false = true →
      (Circuit.wires ⟨gs, 0⟩ (List.ofFn x)).getD w false = true := by
  intro w hw
  have hm : ∀ i, (List.ofFn y).getD i false = true → (List.ofFn x).getD i false = true := by
    intro i hi
    by_cases hlt : i < n
    · rw [List.getD_eq_getElem (List.ofFn y) false (by simpa using hlt), List.getElem_ofFn] at hi
      rw [List.getD_eq_getElem (List.ofFn x) false (by simpa using hlt), List.getElem_ofFn]
      exact hle ⟨i, hlt⟩ hi
    · rw [List.getD_eq_default (List.ofFn y) false (by simpa using hlt)] at hi
      cases hi
  simpa [Circuit.wires] using
    fold_mono gs hgs (List.ofFn y) (List.ofFn x) (by simp) hm w hw

lemma take_andOr {n : ℕ} {C C' : List Gate} {y : Fin n → Bool}
    (hgate : ∀ g ∈ C, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hlen : C'.length = C.length)
    (hrep : ∀ (j : ℕ) (g : Gate), C[j]? = some g →
      (g.op = GateOp.not →
        (readAt (C.take j) g y = true → C'[j]? = some ⟨GateOp.or, []⟩) ∧
        (readAt (C.take j) g y = false → C'[j]? = some ⟨GateOp.and, []⟩)) ∧
      (g.op ≠ GateOp.not → C'[j]? = some g))
    {k : ℕ} (hk : k ≤ C.length) {g : Gate} (hg : g ∈ C'.take k) : andOr g := by
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hg
  have hjl : j < (C'.take k).length := (List.getElem?_eq_some_iff.mp hj).1
  have hjk : j < k := by
    simpa [Nat.min_eq_left (by omega : k ≤ C'.length)] using hjl
  have hjC : j < C.length := by omega
  have hg0 : C[j]? = some (C[j]) := by simp [List.getElem?_eq_getElem hjC]
  have h := hrep j (C[j]) hg0
  have hCj : (C'.take k)[j]? = C'[j]? := by
    rw [List.getElem?_take]
    simp [hjk]
  rw [hCj] at hj
  rcases (hgate (C[j]) (List.mem_of_getElem? hg0)).1 with hand | hor | hnot
  · have hne : (C[j]).op ≠ GateOp.not := by simp [hand]
    have hg' := h.2 hne
    rw [hj] at hg'
    cases hg'
    exact Or.inl hand
  · have hne : (C[j]).op ≠ GateOp.not := by simp [hor]
    have hg' := h.2 hne
    rw [hj] at hg'
    cases hg'
    exact Or.inr hor
  · by_cases hb : readAt (C.take j) (C[j]) y = true
    · have hg' := (h.1 hnot).1 hb
      rw [hj] at hg'
      cases hg'
      exact Or.inr rfl
    · have hb' : readAt (C.take j) (C[j]) y = false := Bool.eq_false_of_ne_true hb
      have hg' := (h.1 hnot).2 hb'
      rw [hj] at hg'
      cases hg'
      exact Or.inl rfl

lemma agree {n : ℕ} (C C' : List Gate) (X : Set (Fin n → Bool)) (y : Fin n → Bool)
    (hgate : ∀ g ∈ C, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hy : y ∈ X)
    (hleast : ∀ u ∈ X, above y u)
    (hstable : ∀ (j : ℕ) (g : Gate), C[j]? = some g → g.op = GateOp.not →
      readAt (C.take j) g y = false → ∀ z ∈ X, readAt (C.take j) g z = false)
    (hlen : C'.length = C.length)
    (hrep : ∀ (j : ℕ) (g : Gate), C[j]? = some g →
      (g.op = GateOp.not →
        (readAt (C.take j) g y = true → C'[j]? = some ⟨GateOp.or, []⟩) ∧
        (readAt (C.take j) g y = false → C'[j]? = some ⟨GateOp.and, []⟩)) ∧
      (g.op ≠ GateOp.not → C'[j]? = some g)) :
    ∀ x ∈ X, Circuit.wires ⟨C', 0⟩ (List.ofFn x) = Circuit.wires ⟨C, 0⟩ (List.ofFn x) := by
  induction C using List.reverseRecOn generalizing C' with
  | nil =>
      intro x hx
      have hC' : C' = [] := by simpa using hlen
      simp [hC', Circuit.wires]
  | append_singleton C0 g ih =>
      intro x hx
      have hlen0 : (C'.take C0.length).length = C0.length := by
        simp [hlen]
      have hgate0 : ∀ a ∈ C0, (a.op = GateOp.and ∨ a.op = GateOp.or ∨ a.op = GateOp.not) ∧
          a.inputs.length ≤ 2 := fun a ha => hgate a (List.mem_append_left [g] ha)
      have hstable0 : ∀ (j : ℕ) (g0 : Gate), C0[j]? = some g0 → g0.op = GateOp.not →
          readAt (C0.take j) g0 y = false → ∀ z ∈ X, readAt (C0.take j) g0 z = false := by
        intro j g0 hj hnot hfalse z hz
        have hj0 : j < C0.length := (List.getElem?_eq_some_iff.mp hj).1
        have hjC : (C0 ++ [g])[j]? = some g0 := by
          rw [List.getElem?_append_left hj0]
          exact hj
        have hfalse' : readAt ((C0 ++ [g]).take j) g0 y = false := by
          simpa [List.take_append_of_le_length (Nat.le_of_lt hj0)] using hfalse
        have := hstable j g0 hjC hnot hfalse' z hz
        simpa [List.take_append_of_le_length (Nat.le_of_lt hj0)] using this
      have hrep0 : ∀ (j : ℕ) (g0 : Gate), C0[j]? = some g0 →
          (g0.op = GateOp.not →
            (readAt (C0.take j) g0 y = true → (C'.take C0.length)[j]? = some ⟨GateOp.or, []⟩) ∧
            (readAt (C0.take j) g0 y = false → (C'.take C0.length)[j]? = some ⟨GateOp.and, []⟩)) ∧
          (g0.op ≠ GateOp.not → (C'.take C0.length)[j]? = some g0) := by
        intro j g0 hj
        have hj0 : j < C0.length := (List.getElem?_eq_some_iff.mp hj).1
        have hjC : (C0 ++ [g])[j]? = some g0 := by
          rw [List.getElem?_append_left hj0]
          exact hj
        have h := hrep j g0 hjC
        have htake : C0.take j = (C0 ++ [g]).take j := by
          simp [List.take_append_of_le_length (Nat.le_of_lt hj0)]
        have hCtake : (C'.take C0.length)[j]? = C'[j]? := by
          rw [List.getElem?_take]
          simp [hj0]
        constructor
        · intro hnot
          rcases h.1 hnot with ⟨ht, hf⟩
          constructor
          · intro hy1
            have := ht (by simpa [htake] using hy1)
            simpa [hCtake] using this
          · intro hy1
            have := hf (by simpa [htake] using hy1)
            simpa [hCtake] using this
        · intro hne
          have := h.2 hne
          simpa [hCtake] using this
      have ihx := ih (C'.take C0.length) hgate0 hstable0 hlen0 hrep0 x hx
      have ihy := ih (C'.take C0.length) hgate0 hstable0 hlen0 hrep0 y hy
      have hlast : (C0 ++ [g])[C0.length]? = some g := by
        simp [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
      have hrepL := hrep C0.length g hlast
      have hg' : ∃ g' : Gate, C'[C0.length]? = some g' ∧
          (g.op = GateOp.not →
            (readAt C0 g y = true → g' = ⟨GateOp.or, []⟩) ∧
            (readAt C0 g y = false → g' = ⟨GateOp.and, []⟩)) ∧
          (g.op ≠ GateOp.not → g' = g) := by
        by_cases hnot : g.op = GateOp.not
        · rcases (hrepL.1 hnot) with ⟨ht, hf⟩
          by_cases hb : readAt C0 g y = true
          · refine ⟨⟨GateOp.or, []⟩, ht (by simpa [List.take_append_of_le_length (Nat.le_refl _)] using hb), ?_, ?_⟩
            · intro _
              exact ⟨fun _ => rfl, fun hfalse => by simp [hb] at hfalse⟩
            · intro hne
              exact (hne hnot).elim
          · have hb' : readAt C0 g y = false := Bool.eq_false_of_ne_true hb
            refine ⟨⟨GateOp.and, []⟩, hf (by simpa [List.take_append_of_le_length (Nat.le_refl _)] using hb'), ?_, ?_⟩
            · intro _
              exact ⟨fun htrue => by simp [hb'] at htrue, fun _ => rfl⟩
            · intro hne
              exact (hne hnot).elim
        · refine ⟨g, hrepL.2 hnot, ?_, fun _ => rfl⟩
          · intro hneq
            exact (hnot hneq).elim
      obtain ⟨g', hg'some, hg'not, hg'eq⟩ := hg'
      have hC' : C' = C'.take C0.length ++ [g'] := by
        have hlen1 : C'.length = C0.length + 1 := by simpa using hlen
        have hdrop : C'.drop C0.length = [g'] := by
          have hlt : C0.length < C'.length := by omega
          have hcons : C'.drop C0.length = C'[C0.length] :: C'.drop (C0.length + 1) :=
            List.drop_eq_getElem_cons hlt
          have htail : C'.drop (C0.length + 1) = [] := by simp [hlen1]
          have hget : C'[C0.length] = g' := by
            have hgq : C'[C0.length]? = some g' := hg'some
            simpa [List.getElem?_eq_getElem hlt] using hgq
          simp [hcons, htail, hget]
        simpa [hdrop] using (List.take_append_drop C0.length C').symm
      rw [hC', wires_snoc, wires_snoc, ihx]
      have hread (z : Fin n → Bool) :
          readAt C0 g z =
            (g.inputs.map fun i =>
              (Circuit.wires ⟨C0, 0⟩ (List.ofFn z)).getD i false).headD false := by
        rfl
      by_cases hnot : g.op = GateOp.not
      · have hpair := hg'not hnot
        by_cases hb : readAt C0 g y = true
        · have hg'id : g' = ⟨GateOp.or, []⟩ := hpair.1 hb
          subst hg'id
          have htrue_x : readAt C0 g x = true := by
            have hmono := wires_mono (C'.take C0.length)
              (fun a ha => take_andOr hgate hlen hrep (k := C0.length) (by simp) ha)
              (hleast x hx)
            cases hinputs : g.inputs with
            | nil =>
                unfold readAt at hb
                rw [hinputs, List.map_nil] at hb
                simp at hb
            | cons i rest =>
                have hyi : (Circuit.wires ⟨C0, 0⟩ (List.ofFn y)).getD i false = true := by
                  unfold readAt at hb
                  rw [hinputs, List.map_cons, List.headD_cons] at hb
                  exact hb
                have hyi' : (Circuit.wires ⟨C'.take C0.length, 0⟩ (List.ofFn y)).getD i false = true := by
                  have htrans := ihy
                  rw [htrans]
                  exact hyi
                have hxi' := hmono i hyi'
                unfold readAt
                rw [hinputs, List.map_cons, List.headD_cons]
                rw [← ihx]
                exact hxi'
          simp only [GateOp.eval, hnot, eval_const_or]
          unfold readAt at htrue_x
          rw [htrue_x]
          rfl
        · have hb' : readAt C0 g y = false := Bool.eq_false_of_ne_true hb
          have hg'id : g' = ⟨GateOp.and, []⟩ := hpair.2 hb'
          subst hg'id
          have hfalse_x : readAt C0 g x = false := by
            have := hstable C0.length g hlast hnot
              (by simpa [List.take_append_of_le_length (Nat.le_refl _)] using hb') x hx
            simpa [List.take_left] using this
          simp only [GateOp.eval, hnot]
          unfold readAt at hfalse_x
          rw [hfalse_x]
          simp [eval_const_and, Bool.not_false]
      · have hg'id : g' = g := hg'eq hnot
        simp [hg'id]

end PEqualNP.Outside.L_meta_749

open PEqualNP.Outside.L_meta_749 PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.L_meta_749 : ∀ (n : ℕ) (C C' : List PEqualNP.CircuitLowerBounds.Gate) (X : Set (Fin n → Bool)) (y : Fin n → Bool), (∀ g ∈ C, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → y ∈ X → (∀ u ∈ X, ∀ p : Fin n, y p = true → u p = true) → (∀ (j1 : ℕ) (g1 : PEqualNP.CircuitLowerBounds.Gate), C[j1]? = some g1 → g1.op = PEqualNP.CircuitLowerBounds.GateOp.not → ((g1.inputs.map (fun i1 => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨C.take j1, 0⟩ (List.ofFn y)).getD i1 false)).headD false) = false → ∀ z ∈ X, ((g1.inputs.map (fun i2 => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨C.take j1, 0⟩ (List.ofFn z)).getD i2 false)).headD false) = false) → C'.length = C.length → (∀ (j2 : ℕ) (g2 : PEqualNP.CircuitLowerBounds.Gate), C[j2]? = some g2 → (g2.op = PEqualNP.CircuitLowerBounds.GateOp.not → (((g2.inputs.map (fun i3 => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨C.take j2, 0⟩ (List.ofFn y)).getD i3 false)).headD false) = true → C'[j2]? = some ({ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] } : PEqualNP.CircuitLowerBounds.Gate)) ∧ (((g2.inputs.map (fun i4 => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨C.take j2, 0⟩ (List.ofFn y)).getD i4 false)).headD false) = false → C'[j2]? = some ({ op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [] } : PEqualNP.CircuitLowerBounds.Gate))) ∧ (g2.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not → C'[j2]? = some g2)) → ∀ x ∈ X, ∀ w : ℕ, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨C', 0⟩ (List.ofFn x)).getD w false = (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨C, 0⟩ (List.ofFn x)).getD w false := by
  intro n C C' X y hgate hy hleast hstable hlen hrep x hx w
  have hleast' : ∀ u ∈ X, above y u := by
    intro u hu p hp
    exact hleast u hu p hp
  have hstable' : ∀ (j : ℕ) (g : Gate), C[j]? = some g → g.op = GateOp.not →
      readAt (C.take j) g y = false → ∀ z ∈ X, readAt (C.take j) g z = false := by
    intro j g hj hnot hfalse z hz
    exact hstable j g hj hnot hfalse z hz
  rw [agree C C' X y hgate hy hleast' hstable' hlen hrep x hx]
