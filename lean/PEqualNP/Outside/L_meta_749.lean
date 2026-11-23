import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_749

open PEqualNP.CircuitLowerBounds

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma run_circuit (gs : List Gate) (x : List Bool) :
    Circuit.wires ⟨gs, 0⟩ x = run gs x := rfl

lemma run_append_gate (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x =
      run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]

def Above (v v' : List Bool) : Prop :=
  v.length = v'.length ∧ ∀ i, v.getD i false = true → v'.getD i false = true

lemma getD_ge {α : Type} (l : List α) (d : α) (i : ℕ) (hi : l.length ≤ i) :
    l.getD i d = d := by
  induction l generalizing i with
  | nil => simp
  | cons a l ih =>
    cases i with
    | zero => simp at hi
    | succ j =>
      rw [List.getD_cons_succ]
      apply ih
      simp at hi
      omega

lemma getD_append_left {α : Type} (l l' : List α) (d : α) (i : ℕ) (hi : i < l.length) :
    (l ++ l').getD i d = l.getD i d := by
  induction l generalizing i with
  | nil => simp at hi
  | cons a l ih =>
    cases i with
    | zero => simp
    | succ j =>
      rw [List.cons_append, List.getD_cons_succ]
      apply ih
      simp at hi
      omega

lemma getD_snoc_last {α : Type} (l : List α) (a d : α) :
    (l ++ [a]).getD l.length d = a := by
  induction l with
  | nil => simp
  | cons b l ih =>
    rw [List.cons_append, List.length_cons, List.getD_cons_succ]
    exact ih

lemma above_inputs {n : ℕ} {x y : Fin n → Bool}
    (hxy : ∀ p : Fin n, x p = true → y p = true) :
    Above (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp, ?_⟩
  intro i hi
  by_cases hin : i < n
  · rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left hin] at hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left hin]
    simpa using hxy ⟨i, hin⟩ (by simpa using hi)
  · rw [getD_ge _ _ _ (by simp; omega)] at hi
    simp at hi

lemma above_snoc {v v' : List Bool} {a a' : Bool} (h : Above v v')
    (ha : a = true → a' = true) : Above (v ++ [a]) (v' ++ [a']) := by
  refine ⟨by simp [h.1], ?_⟩
  intro i hi
  by_cases hiv : i < v.length
  · rw [getD_append_left v [a] false i hiv] at hi
    rw [getD_append_left v' [a'] false i (Nat.lt_of_lt_of_eq hiv h.1)]
    exact h.2 i hi
  · have hlen : i < (v ++ [a]).length := by
      by_contra hge
      rw [getD_ge _ _ _ (le_of_not_gt hge)] at hi
      simp at hi
    have hiv' : i = v.length := by simp at hlen; omega
    subst hiv'
    rw [getD_snoc_last] at hi
    rw [h.1, getD_snoc_last]
    exact ha hi

lemma eval_mono (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or)
    {v v' : List Bool} (h : Above v v')
    (hv : g.op.eval (g.inputs.map fun i => v.getD i false) = true) :
    g.op.eval (g.inputs.map fun i => v'.getD i false) = true := by
  rcases hg with hg | hg
  · rw [hg] at hv ⊢
    simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq] at hv ⊢
    intro b hb
    obtain ⟨j, hj, rfl⟩ := hb
    exact h.2 j (hv _ ⟨j, hj, rfl⟩)
  · rw [hg] at hv ⊢
    simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at hv ⊢
    obtain ⟨b, ⟨j, hj, rfl⟩, hb⟩ := hv
    exact ⟨_, ⟨j, hj, rfl⟩, h.2 j hb⟩

lemma above_run (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ {v v' : List Bool}, Above v v' → Above (run gs v) (run gs v') := by
  induction gs with
  | nil => intro v v' h; exact h
  | cons g gs ih =>
    intro v v' h
    have step (w : List Bool) :
        run (g :: gs) w =
          run gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [step v, step v']
    apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
    apply above_snoc h
    intro ha
    exact eval_mono g (hgs g List.mem_cons_self) h ha

def headRead (gs : List Gate) (ins : List ℕ) (x : List Bool) : Bool :=
  (ins.map fun i => (run gs x).getD i false).headD false

lemma headRead_circuit (gs : List Gate) (ins : List ℕ) (x : List Bool) :
    headRead gs ins x =
      ((ins.map fun i => (Circuit.wires ⟨gs, 0⟩ x).getD i false).headD false) := by
  simp [headRead, run_circuit]

lemma headRead_mono {ins : List ℕ} {v v' : List Bool}
    (h : ∀ i, v.getD i false = true → v'.getD i false = true)
    (hv : (ins.map fun i => v.getD i false).headD false = true) :
    (ins.map fun i => v'.getD i false).headD false = true := by
  cases ins with
  | nil => simp at hv
  | cons i rest =>
    simp only [List.map_cons, List.headD_cons] at hv ⊢
    exact h i hv

lemma not_eval_head (ins : List ℕ) (v : List Bool) :
    GateOp.not.eval (ins.map fun i => v.getD i false) =
      !((ins.map fun i => v.getD i false).headD false) := by
  simp [GateOp.eval]

lemma and_nil : GateOp.and.eval ([] : List Bool) = true := by
  simp [GateOp.eval]

lemma or_nil : GateOp.or.eval ([] : List Bool) = false := by
  simp [GateOp.eval]

lemma bool_eq_false_of_ne_true {b : Bool} (h : b ≠ true) : b = false := by
  cases b <;> simp_all

lemma main : ∀ (n : ℕ) (C C' : List PEqualNP.CircuitLowerBounds.Gate) (X : Set (Fin n → Bool)) (y : Fin n → Bool), (∀ g ∈ C, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → y ∈ X → (∀ u ∈ X, ∀ p : Fin n, y p = true → u p = true) → (∀ (j1 : ℕ) (g1 : PEqualNP.CircuitLowerBounds.Gate), C[j1]? = some g1 → g1.op = PEqualNP.CircuitLowerBounds.GateOp.not → ((g1.inputs.map (fun i1 => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨C.take j1, 0⟩ (List.ofFn y)).getD i1 false)).headD false) = false → ∀ z ∈ X, ((g1.inputs.map (fun i2 => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨C.take j1, 0⟩ (List.ofFn z)).getD i2 false)).headD false) = false) → C'.length = C.length → (∀ (j2 : ℕ) (g2 : PEqualNP.CircuitLowerBounds.Gate), C[j2]? = some g2 → (g2.op = PEqualNP.CircuitLowerBounds.GateOp.not → (((g2.inputs.map (fun i3 => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨C.take j2, 0⟩ (List.ofFn y)).getD i3 false)).headD false) = true → C'[j2]? = some ({ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] } : PEqualNP.CircuitLowerBounds.Gate)) ∧ (((g2.inputs.map (fun i4 => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨C.take j2, 0⟩ (List.ofFn y)).getD i4 false)).headD false) = false → C'[j2]? = some ({ op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [] } : PEqualNP.CircuitLowerBounds.Gate))) ∧ (g2.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not → C'[j2]? = some g2)) → ∀ x ∈ X, ∀ w : ℕ, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨C', 0⟩ (List.ofFn x)).getD w false = (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨C, 0⟩ (List.ofFn x)).getD w false := by
  intro n C C' X y hops hy hup hfalse hlen hrep x hx w
  have gateAt (j : ℕ) (hj : j < C.length) :
      (C'[j]'(by rw [hlen]; exact hj)).op = GateOp.and ∨
        (C'[j]'(by rw [hlen]; exact hj)).op = GateOp.or := by
    have hsome : C[j]? = some C[j] := by simp [List.getElem?_eq_getElem, hj]
    obtain ⟨hif, helse⟩ := hrep j C[j] hsome
    obtain ⟨hop, _⟩ := hops C[j] (List.getElem_mem hj)
    have hidx : j < C'.length := by rw [hlen]; exact hj
    rcases hop with hop | hop | hop
    · have hgate : C'[j] = C[j] := by
        simpa [List.getElem?_eq_getElem hidx] using helse (by simp [hop])
      simp [hgate, hop]
    · have hgate : C'[j] = C[j] := by
        simpa [List.getElem?_eq_getElem hidx] using helse (by simp [hop])
      simp [hgate, hop]
    · cases hhr : headRead (C.take j) C[j].inputs (List.ofFn y)
      · have hgate : C'[j] = { op := GateOp.and, inputs := [] } := by
          simpa [List.getElem?_eq_getElem hidx] using (hif hop).2 hhr
        simp [hgate]
      · have hgate : C'[j] = { op := GateOp.or, inputs := [] } := by
          simpa [List.getElem?_eq_getElem hidx] using (hif hop).1 hhr
        simp [hgate]
  have agree : ∀ k, ∀ z ∈ X, run (C.take k) (List.ofFn z) = run (C'.take k) (List.ofFn z) := by
    intro k
    induction k with
    | zero => intro z hz; simp [run]
    | succ k ih =>
      intro z hz
      by_cases hk : k < C.length
      · have hC'k : k < C'.length := by rw [hlen]; exact hk
        rw [List.take_succ_eq_append_getElem hk, List.take_succ_eq_append_getElem hC'k,
          run_append_gate, run_append_gate, ih z hz]
        apply congrArg (fun b => run (C'.take k) (List.ofFn z) ++ [b])
        have hsome : C[k]? = some C[k] := by simp [List.getElem?_eq_getElem, hk]
        obtain ⟨hif, helse⟩ := hrep k C[k] hsome
        obtain ⟨hop, _⟩ := hops C[k] (List.getElem_mem hk)
        rcases hop with hop | hop | hop
        · have hgate : C'[k] = C[k] := by
            simpa [List.getElem?_eq_getElem hC'k] using helse (by simp [hop])
          simp [hgate]
        · have hgate : C'[k] = C[k] := by
            simpa [List.getElem?_eq_getElem hC'k] using helse (by simp [hop])
          simp [hgate]
        · cases hhr : headRead (C.take k) C[k].inputs (List.ofFn y)
          · have hgate : C'[k] = { op := GateOp.and, inputs := [] } := by
              simpa [List.getElem?_eq_getElem hC'k] using (hif hop).2 hhr
            have hzfalse := hfalse k C[k] hsome hop
              (by simpa [headRead, run_circuit] using hhr) z hz
            have hzfalse_run :
                (C[k].inputs.map fun i =>
                  (run (C'.take k) (List.ofFn z)).getD i false).headD false = false := by
              simpa [headRead, run_circuit, ih z hz] using hzfalse
            rw [hgate, hop, not_eval_head, hzfalse_run]
            simp [GateOp.eval]
          · have hgate : C'[k] = { op := GateOp.or, inputs := [] } := by
              simpa [List.getElem?_eq_getElem hC'k] using (hif hop).1 hhr
            rw [hgate, hop, not_eval_head]
            have hpre : ∀ g ∈ C'.take k, g.op = GateOp.and ∨ g.op = GateOp.or := by
              intro g hg
              obtain ⟨j, hj, hjg⟩ := List.mem_take_iff_getElem.mp hg
              have hjC : j < C.length := by
                have hj' : j < C'.length := (Nat.lt_min.mp hj).2
                rw [hlen] at hj'
                exact hj'
              have hidx : (C'.take k)[j]'(by rw [List.length_take]; exact hj) = C'[j] := by
                simpa using (List.getElem_take (xs := C') (j := k) (i := j)
                  (h := by rw [List.length_take]; exact hj))
              have := gateAt j hjC
              simpa [hjg, hidx] using this
            have hyes' : headRead (C'.take k) C[k].inputs (List.ofFn y) = true := by
              simpa [headRead, ih y hy] using hhr
            have hab := above_run (C'.take k) hpre (above_inputs (hup z hz))
            have hhead := headRead_mono hab.2 hyes'
            have hheadz :
                (C[k].inputs.map fun i =>
                  (run (C'.take k) (List.ofFn z)).getD i false).headD false = true := by
              simpa [headRead, ih z hz] using hhead
            rw [hheadz]
            simp [GateOp.eval]
      · have hk' : C.length ≤ k := le_of_not_gt hk
        have htakeC : C.take (k + 1) = C.take k := by
          rw [List.take_of_length_le hk', List.take_of_length_le (le_trans hk' (Nat.le_succ k))]
        have htakeC' : C'.take (k + 1) = C'.take k := by
          have hk2 : C'.length ≤ k := by rw [hlen]; exact hk'
          rw [List.take_of_length_le hk2, List.take_of_length_le (le_trans hk2 (Nat.le_succ k))]
        rw [htakeC, htakeC']
        exact ih z hz
  have hlists := agree C.length x hx
  rw [List.take_length, show C'.take C.length = C' by rw [← hlen, List.take_length]] at hlists
  rw [run_circuit, run_circuit, hlists]

end PEqualNP.Outside.L_meta_749

theorem PEqualNP.Outside.L_meta_749 : ∀ (n : ℕ) (C C' : List PEqualNP.CircuitLowerBounds.Gate) (X : Set (Fin n → Bool)) (y : Fin n → Bool), (∀ g ∈ C, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → y ∈ X → (∀ u ∈ X, ∀ p : Fin n, y p = true → u p = true) → (∀ (j1 : ℕ) (g1 : PEqualNP.CircuitLowerBounds.Gate), C[j1]? = some g1 → g1.op = PEqualNP.CircuitLowerBounds.GateOp.not → ((g1.inputs.map (fun i1 => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨C.take j1, 0⟩ (List.ofFn y)).getD i1 false)).headD false) = false → ∀ z ∈ X, ((g1.inputs.map (fun i2 => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨C.take j1, 0⟩ (List.ofFn z)).getD i2 false)).headD false) = false) → C'.length = C.length → (∀ (j2 : ℕ) (g2 : PEqualNP.CircuitLowerBounds.Gate), C[j2]? = some g2 → (g2.op = PEqualNP.CircuitLowerBounds.GateOp.not → (((g2.inputs.map (fun i3 => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨C.take j2, 0⟩ (List.ofFn y)).getD i3 false)).headD false) = true → C'[j2]? = some ({ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] } : PEqualNP.CircuitLowerBounds.Gate)) ∧ (((g2.inputs.map (fun i4 => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨C.take j2, 0⟩ (List.ofFn y)).getD i4 false)).headD false) = false → C'[j2]? = some ({ op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [] } : PEqualNP.CircuitLowerBounds.Gate))) ∧ (g2.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not → C'[j2]? = some g2)) → ∀ x ∈ X, ∀ w : ℕ, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨C', 0⟩ (List.ofFn x)).getD w false = (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨C, 0⟩ (List.ofFn x)).getD w false := by
  exact PEqualNP.Outside.L_meta_749.main
