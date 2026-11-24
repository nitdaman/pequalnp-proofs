import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5028

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def stW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def wV (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stW x := rfl

lemma foldl_stepWire_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stW w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stW]
    omega

lemma foldl_stepWire_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stW w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stW w g).length := by simp [stW]; omega
    rw [ih (stW w g) hlt]
    simp [stW, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge_length (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]

lemma gateAt_eq_getElem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    gateAt C j = C.gates[j]'hj := by
  simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]

lemma wireVal_gate (n : ℕ) (C : Circuit) (x : Fin n → Bool) (j : ℕ)
    (hj : j < C.gates.length) :
    wV n C x (n + j) =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
        if i < n + j then wV n C x i else false) := by
  obtain ⟨pre, post, gj, hgs, hpre_len, hget⟩ := split_gates C.gates j hj
  have hgj : gateAt C j = gj := by rw [gateAt_eq_getElem C j hj, hget]
  rw [hgj]
  let w0 := pre.foldl stW (List.ofFn x)
  have hW0L : w0.length = n + j := by
    simp [w0, foldl_stepWire_length, hpre_len]
  have hCj : wV n C x (n + j) = gj.op.eval (gj.inputs.map fun i => w0.getD i false) := by
    unfold wV
    rw [wires_eq_foldl, hgs, List.foldl_append, List.foldl_cons]
    rw [foldl_stepWire_getD_lt post (stW w0 gj) (n + j) (by simp [stW]; omega)]
    simp [stW, List.getD_eq_getElem?_getD, hW0L]
  rw [hCj]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  by_cases hi : i < n + j
  · simp only [hi, ↓reduceIte]
    unfold wV
    rw [wires_eq_foldl, hgs, List.foldl_append]
    exact (foldl_stepWire_getD_lt (gj :: post) w0 i (by omega)).symm
  · simp only [hi, ↓reduceIte]
    exact getD_ge_length w0 i (by omega)

lemma wvGR (n : ℕ) (C : Circuit) (hrb : ReadsBack n C)
    (x : Fin n → Bool) (j : ℕ) (hj : j < C.gates.length) :
    wV n C x (n + j) =
      (gateAt C j).op.eval ((gateAt C j).inputs.map (wV n C x)) := by
  rw [wireVal_gate n C x j hj]
  congr 1
  refine List.map_congr_left fun i hi => ?_
  simp only [hrb j hj i hi, ↓reduceIte]

lemma combine {α : Type} (P : ℕ → Prop) (F : ℕ → α → Bool) (l : List ℕ)
    (h : ∀ i ∈ l, ∃ S : Finset ℕ, (∀ u ∈ S, P u) ∧
      ∀ x, F i x = true ↔ ∃ u ∈ S, F u x = true) :
    ∃ S : Finset ℕ, (∀ u ∈ S, P u) ∧
      ∀ x, (∃ i ∈ l, F i x = true) ↔ ∃ u ∈ S, F u x = true := by
  induction l with
  | nil => exact ⟨∅, by simp, by simp⟩
  | cons a l ih =>
    obtain ⟨S1, hS1, e1⟩ := h a (by simp)
    obtain ⟨S2, hS2, e2⟩ := ih (fun i hi => h i (List.mem_cons_of_mem a hi))
    refine ⟨S1 ∪ S2, ?_, ?_⟩
    · intro u hu
      rcases Finset.mem_union.mp hu with hu | hu
      · exact hS1 u hu
      · exact hS2 u hu
    · intro x
      constructor
      · rintro ⟨i, hi, hv⟩
        rcases List.mem_cons.mp hi with rfl | hi
        · obtain ⟨u, hu, hv'⟩ := (e1 x).mp hv
          exact ⟨u, Finset.mem_union_left _ hu, hv'⟩
        · obtain ⟨u, hu, hv'⟩ := (e2 x).mp ⟨i, hi, hv⟩
          exact ⟨u, Finset.mem_union_right _ hu, hv'⟩
      · rintro ⟨u, hu, hv⟩
        rcases Finset.mem_union.mp hu with hu | hu
        · exact ⟨a, by simp, (e1 x).mpr ⟨u, hu, hv⟩⟩
        · obtain ⟨i, hi, hv'⟩ := (e2 x).mpr ⟨u, hu, hv⟩
          exact ⟨i, List.mem_cons_of_mem a hi, hv'⟩

lemma or_wire (n : ℕ) (C : Circuit) (hm : Monotone2 C) (hrb : ReadsBack n C) :
    ∀ w, n ≤ w → w < n + C.size → (gateAt C (w - n)).op = GateOp.or →
      ∃ S : Finset ℕ, (∀ u ∈ S, u < w ∧ (u < n ∨ (gateAt C (u - n)).op = GateOp.and)) ∧
        ∀ x : Fin n → Bool, wV n C x w = true ↔ ∃ u ∈ S, wV n C x u = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hnw hw hor
    have hj : w - n < C.gates.length := by
      have : C.size = C.gates.length := rfl
      omega
    have hwj : w = n + (w - n) := by omega
    have hval : ∀ x : Fin n → Bool, wV n C x w = true ↔
        ∃ i ∈ (gateAt C (w - n)).inputs, wV n C x i = true := by
      intro x
      rw [hwj, wvGR n C hrb x (w - n) hj, hor]
      simp [GateOp.eval, List.any_eq_true]
    have hlt : ∀ i ∈ (gateAt C (w - n)).inputs, i < w := by
      intro i hi
      have := hrb (w - n) hj i hi
      omega
    obtain ⟨S, hS, hSe⟩ := combine (fun u => u < w ∧ (u < n ∨ (gateAt C (u - n)).op = GateOp.and))
      (fun i x => wV n C x i) (gateAt C (w - n)).inputs (by
        intro i hi
        by_cases hc : i < n ∨ (gateAt C (i - n)).op = GateOp.and
        · exact ⟨{i}, by simpa using ⟨hlt i hi, hc⟩, by simp⟩
        · have hin : n ≤ i := by omega
          have hjn : i - n < C.gates.length := by
            have : C.size = C.gates.length := rfl
            have := hlt i hi
            omega
          have hmem : C.gates[i - n]'hjn ∈ C.gates := List.getElem_mem hjn
          have hop := (hm _ hmem).1
          rw [← gateAt_eq_getElem C (i - n) hjn] at hop
          have hor' : (gateAt C (i - n)).op = GateOp.or := by
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
            rcases hop with h | h
            · exact absurd (Or.inr h) hc
            · exact h
          obtain ⟨Si, hSi, eSi⟩ := ih i (hlt i hi) hin
            (by have := hlt i hi; omega) hor'
          refine ⟨Si, ?_, eSi⟩
          intro u hu
          exact ⟨lt_trans (hSi u hu).1 (hlt i hi), (hSi u hu).2⟩)
    refine ⟨S, hS, ?_⟩
    intro x
    rw [hval x]
    exact hSe x

end PEqualNP.Outside.L_meta_5028

theorem PEqualNP.Outside.L_meta_5028 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → PEqualNP.MetaComplexity.NestedCover.ReadsBack x1 x2 → x1 ≤ x2.output → x2.output < x1 + x2.size → (PEqualNP.MetaComplexity.NestedCover.gateAt x2 (x2.output - x1)).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∃ (x8 : Finset ℕ), (∀ x9 ∈ x8, x9 < x2.output ∧ (x9 < x1 ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 (x9 - x1)).op = PEqualNP.CircuitLowerBounds.GateOp.and)) ∧ ∀ (x9 : Fin x1 → Bool), PEqualNP.MetaComplexity.circuitFun x1 x2 x9 = Bool.true ↔ ∃ x10 ∈ x8, PEqualNP.CircuitLowerBounds.wireValue x2 (List.ofFn x9) x10 = Bool.true := by
  intro x1 x2 hm hrb h1 h2 hor
  obtain ⟨S, hS, hSe⟩ := PEqualNP.Outside.L_meta_5028.or_wire x1 x2 hm hrb x2.output h1 h2 hor
  refine ⟨S, hS, fun x => ?_⟩
  exact hSe x
