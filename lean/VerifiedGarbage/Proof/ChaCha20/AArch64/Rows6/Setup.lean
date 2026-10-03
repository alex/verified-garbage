import VerifiedGarbage.Proof.ChaCha20.AArch64.Rows6.Rounds
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Setup

namespace VG.Proof.ChaCha20.AArch64.Rows6
open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Rows6
open VG.Spec.ChaCha20 (Word stateAt)
abbrev LoadSame := VG.Proof.ChaCha20.AArch64.Neon4.LoadSame

/-- A loaded vector's lane, including the per-block counter offset. -/
def input (s : State) (k : Fin 24) (j : Nat) : Word :=
  let w := s.mem.readW (s.gpr .x0 + BitVec.ofNat 64 (16 * (k.val % 4) + 4 * j)) 32
  if k.val % 4 = 3 ∧ j = 0 then w + BitVec.ofNat 32 (k.val / 4) else w

theorem input_same {s s' : State} (h : LoadSame s s') (k : Fin 24) (j : Nat) :
    input s' k j = input s k j := by rw [input, h.mem, h.gpr _ (by decide)]; rfl

theorem vword_read16 (m : Mem) (a : Addr) (j : Nat) (hj : j < 4) :
    vword (m.read a 16) j = m.readW (a + BitVec.ofNat 64 (4 * j)) 32 := by
  rw [read16, vword_ofVWords _ _ _ _ hj]
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;> rfl

theorem inputRowInto_ok (s : State) (k : Fin 24) (d : VReg)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 (16 * (k.val % 4))) 16)
    (hctr : InRegions (s.rd ++ s.wr) (s.gpr .x0 + 48) 4) :
    WP isa (.block (inputRowInto k d)) s fun u =>
      (∀ j, j < 4 → vword (u.v d) j = input s k j) ∧
      (∀ r, r ≠ d → u.v r = s.v r) ∧ LoadSame s u := by
  have ha : 16 * (k.val % 4) % 16 = 0 ∧ 16 * (k.val % 4) < 4096 * 16 := by omega
  change InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 48) 4 at hctr
  have hb : k.val / 4 < 4096 := by omega
  unfold inputRowInto
  split
  · rename_i hk
    apply WP.of_runBlock
    simp (config := {decide := true}) only [List.cons_append, List.nil_append, runBlock_cons, exec, addr,
      ha, ite_true, State.load, State.setV, hin, Option.bind_some, Option.map_some,
      isa, runStep_some]
    simp (config := {decide := true}) only [hctr, ite_true, Option.map_some, runStep_some,
      runBlock_cons, runBlock_nil, exec, hb, VOp.eval, State.read, Size.bits,
      State.write, State.setV, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq,
      Option.some.injEq, exists_eq_left']
    refine ⟨fun j hj => ?_, fun r hr => ?_, fun r hr => ?_,rfl,rfl,rfl,rfl⟩
    · rw [VG.Proof.ChaCha20.AArch64.Neon4.vword_insert _ _ (i := 0) (by decide) hj]
      simp only [input, hk, Nat.reduceMul, true_and]
      by_cases hj0 : j = 0
      · subst j; simp only [ite_true, Nat.mul_zero, Nat.add_zero]
        rfl
      · simp only [hj0, ite_false]
        rw [vword_read16 _ _ j hj, BitVec.add_assoc, ← BitVec.ofNat_add]
    · simp only [hr, ite_false]
    · simp only [hr, ite_false]
  · rename_i hk
    apply WP.of_runBlock
    simp only [List.append_nil, runBlock_cons, runBlock_nil, exec, addr,
      ha, and_self, ite_true, State.load, State.setV, hin, Option.bind_some, Option.map_some,
      isa, runStep_some, Option.some.injEq, exists_eq_left']
    refine ⟨fun j hj => ?_,fun r hr => ?_,fun r hr => ?_,rfl,rfl,rfl,rfl⟩
    · rw [vword_read16 _ _ j hj, BitVec.add_assoc, ← BitVec.ofNat_add]
      simp only [input, hk, false_and, ite_false]
    · exact RegUpd.v_setV_of_ne _ _ hr
    · rfl
structure Loaded (s₀ : State) (ks : List (Fin 24)) (s : State) : Prop where
  words : ∀ k ∈ ks, ∀ j, j < 4 → vword (s.v (vreg k)) j = input s₀ k j
  same : LoadSame s₀ s

theorem setupRow_ok {s₀ s : State} {ks : List (Fin 24)} (h : Loaded s₀ ks s) (k : Fin 24)
    (hin : ∀ k : Fin 24, InRegions (s₀.rd ++ s₀.wr)
      (s₀.gpr .x0 + BitVec.ofNat 64 (16 * (k.val % 4))) 16)
    (hctr : InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .x0 + 48) 4) :
    WP isa (.block (setupRow k)) s (Loaded s₀ (k :: ks)) := by
  have hi : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 (16 * (k.val % 4))) 16 := by
    rw [h.same.rd,h.same.wr,h.same.gpr _ (by decide)]; exact hin k
  have hc : InRegions (s.rd ++ s.wr) (s.gpr .x0 + 48) 4 := by
    rw [h.same.rd,h.same.wr,h.same.gpr _ (by decide)]; exact hctr
  refine (inputRowInto_ok s k (vreg k) hi hc).mono fun u ⟨hw,hv,hs⟩ => ?_
  refine ⟨fun l hl j hj => ?_, h.same.trans hs⟩
  by_cases e : l = k
  · subst e; rw [hw j hj,input_same h.same]
  · rw [hv _ (fun he => e ((vreg_inj l k).mp he))]
    exact h.words l ((List.mem_cons.mp hl).resolve_left e) j hj

theorem setupList_ok (ks : List (Fin 24)) {s₀ s : State} {done : List (Fin 24)}
    (h : Loaded s₀ done s)
    (hin : ∀ k : Fin 24, InRegions (s₀.rd ++ s₀.wr)
      (s₀.gpr .x0 + BitVec.ofNat 64 (16 * (k.val % 4))) 16)
    (hctr : InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .x0 + 48) 4) :
    WP isa (.block (ks.flatMap setupRow)) s fun u =>
      (∀ k ∈ ks ++ done, ∀ j, j < 4 → vword (u.v (vreg k)) j = input s₀ k j) ∧ LoadSame s₀ u := by
  induction ks generalizing s done with
  | nil => exact WP.block_nil ⟨h.words,h.same⟩
  | cons k ks ih =>
    refine WP.block_append ((setupRow_ok h k hin hctr).mono fun _ h' => ?_)
    exact (ih h').mono fun _ ⟨hw,hs⟩ => ⟨fun l hl j hj => hw l (by simpa [List.mem_append,
      List.mem_cons,or_assoc,or_left_comm,or_comm] using hl) j hj,hs⟩

theorem setup_words (s : State)
    (hin : ∀ k : Fin 24, InRegions (s.rd ++ s.wr)
      (s.gpr .x0 + BitVec.ofNat 64 (16 * (k.val % 4))) 16)
    (hctr : InRegions (s.rd ++ s.wr) (s.gpr .x0 + 48) 4) :
    WP isa (.block setup) s fun u =>
      (∀ k : Fin 24, ∀ j, j < 4 → vword (u.v (vreg k)) j = input s k j) ∧
      LoadSame s u ∧ u.v .v30 = VG.Impl.ChaCha20.AArch64.Neon4.rol8Table := by
  rw [setup]
  refine WP.block_append ((setupList_ok (List.finRange 24) (done := [])
    ⟨(fun _ h => by cases h),VG.Proof.ChaCha20.AArch64.Neon4.LoadSame.refl s⟩ hin hctr).mono fun a ⟨hw,hs⟩ => ?_)
  refine (VG.Proof.ChaCha20.AArch64.Neon4.setupTable_ok a).mono fun u ⟨ht,hv,has⟩ => ⟨?_,hs.trans has,ht⟩
  intro k j hj
  rw [hv (vreg k) (vreg_ne30 k), hw k (by simp) j hj]

theorem input_ctr (s : State) (k : Fin 24) (j : Nat) (hj : j < 4) :
    input s k j = (pack (fun b => ctr (stateAt s.mem (s.gpr .x0)) b) j)[k] := by
  rw [pack_get]
  simp only [Nat.mod_eq_of_lt hj, ctr, Vector.getElem_set, stateAt, Vector.getElem_ofFn]
  have he : (12 = 4 * (k.val % 4) + j) ↔ (k.val % 4 = 3 ∧ j = 0) := by omega
  have hoff : 16 * (k.val % 4) + 4 * j = 4 * (4 * (k.val % 4) + j) := by omega
  simp only [input, he, hoff]
  split
  · rename_i h
    rcases h with ⟨hrow,hj0⟩
    simp only [hrow,hj0]
  · rfl

theorem setup_ok (s : State)
    (hin : ∀ k : Fin 24, InRegions (s.rd ++ s.wr)
      (s.gpr .x0 + BitVec.ofNat 64 (16 * (k.val % 4))) 16)
    (hctr : InRegions (s.rd ++ s.wr) (s.gpr .x0 + 48) 4) :
    WP isa (.block setup) s fun u =>
      Holds (pack (fun b => ctr (stateAt s.mem (s.gpr .x0)) b)) u ∧
      LoadSame s u ∧ u.v .v30 = VG.Impl.ChaCha20.AArch64.Neon4.rol8Table := by
  refine (setup_words s hin hctr).mono fun u ⟨hu,hs,ht⟩ => ⟨?_,hs,ht⟩
  intro k j hj
  exact (hu k j hj).trans (input_ctr s k j hj)

end VG.Proof.ChaCha20.AArch64.Rows6
