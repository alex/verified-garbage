import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Rounds
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.ChaCha20.Keystream

namespace VG.Proof.ChaCha20.AArch64.Neon4

open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Neon4
open VG.Spec.ChaCha20 (Word stateAt)

theorem vword_dup (w : Word) {j : Nat} (hj : j < 4) : vword (ofVWords w w w w) j = w := by
  rw [vword_ofVWords _ _ _ _ hj]
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;> rfl

theorem vword_insert (v : BitVec 128) (w : Word) {i j : Nat} (hi : i < 4) (hj : j < 4) :
    vword (setLane v 32 i w) j = if j = i then w else vword v j := by
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  simp only [vword, setLane, BitVec.getLsbD_extractLsb', BitVec.getLsbD_or,
    BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes, hb, decide_true, Bool.true_and]
  by_cases h : j = i
  · subst h
    simp (disch := omega) [Nat.add_sub_cancel_left, decide_eq_true, decide_eq_false]
  · by_cases hlt : j < i
    · simp (disch := omega) [h, decide_eq_true]
    · simp (disch := omega) [h, decide_eq_true, decide_eq_false,
        BitVec.getLsbD_of_ge]

structure LoadSame (s s' : State) : Prop where
  gpr : ∀ r, r ≠ .x4 → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem LoadSame.refl (s : State) : LoadSame s s := ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
theorem LoadSame.trans {s₀ s₁ s₂ : State} (h : LoadSame s₀ s₁) (h' : LoadSame s₁ s₂) :
    LoadSame s₀ s₂ := ⟨fun r hr => (h'.gpr r hr).trans (h.gpr r hr),
      h'.mem.trans h.mem, h'.rd.trans h.rd, h'.wr.trans h.wr, h'.sp.trans h.sp⟩

def input (s : State) (k : Fin 16) (j : Nat) : Word :=
  let w := s.mem.readW (s.gpr .x0 + BitVec.ofNat 64 (4 * k)) 32
  if k = 12 then w + BitVec.ofNat 32 j else w

theorem input_same {s s' : State} (h : LoadSame s s') (k : Fin 16) (j : Nat) :
    input s' k j = input s k j := by rw [input, h.mem, h.gpr _ (by decide)]; rfl

theorem inputWord_ok (s : State) (k : Fin 16)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 (4 * k)) 4) :
    WP isa (.block (inputWord k)) s fun s' =>
      (∀ j, j < 4 → vword (s'.v .v31) j = input s k j) ∧
      (∀ r, r ≠ .v31 → s'.v r = s.v r) ∧ LoadSame s s' := by
  have ha : 4 * k.val % 4 = 0 ∧ 4 * k.val < 4096 * 4 := by omega
  unfold inputWord
  split
  · rename_i hk
    subst k
    apply WP.of_runBlock
    simp (config := {decide := true}) only [List.cons_append, List.nil_append,
      runBlock_cons, runBlock_nil, exec, addr, Size.bytes, ite_true,
      State.load, hin, Option.bind_some, Option.map_some, isa, runStep_some,
      Option.some.injEq, exists_eq_left', VOp.eval, State.read,
      RegUpd.gpr_write, RegUpd.gpr_setV, RegUpd.v_write, RegUpd.v_setV,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]
    refine ⟨fun j hj => ?_, fun r hr => ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    · simp only [vword_insert _ _ (i := 3) (by decide) hj,
        vword_insert _ _ (i := 2) (by decide) hj,
        vword_insert _ _ (i := 1) (by decide) hj, vword_dup _ hj, input,
        ite_true, Mem.readW, BitVec.setWidth_eq]
      rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;>
        simp (config := {decide := true}) [Size.bits, BitVec.add_assoc]
    · simp only [hr, ite_false]
    · simp only [RegUpd.gpr_setV, RegUpd.gpr_write, hr, ite_false]
  · rename_i hk
    apply WP.of_runBlock
    simp only [List.append_nil, runBlock_cons, runBlock_nil, exec, addr, Size.bytes,
      ha, and_self, ite_true, State.load, hin, Option.bind_some, Option.map_some,
      isa, runStep_some, Option.some.injEq, exists_eq_left', VOp.eval,
      RegUpd.gpr_write_self, BitVec.setWidth_eq]
    refine ⟨fun j hj => ?_, fun r hr => ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    · rw [RegUpd.v_setV_self, vword_dup _ hj]
      simp only [input, hk, ite_false, Mem.readW,
        BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq]
    · exact RegUpd.v_setV_of_ne _ _ hr
    · exact RegUpd.gpr_write_of_ne _ _ _ hr

structure Loaded (s₀ : State) (ks : List (Fin 16)) (s : State) : Prop where
  words : ∀ k ∈ ks, ∀ j, j < 4 → vword (s.v (vreg k)) j = input s₀ k j
  same : LoadSame s₀ s

theorem setupWord_ok {s₀ s : State} {ks : List (Fin 16)} (h : Loaded s₀ ks s) (k : Fin 16)
    (hin : ∀ k : Fin 16, InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .x0 + BitVec.ofNat 64 (4 * k)) 4) :
    WP isa (.block (setupWord k)) s (Loaded s₀ (k :: ks)) := by
  have hi : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 (4 * k)) 4 := by
    rw [h.same.rd, h.same.wr, h.same.gpr _ (by decide)]; exact hin k
  apply WP.block_append
  refine (inputWord_ok s k hi).mono fun s' ⟨hw, hv, hs⟩ => ?_
  apply WP.of_runBlock
  simp only [runBlock_cons, runBlock_nil, exec, VOp.eval, isa, runStep_some,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨fun l hl j hj => ?_, ?_⟩
  · rw [RegUpd.v_setV]
    by_cases e : l = k
    · subst e; rw [ite_eq_left rfl, hw j hj, input_same h.same]
    · rw [ite_eq_right (fun he => e ((vreg_inj l k).mp he)), hv _ (vreg_ne l)]
      exact h.words l ((List.mem_cons.mp hl).resolve_left e) j hj
  · exact h.same.trans ⟨hs.gpr, hs.mem, hs.rd, hs.wr, hs.sp⟩

theorem setupList_ok (ks : List (Fin 16)) {s₀ s : State} {done : List (Fin 16)}
    (h : Loaded s₀ done s)
    (hin : ∀ k : Fin 16, InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .x0 + BitVec.ofNat 64 (4 * k)) 4) :
    WP isa (.block (ks.flatMap setupWord)) s fun s' =>
      (∀ k ∈ ks ++ done, ∀ j, j < 4 → vword (s'.v (vreg k)) j = input s₀ k j) ∧ LoadSame s₀ s' := by
  induction ks generalizing s done with
  | nil => exact WP.block_nil ⟨h.words, h.same⟩
  | cons k ks ih =>
    refine WP.block_append ((setupWord_ok h k hin).mono fun _ h' => ?_)
    exact (ih h').mono fun _ ⟨hw, hs⟩ => ⟨fun l hl j hj => hw l (by simpa [List.mem_append,
      List.mem_cons, or_assoc, or_left_comm, or_comm] using hl) j hj, hs⟩

theorem setup_ok (s : State)
    (hin : ∀ k : Fin 16, InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 (4 * k)) 4) :
    WP isa (.block setup) s fun s' =>
      Holds (fun j => ctr (stateAt s.mem (s.gpr .x0)) j) s' ∧ LoadSame s s' := by
  refine (setupList_ok (List.finRange 16) (done := [])
    ⟨(fun _ h => by cases h), LoadSame.refl s⟩ hin).mono fun _ ⟨hw, hs⟩ => ⟨?_, hs⟩
  intro k j hj
  rw [hw k (by simp) j hj]
  simp only [input, ctr, Vector.getElem_set, stateAt, Vector.getElem_ofFn, Fin.getElem_fin]
  by_cases hk : k = 12
  · subst k; rfl
  · have hk' : k.val ≠ 12 := fun e => hk (Fin.ext e)
    simp only [hk, Ne.symm hk', ite_false]

end VG.Proof.ChaCha20.AArch64.Neon4
