import VerifiedGarbage.Proof.MlKem.X86.Piece
import VerifiedGarbage.Impl.MlKem.X86.Basic

/-!
# ML-KEM on x86 (32-bit): leaf functions

Untrusted: everything here is checked by Lean. A function that calls no
other one (`Impl.MlKem.X86.leaf`) pushes its caller's `ebx`, `esi`, `edi`
and `ebp` in a frame of 16 bytes, runs its body, reloads `esi`, `edi` and
`ebp` from the frame, and pops the frame into `ebx`. If the body changes
memory only within regions `W` apart from the frame and the return
address, the function meets the calling convention (`Piece.leaf`).
-/

namespace VG.Proof.MlKem.X86

open VG VG.X86 VG.Impl.MlKem.X86

theorem ea_at (s : State) (b : Reg) (d : Nat) : s.ea (at_ b d) = addr (s.gpr b) d := rfl

/-- The last word a frame's pop loads is the register it leaves. -/
theorem popReg_last (d : Reg) (hd : d ≠ .esp) :
    ∀ (k : Nat) (s : State), (popReg s d (k + 1)).gpr d =
      s.mem.readW ((s.gpr .esp + BitVec.ofNat 32 (4 * k)).setWidth 64) 32
  | 0, s => by
    simp only [popReg, State.setReg, ite_eq_right hd, ite_true, Nat.mul_zero, BitVec.add_zero]
  | k + 1, s => by
    rw [popReg.eq_2, popReg_last d hd k]
    simp only [State.setReg, ite_true]
    congr 2
    rw [BitVec.add_assoc, show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, ← BitVec.ofNat_add]
    congr 2
    omega

section
variable (s₀ : State)

/-- The entry state's stack pointer. -/
abbrev E0 : BitVec 32 := s₀.gpr .esp

/-- The state after the leaf's frame's push. -/
abbrev P0 : State := pushed saveRegs s₀

/-- The leaf's frame. -/
abbrev frameR : Region := below (E0 s₀) 16

/-- The return address. -/
abbrev retR : Region := ⟨(E0 s₀).setWidth 64, 4⟩

end

theorem saveRegs_len : 4 * saveRegs.length = 16 := rfl

theorem P0_esp (s₀ : State) : (P0 s₀).gpr .esp = E0 s₀ - 16 := by
  rw [pushed_esp]; rfl

theorem P0_wr (s₀ : State) : (P0 s₀).wr = frameR s₀ :: s₀.wr := by
  rw [pushed_wr, saveRegs_len]

/-- Word `i` of the frame holds the register pushed `i`-th from the end. -/
theorem frame_word (s₀ : State) (hE : 16 ≤ (E0 s₀).toNat) {i : Nat} (hi : i < 4) :
    (P0 s₀).mem.readW (((P0 s₀).gpr .esp + BitVec.ofNat 32 (4 * i)).setWidth 64) 32 =
      s₀.gpr (saveRegs[3 - i]'(by simp [saveRegs]; omega)) :=
  pushed_word (rs := saveRegs) (s := s₀) (by decide) hE hi

/-- A word of the frame, at `esp + 4i` after the push, is within it. -/
theorem frame_contains (s₀ : State) (hE : 16 ≤ (E0 s₀).toNat) {i : Nat} (hi : i < 4) :
    (frameR s₀).Contains (((P0 s₀).gpr .esp + BitVec.ofNat 32 (4 * i)).setWidth 64) 4 := by
  rw [P0_esp]
  simp only [Region.Contains]
  have := (E0 s₀).isLt
  bv_omega

/-- What the body of a leaf leaves: memory changed only within `W`, apart
from the frame and the return address, and `esp` and the permissions as
the push left them. -/
structure LeafEnd (s₀ : State) (W : List Region) (s : State) : Prop where
  frame : Frame W (P0 s₀).mem s.mem
  esp : s.gpr .esp = (P0 s₀).gpr .esp
  rd : s.rd = (P0 s₀).rd
  wr : s.wr = (P0 s₀).wr

/-- The final state of a leaf whose body ends in `s`. -/
def leafFinal (s : State) : State :=
  popped .ebx 4 (((s.setReg .esi (s.mem.readW ((s.gpr .esp + BitVec.ofNat 32 8).setWidth 64) 32)).setReg
    .edi (s.mem.readW ((s.gpr .esp + BitVec.ofNat 32 4).setWidth 64) 32)).setReg
    .ebp (s.mem.readW ((s.gpr .esp + BitVec.ofNat 32 0).setWidth 64) 32))

theorem restore_run (s : State)
    (h : ∀ i < 3, InRegions (s.rd ++ s.wr) ((s.gpr .esp + BitVec.ofNat 32 (4 * i)).setWidth 64) 4) :
    WP isa (.block restore) s fun s' => popped .ebx 4 s' = leafFinal s := by
  have h8 := h 2 (by omega)
  have h4 := h 1 (by omega)
  have h0 := h 0 (by omega)
  simp only [Nat.reduceMul] at h8 h4 h0
  apply WP.of_runBlock
  simp (config := {decide := true}) only [restore, at_, runBlock_cons, runStep_some, runBlock_nil, exec,
    readSrc, State.ea, State.load32, State.setReg, Option.map_some, h8, h4, h0, ite_true, ite_false,
    Option.some.injEq, exists_eq_left']
  rfl

/-- The postcondition of a leaf whose body satisfies `B`. -/
def LeafPost (B : State → Prop) (s₀ s' : State) : Prop :=
  abiPreserved s₀ s' ∧ s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧
    ∃ s, B s ∧ s'.mem = s.mem ∧ s'.gpr .eax = s.gpr .eax

theorem leafFinal_ok {s₀ s : State} {W : List Region} {B : State → Prop}
    (hE : 16 ≤ (E0 s₀).toNat)
    (hW : ∀ r ∈ W, (frameR s₀).Disjoint r ∧ (retR s₀).Disjoint r) (h : LeafEnd s₀ W s) (hb : B s) :
    LeafPost B s₀ (leafFinal s) := by
  have hwf : ∀ i (hi : i < 4), s.mem.readW ((s.gpr .esp + BitVec.ofNat 32 (4 * i)).setWidth 64) 32 =
      s₀.gpr (saveRegs[3 - i]'(by simp [saveRegs]; omega)) := fun i hi => by
    rw [h.esp, h.frame.readW (frame_contains s₀ hE hi) (fun r hr => (hW r hr).1) (by decide),
      frame_word s₀ hE hi]
  have hm : (leafFinal s).mem = s.mem := by simp [leafFinal, State.setReg]
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_, ?_, s, hb, hm, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [leafFinal, popped, popReg_last _ (by decide) 3]
      simp only [State.setReg, show Reg.esp ≠ Reg.ebp by decide, show Reg.esp ≠ Reg.edi by decide,
        show Reg.esp ≠ Reg.esi by decide, ite_false]
      exact hwf 3 (by omega)
    · rw [leafFinal, popped_gpr _ _ _ (by decide) (by decide)]
      simp only [State.setReg, show Reg.esi ≠ Reg.ebp by decide, show Reg.esi ≠ Reg.edi by decide,
        ite_false, ite_true]
      exact hwf 2 (by omega)
    · rw [leafFinal, popped_gpr _ _ _ (by decide) (by decide)]
      simp only [State.setReg, show Reg.edi ≠ Reg.ebp by decide, ite_false, ite_true]
      exact hwf 1 (by omega)
    · rw [leafFinal, popped_gpr _ _ _ (by decide) (by decide)]
      simp only [State.setReg, ite_true]
      exact hwf 0 (by omega)
    · rw [leafFinal, popped_esp]
      simp only [State.setReg, show Reg.esp ≠ Reg.ebp by decide, show Reg.esp ≠ Reg.edi by decide,
        show Reg.esp ≠ Reg.esi by decide, ite_false, h.esp, P0_esp]
      rw [show BitVec.ofNat 32 (4 * 4) = 16 from rfl, BitVec.sub_add_cancel]
  · rw [hm, h.frame.readW (Region.contains_self _ _) (fun r hr => (hW r hr).2) (by decide)]
    have hf := pushed_frame (rs := saveRegs) (s := s₀) (by decide) (by rw [saveRegs_len]; exact hE)
    rw [saveRegs_len] at hf
    refine hf.readW (Region.contains_self _ _) ?_ (by decide)
    simp only [List.mem_singleton, forall_eq]
    intro a h₁ h₂
    simp only [Region.Contains] at h₁ h₂
    have := (E0 s₀).isLt
    bv_omega
  · simp [leafFinal, State.setReg, popped_rd, h.rd]
  · simp only [leafFinal, popped_wr]
    simp only [State.setReg, h.wr, P0_wr]
    rfl
  · rw [leafFinal, popped_gpr _ _ _ (by decide) (by decide)]
    simp [State.setReg]

namespace Piece

variable {Pre : State → Prop} {Pub : State → State → Prop}

/-- A leaf, from its body. -/
theorem leaf {body : Prog isa} {B : State → State → Prop} (W : State → List Region)
    (hsp : NoSp body)
    (hE : ∀ s₀, Pre s₀ → 16 ≤ (E0 s₀).toNat ∧ (E0 s₀).toNat + 4 ≤ 2 ^ 32)
    (hW : ∀ s₀, Pre s₀ → ∀ r ∈ W s₀, (frameR s₀).Disjoint r ∧ (retR s₀).Disjoint r)
    (hpub : ∀ s₀ s₀', Pre s₀ → Pre s₀' → Pub s₀ s₀' → E0 s₀ = E0 s₀')
    (hb : Piece Pre Pub (fun s₀ s => s = P0 s₀) (fun s₀ s => LeafEnd s₀ (W s₀) s ∧ B s₀ s) body) :
    Piece Pre Pub (fun s₀ s => s = s₀) (fun s₀ s' => LeafPost (B s₀) s₀ s') (leaf body) := by
  refine Piece.frame (by decide) (by decide) (by decide) (fun i hi => ?_)
    (fun s₀ s h₀ e => by rw [e]; exact (hE s₀ h₀).1)
    (fun s₀ s₀' s s' h₀ h₀' hp e e' => by rw [e, e']; exact hpub _ _ h₀ h₀' hp) ?_
  · have e : X86.instrs (Code.seq body (.block restore)) = X86.instrs body ++ restore := rfl
    rw [e, List.mem_append] at hi
    rcases hi with hi | hi
    · exact hsp i hi
    · simp only [restore, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl <;> rfl
  refine Piece.seq (hb.mono (fun s₀ s _ ⟨s₁, e₁, e₂⟩ => e₁ ▸ e₂) fun _ _ _ h => h) ?_
  refine Piece.taint [.esp] (fun s₀ s h₀ ⟨he, hb'⟩ => ?_) ?_ (by taint_decide)
  · have hE' := hE s₀ h₀
    refine (restore_run s fun i hi => ?_).mono fun s' e => ?_
    · rw [he.rd, he.wr, he.esp, P0_wr]
      exact ⟨frameR s₀, List.mem_append_right _ (List.mem_cons_self ..),
        frame_contains s₀ hE'.1 (by omega)⟩
    · rw [show saveRegs.length = 4 from rfl, e]; exact leafFinal_ok hE'.1 (hW s₀ h₀) he hb'
  · intro s₀ s₀' s s' h₀ h₀' hp ⟨e, _⟩ ⟨e', _⟩ r hr
    simp only [List.mem_singleton] at hr
    subst hr
    rw [e.esp, e'.esp, P0_esp, P0_esp, hpub _ _ h₀ h₀' hp]

end Piece

end VG.Proof.MlKem.X86
