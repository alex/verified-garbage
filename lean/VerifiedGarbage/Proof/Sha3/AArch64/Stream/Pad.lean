import VerifiedGarbage.Proof.Sha3.AArch64.Call
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Sha3.Contract
import VerifiedGarbage.Proof.Framework.Offset

/-!
# The SHA-3 sponge on AArch64: `pad`

The same structure as the x86-64 proof (`VG.Proof.Sha3.X86_64.Stream.Pad`),
inside the frame that saves `x30` (`WP.frameReg`).
-/

namespace VG.Proof.Sha3.AArch64.Stream.Pad

open VG VG.AArch64 VG.Impl.Sha3.AArch64.Stream
open VG.Spec.Sha3 (stateAt keccakF absorb pad rates Repr)
open VG.Proof.Sha3 (xorByte Rep stateAt_xorByte absorb_pad)

section
variable (s₀ : State)

abbrev st : Addr := s₀.gpr .x0
abbrev rt : Nat := (s₀.gpr .x1).toNat
abbrev pos : Nat := (s₀.gpr .x2).toNat
abbrev scr : Addr := s₀.gpr .x4
abbrev stR : Region := ⟨st s₀, 200⟩
abbrev scR : Region := ⟨scr s₀, 640⟩
/-- The frame saving `x30`, below the stack pointer. -/
abbrev stkR : Region := ⟨s₀.sp - 16, 16⟩

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = []
  wr : s₀.wr = [stR s₀, scR s₀]
  st_scr : (stR s₀).Disjoint (scR s₀)
  rate : rt s₀ ∈ rates
  pos_lt : pos s₀ < rt s₀

/-- The frame is below the stack pointer, and disjoint from the buffers. -/
structure Stack (s₀ : State) : Prop where
  sp16 : 16 ≤ s₀.sp.toNat
  st : (stkR s₀).Disjoint (stR s₀)
  scr : (stkR s₀).Disjoint (scR s₀)

theorem pre_of {s₀ : State} (h : Proof.Sha3.padAArch64.pre s₀) : Pre s₀ ∧ Stack s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨⟨h1, h2, h3, h7, h8⟩, ⟨h4, h5, h6⟩⟩

theorem x80 : ((0x80 : BitVec 16).setWidth 64).setWidth 8 = (0x80 : BitVec 8) := by decide

theorem keep_ne : ∀ r ∈ preserved, r ≠ .x9 ∧ r ≠ .x10 ∧ r ≠ .x11 ∧ r ≠ .x1 := by decide

/-- `pad` without its frame: the callee-saved registers but `x30` are kept. -/
theorem correctMain (v : Permutation) {s₀ : State} (hp : Pre s₀) :
    WP isa (padMainWith v.callee) s₀ fun s' => (∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s₀.gpr r) ∧
      s'.sp = s₀.sp ∧
      (∀ r ∈ preservedV, (s'.v r).extractLsb' 0 64 = (s₀.v r).extractLsb' 0 64) ∧
      Proof.Sha3.padAArch64.post s₀ s' := by
  have hr : 72 ≤ (s₀.gpr .x1).toNat ∧ (s₀.gpr .x1).toNat ≤ 168 := Proof.Sha3.rate_bounds hp.rate
  have hpl : (s₀.gpr .x2).toNat < (s₀.gpr .x1).toNat := hp.pos_lt
  have hin : ∀ j < 200, (stR s₀).Contains (st s₀ + BitVec.ofNat 64 j) 1 := fun j hj =>
    contains_offset (by omega) (by omega)
  have hw : ∀ j < 200, InRegions s₀.wr (st s₀ + BitVec.ofNat 64 j) 1 := fun j hj => by
    rw [hp.wr]; exact ⟨_, List.mem_cons_self .., hin j hj⟩
  have hw' : ∀ j < 200, InRegions (s₀.rd ++ s₀.wr) (st s₀ + BitVec.ofNat 64 j) 1 := fun j hj => by
    rw [hp.rd]; exact hw j hj
  unfold padMainWith
  refine WP.seq (wp_add fun s₁ u₁ => ?_)
  have e₁ : s₁.gpr .x9 + BitVec.ofNat 64 0 = st s₀ + BitVec.ofNat 64 ((s₀.gpr .x2).toNat) := by
    rw [u₁.gpr]; simp
  refine wp_ldrb (a := st s₀ + BitVec.ofNat 64 ((s₀.gpr .x2).toNat)) (by omega) e₁
    (by rw [u₁.rd, u₁.wr]; exact hw' _ (by omega)) fun s₂ u₂ => wp_eor fun s₃ u₃ =>
    wp_strb (a := st s₀ + BitVec.ofNat 64 ((s₀.gpr .x2).toNat)) (by omega)
      (by rw [u₃.other _ (by decide), u₂.other _ (by decide)]; exact e₁)
      (by rw [u₃.wr, u₂.wr, u₁.wr]; exact hw _ (by omega)) fun s₄ g₄ => ?_
  have k₄ : ∀ r, r ≠ .x9 → r ≠ .x10 → s₄.gpr r = s₀.gpr r := fun r h h' => by
    rw [g₄.gpr, u₃.other _ h', u₂.other _ h', u₁.other _ h]
  refine wp_add fun s₅ u₅ => wp_subImm (by decide) fun s₆ u₆ => ?_
  have e₆ : s₆.gpr .x9 + BitVec.ofNat 64 0 = st s₀ + BitVec.ofNat 64 ((s₀.gpr .x1).toNat - 1) := by
    rw [u₆.gpr, u₅.gpr, k₄ _ (by decide) (by decide), k₄ _ (by decide) (by decide)]
    simp only [st]
    rw [BitVec.add_zero]; exact Offset.add_sub_one64 _ _ (by omega)
  refine wp_ldrb (a := st s₀ + BitVec.ofNat 64 ((s₀.gpr .x1).toNat - 1)) (by omega) e₆
    (by rw [u₆.rd, u₆.wr, u₅.rd, u₅.wr, g₄.rd, g₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]
        exact hw' _ (by omega))
    fun s₇ u₇ => wp_movz fun s₈ u₈ => wp_eor fun s₉ u₉ =>
    wp_strb (a := st s₀ + BitVec.ofNat 64 ((s₀.gpr .x1).toNat - 1)) (by omega)
      (by rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide)]; exact e₆)
      (by rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, g₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact hw _ (by omega))
    fun s₁₀ g₁₀ => wp_mov fun s₁₁ u₁₁ => wp_nil ?_
  -- The two bytes written.
  have hb₁ : s₄.mem = s₀.mem.writeW (st s₀ + BitVec.ofNat 64 ((s₀.gpr .x2).toNat))
      (s₀.mem (st s₀ + BitVec.ofNat 64 ((s₀.gpr .x2).toNat)) ^^^ (s₀.gpr .x3).setWidth 8) := by
    rw [g₄.mem, u₃.gpr, u₂.gpr, u₂.other _ (by decide), u₁.other _ (by decide), u₃.mem, u₂.mem,
      u₁.mem, Proof.Sha3.xor_byte]
  have hb₂ : s₁₀.mem = s₄.mem.writeW (st s₀ + BitVec.ofNat 64 ((s₀.gpr .x1).toNat - 1))
      (s₄.mem (st s₀ + BitVec.ofNat 64 ((s₀.gpr .x1).toNat - 1)) ^^^ 0x80) := by
    rw [g₁₀.mem, u₉.gpr, u₈.gpr, u₈.other _ (by decide), u₇.gpr, u₉.mem, u₈.mem, u₇.mem, u₆.mem,
      u₅.mem, Proof.Sha3.xor_byte, x80]
  have hS : stateAt s₁₀.mem (st s₀) =
      xorByte (xorByte (stateAt s₀.mem (st s₀)) ((s₀.gpr .x2).toNat) ((s₀.gpr .x3).setWidth 8)) ((s₀.gpr .x1).toNat - 1) 0x80 := by
    rw [← stateAt_xorByte (m := s₀.mem) (m' := s₄.mem) (by omega)
      (by simp only [hb₁, Proof.Sha3.writeW8_apply, ↓reduceIte])
      (fun i hi hne => by
        simp only [hb₁, Proof.Sha3.writeW8_apply, Proof.Sha3.ne_of_lt200 hi (by omega) hne, ite_false])]
    exact stateAt_xorByte (by omega) (by simp only [hb₂, Proof.Sha3.writeW8_apply, ↓reduceIte])
      (fun i hi hne => by
        simp only [hb₂, Proof.Sha3.writeW8_apply, Proof.Sha3.ne_of_lt200 hi (by omega) hne, ite_false])
  have k₁₁ : ∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → r ≠ .x1 → s₁₁.gpr r = s₀.gpr r :=
    fun r h9 h10 h11 h1 => by
      rw [u₁₁.other _ h1, g₁₀.gpr, u₉.other _ h10, u₈.other _ h11, u₇.other _ h10, u₆.other _ h9,
        u₅.other _ h9, k₄ _ h9 h10]
  have sp₁₁ : s₁₁.sp = s₀.sp := by
    rw [u₁₁.sp, g₁₀.sp, u₉.sp, u₈.sp, u₇.sp, u₆.sp, u₅.sp, g₄.sp, u₃.sp, u₂.sp, u₁.sp]
  have e512 : Region.Sub ⟨scr s₀, 512⟩ (scR s₀) := Region.sub_prefix (by omega)
  refine call_ok v (st := st s₀) (scr := scr s₀)
    (by rw [k₁₁ _ (by decide) (by decide) (by decide) (by decide)])
    (by rw [u₁₁.gpr, g₁₀.gpr, u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
      u₆.other _ (by decide), u₅.other _ (by decide), k₄ _ (by decide) (by decide)])
    (hp.st_scr.sub_right e512)
    (by
      rw [u₁₁.wr, g₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, g₄.wr, u₃.wr, u₂.wr, u₁.wr, hp.wr]
      apply Covers.of_sub
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨stR s₀, by simp, 0, by simp, by simp⟩
      · exact ⟨scR s₀, by simp, 0, by simp, by simp⟩)
    fun s' _ _ sp' cs' vc' _ e' => ?_
  refine ⟨fun r hr h30 => ?_, by rw [sp', sp₁₁], (fun r hr => by
    rw [vc' r hr, u₁₁.vec, g₁₀.vec, u₉.vec, u₈.vec, u₇.vec, u₆.vec, u₅.vec, g₄.vec, u₃.vec, u₂.vec, u₁.vec]), fun msg hR hm => ?_⟩
  · have ne := keep_ne r hr
    rw [cs' r hr h30, k₁₁ r ne.1 ne.2.1 ne.2.2.1 ne.2.2.2]
  · rw [e', u₁₁.mem, hS, absorb_pad (by omega) (by omega), ← hm,
      show Rep ((s₀.gpr .x1).toNat) msg = stateAt s₀.mem (st s₀) from hR.symm]

/-- The state `padMain` starts in, inside the frame. -/
abbrev inner (s₀ : State) : State :=
  { s₀ with sp := s₀.sp - 16, mem := s₀.mem.write (s₀.sp - 16) 8 (s₀.gpr .x30) }

theorem correct (v : Permutation) {s₀ : State} (hp : Pre s₀) (hs : Stack s₀) :
    WP isa (Impl.Sha3.AArch64.Stream.padWith v.callee) s₀ fun s' =>
      abiPreserved s₀ s' ∧ Proof.Sha3.padAArch64.post s₀ s' := by
  have hpi : Pre (inner s₀) := ⟨hp.rd, hp.wr, hp.st_scr, hp.rate, hp.pos_lt⟩
  refine WP.frameReg (hn := by rw [v.padMain_depth]; decide) hs.sp16 (fun R hR => ?_) (WP.mono ((correctMain v) hpi) fun s' ⟨hk, hsp, hv, hpost⟩ => ?_)
  · rw [hp.wr] at hR
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl
    · exact hs.st
    · exact hs.scr
  · refine ⟨⟨fun r hr => ?_, rfl, hv⟩, fun msg hm hc => ?_⟩
    · by_cases h30 : r = .x30
      · subst h30; simp [State.write]
      · simp only [State.write, h30, ite_false]
        exact hk r hr h30
    · exact hpost msg (by
        show stateAt (inner s₀).mem (st s₀) = _
        rw [write_frame_state hs.st]; exact hm) hc

theorem agree₀ {s₁ s₂ : State} (hpub : Proof.Sha3.padAArch64.pub s₁ s₂) :
    VG.AArch64.Taint.Agree (VG.AArch64.Taint.ofRegs [.x0, .x1, .x2, .x4]) s₁ s₂ := by
  obtain ⟨p1, p2, p3, p4, hsp⟩ := hpub
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> assumption

/-- A state satisfying the precondition. -/
def sat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 136 | .x4 => 0x3000 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 200⟩, ⟨0x3000, 640⟩]

theorem pad_correct (v : Permutation) (s : State) (hs : Proof.Sha3.padAArch64.pre s) :
    ∃ t s', Exec isa (Impl.Sha3.AArch64.Stream.padWith v.callee) s t s' ∧ abiPreserved s s' ∧
      Proof.Sha3.padAArch64.post s s' := by
  obtain ⟨t, s', he, h⟩ := (correct v) (pre_of hs).1 (pre_of hs).2
  exact ⟨t, s', he, h⟩

theorem pad_ct (v : Permutation) : ConstantTime isa Proof.Sha3.padAArch64.pre Proof.Sha3.padAArch64.pub
    (Impl.Sha3.AArch64.Stream.padWith v.callee) := by
  obtain ⟨hint, hhint⟩ := v.padTaint
  exact VectorTaint.constantTime (Taint.ofRegs [.x0, .x1, .x2, .x4])
    (fun _ _ _ _ hp => agree₀ hp) hhint

theorem pad_verified (v : Permutation) :
    Verified AArch64.target (Impl.Sha3.AArch64.Stream.padWith v.callee) (Spec.Sha3.padContract AArch64.abi 16) :=
  Verified.of_correct (pad_correct v) (pad_ct v) (by
    sig_implies [Spec.Sha3.padContract, Spec.Sha3.padSig, Proof.Sha3.padAArch64, AArch64.abi,
      AArch64.argRegs] [Proof.Sha3.AArch64.Stream.Pad.sat] using Proof.Sha3.AArch64.Stream.Pad.sat)

end VG.Proof.Sha3.AArch64.Stream.Pad
