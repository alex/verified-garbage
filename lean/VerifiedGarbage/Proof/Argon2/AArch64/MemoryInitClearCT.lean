import VerifiedGarbage.Proof.Argon2.AArch64.MemoryInit
import VerifiedGarbage.Proof.Argon2.AArch64.MemoryInitBlockCT
import VerifiedGarbage.Proof.Argon2.AArch64.MemoryInitLit

/-! # Matrix clearing uses only public addresses and the public allocation size -/

namespace VG.Proof.Argon2.AArch64.MemoryInit

open VG VG.AArch64 VG.Impl.Argon2.AArch64.MemoryInit
open VG.Proof.Argon2.AArch64.Initial (wordAt)

structure Ready (memory : Addr) (lanes q : Nat) (s : State) : Prop where
  space : Space s memory (1024 * (lanes * q))
  memoryRead : InRegions (s.rd ++ s.wr) (s.gpr .x19 + 232) 8
  lanesRead : InRegions (s.rd ++ s.wr) (s.gpr .x19 + 184) 8
  blocksRead : InRegions (s.rd ++ s.wr) (s.gpr .x19 + 240) 8
  memoryWord : wordAt s memoryOffset = memory
  lanesWord : wordAt s VG.Impl.Argon2.AArch64.Initial.lanesOffset = BitVec.ofNat 64 lanes
  blocksWord : wordAt s blocksOffset = BitVec.ofNat 64 (lanes * q)
  laneLength : s.gpr .x21 = BitVec.ofNat 64 q

def publicBases : List Reg := [.x19, .x24, .x21]

def AgreeBases (s t : State) : Prop := HPrime.AgreeRegs publicBases s t

theorem clearSetup_rel : RelCT isa AgreeBases clearSetupCode (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs publicBases)
    (fun _ _ h => h.taint) (by taint_decide)

theorem clearLoop_rel : RelCT isa
    (fun s t => VG.AArch64.Taint.Agree (Taint.ofRegs (.x8 :: .x22 :: publicBases)) s t)
    (.loop (.block clearWord) (.nonzero .x .x15)) AgreeBases := by
  apply RelCT.taintRegs (τ := Taint.ofRegs (.x8 :: .x22 :: publicBases))
    (fun _ _ h => h) publicBases
  taint_decide

theorem clear_rel (memory : Addr) (lanes q : Nat) :
    RelCT isa (fun s t => Ready memory lanes q s ∧ Ready memory lanes q t ∧ AgreeBases s t)
      clear AgreeBases := by
  let P := fun s t => Ready memory lanes q s ∧ Ready memory lanes q t ∧ AgreeBases s t
  have prep := (clearSetup_rel.mono (P' := P) (fun _ _ h => h.2.2)
    (fun _ _ h => h)).wpDep (fun s t h =>
      ⟨clearSetup_ok s h.1.memoryRead h.1.blocksRead,
        clearSetup_ok t h.2.1.memoryRead h.2.1.blocksRead⟩)
  refine prep.seq (clearLoop_rel.mono ?_ (fun _ _ h => h))
  intro a b h
  obtain ⟨_, s, t, hp, ha, hb⟩ := h
  refine ⟨ha.sp.trans (hp.2.2.1.trans hb.sp.symm), ?_⟩
  intro r hr
  have hr := RegSet.mem_ofList.mp hr
  simp only [List.mem_cons] at hr
  rcases hr with rfl | rfl | hr
  · rw [ha.count, hb.count, hp.1.blocksWord, hp.2.1.blocksWord]
  · rw [ha.destination, hb.destination, hp.1.memoryWord, hp.2.1.memoryWord]
  · have excluded : ∀ r ∈ publicBases, r ≠ .x22 ∧ r ≠ .x8 ∧ r ≠ .x3 ∧ r ≠ .x12 ∧ r ≠ .x15 := by decide
    have hn := excluded r hr
    exact (ha.other r hn.1 hn.2.1 hn.2.2.1 hn.2.2.2.1 hn.2.2.2.2).trans
      ((hp.2.2.2 r hr).trans (hb.other r hn.1 hn.2.1 hn.2.2.1 hn.2.2.2.1 hn.2.2.2.2).symm)

end VG.Proof.Argon2.AArch64.MemoryInit
