import VerifiedGarbage.Proof.Argon2.X86_64.MemoryInit
import VerifiedGarbage.Proof.Argon2.X86_64.MemoryInitBlockCT
import VerifiedGarbage.Proof.Argon2.X86_64.MemoryInitLit

/-! # Matrix clearing uses only public addresses and the public allocation size -/

namespace VG.Proof.Argon2.X86_64.MemoryInit

open VG VG.X86_64 VG.Impl.Argon2.X86_64.MemoryInit
open VG.Proof.Argon2.X86_64.Initial (wordAt)

structure Ready (memory : Addr) (lanes q : Nat) (s : State) : Prop where
  space : Space s memory (1024 * (lanes * q))
  memoryRead : InRegions (s.rd ++ s.wr) (s.gpr .rbp + 232) 8
  lanesRead : InRegions (s.rd ++ s.wr) (s.gpr .rbp + 184) 8
  blocksRead : InRegions (s.rd ++ s.wr) (s.gpr .rbp + 240) 8
  memoryWord : wordAt s memoryOffset = memory
  lanesWord : wordAt s VG.Impl.Argon2.X86_64.Initial.lanesOffset = BitVec.ofNat 64 lanes
  blocksWord : wordAt s blocksOffset = BitVec.ofNat 64 (lanes * q)
  laneLength : s.gpr .r13 = BitVec.ofNat 64 q

def publicBases : List Reg := [.rbp, .rbx, .rsp, .r13]

def AgreeBases (s t : State) : Prop := ∀ r ∈ publicBases, s.gpr r = t.gpr r

theorem clearSetup_rel : RelCT isa AgreeBases clearSetupCode (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs publicBases)
    (fun _ _ h => Taint.agree_ofRegs h) (by taint_decide)

theorem clearLoop_rel : RelCT isa
    (fun s t => VG.X86_64.Taint.Agree (Taint.ofRegs (.rax :: .r14 :: publicBases)) s t)
    (.loop (.block clearWord) .ne) AgreeBases := by
  apply RelCT.taintRegs (τ := Taint.ofRegs (.rax :: .r14 :: publicBases))
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
  apply Taint.agree_ofRegs
  intro r hr
  simp only [List.mem_cons] at hr
  rcases hr with rfl | rfl | hr
  · rw [ha.count, hb.count, hp.1.blocksWord, hp.2.1.blocksWord]
  · rw [ha.destination, hb.destination, hp.1.memoryWord, hp.2.1.memoryWord]
  · have excluded : ∀ r ∈ publicBases, r ≠ .r14 ∧ r ≠ .rax ∧ r ≠ .rcx := by decide
    have hn := excluded r hr
    exact (ha.other r hn.1 hn.2.1 hn.2.2).trans
      ((hp.2.2 r hr).trans (hb.other r hn.1 hn.2.1 hn.2.2).symm)

end VG.Proof.Argon2.X86_64.MemoryInit
