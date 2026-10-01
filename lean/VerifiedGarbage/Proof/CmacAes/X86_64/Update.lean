import VerifiedGarbage.Proof.CmacAes.X86_64.Contract
import VerifiedGarbage.Proof.Cmac.Mem
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Abi

/-!
# AES-CMAC on x86-64: `vg_cmac_aes_update`

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.CmacAes.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.CmacAes.X86_64

theorem offset_nat (i : Nat) : BitVec.ofInt 64 (i : Int) = BitVec.ofNat 64 i := rfl

/-- The memory after saving the registers. -/
def savedMem (s : State) : Mem :=
  saved.foldl (fun m (r, d) => m.writeW (s.gpr .r9 + BitVec.ofNat 64 d) (s.gpr r)) s.mem

theorem prologue_ok (s : State)
    (hw : ∀ d, 2064 ≤ d → d + 8 ≤ 2112 → InRegions s.wr (s.gpr .r9 + BitVec.ofNat 64 d) 8) :
    ∃ s', runBlock isa (save ++ setup) s = some s' ∧
      s'.gpr .rbx = s.gpr .rdi ∧ s'.gpr .rbp = s.gpr .rsi ∧ s'.gpr .r12 = s.gpr .rdx ∧
      s'.gpr .r13 = s.gpr .rcx ∧ s'.gpr .r14 = s.gpr .r8 ∧ s'.gpr .r15 = s.gpr .r9 ∧
      s'.gpr .rsp = s.gpr .rsp ∧ s'.zf = some (s.gpr .r8 == 0) ∧
      s'.mem = savedMem s ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [save, setup, saved, List.map, List.cons_append, List.nil_append, runBlock_cons,
      runStep_some, runBlock_nil, at_, exec, readSrc, State.store64, State.ea, offset_nat,
      hw 2064 (by decide) (by decide), hw 2072 (by decide) (by decide), hw 2080 (by decide) (by decide),
      hw 2088 (by decide) (by decide), hw 2096 (by decide) (by decide), hw 2104 (by decide) (by decide),
      ite_true, Option.map_some, execAlu, Option.bind_some]
    rfl, ?_⟩
  simp (config := {decide := true}) only [gpr_setReg, gpr_arithFlags, zf_arithFlags, mem_setReg,
    mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags, ite_true, ite_false,
    BitVec.and_self]
  trivial

end VG.Proof.CmacAes.X86_64

namespace VG.Proof.CmacAes.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.CmacAes.X86_64

/-- The memory after `chainIn`: the counter block at `c` is the state at `p`
XORed with the block at `q`, and the state is zeroed. -/
def chainMem (m : Mem) (c p q : Addr) : Mem :=
  let m₁ := m.writeW c (m.readW p 64 ^^^ m.readW q 64)
  let m₂ := m₁.writeW (c + BitVec.ofNat 64 8) (m₁.readW (p + BitVec.ofNat 64 8) 64 ^^^ m₁.readW (q + BitVec.ofNat 64 8) 64)
  (m₂.writeW p (0 : BitVec 64)).writeW (p + BitVec.ofNat 64 8) (0 : BitVec 64)

theorem chainIn_ok (s : State) {C P Q : Addr} (hc : s.gpr .r15 + BitVec.ofNat 64 2048 = C)
    (hp : s.gpr .r12 = P) (hq : s.gpr .r13 = Q)
    (rp : InRegions (s.rd ++ s.wr) P 8) (rp8 : InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 8) 8)
    (rq : InRegions (s.rd ++ s.wr) Q 8) (rq8 : InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 8) 8)
    (wc : InRegions s.wr C 8) (wc8 : InRegions s.wr (C + BitVec.ofNat 64 8) 8)
    (wp : InRegions s.wr P 8) (wp8 : InRegions s.wr (P + BitVec.ofNat 64 8) 8) :
    ∃ s', runBlock isa (chainIn ++ updArgs) s = some s' ∧
      s'.gpr .rdi = s.gpr .rbx ∧ s'.gpr .rsi = s.gpr .rbp ∧ s'.gpr .rdx = C ∧ s'.gpr .rcx = P ∧
      s'.gpr .r8 = 1 ∧ s'.gpr .r9 = s.gpr .r15 ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      s'.mem = chainMem s.mem C P Q ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hc' : s.gpr .r15 + BitVec.ofNat 64 2056 = C + BitVec.ofNat 64 8 := by
    rw [← hc, BitVec.add_assoc]; rfl
  refine ⟨_, by
    simp (config := {decide := true}) only [chainIn, updArgs, ctrArgs, cOff, List.cons_append,
      List.nil_append, runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc, readSrc32,
      State.load64, State.store64, State.ea, offset_nat, execAlu, Option.bind_some, Option.map_some,
      gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg,
      wr_arithFlags, State.setReg32, ite_true, ite_false, hc, hc', hp, hq, BitVec.add_zero,
      rp, rp8, rq, rq8, wc, wc8, wp, wp8]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl⟩
  · simp [gpr_setReg]
  · simp [gpr_setReg]
  · simp [gpr_setReg, ← hc]
  · simp [gpr_setReg]
  · simp [gpr_setReg]
  · simp [gpr_setReg]
  · intro r hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]
  · rfl

theorem frame_store2 {m : Mem} (p : Addr) (w₀ w₁ : BitVec 64) :
    Frame [⟨p, 16⟩] m ((m.writeW p w₀).writeW (p + BitVec.ofNat 64 8) w₁) :=
  ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
    (by simpa using Offset.contains_base p (d := 0) (n := 8) (k := 16) (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (Offset.contains_base p (d := 8) (n := 8) (k := 16) (by decide) (by decide))

theorem chainMem_frame (m : Mem) (C P Q : Addr) : Frame [⟨C, 16⟩, ⟨P, 16⟩] m (chainMem m C P Q) := by
  have f₁ : Frame [⟨C, 16⟩, ⟨P, 16⟩] m _ :=
    (frame_store2 (m := m) C (m.readW P 64 ^^^ m.readW Q 64)
      ((m.writeW C (m.readW P 64 ^^^ m.readW Q 64)).readW (P + BitVec.ofNat 64 8) 64 ^^^
        (m.writeW C (m.readW P 64 ^^^ m.readW Q 64)).readW (Q + BitVec.ofNat 64 8) 64)).mono
      (fun r hr => by simp only [List.mem_singleton] at hr; simp [hr])
  exact f₁.trans ((frame_store2 P 0 0).mono (fun r hr => by simp only [List.mem_singleton] at hr; simp [hr]))

theorem chainMem_state (m : Mem) (C P Q : Addr) :
    Spec.Aes.bytesAt (chainMem m C P Q) P 16 = Spec.Cmac.zeros 16 := by
  rw [chainMem, Proof.Cmac.bytesAt_store2, Proof.Cmac.le8_zero]; rfl

theorem bytesAt_frame' {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (⟨p, 16⟩ : Region).Disjoint r) : Spec.Aes.bytesAt m' p 16 = Spec.Aes.bytesAt m p 16 :=
  bytesAt_frame hf hd (by decide)

theorem readW_frame16 {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {d : Nat} (hd8 : d + 8 ≤ 16)
    (hd : ∀ r ∈ rs, (⟨p, 16⟩ : Region).Disjoint r) :
    m'.readW (p + BitVec.ofNat 64 d) 64 = m.readW (p + BitVec.ofNat 64 d) 64 :=
  hf.readW (r := ⟨p + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _)
    (fun r hr => (hd r hr).sub_left (Offset.sub_base p hd8)) (by decide)

theorem chainMem_counter (m : Mem) {C P Q : Addr} (hcp : (⟨C, 16⟩ : Region).Disjoint ⟨P, 16⟩)
    (hcq : (⟨C, 16⟩ : Region).Disjoint ⟨Q, 16⟩) :
    Spec.Aes.bytesAt (chainMem m C P Q) C 16 =
      Spec.Cmac.xor (Spec.Aes.bytesAt m P 16) (Spec.Aes.bytesAt m Q 16) := by
  rw [chainMem, bytesAt_frame' (frame_store2 P 0 0) (by simpa using hcp), Proof.Cmac.bytesAt_store2]
  have g : Frame [⟨C, 16⟩] m (m.writeW C (m.readW P 64 ^^^ m.readW Q 64)) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (by simpa using Offset.contains_base C (d := 0) (n := 8) (k := 16) (by decide) (by decide))
  rw [readW_frame16 g (d := 8) (by decide) (by simpa using hcp.symm),
    readW_frame16 g (d := 8) (by decide) (by simpa using hcq.symm)]
  exact Proof.Cmac.xor_words m P Q

end VG.Proof.CmacAes.X86_64
