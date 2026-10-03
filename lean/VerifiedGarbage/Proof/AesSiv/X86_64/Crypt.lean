import VerifiedGarbage.Proof.AesSiv.X86_64.S2vAd
import VerifiedGarbage.Proof.AesSiv.X86_64.Finish
import VerifiedGarbage.Proof.AesSiv.X86_64.CtrCT
import VerifiedGarbage.Proof.Cmac.Dbl32

/-!
# AES-SIV on x86-64: what `seal` and `open` share

Both save the registers and keep the arguments in them, the data pointer and
its length also at `W + 208` and `W + 216` (`cryptPre_ok`), and set the
counter `Q` at `W + 64` from an IV at `W` (`counter_ok`): the IV's second
word with bit 7 of its bytes 0 and 4 cleared (`counter_words`).
-/

namespace VG.Proof.AesSiv.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesSiv.X86_64
open VG.Impl.CmacAes.X86_64 (at_)
open VG.Proof.CmacAes.X86_64 (offset_nat bytesAt_frame k0)
open VG.Proof.CmacAes.Stream.X86_64 (toNat_ofNat)
open VG.Proof.Aes.X86_64 (Ctr32Impl)

variable {s₀ : State} {C D P W : Addr} {R L : Nat}

theorem Env.ofCrypt {s₀ : State} (h : cryptPre s₀) :
    Env s₀ (s₀.gpr .rdi) (s₀.gpr .rdx) (s₀.gpr .rcx) (s₀.gpr .r9) (s₀.gpr .rsi).toNat (s₀.gpr .r8).toNat := by
  obtain ⟨sp, rd, wr, _, c_w, d_p, d_w, p_w, ret_c, ret_d, ret_p, ret_w, stk_c, stk_d, stk_p, stk_w, wC, wD, wP,
    wW, rounds⟩ := h
  exact ⟨sp, rounds, by rw [rd, wr]; simp, by rw [rd, wr]; simp, by rw [rd, wr]; simp, by rw [wr]; simp, c_w,
    d_p, d_w, p_w, ret_c, ret_d, ret_p, ret_w, stk_c, stk_d, stk_p, stk_w, wC, wD, wP, wW, (s₀.gpr .r8).isLt⟩

theorem cryptPre_cp {s₀ : State} (h : cryptPre s₀) :
    (⟨s₀.gpr .rdi, 512⟩ : Region).Disjoint ⟨s₀.gpr .rcx, (s₀.gpr .r8).toNat⟩ := h.2.2.2.1

theorem cryptPre_pw {s₀ : State} (h : cryptPre s₀) :
    (⟨s₀.gpr .rcx, (s₀.gpr .r8).toNat⟩ : Region) ∈ s₀.wr := by rw [h.2.2.1]; simp

theorem cryptPre_ww {s₀ : State} (h : cryptPre s₀) : (⟨s₀.gpr .r9, 2560⟩ : Region) ∈ s₀.wr := by
  rw [h.2.2.1]; simp

theorem ArgRegs.ofCrypt {s₀ : State} (h : cryptPre s₀) :
    ArgRegs s₀ (s₀.gpr .rdi) (s₀.gpr .rdx) (s₀.gpr .rcx) (s₀.gpr .r9) (s₀.gpr .rsi).toNat (s₀.gpr .r8).toNat where
  rdi := rfl
  rsi := BitVec.eq_of_toNat_eq (by
    rw [toNat_ofNat (by have := (Env.ofCrypt h).rounds; rcases this with h | h | h <;> omega)])
  rdx := rfl
  rcx := rfl
  r8 := BitVec.eq_of_toNat_eq (by rw [toNat_ofNat (s₀.gpr .r8).isLt])
  r9 := rfl

/-- The memory after saving the registers and the data pointer and length. -/
def cryptMem (s₀ : State) (P W : Addr) (L : Nat) : Mem :=
  ((Spill.saveMem s₀.mem W s₀.gpr saved).writeW (W + BitVec.ofNat 64 dataOff) P).writeW
    (W + BitVec.ofNat 64 lenOff) (BitVec.ofNat 64 L)

theorem cryptPre_ok (h : Env s₀ C D P W R L) (ha : ArgRegs s₀ C D P W R L) :
    ∃ s₁, runBlock isa Impl.AesSiv.X86_64.cryptPre s₀ = some s₁ ∧ Regs s₀ C D P W R L s₁ ∧
      s₁.mem = cryptMem s₀ P W L := by
  obtain ⟨s₁, run₁, hr₁, m₁⟩ := adPre_ok h ha
  have w₁ := h.inW hr₁.wr (d := dataOff) (n := 8) (by decide)
  have w₂ := h.inW hr₁.wr (d := lenOff) (n := 8) (by decide)
  refine ⟨_, by
    rw [Impl.AesSiv.X86_64.cryptPre, runBlock_append, run₁, Option.bind_some]
    simp only [runBlock_cons, runStep_some, runBlock_nil, at_, exec, State.store64, State.ea, offset_nat,
      hr₁.r15, w₁, ite_true, w₂]
    rfl, ?_, ?_⟩
  · exact ⟨hr₁.rbx, hr₁.rbp, hr₁.r12, hr₁.r13, hr₁.r14, hr₁.r15, hr₁.rsp, hr₁.rd, hr₁.wr⟩
  · show ((s₁.mem.writeW _ (s₁.gpr .r13)).writeW _ (s₁.gpr .r14)) = _
    rw [hr₁.r13, hr₁.r14, m₁]; rfl

theorem counter_ok (h : Env s₀ C D P W R L) {s : State} (h15 : s.gpr .r15 = W) (hrd : s.rd = s₀.rd)
    (hwr : s.wr = s₀.wr) :
    ∃ s', runBlock isa (counter 0) s = some s' ∧
      s'.mem = (s.mem.writeW (W + BitVec.ofNat 64 cntOff) (s.mem.readW (W + BitVec.ofNat 64 0) 64)).writeW
        (W + BitVec.ofNat 64 (cntOff + 8)) (s.mem.readW (W + BitVec.ofNat 64 (0 + 8)) 64 &&& qmask) ∧
      (∀ r, r ≠ .rax → r ≠ .rdx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have r₀ := h.inRW hrd hwr (d := 0) (n := 8) (by decide)
  have r₈ := h.inRW hrd hwr (d := 0 + 8) (n := 8) (by decide)
  have w₀ := h.inW hwr (d := cntOff) (n := 8) (by decide)
  have w₈ := h.inW hwr (d := cntOff + 8) (n := 8) (by decide)
  refine ⟨_, by
    simp (config := {decide := true}) only [counter, runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc,
      execAlu, State.load64, State.store64, State.ea, offset_nat, Option.bind_some, Option.map_some, gpr_setReg,
      gpr_arithFlags, mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags, ite_true,
      ite_false, h15, r₀, r₈, w₀, w₈]
    rfl, ?_, ?_, ?_, ?_⟩
  · rw [Mem.readW_writeW_sep (Offset.sep W (d := 0 + 8) (n := 8) (e := cntOff) (k := 8) (by decide) (by decide)
      (by decide)) (by decide), k0]
    rfl
  · intro r h₁ h₂; simp [gpr_setReg, h₁, h₂]
  all_goals rfl

/-- The counter `Q` of the IV `v`, as `ctr` takes it. -/
theorem counter_cnt (m : Mem) (W : Addr) :
    ∃ hi lo : BitVec 64,
      ((m.writeW (W + BitVec.ofNat 64 cntOff) (m.readW (W + BitVec.ofNat 64 0) 64)).writeW
          (W + BitVec.ofNat 64 (cntOff + 8)) (m.readW (W + BitVec.ofNat 64 (0 + 8)) 64 &&& qmask)).readW
          (W + BitVec.ofNat 64 cntOff) 64 = bswap64 hi ∧
      ((m.writeW (W + BitVec.ofNat 64 cntOff) (m.readW (W + BitVec.ofNat 64 0) 64)).writeW
          (W + BitVec.ofNat 64 (cntOff + 8)) (m.readW (W + BitVec.ofNat 64 (0 + 8)) 64 &&& qmask)).readW
          (W + BitVec.ofNat 64 (cntOff + 8)) 64 = bswap64 lo ∧
      (hi ++ lo : BitVec 128) = Spec.Gcm.ofBytes (Spec.Siv.counter (Spec.Aes.bytesAt m W 16)) := by
  refine ⟨bswap64 (m.readW (W + BitVec.ofNat 64 0) 64), bswap64 (m.readW (W + BitVec.ofNat 64 (0 + 8)) 64 &&& qmask),
    ?_, ?_, ?_⟩
  · rw [Mem.readW_writeW_sep (Offset.sep W (d := cntOff) (n := 8) (e := cntOff + 8) (k := 8) (by decide) (by decide)
      (by decide)) (by decide), Mem.readW_writeW_self64, Proof.Gcm.X86_64.bswap64_bswap64]
  · rw [Mem.readW_writeW_self64, Proof.Gcm.X86_64.bswap64_bswap64]
  · rw [← Proof.Cmac.ofBytes_toBytes (bswap64 _ ++ bswap64 _), ← VG.Proof.CmacAes.X86_64.le8_bswap,
      Proof.Gcm.X86_64.bswap64_bswap64, Proof.Gcm.X86_64.bswap64_bswap64, counter_words, Proof.Cmac.le8_readW,
      Proof.Cmac.le8_readW, k0, ← Proof.Cmac.bytesAt_split]

end VG.Proof.AesSiv.X86_64
