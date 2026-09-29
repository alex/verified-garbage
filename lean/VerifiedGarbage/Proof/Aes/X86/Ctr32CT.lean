import VerifiedGarbage.Impl.Aes.X86.Ctr32
import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.Aes.X86.Common
import VerifiedGarbage.Spec.Gcm

/-!
# AES counter mode on x86 (32-bit): the contract, and constant time

Untrusted: everything here is checked by Lean.

The contract the proof is written against, and the constant-time half of
the proof: the taint analysis (`VG.X86.Taint`) starts with `esp` public
and knows where the arguments are and which of them are the base addresses
of the counter block, the data and the scratch buffer. The data pointer
and the count round-trip through public slots of the scratch buffer; the
stores of the keystream through the data pointer forget them, and the code
stores them again from the registers.
-/

namespace VG.Proof.Aes

open Spec.Gcm

open _root_.VG.X86 in
/-- The contract the proof is written against (and verified callers use); the
artifact's is the shared contract of `Spec/`, which implies it.
x86 (32-bit) contract for
`vg_aes_ctr32(schedule: *const [u8; 240], rounds: usize, counter: *mut [u8; 16], data: *mut [u8; 16], n: usize, scratch: *mut [u64; 256])`,
whose arguments are on the stack: XORs the AES counter-mode keystream from
the counter block at `counter` into the `n` blocks at `data`, and advances
the counter block by `n`.

The code may read `schedule` (240 bytes) and the arguments (24 bytes above
the return address), and read and write `counter` (16 bytes), `data`
(`16 n` bytes) and `scratch` (2048 bytes, whose contents on exit are
unspecified). The writable buffers may not overlap each other, `schedule`,
the arguments or the return address; nothing may wrap around the end of the
(32-bit) address space. `rounds` is 10, 12 or 14. `esp` and the arguments
are public; the key schedule, the counter block and the data are secret. -/
def ctr32X86 : Contract X86.isa where
  pre s :=
    let sched : Region := ⟨(arg s 0).setWidth 64, 240⟩
    let counter : Region := ⟨(arg s 2).setWidth 64, 16⟩
    let data : Region := ⟨(arg s 3).setWidth 64, 16 * (arg s 4).toNat⟩
    let scratch : Region := ⟨(arg s 5).setWidth 64, 2048⟩
    let args : Region := ⟨argAddr s 0, 24⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [sched, args] ∧ s.wr = [counter, data, scratch] ∧
    sched.Disjoint counter ∧ sched.Disjoint data ∧ sched.Disjoint scratch ∧
    counter.Disjoint data ∧ counter.Disjoint scratch ∧ data.Disjoint scratch ∧
    args.Disjoint counter ∧ args.Disjoint data ∧ args.Disjoint scratch ∧
    ret.Disjoint counter ∧ ret.Disjoint data ∧ ret.Disjoint scratch ∧
    (arg s 0).toNat + 240 ≤ 2 ^ 32 ∧ (arg s 2).toNat + 16 ≤ 2 ^ 32 ∧
    (arg s 3).toNat + 16 * (arg s 4).toNat ≤ 2 ^ 32 ∧ (arg s 5).toNat + 2048 ≤ 2 ^ 32 ∧
    (s.gpr .esp).toNat + 28 ≤ 2 ^ 32 ∧
    ((arg s 1).toNat = 10 ∨ (arg s 1).toNat = 12 ∨ (arg s 1).toNat = 14)
  post s s' :=
    let ciph := aesWith (arg s 1).toNat
      (Spec.Aes.bytesAt s.mem ((arg s 0).setWidth 64) (16 * ((arg s 1).toNat + 1)))
    blocksAt s'.mem ((arg s 3).setWidth 64) (arg s 4).toNat =
        ctr32 ciph (blockAt s.mem ((arg s 2).setWidth 64))
          (blocksAt s.mem ((arg s 3).setWidth 64) (arg s 4).toNat) ∧
      blockAt s'.mem ((arg s 2).setWidth 64) =
        Nat.repeat inc32 (arg s 4).toNat (blockAt s.mem ((arg s 2).setWidth 64))
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 6, arg s₁ i = arg s₂ i

end VG.Proof.Aes

namespace VG.Proof.Aes.X86

open VG VG.X86

/-! ## The precondition -/

section
variable (s : State)

abbrev schP : BitVec 32 := arg s 0
abbrev nRounds : Nat := (arg s 1).toNat
abbrev ctrP : BitVec 32 := arg s 2
abbrev datP : BitVec 32 := arg s 3
abbrev nBlk : Nat := (arg s 4).toNat
abbrev scrP : BitVec 32 := arg s 5
abbrev schR : Region := reg32 (schP s) 240
abbrev ctrR : Region := reg32 (ctrP s) 16
abbrev datR : Region := reg32 (datP s) (16 * nBlk s)
abbrev scrR : Region := reg32 (scrP s) 2048
abbrev argR : Region := ⟨argAddr s 0, 24⟩
abbrev retR : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩

end

/-- `ctr32X86.pre`, by name. -/
structure CPre (s : State) : Prop where
  rd : s.rd = [schR s, argR s]
  wr : s.wr = [ctrR s, datR s, scrR s]
  dSC : (schR s).Disjoint (ctrR s)
  dSD : (schR s).Disjoint (datR s)
  dSB : (schR s).Disjoint (scrR s)
  dCD : (ctrR s).Disjoint (datR s)
  dCB : (ctrR s).Disjoint (scrR s)
  dDB : (datR s).Disjoint (scrR s)
  aC : (argR s).Disjoint (ctrR s)
  aD : (argR s).Disjoint (datR s)
  aB : (argR s).Disjoint (scrR s)
  rC : (retR s).Disjoint (ctrR s)
  rD : (retR s).Disjoint (datR s)
  rB : (retR s).Disjoint (scrR s)
  fS : (schP s).toNat + 240 ≤ 2 ^ 32
  fC : (ctrP s).toNat + 16 ≤ 2 ^ 32
  fD : (datP s).toNat + 16 * nBlk s ≤ 2 ^ 32
  fB : (scrP s).toNat + 2048 ≤ 2 ^ 32
  fSp : (s.gpr .esp).toNat + 28 ≤ 2 ^ 32
  rounds : nRounds s = 10 ∨ nRounds s = 12 ∨ nRounds s = 14

theorem CPre.of {s : State} (h : Proof.Aes.ctr32X86.pre s) : CPre s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩

/-! ## Constant time -/

/-- The taint analysis starts with `esp` public, and the words holding
`counter`, `data` and `scratch` known to be the base addresses of the
writable regions. -/
def ctrτ₀ : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [16, 0, 2048], argLen := 28,
    argBases := [(12, 0), (16, 1), (24, 2)] }

theorem ctr_wf₀ {s : State} (hp : CPre s) : VG.X86.Taint.Wf ctrτ₀ s := by
  have hC := hp.fC; have hD := hp.fD; have hB := hp.fB; have hs := hp.fSp
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun _ => ⟨?_, ?_, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨by simp only [ctrτ₀]; omega, ?_⟩, ?_⟩
  · rw [hp.wr]
    exact .cons (Nat.le_refl _) (.cons (Nat.zero_le _) (.cons (Nat.le_refl _) .nil))
  · simp only [hp.wr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, List.Pairwise.nil, and_true]
    exact ⟨⟨hp.dCD, hp.dCB⟩, hp.dDB, fun _ h => h.elim⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl) <;> simp only [toNat_setWidth32] <;> omega
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 24) (by omega) hp.rC hp.aC
    · exact VG.X86.Taint.frame_disjoint (n := 24) (by omega) hp.rD hp.aD
    · exact VG.X86.Taint.frame_disjoint (n := 24) (by omega) hp.rB hp.aB
  · intro p hp'
    simp only [ctrτ₀, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl | rfl <;> refine ⟨by decide, ?_⟩ <;>
      simp [VG.X86.Taint.region, hp.wr, addr, arg, argAddr]

theorem ctr_agree₀ {s₁ s₂ : State} (h₁ : Proof.Aes.ctr32X86.pre s₁) (h₂ : Proof.Aes.ctr32X86.pre s₂)
    (hpub : Proof.Aes.ctr32X86.pub s₁ s₂) : VG.X86.Taint.Agree ctrτ₀ s₁ s₂ := by
  obtain ⟨hesp, ha⟩ := hpub
  have hp₁ := CPre.of h₁; have hp₂ := CPre.of h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, ctr_wf₀ hp₁, ctr_wf₀ hp₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => hesp,
    fun k h4 hk => ?_⟩
  · simp only [ctrτ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact hesp
  · rw [hp₁.wr, hp₂.wr]
    simp only [ctrR, datR, scrR, ctrP, datP, nBlk, scrP, ha 2 (by omega), ha 3 (by omega),
      ha 4 (by omega), ha 5 (by omega)]
  · simp only [ctrτ₀] at hk
    rw [show VG.X86.Taint.depth ctrτ₀.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq (n := 28) hp₁.fSp h4 hk, VG.X86.Taint.argByte_eq (n := 28) hp₂.fSp h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega))]
    exact congrArg _ (ha _ (by omega))

theorem ctr32_ct : ConstantTime isa Proof.Aes.ctr32X86.pre Proof.Aes.ctr32X86.pub Impl.Aes.X86.ctr32 :=
  VG.Taint.constantTime (A := VG.X86.taint) ctrτ₀ (fun _ _ h₁ h₂ hp => ctr_agree₀ h₁ h₂ hp)
    (by taint_decide)

end VG.Proof.Aes.X86
