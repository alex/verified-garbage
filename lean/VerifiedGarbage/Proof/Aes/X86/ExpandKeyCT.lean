import VerifiedGarbage.Impl.Aes.X86.ExpandKey
import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.Aes.X86.Common
import VerifiedGarbage.Spec.Aes

/-!
# The AES key expansion on x86 (32-bit): the contract, and constant time

The contract the proof is written against, and the constant-time half of
the proof: the taint analysis (`VG.X86.Taint`) starts with `esp` public
and knows where the arguments are and which of them are the base addresses
of the schedule and the scratch buffer. The counters round-trip through
public slots of the scratch buffer; the stores of the schedule's words
through the moving pointer forget them, and the code stores them again from
the registers.
-/

namespace VG.Proof.Aes

open _root_.VG.X86 in
/-- The contract the proof is written against (and verified callers use); the
artifact's is the shared contract of `Spec/`, which implies it.
x86 (32-bit) contract for
`vg_aes_expand_key(key: *const u8, key_len: usize, schedule: *mut [u8; 240], scratch: *mut [u64; 64])`,
whose arguments are on the stack: writes the key schedule of the key at
`key` to `schedule`.

The code may read `key` (`key_len` bytes) and the arguments (16 bytes above
the return address), and read and write `schedule` (240 bytes) and
`scratch` (512 bytes, whose contents on exit are unspecified). The writable
buffers may not overlap each other, `key`, the arguments or the return
address; nothing may wrap around the end of the (32-bit) address space.
`key_len` is 16, 24 or 32. `esp` and the arguments are public; the key is
secret. -/
def expandKeyX86 : Contract X86.isa where
  pre s :=
    let key : Region := ⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩
    let sched : Region := ⟨(arg s 2).setWidth 64, 240⟩
    let scratch : Region := ⟨(arg s 3).setWidth 64, 512⟩
    let args : Region := ⟨argAddr s 0, 16⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [key, args] ∧ s.wr = [sched, scratch] ∧
    key.Disjoint sched ∧ key.Disjoint scratch ∧ sched.Disjoint scratch ∧
    args.Disjoint sched ∧ args.Disjoint scratch ∧ ret.Disjoint sched ∧ ret.Disjoint scratch ∧
    (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 32 ∧ (arg s 2).toNat + 240 ≤ 2 ^ 32 ∧
    (arg s 3).toNat + 512 ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 20 ≤ 2 ^ 32 ∧
    ((arg s 1).toNat = 16 ∨ (arg s 1).toNat = 24 ∨ (arg s 1).toNat = 32)
  post s s' :=
    Spec.Aes.bytesAt s'.mem ((arg s 2).setWidth 64) (16 * (Spec.Aes.rounds ((arg s 1).toNat / 4) + 1)) =
      Spec.Aes.expandKey (Spec.Aes.bytesAt s.mem ((arg s 0).setWidth 64) (arg s 1).toNat)
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 4, arg s₁ i = arg s₂ i

end VG.Proof.Aes

namespace VG.Proof.Aes.X86

open VG VG.X86

/-! ## The precondition -/

section
variable (s : State)

abbrev keyP : BitVec 32 := arg s 0
abbrev keyLen : Nat := (arg s 1).toNat
abbrev ekSchP : BitVec 32 := arg s 2
abbrev ekScrP : BitVec 32 := arg s 3
abbrev keyR : Region := reg32 (keyP s) (keyLen s)
abbrev ekSchR : Region := reg32 (ekSchP s) 240
abbrev ekScrR : Region := reg32 (ekScrP s) 512
abbrev ekArgR : Region := ⟨argAddr s 0, 16⟩
abbrev ekRetR : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩

end

/-- `expandKeyX86.pre`, by name. -/
structure EPre (s : State) : Prop where
  rd : s.rd = [keyR s, ekArgR s]
  wr : s.wr = [ekSchR s, ekScrR s]
  dKS : (keyR s).Disjoint (ekSchR s)
  dKB : (keyR s).Disjoint (ekScrR s)
  dSB : (ekSchR s).Disjoint (ekScrR s)
  aS : (ekArgR s).Disjoint (ekSchR s)
  aB : (ekArgR s).Disjoint (ekScrR s)
  rS : (ekRetR s).Disjoint (ekSchR s)
  rB : (ekRetR s).Disjoint (ekScrR s)
  fK : (keyP s).toNat + keyLen s ≤ 2 ^ 32
  fS : (ekSchP s).toNat + 240 ≤ 2 ^ 32
  fB : (ekScrP s).toNat + 512 ≤ 2 ^ 32
  fSp : (s.gpr .esp).toNat + 20 ≤ 2 ^ 32
  len : keyLen s = 16 ∨ keyLen s = 24 ∨ keyLen s = 32

theorem EPre.of {s : State} (h : Proof.Aes.expandKeyX86.pre s) : EPre s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩

/-! ## Constant time -/

/-- The taint analysis starts with `esp` public, and the words holding
`schedule` and `scratch` known to be the base addresses of the writable
regions. -/
def ekτ₀ : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [240, 512], argLen := 20,
    argBases := [(12, 0), (16, 1)] }

theorem ek_wf₀ {s : State} (hp : EPre s) : VG.X86.Taint.Wf ekτ₀ s := by
  have hS := hp.fS; have hB := hp.fB; have hs := hp.fSp
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun _ => ⟨?_, ?_, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨by simp only [ekτ₀]; omega, ?_⟩, ?_⟩
  · rw [hp.wr]
    exact .cons (Nat.le_refl _) (.cons (Nat.le_refl _) .nil)
  · simp only [hp.wr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq, List.Pairwise.nil, and_true]
    exact ⟨hp.dSB, fun _ h => h.elim⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [toNat_setWidth32] <;> omega
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by omega) hp.rS hp.aS
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by omega) hp.rB hp.aB
  · intro p hp'
    simp only [ekτ₀, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl <;> refine ⟨by decide, ?_⟩ <;>
      simp [VG.X86.Taint.region, hp.wr, addr, arg, argAddr]

theorem ek_agree₀ {s₁ s₂ : State} (h₁ : Proof.Aes.expandKeyX86.pre s₁) (h₂ : Proof.Aes.expandKeyX86.pre s₂)
    (hpub : Proof.Aes.expandKeyX86.pub s₁ s₂) : VG.X86.Taint.Agree ekτ₀ s₁ s₂ := by
  obtain ⟨hesp, ha⟩ := hpub
  have hp₁ := EPre.of h₁; have hp₂ := EPre.of h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, ek_wf₀ hp₁, ek_wf₀ hp₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => hesp,
    fun k h4 hk => ?_⟩
  · simp only [ekτ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact hesp
  · rw [hp₁.wr, hp₂.wr]
    simp only [ekSchR, ekScrR, ekSchP, ekScrP, ha 2 (by omega), ha 3 (by omega)]
  · simp only [ekτ₀] at hk
    rw [show VG.X86.Taint.depth ekτ₀.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq (n := 20) hp₁.fSp h4 hk, VG.X86.Taint.argByte_eq (n := 20) hp₂.fSp h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega))]
    exact congrArg _ (ha _ (by omega))

theorem expandKey_ct :
    ConstantTime isa Proof.Aes.expandKeyX86.pre Proof.Aes.expandKeyX86.pub Impl.Aes.X86.expandKey :=
  VG.Taint.constantTime (A := VG.X86.taint) ekτ₀ (fun _ _ h₁ h₂ hp => ek_agree₀ h₁ h₂ hp)
    (by taint_decide)

end VG.Proof.Aes.X86
