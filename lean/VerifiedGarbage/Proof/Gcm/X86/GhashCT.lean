import VerifiedGarbage.Impl.Gcm.X86
import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.Aes.X86.Common
import VerifiedGarbage.Spec.Gcm

/-!
# GHASH on x86 (32-bit): the contract, and constant time

Untrusted: everything here is checked by Lean.

The contract the proof is written against, and the constant-time half of
the proof: the taint analysis (`VG.X86.Taint`) starts with `esp` public
and knows where the arguments are and which of them are the base addresses
of `y` and the scratch buffer. The data pointer and the counters live in
public slots of the scratch buffer, and every other store goes through
`edi` (the scratch buffer) or the `y` pointer, which keeps them.
-/

namespace VG.Proof.Gcm

open Spec.Gcm

open _root_.VG.X86 in
/-- The contract the proof is written against (and verified callers use); the
artifact's is the shared contract of `Spec/`, which implies it.
x86 (32-bit) contract for
`vg_ghash(h: *const [u8; 16], y: *mut [u8; 16], data: *const [u8; 16], n: usize, scratch: *mut [u64; 32])`,
whose arguments are on the stack: replaces the block `Y` at `y` with
`GHASH_H` continued from `Y` over the `n` blocks at `data`, where `H` is the
block at `h`.

The code may read `h` (16 bytes), `data` (`16 n` bytes) and the arguments
(20 bytes above the return address), and read and write `y` (16 bytes) and
`scratch` (256 bytes, whose contents on exit are unspecified). The writable
buffers may not overlap each other, the other buffers, the arguments or the
return address; nothing may wrap around the end of the (32-bit) address
space. `esp` and the arguments are public; `H`, `Y` and the data are
secret. -/
def ghashX86 : Contract X86.isa where
  pre s :=
    let h : Region := ⟨(arg s 0).setWidth 64, 16⟩
    let y : Region := ⟨(arg s 1).setWidth 64, 16⟩
    let data : Region := ⟨(arg s 2).setWidth 64, 16 * (arg s 3).toNat⟩
    let scratch : Region := ⟨(arg s 4).setWidth 64, 256⟩
    let args : Region := ⟨argAddr s 0, 20⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [h, data, args] ∧ s.wr = [y, scratch] ∧
    h.Disjoint y ∧ h.Disjoint scratch ∧ y.Disjoint data ∧ y.Disjoint scratch ∧ data.Disjoint scratch ∧
    args.Disjoint y ∧ args.Disjoint scratch ∧ ret.Disjoint y ∧ ret.Disjoint scratch ∧
    (arg s 0).toNat + 16 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 16 ≤ 2 ^ 32 ∧
    (arg s 2).toNat + 16 * (arg s 3).toNat ≤ 2 ^ 32 ∧ (arg s 4).toNat + 256 ≤ 2 ^ 32 ∧
    (s.gpr .esp).toNat + 24 ≤ 2 ^ 32
  post s s' :=
    blockAt s'.mem ((arg s 1).setWidth 64) =
      ghashFrom (blockAt s.mem ((arg s 0).setWidth 64)) (blockAt s.mem ((arg s 1).setWidth 64))
        (blocksAt s.mem ((arg s 2).setWidth 64) (arg s 3).toNat)
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 5, arg s₁ i = arg s₂ i

end VG.Proof.Gcm

namespace VG.Proof.Gcm.X86

open VG VG.X86 VG.Proof.Aes.X86

/-! ## The precondition -/

section
variable (s : State)

abbrev hP : BitVec 32 := arg s 0
abbrev yP : BitVec 32 := arg s 1
abbrev dP : BitVec 32 := arg s 2
abbrev nBlk : Nat := (arg s 3).toNat
abbrev sP : BitVec 32 := arg s 4
abbrev hR : Region := reg32 (hP s) 16
abbrev yR : Region := reg32 (yP s) 16
abbrev dR : Region := reg32 (dP s) (16 * nBlk s)
abbrev sR : Region := reg32 (sP s) 256
abbrev aR : Region := ⟨argAddr s 0, 20⟩
abbrev rR : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩

end

/-- `ghashX86.pre`, by name. -/
structure GPre (s : State) : Prop where
  rd : s.rd = [hR s, dR s, aR s]
  wr : s.wr = [yR s, sR s]
  dHY : (hR s).Disjoint (yR s)
  dHS : (hR s).Disjoint (sR s)
  dYD : (yR s).Disjoint (dR s)
  dYS : (yR s).Disjoint (sR s)
  dDS : (dR s).Disjoint (sR s)
  aY : (aR s).Disjoint (yR s)
  aS : (aR s).Disjoint (sR s)
  rY : (rR s).Disjoint (yR s)
  rS : (rR s).Disjoint (sR s)
  fH : (hP s).toNat + 16 ≤ 2 ^ 32
  fY : (yP s).toNat + 16 ≤ 2 ^ 32
  fD : (dP s).toNat + 16 * nBlk s ≤ 2 ^ 32
  fS : (sP s).toNat + 256 ≤ 2 ^ 32
  fSp : (s.gpr .esp).toNat + 24 ≤ 2 ^ 32

theorem GPre.of {s : State} (h : Proof.Gcm.ghashX86.pre s) : GPre s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩

/-! ## Constant time -/

/-- The taint analysis starts with `esp` public, and the words holding `y`
and `scratch` known to be the base addresses of the writable regions. -/
def ghτ₀ : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [16, 256], argLen := 24,
    argBases := [(8, 0), (20, 1)] }

theorem gh_wf₀ {s : State} (hp : GPre s) : VG.X86.Taint.Wf ghτ₀ s := by
  have hY := hp.fY; have hS := hp.fS; have hs := hp.fSp
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun _ => ⟨?_, ?_, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨by simp only [ghτ₀]; omega, ?_⟩, ?_⟩
  · rw [hp.wr]
    exact .cons (Nat.le_refl _) (.cons (Nat.le_refl _) .nil)
  · simp only [hp.wr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq, List.Pairwise.nil, and_true]
    exact ⟨hp.dYS, fun _ h => h.elim⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [toNat_setWidth32] <;> omega
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 20) (by omega) hp.rY hp.aY
    · exact VG.X86.Taint.frame_disjoint (n := 20) (by omega) hp.rS hp.aS
  · intro p hp'
    simp only [ghτ₀, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl <;> refine ⟨by decide, ?_⟩ <;>
      simp [VG.X86.Taint.region, hp.wr, addr, arg, argAddr]

theorem gh_agree₀ {s₁ s₂ : State} (h₁ : Proof.Gcm.ghashX86.pre s₁) (h₂ : Proof.Gcm.ghashX86.pre s₂)
    (hpub : Proof.Gcm.ghashX86.pub s₁ s₂) : VG.X86.Taint.Agree ghτ₀ s₁ s₂ := by
  obtain ⟨hesp, ha⟩ := hpub
  have hp₁ := GPre.of h₁; have hp₂ := GPre.of h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, gh_wf₀ hp₁, gh_wf₀ hp₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => hesp,
    fun k h4 hk => ?_⟩
  · simp only [ghτ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact hesp
  · rw [hp₁.wr, hp₂.wr]
    simp only [yR, sR, yP, sP, ha 1 (by omega), ha 4 (by omega)]
  · simp only [ghτ₀] at hk
    rw [show VG.X86.Taint.depth ghτ₀.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq (n := 24) hp₁.fSp h4 hk, VG.X86.Taint.argByte_eq (n := 24) hp₂.fSp h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega))]
    exact congrArg _ (ha _ (by omega))

theorem ghash_ct : ConstantTime isa Proof.Gcm.ghashX86.pre Proof.Gcm.ghashX86.pub Impl.Gcm.X86.ghash :=
  VG.Taint.constantTime (A := VG.X86.taint) ghτ₀ (fun _ _ h₁ h₂ hp => gh_agree₀ h₁ h₂ hp)
    (by taint_decide)

end VG.Proof.Gcm.X86
