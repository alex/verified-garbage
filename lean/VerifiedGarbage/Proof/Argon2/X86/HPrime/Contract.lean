import VerifiedGarbage.Proof.Argon2.HPrime
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Sha256.X86.Stream.Common
import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Impl.Argon2.X86.HPrime

/-!
# Argon2 H′ on x86 (32-bit): the contract of the proof

`hPrimeX86`: `vg_argon2_hprime(input, input_len, out, out_len, scratch)` with
its arguments only read; `Spec.Argon2.hPrimeContract`, which lets the code
write them, is reached by narrowing. H′ uses the 60 bytes of stack below its
return address: a call of `vg_blake2b_update` pushes six words and its return
address, and `update` itself uses 32 bytes.
-/

namespace VG.Proof.Argon2.X86.HPrime

open VG VG.X86
open VG.Spec.Blake2 (bytesAt)

def hPrimeX86 : Contract X86.isa where
  pre s :=
    let input : Region := ⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩
    let out : Region := ⟨(arg s 2).setWidth 64, (arg s 3).toNat⟩
    let scratch : Region := ⟨(arg s 4).setWidth 64, 16384⟩
    let args : Region := ⟨argAddr s 0, 20⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := below (s.gpr .esp) 60
    s.rd = [input, args] ∧ s.wr = [out, scratch] ∧
    input.Disjoint scratch ∧ out.Disjoint scratch ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
    ret.Disjoint out ∧ ret.Disjoint scratch ∧
    stack.Disjoint input ∧ stack.Disjoint out ∧ stack.Disjoint scratch ∧
    (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 32 ∧ (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 32 ∧
    (arg s 4).toNat + 16384 ≤ 2 ^ 32 ∧ 60 ≤ (s.gpr .esp).toNat ∧
    (s.gpr .esp).toNat + 24 ≤ 2 ^ 32 ∧ 1 ≤ (arg s 3).toNat
  post s s' := bytesAt s'.mem ((arg s 2).setWidth 64) (arg s 3).toNat =
    Spec.Argon2.hPrime (arg s 3).toNat (bytesAt s.mem ((arg s 0).setWidth 64) (arg s 1).toNat)
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 5, arg s₁ i = arg s₂ i

section
variable (s₀ : State)

abbrev inp : BitVec 32 := arg s₀ 0
abbrev inl : Nat := (arg s₀ 1).toNat
abbrev op : BitVec 32 := arg s₀ 2
abbrev ol : Nat := (arg s₀ 3).toNat
abbrev scr : BitVec 32 := arg s₀ 4
abbrev esp₀ : BitVec 32 := s₀.gpr .esp
/-- `scratch`, as an address. -/
abbrev P : Addr := (scr s₀).setWidth 64
abbrev inR : Region := ⟨(inp s₀).setWidth 64, inl s₀⟩
abbrev outR : Region := ⟨(op s₀).setWidth 64, ol s₀⟩
abbrev scrR : Region := ⟨P s₀, 16384⟩
abbrev argR : Region := ⟨argAddr s₀ 0, 20⟩
abbrev retR : Region := ⟨(esp₀ s₀).setWidth 64, 4⟩
abbrev stkR : Region := below (esp₀ s₀) 60

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [inR s₀, argR s₀]
  wr : s₀.wr = [outR s₀, scrR s₀]
  in_scr : (inR s₀).Disjoint (scrR s₀)
  out_scr : (outR s₀).Disjoint (scrR s₀)
  arg_out : (argR s₀).Disjoint (outR s₀)
  arg_scr : (argR s₀).Disjoint (scrR s₀)
  ret_out : (retR s₀).Disjoint (outR s₀)
  ret_scr : (retR s₀).Disjoint (scrR s₀)
  stk_in : (stkR s₀).Disjoint (inR s₀)
  stk_out : (stkR s₀).Disjoint (outR s₀)
  stk_scr : (stkR s₀).Disjoint (scrR s₀)
  in_fits : (inp s₀).toNat + inl s₀ ≤ 2 ^ 32
  out_fits : (op s₀).toNat + ol s₀ ≤ 2 ^ 32
  scr_fits : (scr s₀).toNat + 16384 ≤ 2 ^ 32
  esp_lo : 60 ≤ (esp₀ s₀).toNat
  esp_hi : (esp₀ s₀).toNat + 24 ≤ 2 ^ 32
  ol_pos : 1 ≤ ol s₀

theorem pre_of (s₀ : State) (h : hPrimeX86.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩

/-- `[scratch + d]`, as the code addresses it. -/
theorem scr_addr {s₀ : State} (hp : Pre s₀) {d : Nat} (hd : d < 16384) :
    addr (scr s₀) d = P s₀ + BitVec.ofNat 64 d := addr_eq (by have := hp.scr_fits; omega)

end VG.Proof.Argon2.X86.HPrime
