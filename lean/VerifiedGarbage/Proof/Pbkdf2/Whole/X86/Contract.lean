import VerifiedGarbage.Proof.Hmac.Generic.Implies
import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Calls

/-!
# PBKDF2-HMAC on x86 (32-bit), the whole derivation: the contract

`pbkG` is the contract the proof of `pbkdf2` is written against:
`VG.Spec.Pbkdf2.pbkdf2Contract` with 76 bytes of stack, with its facts spelt
out, which it implies for any streaming hash function and scratch space
(`pbkImp`). Every argument is on the stack (cdecl): `password`,
`password_len`, `salt`, `salt_len`, `c`, `out`, `out_len`, `scratch`.
-/

namespace VG.Proof.Pbkdf2.Whole.X86

open VG.X86
open Spec.Hmac (StreamingHash)
open Spec.Sha256 (bytesAt)

variable (S : StreamingHash) (W : Nat)

/-- `pbkdf2(password, password_len, salt, salt_len, c, out, out_len, scratch)`,
with `8 W` bytes of scratch space and 76 bytes of stack below the return
address. -/
def pbkG : Contract isa where
  pre s :=
    let pw : Region := ⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩
    let salt : Region := ⟨(arg s 2).setWidth 64, (arg s 3).toNat⟩
    let out : Region := ⟨(arg s 5).setWidth 64, (arg s 6).toNat⟩
    let scratch : Region := ⟨(arg s 7).setWidth 64, W * 8⟩
    let args : Region := ⟨argAddr s 0, 32⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 76, 76⟩
    76 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 36 ≤ 2 ^ 32 ∧
    s.rd = [pw, salt] ∧ s.wr = [out, scratch, args] ∧
    pw.Disjoint out ∧ pw.Disjoint scratch ∧ pw.Disjoint args ∧ salt.Disjoint out ∧ salt.Disjoint scratch ∧
    salt.Disjoint args ∧ out.Disjoint scratch ∧ out.Disjoint args ∧ scratch.Disjoint args ∧
    ret.Disjoint pw ∧ ret.Disjoint salt ∧ ret.Disjoint out ∧ ret.Disjoint scratch ∧ ret.Disjoint args ∧
    stack.Disjoint pw ∧ stack.Disjoint salt ∧ stack.Disjoint out ∧ stack.Disjoint scratch ∧
    stack.Disjoint args ∧
    (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 32 ∧ (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 32 ∧
    (arg s 5).toNat + (arg s 6).toNat ≤ 2 ^ 32 ∧ (arg s 7).toNat + W * 8 ≤ 2 ^ 32 ∧
    0 < (arg s 4).toNat ∧ (arg s 6).toNat ≤ (2 ^ 32 - 1) * S.digestBytes
  post s s' :=
    Spec.Pbkdf2.pbkdf2Hmac S (bytesAt s.mem ((arg s 0).setWidth 64) (arg s 1).toNat)
      (bytesAt s.mem ((arg s 2).setWidth 64) (arg s 3).toNat) (arg s 4).toNat (arg s 6).toNat =
      some (bytesAt s'.mem ((arg s 5).setWidth 64) (arg s 6).toNat)
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 8, arg s₁ i = arg s₂ i

/-- `pbkG` with the arguments readable rather than writable, as the taint
analysis needs them apart from the writable regions: the contract the proof
is written against, which `VG.X86.Verified.narrowTo` moves to `pbkG` (the
code only reads its arguments). -/
def pbkN : Contract isa where
  pre s :=
    let pw : Region := ⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩
    let salt : Region := ⟨(arg s 2).setWidth 64, (arg s 3).toNat⟩
    let out : Region := ⟨(arg s 5).setWidth 64, (arg s 6).toNat⟩
    let scratch : Region := ⟨(arg s 7).setWidth 64, W * 8⟩
    let args : Region := ⟨argAddr s 0, 32⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 76, 76⟩
    76 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 36 ≤ 2 ^ 32 ∧
    s.rd = [pw, salt, args] ∧ s.wr = [out, scratch] ∧
    pw.Disjoint out ∧ pw.Disjoint scratch ∧ pw.Disjoint args ∧ salt.Disjoint out ∧ salt.Disjoint scratch ∧
    salt.Disjoint args ∧ out.Disjoint scratch ∧ out.Disjoint args ∧ scratch.Disjoint args ∧
    ret.Disjoint pw ∧ ret.Disjoint salt ∧ ret.Disjoint out ∧ ret.Disjoint scratch ∧ ret.Disjoint args ∧
    stack.Disjoint pw ∧ stack.Disjoint salt ∧ stack.Disjoint out ∧ stack.Disjoint scratch ∧
    stack.Disjoint args ∧
    (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 32 ∧ (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 32 ∧
    (arg s 5).toNat + (arg s 6).toNat ≤ 2 ^ 32 ∧ (arg s 7).toNat + W * 8 ≤ 2 ^ 32 ∧
    0 < (arg s 4).toNat ∧ (arg s 6).toNat ≤ (2 ^ 32 - 1) * S.digestBytes
  post := (pbkG S W).post
  pub := (pbkG S W).pub

theorem setWidth_inj32 {a b : BitVec 32} (h : (a.setWidth 64).setWidth 32 = (b.setWidth 64).setWidth 32) :
    a = b := by rwa [setWidth32_64, setWidth32_64] at h

/-- `pbkG` implies the shared contract for any hash function and scratch
space, given that the shared contract is satisfiable. -/
theorem pbkImp (h : ∃ s, (Spec.Pbkdf2.pbkdf2Contract S W X86.abi 76).pre s) :
    (pbkG S W).Implies (Spec.Pbkdf2.pbkdf2Contract S W X86.abi 76) := by
  exact
    { pre := by
        intro s h
        sig_pre [Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig, X86.abi] at h
        simp only [argVal32, setWidth32_64, toNat_setWidth64,
          show argBytes [32, 32, 32, 32, 32, 32, 32, 32] = 32 from rfl] at h
        obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20,
          h21, h22, h23, h24, h25, h26, h27, h28⟩ := h
        exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20,
          h21, h22, h23, h24, h25, h26, h27, h28⟩
      post := by
        rintro s s' - h
        sig_post [Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig, X86.abi]
        simp only [argVal32, setWidth32_64]
        exact h
      pub := by
        rintro s₁ s₂ - - h
        sig_pub [Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig, X86.abi] at h
        simp only [argVal32] at h
        obtain ⟨e, a0, a1, a2, a3, a4, a5, a6, a7⟩ := h
        refine ⟨e, fun i hi => ?_⟩
        rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact setWidth_inj32 a0
        · exact setWidth_inj32 a1
        · exact setWidth_inj32 a2
        · exact setWidth_inj32 a3
        · exact setWidth_inj32 a4
        · exact setWidth_inj32 a5
        · exact setWidth_inj32 a6
        · exact setWidth_inj32 a7
      sat := h }

/-- The regions the proof gives `pbkdf2`: the arguments readable. -/
def narrowRd (s : State) : List Region :=
  [⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩, ⟨(arg s 2).setWidth 64, (arg s 3).toNat⟩, ⟨argAddr s 0, 32⟩]
def narrowWr (W : Nat) (s : State) : List Region :=
  [⟨(arg s 5).setWidth 64, (arg s 6).toNat⟩, ⟨(arg s 7).setWidth 64, W * 8⟩]

/-- A state for `pbkG`, given the regions `pbkN` gives. -/
theorem pbkN_pre {s : State} (h : (pbkG S W).pre s) : (pbkN S W).pre (s.withRegions (narrowRd s) (narrowWr W s)) := by
  obtain ⟨h0, h1, _, _, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20,
    h21, h22, h23, h24, h25, h26, h27, h28⟩ := h
  simp only [pbkN, narrowRd, narrowWr, arg_withRegions, argAddr_withRegions, State.withRegions_gpr,
    State.withRegions_rd, State.withRegions_wr]
  exact ⟨h0, h1, trivial, trivial, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20,
    h21, h22, h23, h24, h25, h26, h27, h28⟩

/-- Verified against `pbkN`, so against `pbkG`. -/
theorem verified_pbkG {c : Prog isa} (h : Verified X86.target c (pbkN S W)) (hsat : ∃ s, (pbkG S W).pre s) :
    Verified X86.target c (pbkG S W) := by
  refine Verified.narrowTo h narrowRd (narrowWr W) (fun s h => pbkN_pre S W h) (fun s h => ?_) (fun s h => ?_)
    (fun _ _ _ h => h) (fun _ _ _ _ h => h) hsat
  · obtain ⟨_, _, h2, h3, _⟩ := h
    rw [h2, h3]
    refine Covers.of_sub fun r hr => ⟨r, ?_, 0, by simp, by simp⟩
    simp only [narrowRd, narrowWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp
  · obtain ⟨_, _, _, h3, _⟩ := h
    rw [h3]
    refine Covers.of_sub fun r hr => ⟨r, ?_, 0, by simp, by simp⟩
    simp only [narrowWr, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl <;> simp

end VG.Proof.Pbkdf2.Whole.X86
