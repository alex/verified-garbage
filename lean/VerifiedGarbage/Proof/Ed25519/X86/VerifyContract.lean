import VerifiedGarbage.Proof.Ed25519.X86.InputSlice
import VerifiedGarbage.Proof.Ed25519.X86.CopyWords
import VerifiedGarbage.Proof.Ed25519.X86.RecoverParity

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.X25519.X86 VG.Impl.Ed25519.X86

def verifyLocal : Contract isa where
  pre s :=
    let pk := sub (arg s 0) 0 32
    let sig := sub (arg s 1) 0 64
    let challenge := sub (arg s 2) 0 64
    let scratch := scR 8192 (arg s 3)
    let args : Region := ⟨argAddr s 0, 16⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [pk, sig, challenge, args] ∧ s.wr = [sub (arg s 3) 0 0, scratch] ∧
      pk.Disjoint scratch ∧ sig.Disjoint scratch ∧ challenge.Disjoint scratch ∧
      args.Disjoint scratch ∧ ret.Disjoint scratch ∧
      (arg s 0).toNat + 32 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 64 ≤ 2 ^ 32 ∧
      (arg s 2).toNat + 64 ≤ 2 ^ 32 ∧ (arg s 3).toNat + 8192 ≤ 2 ^ 32 ∧
      (s.gpr .esp).toNat + 20 ≤ 2 ^ 32
  post s t := t.gpr .eax = signWord (Spec.Ed25519.verifyEquation
    (Spec.Ed25519.bytesAt s.mem ((arg s 0).setWidth 64) 32) (Spec.Ed25519.bytesAt s.mem ((arg s 1).setWidth 64) 64)
    (Spec.Ed25519.bytesAt s.mem ((arg s 2).setWidth 64) 64))
  pub s t := s.gpr .esp = t.gpr .esp ∧ arg s 0 = arg t 0 ∧ arg s 1 = arg t 1 ∧
    arg s 2 = arg t 2 ∧ arg s 3 = arg t 3 ∧
    Spec.Ed25519.bytesAt s.mem ((arg s 0).setWidth 64) 32 = Spec.Ed25519.bytesAt t.mem ((arg t 0).setWidth 64) 32 ∧
    Spec.Ed25519.bytesAt s.mem ((arg s 1).setWidth 64) 64 = Spec.Ed25519.bytesAt t.mem ((arg t 1).setWidth 64) 64 ∧
    Spec.Ed25519.bytesAt s.mem ((arg s 2).setWidth 64) 64 = Spec.Ed25519.bytesAt t.mem ((arg t 2).setWidth 64) 64

theorem input_slice {s : State} {scidx i n skip bytes : Nat} (h : InputPre s scidx i n)
    (hn : skip + bytes ≤ 4 * n) (hb : 0 < bytes) :
    SlicePre s scidx (arg s i + BitVec.ofNat 32 skip) bytes := by
  have hf := h.fit
  have hs : skip < 2 ^ 32 := by omega_using [hn, hb, hf]
  refine ⟨?_, ?_, ?_⟩
  · intro k len hl hk
    rw [addr_plus]
    exact ⟨_, h.rd, sub_contains (by omega_using [hf]) (Nat.zero_le _)
      (by omega_using [hn, hk]) hl⟩
  · rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hs,
      Nat.mod_eq_of_lt (by omega_using [hn, hb, hf])]
    omega_using [hn, hf]
  · apply h.sep.sub_left
    rw [sub, addr_plus, Nat.add_zero, sub, addr_eq (by omega_using [hn, hb, hf]), addr_zero]
    exact Offset.sub_base _ hn

structure VerifyPre (s : State) : Prop where
  scratch : ScratchPre s 3 4
  pk : SlicePre s 3 (arg s 0 + BitVec.ofNat 32 0) 32
  r : SlicePre s 3 (arg s 1 + BitVec.ofNat 32 0) 32
  scalar : SlicePre s 3 (arg s 1 + BitVec.ofNat 32 32) 32
  challenge : SlicePre s 3 (arg s 2 + BitVec.ofNat 32 0) 64
  signature_fit : (arg s 1).toNat + 64 ≤ 2 ^ 32

theorem verify_pre {s : State} (h : verifyLocal.pre s) : VerifyPre s := by
  obtain ⟨rd, wr, ps, ss, cs, ars, rs, pf, sf, cf, scf, spf⟩ := h
  have hp : ScratchPre s 3 4 := ⟨by decide, by rw [wr]; simp, scf,
    by rw [rd]; simp, by omega_using [spf], ars, rs⟩
  have p : InputPre s 3 0 8 := ⟨by rw [rd]; simp, pf, ps⟩
  have sg : InputPre s 3 1 16 := ⟨by rw [rd]; simp, sf, ss⟩
  have ch : InputPre s 3 2 16 := ⟨by rw [rd]; simp, cf, cs⟩
  exact ⟨hp, input_slice p (by decide) (by decide), input_slice sg (by decide) (by decide),
    input_slice sg (by decide) (by decide), input_slice ch (by decide) (by decide), sf⟩

end VG.Proof.Ed25519.X86
