import VerifiedGarbage.Proof.Ed25519.X86.ScalarContract

namespace VG.Proof.Ed25519.X86
open VG VG.X86

def scalarMulAddLocal : Contract isa where
  pre s :=
    let out : Region := ⟨(arg s 0).setWidth 64, 32⟩
    let r : Region := ⟨(arg s 1).setWidth 64, 32⟩
    let k : Region := ⟨(arg s 2).setWidth 64, 32⟩
    let a : Region := ⟨(arg s 3).setWidth 64, 32⟩
    let scratch : Region := ⟨(arg s 4).setWidth 64, 8192⟩
    let args : Region := ⟨argAddr s 0, 20⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [r, k, a, args] ∧ s.wr = [out, scratch] ∧ out.Disjoint scratch ∧
      r.Disjoint scratch ∧ k.Disjoint scratch ∧ a.Disjoint scratch ∧
      args.Disjoint out ∧ args.Disjoint scratch ∧ ret.Disjoint out ∧ ret.Disjoint scratch ∧
      (arg s 0).toNat + 32 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 32 ≤ 2 ^ 32 ∧
      (arg s 2).toNat + 32 ≤ 2 ^ 32 ∧ (arg s 3).toNat + 32 ≤ 2 ^ 32 ∧
      (arg s 4).toNat + 8192 ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 24 ≤ 2 ^ 32
  post s t := Spec.Ed25519.bytesAt t.mem ((arg s 0).setWidth 64) 32 =
    Spec.Ed25519.scalarMulAdd (Spec.Ed25519.bytesAt s.mem ((arg s 1).setWidth 64) 32)
      (Spec.Ed25519.bytesAt s.mem ((arg s 2).setWidth 64) 32)
      (Spec.Ed25519.bytesAt s.mem ((arg s 3).setWidth 64) 32)
  pub s t := s.gpr .esp = t.gpr .esp ∧ arg s 0 = arg t 0 ∧ arg s 1 = arg t 1 ∧
    arg s 2 = arg t 2 ∧ arg s 3 = arg t 3 ∧ arg s 4 = arg t 4

theorem scalarMulAdd_pre {s : State} (h : scalarMulAddLocal.pre s) :
    ScratchPre s 4 5 ∧ InputPre s 4 2 8 ∧ InputPre s 4 3 8 ∧ InputPre s 4 1 8 ∧ OutputPre s 4 := by
  obtain ⟨rd, wr, os, rs, ks, ss, _, ars, ro, rsc, ofit, rfit, kfit, afit, sfit, spfit⟩ := h
  refine ⟨⟨by decide, ?_, sfit, ?_, by omega_using [spfit], ars, rsc⟩,
    ⟨?_, kfit, ?_⟩, ⟨?_, afit, ?_⟩, ⟨?_, rfit, ?_⟩, ⟨?_, ofit, os, ro⟩⟩
  · rw [wr]; simp
  · rw [rd]; simp
  · rw [sub, addr_zero, rd]; simp
  · rw [sub, addr_zero]; exact ks
  · rw [sub, addr_zero, rd]; simp
  · rw [sub, addr_zero]; exact ss
  · rw [sub, addr_zero, rd]; simp
  · rw [sub, addr_zero]; exact rs
  · rw [wr]; simp
end VG.Proof.Ed25519.X86
