import VerifiedGarbage.Proof.TripleDes.X86_64.Ecb.IO
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.TripleDes.Contract

namespace VG.Proof.TripleDes.X86_64.Ecb

open VG VG.X86_64

def contract (d : Spec.TripleDes.Direction) : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .rdi, 384⟩
    let data : Region := ⟨s.gpr .rsi, 8 * (s.gpr .rdx).toNat⟩
    let buf : Region := ⟨s.gpr .rcx, 1024⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack := below (s.gpr .rsp) 8
    s.rd = [key] ∧ s.wr = [data, buf] ∧ key.Disjoint data ∧ key.Disjoint buf ∧
      data.Disjoint buf ∧ ret.Disjoint data ∧ ret.Disjoint buf ∧
      stack.Disjoint key ∧ stack.Disjoint data ∧ stack.Disjoint buf ∧
      (s.gpr .rsi).toNat + 8 * (s.gpr .rdx).toNat ≤ 2 ^ 64
  post s s' :=
    Spec.TripleDes.blocksAt s'.mem (s.gpr .rsi) (s.gpr .rdx).toNat =
      Spec.TripleDes.ecb (Spec.TripleDes.scheduleAt s.mem (s.gpr .rdi)) d
        (Spec.TripleDes.blocksAt s.mem (s.gpr .rsi) (s.gpr .rdx).toNat)
  pub := PublicRegs [.rdi, .rsi, .rdx, .rcx, .rsp]

theorem ecbTaint_wf (d : Spec.TripleDes.Direction) (s : State) (hs : (contract d).pre s) :
    Taint.Wf ecbTaint s := by
  obtain ⟨_, hwr, _, _, dataSep, _, _, _, _, _, fit⟩ := hs
  refine ⟨?_, ?_⟩
  · intro _
    rw [hwr]
    refine ⟨?_, ?_, ?_⟩
    · exact List.Forall₂.cons (by change 0 ≤ 8 * (s.gpr .rdx).toNat; omega)
        (List.Forall₂.cons (by change 1024 ≤ 1024; decide) List.Forall₂.nil)
    · exact List.Pairwise.cons
        (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact dataSep)
        (List.Pairwise.cons (by simp) List.Pairwise.nil)
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · change 8 * (s.gpr .rdx).toNat ≤ 2 ^ 64; omega
      · change 1024 ≤ 2 ^ 64; decide
  · intro p hp
    simp only [ecbTaint, List.mem_singleton] at hp
    subst p
    unfold Taint.region
    rw [hwr]
    change s.gpr .rcx = s.gpr .rcx + (0 : BitVec 64)
    exact (BitVec.add_zero _).symm

theorem ecbTaint_agree (d : Spec.TripleDes.Direction) (s t : State)
    (hs : (contract d).pre s) (ht : (contract d).pre t)
    (hp : (contract d).pub s t) : X86_64.Taint.Agree ecbTaint s t := by
  refine ⟨?_, ?_, ecbTaint_wf d s hs, ecbTaint_wf d t ht, ?_, ?_, ?_⟩
  · constructor
    · intro r hr
      exact hp r (by simpa only [ecbTaint, RegSet.mem_ofList] using hr)
    · intro h
      change false = true at h
      contradiction
  · intro _
    rw [hs.2.1, ht.2.1, hp .rsi (by decide), hp .rdx (by decide), hp .rcx (by decide)]
  · intro slot hslot
    change slot ∈ ([] : List (Nat × Nat × Nat)) at hslot
    exact False.elim (List.not_mem_nil hslot)
  · intro slot hslot
    change slot ∈ ([] : List (Nat × Nat × Nat)) at hslot
    exact False.elim (List.not_mem_nil hslot)
  · intro r hr
    simp only [ecbTaint, RegSet.not_mem_empty] at hr

end VG.Proof.TripleDes.X86_64.Ecb
