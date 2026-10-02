import VerifiedGarbage.Proof.TripleDes.X86.ConstantTime
import VerifiedGarbage.Proof.TripleDes.X86.Ecb.Contract

namespace VG.Proof.TripleDes.X86.Ecb
open VG VG.X86
open VG.Proof.Rc2.X86 (addr32)

theorem ecbTaint_wf {d : Spec.TripleDes.Direction} {s : State} (hs : (contract d).pre s) : VG.X86.Taint.Wf ecbTaint s := by
  obtain ⟨_, hwr, _, _, dataSep, argsData, argsScratch, retData, retScratch, _, stackData, stackBuf, _, scratchFit, spFit, stackLo, dataFit⟩ := hs
  refine VG.X86.Taint.Wf.entryRoom rfl ⟨fun _ => ⟨?_, ?_, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨spFit, ?_⟩, ?_⟩ ?_
  · rw [hwr]
    exact .cons (Nat.zero_le _) (.cons (Nat.le_refl _) .nil)
  · simp only [hwr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq, List.Pairwise.nil, and_true]
    exact ⟨dataSep, fun _ h => h.elim⟩
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [addr32, BitVec.toNat_setWidth] <;> omega
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by omega) retData argsData
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by omega) retScratch argsScratch
  · intro p hp
    simp only [ecbTaint, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> refine ⟨by decide, ?_⟩ <;>
      simp [VG.X86.Taint.region, hwr, addr, addr32, arg, argAddr]
  · intro _
    refine ⟨stackLo, ?_⟩
    intro r hr
    have e : (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 16 =
        (s.gpr .esp - BitVec.ofNat 32 16).setWidth 64 := (VG.X86.Taint.sub_setWidth stackLo).symm
    change (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 16, 16⟩ : Region).Disjoint r
    rw [e]
    simp only [hwr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact stackData
    · exact stackBuf

theorem ecbTaint_agree {d : Spec.TripleDes.Direction} {s t : State} (hs : (contract d).pre s)
    (ht : (contract d).pre t) (hp : (contract d).pub s t) :
    VG.X86.Taint.Agree ecbTaint s t := by
  obtain ⟨sp, args⟩ := hp
  have fit : ∀ s, (contract d).pre s → (s.gpr .esp).toNat + 20 ≤ 2 ^ 32 := by
    intro s hs; obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, h, _, _⟩ := hs; exact h
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, ecbTaint_wf hs,
    ecbTaint_wf ht, fun _ h => (List.not_mem_nil h).elim,
    fun _ h => (List.not_mem_nil h).elim, fun _ => sp, fun k h4 hk => ?_⟩
  · simp only [ecbTaint, RegSet.mem_ofList, List.mem_singleton] at hr
    subst r; exact sp
  · rw [hs.2.1, ht.2.1, args 1 (by decide), args 2 (by decide), args 3 (by decide)]
  · simp only [ecbTaint] at hk
    rw [show VG.X86.Taint.depth ecbTaint.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq (fit _ hs) h4 hk, VG.X86.Taint.argByte_eq (fit _ ht) h4 hk,
      Mem.readW_byte s.mem _ (Nat.mod_lt _ (by decide)), Mem.readW_byte t.mem _ (Nat.mod_lt _ (by decide))]
    exact congrArg _ (args ((k - 4) / 4) (by omega))

end VG.Proof.TripleDes.X86.Ecb
