import VerifiedGarbage.Proof.TripleDes.X86.ConstantTime
import VerifiedGarbage.Proof.TripleDes.X86.Contract

namespace VG.Proof.TripleDes.X86
open VG VG.X86
open VG.Proof.Rc2.X86 (addr32)
open VG.Spec.TripleDes (Direction)

theorem blockTaint_wf {d : Direction} {s : State} (hs : (blockContract d).pre s) : VG.X86.Taint.Wf blockTaint s := by
  obtain ⟨_, hwr, _, dataSep, argsData, argsScratch, retData, retScratch, _, dataFit, scratchFit, spFit⟩ := hs
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun _ => ⟨?_, ?_, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨spFit, ?_⟩, ?_⟩
  · rw [hwr]
    exact .cons (Nat.le_refl _) (.cons (Nat.le_refl _) .nil)
  · simp only [hwr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq, List.Pairwise.nil, and_true]
    exact ⟨dataSep, fun _ h => h.elim⟩
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [addr32, BitVec.toNat_setWidth] <;> omega
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 12) (by omega) retData argsData
    · exact VG.X86.Taint.frame_disjoint (n := 12) (by omega) retScratch argsScratch
  · intro p hp
    simp only [blockTaint, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> refine ⟨by decide, ?_⟩ <;>
      simp [VG.X86.Taint.region, hwr, addr, addr32, arg, argAddr]

theorem blockTaint_agree {d : Direction} {s t : State} (hs : (blockContract d).pre s)
    (ht : (blockContract d).pre t) (hp : (blockContract d).pub s t) :
    VG.X86.Taint.Agree blockTaint s t := by
  obtain ⟨sp, args⟩ := hp
  have fit : ∀ s, (blockContract d).pre s → (s.gpr .esp).toNat + 16 ≤ 2 ^ 32 := by
    intro s hs; exact hs.2.2.2.2.2.2.2.2.2.2.2
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, blockTaint_wf hs,
    blockTaint_wf ht, fun _ h => (List.not_mem_nil h).elim,
    fun _ h => (List.not_mem_nil h).elim, fun _ => sp, fun k h4 hk => ?_⟩
  · simp only [blockTaint, RegSet.mem_ofList, List.mem_singleton] at hr
    subst r; exact sp
  · rw [hs.2.1, ht.2.1, args 1 (by decide), args 2 (by decide)]
  · simp only [blockTaint] at hk
    rw [show VG.X86.Taint.depth blockTaint.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq (fit _ hs) h4 hk, VG.X86.Taint.argByte_eq (fit _ ht) h4 hk,
      Mem.readW_byte s.mem _ (Nat.mod_lt _ (by decide)), Mem.readW_byte t.mem _ (Nat.mod_lt _ (by decide))]
    exact congrArg _ (args ((k - 4) / 4) (by omega))

end VG.Proof.TripleDes.X86
