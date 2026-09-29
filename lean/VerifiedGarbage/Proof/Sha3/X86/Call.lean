import VerifiedGarbage.Proof.Sha3.X86.Permute
import VerifiedGarbage.Proof.Sha3.Stream
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Impl.Sha3.X86.Stream

/-!
# SHA-3 on x86 (32-bit): calling the permutation

Untrusted: everything here is checked by Lean. A call of `vg_keccak_f1600`
in a frame of its two arguments (`permuteCall`), from its proof of
`Verified` (`WP.callWith`).
-/

namespace VG.Proof.Sha3.X86

open VG VG.X86
open VG.Spec.Sha3 (stateAt keccakF)

theorem permute_nosp : NoSp Impl.Sha3.X86.permute := NoSp.of_all (by decide +kernel)

theorem permute_stack : stackUse Impl.Sha3.X86.permute = 0 := by decide +kernel

/-- A region at offset `o` within one of `rs'`. -/
theorem within {r : Region} {rs' : List Region} (r' : Region) (hr' : r' ∈ rs') (o : Nat)
    (hb : r.base = r'.base + BitVec.ofNat 64 o) (hl : o + r.len ≤ r'.len) :
    ∃ r' ∈ rs', ∃ o, r.base = r'.base + BitVec.ofNat 64 o ∧ o + r.len ≤ r'.len :=
  ⟨r', hr', o, hb, hl⟩

/-- Calling `vg_keccak_f1600(st, scr)` on the state at `S` with the first 512
bytes of the scratch space at `C` (of 640 bytes): the call uses the 12 bytes
below `esp` (`E`), for its arguments and return address. -/
theorem permuteCall_ok {st scr : Reg} (hst : st ≠ .esp) (hscr : scr ≠ .esp) {s : State}
    {S C E : BitVec 32} (hesp : s.gpr .esp = E) (hS : s.gpr st = S) (hC : s.gpr scr = C)
    (hE : 12 ≤ E.toNat) (fS : S.toNat + 200 ≤ 2 ^ 32) (fC : C.toNat + 512 ≤ 2 ^ 32)
    (d : (reg32 S 200).Disjoint (reg32 C 512)) (dS : (below E 12).Disjoint (reg32 S 200))
    (dC : (below E 12).Disjoint (reg32 C 512)) (wS : reg32 S 200 ∈ s.wr) (wC : reg32 C 640 ∈ s.wr)
    {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [reg32 S 200, reg32 C 512, below E 12] s.mem s'.mem →
      stateAt s'.mem (S.setWidth 64) = keccakF (stateAt s.mem (S.setWidth 64)) → Q s') :
    WP isa (Impl.Sha3.X86.Stream.permuteCall st scr) s Q := by
  have fit : 4 * [scr, st].length + 4 ≤ (s.gpr .esp).toNat := by
    rw [hesp]; simp only [List.length_cons, List.length_nil]; omega
  have hrs : Reg.esp ∉ [scr, st] := by simp [Ne.symm hst, Ne.symm hscr]
  have a0 : arg (pushed [scr, st] s).callEntry 0 = S := by
    rw [callEntry_arg fit hrs (by simp)]; exact hS
  have a1 : arg (pushed [scr, st] s).callEntry 1 = C := by
    rw [callEntry_arg fit hrs (by simp)]; exact hC
  have eA : argAddr (pushed [scr, st] s).callEntry 0 = (E - BitVec.ofNat 32 8).setWidth 64 := by
    rw [callEntry_argAddr0, hesp]; rfl
  have eSp : (pushed [scr, st] s).callEntry.gpr .esp = E - BitVec.ofNat 32 12 := by
    rw [callEntry_esp', hesp]; rfl
  have b8 : Region.Sub (below E 8) (below E 12) := below_sub (by omega) hE
  have r4 : Region.Sub ⟨(E - BitVec.ofNat 32 12).setWidth 64, 4⟩ (below E 12) := by
    have := below_inner (sp := E) (a := 4) (b := 12) (k := 8) (by omega) hE
    rw [show E - BitVec.ofNat 32 12 = E - BitVec.ofNat 32 8 - BitVec.ofNat 32 4 by bv_omega]
    exact this
  refine WP.callWith (k := Proof.Sha3.permuteX86) permute_verified.1 permute_nosp (by simp) hrs
    (by rw [permute_stack, hesp]; simp only [List.length_cons, List.length_nil]; omega)
    (rd := [⟨argAddr (pushed [scr, st] s).callEntry 0, 8⟩]) (wr := [reg32 S 200, reg32 C 512])
    ⟨?_, ?_, ?_⟩ fun s' rd' wr' cs' f' ⟨s₂, m₂, post⟩ => ?_
  · simp only [Proof.Sha3.permuteX86, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr,
      arg_withRegions, argAddr_withRegions, a0, a1, eA, eSp]
    refine ⟨trivial, trivial, d, dS.sub_left b8, dC.sub_left b8, dS.sub_left r4, dC.sub_left r4, fS, fC, ?_⟩
    rw [sub_toNat hE]; have := E.isLt; omega
  · rw [hesp]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact within (below E (4 * [scr, st].length)) (by simp) 0 (by rw [eA]; simp) (by simp)
    · exact within (reg32 S 200) (by simp [wS]) 0 (by simp) (by simp)
    · exact within (reg32 C 640) (by simp [wC]) 0 (by simp) (by simp)
  · refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact within (reg32 S 200) (by simp [wS]) 0 (by simp) (by simp)
    · exact within (reg32 C 640) (by simp [wC]) 0 (by simp) (by simp)
  · rw [permute_stack, hesp] at f'
    have hsE : Frame [below E 12] s.mem (pushed [scr, st] s).callEntry.mem := by
      have := callEntry_frame fit hrs
      rw [hesp] at this; exact this
    simp only [Proof.Sha3.permuteX86, arg_withRegions, State.withRegions_mem, a0, m₂] at post
    refine hQ s' rd' wr' cs' f' ?_
    rw [post]
    refine congrArg keccakF (Proof.Sha3.stateAt_congr fun i hi => ?_)
    exact hsE.bytes (R := reg32 S 200) (by simpa using dS.symm) (by simp) hi

end VG.Proof.Sha3.X86
