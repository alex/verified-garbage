import VerifiedGarbage.Proof.MlKem.X86.TopCall
import VerifiedGarbage.Proof.MlKem.X86.Ntt
import VerifiedGarbage.Proof.MlKem.X86.NttInv
import VerifiedGarbage.Proof.MlKem.X86.Mul
import VerifiedGarbage.Proof.MlKem.X86.AddSub

/-!
# ML-KEM on x86 (32-bit): calls of the primitives in the top-level functions

Untrusted: everything here is checked by Lean. Each primitive is called
(`call_piece`) with its buffers named as `Buf`s, from registers holding
their addresses; its contract's precondition (`Sig.contract`) at the
callee's entry comes from `Ctx` and the buffers' layout, and its
postcondition is restated on the caller's memory.
-/

namespace VG.Proof.MlKem.X86.Top

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Spec.MlKem
open VG.Proof.Sha3.X86 (reg32)

variable {Y : Lay} {lk : State → List Byte} {A B : State → State → Prop}

theorem ntt_nosp : NoSp Impl.MlKem.X86.ntt := NoSp.of_all (by decide +kernel)
theorem ntt_stack : stackUse Impl.MlKem.X86.ntt = 16 := by decide +kernel
theorem nttInv_nosp : NoSp Impl.MlKem.X86.nttInv := NoSp.of_all (by decide +kernel)
theorem nttInv_stack : stackUse Impl.MlKem.X86.nttInv = 16 := by decide +kernel

/-- `NTT` or `NTT⁻¹` in place, of the polynomial at `(fa, fo)`, with the scratch at `(sa, so)`. -/
theorem inPlace_call {t : Poly → Poly} {nm : String} {c : Prog isa}
    (hv : Verified X86.target c (inPlaceContract X86.abi t 16)) (hsp : NoSp c) (hst : stackUse c = 16)
    (fa fo sa so : Nat)
    (hc : (Y.okW ⟨fa, fo, 1024⟩ && Y.okW ⟨sa, so, 1024⟩ && Y.sep ⟨fa, fo, 1024⟩ ⟨sa, so, 1024⟩) = true)
    (hN : 44 ≤ Y.stk)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s ∧ s.gpr .eax = Buf.ptr s₀ ⟨fa, fo, 1024⟩ ∧
      s.gpr .ecx = Buf.ptr s₀ ⟨sa, so, 1024⟩ ∧ Reduced s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩))
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → Ctx Y s₀ s' → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame ([⟨fa, fo, 1024⟩, ⟨sa, so, 1024⟩].map (Buf.rgn s₀) ++ [below (E1 s₀) 28]) s.mem s'.mem →
      PolyIs s'.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩) (t (polyAt s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩))) → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B (callWith [.ecx, .eax] nm c) := by
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨hF, hS⟩, dFS⟩ := hc
  have hF' := (Lay.okW_iff.mp hF).1
  have hS' := (Lay.okW_iff.mp hS).1
  refine call_piece hv hsp (by decide) (by decide) (by rw [hst]; simp only [List.length_cons, List.length_nil]; omega)
    (fun _ => []) (fun s₀ => [Buf.rgn s₀ ⟨fa, fo, 1024⟩, Buf.rgn s₀ ⟨sa, so, 1024⟩, below (E1 s₀) 8])
    (fun s₀ s hp ha => ?_) (fun s₀ s₀' s s' hp hp' hq ha ha' => ?_) (fun s₀ hp r hr => ?_)
    (fun s₀ s s' hp ha h' e₃ fr post => ?_)
  · obtain ⟨h, hax, hcx, hred⟩ := hA s₀ s hp ha
    have hE := ctx_E hp h (N := 28) (by omega)
    have fit : 4 * [Reg.ecx, Reg.eax].length + 4 ≤ (s.gpr .esp).toNat := by
      simp only [List.length_cons, List.length_nil]; omega
    have a0 : arg (pushed [.ecx, .eax] s).callEntry 0 = Buf.ptr s₀ ⟨fa, fo, 1024⟩ := by
      rw [callEntry_arg fit (by decide) (by decide)]; exact hax
    have a1 : arg (pushed [.ecx, .eax] s).callEntry 1 = Buf.ptr s₀ ⟨sa, so, 1024⟩ := by
      rw [callEntry_arg fit (by decide) (by decide)]; exact hcx
    have eA : argAddr (pushed [.ecx, .eax] s).callEntry 0 = (E1 s₀ - BitVec.ofNat 32 8).setWidth 64 := by
      rw [callEntry_argAddr0, h.esp]; rfl
    have eSp : (pushed [.ecx, .eax] s).callEntry.gpr .esp = E1 s₀ - BitVec.ofNat 32 12 := by
      rw [callEntry_esp', h.esp]; rfl
    have hE' : 28 ≤ (E1 s₀).toNat := by rw [← h.esp]; exact hE
    have bF := Buf.stkD hp hF' (N := 4 * 2 + 4 + 16) (by omega)
    have bS := Buf.stkD hp hS' (N := 4 * 2 + 4 + 16) (by omega)
    obtain ⟨rF₁, rF₂, rF₃⟩ := entry_regions hE' bF
    obtain ⟨rS₁, rS₂, rS₃⟩ := entry_regions hE' bS
    obtain ⟨rA₂, rA₃⟩ := entry_self (E := E1 s₀) (k := 2) (K := 16) hE'
    have ef := callEntry_frame fit (by decide)
    have cv := covers_of (s := s) (n := 2) (rd := []) (wr := [Buf.rgn s₀ ⟨fa, fo, 1024⟩,
        Buf.rgn s₀ ⟨sa, so, 1024⟩, below (E1 s₀) 8]) (fun r hr => absurd hr (by simp)) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact .inr (Buf.withinW hp hF' (Lay.okW_iff.mp hF).2 h.wr)
      · exact .inr (Buf.withinW hp hS' (Lay.okW_iff.mp hS).2 h.wr)
      · exact .inl (by rw [h.esp])
    refine ⟨h, ?_, cv.1, cv.2⟩
    sig_pre [inPlaceContract, inPlaceSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr, State.withRegions_mem,
      arg_withRegions, argAddr_withRegions, a0, a1, eA, eSp]
    refine ⟨by rw [sub_toNat (by omega)]; omega, by rw [sub_toNat (by omega)]; have := (E1 s₀).isLt; omega,
      trivial, trivial, Buf.disj hp hF' hS' dFS, rF₁, rS₁, rF₂, rS₂, rA₂, rF₃, rS₃, rA₃,
      Buf.fit hp hF', Buf.fit hp hS', ?_⟩
    refine reduced_frame ef (fun r hr => ?_) hred
    rw [List.mem_singleton] at hr; subst hr; rw [h.esp]
    exact (bF.sub_left (below_sub (by simp) hE')).symm
  · obtain ⟨h, hax, hcx, -⟩ := hA s₀ s hp ha
    obtain ⟨h', hax', hcx', -⟩ := hA s₀' s' hp' ha'
    have hsp : s.gpr .esp = s'.gpr .esp := by rw [h.esp, h'.esp, hq.E1]
    have hr : ∀ r ∈ [Reg.ecx, Reg.eax], s.gpr r = s'.gpr r := by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [hcx, hcx', hq.ptr hS']
      · rw [hax, hax', hq.ptr hF']
    have fit : 4 * [Reg.ecx, Reg.eax].length + 4 ≤ (s.gpr .esp).toNat := by
      have := ctx_E hp h (N := 28) (by omega); simp only [List.length_cons, List.length_nil]; omega
    refine ⟨rfl, by simp only [Buf.rgn, hq.ptr hF', hq.ptr hS', hq.E1], ?_⟩
    sig_pub [inPlaceContract, inPlaceSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [State.withRegions_gpr, arg_withRegions, callEntry_esp', hsp]
    exact ⟨trivial, callEntry_arg_eq (by decide) fit hsp hr (by decide),
      callEntry_arg_eq (by decide) fit hsp hr (by decide)⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Buf.inW hp hF' (Lay.okW_iff.mp hF).2
    · exact Buf.inW hp hS' (Lay.okW_iff.mp hS).2
    · exact ⟨cR Y s₀, TPre.cW, stk_sub hp (by omega) (by have := hp.sp16; omega)⟩
  · obtain ⟨h, hax, -, -⟩ := hA s₀ s hp ha
    obtain ⟨s₂, m₂, post⟩ := post
    have fit : 4 * [Reg.ecx, Reg.eax].length + 4 ≤ (s.gpr .esp).toNat := by
      have := ctx_E hp h (N := 28) (by omega); simp only [List.length_cons, List.length_nil]; omega
    have a0 : arg (pushed [.ecx, .eax] s).callEntry 0 = Buf.ptr s₀ ⟨fa, fo, 1024⟩ := by
      rw [callEntry_arg fit (by decide) (by decide)]; exact hax
    have hE' : 28 ≤ (E1 s₀).toNat := by rw [← h.esp]; exact ctx_E hp h (N := 28) (by omega)
    have bF := Buf.stkD hp hF' (N := 4 * 2 + 4 + 16) (by omega)
    sig_post [inPlaceContract, inPlaceSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at post
    simp only [arg_withRegions, State.withRegions_mem, a0, m₂] at post
    rw [polyAt_frame (callEntry_frame fit (by decide)) (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; rw [h.esp]
      exact (bF.sub_left (below_sub (by simp) hE')).symm)] at post
    refine hQ s₀ s s' hp ha h' e₃ (fr.sub fun r hr => ?_) post
    rw [hst] at hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨Buf.rgn s₀ ⟨fa, fo, 1024⟩, by simp, fun _ h => h⟩
    · exact ⟨Buf.rgn s₀ ⟨sa, so, 1024⟩, by simp, fun _ h => h⟩
    · exact ⟨below (E1 s₀) 28, by simp, stk_sub hp (by omega) (by omega)⟩
    · exact ⟨below (E1 s₀) 28, by simp, fun _ h => h⟩

theorem mul_nosp : NoSp Impl.MlKem.X86.multiplyNTTs := NoSp.of_all (by decide +kernel)
theorem mul_stack : stackUse Impl.MlKem.X86.multiplyNTTs = 16 := by decide +kernel

/-- `h ← MultiplyNTTs(f, g)`, with the polynomials at `(ha, ho)`, `(fa, fo)`, `(ga, go)` and the scratch
at `(sa, so)`, in `eax`, `ecx`, `edx` and `edi`. -/
theorem mul_call (oa oo fa fo ga go sa so : Nat)
    (hc : (Y.okW ⟨oa, oo, 1024⟩ && Y.ok ⟨fa, fo, 1024⟩ && Y.ok ⟨ga, go, 1024⟩ && Y.okW ⟨sa, so, 1024⟩ &&
      Y.sep ⟨oa, oo, 1024⟩ ⟨fa, fo, 1024⟩ && Y.sep ⟨oa, oo, 1024⟩ ⟨ga, go, 1024⟩ &&
      Y.sep ⟨oa, oo, 1024⟩ ⟨sa, so, 1024⟩ && Y.sep ⟨fa, fo, 1024⟩ ⟨sa, so, 1024⟩ &&
      Y.sep ⟨ga, go, 1024⟩ ⟨sa, so, 1024⟩) = true) (hN : 52 ≤ Y.stk)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s ∧ s.gpr .eax = Buf.ptr s₀ ⟨oa, oo, 1024⟩ ∧
      s.gpr .ecx = Buf.ptr s₀ ⟨fa, fo, 1024⟩ ∧ s.gpr .edx = Buf.ptr s₀ ⟨ga, go, 1024⟩ ∧
      s.gpr .edi = Buf.ptr s₀ ⟨sa, so, 1024⟩ ∧ Reduced s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩) ∧
      Reduced s.mem (Buf.addr s₀ ⟨ga, go, 1024⟩))
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → Ctx Y s₀ s' → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame ([⟨oa, oo, 1024⟩, ⟨sa, so, 1024⟩].map (Buf.rgn s₀) ++ [below (E1 s₀) 36]) s.mem s'.mem →
      PolyIs s'.mem (Buf.addr s₀ ⟨oa, oo, 1024⟩)
        (multiplyNTTs (polyAt s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩)) (polyAt s.mem (Buf.addr s₀ ⟨ga, go, 1024⟩))) →
      B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B
      (callWith [.edi, .edx, .ecx, .eax] "vg_mlkem_multiply_ntts" Impl.MlKem.X86.multiplyNTTs) := by
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hH, hF'⟩, hG'⟩, hS⟩, dHF⟩, dHG⟩, dHS⟩, dFS⟩, dGS⟩ := hc
  have hH' := (Lay.okW_iff.mp hH).1
  have hS' := (Lay.okW_iff.mp hS).1
  refine call_piece Mul.verified mul_nosp (by decide) (by decide)
    (by rw [mul_stack]; simp only [List.length_cons, List.length_nil]; omega)
    (fun s₀ => [Buf.rgn s₀ ⟨fa, fo, 1024⟩, Buf.rgn s₀ ⟨ga, go, 1024⟩])
    (fun s₀ => [Buf.rgn s₀ ⟨oa, oo, 1024⟩, Buf.rgn s₀ ⟨sa, so, 1024⟩] ++ [below (E1 s₀) 16])
    (fun s₀ s hp ha => ?_) (fun s₀ s₀' s s' hp hp' hq ha ha' => ?_)
    (fun s₀ hp => wr_sub hp (bs := [⟨oa, oo, 1024⟩, ⟨sa, so, 1024⟩]) (by simp [hH, hS]) (by omega))
    (fun s₀ s s' hp ha h' e₃ fr post => ?_)
  · obtain ⟨h, hax, hcx, hdx, hdi, rF, rG⟩ := hA s₀ s hp ha
    have hE' : 36 ≤ (E1 s₀).toNat := by rw [← h.esp]; exact ctx_E hp h (N := 36) (by omega)
    have fit : 4 * [Reg.edi, Reg.edx, Reg.ecx, Reg.eax].length + 4 ≤ (s.gpr .esp).toNat := by
      rw [h.esp]; simp only [List.length_cons, List.length_nil]; omega
    have a0 : arg (pushed [.edi, .edx, .ecx, .eax] s).callEntry 0 = Buf.ptr s₀ ⟨oa, oo, 1024⟩ := by
      rw [callEntry_arg fit (by decide) (by decide)]; exact hax
    have a1 : arg (pushed [.edi, .edx, .ecx, .eax] s).callEntry 1 = Buf.ptr s₀ ⟨fa, fo, 1024⟩ := by
      rw [callEntry_arg fit (by decide) (by decide)]; exact hcx
    have a2 : arg (pushed [.edi, .edx, .ecx, .eax] s).callEntry 2 = Buf.ptr s₀ ⟨ga, go, 1024⟩ := by
      rw [callEntry_arg fit (by decide) (by decide)]; exact hdx
    have a3 : arg (pushed [.edi, .edx, .ecx, .eax] s).callEntry 3 = Buf.ptr s₀ ⟨sa, so, 1024⟩ := by
      rw [callEntry_arg fit (by decide) (by decide)]; exact hdi
    have eA : argAddr (pushed [.edi, .edx, .ecx, .eax] s).callEntry 0 = (E1 s₀ - BitVec.ofNat 32 16).setWidth 64 := by
      rw [callEntry_argAddr0, h.esp]; rfl
    have eSp : (pushed [.edi, .edx, .ecx, .eax] s).callEntry.gpr .esp = E1 s₀ - BitVec.ofNat 32 20 := by
      rw [callEntry_esp', h.esp]; rfl
    have bH := Buf.stkD hp hH' (N := 4 * 4 + 4 + 16) (by omega)
    have bF := Buf.stkD hp hF' (N := 4 * 4 + 4 + 16) (by omega)
    have bG := Buf.stkD hp hG' (N := 4 * 4 + 4 + 16) (by omega)
    have bS := Buf.stkD hp hS' (N := 4 * 4 + 4 + 16) (by omega)
    obtain ⟨rH₁, rH₂, rH₃⟩ := entry_regions hE' bH
    obtain ⟨rF₁, rF₂, rF₃⟩ := entry_regions hE' bF
    obtain ⟨rG₁, rG₂, rG₃⟩ := entry_regions hE' bG
    obtain ⟨rS₁, rS₂, rS₃⟩ := entry_regions hE' bS
    obtain ⟨rA₂, rA₃⟩ := entry_self (E := E1 s₀) (k := 4) (K := 16) hE'
    have cv := covers_of (s := s) (n := 4) (rd := [Buf.rgn s₀ ⟨fa, fo, 1024⟩, Buf.rgn s₀ ⟨ga, go, 1024⟩])
      (wr := [Buf.rgn s₀ ⟨oa, oo, 1024⟩, Buf.rgn s₀ ⟨sa, so, 1024⟩] ++ [below (E1 s₀) 16])
      (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact Buf.within hp hF' h.rd h.wr
        · exact Buf.within hp hG' h.rd h.wr) fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact .inr (Buf.withinW hp hH' (Lay.okW_iff.mp hH).2 h.wr)
      · exact .inr (Buf.withinW hp hS' (Lay.okW_iff.mp hS).2 h.wr)
      · exact .inl (by rw [h.esp])
    refine ⟨h, ?_, cv.1, cv.2⟩
    sig_pre [mulContract, mulSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr, State.withRegions_mem,
      arg_withRegions, argAddr_withRegions, a0, a1, a2, a3, eA, eSp]
    have ek := @ent_keep Y s₀ s hp h [.edi, .edx, .ecx, .eax] (by decide) (by simp; omega)
    refine ⟨by rw [sub_toNat (by omega)]; omega, by rw [sub_toNat (by omega)]; have := (E1 s₀).isLt; omega,
      trivial, trivial, Buf.disj hp hH' hF' dHF, Buf.disj hp hH' hG' dHG, Buf.disj hp hH' hS' dHS, rH₁,
      Buf.disj hp hF' hS' dFS, rF₁, Buf.disj hp hG' hS' dGS, rG₁, rS₁, rH₂, rF₂, rG₂, rS₂, rA₂,
      rH₃, rF₃, rG₃, rS₃, rA₃, Buf.fit hp hH', Buf.fit hp hF', Buf.fit hp hG', Buf.fit hp hS',
      reduced_congr (ek hF') rF, reduced_congr (ek hG') rG⟩
  · obtain ⟨h, hax, hcx, hdx, hdi, -⟩ := hA s₀ s hp ha
    obtain ⟨h', hax', hcx', hdx', hdi', -⟩ := hA s₀' s' hp' ha'
    have hsp : s.gpr .esp = s'.gpr .esp := by rw [h.esp, h'.esp, hq.E1]
    have hr : ∀ r ∈ [Reg.edi, Reg.edx, Reg.ecx, Reg.eax], s.gpr r = s'.gpr r := by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [hdi, hdi', hq.ptr hS']
      · rw [hdx, hdx', hq.ptr hG']
      · rw [hcx, hcx', hq.ptr hF']
      · rw [hax, hax', hq.ptr hH']
    have fit : 4 * [Reg.edi, Reg.edx, Reg.ecx, Reg.eax].length + 4 ≤ (s.gpr .esp).toNat := by
      have := ctx_E hp h (N := 36) (by omega); simp only [List.length_cons, List.length_nil]; omega
    refine ⟨by simp only [Buf.rgn, hq.ptr hF', hq.ptr hG'], by simp only [Buf.rgn, hq.ptr hH', hq.ptr hS', hq.E1], ?_⟩
    sig_pub [mulContract, mulSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [State.withRegions_gpr, arg_withRegions, callEntry_esp', hsp]
    exact ⟨trivial, callEntry_arg_eq (by decide) fit hsp hr (by decide),
      callEntry_arg_eq (by decide) fit hsp hr (by decide), callEntry_arg_eq (by decide) fit hsp hr (by decide),
      callEntry_arg_eq (by decide) fit hsp hr (by decide)⟩
  · obtain ⟨h, hax, hcx, hdx, -⟩ := hA s₀ s hp ha
    obtain ⟨s₂, m₂, post⟩ := post
    have fit : 4 * [Reg.edi, Reg.edx, Reg.ecx, Reg.eax].length + 4 ≤ (s.gpr .esp).toNat := by
      have := ctx_E hp h (N := 36) (by omega); simp only [List.length_cons, List.length_nil]; omega
    have a0 : arg (pushed [.edi, .edx, .ecx, .eax] s).callEntry 0 = Buf.ptr s₀ ⟨oa, oo, 1024⟩ := by
      rw [callEntry_arg fit (by decide) (by decide)]; exact hax
    have a1 : arg (pushed [.edi, .edx, .ecx, .eax] s).callEntry 1 = Buf.ptr s₀ ⟨fa, fo, 1024⟩ := by
      rw [callEntry_arg fit (by decide) (by decide)]; exact hcx
    have a2 : arg (pushed [.edi, .edx, .ecx, .eax] s).callEntry 2 = Buf.ptr s₀ ⟨ga, go, 1024⟩ := by
      rw [callEntry_arg fit (by decide) (by decide)]; exact hdx
    have ek := @ent_keep Y s₀ s hp h [.edi, .edx, .ecx, .eax] (by decide) (by simp; omega)
    sig_post [mulContract, mulSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at post
    simp only [arg_withRegions, State.withRegions_mem, a0, a1, a2, m₂] at post
    rw [polyAt_congr (ek hF'), polyAt_congr (ek hG')] at post
    exact hQ s₀ s s' hp ha h' e₃ (fr_conv hp (a := 16) (N := 36) (by omega) (by omega)
      (by rw [mul_stack] at fr; exact fr)) post

end VG.Proof.MlKem.X86.Top
