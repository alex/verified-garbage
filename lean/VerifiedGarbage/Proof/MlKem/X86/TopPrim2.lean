import VerifiedGarbage.Proof.MlKem.X86.TopPrim
import VerifiedGarbage.Proof.MlKem.X86.Cbd
import VerifiedGarbage.Proof.MlKem.X86.Encode12
import VerifiedGarbage.Proof.MlKem.X86.Decode12

/-!
# ML-KEM on x86 (32-bit): calls of the primitives of two arguments

Untrusted: everything here is checked by Lean. As `TopPrim.lean`, for
`vg_mlkem_add` and `vg_mlkem_sub` (`acc_call`), `vg_mlkem_cbd2`,
`vg_mlkem_encode12` and `vg_mlkem_decode12`, with their first argument in
`eax` and their second in `ecx`.
-/

namespace VG.Proof.MlKem.X86.Top

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Spec.MlKem
open VG.Proof.Sha3.X86 (reg32)

variable {Y : Lay} {lk : State → List Byte} {A B : State → State → Prop}

theorem cbd2_nosp : NoSp Impl.MlKem.X86.cbd2 := NoSp.of_all (by decide +kernel)
theorem cbd2_stack : stackUse Impl.MlKem.X86.cbd2 = 16 := by decide +kernel
theorem encode12_nosp : NoSp Impl.MlKem.X86.encode12 := NoSp.of_all (by decide +kernel)
theorem encode12_stack : stackUse Impl.MlKem.X86.encode12 = 16 := by decide +kernel
theorem decode12_nosp : NoSp Impl.MlKem.X86.decode12 := NoSp.of_all (by decide +kernel)
theorem decode12_stack : stackUse Impl.MlKem.X86.decode12 = 16 := by decide +kernel
theorem add_nosp : NoSp Impl.MlKem.X86.add := NoSp.of_all (by decide +kernel)
theorem add_stack : stackUse Impl.MlKem.X86.add = 16 := by decide +kernel
theorem sub_nosp : NoSp Impl.MlKem.X86.sub := NoSp.of_all (by decide +kernel)
theorem sub_stack : stackUse Impl.MlKem.X86.sub = 16 := by decide +kernel

/-- `f ← op(f, g)` (`vg_mlkem_add` or `vg_mlkem_sub`), with `f` at `(fa, fo)` and `g` at `(ga, go)`. -/
theorem acc_call {op : Poly → Poly → Poly} {nm : String} {c : Prog isa}
    (hv : Verified X86.target c (accSig.contract X86.abi (pre := fun f g m => Reduced m f ∧ Reduced m g)
      (post := fun f g m m' _ => PolyIs m' f (op (polyAt m f) (polyAt m g))) (writeArgs := true) (stack := 16)))
    (hsp : NoSp c) (hst : stackUse c = 16) (fa fo ga go : Nat)
    (hc : (Y.okW ⟨fa, fo, 1024⟩ && Y.ok ⟨ga, go, 1024⟩ && Y.sep ⟨fa, fo, 1024⟩ ⟨ga, go, 1024⟩) = true) (hN : 44 ≤ Y.stk)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s ∧ s.gpr .eax = Buf.ptr s₀ ⟨fa, fo, 1024⟩ ∧
      s.gpr .ecx = Buf.ptr s₀ ⟨ga, go, 1024⟩ ∧ Reduced s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩) ∧ Reduced s.mem (Buf.addr s₀ ⟨ga, go, 1024⟩))
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → Ctx Y s₀ s' → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame ([⟨fa, fo, 1024⟩].map (Buf.rgn s₀) ++ [below (E1 s₀) 28]) s.mem s'.mem →
      PolyIs s'.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩) (op (polyAt s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩)) (polyAt s.mem (Buf.addr s₀ ⟨ga, go, 1024⟩))) → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B (callWith [.ecx, .eax] nm c) := by
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨h0, h1⟩, d01⟩ := hc
  have h0' := (Lay.okW_iff.mp h0).1
  have h1' := h1
  refine call_piece hv hsp (by decide) (by decide)
    (by rw [hst]; simp only [List.length_cons, List.length_nil]; omega)
    (fun s₀ => [Buf.rgn s₀ ⟨ga, go, 1024⟩]) (fun s₀ => [Buf.rgn s₀ ⟨fa, fo, 1024⟩] ++ [below (E1 s₀) 8])
    (fun s₀ s hp ha => ?_) (fun s₀ s₀' s s' hp hp' hq ha ha' => ?_)
    (fun s₀ hp => wr_sub hp (bs := [⟨fa, fo, 1024⟩]) (by simp [h0]) (by omega))
    (fun s₀ s s' hp ha h' e₃ fr post => ?_)
  · obtain ⟨h, hax, hcx, x0, x1⟩ := hA s₀ s hp ha
    have hE' : 28 ≤ (E1 s₀).toNat := by rw [← h.esp]; exact ctx_E hp h (N := 28) (by omega)
    have fit : 4 * [Reg.ecx, Reg.eax].length + 4 ≤ (s.gpr .esp).toNat := by
      rw [h.esp]; simp only [List.length_cons, List.length_nil]; omega
    have a0 : arg (pushed [.ecx, .eax] s).callEntry 0 = Buf.ptr s₀ ⟨fa, fo, 1024⟩ := by
      rw [callEntry_arg fit (by decide) (by decide)]; exact hax
    have a1 : arg (pushed [.ecx, .eax] s).callEntry 1 = Buf.ptr s₀ ⟨ga, go, 1024⟩ := by
      rw [callEntry_arg fit (by decide) (by decide)]; exact hcx
    have eA : argAddr (pushed [.ecx, .eax] s).callEntry 0 = (E1 s₀ - BitVec.ofNat 32 8).setWidth 64 := by
      rw [callEntry_argAddr0, h.esp]; rfl
    have eSp : (pushed [.ecx, .eax] s).callEntry.gpr .esp = E1 s₀ - BitVec.ofNat 32 12 := by
      rw [callEntry_esp', h.esp]; rfl
    have b0 := Buf.stkD hp h0' (N := 4 * 2 + 4 + 16) (by omega)
    have b1 := Buf.stkD hp h1' (N := 4 * 2 + 4 + 16) (by omega)
    obtain ⟨r0₁, r0₂, r0₃⟩ := entry_regions hE' b0
    obtain ⟨r1₁, r1₂, r1₃⟩ := entry_regions hE' b1
    obtain ⟨rA₂, rA₃⟩ := entry_self (E := E1 s₀) (k := 2) (K := 16) hE'
    have cv := covers_of (s := s) (n := 2) (rd := [Buf.rgn s₀ ⟨ga, go, 1024⟩])
      (wr := [Buf.rgn s₀ ⟨fa, fo, 1024⟩] ++ [below (E1 s₀) 8])
      (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl
        exact Buf.within hp h1' h.rd h.wr) fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact .inr (Buf.withinW hp h0' (Lay.okW_iff.mp h0).2 h.wr)
      · exact .inl (by rw [h.esp])
    refine ⟨h, ?_, cv.1, cv.2⟩
    -- The callee's entry state stays opaque to `sig_pre`, which would unfold it.
    generalize he : (pushed [.ecx, .eax] s).callEntry = e
    sig_pre [accSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    subst he
    simp only [arg_withRegions, argAddr_withRegions, a0, a1, eA, eSp]
    have ek := @ent_keep Y s₀ s hp h [.ecx, .eax] (by decide) (by simp; omega)
    refine ⟨by rw [sub_toNat (by omega)]; omega, by rw [sub_toNat (by omega)]; have := (E1 s₀).isLt; omega,
      trivial, trivial, Buf.disj hp h0' h1' d01, r0₁, r1₁, r0₂, r1₂, rA₂, r0₃, r1₃, rA₃,
      Buf.fit hp h0', Buf.fit hp h1', reduced_congr (ek h0') x0, reduced_congr (ek h1') x1⟩
  · obtain ⟨h, hax, hcx, -⟩ := hA s₀ s hp ha
    obtain ⟨h', hax', hcx', -⟩ := hA s₀' s' hp' ha'
    have hsp : s.gpr .esp = s'.gpr .esp := by rw [h.esp, h'.esp, hq.E1]
    have hr : ∀ r ∈ [Reg.ecx, Reg.eax], s.gpr r = s'.gpr r := by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [hcx, hcx', hq.ptr h1']
      · rw [hax, hax', hq.ptr h0']
    have fit : 4 * [Reg.ecx, Reg.eax].length + 4 ≤ (s.gpr .esp).toNat := by
      have := ctx_E hp h (N := 28) (by omega); simp only [List.length_cons, List.length_nil]; omega
    refine ⟨by simp only [Buf.rgn, hq.ptr h1'], by simp only [Buf.rgn, hq.ptr h0', hq.E1], ?_⟩
    generalize he : (pushed [.ecx, .eax] s).callEntry = e
    generalize he' : (pushed [.ecx, .eax] s').callEntry = e'
    sig_pub [accSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    subst he he'
    simp only [arg_withRegions, callEntry_esp', hsp]
    exact ⟨trivial, callEntry_arg_eq (by decide) fit hsp hr (by decide),
      callEntry_arg_eq (by decide) fit hsp hr (by decide)⟩
  · obtain ⟨h, hax, hcx, -⟩ := hA s₀ s hp ha
    obtain ⟨s₂, m₂, post⟩ := post
    have fit : 4 * [Reg.ecx, Reg.eax].length + 4 ≤ (s.gpr .esp).toNat := by
      have := ctx_E hp h (N := 28) (by omega); simp only [List.length_cons, List.length_nil]; omega
    have a0 : arg (pushed [.ecx, .eax] s).callEntry 0 = Buf.ptr s₀ ⟨fa, fo, 1024⟩ := by
      rw [callEntry_arg fit (by decide) (by decide)]; exact hax
    have a1 : arg (pushed [.ecx, .eax] s).callEntry 1 = Buf.ptr s₀ ⟨ga, go, 1024⟩ := by
      rw [callEntry_arg fit (by decide) (by decide)]; exact hcx
    have ek := @ent_keep Y s₀ s hp h [.ecx, .eax] (by decide) (by simp; omega)
    generalize he : (pushed [.ecx, .eax] s).callEntry = e at post
    sig_post [accSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at post
    subst he
    simp only [arg_withRegions, a0, a1, m₂] at post
    rw [polyAt_congr (ek h0'), polyAt_congr (ek h1')] at post
    exact hQ s₀ s s' hp ha h' e₃ (fr_conv hp (a := 8) (N := 28) (by omega) (by omega)
      (by rw [hst] at fr; exact fr)) post


/-- `f ← SamplePolyCBD₂(b)`, with the 128 bytes `b` at `(ba, bo)` and `f` at `(fa, fo)`. -/
theorem cbd2_call (ba bo fa fo : Nat)
    (hc : (Y.ok ⟨ba, bo, 128⟩ && Y.okW ⟨fa, fo, 1024⟩ && Y.sep ⟨ba, bo, 128⟩ ⟨fa, fo, 1024⟩) = true) (hN : 44 ≤ Y.stk)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s ∧ s.gpr .eax = Buf.ptr s₀ ⟨ba, bo, 128⟩ ∧
      s.gpr .ecx = Buf.ptr s₀ ⟨fa, fo, 1024⟩)
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → Ctx Y s₀ s' → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame ([⟨fa, fo, 1024⟩].map (Buf.rgn s₀) ++ [below (E1 s₀) 28]) s.mem s'.mem →
      PolyIs s'.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩) (samplePolyCBD 2 (Spec.Sha3.bytesAt s.mem (Buf.addr s₀ ⟨ba, bo, 128⟩) 128)) → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B (callWith [.ecx, .eax] "vg_mlkem_cbd2" Impl.MlKem.X86.cbd2) := by
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨h0, h1⟩, d01⟩ := hc
  have h0' := h0
  have h1' := (Lay.okW_iff.mp h1).1
  refine call_piece Cbd.verified cbd2_nosp (by decide) (by decide)
    (by rw [cbd2_stack]; simp only [List.length_cons, List.length_nil]; omega)
    (fun s₀ => [Buf.rgn s₀ ⟨ba, bo, 128⟩]) (fun s₀ => [Buf.rgn s₀ ⟨fa, fo, 1024⟩] ++ [below (E1 s₀) 8])
    (fun s₀ s hp ha => ?_) (fun s₀ s₀' s s' hp hp' hq ha ha' => ?_)
    (fun s₀ hp => wr_sub hp (bs := [⟨fa, fo, 1024⟩]) (by simp [h1]) (by omega))
    (fun s₀ s s' hp ha h' e₃ fr post => ?_)
  · obtain ⟨h, hax, hcx⟩ := hA s₀ s hp ha
    have hE' : 28 ≤ (E1 s₀).toNat := by rw [← h.esp]; exact ctx_E hp h (N := 28) (by omega)
    have fit : 4 * [Reg.ecx, Reg.eax].length + 4 ≤ (s.gpr .esp).toNat := by
      rw [h.esp]; simp only [List.length_cons, List.length_nil]; omega
    have a0 : arg (pushed [.ecx, .eax] s).callEntry 0 = Buf.ptr s₀ ⟨ba, bo, 128⟩ := by
      rw [callEntry_arg fit (by decide) (by decide)]; exact hax
    have a1 : arg (pushed [.ecx, .eax] s).callEntry 1 = Buf.ptr s₀ ⟨fa, fo, 1024⟩ := by
      rw [callEntry_arg fit (by decide) (by decide)]; exact hcx
    have eA : argAddr (pushed [.ecx, .eax] s).callEntry 0 = (E1 s₀ - BitVec.ofNat 32 8).setWidth 64 := by
      rw [callEntry_argAddr0, h.esp]; rfl
    have eSp : (pushed [.ecx, .eax] s).callEntry.gpr .esp = E1 s₀ - BitVec.ofNat 32 12 := by
      rw [callEntry_esp', h.esp]; rfl
    have b0 := Buf.stkD hp h0' (N := 4 * 2 + 4 + 16) (by omega)
    have b1 := Buf.stkD hp h1' (N := 4 * 2 + 4 + 16) (by omega)
    obtain ⟨r0₁, r0₂, r0₃⟩ := entry_regions hE' b0
    obtain ⟨r1₁, r1₂, r1₃⟩ := entry_regions hE' b1
    obtain ⟨rA₂, rA₃⟩ := entry_self (E := E1 s₀) (k := 2) (K := 16) hE'
    have cv := covers_of (s := s) (n := 2) (rd := [Buf.rgn s₀ ⟨ba, bo, 128⟩])
      (wr := [Buf.rgn s₀ ⟨fa, fo, 1024⟩] ++ [below (E1 s₀) 8])
      (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl
        exact Buf.within hp h0' h.rd h.wr) fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact .inr (Buf.withinW hp h1' (Lay.okW_iff.mp h1).2 h.wr)
      · exact .inl (by rw [h.esp])
    refine ⟨h, ?_, cv.1, cv.2⟩
    -- The callee's entry state stays opaque to `sig_pre`, which would unfold it.
    generalize he : (pushed [.ecx, .eax] s).callEntry = e
    sig_pre [cbd2Contract, cbd2Sig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    subst he
    simp only [arg_withRegions, argAddr_withRegions, a0, a1, eA, eSp]
    have ek := @ent_keep Y s₀ s hp h [.ecx, .eax] (by decide) (by simp; omega)
    refine ⟨by rw [sub_toNat (by omega)]; omega, by rw [sub_toNat (by omega)]; have := (E1 s₀).isLt; omega,
      trivial, trivial, Buf.disj hp h0' h1' d01, r0₁, r1₁, r0₂, r1₂, rA₂, r0₃, r1₃, rA₃,
      Buf.fit hp h0', Buf.fit hp h1'⟩
  · obtain ⟨h, hax, hcx⟩ := hA s₀ s hp ha
    obtain ⟨h', hax', hcx'⟩ := hA s₀' s' hp' ha'
    have hsp : s.gpr .esp = s'.gpr .esp := by rw [h.esp, h'.esp, hq.E1]
    have hr : ∀ r ∈ [Reg.ecx, Reg.eax], s.gpr r = s'.gpr r := by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [hcx, hcx', hq.ptr h1']
      · rw [hax, hax', hq.ptr h0']
    have fit : 4 * [Reg.ecx, Reg.eax].length + 4 ≤ (s.gpr .esp).toNat := by
      have := ctx_E hp h (N := 28) (by omega); simp only [List.length_cons, List.length_nil]; omega
    refine ⟨by simp only [Buf.rgn, hq.ptr h0'], by simp only [Buf.rgn, hq.ptr h1', hq.E1], ?_⟩
    generalize he : (pushed [.ecx, .eax] s).callEntry = e
    generalize he' : (pushed [.ecx, .eax] s').callEntry = e'
    sig_pub [cbd2Contract, cbd2Sig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    subst he he'
    simp only [arg_withRegions, callEntry_esp', hsp]
    exact ⟨trivial, callEntry_arg_eq (by decide) fit hsp hr (by decide),
      callEntry_arg_eq (by decide) fit hsp hr (by decide)⟩
  · obtain ⟨h, hax, hcx⟩ := hA s₀ s hp ha
    obtain ⟨s₂, m₂, post⟩ := post
    have fit : 4 * [Reg.ecx, Reg.eax].length + 4 ≤ (s.gpr .esp).toNat := by
      have := ctx_E hp h (N := 28) (by omega); simp only [List.length_cons, List.length_nil]; omega
    have a0 : arg (pushed [.ecx, .eax] s).callEntry 0 = Buf.ptr s₀ ⟨ba, bo, 128⟩ := by
      rw [callEntry_arg fit (by decide) (by decide)]; exact hax
    have a1 : arg (pushed [.ecx, .eax] s).callEntry 1 = Buf.ptr s₀ ⟨fa, fo, 1024⟩ := by
      rw [callEntry_arg fit (by decide) (by decide)]; exact hcx
    have ek := @ent_keep Y s₀ s hp h [.ecx, .eax] (by decide) (by simp; omega)
    generalize he : (pushed [.ecx, .eax] s).callEntry = e at post
    sig_post [cbd2Contract, cbd2Sig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at post
    subst he
    simp only [arg_withRegions, a0, a1, m₂] at post
    rw [bytesAt_congr (ek h0')] at post
    exact hQ s₀ s s' hp ha h' e₃ (fr_conv hp (a := 8) (N := 28) (by omega) (by omega)
      (by rw [cbd2_stack] at fr; exact fr)) post


/-- `out ← ByteEncode₁₂(f)`, with `f` at `(fa, fo)` and the 384 bytes `out` at `(oa, oo)`. -/
theorem encode12_call (fa fo oa oo : Nat)
    (hc : (Y.ok ⟨fa, fo, 1024⟩ && Y.okW ⟨oa, oo, 384⟩ && Y.sep ⟨fa, fo, 1024⟩ ⟨oa, oo, 384⟩) = true) (hN : 44 ≤ Y.stk)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s ∧ s.gpr .eax = Buf.ptr s₀ ⟨fa, fo, 1024⟩ ∧
      s.gpr .ecx = Buf.ptr s₀ ⟨oa, oo, 384⟩ ∧ Reduced s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩))
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → Ctx Y s₀ s' → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame ([⟨oa, oo, 384⟩].map (Buf.rgn s₀) ++ [below (E1 s₀) 28]) s.mem s'.mem →
      Spec.Sha3.bytesAt s'.mem (Buf.addr s₀ ⟨oa, oo, 384⟩) 384 = encode12 (polyAt s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩)) → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B (callWith [.ecx, .eax] "vg_mlkem_encode12" Impl.MlKem.X86.encode12) := by
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨h0, h1⟩, d01⟩ := hc
  have h0' := h0
  have h1' := (Lay.okW_iff.mp h1).1
  refine call_piece Encode12.verified encode12_nosp (by decide) (by decide)
    (by rw [encode12_stack]; simp only [List.length_cons, List.length_nil]; omega)
    (fun s₀ => [Buf.rgn s₀ ⟨fa, fo, 1024⟩]) (fun s₀ => [Buf.rgn s₀ ⟨oa, oo, 384⟩] ++ [below (E1 s₀) 8])
    (fun s₀ s hp ha => ?_) (fun s₀ s₀' s s' hp hp' hq ha ha' => ?_)
    (fun s₀ hp => wr_sub hp (bs := [⟨oa, oo, 384⟩]) (by simp [h1]) (by omega))
    (fun s₀ s s' hp ha h' e₃ fr post => ?_)
  · obtain ⟨h, hax, hcx, x0⟩ := hA s₀ s hp ha
    have hE' : 28 ≤ (E1 s₀).toNat := by rw [← h.esp]; exact ctx_E hp h (N := 28) (by omega)
    have fit : 4 * [Reg.ecx, Reg.eax].length + 4 ≤ (s.gpr .esp).toNat := by
      rw [h.esp]; simp only [List.length_cons, List.length_nil]; omega
    have a0 : arg (pushed [.ecx, .eax] s).callEntry 0 = Buf.ptr s₀ ⟨fa, fo, 1024⟩ := by
      rw [callEntry_arg fit (by decide) (by decide)]; exact hax
    have a1 : arg (pushed [.ecx, .eax] s).callEntry 1 = Buf.ptr s₀ ⟨oa, oo, 384⟩ := by
      rw [callEntry_arg fit (by decide) (by decide)]; exact hcx
    have eA : argAddr (pushed [.ecx, .eax] s).callEntry 0 = (E1 s₀ - BitVec.ofNat 32 8).setWidth 64 := by
      rw [callEntry_argAddr0, h.esp]; rfl
    have eSp : (pushed [.ecx, .eax] s).callEntry.gpr .esp = E1 s₀ - BitVec.ofNat 32 12 := by
      rw [callEntry_esp', h.esp]; rfl
    have b0 := Buf.stkD hp h0' (N := 4 * 2 + 4 + 16) (by omega)
    have b1 := Buf.stkD hp h1' (N := 4 * 2 + 4 + 16) (by omega)
    obtain ⟨r0₁, r0₂, r0₃⟩ := entry_regions hE' b0
    obtain ⟨r1₁, r1₂, r1₃⟩ := entry_regions hE' b1
    obtain ⟨rA₂, rA₃⟩ := entry_self (E := E1 s₀) (k := 2) (K := 16) hE'
    have cv := covers_of (s := s) (n := 2) (rd := [Buf.rgn s₀ ⟨fa, fo, 1024⟩])
      (wr := [Buf.rgn s₀ ⟨oa, oo, 384⟩] ++ [below (E1 s₀) 8])
      (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl
        exact Buf.within hp h0' h.rd h.wr) fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact .inr (Buf.withinW hp h1' (Lay.okW_iff.mp h1).2 h.wr)
      · exact .inl (by rw [h.esp])
    refine ⟨h, ?_, cv.1, cv.2⟩
    -- The callee's entry state stays opaque to `sig_pre`, which would unfold it.
    generalize he : (pushed [.ecx, .eax] s).callEntry = e
    sig_pre [encode12Contract, encode12Sig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    subst he
    simp only [arg_withRegions, argAddr_withRegions, a0, a1, eA, eSp]
    have ek := @ent_keep Y s₀ s hp h [.ecx, .eax] (by decide) (by simp; omega)
    refine ⟨by rw [sub_toNat (by omega)]; omega, by rw [sub_toNat (by omega)]; have := (E1 s₀).isLt; omega,
      trivial, trivial, Buf.disj hp h0' h1' d01, r0₁, r1₁, r0₂, r1₂, rA₂, r0₃, r1₃, rA₃,
      Buf.fit hp h0', Buf.fit hp h1', reduced_congr (ek h0') x0⟩
  · obtain ⟨h, hax, hcx, -⟩ := hA s₀ s hp ha
    obtain ⟨h', hax', hcx', -⟩ := hA s₀' s' hp' ha'
    have hsp : s.gpr .esp = s'.gpr .esp := by rw [h.esp, h'.esp, hq.E1]
    have hr : ∀ r ∈ [Reg.ecx, Reg.eax], s.gpr r = s'.gpr r := by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [hcx, hcx', hq.ptr h1']
      · rw [hax, hax', hq.ptr h0']
    have fit : 4 * [Reg.ecx, Reg.eax].length + 4 ≤ (s.gpr .esp).toNat := by
      have := ctx_E hp h (N := 28) (by omega); simp only [List.length_cons, List.length_nil]; omega
    refine ⟨by simp only [Buf.rgn, hq.ptr h0'], by simp only [Buf.rgn, hq.ptr h1', hq.E1], ?_⟩
    generalize he : (pushed [.ecx, .eax] s).callEntry = e
    generalize he' : (pushed [.ecx, .eax] s').callEntry = e'
    sig_pub [encode12Contract, encode12Sig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    subst he he'
    simp only [arg_withRegions, callEntry_esp', hsp]
    exact ⟨trivial, callEntry_arg_eq (by decide) fit hsp hr (by decide),
      callEntry_arg_eq (by decide) fit hsp hr (by decide)⟩
  · obtain ⟨h, hax, hcx, -⟩ := hA s₀ s hp ha
    obtain ⟨s₂, m₂, post⟩ := post
    have fit : 4 * [Reg.ecx, Reg.eax].length + 4 ≤ (s.gpr .esp).toNat := by
      have := ctx_E hp h (N := 28) (by omega); simp only [List.length_cons, List.length_nil]; omega
    have a0 : arg (pushed [.ecx, .eax] s).callEntry 0 = Buf.ptr s₀ ⟨fa, fo, 1024⟩ := by
      rw [callEntry_arg fit (by decide) (by decide)]; exact hax
    have a1 : arg (pushed [.ecx, .eax] s).callEntry 1 = Buf.ptr s₀ ⟨oa, oo, 384⟩ := by
      rw [callEntry_arg fit (by decide) (by decide)]; exact hcx
    have ek := @ent_keep Y s₀ s hp h [.ecx, .eax] (by decide) (by simp; omega)
    generalize he : (pushed [.ecx, .eax] s).callEntry = e at post
    sig_post [encode12Contract, encode12Sig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at post
    subst he
    simp only [arg_withRegions, a0, a1, m₂] at post
    rw [polyAt_congr (ek h0')] at post
    exact hQ s₀ s s' hp ha h' e₃ (fr_conv hp (a := 8) (N := 28) (by omega) (by omega)
      (by rw [encode12_stack] at fr; exact fr)) post


/-- `f ← ByteDecode₁₂(b)`, with the 384 bytes `b` at `(ba, bo)` and `f` at `(fa, fo)`. -/
theorem decode12_call (ba bo fa fo : Nat)
    (hc : (Y.ok ⟨ba, bo, 384⟩ && Y.okW ⟨fa, fo, 1024⟩ && Y.sep ⟨ba, bo, 384⟩ ⟨fa, fo, 1024⟩) = true) (hN : 44 ≤ Y.stk)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s ∧ s.gpr .eax = Buf.ptr s₀ ⟨ba, bo, 384⟩ ∧
      s.gpr .ecx = Buf.ptr s₀ ⟨fa, fo, 1024⟩)
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → Ctx Y s₀ s' → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame ([⟨fa, fo, 1024⟩].map (Buf.rgn s₀) ++ [below (E1 s₀) 28]) s.mem s'.mem →
      PolyIs s'.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩) (decode12 (Spec.Sha3.bytesAt s.mem (Buf.addr s₀ ⟨ba, bo, 384⟩) 384)) → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B (callWith [.ecx, .eax] "vg_mlkem_decode12" Impl.MlKem.X86.decode12) := by
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨h0, h1⟩, d01⟩ := hc
  have h0' := h0
  have h1' := (Lay.okW_iff.mp h1).1
  refine call_piece Decode12.verified decode12_nosp (by decide) (by decide)
    (by rw [decode12_stack]; simp only [List.length_cons, List.length_nil]; omega)
    (fun s₀ => [Buf.rgn s₀ ⟨ba, bo, 384⟩]) (fun s₀ => [Buf.rgn s₀ ⟨fa, fo, 1024⟩] ++ [below (E1 s₀) 8])
    (fun s₀ s hp ha => ?_) (fun s₀ s₀' s s' hp hp' hq ha ha' => ?_)
    (fun s₀ hp => wr_sub hp (bs := [⟨fa, fo, 1024⟩]) (by simp [h1]) (by omega))
    (fun s₀ s s' hp ha h' e₃ fr post => ?_)
  · obtain ⟨h, hax, hcx⟩ := hA s₀ s hp ha
    have hE' : 28 ≤ (E1 s₀).toNat := by rw [← h.esp]; exact ctx_E hp h (N := 28) (by omega)
    have fit : 4 * [Reg.ecx, Reg.eax].length + 4 ≤ (s.gpr .esp).toNat := by
      rw [h.esp]; simp only [List.length_cons, List.length_nil]; omega
    have a0 : arg (pushed [.ecx, .eax] s).callEntry 0 = Buf.ptr s₀ ⟨ba, bo, 384⟩ := by
      rw [callEntry_arg fit (by decide) (by decide)]; exact hax
    have a1 : arg (pushed [.ecx, .eax] s).callEntry 1 = Buf.ptr s₀ ⟨fa, fo, 1024⟩ := by
      rw [callEntry_arg fit (by decide) (by decide)]; exact hcx
    have eA : argAddr (pushed [.ecx, .eax] s).callEntry 0 = (E1 s₀ - BitVec.ofNat 32 8).setWidth 64 := by
      rw [callEntry_argAddr0, h.esp]; rfl
    have eSp : (pushed [.ecx, .eax] s).callEntry.gpr .esp = E1 s₀ - BitVec.ofNat 32 12 := by
      rw [callEntry_esp', h.esp]; rfl
    have b0 := Buf.stkD hp h0' (N := 4 * 2 + 4 + 16) (by omega)
    have b1 := Buf.stkD hp h1' (N := 4 * 2 + 4 + 16) (by omega)
    obtain ⟨r0₁, r0₂, r0₃⟩ := entry_regions hE' b0
    obtain ⟨r1₁, r1₂, r1₃⟩ := entry_regions hE' b1
    obtain ⟨rA₂, rA₃⟩ := entry_self (E := E1 s₀) (k := 2) (K := 16) hE'
    have cv := covers_of (s := s) (n := 2) (rd := [Buf.rgn s₀ ⟨ba, bo, 384⟩])
      (wr := [Buf.rgn s₀ ⟨fa, fo, 1024⟩] ++ [below (E1 s₀) 8])
      (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl
        exact Buf.within hp h0' h.rd h.wr) fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact .inr (Buf.withinW hp h1' (Lay.okW_iff.mp h1).2 h.wr)
      · exact .inl (by rw [h.esp])
    refine ⟨h, ?_, cv.1, cv.2⟩
    -- The callee's entry state stays opaque to `sig_pre`, which would unfold it.
    generalize he : (pushed [.ecx, .eax] s).callEntry = e
    sig_pre [decode12Contract, decode12Sig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    subst he
    simp only [arg_withRegions, argAddr_withRegions, a0, a1, eA, eSp]
    have ek := @ent_keep Y s₀ s hp h [.ecx, .eax] (by decide) (by simp; omega)
    refine ⟨by rw [sub_toNat (by omega)]; omega, by rw [sub_toNat (by omega)]; have := (E1 s₀).isLt; omega,
      trivial, trivial, Buf.disj hp h0' h1' d01, r0₁, r1₁, r0₂, r1₂, rA₂, r0₃, r1₃, rA₃,
      Buf.fit hp h0', Buf.fit hp h1'⟩
  · obtain ⟨h, hax, hcx⟩ := hA s₀ s hp ha
    obtain ⟨h', hax', hcx'⟩ := hA s₀' s' hp' ha'
    have hsp : s.gpr .esp = s'.gpr .esp := by rw [h.esp, h'.esp, hq.E1]
    have hr : ∀ r ∈ [Reg.ecx, Reg.eax], s.gpr r = s'.gpr r := by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [hcx, hcx', hq.ptr h1']
      · rw [hax, hax', hq.ptr h0']
    have fit : 4 * [Reg.ecx, Reg.eax].length + 4 ≤ (s.gpr .esp).toNat := by
      have := ctx_E hp h (N := 28) (by omega); simp only [List.length_cons, List.length_nil]; omega
    refine ⟨by simp only [Buf.rgn, hq.ptr h0'], by simp only [Buf.rgn, hq.ptr h1', hq.E1], ?_⟩
    generalize he : (pushed [.ecx, .eax] s).callEntry = e
    generalize he' : (pushed [.ecx, .eax] s').callEntry = e'
    sig_pub [decode12Contract, decode12Sig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    subst he he'
    simp only [arg_withRegions, callEntry_esp', hsp]
    exact ⟨trivial, callEntry_arg_eq (by decide) fit hsp hr (by decide),
      callEntry_arg_eq (by decide) fit hsp hr (by decide)⟩
  · obtain ⟨h, hax, hcx⟩ := hA s₀ s hp ha
    obtain ⟨s₂, m₂, post⟩ := post
    have fit : 4 * [Reg.ecx, Reg.eax].length + 4 ≤ (s.gpr .esp).toNat := by
      have := ctx_E hp h (N := 28) (by omega); simp only [List.length_cons, List.length_nil]; omega
    have a0 : arg (pushed [.ecx, .eax] s).callEntry 0 = Buf.ptr s₀ ⟨ba, bo, 384⟩ := by
      rw [callEntry_arg fit (by decide) (by decide)]; exact hax
    have a1 : arg (pushed [.ecx, .eax] s).callEntry 1 = Buf.ptr s₀ ⟨fa, fo, 1024⟩ := by
      rw [callEntry_arg fit (by decide) (by decide)]; exact hcx
    have ek := @ent_keep Y s₀ s hp h [.ecx, .eax] (by decide) (by simp; omega)
    generalize he : (pushed [.ecx, .eax] s).callEntry = e at post
    sig_post [decode12Contract, decode12Sig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at post
    subst he
    simp only [arg_withRegions, a0, a1, m₂] at post
    rw [bytesAt_congr (ek h0')] at post
    exact hQ s₀ s s' hp ha h' e₃ (fr_conv hp (a := 8) (N := 28) (by omega) (by omega)
      (by rw [decode12_stack] at fr; exact fr)) post


end VG.Proof.MlKem.X86.Top
