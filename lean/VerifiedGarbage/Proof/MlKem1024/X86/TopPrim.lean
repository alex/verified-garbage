import VerifiedGarbage.Proof.MlKem.X86.TopSeq2
import VerifiedGarbage.Proof.MlKem1024.X86.CompressEncode
import VerifiedGarbage.Proof.MlKem1024.X86.DecodeDecompress
import VerifiedGarbage.Impl.MlKem1024.X86.Top

/-!
# ML-KEM-1024 on x86 (32-bit): calls of `vg_mlkem1024_compress_encode` and `vg_mlkem1024_decode_decompress`

Untrusted: everything here is checked by Lean. As the calls of
`vg_mlkem_compress_encode` and `vg_mlkem_decode_decompress`
(`Proof/MlKem/X86/TopPrim3.lean` and `TopSeq2.lean`), for the functions of
ML-KEM-1024 (`ce1024_call`, `dd1024_call`), with their arguments
(`ceC1024_piece`, `ddC1024_piece`).
-/

namespace VG.Proof.MlKem.X86.Top

open VG VG.X86 VG.Impl.MlKem.X86 VG.Impl.MlKem1024.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Spec.MlKem
open VG.Proof.Sha3.X86 (reg32)

variable {Y : Lay} {lk : State → List Byte} {A B : State → State → Prop}

theorem ce1024_nosp : NoSp Impl.MlKem1024.X86.compressEncode := NoSp.of_all (by decide +kernel)
theorem ce1024_stack : stackUse Impl.MlKem1024.X86.compressEncode = 16 := by decide +kernel
theorem dd1024_nosp : NoSp Impl.MlKem1024.X86.decodeDecompress := NoSp.of_all (by decide +kernel)
theorem dd1024_stack : stackUse Impl.MlKem1024.X86.decodeDecompress = 16 := by decide +kernel

theorem width_lt1024 {d : Nat} (hd : d ∈ Spec.MlKem1024.compressWidths) : 32 * d < 2 ^ 32 := by
  rcases mem_compressWidths1024 hd with rfl | rfl <;> decide

/-- `out ← ByteEncode_d(Compress_d(f))` for `d` = 5 or 11, with `f` at `(fa, fo)` and the `32d` bytes `out` at `(oa, oo)`,
and `f`, `d`, `out`, `32d` in `eax`, `ecx`, `edx` and `edi`. -/
theorem ce1024_call (d : Nat) (hd : d ∈ Spec.MlKem1024.compressWidths) (fa fo oa oo : Nat)
    (hc : (Y.ok ⟨fa, fo, 1024⟩ && Y.okW ⟨oa, oo, 32 * d⟩ && Y.sep ⟨fa, fo, 1024⟩ ⟨oa, oo, 32 * d⟩) = true)
    (hN : 52 ≤ Y.stk)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s ∧ s.gpr .eax = Buf.ptr s₀ ⟨fa, fo, 1024⟩ ∧
      s.gpr .ecx = BitVec.ofNat 32 d ∧ s.gpr .edx = Buf.ptr s₀ ⟨oa, oo, 32 * d⟩ ∧
      s.gpr .edi = BitVec.ofNat 32 (32 * d) ∧ Reduced s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩))
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → Ctx Y s₀ s' → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame ([⟨oa, oo, 32 * d⟩].map (Buf.rgn s₀) ++ [below (E1 s₀) 36]) s.mem s'.mem →
      Spec.Sha3.bytesAt s'.mem (Buf.addr s₀ ⟨oa, oo, 32 * d⟩) (32 * d) =
        compressEncode d (polyAt s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩)) → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B
      (callWith [.edi, .edx, .ecx, .eax] "vg_mlkem1024_compress_encode" Impl.MlKem1024.X86.compressEncode) := by
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨hF, hO⟩, dFO⟩ := hc
  have hO₁ := (Lay.okW_iff.mp hO).1
  have hd32 := width_lt1024 hd
  have hd' : d < 2 ^ 32 := by omega
  have entry : ∀ s₀ s, TPre Y s₀ → A s₀ s →
      4 * [Reg.edi, Reg.edx, Reg.ecx, Reg.eax].length + 4 ≤ (s.gpr .esp).toNat ∧
      arg (pushed [.edi, .edx, .ecx, .eax] s).callEntry 0 = Buf.ptr s₀ ⟨fa, fo, 1024⟩ ∧
      arg (pushed [.edi, .edx, .ecx, .eax] s).callEntry 1 = BitVec.ofNat 32 d ∧
      arg (pushed [.edi, .edx, .ecx, .eax] s).callEntry 2 = Buf.ptr s₀ ⟨oa, oo, 32 * d⟩ ∧
      arg (pushed [.edi, .edx, .ecx, .eax] s).callEntry 3 = BitVec.ofNat 32 (32 * d) := fun s₀ s hp ha => by
    obtain ⟨h, hax, hcx, hdx, hdi, -⟩ := hA s₀ s hp ha
    have fit : 4 * [Reg.edi, Reg.edx, Reg.ecx, Reg.eax].length + 4 ≤ (s.gpr .esp).toNat := by
      have := ctx_E hp h (N := 36) (by omega); simp only [List.length_cons, List.length_nil]; omega
    refine ⟨fit, ?_, ?_, ?_, ?_⟩
    · rw [callEntry_arg fit (by decide) (by decide)]; exact hax
    · rw [callEntry_arg fit (by decide) (by decide)]; exact hcx
    · rw [callEntry_arg fit (by decide) (by decide)]; exact hdx
    · rw [callEntry_arg fit (by decide) (by decide)]; exact hdi
  refine call_piece MlKem1024.X86.CompressEncode.verified ce1024_nosp (by decide) (by decide)
    (by rw [ce1024_stack]; simp only [List.length_cons, List.length_nil]; omega)
    (fun s₀ => [Buf.rgn s₀ ⟨fa, fo, 1024⟩])
    (fun s₀ => [Buf.rgn s₀ ⟨oa, oo, 32 * d⟩] ++ [below (E1 s₀) 16])
    (fun s₀ s hp ha => ?_) (fun s₀ s₀' s s' hp hp' hq ha ha' => ?_)
    (fun s₀ hp => wr_sub hp (bs := [⟨oa, oo, 32 * d⟩]) (by simp [hO]) (by omega))
    (fun s₀ s s' hp ha h' e₃ fr post => ?_)
  · obtain ⟨h, -, -, -, -, rF⟩ := hA s₀ s hp ha
    obtain ⟨fit, a0, a1, a2, a3⟩ := entry s₀ s hp ha
    have hE' : 36 ≤ (E1 s₀).toNat := by rw [← h.esp]; exact ctx_E hp h (N := 36) (by omega)
    have eA : argAddr (pushed [.edi, .edx, .ecx, .eax] s).callEntry 0 = (E1 s₀ - BitVec.ofNat 32 16).setWidth 64 := by
      rw [callEntry_argAddr0, h.esp]; rfl
    have eSp : (pushed [.edi, .edx, .ecx, .eax] s).callEntry.gpr .esp = E1 s₀ - BitVec.ofNat 32 20 := by
      rw [callEntry_esp', h.esp]; rfl
    have bF := Buf.stkD hp hF (N := 4 * 4 + 4 + 16) (by omega)
    have bO := Buf.stkD hp hO₁ (N := 4 * 4 + 4 + 16) (by omega)
    obtain ⟨rF₁, rF₂, rF₃⟩ := entry_regions hE' bF
    obtain ⟨rO₁, rO₂, rO₃⟩ := entry_regions hE' bO
    obtain ⟨rG₂, rG₃⟩ := entry_self (E := E1 s₀) (k := 4) (K := 16) hE'
    have cv := covers_of (s := s) (n := 4) (rd := [Buf.rgn s₀ ⟨fa, fo, 1024⟩])
      (wr := [Buf.rgn s₀ ⟨oa, oo, 32 * d⟩] ++ [below (E1 s₀) 16])
      (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl
        exact Buf.within hp hF h.rd h.wr) fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact .inr (Buf.withinW hp hO₁ (Lay.okW_iff.mp hO).2 h.wr)
      · exact .inl (by rw [h.esp])
    refine ⟨h, ?_, cv.1, cv.2⟩
    -- The callee's entry state stays opaque to `sig_pre`, which would unfold it.
    generalize he : (pushed [.edi, .edx, .ecx, .eax] s).callEntry = e
    sig_pre [Spec.MlKem1024.compressEncodeContract, Spec.MlKem1024.compressEncodeSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    subst he
    simp only [arg_withRegions, argAddr_withRegions, a0, a1, a2, a3, eA, eSp, toNat_ofNat32 hd',
      toNat_ofNat32 hd32]
    have ek := @ent_keep Y s₀ s hp h [.edi, .edx, .ecx, .eax] (by decide) (by simp; omega)
    refine ⟨by rw [sub_toNat (by omega)]; omega, by rw [sub_toNat (by omega)]; have := (E1 s₀).isLt; omega,
      trivial, trivial, Buf.disj hp hF hO₁ dFO, rF₁, rO₁, rF₂, rO₂, rG₂, rF₃, rO₃, rG₃,
      Buf.fit hp hF, Buf.fit hp hO₁, hd, trivial, reduced_congr (ek hF) rF⟩
  · have h := (hA s₀ s hp ha).1
    have h' := (hA s₀' s' hp' ha').1
    obtain ⟨fit, -⟩ := entry s₀ s hp ha
    obtain ⟨-, hax, hcx, hdx, hdi, -⟩ := hA s₀ s hp ha
    obtain ⟨-, hax', hcx', hdx', hdi', -⟩ := hA s₀' s' hp' ha'
    have hsp : s.gpr .esp = s'.gpr .esp := by rw [h.esp, h'.esp, hq.E1]
    have hr : ∀ r ∈ [Reg.edi, Reg.edx, Reg.ecx, Reg.eax], s.gpr r = s'.gpr r := by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [hdi, hdi']
      · rw [hdx, hdx', hq.ptr hO₁]
      · rw [hcx, hcx']
      · rw [hax, hax', hq.ptr hF]
    refine ⟨by simp only [Buf.rgn, hq.ptr hF], by simp only [Buf.rgn, hq.ptr hO₁, hq.E1], ?_⟩
    generalize he : (pushed [.edi, .edx, .ecx, .eax] s).callEntry = e
    generalize he' : (pushed [.edi, .edx, .ecx, .eax] s').callEntry = e'
    sig_pub [Spec.MlKem1024.compressEncodeContract, Spec.MlKem1024.compressEncodeSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    subst he he'
    simp only [arg_withRegions, callEntry_esp', hsp]
    exact ⟨trivial, callEntry_arg_eq (by decide) fit hsp hr (by decide),
      callEntry_arg_eq (by decide) fit hsp hr (by decide), callEntry_arg_eq (by decide) fit hsp hr (by decide),
      callEntry_arg_eq (by decide) fit hsp hr (by decide)⟩
  · have h := (hA s₀ s hp ha).1
    obtain ⟨fit, a0, a1, a2, a3⟩ := entry s₀ s hp ha
    obtain ⟨s₂, m₂, post⟩ := post
    have ek := @ent_keep Y s₀ s hp h [.edi, .edx, .ecx, .eax] (by decide) (by simp; omega)
    generalize he : (pushed [.edi, .edx, .ecx, .eax] s).callEntry = e at post
    sig_post [Spec.MlKem1024.compressEncodeContract, Spec.MlKem1024.compressEncodeSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at post
    subst he
    simp only [arg_withRegions, a0, a1, a2, a3, m₂, toNat_ofNat32 hd', toNat_ofNat32 hd32] at post
    rw [polyAt_congr (ek hF)] at post
    exact hQ s₀ s s' hp ha h' e₃ (fr_conv hp (a := 16) (N := 36) (by omega) (by omega)
      (by rw [ce1024_stack] at fr; exact fr)) post

/-- `f ← Decompress_d(ByteDecode_d(b))` for `d` = 5 or 11, with the `32d` bytes `b` at `(ba, bo)` and `f` at `(fa, fo)`,
and `b`, `32d`, `d`, `f` in `eax`, `ecx`, `edx` and `edi`. -/
theorem dd1024_call (d : Nat) (hd : d ∈ Spec.MlKem1024.compressWidths) (ba bo fa fo : Nat)
    (hc : (Y.ok ⟨ba, bo, 32 * d⟩ && Y.okW ⟨fa, fo, 1024⟩ && Y.sep ⟨ba, bo, 32 * d⟩ ⟨fa, fo, 1024⟩) = true)
    (hN : 52 ≤ Y.stk)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s ∧ s.gpr .eax = Buf.ptr s₀ ⟨ba, bo, 32 * d⟩ ∧
      s.gpr .ecx = BitVec.ofNat 32 (32 * d) ∧ s.gpr .edx = BitVec.ofNat 32 d ∧
      s.gpr .edi = Buf.ptr s₀ ⟨fa, fo, 1024⟩)
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → Ctx Y s₀ s' → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame ([⟨fa, fo, 1024⟩].map (Buf.rgn s₀) ++ [below (E1 s₀) 36]) s.mem s'.mem →
      PolyIs s'.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩)
        (decodeDecompress d (Spec.Sha3.bytesAt s.mem (Buf.addr s₀ ⟨ba, bo, 32 * d⟩) (32 * d))) → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B
      (callWith [.edi, .edx, .ecx, .eax] "vg_mlkem1024_decode_decompress" Impl.MlKem1024.X86.decodeDecompress) := by
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨hB, hF⟩, dBF⟩ := hc
  have hF₁ := (Lay.okW_iff.mp hF).1
  have hd32 := width_lt1024 hd
  have hd' : d < 2 ^ 32 := by omega
  have entry : ∀ s₀ s, TPre Y s₀ → A s₀ s →
      4 * [Reg.edi, Reg.edx, Reg.ecx, Reg.eax].length + 4 ≤ (s.gpr .esp).toNat ∧
      arg (pushed [.edi, .edx, .ecx, .eax] s).callEntry 0 = Buf.ptr s₀ ⟨ba, bo, 32 * d⟩ ∧
      arg (pushed [.edi, .edx, .ecx, .eax] s).callEntry 1 = BitVec.ofNat 32 (32 * d) ∧
      arg (pushed [.edi, .edx, .ecx, .eax] s).callEntry 2 = BitVec.ofNat 32 d ∧
      arg (pushed [.edi, .edx, .ecx, .eax] s).callEntry 3 = Buf.ptr s₀ ⟨fa, fo, 1024⟩ := fun s₀ s hp ha => by
    obtain ⟨h, hax, hcx, hdx, hdi⟩ := hA s₀ s hp ha
    have fit : 4 * [Reg.edi, Reg.edx, Reg.ecx, Reg.eax].length + 4 ≤ (s.gpr .esp).toNat := by
      have := ctx_E hp h (N := 36) (by omega); simp only [List.length_cons, List.length_nil]; omega
    refine ⟨fit, ?_, ?_, ?_, ?_⟩
    · rw [callEntry_arg fit (by decide) (by decide)]; exact hax
    · rw [callEntry_arg fit (by decide) (by decide)]; exact hcx
    · rw [callEntry_arg fit (by decide) (by decide)]; exact hdx
    · rw [callEntry_arg fit (by decide) (by decide)]; exact hdi
  refine call_piece MlKem1024.X86.DecodeDecompress.verified dd1024_nosp (by decide) (by decide)
    (by rw [dd1024_stack]; simp only [List.length_cons, List.length_nil]; omega)
    (fun s₀ => [Buf.rgn s₀ ⟨ba, bo, 32 * d⟩])
    (fun s₀ => [Buf.rgn s₀ ⟨fa, fo, 1024⟩] ++ [below (E1 s₀) 16])
    (fun s₀ s hp ha => ?_) (fun s₀ s₀' s s' hp hp' hq ha ha' => ?_)
    (fun s₀ hp => wr_sub hp (bs := [⟨fa, fo, 1024⟩]) (by simp [hF]) (by omega))
    (fun s₀ s s' hp ha h' e₃ fr post => ?_)
  · have h := (hA s₀ s hp ha).1
    obtain ⟨fit, a0, a1, a2, a3⟩ := entry s₀ s hp ha
    have hE' : 36 ≤ (E1 s₀).toNat := by rw [← h.esp]; exact ctx_E hp h (N := 36) (by omega)
    have eA : argAddr (pushed [.edi, .edx, .ecx, .eax] s).callEntry 0 = (E1 s₀ - BitVec.ofNat 32 16).setWidth 64 := by
      rw [callEntry_argAddr0, h.esp]; rfl
    have eSp : (pushed [.edi, .edx, .ecx, .eax] s).callEntry.gpr .esp = E1 s₀ - BitVec.ofNat 32 20 := by
      rw [callEntry_esp', h.esp]; rfl
    have bB := Buf.stkD hp hB (N := 4 * 4 + 4 + 16) (by omega)
    have bF := Buf.stkD hp hF₁ (N := 4 * 4 + 4 + 16) (by omega)
    obtain ⟨rB₁, rB₂, rB₃⟩ := entry_regions hE' bB
    obtain ⟨rF₁, rF₂, rF₃⟩ := entry_regions hE' bF
    obtain ⟨rG₂, rG₃⟩ := entry_self (E := E1 s₀) (k := 4) (K := 16) hE'
    have cv := covers_of (s := s) (n := 4) (rd := [Buf.rgn s₀ ⟨ba, bo, 32 * d⟩])
      (wr := [Buf.rgn s₀ ⟨fa, fo, 1024⟩] ++ [below (E1 s₀) 16])
      (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl
        exact Buf.within hp hB h.rd h.wr) fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact .inr (Buf.withinW hp hF₁ (Lay.okW_iff.mp hF).2 h.wr)
      · exact .inl (by rw [h.esp])
    refine ⟨h, ?_, cv.1, cv.2⟩
    -- The callee's entry state stays opaque to `sig_pre`, which would unfold it.
    generalize he : (pushed [.edi, .edx, .ecx, .eax] s).callEntry = e
    sig_pre [Spec.MlKem1024.decodeDecompressContract, Spec.MlKem1024.decodeDecompressSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    subst he
    simp only [arg_withRegions, argAddr_withRegions, a0, a1, a2, a3, eA, eSp, toNat_ofNat32 hd',
      toNat_ofNat32 hd32]
    refine ⟨by rw [sub_toNat (by omega)]; omega, by rw [sub_toNat (by omega)]; have := (E1 s₀).isLt; omega,
      trivial, trivial, Buf.disj hp hB hF₁ dBF, rB₁, rF₁, rB₂, rF₂, rG₂, rB₃, rF₃, rG₃,
      Buf.fit hp hB, Buf.fit hp hF₁, hd, trivial⟩
  · have h := (hA s₀ s hp ha).1
    have h' := (hA s₀' s' hp' ha').1
    obtain ⟨fit, -⟩ := entry s₀ s hp ha
    obtain ⟨-, hax, hcx, hdx, hdi⟩ := hA s₀ s hp ha
    obtain ⟨-, hax', hcx', hdx', hdi'⟩ := hA s₀' s' hp' ha'
    have hsp : s.gpr .esp = s'.gpr .esp := by rw [h.esp, h'.esp, hq.E1]
    have hr : ∀ r ∈ [Reg.edi, Reg.edx, Reg.ecx, Reg.eax], s.gpr r = s'.gpr r := by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [hdi, hdi', hq.ptr hF₁]
      · rw [hdx, hdx']
      · rw [hcx, hcx']
      · rw [hax, hax', hq.ptr hB]
    refine ⟨by simp only [Buf.rgn, hq.ptr hB], by simp only [Buf.rgn, hq.ptr hF₁, hq.E1], ?_⟩
    generalize he : (pushed [.edi, .edx, .ecx, .eax] s).callEntry = e
    generalize he' : (pushed [.edi, .edx, .ecx, .eax] s').callEntry = e'
    sig_pub [Spec.MlKem1024.decodeDecompressContract, Spec.MlKem1024.decodeDecompressSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    subst he he'
    simp only [arg_withRegions, callEntry_esp', hsp]
    exact ⟨trivial, callEntry_arg_eq (by decide) fit hsp hr (by decide),
      callEntry_arg_eq (by decide) fit hsp hr (by decide), callEntry_arg_eq (by decide) fit hsp hr (by decide),
      callEntry_arg_eq (by decide) fit hsp hr (by decide)⟩
  · have h := (hA s₀ s hp ha).1
    obtain ⟨fit, a0, a1, a2, a3⟩ := entry s₀ s hp ha
    obtain ⟨s₂, m₂, post⟩ := post
    have ek := @ent_keep Y s₀ s hp h [.edi, .edx, .ecx, .eax] (by decide) (by simp; omega)
    generalize he : (pushed [.edi, .edx, .ecx, .eax] s).callEntry = e at post
    sig_post [Spec.MlKem1024.decodeDecompressContract, Spec.MlKem1024.decodeDecompressSig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes] at post
    subst he
    simp only [arg_withRegions, a0, a1, a2, a3, m₂, toNat_ofNat32 hd', toNat_ofNat32 hd32] at post
    rw [bytesAt_congr (ek hB)] at post
    exact hQ s₀ s s' hp ha h' e₃ (fr_conv hp (a := 16) (N := 36) (by omega) (by omega)
      (by rw [dd1024_stack] at fr; exact fr)) post

theorem ceC1024_piece (d : Nat) (hd : d ∈ Spec.MlKem1024.compressWidths) (fa fo oa oo : Nat)
    (hc : (Y.ok ⟨fa, fo, 1024⟩ && Y.okW ⟨oa, oo, 32 * d⟩ && Y.sep ⟨fa, fo, 1024⟩ ⟨oa, oo, 32 * d⟩) = true)
    (hN : 52 ≤ Y.stk) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi]) (.block (ptrTo Y.sc .eax ⟨fa, fo, 1024⟩ ++
      ([.mov .ecx (.imm (BitVec.ofNat 32 d))] : List Instr) ++ ptrTo Y.sc .edx ⟨oa, oo, 32 * d⟩ ++
      ([.mov .edi (.imm (BitVec.ofNat 32 (32 * d)))] : List Instr))) ht).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s ∧ Reduced s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩))
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → Ctx Y s₀ s' →
      Frame ([⟨oa, oo, 32 * d⟩].map (Buf.rgn s₀) ++ [below (E1 s₀) 36]) s.mem s'.mem →
      Spec.Sha3.bytesAt s'.mem (Buf.addr s₀ ⟨oa, oo, 32 * d⟩) (32 * d) =
        compressEncode d (polyAt s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩)) → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B (ceC1024 Y.sc d ⟨fa, fo, 1024⟩ ⟨oa, oo, 32 * d⟩) := by
  have hc' := hc
  simp only [Bool.and_eq_true] at hc'
  obtain ⟨⟨h0, h1⟩, -⟩ := hc'
  refine Piece.seq (setup_piece (fun s₀ s₁ => s₁.gpr .eax = Buf.ptr s₀ ⟨fa, fo, 1024⟩ ∧
      s₁.gpr .ecx = BitVec.ofNat 32 d ∧ s₁.gpr .edx = Buf.ptr s₀ ⟨oa, oo, 32 * d⟩ ∧
      s₁.gpr .edi = BitVec.ofNat 32 (32 * d)) (fun s₀ s hp h => ?_) (fun s₀ s hp ha => (hA s₀ s hp ha).1) tt)
    (ce1024_call d hd fa fo oa oo hc hN (fun s₀ s₁ hp ⟨s, ha, h₁, m₁, e₁, e₂, e₃, e₄⟩ =>
      ⟨h₁, e₁, e₂, e₃, e₄, m₁ ▸ (hA s₀ s hp ha).2⟩)
      fun s₀ s₁ s' hp ⟨s, ha, _, m₁, _⟩ h' _ fr post => ?_)
  · simp only [List.append_assoc, List.cons_append, List.nil_append]
    refine ptrTo_ok hp h h0 fun s₁ o₁ v₁ => ?_
    have c₁ := h.only o₁ (by decide) (by decide)
    refine wp_movi fun s₂ o₂ v₂ => ?_
    have c₂ := c₁.only o₂ (by decide) (by decide)
    refine ptrTo_ok hp c₂ (Lay.okW_iff.mp h1).1 fun s₃ o₃ v₃ => ?_
    have c₃ := c₂.only o₃ (by decide) (by decide)
    refine wp_movi fun s₄ o₄ v₄ => WP.block_nil_iff.mpr ?_
    exact ⟨c₃.only o₄ (by decide) (by decide), o₄.mem.trans (o₃.mem.trans (o₂.mem.trans o₁.mem)),
      by rw [o₄.gpr _ (by decide), o₃.gpr _ (by decide), o₂.gpr _ (by decide), v₁],
      by rw [o₄.gpr _ (by decide), o₃.gpr _ (by decide), v₂], by rw [o₄.gpr _ (by decide), v₃], v₄⟩
  · rw [m₁] at fr post
    exact hQ s₀ s s' hp ha h' fr post

theorem ddC1024_piece (d : Nat) (hd : d ∈ Spec.MlKem1024.compressWidths) (ba bo fa fo : Nat)
    (hc : (Y.ok ⟨ba, bo, 32 * d⟩ && Y.okW ⟨fa, fo, 1024⟩ && Y.sep ⟨ba, bo, 32 * d⟩ ⟨fa, fo, 1024⟩) = true)
    (hN : 52 ≤ Y.stk) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi]) (.block (ptrTo Y.sc .eax ⟨ba, bo, 32 * d⟩ ++
      ([.mov .ecx (.imm (BitVec.ofNat 32 (32 * d))), .mov .edx (.imm (BitVec.ofNat 32 d))] : List Instr) ++
      ptrTo Y.sc .edi ⟨fa, fo, 1024⟩)) ht).isSome = true)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s)
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → Ctx Y s₀ s' →
      Frame ([⟨fa, fo, 1024⟩].map (Buf.rgn s₀) ++ [below (E1 s₀) 36]) s.mem s'.mem →
      PolyIs s'.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩)
        (decodeDecompress d (Spec.Sha3.bytesAt s.mem (Buf.addr s₀ ⟨ba, bo, 32 * d⟩) (32 * d))) → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B (ddC1024 Y.sc d ⟨ba, bo, 32 * d⟩ ⟨fa, fo, 1024⟩) := by
  have hc' := hc
  simp only [Bool.and_eq_true] at hc'
  obtain ⟨⟨h0, h1⟩, -⟩ := hc'
  refine Piece.seq (setup_piece (fun s₀ s₁ => s₁.gpr .eax = Buf.ptr s₀ ⟨ba, bo, 32 * d⟩ ∧
      s₁.gpr .ecx = BitVec.ofNat 32 (32 * d) ∧ s₁.gpr .edx = BitVec.ofNat 32 d ∧
      s₁.gpr .edi = Buf.ptr s₀ ⟨fa, fo, 1024⟩) (fun s₀ s hp h => ?_) hA tt)
    (dd1024_call d hd ba bo fa fo hc hN (fun s₀ s₁ hp ⟨_, _, h₁, _, e₁, e₂, e₃, e₄⟩ => ⟨h₁, e₁, e₂, e₃, e₄⟩)
      fun s₀ s₁ s' hp ⟨s, ha, _, m₁, _⟩ h' _ fr post => ?_)
  · simp only [List.append_assoc, List.cons_append, List.nil_append]
    refine ptrTo_ok hp h h0 fun s₁ o₁ v₁ => ?_
    have c₁ := h.only o₁ (by decide) (by decide)
    refine wp_movi fun s₂ o₂ v₂ => ?_
    have c₂ := c₁.only o₂ (by decide) (by decide)
    refine wp_movi fun s₃ o₃ v₃ => ?_
    have c₃ := c₂.only o₃ (by decide) (by decide)
    rw [← List.append_nil (ptrTo Y.sc .edi _)]
    refine ptrTo_ok hp c₃ (Lay.okW_iff.mp h1).1 fun s₄ o₄ v₄ => WP.block_nil_iff.mpr ?_
    exact ⟨c₃.only o₄ (by decide) (by decide), o₄.mem.trans (o₃.mem.trans (o₂.mem.trans o₁.mem)),
      by rw [o₄.gpr _ (by decide), o₃.gpr _ (by decide), o₂.gpr _ (by decide), v₁],
      by rw [o₄.gpr _ (by decide), o₃.gpr _ (by decide), v₂], by rw [o₄.gpr _ (by decide), v₃], v₄⟩
  · rw [m₁] at fr post
    exact hQ s₀ s s' hp ha h' fr post

end VG.Proof.MlKem.X86.Top
