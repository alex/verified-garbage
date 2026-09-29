import VerifiedGarbage.Proof.MlKem.X86.TopPrim
import VerifiedGarbage.Proof.MlKem.X86.Sample
import VerifiedGarbage.Proof.MlKem.X86.CompressEncode
import VerifiedGarbage.Proof.MlKem.X86.DecodeDecompress

/-!
# ML-KEM on x86 (32-bit): calls of `vg_mlkem_sample_ntt`, `vg_mlkem_compress_encode` and `vg_mlkem_decode_decompress`

Untrusted: everything here is checked by Lean. As `TopPrim.lean`.
`vg_mlkem_sample_ntt` returns a value, so its arguments are popped into
`ecx` (`callRet`), and its public data includes its seed: two runs agree on
it when the caller's seeds agree (`hseed`).
-/

namespace VG.Proof.MlKem.X86.Top

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Spec.MlKem
open VG.Proof.Sha3.X86 (reg32)

variable {Y : Lay} {lk : State → List Byte} {A B : State → State → Prop}

theorem sample_nosp : NoSp Impl.MlKem.X86.sampleNTT := NoSp.of_all (by decide +kernel)
theorem sample_stack : stackUse Impl.MlKem.X86.sampleNTT = 56 := by decide +kernel

/-- `a ← SampleNTT(seed)`, returning 1 or 0 in `eax`, with the 34 bytes `seed` at `(da, dO)`, `a` at
`(aa, ao)` and the scratch at `(ca, co)`, in `eax`, `ecx` and `edx`. -/
theorem sample_call (da dO aa ao ca co : Nat)
    (hc : (Y.ok ⟨da, dO, 34⟩ && Y.okW ⟨aa, ao, 1024⟩ && Y.okW ⟨ca, co, 2048⟩ && Y.sep ⟨da, dO, 34⟩ ⟨aa, ao, 1024⟩ &&
      Y.sep ⟨da, dO, 34⟩ ⟨ca, co, 2048⟩ && Y.sep ⟨aa, ao, 1024⟩ ⟨ca, co, 2048⟩) = true) (hN : 88 ≤ Y.stk)
    (hA : ∀ s₀ s, TPre Y s₀ → A s₀ s → Ctx Y s₀ s ∧ s.gpr .eax = Buf.ptr s₀ ⟨da, dO, 34⟩ ∧
      s.gpr .ecx = Buf.ptr s₀ ⟨aa, ao, 1024⟩ ∧ s.gpr .edx = Buf.ptr s₀ ⟨ca, co, 2048⟩)
    (hseed : ∀ s₀ s₀' s s', TPre Y s₀ → TPre Y s₀' → TPub Y lk s₀ s₀' → A s₀ s → A s₀' s' →
      Spec.Sha3.bytesAt s.mem (Buf.addr s₀ ⟨da, dO, 34⟩) 34 = Spec.Sha3.bytesAt s'.mem (Buf.addr s₀' ⟨da, dO, 34⟩) 34)
    (hQ : ∀ s₀ s s', TPre Y s₀ → A s₀ s → Ctx Y s₀ s' → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame ([⟨aa, ao, 1024⟩, ⟨ca, co, 2048⟩].map (Buf.rgn s₀) ++ [below (E1 s₀) 72]) s.mem s'.mem →
      (s'.gpr .eax = 1 → Reduced s'.mem (Buf.addr s₀ ⟨aa, ao, 1024⟩)) →
      Outcome (fun iters => sampleNTT iters (Spec.Sha3.bytesAt s.mem (Buf.addr s₀ ⟨da, dO, 34⟩) 34)) (s'.gpr .eax)
        (polyAt s'.mem (Buf.addr s₀ ⟨aa, ao, 1024⟩)) → B s₀ s') :
    Piece (TPre Y) (TPub Y lk) A B
      (callRet [.edx, .ecx, .eax] "vg_mlkem_sample_ntt" Impl.MlKem.X86.sampleNTT) := by
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨hD, hA'⟩, hC⟩, dDA⟩, dDC⟩, dAC⟩ := hc
  have hA₁ := (Lay.okW_iff.mp hA').1
  have hC₁ := (Lay.okW_iff.mp hC).1
  have entry : ∀ s₀ s, TPre Y s₀ → A s₀ s →
      4 * [Reg.edx, Reg.ecx, Reg.eax].length + 4 ≤ (s.gpr .esp).toNat ∧
      arg (pushed [.edx, .ecx, .eax] s).callEntry 0 = Buf.ptr s₀ ⟨da, dO, 34⟩ ∧
      arg (pushed [.edx, .ecx, .eax] s).callEntry 1 = Buf.ptr s₀ ⟨aa, ao, 1024⟩ ∧
      arg (pushed [.edx, .ecx, .eax] s).callEntry 2 = Buf.ptr s₀ ⟨ca, co, 2048⟩ := fun s₀ s hp ha => by
    obtain ⟨h, hax, hcx, hdx⟩ := hA s₀ s hp ha
    have fit : 4 * [Reg.edx, Reg.ecx, Reg.eax].length + 4 ≤ (s.gpr .esp).toNat := by
      have := ctx_E hp h (N := 72) (by omega); simp only [List.length_cons, List.length_nil]; omega
    refine ⟨fit, ?_, ?_, ?_⟩
    · rw [callEntry_arg fit (by decide) (by decide)]; exact hax
    · rw [callEntry_arg fit (by decide) (by decide)]; exact hcx
    · rw [callEntry_arg fit (by decide) (by decide)]; exact hdx
  refine callR_piece Sample.verified sample_nosp (by decide) (by decide)
    (by rw [sample_stack]; simp only [List.length_cons, List.length_nil]; omega)
    (fun s₀ => [Buf.rgn s₀ ⟨da, dO, 34⟩])
    (fun s₀ => [Buf.rgn s₀ ⟨aa, ao, 1024⟩, Buf.rgn s₀ ⟨ca, co, 2048⟩] ++ [below (E1 s₀) 12])
    (fun s₀ s hp ha => ?_) (fun s₀ s₀' s s' hp hp' hq ha ha' => ?_)
    (fun s₀ hp => wr_sub hp (bs := [⟨aa, ao, 1024⟩, ⟨ca, co, 2048⟩]) (by simp [hA', hC]) (by omega))
    (fun s₀ s s' hp ha h' e₃ fr post => ?_)
  · have h := (hA s₀ s hp ha).1
    obtain ⟨fit, a0, a1, a2⟩ := entry s₀ s hp ha
    have hE' : 72 ≤ (E1 s₀).toNat := by rw [← h.esp]; exact ctx_E hp h (N := 72) (by omega)
    have eA : argAddr (pushed [.edx, .ecx, .eax] s).callEntry 0 = (E1 s₀ - BitVec.ofNat 32 12).setWidth 64 := by
      rw [callEntry_argAddr0, h.esp]; rfl
    have eSp : (pushed [.edx, .ecx, .eax] s).callEntry.gpr .esp = E1 s₀ - BitVec.ofNat 32 16 := by
      rw [callEntry_esp', h.esp]; rfl
    have bD := Buf.stkD hp hD (N := 4 * 3 + 4 + 56) (by omega)
    have bA := Buf.stkD hp hA₁ (N := 4 * 3 + 4 + 56) (by omega)
    have bC := Buf.stkD hp hC₁ (N := 4 * 3 + 4 + 56) (by omega)
    obtain ⟨rD₁, rD₂, rD₃⟩ := entry_regions hE' bD
    obtain ⟨rA₁, rA₂, rA₃⟩ := entry_regions hE' bA
    obtain ⟨rC₁, rC₂, rC₃⟩ := entry_regions hE' bC
    obtain ⟨rG₂, rG₃⟩ := entry_self (E := E1 s₀) (k := 3) (K := 56) hE'
    have cv := covers_of (s := s) (n := 3) (rd := [Buf.rgn s₀ ⟨da, dO, 34⟩])
      (wr := [Buf.rgn s₀ ⟨aa, ao, 1024⟩, Buf.rgn s₀ ⟨ca, co, 2048⟩] ++ [below (E1 s₀) 12])
      (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl
        exact Buf.within hp hD h.rd h.wr) fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact .inr (Buf.withinW hp hA₁ (Lay.okW_iff.mp hA').2 h.wr)
      · exact .inr (Buf.withinW hp hC₁ (Lay.okW_iff.mp hC).2 h.wr)
      · exact .inl (by rw [h.esp])
    refine ⟨h, ?_, cv.1, cv.2⟩
    sig_pre [sampleNTTContract, sampleNTTSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr,
      arg_withRegions, argAddr_withRegions, a0, a1, a2, eA, eSp]
    refine ⟨by rw [sub_toNat (by omega)]; omega, by rw [sub_toNat (by omega)]; have := (E1 s₀).isLt; omega,
      trivial, trivial, Buf.disj hp hD hA₁ dDA, Buf.disj hp hD hC₁ dDC, rD₁, Buf.disj hp hA₁ hC₁ dAC, rA₁,
      rC₁, rD₂, rA₂, rC₂, rG₂, rD₃, rA₃, rC₃, rG₃, Buf.fit hp hD, Buf.fit hp hA₁, Buf.fit hp hC₁⟩
  · have h := (hA s₀ s hp ha).1
    have h' := (hA s₀' s' hp' ha').1
    obtain ⟨fit, a0, -, -⟩ := entry s₀ s hp ha
    obtain ⟨fit', a0', -, -⟩ := entry s₀' s' hp' ha'
    obtain ⟨-, hax, hcx, hdx⟩ := hA s₀ s hp ha
    obtain ⟨-, hax', hcx', hdx'⟩ := hA s₀' s' hp' ha'
    have hsp : s.gpr .esp = s'.gpr .esp := by rw [h.esp, h'.esp, hq.E1]
    have hr : ∀ r ∈ [Reg.edx, Reg.ecx, Reg.eax], s.gpr r = s'.gpr r := by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [hdx, hdx', hq.ptr hC₁]
      · rw [hcx, hcx', hq.ptr hA₁]
      · rw [hax, hax', hq.ptr hD]
    have ek := @ent_keep Y s₀ s hp h [.edx, .ecx, .eax] (by decide) (by simp; omega)
    have ek' := @ent_keep Y s₀' s' hp' h' [.edx, .ecx, .eax] (by decide) (by simp; omega)
    refine ⟨by simp only [Buf.rgn, hq.ptr hD], by simp only [Buf.rgn, hq.ptr hA₁, hq.ptr hC₁, hq.E1], ?_⟩
    sig_pub [sampleNTTContract, sampleNTTSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [State.withRegions_gpr, State.withRegions_mem, arg_withRegions, callEntry_esp', hsp]
    refine ⟨trivial, ?_, callEntry_arg_eq (by decide) fit hsp hr (by decide),
      callEntry_arg_eq (by decide) fit hsp hr (by decide), callEntry_arg_eq (by decide) fit hsp hr (by decide)⟩
    rw [a0, a0', bytesAt_congr (ek hD), bytesAt_congr (ek' hD), hseed s₀ s₀' s s' hp hp' hq ha ha']
  · have h := (hA s₀ s hp ha).1
    obtain ⟨fit, a0, a1, -⟩ := entry s₀ s hp ha
    obtain ⟨s₂, m₂, g₂, post⟩ := post
    have ek := @ent_keep Y s₀ s hp h [.edx, .ecx, .eax] (by decide) (by simp; omega)
    sig_post [sampleNTTContract, sampleNTTSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at post
    simp only [arg_withRegions, State.withRegions_mem, a0, a1, m₂, setWidth_append32, g₂] at post
    rw [bytesAt_congr (ek hD)] at post
    exact hQ s₀ s s' hp ha h' e₃ (fr_conv hp (a := 12) (N := 72) (by omega) (by omega)
      (by rw [sample_stack] at fr; exact fr)) post.1 post.2

theorem ce_nosp : NoSp Impl.MlKem.X86.compressEncode := NoSp.of_all (by decide +kernel)
theorem ce_stack : stackUse Impl.MlKem.X86.compressEncode = 16 := by decide +kernel
theorem dd_nosp : NoSp Impl.MlKem.X86.decodeDecompress := NoSp.of_all (by decide +kernel)
theorem dd_stack : stackUse Impl.MlKem.X86.decodeDecompress = 16 := by decide +kernel

theorem width_lt {d : Nat} (hd : d ∈ compressWidths) : 32 * d < 2 ^ 32 := by
  simp only [compressWidths, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl <;> decide

/-- `out ← ByteEncode_d(Compress_d(f))`, with `f` at `(fa, fo)` and the `32d` bytes `out` at `(oa, oo)`,
and `f`, `d`, `out`, `32d` in `eax`, `ecx`, `edx` and `edi`. -/
theorem ce_call (d : Nat) (hd : d ∈ compressWidths) (fa fo oa oo : Nat)
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
      (callWith [.edi, .edx, .ecx, .eax] "vg_mlkem_compress_encode" Impl.MlKem.X86.compressEncode) := by
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨hF, hO⟩, dFO⟩ := hc
  have hO₁ := (Lay.okW_iff.mp hO).1
  have hd32 := width_lt hd
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
  refine call_piece CompressEncode.verified ce_nosp (by decide) (by decide)
    (by rw [ce_stack]; simp only [List.length_cons, List.length_nil]; omega)
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
    sig_pre [compressEncodeContract, compressEncodeSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr, State.withRegions_mem,
      arg_withRegions, argAddr_withRegions, a0, a1, a2, a3, eA, eSp, toNat_ofNat32 hd', toNat_ofNat32 hd32]
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
    sig_pub [compressEncodeContract, compressEncodeSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [State.withRegions_gpr, arg_withRegions, callEntry_esp', hsp]
    exact ⟨trivial, callEntry_arg_eq (by decide) fit hsp hr (by decide),
      callEntry_arg_eq (by decide) fit hsp hr (by decide), callEntry_arg_eq (by decide) fit hsp hr (by decide),
      callEntry_arg_eq (by decide) fit hsp hr (by decide)⟩
  · have h := (hA s₀ s hp ha).1
    obtain ⟨fit, a0, a1, a2, a3⟩ := entry s₀ s hp ha
    obtain ⟨s₂, m₂, post⟩ := post
    have ek := @ent_keep Y s₀ s hp h [.edi, .edx, .ecx, .eax] (by decide) (by simp; omega)
    sig_post [compressEncodeContract, compressEncodeSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at post
    simp only [arg_withRegions, State.withRegions_mem, a0, a1, a2, a3, m₂, toNat_ofNat32 hd',
      toNat_ofNat32 hd32] at post
    rw [polyAt_congr (ek hF)] at post
    exact hQ s₀ s s' hp ha h' e₃ (fr_conv hp (a := 16) (N := 36) (by omega) (by omega)
      (by rw [ce_stack] at fr; exact fr)) post

/-- `f ← Decompress_d(ByteDecode_d(b))`, with the `32d` bytes `b` at `(ba, bo)` and `f` at `(fa, fo)`,
and `b`, `32d`, `d`, `f` in `eax`, `ecx`, `edx` and `edi`. -/
theorem dd_call (d : Nat) (hd : d ∈ compressWidths) (ba bo fa fo : Nat)
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
      (callWith [.edi, .edx, .ecx, .eax] "vg_mlkem_decode_decompress" Impl.MlKem.X86.decodeDecompress) := by
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨hB, hF⟩, dBF⟩ := hc
  have hF₁ := (Lay.okW_iff.mp hF).1
  have hd32 := width_lt hd
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
  refine call_piece DecodeDecompress.verified dd_nosp (by decide) (by decide)
    (by rw [dd_stack]; simp only [List.length_cons, List.length_nil]; omega)
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
    sig_pre [decodeDecompressContract, decodeDecompressSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr,
      arg_withRegions, argAddr_withRegions, a0, a1, a2, a3, eA, eSp, toNat_ofNat32 hd', toNat_ofNat32 hd32]
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
    sig_pub [decodeDecompressContract, decodeDecompressSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [State.withRegions_gpr, arg_withRegions, callEntry_esp', hsp]
    exact ⟨trivial, callEntry_arg_eq (by decide) fit hsp hr (by decide),
      callEntry_arg_eq (by decide) fit hsp hr (by decide), callEntry_arg_eq (by decide) fit hsp hr (by decide),
      callEntry_arg_eq (by decide) fit hsp hr (by decide)⟩
  · have h := (hA s₀ s hp ha).1
    obtain ⟨fit, a0, a1, a2, a3⟩ := entry s₀ s hp ha
    obtain ⟨s₂, m₂, post⟩ := post
    have ek := @ent_keep Y s₀ s hp h [.edi, .edx, .ecx, .eax] (by decide) (by simp; omega)
    sig_post [decodeDecompressContract, decodeDecompressSig, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes] at post
    simp only [arg_withRegions, State.withRegions_mem, a0, a1, a2, a3, m₂, toNat_ofNat32 hd',
      toNat_ofNat32 hd32] at post
    rw [bytesAt_congr (ek hB)] at post
    exact hQ s₀ s s' hp ha h' e₃ (fr_conv hp (a := 16) (N := 36) (by omega) (by omega)
      (by rw [dd_stack] at fr; exact fr)) post

end VG.Proof.MlKem.X86.Top
