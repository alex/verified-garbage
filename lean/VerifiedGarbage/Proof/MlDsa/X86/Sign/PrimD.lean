import VerifiedGarbage.Proof.MlDsa.X86.Sign.Prims

/-!
# ML-DSA signing on x86 (32-bit): calls of the encodings

Untrusted: everything here is checked by Lean. `SimpleBitPack`
(`sbp_piece`), `BitPack` (`bp_piece`), `BitUnpack` (`bu_piece`) and
`HintBitPack` (`hbp_piece`, which may leak the hint).
-/

namespace VG.Proof.MlDsa.X86.Sign

open VG VG.X86
open VG.Impl.MlKem.X86 (Buf ptrTo at_ callWith callRet)
open VG.Impl.MlDsa.X86.Sign
open VG.Proof.MlKem.X86 (Piece Only wp_cons)
open VG.Proof.MlKem.X86.Top
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

variable {p : Params} {A B : State → State → Prop}

/-- `out ← SimpleBitPack(f, b)`, `len` bytes. -/
theorem sbp_piece {nm : String} {c : Prog isa} (hv : Verified X86.target c (simpleBitPackContract X86.abi 16))
    (ok : COk c) (b len : Nat) (hb : b ∈ simpleBitPackBounds) (hl : len = 32 * bitlen b) (fa fo oa oo : Nat)
    (hc : ((Y p).ok ⟨fa, fo, 1024⟩ && (Y p).okW ⟨oa, oo, len⟩ && (Y p).sep ⟨fa, fo, 1024⟩ ⟨oa, oo, len⟩) = true)
    (hA : ∀ s₀ s, TPre (Y p) s₀ → A s₀ s → Ctx (Y p) s₀ s ∧ ∀ i < n, (coeffAt s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩) i).toNat ≤ b)
    (hQ : ∀ s₀ s s', TPre (Y p) s₀ → A s₀ s → Ctx (Y p) s₀ s' → Frame (FR s₀ [⟨oa, oo, len⟩] 80) s.mem s'.mem →
      bytesAt s'.mem (Buf.addr s₀ ⟨oa, oo, len⟩) len = simpleBitPack (natPolyAt s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩)) b →
      B s₀ s') :
    SP p A B (callP nm c [.buf ⟨fa, fo, 1024⟩, .imm b, .buf ⟨oa, oo, len⟩, .imm len]) := by
  set F : Buf := ⟨fa, fo, 1024⟩
  set O : Buf := ⟨oa, oo, len⟩
  have bl : (BitVec.ofNat 32 b).toNat = b := by
    simp only [simpleBitPackBounds, t1Max, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl <;> rfl
  have ll : (BitVec.ofNat 32 len).toNat = len := by
    simp only [simpleBitPackBounds, t1Max, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl <;> subst hl <;> rfl
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨hF, hO⟩, dFO⟩ := hc
  have hO' := (Lay.okW_iff.mp hO).1
  refine callP_piece _ 4 rfl hv ok (by decide) (by decide) (by simp [argOk, hF, hO']) (fun s₀ => [F.rgn s₀])
    (fun s₀ => [O.rgn s₀, below (E1 s₀) 16]) (fun s₀ s hp ha => (hA s₀ s hp ha).1)
    (fun s₀ s₁ hp ⟨s, ha, h, m, hg⟩ => ?_) (fun s₀ s₀' s₁ s₁' hp hp' hq ⟨s, ha, h, m, hg⟩ ⟨s', ha', h', m', hg'⟩ => ?_)
    (fun s₀ hp r hr => ?_) (fun s₀ s₁ s' hp ⟨s, ha, h, m, hg⟩ h' fr post => ?_)
  · have a0 : arg (pushed (argPush 4) s₁).callEntry 0 = F.ptr s₀ := ent_arg hp h (as := [.buf F, .imm b, .buf O, .imm len]) (by simp) hg (i := 0) (by simp)
    have a1 : arg (pushed (argPush 4) s₁).callEntry 1 = BitVec.ofNat 32 b := ent_arg hp h (as := [.buf F, .imm b, .buf O, .imm len]) (by simp) hg (i := 1) (by simp)
    have a2 : arg (pushed (argPush 4) s₁).callEntry 2 = O.ptr s₀ := ent_arg hp h (as := [.buf F, .imm b, .buf O, .imm len]) (by simp) hg (i := 2) (by simp)
    have a3 : arg (pushed (argPush 4) s₁).callEntry 3 = BitVec.ofNat 32 len := ent_arg hp h (as := [.buf F, .imm b, .buf O, .imm len]) (by simp) hg (i := 3) (by simp)
    have eA : argAddr (pushed (argPush 4) s₁).callEntry 0 = _ := ent_arg0 h (n := 4) (by decide)
    have eSp : (pushed (argPush 4) s₁).callEntry.gpr .esp = _ := ent_esp h (n := 4) (by decide)
    obtain ⟨rF₁, rF₂, rF₃⟩ := ent_rgn hp hF (n := 4) (K := 16) (by decide)
    obtain ⟨rO₁, rO₂, rO₃⟩ := ent_rgn hp hO' (n := 4) (K := 16) (by decide)
    obtain ⟨rA₂, rA₃⟩ := ent_self hp (n := 4) (K := 16) (by decide)
    have hE := E1_big hp
    have cv := covers_of (s := s₁) (n := 4) (rd := [F.rgn s₀]) (wr := [O.rgn s₀, below (E1 s₀) 16])
      (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        subst hr; exact Buf.within hp hF h.rd h.wr) fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact .inr (Buf.withinW hp hO' (Lay.okW_iff.mp hO).2 h.wr)
        · exact .inl (by rw [h.esp])
    refine ⟨?_, cv.1, cv.2⟩
    generalize he : (pushed (argPush 4) s₁).callEntry = e at a0 a1 a2 a3 eA eSp ⊢
    sig_pre [simpleBitPackContract, simpleBitPackSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    subst he
    simp only [arg_withRegions, argAddr_withRegions, a0, a1, a2, a3, eA, eSp, bl, ll]
    refine ⟨by rw [sub_toNat (by omega)]; omega, by rw [sub_toNat (by omega)]; have := (E1 s₀).isLt; omega,
      rfl, rfl, Buf.disj hp hF hO' dFO, rF₁, rO₁, rF₂, rO₂, rA₂, rF₃, rO₃, rA₃,
      Buf.fit hp hF, Buf.fit hp hO', hb, hl, fun i hi => ?_⟩
    rw [coeffAt_congr₂ (ent_bytes hp h (n := 4) (by decide) hF) hi, m]; exact (hA s₀ s hp ha).2 i hi
  · have e₁ : F.ptr s₀ = F.ptr s₀' := hq.t.ptr hF
    have e₂ : O.ptr s₀ = O.ptr s₀' := hq.t.ptr hO'
    refine ⟨by simp only [Buf.rgn, e₁], by simp only [Buf.rgn, e₂, hq.t.E1], ?_⟩
    have a0 : arg (pushed (argPush 4) s₁).callEntry 0 = F.ptr s₀ := ent_arg hp h (as := [.buf F, .imm b, .buf O, .imm len]) (by simp) hg (i := 0) (by simp)
    have a1 : arg (pushed (argPush 4) s₁).callEntry 1 = BitVec.ofNat 32 b := ent_arg hp h (as := [.buf F, .imm b, .buf O, .imm len]) (by simp) hg (i := 1) (by simp)
    have a2 : arg (pushed (argPush 4) s₁).callEntry 2 = O.ptr s₀ := ent_arg hp h (as := [.buf F, .imm b, .buf O, .imm len]) (by simp) hg (i := 2) (by simp)
    have a3 : arg (pushed (argPush 4) s₁).callEntry 3 = BitVec.ofNat 32 len := ent_arg hp h (as := [.buf F, .imm b, .buf O, .imm len]) (by simp) hg (i := 3) (by simp)
    have a0' : arg (pushed (argPush 4) s₁').callEntry 0 = F.ptr s₀' := ent_arg hp' h' (as := [.buf F, .imm b, .buf O, .imm len]) (by simp) hg' (i := 0) (by simp)
    have a1' : arg (pushed (argPush 4) s₁').callEntry 1 = BitVec.ofNat 32 b := ent_arg hp' h' (as := [.buf F, .imm b, .buf O, .imm len]) (by simp) hg' (i := 1) (by simp)
    have a2' : arg (pushed (argPush 4) s₁').callEntry 2 = O.ptr s₀' := ent_arg hp' h' (as := [.buf F, .imm b, .buf O, .imm len]) (by simp) hg' (i := 2) (by simp)
    have a3' : arg (pushed (argPush 4) s₁').callEntry 3 = BitVec.ofNat 32 len := ent_arg hp' h' (as := [.buf F, .imm b, .buf O, .imm len]) (by simp) hg' (i := 3) (by simp)
    have eSp : (pushed (argPush 4) s₁).callEntry.gpr .esp = _ := ent_esp h (n := 4) (by decide)
    have eSp' : (pushed (argPush 4) s₁').callEntry.gpr .esp = _ := ent_esp h' (n := 4) (by decide)
    generalize he : (pushed (argPush 4) s₁).callEntry = e at a0 a1 a2 a3 eSp ⊢
    generalize he' : (pushed (argPush 4) s₁').callEntry = e' at a0' a1' a2' a3' eSp' ⊢
    sig_pub [simpleBitPackContract, simpleBitPackSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [arg_withRegions, a0, a1, a2, a3, a0', a1', a2', a3', eSp, eSp', e₁, e₂, hq.t.E1, and_self]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Buf.inW hp hO' (Lay.okW_iff.mp hO).2
    · exact stk_W hp (by decide)
  · obtain ⟨s₂, m₂, post⟩ := post
    have a0 : arg (pushed (argPush 4) s₁).callEntry 0 = F.ptr s₀ := ent_arg hp h (as := [.buf F, .imm b, .buf O, .imm len]) (by simp) hg (i := 0) (by simp)
    have a1 : arg (pushed (argPush 4) s₁).callEntry 1 = BitVec.ofNat 32 b := ent_arg hp h (as := [.buf F, .imm b, .buf O, .imm len]) (by simp) hg (i := 1) (by simp)
    have a2 : arg (pushed (argPush 4) s₁).callEntry 2 = O.ptr s₀ := ent_arg hp h (as := [.buf F, .imm b, .buf O, .imm len]) (by simp) hg (i := 2) (by simp)
    have a3 : arg (pushed (argPush 4) s₁).callEntry 3 = BitVec.ofNat 32 len := ent_arg hp h (as := [.buf F, .imm b, .buf O, .imm len]) (by simp) hg (i := 3) (by simp)
    generalize he : (pushed (argPush 4) s₁).callEntry = e at a0 a1 a2 a3 post
    sig_post [simpleBitPackContract, simpleBitPackSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at post
    subst he
    simp only [arg_withRegions, a0, a1, a2, a3, m₂, bl, ll] at post
    rw [natPolyAt_congr₂ (ent_bytes hp h (n := 4) (by decide) hF), m] at post
    exact hQ s₀ s s' hp ha h' (fr80 (by decide) (by have := ok.stk; omega) hp (m ▸ fr)) post

/-- `out ← BitPack(f mod± q, a, b)`, `len` bytes. -/
theorem bp_piece {nm : String} {c : Prog isa} (hv : Verified X86.target c (bitPackContract X86.abi 16))
    (ok : COk c) (a b len : Nat) (hab : (a, b) ∈ bitPackParams) (hl : len = 32 * bitlen (a + b))
    (hs : a < 2 ^ 32 ∧ b < 2 ^ 32 ∧ len < 2 ^ 32) (fa fo oa oo : Nat)
    (hc : ((Y p).ok ⟨fa, fo, 1024⟩ && (Y p).okW ⟨oa, oo, len⟩ && (Y p).sep ⟨fa, fo, 1024⟩ ⟨oa, oo, len⟩) = true)
    (hA : ∀ s₀ s, TPre (Y p) s₀ → A s₀ s → Ctx (Y p) s₀ s ∧ Reduced s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩) ∧
      ∀ i < n, -(a : Int) ≤ modPm (coeffAt s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩) i).toNat q ∧
        modPm (coeffAt s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩) i).toNat q ≤ b)
    (hQ : ∀ s₀ s s', TPre (Y p) s₀ → A s₀ s → Ctx (Y p) s₀ s' → Frame (FR s₀ [⟨oa, oo, len⟩] 80) s.mem s'.mem →
      bytesAt s'.mem (Buf.addr s₀ ⟨oa, oo, len⟩) len =
        bitPack ((polyAt s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩)).map fun c => modPm c.val q) a b → B s₀ s') :
    SP p A B (callP nm c [.buf ⟨fa, fo, 1024⟩, .imm a, .imm b, .buf ⟨oa, oo, len⟩, .imm len]) := by
  set F : Buf := ⟨fa, fo, 1024⟩
  set O : Buf := ⟨oa, oo, len⟩
  have al : (BitVec.ofNat 32 a).toNat = a := by rw [BitVec.toNat_ofNat]; omega
  have bl : (BitVec.ofNat 32 b).toNat = b := by rw [BitVec.toNat_ofNat]; omega
  have ll : (BitVec.ofNat 32 len).toNat = len := by rw [BitVec.toNat_ofNat]; omega
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨hF, hO⟩, dFO⟩ := hc
  have hO' := (Lay.okW_iff.mp hO).1
  refine callP_piece _ 5 rfl hv ok (by decide) (by decide) (by simp [argOk, hF, hO']) (fun s₀ => [F.rgn s₀])
    (fun s₀ => [O.rgn s₀, below (E1 s₀) 20]) (fun s₀ s hp ha => (hA s₀ s hp ha).1)
    (fun s₀ s₁ hp ⟨s, ha, h, m, hg⟩ => ?_) (fun s₀ s₀' s₁ s₁' hp hp' hq ⟨s, ha, h, m, hg⟩ ⟨s', ha', h', m', hg'⟩ => ?_)
    (fun s₀ hp r hr => ?_) (fun s₀ s₁ s' hp ⟨s, ha, h, m, hg⟩ h' fr post => ?_)
  · have a0 : arg (pushed (argPush 5) s₁).callEntry 0 = F.ptr s₀ := ent_arg hp h (as := [.buf F, .imm a, .imm b, .buf O, .imm len]) (by simp) hg (i := 0) (by simp)
    have a1 : arg (pushed (argPush 5) s₁).callEntry 1 = BitVec.ofNat 32 a := ent_arg hp h (as := [.buf F, .imm a, .imm b, .buf O, .imm len]) (by simp) hg (i := 1) (by simp)
    have a2 : arg (pushed (argPush 5) s₁).callEntry 2 = BitVec.ofNat 32 b := ent_arg hp h (as := [.buf F, .imm a, .imm b, .buf O, .imm len]) (by simp) hg (i := 2) (by simp)
    have a3 : arg (pushed (argPush 5) s₁).callEntry 3 = O.ptr s₀ := ent_arg hp h (as := [.buf F, .imm a, .imm b, .buf O, .imm len]) (by simp) hg (i := 3) (by simp)
    have a4 : arg (pushed (argPush 5) s₁).callEntry 4 = BitVec.ofNat 32 len := ent_arg hp h (as := [.buf F, .imm a, .imm b, .buf O, .imm len]) (by simp) hg (i := 4) (by simp)
    have eA : argAddr (pushed (argPush 5) s₁).callEntry 0 = _ := ent_arg0 h (n := 5) (by decide)
    have eSp : (pushed (argPush 5) s₁).callEntry.gpr .esp = _ := ent_esp h (n := 5) (by decide)
    obtain ⟨rF₁, rF₂, rF₃⟩ := ent_rgn hp hF (n := 5) (K := 16) (by decide)
    obtain ⟨rO₁, rO₂, rO₃⟩ := ent_rgn hp hO' (n := 5) (K := 16) (by decide)
    obtain ⟨rA₂, rA₃⟩ := ent_self hp (n := 5) (K := 16) (by decide)
    have hE := E1_big hp
    have cv := covers_of (s := s₁) (n := 5) (rd := [F.rgn s₀]) (wr := [O.rgn s₀, below (E1 s₀) 20])
      (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        subst hr; exact Buf.within hp hF h.rd h.wr) fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact .inr (Buf.withinW hp hO' (Lay.okW_iff.mp hO).2 h.wr)
        · exact .inl (by rw [h.esp])
    refine ⟨?_, cv.1, cv.2⟩
    generalize he : (pushed (argPush 5) s₁).callEntry = e at a0 a1 a2 a3 a4 eA eSp ⊢
    sig_pre [bitPackContract, bitPackSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    subst he
    simp only [arg_withRegions, argAddr_withRegions, a0, a1, a2, a3, a4, eA, eSp, al, bl, ll]
    refine ⟨by rw [sub_toNat (by omega)]; omega, by rw [sub_toNat (by omega)]; have := (E1 s₀).isLt; omega,
      rfl, rfl, Buf.disj hp hF hO' dFO, rF₁, rO₁, rF₂, rO₂, rA₂, rF₃, rO₃, rA₃,
      Buf.fit hp hF, Buf.fit hp hO', hab, hl, ?_, fun i hi => ?_⟩
    · exact reduced_congr (ent_bytes hp h (n := 5) (by decide) hF) (m ▸ (hA s₀ s hp ha).2.1)
    · rw [coeffAt_congr₂ (ent_bytes hp h (n := 5) (by decide) hF) hi, m]; exact (hA s₀ s hp ha).2.2 i hi
  · have e₁ : F.ptr s₀ = F.ptr s₀' := hq.t.ptr hF
    have e₂ : O.ptr s₀ = O.ptr s₀' := hq.t.ptr hO'
    refine ⟨by simp only [Buf.rgn, e₁], by simp only [Buf.rgn, e₂, hq.t.E1], ?_⟩
    have a0 : arg (pushed (argPush 5) s₁).callEntry 0 = F.ptr s₀ := ent_arg hp h (as := [.buf F, .imm a, .imm b, .buf O, .imm len]) (by simp) hg (i := 0) (by simp)
    have a1 : arg (pushed (argPush 5) s₁).callEntry 1 = BitVec.ofNat 32 a := ent_arg hp h (as := [.buf F, .imm a, .imm b, .buf O, .imm len]) (by simp) hg (i := 1) (by simp)
    have a2 : arg (pushed (argPush 5) s₁).callEntry 2 = BitVec.ofNat 32 b := ent_arg hp h (as := [.buf F, .imm a, .imm b, .buf O, .imm len]) (by simp) hg (i := 2) (by simp)
    have a3 : arg (pushed (argPush 5) s₁).callEntry 3 = O.ptr s₀ := ent_arg hp h (as := [.buf F, .imm a, .imm b, .buf O, .imm len]) (by simp) hg (i := 3) (by simp)
    have a4 : arg (pushed (argPush 5) s₁).callEntry 4 = BitVec.ofNat 32 len := ent_arg hp h (as := [.buf F, .imm a, .imm b, .buf O, .imm len]) (by simp) hg (i := 4) (by simp)
    have a0' : arg (pushed (argPush 5) s₁').callEntry 0 = F.ptr s₀' := ent_arg hp' h' (as := [.buf F, .imm a, .imm b, .buf O, .imm len]) (by simp) hg' (i := 0) (by simp)
    have a1' : arg (pushed (argPush 5) s₁').callEntry 1 = BitVec.ofNat 32 a := ent_arg hp' h' (as := [.buf F, .imm a, .imm b, .buf O, .imm len]) (by simp) hg' (i := 1) (by simp)
    have a2' : arg (pushed (argPush 5) s₁').callEntry 2 = BitVec.ofNat 32 b := ent_arg hp' h' (as := [.buf F, .imm a, .imm b, .buf O, .imm len]) (by simp) hg' (i := 2) (by simp)
    have a3' : arg (pushed (argPush 5) s₁').callEntry 3 = O.ptr s₀' := ent_arg hp' h' (as := [.buf F, .imm a, .imm b, .buf O, .imm len]) (by simp) hg' (i := 3) (by simp)
    have a4' : arg (pushed (argPush 5) s₁').callEntry 4 = BitVec.ofNat 32 len := ent_arg hp' h' (as := [.buf F, .imm a, .imm b, .buf O, .imm len]) (by simp) hg' (i := 4) (by simp)
    have eSp : (pushed (argPush 5) s₁).callEntry.gpr .esp = _ := ent_esp h (n := 5) (by decide)
    have eSp' : (pushed (argPush 5) s₁').callEntry.gpr .esp = _ := ent_esp h' (n := 5) (by decide)
    generalize he : (pushed (argPush 5) s₁).callEntry = e at a0 a1 a2 a3 a4 eSp ⊢
    generalize he' : (pushed (argPush 5) s₁').callEntry = e' at a0' a1' a2' a3' a4' eSp' ⊢
    sig_pub [bitPackContract, bitPackSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [arg_withRegions, a0, a1, a2, a3, a4, a0', a1', a2', a3', a4', eSp, eSp', e₁, e₂, hq.t.E1, and_self]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Buf.inW hp hO' (Lay.okW_iff.mp hO).2
    · exact stk_W hp (by decide)
  · obtain ⟨s₂, m₂, post⟩ := post
    have a0 : arg (pushed (argPush 5) s₁).callEntry 0 = F.ptr s₀ := ent_arg hp h (as := [.buf F, .imm a, .imm b, .buf O, .imm len]) (by simp) hg (i := 0) (by simp)
    have a1 : arg (pushed (argPush 5) s₁).callEntry 1 = BitVec.ofNat 32 a := ent_arg hp h (as := [.buf F, .imm a, .imm b, .buf O, .imm len]) (by simp) hg (i := 1) (by simp)
    have a2 : arg (pushed (argPush 5) s₁).callEntry 2 = BitVec.ofNat 32 b := ent_arg hp h (as := [.buf F, .imm a, .imm b, .buf O, .imm len]) (by simp) hg (i := 2) (by simp)
    have a3 : arg (pushed (argPush 5) s₁).callEntry 3 = O.ptr s₀ := ent_arg hp h (as := [.buf F, .imm a, .imm b, .buf O, .imm len]) (by simp) hg (i := 3) (by simp)
    have a4 : arg (pushed (argPush 5) s₁).callEntry 4 = BitVec.ofNat 32 len := ent_arg hp h (as := [.buf F, .imm a, .imm b, .buf O, .imm len]) (by simp) hg (i := 4) (by simp)
    generalize he : (pushed (argPush 5) s₁).callEntry = e at a0 a1 a2 a3 a4 post
    sig_post [bitPackContract, bitPackSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at post
    subst he
    simp only [arg_withRegions, a0, a1, a2, a3, a4, m₂, al, bl, ll] at post
    rw [polyAt_congr (ent_bytes hp h (n := 5) (by decide) hF), m] at post
    exact hQ s₀ s s' hp ha h' (fr80 (by decide) (by have := ok.stk; omega) hp (m ▸ fr)) post

/-- `f ← BitUnpack(v, a, b)`, of the `len` bytes `v`. -/
theorem bu_piece {nm : String} {c : Prog isa} (hv : Verified X86.target c (bitUnpackContract X86.abi 16))
    (ok : COk c) (a b len : Nat) (hab : (a, b) ∈ bitPackParams) (hl : len = 32 * bitlen (a + b))
    (hs : a < 2 ^ 32 ∧ b < 2 ^ 32 ∧ len < 2 ^ 32) (va vo fa fo : Nat)
    (hc : ((Y p).ok ⟨va, vo, len⟩ && (Y p).okW ⟨fa, fo, 1024⟩ && (Y p).sep ⟨va, vo, len⟩ ⟨fa, fo, 1024⟩) = true)
    (hA : ∀ s₀ s, TPre (Y p) s₀ → A s₀ s → Ctx (Y p) s₀ s)
    (hQ : ∀ s₀ s s', TPre (Y p) s₀ → A s₀ s → Ctx (Y p) s₀ s' → Frame (FR s₀ [⟨fa, fo, 1024⟩] 80) s.mem s'.mem →
      PolyIs s'.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩) (toRq (bitUnpack (bytesAt s.mem (Buf.addr s₀ ⟨va, vo, len⟩) len) a b)) →
      B s₀ s') :
    SP p A B (callP nm c [.buf ⟨va, vo, len⟩, .imm len, .imm a, .imm b, .buf ⟨fa, fo, 1024⟩]) := by
  set V : Buf := ⟨va, vo, len⟩
  set F : Buf := ⟨fa, fo, 1024⟩
  have al : (BitVec.ofNat 32 a).toNat = a := by rw [BitVec.toNat_ofNat]; omega
  have bl : (BitVec.ofNat 32 b).toNat = b := by rw [BitVec.toNat_ofNat]; omega
  have ll : (BitVec.ofNat 32 len).toNat = len := by rw [BitVec.toNat_ofNat]; omega
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨hV, hF⟩, dVF⟩ := hc
  have hF' := (Lay.okW_iff.mp hF).1
  refine callP_piece _ 5 rfl hv ok (by decide) (by decide) (by simp [argOk, hV, hF']) (fun s₀ => [V.rgn s₀])
    (fun s₀ => [F.rgn s₀, below (E1 s₀) 20]) hA
    (fun s₀ s₁ hp ⟨s, ha, h, m, hg⟩ => ?_) (fun s₀ s₀' s₁ s₁' hp hp' hq ⟨s, ha, h, m, hg⟩ ⟨s', ha', h', m', hg'⟩ => ?_)
    (fun s₀ hp r hr => ?_) (fun s₀ s₁ s' hp ⟨s, ha, h, m, hg⟩ h' fr post => ?_)
  · have a0 : arg (pushed (argPush 5) s₁).callEntry 0 = V.ptr s₀ := ent_arg hp h (as := [.buf V, .imm len, .imm a, .imm b, .buf F]) (by simp) hg (i := 0) (by simp)
    have a1 : arg (pushed (argPush 5) s₁).callEntry 1 = BitVec.ofNat 32 len := ent_arg hp h (as := [.buf V, .imm len, .imm a, .imm b, .buf F]) (by simp) hg (i := 1) (by simp)
    have a2 : arg (pushed (argPush 5) s₁).callEntry 2 = BitVec.ofNat 32 a := ent_arg hp h (as := [.buf V, .imm len, .imm a, .imm b, .buf F]) (by simp) hg (i := 2) (by simp)
    have a3 : arg (pushed (argPush 5) s₁).callEntry 3 = BitVec.ofNat 32 b := ent_arg hp h (as := [.buf V, .imm len, .imm a, .imm b, .buf F]) (by simp) hg (i := 3) (by simp)
    have a4 : arg (pushed (argPush 5) s₁).callEntry 4 = F.ptr s₀ := ent_arg hp h (as := [.buf V, .imm len, .imm a, .imm b, .buf F]) (by simp) hg (i := 4) (by simp)
    have eA : argAddr (pushed (argPush 5) s₁).callEntry 0 = _ := ent_arg0 h (n := 5) (by decide)
    have eSp : (pushed (argPush 5) s₁).callEntry.gpr .esp = _ := ent_esp h (n := 5) (by decide)
    obtain ⟨rV₁, rV₂, rV₃⟩ := ent_rgn hp hV (n := 5) (K := 16) (by decide)
    obtain ⟨rF₁, rF₂, rF₃⟩ := ent_rgn hp hF' (n := 5) (K := 16) (by decide)
    obtain ⟨rA₂, rA₃⟩ := ent_self hp (n := 5) (K := 16) (by decide)
    have hE := E1_big hp
    have cv := covers_of (s := s₁) (n := 5) (rd := [V.rgn s₀]) (wr := [F.rgn s₀, below (E1 s₀) 20])
      (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        subst hr; exact Buf.within hp hV h.rd h.wr) fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact .inr (Buf.withinW hp hF' (Lay.okW_iff.mp hF).2 h.wr)
        · exact .inl (by rw [h.esp])
    refine ⟨?_, cv.1, cv.2⟩
    generalize he : (pushed (argPush 5) s₁).callEntry = e at a0 a1 a2 a3 a4 eA eSp ⊢
    sig_pre [bitUnpackContract, bitUnpackSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    subst he
    simp only [arg_withRegions, argAddr_withRegions, a0, a1, a2, a3, a4, eA, eSp, al, bl, ll]
    exact ⟨by rw [sub_toNat (by omega)]; omega, by rw [sub_toNat (by omega)]; have := (E1 s₀).isLt; omega,
      rfl, rfl, Buf.disj hp hV hF' dVF, rV₁, rF₁, rV₂, rF₂, rA₂, rV₃, rF₃, rA₃,
      Buf.fit hp hV, Buf.fit hp hF', hab, hl⟩
  · have e₁ : V.ptr s₀ = V.ptr s₀' := hq.t.ptr hV
    have e₂ : F.ptr s₀ = F.ptr s₀' := hq.t.ptr hF'
    refine ⟨by simp only [Buf.rgn, e₁], by simp only [Buf.rgn, e₂, hq.t.E1], ?_⟩
    have a0 : arg (pushed (argPush 5) s₁).callEntry 0 = V.ptr s₀ := ent_arg hp h (as := [.buf V, .imm len, .imm a, .imm b, .buf F]) (by simp) hg (i := 0) (by simp)
    have a1 : arg (pushed (argPush 5) s₁).callEntry 1 = BitVec.ofNat 32 len := ent_arg hp h (as := [.buf V, .imm len, .imm a, .imm b, .buf F]) (by simp) hg (i := 1) (by simp)
    have a2 : arg (pushed (argPush 5) s₁).callEntry 2 = BitVec.ofNat 32 a := ent_arg hp h (as := [.buf V, .imm len, .imm a, .imm b, .buf F]) (by simp) hg (i := 2) (by simp)
    have a3 : arg (pushed (argPush 5) s₁).callEntry 3 = BitVec.ofNat 32 b := ent_arg hp h (as := [.buf V, .imm len, .imm a, .imm b, .buf F]) (by simp) hg (i := 3) (by simp)
    have a4 : arg (pushed (argPush 5) s₁).callEntry 4 = F.ptr s₀ := ent_arg hp h (as := [.buf V, .imm len, .imm a, .imm b, .buf F]) (by simp) hg (i := 4) (by simp)
    have a0' : arg (pushed (argPush 5) s₁').callEntry 0 = V.ptr s₀' := ent_arg hp' h' (as := [.buf V, .imm len, .imm a, .imm b, .buf F]) (by simp) hg' (i := 0) (by simp)
    have a1' : arg (pushed (argPush 5) s₁').callEntry 1 = BitVec.ofNat 32 len := ent_arg hp' h' (as := [.buf V, .imm len, .imm a, .imm b, .buf F]) (by simp) hg' (i := 1) (by simp)
    have a2' : arg (pushed (argPush 5) s₁').callEntry 2 = BitVec.ofNat 32 a := ent_arg hp' h' (as := [.buf V, .imm len, .imm a, .imm b, .buf F]) (by simp) hg' (i := 2) (by simp)
    have a3' : arg (pushed (argPush 5) s₁').callEntry 3 = BitVec.ofNat 32 b := ent_arg hp' h' (as := [.buf V, .imm len, .imm a, .imm b, .buf F]) (by simp) hg' (i := 3) (by simp)
    have a4' : arg (pushed (argPush 5) s₁').callEntry 4 = F.ptr s₀' := ent_arg hp' h' (as := [.buf V, .imm len, .imm a, .imm b, .buf F]) (by simp) hg' (i := 4) (by simp)
    have eSp : (pushed (argPush 5) s₁).callEntry.gpr .esp = _ := ent_esp h (n := 5) (by decide)
    have eSp' : (pushed (argPush 5) s₁').callEntry.gpr .esp = _ := ent_esp h' (n := 5) (by decide)
    generalize he : (pushed (argPush 5) s₁).callEntry = e at a0 a1 a2 a3 a4 eSp ⊢
    generalize he' : (pushed (argPush 5) s₁').callEntry = e' at a0' a1' a2' a3' a4' eSp' ⊢
    sig_pub [bitUnpackContract, bitUnpackSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [arg_withRegions, a0, a1, a2, a3, a4, a0', a1', a2', a3', a4', eSp, eSp', e₁, e₂, hq.t.E1, and_self]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Buf.inW hp hF' (Lay.okW_iff.mp hF).2
    · exact stk_W hp (by decide)
  · obtain ⟨s₂, m₂, post⟩ := post
    have a0 : arg (pushed (argPush 5) s₁).callEntry 0 = V.ptr s₀ := ent_arg hp h (as := [.buf V, .imm len, .imm a, .imm b, .buf F]) (by simp) hg (i := 0) (by simp)
    have a1 : arg (pushed (argPush 5) s₁).callEntry 1 = BitVec.ofNat 32 len := ent_arg hp h (as := [.buf V, .imm len, .imm a, .imm b, .buf F]) (by simp) hg (i := 1) (by simp)
    have a2 : arg (pushed (argPush 5) s₁).callEntry 2 = BitVec.ofNat 32 a := ent_arg hp h (as := [.buf V, .imm len, .imm a, .imm b, .buf F]) (by simp) hg (i := 2) (by simp)
    have a3 : arg (pushed (argPush 5) s₁).callEntry 3 = BitVec.ofNat 32 b := ent_arg hp h (as := [.buf V, .imm len, .imm a, .imm b, .buf F]) (by simp) hg (i := 3) (by simp)
    have a4 : arg (pushed (argPush 5) s₁).callEntry 4 = F.ptr s₀ := ent_arg hp h (as := [.buf V, .imm len, .imm a, .imm b, .buf F]) (by simp) hg (i := 4) (by simp)
    have b₁ : bytesAt (pushed (argPush 5) s₁).callEntry.mem ((V.ptr s₀).setWidth 64) len = bytesAt s.mem (V.addr s₀) len := by
      rw [← m]; exact VG.Proof.MlKem.bytesAt_congr (ent_bytes hp h (n := 5) (by decide) hV)
    generalize he : (pushed (argPush 5) s₁).callEntry = e at a0 a1 a2 a3 a4 post
    sig_post [bitUnpackContract, bitUnpackSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at post
    subst he
    simp only [arg_withRegions, a0, a1, a2, a3, a4, m₂, al, bl, ll] at post
    rw [b₁] at post
    exact hQ s₀ s s' hp ha h' (fr80 (by decide) (by have := ok.stk; omega) hp (m ▸ fr)) post

/-- `y ← HintBitPack(h)`, of the hint of `k` polynomials `h`. -/
theorem hbp_piece {nm : String} {c : Prog isa} (hv : Verified X86.target c (hintBitPackContract X86.abi 16))
    (ok : COk c) (w k : Nat) (hwk : (w, k) ∈ hintParams) (ha ho oa oo : Nat)
    (hc : ((Y p).ok ⟨ha, ho, 1024 * k⟩ && (Y p).okW ⟨oa, oo, w + k⟩ && (Y p).sep ⟨ha, ho, 1024 * k⟩ ⟨oa, oo, w + k⟩) = true)
    (hA : ∀ s₀ s, TPre (Y p) s₀ → A s₀ s → Ctx (Y p) s₀ s ∧ hintOnes (hintAt s.mem (Buf.addr s₀ ⟨ha, ho, 1024 * k⟩) k) ≤ w)
    (hleak : ∀ s₀ s₀' s s', TPre (Y p) s₀ → TPre (Y p) s₀' → SPub p s₀ s₀' → A s₀ s → A s₀' s' →
      (List.range (256 * k)).map (fun i => (coeffAt s.mem (Buf.addr s₀ ⟨ha, ho, 1024 * k⟩) i).toNat) =
        (List.range (256 * k)).map (fun i => (coeffAt s'.mem (Buf.addr s₀' ⟨ha, ho, 1024 * k⟩) i).toNat))
    (hQ : ∀ s₀ s s', TPre (Y p) s₀ → A s₀ s → Ctx (Y p) s₀ s' → Frame (FR s₀ [⟨oa, oo, w + k⟩] 80) s.mem s'.mem →
      bytesAt s'.mem (Buf.addr s₀ ⟨oa, oo, w + k⟩) (w + k) =
        hintBitPack w k (hintAt s.mem (Buf.addr s₀ ⟨ha, ho, 1024 * k⟩) k) → B s₀ s') :
    SP p A B (callP nm c [.buf ⟨ha, ho, 1024 * k⟩, .imm (256 * k), .imm w, .buf ⟨oa, oo, w + k⟩, .imm (w + k)]) := by
  set H : Buf := ⟨ha, ho, 1024 * k⟩
  set O : Buf := ⟨oa, oo, w + k⟩
  have hb : w < 100 ∧ k ≤ 8 := by
    simp only [hintParams, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hwk
    rcases hwk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  have wl : (BitVec.ofNat 32 w).toNat = w := by rw [BitVec.toNat_ofNat]; omega
  have kl : (BitVec.ofNat 32 (256 * k)).toNat = 256 * k := by rw [BitVec.toNat_ofNat]; omega
  have ll : (BitVec.ofNat 32 (w + k)).toNat = w + k := by rw [BitVec.toNat_ofNat]; omega
  have ek : w + k - w = k := by omega
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨hH, hO⟩, dHO⟩ := hc
  have hO' := (Lay.okW_iff.mp hO).1
  refine callP_piece _ 5 rfl hv ok (by decide) (by decide) (by simp [argOk, hH, hO']) (fun s₀ => [H.rgn s₀])
    (fun s₀ => [O.rgn s₀, below (E1 s₀) 20]) (fun s₀ s hp ha => (hA s₀ s hp ha).1)
    (fun s₀ s₁ hp ⟨s, ha, h, m, hg⟩ => ?_) (fun s₀ s₀' s₁ s₁' hp hp' hq ⟨s, ha, h, m, hg⟩ ⟨s', ha', h', m', hg'⟩ => ?_)
    (fun s₀ hp r hr => ?_) (fun s₀ s₁ s' hp ⟨s, ha, h, m, hg⟩ h' fr post => ?_)
  · have a0 : arg (pushed (argPush 5) s₁).callEntry 0 = H.ptr s₀ := ent_arg hp h (as := [.buf H, .imm (256 * k), .imm w, .buf O, .imm (w + k)]) (by simp) hg (i := 0) (by simp)
    have a1 : arg (pushed (argPush 5) s₁).callEntry 1 = BitVec.ofNat 32 (256 * k) := ent_arg hp h (as := [.buf H, .imm (256 * k), .imm w, .buf O, .imm (w + k)]) (by simp) hg (i := 1) (by simp)
    have a2 : arg (pushed (argPush 5) s₁).callEntry 2 = BitVec.ofNat 32 w := ent_arg hp h (as := [.buf H, .imm (256 * k), .imm w, .buf O, .imm (w + k)]) (by simp) hg (i := 2) (by simp)
    have a3 : arg (pushed (argPush 5) s₁).callEntry 3 = O.ptr s₀ := ent_arg hp h (as := [.buf H, .imm (256 * k), .imm w, .buf O, .imm (w + k)]) (by simp) hg (i := 3) (by simp)
    have a4 : arg (pushed (argPush 5) s₁).callEntry 4 = BitVec.ofNat 32 (w + k) := ent_arg hp h (as := [.buf H, .imm (256 * k), .imm w, .buf O, .imm (w + k)]) (by simp) hg (i := 4) (by simp)
    have eA : argAddr (pushed (argPush 5) s₁).callEntry 0 = _ := ent_arg0 h (n := 5) (by decide)
    have eSp : (pushed (argPush 5) s₁).callEntry.gpr .esp = _ := ent_esp h (n := 5) (by decide)
    obtain ⟨rH₁, rH₂, rH₃⟩ := ent_rgn hp hH (n := 5) (K := 16) (by decide)
    obtain ⟨rO₁, rO₂, rO₃⟩ := ent_rgn hp hO' (n := 5) (K := 16) (by decide)
    obtain ⟨rA₂, rA₃⟩ := ent_self hp (n := 5) (K := 16) (by decide)
    have hE := E1_big hp
    have cv := covers_of (s := s₁) (n := 5) (rd := [H.rgn s₀]) (wr := [O.rgn s₀, below (E1 s₀) 20])
      (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        subst hr; exact Buf.within hp hH h.rd h.wr) fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact .inr (Buf.withinW hp hO' (Lay.okW_iff.mp hO).2 h.wr)
        · exact .inl (by rw [h.esp])
    refine ⟨?_, cv.1, cv.2⟩
    generalize he : (pushed (argPush 5) s₁).callEntry = e at a0 a1 a2 a3 a4 eA eSp ⊢
    sig_pre [hintBitPackContract, hintBitPackSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    subst he
    simp only [arg_withRegions, argAddr_withRegions, a0, a1, a2, a3, a4, eA, eSp, wl, kl, ll, ek]
    rw [show 256 * k * 4 = 1024 * k by omega]
    refine ⟨by rw [sub_toNat (by omega)]; omega, by rw [sub_toNat (by omega)]; have := (E1 s₀).isLt; omega,
      rfl, rfl, Buf.disj hp hH hO' dHO, rH₁, rO₁, rH₂, rO₂, rA₂, rH₃, rO₃, rA₃,
      Buf.fit hp hH, Buf.fit hp hO', hwk, by omega, trivial, ?_⟩
    rw [hintAt_congr (ent_bytes hp h (n := 5) (by decide) hH), m]; exact (hA s₀ s hp ha).2
  · have e₁ : H.ptr s₀ = H.ptr s₀' := hq.t.ptr hH
    have e₂ : O.ptr s₀ = O.ptr s₀' := hq.t.ptr hO'
    refine ⟨by simp only [Buf.rgn, e₁], by simp only [Buf.rgn, e₂, hq.t.E1], ?_⟩
    have a0 : arg (pushed (argPush 5) s₁).callEntry 0 = H.ptr s₀ := ent_arg hp h (as := [.buf H, .imm (256 * k), .imm w, .buf O, .imm (w + k)]) (by simp) hg (i := 0) (by simp)
    have a1 : arg (pushed (argPush 5) s₁).callEntry 1 = BitVec.ofNat 32 (256 * k) := ent_arg hp h (as := [.buf H, .imm (256 * k), .imm w, .buf O, .imm (w + k)]) (by simp) hg (i := 1) (by simp)
    have a2 : arg (pushed (argPush 5) s₁).callEntry 2 = BitVec.ofNat 32 w := ent_arg hp h (as := [.buf H, .imm (256 * k), .imm w, .buf O, .imm (w + k)]) (by simp) hg (i := 2) (by simp)
    have a3 : arg (pushed (argPush 5) s₁).callEntry 3 = O.ptr s₀ := ent_arg hp h (as := [.buf H, .imm (256 * k), .imm w, .buf O, .imm (w + k)]) (by simp) hg (i := 3) (by simp)
    have a4 : arg (pushed (argPush 5) s₁).callEntry 4 = BitVec.ofNat 32 (w + k) := ent_arg hp h (as := [.buf H, .imm (256 * k), .imm w, .buf O, .imm (w + k)]) (by simp) hg (i := 4) (by simp)
    have a0' : arg (pushed (argPush 5) s₁').callEntry 0 = H.ptr s₀' := ent_arg hp' h' (as := [.buf H, .imm (256 * k), .imm w, .buf O, .imm (w + k)]) (by simp) hg' (i := 0) (by simp)
    have a1' : arg (pushed (argPush 5) s₁').callEntry 1 = BitVec.ofNat 32 (256 * k) := ent_arg hp' h' (as := [.buf H, .imm (256 * k), .imm w, .buf O, .imm (w + k)]) (by simp) hg' (i := 1) (by simp)
    have a2' : arg (pushed (argPush 5) s₁').callEntry 2 = BitVec.ofNat 32 w := ent_arg hp' h' (as := [.buf H, .imm (256 * k), .imm w, .buf O, .imm (w + k)]) (by simp) hg' (i := 2) (by simp)
    have a3' : arg (pushed (argPush 5) s₁').callEntry 3 = O.ptr s₀' := ent_arg hp' h' (as := [.buf H, .imm (256 * k), .imm w, .buf O, .imm (w + k)]) (by simp) hg' (i := 3) (by simp)
    have a4' : arg (pushed (argPush 5) s₁').callEntry 4 = BitVec.ofNat 32 (w + k) := ent_arg hp' h' (as := [.buf H, .imm (256 * k), .imm w, .buf O, .imm (w + k)]) (by simp) hg' (i := 4) (by simp)
    have eSp : (pushed (argPush 5) s₁).callEntry.gpr .esp = _ := ent_esp h (n := 5) (by decide)
    have eSp' : (pushed (argPush 5) s₁').callEntry.gpr .esp = _ := ent_esp h' (n := 5) (by decide)
    have c₁ := coeffs_congr (len := 256 * k) (fun x hx => ent_bytes hp h (n := 5) (by decide) hH x (by show x < 1024 * k; omega))
    have c₂ := coeffs_congr (len := 256 * k) (fun x hx => ent_bytes hp' h' (n := 5) (by decide) hH x (by show x < 1024 * k; omega))
    have key : (List.range (256 * k)).map (fun i => (coeffAt (pushed (argPush 5) s₁).callEntry.mem (H.addr s₀) i).toNat) =
        (List.range (256 * k)).map (fun i => (coeffAt (pushed (argPush 5) s₁').callEntry.mem (H.addr s₀') i).toNat) := by
      rw [c₁, c₂, m, m']; exact hleak s₀ s₀' s s' hp hp' hq ha ha'
    simp only [Buf.addr, e₁] at key
    generalize he : (pushed (argPush 5) s₁).callEntry = e at a0 a1 a2 a3 a4 eSp key ⊢
    generalize he' : (pushed (argPush 5) s₁').callEntry = e' at a0' a1' a2' a3' a4' eSp' key ⊢
    sig_pub [hintBitPackContract, hintBitPackSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [arg_withRegions, a0, a1, a2, a3, a4, a0', a1', a2', a3', a4', eSp, eSp', e₁, e₂, hq.t.E1, and_self,
      kl, key]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Buf.inW hp hO' (Lay.okW_iff.mp hO).2
    · exact stk_W hp (by decide)
  · obtain ⟨s₂, m₂, post⟩ := post
    have a0 : arg (pushed (argPush 5) s₁).callEntry 0 = H.ptr s₀ := ent_arg hp h (as := [.buf H, .imm (256 * k), .imm w, .buf O, .imm (w + k)]) (by simp) hg (i := 0) (by simp)
    have a1 : arg (pushed (argPush 5) s₁).callEntry 1 = BitVec.ofNat 32 (256 * k) := ent_arg hp h (as := [.buf H, .imm (256 * k), .imm w, .buf O, .imm (w + k)]) (by simp) hg (i := 1) (by simp)
    have a2 : arg (pushed (argPush 5) s₁).callEntry 2 = BitVec.ofNat 32 w := ent_arg hp h (as := [.buf H, .imm (256 * k), .imm w, .buf O, .imm (w + k)]) (by simp) hg (i := 2) (by simp)
    have a3 : arg (pushed (argPush 5) s₁).callEntry 3 = O.ptr s₀ := ent_arg hp h (as := [.buf H, .imm (256 * k), .imm w, .buf O, .imm (w + k)]) (by simp) hg (i := 3) (by simp)
    have a4 : arg (pushed (argPush 5) s₁).callEntry 4 = BitVec.ofNat 32 (w + k) := ent_arg hp h (as := [.buf H, .imm (256 * k), .imm w, .buf O, .imm (w + k)]) (by simp) hg (i := 4) (by simp)
    generalize he : (pushed (argPush 5) s₁).callEntry = e at a0 a1 a2 a3 a4 post
    sig_post [hintBitPackContract, hintBitPackSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at post
    subst he
    simp only [arg_withRegions, a0, a2, a3, a4, m₂, wl, ll, ek] at post
    rw [hintAt_congr (ent_bytes hp h (n := 5) (by decide) hH), m] at post
    exact hQ s₀ s s' hp ha h' (fr80 (by decide) (by have := ok.stk; omega) hp (m ▸ fr)) post

end VG.Proof.MlDsa.X86.Sign
