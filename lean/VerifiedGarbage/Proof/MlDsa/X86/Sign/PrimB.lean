import VerifiedGarbage.Proof.MlDsa.X86.Sign.Prims

/-!
# ML-DSA signing on x86 (32-bit): calls of the samplers

`RejNTTPoly` (`rej_piece`), a polynomial of `ExpandMask` (`mask_piece`) and
`SampleInBall` (`ball_piece`); the first and the last return whether they
succeeded, as a function of their seeds, which they may leak.
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

/-- `a ← RejNTTPoly(seed)`, returning 1 or 0 in `eax`. -/
theorem rej_piece {F : List Byte → Bool} {nm : String} {c : Prog isa} (hv : Verified X86.target c (rejK F))
    (ok : COk c) (da dO aa ao ca co : Nat)
    (hc : ((Y p).ok ⟨da, dO, 34⟩ && (Y p).okW ⟨aa, ao, 1024⟩ && (Y p).okW ⟨ca, co, 2048⟩ &&
      (Y p).sep ⟨da, dO, 34⟩ ⟨aa, ao, 1024⟩ && (Y p).sep ⟨da, dO, 34⟩ ⟨ca, co, 2048⟩ &&
      (Y p).sep ⟨aa, ao, 1024⟩ ⟨ca, co, 2048⟩) = true)
    (hA : ∀ s₀ s, TPre (Y p) s₀ → A s₀ s → Ctx (Y p) s₀ s)
    (hseed : ∀ s₀ s₀' s s', TPre (Y p) s₀ → TPre (Y p) s₀' → SPub p s₀ s₀' → A s₀ s → A s₀' s' →
      bytesAt s.mem (Buf.addr s₀ ⟨da, dO, 34⟩) 34 = bytesAt s'.mem (Buf.addr s₀' ⟨da, dO, 34⟩) 34)
    (hQ : ∀ s₀ s s', TPre (Y p) s₀ → A s₀ s → Ctx (Y p) s₀ s' →
      Frame (FR s₀ [⟨aa, ao, 1024⟩, ⟨ca, co, 2048⟩] 80) s.mem s'.mem →
      s'.gpr .eax = (if F (bytesAt s.mem (Buf.addr s₀ ⟨da, dO, 34⟩) 34) then 1 else 0) →
      (s'.gpr .eax = 1 → Reduced s'.mem (Buf.addr s₀ ⟨aa, ao, 1024⟩)) →
      Outcome (fun b => rejNTTPoly b.rejNTT (bytesAt s.mem (Buf.addr s₀ ⟨da, dO, 34⟩) 34)) (s'.gpr .eax)
        (polyAt s'.mem (Buf.addr s₀ ⟨aa, ao, 1024⟩)) → B s₀ s') :
    SP p A B (callPR nm c [.buf ⟨da, dO, 34⟩, .buf ⟨aa, ao, 1024⟩, .buf ⟨ca, co, 2048⟩]) := by
  set D : Buf := ⟨da, dO, 34⟩
  set R : Buf := ⟨aa, ao, 1024⟩
  set C : Buf := ⟨ca, co, 2048⟩
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨hD, hR⟩, hC⟩, dDR⟩, dDC⟩, dRC⟩ := hc
  have hR' := (Lay.okW_iff.mp hR).1
  have hC' := (Lay.okW_iff.mp hC).1
  refine callPR_piece _ 3 rfl hv ok (by decide) (by decide) (by simp [argOk, hD, hR', hC']) (fun s₀ => [D.rgn s₀])
    (fun s₀ => [R.rgn s₀, C.rgn s₀, below (E1 s₀) 12]) hA
    (fun s₀ s₁ hp ⟨s, ha, h, m, hg⟩ => ?_) (fun s₀ s₀' s₁ s₁' hp hp' hq ⟨s, ha, h, m, hg⟩ ⟨s', ha', h', m', hg'⟩ => ?_)
    (fun s₀ hp r hr => ?_) (fun s₀ s₁ s' hp ⟨s, ha, h, m, hg⟩ h' fr post => ?_)
  · have a0 : arg (pushed (argPush 3) s₁).callEntry 0 = D.ptr s₀ := ent_arg hp h (as := [.buf D, .buf R, .buf C]) (by simp) hg (i := 0) (by simp)
    have a1 : arg (pushed (argPush 3) s₁).callEntry 1 = R.ptr s₀ := ent_arg hp h (as := [.buf D, .buf R, .buf C]) (by simp) hg (i := 1) (by simp)
    have a2 : arg (pushed (argPush 3) s₁).callEntry 2 = C.ptr s₀ := ent_arg hp h (as := [.buf D, .buf R, .buf C]) (by simp) hg (i := 2) (by simp)
    have eA : argAddr (pushed (argPush 3) s₁).callEntry 0 = _ := ent_arg0 h (n := 3) (by decide)
    have eSp : (pushed (argPush 3) s₁).callEntry.gpr .esp = _ := ent_esp h (n := 3) (by decide)
    obtain ⟨rD₁, rD₂, rD₃⟩ := ent_rgn hp hD (n := 3) (K := 56) (by decide)
    obtain ⟨rR₁, rR₂, rR₃⟩ := ent_rgn hp hR' (n := 3) (K := 56) (by decide)
    obtain ⟨rC₁, rC₂, rC₃⟩ := ent_rgn hp hC' (n := 3) (K := 56) (by decide)
    obtain ⟨rA₂, rA₃⟩ := ent_self hp (n := 3) (K := 56) (by decide)
    have hE := E1_big hp
    have cv := covers_of (s := s₁) (n := 3) (rd := [D.rgn s₀]) (wr := [R.rgn s₀, C.rgn s₀, below (E1 s₀) 12])
      (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        subst hr; exact Buf.within hp hD h.rd h.wr) fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact .inr (Buf.withinW hp hR' (Lay.okW_iff.mp hR).2 h.wr)
        · exact .inr (Buf.withinW hp hC' (Lay.okW_iff.mp hC).2 h.wr)
        · exact .inl (by rw [h.esp])
    refine ⟨?_, cv.1, cv.2⟩
    generalize he : (pushed (argPush 3) s₁).callEntry = e at a0 a1 a2 eA eSp ⊢
    sig_pre [rejK, withRet, rejNTTContract, rejNTTSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    subst he
    simp only [arg_withRegions, argAddr_withRegions, a0, a1, a2, eA, eSp]
    exact ⟨by rw [sub_toNat (by omega)]; omega, by rw [sub_toNat (by omega)]; have := (E1 s₀).isLt; omega,
      rfl, rfl, Buf.disj hp hD hR' dDR, Buf.disj hp hD hC' dDC, rD₁, Buf.disj hp hR' hC' dRC, rR₁, rC₁,
      rD₂, rR₂, rC₂, rA₂, rD₃, rR₃, rC₃, rA₃, Buf.fit hp hD, Buf.fit hp hR', Buf.fit hp hC'⟩
  · have e₁ : D.ptr s₀ = D.ptr s₀' := hq.t.ptr hD
    have e₂ : R.ptr s₀ = R.ptr s₀' := hq.t.ptr hR'
    have e₃ : C.ptr s₀ = C.ptr s₀' := hq.t.ptr hC'
    refine ⟨by simp only [Buf.rgn, e₁], by simp only [Buf.rgn, e₂, e₃, hq.t.E1], ?_⟩
    have a0 : arg (pushed (argPush 3) s₁).callEntry 0 = D.ptr s₀ := ent_arg hp h (as := [.buf D, .buf R, .buf C]) (by simp) hg (i := 0) (by simp)
    have a1 : arg (pushed (argPush 3) s₁).callEntry 1 = R.ptr s₀ := ent_arg hp h (as := [.buf D, .buf R, .buf C]) (by simp) hg (i := 1) (by simp)
    have a2 : arg (pushed (argPush 3) s₁).callEntry 2 = C.ptr s₀ := ent_arg hp h (as := [.buf D, .buf R, .buf C]) (by simp) hg (i := 2) (by simp)
    have a0' : arg (pushed (argPush 3) s₁').callEntry 0 = D.ptr s₀' := ent_arg hp' h' (as := [.buf D, .buf R, .buf C]) (by simp) hg' (i := 0) (by simp)
    have a1' : arg (pushed (argPush 3) s₁').callEntry 1 = R.ptr s₀' := ent_arg hp' h' (as := [.buf D, .buf R, .buf C]) (by simp) hg' (i := 1) (by simp)
    have a2' : arg (pushed (argPush 3) s₁').callEntry 2 = C.ptr s₀' := ent_arg hp' h' (as := [.buf D, .buf R, .buf C]) (by simp) hg' (i := 2) (by simp)
    have eSp : (pushed (argPush 3) s₁).callEntry.gpr .esp = _ := ent_esp h (n := 3) (by decide)
    have eSp' : (pushed (argPush 3) s₁').callEntry.gpr .esp = _ := ent_esp h' (n := 3) (by decide)
    have b₁ := VG.Proof.MlKem.bytesAt_congr (ent_bytes hp h (n := 3) (by decide) hD)
    have b₂ := VG.Proof.MlKem.bytesAt_congr (ent_bytes hp' h' (n := 3) (by decide) hD)
    have key : bytesAt (pushed (argPush 3) s₁).callEntry.mem (D.addr s₀) 34 =
        bytesAt (pushed (argPush 3) s₁').callEntry.mem (D.addr s₀') 34 := by
      rw [b₁, b₂, m, m']; exact hseed s₀ s₀' s s' hp hp' hq ha ha'
    simp only [Buf.addr, e₁] at key
    generalize he : (pushed (argPush 3) s₁).callEntry = e at a0 a1 a2 eSp key ⊢
    generalize he' : (pushed (argPush 3) s₁').callEntry = e' at a0' a1' a2' eSp' key ⊢
    sig_pub [rejK, withRet, rejNTTContract, rejNTTSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [arg_withRegions, a0, a1, a2, a0', a1', a2', eSp, eSp', e₁, e₂, e₃, hq.t.E1, and_self, key]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Buf.inW hp hR' (Lay.okW_iff.mp hR).2
    · exact Buf.inW hp hC' (Lay.okW_iff.mp hC).2
    · exact stk_W hp (by decide)
  · obtain ⟨s₂, m₂, g₂, post⟩ := post
    have a0 : arg (pushed (argPush 3) s₁).callEntry 0 = D.ptr s₀ := ent_arg hp h (as := [.buf D, .buf R, .buf C]) (by simp) hg (i := 0) (by simp)
    have a1 : arg (pushed (argPush 3) s₁).callEntry 1 = R.ptr s₀ := ent_arg hp h (as := [.buf D, .buf R, .buf C]) (by simp) hg (i := 1) (by simp)
    have b₁ : bytesAt (pushed (argPush 3) s₁).callEntry.mem ((D.ptr s₀).setWidth 64) 34 = bytesAt s.mem (D.addr s₀) 34 := by
      rw [← m]; exact VG.Proof.MlKem.bytesAt_congr (ent_bytes hp h (n := 3) (by decide) hD)
    generalize he : (pushed (argPush 3) s₁).callEntry = e at a0 a1 post
    sig_post [rejK, withRet, rejNTTContract, rejNTTSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at post
    subst he
    simp only [arg_withRegions, a0, a1, m₂, sw32, g₂] at post
    rw [b₁] at post
    exact hQ s₀ s s' hp ha h' (fr80 (by decide) (by have := ok.stk; omega) hp (m ▸ fr)) post.2.2 post.1 post.2.1

/-- `a ←` a polynomial of `ExpandMask`, from the 66 bytes `seed`. -/
theorem mask_piece {nm : String} {c : Prog isa} (hv : Verified X86.target c (expandMaskContract X86.abi 56))
    (ok : COk c) (g1 : Nat) (hg1 : g1 = 2 ^ 17 ∨ g1 = 2 ^ 19) (da dO aa ao ca co : Nat)
    (hc : ((Y p).ok ⟨da, dO, 66⟩ && (Y p).okW ⟨aa, ao, 1024⟩ && (Y p).okW ⟨ca, co, 2048⟩ &&
      (Y p).sep ⟨da, dO, 66⟩ ⟨aa, ao, 1024⟩ && (Y p).sep ⟨da, dO, 66⟩ ⟨ca, co, 2048⟩ &&
      (Y p).sep ⟨aa, ao, 1024⟩ ⟨ca, co, 2048⟩) = true)
    (hA : ∀ s₀ s, TPre (Y p) s₀ → A s₀ s → Ctx (Y p) s₀ s)
    (hQ : ∀ s₀ s s', TPre (Y p) s₀ → A s₀ s → Ctx (Y p) s₀ s' →
      Frame (FR s₀ [⟨aa, ao, 1024⟩, ⟨ca, co, 2048⟩] 80) s.mem s'.mem →
      PolyIs s'.mem (Buf.addr s₀ ⟨aa, ao, 1024⟩)
        (toRq (bitUnpack (H (bytesAt s.mem (Buf.addr s₀ ⟨da, dO, 66⟩) 66) (32 * (1 + bitlen (g1 - 1)))) (g1 - 1) g1)) →
      B s₀ s') :
    SP p A B (callP nm c [.buf ⟨da, dO, 66⟩, .imm g1, .buf ⟨aa, ao, 1024⟩, .buf ⟨ca, co, 2048⟩]) := by
  set D : Buf := ⟨da, dO, 66⟩
  set R : Buf := ⟨aa, ao, 1024⟩
  set C : Buf := ⟨ca, co, 2048⟩
  have g1l : (BitVec.ofNat 32 g1).toNat = g1 := by rcases hg1 with rfl | rfl <;> rfl
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨hD, hR⟩, hC⟩, dDR⟩, dDC⟩, dRC⟩ := hc
  have hR' := (Lay.okW_iff.mp hR).1
  have hC' := (Lay.okW_iff.mp hC).1
  refine callP_piece _ 4 rfl hv ok (by decide) (by decide) (by simp [argOk, hD, hR', hC']) (fun s₀ => [D.rgn s₀])
    (fun s₀ => [R.rgn s₀, C.rgn s₀, below (E1 s₀) 16]) hA
    (fun s₀ s₁ hp ⟨s, ha, h, m, hg⟩ => ?_) (fun s₀ s₀' s₁ s₁' hp hp' hq ⟨s, ha, h, m, hg⟩ ⟨s', ha', h', m', hg'⟩ => ?_)
    (fun s₀ hp r hr => ?_) (fun s₀ s₁ s' hp ⟨s, ha, h, m, hg⟩ h' fr post => ?_)
  · have a0 : arg (pushed (argPush 4) s₁).callEntry 0 = D.ptr s₀ := ent_arg hp h (as := [.buf D, .imm g1, .buf R, .buf C]) (by simp) hg (i := 0) (by simp)
    have a1 : arg (pushed (argPush 4) s₁).callEntry 1 = BitVec.ofNat 32 g1 := ent_arg hp h (as := [.buf D, .imm g1, .buf R, .buf C]) (by simp) hg (i := 1) (by simp)
    have a2 : arg (pushed (argPush 4) s₁).callEntry 2 = R.ptr s₀ := ent_arg hp h (as := [.buf D, .imm g1, .buf R, .buf C]) (by simp) hg (i := 2) (by simp)
    have a3 : arg (pushed (argPush 4) s₁).callEntry 3 = C.ptr s₀ := ent_arg hp h (as := [.buf D, .imm g1, .buf R, .buf C]) (by simp) hg (i := 3) (by simp)
    have eA : argAddr (pushed (argPush 4) s₁).callEntry 0 = _ := ent_arg0 h (n := 4) (by decide)
    have eSp : (pushed (argPush 4) s₁).callEntry.gpr .esp = _ := ent_esp h (n := 4) (by decide)
    obtain ⟨rD₁, rD₂, rD₃⟩ := ent_rgn hp hD (n := 4) (K := 56) (by decide)
    obtain ⟨rR₁, rR₂, rR₃⟩ := ent_rgn hp hR' (n := 4) (K := 56) (by decide)
    obtain ⟨rC₁, rC₂, rC₃⟩ := ent_rgn hp hC' (n := 4) (K := 56) (by decide)
    obtain ⟨rA₂, rA₃⟩ := ent_self hp (n := 4) (K := 56) (by decide)
    have hE := E1_big hp
    have cv := covers_of (s := s₁) (n := 4) (rd := [D.rgn s₀]) (wr := [R.rgn s₀, C.rgn s₀, below (E1 s₀) 16])
      (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        subst hr; exact Buf.within hp hD h.rd h.wr) fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact .inr (Buf.withinW hp hR' (Lay.okW_iff.mp hR).2 h.wr)
        · exact .inr (Buf.withinW hp hC' (Lay.okW_iff.mp hC).2 h.wr)
        · exact .inl (by rw [h.esp])
    refine ⟨?_, cv.1, cv.2⟩
    generalize he : (pushed (argPush 4) s₁).callEntry = e at a0 a1 a2 a3 eA eSp ⊢
    sig_pre [expandMaskContract, expandMaskSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    subst he
    simp only [arg_withRegions, argAddr_withRegions, a0, a1, a2, a3, eA, eSp, g1l]
    exact ⟨by rw [sub_toNat (by omega)]; omega, by rw [sub_toNat (by omega)]; have := (E1 s₀).isLt; omega,
      rfl, rfl, Buf.disj hp hD hR' dDR, Buf.disj hp hD hC' dDC, rD₁, Buf.disj hp hR' hC' dRC, rR₁, rC₁,
      rD₂, rR₂, rC₂, rA₂, rD₃, rR₃, rC₃, rA₃, Buf.fit hp hD, Buf.fit hp hR', Buf.fit hp hC', hg1⟩
  · have e₁ : D.ptr s₀ = D.ptr s₀' := hq.t.ptr hD
    have e₂ : R.ptr s₀ = R.ptr s₀' := hq.t.ptr hR'
    have e₃ : C.ptr s₀ = C.ptr s₀' := hq.t.ptr hC'
    refine ⟨by simp only [Buf.rgn, e₁], by simp only [Buf.rgn, e₂, e₃, hq.t.E1], ?_⟩
    have a0 : arg (pushed (argPush 4) s₁).callEntry 0 = D.ptr s₀ := ent_arg hp h (as := [.buf D, .imm g1, .buf R, .buf C]) (by simp) hg (i := 0) (by simp)
    have a1 : arg (pushed (argPush 4) s₁).callEntry 1 = BitVec.ofNat 32 g1 := ent_arg hp h (as := [.buf D, .imm g1, .buf R, .buf C]) (by simp) hg (i := 1) (by simp)
    have a2 : arg (pushed (argPush 4) s₁).callEntry 2 = R.ptr s₀ := ent_arg hp h (as := [.buf D, .imm g1, .buf R, .buf C]) (by simp) hg (i := 2) (by simp)
    have a3 : arg (pushed (argPush 4) s₁).callEntry 3 = C.ptr s₀ := ent_arg hp h (as := [.buf D, .imm g1, .buf R, .buf C]) (by simp) hg (i := 3) (by simp)
    have a0' : arg (pushed (argPush 4) s₁').callEntry 0 = D.ptr s₀' := ent_arg hp' h' (as := [.buf D, .imm g1, .buf R, .buf C]) (by simp) hg' (i := 0) (by simp)
    have a1' : arg (pushed (argPush 4) s₁').callEntry 1 = BitVec.ofNat 32 g1 := ent_arg hp' h' (as := [.buf D, .imm g1, .buf R, .buf C]) (by simp) hg' (i := 1) (by simp)
    have a2' : arg (pushed (argPush 4) s₁').callEntry 2 = R.ptr s₀' := ent_arg hp' h' (as := [.buf D, .imm g1, .buf R, .buf C]) (by simp) hg' (i := 2) (by simp)
    have a3' : arg (pushed (argPush 4) s₁').callEntry 3 = C.ptr s₀' := ent_arg hp' h' (as := [.buf D, .imm g1, .buf R, .buf C]) (by simp) hg' (i := 3) (by simp)
    have eSp : (pushed (argPush 4) s₁).callEntry.gpr .esp = _ := ent_esp h (n := 4) (by decide)
    have eSp' : (pushed (argPush 4) s₁').callEntry.gpr .esp = _ := ent_esp h' (n := 4) (by decide)
    generalize he : (pushed (argPush 4) s₁).callEntry = e at a0 a1 a2 a3 eSp ⊢
    generalize he' : (pushed (argPush 4) s₁').callEntry = e' at a0' a1' a2' a3' eSp' ⊢
    sig_pub [expandMaskContract, expandMaskSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [arg_withRegions, a0, a1, a2, a3, a0', a1', a2', a3', eSp, eSp', e₁, e₂, e₃, hq.t.E1, and_self]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Buf.inW hp hR' (Lay.okW_iff.mp hR).2
    · exact Buf.inW hp hC' (Lay.okW_iff.mp hC).2
    · exact stk_W hp (by decide)
  · obtain ⟨s₂, m₂, post⟩ := post
    have a0 : arg (pushed (argPush 4) s₁).callEntry 0 = D.ptr s₀ := ent_arg hp h (as := [.buf D, .imm g1, .buf R, .buf C]) (by simp) hg (i := 0) (by simp)
    have a1 : arg (pushed (argPush 4) s₁).callEntry 1 = BitVec.ofNat 32 g1 := ent_arg hp h (as := [.buf D, .imm g1, .buf R, .buf C]) (by simp) hg (i := 1) (by simp)
    have a2 : arg (pushed (argPush 4) s₁).callEntry 2 = R.ptr s₀ := ent_arg hp h (as := [.buf D, .imm g1, .buf R, .buf C]) (by simp) hg (i := 2) (by simp)
    have b₁ : bytesAt (pushed (argPush 4) s₁).callEntry.mem ((D.ptr s₀).setWidth 64) 66 = bytesAt s.mem (D.addr s₀) 66 := by
      rw [← m]; exact VG.Proof.MlKem.bytesAt_congr (ent_bytes hp h (n := 4) (by decide) hD)
    generalize he : (pushed (argPush 4) s₁).callEntry = e at a0 a1 a2 post
    sig_post [expandMaskContract, expandMaskSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at post
    subst he
    simp only [arg_withRegions, a0, a1, a2, m₂, g1l] at post
    rw [b₁] at post
    exact hQ s₀ s s' hp ha h' (fr80 (by decide) (by have := ok.stk; omega) hp (m ▸ fr)) post

/-- `c ← SampleInBall(c̃)`, returning 1 or 0 in `eax`, with the `len` bytes `c̃`. -/
theorem ball_piece {F : Nat → List Byte → Bool} {nm : String} {c : Prog isa} (hv : Verified X86.target c (ballK F))
    (ok : COk c) (len tau : Nat) (hlt : (len, tau) ∈ ballParams) (da dO aa ao ca co : Nat)
    (hc : ((Y p).ok ⟨da, dO, len⟩ && (Y p).okW ⟨aa, ao, 1024⟩ && (Y p).okW ⟨ca, co, 2048⟩ &&
      (Y p).sep ⟨da, dO, len⟩ ⟨aa, ao, 1024⟩ && (Y p).sep ⟨da, dO, len⟩ ⟨ca, co, 2048⟩ &&
      (Y p).sep ⟨aa, ao, 1024⟩ ⟨ca, co, 2048⟩) = true)
    (hA : ∀ s₀ s, TPre (Y p) s₀ → A s₀ s → Ctx (Y p) s₀ s)
    (hseed : ∀ s₀ s₀' s s', TPre (Y p) s₀ → TPre (Y p) s₀' → SPub p s₀ s₀' → A s₀ s → A s₀' s' →
      bytesAt s.mem (Buf.addr s₀ ⟨da, dO, len⟩) len = bytesAt s'.mem (Buf.addr s₀' ⟨da, dO, len⟩) len)
    (hQ : ∀ s₀ s s', TPre (Y p) s₀ → A s₀ s → Ctx (Y p) s₀ s' →
      Frame (FR s₀ [⟨aa, ao, 1024⟩, ⟨ca, co, 2048⟩] 80) s.mem s'.mem →
      s'.gpr .eax = (if F tau (bytesAt s.mem (Buf.addr s₀ ⟨da, dO, len⟩) len) then 1 else 0) →
      (s'.gpr .eax = 1 → Reduced s'.mem (Buf.addr s₀ ⟨aa, ao, 1024⟩)) →
      Outcome (fun b => (sampleInBall tau b.ball (bytesAt s.mem (Buf.addr s₀ ⟨da, dO, len⟩) len)).map toRq)
        (s'.gpr .eax) (polyAt s'.mem (Buf.addr s₀ ⟨aa, ao, 1024⟩)) → B s₀ s') :
    SP p A B (callPR nm c [.buf ⟨da, dO, len⟩, .imm len, .imm tau, .buf ⟨aa, ao, 1024⟩, .buf ⟨ca, co, 2048⟩]) := by
  set D : Buf := ⟨da, dO, len⟩
  set R : Buf := ⟨aa, ao, 1024⟩
  set C : Buf := ⟨ca, co, 2048⟩
  have ll : (BitVec.ofNat 32 len).toNat = len := by simp [ballParams] at hlt; rcases hlt with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
  have tl : (BitVec.ofNat 32 tau).toNat = tau := by simp [ballParams] at hlt; rcases hlt with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨hD, hR⟩, hC⟩, dDR⟩, dDC⟩, dRC⟩ := hc
  have hR' := (Lay.okW_iff.mp hR).1
  have hC' := (Lay.okW_iff.mp hC).1
  refine callPR_piece _ 5 rfl hv ok (by decide) (by decide) (by simp [argOk, hD, hR', hC']) (fun s₀ => [D.rgn s₀])
    (fun s₀ => [R.rgn s₀, C.rgn s₀, below (E1 s₀) 20]) hA
    (fun s₀ s₁ hp ⟨s, ha, h, m, hg⟩ => ?_) (fun s₀ s₀' s₁ s₁' hp hp' hq ⟨s, ha, h, m, hg⟩ ⟨s', ha', h', m', hg'⟩ => ?_)
    (fun s₀ hp r hr => ?_) (fun s₀ s₁ s' hp ⟨s, ha, h, m, hg⟩ h' fr post => ?_)
  · have a0 : arg (pushed (argPush 5) s₁).callEntry 0 = D.ptr s₀ := ent_arg hp h (as := [.buf D, .imm len, .imm tau, .buf R, .buf C]) (by simp) hg (i := 0) (by simp)
    have a1 : arg (pushed (argPush 5) s₁).callEntry 1 = BitVec.ofNat 32 len := ent_arg hp h (as := [.buf D, .imm len, .imm tau, .buf R, .buf C]) (by simp) hg (i := 1) (by simp)
    have a2 : arg (pushed (argPush 5) s₁).callEntry 2 = BitVec.ofNat 32 tau := ent_arg hp h (as := [.buf D, .imm len, .imm tau, .buf R, .buf C]) (by simp) hg (i := 2) (by simp)
    have a3 : arg (pushed (argPush 5) s₁).callEntry 3 = R.ptr s₀ := ent_arg hp h (as := [.buf D, .imm len, .imm tau, .buf R, .buf C]) (by simp) hg (i := 3) (by simp)
    have a4 : arg (pushed (argPush 5) s₁).callEntry 4 = C.ptr s₀ := ent_arg hp h (as := [.buf D, .imm len, .imm tau, .buf R, .buf C]) (by simp) hg (i := 4) (by simp)
    have eA : argAddr (pushed (argPush 5) s₁).callEntry 0 = _ := ent_arg0 h (n := 5) (by decide)
    have eSp : (pushed (argPush 5) s₁).callEntry.gpr .esp = _ := ent_esp h (n := 5) (by decide)
    obtain ⟨rD₁, rD₂, rD₃⟩ := ent_rgn hp hD (n := 5) (K := 56) (by decide)
    obtain ⟨rR₁, rR₂, rR₃⟩ := ent_rgn hp hR' (n := 5) (K := 56) (by decide)
    obtain ⟨rC₁, rC₂, rC₃⟩ := ent_rgn hp hC' (n := 5) (K := 56) (by decide)
    obtain ⟨rA₂, rA₃⟩ := ent_self hp (n := 5) (K := 56) (by decide)
    have hE := E1_big hp
    have cv := covers_of (s := s₁) (n := 5) (rd := [D.rgn s₀]) (wr := [R.rgn s₀, C.rgn s₀, below (E1 s₀) 20])
      (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        subst hr; exact Buf.within hp hD h.rd h.wr) fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact .inr (Buf.withinW hp hR' (Lay.okW_iff.mp hR).2 h.wr)
        · exact .inr (Buf.withinW hp hC' (Lay.okW_iff.mp hC).2 h.wr)
        · exact .inl (by rw [h.esp])
    refine ⟨?_, cv.1, cv.2⟩
    generalize he : (pushed (argPush 5) s₁).callEntry = e at a0 a1 a2 a3 a4 eA eSp ⊢
    sig_pre [ballK, withRet, sampleInBallContract, sampleInBallSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    subst he
    simp only [arg_withRegions, argAddr_withRegions, a0, a1, a2, a3, a4, eA, eSp, ll, tl]
    exact ⟨by rw [sub_toNat (by omega)]; omega, by rw [sub_toNat (by omega)]; have := (E1 s₀).isLt; omega,
      rfl, rfl, Buf.disj hp hD hR' dDR, Buf.disj hp hD hC' dDC, rD₁, Buf.disj hp hR' hC' dRC, rR₁, rC₁,
      rD₂, rR₂, rC₂, rA₂, rD₃, rR₃, rC₃, rA₃, Buf.fit hp hD, Buf.fit hp hR', Buf.fit hp hC', hlt⟩
  · have e₁ : D.ptr s₀ = D.ptr s₀' := hq.t.ptr hD
    have e₂ : R.ptr s₀ = R.ptr s₀' := hq.t.ptr hR'
    have e₃ : C.ptr s₀ = C.ptr s₀' := hq.t.ptr hC'
    refine ⟨by simp only [Buf.rgn, e₁], by simp only [Buf.rgn, e₂, e₃, hq.t.E1], ?_⟩
    have a0 : arg (pushed (argPush 5) s₁).callEntry 0 = D.ptr s₀ := ent_arg hp h (as := [.buf D, .imm len, .imm tau, .buf R, .buf C]) (by simp) hg (i := 0) (by simp)
    have a1 : arg (pushed (argPush 5) s₁).callEntry 1 = BitVec.ofNat 32 len := ent_arg hp h (as := [.buf D, .imm len, .imm tau, .buf R, .buf C]) (by simp) hg (i := 1) (by simp)
    have a2 : arg (pushed (argPush 5) s₁).callEntry 2 = BitVec.ofNat 32 tau := ent_arg hp h (as := [.buf D, .imm len, .imm tau, .buf R, .buf C]) (by simp) hg (i := 2) (by simp)
    have a3 : arg (pushed (argPush 5) s₁).callEntry 3 = R.ptr s₀ := ent_arg hp h (as := [.buf D, .imm len, .imm tau, .buf R, .buf C]) (by simp) hg (i := 3) (by simp)
    have a4 : arg (pushed (argPush 5) s₁).callEntry 4 = C.ptr s₀ := ent_arg hp h (as := [.buf D, .imm len, .imm tau, .buf R, .buf C]) (by simp) hg (i := 4) (by simp)
    have a0' : arg (pushed (argPush 5) s₁').callEntry 0 = D.ptr s₀' := ent_arg hp' h' (as := [.buf D, .imm len, .imm tau, .buf R, .buf C]) (by simp) hg' (i := 0) (by simp)
    have a1' : arg (pushed (argPush 5) s₁').callEntry 1 = BitVec.ofNat 32 len := ent_arg hp' h' (as := [.buf D, .imm len, .imm tau, .buf R, .buf C]) (by simp) hg' (i := 1) (by simp)
    have a2' : arg (pushed (argPush 5) s₁').callEntry 2 = BitVec.ofNat 32 tau := ent_arg hp' h' (as := [.buf D, .imm len, .imm tau, .buf R, .buf C]) (by simp) hg' (i := 2) (by simp)
    have a3' : arg (pushed (argPush 5) s₁').callEntry 3 = R.ptr s₀' := ent_arg hp' h' (as := [.buf D, .imm len, .imm tau, .buf R, .buf C]) (by simp) hg' (i := 3) (by simp)
    have a4' : arg (pushed (argPush 5) s₁').callEntry 4 = C.ptr s₀' := ent_arg hp' h' (as := [.buf D, .imm len, .imm tau, .buf R, .buf C]) (by simp) hg' (i := 4) (by simp)
    have eSp : (pushed (argPush 5) s₁).callEntry.gpr .esp = _ := ent_esp h (n := 5) (by decide)
    have eSp' : (pushed (argPush 5) s₁').callEntry.gpr .esp = _ := ent_esp h' (n := 5) (by decide)
    have b₁ := VG.Proof.MlKem.bytesAt_congr (ent_bytes hp h (n := 5) (by decide) hD)
    have b₂ := VG.Proof.MlKem.bytesAt_congr (ent_bytes hp' h' (n := 5) (by decide) hD)
    have key : bytesAt (pushed (argPush 5) s₁).callEntry.mem (D.addr s₀) len =
        bytesAt (pushed (argPush 5) s₁').callEntry.mem (D.addr s₀') len := by
      rw [b₁, b₂, m, m']; exact hseed s₀ s₀' s s' hp hp' hq ha ha'
    simp only [Buf.addr, e₁] at key
    generalize he : (pushed (argPush 5) s₁).callEntry = e at a0 a1 a2 a3 a4 eSp key ⊢
    generalize he' : (pushed (argPush 5) s₁').callEntry = e' at a0' a1' a2' a3' a4' eSp' key ⊢
    sig_pub [ballK, withRet, sampleInBallContract, sampleInBallSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [arg_withRegions, a0, a1, a2, a3, a4, a0', a1', a2', a3', a4', eSp, eSp', e₁, e₂, e₃, hq.t.E1,
      and_self, ll, key]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Buf.inW hp hR' (Lay.okW_iff.mp hR).2
    · exact Buf.inW hp hC' (Lay.okW_iff.mp hC).2
    · exact stk_W hp (by decide)
  · obtain ⟨s₂, m₂, g₂, post⟩ := post
    have a0 : arg (pushed (argPush 5) s₁).callEntry 0 = D.ptr s₀ := ent_arg hp h (as := [.buf D, .imm len, .imm tau, .buf R, .buf C]) (by simp) hg (i := 0) (by simp)
    have a1 : arg (pushed (argPush 5) s₁).callEntry 1 = BitVec.ofNat 32 len := ent_arg hp h (as := [.buf D, .imm len, .imm tau, .buf R, .buf C]) (by simp) hg (i := 1) (by simp)
    have a2 : arg (pushed (argPush 5) s₁).callEntry 2 = BitVec.ofNat 32 tau := ent_arg hp h (as := [.buf D, .imm len, .imm tau, .buf R, .buf C]) (by simp) hg (i := 2) (by simp)
    have a3 : arg (pushed (argPush 5) s₁).callEntry 3 = R.ptr s₀ := ent_arg hp h (as := [.buf D, .imm len, .imm tau, .buf R, .buf C]) (by simp) hg (i := 3) (by simp)
    have b₁ : bytesAt (pushed (argPush 5) s₁).callEntry.mem ((D.ptr s₀).setWidth 64) len = bytesAt s.mem (D.addr s₀) len := by
      rw [← m]; exact VG.Proof.MlKem.bytesAt_congr (ent_bytes hp h (n := 5) (by decide) hD)
    generalize he : (pushed (argPush 5) s₁).callEntry = e at a0 a1 a2 a3 post
    sig_post [ballK, withRet, sampleInBallContract, sampleInBallSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at post
    subst he
    simp only [arg_withRegions, a0, a1, a2, a3, m₂, sw32, g₂, ll, tl] at post
    rw [b₁] at post
    exact hQ s₀ s s' hp ha h' (fr80 (by decide) (by have := ok.stk; omega) hp (m ▸ fr)) post.2.2 post.1 post.2.1

end VG.Proof.MlDsa.X86.Sign
