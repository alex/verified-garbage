import VerifiedGarbage.Proof.MlDsa.X86.Sign.Prims

/-!
# ML-DSA signing on x86 (32-bit): calls of the arithmetic primitives

Untrusted: everything here is checked by Lean. `NTT` and `NTT⁻¹` in place
(`inPlace_piece`), products (`mul_piece`, with or without the sum), and
sums and differences (`acc_piece`).
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

/-- `f ← t(f)`, with the working space `PS`. -/
theorem inPlace_piece {t : Poly → Poly} {nm : String} {c : Prog isa}
    (hv : Verified X86.target c (inPlaceContract X86.abi t 16)) (ok : COk c) (f : Buf) (hf : f.len = 1024)
    (hc : ((Y p).okW f && (Y p).okW (sc oPS 1024) && (Y p).sep f (sc oPS 1024)) = true)
    (hA : ∀ s₀ s, TPre (Y p) s₀ → A s₀ s → Ctx (Y p) s₀ s ∧ Reduced s.mem (f.addr s₀))
    (hQ : ∀ s₀ s s', TPre (Y p) s₀ → A s₀ s → Ctx (Y p) s₀ s' → Frame (FR s₀ [f, sc oPS 1024] 80) s.mem s'.mem →
      PolyIs s'.mem (f.addr s₀) (t (polyAt s.mem (f.addr s₀))) → B s₀ s') :
    SP p A B (callP nm c [.buf f, .buf (sc oPS 1024)]) := by
  obtain ⟨fa, fo, fl⟩ := f
  simp only at hf
  subst hf
  set f : Buf := ⟨fa, fo, 1024⟩ with hfd
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨hF, hS⟩, dFS⟩ := hc
  have hF' := (Lay.okW_iff.mp hF).1
  have hS' := (Lay.okW_iff.mp hS).1
  refine callP_piece _ 2 rfl hv ok (by decide) (by decide) (by simp [argOk, hF', hS']) (fun _ => [])
    (fun s₀ => [f.rgn s₀, Buf.rgn s₀ (sc oPS 1024), below (E1 s₀) 8]) (fun s₀ s hp ha => (hA s₀ s hp ha).1)
    (fun s₀ s₁ hp ⟨s, ha, h, m, hg⟩ => ?_) (fun s₀ s₀' s₁ s₁' hp hp' hq ⟨s, ha, h, m, hg⟩ ⟨s', ha', h', m', hg'⟩ => ?_)
    (fun s₀ hp r hr => ?_) (fun s₀ s₁ s' hp ⟨s, ha, h, m, hg⟩ h' fr post => ?_)
  · have a0 : arg (pushed (argPush 2) s₁).callEntry 0 = f.ptr s₀ := ent_arg hp h (as := [.buf f, .buf (sc oPS 1024)]) (by simp) hg (i := 0) (by simp)
    have a1 : arg (pushed (argPush 2) s₁).callEntry 1 = Buf.ptr s₀ (sc oPS 1024) := ent_arg hp h (as := [.buf f, .buf (sc oPS 1024)]) (by simp) hg (i := 1) (by simp)
    have eA : argAddr (pushed (argPush 2) s₁).callEntry 0 = _ := ent_arg0 h (n := 2) (by decide)
    have eSp : (pushed (argPush 2) s₁).callEntry.gpr .esp = _ := ent_esp h (n := 2) (by decide)
    obtain ⟨rF₁, rF₂, rF₃⟩ := ent_rgn hp hF' (n := 2) (K := 16) (by decide)
    obtain ⟨rS₁, rS₂, rS₃⟩ := ent_rgn hp hS' (n := 2) (K := 16) (by decide)
    obtain ⟨rA₂, rA₃⟩ := ent_self hp (n := 2) (K := 16) (by decide)
    have hE := E1_big hp
    have cv := covers_of (s := s₁) (n := 2) (rd := []) (wr := [f.rgn s₀, Buf.rgn s₀ (sc oPS 1024), below (E1 s₀) 8])
      (fun r hr => absurd hr (by simp)) fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact .inr (Buf.withinW hp hF' (Lay.okW_iff.mp hF).2 h.wr)
        · exact .inr (Buf.withinW hp hS' (Lay.okW_iff.mp hS).2 h.wr)
        · exact .inl (by rw [h.esp])
    refine ⟨?_, cv.1, cv.2⟩
    generalize he : (pushed (argPush 2) s₁).callEntry = e at a0 a1 eA eSp ⊢
    sig_pre [inPlaceContract, inPlaceSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    subst he
    simp only [arg_withRegions, argAddr_withRegions, a0, a1, eA, eSp]
    refine ⟨by rw [sub_toNat (by omega)]; omega, by rw [sub_toNat (by omega)]; have := (E1 s₀).isLt; omega,
      rfl, Buf.disj hp hF' hS' dFS, rF₁, rS₁, rF₂, rS₂, rA₂, rF₃, rS₃, rA₃, Buf.fit hp hF', Buf.fit hp hS', ?_⟩
    exact reduced_congr (ent_bytes hp h (n := 2) (by decide) hF') (m ▸ (hA s₀ s hp ha).2)
  · have e₁ : f.ptr s₀ = f.ptr s₀' := hq.t.ptr hF'
    have e₂ : Buf.ptr s₀ (sc oPS 1024) = Buf.ptr s₀' (sc oPS 1024) := hq.t.ptr hS'
    refine ⟨rfl, by simp only [Buf.rgn, e₁, e₂, hq.t.E1], ?_⟩
    have a0 : arg (pushed (argPush 2) s₁).callEntry 0 = f.ptr s₀ :=
      ent_arg hp h (as := [.buf f, .buf (sc oPS 1024)]) (by simp) hg (i := 0) (by simp)
    have a1 : arg (pushed (argPush 2) s₁).callEntry 1 = Buf.ptr s₀ (sc oPS 1024) :=
      ent_arg hp h (as := [.buf f, .buf (sc oPS 1024)]) (by simp) hg (i := 1) (by simp)
    have a0' : arg (pushed (argPush 2) s₁').callEntry 0 = f.ptr s₀' :=
      ent_arg hp' h' (as := [.buf f, .buf (sc oPS 1024)]) (by simp) hg' (i := 0) (by simp)
    have a1' : arg (pushed (argPush 2) s₁').callEntry 1 = Buf.ptr s₀' (sc oPS 1024) :=
      ent_arg hp' h' (as := [.buf f, .buf (sc oPS 1024)]) (by simp) hg' (i := 1) (by simp)
    have eSp : (pushed (argPush 2) s₁).callEntry.gpr .esp = _ := ent_esp h (n := 2) (by decide)
    have eSp' : (pushed (argPush 2) s₁').callEntry.gpr .esp = _ := ent_esp h' (n := 2) (by decide)
    generalize he : (pushed (argPush 2) s₁).callEntry = e at a0 a1 eSp ⊢
    generalize he' : (pushed (argPush 2) s₁').callEntry = e' at a0' a1' eSp' ⊢
    sig_pub [inPlaceContract, inPlaceSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [arg_withRegions, a0, a1, a0', a1', eSp, eSp', e₁, e₂, hq.t.E1]
    exact ⟨trivial, trivial, trivial⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Buf.inW hp hF' (Lay.okW_iff.mp hF).2
    · exact Buf.inW hp hS' (Lay.okW_iff.mp hS).2
    · exact stk_W hp (by decide)
  · obtain ⟨s₂, m₂, post⟩ := post
    have a0 : arg (pushed (argPush 2) s₁).callEntry 0 = f.ptr s₀ :=
      ent_arg hp h (as := [.buf f, .buf (sc oPS 1024)]) (by simp) hg (i := 0) (by simp)
    generalize he : (pushed (argPush 2) s₁).callEntry = e at a0 post
    sig_post [inPlaceContract, inPlaceSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at post
    subst he
    simp only [arg_withRegions, a0, m₂] at post
    rw [polyAt_congr (ent_bytes hp h (n := 2) (by decide) hF'), m] at post
    exact hQ s₀ s s' hp ha h' (fr80 (by decide) (by have := ok.stk; omega) hp (m ▸ fr)) post

end VG.Proof.MlDsa.X86.Sign

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

/-- `h ← MultiplyNTT(f, g)`. -/
theorem mul_piece {nm : String} {c : Prog isa} (hv : Verified X86.target c (mulContract X86.abi 16))
    (ok : COk c) (ha ho fa fo ga go : Nat)
    (hc : ((Y p).okW ⟨ha, ho, 1024⟩ && (Y p).ok ⟨fa, fo, 1024⟩ && (Y p).ok ⟨ga, go, 1024⟩ &&
      (Y p).sep ⟨ha, ho, 1024⟩ ⟨fa, fo, 1024⟩ && (Y p).sep ⟨ha, ho, 1024⟩ ⟨ga, go, 1024⟩) = true)
    (hA : ∀ s₀ s, TPre (Y p) s₀ → A s₀ s → Ctx (Y p) s₀ s ∧ Reduced s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩) ∧ Reduced s.mem (Buf.addr s₀ ⟨ga, go, 1024⟩))
    (hQ : ∀ s₀ s s', TPre (Y p) s₀ → A s₀ s → Ctx (Y p) s₀ s' → Frame (FR s₀ [⟨ha, ho, 1024⟩] 80) s.mem s'.mem →
      PolyIs s'.mem (Buf.addr s₀ ⟨ha, ho, 1024⟩)
        (multiplyNTT (polyAt s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩)) (polyAt s.mem (Buf.addr s₀ ⟨ga, go, 1024⟩))) →
      B s₀ s') :
    SP p A B (callP nm c [.buf ⟨ha, ho, 1024⟩, .buf ⟨fa, fo, 1024⟩, .buf ⟨ga, go, 1024⟩]) := by
  set H : Buf := ⟨ha, ho, 1024⟩
  set F : Buf := ⟨fa, fo, 1024⟩
  set G : Buf := ⟨ga, go, 1024⟩
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨hH, hF⟩, hG⟩, dHF⟩, dHG⟩ := hc
  have hH' := (Lay.okW_iff.mp hH).1
  refine callP_piece _ 3 rfl hv ok (by decide) (by decide) (by simp [argOk, hH', hF, hG]) (fun s₀ => [F.rgn s₀, G.rgn s₀])
    (fun s₀ => [H.rgn s₀, below (E1 s₀) 12]) (fun s₀ s hp ha => (hA s₀ s hp ha).1)
    (fun s₀ s₁ hp ⟨s, ha, h, m, hg⟩ => ?_) (fun s₀ s₀' s₁ s₁' hp hp' hq ⟨s, ha, h, m, hg⟩ ⟨s', ha', h', m', hg'⟩ => ?_)
    (fun s₀ hp r hr => ?_) (fun s₀ s₁ s' hp ⟨s, ha, h, m, hg⟩ h' fr post => ?_)
  · have a0 : arg (pushed (argPush 3) s₁).callEntry 0 = H.ptr s₀ := ent_arg hp h (as := [.buf H, .buf F, .buf G]) (by simp) hg (i := 0) (by simp)
    have a1 : arg (pushed (argPush 3) s₁).callEntry 1 = F.ptr s₀ := ent_arg hp h (as := [.buf H, .buf F, .buf G]) (by simp) hg (i := 1) (by simp)
    have a2 : arg (pushed (argPush 3) s₁).callEntry 2 = G.ptr s₀ := ent_arg hp h (as := [.buf H, .buf F, .buf G]) (by simp) hg (i := 2) (by simp)
    have eA : argAddr (pushed (argPush 3) s₁).callEntry 0 = _ := ent_arg0 h (n := 3) (by decide)
    have eSp : (pushed (argPush 3) s₁).callEntry.gpr .esp = _ := ent_esp h (n := 3) (by decide)
    obtain ⟨rH₁, rH₂, rH₃⟩ := ent_rgn hp hH' (n := 3) (K := 16) (by decide)
    obtain ⟨rF₁, rF₂, rF₃⟩ := ent_rgn hp hF (n := 3) (K := 16) (by decide)
    obtain ⟨rG₁, rG₂, rG₃⟩ := ent_rgn hp hG (n := 3) (K := 16) (by decide)
    obtain ⟨rA₂, rA₃⟩ := ent_self hp (n := 3) (K := 16) (by decide)
    have hE := E1_big hp
    have cv := covers_of (s := s₁) (n := 3) (rd := [F.rgn s₀, G.rgn s₀]) (wr := [H.rgn s₀, below (E1 s₀) 12])
      (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact Buf.within hp hF h.rd h.wr
        · exact Buf.within hp hG h.rd h.wr) fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact .inr (Buf.withinW hp hH' (Lay.okW_iff.mp hH).2 h.wr)
        · exact .inl (by rw [h.esp])
    refine ⟨?_, cv.1, cv.2⟩
    generalize he : (pushed (argPush 3) s₁).callEntry = e at a0 a1 a2 eA eSp ⊢
    sig_pre [mulContract, mulSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    subst he
    simp only [arg_withRegions, argAddr_withRegions, a0, a1, a2, eA, eSp]
    refine ⟨by rw [sub_toNat (by omega)]; omega, by rw [sub_toNat (by omega)]; have := (E1 s₀).isLt; omega,
      rfl, rfl, Buf.disj hp hH' hF dHF, Buf.disj hp hH' hG dHG, rH₁, rF₁, rG₁, rH₂, rF₂, rG₂, rA₂, rH₃, rF₃, rG₃, rA₃,
      Buf.fit hp hH', Buf.fit hp hF, Buf.fit hp hG, ?_, ?_⟩
    · exact reduced_congr (ent_bytes hp h (n := 3) (by decide) hF) (m ▸ (hA s₀ s hp ha).2.1)
    · exact reduced_congr (ent_bytes hp h (n := 3) (by decide) hG) (m ▸ (hA s₀ s hp ha).2.2)
  · have e₁ : H.ptr s₀ = H.ptr s₀' := hq.t.ptr hH'
    have e₂ : F.ptr s₀ = F.ptr s₀' := hq.t.ptr hF
    have e₃ : G.ptr s₀ = G.ptr s₀' := hq.t.ptr hG
    refine ⟨by simp only [Buf.rgn, e₂, e₃], by simp only [Buf.rgn, e₁, hq.t.E1], ?_⟩
    have a0 : arg (pushed (argPush 3) s₁).callEntry 0 = H.ptr s₀ := ent_arg hp h (as := [.buf H, .buf F, .buf G]) (by simp) hg (i := 0) (by simp)
    have a1 : arg (pushed (argPush 3) s₁).callEntry 1 = F.ptr s₀ := ent_arg hp h (as := [.buf H, .buf F, .buf G]) (by simp) hg (i := 1) (by simp)
    have a2 : arg (pushed (argPush 3) s₁).callEntry 2 = G.ptr s₀ := ent_arg hp h (as := [.buf H, .buf F, .buf G]) (by simp) hg (i := 2) (by simp)
    have a0' : arg (pushed (argPush 3) s₁').callEntry 0 = H.ptr s₀' := ent_arg hp' h' (as := [.buf H, .buf F, .buf G]) (by simp) hg' (i := 0) (by simp)
    have a1' : arg (pushed (argPush 3) s₁').callEntry 1 = F.ptr s₀' := ent_arg hp' h' (as := [.buf H, .buf F, .buf G]) (by simp) hg' (i := 1) (by simp)
    have a2' : arg (pushed (argPush 3) s₁').callEntry 2 = G.ptr s₀' := ent_arg hp' h' (as := [.buf H, .buf F, .buf G]) (by simp) hg' (i := 2) (by simp)
    have eSp : (pushed (argPush 3) s₁).callEntry.gpr .esp = _ := ent_esp h (n := 3) (by decide)
    have eSp' : (pushed (argPush 3) s₁').callEntry.gpr .esp = _ := ent_esp h' (n := 3) (by decide)
    generalize he : (pushed (argPush 3) s₁).callEntry = e at a0 a1 a2 eSp ⊢
    generalize he' : (pushed (argPush 3) s₁').callEntry = e' at a0' a1' a2' eSp' ⊢
    sig_pub [mulContract, mulSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [arg_withRegions, a0, a1, a2, a0', a1', a2', eSp, eSp', e₁, e₂, e₃, hq.t.E1, and_self]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Buf.inW hp hH' (Lay.okW_iff.mp hH).2
    · exact stk_W hp (by decide)
  · obtain ⟨s₂, m₂, post⟩ := post
    have a0 : arg (pushed (argPush 3) s₁).callEntry 0 = H.ptr s₀ := ent_arg hp h (as := [.buf H, .buf F, .buf G]) (by simp) hg (i := 0) (by simp)
    have a1 : arg (pushed (argPush 3) s₁).callEntry 1 = F.ptr s₀ := ent_arg hp h (as := [.buf H, .buf F, .buf G]) (by simp) hg (i := 1) (by simp)
    have a2 : arg (pushed (argPush 3) s₁).callEntry 2 = G.ptr s₀ := ent_arg hp h (as := [.buf H, .buf F, .buf G]) (by simp) hg (i := 2) (by simp)
    generalize he : (pushed (argPush 3) s₁).callEntry = e at a0 a1 a2 post
    sig_post [mulContract, mulSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at post
    subst he
    simp only [arg_withRegions, a0, a1, a2, m₂] at post
    rw [polyAt_congr (ent_bytes hp h (n := 3) (by decide) hF), polyAt_congr (ent_bytes hp h (n := 3) (by decide) hG),
      m] at post
    exact hQ s₀ s s' hp ha h' (fr80 (by decide) (by have := ok.stk; omega) hp (m ▸ fr)) post

/-- `h ← h + MultiplyNTT(f, g)`. -/
theorem mulAdd_piece {nm : String} {c : Prog isa} (hv : Verified X86.target c (mulAddContract X86.abi 16))
    (ok : COk c) (ha ho fa fo ga go : Nat)
    (hc : ((Y p).okW ⟨ha, ho, 1024⟩ && (Y p).ok ⟨fa, fo, 1024⟩ && (Y p).ok ⟨ga, go, 1024⟩ &&
      (Y p).sep ⟨ha, ho, 1024⟩ ⟨fa, fo, 1024⟩ && (Y p).sep ⟨ha, ho, 1024⟩ ⟨ga, go, 1024⟩) = true)
    (hA : ∀ s₀ s, TPre (Y p) s₀ → A s₀ s → Ctx (Y p) s₀ s ∧ Reduced s.mem (Buf.addr s₀ ⟨ha, ho, 1024⟩) ∧ Reduced s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩) ∧ Reduced s.mem (Buf.addr s₀ ⟨ga, go, 1024⟩))
    (hQ : ∀ s₀ s s', TPre (Y p) s₀ → A s₀ s → Ctx (Y p) s₀ s' → Frame (FR s₀ [⟨ha, ho, 1024⟩] 80) s.mem s'.mem →
      PolyIs s'.mem (Buf.addr s₀ ⟨ha, ho, 1024⟩) (add (polyAt s.mem (Buf.addr s₀ ⟨ha, ho, 1024⟩))
        (multiplyNTT (polyAt s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩)) (polyAt s.mem (Buf.addr s₀ ⟨ga, go, 1024⟩)))) →
      B s₀ s') :
    SP p A B (callP nm c [.buf ⟨ha, ho, 1024⟩, .buf ⟨fa, fo, 1024⟩, .buf ⟨ga, go, 1024⟩]) := by
  set H : Buf := ⟨ha, ho, 1024⟩
  set F : Buf := ⟨fa, fo, 1024⟩
  set G : Buf := ⟨ga, go, 1024⟩
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨hH, hF⟩, hG⟩, dHF⟩, dHG⟩ := hc
  have hH' := (Lay.okW_iff.mp hH).1
  refine callP_piece _ 3 rfl hv ok (by decide) (by decide) (by simp [argOk, hH', hF, hG]) (fun s₀ => [F.rgn s₀, G.rgn s₀])
    (fun s₀ => [H.rgn s₀, below (E1 s₀) 12]) (fun s₀ s hp ha => (hA s₀ s hp ha).1)
    (fun s₀ s₁ hp ⟨s, ha, h, m, hg⟩ => ?_) (fun s₀ s₀' s₁ s₁' hp hp' hq ⟨s, ha, h, m, hg⟩ ⟨s', ha', h', m', hg'⟩ => ?_)
    (fun s₀ hp r hr => ?_) (fun s₀ s₁ s' hp ⟨s, ha, h, m, hg⟩ h' fr post => ?_)
  · have a0 : arg (pushed (argPush 3) s₁).callEntry 0 = H.ptr s₀ := ent_arg hp h (as := [.buf H, .buf F, .buf G]) (by simp) hg (i := 0) (by simp)
    have a1 : arg (pushed (argPush 3) s₁).callEntry 1 = F.ptr s₀ := ent_arg hp h (as := [.buf H, .buf F, .buf G]) (by simp) hg (i := 1) (by simp)
    have a2 : arg (pushed (argPush 3) s₁).callEntry 2 = G.ptr s₀ := ent_arg hp h (as := [.buf H, .buf F, .buf G]) (by simp) hg (i := 2) (by simp)
    have eA : argAddr (pushed (argPush 3) s₁).callEntry 0 = _ := ent_arg0 h (n := 3) (by decide)
    have eSp : (pushed (argPush 3) s₁).callEntry.gpr .esp = _ := ent_esp h (n := 3) (by decide)
    obtain ⟨rH₁, rH₂, rH₃⟩ := ent_rgn hp hH' (n := 3) (K := 16) (by decide)
    obtain ⟨rF₁, rF₂, rF₃⟩ := ent_rgn hp hF (n := 3) (K := 16) (by decide)
    obtain ⟨rG₁, rG₂, rG₃⟩ := ent_rgn hp hG (n := 3) (K := 16) (by decide)
    obtain ⟨rA₂, rA₃⟩ := ent_self hp (n := 3) (K := 16) (by decide)
    have hE := E1_big hp
    have cv := covers_of (s := s₁) (n := 3) (rd := [F.rgn s₀, G.rgn s₀]) (wr := [H.rgn s₀, below (E1 s₀) 12])
      (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact Buf.within hp hF h.rd h.wr
        · exact Buf.within hp hG h.rd h.wr) fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact .inr (Buf.withinW hp hH' (Lay.okW_iff.mp hH).2 h.wr)
        · exact .inl (by rw [h.esp])
    refine ⟨?_, cv.1, cv.2⟩
    generalize he : (pushed (argPush 3) s₁).callEntry = e at a0 a1 a2 eA eSp ⊢
    sig_pre [mulAddContract, mulSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    subst he
    simp only [arg_withRegions, argAddr_withRegions, a0, a1, a2, eA, eSp]
    refine ⟨by rw [sub_toNat (by omega)]; omega, by rw [sub_toNat (by omega)]; have := (E1 s₀).isLt; omega,
      rfl, rfl, Buf.disj hp hH' hF dHF, Buf.disj hp hH' hG dHG, rH₁, rF₁, rG₁, rH₂, rF₂, rG₂, rA₂, rH₃, rF₃, rG₃, rA₃,
      Buf.fit hp hH', Buf.fit hp hF, Buf.fit hp hG, ?_, ?_, ?_⟩
    · exact reduced_congr (ent_bytes hp h (n := 3) (by decide) hH') (m ▸ (hA s₀ s hp ha).2.1)
    · exact reduced_congr (ent_bytes hp h (n := 3) (by decide) hF) (m ▸ (hA s₀ s hp ha).2.2.1)
    · exact reduced_congr (ent_bytes hp h (n := 3) (by decide) hG) (m ▸ (hA s₀ s hp ha).2.2.2)
  · have e₁ : H.ptr s₀ = H.ptr s₀' := hq.t.ptr hH'
    have e₂ : F.ptr s₀ = F.ptr s₀' := hq.t.ptr hF
    have e₃ : G.ptr s₀ = G.ptr s₀' := hq.t.ptr hG
    refine ⟨by simp only [Buf.rgn, e₂, e₃], by simp only [Buf.rgn, e₁, hq.t.E1], ?_⟩
    have a0 : arg (pushed (argPush 3) s₁).callEntry 0 = H.ptr s₀ := ent_arg hp h (as := [.buf H, .buf F, .buf G]) (by simp) hg (i := 0) (by simp)
    have a1 : arg (pushed (argPush 3) s₁).callEntry 1 = F.ptr s₀ := ent_arg hp h (as := [.buf H, .buf F, .buf G]) (by simp) hg (i := 1) (by simp)
    have a2 : arg (pushed (argPush 3) s₁).callEntry 2 = G.ptr s₀ := ent_arg hp h (as := [.buf H, .buf F, .buf G]) (by simp) hg (i := 2) (by simp)
    have a0' : arg (pushed (argPush 3) s₁').callEntry 0 = H.ptr s₀' := ent_arg hp' h' (as := [.buf H, .buf F, .buf G]) (by simp) hg' (i := 0) (by simp)
    have a1' : arg (pushed (argPush 3) s₁').callEntry 1 = F.ptr s₀' := ent_arg hp' h' (as := [.buf H, .buf F, .buf G]) (by simp) hg' (i := 1) (by simp)
    have a2' : arg (pushed (argPush 3) s₁').callEntry 2 = G.ptr s₀' := ent_arg hp' h' (as := [.buf H, .buf F, .buf G]) (by simp) hg' (i := 2) (by simp)
    have eSp : (pushed (argPush 3) s₁).callEntry.gpr .esp = _ := ent_esp h (n := 3) (by decide)
    have eSp' : (pushed (argPush 3) s₁').callEntry.gpr .esp = _ := ent_esp h' (n := 3) (by decide)
    generalize he : (pushed (argPush 3) s₁).callEntry = e at a0 a1 a2 eSp ⊢
    generalize he' : (pushed (argPush 3) s₁').callEntry = e' at a0' a1' a2' eSp' ⊢
    sig_pub [mulAddContract, mulSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [arg_withRegions, a0, a1, a2, a0', a1', a2', eSp, eSp', e₁, e₂, e₃, hq.t.E1, and_self]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Buf.inW hp hH' (Lay.okW_iff.mp hH).2
    · exact stk_W hp (by decide)
  · obtain ⟨s₂, m₂, post⟩ := post
    have a0 : arg (pushed (argPush 3) s₁).callEntry 0 = H.ptr s₀ := ent_arg hp h (as := [.buf H, .buf F, .buf G]) (by simp) hg (i := 0) (by simp)
    have a1 : arg (pushed (argPush 3) s₁).callEntry 1 = F.ptr s₀ := ent_arg hp h (as := [.buf H, .buf F, .buf G]) (by simp) hg (i := 1) (by simp)
    have a2 : arg (pushed (argPush 3) s₁).callEntry 2 = G.ptr s₀ := ent_arg hp h (as := [.buf H, .buf F, .buf G]) (by simp) hg (i := 2) (by simp)
    generalize he : (pushed (argPush 3) s₁).callEntry = e at a0 a1 a2 post
    sig_post [mulAddContract, mulSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at post
    subst he
    simp only [arg_withRegions, a0, a1, a2, m₂] at post
    rw [polyAt_congr (ent_bytes hp h (n := 3) (by decide) hH'), polyAt_congr (ent_bytes hp h (n := 3) (by decide) hF), polyAt_congr (ent_bytes hp h (n := 3) (by decide) hG),
      m] at post
    exact hQ s₀ s s' hp ha h' (fr80 (by decide) (by have := ok.stk; omega) hp (m ▸ fr)) post

/-- `f ← op(f, g)` (`vg_mldsa_add`, `vg_mldsa_sub`). -/
theorem acc_piece {op : Poly → Poly → Poly} {nm : String} {c : Prog isa}
    (hv : Verified X86.target c (accSig.contract X86.abi (pre := fun f g m => Reduced m f ∧ Reduced m g)
      (post := fun f g m m' _ => PolyIs m' f (op (polyAt m f) (polyAt m g))) (writeArgs := true) (stack := 16)))
    (ok : COk c) (fa fo ga go : Nat)
    (hc : ((Y p).okW ⟨fa, fo, 1024⟩ && (Y p).ok ⟨ga, go, 1024⟩ && (Y p).sep ⟨fa, fo, 1024⟩ ⟨ga, go, 1024⟩) = true)
    (hA : ∀ s₀ s, TPre (Y p) s₀ → A s₀ s → Ctx (Y p) s₀ s ∧ Reduced s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩) ∧
      Reduced s.mem (Buf.addr s₀ ⟨ga, go, 1024⟩))
    (hQ : ∀ s₀ s s', TPre (Y p) s₀ → A s₀ s → Ctx (Y p) s₀ s' → Frame (FR s₀ [⟨fa, fo, 1024⟩] 80) s.mem s'.mem →
      PolyIs s'.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩)
        (op (polyAt s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩)) (polyAt s.mem (Buf.addr s₀ ⟨ga, go, 1024⟩))) → B s₀ s') :
    SP p A B (callP nm c [.buf ⟨fa, fo, 1024⟩, .buf ⟨ga, go, 1024⟩]) := by
  set F : Buf := ⟨fa, fo, 1024⟩
  set G : Buf := ⟨ga, go, 1024⟩
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨hF, hG⟩, dFG⟩ := hc
  have hF' := (Lay.okW_iff.mp hF).1
  refine callP_piece _ 2 rfl hv ok (by decide) (by decide) (by simp [argOk, hF', hG]) (fun s₀ => [G.rgn s₀])
    (fun s₀ => [F.rgn s₀, below (E1 s₀) 8]) (fun s₀ s hp ha => (hA s₀ s hp ha).1)
    (fun s₀ s₁ hp ⟨s, ha, h, m, hg⟩ => ?_) (fun s₀ s₀' s₁ s₁' hp hp' hq ⟨s, ha, h, m, hg⟩ ⟨s', ha', h', m', hg'⟩ => ?_)
    (fun s₀ hp r hr => ?_) (fun s₀ s₁ s' hp ⟨s, ha, h, m, hg⟩ h' fr post => ?_)
  · have a0 : arg (pushed (argPush 2) s₁).callEntry 0 = F.ptr s₀ := ent_arg hp h (as := [.buf F, .buf G]) (by simp) hg (i := 0) (by simp)
    have a1 : arg (pushed (argPush 2) s₁).callEntry 1 = G.ptr s₀ := ent_arg hp h (as := [.buf F, .buf G]) (by simp) hg (i := 1) (by simp)
    have eA : argAddr (pushed (argPush 2) s₁).callEntry 0 = _ := ent_arg0 h (n := 2) (by decide)
    have eSp : (pushed (argPush 2) s₁).callEntry.gpr .esp = _ := ent_esp h (n := 2) (by decide)
    obtain ⟨rF₁, rF₂, rF₃⟩ := ent_rgn hp hF' (n := 2) (K := 16) (by decide)
    obtain ⟨rG₁, rG₂, rG₃⟩ := ent_rgn hp hG (n := 2) (K := 16) (by decide)
    obtain ⟨rA₂, rA₃⟩ := ent_self hp (n := 2) (K := 16) (by decide)
    have hE := E1_big hp
    have cv := covers_of (s := s₁) (n := 2) (rd := [G.rgn s₀]) (wr := [F.rgn s₀, below (E1 s₀) 8])
      (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        subst hr; exact Buf.within hp hG h.rd h.wr) fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact .inr (Buf.withinW hp hF' (Lay.okW_iff.mp hF).2 h.wr)
        · exact .inl (by rw [h.esp])
    refine ⟨?_, cv.1, cv.2⟩
    generalize he : (pushed (argPush 2) s₁).callEntry = e at a0 a1 eA eSp ⊢
    sig_pre [accSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    subst he
    simp only [arg_withRegions, argAddr_withRegions, a0, a1, eA, eSp]
    refine ⟨by rw [sub_toNat (by omega)]; omega, by rw [sub_toNat (by omega)]; have := (E1 s₀).isLt; omega,
      rfl, rfl, Buf.disj hp hF' hG dFG, rF₁, rG₁, rF₂, rG₂, rA₂, rF₃, rG₃, rA₃,
      Buf.fit hp hF', Buf.fit hp hG, ?_, ?_⟩
    · exact reduced_congr (ent_bytes hp h (n := 2) (by decide) hF') (m ▸ (hA s₀ s hp ha).2.1)
    · exact reduced_congr (ent_bytes hp h (n := 2) (by decide) hG) (m ▸ (hA s₀ s hp ha).2.2)
  · have e₁ : F.ptr s₀ = F.ptr s₀' := hq.t.ptr hF'
    have e₂ : G.ptr s₀ = G.ptr s₀' := hq.t.ptr hG
    refine ⟨by simp only [Buf.rgn, e₂], by simp only [Buf.rgn, e₁, hq.t.E1], ?_⟩
    have a0 : arg (pushed (argPush 2) s₁).callEntry 0 = F.ptr s₀ := ent_arg hp h (as := [.buf F, .buf G]) (by simp) hg (i := 0) (by simp)
    have a1 : arg (pushed (argPush 2) s₁).callEntry 1 = G.ptr s₀ := ent_arg hp h (as := [.buf F, .buf G]) (by simp) hg (i := 1) (by simp)
    have a0' : arg (pushed (argPush 2) s₁').callEntry 0 = F.ptr s₀' := ent_arg hp' h' (as := [.buf F, .buf G]) (by simp) hg' (i := 0) (by simp)
    have a1' : arg (pushed (argPush 2) s₁').callEntry 1 = G.ptr s₀' := ent_arg hp' h' (as := [.buf F, .buf G]) (by simp) hg' (i := 1) (by simp)
    have eSp : (pushed (argPush 2) s₁).callEntry.gpr .esp = _ := ent_esp h (n := 2) (by decide)
    have eSp' : (pushed (argPush 2) s₁').callEntry.gpr .esp = _ := ent_esp h' (n := 2) (by decide)
    generalize he : (pushed (argPush 2) s₁).callEntry = e at a0 a1 eSp ⊢
    generalize he' : (pushed (argPush 2) s₁').callEntry = e' at a0' a1' eSp' ⊢
    sig_pub [accSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [arg_withRegions, a0, a1, a0', a1', eSp, eSp', e₁, e₂, hq.t.E1, and_self]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Buf.inW hp hF' (Lay.okW_iff.mp hF).2
    · exact stk_W hp (by decide)
  · obtain ⟨s₂, m₂, post⟩ := post
    have a0 : arg (pushed (argPush 2) s₁).callEntry 0 = F.ptr s₀ := ent_arg hp h (as := [.buf F, .buf G]) (by simp) hg (i := 0) (by simp)
    have a1 : arg (pushed (argPush 2) s₁).callEntry 1 = G.ptr s₀ := ent_arg hp h (as := [.buf F, .buf G]) (by simp) hg (i := 1) (by simp)
    generalize he : (pushed (argPush 2) s₁).callEntry = e at a0 a1 post
    sig_post [accSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at post
    subst he
    simp only [arg_withRegions, a0, a1, m₂] at post
    rw [polyAt_congr (ent_bytes hp h (n := 2) (by decide) hF'), polyAt_congr (ent_bytes hp h (n := 2) (by decide) hG),
      m] at post
    exact hQ s₀ s s' hp ha h' (fr80 (by decide) (by have := ok.stk; omega) hp (m ▸ fr)) post

end VG.Proof.MlDsa.X86.Sign
