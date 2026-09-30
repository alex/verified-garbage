import VerifiedGarbage.Proof.MlDsa.X86.Sign.Prims

/-!
# ML-DSA signing on x86 (32-bit): calls of the rounding and hint primitives

Untrusted: everything here is checked by Lean. `HighBits` and `LowBits` of
a polynomial (`hb_piece`, `lb_piece`), the norm check (`norm_piece`) and
`MakeHint` (`hint_piece`), which return their results in `eax`.
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

theorem gamma2_lt {g : Nat} (h : g ∈ gamma2s) : (BitVec.ofNat 32 g).toNat = g := by
  simp only [gamma2s, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl <;> rfl

/-- `out ← HighBits(r)`. -/
theorem hb_piece {nm : String} {c : Prog isa} (hv : Verified X86.target c (highBitsContract X86.abi 16))
    (ok : COk c) (g : Nat) (hγ : g ∈ gamma2s) (ra ro oa oo : Nat)
    (hc : ((Y p).ok ⟨ra, ro, 1024⟩ && (Y p).okW ⟨oa, oo, 1024⟩ && (Y p).sep ⟨ra, ro, 1024⟩ ⟨oa, oo, 1024⟩) = true)
    (hA : ∀ s₀ s, TPre (Y p) s₀ → A s₀ s → Ctx (Y p) s₀ s ∧ Reduced s.mem (Buf.addr s₀ ⟨ra, ro, 1024⟩))
    (hQ : ∀ s₀ s s', TPre (Y p) s₀ → A s₀ s → Ctx (Y p) s₀ s' → Frame (FR s₀ [⟨oa, oo, 1024⟩] 80) s.mem s'.mem →
      NatPolyIs s'.mem (Buf.addr s₀ ⟨oa, oo, 1024⟩)
        ((polyAt s.mem (Buf.addr s₀ ⟨ra, ro, 1024⟩)).map fun c => (highBits g c).toNat) → B s₀ s') :
    SP p A B (callP nm c [.buf ⟨ra, ro, 1024⟩, .imm g, .buf ⟨oa, oo, 1024⟩]) := by
  set R : Buf := ⟨ra, ro, 1024⟩
  set O : Buf := ⟨oa, oo, 1024⟩
  have gl := gamma2_lt hγ
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨hR, hO⟩, dRO⟩ := hc
  have hO' := (Lay.okW_iff.mp hO).1
  refine callP_piece _ 3 rfl hv ok (by decide) (by decide) (by simp [argOk, hR, hO']) (fun s₀ => [R.rgn s₀])
    (fun s₀ => [O.rgn s₀, below (E1 s₀) 12]) (fun s₀ s hp ha => (hA s₀ s hp ha).1)
    (fun s₀ s₁ hp ⟨s, ha, h, m, hg⟩ => ?_) (fun s₀ s₀' s₁ s₁' hp hp' hq ⟨s, ha, h, m, hg⟩ ⟨s', ha', h', m', hg'⟩ => ?_)
    (fun s₀ hp r hr => ?_) (fun s₀ s₁ s' hp ⟨s, ha, h, m, hg⟩ h' fr post => ?_)
  · have a0 : arg (pushed (argPush 3) s₁).callEntry 0 = R.ptr s₀ := ent_arg hp h (as := [.buf R, .imm g, .buf O]) (by simp) hg (i := 0) (by simp)
    have a1 : arg (pushed (argPush 3) s₁).callEntry 1 = BitVec.ofNat 32 g := ent_arg hp h (as := [.buf R, .imm g, .buf O]) (by simp) hg (i := 1) (by simp)
    have a2 : arg (pushed (argPush 3) s₁).callEntry 2 = O.ptr s₀ := ent_arg hp h (as := [.buf R, .imm g, .buf O]) (by simp) hg (i := 2) (by simp)
    have eA : argAddr (pushed (argPush 3) s₁).callEntry 0 = _ := ent_arg0 h (n := 3) (by decide)
    have eSp : (pushed (argPush 3) s₁).callEntry.gpr .esp = _ := ent_esp h (n := 3) (by decide)
    obtain ⟨rR₁, rR₂, rR₃⟩ := ent_rgn hp hR (n := 3) (K := 16) (by decide)
    obtain ⟨rO₁, rO₂, rO₃⟩ := ent_rgn hp hO' (n := 3) (K := 16) (by decide)
    obtain ⟨rA₂, rA₃⟩ := ent_self hp (n := 3) (K := 16) (by decide)
    have hE := E1_big hp
    have cv := covers_of (s := s₁) (n := 3) (rd := [R.rgn s₀]) (wr := [O.rgn s₀, below (E1 s₀) 12])
      (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        subst hr; exact Buf.within hp hR h.rd h.wr) fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact .inr (Buf.withinW hp hO' (Lay.okW_iff.mp hO).2 h.wr)
        · exact .inl (by rw [h.esp])
    refine ⟨?_, cv.1, cv.2⟩
    generalize he : (pushed (argPush 3) s₁).callEntry = e at a0 a1 a2 eA eSp ⊢
    sig_pre [highBitsContract, bitsSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    subst he
    simp only [arg_withRegions, argAddr_withRegions, a0, a1, a2, eA, eSp, gl]
    refine ⟨by rw [sub_toNat (by omega)]; omega, by rw [sub_toNat (by omega)]; have := (E1 s₀).isLt; omega,
      rfl, rfl, Buf.disj hp hR hO' dRO, rR₁, rO₁, rR₂, rO₂, rA₂, rR₃, rO₃, rA₃,
      Buf.fit hp hR, Buf.fit hp hO', hγ, ?_⟩
    exact reduced_congr (ent_bytes hp h (n := 3) (by decide) hR) (m ▸ (hA s₀ s hp ha).2)
  · have e₁ : R.ptr s₀ = R.ptr s₀' := hq.t.ptr hR
    have e₂ : O.ptr s₀ = O.ptr s₀' := hq.t.ptr hO'
    refine ⟨by simp only [Buf.rgn, e₁], by simp only [Buf.rgn, e₂, hq.t.E1], ?_⟩
    have a0 : arg (pushed (argPush 3) s₁).callEntry 0 = R.ptr s₀ := ent_arg hp h (as := [.buf R, .imm g, .buf O]) (by simp) hg (i := 0) (by simp)
    have a1 : arg (pushed (argPush 3) s₁).callEntry 1 = BitVec.ofNat 32 g := ent_arg hp h (as := [.buf R, .imm g, .buf O]) (by simp) hg (i := 1) (by simp)
    have a2 : arg (pushed (argPush 3) s₁).callEntry 2 = O.ptr s₀ := ent_arg hp h (as := [.buf R, .imm g, .buf O]) (by simp) hg (i := 2) (by simp)
    have a0' : arg (pushed (argPush 3) s₁').callEntry 0 = R.ptr s₀' := ent_arg hp' h' (as := [.buf R, .imm g, .buf O]) (by simp) hg' (i := 0) (by simp)
    have a1' : arg (pushed (argPush 3) s₁').callEntry 1 = BitVec.ofNat 32 g := ent_arg hp' h' (as := [.buf R, .imm g, .buf O]) (by simp) hg' (i := 1) (by simp)
    have a2' : arg (pushed (argPush 3) s₁').callEntry 2 = O.ptr s₀' := ent_arg hp' h' (as := [.buf R, .imm g, .buf O]) (by simp) hg' (i := 2) (by simp)
    have eSp : (pushed (argPush 3) s₁).callEntry.gpr .esp = _ := ent_esp h (n := 3) (by decide)
    have eSp' : (pushed (argPush 3) s₁').callEntry.gpr .esp = _ := ent_esp h' (n := 3) (by decide)
    generalize he : (pushed (argPush 3) s₁).callEntry = e at a0 a1 a2 eSp ⊢
    generalize he' : (pushed (argPush 3) s₁').callEntry = e' at a0' a1' a2' eSp' ⊢
    sig_pub [highBitsContract, bitsSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [arg_withRegions, a0, a1, a2, a0', a1', a2', eSp, eSp', e₁, e₂, hq.t.E1, and_self]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Buf.inW hp hO' (Lay.okW_iff.mp hO).2
    · exact stk_W hp (by decide)
  · obtain ⟨s₂, m₂, post⟩ := post
    have a0 : arg (pushed (argPush 3) s₁).callEntry 0 = R.ptr s₀ := ent_arg hp h (as := [.buf R, .imm g, .buf O]) (by simp) hg (i := 0) (by simp)
    have a1 : arg (pushed (argPush 3) s₁).callEntry 1 = BitVec.ofNat 32 g := ent_arg hp h (as := [.buf R, .imm g, .buf O]) (by simp) hg (i := 1) (by simp)
    have a2 : arg (pushed (argPush 3) s₁).callEntry 2 = O.ptr s₀ := ent_arg hp h (as := [.buf R, .imm g, .buf O]) (by simp) hg (i := 2) (by simp)
    generalize he : (pushed (argPush 3) s₁).callEntry = e at a0 a1 a2 post
    sig_post [highBitsContract, bitsSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at post
    subst he
    simp only [arg_withRegions, a0, a1, a2, m₂, gl] at post
    rw [polyAt_congr (ent_bytes hp h (n := 3) (by decide) hR), m] at post
    exact hQ s₀ s s' hp ha h' (fr80 (by decide) (by have := ok.stk; omega) hp (m ▸ fr)) post

/-- `out ← LowBits(r)`, in `R_q`. -/
theorem lb_piece {nm : String} {c : Prog isa} (hv : Verified X86.target c (lowBitsContract X86.abi 16))
    (ok : COk c) (g : Nat) (hγ : g ∈ gamma2s) (ra ro oa oo : Nat)
    (hc : ((Y p).ok ⟨ra, ro, 1024⟩ && (Y p).okW ⟨oa, oo, 1024⟩ && (Y p).sep ⟨ra, ro, 1024⟩ ⟨oa, oo, 1024⟩) = true)
    (hA : ∀ s₀ s, TPre (Y p) s₀ → A s₀ s → Ctx (Y p) s₀ s ∧ Reduced s.mem (Buf.addr s₀ ⟨ra, ro, 1024⟩))
    (hQ : ∀ s₀ s s', TPre (Y p) s₀ → A s₀ s → Ctx (Y p) s₀ s' → Frame (FR s₀ [⟨oa, oo, 1024⟩] 80) s.mem s'.mem →
      PolyIs s'.mem (Buf.addr s₀ ⟨oa, oo, 1024⟩)
        ((polyAt s.mem (Buf.addr s₀ ⟨ra, ro, 1024⟩)).map fun c => ofInt (lowBits g c)) → B s₀ s') :
    SP p A B (callP nm c [.buf ⟨ra, ro, 1024⟩, .imm g, .buf ⟨oa, oo, 1024⟩]) := by
  set R : Buf := ⟨ra, ro, 1024⟩
  set O : Buf := ⟨oa, oo, 1024⟩
  have gl := gamma2_lt hγ
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨hR, hO⟩, dRO⟩ := hc
  have hO' := (Lay.okW_iff.mp hO).1
  refine callP_piece _ 3 rfl hv ok (by decide) (by decide) (by simp [argOk, hR, hO']) (fun s₀ => [R.rgn s₀])
    (fun s₀ => [O.rgn s₀, below (E1 s₀) 12]) (fun s₀ s hp ha => (hA s₀ s hp ha).1)
    (fun s₀ s₁ hp ⟨s, ha, h, m, hg⟩ => ?_) (fun s₀ s₀' s₁ s₁' hp hp' hq ⟨s, ha, h, m, hg⟩ ⟨s', ha', h', m', hg'⟩ => ?_)
    (fun s₀ hp r hr => ?_) (fun s₀ s₁ s' hp ⟨s, ha, h, m, hg⟩ h' fr post => ?_)
  · have a0 : arg (pushed (argPush 3) s₁).callEntry 0 = R.ptr s₀ := ent_arg hp h (as := [.buf R, .imm g, .buf O]) (by simp) hg (i := 0) (by simp)
    have a1 : arg (pushed (argPush 3) s₁).callEntry 1 = BitVec.ofNat 32 g := ent_arg hp h (as := [.buf R, .imm g, .buf O]) (by simp) hg (i := 1) (by simp)
    have a2 : arg (pushed (argPush 3) s₁).callEntry 2 = O.ptr s₀ := ent_arg hp h (as := [.buf R, .imm g, .buf O]) (by simp) hg (i := 2) (by simp)
    have eA : argAddr (pushed (argPush 3) s₁).callEntry 0 = _ := ent_arg0 h (n := 3) (by decide)
    have eSp : (pushed (argPush 3) s₁).callEntry.gpr .esp = _ := ent_esp h (n := 3) (by decide)
    obtain ⟨rR₁, rR₂, rR₃⟩ := ent_rgn hp hR (n := 3) (K := 16) (by decide)
    obtain ⟨rO₁, rO₂, rO₃⟩ := ent_rgn hp hO' (n := 3) (K := 16) (by decide)
    obtain ⟨rA₂, rA₃⟩ := ent_self hp (n := 3) (K := 16) (by decide)
    have hE := E1_big hp
    have cv := covers_of (s := s₁) (n := 3) (rd := [R.rgn s₀]) (wr := [O.rgn s₀, below (E1 s₀) 12])
      (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        subst hr; exact Buf.within hp hR h.rd h.wr) fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact .inr (Buf.withinW hp hO' (Lay.okW_iff.mp hO).2 h.wr)
        · exact .inl (by rw [h.esp])
    refine ⟨?_, cv.1, cv.2⟩
    generalize he : (pushed (argPush 3) s₁).callEntry = e at a0 a1 a2 eA eSp ⊢
    sig_pre [lowBitsContract, bitsSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    subst he
    simp only [arg_withRegions, argAddr_withRegions, a0, a1, a2, eA, eSp, gl]
    refine ⟨by rw [sub_toNat (by omega)]; omega, by rw [sub_toNat (by omega)]; have := (E1 s₀).isLt; omega,
      rfl, rfl, Buf.disj hp hR hO' dRO, rR₁, rO₁, rR₂, rO₂, rA₂, rR₃, rO₃, rA₃,
      Buf.fit hp hR, Buf.fit hp hO', hγ, ?_⟩
    exact reduced_congr (ent_bytes hp h (n := 3) (by decide) hR) (m ▸ (hA s₀ s hp ha).2)
  · have e₁ : R.ptr s₀ = R.ptr s₀' := hq.t.ptr hR
    have e₂ : O.ptr s₀ = O.ptr s₀' := hq.t.ptr hO'
    refine ⟨by simp only [Buf.rgn, e₁], by simp only [Buf.rgn, e₂, hq.t.E1], ?_⟩
    have a0 : arg (pushed (argPush 3) s₁).callEntry 0 = R.ptr s₀ := ent_arg hp h (as := [.buf R, .imm g, .buf O]) (by simp) hg (i := 0) (by simp)
    have a1 : arg (pushed (argPush 3) s₁).callEntry 1 = BitVec.ofNat 32 g := ent_arg hp h (as := [.buf R, .imm g, .buf O]) (by simp) hg (i := 1) (by simp)
    have a2 : arg (pushed (argPush 3) s₁).callEntry 2 = O.ptr s₀ := ent_arg hp h (as := [.buf R, .imm g, .buf O]) (by simp) hg (i := 2) (by simp)
    have a0' : arg (pushed (argPush 3) s₁').callEntry 0 = R.ptr s₀' := ent_arg hp' h' (as := [.buf R, .imm g, .buf O]) (by simp) hg' (i := 0) (by simp)
    have a1' : arg (pushed (argPush 3) s₁').callEntry 1 = BitVec.ofNat 32 g := ent_arg hp' h' (as := [.buf R, .imm g, .buf O]) (by simp) hg' (i := 1) (by simp)
    have a2' : arg (pushed (argPush 3) s₁').callEntry 2 = O.ptr s₀' := ent_arg hp' h' (as := [.buf R, .imm g, .buf O]) (by simp) hg' (i := 2) (by simp)
    have eSp : (pushed (argPush 3) s₁).callEntry.gpr .esp = _ := ent_esp h (n := 3) (by decide)
    have eSp' : (pushed (argPush 3) s₁').callEntry.gpr .esp = _ := ent_esp h' (n := 3) (by decide)
    generalize he : (pushed (argPush 3) s₁).callEntry = e at a0 a1 a2 eSp ⊢
    generalize he' : (pushed (argPush 3) s₁').callEntry = e' at a0' a1' a2' eSp' ⊢
    sig_pub [lowBitsContract, bitsSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [arg_withRegions, a0, a1, a2, a0', a1', a2', eSp, eSp', e₁, e₂, hq.t.E1, and_self]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Buf.inW hp hO' (Lay.okW_iff.mp hO).2
    · exact stk_W hp (by decide)
  · obtain ⟨s₂, m₂, post⟩ := post
    have a0 : arg (pushed (argPush 3) s₁).callEntry 0 = R.ptr s₀ := ent_arg hp h (as := [.buf R, .imm g, .buf O]) (by simp) hg (i := 0) (by simp)
    have a1 : arg (pushed (argPush 3) s₁).callEntry 1 = BitVec.ofNat 32 g := ent_arg hp h (as := [.buf R, .imm g, .buf O]) (by simp) hg (i := 1) (by simp)
    have a2 : arg (pushed (argPush 3) s₁).callEntry 2 = O.ptr s₀ := ent_arg hp h (as := [.buf R, .imm g, .buf O]) (by simp) hg (i := 2) (by simp)
    generalize he : (pushed (argPush 3) s₁).callEntry = e at a0 a1 a2 post
    sig_post [lowBitsContract, bitsSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at post
    subst he
    simp only [arg_withRegions, a0, a1, a2, m₂, gl] at post
    rw [polyAt_congr (ent_bytes hp h (n := 3) (by decide) hR), m] at post
    exact hQ s₀ s s' hp ha h' (fr80 (by decide) (by have := ok.stk; omega) hp (m ▸ fr)) post

/-- `eax ← ‖f‖∞ < bound`. -/
theorem norm_piece {nm : String} {c : Prog isa} (hv : Verified X86.target c (normLtContract X86.abi 16))
    (ok : COk c) (bnd : Nat) (hb : bnd < 2 ^ 32) (fa fo : Nat) (hc : (Y p).ok ⟨fa, fo, 1024⟩ = true)
    (hA : ∀ s₀ s, TPre (Y p) s₀ → A s₀ s → Ctx (Y p) s₀ s ∧ Reduced s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩))
    (hQ : ∀ s₀ s s', TPre (Y p) s₀ → A s₀ s → Ctx (Y p) s₀ s' → Frame (FR s₀ [] 80) s.mem s'.mem →
      s'.gpr .eax = (if normRq [polyAt s.mem (Buf.addr s₀ ⟨fa, fo, 1024⟩)] < bnd then 1 else 0) → B s₀ s') :
    SP p A B (callPR nm c [.buf ⟨fa, fo, 1024⟩, .imm bnd]) := by
  set F : Buf := ⟨fa, fo, 1024⟩
  have bl : (BitVec.ofNat 32 bnd).toNat = bnd := by rw [BitVec.toNat_ofNat]; omega
  refine callPR_piece _ 2 rfl hv ok (by decide) (by decide) (by simp [argOk, hc]) (fun s₀ => [F.rgn s₀, below (E1 s₀) 8])
    (fun _ => []) (fun s₀ s hp ha => (hA s₀ s hp ha).1)
    (fun s₀ s₁ hp ⟨s, ha, h, m, hg⟩ => ?_) (fun s₀ s₀' s₁ s₁' hp hp' hq ⟨s, ha, h, m, hg⟩ ⟨s', ha', h', m', hg'⟩ => ?_)
    (fun s₀ hp r hr => absurd hr List.not_mem_nil) (fun s₀ s₁ s' hp ⟨s, ha, h, m, hg⟩ h' fr post => ?_)
  · have a0 : arg (pushed (argPush 2) s₁).callEntry 0 = F.ptr s₀ := ent_arg hp h (as := [.buf F, .imm bnd]) (by simp) hg (i := 0) (by simp)
    have a1 : arg (pushed (argPush 2) s₁).callEntry 1 = BitVec.ofNat 32 bnd := ent_arg hp h (as := [.buf F, .imm bnd]) (by simp) hg (i := 1) (by simp)
    have eA : argAddr (pushed (argPush 2) s₁).callEntry 0 = _ := ent_arg0 h (n := 2) (by decide)
    have eSp : (pushed (argPush 2) s₁).callEntry.gpr .esp = _ := ent_esp h (n := 2) (by decide)
    obtain ⟨rF₁, rF₂, rF₃⟩ := ent_rgn hp hc (n := 2) (K := 16) (by decide)
    obtain ⟨rA₂, rA₃⟩ := ent_self hp (n := 2) (K := 16) (by decide)
    have hE := E1_big hp
    have cv := covers_ro (s := s₁) (n := 2) (rd := [F.rgn s₀, below (E1 s₀) 8]) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact .inr (Buf.within hp hc h.rd h.wr)
      · exact .inl (by rw [h.esp])
    refine ⟨?_, cv.1, cv.2⟩
    generalize he : (pushed (argPush 2) s₁).callEntry = e at a0 a1 eA eSp ⊢
    sig_pre [normLtContract, normLtSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    subst he
    simp only [arg_withRegions, argAddr_withRegions, a0, eA, eSp]
    refine ⟨by rw [sub_toNat (by omega)]; omega, by rw [sub_toNat (by omega)]; have := (E1 s₀).isLt; omega,
      rfl, rF₂, rA₂, rF₃, rA₃, Buf.fit hp hc, ?_⟩
    exact reduced_congr (ent_bytes hp h (n := 2) (by decide) hc) (m ▸ (hA s₀ s hp ha).2)
  · have e₁ : F.ptr s₀ = F.ptr s₀' := hq.t.ptr hc
    refine ⟨by simp only [Buf.rgn, e₁, hq.t.E1], rfl, ?_⟩
    have a0 : arg (pushed (argPush 2) s₁).callEntry 0 = F.ptr s₀ := ent_arg hp h (as := [.buf F, .imm bnd]) (by simp) hg (i := 0) (by simp)
    have a1 : arg (pushed (argPush 2) s₁).callEntry 1 = BitVec.ofNat 32 bnd := ent_arg hp h (as := [.buf F, .imm bnd]) (by simp) hg (i := 1) (by simp)
    have a0' : arg (pushed (argPush 2) s₁').callEntry 0 = F.ptr s₀' := ent_arg hp' h' (as := [.buf F, .imm bnd]) (by simp) hg' (i := 0) (by simp)
    have a1' : arg (pushed (argPush 2) s₁').callEntry 1 = BitVec.ofNat 32 bnd := ent_arg hp' h' (as := [.buf F, .imm bnd]) (by simp) hg' (i := 1) (by simp)
    have eSp : (pushed (argPush 2) s₁).callEntry.gpr .esp = _ := ent_esp h (n := 2) (by decide)
    have eSp' : (pushed (argPush 2) s₁').callEntry.gpr .esp = _ := ent_esp h' (n := 2) (by decide)
    generalize he : (pushed (argPush 2) s₁).callEntry = e at a0 a1 eSp ⊢
    generalize he' : (pushed (argPush 2) s₁').callEntry = e' at a0' a1' eSp' ⊢
    sig_pub [normLtContract, normLtSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [arg_withRegions, a0, a1, a0', a1', eSp, eSp', e₁, hq.t.E1, and_self]
  · obtain ⟨s₂, m₂, g₂, post⟩ := post
    have a0 : arg (pushed (argPush 2) s₁).callEntry 0 = F.ptr s₀ := ent_arg hp h (as := [.buf F, .imm bnd]) (by simp) hg (i := 0) (by simp)
    have a1 : arg (pushed (argPush 2) s₁).callEntry 1 = BitVec.ofNat 32 bnd := ent_arg hp h (as := [.buf F, .imm bnd]) (by simp) hg (i := 1) (by simp)
    generalize he : (pushed (argPush 2) s₁).callEntry = e at a0 a1 post
    sig_post [normLtContract, normLtSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at post
    subst he
    simp only [arg_withRegions, a0, a1, sw32, g₂, bl] at post
    rw [polyAt_congr (ent_bytes hp h (n := 2) (by decide) hc), m] at post
    refine hQ s₀ s s' hp ha h' ((m ▸ fr).sub fun r hr => ?_) post
    simp only [List.nil_append, List.mem_singleton] at hr; subst hr
    exact ⟨below (E1 s₀) 80, by simp [FR], stk_sub hp (by have := ok.stk; omega) (by show 80 + 16 ≤ 96; omega)⟩

/-- `h ← MakeHint(z, r)`, returning the number of 1s in `eax`. -/
theorem hint_piece {nm : String} {c : Prog isa} (hv : Verified X86.target c (makeHintContract X86.abi 16))
    (ok : COk c) (g : Nat) (hγ : g ∈ gamma2s) (za zo ra ro ha ho : Nat)
    (hc : ((Y p).ok ⟨za, zo, 1024⟩ && (Y p).ok ⟨ra, ro, 1024⟩ && (Y p).okW ⟨ha, ho, 1024⟩ &&
      (Y p).sep ⟨za, zo, 1024⟩ ⟨ha, ho, 1024⟩ && (Y p).sep ⟨ra, ro, 1024⟩ ⟨ha, ho, 1024⟩) = true)
    (hA : ∀ s₀ s, TPre (Y p) s₀ → A s₀ s → Ctx (Y p) s₀ s ∧ Reduced s.mem (Buf.addr s₀ ⟨za, zo, 1024⟩) ∧
      Reduced s.mem (Buf.addr s₀ ⟨ra, ro, 1024⟩))
    (hQ : ∀ s₀ s s', TPre (Y p) s₀ → A s₀ s → Ctx (Y p) s₀ s' → Frame (FR s₀ [⟨ha, ho, 1024⟩] 80) s.mem s'.mem →
      HintIs s'.mem (Buf.addr s₀ ⟨ha, ho, 1024⟩) 1 [Vector.zipWith (makeHint g) (polyAt s.mem (Buf.addr s₀ ⟨za, zo, 1024⟩))
        (polyAt s.mem (Buf.addr s₀ ⟨ra, ro, 1024⟩))] →
      (s'.gpr .eax).toNat = hintOnes [Vector.zipWith (makeHint g) (polyAt s.mem (Buf.addr s₀ ⟨za, zo, 1024⟩))
        (polyAt s.mem (Buf.addr s₀ ⟨ra, ro, 1024⟩))] → B s₀ s') :
    SP p A B (callPR nm c [.buf ⟨za, zo, 1024⟩, .buf ⟨ra, ro, 1024⟩, .imm g, .buf ⟨ha, ho, 1024⟩]) := by
  set Z : Buf := ⟨za, zo, 1024⟩
  set R : Buf := ⟨ra, ro, 1024⟩
  set H : Buf := ⟨ha, ho, 1024⟩
  have gl := gamma2_lt hγ
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨hZ, hR⟩, hH⟩, dZH⟩, dRH⟩ := hc
  have hH' := (Lay.okW_iff.mp hH).1
  refine callPR_piece _ 4 rfl hv ok (by decide) (by decide) (by simp [argOk, hZ, hR, hH']) (fun s₀ => [Z.rgn s₀, R.rgn s₀])
    (fun s₀ => [H.rgn s₀, below (E1 s₀) 16]) (fun s₀ s hp ha => (hA s₀ s hp ha).1)
    (fun s₀ s₁ hp ⟨s, ha, h, m, hg⟩ => ?_) (fun s₀ s₀' s₁ s₁' hp hp' hq ⟨s, ha, h, m, hg⟩ ⟨s', ha', h', m', hg'⟩ => ?_)
    (fun s₀ hp r hr => ?_) (fun s₀ s₁ s' hp ⟨s, ha, h, m, hg⟩ h' fr post => ?_)
  · have a0 : arg (pushed (argPush 4) s₁).callEntry 0 = Z.ptr s₀ := ent_arg hp h (as := [.buf Z, .buf R, .imm g, .buf H]) (by simp) hg (i := 0) (by simp)
    have a1 : arg (pushed (argPush 4) s₁).callEntry 1 = R.ptr s₀ := ent_arg hp h (as := [.buf Z, .buf R, .imm g, .buf H]) (by simp) hg (i := 1) (by simp)
    have a2 : arg (pushed (argPush 4) s₁).callEntry 2 = BitVec.ofNat 32 g := ent_arg hp h (as := [.buf Z, .buf R, .imm g, .buf H]) (by simp) hg (i := 2) (by simp)
    have a3 : arg (pushed (argPush 4) s₁).callEntry 3 = H.ptr s₀ := ent_arg hp h (as := [.buf Z, .buf R, .imm g, .buf H]) (by simp) hg (i := 3) (by simp)
    have eA : argAddr (pushed (argPush 4) s₁).callEntry 0 = _ := ent_arg0 h (n := 4) (by decide)
    have eSp : (pushed (argPush 4) s₁).callEntry.gpr .esp = _ := ent_esp h (n := 4) (by decide)
    obtain ⟨rZ₁, rZ₂, rZ₃⟩ := ent_rgn hp hZ (n := 4) (K := 16) (by decide)
    obtain ⟨rR₁, rR₂, rR₃⟩ := ent_rgn hp hR (n := 4) (K := 16) (by decide)
    obtain ⟨rH₁, rH₂, rH₃⟩ := ent_rgn hp hH' (n := 4) (K := 16) (by decide)
    obtain ⟨rA₂, rA₃⟩ := ent_self hp (n := 4) (K := 16) (by decide)
    have hE := E1_big hp
    have cv := covers_of (s := s₁) (n := 4) (rd := [Z.rgn s₀, R.rgn s₀]) (wr := [H.rgn s₀, below (E1 s₀) 16])
      (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact Buf.within hp hZ h.rd h.wr
        · exact Buf.within hp hR h.rd h.wr) fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact .inr (Buf.withinW hp hH' (Lay.okW_iff.mp hH).2 h.wr)
        · exact .inl (by rw [h.esp])
    refine ⟨?_, cv.1, cv.2⟩
    generalize he : (pushed (argPush 4) s₁).callEntry = e at a0 a1 a2 a3 eA eSp ⊢
    sig_pre [makeHintContract, makeHintSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    subst he
    simp only [arg_withRegions, argAddr_withRegions, a0, a1, a2, a3, eA, eSp, gl]
    refine ⟨by rw [sub_toNat (by omega)]; omega, by rw [sub_toNat (by omega)]; have := (E1 s₀).isLt; omega,
      rfl, rfl, Buf.disj hp hZ hH' dZH, rZ₁, Buf.disj hp hR hH' dRH, rR₁, rH₁, rZ₂, rR₂, rH₂, rA₂, rZ₃, rR₃, rH₃, rA₃,
      Buf.fit hp hZ, Buf.fit hp hR, Buf.fit hp hH', hγ, ?_, ?_⟩
    · exact reduced_congr (ent_bytes hp h (n := 4) (by decide) hZ) (m ▸ (hA s₀ s hp ha).2.1)
    · exact reduced_congr (ent_bytes hp h (n := 4) (by decide) hR) (m ▸ (hA s₀ s hp ha).2.2)
  · have e₁ : Z.ptr s₀ = Z.ptr s₀' := hq.t.ptr hZ
    have e₂ : R.ptr s₀ = R.ptr s₀' := hq.t.ptr hR
    have e₃ : H.ptr s₀ = H.ptr s₀' := hq.t.ptr hH'
    refine ⟨by simp only [Buf.rgn, e₁, e₂], by simp only [Buf.rgn, e₃, hq.t.E1], ?_⟩
    have a0 : arg (pushed (argPush 4) s₁).callEntry 0 = Z.ptr s₀ := ent_arg hp h (as := [.buf Z, .buf R, .imm g, .buf H]) (by simp) hg (i := 0) (by simp)
    have a1 : arg (pushed (argPush 4) s₁).callEntry 1 = R.ptr s₀ := ent_arg hp h (as := [.buf Z, .buf R, .imm g, .buf H]) (by simp) hg (i := 1) (by simp)
    have a2 : arg (pushed (argPush 4) s₁).callEntry 2 = BitVec.ofNat 32 g := ent_arg hp h (as := [.buf Z, .buf R, .imm g, .buf H]) (by simp) hg (i := 2) (by simp)
    have a3 : arg (pushed (argPush 4) s₁).callEntry 3 = H.ptr s₀ := ent_arg hp h (as := [.buf Z, .buf R, .imm g, .buf H]) (by simp) hg (i := 3) (by simp)
    have a0' : arg (pushed (argPush 4) s₁').callEntry 0 = Z.ptr s₀' := ent_arg hp' h' (as := [.buf Z, .buf R, .imm g, .buf H]) (by simp) hg' (i := 0) (by simp)
    have a1' : arg (pushed (argPush 4) s₁').callEntry 1 = R.ptr s₀' := ent_arg hp' h' (as := [.buf Z, .buf R, .imm g, .buf H]) (by simp) hg' (i := 1) (by simp)
    have a2' : arg (pushed (argPush 4) s₁').callEntry 2 = BitVec.ofNat 32 g := ent_arg hp' h' (as := [.buf Z, .buf R, .imm g, .buf H]) (by simp) hg' (i := 2) (by simp)
    have a3' : arg (pushed (argPush 4) s₁').callEntry 3 = H.ptr s₀' := ent_arg hp' h' (as := [.buf Z, .buf R, .imm g, .buf H]) (by simp) hg' (i := 3) (by simp)
    have eSp : (pushed (argPush 4) s₁).callEntry.gpr .esp = _ := ent_esp h (n := 4) (by decide)
    have eSp' : (pushed (argPush 4) s₁').callEntry.gpr .esp = _ := ent_esp h' (n := 4) (by decide)
    generalize he : (pushed (argPush 4) s₁).callEntry = e at a0 a1 a2 a3 eSp ⊢
    generalize he' : (pushed (argPush 4) s₁').callEntry = e' at a0' a1' a2' a3' eSp' ⊢
    sig_pub [makeHintContract, makeHintSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [arg_withRegions, a0, a1, a2, a3, a0', a1', a2', a3', eSp, eSp', e₁, e₂, e₃, hq.t.E1, and_self]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Buf.inW hp hH' (Lay.okW_iff.mp hH).2
    · exact stk_W hp (by decide)
  · obtain ⟨s₂, m₂, g₂, post⟩ := post
    have a0 : arg (pushed (argPush 4) s₁).callEntry 0 = Z.ptr s₀ := ent_arg hp h (as := [.buf Z, .buf R, .imm g, .buf H]) (by simp) hg (i := 0) (by simp)
    have a1 : arg (pushed (argPush 4) s₁).callEntry 1 = R.ptr s₀ := ent_arg hp h (as := [.buf Z, .buf R, .imm g, .buf H]) (by simp) hg (i := 1) (by simp)
    have a2 : arg (pushed (argPush 4) s₁).callEntry 2 = BitVec.ofNat 32 g := ent_arg hp h (as := [.buf Z, .buf R, .imm g, .buf H]) (by simp) hg (i := 2) (by simp)
    have a3 : arg (pushed (argPush 4) s₁).callEntry 3 = H.ptr s₀ := ent_arg hp h (as := [.buf Z, .buf R, .imm g, .buf H]) (by simp) hg (i := 3) (by simp)
    generalize he : (pushed (argPush 4) s₁).callEntry = e at a0 a1 a2 a3 post
    sig_post [makeHintContract, makeHintSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at post
    subst he
    simp only [arg_withRegions, a0, a1, a2, a3, m₂, sw32, g₂, gl] at post
    rw [polyAt_congr (ent_bytes hp h (n := 4) (by decide) hZ), polyAt_congr (ent_bytes hp h (n := 4) (by decide) hR),
      m] at post
    exact hQ s₀ s s' hp ha h' (fr80 (by decide) (by have := ok.stk; omega) hp (m ▸ fr)) post.1 post.2

end VG.Proof.MlDsa.X86.Sign
