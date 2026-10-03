import VerifiedGarbage.Proof.Bignum.X86_64.CTExp

/-!
# `vg_rsa_public` on x86-64: `R² mod m` is constant time but for `m`

`double` and `doubles` (`doubles_ct`), whose count is public, and the
computation of `R² mod m` (`r2_ct`), which branches on the top word of the
public modulus.
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.MlKem.X86_64

/-- `double`'s loads. -/
def dblHead (mo acc tmp o : Nat) : List Instr :=
  [.mov .rbx (.mem (hdr (sArr o))), .mov .r10 (.mem (hdr (sArr mo))), .mov .r8 (.mem (hdr (sArr acc))),
    .mov .r12 (.mem (hdr sW)), .mov .rsi (.mem (hdr (sArr tmp))), .mov32 .rbp (.imm 0)]

/-- After `double`'s loads. -/
def DblHeadL (mo acc tmp o : Nat) (L : Lay) (t : State) : Prop :=
  t.gpr .rbx = off L.B (slot L.w o) ∧ t.gpr .r10 = off L.B (slot L.w mo) ∧
    t.gpr .r8 = off L.B (slot L.w acc) ∧ t.gpr .r12 = BitVec.ofNat 64 L.w ∧
    t.gpr .rsi = off L.B (slot L.w tmp)

theorem dblHead_ok {L : Lay} {t : State} (hg : GoodL L t) {mo acc tmp o : Nat} (hmo : mo < 8) (hacc : acc < 8)
    (htmp : tmp < 8) (ho : o < 8) : WP isa (.block (dblHead mo acc tmp o)) t (DblHeadL mo acc tmp o L) := by
  have hl : ∀ i < 32, InRegions (t.rd ++ t.wr) (off L.B (8 * i)) 8 := fun i hi =>
    hg.1.scr.ld (by have := hdr_lt_slot L.w 8 hi; have := hg.2; omega)
  refine WP.mono (WP.keep [.rbx, .r10, .r8, .r12, .rsi, .rbp] (Q := DblHeadL mo acc tmp o L) ?_ rfl)
    fun t' h => h.1
  unfold dblHead DblHeadL
  xrun [State.ea, hdr, hg.1.rdi, hdrOff, hl (sArr o) (by unfold sArr; omega),
    hl (sArr mo) (by unfold sArr; omega), hl (sArr acc) (by unfold sArr; omega), hl sW (by decide),
    hl (sArr tmp) (by unfold sArr; omega), hg.1.hdr.harr o ho, hg.1.hdr.harr mo hmo, hg.1.hdr.harr acc hacc,
    hg.1.hdr.harr tmp htmp, hg.1.hdr.hw]

theorem pins_dblHead (mo acc tmp o : Nat) : Pins (DblHeadL mo acc tmp o) [.rbx, .r10, .r8, .r12, .rsi] := by
  intro L s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  obtain ⟨a₁, b₁, c₁, d₁, e₁⟩ := h₁
  obtain ⟨a₂, b₂, c₂, d₂, e₂⟩ := h₂
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [a₁, a₂]
  · rw [b₁, b₂]
  · rw [c₁, c₂]
  · rw [d₁, d₂]
  · rw [e₁, e₂]

/-- `double` leaks the same in runs with the same working space. -/
theorem double_ct {mo acc tmp o : Nat} (hmo : mo < 8) (hacc : acc < 8) (htmp : tmp < 8) (ho : o < 8)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (h : (taint.check (Taint.ofRegs [.rdi]) (.block (dblHead mo acc tmp o)) hc).isSome = true) :
    RelCT isa (Two GoodL) (double mo acc tmp o) fun _ _ => True :=
  RelCT.seq (two_piece _ pins_good h fun _ _ hg => dblHead_ok hg hmo hacc htmp ho)
    (two_taint _ (pins_dblHead mo acc tmp o) (by taint_decide))

/-- The public data of `doubles`: the working space and the count. -/
structure DblPub where
  L : Lay
  c : Nat

/-- What `doubles` keeps, after `j` doublings. -/
def DblsAt (mo acc tmp o sl : Nat) (p : DblPub) (j : Nat) (t : State) : Prop :=
  ∃ (σ : State) (O N : Nat), DblsInv σ p.L.B p.L.Z p.L.w p.L.minv mo acc tmp o sl p.c O N j t ∧
    slot p.L.w 8 ≤ p.L.Z ∧ 2 ≤ p.L.w ∧ p.L.w < 2 ^ 31 ∧ p.c < 2 ^ 31 ∧ 0 < N

theorem dblsAt_good {mo acc tmp o sl : Nat} {p : DblPub} {j : Nat} {t : State}
    (h : DblsAt mo acc tmp o sl p j t) : GoodL p.L t :=
  let ⟨_, _, _, hI, hZ, _⟩ := h; ⟨⟨hI.scr, hI.rdi, hI.hdr⟩, hZ⟩

/-- `doubles` leaks the same in runs with the same working space and count. -/
theorem doubles_ct {mo acc tmp o sl : Nat} (hmo : mo < 8) (hacc : acc < 8) (htmp : tmp < 8) (ho : o < 8)
    (d1 : acc ≠ mo) (d2 : acc ≠ tmp) (d3 : acc ≠ o) (d6 : tmp ≠ mo) (d7 : tmp ≠ o) (d8 : o ≠ mo)
    (hsl : 16 ≤ sl) (hsl' : sl < 32) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (h : (taint.check (Taint.ofRegs [.rdi]) (.block (dblHead mo acc tmp o)) hc).isSome = true)
    {hc' : VG.Taint.Hint VG.X86_64.Taint.T}
    (h' : (taint.check (Taint.ofRegs [.rdi]) (.block [.store (hdr sl) .rcx]) hc').isSome = true)
    {hc'' : VG.Taint.Hint VG.X86_64.Taint.T}
    (h'' : (taint.check (Taint.ofRegs [.rdi]) (.block (dblCount sl)) hc'').isSome = true) :
    RelCT isa (Two fun (p : DblPub) s => GoodL p.L s ∧ 2 ≤ p.L.w ∧ p.L.w < 2 ^ 31 ∧ 1 ≤ p.c ∧
      p.c < 2 ^ 31 ∧ s.gpr .rcx = BitVec.ofNat 64 p.c ∧
      wv s.mem p.L.B (slot p.L.w o) p.L.w < wv s.mem p.L.B (slot p.L.w mo) p.L.w)
      (doubles mo acc tmp o sl) (Two fun p s => DblsAt mo acc tmp o sl p p.c s) := by
  rw [doubles_eq]
  refine RelCT.seq (two_piece (Ψ := fun p s => 0 < p.c ∧ DblsAt mo acc tmp o sl p 0 s) _
    (fun p s₁ s₂ h₁ h₂ => pins_good p.L s₁ s₂ h₁.1 h₂.1) h' ?_) ?_
  · rintro p s ⟨hg, hw, hw', hc1, hc', hcx, hO⟩
    exact WP.mono (dblStart_ok (acc := acc) (tmp := tmp) hg.1.scr hg.1.rdi hg.1.hdr hg.2 hmo ho hsl hsl' hcx hO)
      fun t hI => ⟨by omega, s, _, _, hI, hg.2, hw, hw', hc', by omega⟩
  refine two_loop (Φ := DblsAt mo acc tmp o sl) (fun p => p.c) ?_ ?_
  · refine RelCT.seq (two_post (Ψ := fun (q : DblPub × Nat) s => GoodL q.1.L s)
      (two_map (·.1.L) (fun _ _ h => dblsAt_good h.2) (double_ct hmo hacc htmp ho h)) ?_)
      (two_taint _ (fun q s₁ s₂ h₁ h₂ => pins_good q.1.L s₁ s₂ h₁ h₂) h'')
    rintro ⟨p, j⟩ s ⟨hj, σ, O, N, hI, hZ, hw, hw', hc', hN0⟩
    exact WP.mono (double_ok hI.scr hI.rdi hI.hdr hZ hw hw' hmo hacc htmp ho d1 d2 d3 d6 d7
      (by rw [hI.ov, hI.nv]; exact Nat.mod_lt _ hN0)) fun t ⟨_, ha, k⟩ =>
        ⟨⟨hI.scr.congr k.2.2, (k.gpr (by decide)).trans hI.rdi, ha.hdr hI.hdr⟩, hZ⟩
  · rintro p j s hj ⟨σ, O, N, hI, hZ, hw, hw', hc', hN0⟩
    exact WP.mono (dblIter_ok hZ hw hw' hmo hacc htmp ho d1 d2 d3 d6 d7 d8 hsl hsl' hc' hN0 hj hI)
      fun t ⟨hz, hI'⟩ => ⟨eval_ne_count hj hz, fun _ => ⟨σ, O, N, hI', hZ, hw, hw', hc', hN0⟩,
        fun e => e ▸ ⟨σ, O, N, hI', hZ, hw, hw', hc', hN0⟩⟩

/-! ## Squarings -/

/-- What a squaring of `[aR2]` needs. -/
def SqPre (L : Lay) (s : State) : Prop :=
  GoodL L s ∧ 2 ≤ L.w ∧ L.w < 2 ^ 31 ∧
    ((word s.mem L.B (slot L.w aN)).toNat * L.minv.toNat + 1) % 2 ^ 64 = 0 ∧
    wv s.mem L.B (slot L.w aR2) L.w < wv s.mem L.B (slot L.w aN) L.w

theorem sqs_ct (n : Nat) : RelCT isa (Two SqPre) (seqs (List.replicate (n + 1) (mm aR2 aR2 aR2)))
    fun _ _ => True := by
  have one : RelCT isa (Two SqPre) (mm aR2 aR2 aR2) fun _ _ => True :=
    two_map id (fun _ _ h => h.1)
      (montMul_ct (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by taint_decide))
  induction n with
  | zero => exact one
  | succ n ih =>
    show RelCT isa (Two SqPre) (.seq (mm aR2 aR2 aR2) (seqs (List.replicate (n + 1) (mm aR2 aR2 aR2)))) _
    refine RelCT.seq (two_post (Ψ := SqPre) one fun L s ⟨hg, hw, hw', hinv, hlt⟩ =>
      WP.mono (mm_mid hg hw hw' (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) hinv hlt) fun t ⟨g, n, i, lt, _⟩ => ⟨g, hw, hw', i, by rw [n]; exact lt⟩) ih

/-! ## `R² mod m` -/

/-- The public data of `R² mod m`: the working space and `m`. -/
structure R2Pub where
  L : Lay
  N : Nat

/-- The top word of `m`. -/
def R2Pub.top (p : R2Pub) : Nat := p.N / 2 ^ (64 * (p.L.w - 1))

/-- The doublings' count, `64 - j + w` for the top bit `j` of the top word. -/
def R2Pub.cnt (p : R2Pub) : Nat := 64 - p.top.log2 + p.L.w

/-- `r2_ok`'s hypotheses. -/
def R2Pre (p : R2Pub) (s : State) : Prop :=
  GoodL p.L s ∧ 2 ≤ p.L.w ∧ p.L.w < 2 ^ 30 ∧ wv s.mem p.L.B (slot p.L.w aN) p.L.w = p.N ∧
    ((word s.mem p.L.B (slot p.L.w aN)).toNat * p.L.minv.toNat + 1) % 2 ^ 64 = 0 ∧
    s.gpr .r12 = BitVec.ofNat 64 p.L.w ∧ s.gpr .r10 = off p.L.B (slot p.L.w aN) ∧ p.N % 2 = 1 ∧
    2 ^ (64 * (p.L.w - 1)) ≤ p.N

/-- What the top word of `m` gives. -/
theorem r2top {p : R2Pub} {s : State} (hw : 2 ≤ p.L.w) (hn : wv s.mem p.L.B (slot p.L.w aN) p.L.w = p.N)
    (hodd : p.N % 2 = 1) (hlo : 2 ^ (64 * (p.L.w - 1)) ≤ p.N) :
    (word s.mem p.L.B (slot p.L.w aN + 8 * (p.L.w - 1))).toNat = p.top ∧ 0 < p.top ∧ p.top < 2 ^ 64 ∧
      p.top.log2 < 64 ∧ 2 ^ p.top.log2 * 2 ^ (64 * (p.L.w - 1)) < p.N := by
  have hsplit : p.N = p.N % 2 ^ (64 * (p.L.w - 1)) +
      2 ^ (64 * (p.L.w - 1)) * (word s.mem p.L.B (slot p.L.w aN + 8 * (p.L.w - 1))).toNat := by
    have e : wv s.mem p.L.B (slot p.L.w aN) (p.L.w - 1 + 1) = p.N := by
      rw [Nat.sub_add_cancel (by omega : 1 ≤ p.L.w)]; exact hn
    rw [wv] at e
    have hlt := wv_lt s.mem p.L.B (slot p.L.w aN) (p.L.w - 1)
    rw [← e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
  have hT : (word s.mem p.L.B (slot p.L.w aN + 8 * (p.L.w - 1))).toNat = p.top := by
    unfold R2Pub.top
    have hP := Nat.two_pow_pos (64 * (p.L.w - 1))
    have := Nat.mod_lt p.N hP
    rw [Nat.div_eq_of_lt_le (k := (word s.mem p.L.B (slot p.L.w aN + 8 * (p.L.w - 1))).toNat) ?_ ?_]
    · rw [Nat.mul_comm]; omega
    · rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm]; omega
  rw [hT] at hsplit
  have hT0 : 0 < p.top := by
    rcases Nat.eq_zero_or_pos p.top with h | h
    · rw [h, Nat.mul_zero, Nat.add_zero] at hsplit
      have := Nat.mod_lt p.N (Nat.two_pow_pos (64 * (p.L.w - 1))); omega
    · exact h
  have hT1 : p.top < 2 ^ 64 := hT ▸ BitVec.isLt _
  exact ⟨hT, hT0, hT1, (Nat.log2_lt (by omega)).mpr hT1,
    start_lt hw hodd hsplit (Nat.log2_self_le (n := p.top) (by omega))⟩

theorem R2Pre.top {p : R2Pub} {s : State} (h : R2Pre p s) :
    (word s.mem p.L.B (slot p.L.w aN + 8 * (p.L.w - 1))).toNat = p.top ∧ 0 < p.top ∧ p.top < 2 ^ 64 ∧
      p.top.log2 < 64 ∧ 2 ^ p.top.log2 * 2 ^ (64 * (p.L.w - 1)) < p.N :=
  r2top h.2.1 h.2.2.2.1 h.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2

theorem pins_r2Pre : Pins R2Pre [.r10, .r12] := by
  intro p s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [h₁.2.2.2.2.2.2.1, h₂.2.2.2.2.2.2.1]
  · rw [h₁.2.2.2.2.2.1, h₂.2.2.2.2.2.1]

/-- After the top word's load. -/
def R2a (p : R2Pub) (s : State) : Prop := R2Pre p s ∧ s.gpr .rax = BitVec.ofNat 64 p.top

/-- After `topBit`. -/
def R2b (p : R2Pub) (s : State) : Prop :=
  R2Pre p s ∧ s.gpr .rdx = BitVec.ofNat 64 (2 ^ p.top.log2) ∧ s.gpr .rcx = BitVec.ofNat 64 (64 - p.top.log2)

/-- Before and after `setWord`'s load. -/
def R2c (p : R2Pub) (s : State) : Prop :=
  GoodL p.L s ∧ 2 ≤ p.L.w ∧ p.L.w < 2 ^ 30 ∧ wv s.mem p.L.B (slot p.L.w aN) p.L.w = p.N ∧
    ((word s.mem p.L.B (slot p.L.w aN)).toNat * p.L.minv.toNat + 1) % 2 ^ 64 = 0 ∧
    s.gpr .r12 = BitVec.ofNat 64 p.L.w ∧ s.gpr .rcx = BitVec.ofNat 64 (p.L.w - 1) ∧
    s.gpr .rdx = BitVec.ofNat 64 (2 ^ p.top.log2) ∧
    word s.mem p.L.B (8 * sCnt) = BitVec.ofNat 64 (64 - p.top.log2) ∧ p.N % 2 = 1 ∧
    2 ^ (64 * (p.L.w - 1)) ≤ p.N

/-- After the start, `2^(b - 1)`. -/
def R2d (p : R2Pub) (s : State) : Prop :=
  GoodL p.L s ∧ 2 ≤ p.L.w ∧ p.L.w < 2 ^ 30 ∧ wv s.mem p.L.B (slot p.L.w aN) p.L.w = p.N ∧
    ((word s.mem p.L.B (slot p.L.w aN)).toNat * p.L.minv.toNat + 1) % 2 ^ 64 = 0 ∧
    word s.mem p.L.B (8 * sCnt) = BitVec.ofNat 64 (64 - p.top.log2) ∧ p.N % 2 = 1 ∧
    2 ^ (64 * (p.L.w - 1)) ≤ p.N ∧
    wv s.mem p.L.B (slot p.L.w aR2) p.L.w = 2 ^ p.top.log2 * 2 ^ (64 * (p.L.w - 1))

/-- Before the doublings. -/
def R2e (p : R2Pub) (s : State) : Prop :=
  R2d p s ∧ s.gpr .rcx = BitVec.ofNat 64 p.cnt

theorem pins_rdi_of {α : Type} {Φ : α → State → Prop} (L : α → Lay) (h : ∀ a s, Φ a s → GoodL (L a) s) :
    Pins Φ [.rdi] := fun a s₁ s₂ h₁ h₂ => pins_good (L a) s₁ s₂ (h a s₁ h₁) (h a s₂ h₂)

theorem setWord_eq (o : Nat) (i : Reg) : setWord o i =
    .seq (.block [.mov .r8 (.mem (hdr (sArr o)))]) (.seq zeroAccLoop (.block [.store (ix .r8 i) .rdx])) := rfl

/-- `R² mod m` leaks the same in runs that agree on `m`. -/
theorem r2_ct : RelCT isa (Two R2Pre) (seqs r2Steps) fun _ _ => True := by
  unfold r2Steps
  -- The top word.
  refine RelCT.seq (two_piece (Ψ := R2a) _ pins_r2Pre (by taint_decide) ?_) ?_
  · intro p s h
    obtain ⟨hT, -⟩ := h.top
    have hn := h.1.1.scr.nowrap
    have := slot_le (w := p.L.w) (show aN < 8 by decide)
    refine WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .rax = BitVec.ofNat 64 p.top ∧ t.mem = s.mem) (by
      xrun [State.ea, ix, addrm8 h.2.2.2.2.2.2.1 h.2.2.2.2.2.1 (by have := h.2.1; omega),
        h.1.1.scr.ld (show slot p.L.w aN + 8 * (p.L.w - 1) + 8 ≤ p.L.Z by have := h.1.2; omega)]
      rw [← hT, BitVec.ofNat_toNat, BitVec.setWidth_eq]) rfl) fun t ⟨⟨hax, hm⟩, k⟩ => ⟨?_, hax⟩
    obtain ⟨hg, hw, hw', hN, hinv, h12, h10, hodd, hlo⟩ := h
    exact ⟨⟨⟨hg.1.scr.congr k.2.2, (k.gpr (by decide)).trans hg.1.rdi, hm ▸ hg.1.hdr⟩, hg.2⟩, hw, hw',
      hm ▸ hN, hm ▸ hinv, (k.gpr (by decide)).trans h12, (k.gpr (by decide)).trans h10, hodd, hlo⟩
  -- Its top bit.
  refine RelCT.seq (two_piece (Ψ := R2b) [.rax] (fun p s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2, h₂.2]) (by taint_decide) ?_) ?_
  · intro p s ⟨h, hax⟩
    obtain ⟨-, hT0, hT1, -⟩ := h.top
    refine WP.mono (topBit_ok hax hT0 hT1) fun t ⟨hdx, hcx, hm, k⟩ => ⟨?_, hdx, hcx⟩
    obtain ⟨hg, hw, hw', hN, hinv, h12, h10, hodd, hlo⟩ := h
    exact ⟨⟨⟨hg.1.scr.congr k.2.2, (k.gpr (by decide)).trans hg.1.rdi, hm ▸ hg.1.hdr⟩, hg.2⟩, hw, hw',
      hm ▸ hN, hm ▸ hinv, (k.gpr (by decide)).trans h12, (k.gpr (by decide)).trans h10, hodd, hlo⟩
  -- The count into the header, and the start's word index.
  refine RelCT.seq (two_piece (Ψ := R2c) _ (pins_rdi_of (·.L) fun _ _ h => h.1.1) (by taint_decide) ?_) ?_
  · intro p s ⟨⟨hg, hw, hw', hN, hinv, h12, h10, hodd, hlo⟩, hdx, hcx⟩
    have hn := hg.1.scr.nowrap
    have hn' : p.L.B.toNat + slot p.L.w 8 ≤ 2 ^ 64 := by have := hg.2; omega
    have h0 := hdr_lt_slot p.L.w 0 (show sCnt < 32 by decide)
    have h0' := slot_le (w := p.L.w) (show 0 < 8 by decide)
    refine WP.mono (WP.keep [.rcx] (Q := fun t => t.gpr .rcx = BitVec.ofNat 64 (p.L.w - 1) ∧
        t.mem = s.mem.writeW (off p.L.B (8 * sCnt)) (BitVec.ofNat 64 (64 - p.top.log2))) (by
      xrun [State.ea, hdr, hg.1.rdi, hdrOff, hg.1.scr.st (d := 8 * sCnt) (by have := hg.2; omega),
        hcx, h12, ofNat64_pred (show 1 ≤ p.L.w by omega) (by omega)]) rfl) fun t ⟨⟨hcx', hm⟩, k⟩ => ?_
    exact ⟨⟨⟨hg.1.scr.congr k.2.2, (k.gpr (by decide)).trans hg.1.rdi,
      by rw [hm]; exact Hdr.store hg.1.hdr (by decide) (by decide) _⟩, hg.2⟩, hw, hw',
      by rw [hm, hdrStore_wv _ _ _ (by decide) (by decide) hn']; exact hN,
      by rw [hm, hdrStore_word _ _ _ (by decide) (by decide) hn']; exact hinv,
      (k.gpr (by decide)).trans h12, hcx', (k.gpr (by decide)).trans hdx, by rw [hm, word_writeW_self],
      hodd, hlo⟩
  -- The start.
  refine RelCT.seq (two_post (Ψ := R2d) ?_ ?_) ?_
  · rw [setWord_eq]
    refine RelCT.seq (two_piece (Ψ := fun p s => R2c p s ∧ s.gpr .r8 = off p.L.B (slot p.L.w aR2)) _
      (pins_rdi_of (·.L) fun _ _ h => h.1) (by taint_decide) fun p s h => ?_) (two_taint [.r8, .r12, .rcx]
        (fun p s₁ s₂ h₁ h₂ r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · rw [h₁.2, h₂.2]
          · rw [h₁.1.2.2.2.2.2.1, h₂.1.2.2.2.2.2.1]
          · rw [h₁.1.2.2.2.2.2.2.1, h₂.1.2.2.2.2.2.2.1]) (by taint_decide))
    have hl : InRegions (s.rd ++ s.wr) (off p.L.B (8 * sArr aR2)) 8 :=
      h.1.1.scr.ld (by have := hdr_lt_slot p.L.w 8 (show sArr aR2 < 32 by decide); have := h.1.2; omega)
    refine WP.mono (WP.keep [.r8] (Q := fun t => t.gpr .r8 = off p.L.B (slot p.L.w aR2) ∧ t.mem = s.mem) (by
      xrun [State.ea, hdr, h.1.1.rdi, hdrOff, hl, h.1.1.hdr.harr aR2 (by decide)]) rfl)
      fun t ⟨⟨h8, hm⟩, k⟩ => ⟨?_, h8⟩
    obtain ⟨hg, hw, hw', hN, hinv, h12, hcx, hdx, hcnt, hodd, hlo⟩ := h
    exact ⟨⟨⟨hg.1.scr.congr k.2.2, (k.gpr (by decide)).trans hg.1.rdi, hm ▸ hg.1.hdr⟩, hg.2⟩, hw, hw',
      hm ▸ hN, hm ▸ hinv, (k.gpr (by decide)).trans h12, (k.gpr (by decide)).trans hcx,
      (k.gpr (by decide)).trans hdx, hm ▸ hcnt, hodd, hlo⟩
  · intro p s ⟨hg, hw, hw', hN, hinv, h12, hcx, hdx, hcnt, hodd, hlo⟩
    obtain ⟨-, -, -, hL, -⟩ := r2top (s := s) hw hN hodd hlo
    have hn' : p.L.B.toNat + slot p.L.w 8 ≤ 2 ^ 64 := by have := hg.1.scr.nowrap; have := hg.2; omega
    refine WP.mono (setWord_ok hg.1.scr hg.1.rdi hg.1.hdr hg.2 h12 (by omega) (by omega) (o := aR2) (by decide)
      (ri := .rcx) (by decide) (i := p.L.w - 1) (by omega) hcx) fun t ⟨hv, ho, k⟩ => ?_
    have ha : Arrays p.L.B p.L.w [aR2] s.mem t.mem :=
      Arrays.of_outside (List.mem_singleton_self _) ho (Nat.le_refl _) (Nat.le_refl _)
    rw [hdx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hL)] at hv
    exact ⟨⟨⟨hg.1.scr.congr k.2.2, (k.gpr (by decide)).trans hg.1.rdi, ha.hdr hg.1.hdr⟩, hg.2⟩, hw, hw',
      by rw [ha.wv_of_not_mem (by decide) (by decide) hn']; exact hN,
      by rw [ha.word0_of_not_mem (by decide) (by decide) hn' (by omega)]; exact hinv,
      by rw [ha.hslot (by decide)]; exact hcnt, hodd, hlo, hv⟩
  -- The count of doublings.
  refine RelCT.seq (two_piece (Ψ := R2e) _ (pins_rdi_of (·.L) fun _ _ h => h.1) (by taint_decide) ?_) ?_
  · intro p s h
    obtain ⟨hg, hw, hw', hN, hinv, hcnt, hodd, hlo, hv⟩ := h
    have h0 := hdr_lt_slot p.L.w 0 (show 31 < 32 by decide)
    have h0' := slot_le (w := p.L.w) (show 0 < 8 by decide)
    have := hg.2
    refine WP.mono (WP.keep [.rcx] (Q := fun t => t.gpr .rcx = BitVec.ofNat 64 p.cnt ∧ t.mem = s.mem) (by
      xrun [State.ea, hdr, hg.1.rdi, hdrOff, hg.1.scr.ld (d := 8 * sCnt) (by unfold sCnt sFn; omega),
        hg.1.scr.ld (d := 8 * sW) (by unfold sW; omega), hcnt, hg.1.hdr.hw, ← BitVec.ofNat_add]
      rfl) rfl) fun t ⟨⟨hcx, hm⟩, k⟩ => ⟨?_, hcx⟩
    exact ⟨⟨⟨hg.1.scr.congr k.2.2, (k.gpr (by decide)).trans hg.1.rdi, hm ▸ hg.1.hdr⟩, hg.2⟩, hw, hw',
      hm ▸ hN, hm ▸ hinv, hm ▸ hcnt, hodd, hlo, hm ▸ hv⟩
  -- The doublings.
  refine RelCT.seq (two_post (Ψ := fun p s => SqPre p.L s) ((two_map (fun p => (⟨p.L, p.cnt⟩ : DblPub))
    (fun p s h => ?_) (doubles_ct (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by taint_decide)
      (by taint_decide) (by taint_decide))).mono (fun _ _ h => h) fun _ _ _ => trivial) ?_) ?_
  · obtain ⟨⟨hg, hw, hw', hN, -, -, hodd, hlo, hv⟩, hcx⟩ := h
    obtain ⟨-, -, -, hL, hv0⟩ := r2top (s := s) hw hN hodd hlo
    exact ⟨hg, hw, show p.L.w < 2 ^ 31 by omega, show 1 ≤ p.cnt by unfold R2Pub.cnt; omega,
      show p.cnt < 2 ^ 31 by unfold R2Pub.cnt; omega, hcx, by rw [hv, hN]; exact hv0⟩
  · intro p s h
    obtain ⟨⟨hg, hw, hw', hN, hinv, -, hodd, hlo, hv⟩, hcx⟩ := h
    obtain ⟨-, -, -, hL, hv0⟩ := r2top (s := s) hw hN hodd hlo
    have hn' : p.L.B.toNat + slot p.L.w 8 ≤ 2 ^ 64 := by have := hg.1.scr.nowrap; have := hg.2; omega
    refine WP.mono (doubles_ok hg.1.scr hg.1.rdi hg.1.hdr hg.2 hw (by omega) (mo := aN) (acc := aAcc)
      (tmp := aTmp) (o := aR2) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (sl := sCnt) (by decide) (by decide)
      (c := p.cnt) (by unfold R2Pub.cnt; omega) (by unfold R2Pub.cnt; omega) hcx (by rw [hv, hN]; exact hv0))
      fun t ⟨hv', hf, hH, k⟩ => ?_
    have hf' : Frm p.L.B (r2Ranges p.L.w) s.mem t.mem := hf
    have hN0 : 0 < p.N := by omega
    refine ⟨⟨⟨hg.1.scr.congr k.2.2, (k.gpr (by decide)).trans hg.1.rdi, hH⟩, hg.2⟩, hw, by omega,
      by rw [hf'.r2_word hn' (by decide) (by decide) (by decide) (by decide)]; exact hinv, ?_⟩
    rw [hv', hf'.r2_wv hn' (by decide) (by decide) (by decide) (by decide), hN]
    exact Nat.mod_lt _ hN0
  -- The squarings.
  exact two_map (·.L) (fun _ _ h => h) (sqs_ct 5)

end VG.Proof.Bignum.X86_64
