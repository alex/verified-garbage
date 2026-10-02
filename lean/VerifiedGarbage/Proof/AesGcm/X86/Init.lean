import VerifiedGarbage.Proof.AesGcm.X86.Top

/-!
# AES-GCM on x86: `vg_aes_gcm_init`

Untrusted: everything here is checked by Lean. The key schedule
(`vg_aes_expand_key`), then the hash subkey `CIPH_K(0¹²⁸)` (`vg_aes_ctr32`
on a zero block, with a zero counter block at `T`), as one `Pc`
(`init_pc`): correct (`init_correct`) and constant time (`init_ct`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcm.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt KeyRepr)

theorem shr2 {n : Nat} (hn : n < 2 ^ 32) : BitVec.ofNat 32 n >>> 2 = BitVec.ofNat 32 (n / 4) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega)]

/-- The facts of `init`'s precondition about the public data `p` alone. -/
structure InitPure (p : BitVec 32 × (Nat → BitVec 32)) : Prop where
  kc : (⟨w64 (p.2 0), (p.2 1).toNat⟩ : Region).Disjoint ⟨w64 (p.2 2), 256⟩
  kw : (⟨w64 (p.2 0), (p.2 1).toNat⟩ : Region).Disjoint ⟨w64 (p.2 3), 2560⟩
  cw : (⟨w64 (p.2 2), 256⟩ : Region).Disjoint ⟨w64 (p.2 3), 2560⟩
  r_c : (⟨w64 p.1, 4⟩ : Region).Disjoint ⟨w64 (p.2 2), 256⟩
  r_w : (⟨w64 p.1, 4⟩ : Region).Disjoint ⟨w64 (p.2 3), 2560⟩
  k_k : (below p.1 28).Disjoint ⟨w64 (p.2 0), (p.2 1).toNat⟩
  k_c : (below p.1 28).Disjoint ⟨w64 (p.2 2), 256⟩
  k_w : (below p.1 28).Disjoint ⟨w64 (p.2 3), 2560⟩
  fk : (p.2 0).toNat + (p.2 1).toNat ≤ 2 ^ 32
  fc : (p.2 2).toNat + 256 ≤ 2 ^ 32
  fw : (p.2 3).toNat + 2560 ≤ 2 ^ 32
  sp : 28 ≤ p.1.toNat
  len : (p.2 1).toNat = 16 ∨ (p.2 1).toNat = 24 ∨ (p.2 1).toNat = 32

theorem initPure_of {p : BitVec 32 × (Nat → BitVec 32)} {s : State} (h : initPre s) (hp : pubOf 4 s = p) :
    InitPure p := by
  simp only [initPre] at h
  obtain ⟨-, -, d_kc, d_kw, -, d_cw, -, -, -, r_c, r_w, -, k_k, k_c, k_w, -, fk, fc, fw, sp, -, hl⟩ := h
  rw [ofNat_lit, below_eq sp] at k_k k_c k_w
  have a0 := pubOf_arg hp (i := 0) (by decide); have a1 := pubOf_arg hp (i := 1) (by decide)
  have a2 := pubOf_arg hp (i := 2) (by decide); have a3 := pubOf_arg hp (i := 3) (by decide)
  have e := pubOf_esp hp
  simp only [a0, a1, a2, a3, e] at d_kc d_kw d_cw r_c r_w k_k k_c k_w fk fc fw sp hl
  exact ⟨d_kc, d_kw, d_cw, r_c, r_w, k_k, k_c, k_w, fk, fc, fw, sp, hl⟩

/-- `ctx` and `W` and the stack apart, at offsets. -/
theorem InitPure.cw' {p : BitVec 32 × (Nat → BitVec 32)} (h : InitPure p) {a n d k : Nat} (ha : a + n ≤ 256)
    (hd : d + k ≤ 2560) :
    (⟨w64 (p.2 2) + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨w64 (p.2 3) + BitVec.ofNat 64 d, k⟩ :=
  (h.cw.sub_left (Lay.ctxSub ha)).sub_right (Lay.wSub hd)

abbrev initTail : List Instr :=
  [.mov .ecx (argOp 1), .mov .ebx (.reg .ecx), .shift .shr .ebx 2, .alu .add .ebx (imm 6), .mov .eax (argOp 0),
    .mov .edx (.reg .esi), .alu .add .ebp (imm scrO)]

abbrev initMid : List Instr :=
  unscr ++ [.mov .eax (imm 0), .store (at_ .esi 240) .eax, .store (at_ .esi 244) .eax,
      .store (at_ .esi 248) .eax, .store (at_ .esi 252) .eax] ++ zero4 tO ++
      [.mov .eax (.reg .esi), .mov .ecx (.reg .ebx), .mov .edx (.reg .ebp), .alu .add .edx (imm tO),
        .mov .ebx (.reg .esi), .alu .add .ebx (imm 240), .mov .edi (imm 1), .alu .add .ebp (imm scrO)]

theorem init_eq : init = .seq (entry 3 ([.mov .esi (argOp 2)] ++
    (([] : List (Nat × Nat)).flatMap (fun p => keep p.1 p.2) ++ initTail)))
    (.seq keyCall (.seq (.block initMid) (.seq ctrCall (.block (unscr ++ restore))))) := rfl

/-- After the entry: the arguments of `vg_aes_expand_key`. -/
structure IEnt (p : BitVec 32 × (Nat → BitVec 32)) (s₀ s : State) : Prop where
  pre : initPre s₀
  pub : pubOf 4 s₀ = p
  call : KeyCall s (p.2 0) (p.2 2) (p.2 3 + BitVec.ofNat 32 512) (p.2 1).toNat
  ebx : s.gpr .ebx = BitVec.ofNat 32 ((p.2 1).toNat / 4 + 6)
  esi : s.gpr .esi = p.2 2
  esp : s.gpr .esp = p.1
  saved : SavedAt s.mem (p.2 3) s₀
  frame : Frame [⟨w64 (p.2 3) + BitVec.ofNat 64 128, 2432⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem iEntry_pc (p : BitVec 32 × (Nat → BitVec 32)) :
    Pc (fun (s₀ : State) s => initPre s₀ ∧ pubOf 4 s₀ = p ∧ s = s₀)
      (entry 3 ([.mov .esi (argOp 2)] ++ (([] : List (Nat × Nat)).flatMap (fun p => keep p.1 p.2) ++ initTail)))
      (IEnt p) := by
  refine ⟨fun s₀ s ⟨hpre, hpub, hs⟩ => ?_, ?_⟩
  · subst s
    have hc := initPure_of hpre hpub
    have hp := hpre
    simp only [initPre] at hp
    obtain ⟨hrd, hwr, -, -, -, -, -, d_wa, -, -, -, -, -, -, -, -, -, -, -, -, fa, -⟩ := hp
    have a : ∀ i, i < 4 → arg s₀ i = p.2 i := fun i hi => pubOf_arg hpub hi
    have esp := pubOf_esp hpub
    have wW : Covers [⟨w64 (arg s₀ 3), 2560⟩] s₀.wr := by rw [hwr]; exact covers_of_mem (by simp)
    have rA : Covers [argsR (s₀.gpr .esp) 4] (s₀.rd ++ s₀.wr) := by
      rw [argsR_eq, hrd, hwr]; exact covers_of_mem (by simp)
    have aw : (argsR (s₀.gpr .esp) 4).Disjoint ⟨w64 (arg s₀ 3), 2560⟩ := by rw [argsR_eq]; exact d_wa.symm
    refine entry_ok [] initTail (by decide) (by decide) (by decide) (by decide) rfl rfl wW rA aw (by omega)
      (by rw [a 3 (by decide)]; exact hc.fw) fun s₂ e => ?_
    have i₁ : InRegions (s₂.rd ++ s₂.wr) (argA (s₀.gpr .esp) 1) 4 := by
      rw [e.rd, e.wr]; exact argIn_of rA (by omega) (by decide)
    have i₀ : InRegions (s₂.rd ++ s₂.wr) (argA (s₀.gpr .esp) 0) 4 := by
      rw [e.rd, e.wr]; exact argIn_of rA (by omega) (by decide)
    have v₁ := e.args 1 (by decide)
    have v₀ := e.args 0 (by decide)
    have hL : (p.2 1).toNat < 2 ^ 32 := (p.2 1).isLt
    have hsh : arg s₀ 1 >>> 2 + BitVec.ofNat 32 6 = BitVec.ofNat 32 ((p.2 1).toNat / 4 + 6) := by
      rw [a 1 (by decide), ← ofNat_toNat32 (p.2 1), shr2 hL, ofNat_add_ofNat32, toNat_ofNat32 hL]
    refine ⟨_, by xrun [e.esp, i₁, i₀, v₁, v₀, e.esi, e.ebp], ?_⟩
    have eS := w64_add (x := p.2 3) (k := 512) (by have := hc.fw; omega)
    have bsub : Region.Sub (below p.1 20) (below p.1 28) := VG.X86.below_sub (by decide) hc.sp
    have hrd' : s₀.rd = [⟨w64 (p.2 0), (p.2 1).toNat⟩] := by rw [hrd, a 0 (by decide), a 1 (by decide)]
    have hwr' : s₀.wr = [⟨w64 (p.2 2), 256⟩, ⟨w64 (p.2 3), 2560⟩, ⟨argAddr s₀ 0, 16⟩] := by
      rw [hwr, a 2 (by decide), a 3 (by decide)]
    refine ⟨hpre, hpub, ⟨by regs [v₀]; exact a 0 (by decide),
      by regs [v₁]; rw [a 1 (by decide)]; exact (ofNat_toNat32 _).symm,
      by regs [e.esi]; exact a 2 (by decide), by regs [e.ebp]; rw [a 3 (by decide)],
      hc.len, by regs [e.esp, esp]; have := hc.sp; omega, hc.kc.sub_right (Region.sub_prefix (by decide)),
      by rw [eS]; exact hc.kw.sub_right (Lay.wSub (by decide)),
      by rw [eS]; exact (hc.cw.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.wSub (by decide)),
      by regs [e.esp, esp]; exact hc.k_k.sub_left bsub,
      by regs [e.esp, esp]; exact (hc.k_c.sub_left bsub).sub_right (Region.sub_prefix (by decide)),
      by regs [e.esp, esp]; rw [eS]; exact (hc.k_w.sub_left bsub).sub_right (Lay.wSub (by decide)),
      hc.fk, by have := hc.fc; omega, by rw [toNat_add32 (by have := hc.fw; omega)]; have := hc.fw; omega,
      by mems [e.rd, e.wr, hrd']; exact covers_of_mem (by simp), ?_⟩, by regs [hsh], by regs [e.esi]; exact a 2 (by decide),
      by regs [e.esp, esp], by mems []; rw [← a 3 (by decide)]; exact e.saved,
      by mems []; rw [← a 3 (by decide)]; exact e.frame, by mems [e.rd], by mems [e.wr]⟩
    rw [eS]
    mems [e.wr, hwr']
    have c₁ : Covers [⟨w64 (p.2 2), 240⟩] [⟨w64 (p.2 2), 256⟩, ⟨w64 (p.2 3), 2560⟩, ⟨argAddr s₀ 0, 16⟩] := by
      have := covers_off (p := w64 (p.2 2)) (k := 256) (d := 0) (n := 240)
        (rs := [⟨w64 (p.2 2), 256⟩, ⟨w64 (p.2 3), 2560⟩, ⟨argAddr s₀ 0, 16⟩]) (covers_of_mem (by simp)) (by decide)
        (by decide)
      simpa using this
    exact covers_cons c₁ (covers_cons (covers_off (p := w64 (p.2 3)) (k := 2560) (d := 512) (n := 512)
      (covers_of_mem (by simp)) (by decide) (by decide)) covers_nil)
  · refine CT.seq (J := fun s => s.gpr .eax = p.2 3 ∧ s.gpr .esp = p.1)
      (CT.taint [.esp] (fun s₁ s₂ ⟨a₁, _, h₁, e₁⟩ ⟨a₂, _, h₂, e₂⟩ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; subst e₁; subst e₂
        rw [pubOf_esp h₁, pubOf_esp h₂]) (by taint_decide)) (fun s ⟨s₀, hpre, hpub, hs⟩ => ?_)
      (CT.taint [.eax, .esp] (fun s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [h₁.1, h₂.1]
        · rw [h₁.2, h₂.2]) (by taint_decide))
    subst s
    have hp := hpre
    simp only [initPre] at hp
    obtain ⟨hrd, hwr, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, fa, -⟩ := hp
    have rA : Covers [argsR (s₀.gpr .esp) 4] (s₀.rd ++ s₀.wr) := by
      rw [argsR_eq, hrd, hwr]; exact covers_of_mem (by simp)
    exact WP.mono (arg0_ok (argIn_of rA (by omega) (by decide))) fun s' ⟨ax, sp⟩ =>
      ⟨by rw [ax]; exact pubOf_arg hpub (by decide), by rw [sp]; exact pubOf_esp hpub⟩

/-- After the key schedule and `initMid`: the arguments of `vg_aes_ctr32` for `H`. -/
structure IMid (p : BitVec 32 × (Nat → BitVec 32)) (s₀ s : State) : Prop where
  ent : ∃ s₁, IEnt p s₀ s₁ ∧ Frame [⟨w64 (p.2 2), 256⟩, ⟨w64 (p.2 3), 2560⟩, below p.1 28] s₁.mem s.mem
  call : CtrCall s (p.2 2) (p.2 3 + BitVec.ofNat 32 96) (p.2 2 + BitVec.ofNat 32 240) (p.2 3 + BitVec.ofNat 32 512)
    ((p.2 1).toNat / 4 + 6) 1
  esp : s.gpr .esp = p.1
  sched : bytesAt s.mem (w64 (p.2 2)) (16 * ((p.2 1).toNat / 4 + 6 + 1)) =
    Spec.Aes.expandKey (bytesAt s₀.mem (w64 (p.2 0)) (p.2 1).toNat)
  zt : blockAt s.mem (w64 (p.2 3) + BitVec.ofNat 64 96) = 0
  zh : blockAt s.mem (w64 (p.2 2) + BitVec.ofNat 64 240) = 0
  saved : SavedAt s.mem (p.2 3) s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem rounds_of_len {L : Nat} (h : L = 16 ∨ L = 24 ∨ L = 32) : L / 4 + 6 = 10 ∨ L / 4 + 6 = 12 ∨ L / 4 + 6 = 14 := by
  rcases h with rfl | rfl | rfl <;> decide

theorem iMid_ok {p : BitVec 32 × (Nat → BitVec 32)} (hc : InitPure p) {s₀ s₁ s : State} (h : IEnt p s₀ s₁)
    (g : KeyPost s₁ (p.2 0) (p.2 2) (p.2 3 + BitVec.ofNat 32 512) (p.2 1).toNat s) :
    WP isa (.block initMid) s (IMid p s₀) := by
  have eS := w64_add (x := p.2 3) (k := 512) (by have := hc.fw; omega)
  have eT := w64_add (x := p.2 3) (k := 96) (by have := hc.fw; omega)
  have eH := w64_add (x := p.2 2) (k := 240) (by have := hc.fc; omega)
  have bp : s.gpr .ebp = p.2 3 + BitVec.ofNat 32 512 := by rw [g.saved .ebp (by decide), h.call.ebp]
  have si : s.gpr .esi = p.2 2 := by rw [g.saved .esi (by decide), h.esi]
  have bx : s.gpr .ebx = BitVec.ofNat 32 ((p.2 1).toNat / 4 + 6) := by rw [g.saved .ebx (by decide), h.ebx]
  have sp : s.gpr .esp = p.1 := by rw [g.saved .esp (by decide), h.esp]
  have hwr : s.wr = s₀.wr := by rw [g.wr, h.wr]
  have hp := h.pre
  simp only [initPre] at hp
  have hwr₀ : s₀.wr = [⟨w64 (p.2 2), 256⟩, ⟨w64 (p.2 3), 2560⟩, ⟨argAddr s₀ 0, 16⟩] := by
    rw [hp.2.1, pubOf_arg h.pub (i := 2) (by decide), pubOf_arg h.pub (i := 3) (by decide)]
  have wC : Covers [⟨w64 (p.2 2), 256⟩] s.wr := by rw [hwr, hwr₀]; exact covers_of_mem (by simp)
  have wW : Covers [⟨w64 (p.2 3), 2560⟩] s.wr := by rw [hwr, hwr₀]; exact covers_of_mem (by simp)
  have hb0 : p.2 3 + BitVec.ofNat 32 512 - BitVec.ofNat 32 512 = p.2 3 := BitVec.add_sub_cancel _ _
  have aC : ∀ {o}, o < 256 → w64 (p.2 2 + BitVec.ofNat 32 o) = w64 (p.2 2) + BitVec.ofNat 64 o :=
    fun ho => w64_add (by have := hc.fc; omega)
  have aW : ∀ {o}, o < 2560 → w64 (p.2 3 + BitVec.ofNat 32 o) = w64 (p.2 3) + BitVec.ofNat 64 o :=
    fun ho => w64_add (by have := hc.fw; omega)
  have cIn : ∀ {d}, d + 4 ≤ 256 → InRegions s.wr (w64 (p.2 2) + BitVec.ofNat 64 d) 4 :=
    fun hd => in_off wC hd (by decide)
  have wIn : ∀ {d}, d + 4 ≤ 2560 → InRegions s.wr (w64 (p.2 3) + BitVec.ofNat 64 d) 4 :=
    fun hd => in_off wW hd (by decide)
  have hzC : ∀ m : Mem, Cmac.zero4 m (w64 (p.2 2) + BitVec.ofNat 64 240) =
      (((m.writeW (w64 (p.2 2) + BitVec.ofNat 64 240) (BitVec.ofNat 32 0)).writeW (w64 (p.2 2) + BitVec.ofNat 64 244)
      (BitVec.ofNat 32 0)).writeW (w64 (p.2 2) + BitVec.ofNat 64 248) (BitVec.ofNat 32 0)).writeW
      (w64 (p.2 2) + BitVec.ofNat 64 252) (BitVec.ofNat 32 0) := fun m => by
    simp only [Cmac.zero4, Cmac.store4, add_ofNat_assoc]; rfl
  have hzW : ∀ m : Mem, Cmac.zero4 m (w64 (p.2 3) + BitVec.ofNat 64 96) =
      (((m.writeW (w64 (p.2 3) + BitVec.ofNat 64 96) (BitVec.ofNat 32 0)).writeW (w64 (p.2 3) + BitVec.ofNat 64 100)
      (BitVec.ofNat 32 0)).writeW (w64 (p.2 3) + BitVec.ofNat 64 104) (BitVec.ofNat 32 0)).writeW
      (w64 (p.2 3) + BitVec.ofNat 64 108) (BitVec.ofNat 32 0) := fun m => by
    simp only [Cmac.zero4, Cmac.store4, add_ofNat_assoc]; rfl
  refine WP.of_runBlock ⟨_, by xrun [initMid, unscr, bp, si, bx, hb0, aC, aW, cIn, wIn, zero4, ← hzC, ← hzW], ?_⟩
  generalize hZ₁ : Cmac.zero4 s.mem (w64 (p.2 2) + BitVec.ofNat 64 240) = Z₁
  generalize hZ₂ : Cmac.zero4 Z₁ (w64 (p.2 3) + BitVec.ofNat 64 96) = Z₂
  have f₁ : Frame [⟨w64 (p.2 2) + BitVec.ofNat 64 240, 16⟩] s.mem Z₁ := by
    rw [← hZ₁]; exact Cmac.frame_store4 _ _ _ _ _
  have f₂ : Frame [⟨w64 (p.2 3) + BitVec.ofNat 64 96, 16⟩] Z₁ Z₂ := by rw [← hZ₂]; exact Cmac.frame_store4 _ _ _ _ _
  have hfit := hc.fc
  have hfw := hc.fw
  have hsp := hc.sp
  have bsub : Region.Sub (below p.1 20) (below p.1 28) := VG.X86.below_sub (by decide) hsp
  have gf := g.frame
  rw [h.esp, eS] at gf
  have go := g.out
  have dK : ∀ r ∈ [(⟨w64 (p.2 3) + BitVec.ofNat 64 128, 2432⟩ : Region)],
      (⟨w64 (p.2 0), (p.2 1).toNat⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hc.kw.sub_right (Lay.wSub (by decide))
  rw [bytesAt_frame h.frame dK (by have := hc.fk; omega)] at go
  have hR := rounds_of_len hc.len
  have hRb : 16 * ((p.2 1).toNat / 4 + 6 + 1) ≤ 240 := by rcases hR with h' | h' | h' <;> omega
  have dZ : ∀ r ∈ [(⟨w64 (p.2 2) + BitVec.ofNat 64 240, 16⟩ : Region)],
      (⟨w64 (p.2 2), 16 * ((p.2 1).toNat / 4 + 6 + 1)⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    have := Offset.disjoint (w64 (p.2 2)) (d := 0) (n := 16 * ((p.2 1).toNat / 4 + 6 + 1)) (e := 240) (k := 16)
      (.inl (by omega)) (by omega) (by omega)
    simpa using this
  have dZ₂ : ∀ r ∈ [(⟨w64 (p.2 3) + BitVec.ofNat 64 96, 16⟩ : Region)],
      (⟨w64 (p.2 2), 16 * ((p.2 1).toNat / 4 + 6 + 1)⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (hc.cw.sub_left (Region.sub_prefix (by omega))).sub_right (Lay.wSub (by decide))
  have hsv : SavedAt Z₂ (p.2 3) s₀ := by
    refine ((h.saved.frame gf fun r hr => ?_).frame f₁ fun r hr => ?_).frame f₂ fun r hr => ?_
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ((hc.cw.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.wSub (by decide))).symm
      · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
      · exact ((hc.k_w.sub_left bsub).sub_right (Lay.wSub (by decide))).symm
    · simp only [List.mem_singleton] at hr; subst hr; exact (hc.cw' (by decide) (by decide)).symm
    · simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
  have kc := hc.cw' (a := 0) (n := 240) (d := 96) (k := 16) (by decide) (by decide)
  have ks := hc.cw' (a := 0) (n := 240) (d := 512) (k := 2048) (by decide) (by decide)
  have cd := hc.cw' (a := 240) (n := 16) (d := 96) (k := 16) (by decide) (by decide)
  have ds := hc.cw' (a := 240) (n := 16) (d := 512) (k := 2048) (by decide) (by decide)
  simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at kc ks
  have hwr' := hwr
  rw [hwr₀] at hwr'
  have rC : Covers [⟨w64 (p.2 2), 240⟩] (s.rd ++ s.wr) := by
    have := covers_off (p := w64 (p.2 2)) (k := 256) (d := 0) (n := 240) (rs := s.wr) wC (by decide) (by decide)
    exact covers_left (by simpa using this)
  refine ⟨⟨s₁, h, ?_⟩, ⟨by regs [si], by regs [bx], by regs [], by regs [si], by regs [], by regs [],
    hR, by regs [sp]; omega, by rw [eT]; exact kc, ?_, by rw [eS]; exact ks,
    by rw [eT, eH]; exact cd.symm, by rw [eT, eS]; exact Lay.w_w (.inl (by decide)) (by decide) (by decide),
    by rw [eH, eS]; exact ds, by regs [sp]; exact hc.k_c.sub_right (Region.sub_prefix (by decide)),
    by regs [sp]; rw [eT]; exact hc.k_w.sub_right (Lay.wSub (by decide)),
    by regs [sp]; rw [eH]; exact hc.k_c.sub_right (Lay.ctxSub (by decide)),
    by regs [sp]; rw [eS]; exact hc.k_w.sub_right (Lay.wSub (by decide)),
    by omega, by rw [toNat_add32 (by omega)]; omega, by rw [toNat_add32 (by omega)]; omega,
    by rw [toNat_add32 (by omega)]; omega, by mems []; exact rC, ?_⟩, by regs [sp], ?_, ?_, ?_, ?_, by mems [g.rd, h.rd],
    by mems [g.wr, h.wr]⟩
  · simp only [mem_setMem, mem_setReg, mem_arithFlags]
    refine (gf.sub fun r hr => ?_).trans ((f₁.sub fun r hr => ?_).trans (f₂.sub fun r hr => ?_))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by decide)⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Lay.wSub (by decide)⟩
      · exact ⟨_, by simp, bsub⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self .., Lay.ctxSub (by decide)⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Lay.wSub (by decide)⟩
  · rw [eH]
    have := Offset.disjoint (w64 (p.2 2)) (d := 0) (n := 240) (e := 240) (k := 16 * 1) (.inl (by omega)) (by omega)
      (by omega)
    simpa using this
  · mems []
    rw [eT, eH, eS]
    exact covers_cons (covers_off wW (by decide) (by decide)) (covers_cons (covers_off wC (by decide) (by decide))
      (covers_cons (covers_off wW (by decide) (by decide)) covers_nil))
  · simp only [mem_setMem, mem_setReg, mem_arithFlags]
    rw [bytesAt_frame f₂ dZ₂ (by omega), bytesAt_frame f₁ dZ (by omega)]
    exact go
  · simp only [mem_setMem, mem_setReg, mem_arithFlags]
    rw [← hZ₂, blockAt, zero4_bytes', ofBytes_zeros]
  · simp only [mem_setMem, mem_setReg, mem_arithFlags]
    rw [blockAt_frame f₂ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact cd, ← hZ₁, blockAt, zero4_bytes', ofBytes_zeros]
  · simp only [mem_setMem, mem_setReg, mem_arithFlags]; exact hsv

theorem init_pc (p : BitVec 32 × (Nat → BitVec 32)) :
    Pc (fun (s₀ : State) s => initPre s₀ ∧ pubOf 4 s₀ = p ∧ s = s₀) init
      (fun s₀ s' => abiPreserved s₀ s' ∧ initX86.post s₀ s') := by
  by_cases hex : ∃ s₀, initPre s₀ ∧ pubOf 4 s₀ = p
  swap
  · exact Pc.vacuous fun a s ⟨h₁, h₂, _⟩ => hex ⟨a, h₁, h₂⟩
  obtain ⟨z, hz, hzp⟩ := hex
  have hc := initPure_of hz hzp
  rw [init_eq]
  refine Pc.seq (iEntry_pc p) ?_
  refine Pc.seq (Pc.of (I := fun s => KeyCall s (p.2 0) (p.2 2) (p.2 3 + BitVec.ofNat 32 512) (p.2 1).toNat ∧
    s.gpr .esp = p.1) (fun s h => key_call h.1) (key_ct fun s h => h) _ fun _ _ h => ⟨h.call, h.esp⟩) ?_
  refine Pc.seq (Q := IMid p) (Pc.taint [.esi, .ebp] (fun s₀ s ⟨s₁, h, g⟩ => iMid_ok hc h g)
    (fun _ _ s₁ s₂ ⟨t₁, h₁, g₁⟩ ⟨t₂, h₂, g₂⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [g₁.saved .esi (by decide), g₂.saved .esi (by decide), h₁.esi, h₂.esi]
      · rw [g₁.saved .ebp (by decide), g₂.saved .ebp (by decide), h₁.call.ebp, h₂.call.ebp]) (by taint_decide)) ?_
  refine Pc.seq (Pc.of (I := fun s => CtrCall s (p.2 2) (p.2 3 + BitVec.ofNat 32 96) (p.2 2 + BitVec.ofNat 32 240)
    (p.2 3 + BitVec.ofNat 32 512) ((p.2 1).toNat / 4 + 6) 1 ∧ s.gpr .esp = p.1) (fun s h => ctr_call h.1)
    (ctr_ct fun s h => h) _ fun _ _ h => ⟨h.call, h.esp⟩) ?_
  refine Pc.taint [.ebp] (fun s₀ s' ⟨s, hm, g⟩ => ?_) (fun _ _ s₁ s₂ ⟨_, h₁, g₁⟩ ⟨_, h₂, g₂⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [g₁.saved .ebp (by decide), g₂.saved .ebp (by decide), h₁.call.ebp, h₂.call.ebp]) (by taint_decide)
  obtain ⟨s₁, h₁, fE⟩ := hm.ent
  have eS := w64_add (x := p.2 3) (k := 512) (by have := hc.fw; omega)
  have eT := w64_add (x := p.2 3) (k := 96) (by have := hc.fw; omega)
  have eH := w64_add (x := p.2 2) (k := 240) (by have := hc.fc; omega)
  have bp : s'.gpr .ebp = p.2 3 + BitVec.ofNat 32 512 := by rw [g.saved .ebp (by decide), hm.call.ebp]
  have hb0 : p.2 3 + BitVec.ofNat 32 512 - BitVec.ofNat 32 512 = p.2 3 := BitVec.add_sub_cancel _ _
  have gf := g.frame
  rw [hm.esp, eT, eH, eS] at gf
  have hsp := hc.sp
  have dC : ∀ {a k : Nat}, a + k ≤ 240 → ∀ r ∈ [(⟨w64 (p.2 3) + BitVec.ofNat 64 96, 16⟩ : Region),
      ⟨w64 (p.2 2) + BitVec.ofNat 64 240, 16 * 1⟩, ⟨w64 (p.2 3) + BitVec.ofNat 64 512, 2048⟩, below p.1 28],
      (⟨w64 (p.2 2) + BitVec.ofNat 64 a, k⟩ : Region).Disjoint r := fun hk r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hc.cw' (by omega) (by decide)
    · exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)
    · exact hc.cw' (by omega) (by decide)
    · exact (hc.k_c.sub_right (Lay.ctxSub (by omega))).symm
  have hsv : SavedAt s'.mem (p.2 3) s₀ := hm.saved.frame gf fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
    · exact (hc.cw' (by decide) (by decide)).symm
    · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    · exact ((hc.k_w.sub_right (Lay.wSub (by decide)))).symm
  have rG : ∀ r ∈ [(⟨w64 (p.2 3) + BitVec.ofNat 64 96, 16⟩ : Region),
      ⟨w64 (p.2 2) + BitVec.ofNat 64 240, 16 * 1⟩, ⟨w64 (p.2 3) + BitVec.ofNat 64 512, 2048⟩, below p.1 28],
      (⟨w64 p.1, 4⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hc.r_w.sub_right (Lay.wSub (by decide))
    · exact hc.r_c.sub_right (Lay.ctxSub (by decide))
    · exact hc.r_w.sub_right (Lay.wSub (by decide))
    · exact ret_below hsp
  have rF : ∀ r ∈ [(⟨w64 (p.2 2), 256⟩ : Region), ⟨w64 (p.2 3), 2560⟩, below p.1 28],
      (⟨w64 p.1, 4⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hc.r_c
    · exact hc.r_w
    · exact ret_below hsp
  have rE : ∀ r ∈ [(⟨w64 (p.2 3) + BitVec.ofNat 64 128, 2432⟩ : Region)], (⟨w64 p.1, 4⟩ : Region).Disjoint r :=
    fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hc.r_w.sub_right (Lay.wSub (by decide))
  have hret : s'.mem.readW (w64 (s₀.gpr .esp)) 32 = s₀.mem.readW (w64 (s₀.gpr .esp)) 32 := by
    rw [pubOf_esp h₁.pub, ret_kept gf rG, ret_kept fE rF, ret_kept h₁.frame rE]
  have hwr₀ : s'.wr = s₀.wr := by rw [g.wr, hm.wr]
  have hp := h₁.pre
  simp only [initPre] at hp
  have wW : Covers [⟨w64 (p.2 3), 2560⟩] s'.wr := by
    rw [hwr₀, hp.2.1, pubOf_arg h₁.pub (i := 3) (by decide)]; exact covers_of_mem (by simp)
  refine WP.block_append (WP.of_runBlock ⟨_, by xrun [unscr, bp, hb0], ?_⟩)
  refine WP.mono (exit_ok (W := p.2 3) (by regs []) (by regs [g.saved .esp (by decide), hm.esp, pubOf_esp h₁.pub])
    (by mems []; exact covers_left wW) hc.fw (by mems []; exact hsv) (by mems []; exact hret))
    fun s'' ⟨abi, m'', _, _, _⟩ => ⟨abi, ?_⟩
  have hA : ∀ i, i < 4 → arg s₀ i = p.2 i := fun i hi => pubOf_arg h₁.pub hi
  show KeyRepr s''.mem _ _
  rw [hA 0 (by decide), hA 1 (by decide), hA 2 (by decide), m'']
  simp only [mem_setMem, mem_setReg, mem_arithFlags]
  have hlen := length_bytesAt s₀.mem (w64 (p.2 0)) (p.2 1).toNat
  have hR := rounds_of_len hc.len
  have hRb : 16 * ((p.2 1).toNat / 4 + 6 + 1) ≤ 240 := by rcases hR with h' | h' | h' <;> omega
  have hs : bytesAt s'.mem (w64 (p.2 2)) (16 * ((p.2 1).toNat / 4 + 6 + 1)) =
      Spec.Aes.expandKey (bytesAt s₀.mem (w64 (p.2 0)) (p.2 1).toNat) := by
    have := dC (a := 0) (k := 16 * ((p.2 1).toNat / 4 + 6 + 1)) (by omega)
    simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at this
    rw [bytesAt_frame gf this (by omega)]; exact hm.sched
  refine ⟨by rw [hlen]; exact hs, ?_⟩
  have go := g.out
  rw [eH, eT, blocksAt_one, blocksAt_one, hm.zh, hm.zt, hm.sched] at go
  have hb := congrArg (fun l => List.getD l 0 0) go
  simp only [List.getD_cons_zero] at hb
  rw [Proof.Gcm.ctr32_getD _ _ _ (by simp)] at hb
  simp only [List.getD_cons_zero, Nat.repeat, BitVec.zero_xor] at hb
  rw [ctxH_eq, hb]
  simp only [Spec.Gcm.aes, hlen, Spec.Aes.rounds]
  exact BitVec.zero_xor

theorem init_correct (s : State) (hs : initX86.pre s) :
    ∃ t s', Exec isa init s t s' ∧ abiPreserved s s' ∧ initX86.post s s' :=
  (init_pc (pubOf 4 s)).wp s s ⟨hs, rfl, rfl⟩

theorem init_ct : ConstantTime isa initX86.pre initX86.pub init :=
  Pc.constantTime (pubOf 4) (fun _ _ _ _ h => pubOf_eq h) init_pc fun _ hs => ⟨hs, rfl, rfl⟩

end VG.Proof.AesGcm.X86
