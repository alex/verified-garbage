import VerifiedGarbage.Proof.MlKem.X86_64.FragPrim

/-!
# ML-KEM-768 on x86-64: the calls of the SHA-3 sponge

Untrusted: everything here is checked by Lean. Zeroing the Keccak state at
`scratch` (`kzero_ok`), and the calls of `vg_keccak_absorb`,
`vg_keccak_pad` and `vg_keccak_squeeze` on it, with the working space at
`scratch + 200` (`kabs_ok`, `kpad_ok`, `ksqz_ok`), and their traces.
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt stateAt rates absorb pad squeezeFrom)

/-! ## Zeroing -/

theorem kzero_ok (s : State) (hw : Covers [⟨pa s (sc 0), 200⟩] s.wr) :
    WP isa (.block kzero) s fun s' =>
      stateAt s'.mem (pa s (sc 0)) = Spec.Sha3.zero ∧ Frame [⟨pa s (sc 0), 200⟩] s.mem s'.mem ∧
        Keep [.rax] s s' := by
  rw [kzero, ← List.singleton_append, WP.block_append_iff]
  refine WP.mono (WP.keep [.rax] (Q := fun s1 => s1.mem = s.mem ∧ s1.gpr .rax = 0) (by xrun) (by decide))
    fun s1 ⟨⟨hm, hax⟩, k1⟩ => ?_
  have hbx : s1.gpr .rbx = s.gpr .rbx := k1.gpr (by decide)
  refine WP.mono (zeroSt_ok .rbx 0 s1 hax fun i hi => ?_) fun s2 ⟨hz, hf, k2⟩ => ?_
  · rw [k1.2.2, hbx]
    exact hw _ _ ⟨_, List.mem_singleton_self _, contains_offset' (by omega) (by omega)⟩
  · rw [hbx] at hz hf
    exact ⟨hz, by rw [← hm]; exact hf, (k1.trans k2).mono (by decide)⟩

theorem kzero_tr {P : State → State → Prop} (h : ∀ x y, P x y → x.gpr .rbx = y.gpr .rbx) :
    RelCT isa P (.block kzero) fun _ _ => True :=
  taintRel [.rbx] (fun x y hp r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h x y hp)
    (by taint_decide)

/-! ## Absorbing -/

/-- What a call of `vg_keccak_absorb` of the `len` bytes at `src` needs. -/
structure KAbsH (src : Ptr) (len rate pos : Nat) (s : State) : Prop where
  hoff : src.2 < 2 ^ 31
  hlen : len < 2 ^ 31
  hrate : rate ∈ rates
  hpos : pos < rate
  st_scr : Region.Disjoint ⟨pa s (sc 0), 200⟩ ⟨pa s (sc 200), 640⟩
  d_st : Region.Disjoint ⟨pa s src, len⟩ ⟨pa s (sc 0), 200⟩
  d_scr : Region.Disjoint ⟨pa s src, len⟩ ⟨pa s (sc 200), 640⟩
  k_st : (below (s.gpr .rsp) 32).Disjoint ⟨pa s (sc 0), 200⟩
  k_d : (below (s.gpr .rsp) 32).Disjoint ⟨pa s src, len⟩
  k_scr : (below (s.gpr .rsp) 32).Disjoint ⟨pa s (sc 200), 640⟩
  c : Covers ([⟨pa s src, len⟩] ++ [⟨pa s (sc 0), 200⟩, ⟨pa s (sc 200), 640⟩]) (s.rd ++ s.wr)
  w : Covers [⟨pa s (sc 0), 200⟩, ⟨pa s (sc 200), 640⟩] s.wr

theorem pa_sc0 (s : State) : pa s (sc 0) = s.gpr .rbx := BitVec.add_zero _

theorem rate_small {rate : Nat} (h : rate ∈ rates) : rate < 2 ^ 31 := by
  simp only [rates, List.mem_cons, List.not_mem_nil, or_false] at h; omega

theorem kabsGlue_ok (src : Ptr) (len rate pos : Nat) (ho : src.2 < 2 ^ 31) (hl : len < 2 ^ 31) (hr : rate < 2 ^ 31)
    (hp : pos < 2 ^ 31) (hs : NA src) (s : State) :
    WP isa (.block (lea .rdi (sc 0) ++ ([.mov32 .rsi (.imm (BitVec.ofNat 32 rate)),
      .mov32 .rdx (.imm (BitVec.ofNat 32 pos))] : List Instr) ++ lea .rcx src ++
      ([.mov32 .r8 (.imm (BitVec.ofNat 32 len))] : List Instr) ++ lea .r9 (sc 200))) s fun s1 =>
      ((s1.gpr .rdi = pa s (sc 0) ∧ s1.gpr .rsi = BitVec.ofNat 64 rate ∧ s1.gpr .rdx = BitVec.ofNat 64 pos ∧
        s1.gpr .rcx = pa s src ∧ s1.gpr .r8 = BitVec.ofNat 64 len ∧ s1.gpr .r9 = pa s (sc 200)) ∧ s1.mem = s.mem) ∧
        Keep argRegs s s1 := by
  have o1 : src.1 ≠ .rsi := fun e => hs (by rw [e]; decide)
  have o2 : src.1 ≠ .rdi := fun e => hs (by rw [e]; decide)
  have o3 : src.1 ≠ .rdx := fun e => hs (by rw [e]; decide)
  refine WP.keep _ ?_ (by rfl)
  unfold lea
  xrun [sx_ofNat ho, sx_ofNat (show (0 : Nat) < 2 ^ 31 by decide), sx_ofNat (show (200 : Nat) < 2 ^ 31 by decide),
    o1, o2, o3, sw_ofNat (show rate < 2 ^ 32 by omega), sw_ofNat (show pos < 2 ^ 32 by omega),
    sw_ofNat (show len < 2 ^ 32 by omega), List.cons_append, List.nil_append, pa_sc0]

theorem kabsArgs {src : Ptr} {len rate pos : Nat} {s s1 : State} (h : KAbsH src len rate pos s)
    (hv : s1.gpr .rdi = pa s (sc 0) ∧ s1.gpr .rsi = BitVec.ofNat 64 rate ∧ s1.gpr .rdx = BitVec.ofNat 64 pos ∧
      s1.gpr .rcx = pa s src ∧ s1.gpr .r8 = BitVec.ofNat 64 len ∧ s1.gpr .r9 = pa s (sc 200))
    (k : Keep argRegs s s1) : AbsorbArgs s1 (pa s (sc 0)) (pa s src) (pa s (sc 200)) rate pos len := by
  have hsp : s1.gpr .rsp = s.gpr .rsp := k.gpr (by decide)
  exact ⟨hv.1, hv.2.1, hv.2.2.1, hv.2.2.2.1, hv.2.2.2.2.1, hv.2.2.2.2.2, h.hrate, h.hpos, by have := h.hlen; omega,
    h.st_scr, h.d_st, h.d_scr, k16 s1 (by rw [hsp]; exact h.k_st), k16 s1 (by rw [hsp]; exact h.k_d),
    k16 s1 (by rw [hsp]; exact h.k_scr)⟩

theorem kabs_ok {src : Ptr} {len rate pos : Nat} (hs : NA src) {s : State} (h : KAbsH src len rate pos s) :
    WP isa (kabs src len rate pos) s fun s' => Post s s' [⟨pa s (sc 0), 200⟩, ⟨pa s (sc 200), 640⟩] ∧
      ∀ msg, Spec.Sha3.Repr s.mem (pa s (sc 0)) rate msg → pos = msg.length % rate →
        Spec.Sha3.Repr s'.mem (pa s (sc 0)) rate (msg ++ bytesAt s.mem (pa s src) len) := by
  have hr := rate_small h.hrate
  have := h.hpos
  refine WP.seq (WP.mono (kabsGlue_ok src len rate pos h.hoff h.hlen hr (by omega) hs s) fun s1 ⟨⟨hv, hm⟩, k⟩ => ?_)
  have hsp : s1.gpr .rsp = s.gpr .rsp := k.gpr (by decide)
  refine absorb_call (kabsArgs h hv k) (by rw [k.2.1, k.2.2]; exact h.c) (by rw [k.2.2]; exact h.w)
    fun s' hrd hwr hcs hf hR _ => ⟨⟨hrd.trans k.2.1, hwr.trans k.2.2,
      fun r hr => by rw [hcs r hr, k.gpr (argRegs_cs r hr)], ?_⟩, ?_⟩
  · rw [← hm, ← hsp]; exact Frame.below_mono hf (by omega) (by omega)
  · intro msg hmsg hpos
    rw [← hm] at hmsg ⊢
    exact hR msg hmsg hpos

theorem kabs_tr {src : Ptr} {len rate pos : Nat} (hs : NA src) :
    RelCT isa (fun x y => KAbsH src len rate pos x ∧ KAbsH src len rate pos y ∧ x.gpr .rbx = y.gpr .rbx ∧
      x.gpr src.1 = y.gpr src.1 ∧ x.gpr .rsp = y.gpr .rsp) (kabs src len rate pos) fun _ _ => True :=
  RelCT.seq (RelCT.postDep (Q := fun x1 y1 => ∃ x y, (KAbsH src len rate pos x ∧ KAbsH src len rate pos y ∧
      x.gpr .rbx = y.gpr .rbx ∧ x.gpr src.1 = y.gpr src.1 ∧ x.gpr .rsp = y.gpr .rsp) ∧
      (((x1.gpr .rdi = pa x (sc 0) ∧ x1.gpr .rsi = BitVec.ofNat 64 rate ∧ x1.gpr .rdx = BitVec.ofNat 64 pos ∧
        x1.gpr .rcx = pa x src ∧ x1.gpr .r8 = BitVec.ofNat 64 len ∧ x1.gpr .r9 = pa x (sc 200)) ∧ x1.mem = x.mem) ∧
        Keep argRegs x x1) ∧
      (((y1.gpr .rdi = pa y (sc 0) ∧ y1.gpr .rsi = BitVec.ofNat 64 rate ∧ y1.gpr .rdx = BitVec.ofNat 64 pos ∧
        y1.gpr .rcx = pa y src ∧ y1.gpr .r8 = BitVec.ofNat 64 len ∧ y1.gpr .r9 = pa y (sc 200)) ∧ y1.mem = y.mem) ∧
        Keep argRegs y y1))
    (block_nomem_tr (nomem_append (nomem_append (nomem_append (nomem_append (lea_nomem _ _) (fun i hi s => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; rcases hi with rfl | rfl <;> rfl)) (lea_nomem _ _))
      (mov32i_nomem _ _)) (lea_nomem _ _)))
    (fun x y ⟨hx, hy, _⟩ => ⟨kabsGlue_ok src len rate pos hx.hoff hx.hlen (rate_small hx.hrate)
      (by have := rate_small hx.hrate; have := hx.hpos; omega) hs x,
      kabsGlue_ok src len rate pos hy.hoff hy.hlen (rate_small hy.hrate)
      (by have := rate_small hy.hrate; have := hy.hpos; omega) hs y⟩)
    fun x y _ _ hp h1 h2 => ⟨x, y, hp, h1, h2⟩)
    (RelCT.callEx Proof.Sha3.X86_64.Stream.Absorb.absorb_correct Proof.Sha3.X86_64.Stream.Absorb.absorb_ct
      fun x1 y1 ⟨x, y, ⟨hx, hy, e1, e2, e3⟩, ⟨⟨hv1, _⟩, k1⟩, ⟨⟨hv2, _⟩, k2⟩⟩ => by
        have hs1 : x1.gpr .rsp = x.gpr .rsp := k1.gpr (by decide)
        have hs2 : y1.gpr .rsp = y.gpr .rsp := k2.gpr (by decide)
        refine ⟨_, _, _, _, absorb_pre (kabsArgs hx hv1 k1), absorb_pre (kabsArgs hy hv2 k2), ?_,
          by rw [k1.2.1, k1.2.2]; exact hx.c, by rw [k1.2.2]; exact hx.w, by rw [k2.2.1, k2.2.2]; exact hy.c,
          by rw [k2.2.2]; exact hy.w, by rw [hs1, hs2, e3]⟩
        simp only [Proof.Sha3.absorbX86_64, State.withRegions_gpr, State.callEntry_rsp,
          ce_gpr' _ (by decide : Reg.rdi ≠ .rsp), ce_gpr' _ (by decide : Reg.rsi ≠ .rsp),
          ce_gpr' _ (by decide : Reg.rdx ≠ .rsp), ce_gpr' _ (by decide : Reg.rcx ≠ .rsp),
          ce_gpr' _ (by decide : Reg.r8 ≠ .rsp), ce_gpr' _ (by decide : Reg.r9 ≠ .rsp), hv1.1, hv1.2.1, hv1.2.2.1,
          hv1.2.2.2.1, hv1.2.2.2.2.1, hv1.2.2.2.2.2, hv2.1, hv2.2.1, hv2.2.2.1, hv2.2.2.2.1, hv2.2.2.2.2.1,
          hv2.2.2.2.2.2, pa, e1, e2, hs1, hs2, e3, and_self])

/-! ## Padding -/

/-- What a call of `vg_keccak_pad` at position `pos` needs. -/
structure KPadH (rate pos : Nat) (s : State) : Prop where
  hrate : rate ∈ rates
  hpos : pos < rate
  st_scr : Region.Disjoint ⟨pa s (sc 0), 200⟩ ⟨pa s (sc 200), 640⟩
  k_st : (below (s.gpr .rsp) 32).Disjoint ⟨pa s (sc 0), 200⟩
  k_scr : (below (s.gpr .rsp) 32).Disjoint ⟨pa s (sc 200), 640⟩
  w : Covers [⟨pa s (sc 0), 200⟩, ⟨pa s (sc 200), 640⟩] s.wr

theorem b8_ofNat64 {v : Nat} (_hv : v < 256) : BitVec.setWidth 8 (BitVec.ofNat 64 v) = BitVec.ofNat 8 v := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem kpadGlue_ok (rate pos suffix : Nat) (hr : rate < 2 ^ 31) (hp : pos < 2 ^ 31) (hs : suffix < 256) (s : State) :
    WP isa (.block (lea .rdi (sc 0) ++ ([.mov32 .rsi (.imm (BitVec.ofNat 32 rate)),
      .mov32 .rdx (.imm (BitVec.ofNat 32 pos)), .mov32 .rcx (.imm (BitVec.ofNat 32 suffix))] : List Instr) ++
      lea .r8 (sc 200))) s fun s1 =>
      ((s1.gpr .rdi = pa s (sc 0) ∧ s1.gpr .rsi = BitVec.ofNat 64 rate ∧ s1.gpr .rdx = BitVec.ofNat 64 pos ∧
        s1.gpr .rcx = BitVec.ofNat 64 suffix ∧ s1.gpr .r8 = pa s (sc 200)) ∧ s1.mem = s.mem) ∧
        Keep argRegs s s1 := by
  refine WP.keep _ ?_ (by rfl)
  unfold lea
  xrun [sx_ofNat (show (0 : Nat) < 2 ^ 31 by decide), sx_ofNat (show (200 : Nat) < 2 ^ 31 by decide),
    sw_ofNat (show rate < 2 ^ 32 by omega), sw_ofNat (show pos < 2 ^ 32 by omega),
    sw_ofNat (show suffix < 2 ^ 32 by omega), List.cons_append, List.nil_append, pa_sc0]

theorem kpadArgs {rate pos suffix : Nat} {s s1 : State} (h : KPadH rate pos s)
    (hv : s1.gpr .rdi = pa s (sc 0) ∧ s1.gpr .rsi = BitVec.ofNat 64 rate ∧ s1.gpr .rdx = BitVec.ofNat 64 pos ∧
      s1.gpr .rcx = BitVec.ofNat 64 suffix ∧ s1.gpr .r8 = pa s (sc 200))
    (k : Keep argRegs s s1) : PadArgs s1 (pa s (sc 0)) (pa s (sc 200)) rate pos := by
  have hsp : s1.gpr .rsp = s.gpr .rsp := k.gpr (by decide)
  exact ⟨hv.1, hv.2.1, hv.2.2.1, hv.2.2.2.2, h.hrate, h.hpos, h.st_scr, k16 s1 (by rw [hsp]; exact h.k_st),
    k16 s1 (by rw [hsp]; exact h.k_scr)⟩

theorem kpad_ok {rate pos suffix : Nat} (hs : suffix < 256) {s : State} (h : KPadH rate pos s) :
    WP isa (kpad rate pos suffix) s fun s' => Post s s' [⟨pa s (sc 0), 200⟩, ⟨pa s (sc 200), 640⟩] ∧
      ∀ msg, Spec.Sha3.Repr s.mem (pa s (sc 0)) rate msg → pos = msg.length % rate →
        stateAt s'.mem (pa s (sc 0)) = absorb rate (pad rate (BitVec.ofNat 8 suffix) msg) := by
  have hr := rate_small h.hrate
  have := h.hpos
  refine WP.seq (WP.mono (kpadGlue_ok rate pos suffix hr (by omega) hs s) fun s1 ⟨⟨hv, hm⟩, k⟩ => ?_)
  have hsp : s1.gpr .rsp = s.gpr .rsp := k.gpr (by decide)
  refine pad_call (kpadArgs h hv k) (covers_nil_wr (by rw [k.2.2]; exact h.w)) (by rw [k.2.2]; exact h.w)
    fun s' hrd hwr hcs hf hR => ⟨⟨hrd.trans k.2.1, hwr.trans k.2.2,
      fun r hr => by rw [hcs r hr, k.gpr (argRegs_cs r hr)], ?_⟩, ?_⟩
  · rw [← hm, ← hsp]; exact Frame.below_mono hf (by omega) (by omega)
  · intro msg hmsg hpos
    rw [← hm] at hmsg
    rw [hR msg hmsg hpos, hv.2.2.2.1, b8_ofNat64 hs]

theorem kpad_tr {rate pos suffix : Nat} (hs : suffix < 256) :
    RelCT isa (fun x y => KPadH rate pos x ∧ KPadH rate pos y ∧ x.gpr .rbx = y.gpr .rbx ∧ x.gpr .rsp = y.gpr .rsp)
      (kpad rate pos suffix) fun _ _ => True :=
  RelCT.seq (RelCT.postDep (Q := fun x1 y1 => ∃ x y, (KPadH rate pos x ∧ KPadH rate pos y ∧
      x.gpr .rbx = y.gpr .rbx ∧ x.gpr .rsp = y.gpr .rsp) ∧
      (((x1.gpr .rdi = pa x (sc 0) ∧ x1.gpr .rsi = BitVec.ofNat 64 rate ∧ x1.gpr .rdx = BitVec.ofNat 64 pos ∧
        x1.gpr .rcx = BitVec.ofNat 64 suffix ∧ x1.gpr .r8 = pa x (sc 200)) ∧ x1.mem = x.mem) ∧ Keep argRegs x x1) ∧
      (((y1.gpr .rdi = pa y (sc 0) ∧ y1.gpr .rsi = BitVec.ofNat 64 rate ∧ y1.gpr .rdx = BitVec.ofNat 64 pos ∧
        y1.gpr .rcx = BitVec.ofNat 64 suffix ∧ y1.gpr .r8 = pa y (sc 200)) ∧ y1.mem = y.mem) ∧ Keep argRegs y y1))
    (block_nomem_tr (nomem_append (nomem_append (lea_nomem _ _) (fun i hi s => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; rcases hi with rfl | rfl | rfl <;> rfl))
      (lea_nomem _ _)))
    (fun x y ⟨hx, hy, _⟩ => ⟨kpadGlue_ok rate pos suffix (rate_small hx.hrate)
      (by have := rate_small hx.hrate; have := hx.hpos; omega) hs x,
      kpadGlue_ok rate pos suffix (rate_small hy.hrate) (by have := rate_small hy.hrate; have := hy.hpos; omega) hs y⟩)
    fun x y _ _ hp h1 h2 => ⟨x, y, hp, h1, h2⟩)
    (RelCT.callEx Proof.Sha3.X86_64.Stream.Pad.pad_correct Proof.Sha3.X86_64.Stream.Pad.pad_ct
      fun x1 y1 ⟨x, y, ⟨hx, hy, e1, e3⟩, ⟨⟨hv1, _⟩, k1⟩, ⟨⟨hv2, _⟩, k2⟩⟩ => by
        have hs1 : x1.gpr .rsp = x.gpr .rsp := k1.gpr (by decide)
        have hs2 : y1.gpr .rsp = y.gpr .rsp := k2.gpr (by decide)
        refine ⟨_, _, _, _, pad_pre (kpadArgs hx hv1 k1), pad_pre (kpadArgs hy hv2 k2), ?_,
          covers_nil_wr (by rw [k1.2.2]; exact hx.w), by rw [k1.2.2]; exact hx.w,
          covers_nil_wr (by rw [k2.2.2]; exact hy.w), by rw [k2.2.2]; exact hy.w, by rw [hs1, hs2, e3]⟩
        simp only [Proof.Sha3.padX86_64, State.withRegions_gpr, State.callEntry_rsp,
          ce_gpr' _ (by decide : Reg.rdi ≠ .rsp), ce_gpr' _ (by decide : Reg.rsi ≠ .rsp),
          ce_gpr' _ (by decide : Reg.rdx ≠ .rsp), ce_gpr' _ (by decide : Reg.r8 ≠ .rsp), hv1.1, hv1.2.1, hv1.2.2.1,
          hv1.2.2.2.2, hv2.1, hv2.2.1, hv2.2.2.1, hv2.2.2.2.2, pa, e1, hs1, hs2, e3, and_self])

/-! ## Squeezing -/

/-- What a call of `vg_keccak_squeeze` of `len` bytes to `dst` from position 0 needs. -/
structure KSqzH (dst : Ptr) (len rate : Nat) (s : State) : Prop where
  hoff : dst.2 < 2 ^ 31
  hlen : len < 2 ^ 31
  hrate : rate ∈ rates
  st_out : Region.Disjoint ⟨pa s (sc 0), 200⟩ ⟨pa s dst, len⟩
  st_scr : Region.Disjoint ⟨pa s (sc 0), 200⟩ ⟨pa s (sc 200), 640⟩
  out_scr : Region.Disjoint ⟨pa s dst, len⟩ ⟨pa s (sc 200), 640⟩
  k_st : (below (s.gpr .rsp) 32).Disjoint ⟨pa s (sc 0), 200⟩
  k_out : (below (s.gpr .rsp) 32).Disjoint ⟨pa s dst, len⟩
  k_scr : (below (s.gpr .rsp) 32).Disjoint ⟨pa s (sc 200), 640⟩
  w : Covers [⟨pa s (sc 0), 200⟩, ⟨pa s dst, len⟩, ⟨pa s (sc 200), 640⟩] s.wr

theorem ksqzGlue_ok (dst : Ptr) (len rate : Nat) (ho : dst.2 < 2 ^ 31) (hl : len < 2 ^ 31) (hr : rate < 2 ^ 31)
    (hs : NA dst) (s : State) :
    WP isa (.block (lea .rdi (sc 0) ++ ([.mov32 .rsi (.imm (BitVec.ofNat 32 rate)), .mov32 .rdx (.imm 0)] : List Instr) ++
      lea .rcx dst ++ ([.mov32 .r8 (.imm (BitVec.ofNat 32 len))] : List Instr) ++ lea .r9 (sc 200))) s fun s1 =>
      ((s1.gpr .rdi = pa s (sc 0) ∧ s1.gpr .rsi = BitVec.ofNat 64 rate ∧ s1.gpr .rdx = BitVec.ofNat 64 0 ∧
        s1.gpr .rcx = pa s dst ∧ s1.gpr .r8 = BitVec.ofNat 64 len ∧ s1.gpr .r9 = pa s (sc 200)) ∧ s1.mem = s.mem) ∧
        Keep argRegs s s1 := by
  have o1 : dst.1 ≠ .rsi := fun e => hs (by rw [e]; decide)
  have o2 : dst.1 ≠ .rdi := fun e => hs (by rw [e]; decide)
  have o3 : dst.1 ≠ .rdx := fun e => hs (by rw [e]; decide)
  refine WP.keep _ ?_ (by rfl)
  unfold lea
  xrun [sx_ofNat ho, sx_ofNat (show (0 : Nat) < 2 ^ 31 by decide), sx_ofNat (show (200 : Nat) < 2 ^ 31 by decide),
    o1, o2, o3, sw_ofNat (show rate < 2 ^ 32 by omega), sw_ofNat (show (0 : Nat) < 2 ^ 32 by decide),
    sw_ofNat (show len < 2 ^ 32 by omega), List.cons_append, List.nil_append, pa_sc0]

theorem ksqzArgs {dst : Ptr} {len rate : Nat} {s s1 : State} (h : KSqzH dst len rate s)
    (hv : s1.gpr .rdi = pa s (sc 0) ∧ s1.gpr .rsi = BitVec.ofNat 64 rate ∧ s1.gpr .rdx = BitVec.ofNat 64 0 ∧
      s1.gpr .rcx = pa s dst ∧ s1.gpr .r8 = BitVec.ofNat 64 len ∧ s1.gpr .r9 = pa s (sc 200))
    (k : Keep argRegs s s1) : SqueezeArgs s1 (pa s (sc 0)) (pa s dst) (pa s (sc 200)) rate 0 len := by
  have hsp : s1.gpr .rsp = s.gpr .rsp := k.gpr (by decide)
  exact ⟨hv.1, hv.2.1, hv.2.2.1, hv.2.2.2.1, hv.2.2.2.2.1, hv.2.2.2.2.2, h.hrate, Nat.zero_le _,
    by have := h.hlen; omega, h.st_out, h.st_scr, h.out_scr, k16 s1 (by rw [hsp]; exact h.k_st),
    k16 s1 (by rw [hsp]; exact h.k_out), k16 s1 (by rw [hsp]; exact h.k_scr)⟩

theorem ksqz_ok {dst : Ptr} {len rate : Nat} (hs : NA dst) {s : State} (h : KSqzH dst len rate s) :
    WP isa (ksqz rate dst len) s fun s' =>
      Post s s' [⟨pa s (sc 0), 200⟩, ⟨pa s dst, len⟩, ⟨pa s (sc 200), 640⟩] ∧
      bytesAt s'.mem (pa s dst) len = Spec.Sha3.squeezeFrom rate (stateAt s.mem (pa s (sc 0))) 0 len := by
  have hr := rate_small h.hrate
  refine WP.seq (WP.mono (ksqzGlue_ok dst len rate h.hoff h.hlen hr hs s) fun s1 ⟨⟨hv, hm⟩, k⟩ => ?_)
  have hsp : s1.gpr .rsp = s.gpr .rsp := k.gpr (by decide)
  refine squeeze_call (ksqzArgs h hv k) (covers_nil_wr (by rw [k.2.2]; exact h.w)) (by rw [k.2.2]; exact h.w)
    fun s' hrd hwr hcs hf ho => ⟨⟨hrd.trans k.2.1, hwr.trans k.2.2,
      fun r hr => by rw [hcs r hr, k.gpr (argRegs_cs r hr)], ?_⟩, ?_⟩
  · rw [← hm, ← hsp]; exact Frame.below_mono hf (by omega) (by omega)
  · rw [ho, hm]

theorem ksqz_tr {dst : Ptr} {len rate : Nat} (hs : NA dst) :
    RelCT isa (fun x y => KSqzH dst len rate x ∧ KSqzH dst len rate y ∧ x.gpr .rbx = y.gpr .rbx ∧
      x.gpr dst.1 = y.gpr dst.1 ∧ x.gpr .rsp = y.gpr .rsp) (ksqz rate dst len) fun _ _ => True :=
  RelCT.seq (RelCT.postDep (Q := fun x1 y1 => ∃ x y, (KSqzH dst len rate x ∧ KSqzH dst len rate y ∧
      x.gpr .rbx = y.gpr .rbx ∧ x.gpr dst.1 = y.gpr dst.1 ∧ x.gpr .rsp = y.gpr .rsp) ∧
      (((x1.gpr .rdi = pa x (sc 0) ∧ x1.gpr .rsi = BitVec.ofNat 64 rate ∧ x1.gpr .rdx = BitVec.ofNat 64 0 ∧
        x1.gpr .rcx = pa x dst ∧ x1.gpr .r8 = BitVec.ofNat 64 len ∧ x1.gpr .r9 = pa x (sc 200)) ∧ x1.mem = x.mem) ∧
        Keep argRegs x x1) ∧
      (((y1.gpr .rdi = pa y (sc 0) ∧ y1.gpr .rsi = BitVec.ofNat 64 rate ∧ y1.gpr .rdx = BitVec.ofNat 64 0 ∧
        y1.gpr .rcx = pa y dst ∧ y1.gpr .r8 = BitVec.ofNat 64 len ∧ y1.gpr .r9 = pa y (sc 200)) ∧ y1.mem = y.mem) ∧
        Keep argRegs y y1))
    (block_nomem_tr (nomem_append (nomem_append (nomem_append (nomem_append (lea_nomem _ _) (fun i hi s => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; rcases hi with rfl | rfl <;> rfl)) (lea_nomem _ _))
      (mov32i_nomem _ _)) (lea_nomem _ _)))
    (fun x y ⟨hx, hy, _⟩ => ⟨ksqzGlue_ok dst len rate hx.hoff hx.hlen (rate_small hx.hrate) hs x,
      ksqzGlue_ok dst len rate hy.hoff hy.hlen (rate_small hy.hrate) hs y⟩)
    fun x y _ _ hp h1 h2 => ⟨x, y, hp, h1, h2⟩)
    (RelCT.callEx Proof.Sha3.X86_64.Stream.Squeeze.squeeze_correct Proof.Sha3.X86_64.Stream.Squeeze.squeeze_ct
      fun x1 y1 ⟨x, y, ⟨hx, hy, e1, e2, e3⟩, ⟨⟨hv1, _⟩, k1⟩, ⟨⟨hv2, _⟩, k2⟩⟩ => by
        have hs1 : x1.gpr .rsp = x.gpr .rsp := k1.gpr (by decide)
        have hs2 : y1.gpr .rsp = y.gpr .rsp := k2.gpr (by decide)
        refine ⟨_, _, _, _, squeeze_pre (ksqzArgs hx hv1 k1), squeeze_pre (ksqzArgs hy hv2 k2), ?_,
          covers_nil_wr (by rw [k1.2.2]; exact hx.w), by rw [k1.2.2]; exact hx.w,
          covers_nil_wr (by rw [k2.2.2]; exact hy.w), by rw [k2.2.2]; exact hy.w, by rw [hs1, hs2, e3]⟩
        simp only [Proof.Sha3.squeezeX86_64, State.withRegions_gpr, State.callEntry_rsp,
          ce_gpr' _ (by decide : Reg.rdi ≠ .rsp), ce_gpr' _ (by decide : Reg.rsi ≠ .rsp),
          ce_gpr' _ (by decide : Reg.rdx ≠ .rsp), ce_gpr' _ (by decide : Reg.rcx ≠ .rsp),
          ce_gpr' _ (by decide : Reg.r8 ≠ .rsp), ce_gpr' _ (by decide : Reg.r9 ≠ .rsp), hv1.1, hv1.2.1, hv1.2.2.1,
          hv1.2.2.2.1, hv1.2.2.2.2.1, hv1.2.2.2.2.2, hv2.1, hv2.2.1, hv2.2.2.1, hv2.2.2.2.1, hv2.2.2.2.2.1,
          hv2.2.2.2.2.2, pa, e1, e2, hs1, hs2, e3, and_self])

end VG.Proof.MlKem.X86_64
