import VerifiedGarbage.Proof.X25519.X86_64.Ifma.Setup

/-!
# X25519 on x86-64 with AVX512_IFMA: the ladder

`vladder`: `vsetup`, then with MXCSR `0x1FBF` the loop and `vfinish`, leaves
the ladder's final `(x₂, z₂, x₃, z₃)` in the slots `x2, z2, x3, z3`, and its
`swap` at `SWAP`, as `vg_x25519`'s ladder does (`LPost`).
-/

namespace VG.Proof.X25519.X86_64.Ifma

open VG VG.X86_64 VG.Impl.X25519.X86_64 VG.Impl.X25519.X86_64.Ifma VG.Proof.X25519 VG.Spec.X25519
open VG.Proof.X25519.X86_64 (Scr Outside Outside.mono ofs off word val4 F E fe clob contains_sc ea_sc
  writeW_outside LPost)
open VG.Proof.Poly1305.X86_64.Avx2 (xr qw)

/-! ## The loop -/

/-- The ladder's loop, from the counter `n ≥ 1` down to 0. -/
theorem vloop_ok {s₀ : State} {base : Addr} {k : Nat} {u : Fe} {x1 : Nat → Nat}
    (hbits : ∀ t < 255, s₀.mem (off base (BITS + t)) = BitVec.ofNat 8 (bit k t)) :
    ∀ n, ∀ s, 1 ≤ n → n ≤ 255 → VInv base k u x1 s₀ s n →
      WP isa (.loop (.block vstep) .ne) s fun s' => VInv base k u x1 s₀ s' 0 := by
  intro n s h1 h2 hi
  refine WP.loop (M := isa) (body := .block vstep) (c := .ne)
    (Q := fun s' => VInv base k u x1 s₀ s' 0)
    (fun m (s : State) => 1 ≤ m ∧ m ≤ 255 ∧ VInv base k u x1 s₀ s m) ?_ n s ⟨h1, h2, hi⟩
  intro m s ⟨h1, h2, hi⟩
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  refine WP.mono (vstep_ok (by omega) hbits hi) fun s' ⟨hi', hz⟩ => ?_
  simp only [eval, hz, Option.map_some]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact .inl ⟨rfl, hi'⟩
  · refine .inr ⟨by simp only [decide_eq_false (by omega : ¬m = 0), Bool.not_false], m, by omega,
      by omega, by omega, hi'⟩

/-! ## MXCSR -/

theorem mx_in {s : State} {base : Addr} (hs : Scr s base) {d n : Nat} (hd : d + n ≤ 4096) :
    InRegions s.wr (off base d) n := ⟨_, hs.wr, contains_sc hd⟩

theorem mx_in' {s : State} {base : Addr} (hs : Scr s base) {d n : Nat} (hd : d + n ≤ 4096) :
    InRegions (s.rd ++ s.wr) (off base d) n := ⟨_, List.mem_append_right _ hs.wr, contains_sc hd⟩

/-- What the MXCSR blocks keep. -/
structure MxKeep (base : Addr) (s s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : Outside base MX 8 s.mem s'.mem
  xmm : s'.xmm = s.xmm
  ymm : s'.ymmHi = s.ymmHi

theorem MxKeep.lanes {base : Addr} {s s' : State} (h : MxKeep base s s') (r l i : Nat) :
    lanes s' r l i = lanes s r l i := lanes_of_vec h.xmm h.ymm r l i

theorem outside_mx (m : Mem) (base : Addr) {d : Nat} (hd : MX ≤ d ∧ d + 4 ≤ MX + 8) (v : BitVec 32) :
    Outside base MX 8 m (m.writeW (off base d) v) := by
  intro x hx
  simp only [Mem.writeW]
  apply Mem.write_apply
  rw [Offset.lt_iff x base (by simp only [MX] at hd ⊢; omega)]
  simp only [ofs] at hx
  simp only [MX] at hd hx ⊢
  omega

/-- The save: MXCSR (its reserved bits cleared) into `r11`. -/
theorem save_wp {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block [.stmxcsr (sc MX), .mov32 .r11 (.mem (sc MX)), .alu32 .and .r11 (.imm 0xFFFF)]) s
      fun s' => (∀ r, r ≠ .r11 → s'.gpr r = s.gpr r) ∧
        (s'.gpr .r11).setWidth 32 = s.mxcsr &&& 0xFFFF ∧ MxKeep base s s' := by
  apply WP.of_runBlock
  have h1 := mx_in hs (show MX + 4 ≤ 4096 by decide)
  have h2 := mx_in' hs (show MX + 4 ≤ 4096 by decide)
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.store32, State.load32, readSrc32, ea_sc,
    hs.rdi, h1, h2, ite_true, Option.bind_some, Option.map_some, Mem.readW_writeW_self32, execAlu32,
    State.setReg32, Option.some.injEq, exists_eq_left']
  refine ⟨fun r hr => ?_, ?_, ⟨rfl, rfl, outside_mx _ _ (by simp only [MX]; omega) _, rfl, rfl⟩⟩
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]
  · simp only [RegUpd.gpr_setReg_self, BitVec.setWidth_setWidth_of_le _ (show 32 ≤ 64 by decide),
      BitVec.setWidth_eq]

/-- `0x1FBF` into MXCSR, through `[MX + 4]` and `rax`. -/
theorem load_wp {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block [.mov32 .rax (.imm 0x1FBF), .store32 (sc (MX + 4)) .rax, .ldmxcsr (sc (MX + 4)), .lfence]) s
      fun s' => (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧ MxKeep base s s' := by
  apply WP.of_runBlock
  have h1 := mx_in hs (show MX + 4 + 4 ≤ 4096 by decide)
  have h2 := mx_in' hs (show MX + 4 + 4 ≤ 4096 by decide)
  have e : (BitVec.setWidth 32 (BitVec.setWidth 64 (0x1FBF : BitVec 32))).extractLsb' 16 16 = 0 := by decide
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.store32, State.load32, readSrc32, ea_sc,
    RegUpd.gpr_setReg, RegUpd.wr_setReg, RegUpd.rd_setReg, hs.rdi, h1, h2, ite_true, ite_false, reduceCtorEq,
    Option.bind_some, Option.map_some, Mem.readW_writeW_self32, State.setReg32, e, Option.some.injEq,
    exists_eq_left']
  refine ⟨fun r hr => ?_, ⟨rfl, rfl, outside_mx _ _ (by simp only [MX]; omega) _, rfl, rfl⟩⟩
  simp only [hr, ite_false]

/-- MXCSR back from `r11`, through `[MX]`. -/
theorem restore_wp {s : State} {base : Addr} (hs : Scr s base)
    (h11 : ((s.gpr .r11).setWidth 32).extractLsb' 16 16 = 0) :
    WP isa (.block [.store32 (sc MX) .r11, .ldmxcsr (sc MX)]) s
      fun s' => s'.gpr = s.gpr ∧ MxKeep base s s' := by
  apply WP.of_runBlock
  have h1 := mx_in hs (show MX + 4 ≤ 4096 by decide)
  have h2 := mx_in' hs (show MX + 4 ≤ 4096 by decide)
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.store32, State.load32, ea_sc, hs.rdi, h1,
    h2, ite_true, Option.bind_some, Mem.readW_writeW_self32, h11, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, ⟨rfl, rfl, outside_mx _ _ (by simp only [MX]; omega) _, rfl, rfl⟩⟩

theorem and_ffff (v : BitVec 32) : (v &&& 0xFFFF).extractLsb' 16 16 = 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_and, hi, decide_true, Bool.true_and]
  rw [show (0xFFFF : BitVec 32).getLsbD (16 + i) = false by revert i; decide]
  simp

/-! ## The ladder -/

theorem movRbx_wp (s : State) :
    WP isa (.block [.mov32 .rbx (.imm 255)]) s fun s' =>
      s'.gpr .rbx = BitVec.ofNat 64 255 ∧ (∀ r, r ≠ .rbx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
        s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.xmm = s.xmm ∧ s'.ymmHi = s.ymmHi := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, Option.map_some,
    State.setReg32, Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg_self]
  exact ⟨rfl, fun r hr => by simp only [RegUpd.gpr_setReg, hr, ite_false], rfl, rfl, rfl, rfl, rfl⟩

theorem lfence_wp (s : State) : WP isa (.block [.lfence]) s fun s' => s' = s := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Option.some.injEq, exists_eq_left']

theorem fe5_one' : fe5 (fun i => if i = 0 then 1 else 0) = 1 := fe5_one
theorem fe5_zero : fe5 (fun _ => 0) = 0 := rfl

theorem vladder_eq : vladder = .seq (.block vsetup) (.seq (.block [.stmxcsr (sc MX), .mov32 .r11 (.mem (sc MX)),
    .alu32 .and .r11 (.imm 0xFFFF)]) (.seq (.seq (.block [.mov32 .rax (.imm 0x1FBF), .store32 (sc (MX + 4)) .rax,
      .ldmxcsr (sc (MX + 4)), .lfence]) (.seq (.seq (.block [.mov32 .rbx (.imm 255)])
        (.seq (.loop (.block vstep) .ne) (.block vfinish))) (.block [.lfence])))
      (.block [.store32 (sc MX) .r11, .ldmxcsr (sc MX)]))) := rfl

/-- The ladder: from the words of `x₁` at `X1` and `swap = 0`, the ladder's
final state. -/
theorem vladder_ok {s₀ : State} {base : Addr} {k : Nat} {u : Fe} (hs : Scr s₀ base)
    (hbits : ∀ t < 255, s₀.mem (off base (BITS + t)) = BitVec.ofNat 8 (bit k t))
    (hx1 : E s₀.mem base 2 = u) (hsw : word s₀.mem base SWAP = 0) :
    WP isa vladder s₀ (LPost base k u s₀) := by
  rw [vladder_eq]
  refine WP.seq (WP.mono (vsetup_wp hs) fun s₁ ⟨g₁, rd₁, wr₁, mx₁, o₁, hk₁, l₁⟩ => ?_)
  have hs₁ : Scr s₁ base := ⟨by rw [g₁ _ (by decide)]; exact hs.rdi, by rw [wr₁]; exact hs.wr, hs.nowrap⟩
  refine WP.seq (WP.mono (save_wp hs₁) fun s₂ ⟨g₂, r11₂, k₂⟩ => ?_)
  have hs₂ : Scr s₂ base := ⟨by rw [g₂ _ (by decide)]; exact hs₁.rdi, by rw [k₂.wr]; exact hs₁.wr, hs.nowrap⟩
  refine WP.seq (WP.seq (WP.mono (load_wp hs₂) fun s₃ ⟨g₃, k₃⟩ => ?_))
  have hs₃ : Scr s₃ base := ⟨by rw [g₃ _ (by decide)]; exact hs₂.rdi, by rw [k₃.wr]; exact hs₂.wr, hs.nowrap⟩
  refine WP.seq (WP.seq (WP.mono (movRbx_wp s₃) fun s₄ ⟨b₄, g₄, m₄, rd₄, wr₄, x₄, y₄⟩ => ?_))
  have hs₄ : Scr s₄ base := ⟨by rw [g₄ _ (by decide)]; exact hs₃.rdi, by rw [wr₄]; exact hs₃.wr, hs.nowrap⟩
  -- memory up to the loop
  have O₄ : Outside base 64 2152 s₀.mem s₄.mem := by
    rw [m₄]
    exact ((o₁.mono (by decide) (by decide)).trans (k₂.mem.mono (by decide) (by decide))).trans
      (k₃.mem.mono (by decide) (by decide))
  have O₁₄ : Outside base MX 8 s₁.mem s₄.mem := by rw [m₄]; exact k₂.mem.trans k₃.mem
  have hk₄ : Consts s₄.mem base (xl s₀.mem base) := hk₁.of_word fun d h1 h2 => by
    rw [mq_eq_word, mq_eq_word]
    exact O₁₄.word (by simp only [MX]; omega) (by omega)
  have lan₄ : ∀ l < 4, ∀ i < 5, lanes s₄ 0 l i =
      if l = 2 then xl s₀.mem base i else if i = 0 ∧ (l = 0 ∨ l = 3) then 1 else 0 := fun l hl i hi => by
    rw [lanes_of_vec x₄ y₄, k₃.lanes, k₂.lanes, l₁ l hl i hi]
  have bits₄ : ∀ t < 255, s₄.mem (off base (BITS + t)) = BitVec.ofNat 8 (bit k t) := fun t ht => by
    have ho : ofs base (off base (BITS + t)) = BITS + t :=
      VG.Proof.X25519.X86_64.ofs_off' base (by simp only [BITS]; omega)
    rw [O₁₄ _ (by rw [ho]; simp only [BITS, MX]; omega), o₁ _ (by rw [ho]; simp only [BITS]; omega)]
    exact hbits t ht
  have fx1 : fe5 (xl s₀.mem base) = u := by
    rw [← hx1]
    show toFe _ = toFe _
    congr 1
    rw [xl, limbNat_lv _ (fun k _ => BitVec.isLt _)]
    rfl
  have I : VInv base k u (xl s₀.mem base) s₄ s₄ 255 := by
    refine ⟨hs₄, fun _ _ => rfl, b₄, rfl, rfl, VFrame.refl _ _, hk₄, fx1, ?_, fun l hl i hi => ?_, ?_, ?_, ?_, ?_⟩
    · show word s₄.mem base SWAP = BitVec.ofNat 64 0
      rw [O₁₄.word (by simp only [SWAP, MX]; omega) (by simp only [SWAP]; omega),
        o₁.word (by simp only [SWAP]; omega) (by simp only [SWAP]; omega), hsw]; rfl
    · rw [lan₄ l hl i hi]; have := hk₄.x1 i hi; split <;> [omega; split <;> omega]
    · rw [fe5_congr (fun i hi => lan₄ 0 (by decide) i hi)]; exact fe5_one'
    · rw [fe5_congr (fun i hi => lan₄ 1 (by decide) i hi)]; simp only [Nat.one_ne_zero, false_or,
        show (1 : Nat) ≠ 3 by decide, and_false, ite_false]; exact fe5_zero
    · rw [fe5_congr (fun i hi => lan₄ 2 (by decide) i hi)]; simp only [ite_true]; exact fx1
    · rw [fe5_congr (fun i hi => lan₄ 3 (by decide) i hi)]
      simp only [show (3 : Nat) ≠ 2 by decide, ite_false, or_true, and_true]; exact fe5_one'
  refine WP.seq (WP.mono (vloop_ok bits₄ 255 s₄ (by decide) (by decide) I) fun s₅ V => ?_)
  refine WP.mono (vfinish_wp V.scr V.consts V.lim) fun s₆ ⟨g₆, rd₆, wr₆, mx₆, o₆, f₆⟩ => ?_
  refine WP.mono (lfence_wp s₆) fun s₇ e₇ => ?_
  subst e₇
  have hs₆ : Scr s₇ base := ⟨by rw [g₆]; exact V.scr.rdi, by rw [wr₆]; exact V.scr.wr, hs.nowrap⟩
  have r11₇ : s₇.gpr .r11 = s₂.gpr .r11 := by
    rw [g₆, V.gpr _ (by decide), g₄ _ (by decide), g₃ _ (by decide)]
  refine WP.mono (restore_wp hs₆ (by rw [r11₇, r11₂]; exact and_ffff _)) fun s₈ ⟨g₈, k₈⟩ => ?_
  have fe8 : ∀ m (hm : m < 4), E s₈.mem base ⟨3 + m, by omega⟩ = fe5 (lanes s₅ 0 m) := fun m hm => by
    show toFe (fe s₈.mem base (32 * (3 + m))) = _
    have hm' : m < 4 := hm
    rw [k₈.mem.fe (d := 32 * (3 + m)) (by simp only [MX]; left; omega) (by omega)]
    have := f₆ m hm
    simp only [X2] at this
    rw [show 32 * (3 + m) = 96 + 32 * m by omega]
    exact this
  refine ⟨⟨by rw [g₈]; exact hs₆.rdi, by rw [k₈.wr]; exact hs₆.wr, hs.nowrap⟩, fun r hr hb => ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · have h1 : r ∉ cregs := fun h => hr (by simp only [cregs, clob, List.mem_cons] at h ⊢; tauto)
    have h2 : r ≠ .r11 := fun h => hr (by subst h; decide)
    have h3 : r ≠ .rax := fun h => hr (by subst h; decide)
    have h4 : r ∉ [Reg.rax, .rbx, .rcx, .rdx] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      intro h
      rcases h with h | h | h | h <;> subst h
      · exact hr (by decide)
      · exact hb rfl
      · exact hr (by decide)
      · exact hr (by decide)
    rw [g₈, g₆, V.gpr r h4, g₄ r hb, g₃ r h3, g₂ r h2, g₁ r h1]
  · rw [k₈.rd, rd₆, V.rd, rd₄, k₃.rd, k₂.rd, rd₁]
  · rw [k₈.wr, wr₆, V.wr, wr₄, k₃.wr, k₂.wr, wr₁]
  · have F₅ : Outside base 64 2152 s₄.mem s₅.mem := fun x hx => V.mem x (by omega)
    exact ((O₄.trans F₅).trans (o₆.mono (by decide) (by decide))).trans (k₈.mem.mono (by decide) (by decide))
  · exact (fe8 0 (by decide)).trans V.x2
  · exact (fe8 1 (by decide)).trans V.z2
  · exact (fe8 2 (by decide)).trans V.x3
  · exact (fe8 3 (by decide)).trans V.z3
  · rw [k₈.mem.word (by simp only [SWAP, MX]; omega) (by simp only [SWAP]; omega),
      o₆.word (by simp only [SWAP]; omega) (by simp only [SWAP]; omega)]
    exact V.swap

end VG.Proof.X25519.X86_64.Ifma
