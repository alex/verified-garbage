import VerifiedGarbage.Proof.Poly1305.X86_64.Update

/-!
# Poly1305 on x86-64: `update`, from the call on

The call of an implementation of `vg_poly1305_blocks` for the whole blocks of
the data (`BlocksImpl`), copying the rest into the buffer, restoring the
registers, and the whole function.
-/

open VG.PowLit

namespace VG.Proof.Poly1305.X86_64

open VG VG.X86_64 VG.Impl.Poly1305.X86_64
open VG.Spec.Poly1305 (P clamp leNum bytesAt accumulate Repr Buffered)

/-! ## The call -/

/-- After the call, or none: what is kept across it, and the whole blocks of
the data absorbed. -/
structure After (s₀ : State) (c : Nat) (s : State) : Prop where
  rbx : s.gpr .rbx = st s₀
  rbp : s.gpr .rbp = dp s₀ + BitVec.ofNat 64 c
  r12 : s.gpr .r12 = BitVec.ofNat 64 (dl s₀ - c)
  r15 : s.gpr .r15 = scr s₀
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [sR (st s₀), scR s₀, stkR s₀] s₀.mem s.mem
  saved : SavedAt (scr s₀) s₀ s.mem
  c_le : c ≤ dl s₀
  st : StOk s₀ (c + 16 * ((dl s₀ - c) / 16)) s.mem

/-- No whole blocks: nothing to call. -/
theorem Ready.after {s₀ : State} {c : Nat} {s : State} (h : Ready s₀ c s) (hlt : dl s₀ - c < 16) :
    After s₀ c s where
  rbx := h.rbx
  rbp := h.rbp
  r12 := h.r12
  r15 := h.r15
  rsp := h.rsp
  rd := h.rd
  wr := h.wr
  frame := h.frame.mono (by simp)
  saved := h.saved
  c_le := h.c_le
  st := by rw [Nat.div_eq_of_lt hlt, Nat.mul_zero, Nat.add_zero]; exact h.st

/-- The return address a call stores. -/
theorem callEntry_frame (s : State) : Frame [below (s.gpr .rsp) 8] s.mem s.callEntry.mem := by
  rw [State.callEntry_mem]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (below_call _ (by decide) (by decide))

/-- Data from byte `a`. -/
theorem dsub (s₀ : State) {a n : Nat} (h : a + n ≤ dl s₀) :
    Region.Sub ⟨dp s₀ + BitVec.ofNat 64 a, n⟩ (dR s₀) := Offset.sub_base _ h

/-- The stack the callee uses: its return address, and up to 16 bytes below. -/
theorem callee_stk (sp : Addr) {k : Nat} (hk : k ≤ 16) : Region.Sub (below (sp - 8) k) (below sp 24) :=
  fun x hx => below_sub (by omega_using [hk]) (by decide) x (below_callee sp k x hx)

theorem ret8_stk (sp : Addr) : Region.Sub (below sp 8) (below sp 24) := below_sub (by decide) (by decide)

/-- The blocks the call absorbs. -/
abbrev blkR (s₀ : State) (c : Nat) : Region := ⟨dp s₀ + BitVec.ofNat 64 c, 16 * ((dl s₀ - c) / 16)⟩

theorem blk_toNat (s₀ : State) (c : Nat) :
    (BitVec.ofNat 64 ((dl s₀ - c) / 16)).toNat = (dl s₀ - c) / 16 := by
  have := dl_lt s₀
  exact toNat_ofNat_lt (by omega_using [this])

theorem blk_le {s₀ : State} {c : Nat} (h : c ≤ dl s₀) : c + 16 * ((dl s₀ - c) / 16) ≤ dl s₀ := by
  have := Nat.mul_div_le (dl s₀ - c) 16; omega_using [this, h]

theorem blk_dR {s₀ : State} {c : Nat} (h : c ≤ dl s₀) : Region.Sub (blkR s₀ c) (dR s₀) :=
  dsub s₀ (blk_le h)

section
variable (v : BlocksImpl) {s₀ : State} (hp : UPre s₀) {c : Nat} {s : State} (h : Ready s₀ c s)
include hp h

/-- The callee's precondition, with the regions it is given, and that it is given
regions we have. -/
theorem call_pre :
    (blocksStack v.stack).pre (s.callEntry.withRegions [blkR s₀ c] [sR (st s₀)]) ∧
    Covers ([blkR s₀ c] ++ [sR (st s₀)]) (s.rd ++ s.wr) ∧ Covers [sR (st s₀)] s.wr := by
  have hsp : s.gpr .rsp = s₀.gpr .rsp := h.rsp
  have hstk : Region.Sub (below (s.gpr .rsp) 24) (stkR s₀) := by rw [hsp]; exact fun _ h => h
  have hle := blk_le h.c_le
  have hdl := dl_lt s₀
  refine ⟨?_, ?_, ?_⟩
  · simp only [blocksStack, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
      State.callEntry_rsp, State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp),
      State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp),
      h.rdi, h.rsi, h.rdx, blk_toNat]
    refine ⟨trivial, trivial, (hp.d_st.sub_left (blk_dR h.c_le)).symm,
      hp.stk_st.sub_left (fun x hx => hstk x (ret8_stk _ x hx)),
      hp.stk_st.sub_left (fun x hx => hstk x (callee_stk _ v.stack_le x hx)),
      (hp.stk_d.sub_left (fun x hx => hstk x (callee_stk _ v.stack_le x hx))).sub_right (blk_dR h.c_le), ?_⟩
    · have e := BitVec.toNat_add (dp s₀) (BitVec.ofNat 64 c)
      have e' : (dp s₀ + BitVec.ofNat 64 c).toNat ≤ (dp s₀).toNat + c := by
        rw [e, toNat_ofNat_lt (by omega_using [hdl, h.c_le])]; exact Nat.mod_le _ _
      have := hp.nowrap
      omega_using [e', this, hle]
  · refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨dR s₀, by rw [h.rd, hp.rd]; exact List.mem_cons_self, c, rfl, hle⟩
    · exact ⟨sR (st s₀), by rw [h.wr, hp.wr]; exact List.mem_append_right _ List.mem_cons_self, 0,
        by simp, (Nat.zero_add _).le⟩
  · refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨sR (st s₀), by rw [h.wr]; exact hp.st_in, 0, by simp, (Nat.zero_add _).le⟩

/-- The call of an implementation of `vg_poly1305_blocks`, when there are
whole blocks: it keeps the callee-saved registers and the bits of MXCSR that
`abiPreserved` keeps. -/
theorem call_ok (hge : 16 ≤ dl s₀ - c) :
    WP isa (.call v.name v.code) s fun s' => After s₀ c s' ∧ (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      s'.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10 := by
  obtain ⟨hpre, hc, hw⟩ := call_pre v hp h
  have hle := blk_le h.c_le
  have hsp : s.gpr .rsp = s₀.gpr .rsp := h.rsp
  have hd := v.depth_le
  refine WP.call_mx (k := blocksStack v.stack) v.ok v.nosp (by omega_using [hd]) hpre hc hw ?_
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, _, hpost⟩ hmx'
  have cs : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r := hcs
  have hf' : Frame [sR (st s₀), stkR s₀] s.mem s'.mem := hf.sub fun r hr => by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
    · refine ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun x hx => ?_⟩
      rw [hsp] at hx
      exact below_sub (a := 8 * (v.code.depth + 1)) (b := 24) (by omega_using [hd]) (by decide) x hx
  -- The data absorbed, as on entry.
  have hblk : bytesAt s.callEntry.mem (dp s₀ + BitVec.ofNat 64 c) (16 * ((dl s₀ - c) / 16)) =
      bytesAt s₀.mem (dp s₀ + BitVec.ofNat 64 c) (16 * ((dl s₀ - c) / 16)) := by
    have hdl := dl_lt s₀
    rw [Poly1305.bytesAt_frame (callEntry_frame s) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        rw [hsp]
        exact ((hp.stk_d.sub_left (ret8_stk _)).sub_right (blk_dR h.c_le)).symm)
      (by omega_using [hdl, hle])]
    refine Poly1305.bytesAt_frame h.frame (fun r hr => ?_) (by omega_using [hdl, hle])
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.d_st.sub_left (blk_dR h.c_le)
    · exact hp.d_sc.sub_left (blk_dR h.c_le)
  simp only [blocksStack, Proof.Poly1305.blocksX86_64, State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp), h.rdi, h.rsi, h.rdx, blk_toNat, hm₂, hblk] at hpost
  obtain ⟨X, Y, hX, hY, hXY, hYd, hbuf, hrep⟩ := h.st
  have hY0 : Y = [] := hYd.resolve_right (by omega_using [hge])
  subst hY0
  refine ⟨{ rbx := by rw [cs _ (by simp [calleeSaved]), h.rbx]
            rbp := by rw [cs _ (by simp [calleeSaved]), h.rbp]
            r12 := by rw [cs _ (by simp [calleeSaved]), h.r12]
            r15 := by rw [cs _ (by simp [calleeSaved]), h.r15]
            rsp := by rw [cs _ (by simp [calleeSaved]), hsp]
            rd := hrd.trans h.rd
            wr := hwr.trans h.wr
            frame := (h.frame.mono (by simp)).trans (hf'.mono (by simp))
            saved := h.saved.frame hf' (fun r hr => by
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
              rcases hr with rfl | rfl
              · exact hp.st_sc.symm
              · exact hp.stk_sc.symm)
            c_le := h.c_le
            st := ⟨X ++ bytesAt s₀.mem (dp s₀ + BitVec.ofNat 64 c) (16 * ((dl s₀ - c) / 16)), [], ?_, by decide,
              ?_, .inl rfl, rfl, fun key W hr => ?_⟩ }, cs, hmx'⟩
  · simp only [List.length_append, Poly1305.length_bytesAt]; omega_using [hX]
  · rw [List.append_nil, Dt, Poly1305.bytesAt_add, ← List.append_assoc]
    rw [List.append_nil] at hXY
    rw [hXY]
  · have := hpost key (W ++ X) (repr_frame (callEntry_frame s) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [hsp]
      exact (hp.stk_st.sub_left (ret8_stk _)).symm.sub_left (rpR_sub _)) (hrep key W hr))
    rw [List.append_assoc] at this
    exact this

end

/-! ## After the call -/

theorem wp_andi {is : List Instr} {s : State} {Q : State → Prop} {d : Reg} {v : BitVec 32}
    (k : ∀ s', Upd s s' d (s.gpr d &&& v.signExtend 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .and d (.imm v) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _))

theorem wp_add {is : List Instr} {s : State} {Q : State → Prop} {d r : Reg}
    (k : ∀ s', Upd s s' d (s.gpr d + s.gpr r) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .add d (.reg r) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _))

/-- Before copying the rest: `d` bytes of data consumed, fewer than 16 left. -/
structure Res (s₀ : State) (d : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = st s₀
  rsi : s.gpr .rsi = dp s₀ + BitVec.ofNat 64 d
  rcx : s.gpr .rcx = BitVec.ofNat 64 (dl s₀ - d)
  d_le : d ≤ dl s₀
  lt : dl s₀ - d < 16
  r15 : s.gpr .r15 = scr s₀
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [sR (st s₀), scR s₀, stkR s₀] s₀.mem s.mem
  saved : SavedAt (scr s₀) s₀ s.mem
  st : StOk s₀ d s.mem

theorem resume_ok {s₀ : State} {c : Nat} {s : State} (h : After s₀ c s) :
    WP isa (.block resume) s (Res s₀ (c + 16 * ((dl s₀ - c) / 16))) := by
  have hdl := dl_lt s₀
  have hc := h.c_le
  unfold resume
  refine wp_mov fun s₁ u₁ => wp_mov fun s₂ u₂ => wp_andi fun s₃ u₃ => wp_mov fun s₄ u₄ =>
    wp_sub fun s₅ u₅ => wp_add fun s₆ u₆ => WP.block_nil ?_
  have g : ∀ r, r ≠ .rdi → r ≠ .rcx → r ≠ .rsi → s₆.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [u₆.other r h3, u₅.other r h3, u₄.other r h3, u₃.other r h2, u₂.other r h2, u₁.other r h1]
  have mem₆ : s₆.mem = s.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have rcx₆ : s₆.gpr .rcx = BitVec.ofNat 64 ((dl s₀ - c) % 16) := by
    rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.gpr,
      u₁.other _ (by decide), h.r12, and15, toNat_ofNat_lt (by omega_using [hdl])]
  have hm : (dl s₀ - c) % 16 ≤ dl s₀ - c := Nat.mod_le _ _
  have e : dl s₀ - c - (dl s₀ - c) % 16 = 16 * ((dl s₀ - c) / 16) := by
    have := Nat.div_add_mod (dl s₀ - c) 16; omega_using [this]
  have hle : c + 16 * ((dl s₀ - c) / 16) ≤ dl s₀ := blk_le hc
  exact {
    rdi := by
      rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
        u₂.other _ (by decide), u₁.gpr]; exact h.rbx
    rsi := by
      have r12₃ : s₃.gpr .r12 = BitVec.ofNat 64 (dl s₀ - c) := by
        rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.r12]
      have rcx₄ : s₄.gpr .rcx = BitVec.ofNat 64 ((dl s₀ - c) % 16) := by
        rw [u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₁.other _ (by decide), h.r12, and15,
          toNat_ofNat_lt (by omega_using [hdl])]
      have rbp₅ : s₅.gpr .rbp = dp s₀ + BitVec.ofNat 64 c := by
        rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
          u₁.other _ (by decide), h.rbp]
      rw [u₆.gpr, u₅.gpr, u₄.gpr, r12₃, rcx₄, rbp₅, sub_ofNat hm, e, BitVec.add_comm, BitVec.add_assoc,
        ← BitVec.ofNat_add]
    rcx := by
      rw [rcx₆]; congr 1
      have := Nat.div_add_mod (dl s₀ - c) 16; omega_using [this, hc]
    d_le := hle
    lt := by have := Nat.div_add_mod (dl s₀ - c) 16; have := Nat.mod_lt (dl s₀ - c) (show 16 > 0 by decide)
             omega_using [this, hc]
    r15 := by rw [g _ (by decide) (by decide) (by decide)]; exact h.r15
    rsp := by rw [g _ (by decide) (by decide) (by decide)]; exact h.rsp
    rd := by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]; exact h.rd
    wr := by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact h.wr
    frame := by rw [mem₆]; exact h.frame
    saved := by rw [mem₆]; exact h.saved
    st := by rw [mem₆]; exact h.st }

/-- When all the data is consumed. -/
structure Fin (s₀ : State) (s : State) : Prop where
  r15 : s.gpr .r15 = scr s₀
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [sR (st s₀), scR s₀, stkR s₀] s₀.mem s.mem
  saved : SavedAt (scr s₀) s₀ s.mem
  st : StOk s₀ (dl s₀) s.mem

theorem Res.srcOk {s₀ : State} (hp : UPre s₀) {d : Nat} {s : State} (h : Res s₀ d s) :
    SrcOk s s₀.mem (dp s₀ + BitVec.ofNat 64 d) (dl s₀ - d) := by
  intro i hi
  have hdl := dl_lt s₀
  have hd := h.d_le
  have e : dp s₀ + BitVec.ofNat 64 d + BitVec.ofNat 64 i = dp s₀ + BitVec.ofNat 64 (d + i) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  rw [e]
  have hc : (dR s₀).Contains (dp s₀ + BitVec.ofNat 64 (d + i)) 1 := dR_contains s₀ (by omega_using [hi, hd])
  refine ⟨⟨dR s₀, by rw [h.rd, hp.rd]; exact List.mem_append_left _ (List.mem_singleton_self _), hc⟩,
    fun hb => ?_, ?_⟩
  · rw [h.rdi] at hb
    exact hp.d_st _ hc (bfR_sub_sR _ _ hb)
  · refine h.frame.bytes (R := dR s₀) (fun r hr => ?_) (show dl s₀ ≤ 2 ^ 64 by omega_using [hdl])
      (show d + i < dl s₀ by omega_using [hi, hd])
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.d_st
    · exact hp.d_sc
    · exact hp.stk_d.symm

theorem Res.flags {s₀ : State} {d : Nat} {s s' : State} (h : Res s₀ d s) (hf : FlagsOnly s s') :
    Res s₀ d s' :=
  { rdi := by rw [hf.1]; exact h.rdi, rsi := by rw [hf.1]; exact h.rsi, rcx := by rw [hf.1]; exact h.rcx
    d_le := h.d_le, lt := h.lt, r15 := by rw [hf.1]; exact h.r15, rsp := by rw [hf.1]; exact h.rsp
    rd := by rw [hf.2.2.1]; exact h.rd, wr := by rw [hf.2.2.2]; exact h.wr
    frame := by rw [hf.2.1]; exact h.frame, saved := by rw [hf.2.1]; exact h.saved
    st := by rw [hf.2.1]; exact h.st }

theorem rest_ok {s₀ : State} (hp : UPre s₀) {d : Nat} {s : State} (h : Res s₀ d s) :
    WP isa rest s (Fin s₀) := by
  have hdl := dl_lt s₀
  have hd := h.d_le
  refine WP.seq (wp_test fun s₁ g₁ m₁ rd₁ wr₁ z₁ => WP.block_nil ?_)
  have h₁ := h.flags ⟨g₁, m₁, rd₁, wr₁⟩
  refine WP.ite (s.gpr .rcx &&& s.gpr .rcx == 0) (by simp only [eval, z₁]) (fun hb => ?_) (fun hb => ?_)
  · rw [BitVec.and_self, h.rcx, ofNat_beq_zero (by omega_using [hdl])] at hb
    simp only [decide_eq_true_eq] at hb
    have e : d = dl s₀ := by omega_using [hb, hd]
    subst e
    exact WP.block_nil ⟨h₁.r15, h₁.rsp, h₁.rd, h₁.wr, h₁.frame, h₁.saved, h₁.st⟩
  · rw [BitVec.and_self, h.rcx, ofNat_beq_zero (by omega_using [hdl])] at hb
    simp only [decide_eq_false_iff_not] at hb
    refine WP.seq (wp_mov32i fun s₂ u₂ => wp_mov fun s₃ u₃ => WP.block_nil ?_)
    have hg : ∀ r, r ≠ .rax → r ≠ .r12 → s₃.gpr r = s₁.gpr r := fun r h1 h2 => by
      rw [u₃.other r h1, u₂.other r h2]
    have hm₃ : s₃.mem = s₁.mem := by rw [u₃.mem, u₂.mem]
    have hrd₃ : s₃.rd = s₁.rd := by rw [u₃.rd, u₂.rd]
    have hwr₃ : s₃.wr = s₁.wr := by rw [u₃.wr, u₂.wr]
    have h₃ : Res s₀ d s₃ :=
      { rdi := by rw [hg _ (by decide) (by decide)]; exact h₁.rdi
        rsi := by rw [hg _ (by decide) (by decide)]; exact h₁.rsi
        rcx := by rw [hg _ (by decide) (by decide)]; exact h₁.rcx
        d_le := hd, lt := h.lt
        r15 := by rw [hg _ (by decide) (by decide)]; exact h₁.r15
        rsp := by rw [hg _ (by decide) (by decide)]; exact h₁.rsp
        rd := by rw [hrd₃]; exact h₁.rd, wr := by rw [hwr₃]; exact h₁.wr
        frame := by rw [hm₃]; exact h₁.frame, saved := by rw [hm₃]; exact h₁.saved
        st := by rw [hm₃]; exact h₁.st }
    have hw : sR (s₃.gpr .rdi) ∈ s₃.wr := by rw [h₃.wr, h₃.rdi]; exact hp.st_in
    refine WP.mono (copy_ok (j0 := 0) (n := dl s₀ - d) (by omega_using [h.lt]) (by omega_using [hb]) hw
      (h₃.srcOk hp) h₃.rsi (by rw [u₃.other _ (by decide), u₂.gpr]; rfl)
      (by rw [u₃.gpr, u₂.other _ (by decide), h₁.rcx])) fun s' hcp => ?_
    have hk : ∀ r, r ≠ .rsi → r ≠ .r12 → r ≠ .rax → r ≠ .r13 → s'.gpr r = s₃.gpr r := hcp.keep
    have hf : Frame [bfR (st s₀)] s₃.mem s'.mem := by rw [← h₃.rdi]; exact hcp.frame (by omega_using [h.lt])
    obtain ⟨X, Y, hX, hY, hXY, hYd, _, hrep⟩ := h₃.st
    have hY0 : Y = [] := hYd.resolve_right (by omega_using [hb])
    subst hY0
    have hlen : (bytesAt s₀.mem (dp s₀ + BitVec.ofNat 64 d) (dl s₀ - d)).length = dl s₀ - d :=
      Poly1305.length_bytesAt _ _ _
    refine { r15 := by rw [hk _ (by decide) (by decide) (by decide) (by decide)]; exact h₃.r15
             rsp := by rw [hk _ (by decide) (by decide) (by decide) (by decide)]; exact h₃.rsp
             rd := hcp.rd.trans h₃.rd
             wr := hcp.wr.trans h₃.wr
             frame := h₃.frame.trans (hf.sub fun r hr => by
               simp only [List.mem_singleton] at hr; subst hr
               exact ⟨_, List.mem_cons_self, bfR_sub_sR _⟩)
             saved := h₃.saved.frame hf (fun r hr => by
               simp only [List.mem_singleton] at hr; subst hr
               exact hp.st_sc.symm.sub_right (bfR_sub_sR _))
             st := ⟨X, bytesAt s₀.mem (dp s₀ + BitVec.ofNat 64 d) (dl s₀ - d), hX,
               by omega_using [hlen, h.lt], ?_, .inr rfl, ?_, fun key W hr => ?_⟩ }
    · rw [List.append_nil] at hXY
      rw [Dt, show dl s₀ = d + (dl s₀ - d) by omega_using [hd], Poly1305.bytesAt_add, ← List.append_assoc,
        ← Dt, hXY, show d + (dl s₀ - d) - d = dl s₀ - d by omega_using [hd]]
    · have hb' := hcp.buf (by omega_using [h.lt])
      rw [h₃.rdi, Nat.zero_add] at hb'
      rw [hlen, hb']
      rfl
    · refine repr_frame hf (fun r hr' => ?_) (hrep key W hr)
      simp only [List.mem_singleton] at hr'; subst hr'
      exact rpR_bfR _

/-! ## Restoring the registers -/

set_option simprocs false in
theorem restoreS_ok (s : State) (hin : ∀ d, d + 8 ≤ 128 → InRegions (s.rd ++ s.wr) (off (s.gpr .r15) d) 8) :
    WP isa (.block restoreS) s fun s' =>
      s'.mem = s.mem ∧ s'.gpr .rbx = s.mem.readW (off (s.gpr .r15) 0) 64 ∧
      s'.gpr .rbp = s.mem.readW (off (s.gpr .r15) 8) 64 ∧ s'.gpr .r12 = s.mem.readW (off (s.gpr .r15) 16) 64 ∧
      s'.gpr .r13 = s.mem.readW (off (s.gpr .r15) 24) 64 ∧ s'.gpr .r14 = s.mem.readW (off (s.gpr .r15) 32) 64 ∧
      s'.gpr .r15 = s.mem.readW (off (s.gpr .r15) 40) 64 ∧ s'.gpr .rsp = s.gpr .rsp := by
  have i0 := hin 0 (by decide); have i1 := hin 8 (by decide); have i2 := hin 16 (by decide)
  have i3 := hin 24 (by decide); have i4 := hin 32 (by decide); have i5 := hin 40 (by decide)
  simp only [off] at i0 i1 i2 i3 i4 i5
  apply WP.of_runBlock
  rw [restoreS_eq]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, ea_at,
    readSrc, State.load64, State.setReg, i0, i1, i2, i3, i4, i5,
    ite_true, ite_false, Option.map_some, Option.some.injEq, exists_eq_left', and_self]

theorem ret_stkR (s₀ : State) : (retR s₀).Disjoint (stkR s₀) := by
  have := Offset.disjoint_base (s₀.gpr .rsp - BitVec.ofNat 64 24) (d := 24) (n := 8) (k := 24)
    (by decide) (by decide)
  rwa [BitVec.sub_add_cancel] at this

theorem fin_ok {s₀ : State} (hp : UPre s₀) {s : State} (h : Fin s₀ s) :
    WP isa (.block restoreS) s fun s' => gprPreserved s₀ s' ∧ Proof.Poly1305.updateX86_64.post s₀ s' := by
  refine WP.mono (restoreS_ok s fun d hd => ⟨scR s₀, by rw [h.rd, h.wr, hp.wr]; simp,
    by rw [h.r15]; exact contains_off hd (by omega_using [hd])⟩) fun s' ⟨m', g1, g2, g3, g4, g5, g6, g7⟩ => ?_
  obtain ⟨sv1, sv2, sv3, sv4, sv5, sv6⟩ := h.saved
  rw [h.r15] at g1 g2 g3 g4 g5 g6
  refine ⟨⟨fun r hr => ?_, ?_⟩, fun key msg hbuf hcnt => ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [g1, sv1]
    · rw [g2, sv2]
    · rw [g7, h.rsp]
    · rw [g3, sv3]
    · rw [g4, sv4]
    · rw [g5, sv5]
    · rw [g6, sv6]
  · rw [m']
    refine h.frame.readW (Region.contains_self _ _) ?_ (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact hp.ret_st
    · exact hp.ret_sc
    · exact ret_stkR s₀
  · obtain ⟨W, B, rfl, hrep, hBl, hBb⟩ := Buffered.split hbuf
    have hk : kb s₀ = (W ++ B).length % 16 := hcnt
    have hBf : Bf s₀ = B := by rw [Bf, hk, off_56, hBb]
    obtain ⟨X, Y, hX, hY, hXY, _, hbufY, hrepX⟩ := h.st
    have hr := hrepX key W hrep
    change Buffered s'.mem (st s₀) key (W ++ B ++ Dt s₀ (dl s₀))
    rw [List.append_assoc, ← hBf, hXY, ← List.append_assoc, m']
    exact Buffered.of hr hY (by rw [← off_56]; exact hbufY)

theorem updatePost_ok {s₀ : State} (hp : UPre s₀) {c : Nat} {s : State} (h : After s₀ c s) :
    WP isa updatePost s fun s' => gprPreserved s₀ s' ∧ Proof.Poly1305.updateX86_64.post s₀ s' :=
  WP.seq (WP.mono (resume_ok h) fun _ h₁ => WP.seq (WP.mono (rest_ok hp h₁) fun _ h₂ => fin_ok hp h₂))

/-! ## The whole function -/

theorem update_correct (v : BlocksImpl) {s₀ : State} (hp : UPre s₀) :
    WP isa (update v.name v.code) s₀ fun s' =>
      abiPreserved s₀ s' ∧ Proof.Poly1305.updateX86_64.post s₀ s' := by
  refine WP.seq (WP.mono_mx (by lit_decide) (updatePre_ok hp) fun s₁ ⟨c, h₁⟩ mx₁ => ?_)
  refine WP.seq (WP.mono (Q := fun s : State => After s₀ c s ∧ s.mxcsr.extractLsb' 6 10 = s₀.mxcsr.extractLsb' 6 10)
    ?_ fun s₂ ⟨h₂, mx₂⟩ => ?_)
  · refine WP.ite (decide (dl s₀ - c < 16)) (by simp only [eval, h₁.cf]) (fun hb => ?_) (fun hb => ?_)
    · simp only [decide_eq_true_eq] at hb
      exact WP.block_nil ⟨h₁.after hb, by rw [mx₁]⟩
    · simp only [decide_eq_false_iff_not, Nat.not_lt] at hb
      exact WP.mono (call_ok v hp h₁ hb) fun s' ⟨ha, _, mx'⟩ => ⟨ha, by rw [mx', mx₁]⟩
  · exact WP.mono_mx (by lit_decide) (updatePost_ok hp h₂) fun s₃ ⟨hg, hpost⟩ mx₃ =>
      ⟨⟨hg.1, hg.2, by rw [mx₃]; exact mx₂⟩, hpost⟩

theorem update_ok (v : BlocksImpl) (s : State) (hs : Proof.Poly1305.updateX86_64.pre s) :
    ∃ t s', Exec isa (update v.name v.code) s t s' ∧ abiPreserved s s' ∧
      Proof.Poly1305.updateX86_64.post s s' :=
  update_correct v (UPre.of s hs)

end VG.Proof.Poly1305.X86_64
