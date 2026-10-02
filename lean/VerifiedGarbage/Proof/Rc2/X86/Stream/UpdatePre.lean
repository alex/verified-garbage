import VerifiedGarbage.Proof.Rc2.X86.Stream.Contract

/-!
# Streaming RC2-CBC on x86 (32-bit): the update functions' precondition

Names for the arguments and regions of an update (`Pre`), and what holds from
the saving of our caller's registers on (`Common`): the arguments are never
written, so they can be read at any point (`wp_arg`).
-/

namespace VG.Proof.Rc2.X86.Stream.Update

open VG VG.X86 VG.X86.Wp

theorem ofNat_toNat (x : BitVec 32) : BitVec.ofNat 32 x.toNat = x := by simp

section
variable (s₀ : State)

abbrev E : BitVec 32 := s₀.gpr .esp
abbrev ctx : BitVec 32 := arg s₀ 0
abbrev p : Nat := (arg s₀ 1).toNat
abbrev dp : BitVec 32 := arg s₀ 2
abbrev len : Nat := (arg s₀ 3).toNat
abbrev op : BitVec 32 := arg s₀ 4
abbrev O : Nat := (arg s₀ 5).toNat
abbrev scr : BitVec 32 := arg s₀ 6
abbrev cA : Addr := (ctx s₀).setWidth 64
abbrev dA : Addr := (dp s₀).setWidth 64
abbrev oA : Addr := (op s₀).setWidth 64
abbrev sA : Addr := (scr s₀).setWidth 64
abbrev ctxR : Region := ⟨cA s₀, 144⟩
abbrev dR : Region := ⟨dA s₀, len s₀⟩
abbrev oR : Region := ⟨oA s₀, O s₀⟩
abbrev scR : Region := ⟨sA s₀, 576⟩
abbrev argR : Region := ⟨argAddr s₀ 0, 28⟩
abbrev retR : Region := ⟨(E s₀).setWidth 64, 4⟩
abbrev stkR : Region := below (E s₀) 40
/-- The pending block. -/
abbrev pendR : Region := ⟨cA s₀ + BitVec.ofNat 64 136, 8⟩
/-- The schedule and the chaining value. -/
abbrev schR : Region := ⟨cA s₀, 128⟩
abbrev ivR : Region := ⟨cA s₀ + BitVec.ofNat 64 128, 8⟩

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [dR s₀, argR s₀]
  wr : s₀.wr = [ctxR s₀, oR s₀, scR s₀]
  c_d : (ctxR s₀).Disjoint (dR s₀)
  c_o : (ctxR s₀).Disjoint (oR s₀)
  c_s : (ctxR s₀).Disjoint (scR s₀)
  d_o : (dR s₀).Disjoint (oR s₀)
  d_s : (dR s₀).Disjoint (scR s₀)
  o_s : (oR s₀).Disjoint (scR s₀)
  a_c : (argR s₀).Disjoint (ctxR s₀)
  a_o : (argR s₀).Disjoint (oR s₀)
  a_s : (argR s₀).Disjoint (scR s₀)
  r_c : (retR s₀).Disjoint (ctxR s₀)
  r_o : (retR s₀).Disjoint (oR s₀)
  r_s : (retR s₀).Disjoint (scR s₀)
  k_c : (stkR s₀).Disjoint (ctxR s₀)
  k_d : (stkR s₀).Disjoint (dR s₀)
  k_o : (stkR s₀).Disjoint (oR s₀)
  k_s : (stkR s₀).Disjoint (scR s₀)
  c_fit : (ctx s₀).toNat + 144 ≤ 2 ^ 32
  d_fit : (dp s₀).toNat + len s₀ ≤ 2 ^ 32
  o_fit : (op s₀).toNat + O s₀ ≤ 2 ^ 32
  s_fit : (scr s₀).toNat + 576 ≤ 2 ^ 32
  sp_lo : 40 ≤ (E s₀).toNat
  sp_fit : (E s₀).toNat + 32 ≤ 2 ^ 32
  p_lt : p s₀ < 8
  O_eq : O s₀ = (p s₀ + len s₀) / 8 * 8

theorem pre_of {d : Spec.Rc2.Direction} {s₀ : State} (h : (updateContract d).pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20,
    h21, h22, h23, h24, h25, h26⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20,
    h21, h22, h23, h24, h25, h26⟩

namespace Pre
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem argAddr_eq (i : Nat) (hi : i < 7) :
    addr (E s₀) (4 + 4 * i) = (E s₀).setWidth 64 + BitVec.ofNat 64 (4 + 4 * i) := by
  have := hp.sp_fit; exact addr_eq (by omega)

theorem arg_sub {i : Nat} (hi : i < 7) : Region.Sub ⟨addr (E s₀) (4 + 4 * i), 4⟩ (argR s₀) := by
  show Region.Sub _ ⟨addr (E s₀) (4 + 4 * 0), 28⟩
  rw [hp.argAddr_eq i hi, hp.argAddr_eq 0 (by decide)]
  exact Offset.sub _ (by omega) (by omega)

omit hp in
theorem pend_sub : Region.Sub (pendR s₀) (ctxR s₀) := Offset.sub_base _ (by decide)
omit hp in
theorem sch_sub : Region.Sub (schR s₀) (ctxR s₀) := Region.sub_prefix (by decide)
omit hp in
theorem iv_sub : Region.Sub (ivR s₀) (ctxR s₀) := Offset.sub_base _ (by decide)

omit hp in
theorem sch_pend : (schR s₀).Disjoint (pendR s₀) := Offset.base_disjoint _ (by decide) (by decide)
omit hp in
theorem iv_pend : (ivR s₀).Disjoint (pendR s₀) := Offset.disjoint _ (by decide) (by decide) (by decide)
omit hp in
theorem sch_iv : (schR s₀).Disjoint (ivR s₀) := Offset.base_disjoint _ (by decide) (by decide)

/-- A word of the scratch space. -/
theorem scr_addr {d : Nat} (hd : d + 4 ≤ 576) : addr (scr s₀) d = sA s₀ + BitVec.ofNat 64 d := by
  have := hp.s_fit; exact addr_eq (by omega)

theorem scr_sub {d : Nat} (hd : d + 4 ≤ 576) : Region.Sub ⟨addr (scr s₀) d, 4⟩ (scR s₀) := by
  rw [hp.scr_addr hd]; exact Offset.sub_base _ hd

theorem sin {s : State} (hwr : s.wr = s₀.wr) {d : Nat} (hd : d + 4 ≤ 576) :
    InRegions s.wr (addr (scr s₀) d) 4 :=
  ⟨scR s₀, by simp [hwr, hp.wr], by rw [hp.scr_addr hd]; exact Offset.contains_base _ hd (by omega)⟩

theorem rin {s : State} (hrd : s.rd = s₀.rd) {i : Nat} (hi : i < 7) :
    InRegions (s.rd ++ s.wr) (addr (E s₀) (4 + 4 * i)) 4 := by
  refine ⟨argR s₀, by simp [hrd, hp.rd], ?_⟩
  show (⟨addr (E s₀) (4 + 4 * 0), 28⟩ : Region).Contains _ _
  rw [hp.argAddr_eq i hi, hp.argAddr_eq 0 (by decide)]
  exact Offset.contains _ (by omega) (by omega) (by have := hp.sp_fit; omega)

/-- The regions written are disjoint from the arguments, the saved words, the
schedule and the chaining value. -/
theorem sep_pend : ∀ r ∈ [argR s₀, scR s₀, schR s₀, ivR s₀, dR s₀, oR s₀, retR s₀, stkR s₀],
    r.Disjoint (pendR s₀) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  · exact hp.a_c.sub_right Pre.pend_sub
  · exact (hp.c_s.sub_left Pre.pend_sub).symm
  · exact Pre.sch_pend
  · exact Pre.iv_pend
  · exact (hp.c_d.sub_left Pre.pend_sub).symm
  · exact (hp.c_o.sub_left Pre.pend_sub).symm
  · exact hp.r_c.sub_right Pre.pend_sub
  · exact hp.k_c.sub_right Pre.pend_sub

end Pre

/-! ## From the saving of our caller's registers on -/

structure Common (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  esp : s.gpr .esp = E s₀
  edi : s.gpr .edi = s₀.gpr .edi
  ebp : s.gpr .ebp = s₀.gpr .ebp
  frame : Frame [pendR s₀, oR s₀, scR s₀] s₀.mem s.mem
  ebx : s.mem.readW (addr (scr s₀) 512) 32 = s₀.gpr .ebx
  esi : s.mem.readW (addr (scr s₀) 516) 32 = s₀.gpr .esi

theorem Common.arg {s₀ s : State} (hp : Pre s₀) (h : Common s₀ s) {i : Nat} (hi : i < 7) :
    s.mem.readW (addr (E s₀) (4 + 4 * i)) 32 = arg s₀ i := by
  have hs := hp.arg_sub hi
  refine (h.frame.readW (Region.contains_self _ _) ?_ (by decide)).trans rfl
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact ((hp.sep_pend _ (by simp)).sub_left hs)
  · exact hp.a_o.sub_left hs
  · exact hp.a_s.sub_left hs

/-- `mov d, [esp + 4 + 4i]`: argument `i`. -/
theorem wp_arg {s₀ s : State} (hp : Pre s₀) (h : Common s₀ s) {i : Nat} (hi : i < 7) {d : Reg}
    {is : List Instr} {Q : State → Prop}
    (k : ∀ s', Upd s s' d (arg s₀ i) → WP isa (.block is) s' Q) :
    WP isa (.block (.mov d (.mem (Impl.Rc2.X86.Stream.argOp i)) :: is)) s Q :=
  wp_ldm (b := .esp) (o := 4 + 4 * i) h.esp (hp.rin h.rd hi) fun s' u => k s' (h.arg hp hi ▸ u)

/-- `Common` after writing within the pending block or `out`. -/
theorem Common.write {s₀ s s' : State} (hp : Pre s₀) (h : Common s₀ s) {r : Region}
    (hr : Region.Sub r (pendR s₀) ∨ Region.Sub r (oR s₀)) (f : Frame [r] s.mem s'.mem)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hesp : s'.gpr .esp = s.gpr .esp)
    (hedi : s'.gpr .edi = s.gpr .edi) (hebp : s'.gpr .ebp = s.gpr .ebp) : Common s₀ s' := by
  have sd : ∀ {e : Nat}, e + 4 ≤ 576 → r.Disjoint ⟨addr (scr s₀) e, 4⟩ := fun he => by
    rcases hr with hr | hr
    · exact ((hp.c_s.sub_left Pre.pend_sub).sub_left hr).sub_right (hp.scr_sub he)
    · exact (hp.o_s.sub_left hr).sub_right (hp.scr_sub he)
  refine ⟨hrd.trans h.rd, hwr.trans h.wr, hesp.trans h.esp, hedi.trans h.edi, hebp.trans h.ebp,
    h.frame.trans (f.sub ?_), ?_, ?_⟩
  · intro r' hr'
    simp only [List.mem_singleton] at hr'; subst hr'
    rcases hr with hr | hr
    · exact ⟨_, by simp, hr⟩
    · exact ⟨_, by simp, hr⟩
  · rw [f.readW (Region.contains_self _ _) (fun r' hr' => by
      simp only [List.mem_singleton] at hr'; subst hr'; exact (sd (by decide)).symm) (by decide)]
    exact h.ebx
  · rw [f.readW (Region.contains_self _ _) (fun r' hr' => by
      simp only [List.mem_singleton] at hr'; subst hr'; exact (sd (by decide)).symm) (by decide)]
    exact h.esi

end VG.Proof.Rc2.X86.Stream.Update
