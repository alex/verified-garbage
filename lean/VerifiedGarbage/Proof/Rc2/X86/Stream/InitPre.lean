import VerifiedGarbage.Proof.Rc2.X86.Stream.Contract
import VerifiedGarbage.Proof.Rc2.PairMem
import VerifiedGarbage.Proof.Rc2.CbcMemory

/-!
# Streaming RC2-CBC on x86 (32-bit): `init` before the call

Names for the arguments and regions of `init` (`Pre`), the length checks
(`checks_ok`), and the copy of the IV and the arguments of the key expansion
(`initArgs_ok`).
-/

namespace VG.Proof.Rc2.X86.Stream.Init

open VG VG.X86 VG.X86.Wp VG.Impl.Rc2.X86.Stream

theorem ofNat_toNat (x : BitVec 32) : BitVec.ofNat 32 x.toNat = x := by simp

section
variable (s₀ : State)

abbrev E : BitVec 32 := s₀.gpr .esp
abbrev key : BitVec 32 := arg s₀ 0
abbrev kl : Nat := (arg s₀ 1).toNat
abbrev eb : Nat := (arg s₀ 2).toNat
abbrev iv : BitVec 32 := arg s₀ 3
abbrev il : Nat := (arg s₀ 4).toNat
abbrev ctx : BitVec 32 := arg s₀ 5
abbrev scr : BitVec 32 := arg s₀ 6
abbrev kA : Addr := (key s₀).setWidth 64
abbrev ivA : Addr := (iv s₀).setWidth 64
abbrev cA : Addr := (ctx s₀).setWidth 64
abbrev sA : Addr := (scr s₀).setWidth 64
abbrev keyR : Region := ⟨kA s₀, kl s₀⟩
abbrev ivR : Region := ⟨ivA s₀, il s₀⟩
abbrev ctxR : Region := ⟨cA s₀, 144⟩
abbrev scR : Region := ⟨sA s₀, 576⟩
abbrev argR : Region := ⟨argAddr s₀ 0, 28⟩
abbrev retR : Region := ⟨(E s₀).setWidth 64, 4⟩
abbrev stkR : Region := below (E s₀) 24
/-- Where the chaining value goes. -/
abbrev cvR : Region := ⟨cA s₀ + BitVec.ofNat 64 128, 8⟩
abbrev schR : Region := ⟨cA s₀, 128⟩

/-- The value `init` returns. -/
def code : Nat :=
  if ¬(1 ≤ kl s₀ ∧ kl s₀ ≤ 128) then 1 else if ¬(1 ≤ eb s₀ ∧ eb s₀ ≤ 1024) then 2
  else if il s₀ ≠ 8 then 3 else 0

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [keyR s₀, ivR s₀, argR s₀]
  wr : s₀.wr = [ctxR s₀, scR s₀]
  k_c : (keyR s₀).Disjoint (ctxR s₀)
  k_s : (keyR s₀).Disjoint (scR s₀)
  i_c : (ivR s₀).Disjoint (ctxR s₀)
  i_s : (ivR s₀).Disjoint (scR s₀)
  c_s : (ctxR s₀).Disjoint (scR s₀)
  a_c : (argR s₀).Disjoint (ctxR s₀)
  a_s : (argR s₀).Disjoint (scR s₀)
  r_c : (retR s₀).Disjoint (ctxR s₀)
  r_s : (retR s₀).Disjoint (scR s₀)
  t_k : (stkR s₀).Disjoint (keyR s₀)
  t_i : (stkR s₀).Disjoint (ivR s₀)
  t_c : (stkR s₀).Disjoint (ctxR s₀)
  t_s : (stkR s₀).Disjoint (scR s₀)
  k_fit : (key s₀).toNat + kl s₀ ≤ 2 ^ 32
  i_fit : (iv s₀).toNat + il s₀ ≤ 2 ^ 32
  c_fit : (ctx s₀).toNat + 144 ≤ 2 ^ 32
  s_fit : (scr s₀).toNat + 576 ≤ 2 ^ 32
  sp_lo : 24 ≤ (E s₀).toNat
  sp_fit : (E s₀).toNat + 32 ≤ 2 ^ 32

theorem pre_of {s₀ : State} (h : initContract.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20,
    h21⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21⟩

theorem cv_sub {s₀ : State} : Region.Sub (cvR s₀) (ctxR s₀) := Offset.sub_base _ (by decide)
theorem sch_sub {s₀ : State} : Region.Sub (schR s₀) (ctxR s₀) := Region.sub_prefix (by decide)
theorem sch_cv {s₀ : State} : (schR s₀).Disjoint (cvR s₀) := Offset.base_disjoint _ (by decide) (by decide)

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

theorem rin {s : State} (hrd : s.rd = s₀.rd) {i : Nat} (hi : i < 7) :
    InRegions (s.rd ++ s.wr) (addr (E s₀) (4 + 4 * i)) 4 := by
  refine ⟨argR s₀, by simp [hrd, hp.rd], ?_⟩
  show (⟨addr (E s₀) (4 + 4 * 0), 28⟩ : Region).Contains _ _
  rw [hp.argAddr_eq i hi, hp.argAddr_eq 0 (by decide)]
  exact Offset.contains _ (by omega) (by omega) (by have := hp.sp_fit; omega)

theorem scr_addr {d : Nat} (hd : d + 4 ≤ 576) : addr (scr s₀) d = sA s₀ + BitVec.ofNat 64 d := by
  have := hp.s_fit; exact addr_eq (by omega)

theorem scr_sub {d : Nat} (hd : d + 4 ≤ 576) : Region.Sub ⟨addr (scr s₀) d, 4⟩ (scR s₀) := by
  rw [hp.scr_addr hd]; exact Offset.sub_base _ hd

theorem ctx_addr {d : Nat} (hd : d + 4 ≤ 144) : addr (ctx s₀) d = cA s₀ + BitVec.ofNat 64 d := by
  have := hp.c_fit; exact addr_eq (by omega)

end Pre

/-- What holds before the call. -/
structure Common (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  esp : s.gpr .esp = E s₀
  edi : s.gpr .edi = s₀.gpr .edi
  ebp : s.gpr .ebp = s₀.gpr .ebp
  frame : Frame [cvR s₀, scR s₀] s₀.mem s.mem

theorem Common.refl (s₀ : State) : Common s₀ s₀ := ⟨rfl, rfl, rfl, rfl, rfl, Frame.refl _ _⟩

theorem Common.upd {s₀ s s' : State} (h : Common s₀ s) {d : Reg} {v : BitVec 32} (u : Upd s s' d v)
    (h₁ : d ≠ .esp) (h₂ : d ≠ .edi) (h₃ : d ≠ .ebp) : Common s₀ s' :=
  ⟨u.rd.trans h.rd, u.wr.trans h.wr, (u.other _ (Ne.symm h₁)).trans h.esp,
    (u.other _ (Ne.symm h₂)).trans h.edi, (u.other _ (Ne.symm h₃)).trans h.ebp,
    by rw [u.mem]; exact h.frame⟩

theorem Common.fupd {s₀ s s' : State} (h : Common s₀ s) (u : Fupd s s') : Common s₀ s' :=
  ⟨u.rd.trans h.rd, u.wr.trans h.wr, by rw [u.gpr]; exact h.esp, by rw [u.gpr]; exact h.edi,
    by rw [u.gpr]; exact h.ebp, by rw [u.mem]; exact h.frame⟩

theorem Common.arg {s₀ s : State} (hp : Pre s₀) (h : Common s₀ s) {i : Nat} (hi : i < 7) :
    s.mem.readW (addr (E s₀) (4 + 4 * i)) 32 = arg s₀ i := by
  have hs := hp.arg_sub hi
  refine (h.frame.readW (Region.contains_self _ _) ?_ (by decide)).trans rfl
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact (hp.a_c.sub_right cv_sub).sub_left hs
  · exact hp.a_s.sub_left hs

theorem wp_arg {s₀ s : State} (hp : Pre s₀) (h : Common s₀ s) {i : Nat} (hi : i < 7) {d : Reg}
    {is : List Instr} {Q : State → Prop}
    (k : ∀ s', Upd s s' d (arg s₀ i) → WP isa (.block is) s' Q) :
    WP isa (.block (.mov d (.mem (Impl.Rc2.X86.Stream.argOp i)) :: is)) s Q :=
  wp_ldm (b := .esp) (o := 4 + 4 * i) h.esp (hp.rin h.rd hi) fun s' u => k s' (h.arg hp hi ▸ u)

/-! ## The checks -/

theorem pred_lt (x : BitVec 32) {n : Nat} (hn : n < 2 ^ 32) :
    decide ((x - BitVec.ofNat 32 1).toNat < n) = decide (1 ≤ x.toNat ∧ x.toNat ≤ n) := by
  rw [decide_eq_decide, BitVec.toNat_sub, BitVec.toNat_ofNat]
  have := x.isLt
  omega

theorem checks_ok {s₀ : State} (hp : Pre s₀) {Q : State → Prop}
    (hQ : ∀ t, Common s₀ t → t.mem = s₀.mem → t.gpr .eax = BitVec.ofNat 32 (code s₀) →
      t.gpr .ebx = s₀.gpr .ebx → t.gpr .esi = s₀.gpr .esi → Q t) :
    WP isa checks s₀ Q := by
  have c₀ := Common.refl s₀
  rw [checks]
  refine WP.seq ?_
  refine wp_movi fun s₁ u₁ => ?_
  have c₁ := c₀.upd u₁ (by decide) (by decide) (by decide)
  refine wp_arg hp c₁ (i := 1) (by decide) fun s₂ u₂ => ?_
  have c₂ := c₁.upd u₂ (by decide) (by decide) (by decide)
  refine wp_subi fun s₃ u₃ _ _ => ?_
  have c₃ := c₂.upd u₃ (by decide) (by decide) (by decide)
  refine wp_cmpi fun s₄ f₄ cf₄ _ => WP.block_nil ?_
  have c₄ := c₃.fupd f₄
  have k₄ : decide (1 ≤ kl s₀ ∧ kl s₀ ≤ 128) = decide ((s₃.gpr .ecx).toNat < (128 : BitVec 32).toNat) := by
    rw [u₃.gpr, u₂.gpr]; exact (pred_lt _ (by decide)).symm
  have m₄ : s₄.mem = s₀.mem := by rw [f₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have g₄ (r : Reg) (h₁ : r ≠ .eax) (h₂ : r ≠ .ecx) : s₄.gpr r = s₀.gpr r := by
    rw [f₄.gpr, u₃.other _ h₂, u₂.other _ h₂, u₁.other _ h₁]
  have a₄ : s₄.gpr .eax = BitVec.ofNat 32 1 := by
    rw [f₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
  refine WP.ite (!decide (1 ≤ kl s₀ ∧ kl s₀ ≤ 128)) (by
    show s₄.cf.map (!·) = _; rw [cf₄, ← k₄]; rfl) (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · have hk : ¬(1 ≤ kl s₀ ∧ kl s₀ ≤ 128) := of_decide_eq_false (by revert hb; cases decide (1 ≤ kl s₀ ∧ kl s₀ ≤ 128) <;> simp)
    refine hQ s₄ c₄ m₄ (by rw [a₄, code, ite_eq_left_of_eq_true _ _ (eq_true hk)]) (g₄ _ (by decide) (by decide))
      (g₄ _ (by decide) (by decide))
  have hk : 1 ≤ kl s₀ ∧ kl s₀ ≤ 128 := of_decide_eq_true (by revert hb; cases decide (1 ≤ kl s₀ ∧ kl s₀ ≤ 128) <;> simp)
  -- `effective_bits`.
  refine WP.seq ?_
  refine wp_movi fun s₅ u₅ => ?_
  have c₅ := c₄.upd u₅ (by decide) (by decide) (by decide)
  refine wp_arg hp c₅ (i := 2) (by decide) fun s₆ u₆ => ?_
  have c₆ := c₅.upd u₆ (by decide) (by decide) (by decide)
  refine wp_subi fun s₇ u₇ _ _ => ?_
  have c₇ := c₆.upd u₇ (by decide) (by decide) (by decide)
  refine wp_cmpi fun s₈ f₈ cf₈ _ => WP.block_nil ?_
  have c₈ := c₇.fupd f₈
  have k₈ : decide (1 ≤ eb s₀ ∧ eb s₀ ≤ 1024) = decide ((s₇.gpr .ecx).toNat < (1024 : BitVec 32).toNat) := by
    rw [u₇.gpr, u₆.gpr]; exact (pred_lt _ (by decide)).symm
  have m₈ : s₈.mem = s₀.mem := by rw [f₈.mem, u₇.mem, u₆.mem, u₅.mem, m₄]
  have g₈ (r : Reg) (h₁ : r ≠ .eax) (h₂ : r ≠ .ecx) : s₈.gpr r = s₀.gpr r := by
    rw [f₈.gpr, u₇.other _ h₂, u₆.other _ h₂, u₅.other _ h₁, g₄ _ h₁ h₂]
  have a₈ : s₈.gpr .eax = BitVec.ofNat 32 2 := by
    rw [f₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr]
  refine WP.ite (!decide (1 ≤ eb s₀ ∧ eb s₀ ≤ 1024)) (by
    show s₈.cf.map (!·) = _; rw [cf₈, ← k₈]; rfl) (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · have he : ¬(1 ≤ eb s₀ ∧ eb s₀ ≤ 1024) := of_decide_eq_false (by revert hb; cases decide (1 ≤ eb s₀ ∧ eb s₀ ≤ 1024) <;> simp)
    refine hQ s₈ c₈ m₈ (by rw [a₈, code, ite_eq_right_of_eq_false _ _ (eq_false (not_not_intro hk)), ite_eq_left_of_eq_true _ _ (eq_true he)]) (g₈ _ (by decide) (by decide)) (g₈ _ (by decide) (by decide))
  have he : 1 ≤ eb s₀ ∧ eb s₀ ≤ 1024 := of_decide_eq_true (by revert hb; cases decide (1 ≤ eb s₀ ∧ eb s₀ ≤ 1024) <;> simp)
  -- `iv_len`.
  refine WP.seq ?_
  refine wp_movi fun s₉ u₉ => ?_
  have c₉ := c₈.upd u₉ (by decide) (by decide) (by decide)
  refine wp_arg hp c₉ (i := 4) (by decide) fun s₁₀ u₁₀ => ?_
  have c₁₀ := c₉.upd u₁₀ (by decide) (by decide) (by decide)
  refine wp_cmpi fun s₁₁ f₁₁ _ zf₁₁ => WP.block_nil ?_
  have c₁₁ := c₁₀.fupd f₁₁
  have m₁₁ : s₁₁.mem = s₀.mem := by rw [f₁₁.mem, u₁₀.mem, u₉.mem, m₈]
  have g₁₁ (r : Reg) (h₁ : r ≠ .eax) (h₂ : r ≠ .ecx) : s₁₁.gpr r = s₀.gpr r := by
    rw [f₁₁.gpr, u₁₀.other _ h₂, u₉.other _ h₁, g₈ _ h₁ h₂]
  have z : (s₁₀.gpr .ecx - 8 == 0) = decide (il s₀ = 8) := by
    rw [u₁₀.gpr, ← ofNat_toNat (arg s₀ 4)]
    exact sub_beq (arg s₀ 4).isLt (by decide)
  refine WP.ite (!decide (il s₀ = 8)) (by
    show s₁₁.zf.map (!·) = _; rw [zf₁₁, z]; rfl) (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · have hi : il s₀ ≠ 8 := of_decide_eq_false (by revert hb; cases decide (il s₀ = 8) <;> simp)
    refine hQ s₁₁ c₁₁ m₁₁ ?_ (g₁₁ _ (by decide) (by decide)) (g₁₁ _ (by decide) (by decide))
    rw [f₁₁.gpr, u₁₀.other _ (by decide), u₉.gpr]
    rw [code, ite_eq_right_of_eq_false _ _ (eq_false (not_not_intro hk)), ite_eq_right_of_eq_false _ _ (eq_false (not_not_intro he)), ite_eq_left_of_eq_true _ _ (eq_true hi)]
  · have hi : il s₀ = 8 := of_decide_eq_true (by revert hb; cases decide (il s₀ = 8) <;> simp)
    refine wp_movi fun s₁₂ u₁₂ => WP.block_nil ?_
    refine hQ s₁₂ (c₁₁.upd u₁₂ (by decide) (by decide) (by decide)) (by rw [u₁₂.mem, m₁₁]) ?_
      (by rw [u₁₂.other _ (by decide)]; exact g₁₁ _ (by decide) (by decide))
      (by rw [u₁₂.other _ (by decide)]; exact g₁₁ _ (by decide) (by decide))
    rw [u₁₂.gpr]
    rw [code, ite_eq_right_of_eq_false _ _ (eq_false (not_not_intro hk)), ite_eq_right_of_eq_false _ _ (eq_false (not_not_intro he)), ite_eq_right_of_eq_false _ _ (eq_false (not_not_intro hi))]

end VG.Proof.Rc2.X86.Stream.Init
