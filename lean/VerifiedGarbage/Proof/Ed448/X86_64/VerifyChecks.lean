import VerifiedGarbage.Proof.Ed448.X86_64.VerifyRoot
import VerifiedGarbage.Proof.Ed448.X86_64.ScalarWord
import VerifiedGarbage.Proof.Ed448.X86_64.ScalarIO
import VerifiedGarbage.Proof.X448.X86_64.Main

/-!
# Ed448 verification's equation on x86-64: the checks

Each check ORs into the word `BAD` of the working space a word that is 0
exactly when it passes: the equality of two field elements (`eqSlots_ok`, by
comparing their full reductions word by word), and `S < L` (`sCheck_ok`, by
the carry of `S + 2^448 - L` and its byte 56). `erun` runs a block
symbolically, keeping the register writes folded.
-/

namespace VG.Proof.Ed448.X86_64
open VG VG.X86_64 VG.Impl.Ed448.X86_64
open VG.Proof.X448.X86_64 (Scr word off Outside ofs writeW_outside word_writeW_self contains_sc)
open VG.Impl.X448.X86_64 (W w sc at_)

/-- Runs a block symbolically, keeping the register writes folded. -/
syntax "erun" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| erun) => `(tactic| erun [])
  | `(tactic| erun [$ls,*]) => `(tactic| (
      apply WP.of_runBlock
      set_option linter.unusedSimpArgs false in
      simp (config := { decide := true }) only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
        readSrc32, execAlu, execShift, State.setReg32, State.load64, State.load8, State.store64,
        State.store8, sc, VG.Proof.Ed448.X86_64.ea_at, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
        RegUpd.cf_setReg, RegUpd.zf_setReg, RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags,
        RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, RegUpd.cf_arithFlags, RegUpd.zf_arithFlags,
        RegUpd.gpr_setFlags, RegUpd.mem_setFlags, RegUpd.rd_setFlags, RegUpd.wr_setFlags,
        RegUpd.cf_setFlags, Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left',
        ite_true, ite_false, reduceCtorEq, true_and, and_true, $ls,*]))

theorem orBad_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block orBad) s fun t =>
      t.mem = s.mem.writeW (off base BAD) (word s.mem base BAD ||| s.gpr .rdx) ∧
      (∀ r, r ≠ .rax → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have rb : InRegions (s.rd ++ s.wr) (base + BitVec.ofNat 64 BAD) 8 := hs.read (by decide)
  have wb : InRegions s.wr (base + BitVec.ofNat 64 BAD) 8 := ⟨_, hs.wr, contains_sc (by decide)⟩
  erun [orBad, hs.rdi, rb, wb]
  exact fun r hr => by simp only [hr, ite_false]

theorem isZero_ok (s : State) :
    WP isa (.block isZero) s fun t =>
      t.gpr .rdx = (if s.gpr .rdx = 0 then 1 else 0) ∧ t.mem = s.mem ∧
      (∀ r, r ≠ .rdx → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  erun [isZero]
  refine ⟨?_, fun r hr => by simp only [hr, ite_false]⟩
  rw [show (BitVec.signExtend 64 (1 : BitVec 32)).toNat = 1 from rfl]
  by_cases h : s.gpr .rdx = 0
  · rw [h]; decide
  · have h' : ¬ (s.gpr .rdx).toNat < 1 := fun h' => h (BitVec.eq_of_toNat_eq (by
      show _ = 0; omega))
    rw [ite_eq_right h, decide_eq_false h']
    decide

theorem diff7 (f g : Nat → BitVec 64) :
    ((((((((0#64 ||| f 0 ^^^ g 0) ||| f 1 ^^^ g 1) ||| f 2 ^^^ g 2) ||| f 3 ^^^ g 3) |||
      f 4 ^^^ g 4) ||| f 5 ^^^ g 5) ||| f 6 ^^^ g 6) = 0#64) ↔ ∀ i < 7, f i = g i := by
  simp only [BitVec.or_eq_zero_iff, BitVec.xor_eq_zero_iff]
  constructor
  · intro h i hi
    match i, hi with
    | 0, _ => exact h.1.1.1.1.1.1.2
    | 1, _ => exact h.1.1.1.1.1.2
    | 2, _ => exact h.1.1.1.1.2
    | 3, _ => exact h.1.1.1.2
    | 4, _ => exact h.1.1.2
    | 5, _ => exact h.1.2
    | 6, _ => exact h.2
  · intro h
    exact ⟨⟨⟨⟨⟨⟨⟨trivial, h 0 (by decide)⟩, h 1 (by decide)⟩, h 2 (by decide)⟩, h 3 (by decide)⟩,
      h 4 (by decide)⟩, h 5 (by decide)⟩, h 6 (by decide)⟩

theorem diffWords_ok {s : State} {base : Addr} (hs : Scr s base) {o : Nat} (ho : o + 56 ≤ 8192) :
    WP isa (.block (diffWords o)) s fun t =>
      (t.gpr .rdx = 0 ↔ ∀ i < 7, word s.mem base (o + 8 * i) = s.gpr (w i)) ∧ t.mem = s.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rdx → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have r0 : InRegions (s.rd ++ s.wr) (base + BitVec.ofNat 64 (o + 8 * 0)) 8 := hs.read (by omega)
  have r1 : InRegions (s.rd ++ s.wr) (base + BitVec.ofNat 64 (o + 8 * 1)) 8 := hs.read (by omega)
  have r2 : InRegions (s.rd ++ s.wr) (base + BitVec.ofNat 64 (o + 8 * 2)) 8 := hs.read (by omega)
  have r3 : InRegions (s.rd ++ s.wr) (base + BitVec.ofNat 64 (o + 8 * 3)) 8 := hs.read (by omega)
  have r4 : InRegions (s.rd ++ s.wr) (base + BitVec.ofNat 64 (o + 8 * 4)) 8 := hs.read (by omega)
  have r5 : InRegions (s.rd ++ s.wr) (base + BitVec.ofNat 64 (o + 8 * 5)) 8 := hs.read (by omega)
  have r6 : InRegions (s.rd ++ s.wr) (base + BitVec.ofNat 64 (o + 8 * 6)) 8 := hs.read (by omega)
  erun [diffWords, List.range_succ, List.range_zero, List.nil_append, List.flatMap_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.cons_append, w, W, hs.rdi, r0, r1, r2, r3, r4,
    r5, r6]
  exact ⟨diff7 (fun i => word s.mem base (o + 8 * i)) (fun i => s.gpr (W.getD i .r8)),
    fun r h1 h2 => by simp only [h1, h2, ite_false]⟩

open VG.Proof.X448.X86_64 (rv mv fe E Index Keeps freeze_ok stores_ok val7 mv7 rvW slot_lt W_len)

theorem val7_inj {f g : Nat → Nat} (hf : ∀ i < 7, f i < 2 ^ 64) (hg : ∀ i < 7, g i < 2 ^ 64) :
    val7 f = val7 g ↔ ∀ i < 7, f i = g i := by
  constructor
  · intro h i hi
    have := hf 0 (by decide); have := hf 1 (by decide); have := hf 2 (by decide)
    have := hf 3 (by decide); have := hf 4 (by decide); have := hf 5 (by decide)
    have := hf 6 (by decide); have := hg 0 (by decide); have := hg 1 (by decide)
    have := hg 2 (by decide); have := hg 3 (by decide); have := hg 4 (by decide)
    have := hg 5 (by decide); have := hg 6 (by decide)
    simp only [val7] at h
    match i, hi with
    | 0, _ => omega
    | 1, _ => omega
    | 2, _ => omega
    | 3, _ => omega
    | 4, _ => omega
    | 5, _ => omega
    | 6, _ => omega
  · exact fun h => VG.Proof.X448.X86_64.val7_congr h

theorem toFe_eq_iff (x y : Nat) : VG.Proof.X448.toFe x = VG.Proof.X448.toFe y ↔ x % Spec.X448.P = y % Spec.X448.P := by
  constructor
  · intro h
    have := congrArg Fin.val h
    simpa [VG.Proof.X448.toFe_val] using this
  · intro h
    exact Fin.ext (by simpa [VG.Proof.X448.toFe_val] using h)

/-- Checks write only the words `[BAD, CAN + 56)` and the registers `rax`, `rdx`, `r15`, `W`. -/
structure CKeep (base : Addr) (s t : State) : Prop where
  gpr : ∀ r, r ∉ Reg.rax :: Reg.rdx :: Reg.r15 :: W → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mem : Outside base BAD 80 s.mem t.mem

theorem CKeep.trans {base : Addr} {s t u : State} (h₁ : CKeep base s t) (h₂ : CKeep base t u) :
    CKeep base s u :=
  ⟨fun r hr => (h₂.gpr r hr).trans (h₁.gpr r hr), h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr,
    h₁.mem.trans h₂.mem⟩

theorem CKeep.scr {base : Addr} {s t : State} (h : CKeep base s t) (hs : Scr s base) : Scr t base :=
  ⟨(h.gpr _ (by decide)).trans hs.rdi, h.wr ▸ hs.wr, hs.nowrap⟩

theorem E_bad {base : Addr} {m m' : Mem} (h : Outside base BAD 80 m m') : E m' base = E m base := by
  funext i
  have := slot_lt i
  simp only [VG.Impl.X448.X86_64.ACC] at this
  exact VG.Proof.X448.X86_64.E_outside h i (Or.inl (by simp only [BAD]; omega))

theorem CKeep.E {base : Addr} {s t : State} (h : CKeep base s t) : E t.mem base = E s.mem base :=
  E_bad h.mem

/-- `BAD |= c`, with `c = 0` exactly when slots `a` and `b` are the same field element. -/
theorem eqSlots_ok {s : State} {base : Addr} (hs : Scr s base) (a b : Index) :
    WP isa (.block (eqSlots a.val b.val)) s fun t =>
      ∃ c : BitVec 64, (c = 0 ↔ E s.mem base a = E s.mem base b) ∧
        word t.mem base BAD = word s.mem base BAD ||| c ∧ CKeep base s t ∧
        word t.mem base SIGN = word s.mem base SIGN := by
  have ha := slot_lt a; have hb := slot_lt b
  simp only [VG.Impl.X448.X86_64.ACC] at ha hb
  rw [eqSlots, WP.block_append_iff]
  refine WP.mono (freeze_ok hs (a := VG.Impl.X448.X86_64.slot a.val) ha) fun s1 ⟨v1, k1⟩ => ?_
  have hs1 := hs.of_keeps k1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (stores_ok hs1 CAN W (by rw [W_len]; decide)) fun s2 ⟨v2, o2, g2, rd2, wr2⟩ => ?_
  have hs2 : Scr s2 base := ⟨(g2 _).trans hs1.rdi, wr2 ▸ hs1.wr, hs1.nowrap⟩
  rw [WP.block_append_iff]
  refine WP.mono (freeze_ok hs2 (a := VG.Impl.X448.X86_64.slot b.val) hb) fun s3 ⟨v3, k3⟩ => ?_
  have hs3 := hs2.of_keeps k3 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (diffWords_ok hs3 (o := CAN) (by decide)) fun s4 ⟨d4, m4, g4, rd4, wr4⟩ => ?_
  have hs4 : Scr s4 base := ⟨(g4 _ (by decide) (by decide)).trans hs3.rdi, wr4 ▸ hs3.wr, hs3.nowrap⟩
  refine WP.mono (orBad_ok hs4) fun t ⟨mt, gt, rdt, wrt⟩ => ?_
  -- the memory: CAN written, then BAD.
  have O2 : Outside base BAD 80 s.mem s2.mem := by
    rw [← k1.2.1]; exact o2.mono (by decide) (by rw [W_len]; decide)
  have O4 : Outside base BAD 80 s.mem s4.mem := by rw [m4, k3.2.1]; exact O2
  have Ot : Outside base BAD 80 s.mem t.mem := by
    rw [mt]; exact O4.trans ((writeW_outside _ _ _ (by decide)).mono (by decide) (by decide))
  -- the slots are unchanged until the stores.
  have e2 : E s2.mem base = E s.mem base := E_bad O2
  refine ⟨s4.gpr .rdx, ?_, ?_, ?_, ?_⟩
  · rw [d4]
    have hA : mv s3.mem base CAN 7 = fe s.mem base (VG.Impl.X448.X86_64.slot a.val) % Spec.X448.P := by
      rw [k3.2.1, ← v1]; exact v2
    have hB : rv s3 W = fe s.mem base (VG.Impl.X448.X86_64.slot b.val) % Spec.X448.P := by
      rw [v3]; exact congrArg (· % Spec.X448.P) (O2.mv (Or.inl (by simp only [BAD]; omega)) (by omega))
    have key : (∀ i < 7, word s3.mem base (CAN + 8 * i) = s3.gpr (w i)) ↔
        mv s3.mem base CAN 7 = rv s3 W := by
      rw [mv7, rvW, val7_inj (fun i _ => BitVec.isLt _) (fun i _ => BitVec.isLt _)]
      constructor
      · intro h i hi; exact congrArg BitVec.toNat (h i hi)
      · intro h i hi; exact BitVec.eq_of_toNat_eq (h i hi)
    rw [key, hA, hB, ← toFe_eq_iff]
    rfl
  · rw [mt, word_writeW_self, m4, k3.2.1]
    have : word s2.mem base BAD = word s.mem base BAD := by
      rw [o2.word (by left; decide) (by decide), k1.2.1]
    rw [this]
  · refine ⟨fun r hr => ?_, by rw [rdt, rd4, k3.2.2.1, rd2, k1.2.2.1],
      by rw [wrt, wr4, k3.2.2.2, wr2, k1.2.2.2], Ot⟩
    simp only [List.mem_cons, not_or] at hr
    obtain ⟨h1, h2, h3, h4⟩ := hr
    rw [gt r h1, g4 r h1 h2, k3.1 r (by simp only [List.mem_cons, not_or]; exact ⟨h1, h3, h4⟩), g2,
      k1.1 r (by simp only [List.mem_cons, not_or]; exact ⟨h1, h3, h4⟩)]
  · rw [mt, (writeW_outside s4.mem base _ (by decide)).word (Or.inr (by decide)) (by decide), m4, k3.2.1,
      o2.word (Or.inl (by decide)) (by decide), k1.2.1]

open VG.Proof.X448.X86_64 (wv add_chain_ok stable_sc stable_scs W_nodup)

/-- The seven words at `p` into `r8–r14`. -/
theorem loadsS_ok (s : State) {p : Addr} (hp : s.gpr .rsi = p)
    (hr : ∀ i < 7, InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 (8 * i)) 8) :
    WP isa (.block ((List.range 7).map fun i => Instr.mov (w i) (.mem (at_ .rsi (8 * i))))) s fun t =>
      rv t W = mv s.mem p 0 7 ∧ Keeps W s t := by
  have r0 := hr 0 (by decide); have r1 := hr 1 (by decide); have r2 := hr 2 (by decide)
  have r3 := hr 3 (by decide); have r4 := hr 4 (by decide); have r5 := hr 5 (by decide)
  have r6 := hr 6 (by decide)
  erun [List.range_succ, List.range_zero, List.nil_append, List.map_append, List.map_cons, List.map_nil,
    List.cons_append, w, W, hp, r0, r1, r2, r3, r4, r5, r6, List.getD_cons_succ, List.getD_cons_zero, rv, mv,
    Keeps, Nat.reduceMul, Nat.reduceAdd, VG.Proof.X448.X86_64.word, off]
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hr
  simp only [h1, h2, h3, h4, h5, h6, h7, ite_false]

theorem setWidth8_eq_zero (b : Byte) : b.setWidth 64 = 0 ↔ b = 0 := by
  constructor
  · intro h
    apply BitVec.eq_of_toNat_eq
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans b.isLt (by decide))] at this
    exact this
  · rintro rfl; rfl

theorem ofBool_eq_zero (c : Bool) : (BitVec.ofBool c).setWidth 64 = 0 ↔ c = false := by
  cases c <;> decide

theorem or_eq_zero64 (x y : BitVec 64) : x ||| y = 0 ↔ x = 0 ∧ y = 0 := BitVec.or_eq_zero_iff

theorem sTail_ok (s : State) {p : Addr} (hp : s.gpr .rsi = p) {c : Bool} (hc : s.cf = some c)
    (hr : InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 56) 1) :
    WP isa (.block ([.mov32 .rdx (.imm 0), .alu .adc .rdx (.imm 0), .movzx8 .rax (at_ .rsi 56),
      .alu .or .rdx (.reg .rax)] : List Instr)) s fun t =>
      (t.gpr .rdx = 0 ↔ c = false ∧ s.mem (p + BitVec.ofNat 64 56) = 0) ∧ t.mem = s.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rdx → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  erun [hp, hr, hc]
  refine ⟨?_, fun r h1 h2 => by simp only [h1, h2, ite_false]⟩
  rw [show BitVec.setWidth 64 (0 : BitVec 32) + BitVec.signExtend 64 (0 : BitVec 32) +
      BitVec.setWidth 64 (BitVec.ofBool c) = BitVec.setWidth 64 (BitVec.ofBool c) by cases c <;> rfl,
    or_eq_zero64, ofBool_eq_zero, setWidth8_eq_zero]

open VG.Proof.X448.X86_64 (Outside2 len_W)

theorem sCheck_ok {s : State} {base p : Addr} (hs : Scr s base) (hp : s.gpr .rsi = p)
    (hr8 : ∀ i < 7, InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 (8 * i)) 8)
    (hr56 : InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 56) 1)
    (hfar : ∀ i < 57, 8192 ≤ ofs base (p + BitVec.ofNat 64 i)) :
    WP isa (.block sCheck) s fun t =>
      ∃ c : BitVec 64, (c = 0 ↔ Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem p 57) < Spec.Ed448.L) ∧
        word t.mem base BAD = word s.mem base BAD ||| c ∧
        (∀ r, r ∉ Reg.rax :: Reg.rdx :: W → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
        Outside2 base KC 56 BAD 8 s.mem t.mem := by
  rw [sCheck, WP.block_append_iff]
  refine WP.mono (storeK_ok hs) fun s1 ⟨k1, o1, g1, rd1, wr1⟩ => ?_
  have hs1 : Scr s1 base := ⟨(g1 _ (by decide)).trans hs.rdi, wr1 ▸ hs.wr, hs.nowrap⟩
  have hb1 : ∀ i < 57, s1.mem (p + BitVec.ofNat 64 i) = s.mem (p + BitVec.ofNat 64 i) :=
    fun i hi => o1 _ (Or.inr (by have := hfar i hi; simp only [KC]; omega))
  rw [WP.block_append_iff]
  refine WP.mono (loadsS_ok s1 ((g1 _ (by decide)).trans hp) (fun i hi => by
    rw [rd1, wr1]; exact hr8 i hi)) fun s2 ⟨v2, k2⟩ => ?_
  have hs2 := hs1.of_keeps k2 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (add_chain_ok W s2 .r8 [.r9, .r10, .r11, .r12, .r13, .r14]
    (.mem (sc 128)) (kOffs.map fun d => .mem (sc d))
    (word s2.mem base 128) (kOffs.map fun d => word s2.mem base d)
    (fun _ h => h) W_nodup rfl
    (stable_sc hs2 (by decide) (by decide))
    (stable_scs hs2 (by decide) kOffs (by decide))) fun s3 ⟨c, hc, e3, k3⟩ => ?_
  have hs3 := hs2.of_keeps k3 (by decide)
  have p3 : s3.gpr .rsi = p := by rw [k3.1 _ (by decide), k2.1 _ (by decide), g1 _ (by decide), hp]
  rw [WP.block_append_iff]
  refine WP.mono (sTail_ok s3 p3 hc (by rw [k3.2.2.1, k3.2.2.2, k2.2.2.1, k2.2.2.2, rd1, wr1]; exact hr56))
    fun s4 ⟨d4, m4, g4, rd4, wr4⟩ => ?_
  have hs4 : Scr s4 base := ⟨(g4 _ (by decide) (by decide)).trans hs3.rdi, wr4 ▸ hs3.wr, hs3.nowrap⟩
  refine WP.mono (orBad_ok hs4) fun t ⟨mt, gt, rdt, wrt⟩ => ?_
  have m3 : s3.mem = s1.mem := k3.2.1.trans k2.2.1
  refine ⟨s4.gpr .rdx, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [d4]
    have hkv : wv (word s2.mem base 128 :: kOffs.map fun d => word s2.mem base d) =
        2 ^ 448 - Spec.Ed448.L := by
      rw [← kWords_val, ← k1, k2.2.1]; rfl
    have hy : rv s2 W = Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem p 56) := by
      rw [v2, ← VG.Proof.X448.X86_64.leNum_bytesAt_mv, Proof.Ed448.decodeLE_eq]
      congr 1
      simp only [Spec.X448.bytesAt, Spec.Ed448.bytesAt, off, BitVec.add_zero]
      exact List.map_congr_left fun i hi => hb1 i (by simp at hi; omega)
    have hb : s3.mem (p + BitVec.ofNat 64 56) = s.mem (p + BitVec.ofNat 64 56) := by
      rw [m3]; exact hb1 56 (by decide)
    rw [hkv, len7, show rv s2 (Reg.r8 :: [.r9, .r10, .r11, .r12, .r13, .r14]) = rv s2 W from rfl, hy,
      show rv s3 (Reg.r8 :: [.r9, .r10, .r11, .r12, .r13, .r14]) = rv s3 W from rfl] at e3
    rw [bytesAt_57, Proof.Ed448.decodeLE_append, hb]
    have hlen : (Spec.Ed448.bytesAt s.mem p 56).length = 56 := by simp [Spec.Ed448.bytesAt]
    rw [hlen, show Spec.Ed448.decodeLE [s.mem (p + BitVec.ofNat 64 56)] = (s.mem (p + BitVec.ofNat 64 56)).toNat by
      simp [Spec.Ed448.decodeLE]]
    have hyl : Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem p 56) < 2 ^ 448 := by
      have := Proof.Ed448.decodeLE_lt' (Spec.Ed448.bytesAt s.mem p 56)
      rw [hlen] at this
      exact Nat.lt_of_lt_of_le this (by decide +kernel)
    have hrl := VG.Proof.X448.X86_64.rv_lt s3 W
    rw [len_W] at hrl
    have hc1 : c.toNat ≤ 1 := by cases c <;> decide
    have key := Proof.Ed448.sCheck_nat (b := (s.mem (p + BitVec.ofNat 64 56)).toNat) hyl hrl hc1 e3
    rw [← key]
    constructor
    · rintro ⟨rfl, h⟩; exact ⟨rfl, by rw [h]; rfl⟩
    · rintro ⟨h1, h2⟩
      refine ⟨?_, BitVec.eq_of_toNat_eq h2⟩
      cases c with
      | false => rfl
      | true => exact absurd h1 (by decide)
  · rw [mt, word_writeW_self, m4, m3, o1.word (Or.inr (by decide)) (by decide)]
  · intro r hr
    simp only [List.mem_cons, not_or] at hr
    obtain ⟨h1, h2, h3⟩ := hr
    rw [gt r h1, g4 r h1 h2, k3.1 r h3, k2.1 r h3, g1 r h3]
  · rw [rdt, rd4, k3.2.2.1, k2.2.2.1, rd1]
  · rw [wrt, wr4, k3.2.2.2, k2.2.2.2, wr1]
  · intro x hx hy
    rw [mt, (writeW_outside s4.mem base _ (by decide)) x hy, m4, m3]
    exact o1 x hx

end VG.Proof.Ed448.X86_64
