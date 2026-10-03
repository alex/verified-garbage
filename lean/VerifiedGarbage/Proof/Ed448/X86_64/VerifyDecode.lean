import VerifiedGarbage.Proof.Ed448.X86_64.VerifyChecks
import VerifiedGarbage.Proof.Ed448.X86_64.VerifyField
import VerifiedGarbage.Proof.Ed448.Recover
import VerifiedGarbage.Proof.Ed448.DecodeBytes

/-!
# Ed448 verification's equation on x86-64: decoding a point

`decode fld xo yo` on the 57 bytes at `rsi` (RFC 8032 §5.2.3): `y`'s words
and the sign bit (`decodeY_ok`), `u`, `v`, `u³v` and `u⁵v³` (`decodeUV`),
the power by `(p-3)/4` (`root_spec`), `x` and the check `v x² = u`
(`decodeX_ok`), and the sign (`decodeSign_ok`). `decode_ok`: `BAD` gains a
word that is 0 exactly when the bytes decode, and then slots `xo` and `yo`
hold the decoded point's coordinates (`Z = 1`).
-/

namespace VG.Proof.Ed448.X86_64
open VG VG.X86_64 VG.Impl.Ed448.X86_64
open VG.Proof.X448.X86_64 (Scr word off Outside Outside2 ofs writeW_outside word_writeW_self contains_sc rv mv fe E
  Index Keeps freeze_ok stores_ok val7 mv7 rvW slot_lt W_len)
open VG.Impl.X448.X86_64 (W w sc at_ slot)

theorem byteBlock_ok {s : State} {base p : Addr} (hs : Scr s base) (hp : s.gpr .rsi = p)
    (hr : InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 56) 1) :
    WP isa (.block ([.movzx8 .rdx (at_ .rsi 56), .mov .rax (.reg .rdx), .shift .shr .rax 7,
      .store (sc SIGN) .rax, .alu .and .rdx (.imm 0x7f)] : List Instr)) s fun t =>
      t.mem = s.mem.writeW (off base SIGN) (BitVec.ofNat 64 ((s.mem (p + BitVec.ofNat 64 56)).toNat / 128)) ∧
      t.gpr .rdx = BitVec.ofNat 64 ((s.mem (p + BitVec.ofNat 64 56)).toNat % 128) ∧
      (∀ r, r ≠ .rax → r ≠ .rdx → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have wb : InRegions s.wr (base + BitVec.ofNat 64 SIGN) 8 := ⟨_, hs.wr, contains_sc (by decide)⟩
  erun [hp, hr, hs.rdi, wb]
  have hb := (s.mem (p + 56#64)).isLt
  refine ⟨?_, ?_, fun r h1 h2 => by simp only [h1, h2, ite_false]⟩
  · congr 1
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, show (BitVec.signExtend 64 (127 : BitVec 32)).toNat = 2 ^ 7 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : BitVec.toNat (s.mem (p + 56#64)) < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : BitVec.toNat (s.mem (p + 56#64)) % 128 < 2 ^ 64)]

theorem E_outside2 {base : Addr} {m m' : Mem} {o : Nat} (h : Outside2 base o 56 BAD 80 m m') (i : Index)
    (hi : slot i.val + 56 ≤ o ∨ o + 56 ≤ slot i.val) : E m' base i = E m base i := by
  have := slot_lt i
  simp only [VG.Impl.X448.X86_64.ACC] at this
  show VG.Proof.X448.toFe (mv m' base (slot i.val) 7) = VG.Proof.X448.toFe (mv m base (slot i.val) 7)
  rw [h.mv (by omega) (Or.inl (by simp only [BAD]; omega)) (by omega)]

theorem decodeY_ok {s : State} {base p : Addr} (hs : Scr s base) (hp : s.gpr .rsi = p) (yo : Index)
    (hr8 : ∀ i < 7, InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 (8 * i)) 8)
    (hr56 : InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 56) 1)
    (hfar : ∀ i < 57, 8192 ≤ ofs base (p + BitVec.ofNat 64 i)) :
    WP isa (.block (decodeY yo.val)) s fun t =>
      E t.mem base yo = VG.Proof.X448.toFe (Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem p 56)) ∧
      word t.mem base SIGN = BitVec.ofNat 64 ((s.mem (p + BitVec.ofNat 64 56)).toNat / 128) ∧
      (∃ c : BitVec 64, (c = 0 ↔ (s.mem (p + BitVec.ofNat 64 56)).toNat % 128 = 0 ∧
          Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem p 56) < Spec.X448.P) ∧
        word t.mem base BAD = word s.mem base BAD ||| c) ∧
      (∀ i : Index, i ≠ yo → E t.mem base i = E s.mem base i) ∧
      (∀ r, r ∉ Reg.rax :: Reg.rdx :: Reg.r15 :: W → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Outside2 base (slot yo.val) 56 BAD 80 s.mem t.mem := by
  have hy := slot_lt yo
  simp only [VG.Impl.X448.X86_64.ACC] at hy
  rw [decodeY, WP.block_append_iff]
  refine WP.mono (loadsS_ok s hp hr8) fun s1 ⟨v1, k1⟩ => ?_
  have hs1 := hs.of_keeps k1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (stores_ok hs1 (slot yo.val) W (by rw [W_len]; omega)) fun s2 ⟨v2, o2, g2, rd2, wr2⟩ => ?_
  rw [W_len] at v2 o2
  have hs2 : Scr s2 base := ⟨(g2 _).trans hs1.rdi, wr2 ▸ hs1.wr, hs1.nowrap⟩
  have b2 : s2.mem (p + BitVec.ofNat 64 56) = s.mem (p + BitVec.ofNat 64 56) := by
    rw [o2 _ (Or.inr (by have := hfar 56 (by decide); omega)), k1.2.1]
  rw [WP.block_append_iff]
  refine WP.mono (byteBlock_ok hs2 ((g2 _).trans ((k1.1 _ (by decide)).trans hp))
    (by rw [rd2, wr2, k1.2.2.1, k1.2.2.2]; exact hr56)) fun s3 ⟨m3, d3, g3, rd3, wr3⟩ => ?_
  have hs3 : Scr s3 base := ⟨(g3 _ (by decide) (by decide)).trans hs2.rdi, wr3 ▸ hs2.wr, hs2.nowrap⟩
  rw [WP.block_append_iff]
  refine WP.mono (orBad_ok hs3) fun s4 ⟨m4, g4, rd4, wr4⟩ => ?_
  have hs4 : Scr s4 base := ⟨(g4 _ (by decide)).trans hs3.rdi, wr4 ▸ hs3.wr, hs3.nowrap⟩
  rw [WP.block_append_iff]
  refine WP.mono (freeze_ok hs4 (a := slot yo.val) hy) fun s5 ⟨v5, k5⟩ => ?_
  have hs5 := hs4.of_keeps k5 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (diffWords_ok hs5 (o := slot yo.val) (by omega)) fun s6 ⟨d6, m6, g6, rd6, wr6⟩ => ?_
  have hs6 : Scr s6 base := ⟨(g6 _ (by decide) (by decide)).trans hs5.rdi, wr6 ▸ hs5.wr, hs5.nowrap⟩
  refine WP.mono (orBad_ok hs6) fun t ⟨mt, gt, rdt, wrt⟩ => ?_
  have hy0 : mv s.mem p 0 7 = Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem p 56) := by
    rw [← VG.Proof.X448.X86_64.leNum_bytesAt_mv, Proof.Ed448.decodeLE_eq]
    congr 1
    simp only [Spec.X448.bytesAt, Spec.Ed448.bytesAt, off, BitVec.add_zero]
  have O23 : Outside base SIGN 8 s2.mem s3.mem := by rw [m3]; exact writeW_outside _ _ _ (by decide)
  have O34 : Outside base BAD 8 s3.mem s4.mem := by rw [m4]; exact writeW_outside _ _ _ (by decide)
  have O6t : Outside base BAD 8 s6.mem t.mem := by rw [mt]; exact writeW_outside _ _ _ (by decide)
  have hY5 : mv s5.mem base (slot yo.val) 7 = mv s2.mem base (slot yo.val) 7 := by
    rw [k5.2.1, O34.mv (Or.inl (by simp only [BAD]; omega)) (by omega),
      O23.mv (Or.inl (by simp only [SIGN]; omega)) (by omega)]
  have hYt : mv t.mem base (slot yo.val) 7 = mv s5.mem base (slot yo.val) 7 := by
    rw [O6t.mv (Or.inl (by simp only [BAD]; omega)) (by omega), m6]
  have hYv : mv s5.mem base (slot yo.val) 7 = Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem p 56) := by
    rw [hY5, v2, v1, hy0]
  have F : Outside2 base (slot yo.val) 56 BAD 80 s.mem t.mem := by
    intro x h1 h2
    simp only [BAD] at h2 O6t O34
    simp only [SIGN] at O23
    rw [O6t x (by omega), m6, k5.2.1, O34 x (by omega), O23 x (by omega), o2 x h1, k1.2.1]
  refine ⟨?_, ?_, ⟨BitVec.ofNat 64 ((s.mem (p + BitVec.ofNat 64 56)).toNat % 128) ||| s6.gpr .rdx, ?_, ?_⟩,
    fun i hi => E_outside2 F i (by
      have := Fin.val_ne_of_ne hi
      simp only [slot]; omega), ?_, ?_, ?_, F⟩
  · show VG.Proof.X448.toFe (mv t.mem base (slot yo.val) 7) = _
    rw [hYt, hYv]
  · rw [O6t.word (Or.inr (by decide)) (by decide), m6, k5.2.1, O34.word (Or.inr (by decide)) (by decide), m3,
      word_writeW_self, b2]
  · rw [or_eq_zero64, d6, ← hYv]
    have e1 : BitVec.ofNat 64 ((s.mem (p + BitVec.ofNat 64 56)).toNat % 128) = 0 ↔
        (s.mem (p + BitVec.ofNat 64 56)).toNat % 128 = 0 := by
      constructor
      · intro h
        have := congrArg BitVec.toNat h
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
        exact this
      · intro h; rw [h]; rfl
    have e2 : (∀ i < 7, word s5.mem base (slot yo.val + 8 * i) = s5.gpr (w i)) ↔
        mv s5.mem base (slot yo.val) 7 < Spec.X448.P := by
      have hP0 : Spec.X448.P ≠ 0 := by decide +kernel
      have hv : rv s5 W = mv s5.mem base (slot yo.val) 7 % Spec.X448.P := by
        rw [v5, ← k5.2.1]
      have key : (∀ i < 7, word s5.mem base (slot yo.val + 8 * i) = s5.gpr (w i)) ↔
          mv s5.mem base (slot yo.val) 7 = rv s5 W := by
        rw [mv7, rvW, val7_inj (fun i _ => BitVec.isLt _) (fun i _ => BitVec.isLt _)]
        constructor
        · intro h i hi; exact congrArg BitVec.toNat (h i hi)
        · intro h i hi; exact BitVec.eq_of_toNat_eq (h i hi)
      rw [key, hv, eq_comm, Nat.mod_eq_iff_lt hP0]
    rw [e1, e2]
  · rw [mt, word_writeW_self, m6, k5.2.1, m4, word_writeW_self, d3, b2, BitVec.or_assoc,
      O23.word (Or.inl (by decide)) (by decide), o2.word (Or.inr (by simp only [BAD]; omega)) (by decide),
      k1.2.1]
  · intro r hr
    simp only [List.mem_cons, not_or] at hr
    obtain ⟨h1, h2, h3, h4⟩ := hr
    rw [gt r h1, g6 r h1 h2, k5.1 r (by simp only [List.mem_cons, not_or]; exact ⟨h1, h3, h4⟩), g4 r h1,
      g3 r h1 h2, g2, k1.1 r h4]
  · rw [rdt, rd6, k5.2.2.1, rd4, rd3, rd2, k1.2.2.1]
  · rw [wrt, wr6, k5.2.2.2, wr4, wr3, wr2, k1.2.2.2]

theorem or7 (f : Nat → BitVec 64) :
    (f 0 ||| f 1 ||| f 2 ||| f 3 ||| f 4 ||| f 5 ||| f 6 = 0) ↔ ∀ i < 7, f i = 0 := by
  simp only [or_eq_zero64]
  constructor
  · intro h i hi
    match i, hi with
    | 0, _ => exact h.1.1.1.1.1.1
    | 1, _ => exact h.1.1.1.1.1.2
    | 2, _ => exact h.1.1.1.1.2
    | 3, _ => exact h.1.1.1.2
    | 4, _ => exact h.1.1.2
    | 5, _ => exact h.1.2
    | 6, _ => exact h.2
  · intro h
    exact ⟨⟨⟨⟨⟨⟨h 0 (by decide), h 1 (by decide)⟩, h 2 (by decide)⟩, h 3 (by decide)⟩, h 4 (by decide)⟩,
      h 5 (by decide)⟩, h 6 (by decide)⟩

theorem negMask (x : BitVec 64) {sb : Nat} (hsb : sb < 2) :
    BitVec.setWidth 64 (0 : BitVec 32) - (x &&& BitVec.signExtend 64 (1 : BitVec 32) ^^^ BitVec.ofNat 64 sb) =
      VG.Proof.X448.X86_64.mask (decide (x.toNat % 2 ≠ sb)) := by
  have ha : x &&& BitVec.signExtend 64 (1 : BitVec 32) = BitVec.ofNat 64 (x.toNat % 2) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, show (BitVec.signExtend 64 (1 : BitVec 32)).toNat = 2 ^ 1 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : x.toNat % 2 < 2 ^ 64)]
  rw [ha]
  have h2 : x.toNat % 2 < 2 := Nat.mod_lt _ (by decide)
  generalize x.toNat % 2 = a at *
  rcases (by omega : a = 0 ∨ a = 1) with rfl | rfl <;> rcases (by omega : sb = 0 ∨ sb = 1) with rfl | rfl <;>
    decide

/-- The mask of `x`'s low bit differing from the sign bit, and the OR of `x`'s words. -/
theorem signA_ok {s : State} {base : Addr} (hs : Scr s base) {sb : Nat} (hsb : word s.mem base SIGN = BitVec.ofNat 64 sb)
    (hsb2 : sb < 2) :
    WP isa (.block (([.mov .rcx (.reg .r8), .alu .and .rcx (.imm 1), .mov .rax (.mem (sc SIGN)),
      .alu .xor .rcx (.reg .rax), .mov32 .rdx (.imm 0), .alu .sub .rdx (.reg .rcx), .store (sc NEG) .rdx,
      .mov .rdx (.reg .r8)] : List Instr) ++ (List.range 6).map (fun i => Instr.alu .or .rdx (.reg (w (i + 1)))))) s fun t =>
      t.mem = s.mem.writeW (off base NEG)
        (VG.Proof.X448.X86_64.mask (decide ((s.gpr .r8).toNat % 2 ≠ sb))) ∧
      t.gpr .rax = BitVec.ofNat 64 sb ∧
      (t.gpr .rdx = 0 ↔ ∀ i < 7, s.gpr (w i) = 0) ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have rb : InRegions (s.rd ++ s.wr) (base + BitVec.ofNat 64 SIGN) 8 := hs.read (by decide)
  have wb : InRegions s.wr (base + BitVec.ofNat 64 NEG) 8 := ⟨_, hs.wr, contains_sc (by decide)⟩
  erun [hs.rdi, rb, wb, List.range_succ, List.range_zero, List.nil_append, List.map_append, List.map_cons,
    List.map_nil, w, W, List.getD_cons_succ, List.getD_cons_zero, Nat.reduceAdd, List.cons_append,
    List.append_assoc, List.singleton_append]
  rw [show s.mem.readW (base + BitVec.ofNat 64 SIGN) 64 = BitVec.ofNat 64 sb from hsb]
  refine ⟨by rw [negMask _ hsb2], rfl,
    or7 (fun i => s.gpr ([Reg.r8, Reg.r9, Reg.r10, Reg.r11, Reg.r12, Reg.r13, Reg.r14].getD i Reg.r8)),
    fun r h1 h2 h3 => by simp only [h1, h2, h3, ite_false]⟩

open VG.Proof.X448.X86_64 (FieldOk Keep cswapE opSwap mask)

theorem rvW_mod2 (s : State) : rv s W % 2 = (s.gpr .r8).toNat % 2 := by
  simp only [rv, W]; omega

theorem rvW_zero (s : State) : (∀ i < 7, s.gpr (w i) = 0) ↔ rv s W = 0 := by
  rw [rvW, show (0 : Nat) = val7 (fun _ => 0) from rfl,
    val7_inj (fun i _ => BitVec.isLt _) (fun _ _ => by decide)]
  constructor
  · intro h i hi; rw [h i hi]; rfl
  · intro h i hi; exact BitVec.eq_of_toNat_eq (h i hi)

theorem andRax_ok (s : State) :
    WP isa (.block ([.alu .and .rdx (.reg .rax)] : List Instr)) s fun t =>
      t.gpr .rdx = s.gpr .rdx &&& s.gpr .rax ∧ t.mem = s.mem ∧
      (∀ r, r ≠ .rdx → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  erun
  exact fun r hr => by simp only [hr, ite_false]

theorem movNeg_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block ([.mov .rcx (.mem (sc NEG))] : List Instr)) s fun t =>
      t.gpr .rcx = word s.mem base NEG ∧ t.mem = s.mem ∧
      (∀ r, r ≠ .rcx → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have rb : InRegions (s.rd ++ s.wr) (base + BitVec.ofNat 64 NEG) 8 := hs.read (by decide)
  erun [hs.rdi, rb]
  exact fun r hr => by simp only [hr, ite_false]

theorem sign_bit (a sb : Nat) (ha : a < 2) (hsb : sb < 2) :
    ((a == 1) == (sb == 1)) = !(decide (a ≠ sb)) := by
  rcases (by omega : a = 0 ∨ a = 1) with rfl | rfl <;> rcases (by omega : sb = 0 ∨ sb = 1) with rfl | rfl <;>
    decide

theorem zeroSign (z : Bool) (sb : Nat) (hsb : sb < 2) :
    ((if z then (1 : BitVec 64) else 0) &&& BitVec.ofNat 64 sb = 0 ↔ ¬ (z = true ∧ sb = 1)) := by
  rcases (by omega : sb = 0 ∨ sb = 1) with rfl | rfl <;> cases z <;> decide

theorem idx_val (i : Index) : idx i.val = i := Fin.ext (Nat.mod_eq_of_lt i.isLt)

theorem subNeg_eval (xo : Index) (h : xo ≠ 12) (e : VG.Proof.X448.X86_64.Env) :
    evalOps [.sub 12 xo.val xo.val, .sub 12 12 xo.val] e 12 = (e xo - e xo) - e xo ∧
      ∀ i : Index, i ≠ 12 → evalOps [.sub 12 xo.val xo.val, .sub 12 12 xo.val] e i = e i := by
  have h12 : idx 12 = 12 := rfl
  simp only [evalOps, List.foldl, evalOp, idx_val, h12, VG.Proof.X448.X86_64.opSub]
  refine ⟨?_, fun i hi => ?_⟩
  · rw [Function.update_self, Function.update_self, Function.update_of_ne h]
  · rw [Function.update_of_ne hi, Function.update_of_ne hi]

variable {fld : Impl.X448.X86_64.Field} (hf : FieldOk fld)

include hf in
theorem decodeSign_ok {s : State} {base : Addr} (hs : Scr s base) (xo : Index) (hxo : xo = 6 ∨ xo = 8)
    {sb : Nat} (hsb : word s.mem base SIGN = BitVec.ofNat 64 sb) (hsb2 : sb < 2) :
    WP isa (.block (decodeSign fld xo.val)) s fun t =>
      E t.mem base xo = (if ((E s.mem base xo).val % 2 == 1) == (sb == 1) then E s.mem base xo
        else (E s.mem base xo - E s.mem base xo) - E s.mem base xo) ∧
      (∃ c : BitVec 64, (c = 0 ↔ ¬ (E s.mem base xo = 0 ∧ sb = 1)) ∧
        word t.mem base BAD = word s.mem base BAD ||| c) ∧
      (∀ i : Index, i ≠ xo → i ≠ 12 → E t.mem base i = E s.mem base i) ∧
      (∀ r, r ∉ VG.Proof.X448.X86_64.clob → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Outside2 base 64 1584 BAD 80 s.mem t.mem := by
  have hx := slot_lt xo
  simp only [VG.Impl.X448.X86_64.ACC] at hx
  have hx12 : xo ≠ 12 := by rcases hxo with rfl | rfl <;> decide
  rw [show decodeSign fld xo.val = VG.Impl.X448.X86_64.freeze (slot xo.val) ++ (([.mov .rcx (.reg .r8), .alu .and .rcx (.imm 1),
      .mov .rax (.mem (sc SIGN)), .alu .xor .rcx (.reg .rax), .mov32 .rdx (.imm 0), .alu .sub .rdx (.reg .rcx),
      .store (sc NEG) .rdx, .mov .rdx (.reg .r8)] ++
      (List.range 6).map (fun i => Instr.alu .or .rdx (.reg (w (i + 1))))) ++ (isZero ++
      (([.alu .and .rdx (.reg .rax)] : List Instr) ++ (orBad ++ (fieldCode fld [.sub 12 xo.val xo.val, .sub 12 12 xo.val] ++
      (([.mov .rcx (.mem (sc NEG))] : List Instr) ++ VG.Impl.X448.X86_64.cswap (slot xo.val) (slot 12))))))) by
    simp only [decodeSign, List.append_assoc]]
  rw [WP.block_append_iff]
  refine WP.mono (freeze_ok hs (a := slot xo.val) hx) fun s1 ⟨v1, k1⟩ => ?_
  have hs1 := hs.of_keeps k1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (signA_ok hs1 (by rw [k1.2.1]; exact hsb) hsb2) fun s2 ⟨m2, a2, d2, g2, rd2, wr2⟩ => ?_
  have hs2 : Scr s2 base := ⟨(g2 _ (by decide) (by decide) (by decide)).trans hs1.rdi, wr2 ▸ hs1.wr, hs1.nowrap⟩
  rw [WP.block_append_iff]
  refine WP.mono (isZero_ok s2) fun s3 ⟨d3, m3, g3, rd3, wr3⟩ => ?_
  have hs3 : Scr s3 base := ⟨(g3 _ (by decide)).trans hs2.rdi, wr3 ▸ hs2.wr, hs2.nowrap⟩
  rw [WP.block_append_iff]
  refine WP.mono (andRax_ok s3) fun s4 ⟨d4, m4, g4, rd4, wr4⟩ => ?_
  have hs4 : Scr s4 base := ⟨(g4 _ (by decide)).trans hs3.rdi, wr4 ▸ hs3.wr, hs3.nowrap⟩
  rw [WP.block_append_iff]
  refine WP.mono (orBad_ok hs4) fun s5 ⟨m5, g5, rd5, wr5⟩ => ?_
  have hs5 : Scr s5 base := ⟨(g5 _ (by decide)).trans hs4.rdi, wr5 ▸ hs4.wr, hs4.nowrap⟩
  rw [WP.block_append_iff]
  refine WP.mono (fieldCode_ok hf [.sub 12 xo.val xo.val, .sub 12 12 xo.val]
    (by rcases hxo with rfl | rfl <;> decide) hs5) fun s6 ⟨k6, e6⟩ => ?_
  have hs6 := k6.scr hs5
  rw [WP.block_append_iff]
  refine WP.mono (movNeg_ok hs6) fun s7 ⟨c7, m7, g7, rd7, wr7⟩ => ?_
  have hs7 : Scr s7 base := ⟨(g7 _ (by decide)).trans hs6.rdi, wr7 ▸ hs6.wr, hs6.nowrap⟩
  have hxv : rv s1 W = (E s.mem base xo).val := by rw [v1]; rfl
  have hsw : decide ((s1.gpr .r8).toNat % 2 ≠ sb) = decide ((E s.mem base xo).val % 2 ≠ sb) := by
    rw [← rvW_mod2, hxv]
  have O5 : Outside base BAD 80 s.mem s5.mem := by
    intro x hx
    rw [m5, writeW_outside s4.mem base _ (by decide) x (by simp only [BAD] at hx ⊢; omega), m4, m3, m2,
      writeW_outside s1.mem base _ (by decide) x (by simp only [BAD, NEG] at hx ⊢; omega), k1.2.1]
  have e5 : E s5.mem base = E s.mem base := E_bad O5
  obtain ⟨n12, nk⟩ := subNeg_eval xo hx12 (E s5.mem base)
  have hneg : word s6.mem base NEG = mask (decide ((E s.mem base xo).val % 2 ≠ sb)) := by
    rw [k6.mem.word (Or.inr (by decide)) (by decide), m5, (writeW_outside s4.mem base _ (by decide)).word
      (Or.inr (by decide)) (by decide), m4, m3, m2, word_writeW_self, hsw]
  refine WP.mono (cswapE hs7 xo 12 hx12 (sw := decide ((E s.mem base xo).val % 2 ≠ sb))
    (by rw [c7, hneg])) fun t ⟨kt, _, et⟩ => ?_
  have e6 : E s7.mem base = evalOps [.sub 12 xo.val xo.val, .sub 12 12 xo.val] (E s5.mem base) := by
    rw [m7, e6]
  have hx2 : (E s.mem base xo).val % 2 < 2 := Nat.mod_lt _ (by decide)
  refine ⟨?_, ⟨s4.gpr .rdx, ?_, ?_⟩, fun i h1 h2 => ?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · rw [et, sign_bit _ _ hx2 hsb2]
    cases hd : decide ((E s.mem base xo).val % 2 ≠ sb) with
    | false =>
      simp only [opSwap, Bool.not_false, ite_true, Bool.false_eq_true, ite_false]
      rw [Function.update_of_ne hx12, Function.update_self, e6, nk xo hx12, e5]
    | true =>
      simp only [opSwap, Bool.not_true, ite_true, Bool.false_eq_true, ite_false]
      rw [Function.update_of_ne hx12, Function.update_self, e6, n12, e5]
  · rw [d4, d3, g3 _ (by decide), a2]
    have hz : (s2.gpr .rdx = 0) ↔ E s.mem base xo = 0 := by
      rw [d2, rvW_zero, hxv]
      have z0 : (0 : Spec.X448.Fe).val = 0 := by decide +kernel
      constructor
      · intro h; exact Fin.ext (h.trans z0.symm)
      · intro h; rw [h]; exact z0
    by_cases h0 : s2.gpr .rdx = 0
    · rw [ite_eq_left h0]
      have := zeroSign true sb hsb2
      simp only [ite_true] at this
      rw [this, hz.mp h0]
      exact ⟨fun h1 h2 => h1 ⟨trivial, h2.2⟩, fun h1 h2 => h1 ⟨rfl, h2.2⟩⟩
    · rw [ite_eq_right h0]
      have := zeroSign false sb hsb2
      simp only [Bool.false_eq_true, ite_false] at this
      rw [this]
      constructor
      · intro _ h; exact h0 (hz.mpr h.1)
      · intro _ h; exact h.1.elim
  · rw [kt.mem.word (Or.inr (by decide)) (by decide), m7, k6.mem.word (Or.inr (by decide)) (by decide), m5,
      word_writeW_self, m4, m3, m2, (writeW_outside s1.mem base _ (by decide)).word (Or.inl (by decide))
      (by decide), k1.2.1]
  · rw [et]
    simp only [opSwap]
    rw [Function.update_of_ne h2, Function.update_of_ne h1, e6, nk i h2, e5]
  · have hr' : ∀ x ∈ Reg.rax :: Reg.r15 :: W, x ∈ VG.Proof.X448.X86_64.clob := by decide
    rw [kt.gpr r hr, g7 r (fun h => hr (h ▸ by decide)), k6.gpr r hr, g5 r (fun h => hr (h ▸ by decide)),
      g4 r (fun h => hr (h ▸ by decide)), g3 r (fun h => hr (h ▸ by decide)),
      g2 r (fun h => hr (h ▸ by decide)) (fun h => hr (h ▸ by decide)) (fun h => hr (h ▸ by decide)),
      k1.1 r (fun h => hr (hr' r h))]
  · rw [kt.rd, rd7, k6.rd, rd5, rd4, rd3, rd2, k1.2.2.1]
  · rw [kt.wr, wr7, k6.wr, wr5, wr4, wr3, wr2, k1.2.2.2]
  · intro x h1 h2
    rw [kt.mem x h1, m7, k6.mem x h1, O5 x h2]

theorem decodeUV_dest : ∀ xo yo : Nat, (xo = 6 ∧ yo = 7) ∨ (xo = 8 ∧ yo = 9) →
    ∀ op ∈ decodeUV yo xo, fopDest op % 22 = 3 ∨ fopDest op % 22 = 4 ∨ fopDest op % 22 = 5 ∨
      fopDest op % 22 = 12 ∨ fopDest op % 22 = 13 ∨ fopDest op % 22 = xo := by
  rintro xo yo (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> decide

theorem decodeUV_eval (xo yo : Index) (h : (xo = 6 ∧ yo = 7) ∨ (xo = 8 ∧ yo = 9))
    (e : VG.Proof.X448.X86_64.Env) :
    let y := e yo
    let u := y * y - e 10
    let v := e 11 * (y * y) - e 10
    let t := u * u * u * v
    let e' := evalOps (decodeUV yo.val xo.val) e
    e' 13 = u ∧ e' 3 = v ∧ e' xo = t ∧ e' 12 = t * ((u * v) * (u * v)) ∧
      ∀ i : Index, i ≠ 3 → i ≠ 4 → i ≠ 5 → i ≠ 12 → i ≠ 13 → i ≠ xo → e' i = e i := by
  have hk : ∀ i : Index, i ≠ 3 → i ≠ 4 → i ≠ 5 → i ≠ 12 → i ≠ 13 → i ≠ xo →
      evalOps (decodeUV yo.val xo.val) e i = e i := fun i h3 h4 h5 h12 h13 hx =>
    evalOps_keep _ _ _ fun op hop => by
      have hd := decodeUV_dest xo.val yo.val (by rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp) op hop
      have : i.val ≠ 3 := fun h => h3 (Fin.ext h)
      have : i.val ≠ 4 := fun h => h4 (Fin.ext h)
      have : i.val ≠ 5 := fun h => h5 (Fin.ext h)
      have : i.val ≠ 12 := fun h => h12 (Fin.ext h)
      have : i.val ≠ 13 := fun h => h13 (Fin.ext h)
      have := Fin.val_ne_of_ne hx
      omega
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl, rfl, hk⟩
  · exact ⟨rfl, rfl, rfl, rfl, hk⟩

theorem decodeXOps_eval (xo : Index) (h : xo = 6 ∨ xo = 8) (e : VG.Proof.X448.X86_64.Env) :
    let x := e xo * e 21
    let e' := evalOps [.mul xo.val xo.val 21, .sqr 12 xo.val, .mul 12 3 12] e
    e' xo = x ∧ e' 12 = e 3 * (x * x) ∧ e' 13 = e 13 ∧ ∀ i : Index, i ≠ xo → i ≠ 12 → e' i = e i := by
  have hk : ∀ i : Index, i ≠ xo → i ≠ 12 →
      evalOps [.mul xo.val xo.val 21, .sqr 12 xo.val, .mul 12 3 12] e i = e i := fun i hx h12 =>
    evalOps_keep _ _ _ fun op hop => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
      have := Fin.val_ne_of_ne hx
      have : i.val ≠ 12 := fun h => h12 (Fin.ext h)
      have := xo.isLt
      rcases hop with rfl | rfl | rfl <;> simp only [fopDest] <;> omega
  rcases h with rfl | rfl
  · exact ⟨rfl, rfl, rfl, hk⟩
  · exact ⟨rfl, rfl, rfl, hk⟩

include hf in
theorem decodeX_ok {s : State} {base : Addr} (hs : Scr s base) (xo : Index) (hxo : xo = 6 ∨ xo = 8) :
    WP isa (.block (decodeX fld xo.val)) s fun t =>
      E t.mem base xo = E s.mem base xo * E s.mem base 21 ∧
      (∃ c : BitVec 64, (c = 0 ↔ E s.mem base 3 * ((E s.mem base xo * E s.mem base 21) *
          (E s.mem base xo * E s.mem base 21)) = E s.mem base 13) ∧
        word t.mem base BAD = word s.mem base BAD ||| c) ∧
      (∀ i : Index, i ≠ xo → i ≠ 12 → E t.mem base i = E s.mem base i) ∧
      word t.mem base SIGN = word s.mem base SIGN ∧
      (∀ r, r ∉ VG.Proof.X448.X86_64.clob → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Outside2 base 64 1584 BAD 80 s.mem t.mem := by
  rw [decodeX, WP.block_append_iff]
  refine WP.mono (fieldCode_ok hf [.mul xo.val xo.val 21, .sqr 12 xo.val, .mul 12 3 12]
    (by rcases hxo with rfl | rfl <;> decide) hs) fun s1 ⟨k1, e1⟩ => ?_
  have hs1 := k1.scr hs
  obtain ⟨x1, x12, x13, xk⟩ := decodeXOps_eval xo hxo (E s.mem base)
  refine WP.mono (eqSlots_ok hs1 12 13) fun t ⟨c, hc, ht, kt, st⟩ => ?_
  rw [kt.E, e1]
  refine ⟨x1, ⟨c, by rw [hc, e1, x12, x13], by rw [ht, k1.mem.word (Or.inr (by decide)) (by decide)]⟩,
    fun i h1 h2 => xk i h1 h2, by rw [st, k1.mem.word (Or.inr (by decide)) (by decide)],
    fun r hr => ?_, by rw [kt.rd, k1.rd], by rw [kt.wr, k1.wr], fun x h1 h2 => by
      rw [kt.mem x h2, k1.mem x h1]⟩
  have : ∀ x ∈ Reg.rax :: Reg.rdx :: Reg.r15 :: W, x ∈ VG.Proof.X448.X86_64.clob := by decide
  rw [kt.gpr r (fun h => hr (this r h)), k1.gpr r hr]

open VG.Proof.X448.X86_64 (IKeep)

theorem bytesAt57_take (m : Mem) (p : Addr) :
    (Spec.Ed448.bytesAt m p 57).take 56 = Spec.Ed448.bytesAt m p 56 := by
  simp [Spec.Ed448.bytesAt, ← List.map_take, List.take_range]

theorem bytesAt57_getD (m : Mem) (p : Addr) :
    (Spec.Ed448.bytesAt m p 57).getD 56 0 = m (p + BitVec.ofNat 64 56) := by
  simp [Spec.Ed448.bytesAt, List.getD_eq_getElem?_getD]

theorem bytesAt57_len (m : Mem) (p : Addr) : (Spec.Ed448.bytesAt m p 57).length = 57 := by
  simp [Spec.Ed448.bytesAt]

include hf in
theorem decode_ok {s : State} {base p : Addr} (hs : Scr s base) (hp : s.gpr .rsi = p) (xo yo : Index)
    (hxy : (xo = 6 ∧ yo = 7) ∨ (xo = 8 ∧ yo = 9))
    (h10 : E s.mem base 10 = 1) (h11 : E s.mem base 11 = Spec.Ed448.d)
    (hr8 : ∀ i < 7, InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 (8 * i)) 8)
    (hr56 : InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 56) 1)
    (hfar : ∀ i < 57, 8192 ≤ ofs base (p + BitVec.ofNat 64 i)) :
    WP isa (decode fld xo.val yo.val) s fun t =>
      (∃ c : BitVec 64, (c = 0 ↔ (Spec.Ed448.decodePoint (Spec.Ed448.bytesAt s.mem p 57)).isSome) ∧
        word t.mem base BAD = word s.mem base BAD ||| c) ∧
      (∀ pt, Spec.Ed448.decodePoint (Spec.Ed448.bytesAt s.mem p 57) = some pt →
        E t.mem base xo = pt.X ∧ E t.mem base yo = pt.Y ∧ pt.Z = 1) ∧
      (∀ i : Index, i.val < 12 → i ≠ 3 → i ≠ 4 → i ≠ 5 → i ≠ xo → i ≠ yo →
        E t.mem base i = E s.mem base i) ∧
      (∀ r, r ∉ .rbx :: VG.Proof.X448.X86_64.clob → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Outside2 base 64 1584 BAD 80 s.mem t.mem := by
  have hxo : xo = 6 ∨ xo = 8 := by rcases hxy with ⟨h, _⟩ | ⟨h, _⟩ <;> simp [h]
  have hyx : yo ≠ xo := by rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  have hy := slot_lt yo
  simp only [VG.Impl.X448.X86_64.ACC] at hy
  rw [decode]
  apply WP.seq
  rw [WP.block_append_iff]
  refine WP.mono (decodeY_ok hs hp yo hr8 hr56 hfar) fun s1 ⟨y1, sg1, ⟨c1, hc1, b1⟩, e1, g1, rd1, wr1, o1⟩ => ?_
  have hs1 : Scr s1 base := ⟨(g1 _ (by decide)).trans hs.rdi, wr1 ▸ hs.wr, hs.nowrap⟩
  refine WP.mono (fieldCode_ok hf (decodeUV yo.val xo.val)
    (by rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide) hs1) fun s2 ⟨k2, e2⟩ => ?_
  have hs2 := k2.scr hs1
  apply WP.seq
  refine WP.mono (root_spec hf base s2 hs2) fun s3 ⟨k3, e3⟩ => ?_
  have hs3 := k3.scr hs2
  rw [WP.block_append_iff]
  refine WP.mono (decodeX_ok hf hs3 xo hxo) fun s4 ⟨x4, ⟨c2, hc2, b4⟩, e4, sg4, g4, rd4, wr4, o4⟩ => ?_
  have hs4 : Scr s4 base := ⟨(g4 _ (by decide)).trans hs3.rdi, wr4 ▸ hs3.wr, hs3.nowrap⟩
  have hb128 : (s.mem (p + BitVec.ofNat 64 56)).toNat / 128 < 2 := by
    have := (s.mem (p + BitVec.ofNat 64 56)).isLt; omega
  have sg : word s4.mem base SIGN = BitVec.ofNat 64 ((s.mem (p + BitVec.ofNat 64 56)).toNat / 128) := by
    rw [sg4, k3.mem.word (Or.inr (by decide)) (by decide), k2.mem.word (Or.inr (by decide)) (by decide), sg1]
  refine WP.mono (decodeSign_ok hf hs4 xo hxo sg hb128)
    fun t ⟨xt, ⟨c3, hc3, bt⟩, et, gt, rdt, wrt, ot⟩ => ?_
  -- The values.
  have h10' : E s1.mem base 10 = 1 := by
    rw [e1 10 (by rcases hxy with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide), h10]
  have h11' : E s1.mem base 11 = Spec.Ed448.d := by
    rw [e1 11 (by rcases hxy with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide), h11]
  obtain ⟨u2, v2, t2, w2, k2'⟩ := decodeUV_eval xo yo hxy (E s1.mem base)
  simp only [h10', h11', y1] at u2 v2 t2 w2
  simp only [← e2] at u2 v2 t2 w2 k2'
  generalize hY : VG.Proof.X448.toFe (Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem p 56)) = Y at *
  have r21 : E s3.mem base 21 = rootPow (E s2.mem base 12) := by rw [e3, rootEnv_eval]
  have r3k : ∀ i : Index, i.val < 14 → E s3.mem base i = E s2.mem base i := fun i hi => by
    rw [e3, rootEnv_keep _ _ hi]
  have hxlt : xo.val < 14 := by rcases hxo with rfl | rfl <;> decide
  have hylt : yo.val < 14 := by rcases hxy with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide
  rw [r3k xo hxlt, t2, r21, w2, r3k 3 (by decide), v2, r3k 13 (by decide), u2] at hc2
  rw [r3k xo hxlt, t2, r21, w2] at x4
  generalize hu : Y * Y - 1 = u at *
  generalize hv : Spec.Ed448.d * (Y * Y) - 1 = v at *
  generalize ht : u * u * u * v = tt at *
  generalize hx : tt * rootPow (tt * ((u * v) * (u * v))) = x at *
  rw [x4] at xt hc3
  have hD := Proof.Ed448.decodePoint_impl (Spec.Ed448.bytesAt s.mem p 57) (bytesAt57_len _ _)
    (Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem p 56)) ((s.mem (p + BitVec.ofNat 64 56)).toNat)
    (by rw [bytesAt57_take]) (by rw [bytesAt57_getD]) Y u v tt x hY hu hv ht hx
  -- what is kept
  have kY : E t.mem base yo = Y := by
    rw [et yo hyx (by rcases hxy with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide),
      e4 yo hyx (by rcases hxy with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide), r3k yo hylt,
      k2' yo (by rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide) (by rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide)
        (by rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide) (by rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide)
        (by rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide) hyx, y1]
  refine ⟨⟨c1 ||| c2 ||| c3, ?_, ?_⟩, fun pt hpt => ?_, fun i hi h3 h4 h5 hix hiy => ?_, fun r hr => ?_,
    ?_, ?_, ?_⟩
  · rw [or_eq_zero64, or_eq_zero64, hc1, hc2, hc3, hD]
    by_cases hall : ((s.mem (p + BitVec.ofNat 64 56)).toNat % 128 = 0 ∧
        Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem p 56) < Spec.X448.P) ∧ v * (x * x) = u ∧
        ¬ (x = 0 ∧ (s.mem (p + BitVec.ofNat 64 56)).toNat / 128 = 1)
    · rw [ite_eq_left hall]
      exact ⟨fun _ => rfl, fun _ => ⟨⟨hall.1, hall.2.1⟩, hall.2.2⟩⟩
    · rw [ite_eq_right hall]
      exact ⟨fun h => absurd ⟨h.1.1, h.1.2, h.2⟩ hall, fun h => absurd h (by simp)⟩
  · rw [bt, b4, k3.mem.word (Or.inr (by decide)) (by decide), k2.mem.word (Or.inr (by decide)) (by decide),
      b1]
    simp only [BitVec.or_assoc]
  · rw [hD] at hpt
    by_cases hall : ((s.mem (p + BitVec.ofNat 64 56)).toNat % 128 = 0 ∧
        Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem p 56) < Spec.X448.P) ∧ v * (x * x) = u ∧
        ¬ (x = 0 ∧ (s.mem (p + BitVec.ofNat 64 56)).toNat / 128 = 1)
    · rw [ite_eq_left hall] at hpt
      cases hpt
      exact ⟨xt, kY, rfl⟩
    · rw [ite_eq_right hall] at hpt
      cases hpt
  · have hi14 : i.val < 14 := by omega
    have h12 : i ≠ 12 := fun h => by rw [h] at hi; exact absurd hi (by decide)
    have h13 : i ≠ 13 := fun h => by rw [h] at hi; exact absurd hi (by decide)
    rw [et i hix h12, e4 i hix h12, r3k i hi14, k2' i h3 h4 h5 h12 h13 hix, e1 i hiy]
  · have s1 : ∀ x ∈ Reg.rax :: Reg.rdx :: Reg.r15 :: W, x ∈ Reg.rbx :: VG.Proof.X448.X86_64.clob := by decide
    have hr' : r ∉ VG.Proof.X448.X86_64.clob := fun h => hr (List.mem_cons_of_mem _ h)
    have hrb : r ≠ .rbx := fun h => hr (h ▸ List.mem_cons_self)
    rw [gt r hr', g4 r hr', k3.gpr r hr' hrb, k2.gpr r hr', g1 r (fun h => hr (s1 r h))]
  · rw [rdt, rd4, k3.rd, k2.rd, rd1]
  · rw [wrt, wr4, k3.wr, k2.wr, wr1]
  · intro z h1 h2
    have hy2 := o1 z (by
      rcases h1 with h | h
      · left; have := slot_lt yo; simp only [slot] at *; omega
      · right; simp only [slot] at *; omega) h2
    rw [ot z h1 h2, o4 z h1 h2, k3.mem z (by omega), k2.mem z h1, hy2]

end VG.Proof.Ed448.X86_64
