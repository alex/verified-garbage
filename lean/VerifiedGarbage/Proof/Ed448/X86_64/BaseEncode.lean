import VerifiedGarbage.Proof.Ed448.X86_64.BaseConst
import VerifiedGarbage.Proof.Ed448.X86_64.ScalarMain

/-!
# Ed448 base-point multiplication on x86-64: the encoding

`encode`: with `1/Z` in slot 21, `x = X/Z` and `y = Y/Z` (slots 3 and 4)
fully reduced; the seven words of `y` and a byte holding the low bit of `x`
as its top bit are the 57 bytes at the output's address (RFC 8032 §5.2.2);
then the callee-saved registers are restored.
-/

namespace VG.Proof.Ed448.X86_64

open VG VG.X86_64 VG.Impl.Ed448.X86_64
open VG.Proof.X448.X86_64 (Scr Index Env E Keep Keeps FieldOk rv mv wv word off Outside ofs Saved
  saved_lt mulE freeze_ok W_len rvW val7 mv7 fe)
open VG.Proof.X448 (toFe)
open VG.Impl.X448.X86_64 (W w sc at_ slot freeze)
open VG.Spec.Ed448 (L bytesAt)

theorem rotr57 (x : BitVec 64) (h : x.toNat < 2) : (x.rotateRight 57).toNat = 128 * x.toNat := by
  rw [BitVec.toNat_rotateRight]
  simp only [Nat.reduceMod, Nat.reduceSub, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  rw [Nat.div_eq_of_lt (by omega), Nat.zero_or, Nat.mod_eq_of_lt (by omega)]
  omega

/-- `rsi = 128 · (r8 mod 2)`. -/
theorem signBit_ok (s : State) :
    WP isa (.block signBit) s fun t =>
      (t.gpr .rsi).toNat = 128 * ((s.gpr .r8).toNat % 2) ∧ t.mem = s.mem ∧
      (∀ r, r ≠ .rsi → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have h1 : ((s.gpr .r8) &&& BitVec.signExtend 64 (1 : BitVec 32)).toNat = (s.gpr .r8).toNat % 2 := by
    rw [BitVec.toNat_and, show (BitVec.signExtend 64 (1 : BitVec 32)).toNat = 2 ^ 1 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod]
  apply WP.of_runBlock
  simp only [signBit, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, execShift,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags, RegUpd.wr_setReg,
    RegUpd.wr_arithFlags, RegUpd.wr_setFlags, RegUpd.mem_setReg, RegUpd.mem_arithFlags,
    RegUpd.mem_setFlags, RegUpd.rd_setReg, RegUpd.rd_arithFlags, RegUpd.rd_setFlags,
    show 1 ≤ 57 ∧ 57 ≤ 63 by decide, and_self, ite_true, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, trivial, fun r hr => by simp only [hr, ite_false], trivial⟩
  rw [rotr57 _ (by rw [h1]; omega), h1]

/-- The byte `rsi` at `q + 56`, for `rax = q`. -/
theorem byte56_ok {s : State} {q : Addr} (hq : s.gpr .rax = q)
    (hw : InRegions s.wr (q + BitVec.ofNat 64 56) 1) :
    WP isa (.block ([.store8 (at_ .rax 56) .rsi] : List Instr)) s fun t =>
      t.mem = s.mem.writeW (q + BitVec.ofNat 64 56) ((s.gpr .rsi).setWidth 8) ∧ t.gpr = s.gpr ∧
        t.rd = s.rd ∧ t.wr = s.wr := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, ea_at, State.store8, hq, hw,
    ite_true, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, trivial, trivial⟩

theorem rv_mod2 (s : State) : rv s W % 2 = (s.gpr .r8).toNat % 2 := by
  simp only [rv, W]; omega

theorem toFe_val' (x : Nat) : (toFe x).val = x % Spec.X448.P := rfl

theorem bytes56_write {m : Mem} {q : Addr} (v : Byte) :
    bytesAt (m.writeW (q + BitVec.ofNat 64 56) v) q 56 = bytesAt m q 56 := by
  simp only [bytesAt]
  refine List.map_congr_left fun i hi => ?_
  simp only [List.mem_range] at hi
  simp only [Mem.writeW]
  apply Mem.write_apply
  rw [Offset.lt_iff _ q (by omega), Offset.add_sub_cancel_left, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega)]
  omega

theorem byte56_write (m : Mem) (q : Addr) (v : Byte) :
    (m.writeW (q + BitVec.ofNat 64 56) v) (q + BitVec.ofNat 64 56) = v := by
  simp [Mem.writeW, Mem.write]

variable {fld : Impl.X448.X86_64.Field} (hf : FieldOk fld)

include hf in
/-- `encode`: the 57 bytes at `q` are the encoding of `y = Y/Z` and the low
bit of `x = X/Z`, for `1/Z` in slot 21. -/
theorem encode_ok {s : State} {base q : Addr} (hs : Scr s base) (hq : word s.mem base OUT = q)
    (hwo : (⟨q, 57⟩ : Region) ∈ s.wr) (hd : (⟨q, 57⟩ : Region).Disjoint ⟨base, 8192⟩)
    {g : Reg → BitVec 64} (hsv : Saved base g s.mem) :
    WP isa (.block (encode fld)) s fun t =>
      bytesAt t.mem q 57 = Proof.X25519.leBytes 56 (E s.mem base 1 * E s.mem base 21).val ++
        [BitVec.ofNat 8 (128 * ((E s.mem base 0 * E s.mem base 21).val % 2))] ∧
      (∀ rd ∈ Impl.X448.X86_64.saved, t.gpr rd.1 = g rd.1) ∧
      (∀ r, r ∉ .rbx :: .rsi :: Proof.X448.X86_64.clob → t.gpr r = s.gpr r) ∧
      Frame [⟨base, 8192⟩, ⟨q, 57⟩] s.mem t.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  rw [encode, WP.block_append_iff]
  refine WP.mono (mulE hf hs 3 0 21) fun s1 ⟨k1, e1⟩ => ?_
  have hs1 := k1.scr hs
  rw [WP.block_append_iff]
  refine WP.mono (mulE hf hs1 4 1 21) fun s2 ⟨k2, e2⟩ => ?_
  have hs2 := k2.scr hs1
  rw [WP.block_append_iff]
  refine WP.mono (freeze_ok hs2 (a := slot 3) (by decide)) fun s3 ⟨v3, k3⟩ => ?_
  have hs3 := hs2.of_keeps k3 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (signBit_ok s3) fun s4 ⟨r4, m4, g4, rd4, wr4⟩ => ?_
  have hs4 : Scr s4 base := ⟨(g4 _ (by decide)).trans hs3.rdi, wr4 ▸ hs3.wr, hs3.nowrap⟩
  rw [WP.block_append_iff]
  refine WP.mono (freeze_ok hs4 (a := slot 4) (by decide)) fun s5 ⟨v5, k5⟩ => ?_
  have hs5 := hs4.of_keeps k5 (by decide)
  have q5 : word s5.mem base OUT = q := by
    rw [k5.2.1, m4, k3.2.1, k2.mem.word (by decide) (by decide), k1.mem.word (by decide) (by decide),
      hq]
  rw [WP.block_append_iff]
  refine WP.mono (loadOut_ok hs5) fun s6 ⟨r6, k6⟩ => ?_
  have hs6 := hs5.of_keeps k6 (by decide)
  have hc8 : ∀ d, 0 ≤ d → d + 8 ≤ 0 + 8 * W.length → (⟨q, 57⟩ : Region).Contains (off q d) 8 :=
    fun d _ hd' => by
      rw [W_len] at hd'; exact Offset.contains_base _ (by omega) (by omega)
  have wr6 : s6.wr = s.wr := by rw [k6.2.2.2, k5.2.2.2, wr4, k3.2.2.2, k2.wr, k1.wr]
  rw [WP.block_append_iff]
  refine WP.mono (storesR_ok .rax (R := ⟨q, 57⟩) s6 0 W (r6.trans q5) (by rw [wr6]; exact hwo) hc8
    (by decide)) fun s7 ⟨v7, _, f7, g7, rd7, wr7⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (byte56_ok ((g7 _).trans (r6.trans q5)) ⟨_, by rw [wr7, wr6]; exact hwo,
    Offset.contains_base _ (by omega) (by omega)⟩) fun s8 ⟨m8, g8, rd8, wr8⟩ => ?_
  have O6 : Outside base 0 8192 s.mem s6.mem := by
    rw [k6.2.1, k5.2.1, m4, k3.2.1]; exact (k1.mem.trans k2.mem).mono (by decide) (by decide)
  have f8 : Frame [⟨base, 8192⟩, ⟨q, 57⟩] s.mem s8.mem := by
    rw [m8]
    exact (((VG.Proof.Ed448.X86_64.Outside.frame O6).mono (by simp)).trans (f7.mono (by simp))).writeW
      (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _
      (Offset.contains_base q (d := 56) (n := 8 / 8) (k := 57) (by decide) (by decide))
  have sv2 : Saved base g s2.mem := hsv.outside (k1.mem.trans k2.mem) (by decide)
  have sv6 : Saved base g s6.mem := by rw [k6.2.1, k5.2.1, m4, k3.2.1]; exact sv2
  have sv7 : Saved base g s7.mem := fun rd hrd => by
    have := saved_lt rd hrd; rw [← sv6 rd hrd]; exact word_frame f7 hd (by omega)
  have sv8 : Saved base g s8.mem := fun rd hrd => by
    have := saved_lt rd hrd
    rw [← sv7 rd hrd, m8]
    exact word_frame ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains_base q (d := 56) (n := 8 / 8) (k := 57) (by decide) (by decide))) hd (by omega)
  have hs8 : Scr s8 base := ⟨by rw [g8, g7]; exact hs6.rdi, wr8 ▸ wr7 ▸ hs6.wr, hs6.nowrap⟩
  refine WP.mono (Proof.X448.X86_64.restore_ok hs8 sv8) fun t ⟨rt, gt, mt, rdt, wrt⟩ => ?_
  refine ⟨?_, rt, fun r hr => ?_, by rw [mt]; exact f8, by rw [rdt, rd8, rd7, k6.2.2.1, k5.2.2.1,
    rd4, k3.2.2.1, k2.rd, k1.rd], by rw [wrt, wr8, wr7, wr6]⟩
  · -- The bytes.
    have e4 : E s2.mem base 4 = E s.mem base 1 * E s.mem base 21 := by
      rw [e2, e1]; rfl
    have e3 : E s2.mem base 3 = E s.mem base 0 * E s.mem base 21 := by
      rw [e2, e1]; rfl
    have x3 : rv s3 W = (E s.mem base 0 * E s.mem base 21).val := by
      rw [v3, ← e3]; rfl
    have y5 : rv s5 W = (E s.mem base 1 * E s.mem base 21).val := by
      rw [v5, m4, k3.2.1, ← e4]; rfl
    have b7 : bytesAt s7.mem q 56 = Proof.X25519.leBytes 56 (rv s5 W) := by
      have h := Proof.X448.X86_64.bytesAt_mv s7.mem q
      rw [W_len] at v7
      rw [v7, Proof.X448.X86_64.Keeps.rv_eq k6 (by decide)] at h
      exact h
    have rsi7 : s7.gpr .rsi = s4.gpr .rsi := by
      rw [g7, k6.1 _ (by decide), k5.1 _ (by decide)]
    have sb : (s7.gpr .rsi).setWidth 8 =
        BitVec.ofNat 8 (128 * ((E s.mem base 0 * E s.mem base 21).val % 2)) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_setWidth, rsi7, r4, BitVec.toNat_ofNat, ← rv_mod2, x3]
    rw [mt, bytesAt_57, m8, bytes56_write, byte56_write, b7, y5, sb]
  · have s1 : ∀ x ∈ [Reg.rbx, .rbp, .r12, .r13, .r14, .r15],
        x ∈ Reg.rbx :: Reg.rsi :: Proof.X448.X86_64.clob := by decide
    have s3 : ∀ x ∈ Reg.rax :: Reg.r15 :: W, x ∈ Reg.rbx :: Reg.rsi :: Proof.X448.X86_64.clob := by
      decide
    have s4 : ∀ x ∈ [Reg.rax], x ∈ Reg.rbx :: Reg.rsi :: Proof.X448.X86_64.clob := by decide
    have hr' : r ∉ Proof.X448.X86_64.clob := fun h => hr (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))
    have hsi : r ≠ .rsi := fun h => hr (h ▸ List.mem_cons_of_mem _ (List.mem_cons_self ..))
    rw [gt r (fun h => hr (s1 r h)), g8, g7, k6.1 r (fun h => hr (s4 r h)),
      k5.1 r (fun h => hr (s3 r h)), g4 r hsi, k3.1 r (fun h => hr (s3 r h)), k2.gpr r hr',
      k1.gpr r hr']

end VG.Proof.Ed448.X86_64
