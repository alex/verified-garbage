import VerifiedGarbage.Proof.Ed448.X86_64.ScalarWord

/-!
# Ed448 scalar arithmetic on x86-64: the loop over the words

`scalarLoop` consumes the words of an input of `8n + t` bytes from the top,
below the `t` bytes the remainder starts from: the invariant is the value
modulo `L` of the consumed top bytes. The body writes only `TMP`, which the
input does not overlap (it is in another buffer, or elsewhere in the
working space).
-/

namespace VG.Proof.Ed448.X86_64

open VG VG.X86_64 VG.Impl.Ed448.X86_64
open VG.Proof.X448.X86_64 (Keeps Scr rv mv wv word off Outside ofs)
open VG.Spec.Ed448 (L bytesAt decodeLE)

theorem bytesAt_length (m : Mem) (p : Addr) (n : Nat) : (bytesAt m p n).length = n := by
  simp only [bytesAt, List.length_map, List.length_range]

/-- The input from word `k` up: that word, and `2^64` times the bytes above
it. -/
theorem words_step (m : Mem) (p : Addr) (len k : Nat) (hk : 8 * (k + 1) ≤ len) :
    decodeLE (bytesAt m (p + BitVec.ofNat 64 (8 * k)) (len - 8 * k)) =
      (m.readW (p + BitVec.ofNat 64 (8 * k)) 64).toNat +
        2 ^ 64 * decodeLE (bytesAt m (p + BitVec.ofNat 64 (8 * (k + 1))) (len - 8 * (k + 1))) := by
  have e : len - 8 * k = 8 + (len - 8 * (k + 1)) := by omega
  have hs : bytesAt m (p + BitVec.ofNat 64 (8 * k)) (8 + (len - 8 * (k + 1))) =
      bytesAt m (p + BitVec.ofNat 64 (8 * k)) 8 ++
        bytesAt m (p + BitVec.ofNat 64 (8 * k) + BitVec.ofNat 64 8) (len - 8 * (k + 1)) :=
    Proof.X25519.bytesAt_add m _ 8 _
  have hw : decodeLE (bytesAt m (p + BitVec.ofNat 64 (8 * k)) 8) =
      (m.readW (p + BitVec.ofNat 64 (8 * k)) 64).toNat := by
    rw [decodeLE_eq]; exact Proof.X25519.leNum_bytesAt_64 m _
  have ha : p + BitVec.ofNat 64 (8 * k) + BitVec.ofNat 64 8 = p + BitVec.ofNat 64 (8 * (k + 1)) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 8 * k + 8 = 8 * (k + 1) by omega]
  rw [e, hs, decodeLE_append, bytesAt_length, hw, ha]

def wordRead : List Instr :=
  [.alu .sub .rbx (.imm 8), .mov .rax (.mem { base := .rsi, index := some .rbx })]

theorem wordRead_ok (s : State) (k : Nat) (hb : s.gpr .rbx = BitVec.ofNat 64 (8 * (k + 1)))
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofNat 64 (8 * k)) 8) :
    WP isa (.block wordRead) s fun t =>
      t.gpr .rbx = BitVec.ofNat 64 (8 * k) ∧
      t.gpr .rax = s.mem.readW (s.gpr .rsi + BitVec.ofNat 64 (8 * k)) 64 ∧
      Keeps [.rbx, .rax] s t := by
  have hn : s.gpr .rbx - (8 : BitVec 32).signExtend 64 = BitVec.ofNat 64 (8 * k) := by
    rw [hb, show (8 : BitVec 32).signExtend 64 = BitVec.ofNat 64 8 from rfl,
      show 8 * (k + 1) = 8 * k + 8 by omega, BitVec.ofNat_add, BitVec.add_sub_cancel]
  apply WP.of_runBlock
  simp only [wordRead, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    State.ea, State.load64, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    RegUpd.rd_setReg, RegUpd.rd_arithFlags, RegUpd.wr_setReg, RegUpd.wr_arithFlags,
    RegUpd.mem_setReg, RegUpd.mem_arithFlags, hn, ite_true, ite_false, reduceCtorEq,
    BitVec.mul_one, show BitVec.ofInt 64 (0 : Int) = BitVec.ofNat 64 0 from rfl,
    BitVec.add_zero, hr, Option.bind_some, Option.map_some,
    Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, fun r h => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, h.1, h.2, ite_false], rfl, rfl, rfl⟩

theorem test_zero : ∀ n < 128,
    (BitVec.ofNat 64 n &&& BitVec.ofNat 64 n == 0) = decide (n = 0) := by decide

theorem test_ok (s : State) (n : Nat) (hn : n < 128) (hb : s.gpr .rbx = BitVec.ofNat 64 n) :
    WP isa (.block [.alu .test .rbx (.reg .rbx)]) s fun t =>
      t.zf = some (decide (n = 0)) ∧ (∀ r, t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧
        t.wr = s.wr := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    Option.bind_some, Option.some.injEq, exists_eq_left', RegUpd.zf_arithFlags, hb,
    test_zero n hn]
  exact ⟨trivial, fun _ => rfl, rfl, rfl, rfl⟩

/-- The registers the loop changes. -/
def bodyClob : List Reg := [.rbx, .rax, .rcx, .rdx, .rbp, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]

theorem scalarWord_eq : scalarWord = wordRead ++ (wordFold ++ (csub ++
    ([.alu .test .rbx (.reg .rbx)] : List Instr))) := by
  simp only [scalarWord, wordRead, List.append_assoc, List.cons_append, List.nil_append]

/-- One word: read, folded in, reduced. -/
theorem scalarWord_ok {s : State} {base : Addr} (hs : Scr s base)
    (hK : mv s.mem base KC 7 = wv kWords) (k : Nat) (hk : 8 * (k + 1) < 128)
    (hb : s.gpr .rbx = BitVec.ofNat 64 (8 * (k + 1)))
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofNat 64 (8 * k)) 8)
    (hv : rem s < L) :
    WP isa (.block scalarWord) s fun t =>
      t.gpr .rbx = BitVec.ofNat 64 (8 * k) ∧ t.zf = some (decide (k = 0)) ∧
      rem t = ((s.mem.readW (s.gpr .rsi + BitVec.ofNat 64 (8 * k)) 64).toNat + 2 ^ 64 * rem s) % L ∧
      (∀ r, r ∉ bodyClob → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Outside base TMP 56 s.mem t.mem := by
  rw [scalarWord_eq, WP.block_append_iff]
  refine WP.mono (wordRead_ok s k hb hr) fun a ⟨ab, ax, ka⟩ => ?_
  have av : rem a = rem s := ka.rv_eq (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (wordFold_ok a (av ▸ hv)) fun b ⟨b2, bm, kb⟩ => ?_
  have hsb : Scr b base := (hs.of_keeps ka (by decide)).of_keeps kb (by decide)
  have mb : b.mem = s.mem := kb.2.1.trans ka.2.1
  rw [WP.block_append_iff]
  refine WP.mono (csub_ok hsb (by rw [mb]; exact hK) b2) fun c ⟨cv, gc, rdc, wrc, oc⟩ => ?_
  have hbc : c.gpr .rbx = BitVec.ofNat 64 (8 * k) := by
    rw [gc _ (by decide), kb.1 _ (by decide)]; exact ab
  refine WP.mono (test_ok c (8 * k) (by omega) hbc) fun t ⟨tz, tg, tm, trd, twr⟩ => ?_
  refine ⟨(tg _).trans hbc, by rw [tz]; simp; omega, ?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · rw [show rem t = rem c from Proof.X448.X86_64.rv_congr fun r _ => tg r, cv, bm, ax, av]
  · simp only [bodyClob, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [tg, gc r (by simp [csubClob, hr.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2.2.2.2]),
      kb.1 r (by simp [foldClob, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2.2.2.1]),
      ka.1 r (by simp [hr.1, hr.2.1])]
  · rw [trd, rdc, kb.2.2.1, ka.2.2.1]
  · rw [twr, wrc, kb.2.2.2, ka.2.2.2]
  · rw [tm, ← mb]; exact oc

/-- The loop's invariant, after `n` words are left: the remainder is that of
the bytes from word `n` up, of the `len` bytes at `p`. -/
structure LoopInv (base p : Addr) (len : Nat) (s₀ : State) (n : Nat) (s : State) : Prop where
  bound : 8 * n ≤ len
  counter : s.gpr .rbx = BitVec.ofNat 64 (8 * n)
  value : rem s = decodeLE (bytesAt s₀.mem (p + BitVec.ofNat 64 (8 * n)) (len - 8 * n)) % L
  gpr : ∀ r, r ∉ bodyClob → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : Outside base TMP 56 s₀.mem s.mem

theorem readW_outside {base p : Addr} {m m' : Mem} (h : Outside base TMP 56 m m')
    (hp : ∀ i < 8, ofs base (p + BitVec.ofNat 64 i) < TMP ∨
      TMP + 56 ≤ ofs base (p + BitVec.ofNat 64 i)) : m'.readW p 64 = m.readW p 64 :=
  (Mem.readW_congr fun i hi => (h _ (hp i hi)).symm).symm

/-- The loop, from `n₀` words left (`n₀ ≥ 1`), with the remainder of the
bytes above them: the remainder of all `len` bytes. The input's bytes are
outside `TMP`, and readable. -/
theorem scalarLoop_ok {s₀ : State} {base : Addr} (hs : Scr s₀ base)
    (hK : mv s₀.mem base KC 7 = wv kWords) {len n₀ : Nat} (hn : 0 < n₀) (hlen : len < 128)
    (hi : LoopInv base (s₀.gpr .rsi) len s₀ n₀ s₀)
    (hr : ∀ k < n₀, InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .rsi + BitVec.ofNat 64 (8 * k)) 8)
    (hin : ∀ i < len, ofs base (s₀.gpr .rsi + BitVec.ofNat 64 i) < TMP ∨
      TMP + 56 ≤ ofs base (s₀.gpr .rsi + BitVec.ofNat 64 i)) :
    WP isa scalarLoop s₀ fun t =>
      rem t = decodeLE (bytesAt s₀.mem (s₀.gpr .rsi) len) % L ∧
      (∀ r, r ∉ bodyClob → t.gpr r = s₀.gpr r) ∧ t.rd = s₀.rd ∧ t.wr = s₀.wr ∧
      Outside base TMP 56 s₀.mem t.mem := by
  apply WP.loop (fun n s => 0 < n ∧ n ≤ n₀ ∧ LoopInv base (s₀.gpr .rsi) len s₀ n s) (n := n₀)
  · intro n s ⟨hn, hnn, hi⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    have hp : s.gpr .rsi = s₀.gpr .rsi := hi.gpr .rsi (by decide)
    have hss : Scr s base := ⟨(hi.gpr .rdi (by decide)).trans hs.rdi, hi.wr ▸ hs.wr, hs.nowrap⟩
    have hKs : mv s.mem base KC 7 = wv kWords := by
      rw [← hK]; exact hi.mem.mv (Or.inl (by decide)) (by simp only [KC]; omega)
    have hread : InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofNat 64 (8 * k)) 8 := by
      rw [hi.rd, hi.wr, hp]; exact hr k (by omega)
    have hb := hi.bound
    have hv : rem s < L := by rw [hi.value]; exact Nat.mod_lt _ L_pos
    refine WP.mono (scalarWord_ok hss hKs k (by omega) hi.counter hread hv)
      fun t ⟨tb, tz, tv, tg, trd, twr, tm⟩ => ?_
    have hw : s.mem.readW (s₀.gpr .rsi + BitVec.ofNat 64 (8 * k)) 64 =
        s₀.mem.readW (s₀.gpr .rsi + BitVec.ofNat 64 (8 * k)) 64 :=
      readW_outside hi.mem fun i hi' => by
        rw [Offset.add_add]; exact hin (8 * k + i) (by omega)
    have vt : rem t =
        decodeLE (bytesAt s₀.mem (s₀.gpr .rsi + BitVec.ofNat 64 (8 * k)) (len - 8 * k)) % L := by
      rw [tv, hp, hw, hi.value, words_step _ _ len k hb, Nat.mul_comm (2 ^ 64), Nat.add_comm,
        mod_step]
    have it : LoopInv base (s₀.gpr .rsi) len s₀ k t :=
      ⟨by omega, tb, vt, fun r hr => (tg r hr).trans (hi.gpr r hr), trd.trans hi.rd,
        twr.trans hi.wr, hi.mem.trans tm⟩
    by_cases hk0 : k = 0
    · subst hk0
      refine Or.inl ⟨by simp only [eval, tz, decide_true, Option.map_some, Bool.not_true], ?_,
        it.gpr, it.rd, it.wr, it.mem⟩
      simpa only [Nat.mul_zero, BitVec.add_zero, Nat.sub_zero] using vt
    · exact Or.inr ⟨by simp only [eval, tz, decide_eq_false hk0, Option.map_some, Bool.not_false],
        k, by omega, by omega, by omega, it⟩
  · exact ⟨hn, Nat.le_refl _, hi⟩

end VG.Proof.Ed448.X86_64
