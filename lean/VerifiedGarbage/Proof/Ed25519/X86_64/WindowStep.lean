import VerifiedGarbage.Proof.Ed25519.X86_64.WindowTables
import VerifiedGarbage.Proof.Ed25519.X86_64.PointLoop
import VerifiedGarbage.Proof.Ed25519.Bytes
import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyInputs
import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyFrame

/-!
# Verification's windows: doublings, digits and table additions

Untrusted. The accumulator in slots 0–3 always represents a point of the
group (`Rep`): four doublings multiply it by 16, and a nonzero digit `v`
adds entry `v - 1` of a table, which represents `[v]X`.
-/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64 VG.Proof.Ed25519 Edwards
open VG.Proof.X25519.X86_64 (off ofs Keeps clob Outside)

/-- What a window may change: the field workspace, and the registers it
computes with. -/
structure WinKeep (base : Addr) (s t : State) : Prop where
  gpr : ∀ r, r ∉ clob → r ≠ .rbx → r ≠ .rsi → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mem : Outside base 64 704 s.mem t.mem

theorem WinKeep.refl (base : Addr) (s : State) : WinKeep base s s :=
  ⟨fun _ _ _ _ => rfl, rfl, rfl, Outside.refl _ _ _ _⟩

theorem WinKeep.trans {base : Addr} {s t u : State} (h : WinKeep base s t) (k : WinKeep base t u) :
    WinKeep base s u :=
  ⟨fun r a b c => (k.gpr r a b c).trans (h.gpr r a b c), k.rd.trans h.rd, k.wr.trans h.wr,
    h.mem.trans k.mem⟩

theorem WinKeep.scratch {base : Addr} {s t : State} (h : WinKeep base s t) (hs : Scratch s base) :
    Scratch t base := ⟨(h.gpr _ (by decide) (by decide) (by decide)).trans hs.rdi, h.wr ▸ hs.wr, hs.nowrap⟩

theorem WinKeep.of_keep {base : Addr} {s t : State} (h : Keep base s t) : WinKeep base s t :=
  ⟨fun r hr _ _ => h.gpr r hr, h.rd, h.wr, h.mem⟩

theorem WinKeep.of_keeps {base : Addr} {s t : State} {rs : List Reg} (h : Keeps rs s t)
    (hrs : ∀ r ∈ rs, r = .rbx ∨ r = .rsi ∨ r ∈ clob) : WinKeep base s t := by
  refine ⟨fun r hr hb hs => h.1 r (fun hm => ?_), h.2.2.1, h.2.2.2, by rw [h.2.1]; exact Outside.refl _ _ _ _⟩
  rcases hrs r hm with h | h | h
  · exact hb h
  · exact hs h
  · exact hr h

theorem WinKeep.of_double {base : Addr} {s t : State} (h : DoubleKeep base s t) : WinKeep base s t :=
  ⟨fun r hr _ hs => h.gpr r hs hr, h.rd, h.wr, h.mem⟩

theorem WinKeep.of_rbx {base : Addr} {s t : State} (h : RbxKeep base s t) : WinKeep base s t :=
  ⟨fun r hr hb _ => h.gpr r hr hb, h.rd, h.wr, h.mem⟩

theorem WinKeep.counter {base : Addr} {s t : State} (h : WinKeep base s t) :
    t.mem.readW (off base 56) 64 = s.mem.readW (off base 56) 64 :=
  h.mem.word (Or.inl (by decide)) (by decide)

/-! ## Four doublings -/

theorem double4_ok {s : State} {base : Addr} {a : EPoint dZ} (hs : Scratch s base)
    (hd : env s.mem base 16 = Spec.Ed25519.d) (ha : Rep (point (env s.mem base) 0 1 2 3) a) :
    WP isa double4 s fun t => Rep (point (env t.mem base) 0 1 2 3) ((16 : Nat) • a) ∧
      (∀ i : Slot, 16 ≤ i.val → env t.mem base i = env s.mem base i) ∧ DoubleKeep base s t := by
  rw [double4]
  refine WP.seq (WP.mono (show WP isa (.block [.mov32 .rsi (.imm 4)]) s
      (fun t => t.gpr .rsi = 4 ∧ Keeps [.rsi] s t) by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, State.setReg32,
      RegUpd.gpr_setReg, ite_true, Option.map_some, Option.some.injEq, exists_eq_left']
    refine ⟨rfl, fun r hr => ?_, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, hr, ite_false]) fun s₁ ⟨c1, k1⟩ => ?_)
  have hs₁ : Scratch s₁ base := hs.of_keeps k1 (by decide)
  have k1d : DoubleKeep base s s₁ := ⟨fun r hr _ => k1.1 r (by simpa using hr), k1.2.2.1, k1.2.2.2,
    by rw [k1.2.1]; exact Outside.refl _ _ _ _⟩
  apply WP.loop (fun (n : Nat) (t : State) => 0 < n ∧ n ≤ 4 ∧ Scratch t base ∧ t.gpr .rsi = BitVec.ofNat 64 n ∧
    Rep (point (env t.mem base) 0 1 2 3) ((2 ^ (4 - n) : Nat) • a) ∧
    (∀ i : Slot, 16 ≤ i.val → env t.mem base i = env s.mem base i) ∧ DoubleKeep base s t) (n := 4)
  · intro n t ⟨hn0, hn4, ht, tc, tv, th, tk⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    refine WP.mono (doubleBody_ok ht k (by omega) tc ((th 16 (by decide)).trans hd))
      fun u ⟨uc, uz, uv, uh, uk⟩ => ?_
    have urep : Rep (point (env u.mem base) 0 1 2 3) ((2 ^ (4 - k) : Nat) • a) := by
      rw [uv, show 4 - k = (4 - (k + 1)) + 1 by omega, pow_succ, mul_nsmul]
      exact tv.double
    have uh' : ∀ i : Slot, 16 ≤ i.val → env u.mem base i = env s.mem base i :=
      fun i h => (uh i h).trans (th i h)
    by_cases hk0 : k = 0
    · subst hk0
      exact Or.inl ⟨by simp only [eval, uz, decide_true, Option.map_some, Bool.not_true], urep, uh',
        tk.trans uk⟩
    · exact Or.inr ⟨by simp only [eval, uz, decide_eq_false hk0, Option.map_some, Bool.not_false],
        k, by omega, by omega, by omega, uk.scratch ht, uc, urep, uh', tk.trans uk⟩
  · refine ⟨by decide, by decide, hs₁, c1, ?_, fun i _ => by rw [k1.2.1], k1d⟩
    rw [show (2 ^ (4 - 4) : Nat) = 1 from rfl, one_nsmul, k1.2.1]; exact ha

/-! ## Digits -/

theorem addImm_ok (s : State) (r : Reg) (n : Nat) (hn : n < 2 ^ 31) :
    WP isa (.block [.alu .add r (.imm (BitVec.ofNat 32 n))]) s fun t =>
      t.gpr r = off (s.gpr r) n ∧ Keeps [r] s t := by
  have he : (BitVec.ofNat 32 n).signExtend 64 = BitVec.ofNat 64 n := by
    rw [BitVec.signExtend_eq_setWidth_of_msb_false (by
      rw [BitVec.msb_eq_false_iff_two_mul_lt, BitVec.toNat_ofNat]; omega)]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, he,
    Option.bind_some, Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg_self]
  refine ⟨trivial, fun k hk => ?_, rfl, rfl, rfl⟩
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    show k ≠ r by simpa only [List.mem_singleton] using hk, ite_false]

theorem digitByte_ok {s : State} {base : Addr} (hs : Scratch s base) (ptr add : Nat)
    (hptr : ptr + 8 ≤ 8192) (hadd : add < 2 ^ 31) {P : Addr} (hp : s.mem.readW (off base ptr) 64 = P)
    (i : Nat) (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 i)
    (hr : InRegions (s.rd ++ s.wr) (off (off P add) i) 1) :
    WP isa (.block (digitByte ptr add)) s fun t =>
      t.gpr .rbx = (s.mem (off (off P add) i)).setWidth 64 ∧ Keeps [.rsi, .rax, .rbx] s t := by
  rw [digitByte, show ([.mov .rsi (.mem (Impl.X25519.X86_64.sc ptr)),
      .alu .add .rsi (.imm (BitVec.ofNat 32 add)), .mov .rax (.mem (Impl.X25519.X86_64.sc 56)),
      .movzx8 .rbx { base := .rsi, index := some .rax }] : List Instr) =
    [.mov .rsi (.mem (Impl.X25519.X86_64.sc ptr))] ++ ([.alu .add .rsi (.imm (BitVec.ofNat 32 add))] ++
      ([.mov .rax (.mem (Impl.X25519.X86_64.sc 56))] ++
        [.movzx8 .rbx { base := .rsi, index := some .rax }])) from rfl, WP.block_append_iff]
  refine WP.mono (loadPointer_ok hs .rsi ptr hptr) fun a ⟨ap, ka⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (addImm_ok a .rsi add hadd) fun b ⟨bp, kb⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (loadPointer_ok ((hs.of_keeps ka (by decide)).of_keeps kb (by decide)) .rax 56
    (by decide)) fun c ⟨cp, kc⟩ => ?_
  have hm : c.mem = s.mem := kc.2.1.trans (kb.2.1.trans ka.2.1)
  have hrd : c.rd ++ c.wr = s.rd ++ s.wr := by
    rw [kc.2.2.1, kc.2.2.2, kb.2.2.1, kb.2.2.2, ka.2.2.1, ka.2.2.2]
  have crsi : c.gpr .rsi = off P add := by rw [kc.1 _ (by decide), bp, ap, hp]
  have crax : c.gpr .rax = BitVec.ofNat 64 i := by rw [cp, kb.2.1, ka.2.1, hc]
  have hea : c.ea { base := .rsi, index := some .rax } = off (off P add) i := by
    simp only [State.ea, crsi, crax]
    rw [BitVec.mul_one, show BitVec.ofInt 64 (0 : Int) = BitVec.ofNat 64 0 from rfl, BitVec.add_zero]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, hea, State.load8, hrd, hr, hm,
    ite_true, Option.map_some, Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg_self]
  refine ⟨trivial, fun r hr => ?_, hm, kc.2.2.1.trans (kb.2.2.1.trans ka.2.2.1),
    kc.2.2.2.trans (kb.2.2.2.trans ka.2.2.2)⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  rw [RegUpd.gpr_setReg_of_ne _ _ hr.2.2, kc.1 r (by simp [hr.2.1]), kb.1 r (by simp [hr.1]),
    ka.1 r (by simp [hr.1])]

private theorem high_nibble : ∀ b : BitVec 8,
    b.setWidth 64 >>> 4 = BitVec.ofNat 64 (b.toNat / 16) := by decide

private theorem low_nibble : ∀ b : BitVec 8,
    b.setWidth 64 &&& (15 : BitVec 32).signExtend 64 = BitVec.ofNat 64 (b.toNat % 16) := by decide

private theorem nibble_zero : ∀ n < 16, (BitVec.ofNat 64 n == 0) = decide (n = 0) := by decide

theorem digitHigh_ok {s : State} {base : Addr} (hs : Scratch s base) (ptr add : Nat)
    (hptr : ptr + 8 ≤ 8192) (hadd : add < 2 ^ 31) {P : Addr} (hp : s.mem.readW (off base ptr) 64 = P)
    (i : Nat) (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 i)
    (hr : InRegions (s.rd ++ s.wr) (off (off P add) i) 1) :
    WP isa (.block (digitHigh ptr add)) s fun t =>
      t.gpr .rbx = BitVec.ofNat 64 ((s.mem (off (off P add) i)).toNat / 16) ∧
      t.zf = some (decide ((s.mem (off (off P add) i)).toNat / 16 = 0)) ∧
      Keeps [.rsi, .rax, .rbx] s t := by
  rw [digitHigh, WP.block_append_iff]
  refine WP.mono (digitByte_ok hs ptr add hptr hadd hp i hc hr) fun a ⟨av, ka⟩ => ?_
  have hlt : (s.mem (off (off P add) i)).toNat / 16 < 16 := by
    have := (s.mem (off (off P add) i)).isLt; omega
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execShift, execAlu,
    RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.gpr_arithFlags, RegUpd.zf_arithFlags, av,
    show 1 ≤ 4 ∧ 4 ≤ 63 by decide, and_self, ite_true, high_nibble, BitVec.and_self, nibble_zero _ hlt,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, fun r hr => ?_, ka.2.1, ka.2.2.1, ka.2.2.2⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.gpr_arithFlags, hr.2.2, ite_false]
  exact ka.1 r (by simp [hr.1, hr.2.1, hr.2.2])

theorem digitLow_ok {s : State} {base : Addr} (hs : Scratch s base) (ptr add : Nat)
    (hptr : ptr + 8 ≤ 8192) (hadd : add < 2 ^ 31) {P : Addr} (hp : s.mem.readW (off base ptr) 64 = P)
    (i : Nat) (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 i)
    (hr : InRegions (s.rd ++ s.wr) (off (off P add) i) 1) :
    WP isa (.block (digitLow ptr add)) s fun t =>
      t.gpr .rbx = BitVec.ofNat 64 ((s.mem (off (off P add) i)).toNat % 16) ∧
      t.zf = some (decide ((s.mem (off (off P add) i)).toNat % 16 = 0)) ∧
      Keeps [.rsi, .rax, .rbx] s t := by
  rw [digitLow, WP.block_append_iff]
  refine WP.mono (digitByte_ok hs ptr add hptr hadd hp i hc hr) fun a ⟨av, ka⟩ => ?_
  have hlt : (s.mem (off (off P add) i)).toNat % 16 < 16 := Nat.mod_lt _ (by decide)
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.zf_setReg, RegUpd.zf_arithFlags, av, low_nibble,
    nibble_zero _ hlt, ite_true, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, fun r hr => ?_, ka.2.1, ka.2.2.1, ka.2.2.2⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.2.2, ite_false]
  exact ka.1 r (by simp [hr.1, hr.2.1, hr.2.2])

/-! ## Adding a table entry -/

theorem tableEntryAdd_ok {add : List Instr} {f : Spec.Ed25519.Point → Spec.Ed25519.Point}
    (hadd : AddSpec add f) {s : State} {base : Addr} (hs : Scratch s base) {o j : Nat}
    (hlo : 768 ≤ o) (hhi : o + 128 * j + 128 ≤ 8192) (hj : j < 64)
    (hc : s.gpr .rbx = BitVec.ofNat 64 j) (q : Spec.Ed25519.Point)
    (hq : tablePoint s.mem base (o + 128 * j) = f q) (hd : env s.mem base 16 = Spec.Ed25519.d) :
    WP isa (.block (tableAddr o ++ pointFromTableQ ++ add)) s fun t => Keep base s t ∧
      point (env t.mem base) 0 1 2 3 = Spec.Ed25519.pointAdd (point (env s.mem base) 0 1 2 3) q ∧
      env t.mem base 16 = env s.mem base 16 := by
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (tableAddr_ok hs.rdi o j hj hc) fun a ⟨pa, ka⟩ => ?_
  have kae : Keep base s a := Keep.of_keeps ka (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (pointFromTableQ_ok (hs.of_keep kae) pa (by omega) (by omega)) fun b ⟨pb, kb⟩ => ?_
  have kbe := Keep.of_tableQ kb
  have b_low : ∀ i : Slot, i.val < 4 → env b.mem base i = env s.mem base i := by
    intro i hi
    change Proof.X25519.X86_64.F b.mem base (offset i) = Proof.X25519.X86_64.F s.mem base (offset i)
    rw [Outside_F kb.mem (by simp only [offset]; omega) (Or.inl (by simp only [offset]; omega)), ka.2.1]
  have b_high : ∀ i : Slot, 8 ≤ i.val → env b.mem base i = env s.mem base i := by
    intro i hi
    change Proof.X25519.X86_64.F b.mem base (offset i) = Proof.X25519.X86_64.F s.mem base (offset i)
    rw [Outside_F kb.mem (by simp only [offset]; omega) (Or.inr (by simp only [offset]; omega)), ka.2.1]
  have bp : point (env b.mem base) 0 1 2 3 = point (env s.mem base) 0 1 2 3 := by
    simp only [point, b_low 0 (by decide), b_low 1 (by decide), b_low 2 (by decide), b_low 3 (by decide)]
  have bq : point (env b.mem base) 4 5 6 7 = f q := by rw [pb, ka.2.1, hq]
  refine WP.mono (hadd b base q (hs.of_keep (kae.trans kbe)) (by rw [b_high 16 (by decide)]; exact hd) bq)
    fun t ⟨kt, tp, th⟩ => ?_
  exact ⟨(kae.trans kbe).trans kt, by rw [tp, bp], by rw [th 16 (by decide), b_high 16 (by decide)]⟩

/-- Entries `j < 15` of the table at byte `o` are `f` of representatives of `[j + 1]X`. -/
def TableOf (f : Spec.Ed25519.Point → Spec.Ed25519.Point) (m : Mem) (base : Addr) (o : Nat)
    (X : EPoint dZ) : Prop :=
  ∀ j < 15, ∃ q, tablePoint m base (o + 128 * j) = f q ∧ Rep q ((j + 1) • X)

theorem addDigit_ok {add : List Instr} {f : Spec.Ed25519.Point → Spec.Ed25519.Point}
    (hadd : AddSpec add f) {s : State} {base : Addr} (hs : Scratch s base) {o : Nat}
    (hlo : 768 ≤ o) (hhi : o + 1920 ≤ 8192) {X a : EPoint dZ} (htab : TableOf f s.mem base o X)
    (v : Nat) (hv : v < 16) (hc : s.gpr .rbx = BitVec.ofNat 64 v) (hz : s.zf = some (decide (v = 0)))
    (hd : env s.mem base 16 = Spec.Ed25519.d) (ha : Rep (point (env s.mem base) 0 1 2 3) a) :
    WP isa (addDigit o add) s fun t => Rep (point (env t.mem base) 0 1 2 3) (a + v • X) ∧
      env t.mem base 16 = env s.mem base 16 ∧ WinKeep base s t := by
  rw [addDigit]
  refine WP.ite (!decide (v = 0)) (by simp only [eval, hz, Option.map_some]) (fun h => ?_) (fun h => ?_)
  · have hv0 : v ≠ 0 := by simpa using h
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hv0
    rw [List.append_assoc, List.append_assoc, WP.block_append_iff]
    refine WP.mono (accumulateDec_ok s n hc) fun b ⟨bc, kb⟩ => ?_
    obtain ⟨q, hq, hr⟩ := htab n (by omega)
    rw [← List.append_assoc]
    refine WP.mono (tableEntryAdd_ok hadd (hs.of_keeps kb (by decide)) hlo (by omega) (by omega) bc q
      (by rw [kb.2.1]; exact hq) (by rw [kb.2.1]; exact hd)) fun t ⟨kt, tp, td⟩ => ?_
    refine ⟨?_, by rw [td, kb.2.1], (WinKeep.of_keeps kb (by decide)).trans (WinKeep.of_keep kt)⟩
    rw [tp, kb.2.1]
    exact pointAdd_rep ha hr
  · have hv0 : v = 0 := by simpa using h
    subst hv0
    refine WP.block_nil ⟨by rw [zero_smul, add_zero]; exact ha, rfl, WinKeep.refl _ _⟩

/-! ## Windows -/

/-- What verification's windows keep: the tables, the inputs and where they are. -/
structure WinCtx (base kp sp : Addr) (A : EPoint dZ) (s : State) : Prop where
  scratch : Scratch s base
  kHeader : s.mem.readW (off base 7952) 64 = kp
  sHeader : s.mem.readW (off base 7944) 64 = sp
  kRead : ∀ i < 64, InRegions (s.rd ++ s.wr) (off kp i) 1
  sRead : ∀ i < 32, InRegions (s.rd ++ s.wr) (off (off sp 32) i) 1
  kFar : ∀ i < 64, 8192 ≤ ofs base (off kp i)
  sFar : ∀ i < 32, 8192 ≤ ofs base (off (off sp 32) i)
  aTab : TableOf id s.mem base 5376 A
  bTab : TableOf cache s.mem base 2048 (-baseAff)

theorem win_tablePoint {base : Addr} {m m' : Mem} (h : Outside base 56 712 m m') {d : Nat}
    (hd : 768 ≤ d) (hb : d + 128 ≤ 8192) : tablePoint m' base d = tablePoint m base d := by
  simp only [tablePoint]
  rw [Outside_F h (by omega) (Or.inr (by omega)), Outside_F h (by omega) (Or.inr (by omega)),
    Outside_F h (by omega) (Or.inr (by omega)), Outside_F h (by omega) (Or.inr (by omega))]

theorem TableOf.of_win {f : Spec.Ed25519.Point → Spec.Ed25519.Point} {base : Addr} {m m' : Mem}
    {o : Nat} {X : EPoint dZ} (h : TableOf f m base o X) (k : Outside base 56 712 m m')
    (ho : 768 ≤ o) (hb : o + 1920 ≤ 8192) : TableOf f m' base o X := by
  intro j hj
  obtain ⟨q, hq, hr⟩ := h j hj
  exact ⟨q, by rw [win_tablePoint k (by omega) (by omega)]; exact hq, hr⟩

theorem Outside.widen {base : Addr} {m m' : Mem} (h : Outside base 64 704 m m') :
    Outside base 56 712 m m' := h.mono (by decide) (by decide)

theorem WinKeep.header {base : Addr} {s t : State} (h : WinKeep base s t) {d : Nat} (hd : 768 ≤ d)
    (hb : d + 8 ≤ 8192) : t.mem.readW (off base d) 64 = s.mem.readW (off base d) 64 :=
  h.mem.word (Or.inr (by omega)) (by omega)

theorem WinCtx.of_keep {base kp sp : Addr} {A : EPoint dZ} {s t : State} (h : WinCtx base kp sp A s)
    (k : WinKeep base s t) : WinCtx base kp sp A t := by
  refine ⟨k.scratch h.scratch, (k.header (by decide) (by decide)).trans h.kHeader,
    (k.header (by decide) (by decide)).trans h.sHeader, ?_, ?_, h.kFar, h.sFar,
    h.aTab.of_win (Outside.widen k.mem) (by decide) (by decide), h.bTab.of_win (Outside.widen k.mem) (by decide) (by decide)⟩
  · intro i hi; rw [k.rd, k.wr]; exact h.kRead i hi
  · intro i hi; rw [k.rd, k.wr]; exact h.sRead i hi

theorem WinCtx.byteK {base kp sp : Addr} {A : EPoint dZ} {s t : State} (h : WinCtx base kp sp A s)
    (k : WinKeep base s t) {i : Nat} (hi : i < 64) : t.mem (off kp i) = s.mem (off kp i) :=
  k.mem _ (by have := h.kFar i hi; omega)

theorem WinCtx.byteS {base kp sp : Addr} {A : EPoint dZ} {s t : State} (h : WinCtx base kp sp A s)
    (k : WinKeep base s t) {i : Nat} (hi : i < 32) :
    t.mem (off (off sp 32) i) = s.mem (off (off sp 32) i) :=
  k.mem _ (by have := h.sFar i hi; omega)

theorem off_zero (p : Addr) : off p 0 = p := by
  simp only [off, BitVec.add_zero]

/-- A digit's code, with its value `v`, from any state the window has reached. -/
def DigitSpec (base : Addr) (s : State) (digit : List Instr) (v : Nat) : Prop :=
  ∀ t, WinKeep base s t → WP isa (.block digit) t fun u =>
    u.gpr .rbx = BitVec.ofNat 64 v ∧ u.zf = some (decide (v = 0)) ∧ Keeps [.rsi, .rax, .rbx] t u

theorem windowA_ok {s : State} {base kp sp : Addr} {A a : EPoint dZ} (h : WinCtx base kp sp A s)
    (hd : env s.mem base 16 = Spec.Ed25519.d) (ha : Rep (point (env s.mem base) 0 1 2 3) a)
    {digit : List Instr} {v : Nat} (hv : v < 16) (hdig : DigitSpec base s digit v) :
    WP isa (windowA digit) s fun t => Rep (point (env t.mem base) 0 1 2 3) ((16 : Nat) • a + v • A) ∧
      env t.mem base 16 = Spec.Ed25519.d ∧ WinKeep base s t := by
  rw [windowA]
  refine WP.seq (WP.mono (double4_ok h.scratch hd ha) fun b ⟨br, bh, bk⟩ => ?_)
  have kb := WinKeep.of_double bk
  refine WP.seq (WP.mono (hdig b kb) fun c ⟨cv, cz, kc⟩ => ?_)
  have kc' : WinKeep base b c := WinKeep.of_keeps kc (by decide)
  have kbc := kb.trans kc'
  refine WP.mono (addDigit_ok (a := (16 : Nat) • a) pointAdd_spec (kbc.scratch h.scratch) (by decide) (by decide)
    (h.aTab.of_win (Outside.widen kbc.mem) (by decide) (by decide)) v hv cv cz
    (by rw [kc.2.1, bh 16 (by decide)]; exact hd) (by rw [kc.2.1]; exact br)) fun t ⟨tr, td, kt⟩ => ?_
  exact ⟨tr, by rw [td, kc.2.1, bh 16 (by decide)]; exact hd, kbc.trans kt⟩

theorem windowAB_ok {s : State} {base kp sp : Addr} {A a : EPoint dZ} (h : WinCtx base kp sp A s)
    (hd : env s.mem base 16 = Spec.Ed25519.d) (ha : Rep (point (env s.mem base) 0 1 2 3) a)
    {digitA digitB : List Instr} {vA vB : Nat} (hvA : vA < 16) (hvB : vB < 16)
    (hdA : DigitSpec base s digitA vA) (hdB : DigitSpec base s digitB vB) :
    WP isa (windowAB digitA digitB) s fun t =>
      Rep (point (env t.mem base) 0 1 2 3) ((16 : Nat) • a + vA • A + vB • (-baseAff)) ∧
      env t.mem base 16 = Spec.Ed25519.d ∧ WinKeep base s t := by
  rw [windowAB]
  refine WP.seq (WP.mono (windowA_ok h hd ha hvA hdA) fun b ⟨br, bd, kb⟩ => ?_)
  refine WP.seq (WP.mono (hdB b kb) fun c ⟨cv, cz, kc⟩ => ?_)
  have kc' : WinKeep base b c := WinKeep.of_keeps kc (by decide)
  have kbc := kb.trans kc'
  refine WP.mono (addDigit_ok (a := (16 : Nat) • a + vA • A) pointAddCached_spec (kbc.scratch h.scratch)
    (by decide) (by decide) (h.bTab.of_win (Outside.widen kbc.mem) (by decide) (by decide)) vB hvB cv cz
    (by rw [kc.2.1]; exact bd) (by rw [kc.2.1]; exact br)) fun t ⟨tr, td, kt⟩ => ?_
  exact ⟨tr, by rw [td, kc.2.1]; exact bd, kbc.trans kt⟩

end VG.Proof.Ed25519.X86_64
