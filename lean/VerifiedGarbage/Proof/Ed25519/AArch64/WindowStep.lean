import VerifiedGarbage.Impl.Ed25519.AArch64.VerifyWindow
import VerifiedGarbage.Proof.Ed25519.AArch64.BaseAccumulate
import VerifiedGarbage.Proof.Ed25519.AArch64.PointLoop
import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyInputs
import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyFrame
import VerifiedGarbage.Proof.Ed25519.Group.Double

/-!
# Verification's windows: doublings, digits and table additions

Untrusted. The accumulator in slots 0–3 always represents a point of the
group: four doublings multiply it by 16 (`dbl-2008-hwcd`, which reads only
`X : Y : Z`, `RepP`), and a nonzero digit `v` adds entry `v - 1` of a table,
which represents `[v]X`.
-/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 VG.Proof.Ed25519 Edwards

/-- What a window may change: the field workspace, and the registers it
computes with. -/
structure WinKeep (base : Addr) (s t : State) : Prop where
  gpr : ∀ r, r ∉ clob → r ≠ .x19 → r ≠ .x1 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  mem : Outside base 64 704 s.mem t.mem

theorem WinKeep.refl (base : Addr) (s : State) : WinKeep base s s :=
  ⟨fun _ _ _ _ => rfl, rfl, rfl, rfl, Outside.refl _ _ _ _⟩

theorem WinKeep.trans {base : Addr} {s t u : State} (h : WinKeep base s t) (k : WinKeep base t u) :
    WinKeep base s u :=
  ⟨fun r a b c => (k.gpr r a b c).trans (h.gpr r a b c), k.rd.trans h.rd, k.wr.trans h.wr,
    k.sp.trans h.sp, h.mem.trans k.mem⟩

theorem WinKeep.scratch {base : Addr} {s t : State} (h : WinKeep base s t) (hs : Scr s base) :
    Scr t base := ⟨(h.gpr _ (by decide) (by decide) (by decide)).trans hs.x0, h.wr ▸ hs.wr, hs.nowrap⟩

theorem WinKeep.of_keep {base : Addr} {s t : State} (h : Keep base s t) : WinKeep base s t :=
  ⟨fun r hr _ _ => h.gpr r hr, h.rd, h.wr, h.sp, h.mem⟩

theorem WinKeep.of_keeps {base : Addr} {s t : State} {rs : List Reg} (h : Keeps rs s t)
    (hrs : ∀ r ∈ rs, r = .x19 ∨ r = .x1 ∨ r ∈ clob) : WinKeep base s t := by
  refine ⟨fun r hr hb hs => h.gpr r (fun hm => ?_), h.rd, h.wr, h.sp,
    by rw [h.mem]; exact Outside.refl _ _ _ _⟩
  rcases hrs r hm with h | h | h
  · exact hb h
  · exact hs h
  · exact hr h

theorem WinKeep.of_double {base : Addr} {s t : State} (h : DoubleKeep base s t) : WinKeep base s t :=
  ⟨fun r hr _ hs => h.gpr r hs hr, h.rd, h.wr, h.sp, h.mem⟩

theorem WinKeep.of_counter {base : Addr} {s t : State} (h : CounterKeep base s t) : WinKeep base s t :=
  ⟨fun r hr hb _ => h.gpr r hr hb, h.rd, h.wr, h.sp, h.mem⟩

theorem WinKeep.counter {base : Addr} {s t : State} (h : WinKeep base s t) :
    t.mem.readW (off base 56) 64 = s.mem.readW (off base 56) 64 :=
  h.mem.word (Or.inl (by decide)) (by decide)

/-! ## Small blocks -/

theorem movzW_ok (s : State) (r : Reg) (imm : BitVec 16) :
    WP isa (.block [.movz .w r imm 0]) s fun t => t.gpr r = imm.setWidth 64 ∧ Keeps [r] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec,
    show 16 * 0 < Size.w.bits from by decide, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r' hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · rw [RegUpd.gpr_write_self, Nat.mul_zero, BitVec.shiftLeft_zero, BitVec.setWidth_setWidth (by decide)]
  · exact RegUpd.gpr_write_of_ne _ _ _ (by simpa only [List.mem_singleton] using hr)

/-! ## Four doublings -/

theorem dblOps_eval (e : Env) :
    point (evalOps (dblOps true) e) 0 1 2 3 = dblPoint (point e 0 1 2 3) ∧
    evalOps (dblOps false) e 0 = (dblPoint (point e 0 1 2 3)).X ∧
    evalOps (dblOps false) e 1 = (dblPoint (point e 0 1 2 3)).Y ∧
    evalOps (dblOps false) e 2 = (dblPoint (point e 0 1 2 3)).Z :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem dbl_ok {s : State} {base : Addr} (hs : Scr s base) (t : Bool) {a : EPoint dZ}
    (ha : RepP (point (env s.mem base) 0 1 2 3) a) :
    WP isa (.block (fieldCode (dblOps t))) s fun u => Keep base s u ∧
      RepP (point (env u.mem base) 0 1 2 3) (a + a) ∧
      (t = true → Rep (point (env u.mem base) 0 1 2 3) (a + a)) ∧
      ∀ i : Slot, 16 ≤ i.val → env u.mem base i = env s.mem base i := by
  refine WP.mono (fieldCode_ok _ hs) fun u ⟨ku, vu⟩ => ?_
  have hr := dblPoint_rep ha
  refine ⟨ku, ?_, fun ht => ?_, fun i hi => by
    rw [vu]; exact point_ops_high _ (by cases t <;> decide) _ i hi⟩
  · rw [vu]
    cases t
    · obtain ⟨_, ex, ey, ez⟩ := dblOps_eval (env s.mem base)
      refine ⟨?_, ?_, ?_⟩
      · show toZ (evalOps _ _ 2) ≠ 0
        rw [ez]; exact hr.z
      · show toZ (evalOps _ _ 0) = _ * toZ (evalOps _ _ 2)
        rw [ex, ez]; exact hr.x
      · show toZ (evalOps _ _ 1) = _ * toZ (evalOps _ _ 2)
        rw [ey, ez]; exact hr.y
    · rw [(dblOps_eval _).1]; exact hr.proj
  · subst ht
    rw [vu, (dblOps_eval _).1]; exact hr

theorem doubleWindow_ok {s : State} {base : Addr} {a : EPoint dZ} (hs : Scr s base)
    (ha : RepP (point (env s.mem base) 0 1 2 3) a) :
    WP isa doubleWindow s fun t => Rep (point (env t.mem base) 0 1 2 3) ((16 : Nat) • a) ∧
      (∀ i : Slot, 16 ≤ i.val → env t.mem base i = env s.mem base i) ∧ DoubleKeep base s t := by
  rw [doubleWindow]
  refine WP.seq (WP.mono (movzW_ok s .x1 3) fun s₁ ⟨c1, k1⟩ => ?_)
  have hs₁ : Scr s₁ base := hs.of_keeps k1 (by decide)
  have k1d : DoubleKeep base s s₁ := ⟨fun r hr _ => k1.gpr r (by simpa using hr), k1.rd, k1.wr, k1.sp,
    by rw [k1.mem]; exact Outside.refl _ _ _ _⟩
  have keepD {x y : State} (k : Keep base x y) : DoubleKeep base x y :=
    ⟨fun r _ hc => k.gpr r hc, k.rd, k.wr, k.sp, k.mem⟩
  refine WP.seq ?_
  apply WP.loop (fun (n : Nat) (t : State) => 0 < n ∧ n ≤ 3 ∧ Scr t base ∧
    t.gpr .x1 = BitVec.ofNat 64 n ∧ RepP (point (env t.mem base) 0 1 2 3) ((2 ^ (3 - n) : Nat) • a) ∧
    (∀ i : Slot, 16 ≤ i.val → env t.mem base i = env s.mem base i) ∧ DoubleKeep base s t) (n := 3)
  · intro n t ⟨hn0, hn3, ht, tc, tv, th, tk⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    rw [WP.block_append_iff]
    refine WP.mono (dbl_ok ht false tv) fun u ⟨ku, uv, _, uh⟩ => ?_
    refine WP.mono (doubleDec_ok u k ((ku.gpr _ (by decide)).trans tc)) fun w ⟨wc, kw⟩ => ?_
    have wrep : RepP (point (env w.mem base) 0 1 2 3) ((2 ^ (3 - k) : Nat) • a) := by
      rw [kw.mem, show 3 - k = (3 - (k + 1)) + 1 by omega, pow_succ, mul_nsmul, two_nsmul]
      exact uv
    have wh : ∀ i : Slot, 16 ≤ i.val → env w.mem base i = env s.mem base i :=
      fun i h => by rw [kw.mem, uh i h, th i h]
    have wk : DoubleKeep base s w := tk.trans ((keepD ku).trans
      ⟨fun r hr _ => kw.gpr r (by simpa using hr), kw.rd, kw.wr, kw.sp,
        by rw [kw.mem]; exact Outside.refl _ _ _ _⟩)
    have hk : k < 16 := by omega
    by_cases hk0 : k = 0
    · subst hk0
      refine Or.inl ⟨by simp only [eval, read_x, wc, point_counter_nonzero 0 (by decide),
        show decide ((0 : Nat) ≠ 0) = false from rfl], ?_⟩
      refine WP.mono (dbl_ok (wk.scratch hs) true wrep) fun v ⟨kv, _, vr, vh⟩ => ?_
      refine ⟨?_, fun i h => (vh i h).trans (wh i h), wk.trans (keepD kv)⟩
      rw [show (16 : Nat) = 2 ^ (3 - 0) * 2 by rfl, mul_nsmul, two_nsmul]
      exact vr rfl
    · exact Or.inr ⟨by simp only [eval, read_x, wc, point_counter_nonzero k hk, decide_eq_true hk0],
        k, by omega, by omega, by omega, wk.scratch hs, wc, wrep, wh, wk⟩
  · refine ⟨by decide, by decide, hs₁, c1, ?_, fun i _ => by rw [k1.mem], k1d⟩
    rw [show (2 ^ (3 - 3) : Nat) = 1 from rfl, one_nsmul, k1.mem]; exact ha

/-! ## Digits -/

private theorem byte_ext : ∀ b : BitVec 8, (b.setWidth 32).setWidth 64 = BitVec.ofNat 64 b.toNat := by
  decide

private theorem high_nibble : ∀ b : BitVec 8,
    BitVec.ofNat 64 b.toNat >>> 4 = BitVec.ofNat 64 (b.toNat / 16) := by decide

private theorem low_nibble : ∀ b : BitVec 8,
    BitVec.ofNat 64 b.toNat <<< 60 >>> 60 = BitVec.ofNat 64 (b.toNat % 16) := by decide

theorem digitByte_ok {s : State} {base : Addr} (hs : Scr s base) (ptr add : Nat)
    (hpa : ptr % 8 = 0) (hptr : ptr + 8 ≤ 8192) (hadd : add < 4096) {P : Addr}
    (hp : s.mem.readW (off base ptr) 64 = P)
    (i : Nat) (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 i)
    (hr : InRegions (s.rd ++ s.wr) (off (off P add) i) 1) :
    WP isa (.block (digitByte ptr add)) s fun t =>
      t.gpr .x19 = BitVec.ofNat 64 (s.mem (off (off P add) i)).toNat ∧ Keeps [.x2, .x8, .x19] s t := by
  rw [digitByte, show ([ld .x2 ptr, ld .x8 56, .add .x .x8 .x2 .x8, .ldrb .x19 .x8 add] : List Instr) =
      [ld .x2 ptr] ++ ([ld .x8 56] ++ [.add .x .x8 .x2 .x8, .ldrb .x19 .x8 add]) from rfl,
    WP.block_append_iff]
  refine WP.mono (loadPointer_ok hs .x2 ptr hpa hptr) fun a ⟨ap, ka⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (loadPointer_ok (hs.of_keeps ka (by decide)) .x8 56 (by decide) (by decide))
    fun b ⟨bp, kb⟩ => ?_
  have hm : b.mem = s.mem := kb.mem.trans ka.mem
  have hrd : b.rd ++ b.wr = s.rd ++ s.wr := by rw [kb.rd, kb.wr, ka.rd, ka.wr]
  have b2 : b.gpr .x2 = P := by rw [kb.gpr _ (by decide), ap, hp]
  have b8 : b.gpr .x8 = BitVec.ofNat 64 i := by rw [bp, ka.mem, hc]
  have hea : P + BitVec.ofNat 64 i + BitVec.ofNat 64 add = off (off P add) i := by
    simp only [off]
    rw [BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 i), ← BitVec.add_assoc]
  have hok : add % 1 = 0 ∧ add < 4096 * 1 := ⟨Nat.mod_one _, by omega⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, addr, State.load,
    RegUpd.gpr_write, RegUpd.rd_write, RegUpd.wr_write, RegUpd.mem_write, BitVec.setWidth_eq,
    b2, b8, hea, hok, hrd, hm, hr, read_byte, byte_ext, and_self,
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ⟨fun r hr => ?_, hm, by simp only [RegUpd.rd_write, kb.rd, ka.rd],
    by simp only [RegUpd.wr_write, kb.wr, ka.wr], by simp only [RegUpd.sp_write, kb.sp, ka.sp]⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.2.1, hr.2.2, ite_false]
  rw [kb.gpr r (by simp [hr.2.1]), ka.gpr r (by simp [hr.1])]

theorem shiftR4_ok (s : State) (v : Nat) (hc : s.gpr .x19 = BitVec.ofNat 64 v) :
    WP isa (.block [.lsr .x .x19 .x19 4]) s fun t =>
      t.gpr .x19 = BitVec.ofNat 64 v >>> 4 ∧ Keeps [.x19] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    show (4 : Nat) < Size.x.bits from by decide, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨by rw [RegUpd.gpr_write_self, BitVec.setWidth_eq, hc], ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  exact RegUpd.gpr_write_of_ne _ _ _ (by simpa only [List.mem_singleton] using hr)

theorem shiftLR60_ok (s : State) (v : Nat) (hc : s.gpr .x19 = BitVec.ofNat 64 v) :
    WP isa (.block [.lsl .x .x19 .x19 60, .lsr .x .x19 .x19 60]) s fun t =>
      t.gpr .x19 = BitVec.ofNat 64 v <<< 60 >>> 60 ∧ Keeps [.x19] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, BitVec.setWidth_eq,
    show (60 : Nat) < Size.x.bits from by decide, ite_true, Option.some.injEq, exists_eq_left',
    RegUpd.gpr_write_self, hc]
  refine ⟨trivial, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  have h : r ≠ .x19 := by simpa only [List.mem_singleton] using hr
  rw [RegUpd.gpr_write_of_ne _ _ _ h, RegUpd.gpr_write_of_ne _ _ _ h]

theorem digitHigh_ok {s : State} {base : Addr} (hs : Scr s base) (ptr add : Nat)
    (hpa : ptr % 8 = 0) (hptr : ptr + 8 ≤ 8192) (hadd : add < 4096) {P : Addr}
    (hp : s.mem.readW (off base ptr) 64 = P)
    (i : Nat) (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 i)
    (hr : InRegions (s.rd ++ s.wr) (off (off P add) i) 1) :
    WP isa (.block (digitHigh ptr add)) s fun t =>
      t.gpr .x19 = BitVec.ofNat 64 ((s.mem (off (off P add) i)).toNat / 16) ∧
      Keeps [.x2, .x8, .x19] s t := by
  rw [digitHigh, WP.block_append_iff]
  refine WP.mono (digitByte_ok hs ptr add hpa hptr hadd hp i hc hr) fun a ⟨av, ka⟩ => ?_
  refine WP.mono (shiftR4_ok a _ av) fun t ⟨tv, kt⟩ => ?_
  exact ⟨tv.trans (high_nibble _), ka.trans (kt.mono (by decide))⟩

theorem digitLow_ok {s : State} {base : Addr} (hs : Scr s base) (ptr add : Nat)
    (hpa : ptr % 8 = 0) (hptr : ptr + 8 ≤ 8192) (hadd : add < 4096) {P : Addr}
    (hp : s.mem.readW (off base ptr) 64 = P)
    (i : Nat) (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 i)
    (hr : InRegions (s.rd ++ s.wr) (off (off P add) i) 1) :
    WP isa (.block (digitLow ptr add)) s fun t =>
      t.gpr .x19 = BitVec.ofNat 64 ((s.mem (off (off P add) i)).toNat % 16) ∧
      Keeps [.x2, .x8, .x19] s t := by
  rw [digitLow, WP.block_append_iff]
  refine WP.mono (digitByte_ok hs ptr add hpa hptr hadd hp i hc hr) fun a ⟨av, ka⟩ => ?_
  refine WP.mono (shiftLR60_ok a _ av) fun t ⟨tv, kt⟩ => ?_
  exact ⟨tv.trans (low_nibble _), ka.trans (kt.mono (by decide))⟩

/-! ## Adding a table entry -/

/-- `p` agrees with `r`: entirely if `full`, and otherwise on `X : Y : Z`. -/
def Agrees : Bool → Spec.Ed25519.Point → Spec.Ed25519.Point → Prop
  | true, p, r => p = r
  | false, p, r => p.X = r.X ∧ p.Y = r.Y ∧ p.Z = r.Z

/-- `p` represents `a` (`Rep`) if `full`, and otherwise its `X : Y : Z` do (`RepP`). -/
def RepIf : Bool → Spec.Ed25519.Point → EPoint dZ → Prop
  | true, p, a => Rep p a
  | false, p, a => RepP p a

theorem RepIf.of_rep {full : Bool} {p : Spec.Ed25519.Point} {a : EPoint dZ} (h : Rep p a) :
    RepIf full p a := by
  cases full
  · exact h.proj
  · exact h

theorem RepIf.proj {full : Bool} {p : Spec.Ed25519.Point} {a : EPoint dZ} (h : RepIf full p a) :
    RepP p a := by
  cases full
  · exact h
  · exact Rep.proj h

theorem RepIf.of_agrees {full : Bool} {p r : Spec.Ed25519.Point} {a : EPoint dZ} (h : Rep r a)
    (hp : Agrees full p r) : RepIf full p a := by
  cases full
  · obtain ⟨hx, hy, hz⟩ := hp
    exact ⟨by rw [hz]; exact h.z, by rw [hx, hz]; exact h.x, by rw [hy, hz]; exact h.y⟩
  · have e : p = r := hp
    subst e
    exact h

/-- `add` adds `q` to the accumulator in slots 0–3 when slots 4–7 hold `f q`: all of the
sum if `full`, and otherwise its `X : Y : Z`. -/
def AddSpec (add : List Instr) (f : Spec.Ed25519.Point → Spec.Ed25519.Point) (full : Bool) : Prop :=
  ∀ (s : State) (base : Addr) (q : Spec.Ed25519.Point), Scr s base →
    env s.mem base 16 = Spec.Ed25519.d → point (env s.mem base) 4 5 6 7 = f q →
    WP isa (.block add) s fun t => Keep base s t ∧
      Agrees full (point (env t.mem base) 0 1 2 3)
        (Spec.Ed25519.pointAdd (point (env s.mem base) 0 1 2 3) q) ∧
      ∀ i : Slot, 16 ≤ i.val → env t.mem base i = env s.mem base i

theorem pointAddCached_spec : AddSpec pointAddCached cache true := fun _ _ q hs _ hq =>
  pointAddCached_ok hs q hq

theorem cachedP_eval (e : Env) :
    evalOps pointAddCachedOps.dropLast e 0 = evalOps pointAddCachedOps e 0 ∧
    evalOps pointAddCachedOps.dropLast e 1 = evalOps pointAddCachedOps e 1 ∧
    evalOps pointAddCachedOps.dropLast e 2 = evalOps pointAddCachedOps e 2 := ⟨rfl, rfl, rfl⟩

theorem pointAddCachedP_spec : AddSpec pointAddCachedP cache false := fun s base q hs _ hq => by
  refine WP.mono (fieldCode_ok _ hs) fun t ⟨kt, vt⟩ => ⟨kt, ?_, fun i hi => by
    rw [vt]; exact point_ops_high _ (by decide) _ i hi⟩
  have e := pointAddCached_eval (env s.mem base) q hq
  obtain ⟨e0, e1, e2⟩ := cachedP_eval (env s.mem base)
  refine ⟨?_, ?_, ?_⟩
  · show env t.mem base 0 = _
    rw [vt, e0]; exact congrArg Spec.Ed25519.Point.X e
  · show env t.mem base 1 = _
    rw [vt, e1]; exact congrArg Spec.Ed25519.Point.Y e
  · show env t.mem base 2 = _
    rw [vt, e2]; exact congrArg Spec.Ed25519.Point.Z e

theorem tableEntryAdd_ok {add : List Instr} {f : Spec.Ed25519.Point → Spec.Ed25519.Point}
    {full : Bool} (hadd : AddSpec add f full) {s : State} {base : Addr} (hs : Scr s base) {o j : Nat}
    (hlo : 768 ≤ o) (hhi : o + 128 * j + 128 ≤ 8192) (hj : j < 64)
    (hc : s.gpr .x19 = BitVec.ofNat 64 j) (q : Spec.Ed25519.Point)
    (hq : tablePoint s.mem base (o + 128 * j) = f q) (hd : env s.mem base 16 = Spec.Ed25519.d) :
    WP isa (.block (tableAddr o ++ pointFromTableQ ++ add)) s fun t => Keep base s t ∧
      Agrees full (point (env t.mem base) 0 1 2 3)
        (Spec.Ed25519.pointAdd (point (env s.mem base) 0 1 2 3) q) ∧
      env t.mem base 16 = env s.mem base 16 := by
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (tableAddr_ok hs.x0 o j hj hc) fun a ⟨pa, ka⟩ => ?_
  have kae : Keep base s a := Keep.of_keeps ka (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (pointFromTableQ_ok (kae.scr hs) pa (by omega) (by omega)) fun b ⟨pb, kb⟩ => ?_
  have kbe := Keep.of_tableQ kb
  have o := tableQ_other kb
  have bp : point (env b.mem base) 0 1 2 3 = point (env s.mem base) 0 1 2 3 := by
    simp only [point, o 0 (by decide), o 1 (by decide), o 2 (by decide), o 3 (by decide), ka.mem]
  have bq : point (env b.mem base) 4 5 6 7 = f q := by rw [pb, ka.mem, hq]
  have bd : env b.mem base 16 = env s.mem base 16 := by rw [o 16 (by decide), ka.mem]
  refine WP.mono (hadd b base q ((kae.trans kbe).scr hs) (bd.trans hd) bq) fun t ⟨kt, tp, th⟩ => ?_
  rw [bp] at tp
  exact ⟨(kae.trans kbe).trans kt, tp, by rw [th 16 (by decide), bd]⟩

/-- Entries `j < 15` of the table at byte `o` are `f` of representatives of `[j + 1]X`. -/
def TableOf (f : Spec.Ed25519.Point → Spec.Ed25519.Point) (m : Mem) (base : Addr) (o : Nat)
    (X : EPoint dZ) : Prop :=
  ∀ j < 15, ∃ q, tablePoint m base (o + 128 * j) = f q ∧ Rep q ((j + 1) • X)

theorem addDigit_ok {add : List Instr} {f : Spec.Ed25519.Point → Spec.Ed25519.Point} {full : Bool}
    (hadd : AddSpec add f full) {s : State} {base : Addr} (hs : Scr s base) {o : Nat}
    (hlo : 768 ≤ o) (hhi : o + 1920 ≤ 8192) {X a : EPoint dZ} (htab : TableOf f s.mem base o X)
    (v : Nat) (hv : v < 16) (hc : s.gpr .x19 = BitVec.ofNat 64 v)
    (hd : env s.mem base 16 = Spec.Ed25519.d) (ha : Rep (point (env s.mem base) 0 1 2 3) a) :
    WP isa (addDigit o add) s fun t => RepIf full (point (env t.mem base) 0 1 2 3) (a + v • X) ∧
      env t.mem base 16 = env s.mem base 16 ∧ WinKeep base s t := by
  rw [addDigit]
  refine WP.ite (decide (v ≠ 0)) (by simp only [eval, read_x, hc, point_counter_nonzero v hv])
    (fun h => ?_) (fun h => ?_)
  · have hv0 : v ≠ 0 := of_decide_eq_true h
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hv0
    rw [List.append_assoc, List.append_assoc, WP.block_append_iff]
    refine WP.mono (accumulateDec_ok s n hc) fun b ⟨bc, kb⟩ => ?_
    obtain ⟨q, hq, hr⟩ := htab n (by omega)
    rw [← List.append_assoc]
    refine WP.mono (tableEntryAdd_ok hadd (hs.of_keeps kb (by decide)) hlo (by omega) (by omega) bc q
      (by rw [kb.mem]; exact hq) (by rw [kb.mem]; exact hd)) fun t ⟨kt, tp, td⟩ => ?_
    refine ⟨?_, by rw [td, kb.mem], (WinKeep.of_keeps kb (by decide)).trans (WinKeep.of_keep kt)⟩
    rw [kb.mem] at tp
    exact RepIf.of_agrees (pointAdd_rep ha hr) tp
  · have hv0 : v = 0 := by simpa using h
    subst hv0
    exact WP.block_nil ⟨by rw [zero_smul, add_zero]; exact RepIf.of_rep ha, rfl, WinKeep.refl _ _⟩

/-! ## Windows -/

/-- What verification's windows keep: the tables, the inputs and where they are. -/
structure WinCtx (base kp sp : Addr) (A : EPoint dZ) (s : State) : Prop where
  scratch : Scr s base
  kHeader : s.mem.readW (off base 7952) 64 = kp
  sHeader : s.mem.readW (off base 7944) 64 = sp
  kRead : ∀ i < 64, InRegions (s.rd ++ s.wr) (off kp i) 1
  sRead : ∀ i < 32, InRegions (s.rd ++ s.wr) (off (off sp 32) i) 1
  kFar : ∀ i < 64, 8192 ≤ ofs base (off kp i)
  sFar : ∀ i < 32, 8192 ≤ ofs base (off (off sp 32) i)
  aTab : TableOf cache s.mem base 5376 A
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
    h.aTab.of_win (Outside.widen k.mem) (by decide) (by decide),
    h.bTab.of_win (Outside.widen k.mem) (by decide) (by decide)⟩
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
    u.gpr .x19 = BitVec.ofNat 64 v ∧ Keeps [.x2, .x8, .x19] t u

theorem DigitSpec.of_keep {base : Addr} {s t : State} {digit : List Instr} {v : Nat}
    (h : DigitSpec base s digit v) (k : WinKeep base s t) : DigitSpec base t digit v :=
  fun u ku => h u (k.trans ku)

theorem windowWith_ok {s : State} {base kp sp : Addr} {A a : EPoint dZ} (h : WinCtx base kp sp A s)
    (hd : env s.mem base 16 = Spec.Ed25519.d) (ha : RepP (point (env s.mem base) 0 1 2 3) a)
    {digit add : List Instr} {full : Bool} (hadd : AddSpec add cache full) {v : Nat} (hv : v < 16)
    (hdig : DigitSpec base s digit v) :
    WP isa (windowWith digit add) s fun t =>
      RepIf full (point (env t.mem base) 0 1 2 3) ((16 : Nat) • a + v • A) ∧
      env t.mem base 16 = Spec.Ed25519.d ∧ WinKeep base s t := by
  rw [windowWith]
  refine WP.seq (WP.mono (doubleWindow_ok h.scratch ha) fun b ⟨br, bh, bk⟩ => ?_)
  have kb := WinKeep.of_double bk
  refine WP.seq (WP.mono (hdig b kb) fun c ⟨cv, kc⟩ => ?_)
  have kc' : WinKeep base b c := WinKeep.of_keeps kc (by decide)
  have kbc := kb.trans kc'
  refine WP.mono (addDigit_ok (a := (16 : Nat) • a) hadd (kbc.scratch h.scratch) (by decide)
    (by decide) (h.aTab.of_win (Outside.widen kbc.mem) (by decide) (by decide)) v hv cv
    (by rw [kc.mem, bh 16 (by decide)]; exact hd) (by rw [kc.mem]; exact br)) fun t ⟨tr, td, kt⟩ => ?_
  exact ⟨tr, by rw [td, kc.mem, bh 16 (by decide)]; exact hd, kbc.trans kt⟩

theorem windowA_ok {s : State} {base kp sp : Addr} {A a : EPoint dZ} (h : WinCtx base kp sp A s)
    (hd : env s.mem base 16 = Spec.Ed25519.d) (ha : RepP (point (env s.mem base) 0 1 2 3) a)
    {digit : List Instr} {v : Nat} (hv : v < 16) (hdig : DigitSpec base s digit v) :
    WP isa (windowA digit) s fun t => RepP (point (env t.mem base) 0 1 2 3) ((16 : Nat) • a + v • A) ∧
      env t.mem base 16 = Spec.Ed25519.d ∧ WinKeep base s t :=
  windowWith_ok h hd ha pointAddCachedP_spec hv hdig

theorem windowAB_ok {s : State} {base kp sp : Addr} {A a : EPoint dZ} (h : WinCtx base kp sp A s)
    (hd : env s.mem base 16 = Spec.Ed25519.d) (ha : RepP (point (env s.mem base) 0 1 2 3) a)
    {digitA digitB : List Instr} {vA vB : Nat} (hvA : vA < 16) (hvB : vB < 16)
    (hdA : DigitSpec base s digitA vA) (hdB : DigitSpec base s digitB vB) :
    WP isa (windowAB digitA digitB) s fun t =>
      RepP (point (env t.mem base) 0 1 2 3) ((16 : Nat) • a + vA • A + vB • (-baseAff)) ∧
      env t.mem base 16 = Spec.Ed25519.d ∧ WinKeep base s t := by
  rw [windowAB]
  refine WP.seq (WP.mono (windowWith_ok h hd ha pointAddCached_spec hvA hdA) fun b ⟨br, bd, kb⟩ => ?_)
  refine WP.seq (WP.mono (hdB b kb) fun c ⟨cv, kc⟩ => ?_)
  have kc' : WinKeep base b c := WinKeep.of_keeps kc (by decide)
  have kbc := kb.trans kc'
  refine WP.mono (addDigit_ok (a := (16 : Nat) • a + vA • A) pointAddCachedP_spec
    (kbc.scratch h.scratch) (by decide) (by decide)
    (h.bTab.of_win (Outside.widen kbc.mem) (by decide) (by decide)) vB hvB cv
    (by rw [kc.mem]; exact bd) (by rw [kc.mem]; exact br)) fun t ⟨tr, td, kt⟩ => ?_
  exact ⟨tr, by rw [td, kc.mem]; exact bd, kbc.trans kt⟩

end VG.Proof.Ed25519.AArch64
