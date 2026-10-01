import VerifiedGarbage.Impl.Ed25519.AArch64.PointPowers
import VerifiedGarbage.Proof.Ed25519.AArch64.PointTableAddr

/-! Untrusted: constructing bounded tables of exact point doublings. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

/-- Only the field workspace and the specified table can change. -/
def TableFrame (base : Addr) (o n : Nat) (m m' : Mem) : Prop :=
  ∀ p, (ofs base p < 64 ∨ 768 ≤ ofs base p) →
    (ofs base p < o ∨ o + n ≤ ofs base p) → m' p = m p

theorem TableFrame.refl (base : Addr) (o n : Nat) (m : Mem) : TableFrame base o n m m :=
  fun _ _ _ => rfl

theorem TableFrame.trans {base : Addr} {o n : Nat} {m m' m'' : Mem}
    (h : TableFrame base o n m m') (k : TableFrame base o n m' m'') : TableFrame base o n m m'' :=
  fun p hp hq => (k p hp hq).trans (h p hp hq)

theorem TableFrame.mono {base : Addr} {o n o' n' : Nat} {m m' : Mem}
    (h : TableFrame base o n m m') (ho : o' ≤ o) (hn : o + n ≤ o' + n') :
    TableFrame base o' n' m m' := fun p hp hq => h p hp (by omega)

theorem TableFrame.workspace {base : Addr} {o n : Nat} {m m' : Mem}
    (h : Outside base 64 704 m m') : TableFrame base o n m m' := fun p hp _ => h p hp

theorem TableFrame.table {base : Addr} {o n : Nat} {m m' : Mem}
    (h : Outside base o n m m') : TableFrame base o n m m' := fun p _ hp => h p hp

theorem TableFrame.word {base : Addr} {o n : Nat} {m m' : Mem}
    (h : TableFrame base o n m m') {d : Nat} (hd : 768 ≤ d)
    (hsep : d + 8 ≤ o ∨ o + n ≤ d) (hb : d + 8 < 2 ^ 64) :
    word m' base d = word m base d :=
  (Mem.readW_congr fun i hi => (h _ (by rw [ofs_off base (by omega)]; omega)
    (by rw [ofs_off base (by omega)]; omega)).symm).symm

theorem TableFrame.field {base : Addr} {o n : Nat} {m m' : Mem}
    (h : TableFrame base o n m m') {d : Nat} (hd : 768 ≤ d)
    (hsep : d + 32 ≤ o ∨ o + n ≤ d) (hb : d + 32 < 2 ^ 64) :
    F m' base d = F m base d := by
  simp only [F, fe]
  rw [h.word (by omega) (by omega) (by omega), h.word (by omega) (by omega) (by omega),
    h.word (by omega) (by omega) (by omega), h.word (by omega) (by omega) (by omega)]

theorem TableFrame.point {base : Addr} {o n : Nat} {m m' : Mem}
    (h : TableFrame base o n m m') {d : Nat} (hd : 768 ≤ d)
    (hsep : d + 128 ≤ o ∨ o + n ≤ d) (hb : d + 128 < 2 ^ 64) :
    tablePoint m' base d = tablePoint m base d := by
  simp only [tablePoint]
  rw [h.field (by omega) (by omega) (by omega), h.field (by omega) (by omega) (by omega),
    h.field (by omega) (by omega) (by omega), h.field (by omega) (by omega) (by omega)]

theorem workspace_tablePoint {base : Addr} {m m' : Mem}
    (h : Outside base 64 704 m m') {d : Nat} (hd : 768 ≤ d) (hb : d + 128 < 2 ^ 64) :
    tablePoint m' base d = tablePoint m base d := by
  simp only [tablePoint]
  rw [Outside_F h (by omega) (Or.inr (by omega)), Outside_F h (by omega) (Or.inr (by omega)),
    Outside_F h (by omega) (Or.inr (by omega)), Outside_F h (by omega) (Or.inr (by omega))]

structure PowersKeep (base : Addr) (o n : Nat) (s t : State) : Prop where
  gpr : ∀ r, r ≠ .x19 → r ≠ .x1 → r ∉ clob → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  mem : TableFrame base o n s.mem t.mem

theorem PowersKeep.refl (base : Addr) (o n : Nat) (s : State) : PowersKeep base o n s s :=
  ⟨fun _ _ _ _ => rfl, rfl, rfl, rfl, TableFrame.refl _ _ _ _⟩

theorem PowersKeep.scratch {s t : State} {base : Addr} {o n : Nat}
    (h : PowersKeep base o n s t) (hs : Scr s base) : Scr t base :=
  ⟨(h.gpr _ (by decide) (by decide) (by decide)).trans hs.x0, h.wr ▸ hs.wr, hs.nowrap⟩

theorem PowersKeep.trans {s t u : State} {base : Addr} {o n : Nat}
    (h : PowersKeep base o n s t) (k : PowersKeep base o n t u) : PowersKeep base o n s u :=
  ⟨fun r hb hs hc => (k.gpr r hb hs hc).trans (h.gpr r hb hs hc), k.rd.trans h.rd,
    k.wr.trans h.wr, k.sp.trans h.sp, h.mem.trans k.mem⟩

theorem PowersKeep.mono {s t : State} {base : Addr} {o n o' n' : Nat}
    (h : PowersKeep base o n s t) (ho : o' ≤ o) (hn : o + n ≤ o' + n') :
    PowersKeep base o' n' s t := ⟨h.gpr, h.rd, h.wr, h.sp, h.mem.mono ho hn⟩

theorem powersNext_ok (s : State) (j count : Nat) (hj : j < count) (hn : count ≤ 64)
    (hc : s.gpr .x19 = BitVec.ofNat 64 j) :
    WP isa (.block (powersNext count)) s fun t =>
      t.gpr .x19 = BitVec.ofNat 64 (j + 1) ∧ (t.gpr .x8 != 0) = decide (j + 1 ≠ count) ∧
      Keeps [.x8, .x19] s t := by
  have ha : BitVec.ofNat 64 j + BitVec.ofNat 64 1 = BitVec.ofNat 64 (j + 1) := by rw [BitVec.ofNat_add]
  have hz : (BitVec.ofNat 64 (j + 1) - BitVec.ofNat 64 count != 0) = decide (j + 1 ≠ count) := by
    apply Bool.eq_iff_iff.mpr
    simp only [bne_iff_ne, decide_eq_true_eq]
    bv_omega_using [hj, hn]
  apply WP.of_runBlock
  simp only [powersNext, powersLeft, const64, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    show (1 : Nat) < 4096 from by decide,
    show 16 * 0 < Size.x.bits from by decide, show 16 * 1 < Size.x.bits from by decide,
    show 16 * 2 < Size.x.bits from by decide, show 16 * 3 < Size.x.bits from by decide,
    RegUpd.gpr_write, BitVec.setWidth_eq, Size.bits, hc, ha,
    ite_true, ite_false, reduceCtorEq, movz_movk64', hz, Option.some.injEq, exists_eq_left']
  refine ⟨True.intro, True.intro, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

theorem powerBatch_ok {s : State} {base : Addr} (hs : Scr s base)
    (hd : env s.mem base 16 = Spec.Ed25519.d) (batch : Bool) :
    WP isa (powerBatch batch) s fun t =>
      point (env t.mem base) 0 1 2 3 = powerPoint (point (env s.mem base) 0 1 2 3) (powerStride batch) ∧
      (∀ i : Slot, 16 ≤ i.val → env t.mem base i = env s.mem base i) ∧ DoubleKeep base s t := by
  cases batch with
  | true => exact double16_ok hs hd
  | false =>
    refine WP.mono (pointDouble_ok hs hd) fun t ⟨hk, hv, hh⟩ => ?_
    exact ⟨hv, hh, ⟨fun r _ hr => hk.gpr r hr, hk.rd, hk.wr, hk.sp, hk.mem⟩⟩

theorem powersLeft_ok (s : State) (n count : Nat) (hn : n ≤ count) (hc64 : count ≤ 64)
    (hc : s.gpr .x19 = BitVec.ofNat 64 n) :
    WP isa (.block (powersLeft count)) s fun t =>
      (t.gpr .x8 != 0) = decide (n ≠ count) ∧ Keeps [.x8] s t := by
  have hz : (BitVec.ofNat 64 n - BitVec.ofNat 64 count != 0) = decide (n ≠ count) := by
    apply Bool.eq_iff_iff.mpr
    simp only [bne_iff_ne, decide_eq_true_eq]
    bv_omega_using [hn, hc64]
  apply WP.of_runBlock
  simp only [powersLeft, const64, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    show 16 * 0 < Size.x.bits from by decide, show 16 * 1 < Size.x.bits from by decide,
    show 16 * 2 < Size.x.bits from by decide, show 16 * 3 < Size.x.bits from by decide,
    RegUpd.gpr_write, BitVec.setWidth_eq, Size.bits, hc,
    ite_true, ite_false, reduceCtorEq, movz_movk64', hz, Option.some.injEq, exists_eq_left']
  refine ⟨True.intro, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_write, hr, ite_false]

theorem powersBody_ok (batch : Bool) {s : State} {base : Addr} (hs : Scr s base)
    (o j count : Nat) (hlo : 768 ≤ o) (hbound : o + 128 * count ≤ 8192)
    (hj : j < count) (hn : count ≤ 32) (hc : s.gpr .x19 = BitVec.ofNat 64 j)
    (hd : env s.mem base 16 = Spec.Ed25519.d) :
    WP isa (powersBody o count batch) s fun t =>
      t.gpr .x19 = BitVec.ofNat 64 (j + 1) ∧ (t.gpr .x8 != 0) = decide (j + 1 ≠ count) ∧
      tablePoint t.mem base (o + 128 * j) = point (env s.mem base) 0 1 2 3 ∧
      (j + 1 ≠ count → point (env t.mem base) 0 1 2 3 =
        powerPoint (point (env s.mem base) 0 1 2 3) (powerStride batch)) ∧
      (∀ i : Slot, 16 ≤ i.val → env t.mem base i = env s.mem base i) ∧
      PowersKeep base (o + 128 * j) 128 s t := by
  rw [powersBody]
  apply WP.seq
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (tableAddr_ok hs.x0 o j (by omega) hc) fun t ⟨htp, htk⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (pointToTable_ok (hs.of_keeps htk (by decide)) htp (by omega) (by omega))
    fun u ⟨hut, huk⟩ => ?_
  have heu : env u.mem base = env s.mem base := (table_env huk.mem (by omega)).trans
    (congrArg (fun m => env m base) htk.mem)
  have huc : u.gpr .x19 = BitVec.ofNat 64 j := (huk.gpr _ (by decide)).trans ((htk.gpr _ (by decide)).trans hc)
  refine WP.mono (powersNext_ok u j count hj (by omega) huc) fun w ⟨hwc, hwz, hwk⟩ => ?_
  have hus : Scr u base := huk.scratch (hs.of_keeps htk (by decide))
  have hws : Scr w base := hus.of_keeps hwk (by decide)
  have hew : env w.mem base = env s.mem base := by rw [hwk.mem, heu]
  have htw : tablePoint w.mem base (o + 128 * j) = point (env s.mem base) 0 1 2 3 := by
    rw [hwk.mem, hut, htk.mem]
  have kw : PowersKeep base (o + 128 * j) 128 s w := by
    refine ⟨fun r hb hr hc => ?_, hwk.rd.trans (huk.rd.trans htk.rd),
      hwk.wr.trans (huk.wr.trans htk.wr), hwk.sp.trans (huk.sp.trans htk.sp), ?_⟩
    · have ha : r ≠ .x8 := fun he => hc (by subst r; decide)
      have ht : r ∉ [Reg.x8, .x3] := fun hm => hc ((by decide : [Reg.x8, .x3] ⊆ clob) hm)
      have hu : r ∉ [Reg.x4, .x5, .x6, .x7] := fun hm =>
        hc ((by decide : [Reg.x4, .x5, .x6, .x7] ⊆ clob) hm)
      exact (hwk.gpr r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨ha, hb⟩)).trans
        ((huk.gpr r hu).trans (htk.gpr r ht))
    · rw [hwk.mem, ← htk.mem]
      exact TableFrame.table huk.mem
  refine WP.ite (decide (j + 1 ≠ count)) (by simp only [eval, read_x, hwz]) (fun h => ?_) (fun h => ?_)
  · have hne : j + 1 ≠ count := of_decide_eq_true h
    apply WP.seq
    refine WP.mono (powerBatch_ok hws (by rw [hew]; exact hd) batch) fun v ⟨hvp, hvhi, hvk⟩ => ?_
    have hvc : v.gpr .x19 = BitVec.ofNat 64 (j + 1) := (hvk.gpr _ (by decide) (by decide)).trans hwc
    refine WP.mono (powersLeft_ok v (j + 1) count (by omega) (by omega) hvc) fun x ⟨hxz, hxk⟩ => ?_
    refine ⟨(hxk.gpr _ (by decide)).trans hvc, hxz, ?_, fun _ => ?_, ?_, ?_⟩
    · rw [hxk.mem, workspace_tablePoint hvk.mem (by omega) (by omega), htw]
    · rw [hxk.mem, hvp, hew]
    · intro i hi
      rw [hxk.mem, hvhi i hi, hew]
    · refine kw.trans ⟨fun r hb hr hc => ?_, hxk.rd.trans hvk.rd, hxk.wr.trans hvk.wr,
        hxk.sp.trans hvk.sp, ?_⟩
      · have ha : r ≠ .x8 := fun he => hc (by subst r; decide)
        exact (hxk.gpr r (by simp only [List.mem_cons, List.not_mem_nil, or_false]; exact ha)).trans
          (hvk.gpr r hr hc)
      · rw [hxk.mem]; exact TableFrame.workspace hvk.mem
  · have heq : ¬ (j + 1 ≠ count) := of_decide_eq_false h
    exact WP.block_nil ⟨hwc, hwz, htw, fun hne => absurd hne heq, fun i _ => by rw [hew], kw⟩

end VG.Proof.Ed25519.AArch64
