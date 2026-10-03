import VerifiedGarbage.Impl.Ed25519.AArch64.PointTable
import VerifiedGarbage.Proof.Ed25519.AArch64.PointLoop

/-! Merged from `Proof.Ed25519.AArch64.PointTable`. -/
section
/-! Point table accesses remain within the caller's scratch argument. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64
open Word64

theorem tableWords_ok {s : State} {base : Addr} (hs : Scr s base) {o : Nat}
    (hp : s.gpr .x8 = off base o) (dst : Nat) (ha : dst % 8 = 0) (ho : o + dst + 32 ≤ 8192) :
    WP isa (.block (tableWords dst)) s fun t =>
      t.mem = st4 s.mem base (o + dst) (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  have w : ∀ d, d + 8 ≤ 8192 → InRegions s.wr (off base d) 8 :=
    fun d hd => ⟨_, hs.wr, Offset.contains_base _ hd (by omega)⟩
  apply WP.of_runBlock
  simp (disch := omega) only [tableWords, runBlock_cons, runStep_some, runBlock_nil, exec, addr,
    Size.bytes, hp, off, Offset.add_add, State.store, read_x, BitVec.setWidth_eq,
    w (o + dst) (by omega), w (o + (dst + 8)) (by omega),
    w (o + (dst + 16)) (by omega), w (o + (dst + 24)) (by omega), ite_eq_left, ite_true,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, True.intro, True.intro, True.intro, True.intro⟩
  simp only [st4, write64_eq_writeW, Nat.add_assoc]

theorem fromTableWords_ok {s : State} {base : Addr} (hs : Scr s base) {o : Nat}
    (hp : s.gpr .x8 = off base o) (src : Nat) (ha : src % 8 = 0) (ho : o + src + 32 ≤ 8192) :
    WP isa (.block (fromTableWords src)) s fun t =>
      val4 (t.gpr .x4) (t.gpr .x5) (t.gpr .x6) (t.gpr .x7) = fe s.mem base (o + src) ∧
      Keeps [.x4, .x5, .x6, .x7] s t := by
  have r : ∀ d, d + 8 ≤ 8192 → InRegions (s.rd ++ s.wr) (off base d) 8 :=
    fun d hd => ⟨_, List.mem_append_right _ hs.wr, Offset.contains_base _ hd (by omega)⟩
  apply WP.of_runBlock
  simp (disch := omega) only [fromTableWords, runBlock_cons, runStep_some, runBlock_nil, exec, addr,
    Size.bytes, State.load, RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    hp, off, Offset.add_add, BitVec.setWidth_eq,
    r (o + src) (by omega), r (o + (src + 8)) (by omega),
    r (o + (src + 16)) (by omega), r (o + (src + 24)) (by omega),
    ite_eq_left, ite_true, ite_false, reduceCtorEq, Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · simp only [fe, word, off, Nat.add_assoc]; rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

structure TableKeep (base : Addr) (o n : Nat) (s t : State) : Prop where
  gpr : ∀ r, r ∉ [Reg.x4, .x5, .x6, .x7] → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  mem : Outside base o n s.mem t.mem

theorem TableKeep.scratch {s t : State} {base : Addr} {o n : Nat}
    (h : TableKeep base o n s t) (hs : Scr s base) : Scr t base :=
  ⟨(h.gpr _ (by decide)).trans hs.x0, h.wr ▸ hs.wr, hs.nowrap⟩

theorem TableKeep.trans {s t u : State} {base : Addr} {o n : Nat}
    (h : TableKeep base o n s t) (k : TableKeep base o n t u) : TableKeep base o n s u :=
  ⟨fun r hr => (k.gpr r hr).trans (h.gpr r hr), k.rd.trans h.rd, k.wr.trans h.wr, k.sp.trans h.sp, h.mem.trans k.mem⟩

theorem TableKeep.mono {s t : State} {base : Addr} {o n o' n' : Nat}
    (h : TableKeep base o n s t) (ho : o' ≤ o) (hn : o + n ≤ o' + n') : TableKeep base o' n' s t :=
  ⟨h.gpr, h.rd, h.wr, h.sp, h.mem.mono ho hn⟩

theorem table_env {base : Addr} {o n : Nat} {m m' : Mem}
    (h : Outside base o n m m') (ho : 768 ≤ o) : env m' base = env m base := by
  funext i
  simp only [env, F]
  rw [h.fe (by simp only [offset]; omega) (by simp only [offset]; omega)]

theorem toTableQuarter_ok {s : State} {base : Addr} (hs : Scr s base) {o : Nat}
    (hp : s.gpr .x8 = off base o) (j : Nat) (hj : j < 4) (ho : o + 128 ≤ 8192) :
    WP isa (.block (loads (64 + 32 * j) .x4 .x5 .x6 .x7 ++ tableWords (32 * j))) s fun t =>
      F t.mem base (o + 32 * j) = env s.mem base ⟨j, by omega⟩ ∧ TableKeep base (o + 32 * j) 32 s t := by
  rw [WP.block_append_iff]
  refine WP.mono (loadsField_ok hs ⟨j, by omega⟩) fun t ⟨hv, hk⟩ => ?_
  refine WP.mono (tableWords_ok (hs.of_keeps hk (by decide))
    ((hk.gpr _ (by decide)).trans hp) (32 * j) (by omega) (by omega)) fun u ⟨hm, hg, hrd, hwr, hsp⟩ => ?_
  refine ⟨?_, ⟨fun r hr => (congrFun hg r).trans (hk.gpr r hr), hrd.trans hk.rd,
    hwr.trans hk.wr, hsp.trans hk.sp, ?_⟩⟩
  · rw [F, hm, fe_st4 _ _ (by omega), hv]
    rfl
  · rw [hm, hk.mem]; exact st4_outside _ _ (by omega) _ _ _ _

theorem toTablePrefix_ok {s : State} {base : Addr} (hs : Scr s base) {o : Nat}
    (hp : s.gpr .x8 = off base o) (hlo : 768 ≤ o) (ho : o + 128 ≤ 8192)
    (n : Nat) (hn : n ≤ 4) :
    WP isa (.block ((List.range n).flatMap fun j =>
      loads (64 + 32 * j) .x4 .x5 .x6 .x7 ++ tableWords (32 * j))) s fun t =>
      (∀ j (hj : j < n), F t.mem base (o + 32 * j) = env s.mem base ⟨j, by omega⟩) ∧
      TableKeep base o (32 * n) s t := by
  induction n generalizing s with
  | zero =>
    exact WP.block_nil ⟨fun j hj => by omega,
      ⟨fun _ _ => rfl, rfl, rfl, rfl, Outside.refl _ _ _ _⟩⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, WP.block_append_iff]
    refine WP.mono (ih hs hp (by omega)) fun t ⟨hv, hk⟩ => ?_
    refine WP.mono (toTableQuarter_ok (hk.scratch hs)
      ((hk.gpr _ (by decide)).trans hp) n (by omega) ho) fun u ⟨hu, ku⟩ => ?_
    refine ⟨fun j hj => ?_, (hk.mono (by omega) (by omega)).trans
      (ku.mono (by omega) (by omega))⟩
    by_cases h : j < n
    · rw [Outside_F ku.mem (by omega) (Or.inl (by omega)), hv j h]
    · have he : j = n := by omega
      subst j
      rw [hu, table_env hk.mem hlo]

def tablePoint (m : Mem) (base : Addr) (o : Nat) : Spec.Ed25519.Point :=
  ⟨F m base o, F m base (o + 32), F m base (o + 64), F m base (o + 96)⟩

theorem pointToTable_ok {s : State} {base : Addr} (hs : Scr s base) {o : Nat}
    (hp : s.gpr .x8 = off base o) (hlo : 768 ≤ o) (ho : o + 128 ≤ 8192) :
    WP isa (.block pointToTable) s fun t =>
      tablePoint t.mem base o = point (env s.mem base) 0 1 2 3 ∧ TableKeep base o 128 s t := by
  refine WP.mono (toTablePrefix_ok hs hp hlo ho 4 (by decide)) fun t ⟨hv, hk⟩ => ?_
  refine ⟨?_, hk⟩
  have h0 := hv 0 (by decide)
  have h1 := hv 1 (by decide)
  have h2 := hv 2 (by decide)
  have h3 := hv 3 (by decide)
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one] at h0 h1
  simp only [tablePoint, point, h0, h1, h2, h3]
  rfl

end VG.Proof.Ed25519.AArch64
end

/-! Merged from `Proof.Ed25519.AArch64.PointTableLoad`. -/
section
/-! Copying point tables back into the arithmetic workspace. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64
theorem fromTableQuarter_ok {s : State} {base : Addr} (hs : Scr s base) {o : Nat}
    (hp : s.gpr .x8 = off base o) (j : Nat) (hj : j < 4) (ho : o + 128 ≤ 8192) :
    WP isa (.block (fromTableWords (32 * j) ++ stores (64 + 32 * j) .x4 .x5 .x6 .x7)) s fun t =>
      env t.mem base ⟨j, by omega⟩ = F s.mem base (o + 32 * j) ∧
      TableKeep base (64 + 32 * j) 32 s t := by
  have _hcap : workSize true = 8192 := rfl
  rw [WP.block_append_iff]
  refine WP.mono (fromTableWords_ok hs hp (32 * j) (by omega) (by omega)) fun t ⟨hv, hk⟩ => ?_
  have ht := hs.of_keeps hk (by decide)
  refine WP.mono (stores_ok ht (by constructor <;> omega) .x4 .x5 .x6 .x7) fun u hu => ?_
  subst u
  refine ⟨?_, ⟨hk.gpr, hk.rd, hk.wr, hk.sp, ?_⟩⟩
  · change F (st4 _ _ _ _ _ _ _) base (64 + 32 * j) = _
    rw [F, fe_st4 _ _ (by omega), hv]
  · rw [hk.mem]; exact st4_outside _ _ (by omega) _ _ _ _

theorem fromTablePrefix_ok {s : State} {base : Addr} (hs : Scr s base) {o : Nat}
    (hp : s.gpr .x8 = off base o) (hlo : 768 ≤ o) (ho : o + 128 ≤ 8192)
    (n : Nat) (hn : n ≤ 4) :
    WP isa (.block ((List.range n).flatMap fun j =>
      fromTableWords (32 * j) ++ stores (64 + 32 * j) .x4 .x5 .x6 .x7)) s fun t =>
      (∀ j (hj : j < n), env t.mem base ⟨j, by omega⟩ = F s.mem base (o + 32 * j)) ∧
      TableKeep base 64 (32 * n) s t := by
  induction n generalizing s with
  | zero =>
    exact WP.block_nil ⟨fun j hj => by omega,
      ⟨fun _ _ => rfl, rfl, rfl, rfl, Outside.refl _ _ _ _⟩⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, WP.block_append_iff]
    refine WP.mono (ih hs hp (by omega)) fun t ⟨hv, hk⟩ => ?_
    refine WP.mono (fromTableQuarter_ok (hk.scratch hs)
      ((hk.gpr _ (by decide)).trans hp) n (by omega) ho) fun u ⟨hu, ku⟩ => ?_
    refine ⟨fun j hj => ?_, (hk.mono (by omega) (by omega)).trans
      (ku.mono (by omega) (by omega))⟩
    by_cases h : j < n
    · have he : env u.mem base ⟨j, by omega⟩ = env t.mem base ⟨j, by omega⟩ :=
        Outside_F ku.mem (by simp only [offset]; omega) (Or.inl (by simp only [offset]; omega))
      rw [he, hv j h]
    · have he : j = n := by omega
      subst j
      rw [hu, Outside_F hk.mem (by omega) (Or.inr (by omega))]

theorem pointFromTable_ok {s : State} {base : Addr} (hs : Scr s base) {o : Nat}
    (hp : s.gpr .x8 = off base o) (hlo : 768 ≤ o) (ho : o + 128 ≤ 8192) :
    WP isa (.block pointFromTable) s fun t =>
      point (env t.mem base) 0 1 2 3 = tablePoint s.mem base o ∧ TableKeep base 64 128 s t := by
  refine WP.mono (fromTablePrefix_ok hs hp hlo ho 4 (by decide)) fun t ⟨hv, hk⟩ => ?_
  refine ⟨?_, hk⟩
  have h0 := hv 0 (by decide)
  have h1 := hv 1 (by decide)
  have h2 := hv 2 (by decide)
  have h3 := hv 3 (by decide)
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one] at h0 h1
  change env t.mem base 0 = _ at h0
  change env t.mem base 1 = _ at h1
  change env t.mem base 2 = _ at h2
  change env t.mem base 3 = _ at h3
  simp only [tablePoint, point, h0, h1, h2, h3]

end VG.Proof.Ed25519.AArch64
end

/-! Public point-table addresses are a base plus a bounded entry offset. -/
namespace VG.Proof.Ed25519.AArch64
open VG VG.AArch64 VG.Impl.Ed25519.AArch64

theorem tableAddr_ok {s : State} {base : Addr} (hp : s.gpr .x0 = base)
    (o j : Nat) (hj : j < 64) (hc : s.gpr .x19 = BitVec.ofNat 64 j) :
    WP isa (.block (tableAddr o)) s fun t =>
      t.gpr .x8 = off base (o + 128 * j) ∧ Keeps [.x8, .x3] s t := by
  have hshift : (BitVec.ofNat 64 j) <<< 7 = BitVec.ofNat 64 (128 * j) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.shiftLeft_eq, BitVec.toNat_ofNat]
    rw [show 2 ^ 7 = 128 from rfl, Nat.mul_comm]
    rw [Nat.mod_eq_of_lt (by omega : j < 2 ^ 64), Nat.mod_eq_of_lt (by omega : 128 * j < 2 ^ 64)]
  apply WP.of_runBlock
  simp only [tableAddr, const64, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    show (7 : Nat) < Size.x.bits from by decide,
    show 16 * 0 < Size.x.bits from by decide, show 16 * 1 < Size.x.bits from by decide,
    show 16 * 2 < Size.x.bits from by decide, show 16 * 3 < Size.x.bits from by decide,
    RegUpd.gpr_write, BitVec.setWidth_eq, hc, hp, hshift,
    ite_true, ite_false, reduceCtorEq, movz_movk64', Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · rw [BitVec.add_comm (BitVec.ofNat 64 (128 * j)), BitVec.add_assoc, ← BitVec.ofNat_add,
      Nat.add_comm (128 * j)]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

end VG.Proof.Ed25519.AArch64
