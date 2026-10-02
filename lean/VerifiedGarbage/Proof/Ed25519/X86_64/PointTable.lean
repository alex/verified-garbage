import VerifiedGarbage.Impl.Ed25519.X86_64.PointTable
import VerifiedGarbage.Proof.Ed25519.X86_64.PointLoop
import VerifiedGarbage.Proof.X25519.X86_64.Setup

/-! Point table accesses remain within the caller's scratch argument. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off fe val4 st4 ea_at ea_sc Keeps Outside F fe_st4 st4_outside)
open VG.Impl.X25519.X86_64 (loads)

theorem tableWords_ok {s : State} {base : Addr} (hs : Scratch s base) {o : Nat}
    (hp : s.gpr .rax = off base o) (dst : Nat) (ho : o + dst + 32 ≤ 8192) :
    WP isa (.block (tableWords dst)) s fun t =>
      t.mem = st4 s.mem base (o + dst) (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have w : ∀ d, d + 8 ≤ 8192 → InRegions s.wr (off base d) 8 :=
    fun d hd => ⟨_, hs.wr, Offset.contains_base _ hd (by omega)⟩
  apply WP.of_runBlock
  simp only [tableWords, runBlock_cons, runStep_some, runBlock_nil, exec, ea_at, hp,
    Offset.add_add, State.store64, w (o + dst) (by omega), w (o + (dst + 8)) (by omega),
    w (o + (dst + 16)) (by omega), w (o + (dst + 24)) (by omega), ite_true,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, trivial, trivial, trivial⟩
  simp only [st4, Nat.add_assoc]

theorem fromTableWords_ok {s : State} {base : Addr} (hs : Scratch s base) {o : Nat}
    (hp : s.gpr .rax = off base o) (src : Nat) (ho : o + src + 32 ≤ 8192) :
    WP isa (.block (fromTableWords src)) s fun t =>
      val4 (t.gpr .r8) (t.gpr .r9) (t.gpr .r10) (t.gpr .r11) = fe s.mem base (o + src) ∧
      Keeps [.r8, .r9, .r10, .r11] s t := by
  have r : ∀ d, d + 8 ≤ 8192 → InRegions (s.rd ++ s.wr) (off base d) 8 :=
    fun d hd => ⟨_, List.mem_append_right _ hs.wr, Offset.contains_base _ hd (by omega)⟩
  apply WP.of_runBlock
  simp only [fromTableWords, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64,
    ea_at, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    hp, Offset.add_add, r (o + src) (by omega), r (o + (src + 8)) (by omega),
    r (o + (src + 16)) (by omega), r (o + (src + 24)) (by omega),
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp only [fe, Proof.X25519.X86_64.word, Nat.add_assoc]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

theorem loadsFieldWide_ok {s : State} {base : Addr} (hs : Scratch s base) (a : Slot) :
    WP isa (.block (loads (offset a) .r8 .r9 .r10 .r11)) s fun t =>
      val4 (t.gpr .r8) (t.gpr .r9) (t.gpr .r10) (t.gpr .r11) = fe s.mem base (offset a) ∧
      Keeps [.r8, .r9, .r10, .r11] s t := by
  have hr (d : Nat) (hd : d + 8 ≤ 8192) : InRegions (s.rd ++ s.wr) (off base d) 8 :=
    ⟨_, List.mem_append_right _ hs.wr, Offset.contains_base _ hd (by omega)⟩
  apply WP.of_runBlock
  simp only [loads, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64,
    ea_sc, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    hs.rdi, hr (offset a) (by simp only [offset]; omega),
    hr (offset a + 8) (by simp only [offset]; omega),
    hr (offset a + 16) (by simp only [offset]; omega),
    hr (offset a + 24) (by simp only [offset]; omega),
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun r h => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  simp only [RegUpd.gpr_setReg, h.1, h.2.1, h.2.2.1, h.2.2.2, ite_false]

structure TableKeep (base : Addr) (o n : Nat) (s t : State) : Prop where
  gpr : ∀ r, r ∉ [Reg.r8, .r9, .r10, .r11] → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mem : Outside base o n s.mem t.mem

theorem TableKeep.scratch {s t : State} {base : Addr} {o n : Nat}
    (h : TableKeep base o n s t) (hs : Scratch s base) : Scratch t base :=
  ⟨(h.gpr _ (by decide)).trans hs.rdi, h.wr ▸ hs.wr, hs.nowrap⟩

theorem TableKeep.trans {s t u : State} {base : Addr} {o n : Nat}
    (h : TableKeep base o n s t) (k : TableKeep base o n t u) : TableKeep base o n s u :=
  ⟨fun r hr => (k.gpr r hr).trans (h.gpr r hr), k.rd.trans h.rd, k.wr.trans h.wr, h.mem.trans k.mem⟩

theorem TableKeep.mono {s t : State} {base : Addr} {o n o' n' : Nat}
    (h : TableKeep base o n s t) (ho : o' ≤ o) (hn : o + n ≤ o' + n') : TableKeep base o' n' s t :=
  ⟨h.gpr, h.rd, h.wr, h.mem.mono ho hn⟩

theorem table_env {base : Addr} {o n : Nat} {m m' : Mem}
    (h : Outside base o n m m') (ho : 768 ≤ o) : env m' base = env m base := by
  funext i
  simp only [env, F]
  rw [h.fe (by simp only [offset]; omega) (by simp only [offset]; omega)]

theorem toTableQuarter_ok {s : State} {base : Addr} (hs : Scratch s base) {o : Nat}
    (hp : s.gpr .rax = off base o) (j : Nat) (hj : j < 4) (ho : o + 128 ≤ 8192) :
    WP isa (.block (loads (64 + 32 * j) .r8 .r9 .r10 .r11 ++ tableWords (32 * j))) s fun t =>
      F t.mem base (o + 32 * j) = env s.mem base ⟨j, by omega⟩ ∧ TableKeep base (o + 32 * j) 32 s t := by
  rw [WP.block_append_iff]
  refine WP.mono (loadsFieldWide_ok hs ⟨j, by omega⟩) fun t ⟨hv, hk⟩ => ?_
  refine WP.mono (tableWords_ok (hs.of_keeps hk (by decide))
    ((hk.1 _ (by decide)).trans hp) (32 * j) (by omega)) fun u ⟨hm, hg, hrd, hwr⟩ => ?_
  refine ⟨?_, ⟨fun r hr => (congrFun hg r).trans (hk.1 r hr), hrd.trans hk.2.2.1,
    hwr.trans hk.2.2.2, ?_⟩⟩
  · rw [F, hm, fe_st4 _ _ (by omega), hv]
    rfl
  · rw [hm, hk.2.1]; exact st4_outside _ _ (by omega) _ _ _ _

theorem toTablePrefix_ok {s : State} {base : Addr} (hs : Scratch s base) {o : Nat}
    (hp : s.gpr .rax = off base o) (hlo : 768 ≤ o) (ho : o + 128 ≤ 8192)
    (n : Nat) (hn : n ≤ 4) :
    WP isa (.block ((List.range n).flatMap fun j =>
      loads (64 + 32 * j) .r8 .r9 .r10 .r11 ++ tableWords (32 * j))) s fun t =>
      (∀ j (hj : j < n), F t.mem base (o + 32 * j) = env s.mem base ⟨j, by omega⟩) ∧
      TableKeep base o (32 * n) s t := by
  induction n generalizing s with
  | zero =>
    exact WP.block_nil ⟨fun j hj => by omega,
      ⟨fun _ _ => rfl, rfl, rfl, Outside.refl _ _ _ _⟩⟩
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

theorem pointToTable_ok {s : State} {base : Addr} (hs : Scratch s base) {o : Nat}
    (hp : s.gpr .rax = off base o) (hlo : 768 ≤ o) (ho : o + 128 ≤ 8192) :
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

end VG.Proof.Ed25519.X86_64

