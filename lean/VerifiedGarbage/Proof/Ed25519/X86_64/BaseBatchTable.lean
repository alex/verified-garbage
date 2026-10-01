import VerifiedGarbage.Impl.Ed25519.X86_64.BaseMultiply
import VerifiedGarbage.Proof.Ed25519.X86_64.PointPowers
import VerifiedGarbage.Proof.Ed25519.X86_64.FieldMemory

/-!
# Writing a batch's cached powers into the local table

Untrusted. Each constant field is four immediate words stored through `rax`;
the batch is chosen by comparing the public counter `rbx` with each index.
-/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off F Keeps Outside fe_st4 st4_outside)
open VG.Impl.Ed25519 (baseCached)

theorem baseTableStart_ok {s : State} {base : Addr} (hp : s.gpr .rdi = base) :
    WP isa (.block baseTableStart) s fun t =>
      t.gpr .rax = off base 5376 ∧ Keeps [.rax] s t := by
  apply WP.of_runBlock
  simp only [baseTableStart, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hp, ite_true, ite_false, reduceCtorEq,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨BitVec.add_comm _ _, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

theorem cachedFieldStore_ok {s : State} {base : Addr} (hs : Scratch s base) {o : Nat}
    (hp : s.gpr .rax = off base o) (v : Spec.X25519.Fe) (dst : Nat) (ho : o + dst + 32 ≤ 8192) :
    WP isa (.block (cachedFieldStore v dst)) s fun t =>
      F t.mem base (o + dst) = v ∧ TableKeep base (o + dst) 32 s t := by
  rw [cachedFieldStore, WP.block_append_iff]
  refine WP.mono (constWords_ok s v) fun t ⟨hv, hk⟩ => ?_
  refine WP.mono (tableWords_ok (hs.of_keeps hk (by decide)) ((hk.1 _ (by decide)).trans hp) dst ho)
    fun u ⟨hm, hg, hrd, hwr⟩ => ?_
  refine ⟨?_, ⟨fun r hr => (congrFun hg r).trans (hk.1 r hr), hrd.trans hk.2.2.1,
    hwr.trans hk.2.2.2, ?_⟩⟩
  · rw [F, hm, fe_st4 _ _ (by omega), hv, Proof.X25519.toFe_self]
  · rw [hm, hk.2.1]; exact st4_outside _ _ (by omega) _ _ _ _

theorem cachedPointStore_ok {s : State} {base : Addr} (hs : Scratch s base) {o : Nat}
    (hp : s.gpr .rax = off base o) (q : Spec.Ed25519.Point) (dst : Nat) (ho : o + dst + 128 ≤ 8192) :
    WP isa (.block (cachedPointStore q dst)) s fun t =>
      tablePoint t.mem base (o + dst) = q ∧ TableKeep base (o + dst) 128 s t := by
  rw [cachedPointStore, WP.block_append_iff]
  refine WP.mono (cachedFieldStore_ok hs hp q.X dst (by omega)) fun a ⟨ax, ka⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (cachedFieldStore_ok (ka.scratch hs) ((ka.gpr _ (by decide)).trans hp) q.Y (dst + 32)
    (by omega)) fun b ⟨by_, kb⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (cachedFieldStore_ok (kb.scratch (ka.scratch hs))
    ((kb.gpr _ (by decide)).trans ((ka.gpr _ (by decide)).trans hp)) q.Z (dst + 64)
    (by omega)) fun c ⟨cz, kc⟩ => ?_
  refine WP.mono (cachedFieldStore_ok (kc.scratch (kb.scratch (ka.scratch hs)))
    ((kc.gpr _ (by decide)).trans ((kb.gpr _ (by decide)).trans ((ka.gpr _ (by decide)).trans hp)))
    q.T (dst + 96) (by omega)) fun t ⟨tt, kt⟩ => ?_
  refine ⟨?_, ((ka.mono (by omega) (by omega)).trans (kb.mono (by omega) (by omega))).trans
    ((kc.mono (by omega) (by omega)).trans (kt.mono (by omega) (by omega)))⟩
  have ex : F t.mem base (o + dst) = q.X := by
    rw [Outside_F (d := o + dst) kt.mem (by omega) (Or.inl (by omega)),
      Outside_F (d := o + dst) kc.mem (by omega) (Or.inl (by omega)),
      Outside_F (d := o + dst) kb.mem (by omega) (Or.inl (by omega)), ax]
  have ey : F t.mem base (o + dst + 32) = q.Y := by
    rw [show o + dst + 32 = o + (dst + 32) by omega,
      Outside_F (d := o + (dst + 32)) kt.mem (by omega) (Or.inl (by omega)),
      Outside_F (d := o + (dst + 32)) kc.mem (by omega) (Or.inl (by omega)), by_]
  have ez : F t.mem base (o + dst + 64) = q.Z := by
    rw [show o + dst + 64 = o + (dst + 64) by omega,
      Outside_F (d := o + (dst + 64)) kt.mem (by omega) (Or.inl (by omega)), cz]
  have et : F t.mem base (o + dst + 96) = q.T := by
    rw [show o + dst + 96 = o + (dst + 96) by omega, tt]
  simp only [tablePoint, ex, ey, ez, et]

theorem baseBatchPrefix_ok {s : State} {base : Addr} (hs : Scratch s base)
    (hp : s.gpr .rax = off base 5376) (j n : Nat) (hn : n ≤ 16) :
    WP isa (.block ((List.range n).flatMap fun i =>
      cachedPointStore (baseCached (16 * j + i)) (128 * i))) s fun t =>
      (∀ i < n, tablePoint t.mem base (5376 + 128 * i) = baseCached (16 * j + i)) ∧
      TableKeep base 5376 (128 * n) s t := by
  induction n generalizing s with
  | zero =>
    exact WP.block_nil ⟨fun i hi => by omega, ⟨fun _ _ => rfl, rfl, rfl, Outside.refl _ _ _ _⟩⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, WP.block_append_iff]
    refine WP.mono (ih hs hp (by omega)) fun t ⟨hv, hk⟩ => ?_
    refine WP.mono (cachedPointStore_ok (hk.scratch hs) ((hk.gpr _ (by decide)).trans hp)
      (baseCached (16 * j + n)) (128 * n) (by omega)) fun u ⟨hu, ku⟩ => ?_
    refine ⟨fun i hi => ?_, (hk.mono (by omega) (by omega)).trans (ku.mono (by omega) (by omega))⟩
    by_cases h : i < n
    · rw [(TableFrame.table ku.mem).point (by omega) (Or.inl (by omega)) (by omega), hv i h]
    · obtain rfl : i = n := by omega
      exact hu

/-- What a batch's stores leave: its powers in the table, and every register
but `rax` and `r8`–`r11`, and the memory outside the table, unchanged. -/
structure BatchStored (base : Addr) (j : Nat) (s t : State) : Prop where
  table : ∀ i < 16, tablePoint t.mem base (5376 + 128 * i) = baseCached (16 * j + i)
  gpr : ∀ r, r ∉ [Reg.rax, .r8, .r9, .r10, .r11] → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mem : Outside base 5376 2048 s.mem t.mem

theorem baseBatchStores_ok {s : State} {base : Addr} (hs : Scratch s base) (j : Nat) :
    WP isa (.block (baseBatchStores j)) s (BatchStored base j s) := by
  rw [baseBatchStores, WP.block_append_iff]
  refine WP.mono (baseTableStart_ok hs.rdi) fun a ⟨ap, ka⟩ => ?_
  refine WP.mono (baseBatchPrefix_ok (hs.of_keeps ka (by decide)) ap j 16 (by decide))
    fun t ⟨tv, kt⟩ => ?_
  refine ⟨tv, fun r hr => ?_, kt.rd.trans ka.2.2.1, kt.wr.trans ka.2.2.2, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [kt.gpr r (by simp [hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2]), ka.1 r (by simp [hr.1])]
  · rw [← ka.2.1]; exact kt.mem

theorem batchCmp_ok (s : State) (j k : Nat) (hj : j < 16) (hk : k < 16)
    (hc : s.gpr .rbx = BitVec.ofNat 64 j) :
    WP isa (.block [.alu .cmp .rbx (.imm (BitVec.ofNat 32 k))]) s fun t =>
      t.zf = some (decide (j = k)) ∧ t.gpr = s.gpr ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have he : (BitVec.ofNat 32 k).signExtend 64 = BitVec.ofNat 64 k := by
    have : ∀ k < 16, (BitVec.ofNat 32 k).signExtend 64 = BitVec.ofNat 64 k := by decide
    exact this k hk
  have hz : (BitVec.ofNat 64 j - BitVec.ofNat 64 k == 0) = decide (j = k) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq]
    bv_omega_using [hj, hk]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.zf_arithFlags, hc, he, hz, Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, rfl, rfl, rfl, rfl⟩

theorem baseBatchTableFrom_ok (ks : List Nat) (hks : ∀ k ∈ ks, k < 16) {s : State} {j : Nat}
    (hj : j ∈ ks) (hj16 : j < 16) (hc : s.gpr .rbx = BitVec.ofNat 64 j) {Q : State → Prop}
    (hq : ∀ s', s'.gpr = s.gpr → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      WP isa (.block (baseBatchStores j)) s' Q) :
    WP isa (baseBatchTableFrom ks) s Q := by
  induction ks generalizing s with
  | nil => exact absurd hj List.not_mem_nil
  | cons k ks ih =>
    rw [baseBatchTableFrom]
    refine WP.seq (WP.mono (batchCmp_ok s j k hj16 (hks k (by simp)) hc) fun t ⟨tz, tg, tm, tr, tw⟩ => ?_)
    refine WP.ite (decide (j = k)) (by simp only [eval, tz]) (fun h => ?_) (fun h => ?_)
    · obtain rfl : j = k := of_decide_eq_true h
      exact hq t tg tm tr tw
    · have hne : j ≠ k := of_decide_eq_false h
      have hj' : j ∈ ks := by
        rcases List.mem_cons.mp hj with h | h
        · exact absurd h hne
        · exact h
      exact ih (fun k hk => hks k (List.mem_cons_of_mem _ hk)) hj' (by rw [tg]; exact hc)
        (fun s' g m r w => hq s' (g.trans tg) (m.trans tm) (r.trans tr) (w.trans tw))

theorem baseBatchTable_ok {s : State} {base : Addr} (hs : Scratch s base) (j : Nat) (hj : j < 16)
    (hc : s.gpr .rbx = BitVec.ofNat 64 j) :
    WP isa baseBatchTable s (BatchStored base j s) := by
  refine baseBatchTableFrom_ok _ (fun k hk => List.mem_range.mp hk) (List.mem_range.mpr hj) hj hc ?_
  intro s' g m r w
  have hs' : Scratch s' base := ⟨by rw [g]; exact hs.rdi, by rw [w]; exact hs.wr, hs.nowrap⟩
  refine WP.mono (baseBatchStores_ok hs' j) fun t ht => ?_
  exact ⟨ht.table, fun r' hr => (ht.gpr r' hr).trans (congrFun g r'), ht.rd.trans r, ht.wr.trans w,
    by rw [← m]; exact ht.mem⟩

theorem BatchStored.powersKeep {base : Addr} {j : Nat} {s t : State} (h : BatchStored base j s t) :
    PowersKeep base 5376 2048 s t := by
  have hsub : ∀ x ∈ [Reg.rax, .r8, .r9, .r10, .r11], x ∈ Proof.X25519.X86_64.clob := by decide
  exact ⟨fun r _ _ hr => h.gpr r (fun hm => hr (hsub _ hm)), h.rd, h.wr, TableFrame.table h.mem⟩

end VG.Proof.Ed25519.X86_64
