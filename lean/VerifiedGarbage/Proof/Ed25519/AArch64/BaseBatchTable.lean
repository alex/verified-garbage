import VerifiedGarbage.Impl.Ed25519.AArch64.BaseMultiply
import VerifiedGarbage.Proof.Ed25519.AArch64.PointPowers

/-!
# Writing a batch's cached powers into the local table

Untrusted. Each constant field is four immediate words stored at a constant
offset of `x0`; the batch is chosen by subtracting each index from the public
counter `x19` and testing the difference for zero.
-/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 VG.Proof.X25519
open VG.Impl.Ed25519 (baseCached)

theorem cachedFieldStore_ok {s : State} {base : Addr} (hs : Scr s base) (v : Spec.X25519.Fe)
    {dst : Nat} (ha : dst % 8 = 0) (ho : dst + 32 ≤ 8192) :
    WP isa (.block (cachedFieldStore v dst)) s fun t =>
      F t.mem base dst = v ∧ TableKeep base dst 32 s t := by
  rw [cachedFieldStore, WP.block_append_iff]
  refine WP.mono (constWords_ok s v) fun t ⟨hv, hk⟩ => ?_
  refine WP.mono (store4_ok (hs.of_keeps hk (by decide)) ⟨ha, ho⟩) fun u hu => ?_
  subst u
  refine ⟨?_, ⟨hk.gpr, hk.rd, hk.wr, hk.sp, ?_⟩⟩
  · rw [F, fe_st4 _ _ (by omega), hv, toFe_self]
  · rw [hk.mem]; exact st4_outside _ _ (by omega) _ _ _ _

theorem cachedPointStore_ok {s : State} {base : Addr} (hs : Scr s base) (q : Spec.Ed25519.Point)
    {dst : Nat} (ha : dst % 8 = 0) (ho : dst + 128 ≤ 8192) :
    WP isa (.block (cachedPointStore q dst)) s fun t =>
      tablePoint t.mem base dst = q ∧ TableKeep base dst 128 s t := by
  rw [cachedPointStore, WP.block_append_iff]
  refine WP.mono (cachedFieldStore_ok hs q.X ha (by omega)) fun a ⟨ax, ka⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (cachedFieldStore_ok (ka.scratch hs) q.Y (dst := dst + 32) (by omega) (by omega))
    fun b ⟨by_, kb⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (cachedFieldStore_ok (kb.scratch (ka.scratch hs)) q.Z (dst := dst + 64)
    (by omega) (by omega)) fun c ⟨cz, kc⟩ => ?_
  refine WP.mono (cachedFieldStore_ok (kc.scratch (kb.scratch (ka.scratch hs))) q.T
    (dst := dst + 96) (by omega) (by omega)) fun t ⟨tt, kt⟩ => ?_
  refine ⟨?_, ((ka.mono (by omega) (by omega)).trans (kb.mono (by omega) (by omega))).trans
    ((kc.mono (by omega) (by omega)).trans (kt.mono (by omega) (by omega)))⟩
  have ex : F t.mem base dst = q.X := by
    rw [Outside_F kt.mem (by omega) (Or.inl (by omega)),
      Outside_F kc.mem (by omega) (Or.inl (by omega)),
      Outside_F kb.mem (by omega) (Or.inl (by omega)), ax]
  have ey : F t.mem base (dst + 32) = q.Y := by
    rw [Outside_F kt.mem (by omega) (Or.inl (by omega)),
      Outside_F kc.mem (by omega) (Or.inl (by omega)), by_]
  have ez : F t.mem base (dst + 64) = q.Z := by
    rw [Outside_F kt.mem (by omega) (Or.inl (by omega)), cz]
  simp only [tablePoint, ex, ey, ez, tt]

theorem baseBatchPrefix_ok {s : State} {base : Addr} (hs : Scr s base) (j n : Nat) (hn : n ≤ 16) :
    WP isa (.block ((List.range n).flatMap fun i =>
      cachedPointStore (baseCached (16 * j + i)) (5376 + 128 * i))) s fun t =>
      (∀ i < n, tablePoint t.mem base (5376 + 128 * i) = baseCached (16 * j + i)) ∧
      TableKeep base 5376 (128 * n) s t := by
  induction n generalizing s with
  | zero =>
    exact WP.block_nil ⟨fun i hi => by omega, ⟨fun _ _ => rfl, rfl, rfl, rfl, Outside.refl _ _ _ _⟩⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, WP.block_append_iff]
    refine WP.mono (ih hs (by omega)) fun t ⟨hv, hk⟩ => ?_
    refine WP.mono (cachedPointStore_ok (hk.scratch hs) (baseCached (16 * j + n))
      (dst := 5376 + 128 * n) (by omega) (by omega)) fun u ⟨hu, ku⟩ => ?_
    refine ⟨fun i hi => ?_, (hk.mono (by omega) (by omega)).trans (ku.mono (by omega) (by omega))⟩
    by_cases h : i < n
    · rw [(TableFrame.table ku.mem).point (by omega) (Or.inl (by omega)) (by omega), hv i h]
    · obtain rfl : i = n := by omega
      exact hu

/-- What a batch's stores leave: its powers in the table, and every register
but `x4`–`x8`, and the memory outside the table, unchanged. -/
structure BatchStored (base : Addr) (j : Nat) (s t : State) : Prop where
  table : ∀ i < 16, tablePoint t.mem base (5376 + 128 * i) = baseCached (16 * j + i)
  gpr : ∀ r, r ∉ [Reg.x4, .x5, .x6, .x7, .x8] → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  mem : Outside base 5376 2048 s.mem t.mem

theorem baseBatchStores_ok {s : State} {base : Addr} (hs : Scr s base) (j : Nat) :
    WP isa (.block (baseBatchStores j)) s fun t =>
      (∀ i < 16, tablePoint t.mem base (5376 + 128 * i) = baseCached (16 * j + i)) ∧
      TableKeep base 5376 2048 s t :=
  baseBatchPrefix_ok hs j 16 (by decide)

theorem batchCmp_ok (s : State) (j k : Nat) (hj : j < 16) (hk : k < 16)
    (hc : s.gpr .x19 = BitVec.ofNat 64 j) :
    WP isa (.block [.subImm .x .x8 .x19 k]) s fun t =>
      eval (.zero .x .x8) t = some (decide (j = k)) ∧ Keeps [.x8] s t := by
  have hz : (BitVec.ofNat 64 j - BitVec.ofNat 64 k == 0) = decide (j = k) := by
    have h : ∀ j < 16, ∀ k < 16, (BitVec.ofNat 64 j - BitVec.ofNat 64 k == 0) = decide (j = k) := by
      decide
    exact h j hj k hk
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    show k < 4096 from by omega, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · simp only [eval, read_x, RegUpd.gpr_write_self, BitVec.setWidth_eq, hc]
    exact congrArg some hz
  · exact RegUpd.gpr_write_of_ne _ _ _ (by simpa only [List.mem_singleton] using hr)

theorem baseBatchTableFrom_ok (ks : List Nat) (hks : ∀ k ∈ ks, k < 16) {s : State} {j : Nat}
    (hj : j ∈ ks) (hj16 : j < 16) (hc : s.gpr .x19 = BitVec.ofNat 64 j) {Q : State → Prop}
    (hq : ∀ s', Keeps [.x8] s s' → WP isa (.block (baseBatchStores j)) s' Q) :
    WP isa (baseBatchTableFrom ks) s Q := by
  induction ks generalizing s with
  | nil => exact absurd hj List.not_mem_nil
  | cons k ks ih =>
    rw [baseBatchTableFrom]
    refine WP.seq (WP.mono (batchCmp_ok s j k hj16 (hks k (by simp)) hc) fun t ⟨tz, kt⟩ => ?_)
    refine WP.ite (decide (j = k)) tz (fun h => ?_) (fun h => ?_)
    · obtain rfl : j = k := of_decide_eq_true h
      exact hq t kt
    · have hne : j ≠ k := of_decide_eq_false h
      have hj' : j ∈ ks := by
        rcases List.mem_cons.mp hj with h | h
        · exact absurd h hne
        · exact h
      exact ih (fun k hk => hks k (List.mem_cons_of_mem _ hk)) hj' ((kt.gpr _ (by decide)).trans hc)
        (fun s' k' => hq s' (kt.trans k'))

theorem baseBatchTable_ok {s : State} {base : Addr} (hs : Scr s base) (j : Nat) (hj : j < 16)
    (hc : s.gpr .x19 = BitVec.ofNat 64 j) :
    WP isa baseBatchTable s (BatchStored base j s) := by
  refine baseBatchTableFrom_ok _ (fun k hk => List.mem_range.mp hk) (List.mem_range.mpr hj) hj hc ?_
  intro s' k
  refine WP.mono (baseBatchStores_ok (hs.of_keeps k (by decide)) j) fun t ⟨tv, kt⟩ => ?_
  refine ⟨tv, fun r hr => ?_, kt.rd.trans k.rd, kt.wr.trans k.wr, kt.sp.trans k.sp,
    by rw [← k.mem]; exact kt.mem⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  rw [kt.gpr r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1]), k.gpr r (by simp [hr.2.2.2.2])]

theorem BatchStored.powersKeep {base : Addr} {j : Nat} {s t : State} (h : BatchStored base j s t) :
    PowersKeep base 5376 2048 s t := by
  have hsub : ∀ x ∈ [Reg.x4, .x5, .x6, .x7, .x8], x ∈ clob := by decide
  exact ⟨fun r _ _ hr => h.gpr r (fun hm => hr (hsub _ hm)), h.rd, h.wr, h.sp, TableFrame.table h.mem⟩

end VG.Proof.Ed25519.AArch64
