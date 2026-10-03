import VerifiedGarbage.Impl.Ed25519.AArch64.Verify
import VerifiedGarbage.Proof.Ed25519.AArch64.PointMulBatch
import VerifiedGarbage.Proof.Ed25519.AArch64.PointAccumulate
import VerifiedGarbage.Impl.Ed25519.AArch64.BaseMultiply
import VerifiedGarbage.Proof.Ed25519.AArch64.PointPowers
import VerifiedGarbage.Proof.Ed25519.WindowConstants
import VerifiedGarbage.Proof.Ed25519.AArch64.WindowStep
import VerifiedGarbage.Proof.Ed25519.AArch64.WindowLoop
import VerifiedGarbage.Proof.Ed25519.AArch64.PointEqual
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! Merged from `Proof.Ed25519.AArch64.WindowTables`. -/
section
/-! Merged from `Proof.Ed25519.AArch64.VerifyTables`. -/
section
/-! Store and reload verification points beyond the multiplication workspace. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64


theorem tableIndexZero_ok (s : State) :
    WP isa (.block [.movz .w .x19 0 0]) s fun t => t.gpr .x19 = 0 ∧ Keeps [.x19] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec,
    show 16 * 0 < Size.w.bits from by decide, ite_true,
    Option.some.injEq, exists_eq_left']
  refine ⟨rfl, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  exact RegUpd.gpr_write_of_ne _ _ _ (by simpa only [List.mem_singleton] using hr)

theorem pointTableWrite_ok {s : State} {base : Addr} (hs : Scr s base)
    (o : Nat) (hlo : 768 ≤ o) (ho : o + 128 ≤ 8192) :
    WP isa (.block (pointTableWrite o)) s fun t => PowersKeep base o 128 s t ∧
      tablePoint t.mem base o = point (env s.mem base) 0 1 2 3 ∧ env t.mem base = env s.mem base := by
  rw [pointTableWrite, List.append_assoc, WP.block_append_iff]
  refine WP.mono (tableIndexZero_ok s) fun a ⟨az, ka⟩ => ?_
  have kap : PowersKeep base o 128 s a := PowersKeep.of_keeps ka (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (tableAddr_ok (kap.scratch hs).x0 o 0 (by decide) az) fun b ⟨bp, kb⟩ => ?_
  simp only [Nat.mul_zero, Nat.add_zero] at bp
  have kbp : PowersKeep base o 128 a b := PowersKeep.of_keeps kb (by decide)
  refine WP.mono (pointToTable_ok ((kap.trans kbp).scratch hs) bp hlo ho) fun t ⟨tp, kt⟩ => ?_
  have ktp : PowersKeep base o 128 b t := ⟨fun r _ _ hr => kt.gpr r (fun hm => hr (by
    exact (show ∀ r ∈ [Reg.x4, .x5, .x6, .x7], r ∈ clob by decide) r hm)),
    kt.rd, kt.wr, kt.sp, TableFrame.table kt.mem⟩
  refine ⟨(kap.trans kbp).trans ktp, ?_, ?_⟩
  · rw [tp, kb.mem, ka.mem]
  · rw [table_env kt.mem hlo, kb.mem, ka.mem]

theorem pointTableRead_ok {s : State} {base : Addr} (hs : Scr s base)
    (o : Nat) (hlo : 768 ≤ o) (ho : o + 128 ≤ 8192) :
    WP isa (.block (pointTableRead o)) s fun t => CounterKeep base s t ∧
      point (env t.mem base) 0 1 2 3 = tablePoint s.mem base o ∧
      ∀ i : Slot, 4 ≤ i.val → env t.mem base i = env s.mem base i := by
  rw [pointTableRead, List.append_assoc, WP.block_append_iff]
  refine WP.mono (tableIndexZero_ok s) fun a ⟨az, ka⟩ => ?_
  have kar : CounterKeep base s a := CounterKeep.of_keeps ka (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (tableAddr_ok (kar.scr hs).x0 o 0 (by decide) az) fun b ⟨bp, kb⟩ => ?_
  simp only [Nat.mul_zero, Nat.add_zero] at bp
  have kbr : CounterKeep base a b := CounterKeep.of_keeps kb (by decide)
  refine WP.mono (pointFromTable_ok ((kar.trans kbr).scr hs) bp hlo ho) fun t ⟨tp, kt⟩ => ?_
  refine ⟨(kar.trans kbr).trans (CounterKeep.of_keep (Keep.of_table kt)), ?_, ?_⟩
  · rw [tp, kb.mem, ka.mem]
  · intro i hi
    rw [tableLoad_high kt i hi, kb.mem, ka.mem]

end VG.Proof.Ed25519.AArch64
end

/-! Merged from `Proof.Ed25519.AArch64.BaseBatchTable`. -/
section
/-!
# Writing a batch's cached powers into the local table

Each constant field is four immediate words stored at a constant offset of
`x0`; the batch is chosen by subtracting each index from the public counter
`x19` and testing the difference for zero.
-/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 VG.Proof.X25519

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

end VG.Proof.Ed25519.AArch64
end

/-!
# Verification's tables: `[1]A … [15]A` and cached `-[1]B … -[15]B`

The table of multiples of `A` is built by repeated addition of `A`, which
stays in slots 4–7, each entry representing its multiple (`Rep`); the table of
negated multiples of `B` is stored from constants.
-/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 VG.Proof.Ed25519 Edwards
open VG.Impl.Ed25519 (negBaseCached)
open Fin.CommRing

/-! ## Cached `-[i]B` -/

theorem bTablePrefix_ok {s : State} {base : Addr} (hs : Scr s base) (n : Nat) (hn : n ≤ 15) :
    WP isa (.block ((List.range n).flatMap fun i => cachedPointStore (negBaseCached i) (2048 + 128 * i))) s
      fun t => (∀ i < n, tablePoint t.mem base (2048 + 128 * i) = negBaseCached i) ∧
        TableKeep base 2048 (128 * n) s t := by
  induction n generalizing s with
  | zero =>
    exact WP.block_nil ⟨fun i hi => by omega, ⟨fun _ _ => rfl, rfl, rfl, rfl, Outside.refl _ _ _ _⟩⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, WP.block_append_iff]
    refine WP.mono (ih hs (by omega)) fun t ⟨hv, hk⟩ => ?_
    refine WP.mono (cachedPointStore_ok (hk.scratch hs) (negBaseCached n) (dst := 2048 + 128 * n)
      (by omega) (by omega)) fun u ⟨hu, ku⟩ => ?_
    refine ⟨fun i hi => ?_, (hk.mono (by omega) (by omega)).trans (ku.mono (by omega) (by omega))⟩
    by_cases h : i < n
    · rw [(TableFrame.table ku.mem).point (by omega) (Or.inl (by omega)) (by omega), hv i h]
    · obtain rfl : i = n := by omega
      exact hu

theorem bTable_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block bTable) s fun t => (∀ i < 15, tablePoint t.mem base (2048 + 128 * i) = negBaseCached i) ∧
      TableKeep base 2048 1920 s t :=
  bTablePrefix_ok hs 15 (by decide)

/-! ## `[i]A` -/

private theorem aNext_cmp : ∀ n < 15,
    (BitVec.ofNat 64 (n + 1) - BitVec.ofNat 64 15 != 0) = decide (n + 1 ≠ 15) := by decide

theorem aNext_ok (s : State) (n : Nat) (hn : n < 15) (hc : s.gpr .x19 = BitVec.ofNat 64 n) :
    WP isa (.block [.addImm .x .x19 .x19 1, .subImm .x .x8 .x19 15]) s fun t =>
      t.gpr .x19 = BitVec.ofNat 64 (n + 1) ∧ eval (.nonzero .x .x8) t = some (decide (n + 1 ≠ 15)) ∧
      Keeps [.x19, .x8] s t := by
  have ha : BitVec.ofNat 64 n + BitVec.ofNat 64 1 = BitVec.ofNat 64 (n + 1) := by
    rw [BitVec.ofNat_add]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, BitVec.setWidth_eq,
    show (1 : Nat) < 4096 from by decide, show (15 : Nat) < 4096 from by decide, ite_true,
    RegUpd.gpr_write, hc, ha, ite_false, reduceCtorEq, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · simp only [eval, read_x, RegUpd.gpr_write, ite_true, BitVec.setWidth_eq, ite_false, reduceCtorEq,
      aNext_cmp n hn]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

theorem cacheOps_eval (e : Env) (hd : e 16 = Spec.Ed25519.d) :
    point (evalOps (savePointOps ++ cacheOps) e) 0 1 2 3 = cache (point e 0 1 2 3) := by
  have h : point (evalOps (savePointOps ++ cacheOps) e) 0 1 2 3 =
      ⟨e 1 - e 0, e 1 + e 0, (e 3 + e 3) * e 16, e 2 + e 2⟩ := rfl
  rw [h, hd]
  simp only [cache, point]
  congr 1 <;> ring

theorem saveCache_eval (e : Env) :
    point (evalOps (savePointOps ++ cacheOps) e) 4 5 6 7 = point e 4 5 6 7 ∧
    point (evalOps (savePointOps ++ cacheOps) e) 17 18 19 20 = point e 0 1 2 3 ∧
    evalOps (savePointOps ++ cacheOps) e 16 = e 16 := ⟨rfl, rfl, rfl⟩

theorem restore_eval (e : Env) :
    point (evalOps restorePointOps e) 4 5 6 7 = point e 4 5 6 7 ∧
    evalOps restorePointOps e 16 = e 16 := ⟨rfl, rfl⟩

theorem pointAddCached_q (e : Env) :
    point (evalOps pointAddCachedOps e) 4 5 6 7 = point e 4 5 6 7 := rfl

theorem PowersKeep.of_tableKeep {base : Addr} {s t : State} {o n : Nat} (h : TableKeep base o n s t) :
    PowersKeep base o n s t :=
  ⟨fun r _ _ hr => h.gpr r (fun hm => hr (by
    revert hm; simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro (rfl | rfl | rfl | rfl) <;> decide)), h.rd, h.wr, h.sp, TableFrame.table h.mem⟩

theorem storeCached_ok {s : State} {base : Addr} (hs : Scr s base) (j : Nat) (hj : j < 15)
    (hc : s.gpr .x19 = BitVec.ofNat 64 j) (hd : env s.mem base 16 = Spec.Ed25519.d) :
    WP isa (.block storeCached) s fun t =>
      tablePoint t.mem base (5376 + 128 * j) = cache (point (env s.mem base) 0 1 2 3) ∧
      point (env t.mem base) 0 1 2 3 = point (env s.mem base) 0 1 2 3 ∧
      point (env t.mem base) 4 5 6 7 = point (env s.mem base) 4 5 6 7 ∧
      env t.mem base 16 = env s.mem base 16 ∧ t.gpr .x19 = s.gpr .x19 ∧
      PowersKeep base (5376 + 128 * j) 128 s t := by
  rw [storeCached, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (fieldCode_ok (savePointOps ++ cacheOps) hs) fun a ⟨ka, va⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (tableAddr_ok (ka.scr hs).x0 5376 j (by omega) ((ka.gpr _ (by decide)).trans hc))
    fun b ⟨bp, kb⟩ => ?_
  have kbe : Keep base a b := Keep.of_keeps kb (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (pointToTable_ok ((ka.trans kbe).scr hs) bp (by omega) (by omega)) fun c ⟨cp, kc⟩ => ?_
  have ce : env c.mem base = env a.mem base := by rw [table_env kc.mem (by omega), kb.mem]
  refine WP.mono (fieldCode_ok restorePointOps (kc.scratch ((ka.trans kbe).scr hs)))
    fun t ⟨kt, vt⟩ => ?_
  obtain ⟨s4, s17, s16⟩ := saveCache_eval (env s.mem base)
  obtain ⟨r4, r16⟩ := restore_eval (env c.mem base)
  refine ⟨?_, ?_, ?_, ?_, by rw [kt.gpr _ (by decide), kc.gpr _ (by decide), kbe.gpr _ (by decide),
    ka.gpr _ (by decide)], ((PowersKeep.of_keep (ka.trans kbe)).trans
    (PowersKeep.of_tableKeep kc)).trans (PowersKeep.of_keep kt)⟩
  · rw [workspace_tablePoint kt.mem (by omega) (by omega), cp, kb.mem, va, cacheOps_eval _ hd]
  · rw [vt, restorePoint_eval, ce, va, s17]
  · rw [vt, r4, ce, va, s4]
  · rw [vt, r16, ce, va, s16]

/-- The table of `A`'s multiples, cached, with `n` entries, `[n]A` in slots 0–3 and `A`
cached in slots 4–7. -/
structure ATableInv (s₀ : State) (base : Addr) (A : EPoint dZ) (n : Nat) (s : State) : Prop where
  positive : 0 < n
  bound : n ≤ 15
  scratch : Scr s base
  counter : s.gpr .x19 = BitVec.ofNat 64 n
  d : env s.mem base 16 = Spec.Ed25519.d
  value : Rep (point (env s.mem base) 0 1 2 3) (n • A)
  q : ∃ qa, point (env s.mem base) 4 5 6 7 = cache qa ∧ Rep qa A
  table : ∀ j < n, ∃ q, tablePoint s.mem base (5376 + 128 * j) = cache q ∧ Rep q ((j + 1) • A)
  keep : PowersKeep base 5376 1920 s₀ s

theorem aTableBody_ok {s₀ s : State} {base : Addr} {A : EPoint dZ} {n : Nat} (hn : n < 15)
    (h : ATableInv s₀ base A n s) :
    WP isa (.block aTableBody) s fun t => eval (.nonzero .x .x8) t = some (decide (n + 1 ≠ 15)) ∧
      ATableInv s₀ base A (n + 1) t := by
  obtain ⟨qa, hq, hA⟩ := h.q
  rw [aTableBody, List.append_assoc, WP.block_append_iff]
  refine WP.mono (fieldCode_ok pointAddCachedOps h.scratch) fun c ⟨kc, vc⟩ => ?_
  have crep : Rep (point (env c.mem base) 0 1 2 3) ((n + 1) • A) := by
    rw [vc, pointAddCached_eval _ qa hq, succ_nsmul]
    exact pointAdd_rep h.value hA
  have cq : point (env c.mem base) 4 5 6 7 = point (env s.mem base) 4 5 6 7 := by
    rw [vc, pointAddCached_q]
  have cd : env c.mem base 16 = Spec.Ed25519.d := by
    rw [vc, pointAddCached_high _ 16 (by decide)]; exact h.d
  rw [WP.block_append_iff]
  refine WP.mono (storeCached_ok (kc.scr h.scratch) n hn ((kc.gpr _ (by decide)).trans h.counter) cd)
    fun d ⟨dt, d0, d4, d16, d19, kd⟩ => ?_
  refine WP.mono (aNext_ok d n hn (d19.trans
    ((kc.gpr _ (by decide)).trans h.counter))) fun t ⟨tc, tz, kt⟩ => ?_
  have kall : PowersKeep base 5376 1920 s t :=
    ((PowersKeep.of_keep kc).trans (kd.mono (by omega) (by omega))).trans
      (PowersKeep.of_keeps kt (by decide))
  refine ⟨tz, by omega, by omega, kall.scratch h.scratch, tc, ?_, ?_, ?_, ?_, h.keep.trans kall⟩
  · rw [kt.mem, d16]; exact cd
  · rw [kt.mem, d0]; exact crep
  · exact ⟨qa, by rw [kt.mem, d4, cq]; exact hq, hA⟩
  · intro j hj
    rw [kt.mem]
    by_cases hjn : j < n
    · rw [kd.mem.point (by omega) (Or.inl (by omega)) (by omega),
        workspace_tablePoint kc.mem (by omega) (by omega)]
      exact h.table j hjn
    · obtain rfl : j = n := by omega
      exact ⟨_, dt, crep⟩

theorem aTableInit_ok {s : State} {base : Addr} {A : EPoint dZ} (hs : Scr s base)
    (hd : env s.mem base 16 = Spec.Ed25519.d) (hA : Rep (tablePoint s.mem base 7424) A) :
    WP isa (.block aTableInit) s (ATableInv s base A 1) := by
  rw [aTableInit, List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc,
    WP.block_append_iff]
  refine WP.mono (pointTableRead_ok hs 7424 (by decide) (by decide)) fun a ⟨ka, ap, ah⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (tableIndexZero_ok a) fun b ⟨bz, kb⟩ => ?_
  have kab := (PowersKeep.of_counter ka : PowersKeep base 5376 1920 s a).trans
    (PowersKeep.of_keeps kb (by decide))
  have bd : env b.mem base 16 = Spec.Ed25519.d := by rw [kb.mem, ah 16 (by decide)]; exact hd
  have bA : Rep (point (env b.mem base) 0 1 2 3) A := by rw [kb.mem, ap]; exact hA
  rw [WP.block_append_iff]
  refine WP.mono (storeCached_ok (kab.scratch hs) 0 (by decide) bz bd) fun c ⟨ct, c0, _, c16, c19, kc⟩ => ?_
  have kac := kab.trans (kc.mono (by omega) (by omega))
  rw [WP.block_append_iff]
  refine WP.mono (tableAddr_ok (kac.scratch hs).x0 5376 0 (by decide)
    (c19.trans bz)) fun d ⟨dp, kd⟩ => ?_
  have kde : Keep base c d := Keep.of_keeps kd (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (pointFromTableQ_ok (kde.scr (kac.scratch hs)) dp (by decide) (by decide))
    fun e ⟨ep, ke⟩ => ?_
  have kee := Keep.of_tableQ ke
  have o := tableQ_other ke
  refine WP.mono (movzW_ok e .x19 1) fun t ⟨tc, kt⟩ => ?_
  have kall : PowersKeep base 5376 1920 s t :=
    ((kac.trans (PowersKeep.of_keep (kde.trans kee))).trans (PowersKeep.of_keeps kt (by decide)))
  have e0 : point (env e.mem base) 0 1 2 3 = point (env c.mem base) 0 1 2 3 := by
    simp only [point, o 0 (by decide), o 1 (by decide), o 2 (by decide), o 3 (by decide), kd.mem]
  refine ⟨by decide, by decide, kall.scratch hs, tc, ?_, ?_, ?_, ?_, kall⟩
  · rw [kt.mem, o 16 (by decide), kd.mem, c16]; exact bd
  · rw [kt.mem, e0, c0, one_nsmul]; exact bA
  · refine ⟨point (env b.mem base) 0 1 2 3, ?_, bA⟩
    rw [kt.mem, ep, kd.mem]
    simpa using ct
  · intro j hj
    obtain rfl : j = 0 := by omega
    refine ⟨point (env b.mem base) 0 1 2 3, ?_, by rw [zero_add, one_nsmul]; exact bA⟩
    rw [kt.mem, workspace_tablePoint kee.mem (by decide) (by decide), workspace_tablePoint kde.mem
      (by decide) (by decide)]
    simpa using ct

theorem aTable_ok {s : State} {base : Addr} {A : EPoint dZ} (hs : Scr s base)
    (hd : env s.mem base 16 = Spec.Ed25519.d) (hA : Rep (tablePoint s.mem base 7424) A) :
    WP isa aTable s (ATableInv s base A 15) := by
  rw [aTable]
  refine WP.seq (WP.mono (aTableInit_ok hs hd hA) fun a ha => ?_)
  apply WP.loop (fun n t => ATableInv s base A (15 - n) t ∧ 0 < n) (n := 14)
  · intro n t ⟨h, hn⟩
    have hp := h.positive
    refine WP.mono (aTableBody_ok (n := 15 - n) (by omega) h) fun u ⟨uz, hu⟩ => ?_
    by_cases he : 15 - n + 1 = 15
    · exact Or.inl ⟨uz.trans (by rw [he]; rfl), by rw [← he]; exact hu⟩
    · exact Or.inr ⟨uz.trans (by rw [decide_eq_true he]), n - 1, by omega,
        by rw [show 15 - (n - 1) = 15 - n + 1 by omega]; exact hu, by have := hu.bound; omega⟩
  · exact ⟨ha, by decide⟩

end VG.Proof.Ed25519.AArch64
end

/-! Merged from `Proof.Ed25519.AArch64.PointMul`. -/
section
/-! Checkpoint generation before the batch descent. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

theorem mulCounterInit_ok {s : State} {base : Addr} (hs : Scr s base) (count : Nat) :
    WP isa (.block (mulCounterInit count)) s fun t =>
      t.mem.readW (off base 56) 64 = BitVec.ofNat 64 count ∧
      (∀ r, r ≠ .x8 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      Outside base 56 8 s.mem t.mem := by
  rw [mulCounterInit, WP.block_append_iff]
  refine WP.mono (const64_ok s .x8 (BitVec.ofNat 64 count)) fun a ⟨av, ka⟩ => ?_
  apply WP.of_runBlock
  rw [runBlock_cons, store_sc (hs.of_keeps ka (by decide)) (by decide) (by decide), runStep_some, runBlock_nil]
  simp only [Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ka.gpr r (by simpa only [List.mem_singleton] using hr), ka.rd, ka.wr, ka.sp, ?_⟩
  · rw [Mem.readW_writeW_self64]; exact av
  · rw [ka.mem]; exact writeW_outside _ _ _ (by decide)

end VG.Proof.Ed25519.AArch64
end

/-!
# Verification's equation, from the windows

The windows leave a representative of `[k]A - [S]B`, compared with `-R`: they
are equal exactly when `[S]B = R + [k]A`, which, as `A` and `R` represent
points of the group, is the specification's comparison.
-/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 VG.Proof.Ed25519 Edwards

theorem PowersKeep.of_byte {base : Addr} {s t : State} (h : ByteKeep base s t) :
    PowersKeep base 56 7752 s t :=
  ⟨fun r hb hs hc => h.gpr r hc hb hs, h.rd, h.wr, h.sp,
    TableFrame.table (h.mem.mono (by decide) (by decide))⟩

theorem negR_eval (e : Env) :
    point (evalOps [.const 8 0, .sub 4 8 4, .sub 7 8 7] e) 0 1 2 3 = point e 0 1 2 3 ∧
    point (evalOps [.const 8 0, .sub 4 8 4, .sub 7 8 7] e) 4 5 6 7 = negPoint (point e 4 5 6 7) :=
  ⟨rfl, rfl⟩

/-- `-R`, beside the accumulator. -/
theorem negR_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block negR) s fun t => CounterKeep base s t ∧
      point (env t.mem base) 0 1 2 3 = point (env s.mem base) 0 1 2 3 ∧
      point (env t.mem base) 4 5 6 7 = negPoint (tablePoint s.mem base 7552) := by
  rw [negR, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (tableIndexZero_ok s) fun a ⟨az, ka⟩ => ?_
  have kar : CounterKeep base s a := CounterKeep.of_keeps ka (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (tableAddr_ok (kar.scr hs).x0 7552 0 (by decide) az) fun b ⟨pb, kb⟩ => ?_
  simp only [Nat.mul_zero, Nat.add_zero] at pb
  have kbe : Keep base a b := Keep.of_keeps kb (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (pointFromTableQ_ok (kbe.scr (kar.scr hs)) pb (by decide) (by decide))
    fun c ⟨pc, kc⟩ => ?_
  have kce := Keep.of_tableQ kc
  have o := tableQ_other kc
  have c0 : point (env c.mem base) 0 1 2 3 = point (env s.mem base) 0 1 2 3 := by
    simp only [point, o 0 (by decide), o 1 (by decide), o 2 (by decide), o 3 (by decide), kb.mem,
      ka.mem]
  refine WP.mono (fieldCode_ok _ (kce.scr (kbe.scr (kar.scr hs)))) fun t ⟨kt, vt⟩ => ?_
  refine ⟨kar.trans (CounterKeep.of_keep ((kbe.trans kce).trans kt)), ?_, ?_⟩
  · rw [vt, (negR_eval _).1, c0]
  · rw [vt, (negR_eval _).2, pc, kb.mem, ka.mem]

/-- Verification's code before the windows, regrouped. -/
def windowPrep : Prog isa :=
  .seq (.seq (.seq (.block windowSetup) aTable) (.block bTable)) (.block windowInit)

theorem PowersKeep.of_table {base : Addr} {s t : State} {o n : Nat} (h : TableKeep base o n s t)
    (ho : 56 ≤ o) (hn : o + n ≤ 7808) : PowersKeep base 56 7752 s t :=
  ⟨fun r _ _ hr => h.gpr r (fun hm => hr (by
    revert hm; simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro (rfl | rfl | rfl | rfl) <;> decide)), h.rd, h.wr, h.sp,
    TableFrame.table (h.mem.mono (by omega) (by omega))⟩

/-- Before the windows: the tables, an accumulator representing `0` and the counter at 64. -/
theorem windowPrep_ok {s : State} {base sig challenge : Addr} {Aa : EPoint dZ}
    (hs : Scr s base)
    (hp : s.mem.readW (off base 7944) 64 = sig)
    (hc : s.mem.readW (off base 7952) 64 = challenge)
    (hr : ∀ i < 32, InRegions (s.rd ++ s.wr) (off (off sig 32) i) 1)
    (hf : ∀ i < 32, 8192 ≤ ofs base (off (off sig 32) i))
    (hcr : ∀ i < 64, InRegions (s.rd ++ s.wr) (off challenge i) 1)
    (hcf : ∀ i < 64, 8192 ≤ ofs base (off challenge i))
    (hA : Rep (tablePoint s.mem base 7424) Aa) :
    WP isa windowPrep s fun e => WinLoop e base challenge sig Aa
      (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem challenge 64))
      (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (off sig 32) 32)) 64 e ∧
      PowersKeep base 56 7752 s e ∧ tablePoint e.mem base 7552 = tablePoint s.mem base 7552 := by
  rw [windowPrep]
  -- The constant `d`.
  refine WP.seq (WP.seq (WP.seq (WP.mono (constField_ok hs 16 Spec.Ed25519.d) fun a ⟨ka, va⟩ => ?_)))
  have ad : env a.mem base 16 = Spec.Ed25519.d := by rw [va]; exact Function.update_self ..
  have aA : tablePoint a.mem base 7424 = tablePoint s.mem base 7424 :=
    workspace_tablePoint ka.mem (by decide) (by decide)
  have aR : tablePoint a.mem base 7552 = tablePoint s.mem base 7552 :=
    workspace_tablePoint ka.mem (by decide) (by decide)
  have ksa : PowersKeep base 56 7752 s a := PowersKeep.of_keep ka
  -- The multiples of `A`.
  refine WP.mono (aTable_ok (ksa.scratch hs) ad (by rw [aA]; exact hA)) fun b hb => ?_
  have ksb := ksa.trans (hb.keep.mono (by decide) (by decide))
  have bR : tablePoint b.mem base 7552 = tablePoint s.mem base 7552 := by
    rw [hb.keep.mem.point (by decide) (Or.inr (by decide)) (by decide), aR]
  -- The negated multiples of `B`.
  refine WP.mono (bTable_ok hb.scratch) fun c ⟨ct, kc⟩ => ?_
  have ksc := ksb.trans (PowersKeep.of_table kc (by decide) (by decide))
  have cR : tablePoint c.mem base 7552 = tablePoint s.mem base 7552 := by
    rw [(TableFrame.table kc.mem).point (by decide) (Or.inr (by decide)) (by decide), bR]
  have cd : env c.mem base 16 = Spec.Ed25519.d := by rw [table_env kc.mem (by decide)]; exact hb.d
  have cA : TableOf cache c.mem base 5376 Aa := fun j hj => by
    obtain ⟨q, hq, hr⟩ := hb.table j hj
    exact ⟨q, by rw [(TableFrame.table kc.mem).point (by omega) (Or.inr (by omega)) (by omega)]; exact hq,
      hr⟩
  have cB : TableOf cache c.mem base 2048 (-baseAff) := fun j hj => by
    obtain ⟨q, hq, hr⟩ := negBaseCached_ok j hj
    exact ⟨q, by rw [ct j hj, hq], hr⟩
  -- The accumulator and the byte counter.
  rw [windowInit, WP.block_append_iff]
  refine WP.mono (fieldCode_ok (constPointOps Spec.Ed25519.identity) (ksc.scratch hs))
    fun d ⟨kd, vd⟩ => ?_
  have kcd : PowersKeep base 56 7752 c d := PowersKeep.of_keep kd
  refine WP.mono (mulCounterInit_ok ((ksc.trans kcd).scratch hs) 64)
    fun e ⟨ec, eg, er, ew, esp, em⟩ => ?_
  have kde : ByteKeep base d e :=
    ⟨fun r _ _ _ => eg r (by rintro rfl; contradiction), er, ew, esp, em.mono (by decide) (by decide)⟩
  have kce : ByteKeep base c e := (ByteKeep.of_win (WinKeep.of_keep kd)).trans kde
  have kse := ksc.trans (PowersKeep.of_byte kce)
  have eR : tablePoint e.mem base 7552 = tablePoint s.mem base 7552 := by
    rw [win_tablePoint kce.mem (by decide) (by decide), cR]
  have ed : env e.mem base 16 = Spec.Ed25519.d := by rw [header_env em, vd]; exact cd
  have ctx : WinCtx base challenge sig Aa e :=
    ⟨kse.scratch hs, (kse.header (by decide) (by decide) (by decide)).trans hc,
      (kse.header (by decide) (by decide) (by decide)).trans hp,
      fun i hi => by rw [kse.rd, kse.wr]; exact hcr i hi,
      fun i hi => by rw [kse.rd, kse.wr]; exact hr i hi, hcf, hf,
      cA.of_win kce.mem (by decide) (by decide), cB.of_win kce.mem (by decide) (by decide)⟩
  have hK := decodeLE_lt64 e.mem challenge
  have hS := decodeLE_lt32 e.mem (off sig 32)
  have eK := outside_bytes (tableFrame_work kse.mem (by decide) (by decide)) (by decide) hcf
  have eS := outside_bytes (tableFrame_work kse.mem (by decide) (by decide)) (by decide) hf
  refine ⟨⟨ctx, ed, ec, by rw [eK], by rw [eS], ?_, ByteKeep.refl _ _⟩, kse, eR⟩
  rw [← eK, ← eS, Nat.div_eq_of_lt hK, Nat.div_eq_of_lt (Nat.lt_trans hS (by decide)), zero_smul,
    zero_smul, add_zero, header_env em, vd, constPoint_eval]
  exact identity_rep.proj

theorem verifyEquationPoints_ok {s : State} {base sig challenge : Addr} {Aa Ra : EPoint dZ}
    (hs : Scr s base)
    (hp : s.mem.readW (off base 7944) 64 = sig)
    (hc : s.mem.readW (off base 7952) 64 = challenge)
    (hr : ∀ i < 32, InRegions (s.rd ++ s.wr) (off (off sig 32) i) 1)
    (hf : ∀ i < 32, 8192 ≤ ofs base (off (off sig 32) i))
    (hcr : ∀ i < 64, InRegions (s.rd ++ s.wr) (off challenge i) 1)
    (hcf : ∀ i < 64, 8192 ≤ ofs base (off challenge i))
    (hA : Rep (tablePoint s.mem base 7424) Aa) (hR : Rep (tablePoint s.mem base 7552) Ra) :
    WP isa verifyEquationPoints s fun t => PowersKeep base 56 7752 s t ∧
      t.gpr .x8 = signWord (Spec.Ed25519.pointEqual
        (Spec.Ed25519.pointMul
          (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (off sig 32) 32)) Spec.Ed25519.basePoint)
        (Spec.Ed25519.pointAdd (tablePoint s.mem base 7552)
          (Spec.Ed25519.pointMul (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem challenge 64))
            (tablePoint s.mem base 7424)))) := by
  rw [verifyEquationPoints]
  apply WP.assoc; apply WP.assoc; apply WP.assoc
  refine WP.seq (WP.mono (windowPrep_ok hs hp hc hr hf hcr hcf hA) fun e ⟨w0, kse, eR⟩ => ?_)
  -- The windows.
  refine WP.seq (WP.mono (skipZero_ok w0) fun f ⟨c, hc32, hc64, hf'⟩ => ?_)
  refine WP.seq (WP.mono (windowsA_ok hc32 hc64 hf') fun g hg => ?_)
  refine WP.seq (WP.mono (loopB_ok hg) fun h hh => ?_)
  have ksh := kse.trans (PowersKeep.of_byte hh.keep)
  -- The comparison with `-R`.
  refine WP.seq (WP.mono (negR_ok (ksh.scratch hs)) fun u ⟨ku, u0, u4⟩ => ?_)
  have ksu := ksh.trans (PowersKeep.of_counter ku)
  refine WP.mono (pointEqual_ok (ksu.scratch hs)) fun t ⟨kt, tv⟩ => ?_
  refine ⟨ksu.trans (PowersKeep.of_keep kt), ?_⟩
  have hv := hh.value
  simp only [pow_zero, Nat.div_one] at hv
  rw [tv, u0, u4, win_tablePoint hh.keep.mem (by decide) (by decide), eR,
    window_equation hA hR hv hR.neg.proj]

end VG.Proof.Ed25519.AArch64
