import VerifiedGarbage.Proof.Ed25519.WindowConstants
import VerifiedGarbage.Proof.Ed25519.AArch64.WindowStep
import VerifiedGarbage.Proof.Ed25519.AArch64.BaseBatchTable
import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyTables

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
