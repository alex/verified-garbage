import VerifiedGarbage.Proof.Ed25519.X86.AccumulateStep
import VerifiedGarbage.Impl.Ed25519.X86.PointBatch
import VerifiedGarbage.Proof.Ed25519.X86.PointPowersLoop
import VerifiedGarbage.Proof.Ed25519.X86.PrepareAdd
import VerifiedGarbage.Impl.Ed25519.X86.PointMul

/-! Merged from `Proof.Ed25519.X86.PointMulFrame`. -/
section
/-! Merged from `Proof.Ed25519.X86.AccumulateLoop`. -/
section
/-! Consume one sixteen-bit batch from most significant bit to least. -/
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

structure AccumulateInv (x : BitVec 32) (s₀ : State) (scalar batch : Nat)
    (p : Spec.Ed25519.Point) (n : Nat) (s : State) : Prop where
  positive : 0 < n
  bound : n ≤ 16
  keep : IKeep x s₀ s
  counter : s.gpr .esi = BitVec.ofNat 32 n
  value : point (env s.mem x) 0 1 2 3 = after scalar p (16 * batch + n)
  d : env s.mem x 16 = Spec.Ed25519.d

theorem accumulateLoop_ok {x : BitVec 32} {s₀ : State} (hc : Ctx x s₀)
    (scalar batch : Nat) (p : Spec.Ed25519.Point) (hb : batch < 32)
    (hindex : wd s₀.mem x 28 = BitVec.ofNat 32 batch)
    (hcounter : s₀.gpr .esi = BitVec.ofNat 32 16)
    (hbits : ∀ j < 16, s₀.mem (addr x (7168 + (16 * batch + j))) =
      BitVec.ofNat 8 (scalarBit scalar (16 * batch + j)).toNat)
    (htable : ∀ j < 16, tablePoint s₀.mem x (5120 + 128 * j) = powerPoint p (16 * batch + j))
    (hp : point (env s₀.mem x) 0 1 2 3 = after scalar p (16 * batch + 16))
    (hd : env s₀.mem x 16 = Spec.Ed25519.d) :
    WP isa (.loop (.block accumulateBody) .ne) s₀ fun t => IKeep x s₀ t ∧
      point (env t.mem x) 0 1 2 3 = after scalar p (16 * batch) ∧ env t.mem x 16 = Spec.Ed25519.d := by
  apply WP.loop (fun n => AccumulateInv x s₀ scalar batch p n) (n := 16)
  · intro n s h
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by have := h.positive; omega : n ≠ 0)
    have hj : j < 16 := by have := h.bound; omega
    refine WP.mono (accumulateBody_ok (h.keep.ctx hc) j batch scalar p hj hb
      ((h.keep.word hc 28 (by decide)).trans hindex) h.counter
      ((h.keep.bit hc _ (by omega)).trans (hbits j hj)) h.d
      (by simpa only [Nat.add_assoc] using h.value)
      ((workspace_table h.keep hc _ (by omega) (by omega)).trans (htable j hj)))
      fun t ⟨kt, bt, zt, pt, dt⟩ => ?_
    have keep := h.keep.trans kt
    by_cases hz : j = 0
    · subst j
      exact .inl ⟨by rw [zt]; rfl, keep, by simpa only [Nat.add_zero] using pt, dt⟩
    · exact .inr ⟨by rw [zt]; simp only [decide_eq_false hz]; rfl,
        j, by omega, ⟨by omega, by omega, keep, bt, pt, dt⟩⟩
  · exact ⟨by decide, by decide, IKeep.refl _ _, hcounter, hp, hd⟩

theorem accumulate16_ok {x : BitVec 32} {s : State} (hc : Ctx x s)
    (scalar batch : Nat) (p : Spec.Ed25519.Point) (hb : batch < 32)
    (hindex : wd s.mem x 28 = BitVec.ofNat 32 batch)
    (hbits : ∀ j < 16, s.mem (addr x (7168 + (16 * batch + j))) =
      BitVec.ofNat 8 (scalarBit scalar (16 * batch + j)).toNat)
    (htable : ∀ j < 16, tablePoint s.mem x (5120 + 128 * j) = powerPoint p (16 * batch + j))
    (hp : point (env s.mem x) 0 1 2 3 = after scalar p (16 * batch + 16))
    (hd : env s.mem x 16 = Spec.Ed25519.d) :
    WP isa accumulate16 s fun t => IKeep x s t ∧
      point (env t.mem x) 0 1 2 3 = after scalar p (16 * batch) ∧ env t.mem x 16 = Spec.Ed25519.d := by
  refine WP.seq (Wp.wp_movi fun u hu => WP.block_nil ?_)
  have ku : IKeep x s u := IKeep.of_counter hu
  refine WP.mono (accumulateLoop_ok (ku.ctx hc) scalar batch p hb
    (by rw [hu.mem]; exact hindex) hu.gpr (by rw [hu.mem]; exact hbits)
    (by rw [hu.mem]; exact htable) (by rw [hu.mem]; exact hp) (by rw [hu.mem]; exact hd))
    fun t ⟨kt, pt, dt⟩ => ?_
  exact ⟨ku.trans kt, pt, dt⟩

end VG.Proof.Ed25519.X86
end

/-! Merged from `Proof.Ed25519.X86.PointBatch`. -/
section
/-! Each batch contains sixteen consecutive exact powers. -/
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

theorem loadCheckpoint_ok {x : BitVec 32} {s : State} (hc : Ctx x s)
    (j : Nat) (hj : j < 32) (hb : s.gpr .esi = BitVec.ofNat 32 j) :
    WP isa (.block loadCheckpoint) s fun t => FieldKeep x s t ∧
      point (env t.mem x) 0 1 2 3 = tablePoint s.mem x (1024 + 128 * j) ∧
      point (env t.mem x) 17 18 19 20 = point (env s.mem x) 0 1 2 3 ∧
      env t.mem x 16 = env s.mem x 16 := by
  simp only [loadCheckpoint, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (fieldCode_ok savePointOps hc) fun a ⟨ka, ea⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (tableAddr_ok (ka.ctx hc) 1024 j (by omega) (ka.keep.esi.trans hb))
    fun b ⟨kb, mb, pb⟩ => ?_
  have cb := kb.ctx (ka.ctx hc)
  refine WP.mono (pointFromTable_ok cb pb (by omega) (by omega)) fun c ⟨kc, pc⟩ => ?_
  refine ⟨ka.trans ((FieldKeep.of_mem kb mb).trans (FieldKeep.of_copy kc cb)), ?_, ?_, ?_⟩
  · rw [pc, mb]
    exact workspace_table (IKeep.of_field ka) hc _ (by omega) (by omega)
  · rw [point_congr _ _ _ _ (kc.high cb 17 (by decide)) (kc.high cb 18 (by decide))
      (kc.high cb 19 (by decide)) (kc.high cb 20 (by decide)), mb, ea, savePoint_eval]
  · rw [kc.high cb 16 (by decide), mb, ea, savePoint_d]

theorem prepareBatch_ok {x : BitVec 32} {s : State} (hc : Ctx x s)
    (j : Nat) (hj : j < 32) (hb : s.gpr .esi = BitVec.ofNat 32 j)
    (hd : env s.mem x 16 = Spec.Ed25519.d) :
    WP isa prepareBatch s fun t => PowersKeep x 5120 2048 s t ∧
      point (env t.mem x) 0 1 2 3 = point (env s.mem x) 0 1 2 3 ∧
      (∀ i < 16, tablePoint t.mem x (5120 + 128 * i) =
        powerPoint (tablePoint s.mem x (1024 + 128 * j)) i) ∧
      env t.mem x 16 = Spec.Ed25519.d := by
  refine WP.seq (WP.mono (loadCheckpoint_ok hc j hj hb) fun a ⟨ka, pa, sa, da⟩ => ?_)
  refine WP.seq (WP.mono (pointPowers_ok false (ka.ctx hc) 5120 16 (by decide) (by decide)
    (by decide) (by decide) (da.trans hd)) fun b ⟨kb, tb, _, high⟩ => ?_)
  refine WP.mono (fieldCode_ok restorePointOps (kb.ctx (ka.ctx hc))) fun t ⟨kt, et⟩ => ?_
  refine ⟨((PowersKeep.of_ikeep (IKeep.of_field ka) _ _).trans kb).trans
    (PowersKeep.of_ikeep (IKeep.of_field kt) _ _), ?_, ?_, ?_⟩
  · rw [et, restorePoint_eval, point_congr _ _ _ _ (high 17 (by decide)) (high 18 (by decide))
      (high 19 (by decide)) (high 20 (by decide)), sa]
  · intro i hi
    rw [workspace_table (IKeep.of_field kt) (kb.ctx (ka.ctx hc)) _ (by omega) (by omega), tb i hi, pa]
    simp only [powerStride, Bool.false_eq_true, ite_false, Nat.one_mul]
  · rw [et, restorePoint_d, high 16 (by decide), da, hd]

end VG.Proof.Ed25519.X86
end

/-! One scalar batch preserves checkpoints, bits and saved API pointers. -/
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

structure BatchKeep (x : BitVec 32) (s t : State) : Prop where
  edi : t.gpr .edi = s.gpr .edi
  esp : t.gpr .esp = s.gpr .esp
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [sub x 24 904, sub x 5120 2048] s.mem t.mem

theorem BatchKeep.ctx {x : BitVec 32} {s t : State} (h : BatchKeep x s t) (hc : Ctx x s) : Ctx x t :=
  hc.keep h.edi h.wr
theorem BatchKeep.trans {x : BitVec 32} {s t u : State} (h : BatchKeep x s t) (k : BatchKeep x t u) :
    BatchKeep x s u := ⟨k.edi.trans h.edi, k.esp.trans h.esp, k.rd.trans h.rd,
      k.wr.trans h.wr, h.frame.trans k.frame⟩

theorem BatchKeep.of_powers {x : BitVec 32} {s t : State} (hc : Ctx x s)
    (h : PowersKeep x 5120 2048 s t) : BatchKeep x s t := by
  refine ⟨h.edi, h.esp, h.rd, h.wr, h.frame.sub ?_⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨sub x 24 904, by simp, sub_sub hc.fit (by decide) (by decide) (by decide)⟩
  · exact ⟨sub x 24 904, by simp, sub_sub hc.fit (by decide) (by decide) (by decide)⟩
  · exact ⟨sub x 5120 2048, by simp, fun _ ha => ha⟩

theorem BatchKeep.of_ikeep {x : BitVec 32} {s t : State} (hc : Ctx x s) (h : IKeep x s t) :
    BatchKeep x s t := BatchKeep.of_powers hc (PowersKeep.of_ikeep h _ _)

theorem BatchKeep.of_counter {x : BitVec 32} {s t : State} (hc : Ctx x s)
    (he : t.gpr .edi = s.gpr .edi) (hs : t.gpr .esp = s.gpr .esp)
    (hr : t.rd = s.rd) (hw : t.wr = s.wr) (hf : Frame [sub x 28 4] s.mem t.mem) : BatchKeep x s t :=
  ⟨he, hs, hr, hw, hf.sub fun r h => ⟨sub x 24 904, by simp, by
    rw [List.mem_singleton.mp h]; exact sub_sub hc.fit (by decide) (by decide) (by decide)⟩⟩

theorem BatchKeep.checkpoint {x : BitVec 32} {s t : State} (h : BatchKeep x s t) (hc : Ctx x s)
    (j : Nat) (hj : j < 32) : tablePoint t.mem x (1024 + 128 * j) = tablePoint s.mem x (1024 + 128 * j) := by
  apply table_point_of_words
  intro k hk
  apply wd_frame h.frame
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact sub_disj (by omega_using [hc.fit, hj, hk]) (by omega_using [hc.fit]) (Or.inr (by omega))
  · exact sub_disj (by omega_using [hc.fit, hj, hk]) (by omega_using [hc.fit]) (Or.inl (by omega))

theorem BatchKeep.bit {x : BitVec 32} {s t : State} (h : BatchKeep x s t) (hc : Ctx x s)
    (i : Nat) (hi : i < 512) : t.mem (addr x (7168 + i)) = s.mem (addr x (7168 + i)) := by
  apply h.frame
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  have hb : (sub x (7168 + i) 1).Contains (addr x (7168 + i)) 1 := Region.contains_self _ _
  rcases hr with rfl | rfl
  · exact (sub_disj (by omega_using [hc.fit, hi]) (by omega_using [hc.fit]) (Or.inr (by omega))) _ hb
  · exact (sub_disj (by omega_using [hc.fit, hi]) (by omega_using [hc.fit]) (Or.inr (by omega))) _ hb

theorem PowersKeep.batch_index {x : BitVec 32} {s t : State} (hc : Ctx x s)
    (h : PowersKeep x 5120 2048 s t) : wd t.mem x 28 = wd s.mem x 28 := by
  apply wd_frame h.frame
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact sub_disj (by omega_using [hc.fit]) (by omega_using [hc.fit]) (Or.inr (by decide))
  · exact sub_disj (by omega_using [hc.fit]) (by omega_using [hc.fit]) (Or.inl (by decide))
  · exact sub_disj (by omega_using [hc.fit]) (by omega_using [hc.fit]) (Or.inl (by decide))

end VG.Proof.Ed25519.X86
end

/-! Public batch countdown, leaving all coordinate values unchanged. -/
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

theorem counter28_env {x : BitVec 32} {m m' : Mem} (hx : x.toNat + 8192 ≤ 2 ^ 32)
    (h : Frame [sub x 28 4] m m') : env m' x = env m x := by
  funext i
  apply congrArg VG.Proof.X25519.toFe
  exact fe_frame1 h hx (by decide) (by simp only [offset]; omega)
    (Or.inr (by simp only [offset]; omega))

theorem batchBegin_ok {x : BitVec 32} {s : State} (hc : Ctx x s) (n : Nat)
    (hb : wd s.mem x 28 = BitVec.ofNat 32 (n + 1)) :
    WP isa (.block batchBegin) s fun t => BatchKeep x s t ∧
      t.gpr .esi = BitVec.ofNat 32 n ∧ wd t.mem x 28 = BitVec.ofNat 32 n ∧
      Frame [sub x 28 4] s.mem t.mem := by
  refine Wp.wp_ldm hc.edi (hc.inRW (by decide) (by decide)) fun u hu => ?_
  refine Wp.wp_subi fun v hv _ _ => ?_
  have bv : v.gpr .esi = BitVec.ofNat 32 n := by
    rw [hv.gpr, hu.gpr]
    change wd s.mem x 28 - 1 = _
    rw [hb, BitVec.ofNat_add]
    exact BitVec.add_sub_cancel _ _
  have cv := ((IKeep.of_counter hu).trans (IKeep.of_counter hv)).ctx hc
  refine Wp.wp_stm cv.edi (cv.inW (by decide) (by decide)) fun t ht => WP.block_nil ?_
  have mt : t.mem = s.mem.writeW (addr x 28) (BitVec.ofNat 32 n) := by rw [ht.mem, hv.mem, hu.mem, bv]
  have ft : Frame [sub x 28 4] s.mem t.mem := by
    rw [mt]; exact frame_write1 (Frame.refl _ _) hc.fit (by decide) (by decide) (by decide) _
  refine ⟨BatchKeep.of_counter hc ?_ ?_ ?_ ?_ ft, ?_, ?_, ft⟩
  · rw [ht.gpr, hv.other .edi (by decide), hu.other .edi (by decide)]
  · rw [ht.gpr, hv.other .esp (by decide), hu.other .esp (by decide)]
  · rw [ht.rd, hv.rd, hu.rd]
  · rw [ht.wr, hv.wr, hu.wr]
  · rw [ht.gpr]; exact bv
  · rw [mt, wd_write_self]

theorem batchTest_ok {x : BitVec 32} {s : State} (hc : Ctx x s) (n : Nat) (hn : n < 32)
    (hb : wd s.mem x 28 = BitVec.ofNat 32 n) :
    WP isa (.block batchTest) s fun t => IKeep x s t ∧ t.mem = s.mem ∧
      isa.eval .ne t = some (!decide (n = 0)) := by
  refine Wp.wp_ldm hc.edi (hc.inRW (by decide) (by decide)) fun u hu => ?_
  refine Wp.wp_test fun t ht zt => WP.block_nil ?_
  refine ⟨(IKeep.of_counter hu).trans ⟨by rw [ht.gpr], by rw [ht.gpr], ht.rd, ht.wr,
    by rw [ht.mem]; exact Frame.refl _ _⟩, by rw [ht.mem, hu.mem], ?_⟩
  show t.zf.map (!·) = _
  rw [zt, BitVec.and_self, hu.gpr]
  change some (!(wd s.mem x 28 == 0)) = _
  rw [hb, Wp.ofNat_beq_zero (by omega)]

theorem mulCounterInit_ok {x : BitVec 32} {s : State} (hc : Ctx x s) (count : Nat) :
    WP isa (.block (mulCounterInit count)) s fun t =>
      Keep s t ∧ Frame [sub x 28 4] s.mem t.mem ∧ wd t.mem x 28 = BitVec.ofNat 32 count := by
  refine Wp.wp_movi fun u hu => ?_
  have cu := (updKeep hu).ctx hc
  refine Wp.wp_stm cu.edi (cu.inW (by decide) (by decide)) fun t ht => WP.block_nil ?_
  refine ⟨(updKeep hu).trans ⟨by rw [ht.gpr], by rw [ht.gpr], by rw [ht.gpr], ht.rd, ht.wr⟩, ?_, ?_⟩
  · rw [ht.mem, hu.mem]
    exact frame_write1 (Frame.refl _ _) hc.fit (by decide) (by decide) (by decide) _
  · rw [ht.mem, wd_write_self, hu.gpr]

end VG.Proof.Ed25519.X86
