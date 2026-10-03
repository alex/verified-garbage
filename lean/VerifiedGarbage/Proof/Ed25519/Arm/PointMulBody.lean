import VerifiedGarbage.Impl.Ed25519.Arm.PointMul
import VerifiedGarbage.Proof.Ed25519.Arm.MulKeep
import VerifiedGarbage.Proof.Ed25519.Arm.MulInput

/-! Merged from `Proof.Ed25519.Arm.BatchFrame`. -/
section
/-! Merged from `Proof.Ed25519.Arm.BatchCounter`. -/
section
/-! The public descending batch counter is saved across field operations. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem counterStore_ok {b : BitVec 32} {s : State} (hc : Ctx b s) (j : Nat)
    (hv : s.gpr .r11 = BitVec.ofNat 32 j) :
    WP isa (.block [.str .r11 .r0 56]) s fun t => Rest [] s t ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 56, 4⟩] s.mem t.mem ∧
      t.mem.readW (State.addr b + BitVec.ofNat 64 56) 32 = BitVec.ofNat 32 j := by
  refine str0_ok hc (by decide) fun t ht => WP.block_nil ⟨ht.rest _, ?_, ?_⟩
  · rw [ht.mem]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  · rw [ht.mem, Mem.readW_writeW_self32, hv]

theorem MulKeep.of_counter {b : BitVec 32} {o n : Nat} {s t : State} {ws : List Reg}
    (hr : Rest ws s t) (hw : ∀ r ∈ ws, r ∈ powersClob)
    (hf : Frame [⟨State.addr b + BitVec.ofNat 64 56, 4⟩] s.mem t.mem) : MulKeep b o n s t :=
  ⟨hr.mono hw, hf.mono (by
    intro r hr
    rw [List.mem_singleton.mp hr]
    exact List.mem_cons_of_mem _ (List.mem_cons_self ..))⟩

theorem batchStart_ok {b : BitVec 32} {s : State} (hc : Ctx b s) (j : Nat)
    (hv : s.mem.readW (State.addr b + BitVec.ofNat 64 56) 32 = BitVec.ofNat 32 (j + 1)) :
    WP isa (.block batchStart) s fun t => Rest [.r11] s t ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 56, 4⟩] s.mem t.mem ∧
      t.gpr .r11 = BitVec.ofNat 32 j ∧
      t.mem.readW (State.addr b + BitVec.ofNat 64 56) 32 = BitVec.ofNat 32 j := by
  refine ldr0_ok hc (by decide) fun u hu => wp_dp (op2_imm (by decide)) fun v hv' => ?_
  have ev : v.gpr .r11 = BitVec.ofNat 32 j := by
    rw [hv'.gpr]
    change u.gpr .r11 - 1 = _
    rw [hu.gpr, hv, BitVec.ofNat_add]
    exact BitVec.add_sub_cancel _ _
  have rv : Rest [.r11] s v := (hu.rest (by decide)).trans (hv'.rest (by decide))
  have mv : v.mem = s.mem := by rw [hv'.mem, hu.mem]
  refine WP.mono (counterStore_ok (hc.of_rest rv (by decide)) j ev) fun t ⟨tr, tf, tv⟩ => ?_
  exact ⟨rv.trans (tr.mono (by decide)), by rw [← mv]; exact tf,
    (tr.gpr _ (by decide)).trans ev, tv⟩

theorem batchTest_ok {b : BitVec 32} {s : State} (hc : Ctx b s) (j : Nat) (hj : j < 32)
    (hv : s.mem.readW (State.addr b + BitVec.ofNat 64 56) 32 = BitVec.ofNat 32 j) :
    WP isa (.block batchTest) s fun t => Rest [.r11] s t ∧ t.mem = s.mem ∧ t.z = decide (j = 0) := by
  refine ldr0_ok hc (by decide) fun u hu => wp_cmp (op2_imm (by decide)) fun t ht hz => WP.block_nil ?_
  refine ⟨(hu.rest (by decide)).trans (ht.rest _), by rw [ht.mem, hu.mem], ?_⟩
  have he : BitVec.ofNat 32 j - (0 : BitVec 32) = BitVec.ofNat 32 j := BitVec.sub_zero _
  rw [hz, hu.gpr, hv, he, ofNat_beq_zero (by omega)]

end VG.Proof.Ed25519.Arm
end

/-! The saved batch counter survives the table and bit operations. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem PowersKeep.counter {b : BitVec 32} {o n : Nat} {s t : State}
    (h : PowersKeep b o n s t) (ho : 1600 ≤ o) (hn : o + n ≤ 8192) :
    t.mem.readW (State.addr b + BitVec.ofNat 64 56) 32 =
      s.mem.readW (State.addr b + BitVec.ofNat 64 56) 32 := by
  apply BitVec.eq_of_toNat_eq
  exact wd_frame h.frame fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Offset.disjoint _ (.inl (by omega)) (by decide) (by omega)

theorem LoopKeep.counter {b : BitVec 32} {s t : State} (h : LoopKeep b s t) :
    t.mem.readW (State.addr b + BitVec.ofNat 64 56) 32 =
      s.mem.readW (State.addr b + BitVec.ofNat 64 56) 32 := by
  apply BitVec.eq_of_toNat_eq
  exact wd_frame h.frame fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide)

theorem bitsFrame_counter {b : BitVec 32} {m m' : Mem}
    (h : Frame [⟨State.addr b + BitVec.ofNat 64 32, 16⟩] m m') :
    m'.readW (State.addr b + BitVec.ofNat 64 56) 32 =
      m.readW (State.addr b + BitVec.ofNat 64 56) 32 := by
  apply BitVec.eq_of_toNat_eq
  exact wd_frame h fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact Offset.disjoint _ (.inr (by decide)) (by decide) (by decide)

theorem smallFrame_table {b : BitVec 32} {m m' : Mem} {o n d : Nat}
    (h : Frame [⟨State.addr b + BitVec.ofNat 64 o, n⟩] m m') (hn : o + n ≤ 64)
    (hd : 1600 ≤ d) (hb : d + 128 ≤ 8192) : tablePoint m' b d = tablePoint m b d := by
  refine tablePoint_frame h fun r hr => ?_
  rw [List.mem_singleton.mp hr]
  exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)

end VG.Proof.Ed25519.Arm
end

/-! One outer batch consumes exactly sixteen scalar bits. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem pointMulBody_ok {b ptr : BitVec 32} {s : State} (hc : Ctx b s) (hl : AllLim s.mem b)
    (count scalar j : Nat) (p : Spec.Ed25519.Point) (hi : MulInput b ptr count scalar s)
    (hj : j < count) (hd : env s.mem b 16 = Spec.Ed25519.d)
    (hp : point (env s.mem b) 0 1 2 3 = after scalar p (16 * (j + 1)))
    (hcj : s.mem.readW (State.addr b + BitVec.ofNat 64 56) 32 = BitVec.ofNat 32 (j + 1))
    (ht : tablePoint s.mem b (1600 + 128 * j) = powerPoint p (16 * j)) :
    WP isa pointMulBody s fun t => MulKeep b 5696 2048 s t ∧ AllLim t.mem b ∧
      env t.mem b 16 = Spec.Ed25519.d ∧ point (env t.mem b) 0 1 2 3 = after scalar p (16 * j) ∧
      t.mem.readW (State.addr b + BitVec.ofNat 64 56) 32 = BitVec.ofNat 32 j ∧ t.z = decide (j = 0) := by
  have hj32 : j < 32 := Nat.lt_of_lt_of_le hj hi.bound
  refine WP.seq (WP.mono (batchStart_ok hc j hcj) fun a ⟨ar, af, av, ac⟩ => ?_)
  have ak : MulKeep b 5696 2048 s a := MulKeep.of_counter ar (by decide) af
  have al := smallFrame_lim af (by decide) hl
  have ae := smallFrame_env af (by decide)
  have ad : env a.mem b 16 = Spec.Ed25519.d := (congrFun ae 16).trans hd
  refine WP.seq (WP.mono (prepareBatch_ok (ak.ctx hc) al j hj32 av ad) fun u ⟨uk, ul, up, ut, ud⟩ => ?_)
  have kum : MulKeep b 5696 2048 s u := ak.trans (MulKeep.of_powers uk)
  have ui := hi.keep kum (by decide) (by decide)
  have uc := (uk.counter (by decide) (by decide)).trans ac
  have upt : point (env u.mem b) 0 1 2 3 = after scalar p (16 * j + 16) :=
    up.trans ((congrArg (fun e => point e 0 1 2 3) ae).trans
      (hp.trans (congrArg (after scalar p) (by omega))))
  have utt : ∀ i < 16, tablePoint u.mem b (5696 + 128 * i) = powerPoint p (16 * j + i) := by
    intro i hib
    exact (ut i hib).trans ((congrArg (fun q => powerPoint q i)
      ((smallFrame_table af (by decide) (by omega) (by omega)).trans ht)).trans
      (powerPoint_add p (16 * j) i).symm)
  refine WP.seq (WP.mono (batchBits_ok (kum.ctx hc) count j hj ui.bound ui.fit ui.pointer uc ui.readable)
    fun v ⟨vr, vf, vb⟩ => ?_)
  have kv : MulKeep b 5696 2048 u v := MulKeep.of_bits vr (by decide) vf
  have ve := smallFrame_env vf (by decide)
  have vl := smallFrame_lim vf (by decide) ul
  have vbits : ∀ i < 16, v.mem (State.addr b + BitVec.ofNat 64 (32 + i)) =
      BitVec.ofNat 8 (scalarBit scalar (16 * j + i)).toNat := by
    intro i hib
    exact (vb i hib).trans (congrArg (fun x => BitVec.ofNat 8 (scalarBit x (16 * j + i)).toNat) ui.value)
  refine WP.seq (WP.mono (accumulate16_ok (kv.ctx (kum.ctx hc)) vl (16 * j) scalar p vbits
    ((congrFun ve 16).trans ud) ((congrArg (fun e => point e 0 1 2 3) ve).trans upt)
    (fun i hib => (smallFrame_table vf (by decide) (by omega) (by omega)).trans (utt i hib)))
    fun w ⟨wl, wp, wd, wk⟩ => ?_)
  have kwm : MulKeep b 5696 2048 s w := kum.trans (kv.trans (MulKeep.of_loop wk))
  have wc := wk.counter.trans ((bitsFrame_counter vf).trans uc)
  refine WP.mono (batchTest_ok (kwm.ctx hc) j hj32 wc) fun t ⟨tr, tm, tz⟩ => ?_
  exact ⟨kwm.trans (MulKeep.of_rest tr (by decide) tm), tm ▸ wl,
    (congrArg (fun m => env m b 16) tm).trans wd,
    (congrArg (fun m => point (env m b) 0 1 2 3) tm).trans wp,
    (congrArg (fun m => m.readW (State.addr b + BitVec.ofNat 64 56) 32) tm).trans wc, tz⟩

end VG.Proof.Ed25519.Arm
