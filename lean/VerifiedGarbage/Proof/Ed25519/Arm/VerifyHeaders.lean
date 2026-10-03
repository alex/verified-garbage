import VerifiedGarbage.Impl.Ed25519.Arm.PointTableIO
import VerifiedGarbage.Proof.Ed25519.Arm.PointKeep
import VerifiedGarbage.Proof.Ed25519.Arm.ScalarPass
import VerifiedGarbage.Proof.Ed25519.Arm.PointEqual
import VerifiedGarbage.Proof.Ed25519.Arm.PointFromScalar
import VerifiedGarbage.Impl.Ed25519.Arm.Verify

/-! Merged from `Proof.Ed25519.Arm.VerifyContext`. -/
section
/-! Merged from `Proof.Ed25519.Arm.VerifyFrame`. -/
section
/-! Merged from `Proof.Ed25519.Arm.PointTableIO`. -/
section
/-! Save and reload the verification equation's packed points. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem scratchAddr_ok {b : BitVec 32} {s : State} (hc : Ctx b s) (o : Nat) (ho : o < 8192) :
    WP isa (.block (scratchAddr o)) s fun t => Rest [.r12] s t ∧ t.mem = s.mem ∧
      t.gpr .r12 = b + BitVec.ofNat 32 o := by
  refine wp_movw fun u hu => wp_dp (op2_reg _ _) fun t ht => WP.block_nil ?_
  refine ⟨(hu.rest (by decide)).trans (ht.rest (by decide)), by rw [ht.mem, hu.mem], ?_⟩
  rw [ht.gpr]
  change u.gpr .r0 + u.gpr .r12 = _
  rw [hu.other _ (by decide), hc.r0, hu.gpr]
  refine congrArg (b + ·) (BitVec.eq_of_toNat_eq ?_)
  rw [movw_nat (by omega), toNat_imm (by omega)]

theorem pointTableWrite_ok {b : BitVec 32} {s : State} (hc : Ctx b s) (hl : AllLim s.mem b)
    (o : Nat) (ho : 1600 ≤ o) (hn : o + 128 ≤ 8192) :
    WP isa (.block (pointTableWrite o)) s fun t => PowersKeep b o 128 s t ∧ AllLim t.mem b ∧
      env t.mem b = env s.mem b ∧ tablePoint t.mem b o = point (env s.mem b) 0 1 2 3 := by
  unfold pointTableWrite
  rw [WP.block_append_iff]
  refine WP.mono (scratchAddr_ok hc o (by omega)) fun u ⟨ur, um, up⟩ => ?_
  refine WP.mono (pointToTable_ok (hc.of_rest ur (by decide)) (um ▸ hl) up ho hn) fun t ⟨tp, tk⟩ => ?_
  exact ⟨⟨(ur.mono (by decide)).trans (tk.rest.mono (by decide)), by rw [← um]; exact TableFrame.table tk.frame⟩,
    tk.lim ho hn (um ▸ hl), (tk.env ho hn).trans (congrArg (fun m => env m b) um),
    tp.trans (congrArg (fun m => point (env m b) 0 1 2 3) um)⟩

theorem pointTableRead_ok {b : BitVec 32} {s : State} (hc : Ctx b s) (hl : AllLim s.mem b)
    (o : Nat) (ho : 1600 ≤ o) (hn : o + 128 ≤ 8192) :
    WP isa (.block (pointTableRead o)) s fun t => AccKeep b s t ∧ AllLim t.mem b ∧
      point (env t.mem b) 0 1 2 3 = tablePoint s.mem b o ∧
      ∀ i : Slot, 4 ≤ i.val → env t.mem b i = env s.mem b i := by
  unfold pointTableRead
  rw [WP.block_append_iff]
  refine WP.mono (scratchAddr_ok hc o (by omega)) fun u ⟨ur, um, up⟩ => ?_
  refine WP.mono (pointFromTable_ok (hc.of_rest ur (by decide)) (um ▸ hl) up ho hn) fun t ⟨tp, tl, tk⟩ => ?_
  refine ⟨(AccKeep.of_rest ur (by decide) um).trans (AccKeep.of_table tk (by decide) (by decide)), tl,
    tp.trans (congrArg (fun m => tablePoint m b o) um), fun i hi => ?_⟩
  exact (tk.high i hi).trans (congrArg (fun m => env m b i) um)

end VG.Proof.Ed25519.Arm
end

/-! Merged from `Proof.Ed25519.Arm.ScalarCompare`. -/
section
/-! A canonical-scalar check for the public verification inputs. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem scalarCompare_ok {b : BitVec 32} {s : State} (hc : Ctx b s)
    (hl : Lim s.mem (State.addr b) SR) :
    WP isa (.block scalarCompare) s fun t =>
      Rest [.r2, .r3, .r4, .r5, .r6] s t ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 SD, 64⟩] s.mem t.mem ∧
      (t.gpr .r5).toNat = if V s.mem (State.addr b) SR < Spec.Ed25519.L then 0 else 1 := by
  unfold scalarCompare
  simp only [List.cons_append, List.nil_append]
  refine wp_movw fun u hu => wp_mov (op2_imm (by decide)) fun v hv => ?_
  have kv : Rest [.r5, .r6] s v := (hu.rest (by decide)).trans (hv.rest (by decide))
  have mv : v.mem = s.mem := by rw [hv.mem, hu.mem]
  have hcv := hc.of_rest kv (by decide)
  refine WP.mono (scalarSubtractPass_ok hcv (mv ▸ hl) (by rw [hv.gpr]; rfl)
    (by rw [hv.other _ (by decide), hu.gpr])) fun t ht => ?_
  refine ⟨(kv.mono (by decide)).trans (ht.rest.mono (by decide)), ?_, ?_⟩
  · have hf := ht.frame; rwa [hcv.r0, mv] at hf
  · rw [ht.r5, mv, scalarCompare_carry (V_lt hl)]
    rfl

end VG.Proof.Ed25519.Arm
end

/-! Verification preserves the ABI saves and all public input headers. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

abbrev verifyRegion (b : BitVec 32) : Region := ⟨State.addr b + BitVec.ofNat 64 32, 8096⟩
structure VerifyKeep (b : BitVec 32) (s t : State) : Prop where
  rest : Rest powersClob s t
  frame : Frame [verifyRegion b] s.mem t.mem

theorem VerifyKeep.refl (b : BitVec 32) (s : State) : VerifyKeep b s s := ⟨Rest.refl _ _, Frame.refl _ _⟩
theorem VerifyKeep.ctx {b : BitVec 32} {s t : State} (h : VerifyKeep b s t) (hc : Ctx b s) : Ctx b t :=
  hc.of_rest h.rest (by decide)
theorem VerifyKeep.trans {b : BitVec 32} {s t u : State} (h : VerifyKeep b s t) (k : VerifyKeep b t u) :
    VerifyKeep b s u := ⟨h.rest.trans k.rest, h.frame.trans k.frame⟩
theorem VerifyKeep.of_small {b : BitVec 32} {s t : State} {o n : Nat} {ws : List Reg}
    (hr : Rest ws s t) (hw : ∀ r ∈ ws, r ∈ powersClob)
    (hf : Frame [⟨State.addr b + BitVec.ofNat 64 o, n⟩] s.mem t.mem) (ho : 32 ≤ o) (hn : o + n ≤ 8128) :
    VerifyKeep b s t := ⟨hr.mono hw, hf.sub fun r hm => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hm]; exact Offset.sub _ ho hn⟩⟩
theorem VerifyKeep.of_point {b : BitVec 32} {s t : State} (h : PointKeep b s t) : VerifyKeep b s t := by
  refine ⟨h.rest, h.frame.sub fun r hr => ?_⟩
  simp only [pointRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩
theorem VerifyKeep.of_powers {b : BitVec 32} {o n : Nat} {s t : State}
    (h : PowersKeep b o n s t) (ho : 32 ≤ o) (hn : o + n ≤ 8128) : VerifyKeep b s t := by
  refine ⟨h.rest, h.frame.sub fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩
  · exact ⟨_, List.mem_singleton_self _, Offset.sub _ ho hn⟩
theorem VerifyKeep.of_keep {b : BitVec 32} {s t : State} (h : Keep b s t) : VerifyKeep b s t :=
  VerifyKeep.of_point (PointKeep.of_keep h)
theorem VerifyKeep.of_acc {b : BitVec 32} {s t : State} (h : AccKeep b s t) : VerifyKeep b s t :=
  VerifyKeep.of_powers (PowersKeep.of_acc h) (o := 1600) (n := 0) (by decide) (by decide)
theorem VerifyKeep.of_decode {b : BitVec 32} {s t : State} (h : DecodeKeep b s t) : VerifyKeep b s t := by
  refine ⟨h.rest.mono (by decide), h.frame.sub fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩
theorem VerifyKeep.of_rest {b : BitVec 32} {s t : State} {ws : List Reg}
    (hr : Rest ws s t) (hw : ∀ r ∈ ws, r ∈ powersClob) (hm : t.mem = s.mem) : VerifyKeep b s t :=
  ⟨hr.mono hw, by rw [hm]; exact Frame.refl _ _⟩

theorem VerifyKeep.header {b : BitVec 32} {s t : State} (h : VerifyKeep b s t)
    (d : Nat) (hd : 8128 ≤ d) (hn : d + 4 ≤ 8192) :
    t.mem.readW (State.addr b + BitVec.ofNat 64 d) 32 = s.mem.readW (State.addr b + BitVec.ofNat 64 d) 32 := by
  apply BitVec.eq_of_toNat_eq
  exact wd_frame h.frame fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact Offset.disjoint _ (.inr (by omega)) (by omega) (by decide)

end VG.Proof.Ed25519.Arm
end

/-! Readable public inputs remain outside all verification writes. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

structure VerifyInput (b ptr : BitVec 32) (len : Nat) (s : State) : Prop where
  fit : ptr.toNat + len ≤ 2 ^ 32
  readable : ∀ i < len, InRegions (s.rd ++ s.wr) (State.addr ptr + BitVec.ofNat 64 i) 1
  separate : (⟨State.addr ptr, len⟩ : Region).Disjoint ⟨State.addr b, 8192⟩

theorem VerifyInput.keep {b ptr : BitVec 32} {len : Nat} {s t : State}
    (h : VerifyInput b ptr len s) (hk : VerifyKeep b s t) : VerifyInput b ptr len t :=
  ⟨h.fit, fun i hi => by rw [hk.rest.rd, hk.rest.wr]; exact h.readable i hi, h.separate⟩

theorem VerifyInput.bytes {b ptr : BitVec 32} {len : Nat} {s t : State}
    (h : VerifyInput b ptr len s) (hk : VerifyKeep b s t) :
    Spec.Ed25519.bytesAt t.mem (State.addr ptr) len = Spec.Ed25519.bytesAt s.mem (State.addr ptr) len := by
  unfold Spec.Ed25519.bytesAt
  refine List.map_congr_left fun i hi => hk.frame.bytes (R := ⟨State.addr ptr, len⟩)
    (fun r hr => ?_) (by have := h.fit; omega : len ≤ 2 ^ 64) (List.mem_range.mp hi)
  rw [List.mem_singleton.mp hr]
  exact h.separate.sub_right (Offset.sub_base _ (by decide))

theorem VerifyInput.prefix {b ptr : BitVec 32} {len n : Nat} {s : State}
    (h : VerifyInput b ptr len s) (hn : n ≤ len) : VerifyInput b ptr n s :=
  ⟨by have := h.fit; omega, fun i hi => h.readable i (by omega), h.separate.sub_left (Region.sub_prefix hn)⟩

theorem VerifyInput.suffix32 {b ptr : BitVec 32} {s : State} (h : VerifyInput b ptr 64 s) :
    VerifyInput b (ptr + 32) 32 s := by
  have en : (ptr + (32 : BitVec 32)).toNat = ptr.toNat + 32 := by
    rw [toNat_add_lt (by have := h.fit; change ptr.toNat + 32 < 2 ^ 32; omega)]
    rfl
  have ep : State.addr (ptr + (32 : BitVec 32)) = State.addr ptr + BitVec.ofNat 64 32 := addr_add (k := 32) (by have := h.fit; omega)
  refine ⟨by rw [en]; have := h.fit; omega, ?_, ?_⟩
  · intro i hi
    rw [ep, Offset.add_add]
    exact h.readable (32 + i) (by omega)
  · rw [ep]
    exact h.separate.sub_left (Offset.sub_base _ (by decide))

structure VerifyContext (b pk sig challenge : BitVec 32) (s : State) : Prop where
  ctx : Ctx b s
  pkInput : VerifyInput b pk 32 s
  sigInput : VerifyInput b sig 64 s
  challengeInput : VerifyInput b challenge 64 s
  pkHeader : s.mem.readW (State.addr b + BitVec.ofNat 64 8128) 32 = pk
  sigHeader : s.mem.readW (State.addr b + BitVec.ofNat 64 8132) 32 = sig
  challengeHeader : s.mem.readW (State.addr b + BitVec.ofNat 64 8136) 32 = challenge

theorem VerifyContext.keep {b pk sig challenge : BitVec 32} {s t : State}
    (h : VerifyContext b pk sig challenge s) (hk : VerifyKeep b s t) : VerifyContext b pk sig challenge t :=
  ⟨hk.ctx h.ctx, h.pkInput.keep hk, h.sigInput.keep hk, h.challengeInput.keep hk,
    (hk.header _ (by decide) (by decide)).trans h.pkHeader,
    (hk.header _ (by decide) (by decide)).trans h.sigHeader,
    (hk.header _ (by decide) (by decide)).trans h.challengeHeader⟩

end VG.Proof.Ed25519.Arm
end

/-! Load a public argument pointer from the protected header area. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem loadHeader_ok {b : BitVec 32} {s : State} (hc : Ctx b s) (d : Nat) (hd : d + 4 ≤ 8192) :
    WP isa (.block (loadHeader d)) s fun t => Rest [.r12] s t ∧ t.mem = s.mem ∧
      t.gpr .r12 = s.mem.readW (State.addr b + BitVec.ofNat 64 d) 32 := by
  unfold loadHeader
  rw [WP.block_append_iff]
  refine WP.mono (scratchAddr_ok hc d (by omega)) fun u ⟨ur, um, up⟩ => ?_
  refine wp_ldr (a := State.addr b + BitVec.ofNat 64 d) (by decide)
    (by rw [up]; exact (congrArg State.addr (BitVec.add_zero _)).trans (hc.ptr_addr (by omega)))
    (by rw [ur.rd, ur.wr]; exact in_base (List.mem_append_right _ hc.wr) hd (by omega))
    fun t ht => WP.block_nil ⟨ur.trans (ht.rest (by decide)), ht.mem.trans um, ?_⟩
  rw [ht.gpr, um]

theorem addInput32_ok (s : State) :
    WP isa (.block [.dp .add .r12 .r12 (.imm 32)]) s fun t => Rest [.r12] s t ∧ t.mem = s.mem ∧
      t.gpr .r12 = s.gpr .r12 + 32 := by
  refine wp_dp (op2_imm (by decide)) fun t ht => WP.block_nil ⟨ht.rest (by decide), ht.mem, ht.gpr⟩

end VG.Proof.Ed25519.Arm
