import VerifiedGarbage.Proof.Ed25519.Arm.VerifyFrame
import VerifiedGarbage.Proof.Ed25519.Arm.PointFromScalar

/-! Untrusted: readable public inputs remain outside all verification writes. -/
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
