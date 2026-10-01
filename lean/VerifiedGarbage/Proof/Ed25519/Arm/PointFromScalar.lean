import VerifiedGarbage.Impl.Ed25519.Arm.PointFromScalar
import VerifiedGarbage.Proof.Ed25519.Arm.PointMul
import VerifiedGarbage.Proof.Ed25519.Arm.PointKeep
import VerifiedGarbage.Proof.Ed25519.Bytes

/-! Untrusted: scalar multiplication reads either all 256 or all 512 input bits. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem packedDigits_decode (m : Mem) (ptr : Addr) (n : Nat) :
    val16 (packedLimb m ptr) n = Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m ptr (2 * n)) := by
  rw [decodeLE_eq]
  exact (leNum_bytesAt2 m ptr n).symm

theorem packedDigits_frame {m m' : Mem} {ptr : Addr} {n : Nat} {rs : List Region}
    (hf : Frame rs m m') (hn : n ≤ 32) (hs : ∀ r ∈ rs, (⟨ptr, 2 * n⟩ : Region).Disjoint r) :
    val16 (packedLimb m' ptr) n = val16 (packedLimb m ptr) n := by
  apply val16_congr
  intro k hk
  have hb : ∀ i < 2 * n, m' (ptr + BitVec.ofNat 64 i) = m (ptr + BitVec.ofNat 64 i) :=
    fun i hi => hf.bytes hs (by omega : 2 * n ≤ 2 ^ 64) hi
  simp only [packedLimb, byteN, hb (2 * k) (by omega), hb (2 * k + 1) (by omega)]

theorem pointFromScalar_ok {s : State} {base ptr : BitVec 32} (hc : Ctx base s) (hl : AllLim s.mem base)
    (hp : s.gpr .r12 = ptr) (count : Nat) (hn0 : 0 < count) (hn : count ≤ 32)
    (hfit : ptr.toNat + 2 * count ≤ 2 ^ 32)
    (hr : ∀ i < 2 * count, InRegions (s.rd ++ s.wr) (State.addr ptr + BitVec.ofNat 64 i) 1)
    (hsep : (⟨State.addr ptr, 2 * count⟩ : Region).Disjoint ⟨State.addr base, 8192⟩) :
    WP isa (pointFromScalar count) s fun t => PointKeep base s t ∧ AllLim t.mem base ∧
      env t.mem base 16 = Spec.Ed25519.d ∧ point (env t.mem base) 0 1 2 3 =
        Spec.Ed25519.pointMul (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (State.addr ptr) (2 * count)))
          (point (env s.mem base) 0 1 2 3) := by
  refine WP.seq (str0_ok hc (by decide) fun u hu => WP.block_nil ?_)
  have uf : Frame [⟨State.addr base + BitVec.ofNat 64 52, 4⟩] s.mem u.mem := by
    rw [hu.mem]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have uk : PointKeep base s u := PointKeep.of_small (hu.rest []) (by decide) uf (by decide) (by decide)
  have ue := smallFrame_env uf (by decide)
  have ui : MulInput base ptr count (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (State.addr ptr) (2 * count))) u := by
    refine ⟨hn, hfit, ?_, hsep, ?_, ?_⟩
    · intro i hi
      rw [hu.rd, hu.wr]
      exact hr i hi
    · rw [hu.mem, Mem.readW_writeW_self32, hp]
    · exact (packedDigits_frame uf hn (fun r hm => by
        rw [List.mem_singleton.mp hm]; exact hsep.sub_right (Offset.sub_base _ (by decide)))).trans
        (packedDigits_decode _ _ count)
  refine WP.seq (WP.mono (fieldCode_ok [.const 16 Spec.Ed25519.d] (uk.ctx hc)
    (smallFrame_lim uf (by decide) hl)) fun v ⟨vk, vl, ve⟩ => ?_)
  have vm : MulKeep base 1600 6144 u v := MulKeep.of_powers (PowersKeep.of_keep vk)
  have vd : env v.mem base 16 = Spec.Ed25519.d := by rw [ve]; rfl
  have vp : point (env v.mem base) 0 1 2 3 = point (env s.mem base) 0 1 2 3 := by
    rw [ve]
    change point (env u.mem base) 0 1 2 3 = _
    exact congrArg (fun e => point e 0 1 2 3) ue
  refine WP.mono (pointMultiply_ok (vk.ctx (uk.ctx hc)) vl count _
    (ui.keep vm (by decide) (by decide)) hn0 vd) fun t ⟨tk, tl, td, tp⟩ => ?_
  exact ⟨(uk.trans (PointKeep.of_keep vk)).trans (PointKeep.of_mul tk), tl, td,
    tp.trans (congrArg (Spec.Ed25519.pointMul _) vp)⟩

end VG.Proof.Ed25519.Arm
