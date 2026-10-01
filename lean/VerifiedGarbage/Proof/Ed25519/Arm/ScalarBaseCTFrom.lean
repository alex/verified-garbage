import VerifiedGarbage.Proof.Ed25519.Arm.ScalarBaseCTMul
import VerifiedGarbage.Proof.Ed25519.Arm.PointFromScalar

/-! Public scalar pointers remain public across point preparation. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

def pointFromPrepareCT : Prog isa :=
  .seq (.block [.str .r12 .r0 52]) (fieldCode [.const 16 Spec.Ed25519.d])

def FromCTPre (base ptr : BitVec 32) (count : Nat) (s : State) : Prop :=
  Ctx base s ∧ AllLim s.mem base ∧ s.gpr .r12 = ptr ∧ ptr.toNat + 2 * count ≤ 2 ^ 32 ∧
    (∀ i < 2 * count, InRegions (s.rd ++ s.wr) (State.addr ptr + BitVec.ofNat 64 i) 1) ∧
    (⟨State.addr ptr, 2 * count⟩ : Region).Disjoint ⟨State.addr base, 8192⟩

theorem pointFromPrepareCT_ok {s : State} {base ptr : BitVec 32}
    (count : Nat) (hn : count ≤ 32) (h : FromCTPre base ptr count s) :
    WP isa pointFromPrepareCT s (MulCTPre base ptr count
      (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (State.addr ptr) (2 * count)))) := by
  obtain ⟨hc, hl, hp, hfit, hr, hsep⟩ := h
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
  refine WP.mono (fieldCode_ok [.const 16 Spec.Ed25519.d] (uk.ctx hc)
    (smallFrame_lim uf (by decide) hl)) fun v ⟨vk, vl, ve⟩ => ?_
  have vm : MulKeep base 1600 6144 u v := MulKeep.of_powers (PowersKeep.of_keep vk)
  have vd : env v.mem base 16 = Spec.Ed25519.d := by rw [ve]; rfl
  exact ⟨vk.ctx (uk.ctx hc), vl, ui.keep vm (by decide) (by decide), vd⟩

theorem pointFromScalar_ct (base ptr : BitVec 32) (count : Nat) (hn : count = 16 ∨ count = 32) :
    CT (fun x y => FromCTPre base ptr count x ∧ FromCTPre base ptr count y)
      (pointFromScalar count) (fun _ _ => True) := by
  have hc : CT (fun x y => FromCTPre base ptr count x ∧ FromCTPre base ptr count y)
      pointFromPrepareCT (fun _ _ => True) := by
    apply ctRegs [.r0, .r12] _ (by taint_decide)
    intro x y h r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.1.1.r0.trans h.2.1.r0.symm
    · exact h.1.2.2.1.trans h.2.2.2.1.symm
  have hb : count ≤ 32 := by rcases hn with rfl | rfl <;> decide
  intro x y tx ty u v h ex ey
  cases ex with
  | seq es ex =>
    cases ex with
    | seq ef em =>
      cases ey with
      | seq fs ey =>
        cases ey with
        | seq ff fm =>
          have exi := Exec.seq es ef
          have eyi := Exec.seq fs ff
          have ht := (hc _ _ _ _ _ _ h exi eyi).1
          obtain ⟨_, a, ea, ha⟩ := pointFromPrepareCT_ok count hb h.1
          obtain ⟨_, b, eb, hb⟩ := pointFromPrepareCT_ok count hb h.2
          obtain ⟨_, rfl⟩ := Exec.det exi ea
          obtain ⟨_, rfl⟩ := Exec.det eyi eb
          have hm := (pointMultiply_ct base ptr count _ _ hn _ _ _ _ _ _ ⟨ha, hb⟩ em fm).1
          exact ⟨by simpa only [List.append_assoc] using congrArg₂ (fun (a b : List Leak) => a ++ b) ht hm, trivial⟩

end VG.Proof.Ed25519.Arm
