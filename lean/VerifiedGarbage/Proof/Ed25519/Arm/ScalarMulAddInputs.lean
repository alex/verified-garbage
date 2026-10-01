import VerifiedGarbage.Proof.Ed25519.Arm.ScalarLoadInput

/-! Prepare the three arbitrary, unreduced 256-bit scalar inputs. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

def ScalarInputs (b : BitVec 32) (m : Mem) (p : Nat → BitVec 32) (n : Nat) (t : State) : Prop :=
  ∀ i < n, Lim t.mem (State.addr b) (64 + 64 * i) ∧
    V t.mem (State.addr b) (64 + 64 * i) =
      Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m (State.addr (p i)) 32)

structure ScalarInputsInv (b : BitVec 32) (s0 : State) (p : Nat → BitVec 32) (n : Nat) (t : State) : Prop where
  rest : Rest [.r2, .r3, .r12] s0 t
  frame : Frame [⟨State.addr b + BitVec.ofNat 64 64, 64 * n⟩] s0.mem t.mem
  values : ScalarInputs b s0.mem p n t

theorem scalarInputsLoop_ok {b : BitVec 32} {s : State} (hc : Ctx b s)
    {p : Nat → BitVec 32}
    (hp : ∀ i < 3, s.mem.readW (State.addr b + BitVec.ofNat 64 (36 + 4 * i)) 32 = p i)
    (hfit : ∀ i < 3, (p i).toNat + 32 ≤ 2 ^ 32)
    (hr : ∀ i < 3, (⟨State.addr (p i), 32⟩ : Region) ∈ s.rd ++ s.wr)
    (hsep : ∀ i < 3, (⟨State.addr (p i), 32⟩ : Region).Disjoint ⟨State.addr b, 8192⟩) :
    WP isa (.block ((List.range 3).flatMap fun i => scalarLoadInput (64 + 64 * i) (36 + 4 * i))) s
      (ScalarInputsInv b s p 3) := by
  refine wp_range_flatMap (M := isa) (ScalarInputsInv b s p)
    (fun n t hn ht => ?_) 3 (Nat.le_refl _) s
    ⟨Rest.refl _ _, Frame.refl _ _, fun _ h => by omega⟩
  have hct := hc.of_rest ht.rest (by decide)
  have ptr : t.mem.readW (State.addr b + BitVec.ofNat 64 (36 + 4 * n)) 32 = p n := by
    rw [ht.frame.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide), hp n hn]
    rw [List.mem_singleton.mp hr]
    exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)
  refine WP.mono (scalarLoadInput_ok hct (by omega) (by omega) ptr (hfit n hn)
    (by rw [ht.rest.rd, ht.rest.wr]; exact hr n hn) (hsep n hn)) fun u ⟨ku, fu, lu, vu⟩ => ?_
  refine ⟨ht.rest.trans ku, ?_, fun i hi => ?_⟩
  · exact (ht.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by omega)⟩).trans
      (fu.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        rw [List.mem_singleton.mp hr]; exact Offset.sub _ (by omega) (by omega)⟩)
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · have eq : ∀ k < 16, limb u.mem (State.addr b) (64 + 64 * i) k =
          limb t.mem (State.addr b) (64 + 64 * i) k :=
        limb_frame fu fun r hr k hk => by
          rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)
      exact ⟨fun k hk => by rw [eq k hk]; exact (ht.values i hi).1 k hk,
        (val16_congr eq).trans (ht.values i hi).2⟩
    · refine ⟨lu, ?_⟩
      rw [vu]
      apply congrArg Spec.Ed25519.decodeLE
      unfold Spec.Ed25519.bytesAt
      refine List.map_congr_left fun k hk => ht.frame.bytes
        (R := ⟨State.addr (p i), 32⟩) (fun r hr => ?_) (by decide : 32 ≤ 2 ^ 64) (List.mem_range.mp hk)
      rw [List.mem_singleton.mp hr]
      exact (hsep i hn).sub_right (Offset.sub_base _ (by omega))

theorem scalarMulAddInputs_ok {b q : BitVec 32} {s : State} (hc : Ctx b s)
    {p : Nat → BitVec 32}
    (hp : ∀ i < 3, s.mem.readW (State.addr b + BitVec.ofNat 64 (36 + 4 * i)) 32 = p i)
    (hfit : ∀ i < 3, (p i).toNat + 32 ≤ 2 ^ 32)
    (hr : ∀ i < 3, (⟨State.addr (p i), 32⟩ : Region) ∈ s.rd ++ s.wr)
    (hsep : ∀ i < 3, (⟨State.addr (p i), 32⟩ : Region).Disjoint ⟨State.addr b, 8192⟩)
    (hout : s.mem.readW (State.addr b + BitVec.ofNat 64 32) 32 = q) :
    WP isa (.block scalarMulAddInputs) s fun t =>
      Rest [.r2, .r3, .r10, .r12] s t ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 64, 192⟩] s.mem t.mem ∧
      ScalarInputs b s.mem p 3 t ∧ t.gpr .r10 = q := by
  unfold scalarMulAddInputs
  refine WP.append (scalarInputsLoop_ok hc hp hfit hr hsep) fun u hu => ?_
  refine ldr0_ok (hc.of_rest hu.rest (by decide)) (by decide) fun t ht => WP.block_nil ?_
  refine ⟨(hu.rest.mono (by decide)).trans (ht.rest (by decide)), by rw [ht.mem]; exact hu.frame,
    fun i hi => by rw [show t.mem = u.mem from ht.mem]; exact hu.values i hi, ?_⟩
  rw [ht.gpr, hu.frame.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide), hout]
  rw [List.mem_singleton.mp hr]
  exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide)

end VG.Proof.Ed25519.Arm
