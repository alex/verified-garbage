import VerifiedGarbage.Proof.Argon2.AArch64.DeriveMetadata

/-! The private frame and called functions stay within the reviewed stack allowance. -/

namespace VG.Proof.Argon2.AArch64.Derive

open VG VG.AArch64

theorem frameStart_wr_member (s : State) (rs : List Reg) (region : Region) (member : region ∈ s.wr) :
    region ∈ (frameStart s rs).wr := by
  induction rs generalizing s with
  | nil => exact List.mem_cons_of_mem _ member
  | cons r rs ih => apply ih; exact List.mem_cons_of_mem _ member

theorem private_wr_member {s t : State} (prepared : PrivatePrepared (prologueState s) t)
    (region : Region) (member : region ∈ s.wr) : region ∈ t.wr := by
  rw [prepared.wr]
  exact frameStart_wr_member s _ region member

theorem private_bp {s t : State} (prepared : PrivatePrepared (prologueState s) t) :
    t.gpr .x19 = s.sp - BitVec.ofNat 64 384 := prepared.bp.trans (prologue_sp s)

theorem private_sp {s t : State} (prepared : PrivatePrepared (prologueState s) t) :
    t.sp = s.sp - BitVec.ofNat 64 384 := prepared.sp.trans (prologue_sp s)

theorem private_stack_minimum {s t : State} (h : AbiEnvironment s)
    (prepared : PrivatePrepared (prologueState s) t) : 16 ≤ t.sp.toNat := by
  rw [private_sp prepared, BitVec.toNat_sub_of_le (by
    rw [BitVec.le_def]
    change 384 ≤ s.sp.toNat
    have := h.stack; omega)]
  change 16 ≤ s.sp.toNat - 384
  have := h.stack; omega

theorem private_frame_sub {s t : State} (prepared : PrivatePrepared (prologueState s) t) :
    Region.Sub ⟨t.gpr .x19, 272⟩ (below (s.sp) 400) := by
  rw [private_bp prepared]
  exact Offset.sub_below _ (by decide) (by decide)

theorem private_stack_sub {s t : State} (prepared : PrivatePrepared (prologueState s) t)
    (n : Nat) (bound : n ≤ 16) : Region.Sub (below (t.sp) n) (below (s.sp) 400) := by
  rw [private_sp prepared]
  unfold below
  rw [BitVec.sub_sub, ← BitVec.ofNat_add]
  exact Offset.sub_below _ (by omega) (by omega)

theorem private_frame_disjoint {s t : State} (h : AbiEnvironment s)
    (prepared : PrivatePrepared (prologueState s) t) (buffer : Region × Bool)
    (member : buffer ∈ abiBuffers s ++ [(abiArguments s, false)]) :
    (⟨t.gpr .x19, 272⟩ : Region).Disjoint buffer.1 :=
  (h.reserved _ (List.mem_singleton_self _) buffer member).sub_left
    (private_frame_sub prepared)

theorem private_stack_disjoint {s t : State} (h : AbiEnvironment s)
    (prepared : PrivatePrepared (prologueState s) t) (buffer : Region × Bool)
    (member : buffer ∈ abiBuffers s ++ [(abiArguments s, false)]) (n : Nat) (bound : n ≤ 16) :
    (below (t.sp) n).Disjoint buffer.1 :=
  (h.reserved _ (List.mem_singleton_self _) buffer member).sub_left
    (private_stack_sub prepared n bound)

theorem private_frame_stack {s t : State} (prepared : PrivatePrepared (prologueState s) t)
    (n : Nat) (bound : n ≤ 16) : (⟨t.gpr .x19, 272⟩ : Region).Disjoint (below (t.sp) n) := by
  rw [prepared.bp, prepared.sp]
  exact Offset.base_disjoint_below _ (by omega)

theorem private_work_member {s t : State} (h : AbiEnvironment s)
    (prepared : PrivatePrepared (prologueState s) t) : abiWork s ∈ t.wr := by
  apply private_wr_member prepared
  rw [h.wr]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..)

end VG.Proof.Argon2.AArch64.Derive
