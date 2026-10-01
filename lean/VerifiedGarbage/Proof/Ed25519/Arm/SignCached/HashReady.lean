import VerifiedGarbage.Proof.Ed25519.Arm.SignCached.HashInputs
import VerifiedGarbage.Proof.Ed25519.Arm.Whole.HashPre

namespace VG.Proof.Ed25519.Arm.SignCached
open VG VG.Arm
variable {L : Lay}

theorem shaWithin (L : Lay) : Whole.Within (Whole.SHA L.scr) L.SCR :=
  ⟨0, by simp, by change 0 + 192 ≤ 8192; decide⟩
theorem workWithin (L : Lay) : Whole.Within (Whole.WORK L.scr) L.SCR :=
  ⟨192, rfl, by change 192 + 272 ≤ 8192; decide⟩
theorem argsWithin (L : Lay) {n : Nat} (hn : n ≤ 248) :
    Whole.Within (Whole.CALLARGS L.E n) L.FR := ⟨0, by simp, by change 0 + n ≤ 248; omega⟩

theorem init_frame {m n : Mem} (hf : Frame (Whole.initWr L.scr) m n) : Frame (hashWrites L) m n := by
  apply hash_frame hf
  intro r hr; rw [List.mem_singleton.mp hr]
  exact .inl (shaWithin L)

theorem update_frame {m n : Mem} (hf : Frame (Whole.hashWr L.scr) m n) : Frame (hashWrites L) m n := by
  apply hash_frame hf
  simp only [Whole.hashWr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact .inl (shaWithin L)
  · exact .inl (workWithin L)

theorem final_addr (hL : L.Ok) : State.addr (L.E + 184) = State.addr L.E + 184 :=
  frame_addr hL (d := 184) (by decide)

theorem finalize_frame (hL : L.Ok) {m n : Mem} (hf : Frame (Whole.finalizeWr L.scr (L.E + 184)) m n) :
    Frame (hashWrites L) m n := by
  apply hash_frame hf
  simp only [Whole.finalizeWr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact .inl (shaWithin L)
  · exact .inr ⟨0, by rw [final_addr hL]; simp [digest], by change 0 + 64 ≤ 64; decide⟩
  · exact .inl (workWithin L)

theorem final_writes (hL : L.Ok) : ∀ r ∈ Whole.finalizeWr L.scr (L.E + 184),
    Whole.Within r L.FR ∨ ∃ R ∈ L.outputs, Whole.Within r R := by
  apply writes
  simp only [Whole.finalizeWr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact .inr (.inr (shaWithin L))
  · exact .inl ⟨184, final_addr hL, by change 184 + 64 ≤ 248; decide⟩
  · exact .inr (.inr (workWithin L))

theorem update_covers {p n : BitVec 32} (hi : Input L p n) :
    Covers (Whole.updateRd L.E p n ++ Whole.hashWr L.scr) (L.inputs ++ L.FR :: L.outputs) := by
  apply covers
  simp only [Whole.updateRd, Whole.hashWr, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl | rfl)
  · exact hi.cover
  · exact .inl (argsWithin L (by decide))
  · exact .inr ⟨L.SCR, by simp [Lay.outputs], shaWithin L⟩
  · exact .inr ⟨L.SCR, by simp [Lay.outputs], workWithin L⟩

theorem finalize_covers (hL : L.Ok) :
    Covers (Whole.finalizeRd L.E ++ Whole.finalizeWr L.scr (L.E + 184)) (L.inputs ++ L.FR :: L.outputs) := by
  apply covers
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · rw [List.mem_singleton.mp hr]
    exact .inl (argsWithin L (by decide))
  · rcases final_writes hL r hr with hf | ⟨R, hR, hw⟩
    · exact .inl hf
    · exact .inr ⟨R, List.mem_append_right _ hR, hw⟩

def UpdateArgs (L : Lay) (count p n : BitVec 32) (t : State) : Prop :=
  t.gpr .r0 = L.scr ∧ t.gpr .r2 = count ∧ t.gpr .r3 = 0 ∧
    stackArg t 0 = p ∧ stackArg t 1 = n ∧ stackArg t 2 = L.scr + 192

def FinalArgs (L : Lay) (count : BitVec 32) (t : State) : Prop :=
  t.gpr .r0 = L.scr ∧ t.gpr .r2 = count ∧ t.gpr .r3 = 0 ∧
    stackArg t 0 = L.E + 184 ∧ stackArg t 1 = L.scr + 192

theorem update_pre {t : State} (hL : L.Ok) (he : t.sp = L.E)
    {count p n : BitVec 32} (ha : UpdateArgs L count p n t) (hi : Input L p n) :
    Proof.Sha512.updateArm.pre (t.callEntry.withRegions (Whole.updateRd L.E p n) (Whole.hashWr L.scr)) :=
  Whole.update_pre he ha.1 ha.2.2.2.1 ha.2.2.2.2.1 ha.2.2.2.2.2 hi.scratch
    (hL.kc.sub_left (Region.sub_prefix (by decide))) hL.nc hi.fit (by have := hL.top; omega)

theorem finalize_pre {t : State} (hL : L.Ok) (he : t.sp = L.E)
    {count : BitVec 32} (ha : FinalArgs L count t) :
    Proof.Sha512.finalizeArm.pre (t.callEntry.withRegions (Whole.finalizeRd L.E) (Whole.finalizeWr L.scr (L.E + 184))) := by
  refine Whole.finalize_pre he ha.1 ha.2.2.2.1 ha.2.2.2.2 ?_
    (hL.kc.sub_left (Region.sub_prefix (by decide))) ?_ hL.nc
    (frame_fit hL (d := 184) (by decide)) (by have := hL.top; omega)
  · rw [final_addr hL]
    exact hL.kc.sub_left (digestWithin L).sub
  · rw [final_addr hL]
    exact Offset.base_disjoint _ (by decide) (by decide)

theorem count_zero_high (x : BitVec 32) : (0#32) ++ x = BitVec.ofNat 64 x.toNat := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt x.isLt, Nat.shiftLeft_eq]
  have hx := x.isLt
  simp only [BitVec.toNat_ofNat]
  change 0 * 2 ^ 32 + x.toNat = x.toNat % 2 ^ 64
  omega

end VG.Proof.Ed25519.Arm.SignCached
