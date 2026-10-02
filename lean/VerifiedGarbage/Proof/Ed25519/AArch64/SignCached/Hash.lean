import VerifiedGarbage.Proof.Ed25519.AArch64.SignCached.Calls
import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.HashPre

namespace VG.Proof.Ed25519.AArch64.SignCached
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.SignCached

abbrev Backend := Whole.Backend
def hashWrites (L : Lay) : List Region := [L.SCR, digest L, L.CK]

theorem hash_frame {L : Lay} {m n : Mem} {ws : List Region} (hf : Frame ws m n)
    (hw : ∀ r ∈ ws, Region.Sub r L.SCR ∨ Region.Sub r (digest L) ∨ Region.Sub r L.CK) :
    Frame (hashWrites L) m n := by
  refine Frame.sub hf fun r hr => ?_
  rcases hw r hr with hs | hd | hk
  · exact ⟨L.SCR, by simp [hashWrites], hs⟩
  · exact ⟨digest L, by simp [hashWrites], hd⟩
  · exact ⟨L.CK, by simp [hashWrites], hk⟩

theorem init_frame {L : Lay} {m n : Mem} (hf : Frame (Whole.initWr L.scr) m n) :
    Frame (hashWrites L) m n := by
  apply hash_frame hf
  intro r hr; rw [List.mem_singleton.mp hr]
  exact .inl (Whole.sha_sub L.scr)

theorem update_frame {L : Lay} {m n : Mem} (hf : Frame (Whole.hashWr L.scr ++ [L.CK]) m n) :
    Frame (hashWrites L) m n := by
  apply hash_frame hf
  simp only [Whole.hashWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact .inl (Whole.sha_sub L.scr)
  · exact .inl (Whole.work_sub L.scr)
  · exact .inr (.inr fun _ h => h)

theorem finalize_frame {L : Lay} {m n : Mem}
    (hf : Frame (Whole.finalizeWr L.scr (L.E + 192) ++ [L.CK]) m n) : Frame (hashWrites L) m n := by
  apply hash_frame hf
  simp only [Whole.finalizeWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl | rfl)
  · exact .inl (Whole.sha_sub L.scr)
  · exact .inr (.inl fun _ h => h)
  · exact .inl (Whole.work_sub L.scr)
  · exact .inr (.inr fun _ h => h)

theorem final_writes (L : Lay) :
    ∀ r ∈ Whole.finalizeWr L.scr (L.E + 192),
      Whole.Within r L.FR ∨ ∃ R ∈ L.outputs, Whole.Within r R := by
  simp only [Whole.finalizeWr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact .inr ⟨L.SCR, by simp [Lay.outputs], 0, by simp, by change 0+192≤8192; decide⟩
  · exact .inl (digestWithin L)
  · exact .inr ⟨L.SCR, by simp [Lay.outputs], 192, rfl, by change 192+224≤8192; decide⟩

variable {L : Lay} {g : Reg → BitVec 64} {vec : VReg → BitVec 128} {m₀ : Mem} {s : State}

theorem init_step (hc : Ctx L g vec m₀ s) (hL : L.Ok) (ha : Arguments L m₀) :
    WP isa init s fun t => Ctx L g vec m₀ t ∧ Frame (hashWrites L) s.mem t.mem ∧
      Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem L.scr [] := by
  refine WP.seq (WP.mono (args_ok hc hL ha (args := [(.x0, .caller 5 0)])
    (by decide) (by simp [Whole.valid]) (by simp [preserved])) fun u ⟨hu, hm, hs⟩ => ?_)
  have a0 := hs (.x0, .caller 5 0) (by simp)
  change u.gpr .x0 = L.scr + 0#64 at a0
  rw [BitVec.add_zero] at a0
  have hw := Whole.init_writes (E := L.E) (wr := L.outputs) (by simp [Lay.outputs] : L.SCR ∈ L.outputs)
  refine WP.mono (Whole.init_call hu (Whole.init_pre a0) (Whole.covers_writes hw) hw a0)
    fun t ⟨ht, hf, hp⟩ => ⟨ht, ?_, hp⟩
  rw [hm] at hf
  exact init_frame hf

structure Input (L : Lay) (p n : Addr) : Prop where
  cover : Whole.Within ⟨p, n.toNat⟩ L.FR ∨ ∃ R ∈ L.inputs ++ L.outputs, Whole.Within ⟨p,n.toNat⟩ R
  scratch : Region.Disjoint ⟨p,n.toNat⟩ L.SCR

/-- A hashed input is outside the frame of the hash function's calls. -/
theorem Input.ck {p n : Addr} (hL : L.Ok) (hi : Input L p n) : L.CK.Disjoint ⟨p, n.toNat⟩ := by
  rcases hi.cover with ⟨off, hb, hl⟩ | ⟨R, hR, hw⟩
  · simp only at hb hl
    rw [hb]
    exact Whole.ck_frame (by change off + n.toNat ≤ 256 at hl; omega)
  · refine Region.Disjoint.sub_right ?_ hw.sub
    simp only [Lay.outputs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with hR | rfl | rfl
    · exact hL.ck R hR
    · exact hL.co
    · exact hL.cc

theorem update_covers {p n : Addr} (hi : Input L p n) :
    Covers (Whole.updateRd p n ++ Whole.hashWr L.scr) (L.inputs ++ L.FR :: L.outputs) := by
  apply covers
  simp only [Whole.updateRd, Whole.hashWr, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact hi.cover
  · exact .inr ⟨L.SCR, by simp [Lay.outputs], 0, by simp, by change 0+192≤8192; decide⟩
  · exact .inr ⟨L.SCR, by simp [Lay.outputs], 192, rfl, by change 192+224≤8192; decide⟩

end VG.Proof.Ed25519.AArch64.SignCached
