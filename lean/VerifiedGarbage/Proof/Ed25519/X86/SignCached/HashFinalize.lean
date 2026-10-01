import VerifiedGarbage.Proof.Ed25519.X86.SignCached.FinalizeArgs

namespace VG.Proof.Ed25519.X86.SignCached
open VG VG.X86 VG.Impl.Ed25519.X86.SignCached

variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

theorem digest_addr (hL : L.Ok) : (L.E + 192).setWidth 64 = L.E.setWidth 64 + 192 :=
  addr_eq (x := L.E) (k := 192) (by have := hL.top; omega)

theorem digestWithin (hL : L.Ok) : Whole.Within ⟨(L.E + 192).setWidth 64, 64⟩ L.FR :=
  ⟨192, digest_addr hL, by change 192 + 64 ≤ 256; decide⟩

theorem digest_below (hL : L.Ok) : (below L.E 24).Disjoint ⟨(L.E + 192).setWidth 64, 64⟩ := by
  change Region.Disjoint ⟨(L.E - BitVec.ofNat 32 24).setWidth 64, 24⟩ _
  rw [Taint.sub_setWidth hL.below, digest_addr hL]
  exact (Offset.disjoint_below _ (n := 24) (d := 192) (k := 64) (by decide)).symm

theorem finalize_step (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀)
    (n : Nat) (hn : n < 2 ^ 32) (b : Bool) {msg : List Byte}
    (hlen : msg.length < 2 ^ 64) (hcount : (if b then L.len.toNat else 0) + n = msg.length)
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 s.mem (L.scr.setWidth 64) msg) :
    WP isa (finalize n b) s fun t => Ctx L g m₀ t ∧ Frame (hashWrites L) s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem (L.E.setWidth 64 + 192) 64 = Spec.Sha512.sha512 msg := by
  refine WP.seq (WP.mono (finalizeArgs_ok hc hL ha n hn b) fun u ⟨hu, hf, a0, a3, a4, ac⟩ => ?_)
  have H := hashSpace hL
  have fit : (L.E + 192).toNat + 64 ≤ 2 ^ 32 := by
    rw [BitVec.toNat_add, show (192 : BitVec 32).toNat = 192 from rfl,
      Nat.mod_eq_of_lt (by have := hL.top; omega)]
    have := hL.top; omega
  have hd : Region.Disjoint ⟨(L.E + 192).setWidth 64, 64⟩ L.SCR :=
    hL.kc.sub_left (fun p hp => Whole.frame_sub L.E p ((digestWithin hL).sub p hp))
  have hp := Whole.finalize_pre hu.esp H a0 a3 a4 hd (digest_below hL) (by
    rw [digest_addr hL]
    exact Offset.base_disjoint _ (k := 20) (e := 192) (n := 64) (by decide) (by decide)) fit
  have cov := hash_covers (L := L)
    (rs := Whole.finalizeRd L.E ++ Whole.finalizeWr L.scr (L.E + 192)) (by
    simp only [Whole.finalizeRd, Whole.finalizeWr, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact .inl (argsWithin L (by decide))
    · exact scratch_covered (shaWithin L)
    · exact .inl (digestWithin hL)
    · exact scratch_covered (workWithin hL))
  have ws := hash_writes (L := L) (rs := Whole.finalizeWr L.scr (L.E + 192)) (by
    simp only [Whole.finalizeWr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact .inr (shaWithin L)
    · exact .inl (digestWithin hL)
    · exact .inr (workWithin hL))
  have ca {j : Nat} (hj : j < 64) := Whole.call_arg hu.esp H.below H.frameFit hj
  have cnt : Proof.Sha512.countX86 u.callEntry = BitVec.ofNat 64 msg.length := by
    unfold Proof.Sha512.countX86
    rw [ca (j := 2) (by decide), ca (j := 1) (by decide), ac, hcount]
  have hbsha : (Whole.SHA L.scr).Disjoint (below (u.gpr .esp) 4) := by
    rw [hu.esp]; exact (H.below_sha (by decide)).symm
  refine WP.mono (Whole.finalize_call hu H.below hp cov ws (ca (by decide) |>.trans a0)
    (ca (by decide) |>.trans a3) cnt hbsha (setup_repr hL hf hr) hlen)
    fun t ⟨ht, hft, hdigest⟩ => ⟨ht, ?_, ?_⟩
  · refine (setup_frame hf).trans (hash_frame hft ?_)
    simp only [Whole.finalizeWr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact .inl (shaWithin L)
    · exact .inr ⟨0, by rw [digest_addr hL]; simp, by change 0 + 64 ≤ 64; decide⟩
    · exact .inl (workWithin hL)
  · rw [digest_addr hL] at hdigest
    exact hdigest

end VG.Proof.Ed25519.X86.SignCached
