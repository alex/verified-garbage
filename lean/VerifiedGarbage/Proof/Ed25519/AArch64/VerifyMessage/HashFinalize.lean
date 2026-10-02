import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyMessage.Hash

namespace VG.Proof.Ed25519.AArch64.VerifyMessage
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.Whole
open VG.Impl.Ed25519.AArch64.VerifyMessage

variable {L : Lay} {g : Reg → BitVec 64} {v : VReg → BitVec 128} {m₀ : Mem} {s : State}

theorem finalize_writes : ∀ r ∈ Whole.finalizeWr L.scr (L.E+192),
    Whole.Within r (Whole.FR L.E) ∨ ∃ R ∈ L.outputs, Whole.Within r R := by
  intro r hr
  simp only [Whole.finalizeWr, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact .inr ⟨L.SCR, by simp [Lay.outputs], 0, (BitVec.add_zero _).symm, by change 0+192≤8192; decide⟩
  · exact .inl ⟨192, rfl, by change 192+64≤256; decide⟩
  · exact .inr ⟨L.SCR, by simp [Lay.outputs], 192, rfl, by change 192+224≤8192; decide⟩

theorem finalize_ok (backend : Whole.Backend) (hc : Ctx L g v m₀ s) (hL : L.Ok)
    (ha : Arguments L m₀) {msg : List Byte}
    (hm : msg.length = 64 + L.len.toNat)
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 s.mem L.scr msg) :
    WP isa (finalize backend.code backend.suffix) s fun t => Ctx L g v m₀ t ∧
      Spec.Ed25519.bytesAt t.mem (L.E+192) 64 = Spec.Sha512.finalHash Spec.Sha512.H0_512 msg := by
  unfold finalize VG.Impl.Ed25519.AArch64.Whole.callWith finalizeArgs
  apply WP.seq
  refine WP.mono (args_ok hc hL ha
    (args := [(.x0,.caller 4 0),(.x1,.caller 2 64),(.x2,.frame 192),(.x3,.caller 4 192)])
    (by decide) (by simp [Whole.valid]) (by simp [known]) (by decide)) ?_
  intro t ⟨ht, htmem, hav⟩
  have a0 : t.gpr .x0 = L.scr := by
    have hh := hav (.x0,.caller 4 0) (by simp)
    change t.gpr .x0 = L.scr + 0 at hh
    exact hh.trans (BitVec.add_zero _)
  have a1 : t.gpr .x1 = BitVec.ofNat 64 msg.length := by
    have hh := hav (.x1,.caller 2 64) (by simp)
    change t.gpr .x1 = L.len + 64 at hh
    rw [hh, hm, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.add_comm]
    rfl
  have a2 : t.gpr .x2 = L.E+192 := hav (.x2,.frame 192) (by simp)
  have a3 : t.gpr .x3 = L.scr+192 := hav (.x3,.caller 4 192) (by simp)
  have hd : Region.Disjoint ⟨L.E+192,64⟩ L.SCR :=
    hL.kc.sub_left (Offset.sub_base _ (by decide))
  have hr' : Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem L.scr msg := htmem ▸ hr
  refine WP.mono (Whole.finalize_call backend ht (Whole.finalize_pre a0 a2 a3 hd (by rw [ht.sp]; exact hL.e16)
    (by rw [ht.sp]; exact hL.cc) (by rw [ht.sp]; exact Whole.ck_frame (by decide : 192 + 64 ≤ 304)))
    (Whole.covers_writes finalize_writes) finalize_writes a0 a2 a1 hr'
    (by rw [hm]; exact hL.message_bound)) fun u ⟨hu,_,hp⟩ => ⟨hu,hp⟩

end VG.Proof.Ed25519.AArch64.VerifyMessage
