import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyMessage.Args
import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.HashPre

namespace VG.Proof.Ed25519.AArch64.VerifyMessage
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.Whole
open VG.Impl.Ed25519.AArch64.VerifyMessage

variable {L : Lay} {g : Reg → BitVec 64} {v : VReg → BitVec 128} {m₀ : Mem} {s : State}

theorem hash_writes : ∀ r ∈ Whole.hashWr L.scr,
    Whole.Within r (Whole.FR L.E) ∨ ∃ R ∈ L.outputs, Whole.Within r R :=
  Whole.hash_writes (by simp [Lay.outputs])

theorem init_ok (hc : Ctx L g v m₀ s) (hL : L.Ok) (ha : Arguments L m₀) :
    WP isa init s fun t => Ctx L g v m₀ t ∧
      Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem L.scr [] := by
  unfold init VG.Impl.Ed25519.AArch64.Whole.callWith initArgs
  apply WP.seq
  refine WP.mono (args_ok hc hL ha (args := [(.x0,.caller 4 0)]) (by decide) (by simp [Whole.valid]) (by simp [known]) (by decide)) ?_
  intro t ⟨ht, _, hv⟩
  have a0 : t.gpr .x0 = L.scr := by
    have hh := hv (.x0,.caller 4 0) (by simp)
    change t.gpr .x0 = L.scr + 0 at hh
    exact hh.trans (BitVec.add_zero _)
  have hw := Whole.init_writes (E := L.E) (by simp [Lay.outputs] : L.SCR ∈ L.outputs)
  refine WP.mono (Whole.init_call ht (Whole.init_pre a0)
    (Whole.covers_writes hw) hw a0) fun u ⟨hu, _, hr⟩ => ⟨hu, hr⟩

/-- Append a known input buffer without depending on its contents. -/
theorem update_ok (backend : Whole.Backend) (hc : Ctx L g v m₀ s) (hL : L.Ok)
    (ha : Arguments L m₀) {args : List (Reg × Value)}
    (hn : (args.map Prod.fst).Nodup) (hv : ∀ p ∈ args, Whole.valid p.2)
    (hk : ∀ p ∈ args, known p.2) (hregs : ∀ p ∈ args, p.1 ∉ preserved)
    {p len : Addr} {prev : List Byte}
    (hargs : ∀ t, OutArgs L args t → t.gpr .x0 = L.scr ∧
      t.gpr .x1 = BitVec.ofNat 64 prev.length ∧ t.gpr .x2 = p ∧
      t.gpr .x3 = len ∧ t.gpr .x4 = L.scr + 192)
    (hd : Region.Disjoint ⟨p,len.toNat⟩ L.SCR)
    (hi : ∃ R ∈ L.inputs, Whole.Within ⟨p,len.toNat⟩ R)
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 s.mem L.scr prev) :
    WP isa (update backend.code backend.suffix (setup args)) s fun t =>
      Ctx L g v m₀ t ∧ Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem L.scr
        (prev ++ Spec.Ed25519.bytesAt s.mem p len.toNat) := by
  unfold update VG.Impl.Ed25519.AArch64.Whole.callWith
  apply WP.seq
  refine WP.mono (args_ok hc hL ha hn hv hk hregs) ?_
  intro t ⟨ht, hm, hav⟩
  obtain ⟨a0,a1,a2,a3,a4⟩ := hargs t hav
  have hcov : Covers (Whole.updateRd p len ++ Whole.hashWr L.scr)
      (L.inputs ++ Whole.FR L.E :: L.outputs) := by
    refine Covers.of_sub fun R hR => ?_
    rcases List.mem_append.mp hR with hR | hR
    · simp only [Whole.updateRd, List.mem_singleton] at hR
      subst R
      obtain ⟨R,hR,hs⟩ := hi
      exact ⟨R,List.mem_append_left _ hR,hs⟩
    · rcases hash_writes R hR with hf | ⟨S,hS,hs⟩
      · exact ⟨Whole.FR L.E,List.mem_append_right _ List.mem_cons_self,hf⟩
      · exact ⟨S,List.mem_append_right _ (List.mem_cons_of_mem _ hS),hs⟩
  have hr' : Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem L.scr prev := hm ▸ hr
  refine WP.mono (Whole.update_call backend ht (Whole.update_pre a0 a2 a3 a4 hd (by rw [ht.sp]; exact hL.e16)
    (by rw [ht.sp]; exact hL.cc) (by rw [ht.sp]; exact hL.ck_within hi))
    hcov hash_writes a0 a2 a3 a1 hr') fun u ⟨hu,_,huv⟩ => ⟨hu,?_⟩
  rw [hm] at huv
  exact huv

end VG.Proof.Ed25519.AArch64.VerifyMessage
