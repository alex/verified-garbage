import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyMessage.HashInputs
import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyMessage.HashFinalize

namespace VG.Proof.Ed25519.AArch64.VerifyMessage
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.VerifyMessage

variable {L : Lay} {g : Reg → BitVec 64} {v : VReg → BitVec 128} {m₀ : Mem} {s : State}

def hashInput (L : Lay) (m : Mem) : List Byte :=
  Spec.Ed25519.bytesAt m L.sig 32 ++
    Spec.Ed25519.bytesAt m L.pk 32 ++
    Spec.Ed25519.bytesAt m L.msg L.len.toNat

theorem bytes_length (m : Mem) (p : BitVec 64) (n : Nat) :
    (Spec.Ed25519.bytesAt m p n).length = n := by simp [Spec.Ed25519.bytesAt]

theorem sig_prefix_same (hc : Ctx L g v m₀ s) (hL : L.Ok) :
    Spec.Ed25519.bytesAt s.mem L.sig 32 = Spec.Ed25519.bytesAt m₀ L.sig 32 := by
  unfold Spec.Ed25519.bytesAt
  refine List.map_congr_left fun i hi => ?_
  exact hc.frame.bytes (R := L.SIG) (by
    intro r hr
    simp only [Lay.outputs, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hL.sc _ (by simp [Lay.inputs])
    · exact (hL.ks _ (by simp [Lay.inputs])).symm)
    (by change 64 ≤ 2 ^ 64; decide) (by change i < 64; have := List.mem_range.mp hi; omega)

theorem input_sig (hL : L.Ok) : Region.Disjoint ⟨L.value 3,32⟩ L.SCR ∧
    ∃ R ∈ L.inputs, Whole.Within ⟨L.value 3,32⟩ R := by
  refine ⟨(hL.sc L.SIG (by simp [Lay.inputs])).sub_left (Region.sub_prefix (by decide)),
    L.SIG, by simp [Lay.inputs], 0, (BitVec.add_zero _).symm, ?_⟩
  change 0+32≤64
  decide

theorem input_pk (hL : L.Ok) : Region.Disjoint ⟨L.value 0,32⟩ L.SCR ∧
    ∃ R ∈ L.inputs, Whole.Within ⟨L.value 0,32⟩ R := by
  refine ⟨hL.sc L.PK (by simp [Lay.inputs]), L.PK, by simp [Lay.inputs], 0,
    (BitVec.add_zero _).symm, ?_⟩
  change 0+32≤32
  decide

theorem hash_ok (backend : Whole.Backend) (hc : Ctx L g v m₀ s)
    (hL : L.Ok) (ha : Arguments L m₀) :
    WP isa (hash backend.code backend.suffix) s fun t => Ctx L g v m₀ t ∧
      Spec.Ed25519.bytesAt t.mem (L.E + 192) 64 = Spec.Sha512.sha512 (hashInput L m₀) := by
  refine WP.seq (WP.mono (init_ok hc hL ha) fun t ⟨ht,hinit⟩ => ?_)
  refine WP.seq (WP.mono (prefix_step backend ht hL ha (source := 3) (count := 0)
    (by decide) (by decide) rfl (input_sig hL).1 (input_sig hL).2 hinit)
    fun u ⟨hu,hsig⟩ => ?_)
  change Spec.Sha512.Repr _ u.mem _ ([] ++ Spec.Ed25519.bytesAt t.mem L.sig 32) at hsig
  rw [List.nil_append, sig_prefix_same ht hL] at hsig
  refine WP.seq (WP.mono (prefix_step backend hu hL ha (source := 0) (count := 32)
    (by decide) (by decide) (bytes_length _ _ _) (input_pk hL).1 (input_pk hL).2 hsig)
    fun w ⟨hw,hpk⟩ => ?_)
  change Spec.Sha512.Repr _ w.mem _ (_ ++ Spec.Ed25519.bytesAt u.mem L.pk 32) at hpk
  rw [hu.input_bytes hL (r := L.PK) (by simp [Lay.inputs]) (by change 32≤2^64; decide)] at hpk
  have hpkl : (Spec.Ed25519.bytesAt m₀ L.sig 32 ++ Spec.Ed25519.bytesAt m₀ L.pk 32).length = 64 := by
    rw [List.length_append, bytes_length, bytes_length]
  refine WP.seq (WP.mono (message_step backend hw hL ha hpkl hpk) fun z ⟨hz,hmsg⟩ => ?_)
  rw [hw.input_bytes hL (r := L.MSG) (by simp [Lay.inputs])
    (by have := L.len.isLt; change L.len.toNat≤2^64; omega)] at hmsg
  have hlen : (hashInput L m₀).length = 64 + L.len.toNat := by
    simp only [hashInput, List.length_append, bytes_length]
  exact finalize_ok backend hz hL ha hlen hmsg

end VG.Proof.Ed25519.AArch64.VerifyMessage
