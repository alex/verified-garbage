import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Regs
import VerifiedGarbage.Proof.Hmac.Common

/-!
# Deterministic ECDSA on x86-64: copying 32 bytes

`copy4 src so dst d` copies the 32 bytes at `src + so` to `dst + d`, a word
at a time through `rax`, when the two ranges are apart (`copy4_ok`): each
word written is the word read (`copyW_ok`), so the bytes written are the
bytes read (`copyN_ok`, by induction on the words).
-/

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.Rfc6979.X86_64

/-- One word copied through `rax`. -/
theorem copyW_ok {u : State} {src dst : Reg} {S D : Addr} (hs : u.gpr src = S) (hd : u.gpr dst = D)
    {so d : Nat} (hr : InRegions (u.rd ++ u.wr) (S + BitVec.ofNat 64 so) 8)
    (hw : InRegions u.wr (D + BitVec.ofNat 64 d) 8) (hdr : dst ≠ .rax) :
    WP isa (.block [.mov .rax (.mem (at_ src so)), .store (at_ dst d) .rax]) u fun u' =>
      u'.rd = u.rd ∧ u'.wr = u.wr ∧ (∀ r, r ≠ .rax → u'.gpr r = u.gpr r) ∧
      u'.mem = u.mem.writeW (D + BitVec.ofNat 64 d) (u.mem.readW (S + BitVec.ofNat 64 so) 64) := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64, State.store64, ea_at, hs,
    RegUpd.gpr_setReg_of_ne _ _ hdr, hd, hr, ite_true, Option.map_some, RegUpd.rd_setReg, RegUpd.wr_setReg,
    RegUpd.mem_setReg, RegUpd.gpr_setReg_self, hw, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, fun r hr => RegUpd.gpr_setReg_of_ne _ _ hr, trivial⟩

theorem bytesAt_copied (m : Mem) (D S : Addr) :
    Spec.Sha256.bytesAt (m.writeW D (m.readW S 64)) D 8 = Spec.Sha256.bytesAt m S 8 := by
  rw [show (64 : Nat) = 8 * 8 from rfl, Proof.Hmac.Common.writeW_readW]
  have := Proof.Hmac.Common.bytesAt_writeBytes_self m D (Spec.Sha256.bytesAt m S 8) (by simp [Spec.Sha256.bytesAt])
  rwa [Proof.Hmac.Common.bytesAt_length] at this

theorem copyN_ok {src dst : Reg} {S D : Addr} {so d : Nat} (hdr : dst ≠ .rax) (hsr : src ≠ .rax)
    (hsep : Region.Disjoint ⟨S + BitVec.ofNat 64 so, 32⟩ ⟨D + BitVec.ofNat 64 d, 32⟩)
    (hdn : d + 32 < 2 ^ 64) :
    ∀ k ≤ 4, ∀ u : State, u.gpr src = S → u.gpr dst = D →
      (∀ j < 4, InRegions (u.rd ++ u.wr) (S + BitVec.ofNat 64 (so + 8 * j)) 8) →
      (∀ j < 4, InRegions u.wr (D + BitVec.ofNat 64 (d + 8 * j)) 8) →
      WP isa (.block ((List.range k).flatMap fun j =>
        [.mov .rax (.mem (at_ src (so + 8 * j))), .store (at_ dst (d + 8 * j)) .rax])) u fun u' =>
        u'.rd = u.rd ∧ u'.wr = u.wr ∧ (∀ r, r ≠ .rax → u'.gpr r = u.gpr r) ∧
        Frame [⟨D + BitVec.ofNat 64 d, 32⟩] u.mem u'.mem ∧
        Spec.Sha256.bytesAt u'.mem (D + BitVec.ofNat 64 d) (8 * k) =
          Spec.Sha256.bytesAt u.mem (S + BitVec.ofNat 64 so) (8 * k)
  | 0, _, u, _, _, _, _ => WP.of_runBlock ⟨u, rfl, rfl, rfl, fun _ _ => rfl, Frame.refl _ _, rfl⟩
  | k + 1, hk, u, hs, hd, hr, hw => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (copyN_ok hdr hsr hsep hdn k (by omega) u hs hd hr hw)
      fun u₁ ⟨hrd₁, hwr₁, hg₁, hf₁, hb₁⟩ => ?_
    refine WP.mono (copyW_ok (u := u₁) (hg₁ _ hsr ▸ hs) (hg₁ _ hdr ▸ hd) (hrd₁ ▸ hwr₁ ▸ hr k (by omega))
      (hwr₁ ▸ hw k (by omega)) hdr) fun u₂ ⟨hrd₂, hwr₂, hg₂, hm₂⟩ => ?_
    -- The word written, within the destination.
    have hsub : Region.Sub ⟨D + BitVec.ofNat 64 (d + 8 * k), 8⟩ ⟨D + BitVec.ofNat 64 d, 32⟩ :=
      Offset.sub _ (by omega) (by omega)
    have hf₂ : Frame [⟨D + BitVec.ofNat 64 (d + 8 * k), 8⟩] u₁.mem u₂.mem := by
      rw [hm₂]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
        (Offset.contains _ (Nat.le_refl _) (by omega) (by omega))
    -- The word read, unchanged by the earlier words.
    have hsrc : Spec.Sha256.bytesAt u₁.mem (S + BitVec.ofNat 64 (so + 8 * k)) 8 =
        Spec.Sha256.bytesAt u.mem (S + BitVec.ofNat 64 (so + 8 * k)) 8 :=
      bytesAt_frame hf₁ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hsep.sub_left (Offset.sub _ (by omega) (by omega))) (by omega)
    refine ⟨hrd₂.trans hrd₁, hwr₂.trans hwr₁, fun r hr => (hg₂ r hr).trans (hg₁ r hr),
      hf₁.trans (hf₂.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        simp only [List.mem_singleton] at hr; subst hr; exact hsub⟩), ?_⟩
    rw [show 8 * (k + 1) = 8 * k + 8 by omega, Proof.Hmac.Common.bytesAt_add, Proof.Hmac.Common.bytesAt_add,
      Offset.add_add, Offset.add_add, ← hsrc]
    congr 1
    · rw [← hb₁]
      exact bytesAt_frame hf₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by omega)
    · rw [hm₂]; exact bytesAt_copied _ _ _

end VG.Proof.Ecdsa.Rfc6979.X86_64
