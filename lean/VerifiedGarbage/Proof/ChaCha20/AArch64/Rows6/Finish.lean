import VerifiedGarbage.Proof.ChaCha20.AArch64.Rows6.Store
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Finish

namespace VG.Proof.ChaCha20.AArch64.Rows6
open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Rows6
open VG.Proof.ChaCha20.AArch64.Neon4 (output output_word byte_vword)

theorem output_byte (vs : Nat → CState) (k : Nat) :
    (output vs (k / 16)).extractLsb' (8 * (k % 16)) 8 =
      (VG.Spec.ChaCha20.serialize (vs (k / 64))).getD (k % 64) 0 := by
  rw [byte_vword _ (by omega),output_word _ _ (by omega),
    VG.Proof.ChaCha20.serialize_getD _ (by omega)]
  simp only [show k / 16 / 4 = k / 64 by omega,
    show 4 * (k / 16 % 4) + k % 16 / 4 = k % 64 / 4 by omega,
    show k % 16 % 4 = k % 64 % 4 by omega]

theorem Data.frame {m₀ m : Mem} {p : Addr} {out : Nat → BitVec 128} {done : List Nat}
    (h : Data m₀ m p out done) : Frame [⟨p,384⟩] m₀ m := by
  intro x hx
  have hn : ¬ (x - p).toNat < 384 := by
    have hh := hx ⟨p,384⟩ (List.mem_cons_self ..)
    simp only [Region.Contains] at hh
    omega
  rw [h x,ite_eq_right (fun h => hn h.2)]

theorem finishBlocks_ok {s : State} {blocks : Nat → CState} (h : Holds (pack blocks) s)
    (hout : ∀ k : Fin 24, InRegions s.wr (s.gpr .x1 + BitVec.ofNat 64 (16 * k.val)) 16) :
    WP isa (.block ((List.finRange 24).flatMap xorRow)) s fun u =>
      (∀ k < 384, u.mem (s.gpr .x1 + BitVec.ofNat 64 k) =
        s.mem (s.gpr .x1 + BitVec.ofNat 64 k) ^^^
        (VG.Spec.ChaCha20.serialize (blocks (k / 64))).getD (k % 64) 0) ∧
      Frame [⟨s.gpr .x1,384⟩] s.mem u.mem ∧ StoreSame s u := by
  have hv : ∀ k : Fin 24, s.v (vreg k) = output blocks k.val := by
    intro k
    apply vec_ext
    intro j hj
    rw [h k j hj,pack_get,output_word _ _ hj]
    simp only [Nat.mod_eq_of_lt hj]
  refine (xorList_ok (List.finRange 24) (List.nodup_finRange 24)
    (Data.nil s.mem (s.gpr .x1) (output blocks)) rfl hv
    (fun _ _ => List.not_mem_nil) (fun k _ => hout k)).mono fun u ⟨hu,hs⟩ => ⟨?_,hu.frame,hs⟩
  intro k hk
  have hm : k / 16 ∈ (List.finRange 24).map Fin.val ++ [] := by
    apply List.mem_append_left
    exact List.mem_map_of_mem (f := Fin.val) (List.mem_finRange (⟨k / 16,by omega⟩ : Fin 24))
  rw [hu _,Mem.sub_ofNat_toNat _ (by omega : k < 2 ^ 64),ite_eq_left ⟨hm,hk⟩,output_byte]
end VG.Proof.ChaCha20.AArch64.Rows6
