import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stitched.Parts

/-!
# ChaCha20-Poly1305 on AArch64, stitched: the chunks in the context

`Stitch.bulk` runs on the regions of the stream (the ChaCha20 state, the data
and the working space, as `vg_chacha20_xor`'s contract gives them), which the
context and the data contain (`WP.narrow`).
-/

namespace VG.Proof.ChaCha20Poly1305.AArch64

open VG VG.AArch64 VG.Impl.ChaCha20Poly1305.AArch64
open VG.Proof.ChaCha20Poly1305.AArch64.Stitch (Bulked BPre Acc bulk_ok)
open VG.Spec.Poly1305 (Repr bytesAt)

variable {sve : Bool}

@[simp] theorem withRegions_v (s : State) (rd wr : List Region) : (s.withRegions rd wr).v = s.v := rfl

/-- The stream's regions in the context. -/
abbrev streamR (s₀ : State) : List Region := [sub s₀ 64 64, dR s₀, sub s₀ 128 320]

theorem bulk_bpre {s₀ : State} (hp : APre s₀) {s : State} (hx0 : s.gpr .x0 = off (cx s₀) 64)
    (hx1 : s.gpr .x1 = dp s₀) (hx2 : s.gpr .x2 = s₀.gpr .x4) (hx3 : s.gpr .x3 = off (cx s₀) 128) :
    BPre (s.withRegions [] (streamR s₀)) := by
  have hst : (sub s₀ 64 64).Disjoint (dR s₀) := hp.c_d.sub_left (sub_ctx s₀ (by lit_omega))
  have hsb : (sub s₀ 64 64).Disjoint (sub s₀ 128 320) :=
    sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
  have hdb : (dR s₀).Disjoint (sub s₀ 128 320) := hp.c_d.symm.sub_right (sub_ctx s₀ (by lit_omega))
  refine ⟨⟨rfl, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;>
    simp only [VG.Proof.ChaCha20.AArch64.Xor.stR, VG.Proof.ChaCha20.AArch64.Xor.dR,
      VG.Proof.ChaCha20.AArch64.Xor.bR, VG.Proof.ChaCha20.AArch64.Xor.st,
      VG.Proof.ChaCha20.AArch64.Xor.dp, VG.Proof.ChaCha20.AArch64.Xor.L,
      VG.Proof.ChaCha20.AArch64.Xor.bp, State.withRegions_gpr, State.withRegions_wr, hx0, hx1, hx2,
      hx3] <;>
    first | rfl | exact hst | exact hsb | exact hdb | exact hp.wrap_d |
      simp only [off, BitVec.add_assoc, ← BitVec.ofNat_add]

/-- The chunks, on the context's regions. -/
theorem bulkA_ok (enc : Bool) {s₀ : State} (hp : APre s₀) {s : State}
    (hx0 : s.gpr .x0 = off (cx s₀) 64) (hx1 : s.gpr .x1 = dp s₀) (hx2 : s.gpr .x2 = s₀.gpr .x4)
    (hx3 : s.gpr .x3 = off (cx s₀) 128) (hL : 512 ≤ L s₀) (hwr : s.wr = s₀.wr)
    {R a : Nat} (ha : Acc R a s) :
    WP isa (Stitch.bulk sve enc) s fun u => (∃ T, Bulked enc R a (s.withRegions [] (streamR s₀)) T
      (u.withRegions [] (streamR s₀))) ∧ u.rd = s.rd ∧ u.wr = s.wr ∧ u.sp = s.sp ∧
      Frame (streamR s₀) s.mem u.mem := by
  have hb := bulk_bpre hp hx0 hx1 hx2 hx3
  have hL' : 512 ≤ VG.Proof.ChaCha20.AArch64.Xor.L (s.withRegions [] (streamR s₀)) := by
    simp only [VG.Proof.ChaCha20.AArch64.Xor.L, State.withRegions_gpr, hx2]; exact hL
  have ha' : Acc R a (s.withRegions [] (streamR s₀)) := ⟨ha.h, ha.h2, ha.key, ha.k0, ha.k1⟩
  have hw : Covers (streamR s₀) s.wr := by
    rw [hwr, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨ctxR s₀, by simp, 64, rfl, by show 64 + 64 ≤ 1024; omega⟩
    · exact ⟨dR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨ctxR s₀, by simp, 128, rfl, by show 128 + 320 ≤ 1024; omega⟩
  refine WP.narrow (bulk_ok enc hb hL' ha') (Covers.right hw) hw ?_ (by cases sve <;> cases enc <;> decide +kernel)
  intro u hrd' hwr' hsp hf hu
  exact ⟨hu, hrd', hwr', hsp, hf⟩

end VG.Proof.ChaCha20Poly1305.AArch64
