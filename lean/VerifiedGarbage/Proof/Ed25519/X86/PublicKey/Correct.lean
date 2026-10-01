import VerifiedGarbage.Proof.Ed25519.X86.PublicKey.Base
import VerifiedGarbage.Proof.Ed25519.X86.PublicKey.Hash
import VerifiedGarbage.Proof.Ed25519.X86.Whole.Wipe

namespace VG.Proof.Ed25519.X86.PublicKey
open VG VG.X86 VG.Impl.Ed25519.X86.PublicKey

theorem prune_step {s t : State} (h : Facts s) (hc : Ctx s t) {digest : List Byte}
    (hh : Spec.Sha512.bytesAt t.mem ((esp s).setWidth 64 + 192) 64 = digest) :
    WP isa (.block prune) t fun u => Ctx s u ∧
      Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt u.mem ((scalarPtr s).setWidth 64) 32) =
        Spec.Ed25519.prune digest := by
  refine WP.mono (prune_ok hc.esp (by have := h.toBounds.frame; omega)
    (by rw [hc.wr]; exact List.mem_cons_self) hh) fun u ⟨ku, hf, hs⟩ => ⟨?_, ?_⟩
  · refine hc.of_frame ku.rd ku.wr ku.esp ?_ hf ?_
    · intro r hr _
      apply ku.regs
      rintro rfl
      simp [calleeSaved] at hr
    · rintro r hr
      rw [List.mem_singleton.mp hr]
      exact .inl (Offset.sub_base _ (by decide))
  · rw [scalarPtr_addr h.toBounds]
    exact hs

theorem base_step {s t : State} (h : Facts s) (hc : Ctx s t) {n : Nat}
    (hn : Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt t.mem ((scalarPtr s).setWidth 64) 32) = n) :
    WP isa (callWith baseArgs "vg_ed25519_scalar_base" Impl.Ed25519.X86.scalarBase) t
      fun u => Ctx s u ∧ Spec.Ed25519.bytesAt u.mem ((arg s 0).setWidth 64) 32 =
        Spec.Ed25519.encodePoint (Spec.Ed25519.pointMul n Spec.Ed25519.basePoint) := by
  refine WP.seq (WP.mono (setup_ok h hc (vs := [.caller 0 0, .frame 32, .caller 2 0])
    (by decide) (by simp [Whole.valid])) fun u ⟨hu, hf, hs⟩ => ?_)
  have a0 := hs 0 (by decide)
  have a1 := hs 1 (by decide)
  have a2 := hs 2 (by decide)
  simp only [argValue, List.getElem_cons_zero, List.getElem_cons_succ, BitVec.add_zero] at a0 a1 a2
  have he : Spec.Ed25519.bytesAt u.mem ((scalarPtr s).setWidth 64) 32 =
      Spec.Ed25519.bytesAt t.mem ((scalarPtr s).setWidth 64) 32 := by
    apply List.map_congr_left
    intro i hi
    exact hf.bytes (R := ⟨(scalarPtr s).setWidth 64, 32⟩) (by
      rintro r hr; rw [List.mem_singleton.mp hr, scalarPtr_addr h.toBounds]
      exact Offset.disjoint_base _ (by decide) (by decide)) (by change 32 ≤ 2 ^ 64; decide) (List.mem_range.mp hi)
  refine WP.mono (base_call h hu ⟨a0, a1, a2⟩) fun v ⟨hv, ho⟩ => ⟨hv, ?_⟩
  rw [ho, he, Spec.Ed25519.scalarBase, hn]

theorem body_ok {s t : State} (h : Facts s) (hc : Ctx s t) :
    WP isa body t fun u => Ctx s u ∧ Spec.Ed25519.bytesAt u.mem ((arg s 0).setWidth 64) 32 =
      Spec.Ed25519.publicKey (Spec.Ed25519.bytesAt s.mem ((arg s 1).setWidth 64) 32) := by
  refine WP.seq (WP.mono (hash_ok h hc) fun t₁ ⟨hc₁, hh⟩ => ?_)
  refine WP.seq (WP.mono (prune_step h hc₁ hh) fun t₂ ⟨hc₂, hn⟩ => ?_)
  refine WP.seq (WP.mono (base_step h hc₂ hn) fun t₃ ⟨hc₃, ho⟩ => ?_)
  refine WP.mono (Whole.Ctx.zeroWords hc₃ (start := 8) (count := 56)
    (by have := h.toBounds.frame; omega) (by decide)) fun u ⟨hu, hf, _⟩ => ⟨hu, ?_⟩
  have he : Spec.Ed25519.bytesAt u.mem ((arg s 0).setWidth 64) 32 =
      Spec.Ed25519.bytesAt t₃.mem ((arg s 0).setWidth 64) 32 := by
    apply List.map_congr_left
    intro i hi
    exact hf.bytes (R := OUT s) (by
      rintro r hr; rw [List.mem_singleton.mp hr]
      exact (h.ko.sub_left (fun p hp => Whole.frame_sub (esp s) p
        (Offset.sub_base _ (by decide : 4 * 8 + 4 * 56 ≤ 256) p hp))).symm)
      (by change 32 ≤ 2 ^ 64; decide) (List.mem_range.mp hi)
  rw [he, ho]
  rfl

private theorem noSp_seq {a b : Prog isa} (ha : NoSp a) (hb : NoSp b) : NoSp (.seq a b) := by
  intro i hi
  rcases List.mem_append.mp hi with hi | hi
  · exact ha i hi
  · exact hb i hi

theorem body_nosp : NoSp body := by
  have ni : NoSp (.block initArgs) := NoSp.of_all (by decide +kernel)
  have nu : NoSp (.block updateArgs) := NoSp.of_all (by decide +kernel)
  have nf : NoSp (.block finalizeArgs) := NoSp.of_all (by decide +kernel)
  have nb : NoSp (.block baseArgs) := NoSp.of_all (by decide +kernel)
  have np : NoSp (.block prune) := NoSp.of_all (by decide +kernel)
  have nw : NoSp (.block wipe) := NoSp.of_all (by decide +kernel)
  exact noSp_seq
    (noSp_seq (noSp_seq ni Whole.init_nosp)
      (noSp_seq (noSp_seq nu Whole.update_nosp) (noSp_seq nf Whole.finalize_nosp)))
    (noSp_seq np (noSp_seq (noSp_seq nb base_nosp) nw))

theorem publicKey_ok {s : State} (h : pkLocal.pre s) :
    WP isa publicKey s fun t => abiPreserved s t ∧ pkLocal.post s t := by
  have hf := facts h
  refine WP.frame (rs := List.replicate 64 .eax) (by simp) (by simp) (by decide)
    (by simp only [List.length_replicate]; have := hf.below; omega) body_nosp
    (WP.mono (body_ok hf (push_ctx h)) fun u ⟨hu, ho⟩ => ?_)
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · by_cases he : r = .esp
    · subst r
      rw [popped_esp, hu.esp, List.length_replicate]
      exact BitVec.sub_add_cancel _ _
    · rw [popped_gpr _ _ _ he (by intro e; subst r; simp [calleeSaved] at hr), hu.cs r hr he]
  · rw [popped_mem]
    refine hu.frame.readW (r := RET s) (Region.contains_self _ _) ?_ (by decide)
    simp only [pkWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact hf.ro
    · exact hf.rc
    · rw [stack_eq hf.toBounds]
      change Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩
        ⟨(s.gpr .esp - BitVec.ofNat 32 280).setWidth 64, 280⟩
      rw [Taint.sub_setWidth hf.below]
      exact (Offset.below_disjoint _ (by decide)).symm
  · change Spec.Ed25519.bytesAt (popped .eax (List.replicate 64 .eax).length u).mem
      ((arg s 0).setWidth 64) 32 = _
    rw [popped_mem]
    exact ho

end VG.Proof.Ed25519.X86.PublicKey
