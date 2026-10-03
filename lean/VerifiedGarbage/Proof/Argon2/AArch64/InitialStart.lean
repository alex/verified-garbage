import VerifiedGarbage.Proof.Argon2.AArch64.SegmentSetupSteps
import VerifiedGarbage.Proof.Argon2.AArch64.InitialAbsorb
import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Absorb

/-! # H₀: initialize BLAKE2b and absorb the public parameter header -/

namespace VG.Proof.Argon2.AArch64.Initial

open VG VG.AArch64 VG.Impl.Argon2.AArch64.Initial
open VG.Spec.Blake2 (bytesAt b Repr)

def headerBytes (s : State) : List Byte :=
  (List.range 6).flatMap fun j => Spec.Blake2.wordBytes (headerValue s j)

theorem headerBytes_keeps {s t : State} (h : Space s) (k : Keeps s t) :
    headerBytes t = headerBytes s := by
  unfold headerBytes
  simp only [List.flatMap]
  apply congrArg List.flatten
  exact List.map_congr_left fun j _ => congrArg Spec.Blake2.wordBytes (headerValue_keeps h k j)

theorem headerBytes_length (s : State) : (headerBytes s).length = 24 := by
  unfold headerBytes
  change (Spec.Blake2.wordBytes (headerValue s 0) ++ Spec.Blake2.wordBytes (headerValue s 1) ++
    Spec.Blake2.wordBytes (headerValue s 2) ++ Spec.Blake2.wordBytes (headerValue s 3) ++
    Spec.Blake2.wordBytes (headerValue s 4) ++ Spec.Blake2.wordBytes (headerValue s 5)).length = 24
  simp only [Spec.Blake2.wordBytes, List.length_append, List.length_map, List.length_range]

theorem digestLength_ok (s : State) :
    WP isa (.block [Impl.Argon2.AArch64.Instructions.imm .x1 64].flatten) s fun t =>
      t.gpr .x1 = 64 ∧ t.mem = s.mem ∧ HPrime.Keeps s t := by
  refine (SegmentSetup.register_ok s .x1 64 (by decide)).mono ?_
  rintro t ⟨value, keeps⟩
  refine ⟨value, keeps.mem, fun r hr h30 => keeps.regs r ?_, keeps.rd, keeps.wr, keeps.sp, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · rw [keeps.mem]; exact Frame.refl _ _

theorem initialCount_ok (s : State) :
    WP isa (.block [Impl.Argon2.AArch64.Instructions.imm .x20 24].flatten) s fun t =>
      t.gpr .x20 = 24 ∧ t.mem = s.mem ∧ Keeps s t := by
  refine (SegmentSetup.register_ok s .x20 24 (by decide)).mono ?_
  rintro t ⟨value, keeps⟩
  refine ⟨value, keeps.mem, fun r _ h20 _ => keeps.regs r ?_, keeps.sp, keeps.rd, keeps.wr, ?_⟩
  · simpa only [List.mem_singleton] using h20
  · rw [keeps.mem]; exact Frame.refl _ _

theorem start_ok (v : HPrime.Backend) (s : State) (h : Space s) :
    WP isa (start v.hash) s fun t =>
      Repr b (Spec.Blake2.init b 64 0) t.mem (t.gpr .x24) (headerBytes s) ∧
      t.gpr .x20 = 24 ∧ Keeps s t := by
  unfold start headerCode
  refine WP.seq ((digestLength_ok s).mono ?_)
  rintro a ⟨lenA, memA, ka'⟩
  have ka := Keeps.of_hash ka'
  have hA := h.keeps ka
  refine WP.seq ((HPrime.init_ok v a (by rw [lenA]; exact ⟨by decide, by decide⟩)
    hA.work).mono ?_)
  rintro u ⟨reprU, regsU, rdU, wrU, spU, frameU⟩
  have ku : Keeps a u := Keeps.of_hash ⟨regsU, rdU, wrU, spU, HPrime.init_frame _ _ frameU⟩
  have ksu := ka.trans ku
  have hU := h.keeps ksu
  refine WP.seq ((headerWords_ok u 6 (by decide) hU).mono ?_)
  rintro w ⟨memW, kw⟩
  have ksw := ksu.trans kw
  have hW := h.keeps ksw
  have reprW : Repr b (Spec.Blake2.init b 64 0) w.mem (w.gpr .x24) [] := by
    rw [kw.x24]
    apply Proof.Blake2.AArch64.Stream.repr_congr Proof.Blake2.AArch64.Stream.okB
      (mem := u.mem) (h := by simpa only [lenA, ku.x24, show (64 : BitVec 64).toNat = 64 from rfl] using reprU)
    intro i hi
    rw [memW]
    apply (headerMem_frame u 6 (by decide)).bytes (R := ⟨u.gpr .x24, 192⟩) _
      (show (192 : Nat) ≤ 2 ^ 64 from by decide) hi
    intro r hr
    simp only [List.mem_singleton] at hr; subst r
    exact Offset.base_disjoint _ (by decide) (by decide)
  have headW : bytesAt w.mem (w.gpr .x24 + 768) 24 = headerBytes s := by
    rw [kw.x24, memW, headerMem_bytes]
    exact headerBytes_keeps h ksu
  refine WP.seq ((HPrime.absorbFixed_ok v w _ 768 24 (by decide) hW.stackMinimum (by decide) (by decide)
    reprW hW.work hW.stackWork).mono ?_)
  rintro x ⟨reprX, kx'⟩
  have kx := Keeps.of_hash kx'
  have ksx := ksw.trans kx
  refine (initialCount_ok x).mono ?_
  rintro t ⟨countT, memT, kt⟩
  refine ⟨?_, countT, ksx.trans kt⟩
  rw [kt.x24, memT, kx.x24]
  simpa only [headW, show BitVec.ofNat 64 768 = (768 : Addr) from rfl] using reprX

end VG.Proof.Argon2.AArch64.Initial
