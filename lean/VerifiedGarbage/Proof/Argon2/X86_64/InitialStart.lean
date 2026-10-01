import VerifiedGarbage.Proof.Argon2.X86_64.InitialAbsorb
import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Absorb

/-! # H₀: initialize BLAKE2b and absorb the public parameter header -/

namespace VG.Proof.Argon2.X86_64.Initial

open VG VG.X86_64 VG.Impl.Argon2.X86_64.Initial
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
    WP isa (.block [.mov32 .rsi (.imm 64)]) s fun t =>
      t.gpr .rsi = 64 ∧ t.mem = s.mem ∧ HPrime.Keeps s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, State.setReg32,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, fun r hr => ?_, rfl, rfl, Frame.refl _ _⟩
  have hn : r ≠ .rsi := by
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  simp only [RegUpd.gpr_setReg, hn, ite_false]

theorem initialCount_ok (s : State) :
    WP isa (.block [.mov32 .r12 (.imm 24)]) s fun t =>
      t.gpr .r12 = 24 ∧ t.mem = s.mem ∧ Keeps s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, State.setReg32,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, fun r _ h12 _ => ?_, rfl, rfl, Frame.refl _ _⟩
  simp only [RegUpd.gpr_setReg, h12, ite_false]

theorem start_ok (v : Proof.Blake2.X86_64.Backend) (s : State) (h : Space s) :
    WP isa (start (HPrime.hash v)) s fun t =>
      Repr b (Spec.Blake2.init b 64 0) t.mem (t.gpr .rbx) (headerBytes s) ∧
      t.gpr .r12 = 24 ∧ Keeps s t := by
  unfold start headerCode
  refine WP.seq ((digestLength_ok s).mono ?_)
  rintro a ⟨lenA, memA, ka'⟩
  have ka := Keeps.of_hash ka'
  have hA := h.keeps ka
  have retA : (below (a.gpr .rsp) 8).Disjoint ⟨a.gpr .rbx, 192⟩ := (hA.stackWork.sub_left (below_sub (by decide) (by decide))).sub_right
    (Region.sub_prefix (by decide : 192 ≤ 16384))
  refine WP.seq ((HPrime.init_ok v a (by rw [lenA]; exact ⟨by decide, by decide⟩)
    hA.work retA).mono ?_)
  rintro u ⟨reprU, regsU, rdU, wrU, frameU⟩
  have ku : Keeps a u := Keeps.of_hash ⟨regsU, rdU, wrU, HPrime.init_frame _ _ frameU⟩
  have ksu := ka.trans ku
  have hU := h.keeps ksu
  refine WP.seq ((headerWords_ok u 6 (by decide) hU).mono ?_)
  rintro w ⟨memW, kw⟩
  have ksw := ksu.trans kw
  have hW := h.keeps ksw
  have reprW : Repr b (Spec.Blake2.init b 64 0) w.mem (w.gpr .rbx) [] := by
    rw [kw.rbx]
    apply Proof.Blake2.X86_64.Stream.Update.repr_congr Proof.Blake2.X86_64.Stream.okB
      (mem := u.mem) _ (by simpa only [lenA, ku.rbx, show (64 : BitVec 64).toNat = 64 from rfl] using reprU)
    intro i hi
    rw [memW]
    apply (headerMem_frame u 6 (by decide)).bytes (R := ⟨u.gpr .rbx, 192⟩) _
      (show (192 : Nat) ≤ 2 ^ 64 from by decide) hi
    intro r hr
    simp only [List.mem_singleton] at hr; subst r
    exact Offset.base_disjoint _ (by decide) (by decide)
  have headW : bytesAt w.mem (w.gpr .rbx + 768) 24 = headerBytes s := by
    rw [kw.rbx, memW, headerMem_bytes]
    exact headerBytes_keeps h ksu
  refine WP.seq ((HPrime.absorbFixed_ok v w _ 768 24 (by decide) (by decide)
    reprW hW.work hW.stackWork).mono ?_)
  rintro x ⟨reprX, kx'⟩
  have kx := Keeps.of_hash kx'
  have ksx := ksw.trans kx
  refine (initialCount_ok x).mono ?_
  rintro t ⟨countT, memT, kt⟩
  refine ⟨?_, countT, ksx.trans kt⟩
  rw [kt.rbx, memT, kx.rbx]
  simpa only [headW, show BitVec.ofNat 64 768 = (768 : Addr) from rfl] using reprX

end VG.Proof.Argon2.X86_64.Initial
