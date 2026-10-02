import VerifiedGarbage.Proof.Argon2.AArch64.InitialPrep

/-! # H₀: absorb a length-prefixed byte-string input -/

namespace VG.Proof.Argon2.AArch64.Initial

open VG VG.AArch64 VG.Impl.Argon2.AArch64.Initial
open VG.Spec.Blake2 (bytesAt b Repr)
open VG.Proof.Argon2 (appendInput)

theorem slots_aligned (d : Nat) (hd : d ∈ slots) : d % 8 = 0 := by
  have all : ∀ d ∈ slots, d % 8 = 0 := by decide
  exact all d hd

structure InputReady (s : State) (po lo : Nat) : Prop where
  space : Space s
  pointerSlot : po ∈ slots
  lengthSlot : lo ∈ slots
  pointerBound : po + 8 ≤ 272
  lengthBound : lo + 8 ≤ 272
  length : (wordAt s lo).toNat < 2 ^ 32
  cover : Covers [inputRegion s po lo] (s.rd ++ s.wr)
  work : (inputRegion s po lo).Disjoint ⟨s.gpr .x24, 16384⟩
  stack : (inputRegion s po lo).Disjoint (below (s.sp) 16)

theorem InputReady.keeps {s t : State} {po lo : Nat} (h : InputReady s po lo)
    (k : Keeps s t) : InputReady t po lo := by
  have reg := h.space.input_keeps k po lo h.pointerBound h.lengthBound
  refine ⟨h.space.keeps k, h.pointerSlot, h.lengthSlot, h.pointerBound, h.lengthBound,
    ?_, ?_, ?_, ?_⟩
  · rw [h.space.word_keeps k lo h.lengthBound]; exact h.length
  · rw [reg, k.rd, k.wr]; exact h.cover
  · rw [reg, k.x24]; exact h.work
  · rw [reg, k.sp]; exact h.stack

def inputBytes (s : State) (po lo : Nat) : List Byte :=
  bytesAt s.mem (wordAt s po) (wordAt s lo).toNat

theorem inputBytes_length (s : State) (po lo : Nat) :
    (inputBytes s po lo).length = (wordAt s lo).toNat := by
  simp only [inputBytes, bytesAt, List.length_map, List.length_range]

theorem InputReady.bytes_keeps {s t : State} {po lo : Nat} (h : InputReady s po lo)
    (k : Keeps s t) : inputBytes t po lo = inputBytes s po lo := by
  unfold inputBytes
  rw [h.space.word_keeps k po h.pointerBound, h.space.word_keeps k lo h.lengthBound]
  exact k.bytes (inputRegion s po lo) h.work h.stack (by
    change (wordAt s lo).toNat ≤ 2 ^ 64
    exact Nat.le_of_lt (wordAt s lo).isLt)

theorem absorb_ok (v : HPrime.Backend) (s : State) (po lo : Nat)
    (h : InputReady s po lo) (d : List Byte)
    (repr : Repr b (Spec.Blake2.init b 64 0) s.mem (s.gpr .x24) d)
    (count : s.gpr .x20 = BitVec.ofNat 64 d.length)
    (bound : d.length + 4 + (wordAt s lo).toNat < 2 ^ 64) :
    WP isa (absorb v.hash po lo) s fun t =>
      Repr b (Spec.Blake2.init b 64 0) t.mem (t.gpr .x24)
        (appendInput d (inputBytes s po lo)) ∧
      t.gpr .x20 = BitVec.ofNat 64 (appendInput d (inputBytes s po lo)).length ∧ Keeps s t := by
  unfold absorb
  refine WP.seq ((lengthArgs_ok s lo (slots_aligned lo h.lengthSlot) (by have := h.lengthBound; omega) (h.space.readable lo h.lengthSlot)
    (by simpa using h.space.write 792 4 (by decide))).mono ?_)
  intro a ha
  have ka := ha.keeps
  have hA := h.keeps ka
  have lenA : (a.gpr .x3).toNat = 4 := by rw [ha.size]; rfl
  have dataA : Covers [⟨a.gpr .x2, (a.gpr .x3).toNat⟩] (a.rd ++ a.wr) := by
    rw [ha.pointer, lenA, ka.x24.symm]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_singleton] at hr; subst r
    exact ⟨⟨a.gpr .x24, 16384⟩, List.mem_append_right _ hA.space.work,
      792, rfl, by change 792 + 4 ≤ 16384; decide⟩
  have dsA : (⟨a.gpr .x2, (a.gpr .x3).toNat⟩ : Region).Disjoint ⟨a.gpr .x24, 192⟩ := by
    rw [ha.pointer, lenA, ka.x24]
    exact (Offset.base_disjoint _ (by decide) (by decide)).symm
  have dwA : (⟨a.gpr .x2, (a.gpr .x3).toNat⟩ : Region).Disjoint ⟨a.gpr .x24 + 192, 576⟩ := by
    rw [ha.pointer, lenA, ka.x24]
    exact Offset.disjoint _ (by decide) (by decide) (by decide)
  have sdA : (below (a.sp) 16).Disjoint ⟨a.gpr .x2, (a.gpr .x3).toNat⟩ := by
    rw [ha.pointer, lenA, ka.x24.symm]
    exact hA.space.stackWork.sub_right (Offset.sub_base _ (by decide))
  refine WP.seq ((HPrime.update_ok v a _ d (ha.repr _ _ repr)
    (ha.count.trans count) (by rw [lenA]; omega) hA.space.stackMinimum hA.space.work dataA dsA dwA
    hA.space.stackWork sdA).mono ?_)
  rintro u ⟨reprU, regsU, rdU, wrU, spU, frameU⟩
  have ku : Keeps a u := Keeps.of_hash ⟨regsU, rdU, wrU, spU, HPrime.update_frame _ _ frameU⟩
  have ksu := ka.trans ku
  have hU := h.keeps ksu
  have prefixA : bytesAt a.mem (a.gpr .x2) (a.gpr .x3).toNat =
      Spec.Argon2.le32 (wordAt s lo).toNat := by rw [ha.pointer, lenA]; exact ha.prefix
  have r12U : u.gpr .x20 = s.gpr .x20 :=
    (regsU _ (by decide) (by decide)).trans (ha.other _ (by decide))
  have r14U : u.gpr .x22 = wordAt s lo := (regsU _ (by decide) (by decide)).trans ha.length
  refine WP.seq ((inputArgs_ok u po (slots_aligned po h.pointerSlot) (by have := h.pointerBound; omega) (hU.space.readable po h.pointerSlot)).mono ?_)
  intro x hx
  have kux := hx.keeps
  have ksx := ksu.trans kux
  have hX := h.keeps ksx
  have srcX : x.gpr .x2 = wordAt s po :=
    hx.pointer.trans (h.space.word_keeps ksu po h.pointerBound)
  have lenX : x.gpr .x3 = wordAt s lo := hx.length.trans r14U
  have r14X : x.gpr .x22 = wordAt s lo :=
    (hx.other _ (by decide)).trans r14U
  have reprX : Repr b (Spec.Blake2.init b 64 0) x.mem (x.gpr .x24)
      (d ++ Spec.Argon2.le32 (wordAt s lo).toNat) := by
    apply hx.repr
    rw [ku.x24]
    simpa only [prefixA] using reprU
  have prefixLen : (d ++ Spec.Argon2.le32 (wordAt s lo).toNat).length = d.length + 4 := by
    rw [List.length_append, Proof.Argon2.le32_length]
  have countX : x.gpr .x1 = BitVec.ofNat 64 (d ++ Spec.Argon2.le32 (wordAt s lo).toNat).length := by
    rw [hx.count, r12U, count, prefixLen, BitVec.ofNat_add]; rfl
  have coverX : Covers [⟨x.gpr .x2, (x.gpr .x3).toNat⟩] (x.rd ++ x.wr) := by
    rw [srcX, lenX, ksx.rd, ksx.wr]
    exact h.cover
  have dsX : (⟨x.gpr .x2, (x.gpr .x3).toNat⟩ : Region).Disjoint ⟨x.gpr .x24, 192⟩ := by
    rw [srcX, lenX, ksx.x24]
    exact h.work.sub_right (Region.sub_prefix (by decide))
  have dwX : (⟨x.gpr .x2, (x.gpr .x3).toNat⟩ : Region).Disjoint ⟨x.gpr .x24 + 192, 576⟩ := by
    rw [srcX, lenX, ksx.x24]
    exact h.work.sub_right (Offset.sub_base _ (by decide))
  have sdX : (below (x.sp) 16).Disjoint ⟨x.gpr .x2, (x.gpr .x3).toNat⟩ := by
    rw [srcX, lenX, ksx.sp]; exact h.stack.symm
  refine WP.seq ((HPrime.update_ok v x _ _ reprX countX
    (by rw [prefixLen, lenX]; exact bound) hX.space.stackMinimum hX.space.work coverX dsX dwX hX.space.stackWork sdX).mono ?_)
  rintro y ⟨reprY, regsY, rdY, wrY, spY, frameY⟩
  have ky : Keeps x y := Keeps.of_hash ⟨regsY, rdY, wrY, spY, HPrime.update_frame _ _ frameY⟩
  have ksy := ksx.trans ky
  have r12Y : y.gpr .x20 = BitVec.ofNat 64 (d.length + 4) := by
    rw [regsY _ (by decide) (by decide), hx.total, r12U, count, BitVec.ofNat_add]; rfl
  have r14Y : y.gpr .x22 = wordAt s lo := (regsY _ (by decide) (by decide)).trans r14X
  have bytesX : bytesAt x.mem (x.gpr .x2) (x.gpr .x3).toNat = inputBytes s po lo := by
    rw [srcX, lenX]
    exact ksx.bytes (inputRegion s po lo) h.work h.stack (Nat.le_of_lt (wordAt s lo).isLt)
  refine (addCount_ok y).mono ?_
  rintro t ⟨ht12, hm, kt⟩
  refine ⟨?_, ?_, ksy.trans kt⟩
  · rw [kt.x24, hm, ky.x24]
    simpa only [appendInput, inputBytes_length, bytesX] using reprY
  · have hw : BitVec.ofNat 64 (wordAt s lo).toNat = wordAt s lo := by
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    rw [ht12, r12Y, r14Y, ← hw, ← BitVec.ofNat_add,
      Proof.Argon2.appendInput_length, inputBytes_length]

end VG.Proof.Argon2.AArch64.Initial
