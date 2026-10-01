import VerifiedGarbage.Proof.Argon2.X86_64.InitialPrep

/-! # H₀: absorb a length-prefixed byte-string input -/

namespace VG.Proof.Argon2.X86_64.Initial

open VG VG.X86_64 VG.Impl.Argon2.X86_64.Initial
open VG.Spec.Blake2 (bytesAt b Repr)
open VG.Proof.Argon2 (appendInput)

structure InputReady (s : State) (po lo : Nat) : Prop where
  space : Space s
  pointerSlot : po ∈ slots
  lengthSlot : lo ∈ slots
  pointerBound : po + 8 ≤ 272
  lengthBound : lo + 8 ≤ 272
  length : (wordAt s lo).toNat < 2 ^ 32
  cover : Covers [inputRegion s po lo] (s.rd ++ s.wr)
  work : (inputRegion s po lo).Disjoint ⟨s.gpr .rbx, 16384⟩
  stack : (inputRegion s po lo).Disjoint (below (s.gpr .rsp) 16)

theorem InputReady.keeps {s t : State} {po lo : Nat} (h : InputReady s po lo)
    (k : Keeps s t) : InputReady t po lo := by
  have reg := h.space.input_keeps k po lo h.pointerBound h.lengthBound
  refine ⟨h.space.keeps k, h.pointerSlot, h.lengthSlot, h.pointerBound, h.lengthBound,
    ?_, ?_, ?_, ?_⟩
  · rw [h.space.word_keeps k lo h.lengthBound]; exact h.length
  · rw [reg, k.rd, k.wr]; exact h.cover
  · rw [reg, k.rbx]; exact h.work
  · rw [reg, k.rsp]; exact h.stack

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

theorem absorb_ok (v : Proof.Blake2.X86_64.Backend) (s : State) (po lo : Nat)
    (h : InputReady s po lo) (d : List Byte)
    (repr : Repr b (Spec.Blake2.init b 64 0) s.mem (s.gpr .rbx) d)
    (count : s.gpr .r12 = BitVec.ofNat 64 d.length)
    (bound : d.length + 4 + (wordAt s lo).toNat < 2 ^ 64) :
    WP isa (absorb (HPrime.hash v) po lo) s fun t =>
      Repr b (Spec.Blake2.init b 64 0) t.mem (t.gpr .rbx)
        (appendInput d (inputBytes s po lo)) ∧
      t.gpr .r12 = BitVec.ofNat 64 (appendInput d (inputBytes s po lo)).length ∧ Keeps s t := by
  unfold absorb
  refine WP.seq ((lengthArgs_ok s lo (h.space.readable lo h.lengthSlot)
    (by simpa using h.space.write 792 4 (by decide))).mono ?_)
  intro a ha
  have ka := ha.keeps
  have hA := h.keeps ka
  have lenA : (a.gpr .rcx).toNat = 4 := by rw [ha.size]; rfl
  have dataA : Covers [⟨a.gpr .rdx, (a.gpr .rcx).toNat⟩] (a.rd ++ a.wr) := by
    rw [ha.pointer, lenA, ka.rbx.symm]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_singleton] at hr; subst r
    exact ⟨⟨a.gpr .rbx, 16384⟩, List.mem_append_right _ hA.space.work,
      792, rfl, by change 792 + 4 ≤ 16384; decide⟩
  have dsA : (⟨a.gpr .rdx, (a.gpr .rcx).toNat⟩ : Region).Disjoint ⟨a.gpr .rbx, 192⟩ := by
    rw [ha.pointer, lenA, ka.rbx]
    exact (Offset.base_disjoint _ (by decide) (by decide)).symm
  have dwA : (⟨a.gpr .rdx, (a.gpr .rcx).toNat⟩ : Region).Disjoint ⟨a.gpr .rbx + 192, 576⟩ := by
    rw [ha.pointer, lenA, ka.rbx]
    exact Offset.disjoint _ (by decide) (by decide) (by decide)
  have sdA : (below (a.gpr .rsp) 16).Disjoint ⟨a.gpr .rdx, (a.gpr .rcx).toNat⟩ := by
    rw [ha.pointer, lenA, ka.rbx.symm]
    exact hA.space.stackWork.sub_right (Offset.sub_base _ (by decide))
  refine WP.seq ((HPrime.update_ok v a _ d (ha.repr _ _ repr)
    (ha.count.trans count) (by rw [lenA]; omega) hA.space.work dataA dsA dwA
    hA.space.stackWork sdA).mono ?_)
  rintro u ⟨reprU, regsU, rdU, wrU, frameU⟩
  have ku : Keeps a u := Keeps.of_hash ⟨regsU, rdU, wrU, HPrime.update_frame _ _ frameU⟩
  have ksu := ka.trans ku
  have hU := h.keeps ksu
  have prefixA : bytesAt a.mem (a.gpr .rdx) (a.gpr .rcx).toNat =
      Spec.Argon2.le32 (wordAt s lo).toNat := by rw [ha.pointer, lenA]; exact ha.prefix
  have r12U : u.gpr .r12 = s.gpr .r12 :=
    (regsU _ (by decide)).trans (ha.other _ (by decide) (by decide) (by decide) (by decide))
  have r14U : u.gpr .r14 = wordAt s lo := (regsU _ (by decide)).trans ha.length
  refine WP.seq ((inputArgs_ok u po (hU.space.readable po h.pointerSlot)).mono ?_)
  intro x hx
  have kux := hx.keeps
  have ksx := ksu.trans kux
  have hX := h.keeps ksx
  have srcX : x.gpr .rdx = wordAt s po :=
    hx.pointer.trans (h.space.word_keeps ksu po h.pointerBound)
  have lenX : x.gpr .rcx = wordAt s lo := hx.length.trans r14U
  have r14X : x.gpr .r14 = wordAt s lo :=
    (hx.other _ (by decide) (by decide) (by decide) (by decide)).trans r14U
  have reprX : Repr b (Spec.Blake2.init b 64 0) x.mem (x.gpr .rbx)
      (d ++ Spec.Argon2.le32 (wordAt s lo).toNat) := by
    apply hx.repr
    rw [ku.rbx]
    simpa only [prefixA] using reprU
  have prefixLen : (d ++ Spec.Argon2.le32 (wordAt s lo).toNat).length = d.length + 4 := by
    rw [List.length_append, Proof.Argon2.le32_length]
  have countX : x.gpr .rsi = BitVec.ofNat 64 (d ++ Spec.Argon2.le32 (wordAt s lo).toNat).length := by
    rw [hx.count, r12U, count, prefixLen, BitVec.ofNat_add]; rfl
  have coverX : Covers [⟨x.gpr .rdx, (x.gpr .rcx).toNat⟩] (x.rd ++ x.wr) := by
    rw [srcX, lenX, ksx.rd, ksx.wr]
    exact h.cover
  have dsX : (⟨x.gpr .rdx, (x.gpr .rcx).toNat⟩ : Region).Disjoint ⟨x.gpr .rbx, 192⟩ := by
    rw [srcX, lenX, ksx.rbx]
    exact h.work.sub_right (Region.sub_prefix (by decide))
  have dwX : (⟨x.gpr .rdx, (x.gpr .rcx).toNat⟩ : Region).Disjoint ⟨x.gpr .rbx + 192, 576⟩ := by
    rw [srcX, lenX, ksx.rbx]
    exact h.work.sub_right (Offset.sub_base _ (by decide))
  have sdX : (below (x.gpr .rsp) 16).Disjoint ⟨x.gpr .rdx, (x.gpr .rcx).toNat⟩ := by
    rw [srcX, lenX, ksx.rsp]; exact h.stack.symm
  refine WP.seq ((HPrime.update_ok v x _ _ reprX countX
    (by rw [prefixLen, lenX]; exact bound) hX.space.work coverX dsX dwX hX.space.stackWork sdX).mono ?_)
  rintro y ⟨reprY, regsY, rdY, wrY, frameY⟩
  have ky : Keeps x y := Keeps.of_hash ⟨regsY, rdY, wrY, HPrime.update_frame _ _ frameY⟩
  have ksy := ksx.trans ky
  have r12Y : y.gpr .r12 = BitVec.ofNat 64 (d.length + 4) := by
    rw [regsY _ (by decide), hx.total, r12U, count, BitVec.ofNat_add]; rfl
  have r14Y : y.gpr .r14 = wordAt s lo := (regsY _ (by decide)).trans r14X
  have bytesX : bytesAt x.mem (x.gpr .rdx) (x.gpr .rcx).toNat = inputBytes s po lo := by
    rw [srcX, lenX]
    exact ksx.bytes (inputRegion s po lo) h.work h.stack (Nat.le_of_lt (wordAt s lo).isLt)
  refine (addCount_ok y).mono ?_
  rintro t ⟨ht12, hm, kt⟩
  refine ⟨?_, ?_, ksy.trans kt⟩
  · rw [kt.rbx, hm, ky.rbx]
    simpa only [appendInput, inputBytes_length, bytesX] using reprY
  · have hw : BitVec.ofNat 64 (wordAt s lo).toNat = wordAt s lo := by
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    rw [ht12, r12Y, r14Y, ← hw, ← BitVec.ofNat_add,
      Proof.Argon2.appendInput_length, inputBytes_length]

end VG.Proof.Argon2.X86_64.Initial
