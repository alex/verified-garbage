import VerifiedGarbage.Proof.Argon2.X86_64.InitialLayout

/-! Merged from `Proof.Argon2.X86_64.InitialPrep`. -/
section
/-! Merged from `Proof.Argon2.X86_64.InitialHeader`. -/
section
/-! # Writing and reading the six words of the H₀ header -/

namespace VG.Proof.Argon2.X86_64.Initial

open VG VG.X86_64 VG.Impl.Argon2.X86_64.Initial
open VG.Impl.Argon2.X86_64.HPrime (at_)
open VG.Spec.Blake2 (bytesAt)

def headerValue (s : State) (j : Nat) : BitVec 32 :=
  if j = 4 then 0x13 else (wordAt s (headerSource j)).setWidth 32

def headerMem (s : State) : Nat → Mem
  | 0 => s.mem
  | n + 1 => (headerMem s n).writeW (s.gpr .rbx + BitVec.ofNat 64 (768 + 4 * n))
    (headerValue s n)

theorem headerSource_slot (j : Nat) : headerSource j ∈ slots := by
  unfold headerSource
  split <;> (try split) <;> (try split) <;> (try split) <;> decide

theorem headerSource_bound (j : Nat) : headerSource j + 8 ≤ 272 := by
  unfold headerSource
  split <;> (try split) <;> (try split) <;> (try split) <;> decide

theorem headerValue_keeps {s t : State} (h : Space s) (k : Keeps s t) (j : Nat) :
    headerValue t j = headerValue s j := by
  unfold headerValue
  rw [h.word_keeps k _ (headerSource_bound j)]

theorem headerMem_frame (s : State) (n : Nat) (hn : n ≤ 6) :
    Frame [⟨s.gpr .rbx + 768, 24⟩] s.mem (headerMem s n) := by
  induction n with
  | zero => exact Frame.refl _ _
  | succ n ih =>
    exact (ih (by omega)).writeW (List.mem_singleton_self _) _
      (by
        rw [show (768 : Addr) = BitVec.ofNat 64 768 from rfl, BitVec.ofNat_add,
          ← BitVec.add_assoc]
        exact Offset.contains_base _ (by omega) (by omega))

theorem headerMem_read (s : State) (n j : Nat) (hn : n ≤ 6) (hj : j < n) :
    (headerMem s n).readW (s.gpr .rbx + BitVec.ofNat 64 (768 + 4 * j)) 32 =
      headerValue s j := by
  induction n with
  | zero => omega
  | succ n ih =>
    unfold headerMem
    by_cases he : j = n
    · subst j; exact Mem.readW_writeW_self32 ..
    · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega : 768 + 4 * j + 4 ≤ 768 + 4 * n ∨
        768 + 4 * n + 4 ≤ 768 + 4 * j) (by omega) (by omega)) (by decide)]
      exact ih (by omega) (by omega)

theorem headerMem_bytes (s : State) :
    bytesAt (headerMem s 6) (s.gpr .rbx + 768) 24 =
      (List.range 6).flatMap (fun j => Spec.Blake2.wordBytes (headerValue s j)) := by
  rw [show 24 = 32 / 8 * 6 from rfl, Proof.Blake2.bytesAt_words (w := 32)]
  simp only [List.flatMap]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro j hj
  rw [← Proof.Blake2.wordBytes_readW _ _ (Or.inl rfl)]
  rw [show (768 : Addr) = BitVec.ofNat 64 768 from rfl, BitVec.add_assoc,
    ← BitVec.ofNat_add, headerMem_read s 6 j (by decide) (List.mem_range.mp hj)]

theorem headerSlot_ok (s : State) (j : Nat) (hj : j < 6) (h : Space s) :
    WP isa (.block (headerSlot j)) s fun t =>
      t.mem = s.mem.writeW (s.gpr .rbx + BitVec.ofNat 64 (768 + 4 * j)) (headerValue s j) ∧
      Keeps s t := by
  have hw := h.write (768 + 4 * j) 4 (by omega)
  have finish (t : State) (hm : t.mem = s.mem.writeW
      (s.gpr .rbx + BitVec.ofNat 64 (768 + 4 * j)) (headerValue s j))
      (regs : ∀ r, r ≠ .rax → t.gpr r = s.gpr r) (rd : t.rd = s.rd) (wr : t.wr = s.wr) :
      t.mem = s.mem.writeW (s.gpr .rbx + BitVec.ofNat 64 (768 + 4 * j)) (headerValue s j) ∧
        Keeps s t := by
    refine ⟨hm, fun r hr _ _ => regs r ?_, rd, wr, ?_⟩
    · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    · rw [hm]
      exact (Frame.refl _ _).writeW (List.mem_cons_self ..) _
        (Offset.contains_base _ (by omega) (by omega))
  unfold headerSlot
  split
  · next he =>
    subst j
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, State.setReg32,
      State.store32, ea_at, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.wr_setReg,
      hw, reduceCtorEq, ite_true, ite_false, Option.map_some,
      Option.some.injEq, exists_eq_left', BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64),
      BitVec.setWidth_eq]
    refine ⟨rfl, fun r hr _ _ => ?_, rfl, rfl, ?_⟩
    · have hn : r ≠ .rax := by
        simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      simp only [RegUpd.gpr_setReg, hn, ite_false]
    · exact (Frame.refl _ _).writeW (List.mem_cons_self ..) _
        (Offset.contains_base _ (by decide) (by decide))
  · next he =>
    refine (headerWord_ok s _ _ (h.readable _ (headerSource_slot j)) hw).mono ?_
    rintro t ⟨hm, regs, rd, wr⟩
    exact finish t (by simpa only [headerValue, he, ite_false, wordAt] using hm) regs rd wr

theorem headerWords_ok (s : State) (n : Nat) (hn : n ≤ 6) (h : Space s) :
    WP isa (.block ((List.range n).flatMap headerSlot)) s fun t =>
      t.mem = headerMem s n ∧ Keeps s t := by
  induction n with
  | zero =>
    exact WP.block_nil ⟨rfl, fun _ _ _ _ => rfl, rfl, rfl, Frame.refl _ _⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine (ih (by omega)).mono ?_
    rintro u ⟨hu, ku⟩
    refine (headerSlot_ok u n (by omega) (h.keeps ku)).mono ?_
    rintro t ⟨ht, kt⟩
    refine ⟨?_, ku.trans kt⟩
    rw [ht, ku.rbx, headerValue_keeps h ku, hu]
    rfl

theorem header_ok (s : State) (h : Space s) :
    WP isa (.block header) s fun t =>
      bytesAt t.mem (s.gpr .rbx + 768) 24 =
        (List.range 6).flatMap (fun j => Spec.Blake2.wordBytes (headerValue s j)) ∧ Keeps s t :=
  (headerWords_ok s 6 (by decide) h).mono fun t ⟨hm, hk⟩ =>
    ⟨by rw [hm]; exact headerMem_bytes s, hk⟩

end VG.Proof.Argon2.X86_64.Initial
end

/-! # H₀: preserving the stack across input argument preparation -/

namespace VG.Proof.Argon2.X86_64.Initial

open VG VG.X86_64 VG.Impl.Argon2.X86_64.Initial
open VG.Spec.Blake2 (bytesAt)

theorem LengthArgs.keeps {s t : State} {offset : Nat} (h : LengthArgs s offset t) :
    Keeps s t := by
  refine ⟨fun r hr _ h14 => ?_, h.rd, h.wr, ?_⟩
  · have hn : r ≠ .rsi ∧ r ≠ .rdx ∧ r ≠ .rcx := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact h.other r h14 hn.1 hn.2.1 hn.2.2
  · rw [h.mem]
    exact (Frame.refl _ _).writeW (List.mem_cons_self ..) _
      (Offset.contains_base _ (by decide) (by decide))

theorem InputArgs.keeps {s t : State} {offset : Nat} (h : InputArgs s t offset) :
    Keeps s t := by
  refine ⟨fun r hr h12 _ => ?_, h.rd, h.wr, ?_⟩
  · have hn : r ≠ .rsi ∧ r ≠ .rdx ∧ r ≠ .rcx := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact h.other r h12 hn.1 hn.2.1 hn.2.2
  · rw [h.mem]; exact Frame.refl _ _

theorem LengthArgs.prefix {s t : State} {offset : Nat} (h : LengthArgs s offset t) :
    bytesAt t.mem (s.gpr .rbx + 792) 4 = Spec.Argon2.le32 (wordAt s offset).toNat := by
  rw [← Proof.Blake2.wordBytes_readW (w := 32) _ _ (Or.inl rfl), h.mem,
    Mem.readW_writeW_self32]
  rfl

theorem LengthArgs.repr {s t : State} {offset : Nat} (h : LengthArgs s offset t)
    (h0 : Spec.Blake2.HashValue 64) (d : List Byte)
    (repr : Spec.Blake2.Repr Spec.Blake2.b h0 s.mem (s.gpr .rbx) d) :
    Spec.Blake2.Repr Spec.Blake2.b h0 t.mem (t.gpr .rbx) d := by
  rw [h.keeps.rbx]
  apply Proof.Blake2.X86_64.Stream.Update.repr_congr Proof.Blake2.X86_64.Stream.okB
    (mem := s.mem) _ repr
  intro i hi
  have f : Frame [⟨s.gpr .rbx + 792, 4⟩] s.mem t.mem := by
    rw [h.mem]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  apply f.bytes (R := ⟨s.gpr .rbx, 192⟩) _ (show (192 : Nat) ≤ 2 ^ 64 from by decide) hi
  intro r hr
  simp only [List.mem_singleton] at hr; subst r
  exact Offset.base_disjoint _ (by decide) (by decide)

theorem InputArgs.repr {s t : State} {offset : Nat} (h : InputArgs s t offset)
    (h0 : Spec.Blake2.HashValue 64) (d : List Byte)
    (repr : Spec.Blake2.Repr Spec.Blake2.b h0 s.mem (s.gpr .rbx) d) :
    Spec.Blake2.Repr Spec.Blake2.b h0 t.mem (t.gpr .rbx) d := by
  rw [h.keeps.rbx, h.mem]; exact repr

theorem addCount_ok (s : State) :
    WP isa (.block [.alu .add .r12 (.reg .r14)]) s fun t =>
      t.gpr .r12 = s.gpr .r12 + s.gpr .r14 ∧ t.mem = s.mem ∧ Keeps s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, fun r hr h12 _ => ?_, rfl, rfl, Frame.refl _ _⟩
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, h12, ite_false]

end VG.Proof.Argon2.X86_64.Initial
end

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
