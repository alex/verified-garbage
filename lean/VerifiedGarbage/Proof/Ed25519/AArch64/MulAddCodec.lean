import VerifiedGarbage.Proof.Ed25519.AArch64.MulAddMemory
import VerifiedGarbage.Proof.Ed25519.Bytes

/-! Full-width scalars and byte encodings in the working space. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64
open Word64
open VG.Spec.Ed25519 (bytesAt decodeLE)

theorem decodeLE_words (m : Mem) (base : Addr) (o : Nat) :
    decodeLE (bytesAt m (off base o) 32) = fe m base o := by
  rw [decodeLE_eq]
  change Proof.X25519.leNum (Spec.X25519.bytesAt m (off base o) 32) = _
  rw [Proof.X25519.leNum_bytesAt_words64]
  simp only [fe, val4, word, off]
  rw [show base + BitVec.ofNat 64 o + 8 = base + BitVec.ofNat 64 (o + 8) from Offset.add_add ..,
    show base + BitVec.ofNat 64 o + 16 = base + BitVec.ofNat 64 (o + 16) from Offset.add_add ..,
    show base + BitVec.ofNat 64 o + 24 = base + BitVec.ofNat 64 (o + 24) from Offset.add_add ..]

theorem decodeLE_wide (m : Mem) (base : Addr) :
    decodeLE (bytesAt m (off base 128) 64) = fe m base 128 + 2 ^ 256 * fe m base 160 := by
  have hb : bytesAt m (off base 128) 64 =
      bytesAt m (off base 128) 32 ++ bytesAt m (off base 160) 32 := by
    have h := Proof.X25519.bytesAt_add m (off base 128) 32 32
    rw [Offset.add_add] at h
    exact h
  rw [hb, decodeLE_append, bytesAt_length, decodeLE_words, decodeLE_words]
  rfl

theorem scratchFrame {base : Addr} {o n : Nat} {m m' : Mem}
    (h : Outside base o n m m') (hn : o + n ≤ 8192) : Frame [⟨base, 8192⟩] m m' := by
  intro x hx
  apply h x
  right
  have hn' := hx _ (List.mem_singleton_self _)
  simp only [Region.Contains] at hn'
  simp only [ofs]
  omega

theorem fe_frame {base p : Addr} {m m' : Mem} (hf : Frame [⟨base, 8192⟩] m m')
    (hp : (⟨p, 32⟩ : Region).Disjoint ⟨base, 8192⟩) : fe m' p 0 = fe m p 0 := by
  have h : ∀ d, d + 8 ≤ 32 → m'.readW (off p d) 64 = m.readW (off p d) 64 := fun d hd =>
    hf.readW (r := ⟨p, 32⟩) (Offset.contains_base _ hd (by omega))
      (by simpa only [List.mem_singleton, forall_eq]) (by decide)
  simp only [fe, val4, word, h 0 (by decide), h 8 (by decide), h 16 (by decide), h 24 (by decide)]

theorem storeWide_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block storeWide) s fun t =>
      decodeLE (bytesAt t.mem (off base 128) 64) = wideValue s ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      Outside base 128 64 s.mem t.mem := by
  rw [storeWide, WP.block_append_iff]
  refine WP.mono (stores_ok hs (by constructor <;> decide) .x4 .x5 .x6 .x7) fun t ht => ?_
  subst t
  refine WP.mono (stores_ok (hs.setMem _) (by constructor <;> decide) .x21 .x22 .x23 .x24) fun u hu => ?_
  subst u
  have ot := st4_outside s.mem base (show 128 + 32 < 2 ^ 64 by decide)
    (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7)
  have ou := st4_outside (st4 s.mem base 128 (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7))
    base (show 160 + 32 < 2 ^ 64 by decide) (s.gpr .x21) (s.gpr .x22) (s.gpr .x23) (s.gpr .x24)
  refine ⟨?_, rfl, rfl, rfl, rfl,
    (ot.mono (by decide) (by decide)).trans (ou.mono (by decide) (by decide))⟩
  rw [decodeLE_wide, ou.fe (by decide) (by decide), fe_st4 _ _ (by decide), fe_st4 _ _ (by decide)]
  rfl

theorem reduceArgs_ok (s : State) :
    WP isa (.block reduceArgs) s fun t =>
      t.gpr .x1 = off (s.gpr .x0) 128 ∧ t.gpr .x2 = s.gpr .x0 ∧
      t.gpr .x0 = s.gpr .x19 ∧ Keeps [.x1, .x2, .x0] s t := by
  apply WP.of_runBlock
  simp only [reduceArgs, runBlock_cons, runStep_some, runBlock_nil, exec, mov, read_x,
    show (128 : Nat) < 4096 from by decide, show (0 : Nat) < 4096 from by decide,
    RegUpd.gpr_write, BitVec.setWidth_eq, BitVec.add_zero, ite_true, ite_false, reduceCtorEq,
    Option.some.injEq, exists_eq_left']
  refine ⟨True.intro, True.intro, True.intro, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2, ite_false]

end VG.Proof.Ed25519.AArch64
