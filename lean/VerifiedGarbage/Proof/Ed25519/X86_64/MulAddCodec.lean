import VerifiedGarbage.Proof.Ed25519.X86_64.MulAddMemory
import VerifiedGarbage.Proof.Ed25519.Bytes

/-! Untrusted: full-width scalars and byte encodings in the working space. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64 VG.Impl.X25519.X86_64
open VG.Proof.X25519.X86_64
open VG.Spec.Ed25519 (bytesAt decodeLE)

theorem decodeLE_words (m : Mem) (base : Addr) (o : Nat) :
    decodeLE (bytesAt m (off base o) 32) = fe m base o := by
  rw [decodeLE_eq]
  change Proof.X25519.leNum (Spec.X25519.bytesAt m (off base o) 32) = _
  rw [Proof.X25519.leNum_bytesAt_words64]
  simp only [fe, val4, Proof.X25519.X86_64.word, off]
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
  simp only [fe, val4, Proof.X25519.X86_64.word, h 0 (by decide), h 8 (by decide), h 16 (by decide), h 24 (by decide)]

theorem storeWide_ok {s : State} {base : Addr} (hp : s.gpr .rdi = base)
    (hw : (⟨base, 8192⟩ : Region) ∈ s.wr) :
    WP isa (.block storeWide) s fun t =>
      decodeLE (bytesAt t.mem (off base 128) 64) = wideValue s ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ Outside base 128 64 s.mem t.mem := by
  rw [storeWide, WP.block_append_iff]
  refine WP.mono (stores8192_ok hp hw (by decide) .r8 .r9 .r10 .r11) fun t ⟨hm, hg, hrd, hwr⟩ => ?_
  refine WP.mono (stores8192_ok ((congrFun hg _).trans hp) (hwr ▸ hw) (by decide)
    .r12 .r13 .r14 .r15) fun u ⟨hm', hg', hrd', hwr'⟩ => ?_
  have ot : Outside base 128 32 s.mem t.mem := by rw [hm]; exact st4_outside _ _ (by decide) _ _ _ _
  have ou : Outside base 160 32 t.mem u.mem := by rw [hm']; exact st4_outside _ _ (by decide) _ _ _ _
  refine ⟨?_, hg'.trans hg, hrd'.trans hrd, hwr'.trans hwr,
    (ot.mono (by decide) (by decide)).trans (ou.mono (by decide) (by decide))⟩
  rw [decodeLE_wide, ou.fe (by decide) (by decide), hm', fe_st4 _ _ (by decide),
    hm, fe_st4 _ _ (by decide), hg]
  rfl

theorem reduceArgs_ok (s : State) :
    WP isa (.block reduceArgs) s fun t =>
      t.gpr .rsi = off (s.gpr .rdi) 128 ∧ t.gpr .rdx = s.gpr .rdi ∧
      t.gpr .rdi = s.gpr .rbx ∧ Keeps [.rsi, .rdx, .rdi] s t := by
  apply WP.of_runBlock
  simp only [reduceArgs, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, ite_true, ite_false, reduceCtorEq,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, trivial, trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2.1, hr.2.2, ite_false]

end VG.Proof.Ed25519.X86_64
