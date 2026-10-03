import VerifiedGarbage.Proof.Argon2.X86_64.Finish
import VerifiedGarbage.Proof.Argon2.X86_64.Taint
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Argon2.Permutation
import VerifiedGarbage.Proof.Argon2.X86_64.Words

/-! Merged from `Proof.Argon2.X86_64.Round`. -/
section
/-! # The row and column permutations in scratch -/

namespace VG.Proof.Argon2.X86_64

open VG VG.X86_64 VG.Spec.Argon2
open VG.Proof.Argon2

/-- Registers and permissions preserved throughout a scratch permutation. -/
def Keeps (s t : State) : Prop :=
  (∀ r, r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 →
    r ≠ .rax → r ≠ .rdx → r ≠ .rsi → t.gpr r = s.gpr r) ∧
  t.rd = s.rd ∧ t.wr = s.wr

theorem Keeps.refl (s : State) : Keeps s s := ⟨fun _ _ _ _ _ _ _ _ => rfl, rfl, rfl⟩

theorem Keeps.trans {s t u : State} (h : Keeps s t) (h' : Keeps t u) : Keeps s u :=
  ⟨fun r h8 h9 h10 h11 h0 hdx hsi =>
    (h'.1 r h8 h9 h10 h11 h0 hdx hsi).trans (h.1 r h8 h9 h10 h11 h0 hdx hsi),
    h'.2.1.trans h.2.1, h'.2.2.trans h.2.2⟩

theorem Scratch.of_keeps {s t : State} {p : Addr} (hs : Scratch s p)
    (hk : Keeps s t) : Scratch t p :=
  ⟨(hk.1 .rcx (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)).trans hs.reg, hk.2.2 ▸ hs.wr⟩

/-- The selected sixteen words and the unchanged words outside them. -/
def Holds (index : Fin 16 → Fin 128) (b : Block) (v : Vector Word 16)
    (m : Mem) (p : Addr) : Prop :=
  gather index (working m p) = v ∧
  ∀ k : Fin 128, (∀ j, index j ≠ k) → (working m p)[k] = b[k]

theorem holds_self (index : Fin 16 → Fin 128) (m : Mem) (p : Addr) :
    Holds index (working m p) (gather index (working m p)) m p :=
  ⟨rfl, fun _ _ => rfl⟩

/-- One GB advances the selected row or column and preserves its complement. -/
theorem step_ok (index : Fin 16 → Fin 128) (hi : Function.Injective index)
    (s : State) {p : Addr} (hs : Scratch s p) (base : Block) (v : Vector Word 16)
    (hv : Holds index base v s.mem p) (a b c d : Fin 16)
    (hab : a.val ≠ b.val) (hac : a.val ≠ c.val) (had : a.val ≠ d.val)
    (hbc : b.val ≠ c.val) (hbd : b.val ≠ d.val) (hcd : c.val ≠ d.val) :
    WP isa (Impl.Argon2.X86_64.gbAt (index a).val (index b).val (index c).val (index d).val)
      s fun t => Holds index base (GB v a b c d) t.mem p ∧
        Frame [⟨off p 1024, 1024⟩] s.mem t.mem ∧ Keeps s t := by
  refine (gbAt_words s hs (index a) (index b) (index c) (index d)).mono ?_
  rintro t ⟨hw, hf, hk⟩
  refine ⟨⟨?_, ?_⟩, hf, hk⟩
  · rw [hw, gather_mixWords index hi, hv.1, GB_eq_mixWords v hab hac had hbc hbd hcd]
  · intro k hn
    rw [hw]
    have ne (j : Fin 16) : (index j).val ≠ k.val := fun h => hn j (Fin.ext h)
    simp only [mixWords, Fin.getElem_fin, Vector.getElem_set, ne, ite_false]
    exact hv.2 k hn

/-- P on any injectively selected row or column, with a cumulative memory frame. -/
theorem permuteAt_holds (index : Fin 16 → Fin 128) (hi : Function.Injective index)
    (s : State) {p : Addr} (hs : Scratch s p) (base : Block) (v : Vector Word 16)
    (hv : Holds index base v s.mem p) :
    WP isa (Impl.Argon2.X86_64.permuteAt index) s fun t =>
      Holds index base (permute v) t.mem p ∧
      Frame [⟨off p 1024, 1024⟩] s.mem t.mem ∧ Keeps s t := by
  have advance (t : State) (v' : Vector Word 16)
      (h : Holds index base v' t.mem p ∧ Frame [⟨off p 1024, 1024⟩] s.mem t.mem ∧ Keeps s t)
      (a b c d : Fin 16)
      (hab : a.val ≠ b.val) (hac : a.val ≠ c.val) (had : a.val ≠ d.val)
      (hbc : b.val ≠ c.val) (hbd : b.val ≠ d.val) (hcd : c.val ≠ d.val) :
      WP isa (Impl.Argon2.X86_64.gbAt (index a).val (index b).val (index c).val (index d).val)
        t fun u => Holds index base (GB v' a b c d) u.mem p ∧
          Frame [⟨off p 1024, 1024⟩] s.mem u.mem ∧ Keeps s u := by
    refine (step_ok index hi t (hs.of_keeps h.2.2) base v' h.1 a b c d
      hab hac had hbc hbd hcd).mono ?_
    rintro u ⟨hu, hf, hk⟩
    exact ⟨hu, h.2.1.trans hf, h.2.2.trans hk⟩
  unfold Impl.Argon2.X86_64.permuteAt
  apply WP.seq
  refine (advance s _ ⟨hv, Frame.refl _ _, Keeps.refl s⟩ 0 4 8 12
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).mono ?_
  intro s1 h1
  apply WP.seq
  refine (advance s1 _ h1 1 5 9 13
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).mono ?_
  intro s2 h2
  apply WP.seq
  refine (advance s2 _ h2 2 6 10 14
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).mono ?_
  intro s3 h3
  apply WP.seq
  refine (advance s3 _ h3 3 7 11 15
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).mono ?_
  intro s4 h4
  apply WP.seq
  refine (advance s4 _ h4 0 5 10 15
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).mono ?_
  intro s5 h5
  apply WP.seq
  refine (advance s5 _ h5 1 6 11 12
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).mono ?_
  intro s6 h6
  apply WP.seq
  refine (advance s6 _ h6 2 7 8 13
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).mono ?_
  intro s7 h7
  exact advance s7 _ h7 3 4 9 14
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- The row/column code meets the specification's gather, P, scatter definition. -/
theorem permuteAt_ok (index : Fin 16 → Fin 128) (hi : Function.Injective index)
    (s : State) {p : Addr} (hs : Scratch s p) :
    WP isa (Impl.Argon2.X86_64.permuteAt index) s fun t =>
      working t.mem p = Spec.Argon2.permuteAt index (working s.mem p) ∧
      Frame [⟨off p 1024, 1024⟩] s.mem t.mem ∧ Keeps s t := by
  refine (permuteAt_holds index hi s hs (working s.mem p)
    (gather index (working s.mem p)) (holds_self index s.mem p)).mono ?_
  rintro t ⟨ht, hf, hk⟩
  exact ⟨eq_scatter index hi _ _ _ ht.1 ht.2, hf, hk⟩

/-- Compose a list of row or column permutations without re-executing any GB proof. -/
theorem rounds_ok (index : Fin 8 → Fin 16 → Fin 128)
    (hi : ∀ i, Function.Injective (index i)) (is : List (Fin 8))
    (s : State) {p : Addr} (hs : Scratch s p) :
    WP isa (is.foldr (fun i rest => .seq (Impl.Argon2.X86_64.permuteAt (index i)) rest)
      (.block [])) s fun t =>
      working t.mem p = is.foldl (fun b i => Spec.Argon2.permuteAt (index i) b) (working s.mem p) ∧
      Frame [⟨off p 1024, 1024⟩] s.mem t.mem ∧ Keeps s t := by
  induction is generalizing s with
  | nil => exact WP.block_nil ⟨rfl, Frame.refl _ _, Keeps.refl s⟩
  | cons i is ih =>
    apply WP.seq
    refine (permuteAt_ok (index i) (hi i) s hs).mono ?_
    rintro t ⟨ht, hf, hk⟩
    refine (ih t (hs.of_keeps hk)).mono ?_
    rintro u ⟨hu, hf', hk'⟩
    refine ⟨?_, hf.trans hf', hk.trans hk'⟩
    simpa only [List.foldl_cons, ht] using hu

end VG.Proof.Argon2.X86_64
end

/-! # Verified Argon2 block compression on x86-64 -/

namespace VG.Proof.Argon2.X86_64

open VG VG.X86_64 VG.Spec.Argon2

theorem CopyKeeps.callee {s t : State} (h : CopyKeeps s t) :
    ∀ r ∈ calleeSaved, t.gpr r = s.gpr r := by
  intro r hr
  apply h.1
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem Keeps.callee {s t : State} (h : Keeps s t) :
    ∀ r ∈ calleeSaved, t.gpr r = s.gpr r := by
  intro r hr
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact h.1 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem move_output (s : State) :
    WP isa (.block [.mov .rdi (.reg .rdx)]) s fun t =>
      t.gpr .rdi = s.gpr .rdx ∧
      (∀ r, r ≠ .rdi → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    Option.map_some, Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg,
    RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, ite_true]
  exact ⟨trivial, fun r hr => by simp only [hr, ite_false], trivial, trivial, trivial⟩

theorem original_preserved {m m' : Mem} {p : Addr}
    (hf : Frame [⟨off p 1024, 1024⟩] m m') : blockAt m' p = blockAt m p := by
  apply Vector.ext
  intro i hi
  have he : m'.readW (off p (8 * i)) 64 = m.readW (off p (8 * i)) 64 :=
    hf.readW (r := ⟨p, 1024⟩) (Offset.contains_base p (by omega) (by omega))
      (by
        intro r hr
        simp only [List.mem_singleton] at hr
        subst r
        exact Offset.base_disjoint p (by decide) (by decide)) (by decide)
  rw [← blockAt_get m' p ⟨i, hi⟩, ← blockAt_get m p ⟨i, hi⟩] at he
  exact he

theorem round_frame {m m' : Mem} {p out : Addr}
    (hf : Frame [⟨off p 1024, 1024⟩] m m') : Frame [⟨out, 1024⟩, ⟨p, 4096⟩] m m' := by
  apply hf.sub
  intro r hr
  simp only [List.mem_singleton] at hr
  subst r
  exact ⟨⟨p, 4096⟩, by simp, Offset.sub_base p (by decide)⟩

theorem compress_wp (s : State) (hs : compressLocal.pre s) :
    WP isa Impl.Argon2.X86_64.compress s fun t =>
      compressLocal.post s t ∧ (∀ r ∈ calleeSaved, t.gpr r = s.gpr r) ∧
      Frame s.wr s.mem t.mem := by
  obtain ⟨hrd, hwr, hout, hx, hy, _, _⟩ := hs
  have scr : Scratch s (s.gpr .rcx) := ⟨rfl, by simp [hwr]⟩
  have inputs : Inputs s (s.gpr .rdi) (s.gpr .rsi) (s.gpr .rcx) :=
    ⟨rfl, rfl, by simp [hrd], by simp [hrd], hx, hy⟩
  unfold Impl.Argon2.X86_64.compress
  apply WP.seq
  refine (init_prefix 128 (by decide) s scr inputs).mono ?_
  rintro s1 ⟨hinit, hf1, hk1⟩
  obtain ⟨horig, hwork⟩ := initialized_blocks hinit
  apply WP.seq
  refine (move_output s1).mono ?_
  rintro s2 ⟨hout2, hk2, hm2, hr2, hw2⟩
  have scr2 : Scratch s2 (s.gpr .rcx) :=
    ⟨(hk2 .rcx (by decide)).trans ((hk1.1 .rcx (by decide)).trans rfl),
      (hw2.trans hk1.2.2) ▸ scr.wr⟩
  apply WP.seq
  refine (rounds_ok rowIndex Proof.Argon2.rowIndex_injective (List.finRange 8) s2 scr2).mono ?_
  rintro s3 ⟨hrow, hf3, hk3⟩
  apply WP.seq
  refine (rounds_ok colIndex Proof.Argon2.colIndex_injective (List.finRange 8)
    s3 (scr2.of_keeps hk3)).mono ?_
  rintro s4 ⟨hcol, hf4, hk4⟩
  have hout4 : s4.gpr .rdi = s.gpr .rdx := by
    rw [hk4.1 .rdi (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hk3.1 .rdi (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hout2, hk1.1 .rdx (by decide)]
  have hw4 : s4.wr = s.wr := hk4.2.2.trans (hk3.2.2.trans (hw2.trans hk1.2.2))
  refine (finish_prefix 128 (by decide) s4 ((scr2.of_keeps hk3).of_keeps hk4) hout4
    (by rw [hw4, hwr]; simp) hout.symm).mono ?_
  rintro t ⟨hfinish, hf5, hk5⟩
  refine ⟨?_, ?_, ?_⟩
  · have ho4 := original_preserved (hf3.trans hf4)
    rw [hm2, horig] at ho4
    have he := written_block hfinish
    rw [hcol, hrow, hm2, hwork, ho4] at he
    exact he
  · intro r hr
    have ne : r ≠ .rdi := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (hk5.callee r hr).trans ((hk4.callee r hr).trans ((hk3.callee r hr).trans
      ((hk2 r ne).trans (hk1.callee r hr))))
  · rw [hwr]
    have f1 : Frame [⟨s.gpr .rdx, 1024⟩, ⟨s.gpr .rcx, 4096⟩] s.mem s1.mem :=
      hf1.mono (by intro r hr; simp only [List.mem_singleton] at hr; subst r; simp)
    have f2 : Frame [⟨s.gpr .rdx, 1024⟩, ⟨s.gpr .rcx, 4096⟩] s1.mem s2.mem := by
      rw [hm2]; exact Frame.refl _ _
    have f5 : Frame [⟨s.gpr .rdx, 1024⟩, ⟨s.gpr .rcx, 4096⟩] s4.mem t.mem :=
      hf5.mono (by intro r hr; simp only [List.mem_singleton] at hr; subst r; simp)
    exact (((f1.trans f2).trans (round_frame hf3)).trans (round_frame hf4)).trans f5

/-- Correctness, termination, memory safety, and the System V ABI. -/
theorem compress_correct (s : State) (hs : compressLocal.pre s) :
    ∃ tr t, Exec isa Impl.Argon2.X86_64.compress s tr t ∧ abiPreserved s t ∧
      compressLocal.post s t := by
  obtain ⟨tr, t, he, hp, hk, hf⟩ := compress_wp s hs
  refine ⟨tr, t, he, abiPreserved_of_exec (by lit_decide) he ⟨hk, ?_⟩, hp⟩
  apply hf.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) _ (by decide)
  intro r hr
  rw [hs.2.1] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hs.2.2.2.2.2.1
  · exact hs.2.2.2.2.2.2

/-- The emitted primitive is verified against the merged, target-independent contract. -/
theorem compress_verified : Verified X86_64.target Impl.Argon2.X86_64.compress
    (Spec.Argon2.compressContract X86_64.abi) :=
  Verified.of_correct compress_correct compress_ct compress_implies

end VG.Proof.Argon2.X86_64
