import VerifiedGarbage.Impl.Ed25519.AArch64.SignCached.Prefix
import VerifiedGarbage.Proof.Ed25519.AArch64.Mem
import VerifiedGarbage.Proof.Ed25519.Signing
import VerifiedGarbage.Proof.Ed25519.AArch64.MulAddCodec

namespace VG.Proof.Ed25519.AArch64.SignCached
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.SignCached

structure PrefixStep (s t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  vec : t.v = s.v
  regs : ∀ r, r ≠ .x0 → r ≠ .x15 → t.gpr r = s.gpr r

theorem PrefixStep.trans {s t u : State} (h : PrefixStep s t) (h' : PrefixStep t u) : PrefixStep s u :=
  ⟨h'.rd.trans h.rd, h'.wr.trans h.wr, h'.sp.trans h.sp, h'.vec.trans h.vec,
    fun r h0 h15 => (h'.regs r h0 h15).trans (h.regs r h0 h15)⟩

theorem copyWord_ok {s : State} {E : Addr} (he : s.sp = E)
    (hr : (⟨E, 256⟩ : Region) ∈ s.wr) {k : Nat} (hk : k < 4) :
    WP isa (.block (copyWord k)) s fun t => PrefixStep s t ∧
      t.mem = s.mem.writeW (E + BitVec.ofNat 64 (64 + 8 * k))
        (s.mem.readW (E + BitVec.ofNat 64 (224 + 8 * k)) 64) := by
  have source : InRegions (s.rd ++ s.wr) (E + BitVec.ofNat 64 (224 + 8 * k)) 8 :=
    ⟨⟨E, 256⟩, List.mem_append_right _ hr, Offset.contains_base E (by omega) (by omega)⟩
  have dest : InRegions s.wr (E + BitVec.ofNat 64 (64 + 8 * k)) 8 :=
    ⟨⟨E, 256⟩, hr, Offset.contains_base E (by omega) (by omega)⟩
  have hl : exec (.ldrSp .x0 (224 + 8 * k)) s =
      some (s.write .x .x0 (s.mem.readW (E + BitVec.ofNat 64 (224 + 8 * k)) 64)) := by
    simp only [exec, show (224 + 8 * k) % 8 = 0 ∧ 224 + 8 * k < 32768 from by omega,
      and_self, ite_true, State.load, he, source, Option.map_some, Mem.readW, BitVec.setWidth_eq]
  have ha {t : State} : exec (.addSp .x15 64) t = some (t.write .x .x15 (t.sp + BitVec.ofNat 64 64)) := by
    simp only [exec, show 64 < 4096 from by decide, ite_true]
  apply WP.of_runBlock
  simp only [copyWord, runBlock_cons, runStep_some, hl, ha, RegUpd.sp_write]
  rw [exec_str_x ⟨by omega, by omega⟩ (by
    simpa only [RegUpd.wr_write, RegUpd.gpr_write_self, BitVec.setWidth_eq, he, Offset.add_add] using dest)]
  simp only [runStep_some, runBlock_nil, Option.some.injEq, exists_eq_left']
  refine ⟨⟨rfl, rfl, rfl, rfl, ?_⟩, ?_⟩
  · intro r h0 h15
    simp only [RegUpd.gpr_write, h0, h15, ite_false]
  · simp only [RegUpd.mem_write, RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false,
      BitVec.setWidth_eq, he, Offset.add_add]

structure PrefixInv (E : Addr) (s : State) (n : Nat) (t : State) : Prop where
  step : PrefixStep s t
  frame : Frame [⟨E + BitVec.ofNat 64 64, 32⟩] s.mem t.mem
  words : ∀ j < n, t.mem.readW (E + BitVec.ofNat 64 (64 + 8 * j)) 64 =
    s.mem.readW (E + BitVec.ofNat 64 (224 + 8 * j)) 64

theorem copyPrefix_ok {s : State} {E : Addr} (he : s.sp = E)
    (hw : (⟨E, 256⟩ : Region) ∈ s.wr) :
    ∀ n ≤ 4, WP isa (.block ((List.range n).flatMap copyWord)) s (PrefixInv E s n)
  | 0, _ => WP.block_nil ⟨⟨rfl, rfl, rfl, rfl, fun _ _ _ => rfl⟩, Frame.refl _ _, fun _ h => by omega⟩
  | n + 1, hn => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (copyPrefix_ok he hw n (by omega)) fun u hu => ?_
    refine WP.mono (copyWord_ok (hu.step.sp.trans he) (hu.step.wr ▸ hw) (by omega : n < 4))
      fun t ⟨kt, mt⟩ => ?_
    have same : u.mem.readW (E + BitVec.ofNat 64 (224 + 8 * n)) 64 =
        s.mem.readW (E + BitVec.ofNat 64 (224 + 8 * n)) 64 := by
      apply hu.frame.readW (Region.contains_self _ _) _ (by decide)
      simp only [List.mem_singleton]
      rintro r rfl
      exact Offset.disjoint _ (by omega) (by omega) (by decide)
    rw [same] at mt
    refine ⟨hu.step.trans kt, ?_, fun j hj => ?_⟩
    · rw [mt]
      exact hu.frame.writeW (List.mem_singleton_self _) _
        (Offset.contains _ (by omega) (by omega) (by decide))
    · rw [mt]
      by_cases hjn : j = n
      · subst j; exact Mem.readW_writeW_self64 _ _ _
      · rw [Mem.readW_writeW_sep (a := E + BitVec.ofNat 64 (64 + 8 * j))
          (b := E + BitVec.ofNat 64 (64 + 8 * n)) ?_ (by decide)]
        · exact hu.words j (by omega)
        · exact Offset.sep _ (by omega) (by omega) (by omega)

theorem prefix_ok {s : State} {E : Addr} (he : s.sp = E)
    (hw : (⟨E, 256⟩ : Region) ∈ s.wr) :
    WP isa (.block copyPrefix) s fun t => PrefixStep s t ∧
      Frame [⟨E + BitVec.ofNat 64 64, 32⟩] s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem (E + 64) 32 = Spec.Ed25519.bytesAt s.mem (E + 224) 32 := by
  refine WP.mono (copyPrefix_ok he hw 4 (by decide)) fun t ht => ⟨ht.step, ht.frame, ?_⟩
  rw [Proof.Ed25519.bytesAt_encodeLE t.mem, Proof.Ed25519.bytesAt_encodeLE s.mem]
  apply congrArg (Spec.Ed25519.encodeLE 32)
  change Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt t.mem (off E 64) 32) =
    Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (off E 224) 32)
  rw [decodeLE_words, decodeLE_words]
  simp only [fe, word]
  rw [ht.words 0 (by decide), ht.words 1 (by decide), ht.words 2 (by decide), ht.words 3 (by decide)]

end VG.Proof.Ed25519.AArch64.SignCached
