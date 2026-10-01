import VerifiedGarbage.Proof.Ed25519.X86.SignCached.Args
import VerifiedGarbage.Proof.Ed25519.X86.PublicKey.Prune
import VerifiedGarbage.Proof.Ed25519.Signing

namespace VG.Proof.Ed25519.X86.SignCached
open VG VG.X86 VG.Impl.Ed25519.X86.PublicKey VG.Impl.Ed25519.X86.SignCached
open VG.Proof.Ed25519.X86.PublicKey (Step frame_word decode_words)

theorem copyWord_ok {s : State} {E : BitVec 32} {k : Nat} (he : s.gpr .esp = E)
    (hr : InRegions (s.rd ++ s.wr) (addr E (224 + 4 * k)) 4)
    (hw : InRegions s.wr (addr E (64 + 4 * k)) 4) :
    WP isa (.block (copyWord 224 64 k)) s fun t => Step s t ∧
      t.mem = s.mem.writeW (addr E (64 + 4 * k)) (s.mem.readW (addr E (224 + 4 * k)) 32) := by
  simp only [copyWord, at_]
  refine Wp.wp_ldm he hr fun u hu => ?_
  refine Wp.wp_stm (hu.other _ (by decide) |>.trans he) (hu.wr ▸ hw) fun t ht => WP.block_nil ?_
  refine ⟨⟨ht.rd.trans hu.rd, ht.wr.trans hu.wr, fun r h => by rw [ht.gpr]; exact hu.other r h⟩, ?_⟩
  rw [ht.mem, hu.mem, hu.gpr]

structure PrefixInv (E : BitVec 32) (s : State) (n : Nat) (t : State) : Prop where
  step : Step s t
  frame : Frame [⟨E.setWidth 64 + BitVec.ofNat 64 64, 32⟩] s.mem t.mem
  words : ∀ j < n, t.mem.readW (addr E (64 + 4 * j)) 32 =
    s.mem.readW (addr E (224 + 4 * j)) 32

theorem copyPrefix_ok {s : State} {E : BitVec 32} (he : s.gpr .esp = E)
    (hf : E.toNat + 256 ≤ 2 ^ 32) (hw : (⟨E.setWidth 64, 256⟩ : Region) ∈ s.wr) :
    ∀ n ≤ 8, WP isa (.block ((List.range n).flatMap (copyWord 224 64))) s (PrefixInv E s n)
  | 0, _ => WP.block_nil ⟨Step.refl s, Frame.refl _ _, fun _ h => by omega_using [h]⟩
  | n + 1, hn => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (copyPrefix_ok he hf hw n (by omega_using [hn])) fun u hu => ?_
    have ur : InRegions (u.rd ++ u.wr) (addr E (224 + 4 * n)) 4 := by
      obtain ⟨r, hr, hc⟩ := frame_word hf (hu.step.wr ▸ hw) (d := 224 + 4 * n) (by omega_using [hn])
      exact ⟨r, List.mem_append_right _ hr, hc⟩
    have uw := frame_word hf (hu.step.wr ▸ hw) (d := 64 + 4 * n) (by omega_using [hn])
    refine WP.mono (copyWord_ok (hu.step.esp.trans he) ur uw) fun t ⟨kt, mt⟩ => ?_
    have a224 : addr E (224 + 4 * n) = E.setWidth 64 + BitVec.ofNat 64 (224 + 4 * n) :=
      addr_eq (by omega_using [hf, hn])
    have a32 : addr E (64 + 4 * n) = E.setWidth 64 + BitVec.ofNat 64 (64 + 4 * n) :=
      addr_eq (by omega_using [hf, hn])
    have same : u.mem.readW (addr E (224 + 4 * n)) 32 = s.mem.readW (addr E (224 + 4 * n)) 32 := by
      rw [a224]
      apply hu.frame.readW (Region.contains_self _ _) _ (by decide)
      simp only [List.mem_singleton]
      rintro r rfl
      exact Offset.disjoint _ (by omega_using [hn]) (by omega_using [hn]) (by omega_using [hn])
    rw [same] at mt
    refine ⟨hu.step.trans kt, ?_, fun j hj => ?_⟩
    · rw [mt, a32]
      exact hu.frame.writeW (List.mem_singleton_self _) _
        (Offset.contains _ (by omega_using []) (by omega_using [hn]) (by decide))
    · rw [mt]
      by_cases hjn : j = n
      · subst j; exact Mem.readW_writeW_self32 _ _ _
      · rw [Mem.readW_writeW_sep (a := addr E (64 + 4 * j)) (b := addr E (64 + 4 * n)) ?_ (by decide)]
        · exact hu.words j (by omega_using [hj, hjn])
        · rw [a32, addr_eq (by omega_using [hf, hj, hn])]
          exact Offset.sep _ (by omega_using [hj, hjn]) (by omega_using [hj, hn]) (by omega_using [hn])

theorem prefix_ok {s : State} {E : BitVec 32} (he : s.gpr .esp = E)
    (hf : E.toNat + 256 ≤ 2 ^ 32) (hw : (⟨E.setWidth 64, 256⟩ : Region) ∈ s.wr) :
    WP isa (.block copyPrefix) s fun t => Step s t ∧
      Frame [⟨E.setWidth 64 + 64, 32⟩] s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem (E.setWidth 64 + 64) 32 =
        Spec.Ed25519.bytesAt s.mem (E.setWidth 64 + 224) 32 := by
  refine WP.mono (copyPrefix_ok he hf hw 8 (by decide)) fun t ht => ⟨ht.step, ht.frame, ?_⟩
  have words : ∀ j < 8, t.mem.readW (E.setWidth 64 + BitVec.ofNat 64 (64 + 4 * j)) 32 =
      s.mem.readW (E.setWidth 64 + BitVec.ofNat 64 (224 + 4 * j)) 32 := by
    intro j hj
    have h := ht.words j hj
    rw [addr_eq (by omega_using [hf, hj]), addr_eq (by omega_using [hf, hj])] at h
    exact h
  rw [Proof.Ed25519.bytesAt_encodeLE t.mem, Proof.Ed25519.bytesAt_encodeLE s.mem]
  apply congrArg (Spec.Ed25519.encodeLE 32)
  rw [decode_words, decode_words]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have w0 := words 0 (by decide)
  have w1 := words 1 (by decide)
  have w2 := words 2 (by decide)
  have w3 := words 3 (by decide)
  have w4 := words 4 (by decide)
  have w5 := words 5 (by decide)
  have w6 := words 6 (by decide)
  have w7 := words 7 (by decide)
  simp only [Nat.reduceMul, Nat.reduceAdd] at w0 w1 w2 w3 w4 w5 w6 w7
  change t.mem.readW (E.setWidth 64 + (64 : BitVec 64)) 32 = s.mem.readW (E.setWidth 64 + (224 : BitVec 64)) 32 at w0
  rw [w0, w1, w2, w3, w4, w5, w6, w7]

end VG.Proof.Ed25519.X86.SignCached
