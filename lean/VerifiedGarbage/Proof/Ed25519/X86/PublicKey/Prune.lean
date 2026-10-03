import VerifiedGarbage.Proof.Ed25519.Bytes
import VerifiedGarbage.Impl.Ed25519.X86.PublicKey
import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-! Merged from `Proof.Ed25519.X86.PublicKey.PruneArithmetic`. -/
section
namespace VG.Proof.Ed25519.X86.PublicKey
open VG

theorem and_sub8 (x k : Nat) (hk : 3 ≤ k) : x &&& (2 ^ k - 8) = 8 * (x / 8 % 2 ^ (k - 3)) := by
  have e : 2 ^ k - 8 = 2 ^ 3 * (2 ^ (k - 3) - 1) := by
    rw [Nat.mul_sub, Nat.mul_one, ← Nat.pow_add, Nat.add_sub_cancel' hk]
  rw [e, show (8 : Nat) = 2 ^ 3 from rfl]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_two_pow_mul, Nat.testBit_two_pow_mul, Nat.testBit_mod_two_pow,
    Nat.testBit_two_pow_sub_one, Nat.testBit_div_two_pow]
  by_cases h : 3 ≤ i
  · simp only [h, decide_true, Bool.true_and, Nat.sub_add_cancel h]
    cases x.testBit i <;> simp
  · simp [h]

theorem or_two_pow {y k : Nat} (h : y < 2 ^ k) : y ||| 2 ^ k = 2 ^ k + y := by
  have := Nat.two_pow_add_eq_or_of_lt h 1
  rw [Nat.mul_one] at this
  rw [this, Nat.or_comm]

theorem prune_words (d0 d1 d2 d3 d4 d5 d6 d7 : BitVec 32) :
    ((d0.toNat + 2 ^ 32 * d1.toNat + 2 ^ 64 * d2.toNat + 2 ^ 96 * d3.toNat + 2 ^ 128 * d4.toNat + 2 ^ 160 * d5.toNat + 2 ^ 192 * d6.toNat + 2 ^ 224 * d7.toNat) &&& (2 ^ 254 - 8)) ||| 2 ^ 254 =
      (d0 &&& BitVec.ofNat 32 (2 ^ 32 - 8)).toNat + 2 ^ 32 * d1.toNat + 2 ^ 64 * d2.toNat + 2 ^ 96 * d3.toNat + 2 ^ 128 * d4.toNat + 2 ^ 160 * d5.toNat + 2 ^ 192 * d6.toNat + 2 ^ 224 * ((d7 &&& BitVec.ofNat 32 (2 ^ 30 - 1)) ||| BitVec.ofNat 32 (2 ^ 30)).toNat := by
  have h0 := d0.isLt; have h1 := d1.isLt; have h2 := d2.isLt; have h3 := d3.isLt; have h4 := d4.isLt; have h5 := d5.isLt; have h6 := d6.isLt; have h7 := d7.isLt
  have c₁ : (2 ^ 32 - 8) % 2 ^ 32 = 2 ^ 32 - 8 := by decide
  have c₂ : (2 ^ 30 - 1) % 2 ^ 32 = 2 ^ 30 - 1 := by decide
  have c₃ : (2 ^ 30) % 2 ^ 32 = 2 ^ 30 := by decide
  rw [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, c₁, c₂, c₃, and_sub8 _ 32 (by omega), and_sub8 _ 254 (by omega),
    Nat.and_two_pow_sub_one_eq_mod, or_two_pow (Nat.mod_lt _ (by omega)), or_two_pow (by omega)]
  simp only [show (2 : Nat) ^ (254 - 3) = 2 ^ 251 from rfl, show (2 : Nat) ^ (32 - 3) = 2 ^ 29 from rfl]
  omega

end VG.Proof.Ed25519.X86.PublicKey
end

namespace VG.Proof.Ed25519.X86.PublicKey
open VG VG.X86 VG.Impl.Ed25519.X86.PublicKey

def pruneValue (k : Nat) (x : BitVec 32) : BitVec 32 :=
  if k = 0 then x &&& 0xfffffff8
  else if k = 7 then (x &&& 0x3fffffff) ||| 0x40000000 else x

structure Step (s t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  regs : ∀ r, r ≠ .eax → t.gpr r = s.gpr r

theorem Step.refl (s : State) : Step s s := ⟨rfl, rfl, fun _ _ => rfl⟩
theorem Step.trans {s t u : State} (a : Step s t) (b : Step t u) : Step s u :=
  ⟨b.rd.trans a.rd, b.wr.trans a.wr, fun r h => (b.regs r h).trans (a.regs r h)⟩
theorem Step.esp {s t : State} (h : Step s t) : t.gpr .esp = s.gpr .esp := h.regs _ (by decide)

/-- One pruning word; only EAX, flags and the destination word change. -/
theorem pruneWord_ok {s : State} {E : BitVec 32} {k : Nat} (he : s.gpr .esp = E)
    (hr : InRegions (s.rd ++ s.wr) (addr E (192 + 4 * k)) 4)
    (hw : InRegions s.wr (addr E (32 + 4 * k)) 4) :
    WP isa (.block (pruneWord k)) s fun t => Step s t ∧
      t.mem = s.mem.writeW (addr E (32 + 4 * k))
        (pruneValue k (s.mem.readW (addr E (192 + 4 * k)) 32)) := by
  by_cases h0 : k = 0
  · subst k
    apply WP.of_runBlock
    simp only [pruneWord, pruneValue, at_, ↓reduceIte, List.cons_append, List.nil_append,
      runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, State.load32,
      State.store32, ea_mk, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg,
      RegUpd.wr_setReg, RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags,
      RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, reduceCtorEq,
      he, hr, hw, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
    exact ⟨⟨rfl, rfl, fun r h => by simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, h, ite_false]⟩, True.intro⟩
  · by_cases h7 : k = 7
    · subst k
      apply WP.of_runBlock
      simp only [pruneWord, pruneValue, at_, ↓reduceIte, List.cons_append, List.nil_append,
        runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, State.load32,
        State.store32, ea_mk, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg,
        RegUpd.wr_setReg, RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags,
        RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, reduceCtorEq,
        he, hr, hw, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
      exact ⟨⟨rfl, rfl, fun r h => by simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, h, ite_false]⟩, True.intro⟩
    · simp only [pruneWord, h0, h7, ↓reduceIte, List.cons_append, List.nil_append, at_]
      refine Wp.wp_ldm he hr fun u hu => ?_
      refine Wp.wp_stm (hu.other _ (by decide) |>.trans he) (hu.wr ▸ hw) fun t ht => WP.block_nil ?_
      refine ⟨⟨ht.rd.trans hu.rd, ht.wr.trans hu.wr, fun r h => by rw [ht.gpr]; exact hu.other r h⟩, ?_⟩
      rw [ht.mem, hu.mem, hu.gpr, pruneValue, ite_eq_right h0, ite_eq_right h7]

/-- The frame bounds supply readable and writable words. -/
theorem frame_word {s : State} {E : BitVec 32} (hf : E.toNat + 256 ≤ 2 ^ 32)
    (hw : (⟨E.setWidth 64, 256⟩ : Region) ∈ s.wr) {d : Nat} (hd : d + 4 ≤ 256) :
    InRegions s.wr (addr E d) 4 := by
  refine ⟨_, hw, ?_⟩
  rw [addr_eq (by omega_using [hf, hd])]
  exact Offset.contains_base _ (by omega_using [hd]) (by omega_using [hd])

structure PruneInv (E : BitVec 32) (s : State) (n : Nat) (t : State) : Prop where
  step : Step s t
  frame : Frame [⟨E.setWidth 64 + BitVec.ofNat 64 32, 32⟩] s.mem t.mem
  words : ∀ j < n, t.mem.readW (addr E (32 + 4 * j)) 32 =
    pruneValue j (s.mem.readW (addr E (192 + 4 * j)) 32)

theorem prunePrefix_ok {s : State} {E : BitVec 32} (he : s.gpr .esp = E)
    (hf : E.toNat + 256 ≤ 2 ^ 32) (hw : (⟨E.setWidth 64, 256⟩ : Region) ∈ s.wr) :
    ∀ n ≤ 8, WP isa (.block ((List.range n).flatMap pruneWord)) s (PruneInv E s n)
  | 0, _ => WP.block_nil ⟨Step.refl s, Frame.refl _ _, fun _ h => by omega_using [h]⟩
  | n + 1, hn => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (prunePrefix_ok he hf hw n (by omega_using [hn])) fun u hu => ?_
    have ur : InRegions (u.rd ++ u.wr) (addr E (192 + 4 * n)) 4 := by
      obtain ⟨r, hr, hc⟩ := frame_word hf (hu.step.wr ▸ hw) (d := 192 + 4 * n) (by omega_using [hn])
      exact ⟨r, List.mem_append_right _ hr, hc⟩
    have uw := frame_word hf (hu.step.wr ▸ hw) (d := 32 + 4 * n) (by omega_using [hn])
    refine WP.mono (pruneWord_ok (hu.step.esp.trans he) ur uw) fun t ⟨kt, mt⟩ => ?_
    have a192 : addr E (192 + 4 * n) = E.setWidth 64 + BitVec.ofNat 64 (192 + 4 * n) :=
      addr_eq (by omega_using [hf, hn])
    have a32 : addr E (32 + 4 * n) = E.setWidth 64 + BitVec.ofNat 64 (32 + 4 * n) :=
      addr_eq (by omega_using [hf, hn])
    have same : u.mem.readW (addr E (192 + 4 * n)) 32 = s.mem.readW (addr E (192 + 4 * n)) 32 := by
      rw [a192]
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
      · rw [Mem.readW_writeW_sep (a := addr E (32 + 4 * j)) (b := addr E (32 + 4 * n)) ?_ (by decide)]
        · exact hu.words j (by omega_using [hj, hjn])
        · rw [a32, addr_eq (by omega_using [hf, hj, hn])]
          exact Offset.sep _ (by omega_using [hj, hjn]) (by omega_using [hj, hn]) (by omega_using [hn])

theorem decode_words (m : Mem) (p : Addr) :
    Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m p 32) =
      (m.readW p 32).toNat + 2 ^ 32 * (m.readW (p + 4) 32).toNat +
      2 ^ 64 * (m.readW (p + 8) 32).toNat + 2 ^ 96 * (m.readW (p + 12) 32).toNat +
      2 ^ 128 * (m.readW (p + 16) 32).toNat + 2 ^ 160 * (m.readW (p + 20) 32).toNat +
      2 ^ 192 * (m.readW (p + 24) 32).toNat + 2 ^ 224 * (m.readW (p + 28) 32).toNat := by
  rw [Proof.Ed25519.decodeLE_eq]
  exact Proof.X25519.leNum_bytesAt_words32 m p

/-- Prune the first half of a SHA-512 digest into the separate scalar buffer. -/
theorem prune_ok {s : State} {E : BitVec 32} (he : s.gpr .esp = E)
    (hf : E.toNat + 256 ≤ 2 ^ 32) (hw : (⟨E.setWidth 64, 256⟩ : Region) ∈ s.wr)
    {digest : List Byte} (hh : Spec.Sha512.bytesAt s.mem (E.setWidth 64 + 192) 64 = digest) :
    WP isa (.block prune) s fun t => Step s t ∧
      Frame [⟨E.setWidth 64 + 32, 32⟩] s.mem t.mem ∧
      Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt t.mem (E.setWidth 64 + 32) 32) =
        Spec.Ed25519.prune digest := by
  refine WP.mono (prunePrefix_ok he hf hw 8 (by decide)) fun t ht => ⟨ht.step, ht.frame, ?_⟩
  have words : ∀ j < 8, t.mem.readW (E.setWidth 64 + BitVec.ofNat 64 (32 + 4 * j)) 32 =
      pruneValue j (s.mem.readW (E.setWidth 64 + BitVec.ofNat 64 (192 + 4 * j)) 32) := by
    intro j hj
    have h := ht.words j hj
    rw [addr_eq (by omega_using [hf, hj]), addr_eq (by omega_using [hf, hj])] at h
    exact h
  have take : (Spec.Sha512.bytesAt s.mem (E.setWidth 64 + 192) 64).take 32 =
      Spec.Ed25519.bytesAt s.mem (E.setWidth 64 + 192) 32 := by
    simp [Spec.Sha512.bytesAt, Spec.Ed25519.bytesAt, ← List.map_take, List.take_range]
  rw [Spec.Ed25519.prune, ← hh, take, decode_words, decode_words]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have w0 := words 0 (by decide)
  have w1 := words 1 (by decide)
  have w2 := words 2 (by decide)
  have w3 := words 3 (by decide)
  have w4 := words 4 (by decide)
  have w5 := words 5 (by decide)
  have w6 := words 6 (by decide)
  have w7 := words 7 (by decide)
  simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceEqDiff, pruneValue, ↓reduceIte] at w0 w1 w2 w3 w4 w5 w6 w7
  change t.mem.readW (E.setWidth 64 + (32 : BitVec 64)) 32 = _ at w0
  rw [w0, w1, w2, w3, w4, w5, w6, w7]
  exact (prune_words _ _ _ _ _ _ _ _).symm

end VG.Proof.Ed25519.X86.PublicKey
