import VerifiedGarbage.Proof.Poly1305.X86.Reduce
import VerifiedGarbage.Proof.Poly1305.Spec
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.X86.Inline
import VerifiedGarbage.Proof.Framework.Offset

section

/-!
# Poly1305 on x86 (32-bit): the state in memory, as the specification sees it

Untrusted: everything here is checked by Lean. Little-endian numbers of
32-bit words in memory, the key and its clamped `r`, and the tag.
-/

open VG.PowLit

namespace VG.Proof.Poly1305.X86

open VG VG.X86 VG.Impl.Poly1305.X86
open VG.Spec.Poly1305 (P clamp leNum leBytes bytesAt accumulate Repr)

/-! ## Numbers as words -/

theorem leNum_bytesAt_4 (m : Mem) (p : Addr) : leNum (bytesAt m p 4) = (m.readW p 32).toNat := by
  rw [Poly1305.leNum_bytesAt_read]; simp [Mem.readW]

theorem leNum_bytesAt_4add (m : Mem) (p : Addr) (n : Nat) :
    leNum (bytesAt m p (4 + n)) =
      (m.readW p 32).toNat + 2 ^ 32 * leNum (bytesAt m (p + BitVec.ofNat 64 4) n) := by
  rw [Poly1305.bytesAt_add, Poly1305.leNum_append, Poly1305.length_bytesAt, leNum_bytesAt_4]

/-- The word at `p + 4 k`, as a number. -/
abbrev w32 (m : Mem) (p : Addr) (k : Nat) : Nat := (m.readW (p + BitVec.ofNat 64 (4 * k)) 32).toNat

theorem add_ofNat_add (p : Addr) (d e : Nat) :
    p + BitVec.ofNat 64 d + BitVec.ofNat 64 e = p + BitVec.ofNat 64 (d + e) := Offset.add_add p d e

/-- Four little-endian words. -/
theorem leNum_bytesAt_16 (m : Mem) (p : Addr) :
    leNum (bytesAt m p 16) = w32 m p 0 + 2 ^ 32 * w32 m p 1 + 2 ^ 64 * w32 m p 2 + 2 ^ 96 * w32 m p 3 := by
  rw [show 16 = 4 + (4 + (4 + (4 + 0))) from rfl, leNum_bytesAt_4add, leNum_bytesAt_4add,
    leNum_bytesAt_4add, leNum_bytesAt_4add]
  simp only [w32, add_ofNat_add, show bytesAt m _ 0 = [] from rfl, Spec.Poly1305.leNum, BitVec.add_zero,
    Nat.mul_zero, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd]
  omega

/-- Six little-endian words. -/
theorem leNum_bytesAt_24 (m : Mem) (p : Addr) :
    leNum (bytesAt m p 24) = w32 m p 0 + 2 ^ 32 * w32 m p 1 + 2 ^ 64 * w32 m p 2 + 2 ^ 96 * w32 m p 3 +
      2 ^ 128 * w32 m p 4 + 2 ^ 160 * w32 m p 5 := by
  rw [show 24 = 4 + (4 + (4 + (4 + (4 + (4 + 0))))) from rfl, leNum_bytesAt_4add, leNum_bytesAt_4add,
    leNum_bytesAt_4add, leNum_bytesAt_4add, leNum_bytesAt_4add, leNum_bytesAt_4add]
  simp only [w32, add_ofNat_add, show bytesAt m _ 0 = [] from rfl, Spec.Poly1305.leNum, BitVec.add_zero,
    Nat.mul_zero, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd]
  omega

/-- A word of the state as the specification addresses it. -/
theorem w32_eq {m : Mem} {st : BitVec 32} (hfit : st.toNat + 128 ≤ 2 ^ 32) {k : Nat} (hk : k < 32) :
    w32 m (st.setWidth 64) k = wv m st (4 * k) := by
  rw [wv, wd, addr_eq (by omega)]

theorem w32_off {m : Mem} {st : BitVec 32} (hfit : st.toNat + 128 ≤ 2 ^ 32) {d k : Nat}
    (hk : d + 4 * k + 4 ≤ 128) : w32 m (st.setWidth 64 + BitVec.ofNat 64 d) k = wv m st (d + 4 * k) := by
  simp only [w32, wv, wd]
  rw [addr_eq (by omega), add_ofNat_add]

/-- The accumulator in the state's words. -/
theorem leNum_acc {m : Mem} {st : BitVec 32} (hfit : st.toNat + 128 ≤ 2 ^ 32) {f : Nat → Nat}
    (hw : Words m st f) :
    leNum (bytesAt m (st.setWidth 64) 24) = hw5 f + 2 ^ 160 * f 5 := by
  rw [leNum_bytesAt_24, w32_eq hfit (by omega), w32_eq hfit (by omega), w32_eq hfit (by omega),
    w32_eq hfit (by omega), w32_eq hfit (by omega), w32_eq hfit (by omega), hw 0 (by omega),
    hw 1 (by omega), hw 2 (by omega), hw 3 (by omega), hw 4 (by omega), hw 5 (by omega)]
  rfl

/-- The accumulator of a state that represents a message, below `p`, as words. -/
theorem acc_words {m : Mem} {st : BitVec 32} (hfit : st.toNat + 128 ≤ 2 ^ 32) {f : Nat → Nat}
    (hw : Words m st f) (hlt : leNum (bytesAt m (st.setWidth 64) 24) < P) :
    f 5 = 0 ∧ f 4 ≤ 3 ∧ leNum (bytesAt m (st.setWidth 64) 24) = hw5 f := by
  rw [leNum_acc hfit hw] at hlt ⊢
  have h0 := hw.lt (k := 0) (by omega); have h1 := hw.lt (k := 1) (by omega)
  have h2 := hw.lt (k := 2) (by omega); have h3 := hw.lt (k := 3) (by omega)
  simp only [hw5, val5, P] at hlt ⊢
  omega

/-! ## Bytes as words -/

/-- Bytes of memory are the same where the words are. -/
theorem bytesAt_congr_words2 {m m' : Mem} {p q : Addr} {n : Nat}
    (h : ∀ k < n, m'.readW (p + BitVec.ofNat 64 (4 * k)) 32 = m.readW (q + BitVec.ofNat 64 (4 * k)) 32) :
    bytesAt m' p (4 * n) = bytesAt m q (4 * n) := by
  simp only [bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  have e : ∀ x : Addr, x + BitVec.ofNat 64 i = (x + BitVec.ofNat 64 (4 * (i / 4))) + BitVec.ofNat 64 (i % 4) :=
    fun x => by rw [add_ofNat_add]; congr 2; omega
  rw [e p, e q, Mem.readW_byte m' _ (Nat.mod_lt _ (by omega)), Mem.readW_byte m _ (Nat.mod_lt _ (by omega)),
    h _ (by omega)]

theorem bytesAt_congr_words {m m' : Mem} {p : Addr} {n : Nat}
    (h : ∀ k < n, m'.readW (p + BitVec.ofNat 64 (4 * k)) 32 = m.readW (p + BitVec.ofNat 64 (4 * k)) 32) :
    bytesAt m' p (4 * n) = bytesAt m p (4 * n) := bytesAt_congr_words2 h

/-! ## The key -/

theorem land_split32 {a b c d : Nat} (ha : a < 2 ^ 32) (hc : c < 2 ^ 32) :
    (a + 2 ^ 32 * b) &&& (c + 2 ^ 32 * d) = (a &&& c) + 2 ^ 32 * (b &&& d) := by
  apply Nat.eq_of_testBit_eq
  intro i
  have hac : (a &&& c) < 2 ^ 32 := Nat.lt_of_le_of_lt Nat.and_le_left ha
  rw [Nat.testBit_and]
  rw [Nat.add_comm a, Nat.add_comm c, Nat.add_comm (a &&& c)]
  rw [Nat.testBit_two_pow_mul_add _ ha, Nat.testBit_two_pow_mul_add _ hc,
    Nat.testBit_two_pow_mul_add _ hac]
  split <;> simp [Nat.testBit_and]

/-- The clamped `r` of a key of four little-endian words. -/
theorem clamp_words4 {k0 k1 k2 k3 : Nat} (h0 : k0 < 2 ^ 32) (h1 : k1 < 2 ^ 32) (h2 : k2 < 2 ^ 32) :
    clamp (k0 + 2 ^ 32 * k1 + 2 ^ 64 * k2 + 2 ^ 96 * k3) =
      (k0 &&& 0x0fffffff) + 2 ^ 32 * (k1 &&& 0x0ffffffc) + 2 ^ 64 * (k2 &&& 0x0ffffffc) +
        2 ^ 96 * (k3 &&& 0x0ffffffc) := by
  have e : ∀ x y z w : Nat, x + 2 ^ 32 * y + 2 ^ 64 * z + 2 ^ 96 * w =
      x + 2 ^ 32 * (y + 2 ^ 32 * (z + 2 ^ 32 * w)) := fun x y z w => by omega
  rw [clamp, e, show (0x0ffffffc0ffffffc0ffffffc0fffffff : Nat) =
    0x0fffffff + 2 ^ 32 * (0x0ffffffc + 2 ^ 32 * (0x0ffffffc + 2 ^ 32 * 0x0ffffffc)) from rfl,
    land_split32 h0 (by decide), land_split32 h1 (by decide), land_split32 h2 (by decide), e]

theorem mask0_lt (k : Nat) : k &&& 0x0fffffff < 2 ^ 28 :=
  Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

theorem mask1_lt (k : Nat) : k &&& 0x0ffffffc < 2 ^ 28 :=
  Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

theorem mask1_mod (k : Nat) : (k &&& 0x0ffffffc) % 4 = 0 := by
  rw [show (4 : Nat) = 2 ^ 2 from rfl, ← Nat.and_two_pow_sub_one_eq_mod, Nat.and_assoc,
    show (0x0ffffffc : Nat) &&& 2 ^ 2 - 1 = 0 by decide, Nat.and_zero]

/-! ## The tag -/

theorem bytesAt_leBytes_4 (m : Mem) (p : Addr) : bytesAt m p 4 = leBytes 4 (m.readW p 32).toNat := by
  rw [Poly1305.bytesAt_leBytes]; simp [Mem.readW]

/-- Four little-endian words in memory are the 16 bytes of `x`, if they are its
low 128 bits. -/
theorem bytesAt_leBytes_16w (m : Mem) (p : Addr) (x : Nat) (h : ∀ k < 4, w32 m p k = x / 2 ^ (32 * k) % 2 ^ 32) :
    bytesAt m p 16 = leBytes 16 x := by
  have e : ∀ k < 4, bytesAt m (p + BitVec.ofNat 64 (4 * k)) 4 = leBytes 4 (x / 2 ^ (32 * k)) := by
    intro k hk
    rw [bytesAt_leBytes_4, show (m.readW (p + BitVec.ofNat 64 (4 * k)) 32).toNat = w32 m p k from rfl,
      h k hk, show (2 : Nat) ^ 32 = 256 ^ 4 from rfl, Poly1305.leBytes_mod]
  rw [show 16 = 4 + (4 + (4 + 4)) from rfl, Poly1305.bytesAt_add, Poly1305.bytesAt_add,
    Poly1305.bytesAt_add, Poly1305.leBytes_add, Poly1305.leBytes_add, Poly1305.leBytes_add,
    add_ofNat_add, add_ofNat_add]
  have e0 := e 0 (by omega); have e1 := e 1 (by omega); have e2 := e 2 (by omega)
  have e3 := e 3 (by omega)
  simp only [Nat.mul_zero, BitVec.add_zero, Nat.pow_zero, Nat.div_one] at e0
  rw [e0, e1, e2, e3, Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, ← Nat.pow_add, ← Nat.pow_add]

end VG.Proof.Poly1305.X86

end

section

/-!
# Poly1305 on x86 (32-bit): saving registers and clamping the key

Untrusted: everything here is checked by Lean.
-/

open VG.PowLit

namespace VG.Proof.Poly1305.X86

open VG VG.X86 VG.Impl.Poly1305.X86

/-- The state's words on entry. -/
def words (m : Mem) (st : BitVec 32) : Nat → Nat := fun k => wv m st (4 * k)

theorem words_ok (m : Mem) (st : BitVec 32) : Words m st (words m st) := fun _ _ => rfl

theorem save_eq : save = [.mov .eax (.mem (at_ .esp 4)), .store (at_ .eax 116) .ebx,
    .store (at_ .eax 120) .esi, .store (at_ .eax 124) .edi, .store (at_ .eax 20) .ebp,
    .mov .edi (.reg .eax)] := rfl

/-- The callee-saved registers of `s`, saved in the words `f`. -/
def SavedIn (s : State) (f : Nat → Nat) : Prop :=
  f 29 = v s .ebx ∧ f 30 = v s .esi ∧ f 31 = v s .edi ∧ f 5 = v s .ebp

/-- The state at `[esp + 4]` into `edi`, saving `ebx, esi, edi, ebp` in it. -/
theorem save_ok {s : State} {st : BitVec 32} (hst : s.mem.readW (addr (s.gpr .esp) 4) 32 = st)
    (harg : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 4) 4) (hfit : st.toNat + 128 ≤ 2 ^ 32)
    (hw : sR st ∈ s.wr) :
    WP isa (.block save) s fun s' => ∃ f, After st s s' f [.eax, .edi] ∧ s'.gpr .edi = st ∧
      (∀ k, k < 29 → k ≠ 5 → f k = words s.mem st k) ∧ SavedIn s f := by
  have hc : ∀ d, d + 4 ≤ 128 → InRegions s.wr (addr st d) 4 := fun d hd =>
    ⟨_, hw, sR_contains hfit hd (by omega)⟩
  rw [save_eq]
  refine wp_movm (a := addr (s.gpr .esp) 4) (ea_at _ _ _) harg fun s₁ u₁ _ => ?_
  have e₁ : s₁.gpr .eax = st := by rw [u₁.gpr, hst]
  refine wp_store (a := addr st (4 * 29)) (by rw [ea_at, e₁]) (by rw [u₁.wr]; exact hc _ (by omega))
    fun s₂ u₂ => ?_
  refine wp_store (a := addr st (4 * 30)) (by rw [ea_at, u₂.gpr, e₁])
    (by rw [u₂.wr, u₁.wr]; exact hc _ (by omega)) fun s₃ u₃ => ?_
  refine wp_store (a := addr st (4 * 31)) (by rw [ea_at, u₃.gpr, u₂.gpr, e₁])
    (by rw [u₃.wr, u₂.wr, u₁.wr]; exact hc _ (by omega)) fun s₄ u₄ => ?_
  refine wp_store (a := addr st (4 * 5)) (by rw [ea_at, u₄.gpr, u₃.gpr, u₂.gpr, e₁])
    (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact hc _ (by omega)) fun s₅ u₅ => ?_
  refine wp_mov fun s₆ u₆ _ => WP.block_nil ⟨upd (upd (upd (upd (words s.mem st) 29 (v s .ebx)) 30
    (v s .esi)) 31 (v s .edi)) 5 (v s .ebp), ⟨?_, ?_, fun r hr => ?_, ?_, ?_⟩, ?_, fun k hk hk5 => ?_, ?_⟩
  · rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₄.gpr, u₃.gpr, u₂.gpr, u₁.mem, u₁.other .ebx (by decide),
      u₁.other .esi (by decide), u₁.other .edi (by decide), u₁.other .ebp (by decide)]
    exact ((((words_ok s.mem st).write hfit (j := 29) (by omega) _).write hfit (j := 30) (by omega)
      _).write hfit (j := 31) (by omega) _).write hfit (j := 5) (by omega) _
  · rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
    exact frame_write (frame_write (frame_write (frame_write (Frame.refl _ _) hfit (by omega) _) hfit
      (by omega) _) hfit (by omega) _) hfit (by omega) _
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₆.other r hr.2, u₅.gpr, u₄.gpr, u₃.gpr, u₂.gpr, u₁.other r hr.1]
  · rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · rw [u₆.gpr, u₅.gpr, u₄.gpr, u₃.gpr, u₂.gpr, e₁]
  · simp only [upd]
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_right (by omega)]
  · refine ⟨?_, ?_, ?_, ?_⟩ <;> simp (config := {decide := true}) only [upd, ite_true, ite_false]


theorem and0_toNat (x : BitVec 32) : (x &&& 0x0fffffff).toNat = x.toNat &&& 0x0fffffff := by
  rw [BitVec.toNat_and]; rfl

theorem and1_toNat (x : BitVec 32) : (x &&& 0x0ffffffc).toNat = x.toNat &&& 0x0ffffffc := by
  rw [BitVec.toNat_and]; rfl

/-- `r0` clamped. -/
theorem clamp0_ok {st : BitVec 32} {s : State} (hc : Ctx st s) {f : Nat → Nat} (hw : Words s.mem st f) :
    WP isa (.block clamp0) s fun s' => After st s s' (upd f 18 (f 6 &&& 0x0fffffff)) [.eax] := by
  have hfit := hc.fit
  refine wp_movm (a := addr st (4 * 6)) (by rw [ea_at, hc.edi]) (hc.inRW (by omega) (by omega))
    fun s₁ u₁ _ => wp_andx (readSrc_imm _ _) fun s₂ u₂ => ?_
  have edi₂ : s₂.gpr .edi = st := by rw [u₂.other .edi (by decide), u₁.other .edi (by decide), hc.edi]
  refine wp_store (a := addr st (4 * 18)) (by rw [ea_at, edi₂]; rfl)
    (by rw [u₂.wr, u₁.wr]; exact hc.inW (by omega) (by omega))
    fun s₃ u₃ => WP.block_nil ⟨?_, ?_, fun r hr => ?_, ?_, ?_⟩
  · rw [u₃.mem, u₂.mem, u₁.mem, u₂.gpr, u₁.gpr]
    refine (hw.write hfit (by omega) _).congr fun k _ => ?_
    simp only [upd]
    split
    · rw [and0_toNat, hw.readW (k := 6) (by omega)]
    · rfl
  · rw [u₃.mem, u₂.mem, u₁.mem]; exact frame_write (Frame.refl _ _) hfit (by omega) _
  · simp only [List.mem_singleton] at hr; rw [u₃.gpr, u₂.other r hr, u₁.other r hr]
  · rw [u₃.rd, u₂.rd, u₁.rd]
  · rw [u₃.wr, u₂.wr, u₁.wr]

/-- `rj` clamped and `sj = rj + rj / 4`, for `j = 1, 2, 3`. -/
theorem clampS_ok {st : BitVec 32} {s : State} (hc : Ctx st s) {f : Nat → Nat} (hw : Words s.mem st f)
    {j : Nat} (hj : 1 ≤ j ∧ j ≤ 3) :
    WP isa (.block (clampS j)) s fun s' => After st s s' (upd (upd f (18 + j) (f (6 + j) &&& 0x0ffffffc))
      (21 + j) ((f (6 + j) &&& 0x0ffffffc) + (f (6 + j) &&& 0x0ffffffc) / 4)) [.eax, .ecx] := by
  have hfit := hc.fit
  have hr : f (6 + j) &&& 0x0ffffffc < 2 ^ 28 := mask1_lt _
  refine wp_movm (a := addr st (4 * (6 + j))) (by rw [ea_at, hc.edi]; congr 1; omega)
    (hc.inRW (by omega) (by omega)) fun s₁ u₁ _ => wp_andx (readSrc_imm _ _) fun s₂ u₂ => ?_
  have e₂ : (s₂.gpr .eax).toNat = f (6 + j) &&& 0x0ffffffc := by
    rw [u₂.gpr, u₁.gpr, and1_toNat, hw.readW (k := 6 + j) (by omega)]
  have edi₂ : s₂.gpr .edi = st := by rw [u₂.other _ (by decide), u₁.other _ (by decide), hc.edi]
  refine wp_store (a := addr st (4 * (18 + j))) (by rw [ea_at, edi₂]; simp only [rOff]; congr 1; omega)
    (by rw [u₂.wr, u₁.wr]; exact hc.inW (by omega) (by omega)) fun s₃ u₃ => ?_
  refine wp_mov fun s₄ u₄ _ => wp_shr (by omega) fun s₅ u₅ => wp_addx (readSrc_reg _ _) fun s₆ u₆ _ => ?_
  have e₆ : (s₆.gpr .eax).toNat = (f (6 + j) &&& 0x0ffffffc) + (f (6 + j) &&& 0x0ffffffc) / 4 := by
    rw [u₆.gpr, u₅.other .eax (by decide), u₅.gpr, u₄.gpr, u₄.other .eax (by decide), u₃.gpr,
      BitVec.toNat_add, shr2_toNat, e₂]
    omega
  have edi₆ : s₆.gpr .edi = st := by
    rw [u₆.other .edi (by decide), u₅.other .edi (by decide), u₄.other .edi (by decide), u₃.gpr, edi₂]
  refine wp_store (a := addr st (4 * (21 + j))) (by rw [ea_at, edi₆]; simp only [sOff]; congr 1; omega)
    (by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact hc.inW (by omega) (by omega))
    fun s₇ u₇ => WP.block_nil ⟨?_, ?_, fun r hr => ?_, ?_, ?_⟩
  · rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
    refine ((hw.write hfit (j := 18 + j) (by omega) _).write hfit (j := 21 + j) (by omega) _).congr
      fun k _ => ?_
    rw [e₂, e₆]
  · rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
    exact frame_write (frame_write (Frame.refl _ _) hfit (by omega) _) hfit (by omega) _
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₇.gpr, u₆.other r hr.1, u₅.other r hr.2, u₄.other r hr.2, u₃.gpr, u₂.other r hr.1,
      u₁.other r hr.1]
  · rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]


theorem setup_eq : setup = save ++ (clamp0 ++ (clampS 1 ++ (clampS 2 ++ clampS 3))) := by
  simp only [setup, List.append_assoc]

section
variable (m : Mem) (st : BitVec 32)
/-- The clamped `r0`, and `rj = 4 qj`, of the key in the state's words. -/
def r0v : Nat := words m st 6 &&& 0x0fffffff
def qv (j : Nat) : Nat := (words m st (6 + j) &&& 0x0ffffffc) / 4
end

theorem coef_facts {x : Nat} : x &&& 0x0ffffffc = 4 * ((x &&& 0x0ffffffc) / 4) ∧
    (x &&& 0x0ffffffc) + (x &&& 0x0ffffffc) / 4 = 5 * ((x &&& 0x0ffffffc) / 4) ∧
    (x &&& 0x0ffffffc) / 4 < 2 ^ 26 := by
  have h1 := mask1_mod x; have h2 := mask1_lt x
  refine ⟨by omega, by omega, by omega⟩

/-- Everything each function but `init` does first: the state at `[esp + 4]`
into `edi`, the callee-saved registers saved in it, and the clamped `r`
and `sj` in its words. -/
theorem setup_ok {s₀ : State} {st : BitVec 32} (hst : s₀.mem.readW (addr (s₀.gpr .esp) 4) 32 = st)
    (harg : InRegions (s₀.rd ++ s₀.wr) (addr (s₀.gpr .esp) 4) 4) (hfit : st.toNat + 128 ≤ 2 ^ 32)
    (hw : sR st ∈ s₀.wr) :
    WP isa (.block setup) s₀ fun s => ∃ F, After st s₀ s F [.eax, .ecx, .edi] ∧ Ctx st s ∧
      (∀ k, (k < 18 ∧ k ≠ 5) ∨ (25 ≤ k ∧ k < 29) → F k = words s₀.mem st k) ∧ SavedIn s₀ F ∧
      Coefs F (r0v s₀.mem st) (qv s₀.mem st 1) (qv s₀.mem st 2) (qv s₀.mem st 3) := by
  rw [setup_eq]
  refine WP.block_append (WP.mono (save_ok hst harg hfit hw) fun s₁ ⟨f₁, A₁, e₁, h₁, sv₁⟩ => ?_)
  have c₁ : Ctx st s₁ := ⟨e₁, hfit, A₁.wr ▸ hw⟩
  refine WP.block_append (WP.mono (clamp0_ok c₁ A₁.words) fun s₂ A₂ => ?_)
  have c₂ := A₂.ctx c₁
  refine WP.block_append (WP.mono (clampS_ok c₂ A₂.words (j := 1) (by omega)) fun s₃ A₃ => ?_)
  have c₃ := A₃.ctx c₂
  refine WP.block_append (WP.mono (clampS_ok c₃ A₃.words (j := 2) (by omega)) fun s₄ A₄ => ?_)
  have c₄ := A₄.ctx c₃
  refine WP.mono (clampS_ok c₄ A₄.words (j := 3) (by omega)) fun s₅ A₅ =>
    ⟨_, (A₁.trans (A₂.trans (A₃.trans (A₄.trans A₅)))).mono, A₅.ctx c₄, fun k hk => ?_, ?_, ?_⟩
  · simp only [upd]
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), h₁ k (by omega) (by omega)]
  · obtain ⟨b1, b2, b3, b4⟩ := sv₁
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp (config := {decide := true}) only [upd, ite_false] <;>
      assumption
  · have w6 : f₁ 6 = words s₀.mem st 6 := h₁ 6 (by omega) (by omega)
    have w7 : f₁ 7 = words s₀.mem st 7 := h₁ 7 (by omega) (by omega)
    have w8 : f₁ 8 = words s₀.mem st 8 := h₁ 8 (by omega) (by omega)
    have w9 : f₁ 9 = words s₀.mem st 9 := h₁ 9 (by omega) (by omega)
    obtain ⟨a1, a2, a3⟩ := coef_facts (x := words s₀.mem st 7)
    obtain ⟨b1, b2, b3⟩ := coef_facts (x := words s₀.mem st 8)
    obtain ⟨d1, d2, d3⟩ := coef_facts (x := words s₀.mem st 9)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, mask0_lt _, a3, b3, d3⟩ <;>
      simp (config := {decide := true}) only [upd, ite_true, ite_false, w6, w7, w8, w9, r0v, qv,
        Nat.reduceAdd]
    exacts [a1, b1, d1, a2, b2, d2]

end VG.Proof.Poly1305.X86

end

section

/-!
# Poly1305 on x86 (32-bit): straight-line code runs, whatever the values

Untrusted: everything here is checked by Lean. The lemmas of `Absorb.lean`
and `Reduce.lean` state what the code computes where the numbers are within
their bounds (as they are when the state represents a message). Whatever the
values, the code runs without a fault: it accesses only the state (at `edi`)
and the block (at `esi`), stores only some words of the state and writes only
some registers. `okList` checks this of a block of code, by evaluation, and
`okList_ok` proves it.
-/

namespace VG.Proof.Poly1305.X86

open VG VG.X86 VG.Impl.Poly1305.X86

/-- A memory operand the code may read: a word of the state or of the block. -/
def memOk (blk : Bool) (m : MemOp) : Bool :=
  (m.base == .edi && m.disp + 4 ≤ 128) || (blk && m.base == .esi && m.disp + 4 ≤ 16)

def srcOk (blk : Bool) : Src → Bool
  | .mem m => memOk blk m
  | _ => true

/-- Whether an instruction only reads the state or the block, stores only
the words `S` of the state and writes only the registers `rs`, with `c`
whether CF is defined; and then whether CF is defined afterwards. -/
def okStep (blk : Bool) (rs : List Reg) (S : List Nat) (c : Bool) : Instr → Option Bool
  | .mov d src => if rs.contains d && srcOk blk src then some c else none
  | .store m _ =>
    if m.base == .edi && m.disp % 4 == 0 && S.contains (m.disp / 4) && m.disp + 4 ≤ 128 then some c
    else none
  | .alu op d src =>
    if rs.contains d && srcOk blk src && (!Taint.usesCarry op || c) then some true else none
  | .shift _ d n => if rs.contains d && 1 ≤ n && n ≤ 31 then some true else none
  | .mul _ => if rs.contains .eax && rs.contains .edx then some true else none
  | _ => none

def okList (blk : Bool) (rs : List Reg) (S : List Nat) : Bool → List Instr → Bool
  | _, [] => true
  | c, i :: is => match okStep blk rs S c i with
    | some c' => okList blk rs S c' is
    | none => false

/-- What an instruction or block that `okStep` accepts leaves. -/
structure Safe (st : BitVec 32) (rs : List Reg) (S : List Nat) (s s' : State) : Prop where
  gpr : ∀ r, r ∉ rs → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : Frame [sR st] s.mem s'.mem
  same : ∀ k < 32, k ∉ S → wv s'.mem st (4 * k) = wv s.mem st (4 * k)

theorem Safe.refl (st : BitVec 32) (rs : List Reg) (S : List Nat) (s : State) : Safe st rs S s s :=
  ⟨fun _ _ => rfl, rfl, rfl, Frame.refl _ _, fun _ _ _ => rfl⟩

theorem Safe.trans {st : BitVec 32} {rs : List Reg} {S : List Nat} {s₁ s₂ s₃ : State}
    (h₁ : Safe st rs S s₁ s₂) (h₂ : Safe st rs S s₂ s₃) : Safe st rs S s₁ s₃ :=
  ⟨fun r hr => (h₂.gpr r hr).trans (h₁.gpr r hr), h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr,
    h₁.frame.trans h₂.frame, fun k hk hS => (h₂.same k hk hS).trans (h₁.same k hk hS)⟩

/-- The block's words may be read. -/
def BlkIn (s : State) : Prop := ∀ d, d + 4 ≤ 16 → InRegions (s.rd ++ s.wr) (addr (s.gpr .esi) d) 4

theorem readSrc_ok {st : BitVec 32} {s : State} {blk : Bool} (hc : Ctx st s) (hb : blk = true → BlkIn s)
    {src : Src} (h : srcOk blk src = true) : ∃ x, readSrc s src = some x := by
  cases src with
  | reg r => exact ⟨_, rfl⟩
  | imm w => exact ⟨_, rfl⟩
  | mem m =>
    have ea : s.ea m = addr (s.gpr m.base) m.disp := rfl
    simp only [srcOk, memOk, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    rcases h with ⟨hb', hd⟩ | ⟨⟨hbk, hb'⟩, hd⟩
    · rw [hb', hc.edi] at ea
      exact ⟨_, readSrc_mem ea (hc.inRW hd (by omega))⟩
    · rw [hb'] at ea
      exact ⟨_, readSrc_mem ea (hb hbk _ hd)⟩

/-- An instruction that writes at most the register `d`, and no memory. -/
theorem safe_dst {st : BitVec 32} {rs : List Reg} {S : List Nat} {i : Instr} {d : Reg}
    (hd : Taint.dst i = some d) (hdr : d ∈ rs) {s s' : State} (h : exec i s = some s') :
    Safe st rs S s s' := by
  obtain ⟨hw, hm, hg⟩ := Taint.exec_dst hd h
  refine ⟨fun r hr => hg r fun e => hr (e ▸ hdr), (exec_regions h).1, hw, ?_, fun _ _ _ => ?_⟩
  · rw [hm]; exact Frame.refl _ _
  · rw [hm]

theorem okStep_ok {st : BitVec 32} {blk : Bool} {rs : List Reg} {S : List Nat} {c c' : Bool} {i : Instr}
    (h : okStep blk rs S c i = some c') {s : State} (hc : Ctx st s) (hb : blk = true → BlkIn s)
    (hcf : c = true → s.cf.isSome) :
    ∃ s', exec i s = some s' ∧ Safe st rs S s s' ∧ (c' = true → s'.cf.isSome) := by
  have hfit := hc.fit
  cases i with
  | mov d src =>
    simp only [okStep, Bool.and_eq_true, List.contains_iff_mem] at h
    split at h <;> [skip; cases h]
    rename_i hd
    obtain ⟨x, hx⟩ := readSrc_ok hc hb hd.2
    have he : exec (.mov d src) s = some (s.setReg d x) := by simp [exec, hx]
    refine ⟨_, he, safe_dst rfl hd.1 he, ?_⟩
    simp only [Option.some.injEq] at h
    subst h; exact hcf
  | store m r =>
    simp only [okStep, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem, decide_eq_true_eq] at h
    split at h <;> [skip; cases h]
    rename_i hm
    obtain ⟨⟨⟨hb', h4⟩, hS⟩, hd⟩ := hm
    have ea : s.ea m = addr (s.gpr m.base) m.disp := rfl
    rw [hb', hc.edi, show m.disp = 4 * (m.disp / 4) by omega] at ea
    refine ⟨{ s with mem := s.mem.writeW (addr st (4 * (m.disp / 4))) (s.gpr r) }, ?_, ⟨fun _ _ => rfl,
      rfl, rfl, frame_write (Frame.refl _ _) hfit (by omega) _, fun k hk hkS => ?_⟩, ?_⟩
    · simp only [exec, State.store32, ea, hc.inW (by omega : 4 * (m.disp / 4) + 4 ≤ 128) (by omega),
        ite_true]
    · show wv (s.mem.writeW _ _) st (4 * k) = _
      have : k ≠ m.disp / 4 := fun e => hkS (e ▸ hS)
      rw [wv, wd_write_ne _ _ (by omega) (by omega) (by omega)]
    · simp only [Option.some.injEq] at h
      subst h; exact hcf
  | alu op d src =>
    simp only [okStep, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', List.contains_iff_mem] at h
    split at h <;> [skip; cases h]
    rename_i hd
    obtain ⟨⟨hdr, hsrc⟩, hcarry⟩ := hd
    obtain ⟨x, hx⟩ := readSrc_ok hc hb hsrc
    obtain ⟨o, ho⟩ : ∃ o, Taint.aluOut op (s.gpr d) x s.cf = some o := by
      cases op <;> simp only [Taint.aluOut] <;>
        first
        | exact ⟨_, rfl⟩
        | (obtain ⟨c₀, hc₀⟩ := Option.isSome_iff_exists.mp (hcf (hcarry.resolve_left (by decide)))
           rw [hc₀]; exact ⟨_, rfl⟩)
    obtain ⟨r, co, oo⟩ := o
    have he : exec (.alu op d src) s = some (if Taint.writes op then (arithFlags s r co oo).setReg d r
        else arithFlags s r co oo) := by
      simp only [exec, Taint.execAlu_eq, hx, Option.bind_some, ho, Option.map_some]
    refine ⟨_, he, safe_dst rfl hdr he, fun _ => ?_⟩
    split <;> rfl
  | shift op d n =>
    simp only [okStep, Bool.and_eq_true, List.contains_iff_mem, decide_eq_true_eq] at h
    split at h <;> [skip; cases h]
    rename_i hd
    obtain ⟨⟨hdr, h1⟩, h2⟩ := hd
    have hn : 1 ≤ n ∧ n ≤ 31 := ⟨h1, h2⟩
    obtain ⟨s', he⟩ : ∃ s', exec (.shift op d n) s = some s' := by
      cases op <;> exact ⟨_, by simp only [exec, execShift, hn, and_self, ite_true]; rfl⟩
    refine ⟨s', he, safe_dst rfl hdr he, fun _ => ?_⟩
    cases op <;> simp only [exec, execShift, hn, and_self, ite_true, Option.some.injEq] at he <;>
      subst he <;> rfl
  | mul q =>
    simp only [okStep, Bool.and_eq_true, List.contains_iff_mem] at h
    split at h <;> [skip; cases h]
    rename_i hd
    refine ⟨execMul q s, rfl, ⟨fun r hr => Taint.execMul_gpr q s (fun e => hr (e ▸ hd.1))
      (fun e => hr (e ▸ hd.2)), rfl, rfl, Frame.refl _ _, fun _ _ _ => rfl⟩, fun _ => rfl⟩
  | bswap | movzx8 | store8 | push | pop => simp [okStep] at h

/-- A block that `okList` accepts runs, whatever the values. -/
theorem okList_ok {st : BitVec 32} {blk : Bool} {rs : List Reg} {S : List Nat}
    (hrs : Reg.edi ∉ rs ∧ Reg.esi ∉ rs) :
    ∀ (is : List Instr) (c : Bool) (s : State), okList blk rs S c is = true → Ctx st s →
      (blk = true → BlkIn s) →
      (c = true → s.cf.isSome) → WP isa (.block is) s (Safe st rs S s) := by
  intro is
  induction is with
  | nil => intro _ s _ _ _ _; exact WP.block_nil (Safe.refl _ _ _ _)
  | cons i is ih =>
    intro c s h hc hb hcf
    simp only [okList] at h
    split at h <;> [skip; cases h]
    rename_i c' hi
    obtain ⟨s₁, he, hs, hcf₁⟩ := okStep_ok hi hc hb hcf
    refine WP.cons he (WP.mono (ih c' s₁ h (hc.keep (hs.gpr _ hrs.1) hs.wr) ?_ hcf₁)
      fun s₂ h₂ => hs.trans h₂)
    intro hbk d hd
    rw [hs.rd, hs.wr, hs.gpr _ hrs.2]; exact hb hbk d hd

/-- The words a `Safe` block leaves. -/
theorem Safe.after {st : BitVec 32} {rs : List Reg} {S : List Nat} {s s' : State}
    (h : Safe st rs S s s') : After st s s' (words s'.mem st) rs :=
  ⟨words_ok _ _, h.frame, h.gpr, h.rd, h.wr⟩

/-- A run of `c` satisfies `Q₁`, and `Q₂` where `C` holds (runs are deterministic). -/
theorem WP.cond {c : Prog isa} {s : State} {Q₁ Q₂ : State → Prop} {C : Prop}
    (h₁ : WP isa c s Q₁) (h₂ : C → WP isa c s Q₂) : WP isa c s fun s' => Q₁ s' ∧ (C → Q₂ s') := by
  obtain ⟨t, s', he, hq⟩ := h₁
  refine ⟨t, s', he, hq, fun hC => ?_⟩
  obtain ⟨t₂, s₂, he₂, hq₂⟩ := h₂ hC
  rw [(Exec.det he he₂).2]; exact hq₂

theorem words_eq {m : Mem} {st : BitVec 32} {g : Nat → Nat} (hw : Words m st g) {k : Nat}
    (hk : k < 32) : words m st k = g k := hw k hk

end VG.Proof.Poly1305.X86

end

/-!
# Poly1305 on x86 (32-bit): the parts of each function, whatever the values

Untrusted: everything here is checked by Lean. Absorbing a block and the final
reduction run whatever the values (`Safe`), and compute what `Absorb.lean`
and `Reduce.lean` say where the numbers are within their bounds.
-/

open VG.PowLit

namespace VG.Proof.Poly1305.X86

open VG VG.X86 VG.Impl.Poly1305.X86
open VG.Spec.Poly1305 (P)

/-- The registers `absorb` writes, and the words of the state it stores. -/
abbrev aRegs : List Reg := [.eax, .ebx, .ecx, .edx, .ebp]
abbrev hS : List Nat := [0, 1, 2, 3, 4, 25, 26, 27, 28]

/-- The value of the block at `bp`, from its four words, and `pad · 2¹²⁸`. -/
abbrev blkv (m : Mem) (bp : BitVec 32) (pad : Nat) : Nat :=
  wv m bp 0 + 2 ^ 32 * wv m bp 4 + 2 ^ 64 * wv m bp 8 + 2 ^ 96 * wv m bp 12 + 2 ^ 128 * pad

theorem absorb_okList (pad : BitVec 32) : okList true aRegs hS false (absorb pad) = true := rfl

theorem absorbBuf_okList (pad : BitVec 32) : okList false aRegs hS false (absorbAt .edi 56 pad) = true :=
  rfl

/-- Absorbing the block at `b + d` (at `bp`, outside the state or in its
buffer): it runs, and where `C` gives the bounds, the new `h` is congruent to
`(h + m + pad · 2¹²⁸) r` modulo `p`. -/
theorem absorbAtFull_ok {st bp : BitVec 32} {s : State} (hc : Ctx st s) {b : Reg} {d : Nat} {blk : Bool}
    {pad : BitVec 32} (hok : okList blk aRegs hS false (absorbAt b d pad) = true)
    (hb : blk = true → BlkIn s) (hbase : b ≠ .eax)
    (hea : ∀ k < 4, addr (s.gpr b) (d + 4 * k) = addr bp (4 * k))
    (hrd : ∀ k < 4, InRegions (s.rd ++ s.wr) (addr bp (4 * k)) 4)
    (hd : ∀ k < 4, (sub bp (4 * k) 4).Disjoint (sR st) ∨ addr bp (4 * k) = addr st (4 * (14 + k)))
    (hpad : pad.toNat ≤ 1) {C : Prop} {r0 q1 q2 q3 : Nat}
    (hC : C → Coefs (words s.mem st) r0 q1 q2 q3 ∧ words s.mem st 4 ≤ 4) :
    WP isa (.block (absorbAt b d pad)) s fun s' => Safe st aRegs hS s s' ∧ (C → words s'.mem st 4 ≤ 4 ∧
      hw5 (words s'.mem st) % P = ((hw5 (words s.mem st) + blkv s.mem bp pad.toNat) * rval r0 q1 q2 q3) % P) := by
  refine WP.cond (okList_ok ⟨by decide, by decide⟩ _ false s hok hc hb
    (fun h => absurd h (by decide))) fun hC' => ?_
  obtain ⟨hco, h4⟩ := hC hC'
  refine WP.mono (absorb_ok ⟨hc, words_ok _ _, hbase, hea, hrd, hd⟩ hco h4 pad hpad)
    fun s' ⟨g, A, _, _, hv, hg4⟩ => ?_
  have e : ∀ k < 32, words s'.mem st k = g k := fun k hk => A.words k hk
  simp only [hw5, e 0 (by omega), e 1 (by omega), e 2 (by omega), e 3 (by omega), e 4 (by omega)]
  exact ⟨hg4, hv⟩

/-- Absorbing the block at `esi`, outside the state. -/
theorem absorbFull_ok {st : BitVec 32} {s : State} (hc : Ctx st s) (hb : BlkIn s)
    (hd : ∀ k < 4, (sub (s.gpr .esi) (4 * k) 4).Disjoint (sR st)) (pad : BitVec 32)
    (hpad : pad.toNat ≤ 1) {C : Prop} {r0 q1 q2 q3 : Nat}
    (hC : C → Coefs (words s.mem st) r0 q1 q2 q3 ∧ words s.mem st 4 ≤ 4) :
    WP isa (.block (absorb pad)) s fun s' => Safe st aRegs hS s s' ∧ (C → words s'.mem st 4 ≤ 4 ∧
      hw5 (words s'.mem st) % P =
        ((hw5 (words s.mem st) + blkv s.mem (s.gpr .esi) pad.toNat) * rval r0 q1 q2 q3) % P) :=
  absorbAtFull_ok hc (absorb_okList pad) (fun _ => hb) (by decide) (fun k _ => by rw [Nat.zero_add])
    (fun k _ => hb (4 * k) (by omega)) (fun k hk => .inl (hd k hk)) hpad hC

/-- The registers `reduce` writes. -/
abbrev rRegs : List Reg := [.eax, .ecx, .edx, .ebp]

theorem reduce_okList : okList false rRegs hS false reduce = true := by decide

/-- The final reduction: it runs, and where `h4 ≤ 4`, it leaves `h mod p`. -/
theorem reduceFull_ok {st : BitVec 32} {s : State} (hc : Ctx st s) :
    WP isa (.block reduce) s fun s' => Safe st rRegs hS s s' ∧ (words s.mem st 4 ≤ 4 →
      hw5 (words s'.mem st) = hw5 (words s.mem st) % P ∧ words s'.mem st 4 < 4) := by
  refine WP.cond (okList_ok ⟨by decide, by decide⟩ _ false s reduce_okList hc (fun h => absurd h (by decide))
    (fun h => absurd h (by decide))) fun h4 => ?_
  refine WP.mono (reduce_ok hc (words_ok _ _) h4) fun s' ⟨g, A, _, _, hv, hg4⟩ => ?_
  have e : ∀ k < 32, words s'.mem st k = g k := fun k hk => A.words k hk
  simp only [hw5, e 0 (by omega), e 1 (by omega), e 2 (by omega), e 3 (by omega), e 4 (by omega)]
  exact ⟨hv, hg4⟩

theorem restore_eq : restore = [.mov .eax (.reg .edi), .mov .ebx (.mem (at_ .eax 116)),
    .mov .esi (.mem (at_ .eax 120)), .mov .edi (.mem (at_ .eax 124)), .mov .ebp (.mem (at_ .eax 20)),
    .mov .ecx (.imm 0), .store (at_ .eax 20) .ecx] :=
  rfl

/-- Restoring the callee-saved registers from the state, and zeroing the word
that held `ebp`. -/
theorem restore_ok {st : BitVec 32} {s : State} (hc : Ctx st s) :
    WP isa (.block restore) s fun s' =>
      v s' .ebx = words s.mem st 29 ∧ v s' .esi = words s.mem st 30 ∧ v s' .edi = words s.mem st 31 ∧
      v s' .ebp = words s.mem st 5 ∧ s'.gpr .esp = s.gpr .esp ∧
      After st s s' (upd (words s.mem st) 5 0) [.eax, .ebx, .ecx, .esi, .edi, .ebp] := by
  have hfit := hc.fit
  rw [restore_eq]
  refine wp_mov fun s₁ u₁ _ => ?_
  have e₁ : s₁.gpr .eax = st := by rw [u₁.gpr, hc.edi]
  have c₁ : Ctx st s₁ := hc.keep (u₁.other _ (by decide)) u₁.wr
  refine wp_movm (a := addr st (4 * 29)) (by rw [ea_at, e₁]) (c₁.inRW (by omega) (by omega))
    fun s₂ u₂ _ => ?_
  have e₂ : s₂.gpr .eax = st := by rw [u₂.other .eax (by decide), e₁]
  refine wp_movm (a := addr st (4 * 30)) (by rw [ea_at, e₂])
    (by rw [u₂.rd, u₂.wr]; exact c₁.inRW (by omega) (by omega)) fun s₃ u₃ _ => ?_
  have e₃ : s₃.gpr .eax = st := by rw [u₃.other .eax (by decide), e₂]
  refine wp_movm (a := addr st (4 * 31)) (by rw [ea_at, e₃])
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr]; exact c₁.inRW (by omega) (by omega)) fun s₄ u₄ _ => ?_
  have e₄ : s₄.gpr .eax = st := by rw [u₄.other .eax (by decide), e₃]
  have r₄ : InRegions (s₄.rd ++ s₄.wr) (addr st (4 * 5)) 4 := by
    rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr]; exact c₁.inRW (by omega) (by omega)
  refine wp_movm (a := addr st (4 * 5)) (by rw [ea_at, e₄]) r₄ fun s₅ u₅ _ => ?_
  refine wp_movi fun s₆ u₆ _ => ?_
  have e₆ : s₆.gpr .eax = st := by rw [u₆.other .eax (by decide), u₅.other .eax (by decide), e₄]
  have w₆ : sR st ∈ s₆.wr := by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact hc.wr
  refine wp_store (a := addr st (4 * 5)) (by rw [ea_at, e₆]) ⟨_, w₆, sR_contains hfit (by omega) (by omega)⟩
    fun s₇ u₇ => WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, ⟨?_, ?_, fun r hr => ?_, ?_, ?_⟩⟩
  · simp only [v, words, wv, wd]
    rw [u₇.gpr, u₆.other .ebx (by decide), u₅.other .ebx (by decide), u₄.other .ebx (by decide),
      u₃.other .ebx (by decide), u₂.gpr, u₁.mem]
  · simp only [v, words, wv, wd]
    rw [u₇.gpr, u₆.other .esi (by decide), u₅.other .esi (by decide), u₄.other .esi (by decide), u₃.gpr,
      u₂.mem, u₁.mem]
  · simp only [v, words, wv, wd]
    rw [u₇.gpr, u₆.other .edi (by decide), u₅.other .edi (by decide), u₄.gpr, u₃.mem, u₂.mem, u₁.mem]
  · simp only [v, words, wv, wd]
    rw [u₇.gpr, u₆.other .ebp (by decide), u₅.gpr, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  · rw [u₇.gpr, u₆.other .esp (by decide), u₅.other .esp (by decide), u₄.other .esp (by decide),
      u₃.other .esp (by decide), u₂.other .esp (by decide), u₁.other .esp (by decide)]
  · rw [u₇.mem, u₆.gpr, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
    exact (words_ok s.mem st).write hfit (j := 5) (by omega) 0
  · rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
    exact frame_write (Frame.refl _ _) hfit (by omega) _
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₇.gpr, u₆.other r hr.2.2.1, u₅.other r hr.2.2.2.2.2, u₄.other r hr.2.2.2.2.1,
      u₃.other r hr.2.2.2.1, u₂.other r hr.2.1, u₁.other r hr.1]
  · rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]

end VG.Proof.Poly1305.X86
