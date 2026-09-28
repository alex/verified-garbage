import VerifiedGarbage.Proof.Poly1305.AArch64.Init

/-!
# Poly1305 on AArch64: `finalize`

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.Poly1305.AArch64

open VG VG.AArch64 VG.Impl.Poly1305.AArch64
open VG.Spec.Poly1305 (P clamp leNum bytesAt accumulate Repr leBytes mac)

/-! ## Bytes in memory -/

theorem write1_apply (m : Mem) (a x : Addr) (v : BitVec (8 * 1)) :
    m.write a 1 v x = if x = a then v.extractLsb' 0 8 else m x := by
  simp only [Mem.write]
  by_cases h : x = a
  · subst h; simp
  · have : ¬ (x - a).toNat < 1 := by
      intro h'
      apply h
      have h0 : (x - a).toNat = 0 := by omega
      have := BitVec.eq_of_toNat_eq (x := x - a) (y := 0) (by rw [h0]; rfl)
      bv_omega
    simp only [this, h, ↓reduceIte]

theorem writeW64_zero_apply (m : Mem) (a x : Addr) :
    (m.writeW a (0 : BitVec 64)) x = if (x - a).toNat < 8 then 0 else m x := by
  simp only [Mem.writeW, Mem.write]
  split <;> simp

/-- Byte `k` of the padded block. -/
abbrev bufB (st : Addr) (k : Nat) : Addr := st + BitVec.ofNat 64 (96 + k)

/-- The padded block's bytes are `f k`. -/
def BufHas (m : Mem) (st : Addr) (f : Nat → Byte) : Prop := ∀ k < 16, m (bufB st k) = f k

/-- The region of the padded block. -/
abbrev bufR (st : Addr) : Region := ⟨off st 96, 16⟩

theorem bufR_sub_wR (st : Addr) : Region.Sub (bufR st) (wR st) := by
  intro a ha
  simp only [Region.Contains, off] at *
  bv_omega

theorem bufB_contains (st : Addr) {k : Nat} (hk : k < 16) : (bufR st).Contains (bufB st k) 1 := by
  simp only [Region.Contains, off]
  rw [show st + BitVec.ofNat 64 (96 + k) - (st + BitVec.ofNat 64 96) = BitVec.ofNat 64 k by bv_omega,
    toNat_ofNat_lt (by omega)]
  omega

theorem bufB_inj (st : Addr) {j k : Nat} (hj : j < 16) (hk : k < 16) (h : bufB st j = bufB st k) :
    j = k := by
  have := congrArg BitVec.toNat (show BitVec.ofNat 64 (96 + j) = BitVec.ofNat 64 (96 + k) by
    simpa [bufB] using h)
  rw [toNat_ofNat_lt (by omega), toNat_ofNat_lt (by omega)] at this
  omega

/-- The bytes of the padded block, as read from memory. -/
theorem bytesAt_buf {m : Mem} {st : Addr} {f : Nat → Byte} (h : BufHas m st f) :
    bytesAt m (off st 96) 16 = (List.range 16).map f := by
  simp only [bytesAt]
  apply List.map_congr_left
  intro k hk
  have hk := List.mem_range.mp hk
  rw [← h k hk]
  congr 1
  simp only [off, bufB]
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem bufB_zero (m : Mem) (st : Addr) {k : Nat} (hk : k < 16) :
    ((m.writeW (off st 96) (0 : BitVec 64)).writeW (off st 104) (0 : BitVec 64)) (bufB st k) = 0 := by
  rw [writeW64_zero_apply, writeW64_zero_apply]
  simp only [off, bufB]
  by_cases h : 8 ≤ k
  · have hc : (st + BitVec.ofNat 64 (96 + k) - (st + BitVec.ofNat 64 104)).toNat < 8 := by
      rw [show st + BitVec.ofNat 64 (96 + k) - (st + BitVec.ofNat 64 104) = BitVec.ofNat 64 (k - 8) by
        bv_omega, toNat_ofNat_lt (by omega)]
      omega
    simp only [hc, ↓reduceIte]
  · have hc : ¬ (st + BitVec.ofNat 64 (96 + k) - (st + BitVec.ofNat 64 104)).toNat < 8 := by
      rw [show st + BitVec.ofNat 64 (96 + k) - (st + BitVec.ofNat 64 104) =
        BitVec.ofNat 64 (2 ^ 64 - 8 + k) by bv_omega, toNat_ofNat_lt (by omega)]
      omega
    have hc' : (st + BitVec.ofNat 64 (96 + k) - (st + BitVec.ofNat 64 96)).toNat < 8 := by
      rw [show st + BitVec.ofNat 64 (96 + k) - (st + BitVec.ofNat 64 96) = BitVec.ofNat 64 k by
        bv_omega, toNat_ofNat_lt (by omega)]
      omega
    simp only [hc, hc', ↓reduceIte]

/-! ## The precondition -/

section
variable (s₀ : State)
abbrev tp : Addr := s₀.gpr .x1
abbrev tl : Nat := (s₀.gpr .x2).toNat
abbrev op : Addr := s₀.gpr .x3
abbrev tR : Region := ⟨tp s₀, tl s₀⟩
abbrev oR : Region := ⟨op s₀, 16⟩
/-- The message's last bytes. -/
abbrev tail : List Byte := bytesAt s₀.mem (tp s₀) (tl s₀)
end

structure FPre (s₀ : State) : Prop where
  rd : s₀.rd = [tR s₀]
  wr : s₀.wr = [sR (st s₀), oR s₀]
  st_t : (sR (st s₀)).Disjoint (tR s₀)
  st_o : (sR (st s₀)).Disjoint (oR s₀)
  t_o : (tR s₀).Disjoint (oR s₀)
  tl_lt : tl s₀ < 16

theorem FPre.of (s₀ : State) (h : Proof.Poly1305.finalizeAArch64.pre s₀) : FPre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem FPre.in_st {s₀ : State} (hp : FPre s₀) {d n : Nat} (h : d + n ≤ 128) :
    InRegions s₀.wr (off (st s₀) d) n :=
  ⟨_, by rw [hp.wr]; exact List.mem_cons_self, contains_off h (by omega)⟩

/-! ## Copying the last bytes into the padded block -/

/-- The registers the copy writes. -/
abbrev copyRegs : List Reg := [.x1, .x9, .x10, .x11]

/-- The copy loop's invariant, before byte `j`, from the state `s₁` after `setup`. -/
structure CInv (s₀ : State) (m₁ : Mem) (s₁ : State) (j : Nat) (s : State) : Prop where
  x1 : s.gpr .x1 = tp s₀ + BitVec.ofNat 64 j
  x9 : s.gpr .x9 = bufB (st s₀) j
  x10 : s.gpr .x10 = BitVec.ofNat 64 (tl s₀ - j)
  keep : ∀ r, r ∉ copyRegs → s.gpr r = s₁.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [bufR (st s₀)] m₁ s.mem
  buf : BufHas s.mem (st s₀) fun k => if k < j then (tail s₀).getD k 0 else 0

theorem contains_base {a : Addr} {n len : Nat} (h : n ≤ len) : (⟨a, len⟩ : Region).Contains a n := by
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add]; exact h

theorem exec_movz0 {s : State} {d : Reg} {imm : BitVec 16} :
    exec (.movz .x d imm 0) s = some (s.write .x d (imm.setWidth 64 <<< (16 * 0))) := by
  simp [exec, Size.bits]

theorem movz0 : ((0 : BitVec 16).setWidth 64 <<< (16 * 0) : BitVec 64) = 0 := by decide

set_option simprocs false in
theorem zero_ok {s₀ : State} (hp : FPre s₀) {s₁ : State} (h₁ : Setup s₀ s₁) :
    WP isa (.block zeroBuf) s₁ (CInv s₀ s₁.mem s₁ 0) := by
  have x0₁ : s₁.gpr .x0 = st s₀ := h₁.gpr .x0 (by decide)
  have o1 := hp.in_st (d := 96) (n := 8) (by omega)
  have o2 := hp.in_st (d := 104) (n := 8) (by omega)
  rw [← h₁.wr, ← x0₁] at o1 o2
  simp only [off] at o1 o2
  apply WP.of_runBlock
  simp (config := {decide := true}) only [zeroBuf, runBlock_cons, runStep_some, runBlock_nil,
    exec_str_x (show 96 % 8 = 0 ∧ 96 < 32768 by decide), exec_str_x (show 104 % 8 = 0 ∧ 104 < 32768 by decide),
    exec_addImm_x (show 96 < 4096 by decide), exec_addImm_x (show 0 < 4096 by decide), exec_movz0,
    State.read, State.write, Size.bits, BitVec.setWidth_eq, o1, o2, ite_true, ite_false,
    Option.some.injEq, exists_eq_left', movz0]
  refine ⟨?_, ?_, ?_, fun r hr => ?_, h₁.rd, h₁.wr, ?_, fun k hk => ?_⟩
  · simp (config := {decide := true}) only [ite_false]
    rw [h₁.gpr .x1 (by decide), add_ofNat_zero]
  · simp (config := {decide := true}) only [ite_true, ite_false]
    rw [x0₁]
  · simp (config := {decide := true}) only [ite_true]
    rw [h₁.gpr .x2 (by decide), add_ofNat_zero]; simp [tl]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [hr.2.1, hr.2.2.1, hr.2.2.2]
  · rw [x0₁]
    have c96 : (bufR (st s₀)).Contains (off (st s₀) 96) (64 / 8) := contains_base (by decide)
    have c104 : (bufR (st s₀)).Contains (off (st s₀) 104) (64 / 8) := by
      simp only [Region.Contains]
      rw [show st s₀ + BitVec.ofNat 64 104 - (st s₀ + BitVec.ofNat 64 96) = BitVec.ofNat 64 8 by
        bv_omega, toNat_ofNat_lt (by omega)]
    dsimp only
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ c96).writeW
      (List.mem_singleton_self _) _ c104
  · dsimp only
    rw [x0₁]
    simp only [Nat.not_lt_zero, ite_false]
    exact bufB_zero _ _ hk

theorem read_one (m : Mem) (a : Addr) : (m.read a 1 : BitVec 8) = m a := by
  simp only [Mem.read]
  ext i hi
  rw [BitVec.getElem_append]
  simp only [show i < 8 by omega, dite_true]

theorem exec_ldrb' {s : State} {t n : Reg} {off : Nat} (ho : off < 4096)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr n + BitVec.ofNat 64 off) 1) :
    exec (.ldrb t n off) s = some (s.write .w t ((s.mem (s.gpr n + BitVec.ofNat 64 off)).setWidth 32)) := by
  simp only [exec, addr, Nat.mod_one, true_and, show off < 4096 * 1 by omega, ite_true,
    Option.bind_some, State.load, hin, Option.map_some]
  rw [read_one]

theorem exec_strb' {s : State} {t n : Reg} {off : Nat} (ho : off < 4096)
    (hout : InRegions s.wr (s.gpr n + BitVec.ofNat 64 off) 1) :
    exec (.strb t n off) s =
      some { s with mem := s.mem.writeW (s.gpr n + BitVec.ofNat 64 off) ((s.gpr t).setWidth 8) } := by
  simp only [exec, addr, Nat.mod_one, true_and, show off < 4096 * 1 by omega, ite_true,
    Option.bind_some, State.store, hout, Mem.writeW, State.read]
  congr 3
  ext i hi; simp [Size.bits]; try omega

theorem writeW8_apply (m : Mem) (a x : Addr) (v : Byte) :
    (m.writeW a v) x = if x = a then v else m x := by
  simp only [Mem.writeW, Mem.write]
  by_cases h : x = a
  · subst h; simp
  · have : ¬ (x - a).toNat < 8 / 8 := by
      intro h'
      apply h
      have h0 : (x - a).toNat = 0 := by omega
      have := BitVec.eq_of_toNat_eq (x := x - a) (y := 0) (by rw [h0]; rfl)
      bv_omega
    simp only [this, h, ↓reduceIte]

theorem byte_rt (b : Byte) : ((b.setWidth 32).setWidth 64).setWidth 8 = b := by
  ext i hi; simp

theorem tail_getD {s₀ : State} {j : Nat} (hj : j < tl s₀) :
    (tail s₀).getD j 0 = s₀.mem (tp s₀ + BitVec.ofNat 64 j) := by
  simp [tail, bytesAt, hj]

set_option simprocs false in
theorem copy_step {s₀ : State} (hp : FPre s₀) {s₁ : State} (h₁ : Setup s₀ s₁) {j : Nat}
    (hj : j < tl s₀) {s : State} (h : CInv s₀ s₁.mem s₁ j s) :
    WP isa (.block copyBody) s fun s' => CInv s₀ s₁.mem s₁ (j + 1) s' := by
  have htl := hp.tl_lt
  have hin1 : InRegions (s.rd ++ s.wr) (s.gpr .x1 + BitVec.ofNat 64 0) 1 := by
    rw [h.rd, hp.rd, h.x1, add_ofNat_zero]
    refine ⟨tR s₀, List.mem_append_left _ (List.mem_singleton_self _), contains_off (by omega) (by omega)⟩
  have hout : InRegions s.wr (s.gpr .x9 + BitVec.ofNat 64 0) 1 := by
    rw [h.wr, hp.wr, h.x9, add_ofNat_zero]
    refine ⟨sR (st s₀), List.mem_cons_self, ?_⟩
    simp only [Region.Contains, bufB]
    rw [show st s₀ + BitVec.ofNat 64 (96 + j) - st s₀ = BitVec.ofNat 64 (96 + j) by bv_omega,
      toNat_ofNat_lt (by omega)]
    omega
  apply WP.of_runBlock
  simp (config := {decide := true}) only [copyBody, runBlock_cons, runStep_some,
    exec_ldrb' (show 0 < 4096 by decide) hin1]
  rw [exec_strb' (show 0 < 4096 by decide) (by simpa (config := {decide := true}) [State.write] using hout)]
  simp (config := {decide := true}) only [runStep_some, runBlock_nil, runBlock_cons,
    exec_addImm_x (show 1 < 4096 by decide), exec_subImm_x (show 1 < 4096 by decide), State.read,
    State.write, Size.bits, BitVec.setWidth_eq, ite_true, ite_false, Option.some.injEq,
    exists_eq_left', add_ofNat_zero]
  -- The byte copied is byte `j` of the tail.
  have hbyte : s.mem (s.gpr .x1) = (tail s₀).getD j 0 := by
    rw [tail_getD hj, h.x1]
    have hf : Frame [cR (st s₀), bufR (st s₀)] s₀.mem s.mem :=
      (h₁.frame.mono (by simp)).trans (h.frame.mono (by simp))
    refine hf _ fun r hr hc => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    have ht : (tR s₀).Contains (tp s₀ + BitVec.ofNat 64 j) 1 := contains_off (by omega) (by omega)
    rcases hr with rfl | rfl
    · exact hp.st_t _ (cR_sub_sR _ _ hc) ht
    · exact hp.st_t _ (sub_sR _ (by omega) _ hc) ht
  refine ⟨?_, ?_, ?_, fun r hr => ?_, h.rd, h.wr, ?_, fun k hk => ?_⟩
  · dsimp only
    simp (config := {decide := true}) only [ite_true, ite_false]
    rw [h.x1, BitVec.add_assoc, ← BitVec.ofNat_add]
  · dsimp only
    simp (config := {decide := true}) only [ite_true, ite_false]
    rw [h.x9, bufB, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_assoc]
  · dsimp only
    simp (config := {decide := true}) only [ite_true, ite_false]
    rw [h.x10]
    bv_omega
  · dsimp only
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]
    exact h.keep r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2])
  · dsimp only
    rw [h.x9]
    exact h.frame.writeW (List.mem_singleton_self _) _ (bufB_contains _ (by omega))
  · dsimp only
    rw [writeW8_apply, h.x9, byte_rt, hbyte]
    by_cases hkj : k = j
    · subst hkj
      simp only [ite_true, show k < k + 1 by omega]
    · have hne : bufB (st s₀) k ≠ bufB (st s₀) j := fun he => hkj (bufB_inj _ hk (by omega) he)
      simp only [hne, ite_false]
      rw [h.buf k hk]
      by_cases hk' : k < j
      · simp [hk', show k < j + 1 by omega]
      · simp [hk', show ¬ k < j + 1 by omega]

/-- The padded block: the tail, `0x01`, zeros. -/
def padded (s₀ : State) (k : Nat) : Byte :=
  if k < tl s₀ then (tail s₀).getD k 0 else if k = tl s₀ then 1 else 0

/-- After the `0x01` byte, with `x1` pointing at the padded block. -/
structure PInv (s₀ : State) (m₁ : Mem) (s₁ : State) (s : State) : Prop where
  x1 : s.gpr .x1 = off (st s₀) 96
  keep : ∀ r, r ∉ copyRegs → s.gpr r = s₁.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [bufR (st s₀)] m₁ s.mem
  buf : BufHas s.mem (st s₀) (padded s₀)

theorem one_byte : ((((1 : BitVec 16).setWidth 64 <<< (16 * 0) : BitVec 64)).setWidth 8 : Byte) = 1 := by
  decide

set_option simprocs false in
theorem padByte_ok {s₀ : State} (hp : FPre s₀) {s₁ : State} (h₁ : Setup s₀ s₁) {s : State}
    (h : CInv s₀ s₁.mem s₁ (tl s₀) s) :
    WP isa (.block padByte) s (PInv s₀ s₁.mem s₁) := by
  have htl := hp.tl_lt
  have hout : InRegions s.wr (s.gpr .x9 + BitVec.ofNat 64 0) 1 := by
    rw [h.wr, hp.wr, h.x9, add_ofNat_zero]
    refine ⟨sR (st s₀), List.mem_cons_self, ?_⟩
    simp only [Region.Contains, bufB]
    rw [show st s₀ + BitVec.ofNat 64 (96 + tl s₀) - st s₀ = BitVec.ofNat 64 (96 + tl s₀) by bv_omega,
      toNat_ofNat_lt (by omega)]
    omega
  have x0 : s.gpr .x0 = st s₀ := by rw [h.keep .x0 (by decide), h₁.gpr .x0 (by decide)]
  apply WP.of_runBlock
  simp (config := {decide := true}) only [padByte, runBlock_cons, runStep_some, exec_movz0]
  rw [exec_strb' (show 0 < 4096 by decide) (by simpa (config := {decide := true}) [State.write] using hout)]
  simp (config := {decide := true}) only [runStep_some, runBlock_nil, runBlock_cons,
    exec_addImm_x (show 96 < 4096 by decide), State.read, State.write, Size.bits, BitVec.setWidth_eq,
    ite_true, ite_false, Option.some.injEq, exists_eq_left', add_ofNat_zero, one_byte]
  refine ⟨?_, fun r hr => ?_, h.rd, h.wr, ?_, fun k hk => ?_⟩
  · dsimp only
    simp (config := {decide := true}) only [ite_true]
    rw [x0]
  · dsimp only
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [hr.1, hr.2.2.2, ite_false]
    exact h.keep r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2])
  · dsimp only
    rw [h.x9]
    exact h.frame.writeW (List.mem_singleton_self _) _ (bufB_contains _ (by omega))
  · dsimp only
    rw [writeW8_apply, h.x9]
    by_cases hkj : k = tl s₀
    · subst hkj
      simp only [ite_true, padded, Nat.lt_irrefl, ite_false]
    · have hne : bufB (st s₀) k ≠ bufB (st s₀) (tl s₀) := fun he => hkj (bufB_inj _ hk (by omega) he)
      simp only [hne, ite_false]
      rw [h.buf k hk]
      by_cases hk' : k < tl s₀
      · simp [padded, hk']
      · simp [padded, hk', hkj]

/-- The padded block as a number: the tail with `0x01` appended. -/
theorem padded_value {s₀ : State} (hp : FPre s₀) {m : Mem} (h : BufHas m (st s₀) (padded s₀)) :
    w64 m (off (st s₀) 96) 0 + 2 ^ 64 * w64 m (off (st s₀) 96) 8 + 2 ^ 128 * false.toNat =
      leNum (tail s₀ ++ [0x01]) := by
  have htl := hp.tl_lt
  have hl : (List.range 16).map (padded s₀) =
      (tail s₀ ++ [0x01]) ++ List.replicate (15 - tl s₀) 0 := by
    apply List.ext_getElem
    · simp [tail, Poly1305.length_bytesAt]; omega
    · intro k h₁ h₂
      simp only [List.getElem_map, List.getElem_range]
      have hlen : (tail s₀).length = tl s₀ := Poly1305.length_bytesAt _ _ _
      rcases Nat.lt_trichotomy k (tl s₀) with hk | rfl | hk
      · rw [List.getElem_append_left (by simp [hlen]; omega), List.getElem_append_left (by omega)]
        simp only [padded, hk, ite_true]
        simp [tail, bytesAt, hk]
      · rw [List.getElem_append_left (by simp [hlen]), List.getElem_append_right (by omega)]
        simp [padded, hlen]
      · rw [List.getElem_append_right (by simp [hlen]; omega)]
        simp [padded, show ¬ k < tl s₀ by omega, show k ≠ tl s₀ by omega]
  rw [Bool.toNat_false, Nat.mul_zero, Nat.add_zero, ← leNum_key, bytesAt_buf h, hl,
    Poly1305.leNum_append _ (List.replicate _ _), Poly1305.leNum_replicate_zero, Nat.mul_zero,
    Nat.add_zero]

theorem coef_facts : ∀ k < 5, ∀ i < 5, 56 ≤ coef k i ∧ coef k i + 4 ≤ 92 := by decide

/-- The coefficients are unchanged by writes to the padded block. -/
theorem Coefs.frame {m m' : Mem} {st : Addr} {R : Nat} (h : Coefs m st R) (hf : Frame [bufR st] m m') :
    Coefs m' st R := by
  intro k hk i hi
  obtain ⟨c₁, c₂⟩ := coef_facts k hk i hi
  rw [← h k hk i hi]
  refine congrArg BitVec.toNat (hf.readW (r := ⟨off st (coef k i), 4⟩) (Region.contains_self _ _) ?_
    (by decide))
  simp only [List.mem_singleton, forall_eq]
  intro a h₁ h₂
  simp only [Region.Contains, off] at h₁ h₂
  bv_omega

/-- After the last bytes (if any) are absorbed. -/
structure Tail (s₀ : State) (m₁ : Mem) (s₁ : State) (s : State) : Prop where
  keep : ∀ r ∈ [Reg.x0, .x3, .x17], s.gpr r = s₁.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [bufR (st s₀)] m₁ s.mem
  acc : A0 s₀ < P → hv s % P = Poly1305.absorbAll (Rn s₀) (A0 s₀) (tail s₀) % P ∧ Bounds s

theorem tail_nil {s₀ : State} (h : tl s₀ = 0) : tail s₀ = [] := by
  simp [tail, bytesAt, h]

theorem lastBlock_ok {s₀ : State} (hp : FPre s₀) {s₁ : State} (h₁ : Setup s₀ s₁)
    (hpos : 0 < tl s₀) : WP isa lastBlock s₁ (Tail s₀ s₁.mem s₁) := by
  have htl := hp.tl_lt
  refine WP.seq (WP.mono (zero_ok hp h₁) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (Q := CInv s₀ s₁.mem s₁ (tl s₀)) ?_ fun s₃ h₃ => ?_)
  · -- The copy loop.
    let Inv : Nat → State → Prop := fun n s => ∃ j, n = tl s₀ - j ∧ j < tl s₀ ∧ CInv s₀ s₁.mem s₁ j s
    have hstep : ∀ n s, Inv n s → WP isa (.block copyBody) s (fun s' =>
        (eval (.nonzero .x .x10) s' = some false ∧ CInv s₀ s₁.mem s₁ (tl s₀) s') ∨
        (eval (.nonzero .x .x10) s' = some true ∧ ∃ n' < n, Inv n' s')) := by
      rintro n s ⟨j, rfl, hj, h⟩
      refine WP.mono (copy_step hp h₁ hj h) fun s' h' => ?_
      have hev : eval (.nonzero .x .x10) s' = some (BitVec.ofNat 64 (tl s₀ - (j + 1)) != 0) := by
        simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, h'.x10]
      by_cases hl : j + 1 = tl s₀
      · exact .inl ⟨by rw [hev, hl]; simp, hl ▸ h'⟩
      · have h0 : BitVec.ofNat 64 (tl s₀ - (j + 1)) ≠ 0 := by
          intro h0
          have h0' := congrArg BitVec.toNat h0
          rw [toNat_ofNat_lt (by omega)] at h0'
          simp at h0'; omega
        exact .inr ⟨by rw [hev]; simpa using h0, tl s₀ - (j + 1), by omega, j + 1, rfl, by omega, h'⟩
    exact WP.loop (M := isa) Inv hstep (tl s₀) s₂ ⟨0, by simp, hpos, h₂⟩
  · -- The `0x01` byte, and the block.
    refine WP.block_append (WP.mono (padByte_ok hp h₁ h₃) fun s₄ h₄ => ?_)
    have g : ∀ r, r ∉ copyRegs → s₄.gpr r = s₁.gpr r := h₄.keep
    have x0₄ : s₄.gpr .x0 = st s₀ := by rw [g .x0 (by decide), h₁.gpr .x0 (by decide)]
    have hin : ∀ d : Nat, d + 8 ≤ 16 →
        InRegions (s₄.rd ++ s₄.wr) (s₄.gpr .x1 + BitVec.ofNat 64 d) 8 := by
      intro d hd
      rw [h₄.rd, h₄.wr, h₄.x1, ← off, off_off]
      exact ⟨_, List.mem_append_right _ (by rw [hp.wr]; exact List.mem_cons_self),
        contains_off (by omega) (by omega)⟩
    have hco : Coefs s₄.mem (s₄.gpr .x0) (Rn s₀) := by
      rw [x0₄]; exact h₁.coefs.frame h₄.frame
    have hc : CoefIn s₄ := fun off h₁' h₂' => by
      rw [h₄.rd, h₄.wr, x0₄, hp.wr]
      exact ⟨_, List.mem_append_right _ List.mem_cons_self, contains_off (by omega) (by omega)⟩
    have hab := absorb_ok s₄ false (Rk_lt _ _) (by rw [g .x17 (by decide)]; exact h₁.mask) hco hc
      (hin 0 (by omega)) (hin (0 + 8) (by omega))
    refine WP.mono hab fun s₅ ⟨ha, k₅⟩ => ?_
    refine ⟨fun r hr => ?_, by rw [k₅.2.2.1, h₄.rd], by rw [k₅.2.2.2, h₄.wr],
      by rw [k₅.2.1]; exact h₄.frame, fun hA => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> rw [k₅.gpr', g _ (by decide)]
    · have e₄ : ∀ r ∈ [Reg.x4, .x5, .x6, .x7, .x8], s₄.gpr r = s₁.gpr r := fun r hr => g r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)
      obtain ⟨hv₄, hb₄⟩ := bounds_eq e₄
      obtain ⟨hv₁, hb₁⟩ := h₁.acc hA
      obtain ⟨hv, hb⟩ := ha (hb₄ hb₁)
      refine ⟨?_, hb⟩
      have hlen : (tail s₀).length = tl s₀ := Poly1305.length_bytesAt _ _ _
      rw [hv, hv₄, hv₁, h₄.x1, padded_value hp h₄.buf,
        Poly1305.absorbAll_block (by omega) (by omega), Nat.mod_mod, Nat.mul_comm]

/-! ## Epilogue -/

set_option simprocs false in
/-- Storing the tag. -/
theorem storeTag_ok (s : State) (hout : (⟨s.gpr .x3, 16⟩ : Region) ∈ s.wr) :
    WP isa (.block storeTag) s fun s' =>
      s'.mem.readW (s.gpr .x3 + BitVec.ofNat 64 0) 64 = s.gpr .x14 ∧
      s'.mem.readW (s.gpr .x3 + BitVec.ofNat 64 8) 64 = s.gpr .x15 ∧
      Frame [⟨s.gpr .x3, 16⟩] s.mem s'.mem := by
  have o0 : InRegions s.wr (off (s.gpr .x3) 0) 8 := ⟨_, hout, contains_off (by omega) (by omega)⟩
  have o8 : InRegions s.wr (off (s.gpr .x3) 8) 8 := ⟨_, hout, contains_off (by omega) (by omega)⟩
  simp only [off] at o0 o8
  apply WP.of_runBlock
  simp (config := {decide := true}) only [storeTag, runBlock_cons, runStep_some, runBlock_nil,
    exec_str_x (show 0 % 8 = 0 ∧ 0 < 32768 by decide) o0, exec_str_x (show 8 % 8 = 0 ∧ 8 < 32768 by decide),
    o8, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, ?_⟩
  · have := readW_writeW_off (s.mem.writeW (off (s.gpr .x3) 0) (s.gpr .x14)) (s.gpr .x3) (s.gpr .x15)
      (d := 0) (e := 8) (by omega) (by omega) (by omega)
    simp only [off] at this
    rw [this, Mem.readW_writeW_self64]
  · exact Mem.readW_writeW_self64 _ _ _
  · exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_off (by omega) (by omega))).writeW
      (List.mem_singleton_self _) _ (contains_off (by omega) (by omega))

theorem fepi_eq : reduce ++ addS ++ pack ++ storeTag = reduce ++ (load2 .x0 40 ++ (split ++
    ((addLimbs ++ carryStep .x4 .x4 .x5 ++ normalize) ++ (pack ++ storeTag)))) := by
  simp only [addS, List.append_assoc]

/-- A key word, unchanged since entry. -/
theorem key_word {s₀ : State} {m : Mem} (hf : Frame [cR (st s₀), bufR (st s₀)] s₀.mem m) {d : Nat}
    (h₁ : 24 ≤ d) (h₂ : d + 8 ≤ 56) : m.readW (off (st s₀) d) 64 = s₀.mem.readW (off (st s₀) d) 64 := by
  refine hf.readW (r := ⟨off (st s₀) d, 8⟩) (Region.contains_self _ _) ?_ (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl) <;> intro a h₁ h₂ <;> simp only [Region.Contains, off] at h₁ h₂ <;> bv_omega

theorem fepilogue_ok {s₀ : State} (hp : FPre s₀) {s₁ : State} (h₁ : Setup s₀ s₁) {s : State}
    (ht : Tail s₀ s₁.mem s₁ s) :
    WP isa (.block (reduce ++ addS ++ pack ++ storeTag)) s fun s' =>
      Proof.Poly1305.finalizeAArch64.post s₀ s' := by
  have hm : s.gpr .x17 = M26 := by rw [ht.keep .x17 (by simp)]; exact h₁.mask
  have x0 : s.gpr .x0 = st s₀ := by rw [ht.keep .x0 (by simp), h₁.gpr .x0 (by decide)]
  have x3 : s.gpr .x3 = op s₀ := by rw [ht.keep .x3 (by simp), h₁.gpr .x3 (by decide)]
  have hf : Frame [cR (st s₀), bufR (st s₀)] s₀.mem s.mem :=
    (h₁.frame.mono (by simp)).trans (ht.frame.mono (by simp))
  rw [fepi_eq]
  refine WP.block_append (WP.mono (reduce_ok s hm) fun s₂ ⟨hr, k₂⟩ => ?_)
  have hin : ∀ d, d + 8 ≤ 128 → InRegions (s₂.rd ++ s₂.wr) (s₂.gpr .x0 + BitVec.ofNat 64 d) 8 := by
    intro d hd
    rw [k₂.2.2.1, k₂.2.2.2, k₂.gpr', ht.rd, ht.wr, x0, hp.wr]
    exact ⟨_, List.mem_append_right _ List.mem_cons_self, contains_off hd (by omega)⟩
  refine WP.block_append (WP.mono (load2_ok s₂ (n := .x0) (off := 40) (by decide) (by decide)
    (by decide) (hin 40 (by omega)) (hin (40 + 8) (by omega))) fun s₃ ⟨l₁, l₂, k₃⟩ => ?_)
  refine WP.block_append (WP.mono (split_ok s₃ (by rw [k₃.gpr', k₂.gpr']; exact hm))
    fun s₄ ⟨m0, m1, m2, m3, m4, k₄⟩ => ?_)
  refine WP.block_append (WP.mono (addCarry_ok s₄ (by rw [k₄.gpr', k₃.gpr', k₂.gpr']; exact hm))
    fun s₅ ⟨ha, k₅⟩ => ?_)
  refine WP.block_append (WP.mono (pack_ok s₅) fun s₆ ⟨hq, k₆⟩ => ?_)
  have k₂₆ := (((k₂.trans k₃).trans k₄).trans k₅).trans k₆
  refine WP.mono (storeTag_ok s₆ (by
    rw [k₂₆.2.2.2, k₂₆.gpr', ht.wr, x3, hp.wr]; exact List.mem_cons_of_mem _ List.mem_cons_self))
    fun s₇ ⟨t0, t8, _⟩ => ?_
  intro key msg hrep
  have hA := A0_lt hrep
  obtain ⟨hv₀, hb⟩ := ht.acc hA
  obtain ⟨hN, n0, n1, n2, n3, n4⟩ := hr hb
  -- The limbs of `h mod p`, in `s₄`.
  have k₃₄ := k₃.trans k₄
  have e4 : ∀ r ∈ [Reg.x4, .x5, .x6, .x7, .x8], v s₄ r = v s₂ r := fun r hr => by
    simp only [v]; rw [k₃₄.1 r (by revert hr; decide +revert)]
  rw [← e4 .x4 (by simp), ← e4 .x5 (by simp), ← e4 .x6 (by simp), ← e4 .x7 (by simp),
    ← e4 .x8 (by simp)] at hN
  rw [← e4 .x4 (by simp)] at n0; rw [← e4 .x5 (by simp)] at n1; rw [← e4 .x6 (by simp)] at n2
  rw [← e4 .x7 (by simp)] at n3; rw [← e4 .x8 (by simp)] at n4
  -- The key's `s`.
  have hS : v s₃ .x14 + 2 ^ 64 * v s₃ .x15 =
      w64 s₀.mem (off (st s₀) 40) 0 + 2 ^ 64 * w64 s₀.mem (off (st s₀) 40) 8 := by
    simp only [v, w64, l₁, l₂, k₂.2.1, k₂.gpr' (r := .x0), x0, off, add_ofNat_zero, add_ofNat_add]
    rw [key_word hf (d := 40) (by omega) (by omega), key_word hf (d := 40 + 8) (by omega) (by omega)]
  have hSlt : v s₃ .x14 + 2 ^ 64 * v s₃ .x15 < 2 ^ 128 := by
    have := (s₃.gpr .x14).isLt; have := (s₃.gpr .x15).isLt; simp only [v]; omega
  have hsum := ha (by omega) (by omega) (by omega) (by omega) (by omega)
    (by rw [m0]; exact lt_trans (lim_lt _ (by omega)) (by norm_num))
    (by rw [m1]; exact lt_trans (lim_lt _ (by omega)) (by norm_num))
    (by rw [m2]; exact lt_trans (lim_lt _ (by omega)) (by norm_num))
    (by rw [m3]; exact lt_trans (lim_lt _ (by omega)) (by norm_num))
    (by rw [m4]; exact lt_trans (lim4_lt hSlt) (by norm_num))
  obtain ⟨hV, b0, b1, b2, b3, -⟩ := hsum
  rw [m0, m1, m2, m3, m4, val5_lim, hS, hN, hv₀,
    Nat.mod_eq_of_lt (Poly1305.absorbAll_lt hA _)] at hV
  obtain ⟨q0, q1, -⟩ := hq b0 b1 b2 b3
  rw [hV] at q0 q1
  have x3₆ : s₆.gpr .x3 = op s₀ := by rw [k₂₆.gpr', x3]
  rw [x3₆, add_ofNat_zero] at t0
  rw [x3₆] at t8
  simp only [Spec.Poly1305.mac]
  rw [← repr_key hrep, clamp_key, key_drop, leNum_key, Poly1305.accumulate_append hrep.1,
    repr_acc hrep]
  refine Poly1305.bytesAt_leBytes_16 _ _ _ ?_ ?_
  · rw [t0]; exact q0
  · rw [t8]; exact q1

/-! ## The whole function -/

theorem finalize_correct {s₀ : State} (hp : FPre s₀) :
    WP isa finalize s₀ (Proof.Poly1305.finalizeAArch64.post s₀) := by
  refine WP.seq (WP.mono (setup_ok s₀ (by rw [hp.wr]; exact List.mem_cons_self)) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (Q := Tail s₀ s₁.mem s₁) ?_ fun s₂ h₂ => fepilogue_ok hp h₁ h₂)
  have x2₁ : s₁.gpr .x2 = s₀.gpr .x2 := h₁.gpr .x2 (by decide)
  refine WP.ite (s₁.read .x .x2 == 0) rfl (fun h => ?_) (fun h => ?_)
  · have h0 : tl s₀ = 0 := by
      simp only [State.read, Size.bits, BitVec.setWidth_eq, x2₁, beq_iff_eq] at h
      simp [tl, h]
    refine WP.block_nil (M := isa) ⟨fun r _ => rfl, h₁.rd, h₁.wr, Frame.refl _ _, fun hA => ?_⟩
    obtain ⟨e, b⟩ := h₁.acc hA
    refine ⟨?_, b⟩
    rw [tail_nil h0, Poly1305.absorbAll_nil, e]
  · have hpos : 0 < tl s₀ := by
      simp only [State.read, Size.bits, BitVec.setWidth_eq, x2₁, beq_eq_false_iff_ne, ne_eq] at h
      exact Nat.pos_of_ne_zero fun h' => h (BitVec.eq_of_toNat_eq (by simpa using h'))
    exact lastBlock_ok hp h₁ hpos

/-- A state satisfying the precondition (with no tail). -/
def finalizeSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x3 => 0x3000 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, 128⟩, ⟨0x3000, 16⟩]

theorem finalize_untouched : Untouched Impl.Poly1305.AArch64.finalize :=
  Untouched.of_all (by rw [← Code.allInstrs_eq]; decide +kernel)

theorem finalize_verified :
    Verified AArch64.target Impl.Poly1305.AArch64.finalize Proof.Poly1305.finalizeAArch64 := by
  refine ⟨fun s hs => ?_, ?_, ?_⟩
  · obtain ⟨t, s', he, h⟩ := finalize_correct (FPre.of s hs)
    exact ⟨t, s', he, ⟨fun r hr => Exec.gpr (finalize_untouched r hr) he, Exec.sp he⟩, h⟩
  · refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3]) ?_
      (by taint_decide)
    intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, hsp⟩
    refine ⟨hsp, fun r hr => ?_⟩
    simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> assumption
  · refine ⟨finalizeSat, rfl, rfl, ?_, ?_, ?_, by decide⟩ <;>
    · intro a h₁ h₂
      simp only [Region.Contains, finalizeSat] at h₁ h₂
      bv_omega

end VG.Proof.Poly1305.AArch64
