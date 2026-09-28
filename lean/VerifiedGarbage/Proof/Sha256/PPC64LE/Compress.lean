import VerifiedGarbage.Proof.Sha256.PPC64LE.Rounds
import VerifiedGarbage.Proof.Sha256.PPC64LE.Contract
import VerifiedGarbage.Proof.Framework.Range

/-!
# SHA-256 compression function on PPC64LE: the whole function

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.Sha256.PPC64LE

open VG VG.PPC64LE VG.Impl.Sha256.PPC64LE
open VG.Spec.Sha256 (HashValue Word Block K W stateAt blockAt compressBlocks compress parseBlock)

/-! ## Addresses and regions -/

theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem contains_offset {base : Addr} {len off n : Nat} (h : off + n ≤ len) (ho : off < 2 ^ 64) :
    (⟨base, len⟩ : Region).Contains (base + BitVec.ofNat 64 off) n := by
  simp only [Region.Contains]
  rw [show base + BitVec.ofNat 64 off - base = BitVec.ofNat 64 off by bv_omega, toNat_ofNat_lt ho]
  exact h

theorem sub_offset {base : Addr} {off len len' : Nat} (h : off + len ≤ len') (ho : off < 2 ^ 64) :
    Region.Sub ⟨base + BitVec.ofNat 64 off, len⟩ ⟨base, len'⟩ := by
  intro a ha
  simp only [Region.Contains] at *
  have : (a - base).toNat ≤ (a - (base + BitVec.ofNat 64 off)).toNat + off := by
    rw [show a - base = (a - (base + BitVec.ofNat 64 off)) + BitVec.ofNat 64 off by bv_omega,
      BitVec.toNat_add, toNat_ofNat_lt ho]
    exact Nat.mod_le _ _
  omega

theorem word_sep (p : Addr) {j k : Nat} (hj : j < 8) (hk : k < 8) (h : j ≠ k) :
    Mem.Sep (p + BitVec.ofNat 64 (4 * j)) 4 (p + BitVec.ofNat 64 (4 * k)) 4 := by
  intro x hx hy
  bv_omega

theorem readW_writeW_word (m : Mem) (p : Addr) (v : Word) {j k : Nat} (hj : j < 8) (hk : k < 8)
    (h : j ≠ k) :
    (m.writeW (p + BitVec.ofNat 64 (4 * k)) v).readW (p + BitVec.ofNat 64 (4 * j)) 32 =
    m.readW (p + BitVec.ofNat 64 (4 * j)) 32 :=
  Mem.readW_writeW_sep (word_sep p hj hk h) (by decide)

theorem stateAt_eq {m : Mem} {p : Addr} {v : HashValue}
    (h : ∀ k : Nat, (hk : k < 8) → m.readW (p + BitVec.ofNat 64 (4 * k)) 32 = v[k]) :
    stateAt m p = v := by
  apply Vector.ext
  intro k hk
  simp only [stateAt, Vector.getElem_ofFn]
  exact h k hk

theorem stateAt_get (m : Mem) (p : Addr) {k : Nat} (hk : k < 8) :
    (stateAt m p)[k] = m.readW (p + BitVec.ofNat 64 (4 * k)) 32 := by
  simp only [stateAt, Vector.getElem_ofFn]

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev st : Addr := s₀.gpr .r3
abbrev bp : Addr := s₀.gpr .r4
abbrev nb : Nat := (s₀.gpr .r5).toNat
abbrev scr : Addr := s₀.gpr .r6
abbrev stR : Region := ⟨st s₀, 32⟩
abbrev blR : Region := ⟨bp s₀, 64 * nb s₀⟩
abbrev scrR : Region := ⟨scr s₀, 112⟩
abbrev H₀ : HashValue := stateAt s₀.mem (st s₀)
/-- Where the nonvolatile registers are saved. -/
abbrev savR : Region := ⟨scr s₀ + BitVec.ofNat 64 64, 48⟩
/-- Where nonvolatile register `i` is saved. -/
abbrev savAddr (i : Nat) : Addr := scr s₀ + BitVec.ofNat 64 (64 + 8 * i)

/-- Block `i`, and where it starts. -/
abbrev blkAddr (i : Nat) : Addr := bp s₀ + BitVec.ofNat 64 (64 * i)
abbrev blk (i : Nat) : Block := blockAt s₀.mem (blkAddr s₀ i)

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [blR s₀]
  wr : s₀.wr = [stR s₀, scrR s₀]
  st_scr : (stR s₀).Disjoint (scrR s₀)
  blk_st : (blR s₀).Disjoint (stR s₀)
  blk_scr : (blR s₀).Disjoint (scrR s₀)

theorem pre_of (s₀ : State) (h : Proof.Sha256.compressPPC64LE.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

namespace Pre
variable {s₀ : State} (h : Pre s₀)
include h

theorem nb_lt : 64 * nb s₀ < 2 ^ 64 := by
  by_contra hn
  refine h.blk_st (st s₀) ?_ (by simp [Region.Contains])
  simp only [Region.Contains]
  have := (st s₀ - bp s₀).isLt
  omega

theorem in_state {k : Nat} (hk : k < 8) :
    InRegions (s₀.rd ++ s₀.wr) (st s₀ + BitVec.ofNat 64 (4 * k)) 4 :=
  ⟨stR s₀, by simp [h.wr], contains_offset (by omega) (by omega)⟩

theorem out_state {k : Nat} (hk : k < 8) :
    InRegions s₀.wr (st s₀ + BitVec.ofNat 64 (4 * k)) 4 :=
  ⟨stR s₀, by simp [h.wr], contains_offset (by omega) (by omega)⟩

theorem in_slot (j : Nat) : InRegions (s₀.rd ++ s₀.wr) (slotAddr (scr s₀) j) 4 :=
  ⟨scrR s₀, by simp [h.wr], contains_offset (by simp only [slot]; omega) (by simp only [slot]; omega)⟩

theorem out_slot (j : Nat) : InRegions s₀.wr (slotAddr (scr s₀) j) 4 :=
  ⟨scrR s₀, by simp [h.wr], contains_offset (by simp only [slot]; omega) (by simp only [slot]; omega)⟩

theorem blk_contains {i t : Nat} (hi : i < nb s₀) (ht : t < 16) :
    (blR s₀).Contains (blkAddr s₀ i + BitVec.ofNat 64 (4 * t)) 4 := by
  have := h.nb_lt
  rw [show blkAddr s₀ i + BitVec.ofNat 64 (4 * t) =
    bp s₀ + BitVec.ofNat 64 (64 * i + 4 * t) by simp only [blkAddr]; bv_omega]
  exact contains_offset (by omega) (by omega)

theorem in_sav {i : Nat} (hi : i < 6) (rs : List Region) :
    InRegions (rs ++ s₀.wr) (scr s₀ + BitVec.ofNat 64 (64 + 8 * i)) 8 :=
  ⟨scrR s₀, by simp [h.wr], contains_offset (by omega) (by omega)⟩

theorem out_sav {i : Nat} (hi : i < 6) : InRegions s₀.wr (scr s₀ + BitVec.ofNat 64 (64 + 8 * i)) 8 :=
  ⟨scrR s₀, by simp [h.wr], contains_offset (by omega) (by omega)⟩

theorem in_blk {i t : Nat} (hi : i < nb s₀) (ht : t < 16) :
    InRegions (s₀.rd ++ s₀.wr) (blkAddr s₀ i + BitVec.ofNat 64 (4 * t)) 4 :=
  ⟨blR s₀, by simp [h.rd], h.blk_contains hi ht⟩

end Pre

/-! ## Saving and restoring the nonvolatile registers -/

/-- The nonvolatile registers the code does not use: never written. -/
def keepRegs : List Reg := [.r2, .r20, .r21, .r22, .r23, .r24, .r25, .r26, .r27, .r28, .r29, .r30,
  .r31]

theorem keepRegs_pub : ∀ r ∈ keepRegs, r ∈ pubRegs := by decide

/-- A preserved register is saved, or kept. -/
theorem preserved_cases : ∀ r ∈ preserved, (∃ i < 6, r = saved i) ∨ r ∈ keepRegs := by decide

theorem saved_inj {i j : Nat} (hi : i < 6) (hj : j < 6) (h : saved i = saved j) : i = j := by
  have key : ∀ i < 6, ∀ j < 6, saved i = saved j → i = j := by decide
  exact key i hi j hj h

theorem saved_ne {i : Nat} (hi : i < 6) : saved i ≠ .r3 ∧ saved i ≠ .r6 ∧ saved i ∉ keepRegs := by
  have key : ∀ i < 6, saved i ≠ .r3 ∧ saved i ≠ .r6 ∧ saved i ∉ keepRegs := by decide
  exact key i hi

theorem sav_sep (p : Addr) {i j : Nat} (hi : i < 6) (hj : j < 6) (h : i ≠ j) :
    Mem.Sep (p + BitVec.ofNat 64 (64 + 8 * i)) 8 (p + BitVec.ofNat 64 (64 + 8 * j)) 8 := by
  intro x hx hy
  bv_omega

theorem savR_sub (s₀ : State) : Region.Sub (savR s₀) (scrR s₀) := sub_offset (by omega) (by omega)

theorem win_sav (s₀ : State) : (winRegion (scr s₀)).Disjoint (savR s₀) := by
  intro a h₁ h₂
  simp only [Region.Contains] at h₁ h₂
  bv_omega

theorem sav_contains (s₀ : State) {i : Nat} (hi : i < 6) : (savR s₀).Contains (savAddr s₀ i) 8 := by
  simp only [Region.Contains]; bv_omega

/-- The first `n` registers are saved. -/
structure SI (s₀ : State) (n : Nat) (s : State) : Prop where
  gpr : s.gpr = s₀.gpr
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [savR s₀] s₀.mem s.mem
  saved : ∀ i < n, s.mem.readW (savAddr s₀ i) 64 = s₀.gpr (saved i)

theorem save_step {s₀ : State} (hp : Pre s₀) {n : Nat} (hn : n < 6) {s : State} (h : SI s₀ n s) :
    WP isa (.block [.store .d (saved n) .r6 (64 + 8 * n)]) s (SI s₀ (n + 1)) := by
  have hr6 : s.gpr .r6 = scr s₀ := by rw [h.gpr]
  have hout : InRegions s.wr (s.gpr .r6 + BitVec.ofNat 64 (64 + 8 * n)) 8 := by
    rw [h.wr, hr6]; exact hp.out_sav hn
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    exec_store_d (by decide) (show 64 + 8 * n < 2 ^ 15 ∧ (64 + 8 * n) % 4 = 0 by omega) hout,
    Option.some.injEq, exists_eq_left', hr6]
  refine ⟨h.gpr, h.rd, h.wr, h.frame.writeW (List.mem_singleton_self _) _ (sav_contains s₀ hn),
    fun i hi => ?_⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
  · rw [Mem.readW_writeW_sep (sav_sep _ (by omega) hn (by omega)) (by decide)]
    exact h.saved i hi
  · rw [Mem.readW_writeW_self64, h.gpr]

/-- The first `n` registers are restored, from the state `sB` the restoring
starts in. -/
structure RI (s₀ sB : State) (n : Nat) (s : State) : Prop where
  restored : ∀ i < n, s.gpr (saved i) = s₀.gpr (saved i)
  others : ∀ r, (∀ i < 6, r ≠ saved i) → s.gpr r = sB.gpr r
  mem : s.mem = sB.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem restore_step {s₀ sB : State} (hp : Pre s₀) (hr6 : sB.gpr .r6 = scr s₀)
    (hsav : ∀ i < 6, sB.mem.readW (savAddr s₀ i) 64 = s₀.gpr (saved i))
    {n : Nat} (hn : n < 6) {s : State} (h : RI s₀ sB n s) :
    WP isa (.block [.load .d (saved n) .r6 (64 + 8 * n)]) s (RI s₀ sB (n + 1)) := by
  have hr6' : s.gpr .r6 = scr s₀ := by
    rw [h.others _ fun i hi e => (saved_ne hi).2.1 e.symm, hr6]
  have hin : InRegions (s.rd ++ s.wr) (s.gpr .r6 + BitVec.ofNat 64 (64 + 8 * n)) 8 := by
    rw [h.rd, h.wr, hr6']; exact hp.in_sav hn _
  have hv : s.mem.readW (scr s₀ + BitVec.ofNat 64 (64 + 8 * n)) 64 = s₀.gpr (saved n) := by
    rw [h.mem]; exact hsav n hn
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    exec_load_d (by decide) (show 64 + 8 * n < 2 ^ 15 ∧ (64 + 8 * n) % 4 = 0 by omega) hin,
    Option.some.injEq, exists_eq_left', hr6', hv]
  refine ⟨fun i hi => ?_, fun r hr => ?_, h.mem, h.rd, h.wr⟩
  · simp only [State.write]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · have e : saved i ≠ saved n := fun e => absurd (saved_inj (by omega) hn e) (by omega)
      simp only [e, ite_false]; exact h.restored i hi
    · simp
  · simp only [State.write, hr n hn, ite_false]; exact h.others r hr

/-! ## The loop invariant -/

/-- What holds between blocks, after `i` of them. -/
structure Common (s₀ : State) (i : Nat) (s : State) : Prop where
  r3 : s.gpr .r3 = st s₀
  r6 : s.gpr .r6 = scr s₀
  kept : ∀ r ∈ keepRegs, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [stR s₀, scrR s₀] s₀.mem s.mem
  sav : ∀ i < 6, s.mem.readW (savAddr s₀ i) 64 = s₀.gpr (saved i)
  state : stateAt s.mem (st s₀) = compressBlocks (H₀ s₀) s₀.mem (bp s₀) i

/-- The loop invariant, at the start of block `i`. -/
structure LInv (s₀ : State) (i : Nat) (s : State) : Prop extends Common s₀ i s where
  r4 : s.gpr .r4 = blkAddr s₀ i
  r5 : s.gpr .r5 = BitVec.ofNat 64 (nb s₀ - i)

/-! ## One block -/

theorem load_eq : load = [
    .load .w .r7 .r3 (4 * 0), .load .w .r8 .r3 (4 * 1), .load .w .r9 .r3 (4 * 2),
    .load .w .r10 .r3 (4 * 3), .load .w .r11 .r3 (4 * 4), .load .w .r12 .r3 (4 * 5),
    .load .w .r14 .r3 (4 * 6), .load .w .r15 .r3 (4 * 7)] := by
  decide

theorem update_eq : update ++ advance = [
    .load .w .r16 .r3 (4 * 0), .load .w .r17 .r3 (4 * 1), .load .w .r18 .r3 (4 * 2),
    .load .w .r19 .r3 (4 * 3),
    .add .r7 .r7 .r16, .add .r8 .r8 .r17, .add .r9 .r9 .r18, .add .r10 .r10 .r19,
    .load .w .r16 .r3 (4 * (0 + 4)), .load .w .r17 .r3 (4 * (1 + 4)),
    .load .w .r18 .r3 (4 * (2 + 4)), .load .w .r19 .r3 (4 * (3 + 4)),
    .add .r11 .r11 .r16, .add .r12 .r12 .r17, .add .r14 .r14 .r18, .add .r15 .r15 .r19,
    .store .w .r7 .r3 (4 * 0), .store .w .r8 .r3 (4 * 1), .store .w .r9 .r3 (4 * 2),
    .store .w .r10 .r3 (4 * 3), .store .w .r11 .r3 (4 * 4), .store .w .r12 .r3 (4 * 5),
    .store .w .r14 .r3 (4 * 6), .store .w .r15 .r3 (4 * 7),
    .addi .r4 .r4 64, .subi .r5 .r5 1] := by
  decide

theorem vars0 (s : State) (v : HashValue) : Vars 0 s v ↔
    (s.gpr .r7).setWidth 32 = v[0] ∧ (s.gpr .r8).setWidth 32 = v[1] ∧
    (s.gpr .r9).setWidth 32 = v[2] ∧ (s.gpr .r10).setWidth 32 = v[3] ∧
    (s.gpr .r11).setWidth 32 = v[4] ∧ (s.gpr .r12).setWidth 32 = v[5] ∧
    (s.gpr .r14).setWidth 32 = v[6] ∧ (s.gpr .r15).setWidth 32 = v[7] := Iff.rfl

set_option simprocs false in
theorem load_ok {s₀ : State} (hp : Pre s₀) {s : State} (hr3 : s.gpr .r3 = st s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block load) s fun s₁ =>
      Vars 0 s₁ (stateAt s.mem (st s₀)) ∧ (∀ r ∈ pubRegs, s₁.gpr r = s.gpr r) ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr ∧ s₁.mem = s.mem := by
  have hin : ∀ k : Nat, k < 8 → InRegions (s.rd ++ s.wr) (st s₀ + BitVec.ofNat 64 (4 * k)) 4 := by
    rw [hrd, hwr]; exact fun k hk => hp.in_state hk
  have h0 := hin 0 (by decide); have h1 := hin 1 (by decide); have h2 := hin 2 (by decide)
  have h3 := hin 3 (by decide); have h4 := hin 4 (by decide); have h5 := hin 5 (by decide)
  have h6 := hin 6 (by decide); have h7 := hin 7 (by decide)
  apply WP.of_runBlock
  rw [load_eq]
  simp (config := {decide := true}) only [vars0, runBlock_cons, runStep_some,
    runBlock_nil, exec_load_w, isa, State.write, hr3,
    h0, h1, h2, h3, h4, h5, h6, h7, ite_true, ite_false, Option.some.injEq,
    exists_eq_left']
  simp only [stateAt_get _ _ (show 0 < 8 by decide), stateAt_get _ _ (show 1 < 8 by decide),
    stateAt_get _ _ (show 2 < 8 by decide), stateAt_get _ _ (show 3 < 8 by decide),
    stateAt_get _ _ (show 4 < 8 by decide), stateAt_get _ _ (show 5 < 8 by decide),
    stateAt_get _ _ (show 6 < 8 by decide), stateAt_get _ _ (show 7 < 8 by decide)]
  simp (config := {decide := true}) [pubRegs]

/-- Eight 32-bit words written to consecutive addresses. -/
def writeState (m : Mem) (p : Addr) (v : HashValue) : Mem :=
  ((((((((m.writeW (p + BitVec.ofNat 64 (4 * 0)) v[0]).writeW
    (p + BitVec.ofNat 64 (4 * 1)) v[1]).writeW
    (p + BitVec.ofNat 64 (4 * 2)) v[2]).writeW
    (p + BitVec.ofNat 64 (4 * 3)) v[3]).writeW
    (p + BitVec.ofNat 64 (4 * 4)) v[4]).writeW
    (p + BitVec.ofNat 64 (4 * 5)) v[5]).writeW
    (p + BitVec.ofNat 64 (4 * 6)) v[6]).writeW
    (p + BitVec.ofNat 64 (4 * 7)) v[7])

set_option simprocs false in
theorem stateAt_writeState (m : Mem) (p : Addr) (v : HashValue) : stateAt (writeState m p v) p = v := by
  apply stateAt_eq
  intro k hk
  simp only [writeState]
  interval_cases k <;>
  simp (config := {decide := true}) only [Mem.readW_writeW_self32, readW_writeW_word]

theorem frame_writeState {s₀ : State} {m m' : Mem} (h : Frame [stR s₀] m m') (v : HashValue) :
    Frame [stR s₀] m (writeState m' (st s₀) v) := by
  have c : ∀ k, k < 8 → (stR s₀).Contains (st s₀ + BitVec.ofNat 64 (4 * k)) (32 / 8) :=
    fun k hk => contains_offset (by omega) (by omega)
  simp only [writeState]
  refine (((((((h.writeW ?_ _ (c 0 ?_)).writeW ?_ _ (c 1 ?_)).writeW ?_ _ (c 2 ?_)).writeW ?_ _
    (c 3 ?_)).writeW ?_ _ (c 4 ?_)).writeW ?_ _ (c 5 ?_)).writeW ?_ _ (c 6 ?_)).writeW ?_ _ (c 7 ?_) <;>
  simp

set_option simprocs false in
theorem update_ok {s₀ : State} (hp : Pre s₀) {s : State} (V H : HashValue) (hv : Vars 0 s V)
    (hr3 : s.gpr .r3 = st s₀) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hH : ∀ k : Nat, (hk : k < 8) → s.mem.readW (st s₀ + BitVec.ofNat 64 (4 * k)) 32 = H[k]) :
    WP isa (.block (update ++ advance)) s fun s' =>
      s'.mem = writeState s.mem (st s₀) (Vector.zipWith (· + ·) V H) ∧
      s'.gpr .r4 = s.gpr .r4 + 64 ∧ s'.gpr .r5 = s.gpr .r5 - 1 ∧
      s'.gpr .r3 = s.gpr .r3 ∧ s'.gpr .r6 = s.gpr .r6 ∧
      (∀ r ∈ keepRegs, s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hin : ∀ k : Nat, k < 8 → InRegions (s.rd ++ s.wr) (st s₀ + BitVec.ofNat 64 (4 * k)) 4 := by
    rw [hrd, hwr]; exact fun k hk => hp.in_state hk
  have hout : ∀ k : Nat, k < 8 → InRegions s.wr (st s₀ + BitVec.ofNat 64 (4 * k)) 4 := by
    rw [hwr]; exact fun k hk => hp.out_state hk
  have i0 := hin 0 (by decide); have i1 := hin 1 (by decide); have i2 := hin 2 (by decide)
  have i3 := hin 3 (by decide); have i4 := hin (0 + 4) (by decide); have i5 := hin (1 + 4) (by decide)
  have i6 := hin (2 + 4) (by decide); have i7 := hin (3 + 4) (by decide)
  have o0 := hout 0 (by decide); have o1 := hout 1 (by decide); have o2 := hout 2 (by decide)
  have o3 := hout 3 (by decide); have o4 := hout 4 (by decide); have o5 := hout 5 (by decide)
  have o6 := hout 6 (by decide); have o7 := hout 7 (by decide)
  have m0 := hH 0 (by decide); have m1 := hH 1 (by decide); have m2 := hH 2 (by decide)
  have m3 := hH 3 (by decide); have m4 := hH (0 + 4) (by decide); have m5 := hH (1 + 4) (by decide)
  have m6 := hH (2 + 4) (by decide); have m7 := hH (3 + 4) (by decide)
  rw [vars0] at hv
  obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7⟩ := hv
  apply WP.of_runBlock
  rw [update_eq]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some,
    runBlock_nil, exec_load_w, exec_store_w, exec_add, exec_addi, exec_subi, State.write, hr3,
    i0, i1, i2, i3, i4, i5, i6, i7, o0, o1, o2, o3, o4, o5, o6, o7, ite_true, ite_false,
    Option.some.injEq, exists_eq_left']
  simp (config := {decide := true}) only [lo32_add, BitVec.setWidth_setWidth_of_le,
    BitVec.setWidth_eq, m0, m1, m2, m3, m4, m5, m6, m7, v0, v1, v2, v3, v4, v5, v6, v7]
  refine ⟨?_, ?_⟩
  · simp only [writeState, Vector.getElem_zipWith]
  and_intros
  all_goals first
    | trivial
    | rfl
    | (intro r hr
       simp only [keepRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
       rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
       simp (config := {decide := true}))

theorem compressBlocks_succ (H : HashValue) (m : Mem) (p : Addr) (i : Nat) :
    compressBlocks H m p (i + 1) =
      compress (compressBlocks H m p i) (blockAt m (p + BitVec.ofNat 64 (64 * i))) := by
  simp [compressBlocks, List.range_succ, List.foldl_append]

theorem blk_word {s₀ : State} (i t : Nat) (ht : t < 16) :
    rev32 (s₀.mem.readW (blkAddr s₀ i + BitVec.ofNat 64 (4 * t)) 32) = W (blk s₀ i) t := by
  rw [W_lt _ ht, rev32_readW]
  simp only [blk, blockAt, parseBlock]
  rw [show blkAddr s₀ i + BitVec.ofNat 64 (4 * t) + 1 = blkAddr s₀ i + BitVec.ofNat 64 (4 * t + 1) by
      bv_omega,
    show blkAddr s₀ i + BitVec.ofNat 64 (4 * t + 1) + 1 = blkAddr s₀ i + BitVec.ofNat 64 (4 * t + 2) by
      bv_omega,
    show blkAddr s₀ i + BitVec.ofNat 64 (4 * t + 2) + 1 = blkAddr s₀ i + BitVec.ofNat 64 (4 * t + 3) by
      bv_omega]

theorem win_sub (p : Addr) : Region.Sub (winRegion p) ⟨p, 112⟩ := Region.sub_prefix (by omega)

theorem body_ok {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < nb s₀) {s : State}
    (hL : LInv s₀ i s) :
    WP isa body s fun s' =>
      (eval (.nonzero .d .r5) s' = some false ∧ Common s₀ (nb s₀) s') ∨
      (eval (.nonzero .d .r5) s' = some true ∧ i + 1 < nb s₀ ∧ LInv s₀ (i + 1) s') := by
  refine WP.seq (WP.mono (load_ok hp hL.r3 hL.rd hL.wr) fun s₁ ⟨hv₁, hpub₁, hrd₁, hwr₁, hm₁⟩ => ?_)
  have hwin : ∀ r' ∈ [winRegion (scr s₀)], (blR s₀).Disjoint r' := by
    simpa using Region.Disjoint.sub_right hp.blk_scr (win_sub _)
  have hblk : ∀ m, Frame [winRegion (scr s₀)] s₁.mem m → ∀ t : Nat, t < 16 →
      rev32 (m.readW (blkAddr s₀ i + BitVec.ofNat 64 (4 * t)) 32) = W (blk s₀ i) t := by
    intro m hm t ht
    rw [hm.readW (hp.blk_contains hi ht) hwin (by decide), hm₁,
      hL.frame.readW (hp.blk_contains hi ht) (by simpa using ⟨hp.blk_st, hp.blk_scr⟩) (by decide)]
    exact blk_word i t ht
  have hr4₁ : s₁.gpr .r4 = blkAddr s₀ i := (hpub₁ .r4 (by decide)).trans hL.r4
  have hr6₁ : s₁.gpr .r6 = scr s₀ := (hpub₁ .r6 (by decide)).trans hL.r6
  refine WP.seq (WP.mono (rounds_ok _ (blk s₀ i) _ (scr s₀) s₁ hr4₁ hr6₁
    (by rw [hrd₁, hwr₁, hL.rd, hL.wr]; exact hp.in_slot)
    (by rw [hwr₁, hL.wr]; exact hp.out_slot)
    (fun t ht => by rw [hrd₁, hwr₁, hL.rd, hL.wr]; exact hp.in_blk hi ht) hblk hv₁ 64 le_rfl)
    fun s₂ hR => ?_)
  have hst : ∀ r' ∈ [winRegion (scr s₀)], (stR s₀).Disjoint r' := by
    simpa using Region.Disjoint.sub_right hp.st_scr (win_sub _)
  have pub₂ : ∀ r ∈ pubRegs, s₂.gpr r = s.gpr r := fun r hr => by
    rw [hR.pub r hr, hpub₁ r hr]
  have hr3₂ : s₂.gpr .r3 = st s₀ := by rw [pub₂ .r3 (by decide), hL.r3]
  refine WP.mono (update_ok hp _ (stateAt s.mem (st s₀)) hR.vars hr3₂
    (by rw [hR.rd, hrd₁, hL.rd]) (by rw [hR.wr, hwr₁, hL.wr]) fun k hk => ?_) fun s₃ h₃ => ?_
  · rw [hR.frame.readW (contains_offset (by omega) (by omega)) hst (by decide), hm₁,
      stateAt_get _ _ hk]
  obtain ⟨hm₃, hr4₃, hr5₃, hr3₃, hr6₃, hkept₃, hrd₃, hwr₃⟩ := h₃
  have hr5 : s₂.gpr .r5 - 1 = BitVec.ofNat 64 (nb s₀ - (i + 1)) := by
    rw [pub₂ .r5 (by decide), hL.r5]
    have := (s₀.gpr .r5).isLt
    bv_omega
  have hframe : Frame [stR s₀, scrR s₀] s₀.mem s₃.mem := by
    refine hL.frame.trans ?_
    rw [← hm₁]
    refine Frame.trans (hR.frame.sub fun r hr => ⟨scrR s₀, by simp, by simp at hr; subst hr; exact win_sub _⟩) ?_
    rw [hm₃]
    exact (frame_writeState (Frame.refl _ _) _).sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩
  have hsav : ∀ j < 6, s₃.mem.readW (savAddr s₀ j) 64 = s₀.gpr (saved j) := by
    intro j hj
    have hd : (savR s₀).Disjoint (stR s₀) :=
      Region.Disjoint.sub_left hp.st_scr.symm (savR_sub s₀)
    rw [hm₃, writeState]
    simp only [savAddr]
    iterate 8 rw [Mem.readW_writeW_sep (hd.sep (sav_contains s₀ hj) (contains_offset (by omega)
      (by omega))) (by decide)]
    rw [hR.frame.readW (r := savR s₀) (sav_contains s₀ hj) (by simpa using (win_sav s₀).symm)
      (by decide), hm₁]
    exact hL.sav j hj
  have hcommon : ∀ j, j = i + 1 → Common s₀ j s₃ := by
    rintro j rfl
    refine ⟨by rw [hr3₃, hr3₂], by rw [hr6₃, pub₂ .r6 (by decide), hL.r6],
      fun r hr => by rw [hkept₃ r hr, pub₂ r (keepRegs_pub r hr), hL.kept r hr],
      by rw [hrd₃, hR.rd, hrd₁, hL.rd], by rw [hwr₃, hR.wr, hwr₁, hL.wr], hframe, hsav, ?_⟩
    rw [hm₃, stateAt_writeState, compressBlocks_succ, ← hL.state]
    rfl
  have hev : eval (.nonzero .d .r5) s₃ = some (BitVec.ofNat 64 (nb s₀ - (i + 1)) != 0) := by
    simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, hr5₃, hr5]
  have := hp.nb_lt
  by_cases hlast : i + 1 = nb s₀
  · left
    refine ⟨by rw [hev, hlast]; simp, hlast ▸ hcommon _ rfl⟩
  · right
    have hne : nb s₀ - (i + 1) ≠ 0 := by omega
    have h0 : BitVec.ofNat 64 (nb s₀ - (i + 1)) ≠ 0 := by
      intro h
      have h' := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h'
      exact hne h'
    refine ⟨by rw [hev]; simpa using h0, by omega, { hcommon _ rfl with r4 := ?_, r5 := ?_ }⟩
    · rw [hr4₃, pub₂ .r4 (by decide), hL.r4]
      simp only [blkAddr]
      bv_omega
    · rw [hr5₃, hr5]

/-! ## The whole function -/

theorem blocks_ok {s₀ : State} (hp : Pre s₀) {s₁ : State} (hc₀ : Common s₀ 0 s₁)
    (hr4 : s₁.gpr .r4 = bp s₀) (hr5 : s₁.gpr .r5 = s₀.gpr .r5) :
    WP isa blocks s₁ (Common s₀ (nb s₀)) := by
  refine WP.ite (s₁.gpr .r5 == 0) (by simp [eval, State.read]) (fun h => ?_) (fun h => ?_)
  · have h0 : nb s₀ = 0 := by simp [hr5] at h; simp [nb, h]
    exact WP.block_nil (M := isa) (h0 ▸ hc₀)
  · have hpos : 0 < nb s₀ := by
      simp only [beq_eq_false_iff_ne, ne_eq, hr5] at h
      exact Nat.pos_of_ne_zero fun h' => h (BitVec.eq_of_toNat_eq (by simpa using h'))
    let Inv : Nat → State → Prop := fun m s => ∃ i, m = nb s₀ - i ∧ i < nb s₀ ∧ LInv s₀ i s
    have hstep : ∀ m s, Inv m s → WP isa body s (fun s' =>
        (eval (.nonzero .d .r5) s' = some false ∧ Common s₀ (nb s₀) s') ∨
        (eval (.nonzero .d .r5) s' = some true ∧ ∃ m' < m, Inv m' s')) := by
      rintro m s ⟨i, rfl, hi, hL⟩
      refine WP.mono (body_ok hp hi hL) fun s' h => ?_
      rcases h with ⟨he, hc⟩ | ⟨he, hi', hL'⟩
      · exact .inl ⟨he, hc⟩
      · exact .inr ⟨he, nb s₀ - (i + 1), by omega, i + 1, rfl, hi', hL'⟩
    have hL₀ : LInv s₀ 0 s₁ :=
      { hc₀ with
        r4 := by simp [blkAddr, hr4]
        r5 := by simp [nb, hr5] }
    exact WP.loop (M := isa) Inv hstep (nb s₀) s₁ ⟨0, rfl, hpos, hL₀⟩

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa compress s₀ fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ Proof.Sha256.compressPPC64LE.post s₀ s' := by
  have hs₀ : SI s₀ 0 s₀ := ⟨rfl, rfl, rfl, Frame.refl _ _, fun _ h => absurd h (by omega)⟩
  have hsave : WP isa (.block save) s₀ (SI s₀ 6) := by
    unfold save
    exact wp_range_flatMap (M := isa) (SI s₀) (fun k s hk h => save_step hp hk h) 6 le_rfl s₀ hs₀
  refine WP.seq (WP.mono hsave fun s₁ h₁ => ?_)
  have hc₀ : Common s₀ 0 s₁ := by
    refine ⟨by rw [h₁.gpr], by rw [h₁.gpr], fun r _ => by rw [h₁.gpr], h₁.rd, h₁.wr,
      h₁.frame.sub fun r hr => ?_, h₁.saved, ?_⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scrR s₀, by simp, savR_sub s₀⟩
    · show stateAt s₁.mem (st s₀) = H₀ s₀
      apply stateAt_eq
      intro k hk
      rw [h₁.frame.readW (r := stR s₀) (contains_offset (by omega) (by omega))
        (by simpa using Region.Disjoint.sub_right hp.st_scr (savR_sub s₀)) (by decide),
        ← stateAt_get _ _ hk]
  refine WP.seq (WP.mono (blocks_ok hp hc₀ (by rw [h₁.gpr]) (by rw [h₁.gpr])) fun s₂ h₂ => ?_)
  have hr₀ : RI s₀ s₂ 0 s₂ := ⟨fun _ h => absurd h (by omega), fun _ _ => rfl, rfl, h₂.rd, h₂.wr⟩
  unfold restore
  refine WP.mono (wp_range_flatMap (M := isa) (RI s₀ s₂)
    (fun k s hk h => restore_step hp h₂.r6 h₂.sav hk h) 6 le_rfl s₂ hr₀) fun s' h => ⟨?_, ?_⟩
  · intro r hr
    rcases preserved_cases r hr with ⟨i, hi, rfl⟩ | hk
    · exact h.restored i hi
    · rw [h.others r fun i hi e => (saved_ne hi).2.2 (e ▸ hk), h₂.kept r hk]
  · show stateAt s'.mem (s₀.gpr .r3) = _
    rw [h.mem]
    exact h₂.state

/-- A state satisfying the precondition (with no blocks). -/
def satState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r6 => 0x3000 | _ => 0
  lr := 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x3000, 112⟩]

theorem compress_verified :
    Verified PPC64LE.target Impl.Sha256.PPC64LE.compress Proof.Sha256.compressPPC64LE := by
  refine ⟨fun s hs => ?_, ?_, ?_⟩
  · obtain ⟨t, s', he, h₁, h₂⟩ := correct (pre_of s hs)
    exact ⟨t, s', he, ⟨h₁, Exec.sp he, Exec.lr he (by decide +kernel)
      (by rw [← Code.allInstrs_eq]; decide +kernel)⟩, h₂⟩
  · refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6]) ?_ (by taint_decide)
    intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, hsp⟩
    refine ⟨hsp, fun r hr => ?_⟩
    simp only [VG.PPC64LE.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> assumption
  · refine ⟨satState, rfl, rfl, ?_, ?_, ?_⟩ <;>
    · intro a h₁ h₂
      simp only [Region.Contains, satState] at h₁ h₂
      bv_omega

end VG.Proof.Sha256.PPC64LE
