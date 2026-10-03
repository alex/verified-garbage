import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Calls
import VerifiedGarbage.Proof.Sha256.AArch64.Stream.Common
import VerifiedGarbage.Proof.Hmac.Generic.Common
import VerifiedGarbage.Proof.Framework.OmegaLit

/-!
# HMAC and PBKDF2-HMAC over any Merkle–Damgård hash function on AArch64: what the proofs share

As on x86-64 (`Proof/Pbkdf2/Md/X86_64/Common.lean`): instructions and
arithmetic, a loop counted in `x11` (the iterations left), on which it
branches; the registers of our caller and our return address, stored in
`scratch` after the working space of the functions we call (`Stream.saved`)
and loaded back at the end; and facts about two runs.
-/

namespace VG.Proof.Pbkdf2.Md.AArch64.Calls

open VG.AArch64
open VG.Proof.Sha256.Stream (writeBytes)
open VG.Proof.MdStream.AArch64 (toNat_ofNat_lt)
open VG.Proof.MdStream.AArch64 (Upd eval_nonzero)
open Spec.Sha256 (bytesAt)

/-! ## Instructions and arithmetic -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_eor {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n ^^^ s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .eor .x d n m :: is)) s Q :=
  Proof.MdStream.AArch64.WP.cons (s' := s.write .x d (s.gpr n ^^^ s.gpr m))
    (by simp [exec, State.read]) (k _ (Proof.MdStream.AArch64.Upd.write64 _ _ _))

end

theorem movz_ofNat {n : Nat} (h : n < 2 ^ 16) : (BitVec.ofNat 16 n).setWidth 64 = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega_nat

theorem sub_ofNat' {a b : Nat} (h : b ≤ a) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega_nat

theorem ofNat_ne_zero {a : Nat} (h : a < 2 ^ 64) : (BitVec.ofNat 64 a != 0) = decide (a ≠ 0) := by
  by_cases ha : a = 0
  · subst ha; rfl
  · have : BitVec.ofNat 64 a ≠ 0 := fun e => ha (by
      have := congrArg BitVec.toNat e; rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h] at this)
    rw [show (BitVec.ofNat 64 a != 0) = true from bne_iff_ne.mpr this]; simp [ha]
/-- The registers the loops write. -/
abbrev clob : List Reg := [.x9, .x10, .x11, .x12, .x13, .x24]

theorem nm {r : Reg} (h : r ∉ clob) (x : Reg) (hx : x ∈ clob := by decide) : r ≠ x :=
  fun e => h (e ▸ hx)

/-! ## Counted loops -/

/-- A do-while loop on `x11 ≠ 0` that runs its body `n > 0` times, with
`x11` the iterations left after each. -/
theorem count_loop {body : Prog isa} {n : Nat} (hn : 0 < n) (hn' : n < 2 ^ 64) (I : Nat → State → Prop)
    (hstep : ∀ k < n, ∀ s, I k s →
      WP isa body s fun s' => I (k + 1) s' ∧ s'.gpr .x11 = BitVec.ofNat 64 (n - (k + 1)))
    {s : State} (h0 : I 0 s) : WP isa (.loop body (.nonzero .x .x11)) s (I n) := by
  refine WP.loop (M := isa) (fun m s => ∃ k, m = n - k ∧ k < n ∧ I k s) ?_ n s ⟨0, by omega_nat, hn, h0⟩
  rintro m s ⟨k, rfl, hk, hi⟩
  refine WP.mono (hstep k hk s hi) fun s' h' => ?_
  obtain ⟨hi', hx⟩ := h'
  have hz : isa.eval (.nonzero .x .x11) s' = some (decide (n - (k + 1) ≠ 0)) := by
    show VG.AArch64.eval (.nonzero .x .x11) s' = _
    rw [eval_nonzero, hx, ofNat_ne_zero (by omega_nat)]
  by_cases hl : k + 1 = n
  · exact .inl ⟨by rw [hz]; simp [hl], hl ▸ hi'⟩
  · exact .inr ⟨by rw [hz]; simp; omega_nat, n - (k + 1), by omega_nat, k + 1, rfl, by omega_nat, hi'⟩


/-- After `k` bytes of a byte copy from `A` to `B`, counted in `x24`. -/
structure CopyInv (s : State) (A B : Addr) (k : Nat) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  other : ∀ r ∉ clob, t.gpr r = s.gpr r
  x24 : t.gpr .x24 = BitVec.ofNat 64 k
  mem : t.mem = writeBytes s.mem B (bytesAt s.mem A k)

end VG.Proof.Pbkdf2.Md.AArch64.Calls

/-!
# Our caller's registers

As on x86-64 (`Proof/Pbkdf2/Md/X86_64/Common.lean`): the six callee-saved
registers we use, and our return address `x30`, are stored in `scratch` after
the working space of the functions we call (`Stream.saved`), and loaded back
at the end, `x23` (which holds `scratch`) last.
-/

namespace VG.Proof.Pbkdf2.Md.AArch64.Calls

open VG.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Stream)
open VG.Proof.MdStream.AArch64 (contains_offset toNat_ofNat_lt)
open VG.Proof.MdStream.AArch64 (Upd Mupd wp_str wp_ldr)
open VG.Proof.Hmac.Generic.Common (readW_writeW_ne add_ofNat_add InRegions.right')

variable (H : Stream)

/-- The registers saved, in the order of their slots. -/
abbrev savedRegs : List Reg := [.x19, .x20, .x21, .x22, .x24, .x30, .x23]

/-- Where the registers are saved. -/
abbrev saveR (scr : Addr) : Region := ⟨scr + BitVec.ofNat 64 (8 * H.W), 56⟩

/-- Slot `i` of the save area. -/
abbrev slot (scr : Addr) (i : Nat) : Addr := scr + BitVec.ofNat 64 (8 * H.W + 8 * i)

/-- The registers of `s₀` saved in the memory `m`. -/
structure SavedRegs (scr : Addr) (s₀ : State) (m : Mem) : Prop where
  x19 : m.readW (slot H scr 0) 64 = s₀.gpr .x19
  x20 : m.readW (slot H scr 1) 64 = s₀.gpr .x20
  x21 : m.readW (slot H scr 2) 64 = s₀.gpr .x21
  x22 : m.readW (slot H scr 3) 64 = s₀.gpr .x22
  x24 : m.readW (slot H scr 4) 64 = s₀.gpr .x24
  x30 : m.readW (slot H scr 5) 64 = s₀.gpr .x30
  x23 : m.readW (slot H scr 6) 64 = s₀.gpr .x23

theorem slot_sub (scr : Addr) {i : Nat} (hi : i < 7) :
    Region.Sub ⟨slot H scr i, 8⟩ (saveR H scr) := by
  rw [slot, ← add_ofNat_add]
  exact Proof.MdStream.AArch64.sub_offset (by omega_nat) (by omega_nat)

theorem slot_disj (scr : Addr) {i j : Nat} (hi : i < 7) (hj : j < 7) (hij : i ≠ j) (hW : H.W ≤ 1024) :
    Region.Disjoint ⟨slot H scr i, 8⟩ ⟨slot H scr j, 8⟩ := by
  intro a h₁ h₂
  simp only [Region.Contains, slot] at h₁ h₂
  rw [← BitVec.sub_sub] at h₁ h₂
  generalize a - scr = y at h₁ h₂
  rw [BitVec.toNat_sub, toNat_ofNat_lt (by omega_nat)] at h₁ h₂
  have := y.isLt
  omega_nat

theorem SavedRegs.frame {scr : Addr} {s₀ : State} {m m' : Mem} (h : SavedRegs H scr s₀ m)
    {rs : List Region} (hf : Frame rs m m') (hd : ∀ r ∈ rs, (saveR H scr).Disjoint r) :
    SavedRegs H scr s₀ m' := by
  have k : ∀ i < 7, m'.readW (slot H scr i) 64 = m.readW (slot H scr i) 64 := fun i hi =>
    hf.readW (r := ⟨slot H scr i, 8⟩) (Region.contains_self _ _)
      (fun r hr => (hd r hr).sub_left (slot_sub H scr hi)) (by decide)
  exact ⟨by rw [k 0 (by omega_nat), h.x19], by rw [k 1 (by omega_nat), h.x20], by rw [k 2 (by omega_nat), h.x21],
    by rw [k 3 (by omega_nat), h.x22], by rw [k 4 (by omega_nat), h.x24], by rw [k 5 (by omega_nat), h.x30],
    by rw [k 6 (by omega_nat), h.x23]⟩

theorem slot_in {rs : List Region} {scr : Addr} {L : Nat} (h : ⟨scr, L⟩ ∈ rs) (hL : 8 * H.W + 56 ≤ L)
    (hW : H.W ≤ 1024) {i : Nat} (hi : i < 7) : InRegions rs (slot H scr i) 8 :=
  ⟨_, h, contains_offset (by omega_nat) (by omega_nat)⟩

theorem slot_eq (scr : Addr) {o : Nat} (i : Nat) (h : o = 8 * H.W + 8 * i) :
    scr + BitVec.ofNat 64 o = slot H scr i := by rw [h]

/-- Saving the registers, with `scratch` in `x4`. -/
theorem save_ok {s : State} {scr : Addr} {L : Nat} (h4 : s.gpr .x4 = scr) (hW : H.W ≤ 1024)
    (hsc : ⟨scr, L⟩ ∈ s.wr) (hL : 8 * H.W + 56 ≤ L) {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      Frame [saveR H scr] s.mem s'.mem → SavedRegs H scr s s'.mem → WP isa (.block rest) s' Q) :
    WP isa (.block (H.save ++ rest)) s Q := by
  have io : ∀ {t : State}, t.wr = s.wr → ∀ i < 7, InRegions t.wr (slot H scr i) 8 := fun hw i hi => by
    rw [hw]; exact slot_in H hsc hL hW hi
  have ho : ∀ i < 7, (8 * H.W + 8 * i) % 8 = 0 ∧ 8 * H.W + 8 * i < 4096 * 8 := fun i hi => by omega_nat
  have ea : ∀ {t : State}, t.gpr = s.gpr → ∀ {o : Nat} (i : Nat), o = 8 * H.W + 8 * i →
      t.gpr .x4 + BitVec.ofNat 64 o = slot H scr i := fun hg o i h => by rw [hg, h4, h]
  simp only [Stream.save, Stream.saved, List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  refine wp_str (a := slot H scr 0) (by have := ho 0 (by omega_nat); omega_nat) (ea rfl 0 (by omega_nat))
    (io rfl 0 (by omega_nat)) fun s₁ m₁ => ?_
  refine wp_str (a := slot H scr 1) (by have := ho 1 (by omega_nat); omega_nat) (ea m₁.gpr 1 (by omega_nat))
    (io m₁.wr 1 (by omega_nat)) fun s₂ m₂ => ?_
  have g₂ : s₂.gpr = s.gpr := m₂.gpr.trans m₁.gpr
  have w₂ : s₂.wr = s.wr := m₂.wr.trans m₁.wr
  refine wp_str (a := slot H scr 2) (by have := ho 2 (by omega_nat); omega_nat) (ea g₂ 2 (by omega_nat))
    (io w₂ 2 (by omega_nat)) fun s₃ m₃ => ?_
  have g₃ : s₃.gpr = s.gpr := m₃.gpr.trans g₂
  have w₃ : s₃.wr = s.wr := m₃.wr.trans w₂
  refine wp_str (a := slot H scr 3) (by have := ho 3 (by omega_nat); omega_nat) (ea g₃ 3 (by omega_nat))
    (io w₃ 3 (by omega_nat)) fun s₄ m₄ => ?_
  have g₄ : s₄.gpr = s.gpr := m₄.gpr.trans g₃
  have w₄ : s₄.wr = s.wr := m₄.wr.trans w₃
  refine wp_str (a := slot H scr 4) (by have := ho 4 (by omega_nat); omega_nat) (ea g₄ 4 (by omega_nat))
    (io w₄ 4 (by omega_nat)) fun s₅ m₅ => ?_
  have g₅ : s₅.gpr = s.gpr := m₅.gpr.trans g₄
  have w₅ : s₅.wr = s.wr := m₅.wr.trans w₄
  refine wp_str (a := slot H scr 5) (by have := ho 5 (by omega_nat); omega_nat) (ea g₅ 5 (by omega_nat))
    (io w₅ 5 (by omega_nat)) fun s₆ m₆ => ?_
  have g₆ : s₆.gpr = s.gpr := m₆.gpr.trans g₅
  have w₆ : s₆.wr = s.wr := m₆.wr.trans w₅
  refine wp_str (a := slot H scr 6) (by have := ho 6 (by omega_nat); omega_nat) (ea g₆ 6 (by omega_nat))
    (io w₆ 6 (by omega_nat)) fun s₇ m₇ => ?_
  refine k s₇ (m₇.gpr.trans g₆) (by rw [m₇.rd, m₆.rd, m₅.rd, m₄.rd, m₃.rd, m₂.rd, m₁.rd])
    (m₇.wr.trans w₆) (by rw [m₇.sp, m₆.sp, m₅.sp, m₄.sp, m₃.sp, m₂.sp, m₁.sp]) ?_ ?_
  · rw [m₇.mem, m₆.mem, m₅.mem, m₄.mem, m₃.mem, m₂.mem, m₁.mem]
    have c : ∀ i < 7, (saveR H scr).Contains (slot H scr i) (64 / 8) := fun i hi => by
      rw [slot, ← add_ofNat_add]; exact contains_offset (by omega_nat) (by omega_nat)
    exact ((((((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 0 (by omega_nat))).writeW
      (List.mem_singleton_self _) _ (c 1 (by omega_nat))).writeW (List.mem_singleton_self _) _
      (c 2 (by omega_nat))).writeW (List.mem_singleton_self _) _ (c 3 (by omega_nat))).writeW
      (List.mem_singleton_self _) _ (c 4 (by omega_nat))).writeW (List.mem_singleton_self _) _
      (c 5 (by omega_nat))).writeW (List.mem_singleton_self _) _ (c 6 (by omega_nat)))
  · have d : ∀ i j, i < 7 → j < 7 → i ≠ j → Region.Disjoint ⟨slot H scr i, 8⟩ ⟨slot H scr j, 8⟩ :=
      fun i j hi hj hij => slot_disj H scr hi hj hij hW
    rw [m₇.mem, m₆.mem, m₅.mem, m₄.mem, m₃.mem, m₂.mem, m₁.mem, g₆, g₅, g₄, g₃, g₂, m₁.gpr]
    have w : ∀ i j, i < 7 → j < 7 → i ≠ j → ∀ (m : Mem) (v : BitVec 64),
        (m.writeW (slot H scr j) v).readW (slot H scr i) 64 = m.readW (slot H scr i) 64 :=
      fun i j hi hj hij m v => readW_writeW_ne _ _ (d i j hi hj hij)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [w 0 6 (by omega_nat) (by omega_nat) (by omega_nat), w 0 5 (by omega_nat) (by omega_nat) (by omega_nat),
        w 0 4 (by omega_nat) (by omega_nat) (by omega_nat), w 0 3 (by omega_nat) (by omega_nat) (by omega_nat),
        w 0 2 (by omega_nat) (by omega_nat) (by omega_nat), w 0 1 (by omega_nat) (by omega_nat) (by omega_nat),
        Mem.readW_writeW_self64]
    · rw [w 1 6 (by omega_nat) (by omega_nat) (by omega_nat), w 1 5 (by omega_nat) (by omega_nat) (by omega_nat),
        w 1 4 (by omega_nat) (by omega_nat) (by omega_nat), w 1 3 (by omega_nat) (by omega_nat) (by omega_nat),
        w 1 2 (by omega_nat) (by omega_nat) (by omega_nat), Mem.readW_writeW_self64]
    · rw [w 2 6 (by omega_nat) (by omega_nat) (by omega_nat), w 2 5 (by omega_nat) (by omega_nat) (by omega_nat),
        w 2 4 (by omega_nat) (by omega_nat) (by omega_nat), w 2 3 (by omega_nat) (by omega_nat) (by omega_nat),
        Mem.readW_writeW_self64]
    · rw [w 3 6 (by omega_nat) (by omega_nat) (by omega_nat), w 3 5 (by omega_nat) (by omega_nat) (by omega_nat),
        w 3 4 (by omega_nat) (by omega_nat) (by omega_nat), Mem.readW_writeW_self64]
    · rw [w 4 6 (by omega_nat) (by omega_nat) (by omega_nat), w 4 5 (by omega_nat) (by omega_nat) (by omega_nat),
        Mem.readW_writeW_self64]
    · rw [w 5 6 (by omega_nat) (by omega_nat) (by omega_nat), Mem.readW_writeW_self64]
    · rw [Mem.readW_writeW_self64]

/-- Loading them back, with `scratch` in `x23` (loaded last). -/
theorem restore_ok {s : State} {scr : Addr} {L : Nat} (h23 : s.gpr .x23 = scr) (hW : H.W ≤ 1024) {s₀ : State}
    (hs : SavedRegs H scr s₀ s.mem) (hsc : ⟨scr, L⟩ ∈ s.wr) (hL : 8 * H.W + 56 ≤ L) :
    WP isa (.block H.restore) s fun s' => s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp ∧ (∀ r ∈ savedRegs, s'.gpr r = s₀.gpr r) ∧
      (∀ r, r ∉ savedRegs → s'.gpr r = s.gpr r) := by
  have io : ∀ {t : State}, t.rd = s.rd → t.wr = s.wr → ∀ i < 7, InRegions (t.rd ++ t.wr) (slot H scr i) 8 :=
    fun hr hw i hi => by rw [hr, hw]; exact InRegions.right' (slot_in H hsc hL hW hi)
  have ho : ∀ i < 7, (8 * H.W + 8 * i) % 8 = 0 ∧ 8 * H.W + 8 * i < 4096 * 8 := fun i hi => by omega_nat
  have ea : ∀ {t : State}, t.gpr .x23 = scr → ∀ {o : Nat} (i : Nat), o = 8 * H.W + 8 * i →
      t.gpr .x23 + BitVec.ofNat 64 o = slot H scr i := fun h o i ho => by rw [h, ho]
  simp only [Stream.restore, Stream.saved, List.map_cons, List.map_nil]
  refine wp_ldr (a := slot H scr 0) (by have := ho 0 (by omega_nat); omega_nat) (ea h23 0 (by omega_nat))
    (io rfl rfl 0 (by omega_nat)) fun s₁ u₁ => ?_
  refine wp_ldr (a := slot H scr 1) (by have := ho 1 (by omega_nat); omega_nat)
    (ea (by rw [u₁.other _ (by decide), h23]) 1 (by omega_nat)) (io u₁.rd u₁.wr 1 (by omega_nat)) fun s₂ u₂ => ?_
  refine wp_ldr (a := slot H scr 2) (by have := ho 2 (by omega_nat); omega_nat)
    (ea (by rw [u₂.other _ (by decide), u₁.other _ (by decide), h23]) 2 (by omega_nat))
    (io (u₂.rd.trans u₁.rd) (u₂.wr.trans u₁.wr) 2 (by omega_nat)) fun s₃ u₃ => ?_
  refine wp_ldr (a := slot H scr 3) (by have := ho 3 (by omega_nat); omega_nat)
    (ea (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h23]) 3 (by omega_nat))
    (io (u₃.rd.trans (u₂.rd.trans u₁.rd)) (u₃.wr.trans (u₂.wr.trans u₁.wr)) 3 (by omega_nat)) fun s₄ u₄ => ?_
  have r₄ : s₄.rd = s.rd := u₄.rd.trans (u₃.rd.trans (u₂.rd.trans u₁.rd))
  have w₄ : s₄.wr = s.wr := u₄.wr.trans (u₃.wr.trans (u₂.wr.trans u₁.wr))
  have x₄ : s₄.gpr .x23 = scr := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h23]
  refine wp_ldr (a := slot H scr 4) (by have := ho 4 (by omega_nat); omega_nat) (ea x₄ 4 (by omega_nat))
    (io r₄ w₄ 4 (by omega_nat)) fun s₅ u₅ => ?_
  refine wp_ldr (a := slot H scr 5) (by have := ho 5 (by omega_nat); omega_nat)
    (ea (by rw [u₅.other _ (by decide), x₄]) 5 (by omega_nat)) (io (u₅.rd.trans r₄) (u₅.wr.trans w₄) 5 (by omega_nat))
    fun s₆ u₆ => ?_
  refine wp_ldr (a := slot H scr 6) (by have := ho 6 (by omega_nat); omega_nat)
    (ea (by rw [u₆.other _ (by decide), u₅.other _ (by decide), x₄]) 6 (by omega_nat))
    (io (u₆.rd.trans (u₅.rd.trans r₄)) (u₆.wr.trans (u₅.wr.trans w₄)) 6 (by omega_nat)) fun s₇ u₇ => ?_
  refine WP.block_nil ⟨by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem],
    by rw [u₇.rd, u₆.rd, u₅.rd, r₄], by rw [u₇.wr, u₆.wr, u₅.wr, w₄],
    by rw [u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp], ?_, fun r hr => ?_⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
        u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hs.x19]
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
        u₃.other _ (by decide), u₂.gpr, u₁.mem, hs.x20]
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
        u₃.gpr, u₂.mem, u₁.mem, hs.x21]
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.mem, u₂.mem,
        u₁.mem, hs.x22]
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.mem, u₃.mem, u₂.mem, u₁.mem, hs.x24]
    · rw [u₇.other _ (by decide), u₆.gpr, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem, hs.x30]
    · rw [u₇.gpr, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem, hs.x23]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hr
    rw [u₇.other r h7, u₆.other r h6, u₅.other r h5, u₄.other r h4, u₃.other r h3, u₂.other r h2,
      u₁.other r h1]


end VG.Proof.Pbkdf2.Md.AArch64.Calls

/-!
# States and two runs

A streaming state's representation moves with its bytes (`repr_keep`); the
callee-saved registers `x25`–`x28` are never written (`untouched`); and HMAC's
functions are constant time in two runs that agree on their public arguments
(`PubEq`), which are in the argument registers `args`.
-/

namespace VG.Proof.Pbkdf2.Md.AArch64.Calls

open VG.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Stream)

variable {H : Stream} (hH : StreamOK H)

theorem repr_keep {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, H.S⟩ r) {msg : List Byte} (hr : hH.SH.Repr m p msg) :
    hH.SH.Repr m' p msg :=
  hH.repr _ _ _ _ _ (fun i hi => hf.bytes (R := ⟨p, H.S⟩) hd (by show H.S ≤ 2 ^ 64; have := hH.hSB; omega_nat) hi) hr

/-- The callee-saved registers we never write. -/
abbrev untouched : List Reg := [.x25, .x26, .x27, .x28]

/-- The argument registers. -/
abbrev args : List Reg := [.x0, .x1, .x2, .x3, .x4]

/-- The public arguments are the same. -/
structure PubEq (s₀ s₀' : State) : Prop where
  x0 : s₀.gpr .x0 = s₀'.gpr .x0
  x1 : s₀.gpr .x1 = s₀'.gpr .x1
  x2 : s₀.gpr .x2 = s₀'.gpr .x2
  x3 : s₀.gpr .x3 = s₀'.gpr .x3
  x4 : s₀.gpr .x4 = s₀'.gpr .x4
  sp : s₀.sp = s₀'.sp

end VG.Proof.Pbkdf2.Md.AArch64.Calls
