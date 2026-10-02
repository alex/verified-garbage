import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Calls
import VerifiedGarbage.Proof.MdStream.X86_64.Common
import VerifiedGarbage.Proof.Framework.OffsetBelow
import VerifiedGarbage.Proof.Hmac.Generic.Common
import Mathlib.Tactic.Set
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OmegaLit

/-!
# HMAC and PBKDF2-HMAC over any Merkle–Damgård hash function on x86-64: what the proofs share

The byte copy (`copy`), used for states, digests and `U`, a loop that counts
`r14` up from 0 and ends when it reaches its bound; the registers of our
caller, stored in `scratch` after the working space of the functions we call
(`Stream.saved`) and loaded back at the end; and facts about two runs.
-/

namespace VG.Proof.Pbkdf2.Md.X86_64.Calls

open VG.X86_64
open VG.Impl.Pbkdf2.Md.X86_64 (Stream byteAt copy)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_append writeBytes_nil writeW8_apply)
open VG.Proof.Sha256.X86_64 (toNat_ofNat_lt ofInt_natCast)
open VG.Proof.Sha256.X86_64.Stream (Upd wp_mov32i wp_addi wp_cmp wp_cmpi wp_movzx8 wp_store8
  ofNat_succ sub_beq)
open VG.Proof.Hmac.Common (bytesAt_length)
open VG.Proof.Hmac.Generic.Common (writeBytes_snoc bytesAt_snoc' not_mem_of_disjoint)
open Spec.Sha256 (bytesAt)

/-! ## Arithmetic -/

theorem zx_ofNat {n : Nat} (h : n < 2 ^ 32) : (BitVec.ofNat 32 n).setWidth 64 = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega_nat

theorem sx_ofNat {n : Nat} (h : n < 2 ^ 31) : (BitVec.ofNat 32 n).signExtend 64 = BitVec.ofNat 64 n := by
  rw [BitVec.signExtend_eq_setWidth_of_msb_false (by
    simp only [BitVec.msb_eq_decide, BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega_nat)]
  exact zx_ofNat (by omega_nat)

theorem sx_one : (1 : BitVec 32).signExtend 64 = 1 := by decide

theorem ea_byteAt (s : State) (b : Reg) (o k : Nat) (h14 : s.gpr .r14 = BitVec.ofNat 64 k) :
    s.ea (byteAt b o) = s.gpr b + BitVec.ofNat 64 o + BitVec.ofNat 64 k := by
  simp only [State.ea, byteAt, h14, ofInt_natCast, show BitVec.ofNat 64 1 = 1 from rfl]
  ac_rfl

/-! ## Counted loops -/

/-- A do-while loop over `ne` that runs its body `n > 0` times, with ZF set
exactly on the last iteration. -/
theorem count_loop {body : Prog isa} {n : Nat} (hn : 0 < n) (I : Nat → State → Prop)
    (hstep : ∀ k < n, ∀ s, I k s →
      WP isa body s fun s' => I (k + 1) s' ∧ s'.zf = some (decide (k + 1 = n)))
    {s : State} (h0 : I 0 s) : WP isa (.loop body .ne) s (I n) := by
  refine WP.loop (M := isa) (fun m s => ∃ k, m = n - k ∧ k < n ∧ I k s) ?_ n s ⟨0, by omega_nat, hn, h0⟩
  rintro m s ⟨k, rfl, hk, hi⟩
  refine WP.mono (hstep k hk s hi) fun s' ⟨hi', hz⟩ => ?_
  by_cases hl : k + 1 = n
  · exact .inl ⟨by simp [eval, hz, hl], hl ▸ hi'⟩
  · exact .inr ⟨by simp [eval, hz, hl], n - (k + 1), by omega_nat, k + 1, rfl, by omega_nat, hi'⟩

/-- `r14` counted up to `n`: the flags after `add r14, 1; cmp r14, n`. -/
theorem count_zf {k n : Nat} (hk : k < n) (hn : n < 2 ^ 31) :
    (BitVec.ofNat 64 k + (1 : BitVec 32).signExtend 64 - (BitVec.ofNat 32 n).signExtend 64 == 0) =
      decide (k + 1 = n) := by
  rw [sx_one, sx_ofNat hn, ← ofNat_succ, sub_beq (by omega_nat) (by omega_nat)]

/-! ## `copy` -/

/-- After `k` bytes of `copy` from `A` to `B`. -/
structure CopyInv (s : State) (A B : Addr) (k : Nat) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  other : ∀ r, r ≠ .rax → r ≠ .r14 → t.gpr r = s.gpr r
  r14 : t.gpr .r14 = BitVec.ofNat 64 k
  mem : t.mem = writeBytes s.mem B (bytesAt s.mem A k)

/-- The registers and memory `copy` leaves. -/
structure Copied (s : State) (B : Addr) (xs : List Byte) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  other : ∀ r, r ≠ .rax → r ≠ .r14 → t.gpr r = s.gpr r
  mem : t.mem = writeBytes s.mem B xs

theorem copy_ok {src dst : Reg} (hs : src ≠ .rax ∧ src ≠ .r14) (hd : dst ≠ .rax ∧ dst ≠ .r14)
    {so d n : Nat} (hn : 0 < n) (hn' : n < 2 ^ 31) {s : State}
    (hin : ∀ k < n, InRegions (s.rd ++ s.wr) (s.gpr src + BitVec.ofNat 64 so + BitVec.ofNat 64 k) 1)
    (hout : ∀ k < n, InRegions s.wr (s.gpr dst + BitVec.ofNat 64 d + BitVec.ofNat 64 k) 1)
    (hsep : Region.Disjoint ⟨s.gpr src + BitVec.ofNat 64 so, n⟩ ⟨s.gpr dst + BitVec.ofNat 64 d, n⟩) :
    WP isa (copy src so dst d n) s fun t =>
      Copied s (s.gpr dst + BitVec.ofNat 64 d) (bytesAt s.mem (s.gpr src + BitVec.ofNat 64 so) n) t := by
  set A := s.gpr src + BitVec.ofNat 64 so
  set B := s.gpr dst + BitVec.ofNat 64 d
  refine WP.seq (wp_mov32i fun s₀ u₀ _ _ => WP.block_nil ?_)
  have i0 : CopyInv s A B 0 s₀ :=
    ⟨u₀.rd, u₀.wr, fun r _ h => u₀.other r h, by rw [u₀.gpr]; rfl,
      by rw [u₀.mem, bytesAt, List.range_zero, List.map_nil, writeBytes_nil]⟩
  refine WP.mono (count_loop hn (CopyInv s A B) (fun k hk t h => ?_) i0)
    fun t h => ⟨h.rd, h.wr, h.other, h.mem⟩
  refine wp_movzx8 (a := A + BitVec.ofNat 64 k) (by rw [ea_byteAt _ _ _ _ h.r14, h.other _ hs.1 hs.2])
    (by rw [h.rd, h.wr]; exact hin k hk) fun t₁ u₁ => ?_
  refine wp_store8 (a := B + BitVec.ofNat 64 k)
    (by rw [ea_byteAt _ _ _ k (by rw [u₁.other _ (by decide), h.r14]), u₁.other _ hd.1,
      h.other _ hd.1 hd.2]) (by rw [u₁.wr, h.wr]; exact hout k hk) fun t₂ g₂ m₂ rd₂ wr₂ => ?_
  refine wp_addi fun t₃ u₃ => wp_cmpi fun t₄ g₄ m₄ rd₄ wr₄ _ z₄ => WP.block_nil ?_
  have h14 : t₃.gpr .r14 = BitVec.ofNat 64 k + (1 : BitVec 32).signExtend 64 := by
    rw [u₃.gpr, g₂, u₁.other _ (by decide), h.r14]
  refine ⟨⟨by rw [rd₄, u₃.rd, rd₂, u₁.rd, h.rd], by rw [wr₄, u₃.wr, wr₂, u₁.wr, h.wr],
    fun r ha h14' => by rw [g₄, u₃.other r h14', g₂, u₁.other r ha, h.other r ha h14'],
    by rw [g₄, h14, sx_one, ← ofNat_succ], ?_⟩, by rw [z₄, h14, count_zf hk hn']⟩
  have hl : (bytesAt s.mem A k).length = k := bytesAt_length _ _ _
  rw [m₄, u₃.mem, m₂, u₁.gpr, u₁.mem, h.mem, bytesAt_snoc']
  have e : writeBytes s.mem B (bytesAt s.mem A k) (A + BitVec.ofNat 64 k) = s.mem (A + BitVec.ofNat 64 k) := by
    simp only [writeBytes, hl, not_mem_of_disjoint hsep hk (Nat.le_of_lt hk) (by omega_nat), ↓reduceIte]
  have e' := writeBytes_snoc s.mem B (bytesAt s.mem A k) (s.mem (A + BitVec.ofNat 64 k)) (by rw [hl]; omega_nat)
  rw [hl] at e'
  rw [e, show ((s.mem (A + BitVec.ofNat 64 k)).setWidth 64).setWidth 8 = s.mem (A + BitVec.ofNat 64 k) by
    simp, e']


/-! ## Single instructions -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_xor32r {d r : Reg}
    (k : ∀ s', Upd s s' d (((s.gpr d).setWidth 32 ^^^ (s.gpr r).setWidth 32).setWidth 64) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.alu32 .xor d (.reg r) :: is)) s Q :=
  Proof.Sha256.X86_64.Stream.WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _))

theorem wp_mov32r {d r : Reg}
    (k : ∀ s', Upd s s' d (((s.gpr r).setWidth 32).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.mov32 d (.reg r) :: is)) s Q :=
  Proof.Sha256.X86_64.Stream.WP.cons rfl (k _ (Upd.setReg _ _ _))

theorem wp_xor32i {d : Reg} {v : BitVec 32}
    (k : ∀ s', Upd s s' d (((s.gpr d).setWidth 32 ^^^ v).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu32 .xor d (.imm v) :: is)) s Q :=
  Proof.Sha256.X86_64.Stream.WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _))

end

theorem xor_byte (b : Byte) (v : BitVec 32) :
    ((((b.setWidth 64).setWidth 32) ^^^ v).setWidth 64).setWidth 8 = b ^^^ v.setWidth 8 := by
  ext i hi
  simp [BitVec.getElem_setWidth, BitVec.getElem_xor]

end VG.Proof.Pbkdf2.Md.X86_64.Calls

/-!
# Our caller's registers

The six callee-saved registers we use are stored in `scratch` after the
working space of the functions we call (`Stream.saved`), and loaded back at
the end.
-/

namespace VG.Proof.Pbkdf2.Md.X86_64.Calls

open VG.X86_64
open VG.Impl.Pbkdf2.Md.X86_64 (Stream)
open VG.Impl.MdStream.X86_64 (at_)
open VG.Proof.MdStream.X86_64 (ea_at)
open VG.Proof.Sha256.X86_64 (ofInt_natCast contains_offset toNat_ofNat_lt)
open VG.Proof.Sha256.X86_64.Stream (Upd wp_store wp_movm)
open VG.Proof.Hmac.Generic.Common (readW_writeW_ne add_ofNat_add InRegions.right')

variable (H : Stream)

/-- Where the registers are saved. -/
abbrev saveR (scr : Addr) : Region := ⟨scr + BitVec.ofNat 64 (8 * H.W), 48⟩

/-- Slot `i` of the save area. -/
abbrev slot (scr : Addr) (i : Nat) : Addr := scr + BitVec.ofNat 64 (8 * H.W + 8 * i)

/-- The registers of `s₀` saved in the memory `m`. -/
structure SavedRegs (scr : Addr) (s₀ : State) (m : Mem) : Prop where
  rbx : m.readW (slot H scr 0) 64 = s₀.gpr .rbx
  rbp : m.readW (slot H scr 1) 64 = s₀.gpr .rbp
  r12 : m.readW (slot H scr 2) 64 = s₀.gpr .r12
  r13 : m.readW (slot H scr 3) 64 = s₀.gpr .r13
  r14 : m.readW (slot H scr 4) 64 = s₀.gpr .r14
  r15 : m.readW (slot H scr 5) 64 = s₀.gpr .r15

theorem slot_sub (scr : Addr) {i : Nat} (hi : i < 6) :
    Region.Sub ⟨slot H scr i, 8⟩ (saveR H scr) := by
  rw [slot, ← add_ofNat_add]
  exact Proof.Sha256.X86_64.sub_offset (by omega_nat) (by omega_nat)

theorem slot_disj (scr : Addr) {i j : Nat} (hi : i < 6) (hj : j < 6) (hij : i ≠ j) (hW : H.W ≤ 256) :
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
  have k : ∀ i < 6, m'.readW (slot H scr i) 64 = m.readW (slot H scr i) 64 := fun i hi =>
    hf.readW (r := ⟨slot H scr i, 8⟩) (Region.contains_self _ _)
      (fun r hr => (hd r hr).sub_left (slot_sub H scr hi)) (by decide)
  exact ⟨by rw [k 0 (by omega_nat), h.rbx], by rw [k 1 (by omega_nat), h.rbp], by rw [k 2 (by omega_nat), h.r12],
    by rw [k 3 (by omega_nat), h.r13], by rw [k 4 (by omega_nat), h.r14], by rw [k 5 (by omega_nat), h.r15]⟩

theorem ea_slot (s : State) (b : Reg) (scr : Addr) (hb : s.gpr b = scr) (i : Nat) :
    s.ea (at_ b (8 * H.W + 8 * i)) = slot H scr i := by
  rw [ea_at, ofInt_natCast, hb]

theorem slot_in {rs : List Region} {scr : Addr} {L : Nat} (h : ⟨scr, L⟩ ∈ rs) (hL : 8 * H.W + 48 ≤ L)
    (hW : H.W ≤ 256) {i : Nat} (hi : i < 6) : InRegions rs (slot H scr i) 8 :=
  ⟨_, h, contains_offset (by omega_nat) (by omega_nat)⟩

/-- Saving the registers, with `scratch` in `r8`. -/
theorem save_ok {s : State} {scr : Addr} {L : Nat} (h8 : s.gpr .r8 = scr) (hW : H.W ≤ 256)
    (hsc : ⟨scr, L⟩ ∈ s.wr) (hL : 8 * H.W + 48 ≤ L) {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr → Frame [saveR H scr] s.mem s'.mem →
      SavedRegs H scr s s'.mem → WP isa (.block rest) s' Q) :
    WP isa (.block (H.save ++ rest)) s Q := by
  have io : ∀ {t : State}, t.wr = s.wr → ∀ i < 6, InRegions t.wr (slot H scr i) 8 := fun hw i hi => by
    rw [hw]; exact slot_in H hsc hL hW hi
  have ea : ∀ {t : State}, t.gpr = s.gpr → ∀ i, t.ea (at_ .r8 (8 * H.W + 8 * i)) = slot H scr i :=
    fun hg i => by rw [ea_at, ofInt_natCast, hg, h8]
  simp only [Stream.save, Stream.saved, List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  refine wp_store (a := slot H scr 0) (ea rfl 0) (io rfl 0 (by omega_nat)) fun s₁ g₁ m₁ rd₁ wr₁ => ?_
  refine wp_store (a := slot H scr 1) (ea g₁ 1) (io wr₁ 1 (by omega_nat)) fun s₂ g₂ m₂ rd₂ wr₂ => ?_
  refine wp_store (a := slot H scr 2) (ea (g₂.trans g₁) 2) (io (wr₂.trans wr₁) 2 (by omega_nat))
    fun s₃ g₃ m₃ rd₃ wr₃ => ?_
  refine wp_store (a := slot H scr 3) (ea (g₃.trans (g₂.trans g₁)) 3) (io (wr₃.trans (wr₂.trans wr₁)) 3 (by omega_nat))
    fun s₄ g₄ m₄ rd₄ wr₄ => ?_
  refine wp_store (a := slot H scr 4) (ea (g₄.trans (g₃.trans (g₂.trans g₁))) 4)
    (io (wr₄.trans (wr₃.trans (wr₂.trans wr₁))) 4 (by omega_nat)) fun s₅ g₅ m₅ rd₅ wr₅ => ?_
  refine wp_store (a := slot H scr 5) (ea (g₅.trans (g₄.trans (g₃.trans (g₂.trans g₁)))) 5)
    (io (wr₅.trans (wr₄.trans (wr₃.trans (wr₂.trans wr₁)))) 5 (by omega_nat)) fun s₆ g₆ m₆ rd₆ wr₆ => ?_
  have g : s₆.gpr = s.gpr := g₆.trans (g₅.trans (g₄.trans (g₃.trans (g₂.trans g₁))))
  refine k s₆ g (by rw [rd₆, rd₅, rd₄, rd₃, rd₂, rd₁]) (by rw [wr₆, wr₅, wr₄, wr₃, wr₂, wr₁]) ?_ ?_
  · rw [m₆, m₅, m₄, m₃, m₂, m₁]
    have c : ∀ i < 6, (saveR H scr).Contains (slot H scr i) (64 / 8) := fun i hi => by
      rw [slot, ← add_ofNat_add]; exact contains_offset (by omega_nat) (by omega_nat)
    exact (((((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 0 (by omega_nat))).writeW
      (List.mem_singleton_self _) _ (c 1 (by omega_nat))).writeW (List.mem_singleton_self _) _
      (c 2 (by omega_nat))).writeW (List.mem_singleton_self _) _ (c 3 (by omega_nat))).writeW
      (List.mem_singleton_self _) _ (c 4 (by omega_nat))).writeW (List.mem_singleton_self _) _ (c 5 (by omega_nat)))
  · have d : ∀ i j, i < 6 → j < 6 → i ≠ j → Region.Disjoint ⟨slot H scr i, 8⟩ ⟨slot H scr j, 8⟩ :=
      fun i j hi hj hij => slot_disj H scr hi hj hij hW
    rw [m₆, m₅, m₄, m₃, m₂, m₁, g₅, g₄, g₃, g₂, g₁]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [readW_writeW_ne _ _ (d 0 5 (by omega_nat) (by omega_nat) (by omega_nat)),
        readW_writeW_ne _ _ (d 0 4 (by omega_nat) (by omega_nat) (by omega_nat)),
        readW_writeW_ne _ _ (d 0 3 (by omega_nat) (by omega_nat) (by omega_nat)),
        readW_writeW_ne _ _ (d 0 2 (by omega_nat) (by omega_nat) (by omega_nat)),
        readW_writeW_ne _ _ (d 0 1 (by omega_nat) (by omega_nat) (by omega_nat)), Mem.readW_writeW_self64]
    · rw [readW_writeW_ne _ _ (d 1 5 (by omega_nat) (by omega_nat) (by omega_nat)),
        readW_writeW_ne _ _ (d 1 4 (by omega_nat) (by omega_nat) (by omega_nat)),
        readW_writeW_ne _ _ (d 1 3 (by omega_nat) (by omega_nat) (by omega_nat)),
        readW_writeW_ne _ _ (d 1 2 (by omega_nat) (by omega_nat) (by omega_nat)), Mem.readW_writeW_self64]
    · rw [readW_writeW_ne _ _ (d 2 5 (by omega_nat) (by omega_nat) (by omega_nat)),
        readW_writeW_ne _ _ (d 2 4 (by omega_nat) (by omega_nat) (by omega_nat)),
        readW_writeW_ne _ _ (d 2 3 (by omega_nat) (by omega_nat) (by omega_nat)), Mem.readW_writeW_self64]
    · rw [readW_writeW_ne _ _ (d 3 5 (by omega_nat) (by omega_nat) (by omega_nat)),
        readW_writeW_ne _ _ (d 3 4 (by omega_nat) (by omega_nat) (by omega_nat)), Mem.readW_writeW_self64]
    · rw [readW_writeW_ne _ _ (d 4 5 (by omega_nat) (by omega_nat) (by omega_nat)), Mem.readW_writeW_self64]
    · rw [Mem.readW_writeW_self64]

/-- Loading them back, with `scratch` in `r15` (loaded last). -/
theorem restore_ok {s : State} {scr : Addr} {L : Nat} (h15 : s.gpr .r15 = scr) (hW : H.W ≤ 256) {s₀ : State}
    (hs : SavedRegs H scr s₀ s.mem) (hsc : ⟨scr, L⟩ ∈ s.wr) (hL : 8 * H.W + 48 ≤ L) :
    WP isa (.block H.restore) s fun s' => s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r ∈ [Reg.rbx, .rbp, .r12, .r13, .r14, .r15], s'.gpr r = s₀.gpr r) ∧
      (∀ r, r ∉ [Reg.rbx, .rbp, .r12, .r13, .r14, .r15] → s'.gpr r = s.gpr r) := by
  have io : ∀ {t : State}, t.rd = s.rd → t.wr = s.wr → ∀ i < 6, InRegions (t.rd ++ t.wr) (slot H scr i) 8 :=
    fun hr hw i hi => by rw [hr, hw]; exact InRegions.right' (slot_in H hsc hL hW hi)
  have ea : ∀ {t : State}, t.gpr .r15 = scr → ∀ i, t.ea (at_ .r15 (8 * H.W + 8 * i)) = slot H scr i :=
    fun h i => by rw [ea_at, ofInt_natCast, h]
  simp only [Stream.restore, Stream.saved, List.map_cons, List.map_nil]
  refine wp_movm (a := slot H scr 0) (ea h15 0) (io rfl rfl 0 (by omega_nat)) fun s₁ u₁ => ?_
  refine wp_movm (a := slot H scr 1) (ea (by rw [u₁.other _ (by decide), h15]) 1)
    (io u₁.rd u₁.wr 1 (by omega_nat)) fun s₂ u₂ => ?_
  refine wp_movm (a := slot H scr 2) (ea (by rw [u₂.other _ (by decide), u₁.other _ (by decide), h15]) 2)
    (io (u₂.rd.trans u₁.rd) (u₂.wr.trans u₁.wr) 2 (by omega_nat)) fun s₃ u₃ => ?_
  refine wp_movm (a := slot H scr 3) (ea (by rw [u₃.other _ (by decide), u₂.other _ (by decide),
    u₁.other _ (by decide), h15]) 3)
    (io (u₃.rd.trans (u₂.rd.trans u₁.rd)) (u₃.wr.trans (u₂.wr.trans u₁.wr)) 3 (by omega_nat)) fun s₄ u₄ => ?_
  refine wp_movm (a := slot H scr 4) (ea (by rw [u₄.other _ (by decide), u₃.other _ (by decide),
    u₂.other _ (by decide), u₁.other _ (by decide), h15]) 4)
    (io (u₄.rd.trans (u₃.rd.trans (u₂.rd.trans u₁.rd))) (u₄.wr.trans (u₃.wr.trans (u₂.wr.trans u₁.wr))) 4
      (by omega_nat)) fun s₅ u₅ => ?_
  refine wp_movm (a := slot H scr 5) (ea (by rw [u₅.other _ (by decide), u₄.other _ (by decide),
    u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h15]) 5)
    (io (u₅.rd.trans (u₄.rd.trans (u₃.rd.trans (u₂.rd.trans u₁.rd))))
      (u₅.wr.trans (u₄.wr.trans (u₃.wr.trans (u₂.wr.trans u₁.wr)))) 5 (by omega_nat)) fun s₆ u₆ => ?_
  refine WP.block_nil ⟨by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem],
    by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd], by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr],
    ?_, fun r hr => ?_⟩
  · have hm : ∀ t : State, t.mem = s.mem → ∀ i, t.mem.readW (slot H scr i) 64 = s.mem.readW (slot H scr i) 64 :=
      fun t h i => by rw [h]
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
        u₂.other _ (by decide), u₁.gpr, hs.rbx]
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
        u₂.gpr, u₁.mem, hs.rbp]
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.mem, u₁.mem,
        hs.r12]
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.mem, u₂.mem, u₁.mem, hs.r13]
    · rw [u₆.other _ (by decide), u₅.gpr, u₄.mem, u₃.mem, u₂.mem, u₁.mem, hs.r14]
    · rw [u₆.gpr, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem, hs.r15]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hr
    rw [u₆.other r h6, u₅.other r h5, u₄.other r h4, u₃.other r h3, u₂.other r h2, u₁.other r h1]


end VG.Proof.Pbkdf2.Md.X86_64.Calls

/-!
# States and two runs

A streaming state's representation moves with its bytes (`repr_keep`); and
HMAC's functions are constant time in two runs that agree on their public
arguments (`PubEq`), which are in the argument registers `args`.
-/

namespace VG.Proof.Pbkdf2.Md.X86_64.Calls

open VG.X86_64
open VG.Impl.Pbkdf2.Md.X86_64 (Stream)

variable {H : Stream} (hH : StreamOK H)

theorem repr_keep {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, H.S⟩ r) {msg : List Byte} (hr : hH.SH.Repr m p msg) :
    hH.SH.Repr m' p msg :=
  hH.repr _ _ _ _ _ (fun i hi => hf.bytes (R := ⟨p, H.S⟩) hd (by show H.S ≤ 2 ^ 64; have := hH.hSB; omega_nat) hi) hr

/-- The argument registers. -/
abbrev args : List Reg := [.rdi, .rsi, .rdx, .rcx, .r8, .rsp]

/-- The public arguments are the same. -/
structure PubEq (s₀ s₀' : State) : Prop where
  rdi : s₀.gpr .rdi = s₀'.gpr .rdi
  rsi : s₀.gpr .rsi = s₀'.gpr .rsi
  rdx : s₀.gpr .rdx = s₀'.gpr .rdx
  rcx : s₀.gpr .rcx = s₀'.gpr .rcx
  r8 : s₀.gpr .r8 = s₀'.gpr .r8
  rsp : s₀.gpr .rsp = s₀'.gpr .rsp

end VG.Proof.Pbkdf2.Md.X86_64.Calls
