import VerifiedGarbage.Proof.ChaCha20.Arm.Block
import VerifiedGarbage.Proof.ChaCha20.Keystream
import VerifiedGarbage.Proof.Framework.Arm.Call
import VerifiedGarbage.Proof.MdStream.Arm.Common
import VerifiedGarbage.Impl.ChaCha20.Arm.Xor
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.ChaCha20.Arm.Lit
import VerifiedGarbage.Proof.Framework.Omega

/-!
# ChaCha20 keystream XOR on ARMv7

The per-instruction WP rules are those of the streaming hash proofs
(`Proof/MdStream/Arm/Common.lean`).

The call of the block function goes through its `Verified` proof
(`WP.call`): it keeps `r1` (which its code never writes) and `r4`–`r11`,
so the loop's variables survive it, and changes memory only in the first
256 bytes of `buf`. The block function writes `r7`–`r11`, so that the code
keeps our caller's values of those is part of the invariants (`Keep`).

For constant time, the taint analysis runs through the block function's
code too: its saves and restores of `r4`–`r6` (our public pointers and
length) are public slots of `buf`, which needs lower bounds on the lengths
of all three writable regions, `0` for the data (`τ₀`).
-/

namespace VG.Proof.ChaCha20

open Spec.ChaCha20 VG.Arm

/-- The contract the proof is written against (and verified callers use); the
artifact's is the shared contract of `Spec/`, which implies it.
32-bit ARM contract for
`vg_chacha20_xor(state: *mut [u32; 16], data: *mut u8, len: usize, buf: *mut [u32; 80])`:
XORs the first `len` bytes of the keystream of the state at `state` into the
`len` bytes at `data`.

The code may read and write `state` (64 bytes; its contents on exit are
unspecified), `data` (`len` bytes) and `buf` (320 bytes of working space).
They may not overlap each other, and none may wrap around the end of the
(32-bit) address space. The return address is in `lr`, not on the stack, and
the code uses no stack. The pointers and the length are public; the state and
the data are secret. -/
def xorArm : Contract Arm.isa where
  pre s :=
    let state : Region := ⟨State.addr (s.gpr .r0), 64⟩
    let data : Region := ⟨State.addr (s.gpr .r1), (s.gpr .r2).toNat⟩
    let buf : Region := ⟨State.addr (s.gpr .r3), 320⟩
    s.rd = [] ∧ s.wr = [state, data, buf] ∧
    state.Disjoint data ∧ state.Disjoint buf ∧ data.Disjoint buf ∧
    (s.gpr .r0).toNat + 64 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + (s.gpr .r2).toNat ≤ 2 ^ 32 ∧
    (s.gpr .r3).toNat + 320 ≤ 2 ^ 32
  post s s' :=
    bytesAt s'.mem (State.addr (s.gpr .r1)) (s.gpr .r2).toNat =
      List.zipWith (· ^^^ ·) (bytesAt s.mem (State.addr (s.gpr .r1)) (s.gpr .r2).toNat)
        (keystream (stateAt s.mem (State.addr (s.gpr .r0))) (s.gpr .r2).toNat)
  pub s₁ s₂ :=
    s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
    s₁.gpr .r3 = s₂.gpr .r3

end VG.Proof.ChaCha20

namespace VG.Proof.ChaCha20.Arm.Xor

open VG VG.Arm VG.Impl.ChaCha20.Arm.Xor
open VG.Proof.MdStream.Arm (Upd Mupd Fupd op2_imm op2_reg op2_lsr wp_mov wp_add wp_sub wp_subs
  wp_cmp wp_ldr wp_str wp_ldrb wp_strb eval_eq eval_ne ofNat_beq_zero sub_ofNat ofNat_shr)
open VG.Proof.ChaCha20 (ctr ctr_zero ctr_succ keystream_getD length_keystream bytesAt_xor
  serialize_stateAt)
open VG.Proof.ChaCha20.Arm (toNat_ofNat_lt contains_off readW_writeW_off block_correct)
open VG.Spec.ChaCha20 (stateAt keystream serialize bytesAt)

/-! ## One instruction at a time -/

theorem wp_eor {is : List Instr} {s : State} {Q : State → Prop} {d n : Reg} {o : Op2}
    {y : BitVec 32} (ho : o.eval s = some y)
    (k : ∀ s', Upd s s' d (s.gpr n ^^^ y) → WP isa (.block is) s' Q) :
    WP isa (.block (.dp .eor d n o :: is)) s Q :=
  VG.Proof.MdStream.Arm.WP.cons (s' := s.setReg d (s.gpr n ^^^ y)) (by simp [exec, ho])
    (k _ (Upd.setReg _ _ _))

theorem imm0 : encodable 0 = true := by decide
theorem imm1 : encodable 1 = true := by decide
theorem imm64 : encodable 64 = true := by decide

/-! ## Arithmetic -/

theorem add_zero' (x : BitVec 32) : x + 0 = x := by simp

theorem sub_zero' (x : BitVec 32) : x - 0 = x := by simp

theorem add_ofNat32 (p : BitVec 32) (a b : Nat) :
    p + BitVec.ofNat 32 a + BitVec.ofNat 32 b = p + BitVec.ofNat 32 (a + b) := by
  rw [BitVec.ofNat_add, BitVec.add_assoc]

theorem add_one' (p : BitVec 32) (a : Nat) :
    p + BitVec.ofNat 32 a + 1 = p + BitVec.ofNat 32 (a + 1) := by
  rw [show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, add_ofNat32]

theorem sub_one' {a : Nat} (h : 1 ≤ a) : BitVec.ofNat 32 a - 1 = BitVec.ofNat 32 (a - 1) := by
  rw [show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_ofNat h]

/-- `[x, #0]` with `x = p + k`, as a 64-bit address. -/
theorem ea0 {p : BitVec 32} {k : Nat} (h : p.toNat + k < 2 ^ 32) :
    State.addr (p + BitVec.ofNat 32 k + BitVec.ofNat 32 0) = State.addr p + BitVec.ofNat 64 k := by
  rw [show BitVec.ofNat 32 0 = 0 from rfl, add_zero']
  exact addr_add h

theorem addr_toNat (p : BitVec 32) : (State.addr p).toNat = p.toNat := by
  simp only [State.addr, BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (by have := p.isLt; omega)

/-- The byte stored by `eor r0, r0, r12; strb r0, …` after two `ldrb`s. -/
theorem xor_setWidth (a b : Byte) : ((a.setWidth 32 ^^^ b.setWidth 32).setWidth 8) = a ^^^ b := by
  ext i hi; simp

theorem eval_ne_ofNat (s : State) {k : Nat} (hk : k < 2 ^ 32) {x : BitVec 32}
    (hz : s.z = (x - 0 == 0)) (hx : x = BitVec.ofNat 32 k) : isa.eval .ne s = some (decide (k ≠ 0)) := by
  have e : isa.eval .ne s = some !s.z := eval_ne s
  rw [e, hz, hx, sub_zero', ofNat_beq_zero hk]
  simp

/-! ## The entry state -/

section
variable (s₀ : State)
abbrev stP : BitVec 32 := s₀.gpr .r0
abbrev dP : BitVec 32 := s₀.gpr .r1
abbrev L : Nat := (s₀.gpr .r2).toNat
abbrev bP : BitVec 32 := s₀.gpr .r3
abbrev stA : Addr := State.addr (stP s₀)
abbrev dA : Addr := State.addr (dP s₀)
abbrev bA : Addr := State.addr (bP s₀)
abbrev stRg : Region := ⟨stA s₀, 64⟩
abbrev dRg : Region := ⟨dA s₀, L s₀⟩
abbrev bRg : Region := ⟨bA s₀, 320⟩
/-- The state, the data and the keystream on entry. -/
abbrev S0 : CState := stateAt s₀.mem (stA s₀)
abbrev D0 (k : Nat) : Byte := s₀.mem (dA s₀ + BitVec.ofNat 64 k)
abbrev KS : List Byte := keystream (S0 s₀) (L s₀)
/-- The bytes of data done before block `j`. -/
abbrev P (j : Nat) : Nat := min (64 * j) (L s₀)
/-- How many bytes of block `j` are used. -/
abbrev C (j : Nat) : Nat := min 64 (L s₀ - P s₀ j)
end

theorem L_lt (s₀ : State) : L s₀ < 2 ^ 32 := (s₀.gpr .r2).isLt

structure XPre (s₀ : State) : Prop where
  rd : s₀.rd = []
  wr : s₀.wr = [stRg s₀, dRg s₀, bRg s₀]
  st_d : (stRg s₀).Disjoint (dRg s₀)
  st_b : (stRg s₀).Disjoint (bRg s₀)
  d_b : (dRg s₀).Disjoint (bRg s₀)
  st_fit : (stP s₀).toNat + 64 ≤ 2 ^ 32
  d_fit : (dP s₀).toNat + L s₀ ≤ 2 ^ 32
  b_fit : (bP s₀).toNat + 320 ≤ 2 ^ 32

theorem XPre.of (s₀ : State) (h : Proof.ChaCha20.xorArm.pre s₀) : XPre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

namespace XPre
variable {s₀ : State} (hp : XPre s₀)
include hp

theorem eaB {d : Nat} (h : d < 320) : State.addr (bP s₀ + BitVec.ofNat 32 d) = bA s₀ + BitVec.ofNat 64 d :=
  addr_add (by have := hp.b_fit; omega)

theorem eaS {d : Nat} (h : d < 64) : State.addr (stP s₀ + BitVec.ofNat 32 d) = stA s₀ + BitVec.ofNat 64 d :=
  addr_add (by have := hp.st_fit; omega)

theorem inB {d n : Nat} (h : d + n ≤ 320) (rd : List Region) {wr : List Region}
    (hw : wr = s₀.wr) : InRegions (rd ++ wr) (bA s₀ + BitVec.ofNat 64 d) n :=
  ⟨bRg s₀, by simp [hw, hp.wr], contains_off h (by lit_omega)⟩

theorem outB {d n : Nat} (h : d + n ≤ 320) {wr : List Region} (hw : wr = s₀.wr) :
    InRegions wr (bA s₀ + BitVec.ofNat 64 d) n :=
  ⟨bRg s₀, by simp [hw, hp.wr], contains_off h (by lit_omega)⟩

end XPre

/-- Our caller's `r4`, `r5`, `r6` and `lr`, saved in `buf[256, 272)`. -/
def XSaved (s₀ : State) (m : Mem) : Prop :=
  m.readW (bA s₀ + BitVec.ofNat 64 256) 32 = s₀.gpr .r4 ∧
  m.readW (bA s₀ + BitVec.ofNat 64 260) 32 = s₀.gpr .r5 ∧
  m.readW (bA s₀ + BitVec.ofNat 64 264) 32 = s₀.gpr .r6 ∧
  m.readW (bA s₀ + BitVec.ofNat 64 268) 32 = s₀.gpr .lr

/-- The callee-saved registers that the code keeps as they are (the block
function preserves them too). -/
def kept : List Reg := [.r7, .r8, .r9, .r10, .r11]

def Keep (s₀ s : State) : Prop := ∀ r ∈ kept, s.gpr r = s₀.gpr r

theorem Keep.upd {s₀ s s' : State} {d : Reg} {v : BitVec 32} (h : Keep s₀ s) (u : Upd s s' d v)
    (hd : d ∉ kept := by decide) : Keep s₀ s' :=
  fun r hr => by rw [u.other r (fun e => hd (e ▸ hr)), h r hr]

theorem Keep.mupd {s₀ s s' : State} {m : Mem} (h : Keep s₀ s) (u : Mupd s s' m) : Keep s₀ s' :=
  fun r hr => by rw [u.gpr, h r hr]

theorem Keep.fupd {s₀ s s' : State} (h : Keep s₀ s) (u : Fupd s s') : Keep s₀ s' :=
  fun r hr => by rw [u.gpr, h r hr]

/-- Before block `j`, but for the flags. -/
structure Inv (s₀ : State) (j : Nat) (s : State) : Prop where
  r1 : s.gpr .r1 = bP s₀
  r4 : s.gpr .r4 = stP s₀
  r5 : s.gpr .r5 = dP s₀ + BitVec.ofNat 32 (P s₀ j)
  r6 : s.gpr .r6 = BitVec.ofNat 32 (L s₀ - P s₀ j)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  keep : Keep s₀ s
  cnt : stateAt s.mem (stA s₀) = ctr (S0 s₀) j
  data : ∀ k < L s₀, s.mem (dA s₀ + BitVec.ofNat 64 k) =
    if k < P s₀ j then D0 s₀ k ^^^ (KS s₀).getD k 0 else D0 s₀ k
  saved : XSaved s₀ s.mem

/-- Before block `j` (the loop's invariant): `Z` says whether data remains. -/
structure OInv (s₀ : State) (j : Nat) (s : State) : Prop extends Inv s₀ j s where
  z : s.z = (s.gpr .r6 - 0 == 0)

/-! ## Memory -/

/-- The state after its counter (word 12) is stored. -/
theorem stateAt_writeW_counter (m : Mem) (p : Addr) (v : BitVec 32) :
    stateAt (m.writeW (p + BitVec.ofNat 64 48) v) p = (stateAt m p).set 12 v := by
  apply Vector.ext
  intro i hi
  simp only [stateAt, Vector.getElem_ofFn, Vector.getElem_set]
  by_cases h : 12 = i
  · subst h
    simp only [ite_true]
    exact Mem.readW_writeW_self32 _ _ _
  · simp only [h, ite_false]
    exact readW_writeW_off m p v (by lit_omega) (by lit_omega) (by lit_omega)

/-- A state in memory outside a frame is unchanged. -/
theorem stateAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (⟨p, 64⟩ : Region).Disjoint r) : stateAt m' p = stateAt m p := by
  apply Vector.ext
  intro i hi
  simp only [stateAt, Vector.getElem_ofFn]
  exact hf.readW (contains_off (by lit_omega) (by lit_omega)) hd (by decide)

/-- The first 256 bytes of `buf`, which the block function may write. -/
abbrev b256 (s₀ : State) : Region := ⟨bA s₀, 256⟩

/-- Where our caller's registers are saved. -/
abbrev savR (s₀ : State) : Region := ⟨bA s₀ + BitVec.ofNat 64 256, 16⟩

theorem b256_sub (s₀ : State) : Region.Sub (b256 s₀) (bRg s₀) := Region.sub_prefix (by lit_omega)

theorem savR_sub (s₀ : State) : Region.Sub (savR s₀) (bRg s₀) := Offset.sub_base _ (by lit_omega)

theorem savR_b256 (s₀ : State) : (savR s₀).Disjoint (b256 s₀) := Offset.disjoint_base _ (by lit_omega) (by lit_omega)

/-- The saved registers survive a frame that does not touch them. -/
theorem XSaved.frame {s₀ : State} {rs : List Region} {m m' : Mem} (h : XSaved s₀ m)
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (savR s₀).Disjoint r) : XSaved s₀ m' := by
  have c : ∀ d, 256 ≤ d → d + 4 ≤ 272 →
      (savR s₀).Contains (bA s₀ + BitVec.ofNat 64 d) (32 / 8) := by
    intro d h₁ h₂
    exact Offset.contains _ h₁ (by lit_omega) (by lit_omega)
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨by rw [hf.readW (c 256 (Nat.le_refl _) (by lit_omega)) hd (by decide), h1],
    by rw [hf.readW (c 260 (by lit_omega) (by lit_omega)) hd (by decide), h2],
    by rw [hf.readW (c 264 (by lit_omega) (by lit_omega)) hd (by decide), h3],
    by rw [hf.readW (c 268 (by lit_omega) (by lit_omega)) hd (by decide), h4]⟩

/-- Distinct bytes of the data are at distinct addresses. -/
theorem data_ne {s₀ : State} {k k' : Nat} (hk : k < L s₀) (hk' : k' < L s₀) (h : k' ≠ k) :
    dA s₀ + BitVec.ofNat 64 k' ≠ dA s₀ + BitVec.ofNat 64 k := by
  have hL := L_lt s₀
  intro he
  have e : BitVec.ofNat 64 k' = BitVec.ofNat 64 k := by
    have e := congrArg (· - dA s₀) he; simpa using e
  have := congrArg BitVec.toNat e
  rw [toNat_ofNat_lt (by lit_omega), toNat_ofNat_lt (by lit_omega)] at this
  exact h this

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
      rw [← BitVec.sub_add_cancel x a, this]; exact BitVec.zero_add a
    simp only [this, h, ↓reduceIte]

/-! ## The prologue -/

theorem save_eq : save ++ ([.mov .r4 (.reg .r0), .mov .r5 (.reg .r1), .mov .r6 (.reg .r2),
      .mov .r1 (.reg .r3), .cmp .r6 (.imm 0)] : List Instr) =
    [.str .r4 .r3 256, .str .r5 .r3 260, .str .r6 .r3 264, .str .lr .r3 268,
      .mov .r4 (.reg .r0), .mov .r5 (.reg .r1), .mov .r6 (.reg .r2), .mov .r1 (.reg .r3),
      .cmp .r6 (.imm 0)] := rfl

theorem prologue_ok {s₀ : State} (hp : XPre s₀) :
    WP isa (.block (save ++ ([.mov .r4 (.reg .r0), .mov .r5 (.reg .r1), .mov .r6 (.reg .r2),
      .mov .r1 (.reg .r3), .cmp .r6 (.imm 0)] : List Instr))) s₀ (OInv s₀ 0) := by
  rw [save_eq]
  refine wp_str (by decide) (hp.eaB (by lit_omega)) (hp.outB (by lit_omega) rfl) fun s₁ g₁ => ?_
  refine wp_str (by decide) (by rw [g₁.gpr]; exact hp.eaB (by lit_omega))
    (hp.outB (by lit_omega) g₁.wr) fun s₂ g₂ => ?_
  refine wp_str (by decide) (by rw [g₂.gpr, g₁.gpr]; exact hp.eaB (by lit_omega))
    (hp.outB (by lit_omega) (g₂.wr.trans g₁.wr)) fun s₃ g₃ => ?_
  refine wp_str (by decide) (by rw [g₃.gpr, g₂.gpr, g₁.gpr]; exact hp.eaB (by lit_omega))
    (hp.outB (by lit_omega) (g₃.wr.trans (g₂.wr.trans g₁.wr))) fun s₄ g₄ => ?_
  have gr : s₄.gpr = s₀.gpr := by rw [g₄.gpr, g₃.gpr, g₂.gpr, g₁.gpr]
  refine wp_mov (op2_reg _ _) fun s₅ u₅ => wp_mov (op2_reg _ _) fun s₆ u₆ =>
    wp_mov (op2_reg _ _) fun s₇ u₇ => wp_mov (op2_reg _ _) fun s₈ u₈ =>
    wp_cmp (n := .r6) (op2_imm imm0) fun s₉ f₉ hz => WP.block_nil ?_
  have g : ∀ r, s₉.gpr r = s₈.gpr r := fun r => by rw [f₉.gpr]
  have hm : s₉.mem = (((s₀.mem.writeW (bA s₀ + BitVec.ofNat 64 256) (s₀.gpr .r4)).writeW
      (bA s₀ + BitVec.ofNat 64 260) (s₀.gpr .r5)).writeW (bA s₀ + BitVec.ofNat 64 264)
      (s₀.gpr .r6)).writeW (bA s₀ + BitVec.ofNat 64 268) (s₀.gpr .lr) := by
    rw [f₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, g₄.mem, g₃.gpr, g₂.gpr, g₁.gpr, g₃.mem, g₂.gpr,
      g₁.gpr, g₂.mem, g₁.gpr, g₁.mem]
  have hf : Frame [bRg s₀] s₀.mem s₉.mem := by
    rw [hm]
    exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (contains_off (by lit_omega) (by lit_omega))).writeW (List.mem_singleton_self _) _
      (contains_off (by lit_omega) (by lit_omega))).writeW (List.mem_singleton_self _) _
      (contains_off (by lit_omega) (by lit_omega))).writeW (List.mem_singleton_self _) _
      (contains_off (by lit_omega) (by lit_omega))
  have hr6 : s₉.gpr .r6 = s₀.gpr .r2 := by
    rw [g, u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), gr]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun k hk => ?_, ?_⟩, ?_⟩
  · rw [g, u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), gr]
  · rw [g, u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, gr]
  · rw [g, u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), gr]
    simp [P]
  · rw [hr6]; simp [P]
  · rw [f₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, g₄.rd, g₃.rd, g₂.rd, g₁.rd]
  · rw [f₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, g₄.wr, g₃.wr, g₂.wr, g₁.wr]
  · intro r hr
    have hr' : r ≠ .r4 ∧ r ≠ .r5 ∧ r ≠ .r6 ∧ r ≠ .r1 := by
      simp only [kept, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
    rw [g, u₈.other _ hr'.2.2.2, u₇.other _ hr'.2.2.1, u₆.other _ hr'.2.1, u₅.other _ hr'.1, gr]
  · rw [stateAt_frame hf (by simpa using hp.st_b), ctr_zero]
  · simp only [P, Nat.mul_zero, Nat.zero_min, Nat.not_lt_zero, ite_false]
    exact hf.bytes (R := dRg s₀) (by simpa using hp.d_b) (show L s₀ ≤ 2 ^ 64 by have := L_lt s₀; omega) hk
  · rw [hm]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [readW_writeW_off _ _ _ (by lit_omega) (by lit_omega) (by lit_omega),
        readW_writeW_off _ _ _ (by lit_omega) (by lit_omega) (by lit_omega),
        readW_writeW_off _ _ _ (by lit_omega) (by lit_omega) (by lit_omega), Mem.readW_writeW_self32]
    · rw [readW_writeW_off _ _ _ (by lit_omega) (by lit_omega) (by lit_omega),
        readW_writeW_off _ _ _ (by lit_omega) (by lit_omega) (by lit_omega), Mem.readW_writeW_self32]
    · rw [readW_writeW_off _ _ _ (by lit_omega) (by lit_omega) (by lit_omega), Mem.readW_writeW_self32]
    · rw [Mem.readW_writeW_self32]
  · rw [hz, g]

/-! ## Calling the block function -/

theorem block_keeps_r1 : ∀ i ∈ instrs Impl.ChaCha20.Arm.block, dstOf i ≠ some .r1 := by
  have : ((instrs Impl.ChaCha20.Arm.block).all fun i => dstOf i != some .r1) = true := by
    rw [← Code.allInstrs_eq]; lit_decide
  intro i hi
  simpa using List.all_eq_true.mp this i hi

/-- After the block function: `buf` holds block `j`'s keystream. -/
structure AInv (s₀ : State) (j : Nat) (s : State) : Prop extends Inv s₀ j s where
  ks : ∀ t < 64, s.mem (bA s₀ + BitVec.ofNat 64 t) =
    (serialize (Spec.ChaCha20.block (ctr (S0 s₀) j))).getD t 0

theorem call_ok {s₀ : State} (hp : XPre s₀) {j : Nat} {s : State} (h : Inv s₀ j s)
    (h0 : s.gpr .r0 = stP s₀) :
    WP isa (.call "vg_chacha20_block" Impl.ChaCha20.Arm.block) s (AInv s₀ j) := by
  have c0 : s.callEntry.gpr .r0 = stP s₀ := (State.callEntry_gpr _ (by decide)).trans h0
  have c1 : s.callEntry.gpr .r1 = bP s₀ := (State.callEntry_gpr _ (by decide)).trans h.r1
  have hwr : s.wr = [stRg s₀, dRg s₀, bRg s₀] := by rw [h.wr, hp.wr]
  have hrd : s.rd = [] := by rw [h.rd, hp.rd]
  refine WP.call (k := Proof.ChaCha20.blockArm) block_correct
    (rd := [stRg s₀]) (wr := [b256 s₀]) ?_ ?_ ?_ ?_
  · simp only [Proof.ChaCha20.blockArm, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, c0, c1]
    exact ⟨trivial, trivial, (hp.st_b.sub_right (b256_sub s₀)).symm, hp.st_fit,
      by have := hp.b_fit; omega⟩
  · rw [hrd, hwr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨stRg s₀, by simp, 0, by simp, show 0 + 64 ≤ 64 by omega⟩
    · exact ⟨bRg s₀, by simp, 0, by simp, show 0 + 256 ≤ 320 by omega⟩
  · rw [hwr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨bRg s₀, by simp, 0, by simp, show 0 + 256 ≤ 320 by omega⟩
  · intro s₂ hrd₂ hwr₂ _ hf hcs hkeep hpost
    have hst : stateAt s₂.mem (stA s₀) = stateAt s.mem (stA s₀) :=
      stateAt_frame hf (by simpa using hp.st_b.sub_right (b256_sub s₀))
    simp only [Proof.ChaCha20.blockArm, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_mem, c0, c1, h.cnt] at hpost
    have pr : ∀ r ∈ preserved, r ≠ .lr → s₂.gpr r = s.gpr r := hcs
    have hk₂ : Keep s₀ s₂ := by
      intro r hr
      simp only [kept, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      · rw [pr _ (by decide) (by decide)]; exact h.keep _ (by decide)
    refine ⟨⟨by rw [hkeep .r1 block_keeps_r1 (by decide), h.r1],
      by rw [pr .r4 (by decide) (by decide), h.r4],
      by rw [pr .r5 (by decide) (by decide), h.r5],
      by rw [pr .r6 (by decide) (by decide), h.r6],
      by rw [hrd₂, h.rd], by rw [hwr₂, h.wr], hk₂, by rw [hst, h.cnt], fun k hk => ?_,
      h.saved.frame hf (by simpa using savR_b256 s₀)⟩, fun t ht => ?_⟩
    · rw [hf.bytes (R := dRg s₀) (by simpa using hp.d_b.sub_right (b256_sub s₀))
        (show L s₀ ≤ 2 ^ 64 by have := L_lt s₀; omega) hk]
      exact h.data k hk
    · rw [← serialize_stateAt s₂.mem (bA s₀) ht, hpost]

/-! ## The bytes of block `j` -/

/-- Before byte `i` of block `j`. -/
structure IInv (s₀ : State) (j i : Nat) (s : State) : Prop where
  r1 : s.gpr .r1 = bP s₀
  r4 : s.gpr .r4 = stP s₀
  r5 : s.gpr .r5 = dP s₀ + BitVec.ofNat 32 (P s₀ j + i)
  r3 : s.gpr .r3 = bP s₀ + BitVec.ofNat 32 i
  r2 : s.gpr .r2 = BitVec.ofNat 32 (C s₀ j - i)
  r6 : s.gpr .r6 = BitVec.ofNat 32 (L s₀ - P s₀ j - C s₀ j)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  keep : Keep s₀ s
  cnt : stateAt s.mem (stA s₀) = ctr (S0 s₀) j
  data : ∀ k < L s₀, s.mem (dA s₀ + BitVec.ofNat 64 k) =
    if k < P s₀ j + i then D0 s₀ k ^^^ (KS s₀).getD k 0 else D0 s₀ k
  saved : XSaved s₀ s.mem
  ks : ∀ t < 64, s.mem (bA s₀ + BitVec.ofNat 64 t) =
    (serialize (Spec.ChaCha20.block (ctr (S0 s₀) j))).getD t 0

/-- `n = min(64, r6)`, the rest of `r6`, and the keystream pointer. -/
def selA : List Instr := [.mov .r2 (.shifted .r6 .lsr 6), .cmp .r2 (.imm 0)]
def selB : List Instr := [.dp .sub .r6 .r6 (.reg .r2), .mov .r3 (.reg .r1)]

theorem sel_ok {s₀ : State} {j : Nat} (hj : P s₀ j < L s₀) {s : State} (h : AInv s₀ j s) :
    WP isa (.seq (.block selA)
      (.seq (.ite .eq (.block [.mov .r2 (.reg .r6)]) (.block [.mov .r2 (.imm 64)]))
        (.block selB))) s (IInv s₀ j 0) := by
  have hL := L_lt s₀
  have hC : C s₀ j = min 64 (L s₀ - P s₀ j) := rfl
  refine WP.seq (wp_mov (op2_lsr (by decide)) fun s₁ u₁ =>
    wp_cmp (n := .r2) (op2_imm imm0) fun s₂ f₂ hz => WP.block_nil ?_)
  have hx2 : s₁.gpr .r2 = BitVec.ofNat 32 ((L s₀ - P s₀ j) / 64) := by
    rw [u₁.gpr, h.r6, ofNat_shr (by lit_omega), show (2 : Nat) ^ 6 = 64 from rfl]
  have hx6 : s₂.gpr .r6 = BitVec.ofNat 32 (L s₀ - P s₀ j) := by
    rw [f₂.gpr, u₁.other _ (by decide), h.r6]
  refine WP.seq (WP.mono (Q := fun s₃ : State => s₃.gpr .r2 = BitVec.ofNat 32 (C s₀ j) ∧
      (∀ r, r ≠ .r2 → s₃.gpr r = s₂.gpr r) ∧ s₃.mem = s₂.mem ∧ s₃.rd = s₂.rd ∧ s₃.wr = s₂.wr) ?_
    fun s₃ ⟨f₁, f₂', f₃, f₄, f₅⟩ => ?_)
  · refine WP.ite (decide ((L s₀ - P s₀ j) / 64 = 0))
      (by have e : isa.eval .eq s₂ = some s₂.z := eval_eq s₂
          rw [e, hz, hx2, sub_zero', ofNat_beq_zero (by lit_omega)])
      (fun ht => wp_mov (op2_reg _ _) fun s₃ u₃ => WP.block_nil ⟨?_, u₃.other, u₃.mem, u₃.rd, u₃.wr⟩)
      (fun hf => wp_mov (op2_imm imm64) fun s₃ u₃ => WP.block_nil ⟨?_, u₃.other, u₃.mem, u₃.rd, u₃.wr⟩)
    · simp only [decide_eq_true_eq] at ht
      rw [u₃.gpr, hx6, show C s₀ j = L s₀ - P s₀ j by omega]
    · simp only [decide_eq_false_iff_not] at hf
      rw [u₃.gpr, show C s₀ j = 64 by omega]; rfl
  · refine wp_sub (op2_reg _ _) fun s₄ u₄ => wp_mov (op2_reg _ _) fun s₅ u₅ => WP.block_nil ?_
    have g : ∀ r, r ≠ .r2 → r ≠ .r6 → r ≠ .r3 → s₅.gpr r = s.gpr r :=
      fun r h₁ h₂ h₃ => by
        rw [u₅.other r h₃, u₄.other r h₂, f₂' r h₁, f₂.gpr, u₁.other r h₁]
    have gm : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, f₃, f₂.mem, u₁.mem]
    have gk : Keep s₀ s₅ := fun r hr => by
      rw [g r (by rintro rfl; revert hr; decide) (by rintro rfl; revert hr; decide)
        (by rintro rfl; revert hr; decide), h.keep r hr]
    refine ⟨by rw [g _ (by decide) (by decide) (by decide), h.r1],
      by rw [g _ (by decide) (by decide) (by decide), h.r4],
      by rw [g _ (by decide) (by decide) (by decide), h.r5, Nat.add_zero],
      by rw [u₅.gpr, u₄.other _ (by decide), f₂' _ (by decide), f₂.gpr, u₁.other _ (by decide),
        h.r1]; simp,
      by rw [u₅.other _ (by decide), u₄.other _ (by decide), f₁, Nat.sub_zero],
      by rw [u₅.other _ (by decide), u₄.gpr, f₂' _ (by decide), f₁, hx6, sub_ofNat (by lit_omega)],
      by rw [u₅.rd, u₄.rd, f₄, f₂.rd, u₁.rd, h.rd], by rw [u₅.wr, u₄.wr, f₅, f₂.wr, u₁.wr, h.wr],
      gk, by rw [gm, h.cnt], fun k hk => by rw [gm, h.data k hk, Nat.add_zero],
      by rw [gm]; exact h.saved, fun t ht => by rw [gm]; exact h.ks t ht⟩

/-! ## One byte -/

def xorBody : List Instr :=
  [.ldrb .r0 .r5 0, .ldrb .r12 .r3 0, .dp .eor .r0 .r0 (.reg .r12), .strb .r0 .r5 0,
    .dp .add .r5 .r5 (.imm 1), .dp .add .r3 .r3 (.imm 1), .subs .r2 .r2 (.imm 1)]

theorem xorLoop_eq : xorLoop = .loop (.block xorBody) .ne := rfl

/-- `P j = 64 j` while blocks remain. -/
theorem P_eq {s₀ : State} {j : Nat} (hj : P s₀ j < L s₀) : P s₀ j = 64 * j := by
  simp only [P] at *; omega

theorem ks_eq {s₀ : State} {j i : Nat} (hj : P s₀ j < L s₀) (hi : i < C s₀ j) :
    (KS s₀).getD (P s₀ j + i) 0 = (serialize (Spec.ChaCha20.block (ctr (S0 s₀) j))).getD i 0 := by
  have hP := P_eq hj
  have hC : C s₀ j = min 64 (L s₀ - P s₀ j) := rfl
  rw [KS, keystream_getD _ (by lit_omega), hP, show (64 * j + i) / 64 = j by omega,
    show (64 * j + i) % 64 = i by omega]

theorem xor_step {s₀ : State} (hp : XPre s₀) {j i : Nat} (hj : P s₀ j < L s₀) (hi : i < C s₀ j)
    {s : State} (h : IInv s₀ j i s) :
    WP isa (.block xorBody) s (fun s' => IInv s₀ j (i + 1) s' ∧ s'.z = (s'.gpr .r2 - 0 == 0)) := by
  have hL := L_lt s₀
  have hk : P s₀ j + i < L s₀ := by have hC : C s₀ j = min 64 (L s₀ - P s₀ j) := rfl; omega
  have hC64 : C s₀ j ≤ 64 := Nat.min_le_left _ _
  have hdf := hp.d_fit
  have hbf := hp.b_fit
  have cd : (dRg s₀).Contains (dA s₀ + BitVec.ofNat 64 (P s₀ j + i)) 1 :=
    contains_off (by lit_omega) (by lit_omega)
  have cb : (bRg s₀).Contains (bA s₀ + BitVec.ofNat 64 i) 1 := contains_off (by lit_omega) (by lit_omega)
  have i₁ : InRegions (s.rd ++ s.wr) (dA s₀ + BitVec.ofNat 64 (P s₀ j + i)) 1 :=
    ⟨dRg s₀, by simp [h.rd, h.wr, hp.rd, hp.wr], cd⟩
  have i₂ : InRegions (s.rd ++ s.wr) (bA s₀ + BitVec.ofNat 64 i) 1 :=
    ⟨bRg s₀, by simp [h.rd, h.wr, hp.rd, hp.wr], cb⟩
  have o₁ : InRegions s.wr (dA s₀ + BitVec.ofNat 64 (P s₀ j + i)) 1 :=
    ⟨dRg s₀, by simp [h.wr, hp.wr], cd⟩
  have ed : ∀ x : State, x.gpr .r5 = s.gpr .r5 →
      State.addr (x.gpr .r5 + BitVec.ofNat 32 0) = dA s₀ + BitVec.ofNat 64 (P s₀ j + i) :=
    fun x hx => by rw [hx, h.r5]; exact ea0 (by lit_omega)
  unfold xorBody
  refine wp_ldrb (by decide) (ed s rfl) i₁ fun s₁ u₁ => ?_
  refine wp_ldrb (a := bA s₀ + BitVec.ofNat 64 i) (by decide)
    (by rw [u₁.other _ (by decide), h.r3]; exact ea0 (by lit_omega))
    (by rw [u₁.rd, u₁.wr]; exact i₂) fun s₂ u₂ => ?_
  refine wp_eor (op2_reg _ _) fun s₃ u₃ => ?_
  refine wp_strb (by decide) (ed s₃ (by rw [u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide)]))
    (by rw [u₃.wr, u₂.wr, u₁.wr]; exact o₁) fun s₄ g₄ => ?_
  refine wp_add (op2_imm imm1) fun s₅ u₅ => wp_add (op2_imm imm1) fun s₆ u₆ =>
    wp_subs (op2_imm imm1) fun s₇ u₇ hz => WP.block_nil ?_
  have hv : (s₃.gpr .r0).setWidth 8 =
      D0 s₀ (P s₀ j + i) ^^^ (KS s₀).getD (P s₀ j + i) 0 := by
    rw [u₃.gpr, u₂.other _ (by decide), u₁.gpr, u₂.gpr, u₁.mem, xor_setWidth, h.data _ hk,
      h.ks i (by lit_omega), ks_eq hj hi]
    simp
  have hm : s₇.mem = s.mem.writeW (dA s₀ + BitVec.ofNat 64 (P s₀ j + i))
      (D0 s₀ (P s₀ j + i) ^^^ (KS s₀).getD (P s₀ j + i) 0) := by
    rw [u₇.mem, u₆.mem, u₅.mem, g₄.mem, hv, u₃.mem, u₂.mem, u₁.mem]
  have hfd : Frame [dRg s₀] s.mem s₇.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ cd
  have g : ∀ r, r ≠ .r0 → r ≠ .r12 → r ≠ .r5 → r ≠ .r3 → r ≠ .r2 → s₇.gpr r = s.gpr r :=
    fun r h₁ h₂ h₃ h₄ h₅ => by
      rw [u₇.other r h₅, u₆.other r h₄, u₅.other r h₃, g₄.gpr, u₃.other r h₁, u₂.other r h₂,
        u₁.other r h₁]
  have h6 : s₆.gpr .r2 = BitVec.ofNat 32 (C s₀ j - i) := by
    rw [u₆.other _ (by decide), u₅.other _ (by decide), g₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), h.r2]
  have hr2 : s₇.gpr .r2 = BitVec.ofNat 32 (C s₀ j - (i + 1)) := by
    rw [u₇.gpr, h6, sub_one' (by lit_omega), Nat.sub_sub]
  refine ⟨⟨by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), h.r1],
    by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), h.r4], ?_, ?_, hr2,
    by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), h.r6],
    by rw [u₇.rd, u₆.rd, u₅.rd, g₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd],
    by rw [u₇.wr, u₆.wr, u₅.wr, g₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr],
    ((((((h.keep.upd u₁).upd u₂).upd u₃).mupd g₄).upd u₅).upd u₆).upd u₇,
    by rw [stateAt_frame hfd (by simpa using hp.st_d), h.cnt], fun k hk' => ?_,
    h.saved.frame hfd (by simpa using (hp.d_b.sub_right (savR_sub s₀)).symm), fun t ht => ?_⟩, ?_⟩
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, g₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), h.r5, add_one', Nat.add_assoc]
  · rw [u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), g₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), h.r3, add_one']
  · rw [hm, writeW8_apply]
    by_cases he : k = P s₀ j + i
    · subst he; simp
    · simp only [data_ne hk hk' he, ite_false]
      rw [h.data k hk']
      by_cases h₁ : k < P s₀ j + i
      · simp [h₁, show k < P s₀ j + (i + 1) by omega]
      · simp [h₁, show ¬ k < P s₀ j + (i + 1) by omega]
  · rw [hfd.bytes (R := bRg s₀) (by simpa using hp.d_b.symm) (show 320 ≤ 2 ^ 64 by omega)
      (show t < 320 by omega)]
    exact h.ks t ht
  · rw [hz, hr2, h6, sub_one' (by lit_omega), sub_zero', Nat.sub_sub]

/-! ## A whole block -/

theorem xorLoop_ok {s₀ : State} (hp : XPre s₀) {j : Nat} (hj : P s₀ j < L s₀) {s : State}
    (h : IInv s₀ j 0 s) : WP isa xorLoop s (IInv s₀ j (C s₀ j)) := by
  have hL := L_lt s₀
  have hpos : 0 < C s₀ j := by simp only [C]; omega
  have hC : C s₀ j ≤ 64 := by simp only [C]; omega
  rw [xorLoop_eq]
  let Inv : Nat → State → Prop := fun n s => ∃ i, n = C s₀ j - i ∧ i < C s₀ j ∧ IInv s₀ j i s
  have hstep : ∀ n s, Inv n s → WP isa (.block xorBody) s (fun s' =>
      (isa.eval .ne s' = some false ∧ IInv s₀ j (C s₀ j) s') ∨
      (isa.eval .ne s' = some true ∧ ∃ n' < n, Inv n' s')) := by
    rintro n s ⟨i, rfl, hi, hI⟩
    refine WP.mono (xor_step hp hj hi hI) fun s' ⟨h', hz'⟩ => ?_
    have hz := eval_ne_ofNat s' (by lit_omega) hz' h'.r2
    by_cases hl : i + 1 = C s₀ j
    · exact .inl ⟨by rw [hz]; simp [hl], hl ▸ h'⟩
    · exact .inr ⟨by rw [hz]; simp; omega, C s₀ j - (i + 1), by omega, i + 1, rfl, by omega, h'⟩
  exact WP.loop (M := isa) Inv hstep (C s₀ j) s ⟨0, by simp, hpos, h⟩

/-! ## The end of a block -/

def nextInstrs : List Instr :=
  [.ldr .r0 .r4 48, .dp .add .r0 .r0 (.imm 1), .str .r0 .r4 48, .cmp .r6 (.imm 0)]

theorem P_succ {s₀ : State} {j : Nat} (hj : P s₀ j < L s₀) : P s₀ (j + 1) = P s₀ j + C s₀ j := by
  simp only [P, C] at *; omega

theorem next_ok {s₀ : State} (hp : XPre s₀) {j : Nat} (hj : P s₀ j < L s₀) {s : State}
    (h : IInv s₀ j (C s₀ j) s) : WP isa (.block nextInstrs) s (OInv s₀ (j + 1)) := by
  have hP := P_succ hj
  have c₁ : (stRg s₀).Contains (stA s₀ + BitVec.ofNat 64 48) 4 := contains_off (by lit_omega) (by lit_omega)
  unfold nextInstrs
  refine wp_ldr (by decide) (by rw [h.r4]; exact hp.eaS (by lit_omega))
    ⟨stRg s₀, by simp [h.rd, h.wr, hp.rd, hp.wr], c₁⟩ fun s₁ u₁ => wp_add (op2_imm imm1) fun s₂ u₂ => ?_
  have e4 : s₂.gpr .r4 = stP s₀ := by rw [u₂.other _ (by decide), u₁.other _ (by decide), h.r4]
  refine wp_str (by decide) (by rw [e4]; exact hp.eaS (by lit_omega))
    ⟨stRg s₀, by simp [u₂.wr, u₁.wr, h.wr, hp.wr], c₁⟩ fun s₃ g₃ =>
    wp_cmp (n := .r6) (op2_imm imm0) fun s₄ f₄ hz => WP.block_nil ?_
  have hv : s.mem.readW (stA s₀ + BitVec.ofNat 64 48) 32 = (ctr (S0 s₀) j)[12]'(by decide) := by
    rw [← h.cnt]; simp [stateAt]
  have hm : s₄.mem = s.mem.writeW (stA s₀ + BitVec.ofNat 64 48) ((ctr (S0 s₀) j)[12]'(by decide) + 1) := by
    rw [f₄.mem, g₃.mem, u₂.gpr, u₁.gpr, u₂.mem, u₁.mem, hv]
  have hfs : Frame [stRg s₀] s.mem s₄.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ c₁
  have g : ∀ r, r ≠ .r0 → s₄.gpr r = s.gpr r := fun r hr => by
    rw [f₄.gpr, g₃.gpr, u₂.other r hr, u₁.other r hr]
  refine ⟨⟨by rw [g _ (by decide), h.r1], by rw [g _ (by decide), h.r4],
    by rw [g _ (by decide), h.r5, hP], by rw [g _ (by decide), h.r6, hP, Nat.sub_sub],
    by rw [f₄.rd, g₃.rd, u₂.rd, u₁.rd, h.rd], by rw [f₄.wr, g₃.wr, u₂.wr, u₁.wr, h.wr],
    ((h.keep.upd u₁).upd u₂).mupd g₃ |>.fupd f₄,
    by rw [hm, stateAt_writeW_counter, h.cnt, ctr_succ], fun k hk => ?_,
    h.saved.frame hfs (by simpa using (hp.st_b.sub_right (savR_sub s₀)).symm)⟩, ?_⟩
  · rw [hfs.bytes (R := dRg s₀) (by simpa using hp.st_d.symm)
      (show L s₀ ≤ 2 ^ 64 by have := L_lt s₀; omega) hk,
      h.data k hk, hP]
  · rw [hz, g _ (by decide), g₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide)]

theorem body_eq : body =
    .seq (.block [.mov .r0 (.reg .r4)])
    (.seq (.call "vg_chacha20_block" Impl.ChaCha20.Arm.block)
    (.seq (.block selA)
    (.seq (.ite .eq (.block [.mov .r2 (.reg .r6)]) (.block [.mov .r2 (.imm 64)]))
    (.seq (.block selB)
    (.seq xorLoop (.block nextInstrs)))))) := rfl

theorem body_ok {s₀ : State} (hp : XPre s₀) {j : Nat} (hj : P s₀ j < L s₀) {s : State}
    (h : OInv s₀ j s) : WP isa body s (OInv s₀ (j + 1)) := by
  rw [body_eq]
  refine WP.seq (wp_mov (op2_reg _ _) fun s₀' u => WP.block_nil ?_)
  have hI : Inv s₀ j s₀' :=
    ⟨by rw [u.other _ (by decide), h.r1], by rw [u.other _ (by decide), h.r4],
      by rw [u.other _ (by decide), h.r5], by rw [u.other _ (by decide), h.r6],
      by rw [u.rd, h.rd], by rw [u.wr, h.wr], h.keep.upd u, by rw [u.mem, h.cnt],
      by rw [u.mem]; exact h.data, by rw [u.mem]; exact h.saved⟩
  refine WP.seq (WP.mono (call_ok hp hI (by rw [u.gpr, h.r4])) fun s₁ h₁ => ?_)
  have hs := sel_ok hj h₁
  rw [WP.seq_iff] at hs
  rw [WP.seq_iff]
  refine WP.mono hs fun s₂ h₂ => ?_
  rw [WP.seq_iff] at h₂
  rw [WP.seq_iff]
  refine WP.mono h₂ fun s₃ h₃ => ?_
  rw [WP.seq_iff]
  refine WP.mono h₃ fun s₄ h₄ => ?_
  exact WP.seq (WP.mono (xorLoop_ok hp hj h₄) fun s₅ h₅ => next_ok hp hj h₅)

/-! ## The epilogue -/

theorem restore_eq : .mov .r0 (.reg .r4) :: restore =
    [.mov .r0 (.reg .r4), .ldr .r4 .r1 256, .ldr .r5 .r1 260, .ldr .r6 .r1 264,
      .ldr .lr .r1 268] := rfl

/-- What the code guarantees on return. -/
def Post (s₀ s' : State) : Prop :=
  (∀ p ∈ saved, s'.gpr p.1 = s₀.gpr p.1) ∧ Keep s₀ s' ∧ s'.gpr .r0 = stP s₀ ∧
    s'.gpr .r1 = bP s₀ ∧ Proof.ChaCha20.xorArm.post s₀ s'

theorem epilogue_ok {s₀ : State} (hp : XPre s₀) {j : Nat} (hj : P s₀ j = L s₀) {s : State}
    (h : Inv s₀ j s) : WP isa (.block (.mov .r0 (.reg .r4) :: restore)) s (Post s₀) := by
  have i : ∀ d, d + 4 ≤ 320 → InRegions (s.rd ++ s.wr) (bA s₀ + BitVec.ofNat 64 d) 4 :=
    fun d hd => ⟨bRg s₀, by simp [h.rd, h.wr, hp.rd, hp.wr], contains_off hd (by lit_omega)⟩
  obtain ⟨sv1, sv2, sv3, sv4⟩ := h.saved
  rw [restore_eq]
  refine wp_mov (op2_reg _ _) fun s₀' u₀ => ?_
  have e1 : ∀ x : State, x.gpr .r1 = s.gpr .r1 → ∀ d, d < 320 →
      State.addr (x.gpr .r1 + BitVec.ofNat 32 d) = bA s₀ + BitVec.ofNat 64 d :=
    fun x hx d hd => by rw [hx, h.r1]; exact hp.eaB hd
  refine wp_ldr (by decide) (e1 _ (u₀.other _ (by decide)) 256 (by lit_omega))
    (by rw [u₀.rd, u₀.wr]; exact i 256 (by lit_omega)) fun s₁ u₁ => ?_
  refine wp_ldr (by decide) (e1 _ (by rw [u₁.other _ (by decide), u₀.other _ (by decide)]) 260
    (by lit_omega)) (by rw [u₁.rd, u₁.wr, u₀.rd, u₀.wr]; exact i 260 (by lit_omega)) fun s₂ u₂ => ?_
  refine wp_ldr (by decide) (e1 _ (by rw [u₂.other _ (by decide), u₁.other _ (by decide),
      u₀.other _ (by decide)]) 264 (by lit_omega))
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr, u₀.rd, u₀.wr]; exact i 264 (by lit_omega)) fun s₃ u₃ => ?_
  refine wp_ldr (by decide) (e1 _ (by rw [u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), u₀.other _ (by decide)]) 268 (by lit_omega))
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr, u₀.rd, u₀.wr]; exact i 268 (by lit_omega))
    fun s₄ u₄ => WP.block_nil ?_
  have hm : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem, u₀.mem]
  refine ⟨fun p hp' => ?_, ((((h.keep.upd u₀).upd u₁).upd u₂).upd u₃).upd u₄,
    by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), u₀.gpr, h.r4],
    by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), u₀.other _ (by decide), h.r1], ?_⟩
  · simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl | rfl | rfl
    · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, u₀.mem, sv1]
    · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.mem, u₀.mem, sv2]
    · rw [u₄.other _ (by decide), u₃.gpr, u₂.mem, u₁.mem, u₀.mem, sv3]
    · rw [u₄.gpr, u₃.mem, u₂.mem, u₁.mem, u₀.mem, sv4]
  · refine bytesAt_xor (length_keystream _ _) fun k hk => ?_
    have hk' : k < L s₀ := hk
    rw [hm, h.data k hk']
    simp only [show k < P s₀ j by omega, ite_true]

/-! ## The whole function -/

theorem xor_eq : Impl.ChaCha20.Arm.Xor.xor =
    .seq (.block (save ++ ([.mov .r4 (.reg .r0), .mov .r5 (.reg .r1), .mov .r6 (.reg .r2),
      .mov .r1 (.reg .r3), .cmp .r6 (.imm 0)] : List Instr)))
    (.seq (.ite .eq (.block []) (.loop body .ne)) (.block (.mov .r0 (.reg .r4) :: restore))) := rfl

theorem main_ok {s₀ : State} (hp : XPre s₀) : WP isa Impl.ChaCha20.Arm.Xor.xor s₀ (Post s₀) := by
  have hL := L_lt s₀
  rw [xor_eq]
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (Q := fun s => ∃ j, P s₀ j = L s₀ ∧ Inv s₀ j s) ?_
    fun s₂ ⟨j, hj, h₂⟩ => epilogue_ok hp hj h₂)
  have hz : isa.eval .eq s₁ = some (decide (L s₀ = 0)) := by
    have e : isa.eval .eq s₁ = some s₁.z := eval_eq s₁
    rw [e, h₁.z, h₁.r6, sub_zero', ofNat_beq_zero (by lit_omega)]
    simp [P]
  refine WP.ite (decide (L s₀ = 0)) hz (fun h => ?_) (fun h => ?_)
  · simp only [decide_eq_true_eq] at h
    exact WP.block_nil ⟨0, by simp [P, h], h₁.toInv⟩
  · simp only [decide_eq_false_iff_not] at h
    let Inv' : Nat → State → Prop := fun n s => ∃ j, n = L s₀ - P s₀ j ∧ P s₀ j < L s₀ ∧ OInv s₀ j s
    have hstep : ∀ n s, Inv' n s → WP isa body s (fun s' =>
        (isa.eval .ne s' = some false ∧ ∃ j, P s₀ j = L s₀ ∧ Inv s₀ j s') ∨
        (isa.eval .ne s' = some true ∧ ∃ n' < n, Inv' n' s')) := by
      rintro n s ⟨j, rfl, hj, hI⟩
      refine WP.mono (body_ok hp hj hI) fun s' h' => ?_
      have hz' := eval_ne_ofNat s' (by lit_omega) h'.z h'.r6
      have hP := P_succ hj
      have hC : 0 < C s₀ j := by simp only [C]; omega
      have hle : P s₀ (j + 1) ≤ L s₀ := by simp only [P]; omega
      by_cases hl : L s₀ - P s₀ (j + 1) = 0
      · exact .inl ⟨by rw [hz']; simp [hl], j + 1, by omega, h'.toInv⟩
      · exact .inr ⟨by rw [hz']; simp [hl], L s₀ - P s₀ (j + 1), by omega, j + 1, rfl, by omega, h'⟩
    exact WP.loop (M := isa) Inv' hstep (L s₀ - P s₀ 0) s₁ ⟨0, rfl, by simp [P]; omega, h₁⟩

theorem correct {s₀ : State} (hp : XPre s₀) :
    ∃ t s', Exec isa Impl.ChaCha20.Arm.Xor.xor s₀ t s' ∧ abiPreserved s₀ s' ∧
      (Proof.ChaCha20.xorArm.post s₀ s' ∧ s'.gpr .r0 = s₀.gpr .r0 ∧ s'.gpr .r1 = s₀.gpr .r3) := by
  obtain ⟨t, s', he, ⟨hsv, hk, h0, h1, hpost⟩⟩ := main_ok hp
  refine ⟨t, s', he, ⟨fun r hr => ?_, Exec.sp he⟩, hpost, h0, h1⟩
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hsv (.r4, 256) (by simp [saved])
  · exact hsv (.r5, 260) (by simp [saved])
  · exact hsv (.r6, 264) (by simp [saved])
  all_goals first | exact hsv (.lr, 268) (by simp [saved]) | exact hk _ (by simp [kept])

/-- `vg_chacha20_xor` returns with `r0` holding `state` and `r1` holding `buf`
(which was in `r3` on entry), for a caller that recomputes pointers from
them. -/
theorem xor_regs (s : State) (hs : Proof.ChaCha20.xorArm.pre s) :
    ∃ t s', Exec isa Impl.ChaCha20.Arm.Xor.xor s t s' ∧ abiPreserved s s' ∧
      (Proof.ChaCha20.xorArm.post s s' ∧ s'.gpr .r0 = s.gpr .r0 ∧ s'.gpr .r1 = s.gpr .r3) :=
  correct (XPre.of s hs)

/-! ## Constant time -/

/-- The initial taint: the arguments are public, `r0` and `r3` point at the
state and `buf`, and `data`, of unknown length, lies between them. The
block function's saves and restores of `r4`–`r6` are then slots of `buf`. -/
def τ₀ : VG.Arm.Taint.T :=
  { regs := .ofList [.r0, .r1, .r2, .r3], flags := false, lens := [64, 0, 320],
    bases := [(.r0, 0), (.r3, 2)] }

theorem wf₀ {s : State} (h : Proof.ChaCha20.xorArm.pre s) : VG.Arm.Taint.Wf τ₀ s := by
  have hp := XPre.of s h
  refine ⟨fun _ => ⟨by simp [hp.wr, τ₀], ?_, ?_⟩, ?_, fun h => absurd h (by decide),
    fun _ h => by simp [τ₀] at h⟩
  · simp only [hp.wr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, List.Pairwise.nil, and_true]
    exact ⟨⟨hp.st_d, hp.st_b⟩, hp.d_b, fun _ h => h.elim⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl) <;> simp only [addr_toNat]
    · exact hp.st_fit
    · exact hp.d_fit
    · exact hp.b_fit
  · intro p hp'
    simp only [τ₀, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl <;> simp [VG.Arm.Taint.region, hp.wr]

theorem agree₀ {s₁ s₂ : State} (h₁ : Proof.ChaCha20.xorArm.pre s₁)
    (h₂ : Proof.ChaCha20.xorArm.pre s₂) (hpub : Proof.ChaCha20.xorArm.pub s₁ s₂) :
    VG.Arm.Taint.Agree τ₀ s₁ s₂ := by
  obtain ⟨p0, p1, p2, p3⟩ := hpub
  have hp₁ := XPre.of s₁ h₁; have hp₂ := XPre.of s₂ h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, wf₀ h₁, wf₀ h₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun h => absurd h (by decide), fun k hk => absurd hk (by simp [τ₀])⟩
  · simp only [τ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> assumption
  · rw [hp₁.wr, hp₂.wr]; simp only [stRg, dRg, bRg, stA, dA, bA, stP, dP, bP, L, p0, p1, p2, p3]

/-- A state satisfying the precondition (with no data). -/
def sat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r3 => 0x3000 | _ => 0
  sp := 0x5000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 64⟩, ⟨0x2000, 0⟩, ⟨0x3000, 320⟩]

theorem xor_correct (s : State) (hs : Proof.ChaCha20.xorArm.pre s) :
    ∃ t s', Exec isa Impl.ChaCha20.Arm.Xor.xor s t s' ∧ abiPreserved s s' ∧
      Proof.ChaCha20.xorArm.post s s' :=
  (correct (XPre.of s hs)).imp fun _ ⟨s', he, ha, hpost, _⟩ => ⟨s', he, ha, hpost⟩

theorem xor_ct : ConstantTime isa Proof.ChaCha20.xorArm.pre Proof.ChaCha20.xorArm.pub
    Impl.ChaCha20.Arm.Xor.xor :=
  VG.Taint.constantTime (A := taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁ h₂ hp)
    (by taint_decide)

theorem xor_verified :
    Verified Arm.target Impl.ChaCha20.Arm.Xor.xor (Spec.ChaCha20.xorContract Arm.abi) :=
  Verified.of_correct xor_correct xor_ct
    (by sig_implies [Spec.ChaCha20.xorContract, Spec.ChaCha20.xorSig, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, Proof.ChaCha20.xorArm, State.addr]
      [sat] using sat)

end VG.Proof.ChaCha20.Arm.Xor
