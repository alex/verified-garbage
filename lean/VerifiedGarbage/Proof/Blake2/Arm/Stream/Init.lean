import VerifiedGarbage.Proof.Blake2.Arm.Stream.Common
import VerifiedGarbage.Proof.Rc2.PairMem
import VerifiedGarbage.Proof.Framework.Range

/-!
# Streaming BLAKE2 on ARMv7: `init`

Untrusted: everything here is checked by Lean. `initState` stores the
initial hash value as 32-bit words (`word32`, two per word of BLAKE2b), the
first with the parameter block XORed in; for a key, `keyBlock` zeroes the
buffer and copies the key into it. `init` is a leaf function writing only
`r1`–`r3` and `r12`.
-/

namespace VG.Proof.Blake2.Arm.Stream.Init

open VG VG.Arm VG.Spec.Blake2
open VG.Impl.Blake2.Arm.Stream (N B ws ivWord movImm initState keyBlock init)
open VG.Proof.MdStream.Arm (Upd Mupd op2_imm op2_reg op2_lsl wp_mov wp_add wp_subs wp_cmp wp_str wp_ldrb wp_strb
  sub_ofNat cmp0 eval_eq eval_ne)
open VG.WriteBytes (writeBytes writeBytes_nil writeBytes_snoc writeBytes_frame writeBytes_before)
open VG.Proof.Blake2 (initArm repr_keyBlock stateAt_congr)

/-! ## 32-bit words of the hash value -/

theorem split64 (x : BitVec 64) : x = (x >>> 32).setWidth 32 ++ x.setWidth 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_append]
  split
  · simp [*]
  · simp [show i - 32 < 32 by omega]; congr 1; omega

theorem readW64_split (m : Mem) (a : Addr) :
    m.readW a 64 = m.readW (a + BitVec.ofNat 64 4) 32 ++ m.readW a 32 := by
  rw [← VG.Proof.Rc2.Word32.readW64_hi, ← VG.Proof.Rc2.Word32.readW64_lo]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_append]
  split
  · simp [*]
  · simp [show i - 32 < 32 by omega]; congr 1; omega

def word32 {w : Nat} (h : HashValue w) (j : Nat) : BitVec 32 :=
  ((h.toList.getD (j / (ws w / 4)) 0) >>> (32 * (j % (ws w / 4)))).setWidth 32

theorem ivWord_eq {w : Nat} (P : Params w) (j : Nat) : ivWord P j = word32 P.IV j := rfl

theorem word32_32 (h : HashValue 32) {k : Nat} (hk : k < 8) : word32 h k = h[k] := by
  simp [word32, ws, List.getD_eq_getElem?_getD, hk, Nat.mod_one]

theorem word32_64 (h : HashValue 64) {k : Nat} (hk : k < 8) :
    word32 h (2 * k + 1) ++ word32 h (2 * k) = h[k] := by
  simp only [word32, ws, show 64 / 8 / 4 = 2 from rfl, show (2 * k + 1) / 2 = k by omega,
    show (2 * k + 1) % 2 = 1 by omega, show 2 * k / 2 = k by omega, show 2 * k % 2 = 0 by omega]
  simp [List.getD_eq_getElem?_getD, hk]
  exact (split64 _).symm

theorem c_lt {nn kk : Nat} (hn : nn < 256) (hk : kk < 256) :
    ((16842752#64) ^^^ (BitVec.ofNat 64 kk <<< 8) ^^^ BitVec.ofNat 64 nn).toNat < 2 ^ 32 := by
  simp only [BitVec.toNat_xor, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat]
  refine Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (by decide) ?_) (by omega)
  rw [Nat.shiftLeft_eq]; omega

theorem word32_init {w : Nat} (hw : w = 32 ∨ w = 64) (P : Params w) {nn kk : Nat} (hn : nn < 256)
    (hk : kk < 256) {j : Nat} (hj : j < 8 * (ws w / 4)) :
    word32 (Spec.Blake2.init P nn kk) j = if j = 0 then
      word32 P.IV 0 ^^^ 0x01010000 ^^^ (BitVec.ofNat 32 kk <<< 8) ^^^ BitVec.ofNat 32 nn else word32 P.IV j := by
  rcases hw with rfl | rfl
  · have hj' : j < 8 := hj
    rw [word32_32 _ hj', Spec.Blake2.init, Vector.getElem_set]
    split
    · subst_vars; simp [word32_32 _ (show 0 < 8 by decide)]
    · rename_i h; simp [Ne.symm h, word32_32 _ hj']
  · have hj' : j < 16 := hj
    simp only [word32, ws, show 64 / 8 / 4 = 2 from rfl, Spec.Blake2.init, Vector.toList_set]
    have hl : P.IV.toList.length = 8 := by simp
    rcases (by omega : j = 0 ∨ j = 1 ∨ 2 ≤ j) with rfl | rfl | h2
    · simp [List.getD_eq_getElem?_getD, BitVec.setWidth_xor]
    · simp [List.getD_eq_getElem?_getD]
      have hc : ((16842752#64) ^^^ (BitVec.ofNat 64 kk <<< 8) ^^^ BitVec.ofNat 64 nn) >>> 32 = 0 := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt (c_lt hn hk)]
        rfl
      rw [BitVec.xor_assoc, BitVec.xor_assoc, ← BitVec.xor_assoc (16842752#64), BitVec.ushiftRight_xor_distrib, hc]
      simp
    · have hne : j / 2 ≠ 0 := by omega
      simp [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hne), show j ≠ 0 by omega]

theorem stateAt_of_words {w : Nat} (hw : w = 32 ∨ w = 64) {m : Mem} {p : Addr} {h : HashValue w}
    (H : ∀ j < 8 * (ws w / 4), m.readW (p + BitVec.ofNat 64 (4 * j)) 32 = word32 h j) :
    stateAt w m p = h := by
  rcases hw with rfl | rfl
  · apply Vector.ext; intro k hk
    simp only [stateAt, Vector.getElem_ofFn]
    rw [show 32 / 8 * k = 4 * k by omega, H k (by simp [ws]; omega), word32_32 _ hk]
  · apply Vector.ext; intro k hk
    simp only [stateAt, Vector.getElem_ofFn]
    rw [readW64_split, Offset.add_add, show 64 / 8 * k = 4 * (2 * k) by omega,
      show 4 * (2 * k) + 4 = 4 * (2 * k + 1) by omega, H _ (by simp [ws]; omega), H _ (by simp [ws]; omega),
      word32_64 _ hk]

/-! ## The initial hash value -/

section
variable {w : Nat} (P : Params w)

/-- The store of IV word `j + 1`. -/
def ivStep (j : Nat) : List Instr := movImm (ivWord P (j + 1)) ++ [.str .r12 .r0 (4 * (j + 1))]

theorem initState_eq : initState P = (List.range (N w / 4 - 1)).flatMap (ivStep P) ++
    (movImm (ivWord P 0 ^^^ 0x01010000) ++ ([.dp .eor .r12 .r12 (.shifted .r3 .lsl 8),
      .dp .eor .r12 .r12 (.reg .r1), .str .r12 .r0 0] : List Instr)) := by
  rw [initState, List.append_assoc]
  rfl

/-- After storing IV words `1 … n`. -/
structure IvInv (s₀ : State) (n : Nat) (s : State) : Prop where
  gpr : ∀ r, r ≠ .r12 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [⟨State.addr (s₀.gpr .r0), bufOff w⟩] s₀.mem s.mem
  words : ∀ j < n, s.mem.readW (State.addr (s₀.gpr .r0) + BitVec.ofNat 64 (4 * (j + 1))) 32 = ivWord P (j + 1)

variable {P}

theorem wp_movImm {s : State} {v : BitVec 32} {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', Upd s s' .r12 v → WP isa (.block rest) s' Q) :
    WP isa (.block (movImm v ++ rest)) s Q := by
  simp only [movImm, List.cons_append, List.nil_append]
  refine wp_movw fun s₁ u₁ => wp_movt fun s₂ u₂ => k s₂ ⟨?_, fun r h => ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₂.gpr, u₁.gpr, movw_movt]
  · rw [u₂.other r h, u₁.other r h]
  · rw [u₂.mem, u₁.mem]
  · rw [u₂.rd, u₁.rd]
  · rw [u₂.wr, u₁.wr]
  · rw [u₂.sp, u₁.sp]

theorem iv_step (hw : w = 32 ∨ w = 64) {s₀ : State} (hfit : (s₀.gpr .r0).toNat + bufOff w ≤ 2 ^ 32)
    (hwr : ∀ a n, InRegions [⟨State.addr (s₀.gpr .r0), bufOff w⟩] a n → InRegions s₀.wr a n)
    (k : Nat) (s : State) (hk : k < bufOff w / 4 - 1) (h : IvInv P s₀ k s) :
    WP isa (.block (ivStep P k)) s (IvInv P s₀ (k + 1)) := by
  have hN : bufOff w ≤ 64 := by rcases hw with rfl | rfl <;> decide
  have hin : (⟨State.addr (s₀.gpr .r0), bufOff w⟩ : Region).Contains
      (State.addr (s₀.gpr .r0) + BitVec.ofNat 64 (4 * (k + 1))) 4 :=
    contains_off _ (by omega) (by omega)
  unfold ivStep
  refine wp_movImm fun s₁ u₁ => wp_str (a := State.addr (s₀.gpr .r0) + BitVec.ofNat 64 (4 * (k + 1)))
    (by omega) (by rw [u₁.other _ (by decide), h.gpr _ (by decide), addr_add (by omega)])
    (by rw [u₁.wr, h.wr]; exact hwr _ _ ⟨_, List.mem_singleton_self _, hin⟩) fun s₂ g₂ => WP.block_nil ?_
  refine ⟨fun r hr => by rw [g₂.gpr, u₁.other r hr, h.gpr r hr], by rw [g₂.rd, u₁.rd, h.rd],
    by rw [g₂.wr, u₁.wr, h.wr], by rw [g₂.sp, u₁.sp, h.sp], ?_, fun j hj => ?_⟩
  · rw [g₂.mem, u₁.mem]; exact h.frame.writeW (List.mem_singleton_self _) _ hin
  · rw [g₂.mem, u₁.gpr, u₁.mem]
    by_cases e : j = k
    · subst e; exact Mem.readW_writeW_self32 _ _ _
    · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)]
      exact h.words j (by omega)

/-- The state after `initState`. -/
structure StateOk (s₀ : State) (s : State) : Prop where
  gpr : ∀ r, r ≠ .r12 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [⟨State.addr (s₀.gpr .r0), bufOff w⟩] s₀.mem s.mem
  state : stateAt w s.mem (State.addr (s₀.gpr .r0)) =
    Spec.Blake2.init P (s₀.gpr .r1).toNat (s₀.gpr .r3).toNat

theorem initState_ok (hw : w = 32 ∨ w = 64) {s₀ : State} (hfit : (s₀.gpr .r0).toNat + bufOff w ≤ 2 ^ 32)
    (hwr : ∀ a n, InRegions [⟨State.addr (s₀.gpr .r0), bufOff w⟩] a n → InRegions s₀.wr a n)
    (hn : (s₀.gpr .r1).toNat < 256) (hk : (s₀.gpr .r3).toNat < 256) :
    WP isa (.block (initState P)) s₀ (StateOk (P := P) s₀) := by
  have hN : bufOff w ≤ 64 ∧ 8 ≤ bufOff w / 4 ∧ N w / 4 = bufOff w / 4 := by
    rcases hw with rfl | rfl <;> decide
  rw [initState_eq, WP.block_append_iff, hN.2.2]
  refine WP.mono (wp_range_flatMap (M := isa) (IvInv P s₀) (fun k s hk h => iv_step hw hfit hwr k s hk h)
    (bufOff w / 4 - 1) (Nat.le_refl _) s₀
    ⟨fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _, fun _ h => absurd h (by omega)⟩) fun s₇ h₇ => ?_
  have hin : (⟨State.addr (s₀.gpr .r0), bufOff w⟩ : Region).Contains (State.addr (s₀.gpr .r0)) 4 :=
    by simp [Region.Contains]; omega
  refine wp_movImm fun s₁ u₁ => wp_eor (op2_lsl (by decide)) fun s₂ u₂ => wp_eor (op2_reg _ _) fun s₃ u₃ =>
    wp_str (a := State.addr (s₀.gpr .r0)) (by decide) ?_ ?_ fun s₄ g₄ => WP.block_nil ?_
  · rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h₇.gpr _ (by decide),
      BitVec.add_zero]
  · rw [u₃.wr, u₂.wr, u₁.wr, h₇.wr]; exact hwr _ _ ⟨_, List.mem_singleton_self _, hin⟩
  have g : ∀ r, r ≠ .r12 → s₄.gpr r = s₀.gpr r := fun r h1 => by
    rw [g₄.gpr, u₃.other r h1, u₂.other r h1, u₁.other r h1, h₇.gpr r h1]
  have hv : s₃.gpr .r12 = word32 (Spec.Blake2.init P (s₀.gpr .r1).toNat (s₀.gpr .r3).toNat) 0 := by
    rw [word32_init hw P hn hk (by rcases hw with rfl | rfl <;> decide)]
    simp only [↓reduceIte]
    rw [u₃.gpr, u₂.gpr,
      u₁.gpr, u₂.other .r1 (by decide), u₁.other .r1 (by decide), u₁.other .r3 (by decide),
      h₇.gpr .r1 (by decide), h₇.gpr .r3 (by decide), BitVec.ofNat_toNat, BitVec.ofNat_toNat,
      BitVec.setWidth_eq, BitVec.setWidth_eq, ivWord_eq]
    rfl
  have hm : s₄.mem = s₇.mem.writeW (State.addr (s₀.gpr .r0)) (s₃.gpr .r12) := by
    rw [g₄.mem, u₃.mem, u₂.mem, u₁.mem]
  refine ⟨g, by rw [g₄.rd, u₃.rd, u₂.rd, u₁.rd, h₇.rd], by rw [g₄.wr, u₃.wr, u₂.wr, u₁.wr, h₇.wr],
    by rw [g₄.sp, u₃.sp, u₂.sp, u₁.sp, h₇.sp], ?_, ?_⟩
  · rw [hm]; exact h₇.frame.writeW (List.mem_singleton_self _) _ hin
  · refine stateAt_of_words hw fun j hj => ?_
    rw [hm]
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rw [Nat.mul_zero, BitVec.add_zero, Mem.readW_writeW_self32, hv]
    · obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      have hj' : j + 1 < 8 * (ws w / 4) := hj
      have e8 : 8 * (ws w / 4) = bufOff w / 4 := by rcases hw with rfl | rfl <;> decide
      have hs : Mem.Sep (State.addr (s₀.gpr .r0) + BitVec.ofNat 64 (4 * (j + 1))) (32 / 8)
          (State.addr (s₀.gpr .r0)) (32 / 8) := fun x h1 h2 =>
        Offset.sep_base (State.addr (s₀.gpr .r0)) (n := 4) (e := 4 * (j + 1)) (k := 4) (by omega) (by omega)
          x h2 h1
      rw [Mem.readW_writeW_sep hs (by decide), h₇.words j (by omega), word32_init hw P hn hk hj']
      simp only [Nat.add_one_ne_zero, ite_false, ivWord_eq]

end

/-! ## The key block -/

section
variable {w : Nat}

/-- After zeroing the first `n` words of the buffer, from `s₁`. -/
structure ZInv (s₁ : State) (n : Nat) (s : State) : Prop where
  gpr : s.gpr = s₁.gpr
  rd : s.rd = s₁.rd
  wr : s.wr = s₁.wr
  sp : s.sp = s₁.sp
  frame : Frame [⟨State.addr (s₁.gpr .r0) + BitVec.ofNat 64 (bufOff w), blockBytes w⟩] s₁.mem s.mem
  words : ∀ j < n, s.mem.readW (State.addr (s₁.gpr .r0) + BitVec.ofNat 64 (bufOff w) + BitVec.ofNat 64 (4 * j)) 32 = 0

theorem zero_all (hw : w = 32 ∨ w = 64) {s₁ : State}
    (hfit : (s₁.gpr .r0).toNat + (bufOff w + blockBytes w) ≤ 2 ^ 32) (h12 : s₁.gpr .r12 = 0)
    (hwr : ∀ a n, InRegions [⟨State.addr (s₁.gpr .r0) + BitVec.ofNat 64 (bufOff w), blockBytes w⟩] a n →
      InRegions s₁.wr a n) {rest : List Instr} {Q : State → Prop}
    (k : ∀ s, ZInv (w := w) s₁ (blockBytes w / 4) s → WP isa (.block rest) s Q) :
    WP isa (.block ((List.range (B w / 4)).map (fun j => Instr.str .r12 .r0 (N w + 4 * j)) ++ rest)) s₁ Q := by
  have hs : bufOff w ≤ 64 ∧ blockBytes w ≤ 128 ∧ blockBytes w % 4 = 0 := by rcases hw with rfl | rfl <;> decide
  rw [WP.block_append_iff]
  refine WP.mono ?_ k
  rw [B_eq]
  suffices h : ∀ n ≤ blockBytes w / 4, WP isa (.block ((List.range n).map
      (fun j => Instr.str .r12 .r0 (N w + 4 * j)))) s₁ (ZInv (w := w) s₁ n) from h _ (Nat.le_refl _)
  intro n hn
  induction n with
  | zero => exact WP.block_nil ⟨rfl, rfl, rfl, rfl, Frame.refl _ _, fun _ h => absurd h (by omega)⟩
  | succ n ih =>
    rw [List.range_succ, List.map_append, WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun t h => ?_
    simp only [List.map_cons, List.map_nil]
    have hin : (⟨State.addr (s₁.gpr .r0) + BitVec.ofNat 64 (bufOff w), blockBytes w⟩ : Region).Contains
        (State.addr (s₁.gpr .r0) + BitVec.ofNat 64 (bufOff w) + BitVec.ofNat 64 (4 * n)) 4 :=
      contains_off _ (by omega) (by omega)
    refine wp_str (a := State.addr (s₁.gpr .r0) + BitVec.ofNat 64 (bufOff w) + BitVec.ofNat 64 (4 * n))
      (by rw [N_eq]; omega) (by rw [h.gpr, addr_add (by rw [N_eq]; omega), N_eq, Offset.add_add])
      (by rw [h.wr]; exact hwr _ _ ⟨_, List.mem_singleton_self _, hin⟩) fun t₁ g₁ => WP.block_nil ?_
    refine ⟨by rw [g₁.gpr, h.gpr], by rw [g₁.rd, h.rd], by rw [g₁.wr, h.wr], by rw [g₁.sp, h.sp], ?_,
      fun j hj => ?_⟩
    · rw [g₁.mem]; exact h.frame.writeW (List.mem_singleton_self _) _ hin
    · rw [g₁.mem, h.gpr, h12]
      by_cases e : j = n
      · subst e; exact Mem.readW_writeW_self32 _ _ _
      · rw [Offset.add_add, Offset.add_add,
          Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide), ← Offset.add_add]
        exact h.words j (by omega)

/-- The key loop's state after `j` of `k` bytes, from `s₂`. -/
structure KI (s₂ : State) (st key : BitVec 32) (k j : Nat) (s : State) : Prop where
  j_le : j ≤ k
  r1 : s.gpr .r1 = st + BitVec.ofNat 32 (bufOff w) + BitVec.ofNat 32 j
  r2 : s.gpr .r2 = key + BitVec.ofNat 32 j
  r3 : s.gpr .r3 = BitVec.ofNat 32 (k - j)
  other : ∀ x, x ≠ .r1 → x ≠ .r2 → x ≠ .r3 → x ≠ .r12 → s.gpr x = s₂.gpr x
  rd : s.rd = s₂.rd
  wr : s.wr = s₂.wr
  sp : s.sp = s₂.sp
  mem : s.mem = writeBytes s₂.mem (State.addr st + BitVec.ofNat 64 (bufOff w))
    ((bytesAt s₂.mem (State.addr key) k).take j)

theorem keyLoop_ok {s₂ : State} {st key : BitVec 32} {k : Nat} (hk : 1 ≤ k) (hkb : k ≤ blockBytes w)
    (hfit : st.toNat + (bufOff w + blockBytes w) ≤ 2 ^ 32) (hkf : key.toNat + k ≤ 2 ^ 32)
    (h : KI (w := w) s₂ st key k 0 s₂)
    (hsrc : ∀ i < k, InRegions (s₂.rd ++ s₂.wr) (State.addr key + BitVec.ofNat 64 i) 1)
    (hdst : ∀ i < k, InRegions s₂.wr (State.addr st + BitVec.ofNat 64 (bufOff w) + BitVec.ofNat 64 i) 1)
    (hd : Region.Disjoint ⟨State.addr key, k⟩ ⟨State.addr st + BitVec.ofNat 64 (bufOff w), k⟩) :
    WP isa (.loop (.block [.ldrb .r12 .r2 0, .strb .r12 .r1 0, .dp .add .r2 .r2 (.imm 1),
      .dp .add .r1 .r1 (.imm 1), .subs .r3 .r3 (.imm 1)]) .ne) s₂ (KI (w := w) s₂ st key k k) := by
  refine WP.loop (M := isa) (fun n (s : State) => ∃ j, n = k - j ∧ j < k ∧ KI (w := w) s₂ st key k j s) ?_ k s₂
    ⟨0, by omega, by omega, h⟩
  rintro n s ⟨j, rfl, hj, h⟩
  have hbyte : s.mem (State.addr key + BitVec.ofNat 64 j) = s₂.mem (State.addr key + BitVec.ofNat 64 j) := by
    rw [h.mem]
    exact (writeBytes_frame s₂.mem _ _ (contains_prefix (k := k) _ (by simp; omega))).bytes
      (R := ⟨State.addr key, k⟩) (by simpa using hd) (by show k ≤ 2 ^ 64; omega) hj
  refine wp_ldrb (a := State.addr key + BitVec.ofNat 64 j) (by decide)
    (by rw [h.r2, BitVec.add_zero, addr_add (by omega)]) (by rw [h.rd, h.wr]; exact hsrc j hj) fun s₁ u₁ => ?_
  have ht : (st + BitVec.ofNat 32 (bufOff w)).toNat = st.toNat + bufOff w := toNat_add_ofNat (by omega)
  refine wp_strb (a := State.addr st + BitVec.ofNat 64 (bufOff w) + BitVec.ofNat 64 j) (by decide)
    (by rw [u₁.other _ (by decide), h.r1, BitVec.add_zero, addr_add (by omega), addr_add (by omega)])
    (by rw [u₁.wr, h.wr]; exact hdst j hj) fun s₃ g₃ => ?_
  refine wp_add (op2_imm (by decide)) fun s₄ u₄ => wp_add (op2_imm (by decide)) fun s₅ u₅ =>
    wp_subs (op2_imm (by decide)) fun s₆ u₆ z₆ => WP.block_nil ?_
  have hr3 : s₆.gpr .r3 = BitVec.ofNat 32 (k - (j + 1)) := by
    rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), g₃.gpr, u₁.other _ (by decide), h.r3,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_ofNat (by omega), Nat.sub_sub]
  have hI : KI (w := w) s₂ st key k (j + 1) s₆ := by
    refine ⟨by omega, ?_, ?_, hr3, fun x h1 h2 h3 h4 => ?_, ?_, ?_, ?_, ?_⟩
    · rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), g₃.gpr, u₁.other _ (by decide), h.r1,
        BitVec.add_assoc (st + _), show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, ← BitVec.ofNat_add]
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, g₃.gpr, u₁.other _ (by decide), h.r2,
        BitVec.add_assoc, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, ← BitVec.ofNat_add]
    · rw [u₆.other x h3, u₅.other x h1, u₄.other x h2, g₃.gpr, u₁.other x h4, h.other x h1 h2 h3 h4]
    · rw [u₆.rd, u₅.rd, u₄.rd, g₃.rd, u₁.rd, h.rd]
    · rw [u₆.wr, u₅.wr, u₄.wr, g₃.wr, u₁.wr, h.wr]
    · rw [u₆.sp, u₅.sp, u₄.sp, g₃.sp, u₁.sp, h.sp]
    · have hj' : j < (bytesAt s₂.mem (State.addr key) k).length := by rw [bytesAt_length]; omega
      have hl : (List.take j (bytesAt s₂.mem (State.addr key) k)).length = j := by
        rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj')]
      rw [u₆.mem, u₅.mem, u₄.mem, g₃.mem, u₁.mem, u₁.gpr, hbyte, h.mem, List.take_add_one,
        List.getElem?_eq_getElem hj', Option.toList_some, writeBytes_snoc _ _ _ _ (by rw [hl]; omega), hl,
        setWidth_byte]
      congr 1
      simp [bytesAt]
  have hz : isa.eval .ne s₆ = some (decide (k - (j + 1) ≠ 0)) :=
    ne_iff s₆ (by rw [z₆, ← u₆.gpr, hr3]) (by omega)
  by_cases hjk : j + 1 = k
  · exact .inl ⟨by rw [hz]; simp; omega, hjk ▸ hI⟩
  · exact .inr ⟨by rw [hz]; simp; omega, k - (j + 1), by omega, j + 1, rfl, by omega, hI⟩

theorem zero_byte {m : Mem} {a : Addr} (h : m.readW a 32 = 0) {j : Nat} (hj : j < 4) :
    m (a + BitVec.ofNat 64 j) = 0 := by
  rw [← Mem.extractLsb'_read m a hj]
  have : m.read a 4 = 0 := by simpa [Mem.readW] using h
  rw [this]; simp

theorem ZInv.byte {s₁ s : State} (h : ZInv (w := w) s₁ (blockBytes w / 4) s) (hb : blockBytes w % 4 = 0)
    {i : Nat} (hi : i < blockBytes w) :
    s.mem (State.addr (s₁.gpr .r0) + BitVec.ofNat 64 (bufOff w) + BitVec.ofNat 64 i) = 0 := by
  have e : i = 4 * (i / 4) + i % 4 := (Nat.div_add_mod i 4).symm
  rw [e, ← Offset.add_add (State.addr (s₁.gpr .r0) + BitVec.ofNat 64 (bufOff w)) (4 * (i / 4)) (i % 4)]
  exact zero_byte (h.words _ (by omega)) (Nat.mod_lt _ (by decide))

theorem bytesAt_writeBytes_pad {m : Mem} {q : Addr} {xs : List Byte} {n : Nat} (hl : xs.length ≤ n)
    (hn : n < 2 ^ 64) (hz : ∀ i < n, xs.length ≤ i → m (q + BitVec.ofNat 64 i) = 0) :
    bytesAt (writeBytes m q xs) q n = xs ++ List.replicate (n - xs.length) 0 := by
  apply List.ext_getElem (by simp only [bytesAt_length, List.length_append, List.length_replicate]; omega)
  intro i h1 _
  rw [bytesAt_length] at h1
  simp only [bytesAt, List.getElem_map, List.getElem_range, writeBytes, Offset.add_sub_cancel_left,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega)]
  by_cases hi : i < xs.length
  · simp only [hi, ↓reduceIte, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some,
      List.getElem_append_left hi]
  · simp only [hi, ↓reduceIte, hz i h1 (by omega), List.getElem_append_right (Nat.le_of_not_lt hi),
      List.getElem_replicate]

theorem contains_widen {p a : Addr} {d k n : Nat} (hd : d < 2 ^ 64)
    (h : (⟨p + BitVec.ofNat 64 d, k⟩ : Region).Contains a n) : (⟨p, d + k⟩ : Region).Contains a n := by
  unfold Region.Contains at *
  have : (a - p).toNat ≤ (a - (p + BitVec.ofNat 64 d)).toNat + d := by
    rw [← Offset.sub_add_sub_cancel a (p + BitVec.ofNat 64 d) p, BitVec.toNat_add, Offset.add_sub_cancel_left,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt hd]
    exact Nat.mod_le _ _
  simp only at *
  omega

theorem keyBlock_ok (hw : w = 32 ∨ w = 64) {s : State}
    (hfit : (s.gpr .r0).toNat + (bufOff w + blockBytes w) ≤ 2 ^ 32)
    (hkf : (s.gpr .r2).toNat + (s.gpr .r3).toNat ≤ 2 ^ 32)
    (hk1 : (s.gpr .r3).toNat ≠ 0) (hkb : (s.gpr .r3).toNat ≤ blockBytes w)
    (hrd : s.rd = [⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩])
    (hwr : s.wr = [⟨State.addr (s.gpr .r0), bufOff w + blockBytes w⟩])
    (hd : Region.Disjoint ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩
      ⟨State.addr (s.gpr .r0), bufOff w + blockBytes w⟩) :
    WP isa (Impl.Blake2.Arm.Stream.keyBlock (w := w)) s fun s' =>
      (∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧
      (∀ i < bufOff w, s'.mem (State.addr (s.gpr .r0) + BitVec.ofNat 64 i) =
        s.mem (State.addr (s.gpr .r0) + BitVec.ofNat 64 i)) ∧
      bytesAt s'.mem (State.addr (s.gpr .r0) + BitVec.ofNat 64 (bufOff w)) (blockBytes w) =
        bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat ++
          List.replicate (blockBytes w - (s.gpr .r3).toNat) 0 := by
  have hs : bufOff w ≤ 64 ∧ blockBytes w ≤ 128 ∧ blockBytes w % 4 = 0 ∧
      encodable (BitVec.ofNat 32 (N w)) = true := by
    rcases hw with rfl | rfl <;> decide
  have hsub : Region.Sub ⟨State.addr (s.gpr .r0) + BitVec.ofNat 64 (bufOff w), blockBytes w⟩
      ⟨State.addr (s.gpr .r0), bufOff w + blockBytes w⟩ := Offset.sub_base _ (by omega)
  have hdb := hd.sub_right hsub
  unfold Impl.Blake2.Arm.Stream.keyBlock
  refine WP.seq ?_
  rw [List.cons_append]
  refine wp_mov (op2_imm (by decide)) fun s₁ u₁ => ?_
  have e0 : s₁.gpr .r0 = s.gpr .r0 := u₁.other _ (by decide)
  refine zero_all hw (by rw [e0]; omega) u₁.gpr (fun a n h => ?_) fun s₂ z₂ => ?_
  · obtain ⟨R, hR, hc⟩ := h
    simp only [List.mem_singleton] at hR; subst hR
    rw [u₁.wr, hwr]
    exact ⟨_, List.mem_singleton_self _, contains_widen (by omega) (by rw [e0] at hc; exact hc)⟩
  refine wp_add (op2_imm hs.2.2.2) fun s₃ u₃ => WP.block_nil ?_
  have g : ∀ r, r ≠ .r1 → r ≠ .r12 → s₃.gpr r = s.gpr r := fun r h1 h2 => by
    rw [u₃.other r h1, z₂.gpr, u₁.other r h2]
  have hm₃ : s₃.mem = s₂.mem := u₃.mem
  have hrd₃ : s₃.rd = s.rd := by rw [u₃.rd, z₂.rd, u₁.rd]
  have hwr₃ : s₃.wr = s.wr := by rw [u₃.wr, z₂.wr, u₁.wr]
  have hk : (s.gpr .r2) + BitVec.ofNat 32 0 = s.gpr .r2 := BitVec.add_zero _
  have hI : KI (w := w) s₃ (s.gpr .r0) (s.gpr .r2) (s.gpr .r3).toNat 0 s₃ :=
    ⟨Nat.zero_le _, by rw [u₃.gpr, z₂.gpr, e0, N_eq]; exact (BitVec.add_zero _).symm,
      by rw [g _ (by decide) (by decide), hk],
      by rw [g _ (by decide) (by decide), Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq],
      fun _ _ _ _ _ => rfl, rfl, rfl, rfl, by rw [List.take_zero, writeBytes_nil]⟩
  have hdk : Region.Disjoint ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩
      ⟨State.addr (s.gpr .r0) + BitVec.ofNat 64 (bufOff w), (s.gpr .r3).toNat⟩ :=
    hdb.sub_right (Offset.sub (e := bufOff w) (d := bufOff w) _ (Nat.le_refl _) (by omega)) |>.sub_right
      (fun _ h => h)
  refine WP.mono (keyLoop_ok (Nat.one_le_iff_ne_zero.mpr hk1) hkb hfit (by omega) hI
    (fun i hi => ⟨_, by rw [hrd₃, hrd]; exact List.mem_append_left _ (List.mem_singleton_self _),
      Offset.contains_base _ (by omega) (by omega)⟩)
    (fun i hi => ⟨_, by rw [hwr₃, hwr]; exact List.mem_singleton_self _,
      by rw [Offset.add_add]; exact Offset.contains_base _ (by omega) (by omega)⟩) hdk) fun s' h => ?_
  have hfr : Frame [⟨State.addr (s.gpr .r0) + BitVec.ofNat 64 (bufOff w), blockBytes w⟩] s.mem s₂.mem := by
    rw [← u₁.mem, ← e0]; exact z₂.frame
  have hkey : bytesAt s₃.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat =
      bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat := by
    rw [hm₃]
    exact bytesAt_congr fun i hi => hfr.bytes (R := ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hdb) (by dsimp only; omega) hi
  have hlen : (bytesAt s₃.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat).length = (s.gpr .r3).toNat :=
    bytesAt_length _ _ _
  have hmem := h.mem
  rw [List.take_of_length_le (Nat.le_of_eq hlen)] at hmem
  refine ⟨fun r h1 h2 h3 h4 => by rw [h.other r h1 h2 h3 h4, g r h1 h4], by rw [h.sp, u₃.sp, z₂.sp, u₁.sp],
    fun i hi => ?_, ?_⟩
  · rw [hmem, writeBytes_before _ _ _ hi (by rw [hlen]; omega), hm₃]
    exact hfr.bytes (R := ⟨State.addr (s.gpr .r0), bufOff w⟩)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (Offset.disjoint_base _ (Nat.le_refl _) (by omega)).symm) (by dsimp only; omega) hi
  · rw [hmem, bytesAt_writeBytes_pad (by omega) (by omega) fun i hi _ => ?_, hlen, hkey]
    rw [hm₃, ← e0]; exact z₂.byte hs.2.2.1 hi

end

/-! ## `init` -/

section
variable {w : Nat} {P : Params w}

theorem correct (hP : Ok P) {s₀ : State} (hp : (initArm P).pre s₀) :
    WP isa (Impl.Blake2.Arm.Stream.init P) s₀ fun s' => abiPreserved s₀ s' ∧ (initArm P).post s₀ s' := by
  obtain ⟨hrd, hwr, hd, hfit, hkf, -, hn2, hkm⟩ := hp
  have hw : w = 32 ∨ w = 64 := hP.w.symm
  have hmax : P.maxBytes ≤ blockBytes w := hP.max
  have hbb : blockBytes w ≤ 128 := by rcases hw with rfl | rfl <;> decide
  have hsubSt : Region.Sub ⟨State.addr (s₀.gpr .r0), bufOff w⟩
      ⟨State.addr (s₀.gpr .r0), bufOff w + blockBytes w⟩ := fun a h => by
    unfold Region.Contains at h ⊢; dsimp only at h ⊢; omega
  have hpres : ∀ r ∈ preserved, r ≠ .r1 ∧ r ≠ .r2 ∧ r ≠ .r3 ∧ r ≠ .r12 := by decide
  unfold Impl.Blake2.Arm.Stream.init
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (initState_ok hw (by omega) (fun a n h => ?_) (by omega) (by omega)) fun s₁ h₁ => ?_
  · obtain ⟨R, hR, hc⟩ := h
    simp only [List.mem_singleton] at hR; subst hR
    rw [hwr]
    refine ⟨_, List.mem_singleton_self _, ?_⟩
    unfold Region.Contains at hc ⊢; dsimp only at hc ⊢; omega
  refine wp_cmp (op2_imm (by decide)) fun s₂ f₂ z₂ => WP.block_nil ?_
  have g₂ : ∀ r, r ≠ .r12 → s₂.gpr r = s₀.gpr r := fun r hr => by rw [f₂.gpr, h₁.gpr r hr]
  have hm₂ : s₂.mem = s₁.mem := f₂.mem
  have hkey : bytesAt s₂.mem (State.addr (s₀.gpr .r2)) (s₀.gpr .r3).toNat =
      bytesAt s₀.mem (State.addr (s₀.gpr .r2)) (s₀.gpr .r3).toNat := by
    rw [hm₂]
    exact bytesAt_congr fun i hi => h₁.frame.bytes (R := ⟨State.addr (s₀.gpr .r2), (s₀.gpr .r3).toNat⟩)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hd.sub_right hsubSt)
      (by dsimp only; omega) hi
  have e3 : s₀.gpr .r3 = BitVec.ofNat 32 (s₀.gpr .r3).toNat := by simp
  have hz : isa.eval .eq s₂ = some (decide ((s₀.gpr .r3).toNat = 0)) := by
    show VG.Arm.eval .eq s₂ = _
    rw [eval_eq, z₂, h₁.gpr _ (by decide), e3, cmp0 (BitVec.isLt _), ← e3]
  refine WP.ite _ hz (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    refine ⟨⟨fun r hr => g₂ r (hpres r hr).2.2.2, by rw [f₂.sp, h₁.sp]⟩, ?_⟩
    refine repr_keyBlock P hP.pos (by rw [bytesAt_length]; omega) (by rw [hm₂]; exact h₁.state) fun h => ?_
    rw [bytesAt_length] at h; exact absurd hb h
  · simp only [decide_eq_false_iff_not] at hb
    have e0 := g₂ .r0 (by decide)
    have e2 := g₂ .r2 (by decide)
    have e3' := g₂ .r3 (by decide)
    refine WP.mono (keyBlock_ok hw (by rw [e0]; omega) (by rw [e2, e3']; omega) (by rw [e3']; exact hb)
      (by rw [e3']; omega) (by rw [f₂.rd, h₁.rd, hrd, e2, e3']) (by rw [f₂.wr, h₁.wr, hwr, e0])
      (by rw [e0, e2, e3']; exact hd)) fun s' ⟨hg, hsp, hst, hbytes⟩ => ?_
    refine ⟨⟨fun r hr => by
        obtain ⟨h1, h2, h3, h4⟩ := hpres r hr
        rw [hg r h1 h2 h3 h4, g₂ r h4], by rw [hsp, f₂.sp, h₁.sp]⟩, ?_⟩
    rw [e0, e2, e3', hkey] at hbytes
    rw [e0] at hst
    refine repr_keyBlock P hP.pos (by rw [bytesAt_length]; omega) ?_ fun _ => by rw [bytesAt_length]; exact hbytes
    rw [stateAt_congr hst, hm₂]; exact h₁.state

end

end VG.Proof.Blake2.Arm.Stream.Init
