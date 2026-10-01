import VerifiedGarbage.Proof.Blake2.AArch64.Stream.Common
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-!
# Streaming BLAKE2 on AArch64: `init`

Untrusted: everything here is checked by Lean. `initState` stores the
initial hash value (`initState_ok`); for a key, `keyBlock` zeroes the buffer
(`zero_ok`) and copies the key into it (`keyLoop_ok`). `init` is a leaf
function writing only `x2`, `x3` and `x9`–`x12`.
-/

namespace VG.Proof.Blake2.AArch64.Stream.Init

open VG VG.AArch64 VG.Spec.Blake2
open VG.Impl.Blake2.AArch64.Stream (N B initState)
open VG.Impl.Blake2.AArch64 (sz ws movImm64)
open VG.Proof.Blake2 (initAArch64 bufOff repr_keyBlock stateAt_congr)
open VG.Proof.MdStream.AArch64 (Upd Mupd WP.cons toNat_ofNat_lt wp_movz wp_addImm wp_subImm wp_ldrb wp_strb
  wp_str wp_str32 ofNat_succ)
open VG.WriteBytes (writeBytes writeBytes_nil writeBytes_snoc writeBytes_frame writeBytes_append
  write_eq_writeBytes)

/-! ## Instructions at the word size -/

section
variable {w : Nat} {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_movImm64 {d : Reg} {v : BitVec 64} {rest : List Instr}
    (k : ∀ s', Upd s s' d v → WP isa (.block rest) s' Q) :
    WP isa (.block (movImm64 d v ++ rest)) s Q := by
  simp only [movImm64, List.cons_append, List.nil_append]
  refine WP.cons rfl (WP.cons rfl (WP.cons rfl (WP.cons rfl (k _ ⟨?_, fun r h => ?_, rfl, rfl, rfl, rfl⟩))))
  · simp only [State.write, State.read, Size.bits, BitVec.setWidth_eq, ite_true]
    exact movz_movk64' v
  · simp [State.write, h]

theorem wp_strw (hw : w = 64 ∨ w = 32) {t n : Reg} {off : Nat} {a : Addr}
    (ho : off % (w / 8) = 0 ∧ off < 4096 * (w / 8))
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hout : InRegions s.wr a (w / 8))
    (k : ∀ s', Mupd s s' (s.mem.writeW a ((s.gpr t).setWidth w)) → WP isa (.block is) s' Q) :
    WP isa (.block (.str (sz w) t n off :: is)) s Q := by
  rcases hw with rfl | rfl
  · exact wp_str ho ha hout fun s' h => k s' (by rwa [BitVec.setWidth_eq])
  · exact wp_str32 ho ha hout k

theorem wp_lslw (hw : w = 64 ∨ w = 32) {d n : Reg}
    (k : ∀ s', Upd s s' d (((s.gpr n).setWidth w <<< 8).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.lsl (sz w) d n 8 :: is)) s Q := by
  rcases hw with rfl | rfl
  · exact WP.cons rfl (k _ (Upd.write s .x d _))
  · exact WP.cons rfl (k _ (Upd.write s .w d _))

theorem wp_eorw (hw : w = 64 ∨ w = 32) {d n m : Reg}
    (k : ∀ s', Upd s s' d (((s.gpr n).setWidth w ^^^ (s.gpr m).setWidth w).setWidth 64) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.logic .eor (sz w) d n m :: is)) s Q := by
  rcases hw with rfl | rfl
  · exact WP.cons rfl (k _ (Upd.write s .x d _))
  · exact WP.cons rfl (k _ (Upd.write s .w d _))

end

/-! ## Sizes -/

section
variable {w : Nat} (hw : w = 64 ∨ w = 32)
include hw

theorem w_le : w ≤ 64 := by omega

theorem word_in {j : Nat} (hj : j < 8) : w / 8 * j + w / 8 ≤ bufOff w := by
  rcases hw with rfl | rfl <;> simp only [bufOff] <;> omega

theorem word_sep {j k : Nat} (h : j ≠ k) :
    w / 8 * j + w / 8 ≤ w / 8 * k ∨ w / 8 * k + w / 8 ≤ w / 8 * j := by
  rcases hw with rfl | rfl <;> omega

theorem sizes : bufOff w + blockBytes w < 2 ^ 32 ∧ 16 ≤ blockBytes w ∧ blockBytes w % 8 = 0 ∧
    blockBytes w < 2 ^ (w - 8) ∧ w / 8 < 2 ^ 64 ∧ bufOff w ≤ 64 ∧ 0 < w / 8 ∧ w / 8 ≤ 8 := by
  rcases hw with rfl | rfl <;> decide

theorem readW_writeW_self_w (m : Mem) (a : Addr) (v : BitVec w) : (m.writeW a v).readW a w = v := by
  rcases hw with rfl | rfl
  · exact Mem.readW_writeW_self64 m a v
  · exact Mem.readW_writeW_self32 m a v

theorem setWidth_back (x : BitVec w) : (x.setWidth 64).setWidth w = x := by
  rw [BitVec.setWidth_setWidth_of_le _ (w_le hw), BitVec.setWidth_eq]

end

/-! ## The initial hash value -/

section
variable {w : Nat} (P : Params w)

/-- `IV[k]`, for any `k`. -/
def ivAt (k : Nat) : BitVec w := if h : k < 8 then P.IV[k] else 0

/-- The store of `IV[k + 1]`. -/
def ivStep (k : Nat) : List Instr :=
  movImm64 .x9 ((ivAt P (k + 1)).setWidth 64) ++ [.str (sz w) .x9 .x0 (ws w * (k + 1))]

theorem initState_eq : initState P = (List.range 7).flatMap (ivStep P) ++
    (movImm64 .x9 ((P.IV[0] ^^^ 0x01010000).setWidth 64) ++
    ([.lsl (sz w) .x10 .x3 8, .logic .eor (sz w) .x9 .x9 .x10, .logic .eor (sz w) .x9 .x9 .x1,
      .str (sz w) .x9 .x0 0] : List Instr)) := by
  rw [initState, List.append_assoc]
  rfl

/-- After storing `IV[1..k]`. -/
structure IvInv (s₀ : State) (k : Nat) (s : State) : Prop where
  gpr : ∀ r, r ≠ .x9 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [⟨s₀.gpr .x0, bufOff w⟩] s₀.mem s.mem
  words : ∀ j < k, s.mem.readW (s₀.gpr .x0 + BitVec.ofNat 64 (w / 8 * (j + 1))) w = ivAt P (j + 1)

variable {P}

theorem iv_step (hw : w = 64 ∨ w = 32) {s₀ : State}
    (hwr : ∀ a n, InRegions [⟨s₀.gpr .x0, bufOff w⟩] a n → InRegions s₀.wr a n)
    (k : Nat) (s : State) (hk : k < 7) (h : IvInv P s₀ k s) :
    WP isa (.block (ivStep P k)) s (IvInv P s₀ (k + 1)) := by
  have hs := sizes hw
  have hin : (⟨s₀.gpr .x0, bufOff w⟩ : Region).Contains
      (s₀.gpr .x0 + BitVec.ofNat 64 (w / 8 * (k + 1))) (w / 8) :=
    Offset.contains_base _ (word_in hw (by omega)) (by have := word_in hw (j := k + 1) (by omega); omega)
  refine wp_movImm64 fun s₁ u₁ => wp_strw hw (a := s₀.gpr .x0 + BitVec.ofNat 64 (w / 8 * (k + 1)))
    ⟨Nat.mul_mod_right _ _, by unfold ws; have := word_in hw (j := k + 1) (by omega); omega⟩ ?_ ?_
    fun s₂ g₂ => WP.block_nil ?_
  · rw [u₁.other _ (by decide), h.gpr _ (by decide)]; rfl
  · rw [u₁.wr, h.wr]; exact hwr _ _ ⟨_, List.mem_singleton_self _, hin⟩
  have hv : (s₁.gpr .x9).setWidth w = ivAt P (k + 1) := by rw [u₁.gpr, setWidth_back hw]
  refine ⟨fun r hr => by rw [g₂.gpr, u₁.other r hr, h.gpr r hr], by rw [g₂.rd, u₁.rd, h.rd],
    by rw [g₂.wr, u₁.wr, h.wr], by rw [g₂.sp, u₁.sp, h.sp], ?_, fun j hj => ?_⟩
  · rw [g₂.mem, u₁.mem]; exact h.frame.writeW (List.mem_singleton_self _) _ hin
  · rw [g₂.mem, hv, u₁.mem]
    by_cases e : j = k
    · subst e; exact readW_writeW_self_w hw _ _ _
    · rw [Mem.readW_writeW_sep (Offset.sep _ (word_sep hw (fun h => e (by omega)))
        (by have := word_in hw (j := j + 1) (by omega); omega)
        (by have := word_in hw (j := k + 1) (by omega); omega)) hs.2.2.2.2.1]
      exact h.words j (by omega)

/-- The state after `initState`. -/
structure StateOk (s₀ : State) (s : State) : Prop where
  gpr : ∀ r, r ≠ .x9 → r ≠ .x10 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [⟨s₀.gpr .x0, bufOff w⟩] s₀.mem s.mem
  state : stateAt w s.mem (s₀.gpr .x0) = Spec.Blake2.init P (s₀.gpr .x1).toNat (s₀.gpr .x3).toNat

theorem initState_ok (hw : w = 64 ∨ w = 32) {s₀ : State}
    (hwr : ∀ a n, InRegions [⟨s₀.gpr .x0, bufOff w⟩] a n → InRegions s₀.wr a n) :
    WP isa (.block (initState P)) s₀ (StateOk (P := P) s₀) := by
  have hs := sizes hw
  have hle := w_le hw
  rw [initState_eq, WP.block_append_iff]
  refine WP.mono (wp_range_flatMap (M := isa) (IvInv P s₀) (iv_step hw hwr) 7 (Nat.le_refl _) s₀
    ⟨fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _, fun _ h => absurd h (by omega)⟩) fun s₇ h₇ => ?_
  have hin : (⟨s₀.gpr .x0, bufOff w⟩ : Region).Contains (s₀.gpr .x0 + BitVec.ofNat 64 0) (w / 8) :=
    Offset.contains_base _ (by have := word_in hw (j := 0) (by omega); omega) (by omega)
  refine wp_movImm64 fun s₁ u₁ => wp_lslw hw fun s₂ u₂ => wp_eorw hw fun s₃ u₃ => wp_eorw hw fun s₄ u₄ =>
    wp_strw hw (a := s₀.gpr .x0 + BitVec.ofNat 64 0) ⟨Nat.zero_mod _, by omega⟩ ?_ ?_
    fun s₅ g₅ => WP.block_nil ?_
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide),
      h₇.gpr _ (by decide)]
  · rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr, h₇.wr]; exact hwr _ _ ⟨_, List.mem_singleton_self _, hin⟩
  have g : ∀ r, r ≠ .x9 → r ≠ .x10 → s₅.gpr r = s₀.gpr r := fun r h1 h2 => by
    rw [g₅.gpr, u₄.other r h1, u₃.other r h1, u₂.other r h2, u₁.other r h1, h₇.gpr r h1]
  -- The word stored.
  have hv : (s₄.gpr .x9).setWidth w = P.IV[0] ^^^ 0x01010000 ^^^
      (BitVec.ofNat w (s₀.gpr .x3).toNat <<< 8) ^^^ BitVec.ofNat w (s₀.gpr .x1).toNat := by
    rw [u₄.gpr, setWidth_back hw, u₃.other .x1 (by decide),
      u₃.gpr, setWidth_back hw, u₂.other .x9 (by decide), u₂.gpr, setWidth_back hw, u₁.gpr,
      setWidth_back hw, u₂.other .x1 (by decide), u₁.other .x1 (by decide), u₁.other .x3 (by decide),
      h₇.gpr .x1 (by decide), h₇.gpr .x3 (by decide), BitVec.ofNat_toNat, BitVec.ofNat_toNat]
    rfl
  have hm : s₅.mem = s₇.mem.writeW (s₀.gpr .x0 + BitVec.ofNat 64 0) ((s₄.gpr .x9).setWidth w) := by
    rw [g₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  refine ⟨g, by rw [g₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, h₇.rd],
    by rw [g₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h₇.wr], by rw [g₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp, h₇.sp],
    ?_, ?_⟩
  · rw [hm]; exact h₇.frame.writeW (List.mem_singleton_self _) _ hin
  · apply Vector.ext
    intro j hj
    rw [stateAt, Vector.getElem_ofFn, Spec.Blake2.init, Vector.getElem_set, hm]
    simp only
    split
    · rename_i e; subst e
      rw [Nat.mul_zero, readW_writeW_self_w hw, hv]
    · obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      have hsep : Mem.Sep (s₀.gpr .x0 + BitVec.ofNat 64 (w / 8 * (j + 1))) (w / 8)
          (s₀.gpr .x0 + BitVec.ofNat 64 0) (w / 8) :=
        Offset.sep _ (.inr (by rw [Nat.mul_succ]; omega))
          (by have := word_in hw (j := j + 1) hj; omega) (by have := word_in hw (j := 0) (by omega); omega)
      rw [Mem.readW_writeW_sep hsep hs.2.2.2.2.1, h₇.words j (by omega)]
      simp only [ivAt, hj, ↓reduceDIte]

end

/-! ## The key block -/

section
variable {w : Nat}

theorem writeW_zero (m : Mem) (a : Addr) :
    m.writeW a (0 : BitVec 64) = writeBytes m a (List.replicate 8 0) := by
  rw [Mem.writeW, write_eq_writeBytes]; rfl

theorem writeBytes_at (m : Mem) (q : Addr) (xs : List Byte) {i : Nat} (hi : i < 2 ^ 64) :
    writeBytes m q xs (q + BitVec.ofNat 64 i) =
      if i < xs.length then xs.getD i 0 else m (q + BitVec.ofNat 64 i) := by
  simp only [writeBytes, Mem.sub_ofNat_toNat q hi]

theorem bytesAt_writeBytes {m : Mem} {q : Addr} {xs : List Byte} {n : Nat} (hn : n < 2 ^ 64)
    (hx : xs.length ≤ n) (hz : ∀ i < n, m (q + BitVec.ofNat 64 i) = 0) :
    bytesAt (writeBytes m q xs) q n = xs ++ List.replicate (n - xs.length) 0 := by
  apply List.ext_getElem (by simp [bytesAt]; omega)
  intro i h1 _
  simp only [bytesAt, List.length_map, List.length_range] at h1
  simp only [bytesAt, List.getElem_map, List.getElem_range, writeBytes_at m q xs (by omega : i < 2 ^ 64)]
  by_cases hi : i < xs.length
  · simp only [hi, ↓reduceIte]
    rw [List.getElem_append_left hi, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
      Option.getD_some]
  · simp only [hi, ↓reduceIte]
    rw [hz i h1, List.getElem_append_right (by omega), List.getElem_replicate]

/-- After zeroing `8 · j` bytes of the buffer, from `σ`. -/
structure ZInv (σ : State) (j : Nat) (s : State) : Prop where
  gpr : s.gpr = σ.gpr
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  sp : s.sp = σ.sp
  mem : s.mem = writeBytes σ.mem (σ.gpr .x0 + BitVec.ofNat 64 (bufOff w)) (List.replicate (8 * j) 0)

theorem zero_ok (hw : w = 64 ∨ w = 32) {σ : State} (hx9 : σ.gpr .x9 = 0)
    (hwr : ∀ a n, InRegions [⟨σ.gpr .x0, bufOff w + blockBytes w⟩] a n → InRegions σ.wr a n) :
    WP isa (.block ((List.range (B w / 8)).flatMap fun j => [.str .x .x9 .x0 (N w + 8 * j)])) σ
      (ZInv (w := w) σ (blockBytes w / 8)) := by
  have hs := sizes hw
  refine wp_range_flatMap (M := isa) (ZInv (w := w) σ) (fun j s hj h => ?_) _ (Nat.le_refl _) σ
    ⟨rfl, rfl, rfl, rfl, by rw [Nat.mul_zero, List.replicate_zero, writeBytes_nil]⟩
  rw [B_eq] at hj
  refine wp_str (a := σ.gpr .x0 + BitVec.ofNat 64 (bufOff w + 8 * j)) ⟨?_, ?_⟩ (by rw [h.gpr, N_eq])
    ?_ fun s' g' => WP.block_nil ⟨g'.gpr.trans h.gpr, g'.rd.trans h.rd, g'.wr.trans h.wr, g'.sp.trans h.sp, ?_⟩
  · rw [N_eq]; rcases hw with rfl | rfl <;> simp only [bufOff] <;> omega
  · rw [N_eq]; rcases hw with rfl | rfl <;> simp only [bufOff, blockBytes] at hj ⊢ <;> omega
  · rw [h.wr]; exact hwr _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base _ (by omega) (by omega)⟩
  · have e := writeBytes_append σ.mem (σ.gpr .x0 + BitVec.ofNat 64 (bufOff w))
      (List.replicate (8 * j) 0) (List.replicate 8 0) (by simp; omega)
    rw [List.length_replicate] at e
    rw [g'.mem, h.mem, h.gpr, hx9, writeW_zero, ← Offset.add_ofNat_add_ofNat, e,
      List.replicate_append_replicate, Nat.mul_succ]

section
variable (s₀ : State)

abbrev st : Addr := s₀.gpr .x0
abbrev kp : Addr := s₀.gpr .x2
abbrev kk : Nat := (s₀.gpr .x3).toNat
abbrev buf (w : Nat) : Addr := st s₀ + BitVec.ofNat 64 (bufOff w)
abbrev stR (w : Nat) : Region := ⟨st s₀, bufOff w + blockBytes w⟩
abbrev kR : Region := ⟨kp s₀, kk s₀⟩
/-- The key. -/
abbrev key : List Byte := bytesAt s₀.mem (kp s₀) (kk s₀)

end

/-- After copying `j` bytes of the key over the zeroed buffer `Z`. -/
structure KInv (s₀ : State) (Z : Mem) (j : Nat) (s : State) : Prop where
  j_le : j ≤ kk s₀
  x2 : s.gpr .x2 = kp s₀ + BitVec.ofNat 64 j
  x12 : s.gpr .x12 = buf s₀ w + BitVec.ofNat 64 j
  x3 : s.gpr .x3 = BitVec.ofNat 64 (kk s₀ - j)
  other : ∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x2 → r ≠ .x3 → r ≠ .x12 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  mem : s.mem = writeBytes Z (buf s₀ w) ((key s₀).take j)

theorem keyLoop_ok (hw : w = 64 ∨ w = 32) {s₀ : State} {Z : Mem} {σ : State}
    (hrd : s₀.rd = [kR s₀]) (hwr : s₀.wr = [stR s₀ w]) (hd : (kR s₀).Disjoint (stR s₀ w))
    (hk : 1 ≤ kk s₀) (hkb : kk s₀ ≤ blockBytes w) (hZ : Frame [stR s₀ w] s₀.mem Z)
    (hσ : KInv (w := w) s₀ Z 0 σ) :
    WP isa (.loop (.block [.ldrb .x9 .x2 0, .strb .x9 .x12 0, .addImm .x .x2 .x2 1,
        .addImm .x .x12 .x12 1, .subImm .x .x3 .x3 1]) (.nonzero .x .x3)) σ
      (KInv (w := w) s₀ Z (kk s₀)) := by
  have hs := sizes hw
  have hkl : kk s₀ < 2 ^ 64 := (s₀.gpr .x3).isLt
  refine WP.loop (M := isa) (fun n (s : State) => ∃ j, n = kk s₀ - j ∧ j < kk s₀ ∧ KInv (w := w) s₀ Z j s)
    ?_ (kk s₀) σ ⟨0, by omega, by omega, hσ⟩
  rintro n s ⟨j, rfl, hj, h⟩
  -- The key byte read is unchanged.
  have hbyte : s.mem (kp s₀ + BitVec.ofNat 64 j) = s₀.mem (kp s₀ + BitVec.ofNat 64 j) := by
    rw [h.mem]
    have hf : Frame [stR s₀ w] s₀.mem (writeBytes Z (buf s₀ w) ((key s₀).take j)) :=
      hZ.trans (writeBytes_frame Z _ _ (Offset.contains_base _ (by simp; omega) (by omega)))
    exact hf.bytes (R := kR s₀) (by simpa using hd) (by simp; omega) hj
  have hin : InRegions (s.rd ++ s.wr) (kp s₀ + BitVec.ofNat 64 j) 1 := by
    rw [h.rd, hrd]; exact ⟨_, List.mem_cons_self .., Offset.contains_base _ (by omega) (by omega)⟩
  have hout : InRegions s.wr (buf s₀ w + BitVec.ofNat 64 j) 1 := by
    rw [h.wr, hwr, Offset.add_ofNat_add_ofNat]
    exact ⟨_, List.mem_cons_self .., Offset.contains_base _ (by omega) (by omega)⟩
  refine wp_ldrb (a := kp s₀ + BitVec.ofNat 64 j) (by decide) (by rw [h.x2]; simp) hin fun s₁ u₁ => ?_
  refine wp_strb (a := buf s₀ w + BitVec.ofNat 64 j) (by decide) (by rw [u₁.other _ (by decide), h.x12]; simp)
    (by rw [u₁.wr]; exact hout) fun s₂ g₂ => ?_
  refine wp_addImm (by decide) fun s₃ u₃ => wp_addImm (by decide) fun s₄ u₄ =>
    wp_subImm (by decide) fun s₅ u₅ => WP.block_nil ?_
  have hx3 : s₅.gpr .x3 = BitVec.ofNat 64 (kk s₀ - (j + 1)) := by
    rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), g₂.gpr, u₁.other _ (by decide), h.x3,
      sub_ofNat (by omega), Nat.sub_sub]
  have hI : KInv (w := w) s₀ Z (j + 1) s₅ := by
    refine ⟨by omega, ?_, ?_, hx3, fun r h1 h2 h3 h4 h5 => ?_, ?_, ?_, ?_, ?_⟩
    · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, g₂.gpr, u₁.other _ (by decide), h.x2,
        BitVec.add_assoc, ← BitVec.ofNat_add]
    · rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), g₂.gpr, u₁.other _ (by decide), h.x12,
        BitVec.add_assoc, ← BitVec.ofNat_add]
    · rw [u₅.other r h4, u₄.other r h5, u₃.other r h3, g₂.gpr, u₁.other r h1, h.other r h1 h2 h3 h4 h5]
    · rw [u₅.rd, u₄.rd, u₃.rd, g₂.rd, u₁.rd, h.rd]
    · rw [u₅.wr, u₄.wr, u₃.wr, g₂.wr, u₁.wr, h.wr]
    · rw [u₅.sp, u₄.sp, u₃.sp, g₂.sp, u₁.sp, h.sp]
    · have hj' : j < (key s₀).length := by simp [bytesAt]; omega
      have hl : (List.take j (key s₀)).length = j := by
        rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj')]
      rw [u₅.mem, u₄.mem, u₃.mem, g₂.mem, u₁.mem, u₁.gpr, hbyte, h.mem, List.take_add_one,
        List.getElem?_eq_getElem hj', Option.toList_some,
        writeBytes_snoc _ _ _ _ (by rw [hl]; omega), hl, setWidth_byte]
      congr 1
      simp [bytesAt]
  by_cases hjk : j + 1 = kk s₀
  · refine .inl ⟨?_, hjk ▸ hI⟩
    show VG.AArch64.eval (.nonzero .x .x3) s₅ = _
    rw [MdStream.AArch64.eval_nonzero, hx3, bne, MdStream.AArch64.ofNat_beq_zero (by omega)]
    simp; omega
  · refine .inr ⟨?_, kk s₀ - (j + 1), by omega, j + 1, rfl, by omega, hI⟩
    show VG.AArch64.eval (.nonzero .x .x3) s₅ = _
    rw [MdStream.AArch64.eval_nonzero, hx3, bne, MdStream.AArch64.ofNat_beq_zero (by omega)]
    simp; omega

end

section
variable {w : Nat} {P : Params w}

theorem keyBlock_eq : Impl.Blake2.AArch64.Stream.keyBlock (w := w) =
    .seq (.block ((.movz .x .x9 0 0 :: (List.range (B w / 8)).flatMap fun j =>
        ([.str .x .x9 .x0 (N w + 8 * j)] : List Instr)) ++ ([.addImm .x .x12 .x0 (N w)] : List Instr)))
      (.loop (.block [.ldrb .x9 .x2 0, .strb .x9 .x12 0, .addImm .x .x2 .x2 1, .addImm .x .x12 .x12 1,
        .subImm .x .x3 .x3 1]) (.nonzero .x .x3)) := by
  rw [Impl.Blake2.AArch64.Stream.keyBlock, List.map_eq_flatMap]

theorem keyBlock_ok (hw : w = 64 ∨ w = 32) {s₀ σ : State}
    (hrd : s₀.rd = [kR s₀]) (hwr : s₀.wr = [stR s₀ w]) (hd : (kR s₀).Disjoint (stR s₀ w))
    (hk : 1 ≤ kk s₀) (hkb : kk s₀ ≤ blockBytes w) (hσ : StateOk (P := P) s₀ σ) :
    WP isa (Impl.Blake2.AArch64.Stream.keyBlock (w := w)) σ fun s =>
      (∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x2 → r ≠ .x3 → r ≠ .x12 → s.gpr r = s₀.gpr r) ∧
      s.sp = s₀.sp ∧ Frame [⟨buf s₀ w, blockBytes w⟩] σ.mem s.mem ∧
      bytesAt s.mem (buf s₀ w) (blockBytes w) = key s₀ ++ List.replicate (blockBytes w - kk s₀) 0 := by
  have hs := sizes hw
  have hxs : (key s₀).length = kk s₀ := by simp [bytesAt]
  have hbuf : ∀ n, n ≤ blockBytes w → (stR s₀ w).Contains (buf s₀ w) n := fun n hn =>
    Offset.contains_base _ (by omega) (by omega)
  have hσ0 : σ.gpr .x0 = st s₀ := hσ.gpr _ (by decide) (by decide)
  rw [keyBlock_eq]
  refine WP.seq (wp_movz fun σ₁ u₁ => ?_)
  rw [List.append_eq, WP.block_append_iff]
  refine WP.mono (zero_ok hw (σ := σ₁) (by rw [u₁.gpr]; rfl) ?_) fun s₂ h₂ => ?_
  · rw [u₁.wr, hσ.wr, hwr, u₁.other _ (by decide), hσ0]; exact fun _ _ h => h
  have hZ : s₂.mem = writeBytes σ.mem (buf s₀ w) (List.replicate (blockBytes w) 0) := by
    rw [h₂.mem, u₁.other _ (by decide), hσ0, u₁.mem, Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hs.2.2.1)]
  have hfZ : Frame [stR s₀ w] s₀.mem s₂.mem := by
    rw [hZ]
    exact (hσ.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨stR s₀ w, List.mem_singleton_self _, Region.sub_prefix (by omega)⟩).trans
      (writeBytes_frame _ _ _ (by simpa using hbuf _ (Nat.le_refl _)))
  refine wp_addImm (by rw [N_eq]; omega) fun s₃ u₃ => WP.block_nil ?_
  refine WP.mono (keyLoop_ok hw hrd hwr hd hk hkb hfZ ⟨Nat.zero_le _, ?_, ?_, ?_, ?_,
    by rw [u₃.rd, h₂.rd, u₁.rd, hσ.rd], by rw [u₃.wr, h₂.wr, u₁.wr, hσ.wr],
    by rw [u₃.sp, h₂.sp, u₁.sp, hσ.sp], ?_⟩) fun s h => ?_
  · rw [u₃.other _ (by decide), h₂.gpr, u₁.other _ (by decide), hσ.gpr _ (by decide) (by decide)]; simp
  · rw [u₃.gpr, h₂.gpr, u₁.other _ (by decide), hσ0, N_eq]; simp
  · rw [u₃.other _ (by decide), h₂.gpr, u₁.other _ (by decide), hσ.gpr _ (by decide) (by decide),
      Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · intro r h1 h2 h3 h4 h5
    rw [u₃.other r h5, h₂.gpr, u₁.other r h1, hσ.gpr r h1 h2]
  · rw [u₃.mem, List.take_zero, writeBytes_nil]
  have hm : s.mem = writeBytes (writeBytes σ.mem (buf s₀ w) (List.replicate (blockBytes w) 0))
      (buf s₀ w) (key s₀) := by
    rw [h.mem, List.take_of_length_le (by omega), hZ]
  refine ⟨h.other, h.sp, ?_, ?_⟩
  · rw [hm]
    exact (writeBytes_frame _ _ _ (contains_prefix _ (by simp))).trans
      (writeBytes_frame _ _ _ (contains_prefix _ (by omega)))
  · rw [hm, bytesAt_writeBytes (by omega) (by omega) fun i hi => ?_, hxs]
    rw [writeBytes_at _ _ _ (by omega)]
    simp [hi]

end

/-! ## The whole function -/

/-- `init` stores the initial hash value and, for a key, the key block. -/
theorem correct {w : Nat} {P : Params w} {s₀ : State} (hP : Ok P) (hp : (initAArch64 P).pre s₀) :
    WP isa (Impl.Blake2.AArch64.Stream.init P) s₀ fun s' =>
      GprAbi s₀ s' ∧ (initAArch64 P).post s₀ s' := by
  obtain ⟨hrd, hwr, hd, -, -, hkk⟩ := hp
  have hw := hP.w
  have hs := sizes hw
  have hkb : kk s₀ ≤ blockBytes w := Nat.le_trans hkk hP.max
  have hxs : (key s₀).length = kk s₀ := by simp [bytesAt]
  have hsub : ∀ r ∈ [(⟨st s₀, bufOff w⟩ : Region)], ∃ r' ∈ [stR s₀ w], Region.Sub r r' := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨stR s₀ w, List.mem_singleton_self _, Region.sub_prefix (by omega)⟩
  have hcs : ∀ r ∈ preserved, r ≠ .x9 ∧ r ≠ .x10 ∧ r ≠ .x2 ∧ r ≠ .x3 ∧ r ≠ .x12 := by decide
  unfold Impl.Blake2.AArch64.Stream.init
  refine WP.seq (WP.mono (initState_ok (P := P) hw (fun a n h => ?_)) fun σ hσ => ?_)
  · rw [hwr]
    obtain ⟨r, hr, hc⟩ := h
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc ⊢; omega⟩
  have hx3 : σ.gpr .x3 = BitVec.ofNat 64 (kk s₀) := by
    rw [hσ.gpr _ (by decide) (by decide), BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine WP.ite _ (zero_iff σ hx3 (s₀.gpr .x3).isLt) (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    refine ⟨⟨fun r hr => hσ.gpr r (hcs r hr).1 (hcs r hr).2.1, hσ.sp⟩, ?_⟩
    exact repr_keyBlock P hP.pos (hxs ▸ hkb) hσ.state fun h => absurd (hxs ▸ hb) h
  · simp only [decide_eq_false_iff_not] at hb
    refine WP.mono (keyBlock_ok hw hrd hwr hd (by omega) hkb hσ) fun s ⟨hg, hsp, hf, hb'⟩ => ?_
    refine ⟨⟨fun r hr => hg r (hcs r hr).1 (hcs r hr).2.1 (hcs r hr).2.2.1 (hcs r hr).2.2.2.1
      (hcs r hr).2.2.2.2, hsp⟩, ?_⟩
    refine repr_keyBlock P hP.pos (hxs ▸ hkb) ?_ fun _ => by rw [hxs]; exact hb'
    rw [← hσ.state]
    exact stateAt_congr fun i hi => hf.bytes (R := ⟨st s₀, bufOff w⟩)
      (by simpa using Offset.base_disjoint (st s₀) (Nat.le_refl (bufOff w)) (n := blockBytes w) (by omega))
      (by simp only; omega) hi

end VG.Proof.Blake2.AArch64.Stream.Init
