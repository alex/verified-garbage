import VerifiedGarbage.Proof.Blake2.X86_64.Stream.Common
import VerifiedGarbage.Proof.Framework.Range

/-!
# Streaming BLAKE2 on x86-64: `init`

`initState` stores the initial hash value (`initState_ok`); for a key,
`keyBlock` zeroes the buffer (`zero_ok`) and copies the key into it
(`keyLoop_ok`).
-/

namespace VG.Proof.Blake2.X86_64.Stream.Init

open VG VG.X86_64 VG.Spec.Blake2
open VG.Impl.Blake2.X86_64.Stream (initState)
open VG.Impl.Blake2.X86_64 (at_ ws imm)
open VG.Proof.Blake2 (initX86_64 bufOff repr_keyBlock stateAt_congr)
open VG.Proof.Blake2.X86_64.Stream (Ok N_eq B_eq)
open VG.Proof.MdStream.X86_64 (Upd WP.cons wp_mov wp_mov32i wp_store wp_store32 wp_store8 wp_movzx8
  wp_addi wp_subi wp_test ofInt_natCast sx1 ofNat_succ ofNat_pred ofNat_beq_zero toNat_ofNat_lt)
open VG.WriteBytes (writeBytes writeBytes_nil writeBytes_snoc writeBytes_frame writeBytes_append
  write_eq_writeBytes)

/-! ## Instructions at the word size -/

section
variable {w : Nat} {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_imm (hw : w = 64 ∨ w = 32) {d : Reg} {v : BitVec w}
    (k : ∀ s', Upd s s' d (v.setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (imm w d v :: is)) s Q := by
  rcases hw with rfl | rfl
  · exact WP.cons rfl (k _ (Upd.setReg _ _ _))
  · exact WP.cons rfl (k _ (BitVec.setWidth_eq v ▸ Upd.setReg s d ((v.setWidth 32).setWidth 64)))

theorem wp_st (hw : w = 64 ∨ w = 32) {m : MemOp} {r : Reg} {a : Addr} (ha : s.ea m = a)
    (hout : InRegions s.wr a (w / 8))
    (k : ∀ s', s'.gpr = s.gpr → s'.mem = s.mem.writeW a ((s.gpr r).setWidth w) → s'.rd = s.rd →
      s'.wr = s.wr → WP isa (.block is) s' Q) :
    WP isa (.block (VG.Impl.Blake2.X86_64.st w m r :: is)) s Q := by
  rcases hw with rfl | rfl
  · exact wp_store ha hout fun s' g m rd wr => k s' g (by rw [m, BitVec.setWidth_eq]) rd wr
  · exact wp_store32 ha hout k

theorem wp_xorw (hw : w = 64 ∨ w = 32) {d r : Reg}
    (k : ∀ s', Upd s s' d (((s.gpr d).setWidth w ^^^ (s.gpr r).setWidth w).setWidth 64) →
      WP isa (.block is) s' Q) :
    WP isa (.block (VG.Impl.Blake2.X86_64.xor w d (.reg r) :: is)) s Q := by
  rcases hw with rfl | rfl
  · refine WP.cons rfl (k _ ?_)
    simp only [BitVec.setWidth_eq]
    exact Upd.flags s d (s.gpr d ^^^ s.gpr r) false false _
  · exact WP.cons rfl (k _ (Upd.flags s d (w := 32) _ false false _))

theorem wp_rorw (hw : w = 64 ∨ w = 32) {d : Reg}
    (k : ∀ s', Upd s s' d ((((s.gpr d).setWidth w).rotateRight (w - 8)).setWidth 64) →
      WP isa (.block is) s' Q) :
    WP isa (.block (VG.Impl.Blake2.X86_64.ror w d (w - 8) :: is)) s Q := by
  rcases hw with rfl | rfl
  · refine WP.cons rfl (k _ ?_)
    simp only [BitVec.setWidth_eq]
    exact ⟨by simp [State.setReg], fun r h => by simp [State.setReg, h]; rfl, rfl, rfl, rfl⟩
  · refine WP.cons rfl (k _ ?_)
    exact ⟨by simp [State.setReg32, State.setReg], fun r h => by simp [State.setReg32, State.setReg, h]; rfl,
      rfl, rfl, rfl⟩

end

/-! ## Arithmetic -/

theorem ea_at (s : State) (b : Reg) (d : Nat) : s.ea (at_ b d) = s.gpr b + BitVec.ofNat 64 d := by
  show s.gpr b + BitVec.ofInt 64 (d : Int) = _
  rw [ofInt_natCast]

theorem ws_eq (w : Nat) : ws w = w / 8 := rfl

theorem rotr_eq {w : Nat} (hw : w = 64 ∨ w = 32) (x : BitVec w) (h : x.toNat < 2 ^ (w - 8)) :
    x.rotateRight (w - 8) = x <<< 8 := by
  have h0 : x >>> ((w - 8) % w) = 0#w := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega),
      Nat.div_eq_of_lt h]; rfl
  rw [BitVec.rotateRight_def, h0, BitVec.zero_or, Nat.mod_eq_of_lt (by omega),
    show w - (w - 8) = 8 by omega]

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
    blockBytes w < 2 ^ (w - 8) ∧ w / 8 < 2 ^ 64 := by
  rcases hw with rfl | rfl <;> decide

theorem readW_writeW_self_w (m : Mem) (a : Addr) (v : BitVec w) : (m.writeW a v).readW a w = v := by
  rcases hw with rfl | rfl
  · exact Mem.readW_writeW_self64 m a v
  · exact Mem.readW_writeW_self32 m a v

end

/-! ## Bytes -/

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

theorem writeW_zero (m : Mem) (a : Addr) :
    m.writeW a (0 : BitVec 64) = writeBytes m a (List.replicate 8 0) := by
  rw [Mem.writeW, write_eq_writeBytes]; rfl

/-! ## The initial hash value -/

section
variable {w : Nat} (P : Params w)

/-- `IV[k]`, for any `k`. -/
def ivAt (k : Nat) : BitVec w := if h : k < 8 then P.IV[k] else 0

/-- The store of `IV[k + 1]`. -/
def ivStep (k : Nat) : List Instr :=
  [imm w .rax (ivAt P (k + 1)), VG.Impl.Blake2.X86_64.st w (at_ .rdi (ws w * (k + 1))) .rax]

theorem initState_eq : initState P = (List.range 7).flatMap (ivStep P) ++
    [imm w .rax (P.IV[0] ^^^ 0x01010000), .mov .r8 (.reg .rcx),
      VG.Impl.Blake2.X86_64.ror w .r8 (w - 8), VG.Impl.Blake2.X86_64.xor w .rax (.reg .r8),
      VG.Impl.Blake2.X86_64.xor w .rax (.reg .rsi), VG.Impl.Blake2.X86_64.st w (at_ .rdi 0) .rax] := rfl

/-- After storing `IV[1..k]`. -/
structure IvInv (s₀ : State) (k : Nat) (s : State) : Prop where
  gpr : ∀ r, r ≠ .rax → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [⟨s₀.gpr .rdi, bufOff w⟩] s₀.mem s.mem
  words : ∀ j < k, s.mem.readW (s₀.gpr .rdi + BitVec.ofNat 64 (w / 8 * (j + 1))) w = ivAt P (j + 1)

variable {P}

theorem iv_step (hw : w = 64 ∨ w = 32) {s₀ : State}
    (hwr : ∀ a n, InRegions [⟨s₀.gpr .rdi, bufOff w⟩] a n → InRegions s₀.wr a n)
    (k : Nat) (s : State) (hk : k < 7) (h : IvInv P s₀ k s) :
    WP isa (.block (ivStep P k)) s (IvInv P s₀ (k + 1)) := by
  have hin : (⟨s₀.gpr .rdi, bufOff w⟩ : Region).Contains
      (s₀.gpr .rdi + BitVec.ofNat 64 (w / 8 * (k + 1))) (w / 8) :=
    Offset.contains_base _ (word_in hw (by omega))
      (by have := word_in hw (j := k + 1) (by omega); have := (sizes hw).1; omega)
  refine wp_imm hw fun s₁ u₁ => wp_st hw (a := s₀.gpr .rdi + BitVec.ofNat 64 (w / 8 * (k + 1))) ?_ ?_
    fun s₂ g₂ m₂ rd₂ wr₂ => WP.block_nil ?_
  · rw [ea_at, u₁.other _ (by decide), h.gpr _ (by decide), ws_eq]
  · rw [u₁.wr, h.wr]; exact hwr _ _ ⟨_, List.mem_singleton_self _, hin⟩
  have hv : (s₁.gpr .rax).setWidth w = ivAt P (k + 1) := by
    rw [u₁.gpr, BitVec.setWidth_setWidth_of_le _ (w_le hw), BitVec.setWidth_eq]
  refine ⟨fun r hr => by rw [g₂, u₁.other r hr, h.gpr r hr], by rw [rd₂, u₁.rd, h.rd],
    by rw [wr₂, u₁.wr, h.wr], ?_, fun j hj => ?_⟩
  · rw [m₂, u₁.mem]; exact h.frame.writeW (List.mem_singleton_self _) _ hin
  · rw [m₂, hv, u₁.mem]
    by_cases e : j = k
    · subst e; exact readW_writeW_self_w hw _ _ _
    · have hs := sizes hw
      rw [Mem.readW_writeW_sep (Offset.sep _ (word_sep hw (fun h => e (by omega)))
        (by have := word_in hw (j := j + 1) (by omega); omega)
        (by have := word_in hw (j := k + 1) (by omega); omega)) hs.2.2.2.2]
      exact h.words j (by omega)

/-- The state after `initState` and the test of `keylen`. -/
structure StateOk (s₀ : State) (s : State) : Prop where
  gpr : ∀ r, r ≠ .rax → r ≠ .r8 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [⟨s₀.gpr .rdi, bufOff w⟩] s₀.mem s.mem
  state : stateAt w s.mem (s₀.gpr .rdi) = Spec.Blake2.init P (s₀.gpr .rsi).toNat (s₀.gpr .rcx).toNat
  zf : s.zf = some (decide ((s₀.gpr .rcx).toNat = 0))

theorem initState_ok (hw : w = 64 ∨ w = 32) {s₀ : State}
    (hwr : ∀ a n, InRegions [⟨s₀.gpr .rdi, bufOff w⟩] a n → InRegions s₀.wr a n)
    (hkk : (s₀.gpr .rcx).toNat < 2 ^ (w - 8)) :
    WP isa (.block (initState P ++ ([.alu .test .rcx (.reg .rcx)] : List Instr))) s₀ (StateOk (P := P) s₀) := by
  have hs := sizes hw
  have hle := w_le hw
  rw [initState_eq, List.append_assoc, WP.block_append_iff]
  refine WP.mono (wp_range_flatMap (M := isa) (IvInv P s₀) (iv_step hw hwr) 7 (Nat.le_refl _) s₀
    ⟨fun _ _ => rfl, rfl, rfl, Frame.refl _ _, fun _ h => absurd h (by omega)⟩) fun s₇ h₇ => ?_
  have hin : (⟨s₀.gpr .rdi, bufOff w⟩ : Region).Contains (s₀.gpr .rdi + BitVec.ofNat 64 0) (w / 8) :=
    Offset.contains_base _ (by have := word_in hw (j := 0) (by omega); omega) (by omega)
  refine wp_imm hw fun s₁ u₁ => wp_mov fun s₂ u₂ _ _ => wp_rorw hw fun s₃ u₃ => wp_xorw hw fun s₄ u₄ =>
    wp_xorw hw fun s₅ u₅ => wp_st hw (a := s₀.gpr .rdi + BitVec.ofNat 64 0) ?_ ?_
    fun s₆ g₆ m₆ rd₆ wr₆ => wp_test fun s₇' g₇ m₇ rd₇ wr₇ z₇ => WP.block_nil ?_
  · rw [ea_at, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), h₇.gpr _ (by decide)]
  · rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h₇.wr]; exact hwr _ _ ⟨_, List.mem_singleton_self _, hin⟩
  have g : ∀ r, r ≠ .rax → r ≠ .r8 → s₇'.gpr r = s₀.gpr r := fun r h1 h2 => by
    rw [g₇, g₆, u₅.other r h1, u₄.other r h1, u₃.other r h2, u₂.other r h2, u₁.other r h1, h₇.gpr r h1]
  -- The word stored.
  have hv : (s₅.gpr .rax).setWidth w = P.IV[0] ^^^ 0x01010000 ^^^
      (BitVec.ofNat w (s₀.gpr .rcx).toNat <<< 8) ^^^ BitVec.ofNat w (s₀.gpr .rsi).toNat := by
    have sw : ∀ x : BitVec w, (x.setWidth 64).setWidth w = x := fun x => by
      rw [BitVec.setWidth_setWidth_of_le _ hle, BitVec.setWidth_eq]
    simp only [u₅.gpr, u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr, u₄.other .rsi (by decide),
      u₃.other .rax (by decide), u₃.other .rsi (by decide), u₂.other .rax (by decide),
      u₂.other .rsi (by decide), u₁.other .rsi (by decide), u₁.other .rcx (by decide),
      h₇.gpr .rsi (by decide), h₇.gpr .rcx (by decide), sw]
    rw [← BitVec.ofNat_toNat w (s₀.gpr .rcx), ← BitVec.ofNat_toNat w (s₀.gpr .rsi),
      rotr_eq hw _ (by rw [BitVec.toNat_ofNat]; exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) hkk)]
    rfl
  have hm : s₇'.mem = s₇.mem.writeW (s₀.gpr .rdi + BitVec.ofNat 64 0) ((s₅.gpr .rax).setWidth w) := by
    rw [m₇, m₆, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  refine ⟨g, by rw [rd₇, rd₆, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, h₇.rd],
    by rw [wr₇, wr₆, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h₇.wr], ?_, ?_, ?_⟩
  · rw [hm]; exact h₇.frame.writeW (List.mem_singleton_self _) _ hin
  · apply Vector.ext
    intro j hj
    rw [stateAt, Vector.getElem_ofFn, Spec.Blake2.init, Vector.getElem_set, hm]
    simp only
    split
    · rename_i e; subst e
      rw [Nat.mul_zero, readW_writeW_self_w hw, hv]
    · obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      have hsep : Mem.Sep (s₀.gpr .rdi + BitVec.ofNat 64 (w / 8 * (j + 1))) (w / 8)
          (s₀.gpr .rdi + BitVec.ofNat 64 0) (w / 8) :=
        Offset.sep _ (.inr (by rw [Nat.mul_succ]; omega))
          (by have := word_in hw (j := j + 1) hj; omega) (by have := word_in hw (j := 0) (by omega); omega)
      rw [Mem.readW_writeW_sep hsep hs.2.2.2.2, h₇.words j (by omega)]
      simp only [ivAt, hj, ↓reduceDIte]
  · rw [z₇, g₆, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), h₇.gpr _ (by decide), BitVec.and_self,
      ← ofNat_beq_zero (s₀.gpr .rcx).isLt, BitVec.ofNat_toNat, BitVec.setWidth_eq]

end

/-! ## The key block -/

section
variable {w : Nat}

/-- After zeroing `8 · j` bytes of the buffer, from `σ`. -/
structure ZInv (σ : State) (j : Nat) (s : State) : Prop where
  gpr : s.gpr = σ.gpr
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  mem : s.mem = writeBytes σ.mem (σ.gpr .rdi + BitVec.ofNat 64 (bufOff w)) (List.replicate (8 * j) 0)

theorem zero_ok (hw : w = 64 ∨ w = 32) {σ : State} (hrax : σ.gpr .rax = 0)
    (hwr : ∀ a n, InRegions [⟨σ.gpr .rdi, bufOff w + blockBytes w⟩] a n → InRegions σ.wr a n) :
    WP isa (.block ((List.range (Impl.Blake2.X86_64.Stream.B w / 8)).flatMap fun j =>
      [.store (at_ .rdi (Impl.Blake2.X86_64.Stream.N w + 8 * j)) .rax])) σ
      (ZInv (w := w) σ (blockBytes w / 8)) := by
  have hs := sizes hw
  refine wp_range_flatMap (M := isa) (ZInv (w := w) σ) (fun j s hj h => ?_) _ (Nat.le_refl _) σ
    ⟨rfl, rfl, rfl, by rw [Nat.mul_zero, List.replicate_zero, writeBytes_nil]⟩
  rw [B_eq] at hj
  refine wp_store (a := σ.gpr .rdi + BitVec.ofNat 64 (bufOff w + 8 * j)) (by rw [ea_at, h.gpr, N_eq])
    ?_ fun s' g' m' rd' wr' => WP.block_nil ⟨g'.trans h.gpr, rd'.trans h.rd, wr'.trans h.wr, ?_⟩
  · rw [h.wr]; exact hwr _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base _ (by omega) (by omega)⟩
  · have e := writeBytes_append σ.mem (σ.gpr .rdi + BitVec.ofNat 64 (bufOff w))
      (List.replicate (8 * j) 0) (List.replicate 8 0) (by simp; omega)
    rw [List.length_replicate] at e
    rw [m', h.mem, h.gpr, hrax, writeW_zero, ← Offset.add_ofNat_add_ofNat, e,
      List.replicate_append_replicate, Nat.mul_succ]

section
variable (s₀ : State)

abbrev st : Addr := s₀.gpr .rdi
abbrev kp : Addr := s₀.gpr .rdx
abbrev kk : Nat := (s₀.gpr .rcx).toNat
abbrev buf (w : Nat) : Addr := st s₀ + BitVec.ofNat 64 (bufOff w)
abbrev stR (w : Nat) : Region := ⟨st s₀, bufOff w + blockBytes w⟩
abbrev kR : Region := ⟨kp s₀, kk s₀⟩
/-- The key. -/
abbrev key : List Byte := bytesAt s₀.mem (kp s₀) (kk s₀)

end

/-- After copying `j` bytes of the key over the zeroed buffer `Z`. -/
structure KInv (s₀ : State) (Z : Mem) (j : Nat) (s : State) : Prop where
  j_le : j ≤ kk s₀
  r8 : s.gpr .r8 = BitVec.ofNat 64 j
  rcx : s.gpr .rcx = BitVec.ofNat 64 (kk s₀ - j)
  other : ∀ r, r ≠ .rax → r ≠ .r8 → r ≠ .rcx → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : s.mem = writeBytes Z (buf s₀ w) ((key s₀).take j)

theorem keyLoop_ok (hw : w = 64 ∨ w = 32) {s₀ : State} {Z : Mem} {σ : State}
    (hrd : s₀.rd = [kR s₀]) (hwr : s₀.wr = [stR s₀ w]) (hd : (kR s₀).Disjoint (stR s₀ w))
    (hk : 1 ≤ kk s₀) (hkb : kk s₀ ≤ blockBytes w) (hZ : Frame [stR s₀ w] s₀.mem Z)
    (hσ : KInv (w := w) s₀ Z 0 σ) :
    WP isa (.loop (.block [.movzx8 .rax { base := .rdx, index := some .r8, scale := 1 },
        .store8 { base := .rdi, index := some .r8, scale := 1, disp := Impl.Blake2.X86_64.Stream.N w } .rax,
        .alu .add .r8 (.imm 1), .alu .sub .rcx (.imm 1)]) .ne) σ
      (KInv (w := w) s₀ Z (kk s₀)) := by
  have hs := sizes hw
  have hkl : kk s₀ < 2 ^ 64 := (s₀.gpr .rcx).isLt
  have hxs : (key s₀).length = kk s₀ := by simp [bytesAt]
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
  refine wp_movzx8 (d := .rax) (a := kp s₀ + BitVec.ofNat 64 j)
    (by simp [State.ea, h.r8, h.other .rdx (by decide) (by decide) (by decide)]) hin fun s₁ u₁ => ?_
  refine wp_store8 (r := .rax) (a := buf s₀ w + BitVec.ofNat 64 j) ?_ (by rw [u₁.wr]; exact hout)
    fun s₂ g₂ m₂ rd₂ wr₂ => ?_
  · simp only [State.ea, u₁.other .rdi (by decide), u₁.other .r8 (by decide),
      h.other .rdi (by decide) (by decide) (by decide), h.r8, N_eq, BitVec.mul_one, ofInt_natCast]
    rw [BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 j), ← BitVec.add_assoc]
  refine wp_addi fun s₃ u₃ => wp_subi fun s₄ u₄ hz₄ => WP.block_nil ?_
  have hrcx : s₄.gpr .rcx = BitVec.ofNat 64 (kk s₀ - (j + 1)) := by
    rw [u₄.gpr, u₃.other .rcx (by decide), g₂, u₁.other .rcx (by decide), h.rcx, sx1,
      ofNat_pred (by omega), Nat.sub_sub]
  have hI : KInv (w := w) s₀ Z (j + 1) s₄ := by
    refine ⟨by omega, ?_, hrcx, fun r h1 h2 h3 => ?_, ?_, ?_, ?_⟩
    · rw [u₄.other .r8 (by decide), u₃.gpr, g₂, u₁.other .r8 (by decide), h.r8, sx1, ofNat_succ]
    · rw [u₄.other r h3, u₃.other r h2, g₂, u₁.other r h1, h.other r h1 h2 h3]
    · rw [u₄.rd, u₃.rd, rd₂, u₁.rd, h.rd]
    · rw [u₄.wr, u₃.wr, wr₂, u₁.wr, h.wr]
    · have hj' : j < (key s₀).length := by omega
      have hl : (List.take j (key s₀)).length = j := by
        rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj')]
      rw [u₄.mem, u₃.mem, m₂, u₁.mem, u₁.gpr, hbyte, h.mem, List.take_add_one,
        List.getElem?_eq_getElem hj', Option.toList_some,
        writeBytes_snoc _ _ _ _ (by rw [hl]; omega), hl,
        BitVec.setWidth_setWidth_of_le _ (by omega), BitVec.setWidth_eq]
      congr 1
      simp [bytesAt]
  have hzf : s₄.zf = some (decide (kk s₀ - (j + 1) = 0)) := by
    rw [hz₄, u₃.other .rcx (by decide), g₂, u₁.other .rcx (by decide), h.rcx, sx1,
      ofNat_pred (show 1 ≤ kk s₀ - j by omega), ofNat_beq_zero (by omega),
      show kk s₀ - j - 1 = kk s₀ - (j + 1) by omega]
  by_cases hjk : j + 1 = kk s₀
  · refine .inl ⟨?_, hjk ▸ hI⟩
    simp only [eval, hzf, show kk s₀ - (j + 1) = 0 by omega, decide_true, Option.map_some,
      Bool.not_true]
  · refine .inr ⟨?_, kk s₀ - (j + 1), by omega, j + 1, rfl, by omega, hI⟩
    simp only [eval, hzf, show kk s₀ - (j + 1) ≠ 0 by omega, decide_false, Option.map_some,
      Bool.not_false]

end

section
variable {w : Nat} {P : Params w}

theorem keyBlock_ok (hw : w = 64 ∨ w = 32) {s₀ σ : State}
    (hrd : s₀.rd = [kR s₀]) (hwr : s₀.wr = [stR s₀ w]) (hd : (kR s₀).Disjoint (stR s₀ w))
    (hk : 1 ≤ kk s₀) (hkb : kk s₀ ≤ blockBytes w) (hσ : StateOk (P := P) s₀ σ) :
    WP isa (Impl.Blake2.X86_64.Stream.keyBlock (w := w)) σ fun s =>
      (∀ r, r ≠ .rax → r ≠ .r8 → r ≠ .rcx → s.gpr r = s₀.gpr r) ∧
      Frame [⟨buf s₀ w, blockBytes w⟩] σ.mem s.mem ∧
      bytesAt s.mem (buf s₀ w) (blockBytes w) = key s₀ ++ List.replicate (blockBytes w - kk s₀) 0 := by
  have hs := sizes hw
  have hxs : (key s₀).length = kk s₀ := by simp [bytesAt]
  have hbuf : ∀ n, n ≤ blockBytes w → (stR s₀ w).Contains (buf s₀ w) n := fun n hn =>
    Offset.contains_base _ (by omega) (by omega)
  have hσdi : σ.gpr .rdi = st s₀ := hσ.gpr _ (by decide) (by decide)
  unfold Impl.Blake2.X86_64.Stream.keyBlock
  rw [List.map_eq_flatMap]
  refine WP.seq (wp_mov32i fun σ₁ u₁ _ _ => WP.mono (zero_ok hw (σ := σ₁) (by rw [u₁.gpr]; rfl) ?_)
    fun s₂ h₂ => ?_)
  · rw [u₁.wr, hσ.wr, hwr, u₁.other _ (by decide), hσdi]; exact fun _ _ h => h
  have hZ : s₂.mem = writeBytes σ.mem (buf s₀ w) (List.replicate (blockBytes w) 0) := by
    rw [h₂.mem, u₁.other _ (by decide), hσdi, u₁.mem, Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hs.2.2.1)]
  have hfZ : Frame [stR s₀ w] s₀.mem s₂.mem := by
    rw [hZ]
    exact (hσ.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨stR s₀ w, List.mem_singleton_self _, Region.sub_prefix (by omega)⟩).trans
      (writeBytes_frame _ _ _ (by simpa using hbuf _ (Nat.le_refl _)))
  refine WP.seq (wp_mov32i fun s₃ u₃ _ _ => WP.block_nil ?_)
  refine WP.mono (keyLoop_ok hw hrd hwr hd hk hkb hfZ ⟨Nat.zero_le _, by rw [u₃.gpr]; rfl, ?_, ?_,
    by rw [u₃.rd, h₂.rd, u₁.rd, hσ.rd], by rw [u₃.wr, h₂.wr, u₁.wr, hσ.wr], ?_⟩) fun s h => ?_
  · rw [u₃.other _ (by decide), h₂.gpr, u₁.other _ (by decide), hσ.gpr _ (by decide) (by decide),
      Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · intro r h1 h2 h3
    rw [u₃.other r h2, h₂.gpr, u₁.other r h1, hσ.gpr r h1 h2]
  · rw [u₃.mem, List.take_zero, writeBytes_nil]
  have hm : s.mem = writeBytes (writeBytes σ.mem (buf s₀ w) (List.replicate (blockBytes w) 0))
      (buf s₀ w) (key s₀) := by
    rw [h.mem, List.take_of_length_le (by omega), hZ]
  refine ⟨h.other, ?_, ?_⟩
  · rw [hm]
    exact (writeBytes_frame _ _ _ (VG.Proof.Blake2.X86_64.Stream.contains_prefix _ (by simp))).trans
      (writeBytes_frame _ _ _ (VG.Proof.Blake2.X86_64.Stream.contains_prefix _ (by omega)))
  · rw [hm, bytesAt_writeBytes (by omega) (by omega) fun i hi => ?_, hxs]
    rw [writeBytes_at _ _ _ (by omega)]
    simp [hi]

theorem finish {s₀ s : State} (hw : w = 64 ∨ w = 32) (hkb : kk s₀ ≤ blockBytes w)
    (hret : Region.Disjoint ⟨s₀.gpr .rsp, 8⟩ (stR s₀ w))
    (hg : ∀ r ∈ calleeSaved, s.gpr r = s₀.gpr r) (hf : Frame [stR s₀ w] s₀.mem s.mem)
    (hst : stateAt w s.mem (st s₀) = Spec.Blake2.init P (s₀.gpr .rsi).toNat (kk s₀))
    (hb : kk s₀ ≠ 0 → bytesAt s.mem (buf s₀ w) (blockBytes w) =
      key s₀ ++ List.replicate (blockBytes w - kk s₀) 0) :
    gprPreserved s₀ s ∧ (initX86_64 P).post s₀ s := by
  have hxs : (key s₀).length = kk s₀ := by simp [bytesAt]
  refine ⟨⟨hg, hf.readW (Region.contains_self _ _) (by simpa using hret) (by decide)⟩, ?_⟩
  exact repr_keyBlock P (by have := (sizes hw).2.1; omega) (hxs ▸ hkb) hst
    fun h => by rw [hxs]; exact hb (hxs ▸ h)

end

/-! ## The whole function -/

/-- `init` stores the initial hash value and, for a key, the key block. -/
theorem correct {w : Nat} {P : Params w} {s₀ : State} (hP : Ok P)
    (hp : (initX86_64 P).pre s₀) :
    WP isa (Impl.Blake2.X86_64.Stream.init P) s₀ fun s' =>
      gprPreserved s₀ s' ∧ (initX86_64 P).post s₀ s' := by
  obtain ⟨hrd, hwr, hd, hret, -, -, hkk⟩ := hp
  have hw := hP.w
  have hs := sizes hw
  have hmax := hP.max
  have hkb : kk s₀ ≤ blockBytes w := Nat.le_trans hkk hmax
  have hsub : ∀ r ∈ [(⟨st s₀, bufOff w⟩ : Region)], ∃ r' ∈ [stR s₀ w], Region.Sub r r' := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨stR s₀ w, List.mem_singleton_self _, Region.sub_prefix (by omega)⟩
  have hcs : ∀ r ∈ calleeSaved, r ≠ .rax ∧ r ≠ .r8 ∧ r ≠ .rcx := by decide
  unfold Impl.Blake2.X86_64.Stream.init
  refine WP.seq (WP.mono (initState_ok (P := P) hw (fun a n h => ?_) (by omega)) fun σ hσ => ?_)
  · rw [hwr]
    obtain ⟨r, hr, hc⟩ := h
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc ⊢; omega⟩
  refine WP.ite (decide (kk s₀ = 0)) hσ.zf (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    exact finish hw hkb hret (fun r hr => hσ.gpr r (hcs r hr).1 (hcs r hr).2.1) (hσ.frame.sub hsub)
      hσ.state fun h => absurd hb h
  · simp only [decide_eq_false_iff_not] at hb
    refine WP.mono (keyBlock_ok hw hrd hwr hd (by omega) hkb hσ) fun s ⟨hg, hf, hb'⟩ => ?_
    have hf' : Frame [stR s₀ w] σ.mem s.mem := hf.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨stR s₀ w, List.mem_singleton_self _, Offset.sub_base _ (by omega)⟩
    refine finish hw hkb hret (fun r hr => hg r (hcs r hr).1 (hcs r hr).2.1 (hcs r hr).2.2)
      ((hσ.frame.sub hsub).trans hf') ?_ fun _ => hb'
    rw [← hσ.state]
    exact stateAt_congr fun i hi => hf.bytes (R := ⟨st s₀, bufOff w⟩)
      (by simpa using Offset.base_disjoint (st s₀) (Nat.le_refl (bufOff w)) (n := blockBytes w) (by omega))
      (by simp only; omega) hi

end VG.Proof.Blake2.X86_64.Stream.Init
