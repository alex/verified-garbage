import VerifiedGarbage.Proof.ChaCha20.PPC64LE.Stream.Calls

/-!
# Streaming ChaCha20 on PPC64LE: `apply`, correctness

Untrusted: everything here is checked by Lean. The pieces of `apply`
(`Impl/ChaCha20/PPC64LE/Stream.lean`), each from what holds before it
(`Q0` … `Q3`), and the whole function, as on AArch64
(`VG.Proof.ChaCha20.AArch64.Stream`). The pieces are those that the proof of
constant time (`ApplyCT.lean`) relates in two runs.
-/

namespace VG.Proof.ChaCha20

open VG.PPC64LE
open VG.Spec.ChaCha20 (keyAt restAt leftAt bytesAt)

/-- PPC64LE contract for `vg_chacha20_apply(state = r3, data = r4, len = r5) -> r3`.
The return address is in the link register, which the code saves in the
state, so no stack is used. -/
def applyPPC64LE : Contract PPC64LE.isa where
  pre s :=
    let state : Region := ⟨s.gpr .r3, 768⟩
    let data : Region := ⟨s.gpr .r4, (s.gpr .r5).toNat⟩
    s.rd = [] ∧ s.wr = [state, data] ∧ state.Disjoint data ∧
    (s.gpr .r3).toNat + 768 ≤ 2 ^ 64 ∧ (s.gpr .r4).toNat + (s.gpr .r5).toNat ≤ 2 ^ 64
  post s s' :=
    keyAt s'.mem (s.gpr .r3) = keyAt s.mem (s.gpr .r3) ∧
      if (s.gpr .r5).toNat ≤ leftAt s.mem (s.gpr .r3) then
        (s'.gpr .r3).setWidth 32 = 1 ∧
          bytesAt s'.mem (s.gpr .r4) (s.gpr .r5).toNat =
            List.zipWith (· ^^^ ·) (bytesAt s.mem (s.gpr .r4) (s.gpr .r5).toNat)
              ((restAt s.mem (s.gpr .r3)).take (s.gpr .r5).toNat) ∧
          restAt s'.mem (s.gpr .r3) = (restAt s.mem (s.gpr .r3)).drop (s.gpr .r5).toNat
      else
        (s'.gpr .r3).setWidth 32 = 0 ∧
          bytesAt s'.mem (s.gpr .r4) (s.gpr .r5).toNat = bytesAt s.mem (s.gpr .r4) (s.gpr .r5).toNat ∧
          restAt s'.mem (s.gpr .r3) = restAt s.mem (s.gpr .r3)
  pub s₁ s₂ :=
    s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
      s₁.sp = s₂.sp ∧ [leftAt s₁.mem (s₁.gpr .r3)] = [leftAt s₂.mem (s₂.gpr .r3)]

end VG.Proof.ChaCha20

namespace VG.Proof.ChaCha20.PPC64LE.Stream

open VG VG.PPC64LE VG.Impl.ChaCha20.PPC64LE.Stream
open VG.Impl.ChaCha20.PPC64LE.Xor (mov)
open VG.Spec.ChaCha20 (keyAt restAt leftAt bytesAt stateAt serialize block)
open VG.Proof.ChaCha20.PPC64LE.Xor (Upd Mupd wp_li wp_addi wp_subi wp_mov wp_sub wp_lsr wp_ld wp_std wp_lwz
  wp_stw wp_mflr wp_mtlr sub_ofNat add_ofNat eval_zero eval_nonzero eval_nonzero_ofNat ofNat_beq_zero stateAt_frame
  stateAt_writeW_counter inc_setWidth)
open VG.Proof.ChaCha20.PPC64LE (toNat_ofNat_lt)

/-! ## Instructions -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_and {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n &&& s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .and d n m :: is)) s Q :=
  Proof.ChaCha20.PPC64LE.Xor.WP.cons exec_logic (k _ (Upd.write _ _ _))

theorem wp_add {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n + s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.add d n m :: is)) s Q :=
  Proof.ChaCha20.PPC64LE.Xor.WP.cons exec_add (k _ (Upd.write _ _ _))

theorem wp_lsl {d n : Reg} {sh : Nat} (h : sh < 64)
    (k : ∀ s', Upd s s' d (s.gpr n <<< sh) → WP isa (.block is) s' Q) :
    WP isa (.block (.lsl d n sh :: is)) s Q :=
  Proof.ChaCha20.PPC64LE.Xor.WP.cons (exec_lsl h) (k _ (Upd.write _ _ _))

end

/-! ## The comparisons -/

/-- `borrow`'s result: 1 iff `a < b`. -/
theorem borrow_eq (a b : BitVec 64) :
    ((a >>> 1) - (b >>> 1) - ((a &&& 1#64) - (b &&& 1#64)) >>> 63) >>> 63 =
      BitVec.ofNat 64 (decide (a.toNat < b.toNat)).toNat := by
  have ha := a.isLt
  have hb := b.isLt
  have e1 : (a &&& 1#64).toNat = a.toNat % 2 := by
    rw [BitVec.toNat_and, show (1#64).toNat = 1 from rfl, Nat.and_one_is_mod]
  have e2 : (b &&& 1#64).toNat = b.toNat % 2 := by
    rw [BitVec.toNat_and, show (1#64).toNat = 1 from rfl, Nat.and_one_is_mod]
  have c : (((a &&& 1#64) - (b &&& 1#64)) >>> 63).toNat = (decide (a.toNat % 2 < b.toNat % 2)).toNat := by
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, e1, e2, Nat.shiftRight_eq_div_pow]
    by_cases h : a.toNat % 2 < b.toNat % 2 <;> simp [h] <;> omega
  have h1 : (a >>> 1).toNat = a.toNat / 2 := by rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have h2 : (b >>> 1).toNat = b.toNat / 2 := by rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_sub, c, h1, h2, Nat.shiftRight_eq_div_pow,
    BitVec.toNat_ofNat]
  by_cases h : a.toNat < b.toNat <;> by_cases h' : a.toNat % 2 < b.toNat % 2 <;> simp [h, h'] <;> omega

/-- `x & 63` keeps the low 6 bits. -/
theorem and63 (x : BitVec 64) : x &&& BitVec.ofNat 64 63 = BitVec.ofNat 64 (x.toNat % 64) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (BitVec.ofNat 64 63).toNat = 2 ^ 6 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    BitVec.toNat_ofNat]
  have := x.isLt
  omega

/-- `s'` is `s` but for the registers `ws`. -/
structure Rest (ws : List Reg) (s s' : State) : Prop where
  other : ∀ r, r ∉ ws → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  lr : s'.lr = s.lr

theorem Rest.trans {ws : List Reg} {s s' s'' : State} (h : Rest ws s s') (h' : Rest ws s' s'') : Rest ws s s'' :=
  ⟨fun r hr => (h'.other r hr).trans (h.other r hr), h'.mem.trans h.mem, h'.rd.trans h.rd, h'.wr.trans h.wr,
    h'.lr.trans h.lr⟩

theorem Rest.upd {ws : List Reg} {s s' : State} {d : Reg} {v : BitVec 64} (u : Upd s s' d v) (hd : d ∈ ws) :
    Rest ws s s' :=
  ⟨fun r hr => u.other r fun e => hr (e ▸ hd), u.mem, u.rd, u.wr, u.lr⟩

theorem borrow_ok {d a b : Reg} {s : State} {A B : BitVec 64} {is : List Instr} {Q : State → Prop}
    (ha : s.gpr a = A) (hb : s.gpr b = B) (h12 : s.gpr .r12 = BitVec.ofNat 64 1)
    (hda : d ≠ a) (hdb : d ≠ b) (hd0 : d ≠ .r11) (hd6 : d ≠ .r6) (ha11 : a ≠ .r11) (hb11 : b ≠ .r11)
    (h11 : d ≠ .r12)
    (k : ∀ s', s'.gpr d = BitVec.ofNat 64 (decide (A.toNat < B.toNat)).toNat → Rest [d, .r6, .r11] s s' →
      WP isa (.block is) s' Q) :
    WP isa (.block (borrow d a b ++ is)) s Q := by
  simp only [borrow, List.cons_append, List.nil_append]
  refine wp_lsr (by decide) fun s₁ u₁ => wp_lsr (by decide) fun s₂ u₂ => wp_sub fun s₃ u₃ => ?_
  refine wp_and fun s₄ u₄ => wp_and fun s₅ u₅ => wp_sub fun s₆ u₆ => wp_lsr (by decide) fun s₇ u₇ => ?_
  refine wp_sub fun s₈ u₈ => wp_lsr (by decide) fun s₉ u₉ => k s₉ ?_ ?_
  · have hA : s.gpr a = A := ha
    have v1 : s₁.gpr d = A >>> 1 := by rw [u₁.gpr, hA]
    have a1 : s₁.gpr a = A := by rw [u₁.other _ (Ne.symm hda), hA]
    have b1 : s₁.gpr b = B := by rw [u₁.other _ (Ne.symm hdb), hb]
    have t1 : s₁.gpr .r12 = BitVec.ofNat 64 1 := by rw [u₁.other _ (Ne.symm h11), h12]
    have v2 : s₂.gpr .r11 = B >>> 1 := by rw [u₂.gpr, b1]
    have d2 : s₂.gpr d = A >>> 1 := by rw [u₂.other _ hd0, v1]
    have a2 : s₂.gpr a = A := by rw [u₂.other _ ha11, a1]
    have b2 : s₂.gpr b = B := by rw [u₂.other _ hb11, b1]
    have t2 : s₂.gpr .r12 = BitVec.ofNat 64 1 := by rw [u₂.other _ (by decide), t1]
    have v3 : s₃.gpr d = (A >>> 1) - (B >>> 1) := by rw [u₃.gpr, d2, u₂.gpr, b1]
    have a3 : s₃.gpr a = A := by rw [u₃.other _ (Ne.symm hda), a2]
    have b3 : s₃.gpr b = B := by rw [u₃.other _ (Ne.symm hdb), b2]
    have t3 : s₃.gpr .r12 = BitVec.ofNat 64 1 := by rw [u₃.other _ (Ne.symm h11), t2]
    have v4 : s₄.gpr .r11 = A &&& 1#64 := by rw [u₄.gpr, a3, t3]
    have d4 : s₄.gpr d = (A >>> 1) - (B >>> 1) := by rw [u₄.other _ hd0, v3]
    have b4 : s₄.gpr b = B := by rw [u₄.other _ hb11, b3]
    have t4 : s₄.gpr .r12 = BitVec.ofNat 64 1 := by rw [u₄.other _ (by decide), t3]
    have v5 : s₅.gpr .r6 = B &&& 1#64 := by rw [u₅.gpr, b4, t4]
    have d5 : s₅.gpr d = (A >>> 1) - (B >>> 1) := by rw [u₅.other _ hd6, d4]
    have r5 : s₅.gpr .r11 = A &&& 1#64 := by rw [u₅.other _ (by decide), v4]
    have v6 : s₆.gpr .r11 = (A &&& 1#64) - (B &&& 1#64) := by rw [u₆.gpr, r5, v5]
    have d6 : s₆.gpr d = (A >>> 1) - (B >>> 1) := by rw [u₆.other _ hd0, d5]
    have v7 : s₇.gpr .r11 = ((A &&& 1#64) - (B &&& 1#64)) >>> 63 := by rw [u₇.gpr, v6]
    have d7 : s₇.gpr d = (A >>> 1) - (B >>> 1) := by rw [u₇.other _ hd0, d6]
    have v8 : s₈.gpr d = (A >>> 1) - (B >>> 1) - ((A &&& 1#64) - (B &&& 1#64)) >>> 63 := by
      rw [u₈.gpr, d7, v7]
    rw [u₉.gpr, v8]
    exact borrow_eq A B
  · exact (((((((((Rest.upd u₁ (by simp)).trans (Rest.upd u₂ (by simp))).trans (Rest.upd u₃ (by simp))).trans
      (Rest.upd u₄ (by simp))).trans (Rest.upd u₅ (by simp))).trans (Rest.upd u₆ (by simp))).trans
      (Rest.upd u₇ (by simp))).trans (Rest.upd u₈ (by simp))).trans (Rest.upd u₉ (by simp)))


/-! ## The entry state -/

section
variable (s₀ : State)
abbrev st : Addr := s₀.gpr .r3
abbrev dp : Addr := s₀.gpr .r4
abbrev L : Nat := (s₀.gpr .r5).toNat
/-- The number of bytes of keystream left, and those in the buffered block. -/
abbrev N : Nat := leftAt s₀.mem (st s₀)
abbrev O : Nat := N s₀ % 64
/-- The bytes from the buffered block, the whole blocks and the bytes of the
next block that `apply` uses. -/
abbrev H : Nat := headLen s₀.mem (st s₀) (L s₀)
abbrev NB : Nat := blocksOf s₀.mem (st s₀) (L s₀)
abbrev T : Nat := tailLen s₀.mem (st s₀) (L s₀)
abbrev S0 : CState := stateAt s₀.mem (st s₀)
abbrev D0 (k : Nat) : Byte := s₀.mem (dp s₀ + BitVec.ofNat 64 k)
abbrev stR : Region := ⟨st s₀, 768⟩
abbrev dR : Region := ⟨dp s₀, L s₀⟩
/-- The keystream byte XORed into byte `k` of the data. -/
abbrev KS (k : Nat) : Byte :=
  if k < H s₀ then s₀.mem (st s₀ + BitVec.ofNat 64 (128 - O s₀ + k))
  else (serialize (block (ctr (S0 s₀) ((k - H s₀) / 64)))).getD ((k - H s₀) % 64) 0
/-- The data with its first `j` bytes XORed. -/
abbrev Done (j : Nat) (m : Mem) : Prop :=
  ∀ k < L s₀, m (dp s₀ + BitVec.ofNat 64 k) = if k < j then D0 s₀ k ^^^ KS s₀ k else D0 s₀ k
end

theorem L_lt (s₀ : State) : L s₀ < 2 ^ 64 := (s₀.gpr .r5).isLt
theorem N_lt (s₀ : State) : N s₀ < 2 ^ 64 := (s₀.mem.readW (st s₀ + 128) 64).isLt
theorem H_le (s₀ : State) : H s₀ ≤ L s₀ := Nat.min_le_right _ _
theorem H_le_O (s₀ : State) : H s₀ ≤ O s₀ := Nat.min_le_left _ _
theorem O_lt (s₀ : State) : O s₀ < 64 := Nat.mod_lt _ (by decide)
theorem T_eq (s₀ : State) : T s₀ = L s₀ - H s₀ - 64 * NB s₀ := by simp only [T, NB, tailLen, blocksOf, H]; omega
theorem HNB_le (s₀ : State) : H s₀ + 64 * NB s₀ ≤ L s₀ := by
  have := H_le s₀; simp only [NB, blocksOf, H] at *; omega

structure APre (s₀ : State) : Prop where
  rd : s₀.rd = []
  wr : s₀.wr = [stR s₀, dR s₀]
  st_d : (stR s₀).Disjoint (dR s₀)
  wrap_st : (st s₀).toNat + 768 ≤ 2 ^ 64
  wrap_d : (dp s₀).toNat + L s₀ ≤ 2 ^ 64

theorem APre.of (s₀ : State) (h : Proof.ChaCha20.applyPPC64LE.pre s₀) : APre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

theorem APre.w_st {s₀ : State} (hp : APre s₀) {d n : Nat} (h : d + n ≤ 768) :
    InRegions s₀.wr (st s₀ + BitVec.ofNat 64 d) n :=
  ⟨stR s₀, by rw [hp.wr]; exact List.mem_cons_self .., Offset.contains_base _ h (by omega)⟩

theorem APre.r_st {s₀ : State} (hp : APre s₀) {d n : Nat} (h : d + n ≤ 768) :
    InRegions (s₀.rd ++ s₀.wr) (st s₀ + BitVec.ofNat 64 d) n := by
  rw [hp.rd, List.nil_append]; exact hp.w_st h

/-- Our caller's `r24`–`r26`, our return address, and the bytes left after
`apply`. -/
structure Saved (s₀ : State) (m : Mem) : Prop where
  r24 : m.readW (st s₀ + BitVec.ofNat 64 576) 64 = s₀.gpr .r24
  r25 : m.readW (st s₀ + BitVec.ofNat 64 584) 64 = s₀.gpr .r25
  r26 : m.readW (st s₀ + BitVec.ofNat 64 592) 64 = s₀.gpr .r26
  lr : m.readW (st s₀ + BitVec.ofNat 64 600) 64 = s₀.lr
  left : m.readW (st s₀ + BitVec.ofNat 64 608) 64 = BitVec.ofNat 64 (N s₀ - L s₀)

/-- Where they are. -/
abbrev savR (s₀ : State) : Region := ⟨st s₀ + BitVec.ofNat 64 576, 40⟩

theorem savR_sub (s₀ : State) : Region.Sub (savR s₀) (stR s₀) := Offset.sub_base _ (by omega)

theorem Saved.frame {s₀ : State} {rs : List Region} {m m' : Mem} (h : Saved s₀ m) (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (savR s₀).Disjoint r) : Saved s₀ m' := by
  have c : ∀ d, 576 ≤ d → d + 8 ≤ 616 → (savR s₀).Contains (st s₀ + BitVec.ofNat 64 d) (64 / 8) :=
    fun d h₁ h₂ => Offset.contains _ h₁ (by omega) (by omega)
  exact ⟨by rw [hf.readW (c 576 (by decide) (by decide)) hd (by decide), h.r24],
    by rw [hf.readW (c 584 (by decide) (by decide)) hd (by decide), h.r25],
    by rw [hf.readW (c 592 (by decide) (by decide)) hd (by decide), h.r26],
    by rw [hf.readW (c 600 (by decide) (by decide)) hd (by decide), h.lr],
    by rw [hf.readW (c 608 (by decide) (by decide)) hd (by decide), h.left]⟩

/-! ## The check -/

/-- The registers the check writes. -/
abbrev chk : List Reg := [.r6, .r7, .r8, .r9, .r10, .r11, .r12]

/-- After the check. -/
structure Q0 (s₀ s : State) : Prop where
  r9 : s.gpr .r9 = BitVec.ofNat 64 (N s₀)
  r7 : s.gpr .r7 = BitVec.ofNat 64 (O s₀)
  r10 : s.gpr .r10 = BitVec.ofNat 64 (decide (N s₀ < L s₀)).toNat
  r8 : s.gpr .r8 = BitVec.ofNat 64 (decide (O s₀ < L s₀)).toNat
  rest : Rest chk s₀ s

theorem Rest.mono {ws ws' : List Reg} {s s' : State} (h : Rest ws s s') (hs : ∀ r ∈ ws, r ∈ ws') :
    Rest ws' s s' :=
  ⟨fun r hr => h.other r fun h' => hr (hs r h'), h.mem, h.rd, h.wr, h.lr⟩

theorem check_ok {s₀ : State} (hp : APre s₀) : WP isa (.block check) s₀ (Q0 s₀) := by
  have hL := L_lt s₀
  have hN := N_lt s₀
  have i₁ := hp.r_st (d := 128) (n := 8) (by decide)
  unfold check
  simp only [List.cons_append, List.append_assoc]
  refine wp_ld (a := st s₀ + BitVec.ofNat 64 128) (by decide) ⟨by decide, by decide⟩ rfl i₁ fun s₁ u₁ => ?_
  refine wp_li (by decide) fun s₂ u₂ => wp_li (by decide) fun s₃ u₃ => wp_and fun s₄ u₄ => ?_
  have n4 : s₄.gpr .r9 = BitVec.ofNat 64 (N s₀) := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
    simp [N, leftAt]
  have o4 : s₄.gpr .r7 = BitVec.ofNat 64 (O s₀) := by
    rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, u₃.gpr, and63,
      show (st s₀ + BitVec.ofNat 64 128 : Addr) = st s₀ + 128 from rfl]
    simp only [O, N, leftAt]
  have l4 : s₄.gpr .r5 = BitVec.ofNat 64 (L s₀) := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
    simp [L]
  have t4 : s₄.gpr .r12 = BitVec.ofNat 64 1 := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr]
  have r4 : Rest chk s₀ s₄ :=
    (((Rest.upd u₁ (by simp)).trans (Rest.upd u₂ (by simp))).trans (Rest.upd u₃ (by simp))).trans
      (Rest.upd u₄ (by simp))
  refine borrow_ok (A := BitVec.ofNat 64 (N s₀)) (B := BitVec.ofNat 64 (L s₀)) n4 l4 t4 (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) fun s₅ v₅ r₅ => ?_
  rw [← List.append_nil (borrow .r8 .r7 .r5)]
  have n5 : s₅.gpr .r7 = BitVec.ofNat 64 (O s₀) := by rw [r₅.other _ (by decide), o4]
  have l5 : s₅.gpr .r5 = BitVec.ofNat 64 (L s₀) := by rw [r₅.other _ (by decide), l4]
  have t5 : s₅.gpr .r12 = BitVec.ofNat 64 1 := by rw [r₅.other _ (by decide), t4]
  refine borrow_ok (A := BitVec.ofNat 64 (O s₀)) (B := BitVec.ofNat 64 (L s₀)) n5 l5 t5 (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) fun s₆ v₆ r₆ => WP.block_nil ?_
  have hO := O_lt s₀
  rw [toNat_ofNat_lt hN, toNat_ofNat_lt hL] at v₅
  rw [toNat_ofNat_lt (by omega), toNat_ofNat_lt hL] at v₆
  refine ⟨by rw [r₆.other _ (by decide), r₅.other _ (by decide), n4],
    by rw [r₆.other _ (by decide), n5], by rw [r₆.other _ (by decide), v₅], v₆, ?_⟩
  exact (r4.trans (r₅.mono (by simp))).trans (r₆.mono (by simp))

/-- The callee-saved registers our code never writes. -/
def kept : List Reg := [.r2, .r14, .r15, .r16, .r17, .r18, .r19, .r20, .r21, .r22, .r23, .r27, .r28, .r29,
  .r30, .r31]

theorem kept_ne {r : Reg} (hr : r ∈ kept) {r' : Reg} (h : r' ∉ kept := by decide) : r ≠ r' :=
  fun e => h (e ▸ hr)

/-- What `apply` guarantees (`applyPPC64LE`), and the registers it keeps. -/
def Final (s₀ s : State) : Prop :=
  (∀ r ∈ preserved, s.gpr r = s₀.gpr r) ∧ s.lr = s₀.lr ∧ Proof.ChaCha20.applyPPC64LE.post s₀ s

theorem fail_ok {s₀ : State} (hlt : N s₀ < L s₀) {s : State} (h : Q0 s₀ s) :
    WP isa (.block [.li .r3 0]) s (Final s₀) := by
  refine wp_li (by decide) fun s₁ u₁ => WP.block_nil ?_
  refine ⟨fun r hr => ?_, by rw [u₁.lr, h.rest.lr], ?_⟩
  · have : r ≠ .r3 ∧ r ∉ chk := by revert r hr; decide
    rw [u₁.other _ this.1, h.rest.other _ this.2]
  · show keyAt _ _ = _ ∧ _
    rw [ite_neg (show ¬ L s₀ ≤ N s₀ by omega)]
    rw [u₁.mem, h.rest.mem]
    exact ⟨rfl, by rw [u₁.gpr]; decide, rfl, rfl⟩

/-! ## The bytes left in the buffered block -/

/-- The state of memory before the data is touched. -/
structure Mid (s₀ : State) (m : Mem) : Prop where
  keep : ∀ i < 136, m (st s₀ + BitVec.ofNat 64 i) = s₀.mem (st s₀ + BitVec.ofNat 64 i)
  saved : Saved s₀ m

theorem Mid.state {s₀ : State} {m : Mem} (h : Mid s₀ m) : stateAt m (st s₀) = S0 s₀ :=
  stateAt_congr fun i hi => h.keep i (by omega)

/-- After `start`, with `x` in `r5`. -/
structure R1 (s₀ : State) (x : Nat) (s : State) : Prop where
  r24 : s.gpr .r24 = st s₀
  r25 : s.gpr .r25 = dp s₀
  r26 : s.gpr .r26 = BitVec.ofNat 64 (L s₀)
  r5 : s.gpr .r5 = BitVec.ofNat 64 x
  r7 : s.gpr .r7 = BitVec.ofNat 64 (O s₀)
  keep : ∀ r ∈ kept, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mid : Mid s₀ s.mem
  done : Done s₀ 0 s.mem
  frame : Frame [stR s₀] s₀.mem s.mem

theorem kept_chk : ∀ r ∈ kept, r ∉ chk := by decide

/-- The memory after `start`. -/
def startMem (s₀ : State) : Mem :=
  ((((s₀.mem.writeW (st s₀ + BitVec.ofNat 64 576) (s₀.gpr .r24)).writeW (st s₀ + BitVec.ofNat 64 584)
    (s₀.gpr .r25)).writeW (st s₀ + BitVec.ofNat 64 592) (s₀.gpr .r26)).writeW (st s₀ + BitVec.ofNat 64 600)
    s₀.lr).writeW (st s₀ + BitVec.ofNat 64 608) (BitVec.ofNat 64 (N s₀ - L s₀))

theorem startMem_frame (s₀ : State) : Frame [stR s₀] s₀.mem (startMem s₀) := by
  simp only [startMem]
  exact (((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_st _ (d := 576) (by decide))).writeW
    (List.mem_singleton_self _) _ (contains_st _ (d := 584) (by decide))).writeW (List.mem_singleton_self _) _
    (contains_st _ (d := 592) (by decide))).writeW (List.mem_singleton_self _) _
    (contains_st _ (d := 600) (by decide))).writeW (List.mem_singleton_self _) _
    (contains_st _ (d := 608) (by decide))

theorem startMem_mid (s₀ : State) : Mid s₀ (startMem s₀) := by
  refine ⟨fun i hi => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [startMem]
    rw [byte_writeW_ofNat _ _ _ (by omega) (by omega) (by omega),
      byte_writeW_ofNat _ _ _ (by omega) (by omega) (by omega),
      byte_writeW_ofNat _ _ _ (by omega) (by omega) (by omega),
      byte_writeW_ofNat _ _ _ (by omega) (by omega) (by omega),
      byte_writeW_ofNat _ _ _ (by omega) (by omega) (by omega)]
  all_goals simp (config := {decide := true}) only [startMem, Mem.readW_writeW_self64, readW_writeW_ofNat]

theorem start_ok {s₀ : State} (hp : APre s₀) (hle : L s₀ ≤ N s₀) {s : State} (h : Q0 s₀ s) :
    WP isa (.block start) s fun s' => R1 s₀ (L s₀) s' ∧ s'.gpr .r8 = s.gpr .r8 := by
  have hw : ∀ d, d + 8 ≤ 768 → InRegions s.wr (st s₀ + BitVec.ofNat 64 d) 8 := fun d hd => by
    rw [h.rest.wr]; exact hp.w_st hd
  have g : ∀ r, r ∉ chk → s.gpr r = s₀.gpr r := h.rest.other
  have r3 : s.gpr .r3 = st s₀ := g _ (by decide)
  unfold start
  refine wp_std (a := st s₀ + BitVec.ofNat 64 576) (by decide) ⟨by decide, by decide⟩ (by rw [r3])
    (hw 576 (by decide)) fun s₁ u₁ l₁ => ?_
  refine wp_std (a := st s₀ + BitVec.ofNat 64 584) (by decide) ⟨by decide, by decide⟩ (by rw [u₁.gpr, r3])
    (by rw [u₁.wr]; exact hw 584 (by decide)) fun s₂ u₂ l₂ => ?_
  refine wp_std (a := st s₀ + BitVec.ofNat 64 592) (by decide) ⟨by decide, by decide⟩
    (by rw [u₂.gpr, u₁.gpr, r3]) (by rw [u₂.wr, u₁.wr]; exact hw 592 (by decide)) fun s₃ u₃ l₃ => ?_
  refine wp_mflr fun s₄ u₄ => ?_
  have g₄ : ∀ r, r ≠ .r0 → s₄.gpr r = s.gpr r := fun r hr => by rw [u₄.other r hr, u₃.gpr, u₂.gpr, u₁.gpr]
  refine wp_std (a := st s₀ + BitVec.ofNat 64 600) (by decide) ⟨by decide, by decide⟩
    (by rw [g₄ _ (by decide), r3]) (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact hw 600 (by decide))
    fun s₅ u₅ _ => ?_
  refine wp_mov fun s₆ u₆ => wp_mov fun s₇ u₇ => wp_mov fun s₈ u₈ => wp_sub fun s₉ u₉ => ?_
  have g₈ : ∀ r, r ≠ .r0 → r ≠ .r24 → r ≠ .r25 → r ≠ .r26 → s₈.gpr r = s.gpr r :=
    fun r h0 h24 h25 h26 => by rw [u₈.other r h26, u₇.other r h25, u₆.other r h24, u₅.gpr, g₄ r h0]
  have g₉ : ∀ r, r ≠ .r0 → r ≠ .r24 → r ≠ .r25 → r ≠ .r26 → r ≠ .r9 → s₉.gpr r = s.gpr r :=
    fun r h0 h24 h25 h26 h9 => by rw [u₉.other r h9, g₈ r h0 h24 h25 h26]
  have v24 : s₉.gpr .r24 = st s₀ := by
    rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, u₅.gpr,
      g₄ _ (by decide), r3]
  have hL5 : s.gpr .r5 = BitVec.ofNat 64 (L s₀) := by rw [g _ (by decide)]; simp [L]
  have v9 : s₉.gpr .r9 = BitVec.ofNat 64 (N s₀ - L s₀) := by
    rw [u₉.gpr, g₈ .r9 (by decide) (by decide) (by decide) (by decide),
      g₈ .r5 (by decide) (by decide) (by decide) (by decide), h.r9, hL5, sub_ofNat hle]
  refine wp_std (a := st s₀ + BitVec.ofNat 64 608) (by decide) ⟨by decide, by decide⟩ (by rw [v24])
    (by rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact hw 608 (by decide))
    fun s₁₀ u₁₀ _ => WP.block_nil ?_
  have e24 : s.gpr .r24 = s₀.gpr .r24 := g _ (by decide)
  have e25 : s₁.gpr .r25 = s₀.gpr .r25 := by rw [u₁.gpr]; exact g _ (by decide)
  have e26 : s₂.gpr .r26 = s₀.gpr .r26 := by rw [u₂.gpr, u₁.gpr]; exact g _ (by decide)
  have e0 : s₄.gpr .r0 = s₀.lr := by rw [u₄.gpr, l₃, l₂, l₁, h.rest.lr]
  have hm : s₁₀.mem = startMem s₀ := by
    rw [u₁₀.mem, v9, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, e0, u₄.mem, u₃.mem, e26, u₂.mem, e25, u₁.mem, e24,
      h.rest.mem]
    rfl
  refine ⟨⟨by rw [u₁₀.gpr, v24], ?_, ?_, by rw [u₁₀.gpr, g₉ _ (by decide) (by decide) (by decide) (by decide)
      (by decide), hL5], by rw [u₁₀.gpr, g₉ _ (by decide) (by decide) (by decide) (by decide) (by decide), h.r7],
    fun r hr => ?_, ?_, ?_, by rw [hm]; exact startMem_mid s₀, fun k hk => ?_, by rw [hm]; exact startMem_frame s₀⟩,
    by rw [u₁₀.gpr, g₉ _ (by decide) (by decide) (by decide) (by decide) (by decide)]⟩
  · rw [u₁₀.gpr, u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), u₅.gpr,
      g₄ _ (by decide), g _ (by decide)]
  · rw [u₁₀.gpr, u₉.other _ (by decide), u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr,
      g₄ _ (by decide), hL5]
  · rw [u₁₀.gpr, g₉ r (kept_ne hr) (kept_ne hr) (kept_ne hr) (kept_ne hr) (kept_ne hr)]
    exact g r (kept_chk r hr)
  · rw [u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rest.rd]
  · rw [u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.rest.wr]
  · rw [hm, (startMem_frame s₀).bytes (R := dR s₀) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hp.st_d.symm)
      (show L s₀ ≤ 2 ^ 64 by have := L_lt s₀; omega) hk, ite_neg (Nat.not_lt_zero _)]

theorem sel_ok {s₀ : State} {s : State} (h : R1 s₀ (L s₀) s)
    (hc : s.gpr .r8 = BitVec.ofNat 64 (decide (O s₀ < L s₀)).toNat) :
    WP isa (.ite (.nonzero .d .r8) (.block [mov .r5 .r7]) (.block [])) s (R1 s₀ (H s₀)) := by
  refine WP.ite (decide (O s₀ < L s₀)) (by
      rw [eval_nonzero_ofNat s .r8 (by cases decide (O s₀ < L s₀) <;> decide) hc]
      by_cases hh : O s₀ < L s₀ <;> simp [hh]) (fun hlt => ?_) (fun hge => ?_)
  · simp only [decide_eq_true_eq] at hlt
    refine wp_mov fun s' u => WP.block_nil ?_
    exact ⟨by rw [u.other _ (by decide), h.r24], by rw [u.other _ (by decide), h.r25],
      by rw [u.other _ (by decide), h.r26],
      by rw [u.gpr, h.r7, H, headLen, bufLeft, Nat.min_eq_left (Nat.le_of_lt hlt)],
      by rw [u.other _ (by decide), h.r7],
      fun r hr => by rw [u.other r (kept_ne hr)]; exact h.keep r hr,
      by rw [u.rd, h.rd], by rw [u.wr, h.wr], u.mem ▸ h.mid, u.mem ▸ h.done, u.mem ▸ h.frame⟩
  · simp only [decide_eq_false_iff_not, Nat.not_lt] at hge
    refine WP.block_nil (M := isa) ⟨h.r24, h.r25, h.r26, ?_, h.r7, h.keep, h.rd, h.wr, h.mid, h.done, h.frame⟩
    rw [h.r5, H, headLen, bufLeft, Nat.min_eq_right hge]

/-- After `part1`: the bytes from the buffered block XORed, and `r5` the
bytes of the whole blocks. -/
structure Q1 (s₀ s : State) : Prop where
  r24 : s.gpr .r24 = st s₀
  r25 : s.gpr .r25 = dp s₀ + BitVec.ofNat 64 (H s₀)
  r26 : s.gpr .r26 = BitVec.ofNat 64 (L s₀ - H s₀)
  r5 : s.gpr .r5 = BitVec.ofNat 64 (64 * NB s₀)
  keep : ∀ r ∈ kept, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mid : Mid s₀ s.mem
  done : Done s₀ (H s₀) s.mem
  frame : Frame [stR s₀, dR s₀] s₀.mem s.mem

theorem d_ne_st {s₀ : State} (hp : APre s₀) {j k : Nat} (hj : j < L s₀) (hk : k < 768) :
    dp s₀ + BitVec.ofNat 64 j ≠ st s₀ + BitVec.ofNat 64 k := by
  intro he
  have c₁ : (dR s₀).Contains (dp s₀ + BitVec.ofNat 64 j) 1 :=
    Offset.contains_base _ (by omega) (by have := L_lt s₀; omega)
  have c₂ : (stR s₀).Contains (st s₀ + BitVec.ofNat 64 k) 1 := Offset.contains_base _ (by omega) (by omega)
  rw [he] at c₁
  exact hp.st_d _ c₂ c₁

theorem dR_byte {s₀ : State} (hp : APre s₀) {k : Nat} (hk : k < L s₀) : InRegions s₀.wr (dp s₀ + BitVec.ofNat 64 k) 1 :=
  ⟨dR s₀, by rw [hp.wr]; simp, Offset.contains_base _ (by omega) (by have := L_lt s₀; omega)⟩

theorem stR_byte {s₀ : State} (hp : APre s₀) {k : Nat} (hk : k < 768) : InRegions s₀.wr (st s₀ + BitVec.ofNat 64 k) 1 :=
  ⟨stR s₀, by rw [hp.wr]; simp, Offset.contains_base _ (by omega) (by omega)⟩

theorem not_in_prefix (p : Addr) {k c : Nat} (hk : c ≤ k) (hk' : k < 2 ^ 64) :
    ¬ (⟨p, c⟩ : Region).Contains (p + BitVec.ofNat 64 k) 1 := by
  simp only [Region.Contains]
  rw [Mem.sub_ofNat_toNat p hk']
  omega

theorem prefix_sub (p : Addr) {c n : Nat} (h : c ≤ n) : Region.Sub ⟨p, c⟩ ⟨p, n⟩ := Region.sub_prefix h

/-- `(x >>> 6) <<< 6` rounds down to a multiple of 64. -/
theorem round64 {x : Nat} (hx : x < 2 ^ 64) :
    (BitVec.ofNat 64 x >>> 6) <<< 6 = BitVec.ofNat 64 (64 * (x / 64)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hx, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  omega

theorem part1_ok {s₀ : State} (hp : APre s₀) (hle : L s₀ ≤ N s₀) {s : State} (h : Q0 s₀ s) :
    WP isa part1 s (Q1 s₀) := by
  have hL := L_lt s₀
  have hH := H_le s₀
  have hHO := H_le_O s₀
  have hO := O_lt s₀
  refine WP.seq (WP.mono (start_ok hp hle h) fun s₁ ⟨h₁, hc₁⟩ => ?_)
  refine WP.seq (WP.mono (sel_ok h₁ (by rw [hc₁, h.r8])) fun s₂ h₂ => ?_)
  -- The pointer to the bytes left in the buffered block.
  have h₃ : WP isa (.block [.addi .r4 .r24 128, .sub .r4 .r4 .r7]) s₂
      fun s₃ => R1 s₀ (H s₀) s₃ ∧ s₃.gpr .r4 = st s₀ + BitVec.ofNat 64 (128 - O s₀) := by
    refine wp_addi (by decide) (by decide) fun s' u => ?_
    refine wp_sub fun s'' u' => WP.block_nil ?_
    have g : ∀ r, r ≠ .r4 → s''.gpr r = s₂.gpr r := fun r hr => by rw [u'.other r hr, u.other r hr]
    refine ⟨⟨by rw [g _ (by decide), h₂.r24], by rw [g _ (by decide), h₂.r25], by rw [g _ (by decide), h₂.r26],
      by rw [g _ (by decide), h₂.r5], by rw [g _ (by decide), h₂.r7],
      fun r hr => by rw [g r (kept_ne hr)]; exact h₂.keep r hr,
      by rw [u'.rd, u.rd, h₂.rd], by rw [u'.wr, u.wr, h₂.wr], by rw [u'.mem, u.mem]; exact h₂.mid,
      by rw [u'.mem, u.mem]; exact h₂.done, by rw [u'.mem, u.mem]; exact h₂.frame⟩, ?_⟩
    rw [u'.gpr, u.gpr, u.other .r7 (by decide), h₂.r24, h₂.r7,
      show (BitVec.ofNat 64 128 : BitVec 64) = BitVec.ofNat 64 (128 - O s₀) + BitVec.ofNat 64 (O s₀) by
        rw [BitVec.ofNat_add_ofNat, show 128 - O s₀ + O s₀ = 128 by omega],
      ← BitVec.add_assoc, BitVec.add_sub_cancel]
  refine WP.seq (WP.mono h₃ fun s₃ ⟨h₃, hr4⟩ => ?_)
  have hb : BPre s₃ (dp s₀) (st s₀ + BitVec.ofNat 64 (128 - O s₀)) (H s₀) :=
    ⟨h₃.r25, hr4, h₃.r5, by omega, fun k hk => by rw [h₃.wr]; exact dR_byte hp (by omega),
      fun k hk => by
        rw [h₃.wr, Offset.add_add]
        obtain ⟨r, hr, hc⟩ := stR_byte hp (k := 128 - O s₀ + k) (by omega)
        exact ⟨r, List.mem_append_right _ hr, hc⟩,
      fun j hj k hk => by rw [Offset.add_add]; exact d_ne_st hp (by omega) (by omega)⟩
  refine WP.seq (WP.mono (xorBytes_ok hb) fun s₄ h₄ => ?_)
  have hr26 : s₄.gpr .r26 = BitVec.ofNat 64 (L s₀ - H s₀) := by
    rw [h₄.r26, h₃.r26, sub_ofNat hH]
  refine wp_lsr (by decide) fun s₅ u₅ => wp_lsl (by decide) fun s₆ u₆ => WP.block_nil ?_
  have g : ∀ r, r ≠ .r5 → s₆.gpr r = s₄.gpr r := fun r hr => by rw [u₆.other r hr, u₅.other r hr]
  have hm : s₆.mem = s₄.mem := by rw [u₆.mem, u₅.mem]
  have hnb : 64 * ((L s₀ - H s₀) / 64) = 64 * NB s₀ := by simp only [NB, blocksOf, H]
  refine ⟨by rw [g _ (by decide), h₄.keep _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), h₃.r24],
    by rw [g _ (by decide), h₄.r25], by rw [g _ (by decide), hr26],
    by rw [u₆.gpr, u₅.gpr, hr26, round64 (by omega), hnb],
    fun r hr => by
      rw [g r (kept_ne hr), h₄.keep r (kept_ne hr) (kept_ne hr) (kept_ne hr) (kept_ne hr) (kept_ne hr)
        (kept_ne hr)]
      exact h₃.keep r hr,
    by rw [u₆.rd, u₅.rd, h₄.rd, h₃.rd], by rw [u₆.wr, u₅.wr, h₄.wr, h₃.wr], ⟨fun i hi => ?_, ?_⟩,
    fun k hk => ?_, ?_⟩
  · rw [hm, h₄.frame _ fun r hr hc => ?_]
    · exact h₃.mid.keep i hi
    · simp only [List.mem_singleton] at hr; subst hr
      exact hp.st_d _ (Offset.contains_base (st s₀) (d := i) (n := 1) (k := 768) (by omega) (by omega))
        (Offset.sub_base (dp s₀) (d := 0) (n := H s₀) (k := L s₀) (by omega) _ (by simpa using hc))
  · rw [hm]
    exact h₃.mid.saved.frame h₄.frame fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.st_d.sub_left (savR_sub s₀)).sub_right fun x hx => by
        simpa using Offset.sub_base (dp s₀) (d := 0) (n := H s₀) (k := L s₀) (by omega) x (by simpa using hx)
  · rw [hm]
    by_cases hk' : k < H s₀
    · rw [h₄.data k hk', h₃.done k hk, Offset.add_add, h₃.mid.keep _ (by omega)]
      simp [hk', KS]
    · rw [h₄.frame _ fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact not_in_prefix _ (by omega) (by omega),
        h₃.done k hk]
      simp [hk']
  · rw [hm]
    exact (h₃.frame.mono (by simp)).trans (h₄.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨dR s₀, by simp, prefix_sub _ hH⟩)

/-! ## The whole blocks -/

/-- The memory before the counter is advanced: the state copied to
`p + 192`. -/
def copyMem8 (m : Mem) (p : Addr) : Mem :=
  (((((((m.writeW (p + BitVec.ofNat 64 192) (m.readW p 64)).writeW (p + BitVec.ofNat 64 200)
    (m.readW (p + BitVec.ofNat 64 8) 64)).writeW (p + BitVec.ofNat 64 208) (m.readW (p + BitVec.ofNat 64 16) 64)).writeW
    (p + BitVec.ofNat 64 216) (m.readW (p + BitVec.ofNat 64 24) 64)).writeW (p + BitVec.ofNat 64 224)
    (m.readW (p + BitVec.ofNat 64 32) 64)).writeW (p + BitVec.ofNat 64 232) (m.readW (p + BitVec.ofNat 64 40) 64)).writeW
    (p + BitVec.ofNat 64 240) (m.readW (p + BitVec.ofNat 64 48) 64)).writeW (p + BitVec.ofNat 64 248)
    (m.readW (p + BitVec.ofNat 64 56) 64)

/-- And its counter advanced by `c`. -/
def copyMem (m : Mem) (p : Addr) (c : BitVec 32) : Mem :=
  (copyMem8 m p).writeW (p + BitVec.ofNat 64 48) (m.readW (p + BitVec.ofNat 64 48) 32 + c)

/-- Reading a word after writing a 64-bit word elsewhere, at offsets from `p`. -/
theorem readW64_ofNat (m : Mem) (p : Addr) (v : BitVec 64) {d e : Nat} (h : d + 8 ≤ e ∨ e + 8 ≤ d)
    (hd : d < 2 ^ 32) (he : e < 2 ^ 32) :
    (m.writeW (p + BitVec.ofNat 64 e) v).readW (p + BitVec.ofNat 64 d) 64 = m.readW (p + BitVec.ofNat 64 d) 64 :=
  readW_writeW_ofNat m p v h (by omega) (by omega) (by decide)

/-- `lo32_add`, with the width as the model writes it. -/
theorem lo32_add' (x y : BitVec 64) : (x + y).setWidth (8 * 4) = x.setWidth 32 + y.setWidth 32 := lo32_add x y

set_option simprocs false in
theorem args_exec {s : State} {p : Addr} (hr24 : s.gpr .r24 = p)
    (hw : ∀ d, d + 8 ≤ 768 → InRegions s.wr (p + BitVec.ofNat 64 d) 8) (hrd : s.rd = []) :
    WP isa (.block blocksArgs) s fun s' => s'.mem = copyMem s.mem p ((s.gpr .r5 >>> 6).setWidth 32) ∧
      s'.gpr .r3 = p + BitVec.ofNat 64 192 ∧ s'.gpr .r4 = s.gpr .r25 ∧ s'.gpr .r6 = p + BitVec.ofNat 64 256 ∧
      s'.gpr .r5 = s.gpr .r5 ∧ s'.gpr .r25 = s.gpr .r25 + s.gpr .r5 ∧
      s'.gpr .r26 = s.gpr .r26 - s.gpr .r5 ∧ s'.gpr .r24 = p ∧
      (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have i : ∀ d, d + 8 ≤ 768 → InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 d) 8 := fun d hd => by
    rw [hrd, List.nil_append]; exact hw d hd
  have o4 : InRegions s.wr (p + BitVec.ofNat 64 48) 4 := by
    obtain ⟨r, hr, hc⟩ := hw 48 (by decide); exact ⟨r, hr, by simp only [Region.Contains] at hc ⊢; omega⟩
  have i4 : InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 48) 4 := by rw [hrd, List.nil_append]; exact o4
  have i0 := i 0 (by decide); have i8 := i 8 (by decide); have i16 := i 16 (by decide)
  have i24 := i 24 (by decide); have i32 := i 32 (by decide); have i40 := i 40 (by decide)
  have i48 := i 48 (by decide); have i56 := i 56 (by decide)
  have o192 := hw 192 (by decide); have o200 := hw 200 (by decide); have o208 := hw 208 (by decide)
  have o216 := hw 216 (by decide); have o224 := hw 224 (by decide); have o232 := hw 232 (by decide)
  have o240 := hw 240 (by decide); have o248 := hw 248 (by decide)
  simp only [BitVec.add_zero] at i0
  apply WP.of_runBlock
  simp (config := {decide := true}) only [blocksArgs, Impl.ChaCha20.PPC64LE.Xor.mov, runBlock_cons, runStep_some,
    runBlock_nil, exec, addr, Size.bytes, State.load, State.store, State.write, State.read, Size.bits, Size.ext,
    BitVec.setWidth_eq, Option.bind_some, Option.map_some, hr24, i0, i8, i16, i24, i32, i40, i48, i56, i4, o4, o192, o200, o208, o216,
    o224, o232, o240, o248, ite_true, ite_false, Option.some.injEq, exists_eq_left', write64_eq, read64_eq,
    write32_eq, read32_eq, BitVec.add_zero]
  simp (config := {decide := true}) only [readW_writeW_ofNat, copyMem, copyMem8]
  refine ⟨by rw [lo32_add', lo32_ext], trivial, trivial, trivial, trivial, trivial, trivial, trivial, fun r hr => ?_, trivial⟩
  simp only [kept, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (config := {decide := true})

theorem copyMem8_frame (m : Mem) (p : Addr) : Frame [⟨p + BitVec.ofNat 64 192, 64⟩] m (copyMem8 m p) := by
  have c : ∀ d, 192 ≤ d → d + 8 ≤ 256 →
      (⟨p + BitVec.ofNat 64 192, 64⟩ : Region).Contains (p + BitVec.ofNat 64 d) (64 / 8) :=
    fun d h₁ h₂ => Offset.contains _ h₁ (by omega) (by omega)
  simp only [copyMem8]
  have w : ∀ {m' : Mem} (_ : Frame [⟨p + BitVec.ofNat 64 192, 64⟩] m m') (d : Nat), 192 ≤ d → d + 8 ≤ 256 →
      ∀ v : BitVec 64, Frame [⟨p + BitVec.ofNat 64 192, 64⟩] m (m'.writeW (p + BitVec.ofNat 64 d) v) :=
    fun hf d h₁ h₂ v => hf.writeW (List.mem_singleton_self _) v (c d h₁ h₂)
  exact w (w (w (w (w (w (w (w (Frame.refl _ _) 192 (by decide) (by decide) _) 200 (by decide) (by decide) _)
    208 (by decide) (by decide) _) 216 (by decide) (by decide) _) 224 (by decide) (by decide) _) 232 (by decide)
    (by decide) _) 240 (by decide) (by decide) _) 248 (by decide) (by decide) _

theorem copyMem_frame (m : Mem) (p : Addr) (c : BitVec 32) :
    Frame [⟨p, 64⟩, ⟨p + BitVec.ofNat 64 192, 64⟩] m (copyMem m p c) := by
  refine ((copyMem8_frame m p).mono (by simp)).writeW (List.mem_cons_self ..) _ ?_
  exact Offset.contains_base _ (by omega) (by omega)

/-- The copy of the state. -/
theorem copyMem_copy (m : Mem) (p : Addr) (c : BitVec 32) :
    stateAt (copyMem m p c) (p + BitVec.ofNat 64 192) = stateAt m p := by
  refine stateAt_congr fun i hi => ?_
  rw [copyMem, Offset.add_add, byte_writeW_ofNat _ _ _ (by omega) (by omega) (by omega)]
  have hw : ∀ k, 24 ≤ k → k < 32 → (copyMem8 m p).readW (p + BitVec.ofNat 64 (8 * k)) 64 =
      m.readW (p + BitVec.ofNat 64 (8 * (k - 24))) 64 := by
    intro k h₁ h₂
    simp only [copyMem8]
    obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl :
      k = 24 ∨ k = 25 ∨ k = 26 ∨ k = 27 ∨ k = 28 ∨ k = 29 ∨ k = 30 ∨ k = 31 := by omega
    all_goals simp (config := {decide := true}) only [Nat.reduceMul, Nat.reduceSub, Mem.readW_writeW_self64,
      readW64_ofNat, BitVec.add_zero]
  have hm : ∀ k, 0 ≤ k → k < 8 → m.readW (p + BitVec.ofNat 64 (8 * k)) 64 = m.readW (p + BitVec.ofNat 64 (8 * k)) 64 :=
    fun _ _ _ => rfl
  rw [byte_of_words64 hw (by omega) (by omega), byte_of_words64 hm (i := i) (Nat.zero_le _) (by omega),
    show (192 + i) / 8 - 24 = i / 8 by omega, show (192 + i) % 8 = i % 8 by omega]

/-- The state, with its counter advanced. -/
theorem copyMem_state (m : Mem) (p : Addr) (c : BitVec 32) :
    stateAt (copyMem m p c) p = (stateAt m p).set 12 ((stateAt m p)[12] + c) := by
  rw [copyMem, stateAt_writeW_counter, stateAt_frame (copyMem8_frame m p) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.base_disjoint _ (by omega) (by omega))]
  simp [stateAt]

theorem shr_eq {nb : Nat} (h : 64 * nb < 2 ^ 64) :
    (BitVec.ofNat 64 (64 * nb) >>> 6).setWidth 32 = BitVec.ofNat 32 nb := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt h, Nat.shiftRight_eq_div_pow]
  omega

/-- After `part2`: the whole blocks XORed, and the counter advanced past
them. -/
structure Q2 (s₀ s : State) : Prop where
  r24 : s.gpr .r24 = st s₀
  r25 : s.gpr .r25 = dp s₀ + BitVec.ofNat 64 (H s₀ + 64 * NB s₀)
  r26 : s.gpr .r26 = BitVec.ofNat 64 (T s₀)
  keep : ∀ r ∈ kept, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  state : stateAt s.mem (st s₀) = ctr (S0 s₀) (NB s₀)
  buf : ∀ i < 64, s.mem (st s₀ + BitVec.ofNat 64 (64 + i)) = s₀.mem (st s₀ + BitVec.ofNat 64 (64 + i))
  saved : Saved s₀ s.mem
  done : Done s₀ (H s₀ + 64 * NB s₀) s.mem
  frame : Frame [stR s₀, dR s₀] s₀.mem s.mem

theorem nb_zero_ok {s₀ : State} {s : State} (h : Q1 s₀ s) (h0 : 64 * NB s₀ = 0) : Q2 s₀ s := by
  have hT := T_eq s₀
  refine ⟨h.r24, by rw [h.r25, h0, Nat.add_zero], by rw [h.r26, hT, h0, Nat.sub_zero], h.keep, h.rd, h.wr,
    by rw [h.mid.state, show NB s₀ = 0 by omega, ctr_zero], fun i hi => h.mid.keep _ (by omega), h.mid.saved,
    by rw [h0, Nat.add_zero]; exact h.done, h.frame⟩

theorem Q1.w {s₀ s : State} (hp : APre s₀) (h : Q1 s₀ s) :
    ∀ d, d + 8 ≤ 768 → InRegions s.wr (st s₀ + BitVec.ofNat 64 d) 8 := fun d hd => by
  rw [h.wr]; exact hp.w_st hd

/-- The regions of the call of `vg_chacha20_xor`: the copy of the state,
the data and the working space. -/
abbrev cpR (s₀ : State) : Region := ⟨st s₀ + BitVec.ofNat 64 192, 64⟩
abbrev blR (s₀ : State) : Region := ⟨dp s₀ + BitVec.ofNat 64 (H s₀), 64 * NB s₀⟩
abbrev wkR (s₀ : State) : Region := ⟨st s₀ + BitVec.ofNat 64 256, 320⟩

theorem cpR_sub (s₀ : State) : Region.Sub (cpR s₀) (stR s₀) := Offset.sub_base _ (by omega)
theorem wkR_sub (s₀ : State) : Region.Sub (wkR s₀) (stR s₀) := Offset.sub_base _ (by omega)
theorem blR_sub (s₀ : State) : Region.Sub (blR s₀) (dR s₀) := Offset.sub_base _ (HNB_le s₀)

/-- The registers kept are callee-saved. -/
theorem kept_preserved : ∀ r ∈ kept, r ∈ preserved := by decide

theorem blocks_ok {s₀ : State} (hp : APre s₀) {s : State} (h : Q1 s₀ s) (hnb : 0 < NB s₀) :
    WP isa (.seq (.block blocksArgs) (.call "vg_chacha20_xor" Impl.ChaCha20.PPC64LE.Xor.xor)) s (Q2 s₀) := by
  have hL := L_lt s₀
  have hH := H_le s₀
  have hHNB := HNB_le s₀
  have hT := T_eq s₀
  refine WP.seq (WP.mono (args_exec h.r24 (h.w hp) (by rw [h.rd, hp.rd])) fun s₁ ⟨m₁, r3₁, r4₁, r6₁, r5₁,
    r25₁, r26₁, r24₁, k₁, rd₁, wr₁⟩ => ?_)
  rw [h.r5, shr_eq (by omega)] at m₁
  rw [h.r5] at r5₁
  rw [h.r25] at r4₁
  have hwr₁ : s₁.wr = [stR s₀, dR s₀] := by rw [wr₁, h.wr, hp.wr]
  have hrd₁ : s₁.rd = [] := by rw [rd₁, h.rd, hp.rd]
  have dSB : (cpR s₀).Disjoint (wkR s₀) := Offset.disjoint _ (by omega) (by omega) (by omega)
  have dSD : (cpR s₀).Disjoint (blR s₀) := (hp.st_d.sub_left (cpR_sub s₀)).sub_right (blR_sub s₀)
  have dDB : (blR s₀).Disjoint (wkR s₀) := (hp.st_d.sub_left (wkR_sub s₀)).symm.sub_left (blR_sub s₀)
  have hcov : ∀ r ∈ [cpR s₀, blR s₀, wkR s₀], ∃ r' ∈ [stR s₀, dR s₀], ∃ o,
      r.base = r'.base + BitVec.ofNat 64 o ∧ o + r.len ≤ r'.len := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨stR s₀, by simp, 192, rfl, by simp⟩
    · exact ⟨dR s₀, by simp, H s₀, rfl, hHNB⟩
    · exact ⟨stR s₀, by simp, 256, rfl, by simp⟩
  have hwrap : (dp s₀ + BitVec.ofNat 64 (H s₀)).toNat + 64 * NB s₀ ≤ 2 ^ 64 := by
    have := hp.wrap_d
    rw [BitVec.toNat_add, toNat_ofNat_lt (by omega)]
    omega
  refine xor_call (S := st s₀ + BitVec.ofNat 64 192) (D := dp s₀ + BitVec.ofNat 64 (H s₀))
    (B := st s₀ + BitVec.ofNat 64 256) (n := 64 * NB s₀) r3₁ r4₁ r5₁ r6₁ (by omega) dSD dSB dDB hwrap
    (by rw [hrd₁, hwr₁, List.nil_append, List.nil_append]; exact Covers.of_sub hcov)
    (by rw [hwr₁]; exact Covers.of_sub hcov) ?_
  intro s₂ k₂ x₂
  have g : ∀ r ∈ preserved, s₂.gpr r = s₁.gpr r := k₂.cs
  -- Regions the call does not write.
  have nd : ∀ R : Region, R.Disjoint (cpR s₀) → R.Disjoint (blR s₀) → R.Disjoint (wkR s₀) →
      ∀ r ∈ [cpR s₀, blR s₀, wkR s₀], R.Disjoint r := by
    intro R h₁ h₂ h₃ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> assumption
  have nc : ∀ R : Region, R.Disjoint ⟨st s₀, 64⟩ → R.Disjoint ⟨st s₀ + BitVec.ofNat 64 192, 64⟩ →
      ∀ r ∈ [⟨st s₀, 64⟩, ⟨st s₀ + BitVec.ofNat 64 192, 64⟩], R.Disjoint r := by
    intro R h₁ h₂ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> assumption
  have fc := copyMem_frame s.mem (st s₀) (BitVec.ofNat 32 (NB s₀))
  rw [← m₁] at fc
  have stS : Region.Sub ⟨st s₀, 64⟩ (stR s₀) := prefix_sub _ (by omega)
  have bufS : Region.Sub ⟨st s₀ + BitVec.ofNat 64 64, 64⟩ (stR s₀) := Offset.sub_base _ (by omega)
  have svS := savR_sub s₀
  -- Anything in the state is apart from the data.
  have sd : ∀ R, Region.Sub R (stR s₀) → R.Disjoint (blR s₀) := fun R hR =>
    (hp.st_d.sub_left hR).sub_right (blR_sub s₀)
  have ds : ∀ R R', Region.Sub R (dR s₀) → Region.Sub R' (stR s₀) → R.Disjoint R' := fun R R' h₁ h₂ =>
    (hp.st_d.symm.sub_left h₁).sub_right h₂
  refine ⟨by rw [g .r24 (by decide), r24₁], ?_, ?_, fun r hr => ?_,
    by rw [k₂.rd, rd₁, h.rd], by rw [k₂.wr, wr₁, h.wr], ?_, fun i hi => ?_, ?_, fun k hk => ?_, ?_⟩
  · rw [g .r25 (by decide), r25₁, h.r25, h.r5, Offset.add_add]
  · rw [g .r26 (by decide), r26₁, h.r26, h.r5, sub_ofNat (by omega), hT, Nat.sub_sub]
  · rw [g r (kept_preserved r hr), k₁ r hr]
    exact h.keep r hr
  · rw [stateAt_frame k₂.frame (nd _
        (Offset.base_disjoint _ (by omega) (by omega)) (sd _ stS)
        (Offset.base_disjoint _ (by omega) (by omega))),
      m₁, copyMem_state, h.mid.state]
    rfl
  · rw [← Offset.add_add, k₂.frame.bytes (R := ⟨st s₀ + BitVec.ofNat 64 64, 64⟩) (nd _
        (Offset.disjoint _ (by omega) (by omega) (by omega)) (sd _ bufS)
        (Offset.disjoint _ (by omega) (by omega) (by omega))) (show 64 ≤ 2 ^ 64 by decide) hi,
      fc.bytes (R := ⟨st s₀ + BitVec.ofNat 64 64, 64⟩) (nc _ (Offset.disjoint_base _ (by omega) (by omega))
        (Offset.disjoint _ (by omega) (by omega) (by omega))) (show 64 ≤ 2 ^ 64 by decide) hi,
      Offset.add_add]
    exact h.mid.keep _ (by omega)
  · refine (h.mid.saved.frame fc (nc _ ?_ ?_)).frame k₂.frame (nd _ ?_ (sd _ svS) ?_)
    · exact Offset.disjoint_base _ (by omega) (by omega)
    · exact Offset.disjoint _ (by omega) (by omega) (by omega)
    · exact Offset.disjoint _ (by omega) (by omega) (by omega)
    · exact Offset.disjoint _ (by omega) (by omega) (by omega)
  · have fcd : s₁.mem (dp s₀ + BitVec.ofNat 64 k) = s.mem (dp s₀ + BitVec.ofNat 64 k) :=
      fc.bytes (R := dR s₀) (nc _ (ds _ _ (fun _ h => h) stS) (ds _ _ (fun _ h => h) (cpR_sub s₀)))
        (show L s₀ ≤ 2 ^ 64 by omega) hk
    by_cases hk₁ : k < H s₀
    · have hpre : Region.Sub ⟨dp s₀, H s₀⟩ (dR s₀) := prefix_sub _ hH
      rw [k₂.frame.bytes (R := ⟨dp s₀, H s₀⟩) (nd _ (ds _ _ hpre (cpR_sub s₀))
          (Offset.base_disjoint _ (by omega) (by omega)) (ds _ _ hpre (wkR_sub s₀)))
          (show H s₀ ≤ 2 ^ 64 by omega) hk₁]
      rw [fcd, h.done k hk, ite_pos hk₁, ite_pos (by omega)]
    by_cases hk₂ : k < H s₀ + 64 * NB s₀
    · have e := xor_getD (length_keystream _ _) x₂ (j := k - H s₀) (by omega)
      rw [Offset.add_add, show H s₀ + (k - H s₀) = k by omega, fcd, h.done k hk, ite_neg hk₁, m₁,
        copyMem_copy, h.mid.state, keystream_getD _ (by omega)] at e
      rw [e, ite_pos hk₂]
      simp only [KS, ite_neg hk₁]
    · have hR : Region.Sub ⟨dp s₀ + BitVec.ofNat 64 (H s₀ + 64 * NB s₀), L s₀ - (H s₀ + 64 * NB s₀)⟩ (dR s₀) :=
        Offset.sub_base _ (by omega)
      have := k₂.frame.bytes (R := ⟨dp s₀ + BitVec.ofNat 64 (H s₀ + 64 * NB s₀), L s₀ - (H s₀ + 64 * NB s₀)⟩)
        (nd _ (ds _ _ hR (cpR_sub s₀)) (Offset.disjoint _ (by omega) (by omega) (by omega))
          (ds _ _ hR (wkR_sub s₀))) (show L s₀ - (H s₀ + 64 * NB s₀) ≤ 2 ^ 64 by omega)
          (i := k - (H s₀ + 64 * NB s₀)) (by simp only; omega)
      rw [Offset.add_add, show H s₀ + 64 * NB s₀ + (k - (H s₀ + 64 * NB s₀)) = k by omega] at this
      rw [this, fcd, h.done k hk, ite_neg hk₁, ite_neg hk₂]
  · refine (h.frame.trans (fc.sub fun r hr => ?_)).trans (k₂.frame.sub fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨stR s₀, by simp, stS⟩
      · exact ⟨stR s₀, by simp, cpR_sub s₀⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨stR s₀, by simp, cpR_sub s₀⟩
      · exact ⟨dR s₀, by simp, blR_sub s₀⟩
      · exact ⟨stR s₀, by simp, wkR_sub s₀⟩

theorem part2_ok {s₀ : State} (hp : APre s₀) {s : State} (h : Q1 s₀ s) : WP isa part2 s (Q2 s₀) := by
  have hL := L_lt s₀
  have hHNB := HNB_le s₀
  refine WP.ite (decide (64 * NB s₀ = 0)) (by rw [eval_zero, h.r5, ofNat_beq_zero (by omega)])
    (fun h0 => WP.block_nil (M := isa) (nb_zero_ok h (by simpa using h0)))
    (fun h0 => blocks_ok hp h (by simp only [decide_eq_false_iff_not] at h0; omega))

/-! ## The last bytes -/

/-- After `part3`: all the data XORed; the counter advanced past the block
started, if any, which is buffered. -/
structure Q3 (s₀ s : State) : Prop where
  r24 : s.gpr .r24 = st s₀
  keep : ∀ r ∈ kept, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  state : stateAt s.mem (st s₀) = ctr (S0 s₀) (NB s₀ + if T s₀ = 0 then 0 else 1)
  buf : ∀ i < 64, s.mem (st s₀ + BitVec.ofNat 64 (64 + i)) =
    if T s₀ = 0 then s₀.mem (st s₀ + BitVec.ofNat 64 (64 + i))
    else (serialize (block (ctr (S0 s₀) (NB s₀)))).getD i 0
  saved : Saved s₀ s.mem
  done : Done s₀ (L s₀) s.mem
  frame : Frame [stR s₀, dR s₀] s₀.mem s.mem

theorem t_zero_ok {s₀ : State} {s : State} (h : Q2 s₀ s) (h0 : T s₀ = 0) : Q3 s₀ s := by
  have hT := T_eq s₀
  have hHNB := HNB_le s₀
  refine ⟨h.r24, h.keep, h.rd, h.wr, by rw [h.state, h0]; rfl, fun i hi => by rw [h.buf i hi, h0]; rfl, h.saved,
    by rw [show L s₀ = H s₀ + 64 * NB s₀ by omega]; exact h.done, h.frame⟩

/-- The buffered block, and the bytes the block function may write. -/
abbrev bufR (s₀ : State) : Region := ⟨st s₀ + BitVec.ofNat 64 64, 256⟩

theorem bufR_sub (s₀ : State) : Region.Sub (bufR s₀) (stR s₀) := Offset.sub_base _ (by omega)

/-- The counter advanced, and the arguments of `xorBytes` for the buffered
block. -/
theorem ctr_exec {s : State} {p : Addr} (hr24 : s.gpr .r24 = p) (hw : InRegions s.wr (p + BitVec.ofNat 64 48) 4)
    (hr : InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 48) 4) :
    WP isa (.block [.load .w .r9 .r24 48, .addi .r9 .r9 1, .store .w .r9 .r24 48, .addi .r4 .r24 64,
      mov .r5 .r26]) s fun s' =>
      s'.mem = s.mem.writeW (p + BitVec.ofNat 64 48) (s.mem.readW (p + BitVec.ofNat 64 48) 32 + 1) ∧
      s'.gpr .r4 = p + BitVec.ofNat 64 64 ∧ s'.gpr .r5 = s.gpr .r26 ∧
      (∀ r, r ≠ .r9 → r ≠ .r4 → r ≠ .r5 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine wp_lwz (a := p + BitVec.ofNat 64 48) (by decide) (by decide) (by rw [hr24]) hr fun s₁ u₁ => ?_
  refine wp_addi (by decide) (by decide) fun s₂ u₂ => ?_
  refine wp_stw (a := p + BitVec.ofNat 64 48) (by decide) (by decide)
    (by rw [u₂.other _ (by decide), u₁.other _ (by decide), hr24]) (by rw [u₂.wr, u₁.wr]; exact hw)
    fun s₃ g₃ => ?_
  refine wp_addi (by decide) (by decide) fun s₄ u₄ => wp_mov fun s₅ u₅ => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, fun r h₁ h₂ h₃ => ?_, ?_, ?_⟩
  · rw [u₅.mem, u₄.mem, g₃.mem, u₂.gpr, u₁.gpr, inc_setWidth, u₂.mem, u₁.mem]
  · rw [u₅.other _ (by decide), u₄.gpr, g₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), hr24]
  · rw [u₅.gpr, u₄.other _ (by decide), g₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide)]
  · rw [u₅.other r h₃, u₄.other r h₂, g₃.gpr, u₂.other r h₁, u₁.other r h₁]
  · rw [u₅.rd, u₄.rd, g₃.rd, u₂.rd, u₁.rd]
  · rw [u₅.wr, u₄.wr, g₃.wr, u₂.wr, u₁.wr]

theorem preserved_ne : ∀ r ∈ preserved, r ≠ .r3 ∧ r ≠ .r4 := by decide

theorem tail_ok {s₀ : State} (hp : APre s₀) {s : State} (h : Q2 s₀ s) (ht : T s₀ ≠ 0) :
    WP isa (.seq (.block tailArgs) (.seq (.call "vg_chacha20_block" Impl.ChaCha20.PPC64LE.block) tailXor))
      s (Q3 s₀) := by
  have hT := T_eq s₀
  have hHNB := HNB_le s₀
  have hL := L_lt s₀
  have h₁ : WP isa (.block tailArgs) s fun s₁ => s₁.gpr .r3 = st s₀ ∧
      s₁.gpr .r4 = st s₀ + BitVec.ofNat 64 64 ∧
      (∀ r, r ≠ .r3 → r ≠ .r4 → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine wp_mov fun s' u => wp_addi (by decide) (by decide) fun s'' u' => WP.block_nil ?_
    exact ⟨by rw [u'.other _ (by decide), u.gpr, h.r24], by rw [u'.gpr, u.other _ (by decide), h.r24],
      fun r h₁ h₂ => by rw [u'.other r h₂, u.other r h₁], by rw [u'.mem, u.mem], by rw [u'.rd, u.rd],
      by rw [u'.wr, u.wr]⟩
  refine WP.seq (WP.mono h₁ fun s₁ ⟨r3₁, r4₁, k₁, m₁, rd₁, wr₁⟩ => ?_)
  have hwr₁ : s₁.wr = [stR s₀, dR s₀] := by rw [wr₁, h.wr, hp.wr]
  have hrd₁ : s₁.rd = [] := by rw [rd₁, h.rd, hp.rd]
  have stS : Region.Sub ⟨st s₀, 64⟩ (stR s₀) := prefix_sub _ (by omega)
  refine WP.seq (block_call r3₁ r4₁ (Offset.disjoint_base _ (by omega) (by omega))
    (by
      rw [hrd₁, hwr₁]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨stR s₀, by simp, 0, by simp, show 0 + 64 ≤ 768 by decide⟩
      · exact ⟨stR s₀, by simp, 64, rfl, show 64 + 256 ≤ 768 by decide⟩)
    (by
      rw [hwr₁]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨stR s₀, by simp, 64, rfl, show 64 + 256 ≤ 768 by decide⟩) fun s₂ k₂ blk₂ => ?_)
  have g : ∀ r ∈ preserved, s₂.gpr r = s.gpr r := fun r hr => by
    rw [k₂.cs r hr, k₁ r (preserved_ne r hr).1 (preserved_ne r hr).2]
  have hw48 : InRegions s₂.wr (st s₀ + BitVec.ofNat 64 48) 4 := by
    rw [k₂.wr, hwr₁]; exact ⟨stR s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  have hr48 : InRegions (s₂.rd ++ s₂.wr) (st s₀ + BitVec.ofNat 64 48) 4 := by
    rw [k₂.rd, hrd₁, List.nil_append]; exact hw48
  refine WP.seq (WP.mono (ctr_exec (by rw [g .r24 (by decide), h.r24]) hw48 hr48)
    fun s₃ ⟨m₃, r4₃, r5₃, k₃, rd₃, wr₃⟩ => ?_)
  have hT64 : T s₀ < 64 := Nat.mod_lt _ (by decide)
  have hr25₃ : s₃.gpr .r25 = dp s₀ + BitVec.ofNat 64 (H s₀ + 64 * NB s₀) := by
    rw [k₃ .r25 (by decide) (by decide) (by decide), g .r25 (by decide), h.r25]
  have dS : ∀ R R', Region.Sub R (dR s₀) → Region.Sub R' (stR s₀) → R.Disjoint R' := fun R R' h₁ h₂ =>
    (hp.st_d.symm.sub_left h₁).sub_right h₂
  have hb : BPre s₃ (dp s₀ + BitVec.ofNat 64 (H s₀ + 64 * NB s₀)) (st s₀ + BitVec.ofNat 64 64) (T s₀) :=
    ⟨hr25₃, r4₃, by rw [r5₃, g .r26 (by decide), h.r26], by omega,
      fun k hk => by
        rw [wr₃, k₂.wr, hwr₁, Offset.add_add]
        exact ⟨dR s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩,
      fun k hk => by
        rw [rd₃, wr₃, k₂.rd, k₂.wr, hrd₁, hwr₁, List.nil_append, Offset.add_add]
        exact ⟨stR s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩,
      fun j hj k hk => by rw [Offset.add_add, Offset.add_add]; exact d_ne_st hp (by omega) (by omega)⟩
  refine WP.mono (xorBytes_ok hb) fun s₄ h₄ => ?_
  have f₂ := k₂.frame
  have f₃ : Frame [⟨st s₀ + BitVec.ofNat 64 48, 4⟩] s₂.mem s₃.mem := by
    rw [m₃]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have tR : Region.Sub ⟨dp s₀ + BitVec.ofNat 64 (H s₀ + 64 * NB s₀), T s₀⟩ (dR s₀) :=
    Offset.sub_base _ (by omega)
  have c48 : Region.Sub ⟨st s₀ + BitVec.ofNat 64 48, 4⟩ (stR s₀) := Offset.sub_base _ (by omega)
  have st₂ : stateAt s₂.mem (st s₀) = ctr (S0 s₀) (NB s₀) := by
    rw [stateAt_frame f₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.base_disjoint _ (by omega) (by omega)),
      m₁, h.state]
  have bb : ∀ i < 64, s₂.mem (st s₀ + BitVec.ofNat 64 (64 + i)) =
      (serialize (block (ctr (S0 s₀) (NB s₀)))).getD i 0 := by
    intro i hi
    rw [← Offset.add_add, ← serialize_stateAt s₂.mem _ hi, blk₂, m₁, h.state]
  have b3 : ∀ i < 64, s₃.mem (st s₀ + BitVec.ofNat 64 (64 + i)) = s₂.mem (st s₀ + BitVec.ofNat 64 (64 + i)) := by
    intro i hi
    rw [m₃]; exact byte_writeW_ofNat _ _ _ (by omega) (by omega) (by omega)
  have b4 : ∀ i < 64, s₄.mem (st s₀ + BitVec.ofNat 64 (64 + i)) = s₃.mem (st s₀ + BitVec.ofNat 64 (64 + i)) := by
    intro i hi
    rw [← Offset.add_add]
    exact h₄.frame.bytes (R := ⟨st s₀ + BitVec.ofNat 64 64, 64⟩) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (dS _ _ tR (Offset.sub_base _ (by omega))).symm) (show 64 ≤ 2 ^ 64 by decide) hi
  refine ⟨?_, fun r hr => ?_, by rw [h₄.rd, rd₃, k₂.rd, rd₁, h.rd], by rw [h₄.wr, wr₃, k₂.wr, wr₁, h.wr], ?_,
    fun i hi => ?_, ?_, fun k hk => ?_, ?_⟩
  · rw [h₄.keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      k₃ .r24 (by decide) (by decide) (by decide), g .r24 (by decide), h.r24]
  · rw [h₄.keep r (kept_ne hr) (kept_ne hr) (kept_ne hr) (kept_ne hr) (kept_ne hr) (kept_ne hr),
      k₃ r (kept_ne hr) (kept_ne hr) (kept_ne hr), g r (kept_preserved r hr)]
    exact h.keep r hr
  · have e12 : s₂.mem.readW (st s₀ + BitVec.ofNat 64 48) 32 = (ctr (S0 s₀) (NB s₀))[12] := by
      rw [← st₂]; simp [stateAt]
    rw [stateAt_frame h₄.frame (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (dS _ _ tR stS).symm),
      m₃, stateAt_writeW_counter, st₂, e12, ctr_succ, ite_neg ht]
  · rw [b4 i hi, b3 i hi, bb i hi, ite_neg ht]
  · have svS := savR_sub s₀
    rw [m₁] at f₂
    refine ((h.saved.frame f₂ fun r hr => ?_).frame f₃ fun r hr => ?_).frame h₄.frame fun r hr => ?_
    · simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (by omega) (by omega) (by omega)
    · simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (by omega) (by omega) (by omega)
    · simp only [List.mem_singleton] at hr; subst hr
      exact (dS _ _ tR svS).symm
  · have dS48 : (dR s₀).Disjoint ⟨st s₀ + BitVec.ofNat 64 48, 4⟩ := dS _ _ (fun _ h => h) c48
    have back : s₃.mem (dp s₀ + BitVec.ofNat 64 k) = s.mem (dp s₀ + BitVec.ofNat 64 k) := by
      rw [f₃.bytes (R := dR s₀) (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dS48)
          (show L s₀ ≤ 2 ^ 64 by omega) hk,
        f₂.bytes (R := dR s₀) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact dS _ _ (fun _ h => h) (bufR_sub s₀)) (show L s₀ ≤ 2 ^ 64 by omega) hk, m₁]
    by_cases hk₁ : k < H s₀ + 64 * NB s₀
    · rw [h₄.frame.bytes (R := ⟨dp s₀, H s₀ + 64 * NB s₀⟩) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.base_disjoint _ (by omega) (by omega)) (show H s₀ + 64 * NB s₀ ≤ 2 ^ 64 by omega) hk₁,
        back, h.done k hk, ite_pos hk₁, ite_pos hk]
    · have e := h₄.data (k - (H s₀ + 64 * NB s₀)) (by omega)
      rw [Offset.add_add, Offset.add_add, show H s₀ + 64 * NB s₀ + (k - (H s₀ + 64 * NB s₀)) = k by omega,
        back, b3 _ (by omega), bb _ (by omega), h.done k hk, ite_neg hk₁] at e
      rw [e, ite_pos hk]
      simp only [KS, ite_neg (show ¬ k < H s₀ by omega)]
      rw [show (k - H s₀) / 64 = NB s₀ by omega, show (k - H s₀) % 64 = k - (H s₀ + 64 * NB s₀) by omega]
  · rw [m₁] at f₂
    refine ((h.frame.trans (f₂.sub fun r hr => ?_)).trans (f₃.sub fun r hr => ?_)).trans
      (h₄.frame.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨stR s₀, by simp, bufR_sub s₀⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨stR s₀, by simp, c48⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨dR s₀, by simp, tR⟩

theorem part3_ok {s₀ : State} (hp : APre s₀) {s : State} (h : Q2 s₀ s) : WP isa part3 s (Q3 s₀) := by
  have hT64 : T s₀ < 64 := Nat.mod_lt _ (by decide)
  refine WP.ite (decide (T s₀ = 0)) (by rw [eval_zero, h.r26, ofNat_beq_zero (by omega)])
    (fun h0 => WP.block_nil (M := isa) (t_zero_ok h (by simpa using h0)))
    (fun h0 => tail_ok hp h (by simpa using h0))

/-! ## The end -/

theorem preserved_kept : ∀ r ∈ preserved, r ≠ .r24 → r ≠ .r25 → r ≠ .r26 → r ∈ kept := by decide

theorem finish_ok {s₀ : State} (hp : APre s₀) (hle : L s₀ ≤ N s₀) {s : State} (h : Q3 s₀ s) :
    WP isa (.block finish) s (Final s₀) := by
  have hL := L_lt s₀
  have hN := N_lt s₀
  have w : ∀ d, d + 8 ≤ 768 → InRegions s.wr (st s₀ + BitVec.ofNat 64 d) 8 := fun d hd => by
    rw [h.wr]; exact hp.w_st hd
  have r : ∀ d, d + 8 ≤ 768 → InRegions (s.rd ++ s.wr) (st s₀ + BitVec.ofNat 64 d) 8 := fun d hd => by
    rw [h.rd, hp.rd, List.nil_append]; exact w d hd
  refine wp_ld (a := st s₀ + BitVec.ofNat 64 608) (by decide) ⟨by decide, by decide⟩ (by rw [h.r24])
    (r 608 (by decide)) fun s₁ u₁ => ?_
  refine wp_std (a := st s₀ + BitVec.ofNat 64 128) (by decide) ⟨by decide, by decide⟩
    (by rw [u₁.other _ (by decide), h.r24]) (by rw [u₁.wr]; exact w 128 (by decide)) fun s₂ g₂ _ => ?_
  have rr : ∀ d, d + 8 ≤ 768 → InRegions (s₂.rd ++ s₂.wr) (st s₀ + BitVec.ofNat 64 d) 8 := fun d hd => by
    rw [g₂.rd, g₂.wr, u₁.rd, u₁.wr]; exact r d hd
  have r24₂ : s₂.gpr .r24 = st s₀ := by rw [g₂.gpr, u₁.other _ (by decide), h.r24]
  refine wp_ld (a := st s₀ + BitVec.ofNat 64 600) (by decide) ⟨by decide, by decide⟩ (by rw [r24₂])
    (rr 600 (by decide)) fun s₃ u₃ => ?_
  refine wp_mtlr fun s₄ g₄ hl₄ => ?_
  have r24₄ : s₄.gpr .r24 = st s₀ := by rw [g₄.gpr, u₃.other _ (by decide), r24₂]
  have rr₄ : ∀ d, d + 8 ≤ 768 → InRegions (s₄.rd ++ s₄.wr) (st s₀ + BitVec.ofNat 64 d) 8 := fun d hd => by
    rw [g₄.rd, g₄.wr, u₃.rd, u₃.wr]; exact rr d hd
  refine wp_ld (a := st s₀ + BitVec.ofNat 64 584) (by decide) ⟨by decide, by decide⟩ (by rw [r24₄])
    (rr₄ 584 (by decide)) fun s₅ u₅ => ?_
  refine wp_ld (a := st s₀ + BitVec.ofNat 64 592) (by decide) ⟨by decide, by decide⟩
    (by rw [u₅.other _ (by decide), r24₄]) (by rw [u₅.rd, u₅.wr]; exact rr₄ 592 (by decide)) fun s₆ u₆ => ?_
  refine wp_ld (a := st s₀ + BitVec.ofNat 64 576) (by decide) ⟨by decide, by decide⟩
    (by rw [u₆.other _ (by decide), u₅.other _ (by decide), r24₄])
    (by rw [u₆.rd, u₆.wr, u₅.rd, u₅.wr]; exact rr₄ 576 (by decide)) fun s₇ u₇ => ?_
  refine wp_li (by decide) fun s₈ u₈ => WP.block_nil ?_
  -- The memory, from the bytes left stored.
  have hm₂ : s₂.mem = s.mem.writeW (st s₀ + BitVec.ofNat 64 128) (BitVec.ofNat 64 (N s₀ - L s₀)) := by
    rw [g₂.mem, u₁.gpr, u₁.mem, h.saved.left]
  have hm₄ : s₄.mem = s₂.mem := by rw [g₄.mem, u₃.mem]
  have hm : s₈.mem = s.mem.writeW (st s₀ + BitVec.ofNat 64 128) (BitVec.ofNat 64 (N s₀ - L s₀)) := by
    rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, hm₄, hm₂]
  have sv : ∀ d, 576 ≤ d → d + 8 ≤ 616 →
      (s.mem.writeW (st s₀ + BitVec.ofNat 64 128) (BitVec.ofNat 64 (N s₀ - L s₀))).readW
        (st s₀ + BitVec.ofNat 64 d) 64 = s.mem.readW (st s₀ + BitVec.ofNat 64 d) 64 :=
    fun d h₁ h₂ => readW64_ofNat _ _ _ (by omega) (by omega) (by omega)
  have g : ∀ r ∈ kept, s₈.gpr r = s.gpr r := fun r hr => by
    rw [u₈.other r (kept_ne hr), u₇.other r (kept_ne hr), u₆.other r (kept_ne hr), u₅.other r (kept_ne hr),
      g₄.gpr, u₃.other r (kept_ne hr), g₂.gpr, u₁.other r (kept_ne hr)]
  have hfw : Frame [⟨st s₀ + BitVec.ofNat 64 128, 8⟩] s.mem
      (s.mem.writeW (st s₀ + BitVec.ofNat 64 128) (BitVec.ofNat 64 (N s₀ - L s₀))) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have c128 : Region.Sub ⟨st s₀ + BitVec.ofNat 64 128, 8⟩ (stR s₀) := Offset.sub_base _ (by omega)
  have hS : stateAt (s.mem.writeW (st s₀ + BitVec.ofNat 64 128) (BitVec.ofNat 64 (N s₀ - L s₀))) (st s₀) =
      ctr (S0 s₀) (NB s₀ + if T s₀ = 0 then 0 else 1) := by
    rw [stateAt_frame hfw (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.base_disjoint _ (by omega) (by omega)), h.state]
  refine ⟨fun r hr => ?_, ?_, ?_⟩
  · by_cases h24 : r = .r24
    · subst h24
      rw [u₈.other _ (by decide), u₇.gpr, u₆.mem, u₅.mem, hm₄, hm₂, sv 576 (by decide) (by decide)]
      exact h.saved.r24
    by_cases h25 : r = .r25
    · subst h25
      rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, hm₄, hm₂,
        sv 584 (by decide) (by decide)]
      exact h.saved.r25
    by_cases h26 : r = .r26
    · subst h26
      rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, u₅.mem, hm₄, hm₂,
        sv 592 (by decide) (by decide)]
      exact h.saved.r26
    have hk := preserved_kept r hr h24 h25 h26
    rw [g r hk]
    exact h.keep r hk
  · rw [u₈.lr, u₇.lr, u₆.lr, u₅.lr, hl₄, u₃.gpr, hm₂, sv 600 (by decide) (by decide)]
    exact h.saved.lr
  · have hd : ∀ k < L s₀, (s.mem.writeW (st s₀ + BitVec.ofNat 64 128) (BitVec.ofNat 64 (N s₀ - L s₀)))
        (dp s₀ + BitVec.ofNat 64 k) = s.mem (dp s₀ + BitVec.ofNat 64 k) := fun k hk =>
      hfw.bytes (R := dR s₀) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hp.st_d.symm.sub_right c128)) (show L s₀ ≤ 2 ^ 64 by omega) hk
    show keyAt _ _ = _ ∧ _
    rw [hm]
    refine ⟨Proof.ChaCha20.keyAt_of_ctr hS, ?_⟩
    rw [ite_pos hle]
    refine ⟨by rw [u₈.gpr]; decide, apply_data hle fun k hk => ?_, apply_rest hle ?_ hS fun i hi => ?_⟩
    · rw [hd k hk, h.done k hk, ite_pos hk]
    · simp only [leftAt]
      rw [show (st s₀ + 128 : Addr) = st s₀ + BitVec.ofNat 64 128 from rfl, Mem.readW_writeW_self64,
        toNat_ofNat_lt (by omega)]
    · rw [byte_writeW_ofNat _ _ _ (by omega) (by omega) (by omega), h.buf i hi]

theorem apply_eq : apply = .seq (.block check)
    (.ite (.nonzero .d .r10) (.block [.li .r3 0]) (.seq part1 (.seq part2 (.seq part3 (.block finish))))) :=
  rfl

theorem apply_correct {s₀ : State} (hp : APre s₀) : WP isa apply s₀ (Final s₀) := by
  rw [apply_eq]
  refine WP.seq (WP.mono (check_ok hp) fun s h => ?_)
  refine WP.ite (decide (N s₀ < L s₀)) (by
      rw [eval_nonzero_ofNat s .r10 (by cases decide (N s₀ < L s₀) <;> decide) h.r10]
      by_cases hh : N s₀ < L s₀ <;> simp [hh])
    (fun hlt => fail_ok (by simpa using hlt) h) (fun hge => ?_)
  have hle : L s₀ ≤ N s₀ := by simp only [decide_eq_false_iff_not] at hge; omega
  exact WP.seq (WP.mono (part1_ok hp hle h) fun s₁ h₁ => WP.seq (WP.mono (part2_ok hp h₁) fun s₂ h₂ =>
    WP.seq (WP.mono (part3_ok hp h₂) fun s₃ h₃ => finish_ok hp hle h₃)))

end VG.Proof.ChaCha20.PPC64LE.Stream
