import VerifiedGarbage.Proof.Sha1.AArch64.Stream.Common

/-!
# Streaming SHA-1 on AArch64: `update`

Untrusted: everything here is checked by Lean. The same structure as the
x86-64 proof (`VG.Proof.Sha1.X86_64.Stream.Update`); the loop runs while
data is left, so every iteration consumes at least one byte.
-/

namespace VG.Proof.Sha1.AArch64.Stream.Update

open VG VG.AArch64 VG.Impl.Sha1.AArch64.Stream
open VG.Proof.Sha1.AArch64 (contains_offset toNat_ofNat_lt sub_offset)
open VG.Proof.Sha1.AArch64.Stream
open VG.Proof.Sha1.Stream
open VG.Spec.Sha1 (HashValue stateAt blockAt compress parseBlock bytesAt)

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev st : Addr := s₀.gpr .x0
abbrev cnt : Nat := (s₀.gpr .x1).toNat
abbrev dp : Addr := s₀.gpr .x2
abbrev len : Nat := (s₀.gpr .x3).toNat
abbrev scr : Addr := s₀.gpr .x4
abbrev stR : Region := ⟨st s₀, 84⟩
abbrev dR : Region := ⟨dp s₀, len s₀⟩
abbrev scR : Region := ⟨scr s₀, 160⟩
/-- The data. -/
abbrev D : List Byte := bytesAt s₀.mem (dp s₀) (len s₀)

/-- The messages the initial state represents. -/
def R₀ (m : List Byte) : Prop :=
  Spec.Sha1.Repr s₀.mem (st s₀) m ∧ s₀.gpr .x1 = BitVec.ofNat 64 m.length

/-- The caller's registers are saved in the scratch space. -/
def Saved (m : Mem) : Prop :=
  ∀ p ∈ saved, m.readW (scr s₀ + BitVec.ofNat 64 p.2) 64 = s₀.gpr p.1

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [dR s₀]
  wr : s₀.wr = [stR s₀, scR s₀]
  st_scr : (stR s₀).Disjoint (scR s₀)
  d_st : (dR s₀).Disjoint (stR s₀)
  d_scr : (dR s₀).Disjoint (scR s₀)

/-- The frame saving `x30`, below the stack pointer. -/
abbrev stkR (s₀ : State) : Region := ⟨s₀.sp - 16, 16⟩

/-- The frame is below the stack pointer, and disjoint from the buffers. -/
structure Stack (s₀ : State) : Prop where
  sp16 : 16 ≤ s₀.sp.toNat
  st : (stkR s₀).Disjoint (stR s₀)
  d : (stkR s₀).Disjoint (dR s₀)
  scr : (stkR s₀).Disjoint (scR s₀)

theorem pre_of {s₀ : State} (h : Proof.Sha1.updateAArch64.pre s₀) : Pre s₀ ∧ Stack s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨⟨h1, h2, h3, h4, h5⟩, ⟨h6, h7, h8, h9⟩⟩

theorem R₀.length {s₀ : State} {m : List Byte} (h : R₀ s₀ m) : cnt s₀ % 64 = m.length % 64 := by
  rw [cnt, h.2, BitVec.toNat_ofNat]
  omega

theorem len_lt (s₀ : State) : len s₀ < 2 ^ 64 := (s₀.gpr .x3).isLt

theorem D_length (s₀ : State) : (D s₀).length = len s₀ := by simp [bytesAt]

/-! ## Invariants -/

/-- What holds throughout, after consuming `c` bytes of data. -/
structure Common (s₀ : State) (c : Nat) (s : State) : Prop where
  c_le : c ≤ len s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  x19 : s.gpr .x19 = st s₀
  x20 : s.gpr .x20 = scr s₀
  sp : s.sp = s₀.sp
  x21 : s.gpr .x21 = dp s₀ + BitVec.ofNat 64 c
  x22 : s.gpr .x22 = BitVec.ofNat 64 (len s₀ - c)
  frame : Frame [stR s₀, scR s₀] s₀.mem s.mem
  saved : Saved s₀ s.mem

/-- The loop invariant: the state represents the message followed by the
first `c` bytes of data. -/
structure Inv (s₀ : State) (c : Nat) (s : State) : Prop extends Common s₀ c s where
  x23 : s.gpr .x23 = BitVec.ofNat 64 ((cnt s₀ + c) % 64)
  repr : ∀ m, R₀ s₀ m → Spec.Sha1.Repr s.mem (st s₀) (m ++ (D s₀).take c)

/-- A whole block is ready at `x1`, and compressing it absorbs the first `c`
bytes of data. -/
structure Pending (s₀ : State) (c : Nat) (s : State) : Prop extends Common s₀ c s where
  x23 : s.gpr .x23 = 0
  x10 : s.gpr .x10 = 1
  mod : (cnt s₀ + c) % 64 = 0
  src : s.gpr .x1 = st s₀ + 20 ∨ ∃ c₀, s.gpr .x1 = dp s₀ + BitVec.ofNat 64 c₀ ∧ c₀ + 64 ≤ len s₀
  repr : ∀ m, R₀ s₀ m → ∀ mem', stateAt mem' (st s₀) =
      compress (stateAt s.mem (st s₀)) (blockAt s.mem (s.gpr .x1)) →
    Spec.Sha1.Repr mem' (st s₀) (m ++ (D s₀).take c)

/-- All the data is absorbed, and nothing is pending. -/
def Done (s₀ : State) (s : State) : Prop := Inv s₀ (len s₀) s ∧ s.gpr .x10 = 0

theorem Common.of_gpr {s₀ : State} {c : Nat} {s s' : State} (h : Common s₀ c s)
    (hg : ∀ r ∈ [Reg.x19, .x20, .x21, .x22], s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) :
    Common s₀ c s' where
  c_le := h.c_le
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  x19 := by rw [hg _ (by simp)]; exact h.x19
  x20 := by rw [hg _ (by simp)]; exact h.x20
  sp := hsp.trans h.sp
  x21 := by rw [hg _ (by simp)]; exact h.x21
  x22 := by rw [hg _ (by simp)]; exact h.x22
  frame := by rw [hm]; exact h.frame
  saved := by rw [hm]; exact h.saved

theorem Inv.of_gpr {s₀ : State} {c : Nat} {s s' : State} (h : Inv s₀ c s)
    (hg : ∀ r ∈ [Reg.x19, .x20, .x21, .x22, .x23], s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) :
    Inv s₀ c s' :=
  { h.toCommon.of_gpr (fun r hr => hg r (by simp at hr ⊢; tauto)) hm hrd hwr hsp with
    x23 := by rw [hg _ (by simp)]; exact h.x23
    repr := by rw [hm]; exact h.repr }

/-- Where the caller's registers are saved. -/
theorem saved_sub {s₀ : State} {p : Reg × Nat} (hp : p ∈ saved) :
    Region.Sub ⟨scr s₀ + BitVec.ofNat 64 p.2, 8⟩ (scR s₀) := by
  simp only [Impl.Sha1.AArch64.Stream.saved, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> exact sub_offset (by omega) (by omega)

/-! ## Consuming data -/

theorem D_getD (s₀ : State) {i : Nat} (hi : i < len s₀) :
    (D s₀).getD i 0 = s₀.mem (dp s₀ + BitVec.ofNat 64 i) := by
  simp [bytesAt, List.getD_eq_getElem?_getD, hi]

/-- The data is unchanged. -/
theorem Common.data {s₀ : State} (hp : Pre s₀) {c : Nat} {s : State} (h : Common s₀ c s) {i : Nat}
    (hi : i < len s₀) : s.mem (dp s₀ + BitVec.ofNat 64 i) = (D s₀).getD i 0 := by
  rw [D_getD s₀ hi]
  exact frame_bytes h.frame (R := dR s₀) (by simpa using ⟨hp.d_st, hp.d_scr⟩) (len_lt s₀).le hi

theorem length_mid (s₀ : State) {m : List Byte} (hm : R₀ s₀ m) {c : Nat} (hc : c ≤ len s₀) :
    (m ++ (D s₀).take c).length % 64 = (cnt s₀ + c) % 64 := by
  have := hm.length
  simp only [List.length_append, List.length_take, D_length, Nat.min_eq_left hc]
  omega

theorem take_add_data (s₀ : State) (c t : Nat) (m : List Byte) :
    m ++ (D s₀).take c ++ ((D s₀).drop c).take t = m ++ (D s₀).take (c + t) := by
  rw [List.take_add, List.append_assoc]

/-! ## Compressing a pending block -/

theorem Pending.compress_ok {s₀ : State} (hp : Pre s₀) {c : Nat} {s : State} (h : Pending s₀ c s) :
    WP isa compressAt s (Inv s₀ c) := by
  have e20 : Region.Sub ⟨st s₀, 20⟩ (stR s₀) := Region.sub_prefix (by omega)
  have e112 : Region.Sub ⟨scr s₀, 112⟩ (scR s₀) := Region.sub_prefix (by omega)
  have eSrc : Region.Sub ⟨s.gpr .x1, 64⟩ (stR s₀) ∨ Region.Sub ⟨s.gpr .x1, 64⟩ (dR s₀) := by
    rcases h.src with h' | ⟨c₀, h', hc₀⟩
    · exact .inl (h' ▸ sub_offset (off := 20) (by omega) (by omega))
    · exact .inr (h' ▸ sub_offset (by omega) (by have := len_lt s₀; omega))
  refine compressAt_ok h.x19 h.x20 rfl ((hp.st_scr.sub_left e20).sub_right e112) ?_ ?_ ?_ ?_ ?_
  · rcases h.src with h' | ⟨c₀, h', hc₀⟩
    · rw [h']; intro a h₁ h₂; simp only [Region.Contains] at h₁ h₂; bv_omega
    · exact (hp.d_st.sub_left (h' ▸ sub_offset (by omega) (by have := len_lt s₀; omega))).sub_right e20
  · rcases eSrc with e | e
    · exact (hp.st_scr.sub_left e).sub_right e112
    · exact (hp.d_scr.sub_left e).sub_right e112
  · rw [h.rd, h.wr, hp.rd, hp.wr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rcases h.src with h' | ⟨c₀, h', hc₀⟩
      · exact ⟨stR s₀, by simp, 20, by rw [h']; rfl, by simp⟩
      · exact ⟨dR s₀, by simp, c₀, h', hc₀⟩
    · exact ⟨stR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨scR s₀, by simp, 0, by simp, by simp⟩
  · rw [h.wr, hp.wr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨stR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨scR s₀, by simp, 0, by simp, by simp⟩
  · intro s' hrd hwr hcs hsp hf hstate
    have cs : ∀ r, r ∈ preserved → r ≠ .x30 → s'.gpr r = s.gpr r := hcs
    refine ⟨⟨h.c_le, hrd.trans h.rd, hwr.trans h.wr, by rw [cs _ (by decide) (by decide)]; exact h.x19,
      by rw [cs _ (by decide) (by decide)]; exact h.x20, hsp.trans h.sp,
      by rw [cs _ (by decide) (by decide)]; exact h.x21,
      by rw [cs _ (by decide) (by decide)]; exact h.x22,
      h.frame.trans (hf.sub ?_), fun p hp' => ?_⟩, ?_, fun m hm => h.repr m hm _ hstate⟩
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨stR s₀, by simp, e20⟩
      · exact ⟨scR s₀, by simp, e112⟩
    · rw [← h.saved p hp']
      refine hf.readW (r := ⟨scr s₀ + BitVec.ofNat 64 p.2, 8⟩) (Region.contains_self _ _) ?_ (by decide)
      intro r' hr'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl
      · exact (hp.st_scr.symm.sub_left (saved_sub hp')).sub_right e20
      · simp only [Impl.Sha1.AArch64.Stream.saved, List.mem_cons, List.not_mem_nil, or_false] at hp'
        rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl <;>
        · intro a h₁ h₂; simp only [Region.Contains] at h₁ h₂; bv_omega
    · rw [cs _ (by decide) (by decide), h.x23, h.mod]; rfl

/-! ## A whole block straight from the data -/

theorem direct_ok {s₀ : State} (hp : Pre s₀) {c : Nat} {s : State} (hI : Inv s₀ c s)
    (hr : (cnt s₀ + c) % 64 = 0) (hl : 64 ≤ len s₀ - c) :
    WP isa (.block direct) s (Pending s₀ (c + 64)) := by
  have hlen := len_lt s₀
  unfold direct
  refine wp_mov fun s₁ u₁ => wp_addImm (by decide) fun s₂ u₂ => wp_subImm (by decide) fun s₃ u₃ =>
    wp_movz fun s₄ u₄ => WP.block_nil ?_
  have g : ∀ r, r ≠ .x1 → r ≠ .x21 → r ≠ .x22 → r ≠ .x10 → s₄.gpr r = s.gpr r := fun r h1 h2 h3 h4 => by
    rw [u₄.other r h4, u₃.other r h3, u₂.other r h2, u₁.other r h1]
  have m₄ : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have h1 : s₄.gpr .x1 = dp s₀ + BitVec.ofNat 64 c := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hI.x21]
  refine ⟨⟨by omega, by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd, hI.rd], by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr, hI.wr],
    by rw [g _ (by decide) (by decide) (by decide) (by decide), hI.x19],
    by rw [g _ (by decide) (by decide) (by decide) (by decide), hI.x20],
    by rw [u₄.sp, u₃.sp, u₂.sp, u₁.sp, hI.sp], ?_, ?_, by rw [m₄]; exact hI.frame,
    by rw [m₄]; exact hI.saved⟩, ?_, by rw [u₄.gpr]; rfl, by omega, .inr ⟨c, h1, by omega⟩, ?_⟩
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), hI.x21,
      BitVec.add_assoc, ← BitVec.ofNat_add]
  · rw [u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), hI.x22,
      sub_ofNat (by omega), Nat.sub_sub]
  · rw [g _ (by decide) (by decide) (by decide) (by decide), hI.x23, hr]; rfl
  · intro m hm mem' hs
    have hmod := length_mid s₀ hm (c := c) (by omega)
    rw [← take_add_data]
    refine repr_append_block (hI.repr m hm)
      (by rw [hmod, hr, List.length_take, List.length_drop, D_length]; omega) ?_
    rw [hs, m₄, h1]
    refine congrArg (compress _) ?_
    rw [show (m ++ List.take c (D s₀)).drop (64 * ((m ++ List.take c (D s₀)).length / 64)) = [] by
      rw [List.drop_eq_nil_iff]; omega, List.nil_append]
    apply parseBlock_congr
    intro k hk
    rw [show dp s₀ + BitVec.ofNat 64 c + BitVec.ofNat 64 k = dp s₀ + BitVec.ofNat 64 (c + k) by
      simp only [BitVec.ofNat_add]; rw [BitVec.add_assoc], hI.data hp (by omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_drop, hk]

/-! ## Buffering data -/

section
variable (s₀ : State) (c : Nat)
/-- Bytes in the buffer before this iteration. -/
abbrev rr : Nat := (cnt s₀ + c) % 64
/-- Bytes copied into the buffer in this iteration. -/
abbrev tt : Nat := min (64 - rr s₀ c) (len s₀ - c)
/-- Where they go. -/
abbrev q : Addr := st s₀ + 20 + BitVec.ofNat 64 (rr s₀ c)
/-- The data copied. -/
abbrev xs : List Byte := ((D s₀).drop c).take (tt s₀ c)
end

theorem rr_lt (s₀ : State) (c : Nat) : rr s₀ c < 64 := Nat.mod_lt _ (by omega)
theorem tt_le (s₀ : State) (c : Nat) : tt s₀ c ≤ len s₀ - c := Nat.min_le_right _ _
theorem tt_le' (s₀ : State) (c : Nat) : tt s₀ c ≤ 64 - rr s₀ c := Nat.min_le_left _ _
theorem rr_eq (s₀ : State) (c : Nat) : rr s₀ c = (cnt s₀ + c) % 64 := rfl
theorem tt_eq (s₀ : State) (c : Nat) : tt s₀ c = min (64 - rr s₀ c) (len s₀ - c) := rfl

theorem q_eq (s₀ : State) (c : Nat) : q s₀ c = st s₀ + BitVec.ofNat 64 (20 + rr s₀ c) := by
  simp only [q, BitVec.ofNat_add]; rw [BitVec.add_assoc]; rfl

theorem xs_length (s₀ : State) (c : Nat) : (xs s₀ c).length = tt s₀ c := by
  have := tt_le s₀ c
  simp only [xs, List.length_take, List.length_drop, D_length]; omega

/-- The state while copying: `j` bytes copied, into memory otherwise as in `mI`. -/
structure Copy (s₀ : State) (c : Nat) (mI : Mem) (j : Nat) (s : State) : Prop where
  j_le : j ≤ tt s₀ c
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  x19 : s.gpr .x19 = st s₀
  x20 : s.gpr .x20 = scr s₀
  sp : s.sp = s₀.sp
  x21 : s.gpr .x21 = dp s₀ + BitVec.ofNat 64 (c + j)
  x22 : s.gpr .x22 = BitVec.ofNat 64 (len s₀ - c - tt s₀ c)
  x23 : s.gpr .x23 = BitVec.ofNat 64 (rr s₀ c + j)
  x11 : s.gpr .x11 = BitVec.ofNat 64 (tt s₀ c - j)
  x10 : s.gpr .x10 = 0
  mem : s.mem = writeBytes mI (q s₀ c) ((xs s₀ c).take j)

theorem write_frame (s₀ : State) (c : Nat) (mI : Mem) (j : Nat) (hj : j ≤ tt s₀ c) :
    Frame [stR s₀] mI (writeBytes mI (q s₀ c) ((xs s₀ c).take j)) := by
  have := tt_le' s₀ c; have := rr_lt s₀ c
  refine writeBytes_frame _ _ _ ?_
  rw [q_eq]
  exact contains_offset (by simp only [List.length_take]; omega) (by omega)

/-- The copy loop's body. -/
def copyBody : List Instr :=
  [.ldrb .x9 .x21 0, .add .x .x12 .x19 .x23, .strb .x9 .x12 20, .addImm .x .x21 .x21 1,
    .addImm .x .x23 .x23 1, .subImm .x .x11 .x11 1]

theorem copy_step {s₀ : State} (hp : Pre s₀) {c : Nat} {sI : State} (hI : Inv s₀ c sI) {j : Nat}
    (hj : j < tt s₀ c) {s : State} (h : Copy s₀ c sI.mem j s) :
    WP isa (.block copyBody) s fun s' =>
      Copy s₀ c sI.mem (j + 1) s' ∧ s'.gpr .x11 = BitVec.ofNat 64 (tt s₀ c - (j + 1)) := by
  have hlen := len_lt s₀
  have hc := hI.c_le
  have hr := rr_lt s₀ c
  have ht := tt_le s₀ c; have ht' := tt_le' s₀ c
  -- The byte read.
  have hin : InRegions (s.rd ++ s.wr) (dp s₀ + BitVec.ofNat 64 (c + j)) 1 :=
    ⟨dR s₀, by simp [h.rd, hp.rd], contains_offset (by omega) (by omega)⟩
  have hbyte : s.mem (dp s₀ + BitVec.ofNat 64 (c + j)) = (D s₀).getD (c + j) 0 := by
    rw [h.mem, ← hI.data hp (by omega)]
    exact frame_bytes (write_frame s₀ c sI.mem j h.j_le) (R := dR s₀) (by simpa using hp.d_st)
      (by show len s₀ ≤ 2 ^ 64; omega) (by show c + j < len s₀; omega)
  -- The byte written.
  have hout : InRegions s.wr (q s₀ c + BitVec.ofNat 64 j) 1 :=
    ⟨stR s₀, by simp [h.wr, hp.wr], by
      rw [q_eq, BitVec.add_assoc, ← BitVec.ofNat_add]; exact contains_offset (by omega) (by omega)⟩
  have hxs := xs_length s₀ c
  unfold copyBody
  refine wp_ldrb (a := dp s₀ + BitVec.ofNat 64 (c + j)) (by omega) (by rw [h.x21]; simp) hin
    fun s₁ u₁ => ?_
  refine wp_add fun s₂ u₂ => wp_strb (a := q s₀ c + BitVec.ofNat 64 j) (by omega) ?_
    (by rw [u₂.wr, u₁.wr]; exact hout) fun s₃ g₃ => ?_
  · rw [u₂.gpr, u₁.other _ (by decide), u₁.other _ (by decide), h.x19, h.x23, q]
    simp only [BitVec.ofNat_add, show BitVec.ofNat 64 20 = (20 : BitVec 64) from rfl]
    ac_rfl
  refine wp_addImm (by decide) fun s₄ u₄ => wp_addImm (by decide) fun s₅ u₅ =>
    wp_subImm (by decide) fun s₆ u₆ => WP.block_nil ?_
  have g : ∀ r, r ≠ .x9 → r ≠ .x12 → r ≠ .x21 → r ≠ .x23 → r ≠ .x11 → s₆.gpr r = s.gpr r :=
    fun r h1 h2 h3 h4 h5 => by
      rw [u₆.other r h5, u₅.other r h4, u₄.other r h3, g₃.gpr, u₂.other r h2, u₁.other r h1]
  have hx11 : s₆.gpr .x11 = BitVec.ofNat 64 (tt s₀ c - (j + 1)) := by
    rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), g₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), h.x11, sub_ofNat (by omega), Nat.sub_sub]
  refine ⟨⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hx11, ?_, ?_⟩, hx11⟩
  · rw [u₆.rd, u₅.rd, u₄.rd, g₃.rd, u₂.rd, u₁.rd, h.rd]
  · rw [u₆.wr, u₅.wr, u₄.wr, g₃.wr, u₂.wr, u₁.wr, h.wr]
  · rw [g .x19 (by decide) (by decide) (by decide) (by decide) (by decide), h.x19]
  · rw [g .x20 (by decide) (by decide) (by decide) (by decide) (by decide), h.x20]
  · rw [u₆.sp, u₅.sp, u₄.sp, g₃.sp, u₂.sp, u₁.sp, h.sp]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, g₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), h.x21, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_assoc]
  · rw [g .x22 (by decide) (by decide) (by decide) (by decide) (by decide), h.x22]
  · rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), g₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), h.x23, ← BitVec.ofNat_add, Nat.add_assoc]
  · rw [g .x10 (by decide) (by decide) (by decide) (by decide) (by decide), h.x10]
  · have hj' : j < (xs s₀ c).length := by omega
    rw [u₆.mem, u₅.mem, u₄.mem, g₃.mem, u₂.mem, u₁.mem, u₂.other _ (by decide), u₁.gpr, hbyte, h.mem,
      List.take_add_one, List.getElem?_eq_getElem hj', Option.toList_some,
      writeBytes_snoc _ _ _ _ (by simp only [List.length_take]; omega)]
    have hl : (List.take j (xs s₀ c)).length = j := by rw [List.length_take, Nat.min_eq_left hj'.le]
    rw [hl]
    have e : ((List.getD (D s₀) (c + j) 0).setWidth 64).setWidth 8 = List.getD (D s₀) (c + j) 0 := by
      ext i hi; simp
    rw [e]
    congr 1
    simp only [xs, List.getElem_take, List.getElem_drop, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (show c + j < (D s₀).length by rw [D_length]; omega), Option.getD_some]

theorem copy_loop_ok {s₀ : State} (hp : Pre s₀) {c : Nat} {sI : State} (hI : Inv s₀ c sI) {s : State}
    (h : Copy s₀ c sI.mem 0 s) (ht : 0 < tt s₀ c) :
    WP isa (.loop (.block copyBody) (.nonzero .x .x11)) s (Copy s₀ c sI.mem (tt s₀ c)) := by
  refine WP.loop (M := isa) (fun n s => ∃ j, n = tt s₀ c - j ∧ j < tt s₀ c ∧ Copy s₀ c sI.mem j s)
    ?_ (tt s₀ c) s ⟨0, rfl, ht, h⟩
  rintro n s ⟨j, rfl, hj, hc⟩
  refine WP.mono (copy_step hp hI hj hc) fun s' ⟨hc', h11⟩ => ?_
  have hz : isa.eval (.nonzero .x .x11) s' = some (decide (tt s₀ c - (j + 1) ≠ 0)) := by
    show VG.AArch64.eval (.nonzero .x .x11) s' = _
    rw [eval_nonzero, h11, bne, ofNat_beq_zero (by have := tt_le' s₀ c; omega)]
    simp
  by_cases hl : tt s₀ c - (j + 1) = 0
  · refine .inl ⟨by rw [hz]; simp [hl], ?_⟩
    rwa [show j + 1 = tt s₀ c by omega] at hc'
  · exact .inr ⟨by rw [hz]; simp [hl], _, by omega, j + 1, rfl, by omega, hc'⟩

/-- The memory after copying `tt` bytes. -/
theorem copied_facts {s₀ : State} (hp : Pre s₀) {c : Nat} {sI : State} (hI : Inv s₀ c sI) :
    let mem := writeBytes sI.mem (q s₀ c) (xs s₀ c)
    Frame [stR s₀, scR s₀] s₀.mem mem ∧ Saved s₀ mem ∧ stateAt mem (st s₀) = stateAt sI.mem (st s₀) ∧
      bytesAt mem (st s₀ + 20) (rr s₀ c + tt s₀ c) = bytesAt sI.mem (st s₀ + 20) (rr s₀ c) ++ xs s₀ c := by
  intro mem
  have hr := rr_lt s₀ c; have ht' := tt_le' s₀ c
  have hxs := xs_length s₀ c
  have hf : Frame [stR s₀] sI.mem mem := by
    have := write_frame s₀ c sI.mem (tt s₀ c) le_rfl
    rwa [List.take_of_length_le (by omega)] at this
  refine ⟨hI.frame.trans (hf.mono (by simp)), fun p hp' => ?_, ?_, ?_⟩
  · rw [← hI.saved p hp']
    refine hf.readW (r := ⟨scr s₀ + BitVec.ofNat 64 p.2, 8⟩) (Region.contains_self _ _) ?_ (by decide)
    intro r' hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    subst hr'
    exact hp.st_scr.symm.sub_left (saved_sub hp')
  · apply stateAt_congr
    intro i hi
    simp only [mem, q_eq]
    exact writeBytes_before _ _ _ (by omega) (by omega)
  · rw [← hxs]
    exact bytesAt_writeBytes _ _ _ _ (by omega)

/-- A full buffer: compress it. -/
theorem fill_pending {s₀ : State} (hp : Pre s₀) {c : Nat} {sI : State} (hI : Inv s₀ c sI) {s : State}
    (h : Copy s₀ c sI.mem (tt s₀ c) s) (hfull : rr s₀ c + tt s₀ c = 64) :
    WP isa (.block [.addImm .x .x1 .x19 20, .movz .x .x23 0 0, .movz .x .x10 1 0]) s
      (Pending s₀ (c + tt s₀ c)) := by
  have hr := rr_lt s₀ c; have ht := tt_le s₀ c; have ht' := tt_le' s₀ c
  have hrr := rr_eq s₀ c; have htt := tt_eq s₀ c
  have hxs := xs_length s₀ c
  have hc := hI.c_le
  obtain ⟨hfr, hsv, hst, hby⟩ := copied_facts hp hI
  have hmem : s.mem = writeBytes sI.mem (q s₀ c) (xs s₀ c) := by
    rw [h.mem, List.take_of_length_le (by omega)]
  refine wp_addImm (by decide) fun s₁ u₁ => wp_movz fun s₂ u₂ => wp_movz fun s₃ u₃ => WP.block_nil ?_
  have g : ∀ r, r ≠ .x1 → r ≠ .x23 → r ≠ .x10 → s₃.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [u₃.other r h3, u₂.other r h2, u₁.other r h1]
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have hx1 : s₃.gpr .x1 = st s₀ + 20 := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h.x19]; rfl
  refine ⟨⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by rw [m₃, hmem]; exact hfr, by rw [m₃, hmem]; exact hsv⟩,
    by rw [u₃.other _ (by decide), u₂.gpr]; rfl, by rw [u₃.gpr]; rfl, by omega, .inl hx1, ?_⟩
  · rw [u₃.rd, u₂.rd, u₁.rd, h.rd]
  · rw [u₃.wr, u₂.wr, u₁.wr, h.wr]
  · rw [g .x19 (by decide) (by decide) (by decide), h.x19]
  · rw [g .x20 (by decide) (by decide) (by decide), h.x20]
  · rw [u₃.sp, u₂.sp, u₁.sp, h.sp]
  · rw [g .x21 (by decide) (by decide) (by decide), h.x21]
  · rw [g .x22 (by decide) (by decide) (by decide), h.x22, Nat.sub_sub]
  · intro m hm mem' hs
    rw [← take_add_data]
    have hmod := length_mid s₀ hm hc
    refine repr_append_block (hI.repr m hm) (by rw [hmod, hxs]; exact hfull) ?_
    rw [hs, m₃, hmem, hst, hx1]
    refine congrArg (compress _) (parseBlock_congr fun k hk => ?_)
    have hb := (hI.repr m hm).2
    rw [hmod] at hb
    rw [hb, show rr s₀ c + tt s₀ c = 64 from hfull] at hby
    exact bytesAt_getD hby hk

/-- All the data fits in the buffer. -/
theorem fill_done {s₀ : State} (hp : Pre s₀) {c : Nat} {sI : State} (hI : Inv s₀ c sI) {s : State}
    (h : Copy s₀ c sI.mem (tt s₀ c) s) (hnf : rr s₀ c + tt s₀ c ≠ 64) : Done s₀ s := by
  have hr := rr_lt s₀ c; have ht := tt_le s₀ c; have ht' := tt_le' s₀ c
  have hrr := rr_eq s₀ c; have htt := tt_eq s₀ c
  have hxs := xs_length s₀ c
  have hc := hI.c_le
  have htl : tt s₀ c = len s₀ - c := by omega
  obtain ⟨hfr, hsv, hst, hby⟩ := copied_facts hp hI
  have hmem : s.mem = writeBytes sI.mem (q s₀ c) (xs s₀ c) := by
    rw [h.mem, List.take_of_length_le (by omega)]
  refine ⟨⟨⟨le_rfl, h.rd, h.wr, h.x19, h.x20, h.sp, ?_, ?_, by rw [hmem]; exact hfr,
    by rw [hmem]; exact hsv⟩, ?_, fun m hm => ?_⟩, h.x10⟩
  · rw [h.x21]; congr 2; omega
  · rw [h.x22]; congr 1; omega
  · rw [h.x23]; congr 1; omega
  · have hmod := length_mid s₀ hm hc
    rw [show len s₀ = c + tt s₀ c by omega, ← take_add_data]
    refine repr_append_buf (hI.repr m hm) (by rw [hmod, hxs]; omega) (by rw [hmem, hst]) ?_
    rw [hmod, hxs, hmem, hby]
    have hb := (hI.repr m hm).2
    rw [hmod] at hb
    rw [hb]

theorem fill_eq : fill =
    .seq (.block [.movz .x .x11 64 0, .sub .x .x11 .x11 .x23, .lsr .x .x9 .x22 6])
    (.seq (.ite (.zero .x .x9)
        (.seq (.block [.add .x .x9 .x22 .x23, .lsr .x .x9 .x9 6])
          (.ite (.zero .x .x9) (.block [mov .x11 .x22]) (.block [])))
        (.block []))
    (.seq (.block [.sub .x .x22 .x22 .x11])
    (.seq (.loop (.block copyBody) (.nonzero .x .x11))
    (.seq (.block [.subImm .x .x9 .x23 64])
      (.ite (.zero .x .x9) (.block [.addImm .x .x1 .x19 20, .movz .x .x23 0 0, .movz .x .x10 1 0])
        (.block [])))))) := rfl

theorem fill_ok {s₀ : State} (hp : Pre s₀) {c : Nat} {s : State} (hI : Inv s₀ c s) (hcl : c < len s₀)
    (h10 : s.gpr .x10 = 0) :
    WP isa fill s fun s' => (∃ c', c < c' ∧ Pending s₀ c' s') ∨ Done s₀ s' := by
  have hr := rr_lt s₀ c; have ht := tt_le s₀ c; have ht' := tt_le' s₀ c
  have hrr := rr_eq s₀ c; have htt := tt_eq s₀ c
  have ne : ∀ r ∈ [Reg.x19, .x20, .x21, .x22, .x23], r ≠ .x9 ∧ r ≠ .x11 := by decide
  have hc := hI.c_le; have hlen := len_lt s₀
  rw [fill_eq]
  -- `x11 := 64 - r; x9 := len >> 6`
  refine WP.seq (wp_movz fun s₁ u₁ => wp_sub fun s₂ u₂ => wp_lsr (by decide) fun s₃ u₃ => WP.block_nil ?_)
  have e₃ : ∀ r, r ≠ .x9 → r ≠ .x11 → s₃.gpr r = s.gpr r := fun r h h' => by
    rw [u₃.other r h, u₂.other r h', u₁.other r h']
  have hI₃ : Inv s₀ c s₃ := hI.of_gpr (fun r hr => e₃ r (ne r hr).1 (ne r hr).2)
    (by rw [u₃.mem, u₂.mem, u₁.mem]) (by rw [u₃.rd, u₂.rd, u₁.rd]) (by rw [u₃.wr, u₂.wr, u₁.wr])
    (by rw [u₃.sp, u₂.sp, u₁.sp])
  have h11₃ : s₃.gpr .x11 = BitVec.ofNat 64 (64 - rr s₀ c) := by
    rw [u₃.other _ (by decide), u₂.gpr, u₁.gpr, u₁.other _ (by decide), hI.x23,
      show BitVec.setWidth 64 (64 : BitVec 16) = BitVec.ofNat 64 64 from rfl, sub_ofNat (by omega)]
  have h9₃ : s₃.gpr .x9 = BitVec.ofNat 64 ((len s₀ - c) / 64) := by
    rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), hI.x22, ofNat_shr6 (by omega)]
  -- `x11 := min(x11, len)`
  refine WP.seq (WP.mono (Q := fun (s₄ : State) => Inv s₀ c s₄ ∧ s₄.gpr .x11 = BitVec.ofNat 64 (tt s₀ c) ∧
    s₄.gpr .x10 = 0 ∧ s₄.mem = s.mem) ?_ fun s₄ ⟨hI₄, h11₄, h10₄, hm₄⟩ => ?_)
  · have hm₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
    have h10₃ : s₃.gpr .x10 = 0 := by rw [e₃ _ (by decide) (by decide), h10]
    refine WP.ite (decide ((len s₀ - c) / 64 = 0))
      (by show VG.AArch64.eval (.zero .x .x9) s₃ = _; rw [eval_zero, h9₃, ofNat_beq_zero (by omega)]) (fun hb => ?_) (fun hb => ?_)
    · simp only [decide_eq_true_eq] at hb
      refine WP.seq (wp_add fun s₅ u₅ => wp_lsr (by decide) fun s₆ u₆ => WP.block_nil ?_)
      have e₆ : ∀ r, r ≠ .x9 → s₆.gpr r = s₃.gpr r := fun r h => by rw [u₆.other r h, u₅.other r h]
      have hI₆ : Inv s₀ c s₆ := hI₃.of_gpr (fun r hr => e₆ r (ne r hr).1) (by rw [u₆.mem, u₅.mem]) (by rw [u₆.rd, u₅.rd]) (by rw [u₆.wr, u₅.wr])
        (by rw [u₆.sp, u₅.sp])
      have h9₆ : s₆.gpr .x9 = BitVec.ofNat 64 ((len s₀ - c + rr s₀ c) / 64) := by
        rw [u₆.gpr, u₅.gpr, hI₃.x22, hI₃.x23, ← BitVec.ofNat_add, ofNat_shr6 (by omega)]
      refine WP.ite (decide ((len s₀ - c + rr s₀ c) / 64 = 0))
        (by show VG.AArch64.eval (.zero .x .x9) s₆ = _; rw [eval_zero, h9₆, ofNat_beq_zero (by omega)]) (fun hb' => ?_) (fun hb' => ?_)
      · simp only [decide_eq_true_eq] at hb'
        refine wp_mov fun s₇ u₇ => WP.block_nil ⟨hI₆.of_gpr (fun r hr => u₇.other r (ne r hr).2)
          u₇.mem u₇.rd u₇.wr u₇.sp,
          ?_, by rw [u₇.other _ (by decide), e₆ _ (by decide), h10₃], by rw [u₇.mem, u₆.mem, u₅.mem, hm₃]⟩
        rw [u₇.gpr, hI₆.x22]; congr 1; omega
      · simp only [decide_eq_false_iff_not] at hb'
        refine WP.block_nil ⟨hI₆, ?_, by rw [e₆ _ (by decide), h10₃], by rw [u₆.mem, u₅.mem, hm₃]⟩
        rw [e₆ _ (by decide), h11₃]; congr 1; omega
    · simp only [decide_eq_false_iff_not] at hb
      refine WP.block_nil ⟨hI₃, ?_, h10₃, hm₃⟩
      rw [h11₃]; congr 1; omega
  -- `x22 -= x11`
  refine WP.seq (wp_sub fun s₅ u₅ => WP.block_nil ?_)
  have hC₀ : Copy s₀ c s.mem 0 s₅ := by
    have e : ∀ r, r ≠ .x22 → s₅.gpr r = s₄.gpr r := fun r h => u₅.other r h
    refine ⟨Nat.zero_le _, by rw [u₅.rd, hI₄.rd], by rw [u₅.wr, hI₄.wr],
      by rw [e _ (by decide), hI₄.x19], by rw [e _ (by decide), hI₄.x20], by rw [u₅.sp, hI₄.sp],
      by rw [e _ (by decide), hI₄.x21, Nat.add_zero], ?_, by rw [e _ (by decide), hI₄.x23, Nat.add_zero],
      by rw [e _ (by decide), h11₄, Nat.sub_zero], by rw [e _ (by decide), h10₄], ?_⟩
    · rw [u₅.gpr, hI₄.x22, h11₄, sub_ofNat (by omega), Nat.sub_sub]
    · rw [u₅.mem, hm₄, List.take_zero, writeBytes_nil]
  -- Copy the bytes.
  refine WP.seq (WP.mono (copy_loop_ok hp hI hC₀ (by omega)) fun s₆ hC => ?_)
  -- Is the buffer full?
  refine WP.seq (wp_subImm (by decide) fun s₇ u₇ => WP.block_nil ?_)
  have hC₇ : Copy s₀ c s.mem (tt s₀ c) s₇ :=
    ⟨hC.j_le, by rw [u₇.rd, hC.rd], by rw [u₇.wr, hC.wr], by rw [u₇.other _ (by decide), hC.x19],
      by rw [u₇.other _ (by decide), hC.x20], by rw [u₇.sp, hC.sp], by rw [u₇.other _ (by decide), hC.x21],
      by rw [u₇.other _ (by decide), hC.x22], by rw [u₇.other _ (by decide), hC.x23],
      by rw [u₇.other _ (by decide), hC.x11], by rw [u₇.other _ (by decide), hC.x10],
      by rw [u₇.mem, hC.mem]⟩
  have hz : eval (.zero .x .x9) s₇ = some (decide (rr s₀ c + tt s₀ c = 64)) := by
    rw [eval_zero, u₇.gpr, hC.x23, sub_beq (by omega) (by omega)]
  refine WP.ite (decide (rr s₀ c + tt s₀ c = 64)) hz (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    exact WP.mono (fill_pending hp hI hC₇ hb) fun s' h => .inl ⟨c + tt s₀ c, by omega, h⟩
  · simp only [decide_eq_false_iff_not] at hb
    exact WP.block_nil (.inr (fill_done hp hI hC₇ hb))

/-! ## One iteration -/

theorem body_eq : updateBody =
    .seq (.block [.movz .x .x10 0 0])
    (.seq (.ite (.zero .x .x23)
        (.seq (.block [.lsr .x .x9 .x22 6]) (.ite (.zero .x .x9) fill (.block direct)))
        fill)
      (.ite (.zero .x .x10) (.block []) compressAt)) := rfl

theorem body_ok {s₀ : State} (hp : Pre s₀) {c : Nat} {s : State} (hI : Inv s₀ c s) (hcl : c < len s₀) :
    WP isa updateBody s fun s' => ∃ c', c < c' ∧ Inv s₀ c' s' := by
  have hlen := len_lt s₀; have hc := hI.c_le; have hr := rr_lt s₀ c
  have ne : ∀ r ∈ [Reg.x19, .x20, .x21, .x22, .x23], r ≠ .x10 ∧ r ≠ .x9 := by decide
  rw [body_eq]
  refine WP.seq (wp_movz fun s₁ u₁ => WP.block_nil ?_)
  have hI₁ : Inv s₀ c s₁ := hI.of_gpr (fun r hr => u₁.other r (ne r hr).1) u₁.mem u₁.rd u₁.wr u₁.sp
  have h10₁ : s₁.gpr .x10 = 0 := by rw [u₁.gpr]; rfl
  refine WP.seq (WP.mono (Q := fun s' => (∃ c', c < c' ∧ Pending s₀ c' s') ∨ Done s₀ s') ?_
    fun s' h => ?_)
  · refine WP.ite (decide (rr s₀ c = 0))
      (by show VG.AArch64.eval (.zero .x .x23) s₁ = _; rw [eval_zero, hI₁.x23, ofNat_beq_zero (by omega)])
      (fun hb => ?_) (fun _ => fill_ok hp hI₁ hcl h10₁)
    simp only [decide_eq_true_eq] at hb
    refine WP.seq (wp_lsr (by decide) fun s₂ u₂ => WP.block_nil ?_)
    have hI₂ : Inv s₀ c s₂ := hI₁.of_gpr (fun r hr => u₂.other r (ne r hr).2) u₂.mem u₂.rd u₂.wr u₂.sp
    have h10₂ : s₂.gpr .x10 = 0 := by rw [u₂.other _ (by decide), h10₁]
    refine WP.ite (decide ((len s₀ - c) / 64 = 0))
      (by show VG.AArch64.eval (.zero .x .x9) s₂ = _
          rw [eval_zero, u₂.gpr, hI₁.x22, ofNat_shr6 (by omega), ofNat_beq_zero (by omega)])
      (fun _ => fill_ok hp hI₂ hcl h10₂) (fun hb' => ?_)
    simp only [decide_eq_false_iff_not] at hb'
    exact WP.mono (direct_ok hp hI₂ hb (by omega)) fun s' h => .inl ⟨c + 64, by omega, h⟩
  · rcases h with ⟨c', hc', hP⟩ | ⟨hD, h10⟩
    · refine WP.ite false (by show VG.AArch64.eval (.zero .x .x10) s' = _; rw [eval_zero, hP.x10]; rfl)
        (fun h => by cases h) fun _ => WP.mono (hP.compress_ok hp) fun s'' h => ⟨c', hc', h⟩
    · refine WP.ite true (by show VG.AArch64.eval (.zero .x .x10) s' = _; rw [eval_zero, h10]; rfl)
        (fun _ => WP.block_nil ⟨len s₀, hcl, hD⟩) fun h => by cases h

/-! ## Prologue and epilogue -/

/-- The prologue after saving. -/
def prologue : List Instr :=
  [mov .x19 .x0, mov .x20 .x4, mov .x21 .x2, mov .x22 .x3, .movz .x .x9 63 0, .logic .and .x .x23 .x1 .x9]

theorem update_eq : updateMain = .seq (.block (save .x4 ++ prologue))
    (.seq (.ite (.zero .x .x22) (.block []) (.loop updateBody (.nonzero .x .x22))) (.block restore)) := rfl

theorem prologue_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block (save .x4 ++ prologue)) s₀ (Inv s₀ 0) := by
  refine save_ok (fun d hd₁ hd₂ => ⟨scR s₀, by simp [hp.wr], contains_offset (by omega) (by omega)⟩)
    fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
  unfold prologue
  refine wp_mov fun s₂ u₂ => wp_mov fun s₃ u₃ => wp_mov fun s₄ u₄ => wp_mov fun s₅ u₅ =>
    wp_movz fun s₆ u₆ => wp_and fun s₇ u₇ => WP.block_nil ?_
  have hm₇ : s₇.mem = saveMem s₀.mem (scr s₀) s₀.gpr := by
    rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, m₁]
  refine ⟨⟨Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, fun m hm => ?_⟩
  · rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁]
  · rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.gpr, g₁]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.gpr, u₂.other _ (by decide), g₁]
  · rw [u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, sp₁]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr,
      u₃.other _ (by decide), u₂.other _ (by decide), g₁]
    simp
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), g₁]
    simp
  · rw [hm₇]; exact (saveMem_frame _ _ _).mono (by simp)
  · rw [hm₇]; exact saveMem_saved _ _ _
  · rw [u₇.gpr, u₆.gpr, u₆.other .x1 (by decide), u₅.other .x1 (by decide), u₄.other .x1 (by decide),
      u₃.other .x1 (by decide), u₂.other .x1 (by decide), g₁, and63, Nat.add_zero]
  · rw [List.take_zero, List.append_nil, hm₇]
    exact repr_congr (fun i hi => frame_bytes (saveMem_frame s₀.mem (scr s₀) s₀.gpr) (R := stR s₀)
      (by simpa using hp.st_scr) (by simp) hi) hm.1

/-- The epilogue's postcondition. -/
def Post (s₀ s' : State) : Prop :=
  (∀ p ∈ saved, s'.gpr p.1 = s₀.gpr p.1) ∧ s'.sp = s₀.sp ∧ Proof.Sha1.updateAArch64.post s₀ s'

theorem epilogue_ok {s₀ : State} (hp : Pre s₀) {s : State} (hI : Inv s₀ (len s₀) s) :
    WP isa (.block restore) s (Post s₀) := by
  refine restore_ok (scr := scr s₀) hI.x20
    (fun d hd₁ hd₂ => ⟨scR s₀, by simp [hI.rd, hI.wr, hp.wr], contains_offset hd₂ (by omega)⟩) s₀.gpr
    hI.saved fun s' hs _ hmem _ _ hsp => ⟨hs, by rw [hsp, hI.sp], fun m hr hc => ?_⟩
  have := hI.repr m ⟨hr, hc⟩
  rwa [List.take_of_length_le (by rw [D_length]), ← hmem] at this

/-- No instruction of `updateMain` writes the callee-saved registers it does not save. -/
theorem untouched_ok : ∀ r ∈ untouched, ∀ i ∈ instrs updateMain, dstOf i ≠ some r := by
  have : ((instrs updateMain).all fun i => untouched.all fun r => dstOf i != some r) = true := by
    rw [← Code.allInstrs_eq]; decide +kernel
  intro r hr i hi
  have := List.all_eq_true.mp (List.all_eq_true.mp this i hi) r hr
  simpa using this

/-- `update` without its frame: the callee-saved registers but `x30` are kept. -/
theorem correctMain {s₀ : State} (hp : Pre s₀) :
    WP isa updateMain s₀ fun s' => (∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s₀.gpr r) ∧
      s'.sp = s₀.sp ∧ Proof.Sha1.updateAArch64.post s₀ s' := by
  have hlen := len_lt s₀
  refine WP.mono (WP.gprs (Q := Post s₀) ?_ untouched_ok) fun s' ⟨⟨hsv, hsp, hpost⟩, hu⟩ =>
    ⟨fun r hr h30 => ?_, hsp, hpost⟩
  · rw [update_eq]
    refine WP.seq (WP.mono (prologue_ok hp) fun s₁ hI => ?_)
    refine WP.seq (WP.mono (Q := Inv s₀ (len s₀)) ?_ fun s₂ hI₂ => epilogue_ok hp hI₂)
    refine WP.ite (decide (len s₀ = 0))
      (by show VG.AArch64.eval (.zero .x .x22) s₁ = _
          rw [eval_zero, hI.x22, Nat.sub_zero, ofNat_beq_zero (by omega)])
      (fun hb => ?_) (fun hb => ?_)
    · simp only [decide_eq_true_eq] at hb
      exact WP.block_nil (hb ▸ hI)
    · simp only [decide_eq_false_iff_not] at hb
      refine WP.loop (M := isa) (fun n s => ∃ c, n = len s₀ - c ∧ c < len s₀ ∧ Inv s₀ c s) ?_ (len s₀) s₁
        ⟨0, rfl, by omega, hI⟩
      rintro n s ⟨c, rfl, hcl, hI⟩
      refine WP.mono (body_ok hp hI hcl) fun s' ⟨c', hc, hI'⟩ => ?_
      have hc' := hI'.c_le
      have hz : isa.eval (.nonzero .x .x22) s' = some (decide (len s₀ - c' ≠ 0)) := by
        show VG.AArch64.eval (.nonzero .x .x22) s' = _
        rw [eval_nonzero, hI'.x22, bne, ofNat_beq_zero (by omega)]
        simp
      by_cases hl : len s₀ - c' = 0
      · refine .inl ⟨by rw [hz]; simp [hl], ?_⟩
        rwa [show c' = len s₀ by omega] at hI'
      · exact .inr ⟨by rw [hz]; simp [hl], len s₀ - c', by omega, c', rfl, by omega, hI'⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hsv (.x19, 112) (by simp [saved])
    · exact hsv (.x20, 120) (by simp [saved])
    · exact hsv (.x21, 128) (by simp [saved])
    · exact hsv (.x22, 136) (by simp [saved])
    · exact hsv (.x23, 144) (by simp [saved])
    · exact hsv (.x24, 152) (by simp [saved])
    all_goals first | exact absurd rfl h30 | exact hu _ (by simp [untouched])

/-- The state `updateMain` starts in, inside the frame. -/
abbrev inner (s₀ : State) : State :=
  { s₀ with sp := s₀.sp - 16, mem := s₀.mem.write (s₀.sp - 16) 8 (s₀.gpr .x30) }

theorem correct {s₀ : State} (hp : Pre s₀) (hs : Stack s₀) :
    WP isa update s₀ fun s' => abiPreserved s₀ s' ∧ Proof.Sha1.updateAArch64.post s₀ s' := by
  have hpi : Pre (inner s₀) := ⟨hp.rd, hp.wr, hp.st_scr, hp.d_st, hp.d_scr⟩
  refine WP.frameReg hs.sp16 (fun R hR => ?_) (WP.mono (correctMain hpi) fun s' ⟨hk, hsp, hpost⟩ => ?_)
  · rw [hp.wr] at hR
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl
    · exact hs.st
    · exact hs.scr
  · refine ⟨⟨fun r hr => ?_, rfl⟩, fun m hm hc => ?_⟩
    · by_cases h30 : r = .x30
      · subst h30; simp [State.write]
      · simp only [State.write, h30, ite_false]
        exact hk r hr h30
    · have e : bytesAt (inner s₀).mem (dp s₀) (len s₀) = bytesAt s₀.mem (dp s₀) (len s₀) :=
        bytesAt_congr fun i hi => write_frame_bytes hs.d (len_lt s₀) hi
      have := hpost m (repr_congr (fun i hi => write_frame_bytes (R := stR s₀) hs.st
        (by simp) hi) hm) hc
      rw [e] at this
      exact this

theorem agree₀ {s₁ s₂ : State} (hpub : Proof.Sha1.updateAArch64.pub s₁ s₂) :
    VG.AArch64.Taint.Agree (VG.AArch64.Taint.ofRegs [.x0, .x1, .x2, .x3, .x4]) s₁ s₂ := by
  obtain ⟨p1, p2, p3, p4, p5, hsp⟩ := hpub
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> assumption

/-- A state satisfying the precondition (with no data). -/
def sat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x2 => 0x2000 | .x4 => 0x3000 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, 84⟩, ⟨0x3000, 160⟩]

theorem update_verified : Verified AArch64.target update Proof.Sha1.updateAArch64 := by
  refine ⟨fun s hs => ?_, ?_, ?_⟩
  · obtain ⟨t, s', he, h⟩ := correct (pre_of hs).1 (pre_of hs).2
    exact ⟨t, s', he, h⟩
  · exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4]) (fun _ _ _ _ hp => agree₀ hp)
      (by taint_decide)
  · refine ⟨sat, rfl, rfl, ?_, ?_, ?_, by decide, ?_, ?_, ?_⟩ <;>
    · intro a h₁ h₂
      simp only [Region.Contains, sat] at h₁ h₂
      bv_omega

end VG.Proof.Sha1.AArch64.Stream.Update
