import VerifiedGarbage.Proof.Sha256.PPC64LE.Stream.Common

/-!
# Streaming SHA-256 on PPC64LE: `update`

Untrusted: everything here is checked by Lean. The same structure as the
x86-64 proof (`VG.Proof.Sha256.X86_64.Stream.Update`); the loop runs while
data is left, so every iteration consumes at least one byte.
-/

namespace VG.Proof.Sha256.PPC64LE.Stream.Update

open VG VG.PPC64LE VG.Impl.Sha256.PPC64LE.Stream
open VG.Proof.Sha256.PPC64LE (contains_offset toNat_ofNat_lt sub_offset)
open VG.Proof.Sha256.PPC64LE.Stream
open VG.Proof.Sha256.Stream
open VG.Spec.Sha256 (HashValue stateAt blockAt compress parseBlock bytesAt)

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev st : Addr := s₀.gpr .r3
abbrev cnt : Nat := (s₀.gpr .r4).toNat
abbrev dp : Addr := s₀.gpr .r5
abbrev len : Nat := (s₀.gpr .r6).toNat
abbrev scr : Addr := s₀.gpr .r7
abbrev stR : Region := ⟨st s₀, 96⟩
abbrev dR : Region := ⟨dp s₀, len s₀⟩
abbrev scR : Region := ⟨scr s₀, 160⟩
/-- The data. -/
abbrev D : List Byte := bytesAt s₀.mem (dp s₀) (len s₀)

/-- The messages the initial state represents. -/
def R₀ (iv : HashValue) (m : List Byte) : Prop :=
  Spec.Sha256.ReprFrom iv s₀.mem (st s₀) m ∧ s₀.gpr .r4 = BitVec.ofNat 64 m.length

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

/-- The frame saving the link register, below the stack pointer. -/
abbrev stkR (s₀ : State) : Region := ⟨s₀.sp - 48, 48⟩

/-- The frame is below the stack pointer, and disjoint from the buffers. -/
structure Stack (s₀ : State) : Prop where
  sp48 : 48 ≤ s₀.sp.toNat
  st : (stkR s₀).Disjoint (stR s₀)
  d : (stkR s₀).Disjoint (dR s₀)
  scr : (stkR s₀).Disjoint (scR s₀)

theorem pre_of {s₀ : State} (h : Proof.Sha256.updatePPC64LE.pre s₀) : Pre s₀ ∧ Stack s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨⟨h1, h2, h3, h4, h5⟩, ⟨h6, h7, h8, h9⟩⟩

theorem R₀.length {s₀ : State} {iv : HashValue} {m : List Byte} (h : R₀ s₀ iv m) : cnt s₀ % 64 = m.length % 64 := by
  rw [cnt, h.2, BitVec.toNat_ofNat]
  omega

theorem len_lt (s₀ : State) : len s₀ < 2 ^ 64 := (s₀.gpr .r6).isLt

theorem D_length (s₀ : State) : (D s₀).length = len s₀ := by simp [bytesAt]

/-! ## Invariants -/

/-- What holds throughout, after consuming `c` bytes of data. -/
structure Common (s₀ : State) (c : Nat) (s : State) : Prop where
  c_le : c ≤ len s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  r26 : s.gpr .r26 = st s₀
  r27 : s.gpr .r27 = scr s₀
  sp : s.sp = s₀.sp
  r28 : s.gpr .r28 = dp s₀ + BitVec.ofNat 64 c
  r29 : s.gpr .r29 = BitVec.ofNat 64 (len s₀ - c)
  frame : Frame [stR s₀, scR s₀] s₀.mem s.mem
  saved : Saved s₀ s.mem

/-- The loop invariant: the state represents the message followed by the
first `c` bytes of data. -/
structure Inv (s₀ : State) (c : Nat) (s : State) : Prop extends Common s₀ c s where
  r30 : s.gpr .r30 = BitVec.ofNat 64 ((cnt s₀ + c) % 64)
  repr : ∀ iv m, R₀ s₀ iv m → Spec.Sha256.ReprFrom iv s.mem (st s₀) (m ++ (D s₀).take c)

/-- A whole block is ready at `r4`, and compressing it absorbs the first `c`
bytes of data. -/
structure Pending (s₀ : State) (c : Nat) (s : State) : Prop extends Common s₀ c s where
  r30 : s.gpr .r30 = 0
  r9 : s.gpr .r9 = 1
  mod : (cnt s₀ + c) % 64 = 0
  src : s.gpr .r4 = st s₀ + 32 ∨ ∃ c₀, s.gpr .r4 = dp s₀ + BitVec.ofNat 64 c₀ ∧ c₀ + 64 ≤ len s₀
  repr : ∀ iv m, R₀ s₀ iv m → ∀ mem', stateAt mem' (st s₀) =
      compress (stateAt s.mem (st s₀)) (blockAt s.mem (s.gpr .r4)) →
    Spec.Sha256.ReprFrom iv mem' (st s₀) (m ++ (D s₀).take c)

/-- All the data is absorbed, and nothing is pending. -/
def Done (s₀ : State) (s : State) : Prop := Inv s₀ (len s₀) s ∧ s.gpr .r9 = 0

theorem Common.of_gpr {s₀ : State} {c : Nat} {s s' : State} (h : Common s₀ c s)
    (hg : ∀ r ∈ [Reg.r26, .r27, .r28, .r29], s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) :
    Common s₀ c s' where
  c_le := h.c_le
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  r26 := by rw [hg _ (by simp)]; exact h.r26
  r27 := by rw [hg _ (by simp)]; exact h.r27
  sp := hsp.trans h.sp
  r28 := by rw [hg _ (by simp)]; exact h.r28
  r29 := by rw [hg _ (by simp)]; exact h.r29
  frame := by rw [hm]; exact h.frame
  saved := by rw [hm]; exact h.saved

theorem Inv.of_gpr {s₀ : State} {c : Nat} {s s' : State} (h : Inv s₀ c s)
    (hg : ∀ r ∈ [Reg.r26, .r27, .r28, .r29, .r30], s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) :
    Inv s₀ c s' :=
  { h.toCommon.of_gpr (fun r hr => hg r (by simp at hr ⊢; tauto)) hm hrd hwr hsp with
    r30 := by rw [hg _ (by simp)]; exact h.r30
    repr := by rw [hm]; exact h.repr }

/-- Where the caller's registers are saved. -/
theorem saved_sub {s₀ : State} {p : Reg × Nat} (hp : p ∈ saved) :
    Region.Sub ⟨scr s₀ + BitVec.ofNat 64 p.2, 8⟩ (scR s₀) := by
  simp only [Impl.Sha256.PPC64LE.Stream.saved, List.mem_cons, List.not_mem_nil, or_false] at hp
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

theorem length_mid (s₀ : State) {iv : HashValue} {m : List Byte} (hm : R₀ s₀ iv m) {c : Nat} (hc : c ≤ len s₀) :
    (m ++ (D s₀).take c).length % 64 = (cnt s₀ + c) % 64 := by
  have := hm.length
  simp only [List.length_append, List.length_take, D_length, Nat.min_eq_left hc]
  omega

theorem take_add_data (s₀ : State) (c t : Nat) (m : List Byte) :
    m ++ (D s₀).take c ++ ((D s₀).drop c).take t = m ++ (D s₀).take (c + t) := by
  rw [List.take_add, List.append_assoc]

/-! ## Compressing a pending block -/

theorem Pending.compress_ok {s₀ : State} (hp : Pre s₀) {c : Nat} {s : State} (h : Pending s₀ c s) :
    WP isa compressAt s fun s' => Inv s₀ c s' ∧ ∀ r ∈ preserved, s'.gpr r = s.gpr r := by
  have e32 : Region.Sub ⟨st s₀, 32⟩ (stR s₀) := Region.sub_prefix (by omega)
  have e112 : Region.Sub ⟨scr s₀, 112⟩ (scR s₀) := Region.sub_prefix (by omega)
  have eSrc : Region.Sub ⟨s.gpr .r4, 64⟩ (stR s₀) ∨ Region.Sub ⟨s.gpr .r4, 64⟩ (dR s₀) := by
    rcases h.src with h' | ⟨c₀, h', hc₀⟩
    · exact .inl (h' ▸ sub_offset (off := 32) (by omega) (by omega))
    · exact .inr (h' ▸ sub_offset (by omega) (by have := len_lt s₀; omega))
  refine compressAt_ok h.r26 h.r27 rfl ((hp.st_scr.sub_left e32).sub_right e112) ?_ ?_ ?_ ?_ ?_
  · rcases h.src with h' | ⟨c₀, h', hc₀⟩
    · rw [h']; intro a h₁ h₂; simp only [Region.Contains] at h₁ h₂; bv_omega
    · exact (hp.d_st.sub_left (h' ▸ sub_offset (by omega) (by have := len_lt s₀; omega))).sub_right e32
  · rcases eSrc with e | e
    · exact (hp.st_scr.sub_left e).sub_right e112
    · exact (hp.d_scr.sub_left e).sub_right e112
  · rw [h.rd, h.wr, hp.rd, hp.wr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rcases h.src with h' | ⟨c₀, h', hc₀⟩
      · exact ⟨stR s₀, by simp, 32, by rw [h']; rfl, by simp⟩
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
    have cs : ∀ r, r ∈ preserved → s'.gpr r = s.gpr r := hcs
    refine ⟨⟨⟨h.c_le, hrd.trans h.rd, hwr.trans h.wr, by rw [cs _ (by decide)]; exact h.r26,
      by rw [cs _ (by decide)]; exact h.r27, hsp.trans h.sp,
      by rw [cs _ (by decide)]; exact h.r28,
      by rw [cs _ (by decide)]; exact h.r29,
      h.frame.trans (hf.sub ?_), fun p hp' => ?_⟩, ?_, fun iv m hm => h.repr iv m hm _ hstate⟩, cs⟩
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨stR s₀, by simp, e32⟩
      · exact ⟨scR s₀, by simp, e112⟩
    · rw [← h.saved p hp']
      refine hf.readW (r := ⟨scr s₀ + BitVec.ofNat 64 p.2, 8⟩) (Region.contains_self _ _) ?_ (by decide)
      intro r' hr'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl
      · exact (hp.st_scr.symm.sub_left (saved_sub hp')).sub_right e32
      · simp only [Impl.Sha256.PPC64LE.Stream.saved, List.mem_cons, List.not_mem_nil, or_false] at hp'
        rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl <;>
        · intro a h₁ h₂; simp only [Region.Contains] at h₁ h₂; bv_omega
    · rw [cs _ (by decide), h.r30, h.mod]; rfl

/-! ## A whole block straight from the data -/

theorem direct_ok {s₀ : State} (hp : Pre s₀) {c : Nat} {s : State} (hI : Inv s₀ c s)
    (hr : (cnt s₀ + c) % 64 = 0) (hl : 64 ≤ len s₀ - c) :
    WP isa (.block direct) s (Pending s₀ (c + 64)) := by
  have hlen := len_lt s₀
  unfold direct
  refine wp_mov fun s₁ u₁ => wp_addi (by decide) (by decide) fun s₂ u₂ => wp_subi (by decide) (by decide) fun s₃ u₃ =>
    wp_li (by decide) fun s₄ u₄ => WP.block_nil ?_
  have g : ∀ r, r ≠ .r4 → r ≠ .r28 → r ≠ .r29 → r ≠ .r9 → s₄.gpr r = s.gpr r := fun r h1 h2 h3 h4 => by
    rw [u₄.other r h4, u₃.other r h3, u₂.other r h2, u₁.other r h1]
  have m₄ : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have h1 : s₄.gpr .r4 = dp s₀ + BitVec.ofNat 64 c := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hI.r28]
  refine ⟨⟨by omega, by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd, hI.rd], by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr, hI.wr],
    by rw [g _ (by decide) (by decide) (by decide) (by decide), hI.r26],
    by rw [g _ (by decide) (by decide) (by decide) (by decide), hI.r27],
    by rw [u₄.sp, u₃.sp, u₂.sp, u₁.sp, hI.sp], ?_, ?_, by rw [m₄]; exact hI.frame,
    by rw [m₄]; exact hI.saved⟩, ?_, by rw [u₄.gpr]; rfl, by omega, .inr ⟨c, h1, by omega⟩, ?_⟩
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), hI.r28,
      BitVec.add_assoc, ← BitVec.ofNat_add]
  · rw [u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), hI.r29,
      sub_ofNat (by omega), Nat.sub_sub]
  · rw [g _ (by decide) (by decide) (by decide) (by decide), hI.r30, hr]; rfl
  · intro iv m hm mem' hs
    have hmod := length_mid s₀ hm (c := c) (by omega)
    rw [← take_add_data]
    refine reprFrom_append_block (hI.repr iv m hm)
      (by rw [hmod, hr, List.length_take, List.length_drop, D_length]; omega) ?_
    rw [hs, m₄, h1]
    congr 1
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
abbrev q : Addr := st s₀ + 32 + BitVec.ofNat 64 (rr s₀ c)
/-- The data copied. -/
abbrev xs : List Byte := ((D s₀).drop c).take (tt s₀ c)
end

theorem rr_lt (s₀ : State) (c : Nat) : rr s₀ c < 64 := Nat.mod_lt _ (by omega)
theorem tt_le (s₀ : State) (c : Nat) : tt s₀ c ≤ len s₀ - c := Nat.min_le_right _ _
theorem tt_le' (s₀ : State) (c : Nat) : tt s₀ c ≤ 64 - rr s₀ c := Nat.min_le_left _ _
theorem rr_eq (s₀ : State) (c : Nat) : rr s₀ c = (cnt s₀ + c) % 64 := rfl
theorem tt_eq (s₀ : State) (c : Nat) : tt s₀ c = min (64 - rr s₀ c) (len s₀ - c) := rfl

theorem q_eq (s₀ : State) (c : Nat) : q s₀ c = st s₀ + BitVec.ofNat 64 (32 + rr s₀ c) := by
  simp only [q, BitVec.ofNat_add]; rw [BitVec.add_assoc]; rfl

theorem xs_length (s₀ : State) (c : Nat) : (xs s₀ c).length = tt s₀ c := by
  have := tt_le s₀ c
  simp only [xs, List.length_take, List.length_drop, D_length]; omega

/-- The state while copying: `j` bytes copied, into memory otherwise as in `mI`. -/
structure Copy (s₀ : State) (c : Nat) (mI : Mem) (j : Nat) (s : State) : Prop where
  j_le : j ≤ tt s₀ c
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  r26 : s.gpr .r26 = st s₀
  r27 : s.gpr .r27 = scr s₀
  sp : s.sp = s₀.sp
  r28 : s.gpr .r28 = dp s₀ + BitVec.ofNat 64 (c + j)
  r29 : s.gpr .r29 = BitVec.ofNat 64 (len s₀ - c - tt s₀ c)
  r30 : s.gpr .r30 = BitVec.ofNat 64 (rr s₀ c + j)
  r10 : s.gpr .r10 = BitVec.ofNat 64 (tt s₀ c - j)
  r9 : s.gpr .r9 = 0
  mem : s.mem = writeBytes mI (q s₀ c) ((xs s₀ c).take j)

theorem write_frame (s₀ : State) (c : Nat) (mI : Mem) (j : Nat) (hj : j ≤ tt s₀ c) :
    Frame [stR s₀] mI (writeBytes mI (q s₀ c) ((xs s₀ c).take j)) := by
  have := tt_le' s₀ c; have := rr_lt s₀ c
  refine writeBytes_frame _ _ _ ?_
  rw [q_eq]
  exact contains_offset (by simp only [List.length_take]; omega) (by omega)

/-- The copy loop's body. -/
def copyBody : List Instr :=
  [.lbz .r8 .r28 0, .add .r11 .r26 .r30, .stb .r8 .r11 32, .addi .r28 .r28 1,
    .addi .r30 .r30 1, .subi .r10 .r10 1]

theorem copy_step {s₀ : State} (hp : Pre s₀) {c : Nat} {sI : State} (hI : Inv s₀ c sI) {j : Nat}
    (hj : j < tt s₀ c) {s : State} (h : Copy s₀ c sI.mem j s) :
    WP isa (.block copyBody) s fun s' =>
      Copy s₀ c sI.mem (j + 1) s' ∧ s'.gpr .r10 = BitVec.ofNat 64 (tt s₀ c - (j + 1)) := by
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
  refine wp_lbz (a := dp s₀ + BitVec.ofNat 64 (c + j)) (by decide) (by omega) (by rw [h.r28]; simp) hin
    fun s₁ u₁ => ?_
  refine wp_add fun s₂ u₂ => wp_stb (a := q s₀ c + BitVec.ofNat 64 j) (by decide) (by omega) ?_
    (by rw [u₂.wr, u₁.wr]; exact hout) fun s₃ g₃ => ?_
  · rw [u₂.gpr, u₁.other _ (by decide), u₁.other _ (by decide), h.r26, h.r30, q]
    simp only [BitVec.ofNat_add, show BitVec.ofNat 64 32 = (32 : BitVec 64) from rfl]
    ac_rfl
  refine wp_addi (by decide) (by decide) fun s₄ u₄ => wp_addi (by decide) (by decide) fun s₅ u₅ =>
    wp_subi (by decide) (by decide) fun s₆ u₆ => WP.block_nil ?_
  have g : ∀ r, r ≠ .r8 → r ≠ .r11 → r ≠ .r28 → r ≠ .r30 → r ≠ .r10 → s₆.gpr r = s.gpr r :=
    fun r h1 h2 h3 h4 h5 => by
      rw [u₆.other r h5, u₅.other r h4, u₄.other r h3, g₃.gpr, u₂.other r h2, u₁.other r h1]
  have hx11 : s₆.gpr .r10 = BitVec.ofNat 64 (tt s₀ c - (j + 1)) := by
    rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), g₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), h.r10, sub_ofNat (by omega), Nat.sub_sub]
  refine ⟨⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hx11, ?_, ?_⟩, hx11⟩
  · rw [u₆.rd, u₅.rd, u₄.rd, g₃.rd, u₂.rd, u₁.rd, h.rd]
  · rw [u₆.wr, u₅.wr, u₄.wr, g₃.wr, u₂.wr, u₁.wr, h.wr]
  · rw [g .r26 (by decide) (by decide) (by decide) (by decide) (by decide), h.r26]
  · rw [g .r27 (by decide) (by decide) (by decide) (by decide) (by decide), h.r27]
  · rw [u₆.sp, u₅.sp, u₄.sp, g₃.sp, u₂.sp, u₁.sp, h.sp]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, g₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), h.r28, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_assoc]
  · rw [g .r29 (by decide) (by decide) (by decide) (by decide) (by decide), h.r29]
  · rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), g₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), h.r30, ← BitVec.ofNat_add, Nat.add_assoc]
  · rw [g .r9 (by decide) (by decide) (by decide) (by decide) (by decide), h.r9]
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
    WP isa (.loop (.block copyBody) (.nonzero .d .r10)) s (Copy s₀ c sI.mem (tt s₀ c)) := by
  refine WP.loop (M := isa) (fun n s => ∃ j, n = tt s₀ c - j ∧ j < tt s₀ c ∧ Copy s₀ c sI.mem j s)
    ?_ (tt s₀ c) s ⟨0, rfl, ht, h⟩
  rintro n s ⟨j, rfl, hj, hc⟩
  refine WP.mono (copy_step hp hI hj hc) fun s' ⟨hc', h11⟩ => ?_
  have hz : isa.eval (.nonzero .d .r10) s' = some (decide (tt s₀ c - (j + 1) ≠ 0)) := by
    show VG.PPC64LE.eval (.nonzero .d .r10) s' = _
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
      bytesAt mem (st s₀ + 32) (rr s₀ c + tt s₀ c) = bytesAt sI.mem (st s₀ + 32) (rr s₀ c) ++ xs s₀ c := by
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
    WP isa (.block [.addi .r4 .r26 32, .li .r30 0, .li .r9 1]) s
      (Pending s₀ (c + tt s₀ c)) := by
  have hr := rr_lt s₀ c; have ht := tt_le s₀ c; have ht' := tt_le' s₀ c
  have hrr := rr_eq s₀ c; have htt := tt_eq s₀ c
  have hxs := xs_length s₀ c
  have hc := hI.c_le
  obtain ⟨hfr, hsv, hst, hby⟩ := copied_facts hp hI
  have hmem : s.mem = writeBytes sI.mem (q s₀ c) (xs s₀ c) := by
    rw [h.mem, List.take_of_length_le (by omega)]
  refine wp_addi (by decide) (by decide) fun s₁ u₁ => wp_li (by decide) fun s₂ u₂ => wp_li (by decide) fun s₃ u₃ => WP.block_nil ?_
  have g : ∀ r, r ≠ .r4 → r ≠ .r30 → r ≠ .r9 → s₃.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [u₃.other r h3, u₂.other r h2, u₁.other r h1]
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have hx1 : s₃.gpr .r4 = st s₀ + 32 := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h.r26]; rfl
  refine ⟨⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by rw [m₃, hmem]; exact hfr, by rw [m₃, hmem]; exact hsv⟩,
    by rw [u₃.other _ (by decide), u₂.gpr]; rfl, by rw [u₃.gpr]; rfl, by omega, .inl hx1, ?_⟩
  · rw [u₃.rd, u₂.rd, u₁.rd, h.rd]
  · rw [u₃.wr, u₂.wr, u₁.wr, h.wr]
  · rw [g .r26 (by decide) (by decide) (by decide), h.r26]
  · rw [g .r27 (by decide) (by decide) (by decide), h.r27]
  · rw [u₃.sp, u₂.sp, u₁.sp, h.sp]
  · rw [g .r28 (by decide) (by decide) (by decide), h.r28]
  · rw [g .r29 (by decide) (by decide) (by decide), h.r29, Nat.sub_sub]
  · intro iv m hm mem' hs
    rw [← take_add_data]
    have hmod := length_mid s₀ hm hc
    refine reprFrom_append_block (hI.repr iv m hm) (by rw [hmod, hxs]; exact hfull) ?_
    rw [hs, m₃, hmem, hst, hx1]
    refine congrArg (compress _) (parseBlock_congr fun k hk => ?_)
    have hb := (hI.repr iv m hm).2
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
  refine ⟨⟨⟨le_rfl, h.rd, h.wr, h.r26, h.r27, h.sp, ?_, ?_, by rw [hmem]; exact hfr,
    by rw [hmem]; exact hsv⟩, ?_, fun iv m hm => ?_⟩, h.r9⟩
  · rw [h.r28]; congr 2; omega
  · rw [h.r29]; congr 1; omega
  · rw [h.r30]; congr 1; omega
  · have hmod := length_mid s₀ hm hc
    rw [show len s₀ = c + tt s₀ c by omega, ← take_add_data]
    refine reprFrom_append_buf (hI.repr iv m hm) (by rw [hmod, hxs]; omega) (by rw [hmem, hst]) ?_
    rw [hmod, hxs, hmem, hby]
    have hb := (hI.repr iv m hm).2
    rw [hmod] at hb
    rw [hb]

theorem fill_eq : fill =
    .seq (.block [.li .r10 64, .sub .r10 .r10 .r30, .lsr .d .r8 .r29 6])
    (.seq (.ite (.zero .d .r8)
        (.seq (.block [.add .r8 .r29 .r30, .lsr .d .r8 .r8 6])
          (.ite (.zero .d .r8) (.block [mov .r10 .r29]) (.block [])))
        (.block []))
    (.seq (.block [.sub .r29 .r29 .r10])
    (.seq (.loop (.block copyBody) (.nonzero .d .r10))
    (.seq (.block [.subi .r8 .r30 64])
      (.ite (.zero .d .r8) (.block [.addi .r4 .r26 32, .li .r30 0, .li .r9 1])
        (.block [])))))) := rfl

theorem fill_ok {s₀ : State} (hp : Pre s₀) {c : Nat} {s : State} (hI : Inv s₀ c s) (hcl : c < len s₀)
    (h10 : s.gpr .r9 = 0) :
    WP isa fill s fun s' => (∃ c', c < c' ∧ Pending s₀ c' s') ∨ Done s₀ s' := by
  have hr := rr_lt s₀ c; have ht := tt_le s₀ c; have ht' := tt_le' s₀ c
  have hrr := rr_eq s₀ c; have htt := tt_eq s₀ c
  have ne : ∀ r ∈ [Reg.r26, .r27, .r28, .r29, .r30], r ≠ .r8 ∧ r ≠ .r10 := by decide
  have hc := hI.c_le; have hlen := len_lt s₀
  rw [fill_eq]
  -- `r10 := 64 - r; r8 := len >> 6`
  refine WP.seq (wp_li (by decide) fun s₁ u₁ => wp_sub fun s₂ u₂ => wp_lsr (by decide) fun s₃ u₃ => WP.block_nil ?_)
  have e₃ : ∀ r, r ≠ .r8 → r ≠ .r10 → s₃.gpr r = s.gpr r := fun r h h' => by
    rw [u₃.other r h, u₂.other r h', u₁.other r h']
  have hI₃ : Inv s₀ c s₃ := hI.of_gpr (fun r hr => e₃ r (ne r hr).1 (ne r hr).2)
    (by rw [u₃.mem, u₂.mem, u₁.mem]) (by rw [u₃.rd, u₂.rd, u₁.rd]) (by rw [u₃.wr, u₂.wr, u₁.wr])
    (by rw [u₃.sp, u₂.sp, u₁.sp])
  have h11₃ : s₃.gpr .r10 = BitVec.ofNat 64 (64 - rr s₀ c) := by
    rw [u₃.other _ (by decide), u₂.gpr, u₁.gpr, u₁.other _ (by decide), hI.r30, sub_ofNat (by omega)]
  have h9₃ : s₃.gpr .r8 = BitVec.ofNat 64 ((len s₀ - c) / 64) := by
    rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), hI.r29, ofNat_shr6 (by omega)]
  -- `r10 := min(r10, len)`
  refine WP.seq (WP.mono (Q := fun (s₄ : State) => Inv s₀ c s₄ ∧ s₄.gpr .r10 = BitVec.ofNat 64 (tt s₀ c) ∧
    s₄.gpr .r9 = 0 ∧ s₄.mem = s.mem) ?_ fun s₄ ⟨hI₄, h11₄, h10₄, hm₄⟩ => ?_)
  · have hm₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
    have h10₃ : s₃.gpr .r9 = 0 := by rw [e₃ _ (by decide) (by decide), h10]
    refine WP.ite (decide ((len s₀ - c) / 64 = 0))
      (by show VG.PPC64LE.eval (.zero .d .r8) s₃ = _; rw [eval_zero, h9₃, ofNat_beq_zero (by omega)]) (fun hb => ?_) (fun hb => ?_)
    · simp only [decide_eq_true_eq] at hb
      refine WP.seq (wp_add fun s₅ u₅ => wp_lsr (by decide) fun s₆ u₆ => WP.block_nil ?_)
      have e₆ : ∀ r, r ≠ .r8 → s₆.gpr r = s₃.gpr r := fun r h => by rw [u₆.other r h, u₅.other r h]
      have hI₆ : Inv s₀ c s₆ := hI₃.of_gpr (fun r hr => e₆ r (ne r hr).1) (by rw [u₆.mem, u₅.mem]) (by rw [u₆.rd, u₅.rd]) (by rw [u₆.wr, u₅.wr])
        (by rw [u₆.sp, u₅.sp])
      have h9₆ : s₆.gpr .r8 = BitVec.ofNat 64 ((len s₀ - c + rr s₀ c) / 64) := by
        rw [u₆.gpr, u₅.gpr, hI₃.r29, hI₃.r30, ← BitVec.ofNat_add, ofNat_shr6 (by omega)]
      refine WP.ite (decide ((len s₀ - c + rr s₀ c) / 64 = 0))
        (by show VG.PPC64LE.eval (.zero .d .r8) s₆ = _; rw [eval_zero, h9₆, ofNat_beq_zero (by omega)]) (fun hb' => ?_) (fun hb' => ?_)
      · simp only [decide_eq_true_eq] at hb'
        refine wp_mov fun s₇ u₇ => WP.block_nil ⟨hI₆.of_gpr (fun r hr => u₇.other r (ne r hr).2)
          u₇.mem u₇.rd u₇.wr u₇.sp,
          ?_, by rw [u₇.other _ (by decide), e₆ _ (by decide), h10₃], by rw [u₇.mem, u₆.mem, u₅.mem, hm₃]⟩
        rw [u₇.gpr, hI₆.r29]; congr 1; omega
      · simp only [decide_eq_false_iff_not] at hb'
        refine WP.block_nil ⟨hI₆, ?_, by rw [e₆ _ (by decide), h10₃], by rw [u₆.mem, u₅.mem, hm₃]⟩
        rw [e₆ _ (by decide), h11₃]; congr 1; omega
    · simp only [decide_eq_false_iff_not] at hb
      refine WP.block_nil ⟨hI₃, ?_, h10₃, hm₃⟩
      rw [h11₃]; congr 1; omega
  -- `r29 -= r10`
  refine WP.seq (wp_sub fun s₅ u₅ => WP.block_nil ?_)
  have hC₀ : Copy s₀ c s.mem 0 s₅ := by
    have e : ∀ r, r ≠ .r29 → s₅.gpr r = s₄.gpr r := fun r h => u₅.other r h
    refine ⟨Nat.zero_le _, by rw [u₅.rd, hI₄.rd], by rw [u₅.wr, hI₄.wr],
      by rw [e _ (by decide), hI₄.r26], by rw [e _ (by decide), hI₄.r27], by rw [u₅.sp, hI₄.sp],
      by rw [e _ (by decide), hI₄.r28, Nat.add_zero], ?_, by rw [e _ (by decide), hI₄.r30, Nat.add_zero],
      by rw [e _ (by decide), h11₄, Nat.sub_zero], by rw [e _ (by decide), h10₄], ?_⟩
    · rw [u₅.gpr, hI₄.r29, h11₄, sub_ofNat (by omega), Nat.sub_sub]
    · rw [u₅.mem, hm₄, List.take_zero, writeBytes_nil]
  -- Copy the bytes.
  refine WP.seq (WP.mono (copy_loop_ok hp hI hC₀ (by omega)) fun s₆ hC => ?_)
  -- Is the buffer full?
  refine WP.seq (wp_subi (by decide) (by decide) fun s₇ u₇ => WP.block_nil ?_)
  have hC₇ : Copy s₀ c s.mem (tt s₀ c) s₇ :=
    ⟨hC.j_le, by rw [u₇.rd, hC.rd], by rw [u₇.wr, hC.wr], by rw [u₇.other _ (by decide), hC.r26],
      by rw [u₇.other _ (by decide), hC.r27], by rw [u₇.sp, hC.sp], by rw [u₇.other _ (by decide), hC.r28],
      by rw [u₇.other _ (by decide), hC.r29], by rw [u₇.other _ (by decide), hC.r30],
      by rw [u₇.other _ (by decide), hC.r10], by rw [u₇.other _ (by decide), hC.r9],
      by rw [u₇.mem, hC.mem]⟩
  have hz : eval (.zero .d .r8) s₇ = some (decide (rr s₀ c + tt s₀ c = 64)) := by
    rw [eval_zero, u₇.gpr, hC.r30, sub_beq (by omega) (by omega)]
  refine WP.ite (decide (rr s₀ c + tt s₀ c = 64)) hz (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    exact WP.mono (fill_pending hp hI hC₇ hb) fun s' h => .inl ⟨c + tt s₀ c, by omega, h⟩
  · simp only [decide_eq_false_iff_not] at hb
    exact WP.block_nil (.inr (fill_done hp hI hC₇ hb))

/-! ## One iteration -/

theorem body_eq : updateBody =
    .seq (.block [.li .r9 0])
    (.seq (.ite (.zero .d .r30)
        (.seq (.block [.lsr .d .r8 .r29 6]) (.ite (.zero .d .r8) fill (.block direct)))
        fill)
      (.ite (.zero .d .r9) (.block []) compressAt)) := rfl

theorem body_ok {s₀ : State} (hp : Pre s₀) {c : Nat} {s : State} (hI : Inv s₀ c s) (hcl : c < len s₀) :
    WP isa updateBody s fun s' => (∃ c', c < c' ∧ Inv s₀ c' s') ∧ ∀ r ∈ nvRegs, s'.gpr r = s.gpr r := by
  have hlen := len_lt s₀; have hc := hI.c_le; have hr := rr_lt s₀ c
  have ne : ∀ r ∈ [Reg.r26, .r27, .r28, .r29, .r30], r ≠ .r9 ∧ r ≠ .r8 := by decide
  rw [body_eq]
  refine WP.seq (wp_li (by decide) fun s₁ u₁ => WP.block_nil ?_)
  have hI₁ : Inv s₀ c s₁ := hI.of_gpr (fun r hr => u₁.other r (ne r hr).1) u₁.mem u₁.rd u₁.wr u₁.sp
  have h10₁ : s₁.gpr .r9 = 0 := by rw [u₁.gpr]; rfl
  have nv₁ : ∀ r ∈ nvRegs, s₁.gpr r = s.gpr r := fun r hr => u₁.other r (by revert r hr; decide)
  refine WP.seq (WP.mono (WP.gprs (rs := nvRegs) (Q := fun s' => (∃ c', c < c' ∧ Pending s₀ c' s') ∨ Done s₀ s')
    ?_ (by
      intro r hr i hi
      have : ((instrs (.ite (.zero .d .r30)
          (.seq (.block [.lsr .d .r8 .r29 6]) (.ite (.zero .d .r8) fill (.block direct))) fill :
          Prog isa)).all fun i => nvRegs.all fun r => dstOf i != some r) = true := by
        rw [← Code.allInstrs_eq]; decide +kernel
      simpa using List.all_eq_true.mp (List.all_eq_true.mp this i hi) r hr))
    fun s' ⟨h, hnv⟩ => ?_)
  · refine WP.ite (decide (rr s₀ c = 0))
      (by show VG.PPC64LE.eval (.zero .d .r30) s₁ = _; rw [eval_zero, hI₁.r30, ofNat_beq_zero (by omega)])
      (fun hb => ?_) (fun _ => fill_ok hp hI₁ hcl h10₁)
    simp only [decide_eq_true_eq] at hb
    refine WP.seq (wp_lsr (by decide) fun s₂ u₂ => WP.block_nil ?_)
    have hI₂ : Inv s₀ c s₂ := hI₁.of_gpr (fun r hr => u₂.other r (ne r hr).2) u₂.mem u₂.rd u₂.wr u₂.sp
    have h10₂ : s₂.gpr .r9 = 0 := by rw [u₂.other _ (by decide), h10₁]
    refine WP.ite (decide ((len s₀ - c) / 64 = 0))
      (by show VG.PPC64LE.eval (.zero .d .r8) s₂ = _
          rw [eval_zero, u₂.gpr, hI₁.r29, ofNat_shr6 (by omega), ofNat_beq_zero (by omega)])
      (fun _ => fill_ok hp hI₂ hcl h10₂) (fun hb' => ?_)
    simp only [decide_eq_false_iff_not] at hb'
    exact WP.mono (direct_ok hp hI₂ hb (by omega)) fun s' h => .inl ⟨c + 64, by omega, h⟩
  · have nv : ∀ r ∈ nvRegs, s'.gpr r = s.gpr r := fun r hr => (hnv r hr).trans (nv₁ r hr)
    rcases h with ⟨c', hc', hP⟩ | ⟨hD, h10⟩
    · refine WP.ite false (by show VG.PPC64LE.eval (.zero .d .r9) s' = _; rw [eval_zero, hP.r9]; rfl)
        (fun h => by cases h) fun _ => WP.mono (hP.compress_ok hp) fun s'' ⟨h, hpr⟩ =>
          ⟨⟨c', hc', h⟩, fun r hr => (hpr r (nv_pres r hr)).trans (nv r hr)⟩
    · refine WP.ite true (by show VG.PPC64LE.eval (.zero .d .r9) s' = _; rw [eval_zero, h10]; rfl)
        (fun _ => WP.block_nil ⟨⟨len s₀, hcl, hD⟩, nv⟩) fun h => by cases h

/-! ## Prologue and epilogue -/

/-- The prologue after saving. -/
def prologue : List Instr :=
  [mov .r26 .r3, mov .r27 .r7, mov .r28 .r5, mov .r29 .r6, .li .r8 63, .logic .and .r30 .r4 .r8]

theorem update_eq : updateMain = .seq (.block (save .r7 ++ prologue))
    (.seq (.ite (.zero .d .r29) (.block []) (.loop updateBody (.nonzero .d .r29))) (.block restore)) := rfl

theorem prologue_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block (save .r7 ++ prologue)) s₀ (Inv s₀ 0) := by
  refine save_ok (by decide) (fun d hd₁ hd₂ => ⟨scR s₀, by simp [hp.wr], contains_offset (by omega) (by omega)⟩)
    fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
  unfold prologue
  refine wp_mov fun s₂ u₂ => wp_mov fun s₃ u₃ => wp_mov fun s₄ u₄ => wp_mov fun s₅ u₅ =>
    wp_li (by decide) fun s₆ u₆ => wp_and fun s₇ u₇ => WP.block_nil ?_
  have hm₇ : s₇.mem = saveMem s₀.mem (scr s₀) s₀.gpr := by
    rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, m₁]
  refine ⟨⟨Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, fun iv m hm => ?_⟩
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
  · rw [u₇.gpr, u₆.gpr, u₆.other .r4 (by decide), u₅.other .r4 (by decide), u₄.other .r4 (by decide),
      u₃.other .r4 (by decide), u₂.other .r4 (by decide), g₁, and63, Nat.add_zero]
  · rw [List.take_zero, List.append_nil, hm₇]
    exact reprFrom_congr (fun i hi => frame_bytes (saveMem_frame s₀.mem (scr s₀) s₀.gpr) (R := stR s₀)
      (by simpa using hp.st_scr) (by simp) hi) hm.1

/-- The epilogue's postcondition. -/
def Post (s₀ s' : State) : Prop :=
  (∀ p ∈ saved, s'.gpr p.1 = s₀.gpr p.1) ∧ s'.sp = s₀.sp ∧ Proof.Sha256.updatePPC64LE.post s₀ s'

theorem epilogue_ok {s₀ : State} (hp : Pre s₀) {s : State} (hI : Inv s₀ (len s₀) s) :
    WP isa (.block restore) s (Post s₀) := by
  refine restore_ok (scr := scr s₀) hI.r27
    (fun d hd₁ hd₂ => ⟨scR s₀, by simp [hI.rd, hI.wr, hp.wr], contains_offset hd₂ (by omega)⟩) s₀.gpr
    hI.saved fun s' hs _ hmem _ _ hsp => ⟨hs, by rw [hsp, hI.sp], fun iv m hr hc => ?_⟩
  have := hI.repr iv m ⟨hr, hc⟩
  rwa [List.take_of_length_le (by rw [D_length]), ← hmem] at this

/-- No instruction of `updateMain` writes the callee-saved registers it does not save. -/
theorem untouched_ok : ∀ r ∈ untouched, ∀ i ∈ instrs updateMain, dstOf i ≠ some r := by
  have : ((instrs updateMain).all fun i => untouched.all fun r => dstOf i != some r) = true := by
    rw [← Code.allInstrs_eq]; decide +kernel
  intro r hr i hi
  have := List.all_eq_true.mp (List.all_eq_true.mp this i hi) r hr
  simpa using this

/-- `update` without its frame: the callee-saved registers are kept. -/
theorem correctMain {s₀ : State} (hp : Pre s₀) :
    WP isa updateMain s₀ fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧
      s'.sp = s₀.sp ∧ Proof.Sha256.updatePPC64LE.post s₀ s' := by
  have hlen := len_lt s₀
  refine WP.mono (WP.gprs (Q := fun (s' : State) => Post s₀ s' ∧ ∀ r ∈ nvRegs, s'.gpr r = s₀.gpr r) ?_
      untouched_ok)
    fun s' ⟨⟨⟨hsv, hsp, hpost⟩, hnv⟩, hu⟩ => ⟨fun r hr => ?_, hsp, hpost⟩
  · rw [update_eq]
    refine WP.seq (WP.mono (WP.gprs (rs := nvRegs) (prologue_ok hp) (by
        intro r hr i hi
        have : ((instrs (.block (save .r7 ++ prologue) : Prog isa)).all fun i =>
            nvRegs.all fun r => dstOf i != some r) = true := by decide
        simpa using List.all_eq_true.mp (List.all_eq_true.mp this i hi) r hr))
      fun s₁ ⟨hI, hnv₁⟩ => ?_)
    refine WP.seq (WP.mono (Q := fun (s : State) => Inv s₀ (len s₀) s ∧ ∀ r ∈ nvRegs, s.gpr r = s₀.gpr r) ?_
      fun s₂ ⟨hI₂, hnv₂⟩ => WP.mono (WP.gprs (rs := nvRegs) (epilogue_ok hp hI₂) (by decide))
        fun s₃ ⟨h, hnv₃⟩ => ⟨h, fun r hr => (hnv₃ r hr).trans (hnv₂ r hr)⟩)
    refine WP.ite (decide (len s₀ = 0))
      (by show VG.PPC64LE.eval (.zero .d .r29) s₁ = _
          rw [eval_zero, hI.r29, Nat.sub_zero, ofNat_beq_zero (by omega)])
      (fun hb => ?_) (fun hb => ?_)
    · simp only [decide_eq_true_eq] at hb
      exact WP.block_nil ⟨hb ▸ hI, hnv₁⟩
    · simp only [decide_eq_false_iff_not] at hb
      refine WP.loop (M := isa) (fun n s => ∃ c, n = len s₀ - c ∧ c < len s₀ ∧ Inv s₀ c s ∧
          ∀ r ∈ nvRegs, s.gpr r = s₀.gpr r) ?_ (len s₀) s₁
        ⟨0, rfl, by omega, hI, hnv₁⟩
      rintro n s ⟨c, rfl, hcl, hI, hnv⟩
      refine WP.mono (body_ok hp hI hcl) fun s' ⟨⟨c', hc, hI'⟩, hnv'⟩ => ?_
      have hnv'' : ∀ r ∈ nvRegs, s'.gpr r = s₀.gpr r := fun r hr => (hnv' r hr).trans (hnv r hr)
      have hc' := hI'.c_le
      have hz : isa.eval (.nonzero .d .r29) s' = some (decide (len s₀ - c' ≠ 0)) := by
        show VG.PPC64LE.eval (.nonzero .d .r29) s' = _
        rw [eval_nonzero, hI'.r29, bne, ofNat_beq_zero (by omega)]
        simp
      by_cases hl : len s₀ - c' = 0
      · refine .inl ⟨by rw [hz]; simp [hl], ?_, hnv''⟩
        rwa [show c' = len s₀ by omega] at hI'
      · exact .inr ⟨by rw [hz]; simp [hl], len s₀ - c', by omega, c', rfl, by omega, hI', hnv''⟩
  · have key : ∀ r ∈ preserved, r ∈ untouched ∨ r ∈ nvRegs ∨ r ∈ saved.map Prod.fst := by decide
    rcases key r hr with hr' | hr' | hr'
    · exact hu r hr'
    · exact hnv r hr'
    · obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hr'
      exact hsv p hp'

/-- The state `updateMain` starts in: the link register moved to `r0`, then
pushed in a frame. -/
abbrev inner (s₀ : State) : State := framed .r0 (s₀.write .r0 s₀.lr)

theorem correct {s₀ : State} (hp : Pre s₀) (hs : Stack s₀) :
    WP isa update s₀ fun s' => abiPreserved s₀ s' ∧ Proof.Sha256.updatePPC64LE.post s₀ s' := by
  have hpi : Pre (inner s₀) := ⟨hp.rd, hp.wr, hp.st_scr, hp.d_st, hp.d_scr⟩
  refine WP.seq (WP.cons exec_mflr (WP.block_nil (WP.seq ?_)))
  refine WP.frameReg (by exact hs.sp48) (fun R hR => ?_) (WP.mono (correctMain hpi)
    fun s' ⟨hk, hsp, hpost⟩ => ?_)
  · rw [show (s₀.write .r0 s₀.lr).wr = s₀.wr from rfl, hp.wr] at hR
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl
    · exact hs.st.sub_left (frame_sub _)
    · exact hs.scr.sub_left (frame_sub _)
  · refine WP.cons exec_mtlr (WP.block_nil ⟨⟨fun r hr => ?_, rfl, ?_⟩, fun iv m hm hc => ?_⟩)
    · have h0 : r ≠ .r0 := by revert r hr; decide
      simp only [State.write, h0, ite_false]
      rw [hk r hr]
      simp only [framed, State.write, h0, ite_false]
    · simp [State.write]
    · have e : bytesAt (inner s₀).mem (dp s₀) (len s₀) = bytesAt s₀.mem (dp s₀) (len s₀) :=
        bytesAt_congr fun i hi => write_frame_bytes hs.d (len_lt s₀) hi
      have := hpost iv m (reprFrom_congr (fun i hi => write_frame_bytes (R := stR s₀) hs.st
        (by simp) hi) hm) hc
      change Spec.Sha256.ReprFrom iv s'.mem (s₀.gpr .r3)
        (m ++ bytesAt (inner s₀).mem (s₀.gpr .r5) (s₀.gpr .r6).toNat) at this
      rw [e] at this
      exact this

theorem agree₀ {s₁ s₂ : State} (hpub : Proof.Sha256.updatePPC64LE.pub s₁ s₂) :
    VG.PPC64LE.Taint.Agree (VG.PPC64LE.Taint.ofRegs [.r3, .r4, .r5, .r6, .r7]) s₁ s₂ := by
  obtain ⟨p1, p2, p3, p4, p5, hsp⟩ := hpub
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.PPC64LE.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> assumption

/-- A state satisfying the precondition (with no data). -/
def sat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r5 => 0x2000 | .r7 => 0x3000 | _ => 0
  lr := 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, 96⟩, ⟨0x3000, 160⟩]

theorem update_verified : Verified PPC64LE.target update Proof.Sha256.updatePPC64LE := by
  refine ⟨fun s hs => ?_, ?_, ?_⟩
  · obtain ⟨t, s', he, h⟩ := correct (pre_of hs).1 (pre_of hs).2
    exact ⟨t, s', he, h⟩
  · exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7]) (fun _ _ _ _ hp => agree₀ hp)
      (by taint_decide)
  · refine ⟨sat, rfl, rfl, ?_, ?_, ?_, by decide, ?_, ?_, ?_⟩ <;>
    · intro a h₁ h₂
      simp only [Region.Contains, sat] at h₁ h₂
      bv_omega

end VG.Proof.Sha256.PPC64LE.Stream.Update
