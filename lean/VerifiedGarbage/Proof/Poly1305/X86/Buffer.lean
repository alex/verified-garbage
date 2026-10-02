import VerifiedGarbage.Proof.Poly1305.X86.Blocks
import VerifiedGarbage.Proof.Poly1305.Stream
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Poly1305 on x86 (32-bit): the buffer

The buffer (bytes 56–71 of the state, words 14 to 17), bytes copied into it,
absorbing it as a block, and what `update` and `finalize` share: the number of
bytes buffered, from `count`.
-/

open VG.PowLit

namespace VG.Proof.Poly1305.X86

open VG VG.X86 VG.Impl.Poly1305.X86
open VG.Spec.Poly1305 (P leNum bytesAt Repr Buffered)

/-! ## Addresses -/

/-- The buffer's address, and its region. -/
abbrev bq (st : BitVec 32) : Addr := addr st 56
abbrev bfR (st : BitVec 32) : Region := sub st 56 16

theorem bq_eq {st : BitVec 32} (hfit : st.toNat + 128 ≤ 2 ^ 32) : bq st = st.setWidth 64 + 56 := by
  rw [bq, addr_eq (by omega_using [hfit])]; rfl

/-- Byte `k` of the buffer. -/
theorem bufB_eq {st : BitVec 32} (hfit : st.toNat + 128 ≤ 2 ^ 32) {k : Nat} (hk : k ≤ 16) :
    addr st (56 + k) = bq st + BitVec.ofNat 64 k := by
  rw [bq, addr_eq (by omega_using [hfit, hk]), addr_eq (by omega_using [hfit]), BitVec.add_assoc, ← BitVec.ofNat_add]

/-- The address `[x + 56]`, for `x = st + k`. -/
theorem addr_buf {st : BitVec 32} (hfit : st.toNat + 128 ≤ 2 ^ 32) {k : Nat} (hk : k ≤ 16) :
    addr (st + BitVec.ofNat 32 k) 56 = bq st + BitVec.ofNat 64 k := by
  rw [← bufB_eq hfit hk]
  simp only [addr]
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_comm]

theorem bfR_contains {d n : Nat} (st : BitVec 32) (h : d + n ≤ 16) :
    (bfR st).Contains (bq st + BitVec.ofNat 64 d) n := by
  exact Offset.contains_base _ h (by omega_using [h])

theorem bfR_sub {st : BitVec 32} (hfit : st.toNat + 128 ≤ 2 ^ 32) : Region.Sub (bfR st) (sR st) :=
  fun _ ha => (sR_contains hfit (d := 56) (n := 16) (by decide) (by decide)).byte (by
    simp only [Region.Contains] at ha; omega_using [ha])

/-- The words outside the buffer, after writes only to it. -/
theorem words_bf {st : BitVec 32} (hfit : st.toNat + 128 ≤ 2 ^ 32) {m m' : Mem} (hf : Frame [bfR st] m m')
    {k : Nat} (hk : k < 32) (h : k < 14 ∨ 18 ≤ k) : words m' st k = words m st k := by
  show wv _ _ _ = wv _ _ _
  rw [wv, wv, wd_frame hf (by
    simp only [List.mem_singleton]; rintro r rfl
    exact sub_disj (by omega_using [hfit, hk]) (by omega_using [hfit]) (by omega_using [hk, h]))]

/-- The first `n` bytes of the buffer, where its words are unchanged. -/
theorem bytes_words {st : BitVec 32} (hfit : st.toNat + 128 ≤ 2 ^ 32) {m m' : Mem}
    (h : ∀ k, 14 ≤ k → k < 18 → words m' st k = words m st k) {n : Nat} (hn : n ≤ 16) :
    bytesAt m' (bq st) n = bytesAt m (bq st) n := by
  have e : bytesAt m' (bq st) (4 * 4) = bytesAt m (bq st) (4 * 4) :=
    bytesAt_congr_words fun k hk => BitVec.eq_of_toNat_eq (by
      have := h (14 + k) (by omega_using [hk]) (by omega_using [hk])
      simp only [words, wv, wd] at this
      rw [bq, addr_eq (by omega_using [hfit]), add_ofNat_add, ← addr_eq (by omega_using [hfit, hk]), show 56 + 4 * k = 4 * (14 + k) by omega_using []]
      exact this)
  have t : ∀ m'' : Mem, bytesAt m'' (bq st) n = (bytesAt m'' (bq st) (4 * 4)).take n := fun m'' => by
    rw [show 4 * 4 = n + (16 - n) by omega_using [hn], Poly1305.bytesAt_add, List.take_left' (Poly1305.length_bytesAt _ _ _)]
  rw [t, t, e]

/-- The buffer's words, as `absorbAt .edi 56` reads them. -/
theorem buf_ea {st : BitVec 32} (k : Nat) :
    addr st (56 + 4 * k) = addr (st + BitVec.ofNat 32 56) (4 * k) := by
  simp only [addr]; rw [BitVec.add_assoc, ← BitVec.ofNat_add]

/-- The buffer's value as a block: its four words, as `absorbAt .edi 56` reads
them. -/
theorem buf_value {st : BitVec 32} (hfit : st.toNat + 128 ≤ 2 ^ 32) (m : Mem) (pad : Nat) :
    blkv m (st + BitVec.ofNat 32 56) pad = leNum (bytesAt m (bq st) 16) + 2 ^ 128 * pad := by
  have hw : ∀ k < 4, wv m (st + BitVec.ofNat 32 56) (4 * k) = w32 m (bq st) k := fun k hk => by
    simp only [wv, wd, w32]
    rw [← buf_ea, bufB_eq hfit (by omega_using [hk])]
  rw [leNum_bytesAt_16, ← hw 0 (by decide), ← hw 1 (by decide), ← hw 2 (by decide), ← hw 3 (by decide)]

/-! ## The number of bytes buffered -/

theorem and15 (x : BitVec 32) : x &&& 15 = BitVec.ofNat 32 (x.toNat % 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (15 : BitVec 32).toNat = 2 ^ 4 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := x.toNat % 16) (by omega_using [])]

theorem count_mod (s : State) : (Proof.Poly1305.countX86 s).toNat % 16 = (arg s 1).toNat % 16 := by
  simp only [Proof.Poly1305.countX86]
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt (arg s 1).isLt, Nat.shiftLeft_eq]
  omega_using []

section
variable (s₀ : State)
/-- The number of bytes buffered, `count mod 16`. -/
abbrev kb : Nat := (arg s₀ 1).toNat % 16
/-- The bytes buffered. -/
abbrev Bf : List Byte := bytesAt s₀.mem (bq (stp s₀)) (kb s₀)
end

theorem kb_lt (s₀ : State) : kb s₀ < 16 := Nat.mod_lt _ (by decide)

/-- The length of a message of `count` bytes, modulo 16. -/
theorem count_mod16 {count : BitVec 64} {n : Nat} (h : count = BitVec.ofNat 64 n) :
    count.toNat % 16 = n % 16 := by
  rw [h, BitVec.toNat_ofNat]; omega_using []

/-- A state representing a message of `count` bytes (modulo 16): its whole
blocks, and the bytes buffered. -/
theorem buffered_split {s₀ : State} (hfit : (stp s₀).toNat + 128 ≤ 2 ^ 32) {key msg : List Byte}
    (h : Buffered s₀.mem ((stp s₀).setWidth 64) key msg)
    (hc : (Proof.Poly1305.countX86 s₀).toNat % 16 = msg.length % 16) :
    ∃ W, msg = W ++ Bf s₀ ∧ Repr s₀.mem ((stp s₀).setWidth 64) key W := by
  obtain ⟨W, B, rfl, hr, -, hBb⟩ := Buffered.split h
  have hk : kb s₀ = (W ++ B).length % 16 := by
    rw [kb, ← count_mod, hc]
  refine ⟨W, ?_, hr⟩
  rw [Bf, hk, bq_eq hfit, hBb]

theorem eq16_beq {a : Nat} (ha : a ≤ 16) : (BitVec.ofNat 32 a - 16 == 0) = decide (a = 16) := by
  by_cases h : a = 16
  · subst h; rfl
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro h'
    have := congrArg BitVec.toNat h'
    rw [show (0 : BitVec 32).toNat = 0 from rfl] at this
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at this
    rw [show (16 : BitVec 32).toNat = 16 from rfl, Nat.mod_eq_of_lt (a := a) (by omega_using [ha, this])] at this
    omega_using [ha, h, this]

/-! ## What holds throughout `update` and `finalize` -/

/-- What holds throughout, with the words `F` of `setup`. -/
structure UCommon (s₀ : State) (F : Nat → Nat) (s : State) : Prop where
  ctx : Ctx (stp s₀) s
  esp : s.gpr .esp = s₀.gpr .esp
  frame : Frame [sR (stp s₀)] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  keep : ∀ k < 32, k ∉ hS → (k < 14 ∨ 18 ≤ k) → words s.mem (stp s₀) k = F k

theorem UCommon.regs {s₀ s s' : State} {F : Nat → Nat} (h : UCommon s₀ F s) (hedi : s'.gpr .edi = s.gpr .edi)
    (hesp : s'.gpr .esp = s.gpr .esp) (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    UCommon s₀ F s' :=
  ⟨h.ctx.keep hedi hwr, hesp.trans h.esp, hm ▸ h.frame, hrd.trans h.rd, hwr.trans h.wr,
    fun k hk hS h' => hm ▸ h.keep k hk hS h'⟩

/-- Writing the buffer keeps what holds throughout. -/
theorem UCommon.buf {s₀ s s' : State} {F : Nat → Nat} (h : UCommon s₀ F s) (hedi : s'.gpr .edi = s.gpr .edi)
    (hesp : s'.gpr .esp = s.gpr .esp) (hf : Frame [bfR (stp s₀)] s.mem s'.mem) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) (hfit : (stp s₀).toNat + 128 ≤ 2 ^ 32) : UCommon s₀ F s' :=
  ⟨h.ctx.keep hedi hwr, hesp.trans h.esp,
    h.frame.trans (hf.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, bfR_sub hfit⟩),
    hrd.trans h.rd, hwr.trans h.wr, fun k hk hS h' => (words_bf hfit hf hk h').trans (h.keep k hk hS h')⟩

/-- The accumulator in the state's words is that of the message on entry
followed by the whole blocks `X`. -/
def Acc (s₀ : State) (X : List Byte) (m : Mem) : Prop :=
  A0 s₀ < P → words m (stp s₀) 4 ≤ 4 ∧
    hw5 (words m (stp s₀)) % P = Poly1305.absorbAll (Rn s₀) (A0 s₀) X % P

theorem Acc.words {s₀ : State} {X : List Byte} {m m' : Mem} (h : Acc s₀ X m)
    (hk : ∀ k < 5, words m' (stp s₀) k = words m (stp s₀) k) : Acc s₀ X m' := fun hA => by
  obtain ⟨h4, hv⟩ := h hA
  refine ⟨by rw [hk 4 (by decide)]; exact h4, ?_⟩
  simp only [hw5, hk 0 (by decide), hk 1 (by decide), hk 2 (by decide), hk 3 (by decide), hk 4 (by decide)]
  exact hv

/-! ## Copying bytes into the buffer -/

/-- The copy loop's body. -/
def copyBody : List Instr :=
  [.movzx8 .ecx (at_ .esi 0), .store8 (at_ .edx 56) .cl, .alu .add .esi (.imm 1),
    .alu .add .edx (.imm 1), .alu .sub .eax (.imm 1)]

theorem copyIn_eq : copyIn = .loop (.block copyBody) .ne := rfl

/-- While copying the `n` bytes at `src`, as in the memory `m₀`, to the buffer
of the state at `st` from byte `j0` on, from the state `sI`: after `j` bytes. -/
structure CopyInv (sI : State) (st : BitVec 32) (m₀ : Mem) (src : BitVec 32) (j0 n j : Nat) (s : State) :
    Prop where
  j_le : j ≤ n
  esi : s.gpr .esi = src + BitVec.ofNat 32 j
  edx : s.gpr .edx = st + BitVec.ofNat 32 (j0 + j)
  eax : s.gpr .eax = BitVec.ofNat 32 (n - j)
  keep : ∀ r, r ≠ .esi → r ≠ .edx → r ≠ .eax → r ≠ .ecx → s.gpr r = sI.gpr r
  rd : s.rd = sI.rd
  wr : s.wr = sI.wr
  mem : s.mem = Poly1305.writeBytes sI.mem (bq st + BitVec.ofNat 64 j0)
    ((bytesAt m₀ (src.setWidth 64) n).take j)

/-- What copying needs of the source: its bytes are readable, not in the
buffer, and as in `m₀`. -/
def SrcOk (sI : State) (st : BitVec 32) (m₀ : Mem) (src : BitVec 32) (n : Nat) : Prop :=
  src.toNat + n ≤ 2 ^ 32 ∧ ∀ i < n, InRegions (sI.rd ++ sI.wr) (addr src i) 1 ∧
    ¬ (bfR st).Contains (addr src i) 1 ∧ sI.mem (addr src i) = m₀ (addr src i)

theorem ofNat32_pred {k : Nat} (h : 1 ≤ k) (hk : k < 2 ^ 32) :
    BitVec.ofNat 32 k - 1 = BitVec.ofNat 32 (k - 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  rw [show (1 : BitVec 32).toNat = 1 from rfl]
  omega_using [h, hk]

theorem copy_step {sI : State} {st : BitVec 32} {m₀ : Mem} {src : BitVec 32} {j0 n : Nat}
    (hfit : st.toNat + 128 ≤ 2 ^ 32) (hj0 : j0 + n ≤ 16) (hw : sR st ∈ sI.wr) (hs : SrcOk sI st m₀ src n)
    {j : Nat} (hj : j < n) {s : State} (h : CopyInv sI st m₀ src j0 n j s) :
    WP isa (.block copyBody) s fun s' =>
      CopyInv sI st m₀ src j0 n (j + 1) s' ∧ s'.zf = some (decide (n - (j + 1) = 0)) := by
  obtain ⟨hsf, hsrc⟩ := hs
  obtain ⟨hin, hnb, hm₀⟩ := hsrc j hj
  have hxs : (bytesAt m₀ (src.setWidth 64) n).length = n := Poly1305.length_bytesAt _ _ _
  have hq : (bfR st).Contains (bq st + BitVec.ofNat 64 j0) ((bytesAt m₀ (src.setWidth 64) n).take j).length := by
    rw [List.length_take]
    exact bfR_contains st (by omega_using [hj0, hj, hxs])
  -- The byte read.
  have hbyte : s.mem (addr src j) = m₀ (addr src j) := by
    rw [h.mem, ← hm₀]
    exact Poly1305.writeBytes_frame _ _ _ hq _ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hnb
  refine wp_movzx8 (d := .ecx) (a := addr src j)
    (by rw [ea_at, h.esi]; simp only [addr]; rw [BitVec.add_zero]) (by rw [h.rd, h.wr]; exact hin)
    fun s₁ u₁ => ?_
  refine wp_store8 (r := .cl) (a := bq st + BitVec.ofNat 64 (j0 + j))
    (by rw [ea_at, u₁.other _ (by decide), h.edx, addr_buf hfit (by omega_using [hj0, hj, hxs])])
    (by rw [u₁.wr, h.wr]; exact ⟨_, hw, (bfR_sub hfit) _ (bfR_contains st (d := j0 + j) (n := 1) (by omega_using [hj0, hj, hxs]))⟩) fun s₂ m₂ => ?_
  refine wp_addx (readSrc_imm _ _) fun s₃ u₃ _ => wp_addx (readSrc_imm _ _) fun s₄ u₄ _ => ?_
  refine wp_subx (readSrc_imm _ _) fun s₅ u₅ hz₅ => WP.block_nil ?_
  have g : ∀ r, r ≠ .eax → r ≠ .edx → r ≠ .esi → r ≠ .ecx → s₅.gpr r = s.gpr r :=
    fun r h1 h2 h3 h4 => by rw [u₅.other r h1, u₄.other r h2, u₃.other r h3, m₂.gpr, u₁.other r h4]
  have heax : s₅.gpr .eax = BitVec.ofNat 32 (n - (j + 1)) := by
    rw [u₅.gpr, u₄.other .eax (by decide), u₃.other .eax (by decide), m₂.gpr, u₁.other .eax (by decide), h.eax,
      ofNat32_pred (by omega_using [hj, hxs]) (by omega_using [hj0, hj, hxs]), Nat.sub_sub]
  refine ⟨⟨by omega_using [hj, hxs], ?_, ?_, heax, fun r h1 h2 h3 h4 => ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [u₅.other .esi (by decide), u₄.other .esi (by decide), u₃.gpr, m₂.gpr, u₁.other .esi (by decide), h.esi,
      BitVec.add_assoc, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, ← BitVec.ofNat_add]
  · rw [u₅.other .edx (by decide), u₄.gpr, u₃.other .edx (by decide), m₂.gpr, u₁.other .edx (by decide), h.edx,
      BitVec.add_assoc, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, ← BitVec.ofNat_add, Nat.add_assoc]
  · rw [g r h3 h2 h1 h4, h.keep r h1 h2 h3 h4]
  · rw [u₅.rd, u₄.rd, u₃.rd, m₂.rd, u₁.rd, h.rd]
  · rw [u₅.wr, u₄.wr, u₃.wr, m₂.wr, u₁.wr, h.wr]
  · have hj' : j < (bytesAt m₀ (src.setWidth 64) n).length := by omega_using [hj, hxs]
    have hl : ((bytesAt m₀ (src.setWidth 64) n).take j).length = j := by
      rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj')]
    have ea : bq st + BitVec.ofNat 64 (j0 + j) =
        bq st + BitVec.ofNat 64 j0 + BitVec.ofNat 64 ((bytesAt m₀ (src.setWidth 64) n).take j).length := by
      rw [hl, BitVec.add_assoc, ← BitVec.ofNat_add]
    have haddr : addr src j = src.setWidth 64 + BitVec.ofNat 64 j := addr_eq (by omega_using [hj, hsf, hxs, hl])
    have hv : (BitVec.setWidth 32 (s.mem (addr src j))).setWidth 8 = (bytesAt m₀ (src.setWidth 64) n)[j] := by
      rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq, hbyte, haddr]; simp [bytesAt]
    rw [u₅.mem, u₄.mem, u₃.mem, m₂.mem, show Reg8.cl.reg = Reg.ecx from rfl, u₁.gpr, hv, ea, u₁.mem, h.mem, List.take_add_one,
      List.getElem?_eq_getElem hj', Option.toList_some, Poly1305.writeBytes_snoc _ _ _ _ (by omega_using [hj0, hj, hxs, hl])]
  · rw [hz₅, u₄.other .eax (by decide), u₃.other .eax (by decide), m₂.gpr, u₁.other .eax (by decide), h.eax,
      ofNat32_pred (by omega_using [hj, hxs]) (by omega_using [hj0, hj, hxs]), ofNat32_beq_zero (by omega_using [hj0, hj, hxs]), show n - j - 1 = n - (j + 1) by omega_using []]

theorem copy_ok {sI : State} {st : BitVec 32} {m₀ : Mem} {src : BitVec 32} {j0 n : Nat}
    (hfit : st.toNat + 128 ≤ 2 ^ 32) (hj0 : j0 + n ≤ 16) (hn : 0 < n) (hw : sR st ∈ sI.wr)
    (hs : SrcOk sI st m₀ src n) (hesi : sI.gpr .esi = src) (hedx : sI.gpr .edx = st + BitVec.ofNat 32 j0)
    (heax : sI.gpr .eax = BitVec.ofNat 32 n) :
    WP isa copyIn sI (CopyInv sI st m₀ src j0 n n) := by
  have h₀ : CopyInv sI st m₀ src j0 n 0 sI :=
    ⟨by omega_using [hn], by rw [hesi]; simp, by rw [hedx, Nat.add_zero], by rw [heax, Nat.sub_zero], fun _ _ _ _ _ => rfl, rfl, rfl,
      by rw [List.take_zero, Poly1305.writeBytes_nil]⟩
  rw [copyIn_eq]
  refine WP.loop (M := isa) (fun k s => ∃ j, k = n - j ∧ j < n ∧ CopyInv sI st m₀ src j0 n j s)
    ?_ n sI ⟨0, rfl, hn, h₀⟩
  rintro k s ⟨j, rfl, hj, hc⟩
  refine WP.mono (copy_step hfit hj0 hw hs hj hc) fun s' ⟨hc', hz⟩ => ?_
  by_cases hl : n - (j + 1) = 0
  · refine .inl ⟨by simp [eval, hz, hl], ?_⟩
    rwa [show j + 1 = n by omega_using [hj, hl]] at hc'
  · exact .inr ⟨by simp [eval, hz, hl], _, by omega_using [hj], j + 1, rfl, by omega_using [hj, hl], hc'⟩

/-- After copying: the buffer's first `j0` bytes and the `n` bytes copied. -/
theorem CopyInv.buf {sI : State} {st : BitVec 32} {m₀ : Mem} {src : BitVec 32} {j0 n : Nat} (hj0 : j0 + n ≤ 16)
    {s : State} (h : CopyInv sI st m₀ src j0 n n s) :
    bytesAt s.mem (bq st) (j0 + n) = bytesAt sI.mem (bq st) j0 ++ bytesAt m₀ (src.setWidth 64) n := by
  have hxs : (bytesAt m₀ (src.setWidth 64) n).length = n := Poly1305.length_bytesAt _ _ _
  have e := Poly1305.bytesAt_writeBytes sI.mem (bq st) j0 (bytesAt m₀ (src.setWidth 64) n) (by omega_using [hj0, hxs])
  rw [hxs] at e
  rw [h.mem, List.take_of_length_le (by omega_using [hxs])]
  exact e

theorem CopyInv.frame {sI : State} {st : BitVec 32} {m₀ : Mem} {src : BitVec 32} {j0 n : Nat}
    (hj0 : j0 + n ≤ 16) {s : State} (h : CopyInv sI st m₀ src j0 n n s) :
    Frame [bfR st] sI.mem s.mem := by
  have hxs : (bytesAt m₀ (src.setWidth 64) n).length = n := Poly1305.length_bytesAt _ _ _
  rw [h.mem, List.take_of_length_le (by omega_using [hxs])]
  refine Poly1305.writeBytes_frame _ _ _ ?_
  rw [hxs]
  exact bfR_contains st hj0

end VG.Proof.Poly1305.X86
