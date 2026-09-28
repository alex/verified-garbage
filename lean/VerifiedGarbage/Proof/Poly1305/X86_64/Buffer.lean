import VerifiedGarbage.Proof.Poly1305.X86_64.Blocks
import VerifiedGarbage.Proof.Sha3.X86_64.Wp
import VerifiedGarbage.Proof.Sha3.Arith

/-!
# Poly1305 on x86-64: the buffer

Untrusted: everything here is checked by Lean. Bytes stored into the buffer
(bytes 56–71 of the state), absorbing the buffer as a block, and a message
with its last bytes buffered (`Buffered`) as its whole blocks and the rest.
-/

namespace VG.Proof.Poly1305.X86_64

open VG VG.X86_64 VG.Impl.Poly1305.X86_64
open VG.Spec.Poly1305 (P leNum bytesAt Repr Buffered)
open VG.Proof.Sha3.X86_64 (Upd wp_movzx8 wp_store8 wp_addi wp_subi)
open VG.Proof.Sha3 (ofNat_succ ofNat_pred ofNat_beq_zero)

/-! ## Bytes in memory -/

theorem off_56 (p : Addr) : off p 56 = p + 56 := by rw [off_eq]; rfl

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
      bv_omega
    simp only [this, h, ↓reduceIte]

theorem writeW64_zero_apply (m : Mem) (a x : Addr) :
    (m.writeW a (0 : BitVec 64)) x = if (x - a).toNat < 8 then 0 else m x := by
  simp only [Mem.writeW, Mem.write]
  split <;> simp

/-- Bytes outside a frame are unchanged. -/
theorem bytesAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, n⟩ : Region).Disjoint r) (hn : n ≤ 2 ^ 64) : bytesAt m' p n = bytesAt m p n := by
  simp only [bytesAt]
  apply List.map_congr_left
  intro i hi
  exact hf.bytes (R := ⟨p, n⟩) hd hn (List.mem_range.mp hi)

/-- `m` with the bytes `xs` written from `q` on. -/
def writeBytes (m : Mem) (q : Addr) (xs : List Byte) : Mem :=
  fun a => if (a - q).toNat < xs.length then xs.getD (a - q).toNat 0 else m a

theorem writeBytes_nil (m : Mem) (q : Addr) : writeBytes m q [] = m := by
  funext a; simp [writeBytes]

theorem writeBytes_snoc (m : Mem) (q : Addr) (xs : List Byte) (b : Byte) (h : xs.length < 2 ^ 64) :
    writeBytes m q (xs ++ [b]) = (writeBytes m q xs).writeW (q + BitVec.ofNat 64 xs.length) b := by
  funext a
  rw [writeW8_apply]
  simp only [writeBytes, List.length_append, List.length_singleton]
  by_cases ha : a = q + BitVec.ofNat 64 xs.length
  · subst ha
    rw [show q + BitVec.ofNat 64 xs.length - q = BitVec.ofNat 64 xs.length by bv_omega,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]
    simp [List.getD_eq_getElem?_getD]
  · have hne : (a - q).toNat ≠ xs.length := by
      intro h'
      apply ha
      have : a - q = BitVec.ofNat 64 xs.length :=
        BitVec.eq_of_toNat_eq (by rw [h', BitVec.toNat_ofNat, Nat.mod_eq_of_lt h])
      bv_omega
    simp only [ha, ite_false]
    by_cases hl : (a - q).toNat < xs.length
    · simp only [show (a - q).toNat < xs.length + 1 by omega, hl, ite_true]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hl]
    · simp only [show ¬ (a - q).toNat < xs.length + 1 by omega, hl, ite_false]

/-- The bytes before `q` (within `2⁶⁴ - |xs|`) are unchanged. -/
theorem writeBytes_before (m : Mem) (q : Addr) (xs : List Byte) {i d : Nat} (hi : i < d)
    (h : d + xs.length < 2 ^ 64) :
    writeBytes m (q + BitVec.ofNat 64 d) xs (q + BitVec.ofNat 64 i) = m (q + BitVec.ofNat 64 i) := by
  simp only [writeBytes]
  split
  · rename_i hc
    rw [show q + BitVec.ofNat 64 i - (q + BitVec.ofNat 64 d) = BitVec.ofNat 64 i - BitVec.ofNat 64 d by
      bv_omega, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := i) (by omega),
      Nat.mod_eq_of_lt (a := d) (by omega), show 2 ^ 64 - d + i = 2 ^ 64 - (d - i) by omega,
      Nat.mod_eq_of_lt (by omega)] at hc
    omega
  · rfl

/-- Bytes `[0, r)` from `p` stay, and the bytes `xs` follow them. -/
theorem bytesAt_writeBytes (m : Mem) (p : Addr) (r : Nat) (xs : List Byte) (h : r + xs.length < 2 ^ 64) :
    bytesAt (writeBytes m (p + BitVec.ofNat 64 r) xs) p (r + xs.length) = bytesAt m p r ++ xs := by
  simp only [bytesAt, List.range_add, List.map_append, List.map_map]
  congr 1
  · apply List.map_congr_left
    intro i hi
    have hi := List.mem_range.mp hi
    exact writeBytes_before m p xs hi (by omega)
  · apply List.ext_getElem (by simp)
    intro j h₁ h₂
    simp only [List.getElem_map, List.getElem_range, Function.comp, writeBytes]
    have hj : j < xs.length := by simpa using h₁
    rw [show p + BitVec.ofNat 64 (r + j) - (p + BitVec.ofNat 64 r) = BitVec.ofNat 64 j by
      simp only [BitVec.ofNat_add]; bv_omega, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    simp [hj, List.getD_eq_getElem?_getD]

theorem writeBytes_frame (m : Mem) (q : Addr) (xs : List Byte) {R : Region} (hR : R.Contains q xs.length) :
    Frame [R] m (writeBytes m q xs) := by
  intro x hx
  simp only [writeBytes]
  split
  · rename_i h; exact absurd (hR.byte h) (hx R (List.mem_singleton_self _))
  · rfl

/-! ## The buffer -/

/-- Byte `k` of the buffer. -/
abbrev bufB (st : Addr) (k : Nat) : Addr := st + BitVec.ofNat 64 (56 + k)

theorem bufB_eq (st : Addr) (k : Nat) : bufB st k = off st 56 + BitVec.ofNat 64 k := by
  rw [off_eq, BitVec.add_assoc, ← BitVec.ofNat_add]

/-- The address `[rdi + i + 56]`, for `i = j`. -/
theorem ea_bufAt (s : State) (i : Reg) {j : Nat} (h : s.gpr i = BitVec.ofNat 64 j) :
    s.ea (bufAt i) = bufB (s.gpr .rdi) j := by
  simp only [State.ea, bufAt, h]
  rw [BitVec.mul_one, show BitVec.ofInt 64 56 = BitVec.ofNat 64 56 by decide, bufB]
  bv_omega

theorem bfR_contains (st : Addr) {d n : Nat} (h : d + n ≤ 16) :
    (bfR st).Contains (off st 56 + BitVec.ofNat 64 d) n := by
  simp only [Region.Contains]
  rw [show off st 56 + BitVec.ofNat 64 d - off st 56 = BitVec.ofNat 64 d by bv_omega,
    toNat_ofNat_lt (by omega)]
  omega

theorem bufB_contains (st : Addr) {k : Nat} (hk : k < 16) : (bfR st).Contains (bufB st k) 1 := by
  rw [bufB_eq]; exact bfR_contains st (by omega)

theorem bufB_ne {st : Addr} {j k : Nat} (hj : j < 16) (hk : k < 16) (h : j ≠ k) :
    bufB st j ≠ bufB st k := by
  intro he
  have := congrArg BitVec.toNat (show BitVec.ofNat 64 (56 + j) = BitVec.ofNat 64 (56 + k) by
    simpa [bufB] using he)
  rw [toNat_ofNat_lt (by omega), toNat_ofNat_lt (by omega)] at this
  omega

/-- The buffer is writable when the state is. -/
theorem bufB_in {s : State} (hw : sR (s.gpr .rdi) ∈ s.wr) {k : Nat} (hk : k < 16) :
    InRegions s.wr (bufB (s.gpr .rdi) k) 1 :=
  ⟨_, hw, by rw [bufB, ← ofInt_natCast]; exact contains_off (by omega) (by omega)⟩

/-- The saved registers are not in the buffer. -/
theorem Saved.of_frame {st : Addr} {s₀ : State} {m m' : Mem} (h : Saved st s₀ m) (hf : Frame [bfR st] m m') :
    Saved st s₀ m' := by
  have e : ∀ d, 72 ≤ d → d + 8 ≤ 128 → m'.readW (off st d) 64 = m.readW (off st d) 64 := by
    intro d h₁ h₂
    refine hf.readW (r := ⟨off st d, 8⟩) (Region.contains_self _ _) ?_ (by decide)
    simp only [List.mem_singleton, forall_eq]
    intro a ha hb
    simp only [Region.Contains, off, ofInt_natCast] at ha hb
    bv_omega
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨(e 72 (by omega) (by omega)).trans h1, (e 80 (by omega) (by omega)).trans h2,
    (e 88 (by omega) (by omega)).trans h3, (e 96 (by omega) (by omega)).trans h4,
    (e 104 (by omega) (by omega)).trans h5, (e 112 (by omega) (by omega)).trans h6⟩

theorem bfR_disjoint_svR (st : Addr) : (bfR st).Disjoint (svR st) := by
  intro a h₁ h₂
  simp only [Region.Contains, off, ofInt_natCast] at h₁ h₂
  bv_omega

/-- The first `n` bytes of the buffer are not where the registers are saved. -/
theorem buf_disjoint_svR (st : Addr) {n : Nat} (hn : n ≤ 16) :
    (⟨off st 56, n⟩ : Region).Disjoint (svR st) :=
  (bfR_disjoint_svR st).sub_left (Region.sub_prefix hn)

theorem bfR_sub_wR (st : Addr) : Region.Sub (bfR st) (wR st) := by
  intro a ha
  simp only [Region.Contains, off, ofInt_natCast] at *
  bv_omega

/-- Absorbing the buffer: its 16 bytes, and `pad · 2¹²⁸`. -/
theorem absorbBuf_ok (s : State) {pad : BitVec 32} (hpad : pad = 0 ∨ pad = 1)
    (hw : sR (s.gpr .rdi) ∈ s.wr) {q : Nat} (hr0 : (s.gpr .r8).toNat < 2 ^ 60)
    (hr1 : (s.gpr .r9).toNat = 4 * q) (hq : q < 2 ^ 58) (hs1 : (s.gpr .r10).toNat = 5 * q) :
    WP isa (.block (absorbAt .rdi 56 pad)) s fun s' =>
      ((s.gpr .rbp).toNat ≤ 4 →
        hval s' % P = ((hval s + (leNum (bytesAt s.mem (off (s.gpr .rdi) 56) 16) + 2 ^ 128 * pad.toNat)) *
          ((s.gpr .r8).toNat + 2 ^ 64 * (s.gpr .r9).toNat)) % P ∧
        (s'.gpr .rbp).toNat ≤ 4) ∧ Keeps absorbRegs s s' := by
  have hin : ∀ d : Nat, d + 8 ≤ 128 → InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofInt 64 (d : Int)) 8 :=
    fun d hd => ⟨_, List.mem_append_right _ hw, contains_off hd (by omega)⟩
  refine WP.mono (absorbAt_ok s (b := .rdi) (d := 56) (by decide) hpad hr0 hr1 hq hs1 (hin 56 (by omega))
    (hin (56 + 8) (by omega))) fun s' ⟨ha, k⟩ => ⟨fun hb => ?_, k⟩
  obtain ⟨hv, hb'⟩ := ha hb
  refine ⟨?_, hb'⟩
  rw [hv, leNum_key, off_off, off_off]

/-! ## Instructions -/

theorem and15 (x : BitVec 64) :
    x &&& BitVec.signExtend 64 (15 : BitVec 32) = BitVec.ofNat 64 (x.toNat % 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (BitVec.signExtend 64 (15 : BitVec 32)).toNat = 2 ^ 4 - 1 by decide,
    Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := x.toNat % 16) (by omega)]

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_sub {d r : Reg}
    (k : ∀ s', Upd s s' d (s.gpr d - s.gpr r) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .sub d (.reg r) :: is)) s Q :=
  VG.Proof.Sha3.X86_64.WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _))

theorem wp_cmpi {d : Reg} {v : BitVec 32}
    (k : ∀ s', s'.gpr = s.gpr → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      s'.cf = some (decide ((s.gpr d).toNat < (v.signExtend 64).toNat)) →
      s'.zf = some (s.gpr d - v.signExtend 64 == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .cmp d (.imm v) :: is)) s Q :=
  VG.Proof.Sha3.X86_64.WP.cons rfl (k _ rfl rfl rfl rfl rfl rfl)

end

theorem se16' : BitVec.signExtend 64 (16 : BitVec 32) = BitVec.ofNat 64 16 := by decide

/-! ## Copying bytes into the buffer -/

/-- The copy loop's body. -/
def copyBody : List Instr :=
  [.movzx8 .r13 (at_ .rsi 0), .store8 (bufAt .r12) .r13, .alu .add .rsi (.imm 1),
    .alu .add .r12 (.imm 1), .alu .sub .rax (.imm 1)]

theorem copyIn_eq : copyIn = .loop (.block copyBody) .ne := rfl

/-- While copying the `n` bytes at `src`, as in the memory `m₀`, to the buffer
from byte `j0` on, from the state `sI`: after `j` bytes. -/
structure CopyInv (sI : State) (m₀ : Mem) (src : Addr) (j0 n j : Nat) (s : State) : Prop where
  j_le : j ≤ n
  rsi : s.gpr .rsi = src + BitVec.ofNat 64 j
  r12 : s.gpr .r12 = BitVec.ofNat 64 (j0 + j)
  rax : s.gpr .rax = BitVec.ofNat 64 (n - j)
  keep : ∀ r, r ≠ .rsi → r ≠ .r12 → r ≠ .rax → r ≠ .r13 → s.gpr r = sI.gpr r
  rd : s.rd = sI.rd
  wr : s.wr = sI.wr
  mem : s.mem = writeBytes sI.mem (bufB (sI.gpr .rdi) j0) ((bytesAt m₀ src n).take j)

/-- What copying needs of the source: its bytes are readable, not in the
buffer, and as in `m₀`. -/
def SrcOk (sI : State) (m₀ : Mem) (src : Addr) (n : Nat) : Prop :=
  ∀ i < n, InRegions (sI.rd ++ sI.wr) (src + BitVec.ofNat 64 i) 1 ∧
    ¬ (bfR (sI.gpr .rdi)).Contains (src + BitVec.ofNat 64 i) 1 ∧
    sI.mem (src + BitVec.ofNat 64 i) = m₀ (src + BitVec.ofNat 64 i)

theorem ofNat_add_one (a : Addr) (j : Nat) :
    a + BitVec.ofNat 64 j + BitVec.signExtend 64 (1 : BitVec 32) = a + BitVec.ofNat 64 (j + 1) := by
  rw [show BitVec.signExtend 64 (1 : BitVec 32) = 1 by decide, ofNat_succ, BitVec.add_assoc]

theorem copy_step {sI : State} {m₀ : Mem} {src : Addr} {j0 n : Nat} (hj0 : j0 + n ≤ 16)
    (hw : sR (sI.gpr .rdi) ∈ sI.wr) (hs : SrcOk sI m₀ src n) {j : Nat} (hj : j < n) {s : State}
    (h : CopyInv sI m₀ src j0 n j s) :
    WP isa (.block copyBody) s fun s' =>
      CopyInv sI m₀ src j0 n (j + 1) s' ∧ s'.zf = some (decide (n - (j + 1) = 0)) := by
  obtain ⟨hin, hnb, hm₀⟩ := hs j hj
  have hrdi : s.gpr .rdi = sI.gpr .rdi := h.keep _ (by decide) (by decide) (by decide) (by decide)
  have hxs : (bytesAt m₀ src n).length = n := Poly1305.length_bytesAt _ _ _
  have hq : (bfR (sI.gpr .rdi)).Contains (bufB (sI.gpr .rdi) j0) ((bytesAt m₀ src n).take j).length := by
    rw [bufB_eq, List.length_take]; exact bfR_contains _ (by omega)
  -- The byte read.
  have hbyte : s.mem (src + BitVec.ofNat 64 j) = m₀ (src + BitVec.ofNat 64 j) := by
    rw [h.mem, ← hm₀]
    exact writeBytes_frame _ _ _ hq _ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hnb
  refine wp_movzx8 (d := .r13) (a := src + BitVec.ofNat 64 j)
    (by rw [ea_at, h.rsi, ofInt_natCast, BitVec.add_zero]) (by rw [h.rd, h.wr]; exact hin)
    fun s₁ u₁ => ?_
  refine wp_store8 (r := .r13) (a := bufB (sI.gpr .rdi) (j0 + j))
    (by rw [ea_bufAt s₁ .r12 (by rw [u₁.other _ (by decide), h.r12]), u₁.other _ (by decide), hrdi])
    (by rw [u₁.wr, h.wr]; exact bufB_in hw (by omega)) fun s₂ g₂ m₂ rd₂ wr₂ => ?_
  refine wp_addi fun s₃ u₃ => wp_addi fun s₄ u₄ => wp_subi fun s₅ u₅ hz₅ => WP.block_nil ?_
  have g : ∀ r, r ≠ .rax → r ≠ .r12 → r ≠ .rsi → r ≠ .r13 → s₅.gpr r = s.gpr r :=
    fun r h1 h2 h3 h4 => by rw [u₅.other r h1, u₄.other r h2, u₃.other r h3, g₂, u₁.other r h4]
  have e1 : BitVec.signExtend 64 (1 : BitVec 32) = 1 := by decide
  have hrax : s₅.gpr .rax = BitVec.ofNat 64 (n - (j + 1)) := by
    rw [u₅.gpr, u₄.other .rax (by decide), u₃.other .rax (by decide), g₂, u₁.other .rax (by decide), h.rax,
      e1, ofNat_pred (by omega), Nat.sub_sub]
  refine ⟨⟨by omega, ?_, ?_, hrax, fun r h1 h2 h3 h4 => ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [u₅.other .rsi (by decide), u₄.other .rsi (by decide), u₃.gpr, g₂, u₁.other .rsi (by decide), h.rsi,
      ofNat_add_one]
  · rw [u₅.other .r12 (by decide), u₄.gpr, u₃.other .r12 (by decide), g₂, u₁.other .r12 (by decide), h.r12,
      e1, ← Nat.add_assoc, ofNat_succ]
  · rw [g r h3 h2 h1 h4, h.keep r h1 h2 h3 h4]
  · rw [u₅.rd, u₄.rd, u₃.rd, rd₂, u₁.rd, h.rd]
  · rw [u₅.wr, u₄.wr, u₃.wr, wr₂, u₁.wr, h.wr]
  · have hj' : j < (bytesAt m₀ src n).length := by omega
    have hl : ((bytesAt m₀ src n).take j).length = j := by rw [List.length_take, Nat.min_eq_left hj'.le]
    have ea : bufB (sI.gpr .rdi) (j0 + j) =
        bufB (sI.gpr .rdi) j0 + BitVec.ofNat 64 ((bytesAt m₀ src n).take j).length := by
      rw [hl, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_assoc]
    have hv : (BitVec.setWidth 64 (s.mem (src + BitVec.ofNat 64 j))).setWidth 8 = (bytesAt m₀ src n)[j] := by
      rw [BitVec.setWidth_setWidth_of_le _ (by omega), BitVec.setWidth_eq, hbyte]; simp [bytesAt]
    rw [u₅.mem, u₄.mem, u₃.mem, m₂, u₁.mem, u₁.gpr, hv, ea, h.mem, List.take_add_one,
      List.getElem?_eq_getElem hj', Option.toList_some, writeBytes_snoc _ _ _ _ (by omega)]
  · rw [hz₅, u₄.other .rax (by decide), u₃.other .rax (by decide), g₂, u₁.other .rax (by decide), h.rax, e1,
      ofNat_pred (by omega), ofNat_beq_zero (by omega), show n - j - 1 = n - (j + 1) by omega]

theorem copy_ok {sI : State} {m₀ : Mem} {src : Addr} {j0 n : Nat} (hj0 : j0 + n ≤ 16) (hn : 0 < n)
    (hw : sR (sI.gpr .rdi) ∈ sI.wr) (hs : SrcOk sI m₀ src n) (hrsi : sI.gpr .rsi = src)
    (hr12 : sI.gpr .r12 = BitVec.ofNat 64 j0) (hrax : sI.gpr .rax = BitVec.ofNat 64 n) :
    WP isa copyIn sI (CopyInv sI m₀ src j0 n n) := by
  have h₀ : CopyInv sI m₀ src j0 n 0 sI :=
    ⟨by omega, by rw [hrsi]; simp, by rw [hr12]; simp, by rw [hrax]; simp, fun _ _ _ _ _ => rfl, rfl, rfl,
      by rw [List.take_zero, writeBytes_nil]⟩
  rw [copyIn_eq]
  refine WP.loop (M := isa) (fun k s => ∃ j, k = n - j ∧ j < n ∧ CopyInv sI m₀ src j0 n j s)
    ?_ n sI ⟨0, rfl, hn, h₀⟩
  rintro k s ⟨j, rfl, hj, hc⟩
  refine WP.mono (copy_step hj0 hw hs hj hc) fun s' ⟨hc', hz⟩ => ?_
  by_cases hl : n - (j + 1) = 0
  · refine .inl ⟨by simp [eval, hz, hl], ?_⟩
    rwa [show j + 1 = n by omega] at hc'
  · exact .inr ⟨by simp [eval, hz, hl], _, by omega, j + 1, rfl, by omega, hc'⟩

/-- After copying: the buffer's first `j0` bytes and the `n` bytes copied. -/
theorem CopyInv.buf {sI : State} {m₀ : Mem} {src : Addr} {j0 n : Nat} (hj0 : j0 + n ≤ 16) {s : State}
    (h : CopyInv sI m₀ src j0 n n s) :
    bytesAt s.mem (off (sI.gpr .rdi) 56) (j0 + n) = bytesAt sI.mem (off (sI.gpr .rdi) 56) j0 ++ bytesAt m₀ src n := by
  have hxs : (bytesAt m₀ src n).length = n := Poly1305.length_bytesAt _ _ _
  have e := bytesAt_writeBytes sI.mem (off (sI.gpr .rdi) 56) j0 (bytesAt m₀ src n) (by omega)
  rw [hxs] at e
  rw [h.mem, List.take_of_length_le (by omega), bufB_eq]
  exact e

theorem CopyInv.frame {sI : State} {m₀ : Mem} {src : Addr} {j0 n : Nat} (hj0 : j0 + n ≤ 16) {s : State}
    (h : CopyInv sI m₀ src j0 n n s) : Frame [bfR (sI.gpr .rdi)] sI.mem s.mem := by
  have hxs : (bytesAt m₀ src n).length = n := Poly1305.length_bytesAt _ _ _
  rw [h.mem, List.take_of_length_le (by omega)]
  refine writeBytes_frame _ _ _ ?_
  rw [bufB_eq, hxs]; exact bfR_contains _ hj0

/-! ## Whole blocks and the rest -/

theorem take_whole {a b : List Byte} (ha : a.length % 16 = 0) (hb : b.length < 16) :
    (a ++ b).take (16 * ((a ++ b).length / 16)) = a := by
  rw [show 16 * ((a ++ b).length / 16) = a.length by simp only [List.length_append]; omega,
    List.take_left' rfl]

theorem drop_whole {a b : List Byte} (ha : a.length % 16 = 0) (hb : b.length < 16) :
    (a ++ b).drop (16 * ((a ++ b).length / 16)) = b := by
  rw [show 16 * ((a ++ b).length / 16) = a.length by simp only [List.length_append]; omega,
    List.drop_left' rfl]

/-- A message with its last bytes buffered: its whole blocks, which the
state represents as `Repr` does, and the buffered bytes. -/
theorem Buffered.split {m : Mem} {st : Addr} {key msg : List Byte} (h : Buffered m st key msg) :
    ∃ w b, msg = w ++ b ∧ Repr m st key w ∧ b.length = msg.length % 16 ∧
      bytesAt m (st + 56) (msg.length % 16) = b :=
  ⟨_, _, (List.take_append_drop _ _).symm, h.1, by simp only [List.length_drop]; omega, h.2⟩

theorem Buffered.of {m : Mem} {st : Addr} {key w b : List Byte} (hr : Repr m st key w) (hb : b.length < 16)
    (hbuf : bytesAt m (st + 56) b.length = b) : Buffered m st key (w ++ b) := by
  have hw := hr.1
  refine ⟨by rw [take_whole hw hb]; exact hr, ?_⟩
  rw [drop_whole hw hb, show (w ++ b).length % 16 = b.length by simp only [List.length_append]; omega]
  exact hbuf

/-- A message of whole blocks, with nothing buffered. -/
theorem Repr.buffered {m : Mem} {st : Addr} {key msg : List Byte} (h : Repr m st key msg) :
    Buffered m st key msg := by
  have e := Buffered.of (b := []) h (by simp) rfl
  rwa [List.append_nil] at e

end VG.Proof.Poly1305.X86_64
