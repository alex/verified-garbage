import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Rc2.Stream
import VerifiedGarbage.Impl.Rc2.X86.Stream

/-!
# Streaming RC2-CBC on x86 (32-bit): copying bytes

Untrusted: everything here is checked by Lean. Addresses `[x + d]` within
the 32-bit address space, the bytes a copy leaves, and the loop copying
`ecx` bytes from `esi + sd` to `edx + dd` (`copy_ok`), which every copy of
`init` and the updates uses.
-/

namespace VG.Proof.Rc2.X86.Stream

open VG VG.X86 VG.X86.Wp
open VG.WriteBytes (writeBytes writeBytes_snoc writeBytes_frame writeBytes_nil writeBytes_before)

/-! ## Addresses -/

theorem toNat_sw (x : BitVec 32) : (x.setWidth 64).toNat = x.toNat := by
  simp only [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by have := x.isLt; omega)

/-- `[(x + k) + d]`, where nothing wraps around the 32-bit address space. -/
theorem addr_add {x : BitVec 32} {k d : Nat} (h : x.toNat + k + d < 2 ^ 32) :
    addr (x + BitVec.ofNat 32 k) d = x.setWidth 64 + BitVec.ofNat 64 (k + d) := by
  simp only [addr]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
  have := x.isLt
  rw [Nat.mod_eq_of_lt (a := k) (by omega), Nat.mod_eq_of_lt (a := d) (by omega),
    Nat.mod_eq_of_lt (a := x.toNat + k) (by omega), Nat.mod_eq_of_lt (a := x.toNat + k + d) (by omega),
    Nat.mod_eq_of_lt (a := x.toNat + k + d) (by omega), Nat.mod_eq_of_lt (a := x.toNat) (by omega),
    Nat.mod_eq_of_lt (a := k + d) (by omega), Nat.mod_eq_of_lt (a := x.toNat + (k + d)) (by omega)]
  omega

/-- `[(x + j) + d]` is byte `j` from `[x + d]`. -/
theorem addr_step {x : BitVec 32} {j d : Nat} (h : x.toNat + j + d < 2 ^ 32) :
    addr (x + BitVec.ofNat 32 j) d = addr x d + BitVec.ofNat 64 j := by
  rw [addr_add h, addr_eq (by omega), Offset.add_add, Nat.add_comm]

theorem toNat_add_ofNat {x : BitVec 32} {c : Nat} (h : x.toNat + c < 2 ^ 32) :
    (x + BitVec.ofNat 32 c).toNat = x.toNat + c := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := c) (by omega), Nat.mod_eq_of_lt h]

theorem toNat_add {x y : BitVec 32} (h : x.toNat + y.toNat < 2 ^ 32) :
    (x + y).toNat = x.toNat + y.toNat := by
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt h]

/-- Each byte of a range within one of the regions. -/
theorem inBytes {rs : List Region} {R : Region} (hR : R ∈ rs) {A : Addr} {n : Nat}
    (hs : Region.Sub ⟨A, n⟩ R) (hn : n < 2 ^ 64) : ∀ i < n, InRegions rs (A + BitVec.ofNat 64 i) 1 :=
  fun i hi => ⟨R, hR, hs _ (Offset.contains_base _ (by omega) (by omega))⟩

/-! ## Bytes -/

theorem bytesAt_len (m : Mem) (p : Addr) (n : Nat) : (Spec.Rc2.bytesAt m p n).length = n := by
  simp [Spec.Rc2.bytesAt]

/-- Bytes `[0, r)` from `p` stay, and the bytes `xs` follow them. -/
theorem bytesAt_writeBytes (m : Mem) (p : Addr) (r : Nat) (xs : List Byte) (h : r + xs.length < 2 ^ 64) :
    Spec.Rc2.bytesAt (writeBytes m (p + BitVec.ofNat 64 r) xs) p (r + xs.length) =
      Spec.Rc2.bytesAt m p r ++ xs := by
  simp only [Spec.Rc2.bytesAt, List.range_add, List.map_append, List.map_map]
  congr 1
  · apply List.map_congr_left
    intro i hi
    have hi := List.mem_range.mp hi
    exact writeBytes_before m p xs hi (by omega)
  · apply List.ext_getElem (by simp)
    intro j h₁ h₂
    simp only [List.getElem_map, List.getElem_range, Function.comp, writeBytes]
    have hj : j < xs.length := by simpa using h₁
    rw [show p + BitVec.ofNat 64 (r + j) - (p + BitVec.ofNat 64 r) = BitVec.ofNat 64 j from
      Offset.add_ofNat_add_sub p r j, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    simp [hj, List.getD_eq_getElem?_getD]

/-- The bytes written, read back. -/
theorem bytesAt_writeBytes_self (m : Mem) (q : Addr) (xs : List Byte) (h : xs.length < 2 ^ 64) :
    Spec.Rc2.bytesAt (writeBytes m q xs) q xs.length = xs := by
  have := bytesAt_writeBytes m q 0 xs (by omega)
  rwa [Nat.zero_add, BitVec.add_zero, show Spec.Rc2.bytesAt m q 0 = [] from rfl, List.nil_append] at this

/-! ## Instructions on bytes -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

/-- `movzx d, BYTE PTR [b + o]` -/
theorem wp_ldb {d b : Reg} {B : BitVec 32} {o : Nat} (hb : s.gpr b = B)
    (hin : InRegions (s.rd ++ s.wr) (addr B o) 1)
    (k : ∀ s', Upd s s' d ((s.mem (addr B o)).setWidth 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.movzx8 d ⟨b, o⟩ :: is)) s Q :=
  cons (s' := s.setReg d _) (by simp [exec, State.load8, ea_mk, hb, hin]) (k _ (Upd.setReg _ _ _))

/-- `mov BYTE PTR [b + o], r` -/
theorem wp_stb {b : Reg} {r : Reg8} {B : BitVec 32} {o : Nat} (hb : s.gpr b = B)
    (hout : InRegions s.wr (addr B o) 1)
    (k : ∀ s', Mupd s s' (s.mem.writeW (addr B o) ((s.gpr r.reg).setWidth 8)) → WP isa (.block is) s' Q) :
    WP isa (.block (.store8 ⟨b, o⟩ r :: is)) s Q := by
  refine cons (s' := { s with mem := s.mem.writeW (addr B o) ((s.gpr r.reg).setWidth 8) }) ?_
    (k _ ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)
  simp [exec, State.store8, ea_mk, hb, hout]

end

/-! ## The copy loop -/

/-- What a copy of `n` bytes from `addr S sd` to `addr D dd`, from `s₀`, leaves. -/
structure CopyPost (s₀ : State) (S D : BitVec 32) (sd dd n : Nat) (s : State) : Prop where
  esi : s.gpr .esi = S + BitVec.ofNat 32 n
  edx : s.gpr .edx = D + BitVec.ofNat 32 n
  other : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .esi → r ≠ .edx → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : s.mem = writeBytes s₀.mem (addr D dd) (Spec.Rc2.bytesAt s₀.mem (addr S sd) n)

/-- The loop's state after `j` of the `n` bytes. -/
structure CopyI (s₀ : State) (S D : BitVec 32) (sd dd n j : Nat) (s : State) : Prop where
  j_le : j ≤ n
  esi : s.gpr .esi = S + BitVec.ofNat 32 j
  edx : s.gpr .edx = D + BitVec.ofNat 32 j
  ecx : s.gpr .ecx = BitVec.ofNat 32 (n - j)
  other : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .esi → r ≠ .edx → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : s.mem = writeBytes s₀.mem (addr D dd) ((Spec.Rc2.bytesAt s₀.mem (addr S sd) n).take j)

theorem contains_prefix (q : Addr) {j k : Nat} (h : j ≤ k) : (⟨q, k⟩ : Region).Contains q j := by
  simp [Region.Contains, h]

theorem copyI_post {s₀ s : State} {S D : BitVec 32} {sd dd n : Nat} (h : CopyI s₀ S D sd dd n n s) :
    CopyPost s₀ S D sd dd n s := by
  refine ⟨h.esi, h.edx, h.other, h.rd, h.wr, ?_⟩
  rw [h.mem, List.take_of_length_le (by rw [bytesAt_len])]

section
variable {sd dd n : Nat} {s₀ : State} {S D : BitVec 32}
  (hn : n < 2 ^ 32) (hfs : S.toNat + sd + n ≤ 2 ^ 32) (hfd : D.toNat + dd + n ≤ 2 ^ 32)
  (hin : ∀ i < n, InRegions (s₀.rd ++ s₀.wr) (addr S sd + BitVec.ofNat 64 i) 1)
  (hout : ∀ i < n, InRegions s₀.wr (addr D dd + BitVec.ofNat 64 i) 1)
  (hd : Region.Disjoint ⟨addr S sd, n⟩ ⟨addr D dd, n⟩)
include hn hfs hfd hin hout hd

/-- One iteration, from byte `j < n`. -/
theorem copyBody_ok {j : Nat} (hj : j < n) {s : State} (h : CopyI s₀ S D sd dd n j s) :
    WP isa (.block (Impl.Rc2.X86.Stream.copyBody sd dd)) s (fun s' =>
      CopyI s₀ S D sd dd n (j + 1) s' ∧ s'.zf = some (decide (n - (j + 1) = 0))) := by
  have eS : addr (S + BitVec.ofNat 32 j) sd = addr S sd + BitVec.ofNat 64 j := addr_step (by omega)
  have eD : addr (D + BitVec.ofNat 32 j) dd = addr D dd + BitVec.ofNat 64 j := addr_step (by omega)
  have hbyte : s.mem (addr S sd + BitVec.ofNat 64 j) = s₀.mem (addr S sd + BitVec.ofNat 64 j) := by
    rw [h.mem]
    exact (writeBytes_frame s₀.mem _ _ (contains_prefix (k := n) _ (by simp; omega))).bytes
      (R := ⟨addr S sd, n⟩) (by simpa using hd) (by show n ≤ 2 ^ 64; omega) hj
  simp only [Impl.Rc2.X86.Stream.copyBody, Impl.Rc2.X86.memOp]
  refine wp_ldb h.esi (by rw [h.rd, h.wr, eS]; exact hin j hj) fun s₁ u₁ => ?_
  refine wp_stb (B := D + BitVec.ofNat 32 j)
    (by rw [u₁.other _ (by decide)]; exact h.edx) (by rw [u₁.wr, h.wr, eD]; exact hout j hj)
    fun s₂ u₂ => ?_
  refine wp_addi fun s₃ u₃ => wp_addi fun s₄ u₄ => wp_subi fun s₅ u₅ _ hz₅ => WP.block_nil ?_
  have g₂ : ∀ r, r ≠ .eax → s₂.gpr r = s.gpr r := fun r hr => by rw [u₂.gpr]; exact u₁.other r hr
  have hecx : s₄.gpr .ecx = s.gpr .ecx := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), g₂ _ (by decide)]
  have hc : s.gpr .ecx - 1 = BitVec.ofNat 32 (n - (j + 1)) := by
    rw [h.ecx, ofNat_pred (by omega), Nat.sub_sub]
  refine ⟨⟨by omega, ?_, ?_, ?_, fun r a b c d => ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, g₂ _ (by decide), h.esi,
      BitVec.ofNat_add, BitVec.add_assoc]; rfl
  · rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), g₂ _ (by decide), h.edx,
      BitVec.ofNat_add, BitVec.add_assoc]; rfl
  · rw [u₅.gpr, hecx, hc]
  · rw [u₅.other _ b, u₄.other _ d, u₃.other _ c, g₂ _ a]; exact h.other r a b c d
  · rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]; exact h.rd
  · rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact h.wr
  · have hj' : j < (Spec.Rc2.bytesAt s₀.mem (addr S sd) n).length := by rw [bytesAt_len]; exact hj
    have hlen : (List.take j (Spec.Rc2.bytesAt s₀.mem (addr S sd) n)).length = j := by
      rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj')]
    rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem, show Reg8.al.reg = Reg.eax from rfl, u₁.gpr, h.mem, List.take_add_one,
      List.getElem?_eq_getElem hj', Option.toList_some,
      writeBytes_snoc _ _ _ _ (by rw [hlen]; omega), hlen, eD, eS, ← h.mem, hbyte,
      BitVec.setWidth_setWidth_of_le _ (by omega), BitVec.setWidth_eq]
    congr 1
    simp [Spec.Rc2.bytesAt]
  · rw [hz₅, hecx, hc, ofNat_beq_zero (by omega)]

theorem copyLoop_ok {s : State} (hpos : 0 < n) (h : CopyI s₀ S D sd dd n 0 s) {Q : State → Prop}
    (hQ : ∀ s', CopyPost s₀ S D sd dd n s' → Q s') :
    WP isa (.loop (.block (Impl.Rc2.X86.Stream.copyBody sd dd)) .ne) s Q := by
  refine WP.loop (M := isa) (fun k (s : State) => ∃ j, k = n - j ∧ j < n ∧ CopyI s₀ S D sd dd n j s) ?_ n s
    ⟨0, by omega, hpos, h⟩
  rintro k s ⟨j, rfl, hj, h⟩
  refine (copyBody_ok hn hfs hfd hin hout hd hj h).mono fun s' ⟨h', hz⟩ => ?_
  by_cases hjn : j + 1 = n
  · refine .inl ⟨?_, hQ _ (copyI_post (hjn ▸ h'))⟩
    simp only [eval, hz, show n - (j + 1) = 0 by omega, decide_true, Option.map_some, Bool.not_true]
  · refine .inr ⟨?_, n - (j + 1), by omega, j + 1, rfl, by omega, h'⟩
    simp only [eval, hz, show n - (j + 1) ≠ 0 by omega, decide_false, Option.map_some, Bool.not_false]

/-- The copy of `ecx = n` bytes from `esi = S` (`[esi + sd]`) to `edx = D`
(`[edx + dd]`). -/
theorem copy_ok (hS : s₀.gpr .esi = S) (hD : s₀.gpr .edx = D) (hC : s₀.gpr .ecx = BitVec.ofNat 32 n)
    {Q : State → Prop} (hQ : ∀ s', CopyPost s₀ S D sd dd n s' → Q s') :
    WP isa (Impl.Rc2.X86.Stream.copy sd dd) s₀ Q := by
  refine WP.seq (wp_test fun s₁ f₁ hz₁ => WP.block_nil ?_)
  have hz : s₁.zf = some (decide (n = 0)) := by
    rw [hz₁, hC, BitVec.and_self, ofNat_beq_zero hn]
  refine WP.ite _ hz (fun h0 => WP.block_nil ?_) (fun h0 => ?_)
  · have h0 : n = 0 := by simpa using h0
    subst h0
    refine hQ _ ⟨?_, ?_, fun r _ _ _ _ => by rw [f₁.gpr], f₁.rd, f₁.wr, ?_⟩
    · rw [f₁.gpr, hS]; simp
    · rw [f₁.gpr, hD]; simp
    · rw [f₁.mem]; simp [Spec.Rc2.bytesAt, writeBytes_nil]
  · have hpos : 0 < n := by simp at h0; omega
    exact copyLoop_ok hn hfs hfd hin hout hd hpos
      ⟨by omega, by rw [f₁.gpr, hS]; simp, by rw [f₁.gpr, hD]; simp, by rw [f₁.gpr, hC]; simp,
        fun r _ _ _ _ => by rw [f₁.gpr], f₁.rd, f₁.wr, by rw [f₁.mem]; simp [writeBytes_nil]⟩ hQ

end

end VG.Proof.Rc2.X86.Stream
