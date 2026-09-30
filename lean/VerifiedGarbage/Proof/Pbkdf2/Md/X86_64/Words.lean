import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hash
import VerifiedGarbage.Proof.MdStream.X86_64.Words
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Spec.Pbkdf2

/-!
# PBKDF2-HMAC over any Merkle–Damgård hash function on x86-64: words

Untrusted: everything here is checked by Lean. What the straight-line pieces
of `iterate` (`Impl/Pbkdf2/Md/X86_64.lean`) write: 32-bit words copied from
one region to another (`copy32`), the padding after the digest in the block
(`padTo`), and `T ← T ⊕ U` (`xor32`).
-/

namespace VG.Proof.Pbkdf2.Md.X86_64

open VG.X86_64 VG.Proof.MdStream VG.Proof.MdStream.X86_64
open VG.Impl.MdStream.X86_64 (at_)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil writeBytes_append write_eq_writeBytes)
open VG.Proof.Hmac.Common (copy_mem bytesAt_add bytesAt_writeBytes_sep bytesAt_zero bytesAt_length)
open Spec.Sha256 (bytesAt)

theorem ea_off (s : State) (b : Reg) (o j : Nat) :
    s.ea (at_ b (o + j)) = s.gpr b + BitVec.ofNat 64 o + BitVec.ofNat 64 j := by
  rw [ea_at, ofInt_natCast, BitVec.ofNat_add, BitVec.add_assoc]

theorem ea_nat (s : State) (b : Reg) (o : Nat) : s.ea (at_ b o) = s.gpr b + BitVec.ofNat 64 o := by
  rw [ea_at, ofInt_natCast]

/-! ## Copies -/

/-- `copy32 src so dst d n` writes the `4 n` bytes at `src + so` to `dst + d`. -/
theorem copy32_ok {src dst : Reg} (hs : src ≠ .rax) (hd : dst ≠ .rax) (o₁ o₂ : Nat) (n : Nat) :
    ∀ (rest : List Instr) (s : State) (Q : State → Prop),
    (∀ k < n, InRegions (s.rd ++ s.wr) (s.gpr src + BitVec.ofNat 64 o₁ + BitVec.ofNat 64 (4 * k)) 4) →
    (∀ k < n, InRegions s.wr (s.gpr dst + BitVec.ofNat 64 o₂ + BitVec.ofNat 64 (4 * k)) 4) →
    Mem.Sep (s.gpr src + BitVec.ofNat 64 o₁) (4 * n) (s.gpr dst + BitVec.ofNat 64 o₂) (4 * n) →
    4 * n < 2 ^ 64 →
    (∀ s', (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      s'.mem = writeBytes s.mem (s.gpr dst + BitVec.ofNat 64 o₂)
        (bytesAt s.mem (s.gpr src + BitVec.ofNat 64 o₁) (4 * n)) → WP isa (.block rest) s' Q) →
    WP isa (.block (Hash.copy32 src o₁ dst o₂ n ++ rest)) s Q := by
  induction n with
  | zero =>
    intro rest s Q _ _ _ _ k
    exact k s (fun _ _ => rfl) rfl rfl (by rw [Nat.mul_zero, bytesAt_zero, writeBytes_nil])
  | succ n ih =>
    intro rest s Q hin hout hsep hlt k
    rw [Hash.copy32, List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]
    refine ih _ s Q (fun j hj => hin j (by omega)) (fun j hj => hout j (by omega))
      (fun x hx hy => hsep x (by omega) (by omega)) (by omega) fun s₁ g₁ rd₁ wr₁ m₁ => ?_
    simp only [List.cons_append, List.nil_append]
    refine wp_mov32m (a := s.gpr src + BitVec.ofNat 64 o₁ + BitVec.ofNat 64 (4 * n))
      (by rw [ea_off, g₁ _ hs]) (by rw [rd₁, wr₁]; exact hin n (by omega)) fun s₂ u₂ => ?_
    refine wp_store32 (a := s.gpr dst + BitVec.ofNat 64 o₂ + BitVec.ofNat 64 (4 * n))
      (by rw [ea_off, u₂.other _ hd, g₁ _ hd]) (by rw [u₂.wr, wr₁]; exact hout n (by omega))
      fun s₃ g₃ m₃ rd₃ wr₃ => k s₃ (fun r hr => by rw [g₃, u₂.other r hr, g₁ r hr])
        (by rw [rd₃, u₂.rd, rd₁]) (by rw [wr₃, u₂.wr, wr₁]) ?_
    rw [m₃, u₂.gpr, u₂.mem, m₁, BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq,
      Nat.mul_succ]
    exact copy_mem s.mem _ _ n 4 (by rwa [← Nat.mul_succ]) (by omega)

/-! ## Padding -/

/-- The four bytes of a 32-bit word, little-endian. -/
theorem writeW32_le (m : Mem) (a : Addr) (x : BitVec 32) : m.writeW a x = writeBytes m a (bytes32 false x) :=
  writeW32 m a false x

theorem bytes32_zero : bytes32 false 0 = List.replicate 4 (0 : Byte) := by decide

theorem bytes32_80 : bytes32 false 0x80 = [(0x80 : Byte), 0, 0, 0] := by decide

/-- Zero words at `b + e + 4 k` for `k < n`, with `rax = 0`. -/
theorem zeros_ok {b : Reg} (e : Nat) (n : Nat) :
    ∀ (rest : List Instr) (s : State) (Q : State → Prop), s.gpr .rax = 0 →
    (∀ k < n, InRegions s.wr (s.gpr b + BitVec.ofNat 64 e + BitVec.ofNat 64 (4 * k)) 4) →
    4 * n < 2 ^ 64 →
    (∀ s', s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr →
      s'.mem = writeBytes s.mem (s.gpr b + BitVec.ofNat 64 e) (List.replicate (4 * n) 0) →
      WP isa (.block rest) s' Q) →
    WP isa (.block (((List.range n).map fun k => Instr.store32 (at_ b (e + 4 * k)) .rax) ++ rest)) s Q := by
  induction n with
  | zero =>
    intro rest s Q _ _ _ k
    exact k s rfl rfl rfl (by rw [Nat.mul_zero, List.replicate_zero, writeBytes_nil])
  | succ n ih =>
    intro rest s Q hax hout hlt k
    rw [List.range_succ, List.map_append, List.map_singleton, List.append_assoc]
    refine ih _ s Q hax (fun j hj => hout j (by omega)) (by omega) fun s₁ g₁ rd₁ wr₁ m₁ => ?_
    simp only [List.singleton_append]
    refine wp_store32 (a := s.gpr b + BitVec.ofNat 64 e + BitVec.ofNat 64 (4 * n))
      (by rw [ea_off, g₁]) (by rw [wr₁]; exact hout n (by omega))
      fun s₂ g₂ m₂ rd₂ wr₂ => k s₂ (by rw [g₂, g₁]) (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁]) ?_
    have hl : (List.replicate (4 * n) (0 : Byte)).length = 4 * n := List.length_replicate
    have hax' : s₁.gpr .rax = 0 := by rw [g₁, hax]
    rw [m₂, hax', m₁, show ((0 : BitVec 64).setWidth 32) = 0 from rfl, writeW32_le, bytes32_zero,
      show s.gpr b + BitVec.ofNat 64 e + BitVec.ofNat 64 (4 * n) =
        s.gpr b + BitVec.ofNat 64 e + BitVec.ofNat 64 (List.replicate (4 * n) (0 : Byte)).length by rw [hl],
      writeBytes_append _ _ _ _ (by rw [hl, List.length_replicate]; omega), List.replicate_append_replicate,
      Nat.mul_succ]

/-- `padTo e` writes the byte `0x80` and zeros from `rbp + D` to `rbp + e`. -/
theorem padTo_ok (H : Hash) {e : Nat} (he : H.D + 4 ≤ e) (h4 : (e - H.D) % 4 = 0) (hlt : e < 2 ^ 32)
    {rest : List Instr} {s : State} {Q : State → Prop}
    (hout : ∀ j, H.D ≤ j → j + 4 ≤ e → InRegions s.wr (s.gpr .rbp + BitVec.ofNat 64 j) 4)
    (k : ∀ s', (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      s'.mem = writeBytes s.mem (s.gpr .rbp + BitVec.ofNat 64 H.D)
        ((0x80 : Byte) :: List.replicate (e - H.D - 1) 0) → WP isa (.block rest) s' Q) :
    WP isa (.block (H.padTo e ++ rest)) s Q := by
  simp only [Hash.padTo, List.cons_append, List.nil_append]
  refine wp_mov32i fun s₁ u₁ _ _ => wp_store32 (a := s.gpr .rbp + BitVec.ofNat 64 H.D)
    (by rw [ea_nat, u₁.other _ (by decide)]) (by rw [u₁.wr]; exact hout H.D (Nat.le_refl _) he)
    fun s₂ g₂ m₂ rd₂ wr₂ => wp_mov32i fun s₃ u₃ _ _ => ?_
  have e₃ : ∀ r, r ≠ .rax → s₃.gpr r = s.gpr r := fun r hr => by rw [u₃.other r hr, g₂, u₁.other r hr]
  refine zeros_ok (b := .rbp) (H.D + 4) ((e - H.D - 4) / 4) rest s₃ Q (by rw [u₃.gpr]; rfl)
    (fun j hj => by
      rw [e₃ _ (by decide), u₃.wr, wr₂, u₁.wr, BitVec.add_assoc, ← BitVec.ofNat_add]
      exact hout _ (by omega) (by omega)) (by omega) fun s₄ g₄ rd₄ wr₄ m₄ => k s₄
    (fun r hr => by rw [g₄, e₃ r hr]) (by rw [rd₄, u₃.rd, rd₂, u₁.rd]) (by rw [wr₄, u₃.wr, wr₂, u₁.wr]) ?_
  rw [m₄, u₃.mem, m₂, u₁.gpr, e₃ _ (by decide), u₁.mem, show ((BitVec.setWidth 64 (0x80 : BitVec 32)).setWidth 32) =
    (0x80 : BitVec 32) from rfl, writeW32_le, bytes32_80, show s.gpr .rbp + BitVec.ofNat 64 (H.D + 4) =
      s.gpr .rbp + BitVec.ofNat 64 H.D + BitVec.ofNat 64 ([(0x80 : Byte), 0, 0, 0].length) by
        rw [BitVec.add_assoc, ← BitVec.ofNat_add]; rfl,
    writeBytes_append _ _ _ _ (by simp only [List.length_cons, List.length_nil, List.length_replicate]; omega)]
  congr 1
  simp only [List.cons_append, List.nil_append, List.cons.injEq, true_and]
  rw [show e - H.D - 1 = 4 * ((e - H.D - 4) / 4) + 1 + 1 + 1 by omega, List.replicate_succ,
    List.replicate_succ, List.replicate_succ]

/-! ## `T ← T ⊕ U` -/

theorem writeW_xor32 (m m' : Mem) (d a b : Addr) :
    m.writeW d (m'.readW a 32 ^^^ m'.readW b 32) =
      writeBytes m d (Spec.Pbkdf2.xorBytes (bytesAt m' b 4) (bytesAt m' a 4)) := by
  simp only [Mem.writeW, Mem.readW]
  rw [show (32 : Nat) / 8 = 4 from rfl, BitVec.setWidth_eq, BitVec.setWidth_eq, BitVec.setWidth_eq,
    write_eq_writeBytes]
  congr 1
  apply List.ext_getElem (by simp [Spec.Pbkdf2.xorBytes, bytesAt])
  intro j h₁ h₂
  simp only [List.length_map, List.length_range] at h₁
  simp only [Spec.Pbkdf2.xorBytes, bytesAt, List.getElem_map, List.getElem_range, List.getElem_zipWith]
  rw [BitVec.extractLsb'_xor, Mem.extractLsb'_read _ _ h₁, Mem.extractLsb'_read _ _ h₁, BitVec.xor_comm]

theorem wp_xor32m {is : List Instr} {s : State} {Q : State → Prop} {d : Reg} {m : MemOp} {a : Addr}
    (ha : s.ea m = a) (hin : InRegions (s.rd ++ s.wr) a 4)
    (k : ∀ s', Upd s s' d ((((s.gpr d).setWidth 32) ^^^ s.mem.readW a 32).setWidth 64) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.alu32 .xor d (.mem m) :: is)) s Q := by
  refine WP.cons (s' := (arithFlags s (((s.gpr d).setWidth 32) ^^^ s.mem.readW a 32) false false).setReg d _) ?_
    (k _ (Upd.flags _ _ _ _ _ _))
  simp [exec, execAlu32, readSrc32, State.load32, State.setReg32, ha, hin]

theorem xorBytes_len (a b : List Byte) (h : a.length = b.length) :
    (Spec.Pbkdf2.xorBytes a b).length = a.length := by
  simp [Spec.Pbkdf2.xorBytes, h]

/-- `T ← T ⊕ U` for the first `n` 32-bit words of `T` at `r14` and `U` at `rbp`. -/
theorem xor32_ok {tp up : Addr} {n₀ : Nat} (hd : Region.Disjoint ⟨tp, 4 * n₀⟩ ⟨up, 4 * n₀⟩)
    (hn : 4 * n₀ < 2 ^ 64) : ∀ n ≤ n₀,
    ∀ (rest : List Instr) (s : State) (Q : State → Prop), s.gpr .r14 = tp → s.gpr .rbp = up →
    (∀ k < n, InRegions (s.rd ++ s.wr) (up + BitVec.ofNat 64 (4 * k)) 4) →
    (∀ k < n, InRegions s.wr (tp + BitVec.ofNat 64 (4 * k)) 4) →
    (∀ s', (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      s'.mem = writeBytes s.mem tp
        (Spec.Pbkdf2.xorBytes (bytesAt s.mem tp (4 * n)) (bytesAt s.mem up (4 * n))) →
      WP isa (.block rest) s' Q) →
    WP isa (.block (((List.range n).flatMap fun k =>
      [.mov32 .rax (.mem (at_ .rbp (4 * k))), .alu32 .xor .rax (.mem (at_ .r14 (4 * k))),
        .store32 (at_ .r14 (4 * k)) .rax]) ++ rest)) s Q := by
  intro n
  induction n with
  | zero =>
    intro _ rest s Q _ _ _ _ k
    exact k s (fun _ _ => rfl) rfl rfl (by simp [bytesAt, Spec.Pbkdf2.xorBytes, writeBytes_nil])
  | succ n ih =>
    intro hn₀ rest s Q htp hup hin hout k
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]
    refine ih (by omega) _ s Q htp hup (fun j hj => hin j (by omega)) (fun j hj => hout j (by omega))
      fun s₁ g₁ rd₁ wr₁ m₁ => ?_
    simp only [List.cons_append, List.nil_append]
    refine wp_mov32m (a := up + BitVec.ofNat 64 (4 * n))
      (by rw [ea_nat, g₁ _ (by decide), hup]) (by rw [rd₁, wr₁]; exact hin n (by omega)) fun s₂ u₂ => ?_
    have hw := hout n (by omega)
    refine wp_xor32m (a := tp + BitVec.ofNat 64 (4 * n))
      (by rw [ea_nat, u₂.other _ (by decide), g₁ _ (by decide), htp])
      (by rw [u₂.rd, u₂.wr, rd₁, wr₁]; obtain ⟨r, hr, hc⟩ := hw; exact ⟨r, List.mem_append_right _ hr, hc⟩)
      fun s₃ u₃ => ?_
    refine wp_store32 (a := tp + BitVec.ofNat 64 (4 * n))
      (by rw [ea_nat, u₃.other _ (by decide), u₂.other _ (by decide), g₁ _ (by decide), htp])
      (by rw [u₃.wr, u₂.wr, wr₁]; exact hw)
      fun s₄ g₄ m₄ rd₄ wr₄ => k s₄ (fun r hr => by rw [g₄, u₃.other r hr, u₂.other r hr, g₁ r hr])
        (by rw [rd₄, u₃.rd, u₂.rd, rd₁]) (by rw [wr₄, u₃.wr, u₂.wr, wr₁]) ?_
    have hl : (Spec.Pbkdf2.xorBytes (bytesAt s.mem tp (4 * n)) (bytesAt s.mem up (4 * n))).length =
        4 * n := by rw [xorBytes_len _ _ (by simp [bytesAt_length]), bytesAt_length]
    have ct : (⟨tp, 4 * n₀⟩ : Region).Contains tp (4 * n) := by
      simpa using Offset.contains_base tp (d := 0) (n := 4 * n) (k := 4 * n₀) (by omega) (by omega)
    have cu : (⟨up, 4 * n₀⟩ : Region).Contains (up + BitVec.ofNat 64 (4 * n)) 4 :=
      Offset.contains_base up (by omega) (by omega)
    have hsep : Mem.Sep (up + BitVec.ofNat 64 (4 * n)) 4 tp (4 * n) := fun x h₁ h₂ => hd.sep ct cu x h₂ h₁
    have hsep' : Mem.Sep (tp + BitVec.ofNat 64 (4 * n)) 4 tp (4 * n) :=
      fun x h₁ h₂ => Offset.sep_base tp (Nat.le_refl _) (by omega) x h₂ h₁
    have b₁ := bytesAt_writeBytes_sep s.mem (p := tp + BitVec.ofNat 64 (4 * n)) (n := 4)
      (Spec.Pbkdf2.xorBytes (bytesAt s.mem tp (4 * n)) (bytesAt s.mem up (4 * n))) (by rw [hl]; exact hsep')
      (by omega)
    have b₂ := bytesAt_writeBytes_sep s.mem (p := up + BitVec.ofNat 64 (4 * n)) (n := 4)
      (Spec.Pbkdf2.xorBytes (bytesAt s.mem tp (4 * n)) (bytesAt s.mem up (4 * n))) (by rw [hl]; exact hsep)
      (by omega)
    rw [m₄, u₃.gpr, u₃.mem, u₂.gpr, u₂.mem, setWidth32, BitVec.setWidth_setWidth_of_le _ (by decide),
      BitVec.setWidth_eq, m₁, writeW_xor32, b₁, b₂]
    have e := writeBytes_append s.mem tp _ (Spec.Pbkdf2.xorBytes (bytesAt s.mem (tp + BitVec.ofNat 64 (4 * n)) 4)
      (bytesAt s.mem (up + BitVec.ofNat 64 (4 * n)) 4))
      (by rw [hl, xorBytes_len _ _ (by simp [bytesAt_length]), bytesAt_length]; omega)
    rw [hl] at e
    rw [e, Nat.mul_succ, bytesAt_add, bytesAt_add, Spec.Pbkdf2.xorBytes, Spec.Pbkdf2.xorBytes,
      Spec.Pbkdf2.xorBytes, List.zipWith_append (by simp [bytesAt_length])]

end VG.Proof.Pbkdf2.Md.X86_64
