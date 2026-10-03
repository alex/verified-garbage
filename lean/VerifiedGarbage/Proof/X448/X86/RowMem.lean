import VerifiedGarbage.Proof.X448.X86.RowPass

/-!
# X448 on x86 (32-bit): multiplication-row memory

The public row pointer moves through the working space while all field inputs
remain unchanged.
-/

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86 VG.Proof.X448.Radix16

abbrev accw (m : Mem) (base : Addr) (k : Nat) : Nat := limbs m base ACC k

theorem rowEa {s : State} {base : Addr} (hs : Scr s base) {i d : Nat}
    (hp : s.gpr .ebp = s.gpr .edi + BitVec.ofNat 32 (4 * i)) (hd : 4 * i + d < 8192) :
    s.ea (at_ .ebp d) = off base (4 * i + d) := by
  change ((s.gpr .ebp + BitVec.ofNat 32 d).setWidth 64) = _
  rw [hp, Offset.add_add]
  exact hs.ea hd

structure RowInv (base : Addr) (a b : Nat) (s0 : State) (i : Nat) (s : State) : Prop where
  scr : Scr s base
  regs : Keeps clob s0 s
  ptr : s.gpr .ebp = s.gpr .edi + BitVec.ofNat 32 (4 * i)
  mem : Outside base ACC 224 s0.mem s.mem
  lt : ∀ k < i + 28, accw s.mem base k < radix
  val : valN (accw s.mem base) (i + 28) = valN (limbs s0.mem base a) i * fe s0.mem base b

def rowSrc (b j : Nat) : List Instr :=
  [ld .eax (b + 4 * j), .mul .ecx, .alu .add .eax (.mem (at_ .ebp (ACC + 4 * j)))]

theorem rowSrc_ok {s : State} {base : Addr} (hs : Scr s base) {b i j : Nat}
    (hb : Slot b) (hi : i < 28) (hj : j < 28)
    (hp : s.gpr .ebp = s.gpr .edi + BitVec.ofNat 32 (4 * i))
    (hc : (s.gpr .ecx).toNat < radix) (hy : limbs s.mem base b j < radix)
    (hacc : accw s.mem base (i + j) < radix) :
    WP isa (.block (rowSrc b j)) s fun t =>
      (t.gpr .eax).toNat = (s.gpr .ecx).toNat * limbs s.mem base b j + accw s.mem base (i + j) ∧
      Keeps [.eax, .edx] s t ∧ t.mem = s.mem := by
  have hb' : b + 112 ≤ 3584 := hb
  unfold rowSrc
  refine load_ok hs (by omega) fun t ht => ?_
  refine wp_mul fun u uv um uk => ?_
  have us := (hs.of_upd ht (by decide)).of_keeps uk (by decide)
  have up : u.gpr .ebp = u.gpr .edi + BitVec.ofNat 32 (4 * i) := by
    rw [uk.1 _ (by decide), uk.1 _ (by decide), ht.other .ebp (by decide), ht.other .edi (by decide)]
    exact hp
  have ea : u.ea (at_ .ebp (ACC + 4 * j)) = off base (ACC + 4 * (i + j)) := by
    rw [rowEa us up (by simp only [ACC]; omega), show 4 * i + (ACC + 4 * j) = ACC + 4 * (i + j) by omega]
  have rd : readSrc u (.mem (at_ .ebp (ACC + 4 * j))) = some (word u.mem base (ACC + 4 * (i + j))) := by
    simp only [readSrc, ea, State.load32, us.read (d := ACC + 4 * (i + j)) (n := 4) (by simp only [ACC]; omega), ite_true]
  refine wp_alu (Or.inl rfl) rd fun v hv _ => WP.block_nil ⟨?_, ?_, hv.mem.trans (um.trans ht.mem)⟩
  · rw [hv.gpr]
    change (u.gpr .eax + word u.mem base (ACC + 4 * (i + j))).toNat = _
    rw [uv, ht.gpr, ht.other .ecx (by decide), um, ht.mem, BitVec.toNat_add, BitVec.toNat_ofNat]
    have prod := Nat.mul_le_mul (Nat.le_of_lt_succ hc) (Nat.le_of_lt_succ hy)
    simp only [radix] at hc hy hacc prod
    change ((limbs s.mem base b j * (s.gpr .ecx).toNat) % 2 ^ 32 + accw s.mem base (i + j)) % 2 ^ 32 = _
    rw [Nat.mul_comm (limbs s.mem base b j)]
    omega
  · exact (ht.rest (by decide)).trans (uk.trans (hv.rest (by decide)))

end VG.Proof.X448.X86
