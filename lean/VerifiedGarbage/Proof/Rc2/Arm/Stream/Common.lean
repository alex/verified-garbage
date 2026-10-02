import VerifiedGarbage.Proof.Rc2.Arm.Stream.Copy
import VerifiedGarbage.Proof.Rc2.Arm.Stream.Call
import VerifiedGarbage.Proof.Rc2.Arm.Stream.Contract

/-!
# Streaming RC2-CBC on ARMv7: facts shared by the proofs

Untrusted: everything here is checked by Lean. Sub-ranges of buffers,
stack arguments, and the preconditions of `update` and `init` by name
(`UPre`, `IPre`).
-/

namespace VG.Proof.Rc2.Arm.Stream

open VG VG.Arm

theorem ofNat_toNat32 (x : BitVec 32) : x = BitVec.ofNat 32 x.toNat := by simp

theorem add0 (a : Addr) : a + BitVec.ofNat 64 0 = a := BitVec.add_zero a

theorem e128 : (128 : Addr) = BitVec.ofNat 64 128 := rfl
theorem e136 : (136 : Addr) = BitVec.ofNat 64 136 := rfl
theorem e512 : (512 : Addr) = BitVec.ofNat 64 512 := rfl

/-- A range at an offset within a region of `rs`. -/
theorem cov1 {rs : List Region} {b : Addr} {len : Nat} (hR : (⟨b, len⟩ : Region) ∈ rs) {off n : Nat}
    (h : off + n ≤ len) : Covers [⟨b + BitVec.ofNat 64 off, n⟩] rs :=
  Covers.of_sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, hR, off, rfl, h⟩

/-- The `i`-th stack argument, of the 12 bytes of them. -/
theorem stackArgAddr_eq (s : State) {i : Nat} (hi : i < 3) (hsp : s.sp.toNat + 12 ≤ 2 ^ 32) :
    stackArgAddr s i = stackArgAddr s 0 + BitVec.ofNat 64 (4 * i) := by
  unfold stackArgAddr
  rw [show s.sp + BitVec.ofNat 32 (4 * 0) = s.sp from BitVec.add_zero _, addr_add (by omega)]

theorem argIn {s : State} {rs : List Region} (hR : (⟨stackArgAddr s 0, 12⟩ : Region) ∈ rs) {i : Nat}
    (hi : i < 3) (hsp : s.sp.toNat + 12 ≤ 2 ^ 32) : InRegions rs (stackArgAddr s i) 4 := by
  rw [stackArgAddr_eq s hi hsp]
  exact ⟨_, hR, Offset.contains_base _ (by omega) (by omega)⟩

theorem ldrSp_addr (s : State) (i : Nat) :
    State.addr (s.sp + BitVec.ofNat 32 (4 * i)) = stackArgAddr s i := rfl

/-- Memory reads of 1 byte within a word written elsewhere. -/
theorem bytesAt_writeW {m : Mem} {p a : Addr} {n : Nat} (v : BitVec 32) (hn : n ≤ 2 ^ 64)
    (hd : (⟨p, n⟩ : Region).Disjoint ⟨a, 4⟩) :
    Spec.Rc2.bytesAt (m.writeW a v) p n = Spec.Rc2.bytesAt m p n :=
  VG.Proof.Rc2.bytesAt_frame ((Frame.refl _ _).writeW (r := ⟨a, 4⟩) (List.mem_singleton_self _) _
    (Region.contains_self _ _)) p n hn (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hd)

/-- A stack argument, read from memory that changed only outside the arguments. -/
theorem stackArg_frame {s : State} {m : Mem} {rs : List Region} (hf : Frame rs s.mem m)
    (hsp : s.sp.toNat + 12 ≤ 2 ^ 32) (hd : ∀ r ∈ rs, (⟨stackArgAddr s 0, 12⟩ : Region).Disjoint r)
    {i : Nat} (hi : i < 3) : m.readW (stackArgAddr s i) 32 = stackArg s i := by
  rw [stackArg]
  refine hf.readW ?_ hd (by decide)
  rw [stackArgAddr_eq s hi hsp]
  exact Offset.contains_base _ (by omega) (by omega)

theorem preserved_ne {r : Reg} (hr : r ∈ preserved) (hl : r ≠ .lr) :
    r ≠ .r0 ∧ r ≠ .r1 ∧ r ≠ .r2 ∧ r ≠ .r3 ∧ r ≠ .r12 := by
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact absurd rfl hl | decide

/-- `t` is `s` but for `r12` and the flags. -/
structure Keep (s t : State) : Prop where
  reg : ∀ r, r ≠ .r12 → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

/-- `copy_wp`, with the buffers' addresses named. -/
theorem copy_ok {s : State} {src dst cnt : Reg} {so dd L : Nat} {A B : Addr}
    (h1 : src ≠ dst) (h2 : src ≠ cnt) (h3 : dst ≠ cnt) (h4 : src ≠ .r12) (h5 : dst ≠ .r12)
    (h6 : cnt ≠ .r12) (hso : so < 4096) (hdd : dd < 4096)
    (hc : s.gpr cnt = BitVec.ofNat 32 L) (hL : L < 2 ^ 32)
    (fp : (s.gpr src).toNat + so + L ≤ 2 ^ 32) (fd : (s.gpr dst).toNat + dd + L ≤ 2 ^ 32)
    (hA : State.addr (s.gpr src) + BitVec.ofNat 64 so = A)
    (hB : State.addr (s.gpr dst) + BitVec.ofNat 64 dd = B)
    (hr : 0 < L → Covers [⟨A, L⟩] (s.rd ++ s.wr)) (hw : 0 < L → Covers [⟨B, L⟩] s.wr)
    (hd : 0 < L → (⟨A, L⟩ : Region).Disjoint ⟨B, L⟩) :
    WP isa (Impl.Rc2.Arm.Stream.copy src so dst dd cnt) s (CopyPost s src dst cnt A B L) := by
  subst hA hB
  exact copy_wp h1 h2 h3 h4 h5 h6 hso hdd hc hL fp fd hr hw hd

theorem writeBytes_frame' (m : Mem) (q : Addr) (xs : List Byte) {n : Nat} (hn : xs.length = n) :
    Frame [⟨q, n⟩] m (VG.WriteBytes.writeBytes m q xs) :=
  VG.WriteBytes.writeBytes_frame _ _ _ (by rw [hn]; exact Region.contains_self _ _)

end VG.Proof.Rc2.Arm.Stream
