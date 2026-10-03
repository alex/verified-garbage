import VerifiedGarbage.Proof.Curve448.AArch64.Neon.Lanes
import VerifiedGarbage.Proof.X448.AArch64.Mem
import VerifiedGarbage.Impl.Curve448.AArch64.Neon
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

/-!
# The vector loads and stores of `Neon.mul2`

Untrusted: everything here is checked by Lean. `nw m base d` is the 32-bit
word at offset `d` of the working space; vector loads and stores move four of
them at once.
-/

namespace VG.Proof.Curve448.AArch64.Neon

open VG VG.AArch64
open VG.Impl.Curve448.AArch64.Neon
open VG.Proof.X448.AArch64 (Scr off ofs Outside)

/-- The 32-bit word at offset `d`. -/
abbrev nw (m : Mem) (base : Addr) (d : Nat) : Nat := (m.readW (off base d) 32).toNat

theorem off_add (base : Addr) (d e : Nat) : off base d + BitVec.ofNat 64 e = off base (d + e) := by
  simp only [off, BitVec.add_assoc, ← BitVec.ofNat_add]

theorem exec_ldq {s : State} {base : Addr} (hs : Scr s base) (t : Nat) {d : Nat} (h16 : d % 16 = 0)
    (hd : d + 16 ≤ 8192) : isa.exec (ldq t d) s = some (s.setV (V t) (s.mem.read (off base d) 16)) := by
  have hr := hs.read (d := d) (n := 16) hd
  simp only [ldq, exec, addr, show d % 16 = 0 ∧ d < 4096 * 16 from ⟨h16, by omega⟩, and_self, ite_true,
    Option.bind_some, State.load, hs.x3]
  rw [ite_eq_left_iff.mpr fun h => absurd hr h]
  rfl

theorem vword_ld (m : Mem) (base : Addr) (d : Nat) {c : Nat} (hc : c < 4) :
    (vword (m.read (off base d) 16) c).toNat = nw m base (d + 4 * c) := by
  rw [vword_read16 _ _ hc, off_add]

/-- `s` with memory `m`. -/
def setMem (s : State) (m : Mem) : State := { s with mem := m }

@[simp] theorem setMem_mem (s : State) (m : Mem) : (setMem s m).mem = m := rfl
@[simp] theorem setMem_v (s : State) (m : Mem) : (setMem s m).v = s.v := rfl
@[simp] theorem setMem_gpr (s : State) (m : Mem) : (setMem s m).gpr = s.gpr := rfl
@[simp] theorem setMem_rd (s : State) (m : Mem) : (setMem s m).rd = s.rd := rfl
@[simp] theorem setMem_wr (s : State) (m : Mem) : (setMem s m).wr = s.wr := rfl
@[simp] theorem setMem_sp (s : State) (m : Mem) : (setMem s m).sp = s.sp := rfl
@[simp] theorem setMem_c (s : State) (m : Mem) : (setMem s m).c = s.c := rfl

theorem exec_stq {s : State} {base : Addr} (hs : Scr s base) (t : Nat) {d : Nat} (h16 : d % 16 = 0)
    (hd : d + 16 ≤ 8192) :
    isa.exec (stq t d) s = some (setMem s (s.mem.write (off base d) 16 (s.v (V t)))) := by
  have hw := hs.write (d := d) (n := 16) hd
  simp only [stq, exec, addr, show d % 16 = 0 ∧ d < 4096 * 16 from ⟨h16, by omega⟩, and_self, ite_true,
    Option.bind_some, State.store, hs.x3]
  rw [ite_eq_left_iff.mpr fun h => absurd hw h]
  rfl

theorem nw_st (m : Mem) (base : Addr) (d : Nat) (v : BitVec 128) {c : Nat} (hc : c < 4) :
    nw (m.write (off base d) 16 v) base (d + 4 * c) = (vword v c).toNat := by
  rw [nw, ← off_add, write16_word _ _ _ hc]

theorem st_outside (m : Mem) (base : Addr) {d : Nat} (v : BitVec 128) (h : d + 16 ≤ 8192) :
    Outside base d 16 m (m.write (off base d) 16 v) := by
  intro x hx
  apply Mem.write_apply
  rw [Offset.lt_iff x base (by omega)]
  simp only [ofs] at hx
  omega

theorem Outside.nw {base : Addr} {o n : Nat} {m m' : Mem} (h : Outside base o n m m') {d : Nat}
    (hd : d + 4 ≤ o ∨ o + n ≤ d) (hd' : d + 4 ≤ 8192) : nw m' base d = nw m base d :=
  congrArg BitVec.toNat
    (Mem.readW_congr fun i hi => (h _ (by rw [VG.Proof.X448.AArch64.ofs_off base (by omega)]; omega)).symm).symm

theorem nw_st_other (m : Mem) (base : Addr) {d d' : Nat} (v : BitVec 128) (h : d + 16 ≤ 8192)
    (h' : d' + 4 ≤ 8192) (hd : d' + 4 ≤ d ∨ d + 16 ≤ d') : nw (m.write (off base d) 16 v) base d' = nw m base d' :=
  Outside.nw (st_outside m base v h) hd h'

theorem scr_of {s t : State} {base : Addr} (hs : Scr s base) (hg : t.gpr = s.gpr) (hw : t.wr = s.wr) :
    Scr t base := ⟨by rw [hg]; exact hs.x3, by rw [hg]; exact hs.mask, hw ▸ hs.wr, hs.nowrap⟩

/-- Read vector registers through the writes after them (distinctness from the context). -/
macro "vred" : tactic =>
  `(tactic| simp (disch := assumption) only [RegUpd.v_setV_self, RegUpd.v_setV_of_ne, RegUpd.mem_setV,
    setMem_mem, setMem_v])

/-- `Scr` of a state the vector code built from one where it holds. -/
macro "scr" : tactic =>
  `(tactic| exact scr_of (by assumption) (by simp only [RegUpd.gpr_setV, setMem_gpr])
    (by simp only [RegUpd.wr_setV, setMem_wr]))

end VG.Proof.Curve448.AArch64.Neon
