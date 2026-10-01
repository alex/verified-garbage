import VerifiedGarbage.Proof.X448.Arm.Normalize

/-!
# X448 on ARMv7: field operations and their frame

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.X448.Arm

open VG VG.Arm VG.Impl.X448.Arm VG.Proof.X448.Radix16

abbrev F (m : Mem) (base : Addr) (o : Nat) : Spec.X448.Fe := toFe (fe m base o)

def clob : List Reg := [.r1, .r2, .r3, .r4, .r5, .r7, .r9]

structure Op (base : Addr) (o : Nat) (s t : State) : Prop where
  keeps : Keeps clob s t
  mem : FieldMem base o s.mem t.mem

theorem Op.scr {base : Addr} {o : Nat} {s t : State} (h : Op base o s t) (hs : Scr s base) :
    Scr t base := hs.of_keeps h.keeps (by decide)

abbrev Slot (o : Nat) : Prop := o + 112 ≤ ACC

/-- A register update preserving the working-space pointer and limb mask. -/
theorem Scr.of_upd {s t : State} {base : Addr} {r : Reg} {v : BitVec 32}
    (hs : Scr s base) (h : VG.Proof.X25519.Arm.Upd s t r v) (h0 : Reg.r0 ≠ r) (h6 : Reg.r6 ≠ r) :
    Scr t base :=
  ⟨by rw [h.other _ h0]; exact hs.r0, (h.other _ h6).trans hs.mask, h.wr ▸ hs.wr,
    by rw [h.other _ h0]; exact hs.nowrap⟩

theorem load_ok {s : State} {base : Addr} (hs : Scr s base) {r : Reg} {d : Nat}
    (hd : d + 4 ≤ 4096) {is : List Instr} {Q : State → Prop}
    (k : ∀ t, VG.Proof.X25519.Arm.Upd s t r (word s.mem base d) → WP isa (.block is) t Q) :
    WP isa (.block (ld r d :: is)) s Q :=
  VG.Proof.X25519.Arm.wp_ldr (by omega) (hs.ea (by omega)) (hs.read (by omega)) k

theorem store_ok {s : State} {base : Addr} (hs : Scr s base) {r : Reg} {d : Nat}
    (hd : d + 4 ≤ 4096) {is : List Instr} {Q : State → Prop}
    (k : ∀ t, VG.Proof.X25519.Arm.Mupd s t (s.mem.writeW (off base d) (s.gpr r)) →
      WP isa (.block is) t Q) : WP isa (.block (st r d :: is)) s Q :=
  VG.Proof.X25519.Arm.wp_str (by omega) (hs.ea (by omega)) (hs.write (by omega)) k

end VG.Proof.X448.Arm
