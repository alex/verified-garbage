import VerifiedGarbage.Proof.X448.X86.Save

/-!
# X448 on x86 (32-bit): restoring the callee-saved registers

Untrusted: everything here is checked by Lean. The address is retained in
eax so edi can be restored after the other saved registers.
-/

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86

def restoreRegs : List Reg := [.eax, .ebx, .esi, .ebp, .edi]

theorem restore_ok {s : State} {base : Addr} (hs : Scr s base) {g : Reg → BitVec 32}
    (hsv : Saved base g s.mem) :
    WP isa (.block restore) s fun t =>
      (∀ i < 4, t.gpr (saved[i]!) = g (saved[i]!)) ∧ t.mem = s.mem ∧ Keeps restoreRegs s t := by
  have ea : ∀ d < 16, addr (s.gpr .edi) d = off base d := fun d hd => hs.ea (by omega)
  unfold restore
  refine wp_mov rfl fun t ht => ?_
  refine wp_load (a := off base 0)
    (by change addr (t.gpr .eax) 0 = _; rw [ht.gpr]; exact ea 0 (by decide))
    (by rw [ht.rd, ht.wr]; exact hs.read (by decide)) fun u hu => ?_
  refine wp_load (a := off base 4)
    (by change addr (u.gpr .eax) 4 = _; rw [hu.other _ (by decide), ht.gpr]; exact ea 4 (by decide))
    (by rw [hu.rd, hu.wr, ht.rd, ht.wr]; exact hs.read (by decide)) fun v hv => ?_
  refine wp_load (a := off base 12)
    (by change addr (v.gpr .eax) 12 = _; rw [hv.other _ (by decide), hu.other _ (by decide), ht.gpr]; exact ea 12 (by decide))
    (by rw [hv.rd, hv.wr, hu.rd, hu.wr, ht.rd, ht.wr]; exact hs.read (by decide)) fun w hw => ?_
  refine wp_load (a := off base 8)
    (by change addr (w.gpr .eax) 8 = _; rw [hw.other _ (by decide), hv.other _ (by decide), hu.other _ (by decide), ht.gpr]; exact ea 8 (by decide))
    (by rw [hw.rd, hw.wr, hv.rd, hv.wr, hu.rd, hu.wr, ht.rd, ht.wr]; exact hs.read (by decide)) fun x hx => WP.block_nil ⟨?_, ?_, ?_⟩
  · intro i hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
    · change x.gpr .ebx = g .ebx
      rw [hx.other _ (by decide), hw.other _ (by decide), hv.other _ (by decide), hu.gpr, ht.mem]
      exact hsv 0 (by decide)
    · change x.gpr .esi = g .esi
      rw [hx.other _ (by decide), hw.other _ (by decide), hv.gpr, hu.mem, ht.mem]
      exact hsv 1 (by decide)
    · change x.gpr .edi = g .edi
      rw [hx.gpr, hw.mem, hv.mem, hu.mem, ht.mem]
      exact hsv 2 (by decide)
    · change x.gpr .ebp = g .ebp
      rw [hx.other _ (by decide), hw.gpr, hv.mem, hu.mem, ht.mem]
      exact hsv 3 (by decide)
  · exact hx.mem.trans (hw.mem.trans (hv.mem.trans (hu.mem.trans ht.mem)))
  · exact (ht.rest (by decide)).trans ((hu.rest (by decide)).trans ((hv.rest (by decide)).trans
      ((hw.rest (by decide)).trans (hx.rest (by decide)))))

end VG.Proof.X448.X86
