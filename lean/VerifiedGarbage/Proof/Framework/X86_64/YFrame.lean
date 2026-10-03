import VerifiedGarbage.TCB.X86_64.Isa

/-!
# x86-64: what a block leaves of the vector registers, lane by lane

`YFrame rs s s'`: `s'` is `s` but for the vector registers `rs` (both
128-bit lanes of each) and the flags, as `XFrame`-like frames state of the
SSE registers alone.
-/

namespace VG.X86_64

/-- `s'` is `s` but for the vector registers `rs` (and the flags). -/
structure YFrame (rs : List XReg) (s s' : State) : Prop where
  gpr : s'.gpr = s.gpr
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  lane : ∀ r, r ∉ rs → ∀ l < 2, s'.lane r l = s.lane r l

theorem YFrame.refl (rs : List XReg) (s : State) : YFrame rs s s :=
  ⟨rfl, rfl, rfl, rfl, fun _ _ _ _ => rfl⟩

theorem YFrame.trans {rs : List XReg} {s s' s'' : State} (h : YFrame rs s s') (h' : YFrame rs s' s'') :
    YFrame rs s s'' :=
  ⟨h'.gpr.trans h.gpr, h'.mem.trans h.mem, h'.rd.trans h.rd, h'.wr.trans h.wr,
    fun r hr l hl => (h'.lane r hr l hl).trans (h.lane r hr l hl)⟩

theorem YFrame.comp {rs rs' : List XReg} {s s' s'' : State} (h : YFrame rs s s')
    (h' : YFrame rs' s' s'') : YFrame (rs ++ rs') s s'' :=
  ⟨h'.gpr.trans h.gpr, h'.mem.trans h.mem, h'.rd.trans h.rd, h'.wr.trans h.wr, fun r hr l hl => by
    simp only [List.mem_append, not_or] at hr
    exact (h'.lane r hr.2 l hl).trans (h.lane r hr.1 l hl)⟩

theorem YFrame.mono {rs rs' : List XReg} {s s' : State} (h : YFrame rs s s') (hs : ∀ r ∈ rs, r ∈ rs') :
    YFrame rs' s s' :=
  ⟨h.gpr, h.mem, h.rd, h.wr, fun r hr => h.lane r fun h' => hr (hs r h')⟩

end VG.X86_64
