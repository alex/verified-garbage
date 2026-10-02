import VerifiedGarbage.Proof.Rc2.X86.Stream.UpdatePre

/-!
# Streaming RC2-CBC on x86 (32-bit): the copies of the update functions

Untrusted: everything here is checked by Lean. Saving our caller's registers
(`entry_ok`), and the copies: with no complete block, the data after the
pending bytes (`short_ok`); otherwise the pending bytes and the first
`out_len - pending_len` bytes of data to `out` and the rest to the pending
block (`long_ok`).
-/

namespace VG.Proof.Rc2.X86.Stream.Update

open VG VG.X86 VG.X86.Wp VG.Impl.Rc2.X86.Stream
open VG.WriteBytes (writeBytes writeBytes_frame)

theorem Common.upd {s₀ s s' : State} (h : Common s₀ s) {d : Reg} {v : BitVec 32} (u : Upd s s' d v)
    (h₁ : d ≠ .esp) (h₂ : d ≠ .edi) (h₃ : d ≠ .ebp) : Common s₀ s' :=
  ⟨u.rd.trans h.rd, u.wr.trans h.wr, (u.other _ (Ne.symm h₁)).trans h.esp,
    (u.other _ (Ne.symm h₂)).trans h.edi, (u.other _ (Ne.symm h₃)).trans h.ebp,
    by rw [u.mem]; exact h.frame, by rw [u.mem]; exact h.ebx, by rw [u.mem]; exact h.esi⟩

theorem Common.fupd {s₀ s s' : State} (h : Common s₀ s) (u : Fupd s s') : Common s₀ s' :=
  ⟨u.rd.trans h.rd, u.wr.trans h.wr, by rw [u.gpr]; exact h.esp, by rw [u.gpr]; exact h.edi,
    by rw [u.gpr]; exact h.ebp, by rw [u.mem]; exact h.frame, by rw [u.mem]; exact h.ebx,
    by rw [u.mem]; exact h.esi⟩

theorem frame_writeBytes (m : Mem) (q : Addr) (xs : List Byte) : Frame [⟨q, xs.length⟩] m (writeBytes m q xs) :=
  writeBytes_frame _ _ _ (Region.contains_self _ _)

/-- A copy leaves `Common`, if it writes within the pending block or `out`. -/
theorem Common.copy {s₀ s s' : State} (hp : Pre s₀) (h : Common s₀ s) {S D : BitVec 32} {sd dd n : Nat}
    (c : CopyPost s S D sd dd n s')
    (hr : Region.Sub ⟨addr D dd, n⟩ (pendR s₀) ∨ Region.Sub ⟨addr D dd, n⟩ (oR s₀)) : Common s₀ s' := by
  refine h.write hp hr ?_ c.rd c.wr (c.other _ (by decide) (by decide) (by decide) (by decide))
    (c.other _ (by decide) (by decide) (by decide) (by decide))
    (c.other _ (by decide) (by decide) (by decide) (by decide))
  have := frame_writeBytes s.mem (addr D dd) (Spec.Rc2.bytesAt s.mem (addr S sd) n)
  rwa [bytesAt_len, ← c.mem] at this

theorem copy_bytes {s s' : State} {S D : BitVec 32} {sd dd n : Nat} (c : CopyPost s S D sd dd n s')
    (hn : n < 2 ^ 64) :
    Spec.Rc2.bytesAt s'.mem (addr D dd) n = Spec.Rc2.bytesAt s.mem (addr S sd) n := by
  have h := bytesAt_writeBytes_self s.mem (addr D dd) (Spec.Rc2.bytesAt s.mem (addr S sd) n)
    (by rw [bytesAt_len]; exact hn)
  rwa [bytesAt_len, ← c.mem] at h

theorem copy_frame {s s' : State} {S D : BitVec 32} {sd dd n : Nat} (c : CopyPost s S D sd dd n s') :
    Frame [⟨addr D dd, n⟩] s.mem s'.mem := by
  have := frame_writeBytes s.mem (addr D dd) (Spec.Rc2.bytesAt s.mem (addr S sd) n)
  rwa [bytesAt_len, ← c.mem] at this

/-! ## Saving our caller's registers -/

theorem entry_ok {s₀ : State} (hp : Pre s₀) {Q : State → Prop}
    (hQ : ∀ s, Common s₀ s → Frame [scR s₀] s₀.mem s.mem → s.zf = some (decide (O s₀ = 0)) → Q s) :
    WP isa (.block entry) s₀ Q := by
  simp only [entry, save, List.cons_append, List.nil_append]
  have sc (d : Nat) (hd : d + 4 ≤ 576) : (scR s₀).Contains (addr (scr s₀) d) (32 / 8) := by
    rw [hp.scr_addr hd]; exact Offset.contains_base _ hd (by omega)
  refine wp_ldm (b := .esp) (o := 4 + 4 * 6) rfl (hp.rin rfl (by decide)) fun s₁ u₁ => ?_
  have e₁ : s₁.gpr .eax = scr s₀ := u₁.gpr
  refine wp_stm e₁ (hp.sin (u₁.wr) (d := 512) (by decide)) fun s₂ u₂ => ?_
  refine wp_stm (by rw [u₂.gpr]; exact e₁) (hp.sin (u₂.wr.trans u₁.wr) (d := 516) (by decide))
    fun s₃ u₃ => ?_
  have m₃ : s₃.mem = (s₀.mem.writeW (addr (scr s₀) 512) (s₀.gpr .ebx)).writeW (addr (scr s₀) 516)
      (s₀.gpr .esi) := by
    rw [u₃.mem, u₂.mem, u₂.gpr, u₁.mem, u₁.other _ (by decide), u₁.other _ (by decide)]
  have f₃ : Frame [scR s₀] s₀.mem s₃.mem := by
    rw [m₃]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (sc 512 (by decide))).writeW
      (List.mem_singleton_self _) _ (sc 516 (by decide))
  have g₃ (r : Reg) (hr : r ≠ .eax) : s₃.gpr r = s₀.gpr r := by
    rw [u₃.gpr, u₂.gpr]; exact u₁.other r hr
  have c₃ : Common s₀ s₃ := by
    refine ⟨by rw [u₃.rd, u₂.rd, u₁.rd], by rw [u₃.wr, u₂.wr, u₁.wr], g₃ _ (by decide), g₃ _ (by decide),
      g₃ _ (by decide), f₃.mono (by simp), ?_, ?_⟩
    · rw [m₃, Mem.readW_writeW_sep _ (by decide), Mem.readW_writeW_self32]
      rw [hp.scr_addr (d := 512) (by decide), hp.scr_addr (d := 516) (by decide)]
      exact Offset.sep _ (by decide) (by decide) (by decide)
    · rw [m₃, Mem.readW_writeW_self32]
  refine wp_arg hp c₃ (i := 5) (by decide) fun s₄ u₄ => wp_test fun s₅ f₅ hz₅ => WP.block_nil ?_
  refine hQ s₅ ((c₃.upd u₄ (by decide) (by decide) (by decide)).fupd f₅) (by rw [f₅.mem, u₄.mem]; exact f₃) ?_
  rw [hz₅, u₄.gpr, BitVec.and_self, ← ofNat_toNat (arg s₀ 5), ofNat_beq_zero (arg s₀ 5).isLt]

/-! ## No complete block -/

theorem short_ok {s₀ s : State} (hp : Pre s₀) (hO : O s₀ = 0) (hc : Common s₀ s)
    (hf : Frame [scR s₀] s₀.mem s.mem) {Q : State → Prop}
    (hQ : ∀ s', Common s₀ s' →
      Spec.Rc2.bytesAt s'.mem (cA s₀ + BitVec.ofNat 64 136) (p s₀ + len s₀) =
        Spec.Rc2.bytesAt s₀.mem (cA s₀ + BitVec.ofNat 64 136) (p s₀) ++
          Spec.Rc2.bytesAt s₀.mem (dA s₀) (len s₀) → Q s') :
    WP isa short s Q := by
  have hpl : p s₀ + len s₀ < 8 := by have := hp.O_eq; omega
  have hcf := hp.c_fit
  have hdf := hp.d_fit
  rw [short]
  refine WP.seq ?_
  refine wp_arg hp hc (i := 2) (by decide) fun s₁ u₁ => ?_
  have c₁ := hc.upd u₁ (by decide) (by decide) (by decide)
  refine wp_arg hp c₁ (i := 0) (by decide) fun s₂ u₂ => ?_
  have c₂ := c₁.upd u₂ (by decide) (by decide) (by decide)
  refine wp_arg hp c₂ (i := 1) (by decide) fun s₃ u₃ => ?_
  have c₃ := c₂.upd u₃ (by decide) (by decide) (by decide)
  refine wp_add fun s₄ u₄ _ => ?_
  have c₄ := c₃.upd u₄ (by decide) (by decide) (by decide)
  refine wp_arg hp c₄ (i := 3) (by decide) fun s₅ u₅ => WP.block_nil ?_
  have c₅ := c₄.upd u₅ (by decide) (by decide) (by decide)
  have esi₅ : s₅.gpr .esi = dp s₀ := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.gpr]
  have edx₅ : s₅.gpr .edx = ctx s₀ + BitVec.ofNat 32 (p s₀) := by
    rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), u₃.gpr, u₂.gpr, ofNat_toNat]
  have ecx₅ : s₅.gpr .ecx = BitVec.ofNat 32 (len s₀) := by rw [u₅.gpr, ofNat_toNat]
  have mem₅ : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have hS : addr (dp s₀) 0 = dA s₀ := by
    rw [addr_eq (by have := (dp s₀).isLt; omega)]; exact BitVec.add_zero _
  have hD : addr (ctx s₀ + BitVec.ofNat 32 (p s₀)) 136 = cA s₀ + BitVec.ofNat 64 (p s₀ + 136) :=
    addr_add (by omega)
  have dst : Region.Sub ⟨cA s₀ + BitVec.ofNat 64 (p s₀ + 136), len s₀⟩ (pendR s₀) :=
    Offset.sub _ (by omega) (by omega)
  refine copy_ok (sd := 0) (dd := 136) (n := len s₀) (S := dp s₀) (D := ctx s₀ + BitVec.ofNat 32 (p s₀))
    (arg s₀ 3).isLt (by omega) (by rw [toNat_add_ofNat (by omega)]; omega)
    (fun i hi => by
      rw [c₅.rd, c₅.wr, hS]
      exact inBytes (R := dR s₀) (by simp [hp.rd]) (fun _ h => h) (by omega) i hi)
    (fun i hi => by
      rw [c₅.wr, hD]
      exact inBytes (R := ctxR s₀) (by simp [hp.wr]) (fun a h => Pre.pend_sub a (dst a h)) (by omega) i hi)
    (by rw [hS, hD]; exact hp.c_d.symm.sub_right (fun a h => Pre.pend_sub a (dst a h)))
    esi₅ edx₅ ecx₅ fun s' c => hQ s' (c₅.copy hp c (.inl (by rw [hD]; exact dst))) ?_
  have hw := bytesAt_writeBytes s.mem (cA s₀ + BitVec.ofNat 64 136) (p s₀)
    (Spec.Rc2.bytesAt s.mem (dA s₀) (len s₀)) (by rw [bytesAt_len]; omega)
  rw [bytesAt_len, Offset.add_add, Nat.add_comm 136] at hw
  rw [c.mem, mem₅, hS, hD, hw,
    Proof.Rc2.bytesAt_frame hf _ _ (by omega) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.c_s.sub_left (fun a h => Pre.pend_sub a (Offset.sub _ (by omega) (by omega) a h)))),
    Proof.Rc2.bytesAt_frame hf _ _ (by omega) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.d_s)]

end VG.Proof.Rc2.X86.Stream.Update
