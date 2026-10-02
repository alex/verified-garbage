import VerifiedGarbage.Proof.Rc2.X86_64.Stream.Short

/-! # Streaming RC2-CBC on x86-64: the copies before CBC

With `out_len ≠ 0`: the pending bytes and the first `out_len - pending_len`
bytes of data to `out`, the rest of the data to `ctx + 136`, and the
arguments of the CBC function (`Mid`). -/

set_option linter.unusedSimpArgs false
namespace VG.Proof.Rc2.X86_64.Stream

open VG VG.X86_64 VG.X86_64.RegUpd VG.WriteBytes VG.Impl.Rc2.X86_64 VG.Impl.Rc2.X86_64.Stream

/-- The state before the call of the CBC function, from the entry state `s`. -/
structure Mid (s t : State) : Prop where
  rdi : t.gpr .rdi = s.gpr .rdi
  rsi : t.gpr .rsi = s.gpr .rdi + 128
  rdx : t.gpr .rdx = s.gpr .r8
  rcx : t.gpr .rcx = BitVec.ofNat 64 ((s.gpr .r9).toNat / 8)
  r8 : t.gpr .r8 = stackArg s 0
  rsp : t.gpr .rsp = s.gpr .rsp
  callee : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  /-- Memory changed only in `out` and the pending block. -/
  frame : Frame [⟨s.gpr .r8, (s.gpr .r9).toNat⟩, ⟨s.gpr .rdi + BitVec.ofNat 64 136, 8⟩] s.mem t.mem
  out : Spec.Rc2.bytesAt t.mem (s.gpr .r8) (s.gpr .r9).toNat =
    Spec.Rc2.bytesAt s.mem (s.gpr .rdi + 136) (s.gpr .rsi).toNat ++
      Spec.Rc2.bytesAt s.mem (s.gpr .rdx) ((s.gpr .r9).toNat - (s.gpr .rsi).toNat)
  pend : Spec.Rc2.bytesAt t.mem (s.gpr .rdi + 136) (((s.gpr .rsi).toNat + (s.gpr .rcx).toNat) % 8) =
    Spec.Rc2.bytesAt s.mem (s.gpr .rdx + BitVec.ofNat 64 ((s.gpr .r9).toNat - (s.gpr .rsi).toNat))
      (((s.gpr .rsi).toNat + (s.gpr .rcx).toNat) % 8)

theorem long_ok (d : Spec.Rc2.Direction) (s : State) (hs : (updateContract d).pre s)
    (hnz : (s.gpr .r9).toNat ≠ 0) (t : State) (ht : Keep [] s t) {Q : State → Prop}
    (hQ : ∀ t', Mid s t' → WP isa (cbcCall d) t' Q) :
    WP isa (long d) t Q := by
  obtain ⟨_, _, hrd, hwr, ctxData, ctxOut, _, ctxArgs, dataOut, _, _, outArgs, _, _, _, _, _, _,
    _, _, _, _, _, _, fitData, fitOut, _, hp, hN⟩ := hs
  -- Names for the arguments.
  generalize hC : s.gpr .rdi = C at *
  generalize hP : (s.gpr .rsi).toNat = P at *
  generalize hA : s.gpr .rdx = A at *
  generalize hL : (s.gpr .rcx).toNat = L at *
  generalize hO : s.gpr .r8 = O at *
  generalize hNN : (s.gpr .r9).toNat = N at *
  have h8 : 8 ≤ N := by omega
  have hPN : P ≤ N := by omega
  have hNL : N - P ≤ L := by omega
  have hR : L - (N - P) = (P + L) % 8 := by omega
  have rsi₀ : s.gpr .rsi = BitVec.ofNat 64 P := by rw [← hP]; exact toNat_eq _
  have rcx₀ : s.gpr .rcx = BitVec.ofNat 64 L := by rw [← hL]; exact toNat_eq _
  have r9₀ : s.gpr .r9 = BitVec.ofNat 64 N := by rw [← hNN]; exact toNat_eq _
  have K_def : N - P + (P + L) % 8 = L := by omega
  have hRlt : (P + L) % 8 < 8 := Nat.mod_lt _ (by decide)
  have dataR (i n : Nat) (h : i + n ≤ L) : InRegions s.rd (A + BitVec.ofNat 64 i) n := by
    rw [hrd]; exact ⟨⟨A, L⟩, by simp, Offset.contains_base _ h (by omega)⟩
  have outW (i n : Nat) (h : i + n ≤ N) : InRegions s.wr (O + BitVec.ofNat 64 i) n := by
    rw [hwr]; exact ⟨⟨O, N⟩, by simp, Offset.contains_base _ h (by omega)⟩
  have ctxW (i n : Nat) (h : i + n ≤ 144) : InRegions s.wr (C + BitVec.ofNat 64 i) n := by
    rw [hwr]; exact ⟨⟨C, 144⟩, by simp, Offset.contains_base _ h (by omega)⟩
  have rdwr {a : Addr} {n : Nat} (h : InRegions s.wr a n) : InRegions (s.rd ++ s.wr) a n := by
    obtain ⟨r, hr, hc⟩ := h; exact ⟨r, List.mem_append_right _ hr, hc⟩
  have rdrd {a : Addr} {n : Nat} (h : InRegions s.rd a n) : InRegions (s.rd ++ s.wr) a n := by
    obtain ⟨r, hr, hc⟩ := h; exact ⟨r, List.mem_append_left _ hr, hc⟩
  -- The pending bytes to `out`.
  refine WP.seq (WP.mono (copy_ok t (src := .rdi) (dst := .r8) (cnt := .rsi) (sd := 136) (dd := 0)
    ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
    (S := C + BitVec.ofNat 64 136) (D := O) (n := P)
    (by rw [ht.reg _ (by simp), hC]) (by rw [ht.reg _ (by simp), hO]; exact BitVec.add_zero _)
    (by rw [ht.reg _ (by simp), rsi₀]) (by omega)
    (fun i hi => by rw [ht.rd, ht.wr, Offset.add_add]; exact rdwr (ctxW _ _ (by omega)))
    (fun i hi => by rw [ht.wr]; exact outW _ _ (by omega))
    ((ctxOut.sub_left (Offset.sub_base _ (by omega))).sub_right (Region.sub_prefix hPN))) ?_)
  rintro s₁ ⟨mem₁, g₁, rd₁, wr₁⟩
  rw [ht.mem] at mem₁
  have f₁ : Frame [⟨O, P⟩] s.mem s₁.mem := by
    rw [mem₁]; exact writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
  have c₁ : Spec.Rc2.bytesAt s₁.mem O P = Spec.Rc2.bytesAt s.mem (C + BitVec.ofNat 64 136) P := by
    have h := bytesAt_writeBytes_self s.mem O (Spec.Rc2.bytesAt s.mem (C + BitVec.ofNat 64 136) P)
      (by rw [bytesAt_length]; omega)
    rwa [bytesAt_length, ← mem₁] at h
  clear mem₁
  have k₁ (r : Reg) (h₁ : r ≠ .r10) (h₂ : r ≠ .r11) : s₁.gpr r = s.gpr r := (g₁ r h₁ h₂).trans (ht.reg r (by simp))
  -- The registers for the data.
  obtain ⟨s₂, run₂, r9₂, r8₂, keep₂⟩ := toOut_ok s₁
  refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  have k₂ (r : Reg) (h₁ : r ≠ .r10) (h₂ : r ≠ .r11) (h₃ : r ≠ .r9) (h₄ : r ≠ .r8) : s₂.gpr r = s.gpr r :=
    (keep₂.reg r (by simp [h₃, h₄])).trans (k₁ r h₁ h₂)
  rw [k₁ _ (by decide) (by decide), k₁ _ (by decide) (by decide), r9₀, rsi₀,
    Offset.ofNat_sub_ofNat hPN] at r9₂
  rw [k₁ _ (by decide) (by decide), k₁ _ (by decide) (by decide), hO, rsi₀] at r8₂
  -- The first `out_len - pending_len` bytes of data to `out + pending_len`.
  refine WP.seq (WP.mono (copy_ok s₂ (src := .rdx) (dst := .r8) (cnt := .r9) (sd := 0) (dd := 0)
    ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
    (S := A) (D := O + BitVec.ofNat 64 P) (n := N - P)
    (by rw [k₂ _ (by decide) (by decide) (by decide) (by decide), hA]; exact BitVec.add_zero _)
    (by rw [r8₂]; exact BitVec.add_zero _) r9₂ (by omega)
    (fun i hi => by rw [keep₂.rd, keep₂.wr, rd₁, wr₁, ht.rd, ht.wr]; exact rdrd (dataR _ _ (by omega)))
    (fun i hi => by rw [keep₂.wr, wr₁, ht.wr, Offset.add_add]; exact outW _ _ (by omega))
    ((dataOut.sub_left (Region.sub_prefix hNL)).sub_right (Offset.sub_base _ (by omega)))) ?_)
  rintro s₃ ⟨mem₃, g₃, rd₃, wr₃⟩
  rw [keep₂.mem] at mem₃
  have f₃ : Frame [⟨O + BitVec.ofNat 64 P, N - P⟩] s₁.mem s₃.mem := by
    rw [mem₃]; exact writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
  have c₃ : Spec.Rc2.bytesAt s₃.mem (O + BitVec.ofNat 64 P) (N - P) = Spec.Rc2.bytesAt s₁.mem A (N - P) := by
    have h := bytesAt_writeBytes_self s₁.mem (O + BitVec.ofNat 64 P) (Spec.Rc2.bytesAt s₁.mem A (N - P))
      (by rw [bytesAt_length]; omega)
    rwa [bytesAt_length, ← mem₃] at h
  clear mem₃
  have k₃ (r : Reg) (h₁ : r ≠ .r10) (h₂ : r ≠ .r11) : s₃.gpr r = s₂.gpr r := g₃ r h₁ h₂
  -- The registers for the rest.
  obtain ⟨s₄, run₄, rdx₄, rcx₄, keep₄⟩ := toPending_ok s₃
  refine WP.seq (WP.of_runBlock ⟨s₄, run₄, ?_⟩)
  rw [k₃ _ (by decide) (by decide), k₃ _ (by decide) (by decide), r9₂,
    k₂ _ (by decide) (by decide) (by decide) (by decide), hA] at rdx₄
  rw [k₃ _ (by decide) (by decide), k₃ _ (by decide) (by decide), r9₂,
    k₂ _ (by decide) (by decide) (by decide) (by decide), rcx₀, Offset.ofNat_sub_ofNat hNL, hR] at rcx₄
  -- The rest to `ctx + 136`.
  refine WP.seq (WP.mono (copy_ok s₄ (src := .rdx) (dst := .rdi) (cnt := .rcx) (sd := 0) (dd := 136)
    ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
    (S := A + BitVec.ofNat 64 (N - P)) (D := C + BitVec.ofNat 64 136) (n := (P + L) % 8)
    (by rw [rdx₄]; exact BitVec.add_zero _)
    (by rw [keep₄.reg _ (by simp), k₃ _ (by decide) (by decide),
      k₂ _ (by decide) (by decide) (by decide) (by decide), hC]) rcx₄ (by omega)
    (fun i hi => by
      rw [keep₄.rd, keep₄.wr, rd₃, wr₃, keep₂.rd, keep₂.wr, rd₁, wr₁, ht.rd, ht.wr, Offset.add_add]
      exact rdrd (dataR _ _ (by omega)))
    (fun i hi => by
      rw [keep₄.wr, wr₃, keep₂.wr, wr₁, ht.wr, Offset.add_add]; exact ctxW _ _ (by omega))
    ((ctxData.symm.sub_left (Offset.sub_base _ (by omega))).sub_right (Offset.sub_base _ (by omega)))) ?_)
  rintro s₅ ⟨mem₅, g₅, rd₅, wr₅⟩
  rw [keep₄.mem] at mem₅
  have f₅ : Frame [⟨C + BitVec.ofNat 64 136, (P + L) % 8⟩] s₃.mem s₅.mem := by
    rw [mem₅]; exact writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
  have c₅ : Spec.Rc2.bytesAt s₅.mem (C + BitVec.ofNat 64 136) ((P + L) % 8) =
      Spec.Rc2.bytesAt s₃.mem (A + BitVec.ofNat 64 (N - P)) ((P + L) % 8) := by
    have h := bytesAt_writeBytes_self s₃.mem (C + BitVec.ofNat 64 136)
      (Spec.Rc2.bytesAt s₃.mem (A + BitVec.ofNat 64 (N - P)) ((P + L) % 8)) (by rw [bytesAt_length]; omega)
    rwa [bytesAt_length, ← mem₅] at h
  clear mem₅
  have k₅ (r : Reg) (h₁ : r ≠ .r10) (h₂ : r ≠ .r11) (h₃ : r ≠ .r9) (h₄ : r ≠ .r8) (h₅ : r ≠ .rdx)
      (h₆ : r ≠ .rcx) : s₅.gpr r = s.gpr r := by
    rw [g₅ r h₁ h₂, keep₄.reg r (by simp [h₅, h₆]), k₃ r h₁ h₂, k₂ r h₁ h₂ h₃ h₄]
  have rd₅' : s₅.rd = s.rd := by rw [rd₅, keep₄.rd, rd₃, keep₂.rd, rd₁, ht.rd]
  have wr₅' : s₅.wr = s.wr := by rw [wr₅, keep₄.wr, wr₃, keep₂.wr, wr₁, ht.wr]
  -- Memory changed only in `out` and the pending block.
  have frame : Frame [⟨O, N⟩, ⟨C + BitVec.ofNat 64 136, 8⟩] s.mem s₅.mem := by
    refine ((f₁.sub ?_).trans (f₃.sub ?_)).trans (f₅.sub ?_) <;> intro r hr <;>
      simp only [List.mem_singleton] at hr <;> subst hr
    · exact ⟨_, List.mem_cons_self .., Region.sub_prefix hPN⟩
    · exact ⟨_, List.mem_cons_self .., Offset.sub_base _ (by omega)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), Region.sub_prefix (by omega)⟩
  have argsAddr : stackArgAddr s 0 = s.gpr .rsp + BitVec.ofNat 64 8 := rfl
  have argsSep : ∀ r ∈ [(⟨O, N⟩ : Region), ⟨C + BitVec.ofNat 64 136, 8⟩],
      (Region.mk (stackArgAddr s 0) 8).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact outArgs.symm
    · exact ctxArgs.symm.sub_right (Offset.sub_base _ (by omega))
  -- The arguments of the CBC function.
  obtain ⟨s₆, run₆, rdi₆, rsi₆, rdx₆, rcx₆, r8₆, keep₆⟩ := cbcArgs_ok s₅ (by
    rw [rd₅', wr₅', k₅ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), ← argsAddr]
    exact rdrd (by rw [hrd]; exact ⟨_, by simp, Region.contains_self _ _⟩))
  refine WP.seq (WP.of_runBlock ⟨s₆, run₆, ?_⟩)
  have s5rdi : s₅.gpr .rdi = C := by
    rw [k₅ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hC]
  have s5rsi : s₅.gpr .rsi = BitVec.ofNat 64 P := by
    rw [k₅ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), rsi₀]
  have s5r8 : s₅.gpr .r8 = O + BitVec.ofNat 64 P := by
    rw [g₅ _ (by decide) (by decide), keep₄.reg _ (by simp), k₃ _ (by decide) (by decide), r8₂]
  have s5r9 : s₅.gpr .r9 = BitVec.ofNat 64 (N - P) := by
    rw [g₅ _ (by decide) (by decide), keep₄.reg _ (by simp), k₃ _ (by decide) (by decide), r9₂]
  have mem₆ : s₆.mem = s₅.mem := keep₆.mem
  apply hQ s₆
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [rdi₆, s5rdi, hC]
  · rw [rsi₆, s5rdi, hC]
  · rw [rdx₆, s5r8, s5rsi, BitVec.add_sub_cancel, hO]
  · rw [rcx₆, s5r9, s5rsi, ← BitVec.ofNat_add, Nat.sub_add_cancel hPN, hNN]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  · rw [r8₆, k₅ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), ← argsAddr]
    exact frame.readW (Region.contains_self _ _) argsSep (by decide)
  · rw [keep₆.reg _ (by simp), k₅ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
  · intro r hr
    have h : r ∉ [Reg.r8, .r9, .rdx, .rcx, .rsi] ∧ r ≠ .r10 ∧ r ≠ .r11 ∧ r ≠ .r9 ∧ r ≠ .r8 ∧ r ≠ .rdx ∧
        r ≠ .rcx := by
      revert hr; revert r; decide
    rw [keep₆.reg _ h.1, k₅ _ h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2]
  · rw [keep₆.rd, rd₅']
  · rw [keep₆.wr, wr₅']
  · rw [mem₆, hO, hNN, hC]; exact frame
  · -- `out`: the pending bytes, then the data.
    rw [mem₆, hO, hNN, hC, hP, hA, show C + 136 = C + BitVec.ofNat 64 136 from rfl,
      show N = P + (N - P) by omega, bytesAt_add, Nat.add_sub_cancel_left]
    have outSub : ∀ r ∈ [(⟨C + BitVec.ofNat 64 136, (P + L) % 8⟩ : Region)], (Region.mk O N).Disjoint r := by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr
      exact ctxOut.symm.sub_right (Offset.sub_base _ (by omega))
    congr 1
    · rw [Proof.Rc2.bytesAt_frame f₅ _ _ (by omega) (fun r hr => (outSub r hr).sub_left (Region.sub_prefix hPN)),
        Proof.Rc2.bytesAt_frame f₃ _ _ (by omega) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.base_disjoint _ (by omega) (by omega)), c₁]
    · rw [Proof.Rc2.bytesAt_frame f₅ _ _ (by omega)
          (fun r hr => (outSub r hr).sub_left (Offset.sub_base _ (by omega))), c₃,
        Proof.Rc2.bytesAt_frame f₁ _ _ (by omega) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact (dataOut.sub_left (Region.sub_prefix hNL)).sub_right (Region.sub_prefix hPN))]
  · -- The pending block: the rest of the data.
    rw [mem₆, hC, hP, hL, hA, hNN, show C + 136 = C + BitVec.ofNat 64 136 from rfl, c₅]
    have dataSub : Region.Sub ⟨A + BitVec.ofNat 64 (N - P), (P + L) % 8⟩ ⟨A, L⟩ := Offset.sub_base _ (by omega)
    rw [Proof.Rc2.bytesAt_frame f₃ _ _ (by omega) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact (dataOut.sub_left dataSub).sub_right (Offset.sub_base _ (by omega))),
      Proof.Rc2.bytesAt_frame f₁ _ _ (by omega) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact (dataOut.sub_left dataSub).sub_right (Region.sub_prefix hPN))]
end VG.Proof.Rc2.X86_64.Stream
