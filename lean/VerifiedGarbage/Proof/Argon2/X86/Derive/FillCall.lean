import VerifiedGarbage.Proof.Argon2.X86.Derive.FillState

/-!
# Argon2 on x86 (32-bit): calls of G in the filling loops

The filling loops call `vg_argon2_compress` in a frame of its four arguments,
`compress(eax, esi, ecx, edx)`: G of the blocks at `eax` and `esi`, each a
cell of the memory matrix or a block of `scratch` from offset 4096 on
(`GArg`), to `scratch + o`, with `scratch[0, 4096)` as its working space
(`ccall_ok`).
-/

namespace VG.Proof.Argon2.X86.Derive

open VG VG.X86
open VG.Spec.Argon2 (Block blockAt compress)
open VG.Proof.Argon2.X86 (blk compressX86)

theorem compress_nosp : NoSp Impl.Argon2.X86.compress := NoSp.of_all (by lit_decide)
theorem compress_stack : stackUse Impl.Argon2.X86.compress = 0 := by lit_decide

/-- `scratch`, as an address. -/
abbrev scrB (s₀ : State) : Addr := (scrP s₀).setWidth 64

/-- A block G may read: a cell of the matrix, or a block of `scratch` from 4096
on apart from the output at offset `o`. -/
def GArg (s₀ : State) (o : Nat) (p : BitVec 32) : Prop :=
  (∃ k < blocksN s₀, p = memP s₀ + BitVec.ofNat 32 (k * 1024)) ∨
    ∃ d, 4096 ≤ d ∧ d + 1024 ≤ 16384 ∧ (d + 1024 ≤ o ∨ o + 1024 ≤ d) ∧ p = scrP s₀ + BitVec.ofNat 32 d

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- What a call needs of a block it reads. -/
theorem GArg.facts {o : Nat} (ho : 4096 ≤ o) (ho' : o + 1024 ≤ 16384) {p : BitVec 32} (h : GArg s₀ o p) :
    (∃ R ∈ [memR s₀, scrR s₀], ∃ off, p.setWidth 64 = R.base + BitVec.ofNat 64 off ∧ off + 1024 ≤ R.len) ∧
    p.toNat + 1024 ≤ 2 ^ 32 ∧
    Region.Disjoint ⟨p.setWidth 64, 1024⟩ ⟨scrB s₀ + BitVec.ofNat 64 o, 1024⟩ ∧
    Region.Disjoint ⟨p.setWidth 64, 1024⟩ ⟨scrB s₀, 4096⟩ ∧
    Region.Disjoint ⟨p.setWidth 64, 1024⟩ (callR s₀) := by
  have hs := hp.scr_fits
  have hm := hp.mem_fits
  rcases h with ⟨k, hk, rfl⟩ | ⟨d, hd, hd', hdo, rfl⟩
  · have hk' : k * 1024 + 1024 ≤ blocksN s₀ * 1024 := by omega
    have e := cell_addr hp hk
    have sub : Region.Sub ⟨(memP s₀ + BitVec.ofNat 32 (k * 1024)).setWidth 64, 1024⟩ (memR s₀) := by
      rw [e]; exact cell_in_mem hk
    refine ⟨⟨memR s₀, by simp, k * 1024, e, hk'⟩, by rw [add_nat (by omega)]; omega, ?_, ?_, ?_⟩
    · exact (hp.mem_scr.sub_left sub).sub_right (Offset.sub_base _ ho')
    · exact (hp.mem_scr.sub_left sub).sub_right (Offset.sub_base (d := 0) (n := 4096) (k := 16384) _ (by omega) |> fun h => by
        simpa using h)
    · exact (call_disj hp (R := memR s₀) (by simp)).symm.sub_left sub
  · have e : (scrP s₀ + BitVec.ofNat 32 d).setWidth 64 = scrB s₀ + BitVec.ofNat 64 d :=
      HPrime.setWidth_add (by omega)
    refine ⟨⟨scrR s₀, by simp, d, e, hd'⟩, by rw [add_nat (by omega)]; omega, ?_, ?_, ?_⟩
    · rw [e]; exact Offset.disjoint _ hdo (by omega) (by omega)
    · rw [e]; exact Offset.disjoint_base _ hd (by omega)
    · rw [e]; exact (call_disj hp (R := scrR s₀) (by simp)).symm.sub_left (Offset.sub_base _ hd')

/-- What G needs, from the body: `compress(eax, esi, ecx, edx)`, to `scratch + o`. -/
theorem ccall_pre {s : State} (h : Inv s₀ s) (hdx : s.gpr .edx = scrP s₀) {o : Nat} (ho : 4096 ≤ o)
    (ho' : o + 1024 ≤ 16384) (hcx : s.gpr .ecx = scrP s₀ + BitVec.ofNat 32 o) (hx : GArg s₀ o (s.gpr .eax))
    (hy : GArg s₀ o (s.gpr .esi)) :
    CallPre compressX86 [.edx, .ecx, .esi, .eax]
      [⟨(s.gpr .eax).setWidth 64, 1024⟩, ⟨(s.gpr .esi).setWidth 64, 1024⟩,
        ⟨(s.gpr .esp - BitVec.ofNat 32 16).setWidth 64, 16⟩]
      [⟨scrB s₀ + BitVec.ofNat 64 o, 1024⟩, ⟨scrB s₀, 4096⟩] s := by
  have hE := E_nat hp
  have hlo := hp.esp_lo
  have hhi := E_hi hp
  have hs := hp.scr_fits
  have esp := h.esp
  have nesp : Reg.esp ∉ [Reg.edx, .ecx, .esi, .eax] := by decide
  have fit : 4 * [Reg.edx, .ecx, .esi, .eax].length + 4 ≤ (s.gpr .esp).toNat := by
    simp only [List.length_cons, List.length_nil]; rw [esp]; omega
  have a0 := callEntry_arg fit nesp (i := 0) (by simp)
  have a1 := callEntry_arg fit nesp (i := 1) (by simp)
  have a2 := callEntry_arg fit nesp (i := 2) (by simp)
  have a3 := callEntry_arg fit nesp (i := 3) (by simp)
  simp only [List.length_cons, List.length_nil, List.getElem_cons_succ, List.getElem_cons_zero,
    Nat.reduceAdd, Nat.reduceSub] at a0 a1 a2 a3
  rw [hdx] at a3
  rw [hcx] at a2
  obtain ⟨⟨RX, hRX, oX, bX, lX⟩, fX, X_out, X_scr, X_call⟩ := hx.facts hp ho ho'
  obtain ⟨⟨RY, hRY, oY, bY, lY⟩, fY, Y_out, Y_scr, Y_call⟩ := hy.facts hp ho ho'
  have eO : (scrP s₀ + BitVec.ofNat 32 o).setWidth 64 = scrB s₀ + BitVec.ofNat 64 o :=
    HPrime.setWidth_add (by omega)
  have memW : ∀ R ∈ [memR s₀, scrR s₀], R ∈ s.wr := fun R hR => by
    rw [h.wr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl
    · exact mem_mem hp
    · exact scr_mem hp
  have scrW : scrR s₀ ∈ s.wr := memW _ (by simp)
  have cX : Covers [⟨(s.gpr .eax).setWidth 64, 1024⟩] s.wr :=
    Covers.of_sub fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact ⟨RX, memW _ hRX, oX, bX, lX⟩
  have cY : Covers [⟨(s.gpr .esi).setWidth 64, 1024⟩] s.wr :=
    Covers.of_sub fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact ⟨RY, memW _ hRY, oY, bY, lY⟩
  have cO : Covers [⟨scrB s₀ + BitVec.ofNat 64 o, 1024⟩] s.wr :=
    Covers.of_sub fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact ⟨scrR s₀, scrW, o, rfl, ho'⟩
  have cW : Covers [⟨scrB s₀, 4096⟩] s.wr :=
    Covers.of_sub fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact ⟨scrR s₀, scrW, 0, by simp, by simp⟩
  have O_W : Region.Disjoint ⟨scrB s₀ + BitVec.ofNat 64 o, 1024⟩ ⟨scrB s₀, 4096⟩ :=
    Offset.disjoint_base _ ho (by omega)
  have O_call : Region.Disjoint ⟨scrB s₀ + BitVec.ofNat 64 o, 1024⟩ (callR s₀) :=
    (call_disj hp (R := scrR s₀) (by simp)).symm.sub_left (Offset.sub_base _ ho')
  have W_call : Region.Disjoint ⟨scrB s₀, 4096⟩ (callR s₀) :=
    (call_disj hp (R := scrR s₀) (by simp)).symm.sub_left (Region.sub_prefix (by decide))
  have e16 : (s.gpr .esp - BitVec.ofNat 32 16).toNat = (E s₀).toNat - 16 := by rw [esp, sub_nat (by omega)]
  have e20 : (s.gpr .esp - BitVec.ofNat 32 20).toNat = (E s₀).toNat - 20 := by rw [esp, sub_nat (by omega)]
  have cA : Region.Sub ⟨(s.gpr .esp - BitVec.ofNat 32 16).setWidth 64, 16⟩ (callR s₀) :=
    in_call hp (by omega) (by omega)
  have cR : Region.Sub ⟨(s.gpr .esp - BitVec.ofNat 32 20).setWidth 64, 4⟩ (callR s₀) :=
    in_call hp (by omega) (by omega)
  have a16 : argAddr (pushed [Reg.edx, .ecx, .esi, .eax] s).callEntry 0 =
      (s.gpr .esp - BitVec.ofNat 32 16).setWidth 64 := callEntry_argAddr0 _ _
  have ce : (pushed [Reg.edx, .ecx, .esi, .eax] s).callEntry.gpr .esp = s.gpr .esp - BitVec.ofNat 32 20 :=
    callEntry_esp' _ _
  refine ⟨?_, ?_, ?_⟩
  · simp only [compressX86, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr, arg_withRegions,
      argAddr_withRegions, a0, a1, a2, a3, a16, ce, eO]
    refine ⟨trivial, trivial, O_W, X_out, X_scr, Y_out, Y_scr, O_call.symm.sub_left cA,
      W_call.symm.sub_left cA, O_call.symm.sub_left cR, W_call.symm.sub_left cR, fX, fY,
      by rw [add_nat (by omega)]; omega, hs |> fun _ => by omega, by rw [e20]; omega⟩
  · intro a n ⟨q, hq, hc⟩
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · obtain ⟨q', hq', hc'⟩ := cX a n ⟨_, List.mem_singleton_self _, hc⟩
      exact InRegions_append_cons.mpr (.inr ⟨q', List.mem_append_right _ hq', hc'⟩)
    · obtain ⟨q', hq', hc'⟩ := cY a n ⟨_, List.mem_singleton_self _, hc⟩
      exact InRegions_append_cons.mpr (.inr ⟨q', List.mem_append_right _ hq', hc'⟩)
    · exact InRegions_append_cons.mpr (.inl (by simpa using hc))
    · obtain ⟨q', hq', hc'⟩ := cO a n ⟨_, List.mem_singleton_self _, hc⟩
      exact InRegions_append_cons.mpr (.inr ⟨q', List.mem_append_right _ hq', hc'⟩)
    · obtain ⟨q', hq', hc'⟩ := cW a n ⟨_, List.mem_singleton_self _, hc⟩
      exact InRegions_append_cons.mpr (.inr ⟨q', List.mem_append_right _ hq', hc'⟩)
  · intro a n ⟨q, hq, hc⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · obtain ⟨q', hq', hc'⟩ := cO a n ⟨_, List.mem_singleton_self _, hc⟩
      exact ⟨q', List.mem_cons_of_mem _ hq', hc'⟩
    · obtain ⟨q', hq', hc'⟩ := cW a n ⟨_, List.mem_singleton_self _, hc⟩
      exact ⟨q', List.mem_cons_of_mem _ hq', hc'⟩

/-- A call of G from the body: `compress(eax, esi, ecx, edx)`, to `scratch + o`. -/
theorem ccall_ok {s : State} (h : Inv s₀ s) (hdx : s.gpr .edx = scrP s₀) {o : Nat} (ho : 4096 ≤ o)
    (ho' : o + 1024 ≤ 16384) (hcx : s.gpr .ecx = scrP s₀ + BitVec.ofNat 32 o) (hx : GArg s₀ o (s.gpr .eax))
    (hy : GArg s₀ o (s.gpr .esi)) {Q : State → Prop}
    (k : ∀ t, Inv s₀ t → (∀ q ∈ calleeSaved, t.gpr q = s.gpr q) →
      Frame [⟨scrB s₀ + BitVec.ofNat 64 o, 1024⟩, ⟨scrB s₀, 4096⟩, callR s₀] s.mem t.mem →
      blk t.mem (scrP s₀) o =
        compress (blockAt s.mem ((s.gpr .eax).setWidth 64)) (blockAt s.mem ((s.gpr .esi).setWidth 64)) → Q t) :
    WP isa (.frame (.push [.edx, .ecx, .esi, .eax]) (.call Impl.Argon2.X86.Derive.compressName
      Impl.Argon2.X86.compress) (.pop .eax 4)) s Q := by
  have hE := E_nat hp
  have hlo := hp.esp_lo
  have hhi := E_hi hp
  have hs := hp.scr_fits
  have esp := h.esp
  have nesp : Reg.esp ∉ [Reg.edx, .ecx, .esi, .eax] := by decide
  have fit : 4 * [Reg.edx, .ecx, .esi, .eax].length + 4 ≤ (s.gpr .esp).toNat := by
    simp only [List.length_cons, List.length_nil]; rw [esp]; omega
  have a0 := callEntry_arg fit nesp (i := 0) (by simp)
  have a1 := callEntry_arg fit nesp (i := 1) (by simp)
  have a2 := callEntry_arg fit nesp (i := 2) (by simp)
  have a3 := callEntry_arg fit nesp (i := 3) (by simp)
  simp only [List.length_cons, List.length_nil, List.getElem_cons_succ, List.getElem_cons_zero,
    Nat.reduceAdd, Nat.reduceSub] at a0 a1 a2 a3
  rw [hdx] at a3
  rw [hcx] at a2
  obtain ⟨⟨RX, hRX, oX, bX, lX⟩, fX, X_out, X_scr, X_call⟩ := hx.facts hp ho ho'
  obtain ⟨⟨RY, hRY, oY, bY, lY⟩, fY, Y_out, Y_scr, Y_call⟩ := hy.facts hp ho ho'
  have eO : (scrP s₀ + BitVec.ofNat 32 o).setWidth 64 = scrB s₀ + BitVec.ofNat 64 o :=
    HPrime.setWidth_add (by omega)
  have memW : ∀ R ∈ [memR s₀, scrR s₀], R ∈ s.wr := fun R hR => by
    rw [h.wr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl
    · exact mem_mem hp
    · exact scr_mem hp
  have scrW : scrR s₀ ∈ s.wr := memW _ (by simp)
  have cX : Covers [⟨(s.gpr .eax).setWidth 64, 1024⟩] s.wr :=
    Covers.of_sub fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact ⟨RX, memW _ hRX, oX, bX, lX⟩
  have cY : Covers [⟨(s.gpr .esi).setWidth 64, 1024⟩] s.wr :=
    Covers.of_sub fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact ⟨RY, memW _ hRY, oY, bY, lY⟩
  have cO : Covers [⟨scrB s₀ + BitVec.ofNat 64 o, 1024⟩] s.wr :=
    Covers.of_sub fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact ⟨scrR s₀, scrW, o, rfl, ho'⟩
  have cW : Covers [⟨scrB s₀, 4096⟩] s.wr :=
    Covers.of_sub fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact ⟨scrR s₀, scrW, 0, by simp, by simp⟩
  have O_W : Region.Disjoint ⟨scrB s₀ + BitVec.ofNat 64 o, 1024⟩ ⟨scrB s₀, 4096⟩ :=
    Offset.disjoint_base _ ho (by omega)
  have O_call : Region.Disjoint ⟨scrB s₀ + BitVec.ofNat 64 o, 1024⟩ (callR s₀) :=
    (call_disj hp (R := scrR s₀) (by simp)).symm.sub_left (Offset.sub_base _ ho')
  have W_call : Region.Disjoint ⟨scrB s₀, 4096⟩ (callR s₀) :=
    (call_disj hp (R := scrR s₀) (by simp)).symm.sub_left (Region.sub_prefix (by decide))
  have e16 : (s.gpr .esp - BitVec.ofNat 32 16).toNat = (E s₀).toNat - 16 := by rw [esp, sub_nat (by omega)]
  have e20 : (s.gpr .esp - BitVec.ofNat 32 20).toNat = (E s₀).toNat - 20 := by rw [esp, sub_nat (by omega)]
  have cA : Region.Sub ⟨(s.gpr .esp - BitVec.ofNat 32 16).setWidth 64, 16⟩ (callR s₀) :=
    in_call hp (by omega) (by omega)
  have cR : Region.Sub ⟨(s.gpr .esp - BitVec.ofNat 32 20).setWidth 64, 4⟩ (callR s₀) :=
    in_call hp (by omega) (by omega)
  have a16 : argAddr (pushed [Reg.edx, .ecx, .esi, .eax] s).callEntry 0 =
      (s.gpr .esp - BitVec.ofNat 32 16).setWidth 64 := callEntry_argAddr0 _ _
  have ce : (pushed [Reg.edx, .ecx, .esi, .eax] s).callEntry.gpr .esp = s.gpr .esp - BitVec.ofNat 32 20 :=
    callEntry_esp' _ _
  have pre := ccall_pre hp h hdx ho ho' hcx hx hy
  refine WP.callWith Proof.Argon2.X86.compress_verified.1 compress_nosp (by simp) nesp
    (by rw [compress_stack, esp]; simp only [List.length_cons, List.length_nil]; omega) pre
    fun t rd' wr' cs' f' ⟨s₂, m₂, post⟩ => ?_
  simp only [compressX86, arg_withRegions, State.withRegions_mem, a0, a1, a2] at post
  have cB : Region.Sub (below (s.gpr .esp) 20) (callR s₀) := in_call hp (by rw [e20]; omega) (by rw [e20]; omega)
  have cf := callEntry_frame fit nesp
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul, Nat.zero_add] at cf
  rw [compress_stack] at f'
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul, Nat.zero_add] at f'
  rw [m₂, blockAt_keep cf (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact X_call.sub_right cB),
    blockAt_keep cf (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact Y_call.sub_right cB),
    Proof.Argon2.X86.blockAt_eq (by rw [add_nat (by omega)]; omega), blk_shift] at post
  have f₁ : Frame [⟨scrB s₀ + BitVec.ofNat 64 o, 1024⟩, ⟨scrB s₀, 4096⟩, callR s₀] s.mem t.mem :=
    f'.sub fun q hq => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
      · exact ⟨callR s₀, by simp, cB⟩
  refine k t (h.step (cs' .esp (by decide)) (cs' .ebp (by decide)) rd' wr' (f₁.sub fun q hq => ?_)) cs' f₁ post
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact ⟨scrR s₀, by simp, Offset.sub_base _ ho'⟩
  · exact ⟨scrR s₀, by simp, Region.sub_prefix (by decide)⟩
  · exact ⟨_, by simp, fun _ h => h⟩

end

end VG.Proof.Argon2.X86.Derive
