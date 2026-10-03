import VerifiedGarbage.Proof.Argon2.X86.HPrime.Contract
import VerifiedGarbage.Proof.Blake2.X86.Blake2b

/-!
# Argon2 H′ on x86 (32-bit): the calls of the BLAKE2b functions

`init_ok`, `update_ok`, `finalize_ok`: H′'s macros (`Impl.Argon2.X86.HPrime`)
call the x86 BLAKE2b streaming functions with the state at `scratch` (in
`ebx`, at `B`), their scratch at `scratch + 192`, and the stack below `esp`
(`E`). Each is stated for any `B` and `E`, so that the derivation can use them
too: they write only the state, their scratch, the digest (`finalize`) and
the stack below `E`, and keep `ebx`, `ebp` and `esp`.
-/

namespace VG.Proof.Argon2.X86.HPrime

open VG VG.X86 VG.Spec.Blake2
open VG.Impl.Argon2.X86.HPrime (update finalize initCode updateCode finalizeCode initName
  updateName finalizeName)
open VG.Proof.Blake2 (initX86 updateX86 finalizeX86 countX86)
open VG.Proof.Sha256.X86.Stream (Upd wp_movi wp_mov wp_addi)

/-! ## The callees -/

theorem init_correct : ∀ s, (initX86 b).pre s →
    ∃ t s', Exec isa initCode s t s' ∧ abiPreserved s s' ∧ (initX86 b).post s s' :=
  (Proof.Blake2.X86.Stream.init_verified Proof.Blake2.X86.B.ok Proof.Blake2.X86.B.init_ct
    Proof.Blake2.X86.B.init_implies.sat_left).1

theorem update_correct : ∀ s, (updateX86 b).pre s →
    ∃ t s', Exec isa updateCode s t s' ∧ abiPreserved s s' ∧ (updateX86 b).post s s' :=
  (Proof.Blake2.X86.Stream.update_verified Proof.Blake2.X86.B.ok Proof.Blake2.X86.B.callee
    Proof.Blake2.X86.B.update_ct Proof.Blake2.X86.B.update_implies.sat_left).1

theorem finalize_correct : ∀ s, (finalizeX86 b).pre s →
    ∃ t s', Exec isa finalizeCode s t s' ∧ abiPreserved s s' ∧ (finalizeX86 b).post s s' :=
  (Proof.Blake2.X86.Stream.finalize_verified Proof.Blake2.X86.B.ok Proof.Blake2.X86.B.callee
    Proof.Blake2.X86.B.finalize_ct Proof.Blake2.X86.B.finalize_implies.sat_left).1

theorem init_nosp : NoSp initCode := NoSp.of_all (by lit_decide)
theorem update_nosp : NoSp updateCode := NoSp.of_all (by lit_decide)
theorem finalize_nosp : NoSp finalizeCode := NoSp.of_all (by lit_decide)
theorem init_stack : stackUse initCode = 0 := by lit_decide
theorem update_stack : stackUse updateCode = 32 := by lit_decide
theorem finalize_stack : stackUse finalizeCode = 32 := by lit_decide

/-! ## Regions -/

/-- `[x + d, x + d + n)`, for a buffer at `x` inside the 32-bit address space. -/
theorem setWidth_add {x : BitVec 32} {d : Nat} (h : x.toNat + d < 2 ^ 32) :
    (x + BitVec.ofNat 32 d).setWidth 64 = x.setWidth 64 + BitVec.ofNat 64 d := addr_eq h

/-- What every call needs: `ebx` holds `B`, `esp` is `E`, the state, the
callees' scratch and the digest (`scratch[0, 832)`) are writable, and the 60
bytes below `E` are outside them. -/
structure Ctx (B E : BitVec 32) (s : State) : Prop where
  ebx : s.gpr .ebx = B
  esp : s.gpr .esp = E
  fits : B.toNat + 832 ≤ 2 ^ 32
  lo : 60 ≤ E.toNat
  hi : E.toNat + 4 ≤ 2 ^ 32
  wr : Covers [⟨B.setWidth 64, 832⟩] s.wr
  stk : (below E 60).Disjoint ⟨B.setWidth 64, 832⟩

theorem Ctx.of_regs {B E : BitVec 32} {s t : State} (h : Ctx B E s) (hb : t.gpr .ebx = s.gpr .ebx)
    (hs : t.gpr .esp = s.gpr .esp) (hw : t.wr = s.wr) : Ctx B E t :=
  ⟨hb.trans h.ebx, hs.trans h.esp, h.fits, h.lo, h.hi, hw ▸ h.wr, h.stk⟩

section
variable {B E : BitVec 32} {s : State}

theorem Ctx.sub (_h : Ctx B E s) {d n : Nat} (hd : d + n ≤ 832) :
    Region.Sub ⟨B.setWidth 64 + BitVec.ofNat 64 d, n⟩ ⟨B.setWidth 64, 832⟩ :=
  Offset.sub_base _ hd

theorem Ctx.cov (h : Ctx B E s) {d n : Nat} (hd : d + n ≤ 832) :
    Covers [⟨B.setWidth 64 + BitVec.ofNat 64 d, n⟩] s.wr :=
  (Covers.of_sub (rs' := [⟨B.setWidth 64, 832⟩]) fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, d, rfl, hd⟩).trans h.wr

theorem Ctx.stk_sub (h : Ctx B E s) {d n k : Nat} (hd : d + n ≤ 832) (hk : k ≤ 60) :
    (below E k).Disjoint ⟨B.setWidth 64 + BitVec.ofNat 64 d, n⟩ :=
  (h.stk.sub_right (h.sub hd)).sub_left (below_sub hk h.lo)

theorem Ctx.cov0 (h : Ctx B E s) {n : Nat} (hn : n ≤ 832) : Covers [⟨B.setWidth 64, n⟩] s.wr :=
  (Covers.of_sub (rs' := [⟨B.setWidth 64, 832⟩]) fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, 0, by simp, by simp; omega⟩).trans h.wr

end

theorem covers_ins {rs a b : List Region} (f : Region) (h : Covers rs (a ++ b)) :
    Covers rs (a ++ f :: b) := fun x n hi => InRegions_append_cons.mpr (.inr (h x n hi))

theorem covers_cons {rs b : List Region} (f : Region) (h : Covers rs b) : Covers rs (f :: b) :=
  fun x n hi => let ⟨r, hr, hc⟩ := h x n hi; ⟨r, List.mem_cons_of_mem _ hr, hc⟩

theorem covers_frame {E : BitVec 32} {k : Nat} {rd : List Region} {a : Addr}
    (ha : a = (E - BitVec.ofNat 32 k).setWidth 64) (wr : List Region) :
    Covers [⟨a, k⟩] (rd ++ below E k :: wr) := by
  intro x n ⟨r, hr, hc⟩
  simp only [List.mem_singleton] at hr; subst hr
  exact InRegions_append_cons.mpr (.inl (by subst ha; exact hc))

/-! ## `init` -/

theorem keyBlock_nil (m : Mem) (p : Addr) : keyBlock 64 (bytesAt m p 0) = [] := rfl

theorem init_ok {B E : BitVec 32} {s : State} (h : Ctx B E s) {n : Nat} (hn : s.gpr .edx = BitVec.ofNat 32 n)
    (hn₁ : 1 ≤ n) (hn₂ : n ≤ 64) :
    WP isa Impl.Argon2.X86.HPrime.init s fun t => Repr b (Spec.Blake2.init b n 0) t.mem (B.setWidth 64) [] ∧
      (∀ r ∈ calleeSaved, t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Frame [⟨B.setWidth 64, 192⟩, below E 20] s.mem t.mem := by
  unfold Impl.Argon2.X86.HPrime.init
  refine WP.seq (wp_movi fun s₁ u₁ => wp_mov fun s₂ u₂ => WP.block_nil ?_)
  have rs : [Reg.eax, .ecx, .edx, .ebx] ≠ [] := by simp
  have hrs : Reg.esp ∉ [Reg.eax, .ecx, .edx, .ebx] := by decide
  have esp₂ : s₂.gpr .esp = E := by rw [u₂.other _ (by decide), u₁.other _ (by decide), h.esp]
  have fit : 4 * [Reg.eax, .ecx, .edx, .ebx].length + 4 ≤ (s₂.gpr .esp).toNat := by
    rw [esp₂]; have := h.lo; simp only [List.length_cons, List.length_nil]; omega
  set sE := (pushed [Reg.eax, .ecx, .edx, .ebx] s₂).callEntry with hsE
  have a0 : arg sE 0 = B := by
    rw [hsE, callEntry_arg fit hrs (by simp)]
    simp [u₂.other _ (by decide : Reg.ebx ≠ .ecx), u₁.other _ (by decide : Reg.ebx ≠ .eax), h.ebx]
  have a1 : arg sE 1 = BitVec.ofNat 32 n := by
    rw [hsE, callEntry_arg fit hrs (by simp)]
    simp [u₂.other _ (by decide : Reg.edx ≠ .ecx), u₁.other _ (by decide : Reg.edx ≠ .eax), hn]
  have a2 : arg sE 2 = B := by
    rw [hsE, callEntry_arg fit hrs (by simp)]
    simp [u₂.gpr, u₁.other _ (by decide : Reg.ebx ≠ .eax), h.ebx]
  have a3 : arg sE 3 = 0 := by
    rw [hsE, callEntry_arg fit hrs (by simp)]
    simp [u₂.other _ (by decide : Reg.eax ≠ .ecx), u₁.gpr]
  have eA : argAddr sE 0 = (E - BitVec.ofNat 32 16).setWidth 64 := by
    rw [hsE, callEntry_argAddr0, esp₂]; rfl
  have eSp : sE.gpr .esp = E - BitVec.ofNat 32 20 := by
    rw [hsE, callEntry_esp', esp₂]; rfl
  have w₂ : s₂.wr = s.wr := u₂.wr.trans u₁.wr
  have stR : Region.Sub ⟨B.setWidth 64, 192⟩ ⟨B.setWidth 64, 832⟩ := Region.sub_prefix (by decide)
  have d20 : (below E 20).Disjoint ⟨B.setWidth 64, 192⟩ :=
    (h.stk.sub_right stR).sub_left (below_sub (by decide) h.lo)
  refine WP.callWith (k := initX86 b) init_correct init_nosp rs hrs
    (by rw [init_stack, esp₂]; have := h.lo; simp only [List.length_cons, List.length_nil]; omega)
    (rd := [⟨(B.setWidth 64), 0⟩, ⟨argAddr sE 0, 16⟩]) (wr := [⟨B.setWidth 64, 192⟩])
    ⟨?_, ?_, ?_⟩ fun t rd' wr' cs' f' ⟨s₃, m₃, post⟩ => ?_
  · rw [← hsE]
    simp only [initX86, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr,
      arg_withRegions, argAddr_withRegions, a0, a1, a2, a3, eA, eSp]
    have mb : (64 : Nat) ≤ b.maxBytes := by decide
    refine ⟨rfl, rfl, fun _ h₁ _ => by simp [Region.Contains] at h₁, ?_, ?_,
      by simp only [Proof.Blake2.bufOff, blockBytes]; have := h.fits; omega,
      by simp; have := B.isLt; omega, ?_, by simp [BitVec.toNat_ofNat]; omega,
      by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega, by simp⟩
    · exact d20.sub_left (below_sub (by decide) (by have := h.lo; omega))
    · refine d20.sub_left ?_
      have := below_inner (sp := E) (a := 4) (b := 20) (k := 16) (by omega) (by have := h.lo; omega)
      rw [show E - BitVec.ofNat 32 20 = E - BitVec.ofNat 32 16 - BitVec.ofNat 32 4 by
        rw [← VG.Offset.sub_add_eq]; rfl]
      exact this
    · rw [sub_toNat (by have := h.lo; omega)]; have := E.isLt; omega
  · rw [esp₂, w₂]
    refine Covers.append_left (Covers.cons ?_ (Covers.cons ?_ Covers.nil)) ?_
    · intro a k ⟨r, hr, hc⟩
      simp only [List.mem_singleton] at hr; subst hr
      obtain ⟨r', hr', hc'⟩ := h.wr a k ⟨_, List.mem_singleton_self _, by
        simp only [Region.Contains] at hc ⊢; omega⟩
      exact InRegions_append_cons.mpr (.inr ⟨r', List.mem_append_right _ hr', hc'⟩)
    · intro a k ⟨r, hr, hc⟩
      simp only [List.mem_singleton] at hr; subst hr
      refine InRegions_append_cons.mpr (.inl ?_)
      rw [eA] at hc; simpa using hc
    · exact (Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_singleton_self _, 0, by simp, by simp⟩).trans
        ((h.wr.trans fun a k hi => let ⟨r', hr', hc'⟩ := hi
          InRegions_append_cons.mpr (.inr ⟨r', List.mem_append_right _ hr', hc'⟩)))
  · rw [esp₂, w₂]
    exact (Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_singleton_self _, 0, by simp, by simp⟩).trans
      (h.wr.trans fun a k ⟨r', hr', hc'⟩ => ⟨r', List.mem_cons_of_mem _ hr', hc'⟩)
  · rw [← hsE] at post
    simp only [initX86, arg_withRegions, State.withRegions_mem, a0, a1, a3, m₃] at post
    refine ⟨?_, fun r hr => (cs' r hr).trans ?_, rd'.trans (u₂.rd.trans u₁.rd), wr'.trans w₂, ?_⟩
    · have kb : ∀ (m : Mem) (p : Addr), keyBlock 64 (bytesAt m p (BitVec.toNat (0 : BitVec 32))) = [] :=
        fun _ _ => rfl
      rw [kb, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show n < 2 ^ 32 by omega)] at post
      exact post
    · have : r ≠ .eax ∧ r ≠ .ecx := by
        simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
      rw [u₂.other _ this.2, u₁.other _ this.1]
    · rw [init_stack, esp₂] at f'
      rw [← u₁.mem, ← u₂.mem]
      exact f'.mono fun r hr => by
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> simp

/-! ## Streaming states in memory -/

/-- A streaming state is kept while only memory outside its 192 bytes changes. -/
theorem repr_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, 192⟩ r) {h0 : HashValue 64} {d : List Byte}
    (h : Repr b h0 m p d) : Repr b h0 m' p d := by
  have hb : ∀ i < 192, m' (p + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i) :=
    fun i hi => hf.bytes (R := ⟨p, 192⟩) hd (by simp) hi
  obtain ⟨h1, h2⟩ := h
  have hl := Proof.Blake2.bufLen_le (w := 64) (by decide) d.length
  have hs := Proof.Blake2.sub_bufLen (w := 64) d
  have hs' := Proof.Blake2.bufLen_le_self (w := 64) d.length
  refine ⟨?_, ?_⟩
  · rw [Proof.Blake2.stateAt_congr (fun i hi => hb i (by simp only [Proof.Blake2.bufOff] at hi; omega))]
    exact h1
  · rw [← h2]
    apply Proof.Blake2.bytesAt_congr
    intro i hi
    rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    have hbb : blockBytes 64 = 128 := rfl
    rw [hbb] at hl hs hi
    exact hb _ (by omega)

/-! ## `update` -/

/-- `update` hashes the `L` bytes at `D` (in `esi` and `edi`) into the state at
`B`, whose byte count is in `edx:ecx`. -/
theorem update_ok {B E : BitVec 32} {s : State} (h : Ctx B E s) {D : BitVec 32} {L : Nat}
    (hD : s.gpr .esi = D) (hL : (s.gpr .edi).toNat = L) (hDfit : D.toNat + L ≤ 2 ^ 32)
    (hDc : Covers [⟨D.setWidth 64, L⟩] (s.rd ++ s.wr))
    (hDs : Region.Disjoint ⟨D.setWidth 64, L⟩ ⟨B.setWidth 64, 768⟩)
    (hDk : (below E 60).Disjoint ⟨D.setWidth 64, L⟩)
    {h0 : HashValue 64} {d : List Byte} (repr : Repr b h0 s.mem (B.setWidth 64) d)
    (hc : s.gpr .edx ++ s.gpr .ecx = BitVec.ofNat 64 d.length) (hlen : d.length + L < 2 ^ 64) :
    WP isa update s fun t => Repr b h0 t.mem (B.setWidth 64) (d ++ bytesAt s.mem (D.setWidth 64) L) ∧
      (∀ r ∈ calleeSaved, t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Frame [⟨B.setWidth 64, 768⟩, below E 60] s.mem t.mem := by
  unfold update
  refine WP.seq (wp_mov fun s₁ u₁ => wp_addi fun s₂ u₂ => WP.block_nil ?_)
  have rs : [Reg.eax, .edi, .esi, .edx, .ecx, .ebx] ≠ [] := by simp
  have hrs : Reg.esp ∉ [Reg.eax, .edi, .esi, .edx, .ecx, .ebx] := by decide
  have o₂ : ∀ r, r ≠ .eax → s₂.gpr r = s.gpr r := fun r hr => by
    rw [u₂.other _ hr, u₁.other _ hr]
  have esp₂ : s₂.gpr .esp = E := by rw [o₂ _ (by decide), h.esp]
  have hlo := h.lo
  have fit : 4 * [Reg.eax, .edi, .esi, .edx, .ecx, .ebx].length + 4 ≤ (s₂.gpr .esp).toNat := by
    rw [esp₂]; simp only [List.length_cons, List.length_nil]; omega
  set sE := (pushed [Reg.eax, .edi, .esi, .edx, .ecx, .ebx] s₂).callEntry with hsE
  have a0 : arg sE 0 = B := by
    rw [hsE, callEntry_arg fit hrs (by simp)]; simp [o₂ .ebx (by decide), h.ebx]
  have a1 : arg sE 1 = s.gpr .ecx := by
    rw [hsE, callEntry_arg fit hrs (by simp)]; simp [o₂ .ecx (by decide)]
  have a2 : arg sE 2 = s.gpr .edx := by
    rw [hsE, callEntry_arg fit hrs (by simp)]; simp [o₂ .edx (by decide)]
  have a3 : arg sE 3 = D := by
    rw [hsE, callEntry_arg fit hrs (by simp)]; simp [o₂ .esi (by decide), hD]
  have a4 : (arg sE 4).toNat = L := by
    rw [hsE, callEntry_arg fit hrs (by simp)]; simp [o₂ .edi (by decide), hL]
  have a5 : arg sE 5 = B + 192 := by
    rw [hsE, callEntry_arg fit hrs (by simp)]; simp [u₂.gpr, u₁.gpr, h.ebx]
  have eA : argAddr sE 0 = (E - BitVec.ofNat 32 24).setWidth 64 := by
    rw [hsE, callEntry_argAddr0, esp₂]; rfl
  have eSp : sE.gpr .esp = E - BitVec.ofNat 32 28 := by
    rw [hsE, callEntry_esp', esp₂]; rfl
  have w₂ : s₂.wr = s.wr := u₂.wr.trans u₁.wr
  have r₂ : s₂.rd = s.rd := u₂.rd.trans u₁.rd
  have hfit := h.fits
  have e192 : (B + 192).setWidth 64 = B.setWidth 64 + 192 := setWidth_add (d := 192) (by omega)
  have stR : (below E 60).Disjoint ⟨B.setWidth 64, 192⟩ :=
    h.stk.sub_right (Region.sub_prefix (by decide))
  have scR : (below E 60).Disjoint ⟨B.setWidth 64 + 192, 576⟩ := h.stk_sub (d := 192) (by decide) (Nat.le_refl _)
  have stk60 : ∀ {k : Nat} {r : Region}, k ≤ 60 → (below E 60).Disjoint r → (below E k).Disjoint r :=
    fun hk d => d.sub_left (below_sub hk hlo)
  have retSub : Region.Sub ⟨(E - BitVec.ofNat 32 28).setWidth 64, 4⟩ (below E 60) := by
    have := below_inner (sp := E) (a := 4) (b := 60) (k := 24) (by omega) hlo
    rw [show E - BitVec.ofNat 32 28 = E - BitVec.ofNat 32 24 - BitVec.ofNat 32 4 by
      rw [← VG.Offset.sub_add_eq]; rfl]
    exact this
  have calleeStk : Region.Sub ⟨(E - BitVec.ofNat 32 28).setWidth 64 - 32, 32⟩ (below E 60) := by
    have := below_inner (sp := E) (a := 32) (b := 60) (k := 28) (by omega) hlo
    have e : (E - BitVec.ofNat 32 28 - BitVec.ofNat 32 32).setWidth 64 =
        (E - BitVec.ofNat 32 28).setWidth 64 - 32 :=
      Taint.sub_setWidth (m := 32) (by rw [sub_toNat (by omega)]; omega)
    show Region.Sub ⟨_, 32⟩ _
    rw [← e]; exact this
  have argSub : Region.Sub ⟨(E - BitVec.ofNat 32 24).setWidth 64, 24⟩ (below E 60) :=
    below_sub (by decide) hlo
  have b192 : (B + 192).toNat = B.toNat + 192 := by
    rw [BitVec.toNat_add, show (192 : BitVec 32).toNat = 192 from rfl]; omega
  refine WP.callWith (k := updateX86 b) update_correct update_nosp rs hrs
    (by rw [update_stack, esp₂]; simp only [List.length_cons, List.length_nil]; omega)
    (rd := [⟨D.setWidth 64, L⟩, ⟨argAddr sE 0, 24⟩])
    (wr := [⟨B.setWidth 64, 192⟩, ⟨B.setWidth 64 + 192, 576⟩])
    ⟨?_, ?_, ?_⟩ fun t rd' wr' cs' f' ⟨s₃, m₃, post⟩ => ?_
  · rw [← hsE]
    simp only [updateX86, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr,
      arg_withRegions, argAddr_withRegions, a0, a3, a4, a5, eA, eSp, e192, Proof.Blake2.bufOff,
      blockBytes, Nat.reduceDiv, Nat.reduceMul, Nat.reduceAdd]
    refine ⟨trivial, trivial, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact Offset.base_disjoint _ (by decide) (by decide)
    · exact hDs.sub_right (Region.sub_prefix (by decide))
    · exact hDs.sub_right (Offset.sub_base _ (by decide))
    · exact stR.sub_left argSub
    · exact scR.sub_left argSub
    · exact stR.sub_left retSub
    · exact scR.sub_left retSub
    · exact stR.sub_left calleeStk
    · exact scR.sub_left calleeStk
    · exact hDk.sub_left calleeStk
    · omega
    · omega
    · rw [b192]; omega
    · rw [sub_toNat (by omega)]; omega
    · rw [sub_toNat (by omega)]; have := E.isLt; omega
  · rw [esp₂, w₂, r₂]
    refine Covers.append_left (Covers.cons (covers_ins _ hDc) (Covers.cons (covers_frame eA _)
      Covers.nil)) (covers_ins _ (Covers.right ((h.cov0 (by decide)).pair (h.cov (d := 192) (by decide)))))
  · rw [esp₂, w₂]
    exact covers_cons _ ((h.cov0 (by decide)).pair (h.cov (d := 192) (by decide)))
  · rw [update_stack, esp₂] at f'
    have hpush : Frame [below E 28] s₂.mem sE.mem := by
      have := callEntry_frame fit hrs; rw [esp₂] at this; exact this
    have mE : s₂.mem = s.mem := u₂.mem.trans u₁.mem
    rw [← hsE] at post
    simp only [updateX86, arg_withRegions, State.withRegions_mem, a0, a3, a4, m₃] at post
    have reprE : Repr b h0 sE.mem (B.setWidth 64) d :=
      repr_frame hpush (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (stk60 (by decide) stR).symm) (mE ▸ repr)
    have countE : countX86 (sE.withRegions [⟨D.setWidth 64, L⟩, ⟨argAddr sE 0, 24⟩]
        [⟨B.setWidth 64, 192⟩, ⟨B.setWidth 64 + 192, 576⟩]) = BitVec.ofNat 64 d.length := by
      simp only [countX86, arg_withRegions]
      rw [hsE, callEntry_arg fit hrs (by simp), callEntry_arg fit hrs (by simp)]
      simpa [o₂ .ecx (by decide), o₂ .edx (by decide)] using hc
    have dataE : bytesAt sE.mem (D.setWidth 64) L = bytesAt s.mem (D.setWidth 64) L := by
      rw [← mE]
      exact Proof.Blake2.bytesAt_congr fun i hi =>
        hpush.bytes (R := ⟨D.setWidth 64, L⟩) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact (stk60 (by decide) hDk).symm) (by simp; omega) hi
    have := post h0 d reprE (by simpa using countE) (by omega)
    rw [dataE] at this
    refine ⟨this, fun r hr => (cs' r hr).trans ?_, rd'.trans r₂, wr'.trans w₂, ?_⟩
    · have : r ≠ .eax := by
        simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
      exact o₂ r this
    · rw [← mE]
      exact f'.sub fun r hr => by
        simp only [List.cons_append, List.nil_append, List.mem_cons,
          List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ⟨_, List.mem_cons_self, Region.sub_prefix (by decide)⟩
        · exact ⟨_, List.mem_cons_self, Offset.sub_base _ (by decide)⟩
        · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, below_sub (by decide) hlo⟩

/-! ## `finalize` -/

/-- `finalize` writes the hash of the data in the state at `B`, whose byte
count is in `edx:ecx`, to `scratch[768, 832)`. -/
theorem finalize_ok {B E : BitVec 32} {s : State} (h : Ctx B E s)
    {h0 : HashValue 64} {d : List Byte} (repr : Repr b h0 s.mem (B.setWidth 64) d)
    (hc : s.gpr .edx ++ s.gpr .ecx = BitVec.ofNat 64 d.length) (hlen : d.length < 2 ^ 64) :
    WP isa finalize s fun t => bytesAt t.mem (B.setWidth 64 + 768) 64 = finalHash b h0 d ∧
      (∀ r ∈ calleeSaved, r ≠ .esi → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Frame [⟨B.setWidth 64, 832⟩, below E 60] s.mem t.mem := by
  unfold finalize
  refine WP.seq (wp_mov fun s₁ u₁ => wp_addi fun s₂ u₂ => wp_mov fun s₃ u₃ => wp_addi fun s₄ u₄ =>
    WP.block_nil ?_)
  have rs : [Reg.eax, .esi, .edx, .ecx, .ebx] ≠ [] := by simp
  have hrs : Reg.esp ∉ [Reg.eax, .esi, .edx, .ecx, .ebx] := by decide
  have o₄ : ∀ r, r ≠ .eax → r ≠ .esi → s₄.gpr r = s.gpr r := fun r h1 h2 => by
    rw [u₄.other _ h2, u₃.other _ h2, u₂.other _ h1, u₁.other _ h1]
  have esp₄ : s₄.gpr .esp = E := by rw [o₄ _ (by decide) (by decide), h.esp]
  have hlo := h.lo
  have hfit := h.fits
  have fit : 4 * [Reg.eax, .esi, .edx, .ecx, .ebx].length + 4 ≤ (s₄.gpr .esp).toNat := by
    rw [esp₄]; simp only [List.length_cons, List.length_nil]; omega
  set sE := (pushed [Reg.eax, .esi, .edx, .ecx, .ebx] s₄).callEntry with hsE
  have a0 : arg sE 0 = B := by
    rw [hsE, callEntry_arg fit hrs (by simp)]; simp [o₄ .ebx (by decide) (by decide), h.ebx]
  have a1 : arg sE 1 = s.gpr .ecx := by
    rw [hsE, callEntry_arg fit hrs (by simp)]; simp [o₄ .ecx (by decide) (by decide)]
  have a2 : arg sE 2 = s.gpr .edx := by
    rw [hsE, callEntry_arg fit hrs (by simp)]; simp [o₄ .edx (by decide) (by decide)]
  have a3 : arg sE 3 = B + 768 := by
    rw [hsE, callEntry_arg fit hrs (by simp)]
    simp [u₄.gpr, u₃.gpr, u₂.other _ (by decide : Reg.ebx ≠ .eax), u₁.other _ (by decide : Reg.ebx ≠ .eax),
      h.ebx]
  have a4 : arg sE 4 = B + 192 := by
    rw [hsE, callEntry_arg fit hrs (by simp)]
    simp [u₄.other _ (by decide : Reg.eax ≠ .esi), u₃.other _ (by decide : Reg.eax ≠ .esi), u₂.gpr, u₁.gpr,
      h.ebx]
  have eA : argAddr sE 0 = (E - BitVec.ofNat 32 20).setWidth 64 := by
    rw [hsE, callEntry_argAddr0, esp₄]; rfl
  have eSp : sE.gpr .esp = E - BitVec.ofNat 32 24 := by
    rw [hsE, callEntry_esp', esp₄]; rfl
  have w₄ : s₄.wr = s.wr := u₄.wr.trans (u₃.wr.trans (u₂.wr.trans u₁.wr))
  have r₄ : s₄.rd = s.rd := u₄.rd.trans (u₃.rd.trans (u₂.rd.trans u₁.rd))
  have mE : s₄.mem = s.mem := u₄.mem.trans (u₃.mem.trans (u₂.mem.trans u₁.mem))
  have e192 : (B + 192).setWidth 64 = B.setWidth 64 + 192 := setWidth_add (d := 192) (by omega)
  have e768 : (B + 768).setWidth 64 = B.setWidth 64 + 768 := setWidth_add (d := 768) (by omega)
  have stR : (below E 60).Disjoint ⟨B.setWidth 64, 192⟩ :=
    (h.stk.sub_right (Region.sub_prefix (by decide)))
  have scR : (below E 60).Disjoint ⟨B.setWidth 64 + 192, 576⟩ := h.stk_sub (d := 192) (by decide) (Nat.le_refl _)
  have dgR : (below E 60).Disjoint ⟨B.setWidth 64 + 768, 64⟩ := h.stk_sub (d := 768) (by decide) (Nat.le_refl _)
  have argSub : Region.Sub ⟨(E - BitVec.ofNat 32 20).setWidth 64, 20⟩ (below E 60) :=
    below_sub (by decide) hlo
  have retSub : Region.Sub ⟨(E - BitVec.ofNat 32 24).setWidth 64, 4⟩ (below E 60) := by
    have := below_inner (sp := E) (a := 4) (b := 60) (k := 20) (by omega) hlo
    rw [show E - BitVec.ofNat 32 24 = E - BitVec.ofNat 32 20 - BitVec.ofNat 32 4 by
      rw [← VG.Offset.sub_add_eq]; rfl]
    exact this
  have calleeStk : Region.Sub ⟨(E - BitVec.ofNat 32 24).setWidth 64 - 32, 32⟩ (below E 60) := by
    have := below_inner (sp := E) (a := 32) (b := 60) (k := 24) (by omega) hlo
    have e : (E - BitVec.ofNat 32 24 - BitVec.ofNat 32 32).setWidth 64 =
        (E - BitVec.ofNat 32 24).setWidth 64 - 32 :=
      Taint.sub_setWidth (m := 32) (by rw [sub_toNat (by omega)]; omega)
    show Region.Sub ⟨_, 32⟩ _
    rw [← e]; exact this
  have b192 : (B + 192).toNat = B.toNat + 192 := by
    rw [BitVec.toNat_add, show (192 : BitVec 32).toNat = 192 from rfl]; omega
  have b768 : (B + 768).toNat = B.toNat + 768 := by
    rw [BitVec.toNat_add, show (768 : BitVec 32).toNat = 768 from rfl]; omega
  refine WP.callWith (k := finalizeX86 b) finalize_correct finalize_nosp rs hrs
    (by rw [finalize_stack, esp₄]; simp only [List.length_cons, List.length_nil]; omega)
    (rd := [⟨argAddr sE 0, 20⟩])
    (wr := [⟨B.setWidth 64, 192⟩, ⟨B.setWidth 64 + 768, 64⟩, ⟨B.setWidth 64 + 192, 576⟩])
    ⟨?_, ?_, ?_⟩ fun t rd' wr' cs' f' ⟨s₃, m₃, post⟩ => ?_
  · rw [← hsE]
    simp only [finalizeX86, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr,
      arg_withRegions, argAddr_withRegions, a0, a3, a4, eA, eSp, e192, e768, Proof.Blake2.bufOff,
      blockBytes, Nat.reduceDiv, Nat.reduceMul, Nat.reduceAdd]
    refine ⟨trivial, trivial, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact Offset.base_disjoint _ (by decide) (by decide)
    · exact Offset.base_disjoint _ (by decide) (by decide)
    · exact Offset.disjoint _ (by decide) (by decide) (by decide)
    · exact stR.sub_left argSub
    · exact dgR.sub_left argSub
    · exact scR.sub_left argSub
    · exact stR.sub_left retSub
    · exact dgR.sub_left retSub
    · exact scR.sub_left retSub
    · exact stR.sub_left calleeStk
    · exact dgR.sub_left calleeStk
    · exact scR.sub_left calleeStk
    · omega
    · rw [b768]; omega
    · rw [b192]; omega
    · rw [sub_toNat (by omega)]; omega
    · rw [sub_toNat (by omega)]; have := E.isLt; omega
  · rw [esp₄, w₄, r₄]
    refine Covers.append_left (Covers.cons (covers_frame eA _) Covers.nil)
      (covers_ins _ (Covers.right ((h.cov0 (by decide)).cons ((h.cov (d := 768) (by decide)).pair
        (h.cov (d := 192) (by decide))))))
  · rw [esp₄, w₄]
    exact covers_cons _ ((h.cov0 (by decide)).cons ((h.cov (d := 768) (by decide)).pair
      (h.cov (d := 192) (by decide))))
  · rw [finalize_stack, esp₄] at f'
    have hpush : Frame [below E 24] s₄.mem sE.mem := by
      have := callEntry_frame fit hrs; rw [esp₄] at this; exact this
    rw [← hsE] at post
    simp only [finalizeX86, arg_withRegions, State.withRegions_mem, a0, a3, e768, m₃] at post
    have reprE : Repr b h0 sE.mem (B.setWidth 64) d :=
      repr_frame hpush (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (stR.sub_left (below_sub (by decide) hlo)).symm) (mE ▸ repr)
    have countE : countX86 (sE.withRegions [⟨argAddr sE 0, 20⟩]
        [⟨B.setWidth 64, 192⟩, ⟨B.setWidth 64 + 768, 64⟩, ⟨B.setWidth 64 + 192, 576⟩]) =
        BitVec.ofNat 64 d.length := by
      simp only [countX86, arg_withRegions, a1, a2]; exact hc
    refine ⟨post h0 d reprE hlen countE, fun r hr hne => (cs' r hr).trans ?_, rd'.trans r₄, wr'.trans w₄, ?_⟩
    · have : r ≠ .eax := by
        simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
      exact o₄ r this hne
    · rw [← mE]
      exact f'.sub fun r hr => by
        simp only [List.cons_append, List.nil_append, List.mem_cons,
          List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact ⟨_, List.mem_cons_self, Region.sub_prefix (by decide)⟩
        · exact ⟨_, List.mem_cons_self, Offset.sub_base _ (by decide)⟩
        · exact ⟨_, List.mem_cons_self, Offset.sub_base _ (by decide)⟩
        · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, below_sub (by decide) hlo⟩

end VG.Proof.Argon2.X86.HPrime
