import VerifiedGarbage.Proof.AesGcm.X86.Common
import VerifiedGarbage.Proof.Gcm.Stream

/-!
# AES-GCM on x86: GHASH absorbing a piece (`absorb`)

Untrusted: everything here is checked by Lean. `absorb yo` absorbs the
`nO` bytes at `dO` into GHASH, with the accumulator at `St + yo` and the
`bO` buffered bytes at `St + 32` (`absorb_pc`): it fills the buffer
(`head_pc`), absorbs whole blocks (`whole_pc`) and buffers the rest
(`tail_pc`), by the steps of `Proof/Gcm/Stream.lean`. Each is a `Pc`:
correct and constant time, indexed by the memory it started from.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcm.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom)
open VG.Proof.Gcm (Absorbed)

/-- The regions `absorb` writes. -/
abbrev absFrame (St W SP : BitVec 32) (K yo : Nat) : List Region :=
  [⟨w64 St + BitVec.ofNat 64 yo, 16⟩, ⟨w64 St + BitVec.ofNat 64 32, 16⟩, wsR W, below SP K]

/-- The hash subkey in the context. -/
abbrev Hk (m : Mem) (Ctx : BitVec 32) : Block := blockAt m (w64 Ctx + BitVec.ofNat 64 240)

/-- Before `absorb yo`: the `n` bytes at `D` and `b` bytes buffered. -/
structure AbsIn (Ctx St W SP : BitVec 32) (K : Nat) (D : BitVec 32) (n b : Nat) (s : State) : Prop where
  env : Env Ctx St W SP s
  dO : slotv s.mem W dO = D
  nO : slotv s.mem W nO = BitVec.ofNat 32 n
  bO : slotv s.mem W bO = BitVec.ofNat 32 b
  b16 : b < 16
  nlt : n < 2 ^ 32
  data : DataOk St W SP K s D n

/-- Part of the way: `j` bytes absorbed, from `m₀`. -/
structure AbsMid (Ctx St W SP : BitVec 32) (K yo : Nat) (D : BitVec 32) (n b : Nat) (m₀ : Mem) (j : Nat)
    (s : State) : Prop where
  env : Env Ctx St W SP s
  le : j ≤ n
  nlt : n < 2 ^ 32
  dO : slotv s.mem W dO = D + BitVec.ofNat 32 j
  nO : slotv s.mem W nO = BitVec.ofNat 32 (n - j)
  data : DataOk St W SP K s D n
  abs : ∀ x : List Byte, x.length % 16 = b →
    Absorbed m₀ (w64 St + BitVec.ofNat 64 yo) (w64 St + BitVec.ofNat 64 32) (Hk m₀ Ctx) x →
    Absorbed s.mem (w64 St + BitVec.ofNat 64 yo) (w64 St + BitVec.ofNat 64 32) (Hk m₀ Ctx) (x ++ bytesAt m₀ (w64 D) j)
  whole : n - j = 0 ∨ (b + j) % 16 = 0
  frame : Frame (absFrame St W SP K yo) m₀ s.mem

/-- After: everything absorbed, from `m₀`. -/
structure AbsOut (Ctx St W SP : BitVec 32) (K yo : Nat) (D : BitVec 32) (n b : Nat) (m₀ : Mem) (s : State) : Prop where
  env : Env Ctx St W SP s
  abs : ∀ x : List Byte, x.length % 16 = b →
    Absorbed m₀ (w64 St + BitVec.ofNat 64 yo) (w64 St + BitVec.ofNat 64 32) (Hk m₀ Ctx) x →
    Absorbed s.mem (w64 St + BitVec.ofNat 64 yo) (w64 St + BitVec.ofNat 64 32) (Hk m₀ Ctx) (x ++ bytesAt m₀ (w64 D) n)
  frame : Frame (absFrame St W SP K yo) m₀ s.mem

section
variable {Ctx St W SP : BitVec 32} {K : Nat} (L : Lay Ctx St W SP K) {yo : Nat} (hyo : yo = 0 ∨ yo = 16)
include L hyo

omit L in
/-- The data is apart from what `absorb` writes. -/
theorem data_absFrame {s : State} {D : BitVec 32} {n : Nat} (hd : DataOk St W SP K s D n) :
    ∀ r ∈ absFrame St W SP K yo, (⟨w64 D, n⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hd.st.sub_right (Lay.stSub (by omega))
  · exact hd.st.sub_right (Lay.stSub (by decide))
  · exact hd.w.sub_right (Lay.wSub (by decide))
  · exact hd.stk.symm

/-- The context is apart from what `absorb` writes. -/
theorem ctx_absFrame : ∀ r ∈ absFrame St W SP K yo, (⟨w64 Ctx + BitVec.ofNat 64 240, 16⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact L.ctx_st (by decide) (by omega)
  · exact L.ctx_st (by decide) (by decide)
  · exact L.ctx_w (by decide) (by decide)
  · exact (L.stk_ctx (by decide)).symm

/-- The context's slot is apart from what `absorb` writes. -/
theorem slot_absFrame {o : Nat} (h₁ : 96 ≤ o) (h₂ : o + 4 ≤ 240) :
    ∀ r ∈ absFrame St W SP K yo, (⟨w64 W + BitVec.ofNat 64 o, 4⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (L.st_w (by omega) (.inr ⟨h₁, by omega⟩)).symm
  · exact (L.st_w (by decide) (.inr ⟨h₁, by omega⟩)).symm
  · exact Lay.w_w (.inl (by omega)) (by omega) (by decide)
  · exact (L.stk_w (by omega)).symm

theorem hk_frame {m m' : Mem} (h : Frame (absFrame St W SP K yo) m m') : Hk m' Ctx = Hk m Ctx :=
  blockAt_frame h (ctx_absFrame L hyo)

/-- An environment survives `absorb`'s writes, if the registers do. -/
theorem env_absFrame {s s' : State} (he : Env Ctx St W SP s) (hf : Frame (absFrame St W SP K yo) s.mem s'.mem)
    (hbp : s'.gpr .ebp = s.gpr .ebp) (hsi : s'.gpr .esi = s.gpr .esi) (hsp : s'.gpr .esp = s.gpr .esp)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Env Ctx St W SP s' :=
  he.keep hbp hsi hsp hrd hwr (slot_frame hf (slot_absFrame L hyo (by decide) (by decide)))

end

theorem pslot_absFrame {St W SP : BitVec 32} {K yo : Nat} {m m' : Mem} (h : Frame [pslotR W] m m') :
    Frame (absFrame St W SP K yo) m m' :=
  h.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, by simp, pslot_ws W⟩

theorem buf_absFrame {St W SP : BitVec 32} {K yo : Nat} {m m' : Mem} {o k : Nat}
    (h : Frame [⟨w64 St + BitVec.ofNat 64 (32 + o), k⟩] m m') (hk : o + k ≤ 16) :
    Frame (absFrame St W SP K yo) m m' :=
  h.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Offset.sub _ (by omega) (by omega)⟩

theorem gh_absFrame {St W SP : BitVec 32} {K yo : Nat} {m m' : Mem}
    (h : Frame [⟨w64 St + BitVec.ofNat 64 yo, 16⟩, ⟨w64 W + BitVec.ofNat 64 512, 256⟩, below SP K] m m') :
    Frame (absFrame St W SP K yo) m m' :=
  h.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
    · exact ⟨wsR W, by simp, Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨below SP K, by simp, fun _ h => h⟩

theorem add_ofNat_assoc (p : Addr) (a b : Nat) :
    p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem add_ofNat_assoc32 (p : BitVec 32) (a b : Nat) :
    p + BitVec.ofNat 32 a + BitVec.ofNat 32 b = p + BitVec.ofNat 32 (a + b) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem bytesAt_add (m : Mem) (p : Addr) (a b : Nat) :
    bytesAt m p (a + b) = bytesAt m p a ++ bytesAt m (p + BitVec.ofNat 64 a) b := by
  simp only [bytesAt]
  rw [List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp, BitVec.add_assoc]
  congr 1
  rw [BitVec.ofNat_add]

/-- The bytes at `p`, after writing `xs` at `p + o`: the first `o`, then `xs`. -/
theorem bytesAt_writeBytes (m : Mem) (p : Addr) (o : Nat) (xs : List Byte) (h : o + xs.length < 2 ^ 64) :
    bytesAt (writeBytes m (p + BitVec.ofNat 64 o) xs) p (o + xs.length) = bytesAt m p o ++ xs := by
  rw [bytesAt_add]
  congr 1
  · simp only [bytesAt]
    refine List.map_congr_left fun i hi => ?_
    have hi := List.mem_range.mp hi
    exact writeBytes_before m p xs hi (by omega)
  · apply List.ext_getElem (by simp [bytesAt])
    intro i h₁ h₂
    simp only [bytesAt, List.length_map, List.length_range] at h₁
    simp only [bytesAt, List.getElem_map, List.getElem_range, writeBytes, Offset.add_sub_cancel_left,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega), h₁, ite_true,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₁, Option.getD_some]

theorem bytesAt_writeBytes_self (m : Mem) (p : Addr) (xs : List Byte) (h : xs.length < 2 ^ 64) :
    bytesAt (writeBytes m p xs) p xs.length = xs := by
  have := bytesAt_writeBytes m p 0 xs (by omega)
  simp only [Nat.zero_add, BitVec.add_zero] at this
  rw [this]; rfl

/-- A write of `xs` at `q`, within `R`, keeps everything outside `R`. -/
theorem writeBytes_frame' (m : Mem) {q : Addr} {xs : List Byte} {n : Nat} (hn : xs.length = n) :
    Frame [⟨q, n⟩] m (writeBytes m q xs) :=
  writeBytes_frame m q xs (by rw [hn]; exact Region.contains_self _ _)

/-- The bytes `[j, n)` of the data, from those `[0, n)`. -/
theorem bytesAt_drop (m : Mem) (D : Addr) {j n : Nat} (h : j ≤ n) :
    (bytesAt m D n).drop j = bytesAt m (D + BitVec.ofNat 64 j) (n - j) := by
  rw [show n = j + (n - j) by omega, bytesAt_add, List.drop_left' (length_bytesAt _ _ _), Nat.add_sub_cancel_left]

theorem bytesAt_take (m : Mem) (D : Addr) {k n : Nat} (h : k ≤ n) :
    (bytesAt m D n).take k = bytesAt m D k := by
  rw [show n = k + (n - k) by omega, bytesAt_add, List.take_left' (length_bytesAt _ _ _)]

/-- The bytes `[j, j + k)` of the data in `m` are as in `m₀` if all of them are. -/
theorem bytesAt_part {m m₀ : Mem} {D : Addr} {n j k : Nat} (h : bytesAt m D n = bytesAt m₀ D n)
    (hk : j + k ≤ n) : bytesAt m (D + BitVec.ofNat 64 j) k = bytesAt m₀ (D + BitVec.ofNat 64 j) k := by
  have e := congrArg (fun l => (l.drop j).take k) h
  rwa [bytesAt_drop _ _ (by omega), bytesAt_drop _ _ (by omega), bytesAt_take _ _ (by omega),
    bytesAt_take _ _ (by omega)] at e

/-! ## Filling the buffer -/

section
variable {Ctx St W SP : BitVec 32} {K : Nat} (L : Lay Ctx St W SP K) {yo : Nat}
  {D : BitVec 32} {n b : Nat}
include L

/-- After the block that sets up the copy into the buffer. -/
structure Head2 (k : Nat) (m₀ : Mem) (s : State) : Prop where
  env : Env Ctx St W SP s
  edi : s.gpr .edi = D
  edx : s.gpr .edx = St + BitVec.ofNat 32 (32 + b)
  ecx : s.gpr .ecx = BitVec.ofNat 32 k
  dO : slotv s.mem W dO = D + BitVec.ofNat 32 k
  nO : slotv s.mem W nO = BitVec.ofNat 32 (n - k)
  bO : slotv s.mem W bO = BitVec.ofNat 32 (b + k)
  fr : Frame [pslotR W] m₀ s.mem
  data : DataOk St W SP K s D n

/-- After the copy. -/
structure Head3 (k : Nat) (m₀ : Mem) (s : State) : Prop where
  env : Env Ctx St W SP s
  dO : slotv s.mem W dO = D + BitVec.ofNat 32 k
  nO : slotv s.mem W nO = BitVec.ofNat 32 (n - k)
  bO : slotv s.mem W bO = BitVec.ofNat 32 (b + k)
  data : DataOk St W SP K s D n
  buf : bytesAt s.mem (w64 St + BitVec.ofNat 64 32) (b + k) =
    bytesAt m₀ (w64 St + BitVec.ofNat 64 32) b ++ bytesAt m₀ (w64 D) k
  fr : Frame (absFrame St W SP K yo) m₀ s.mem
  fbuf : Frame [pslotR W, ⟨w64 St + BitVec.ofNat 64 (32 + b), k⟩] m₀ s.mem

theorem head2_ok (k : Nat) (hk : k ≤ n) (m₀ : Mem) {s : State} (h : AbsIn Ctx St W SP K D n b s)
    (hm : s.mem = m₀) {s₁ : State} (hs₁ : MinOut k s s₁) :
    WP isa (.block [.mov .edi (slot dO), .mov .edx (.reg .esi), .alu .add .edx (imm 32), .alu .add .edx (slot bO),
      .mov .eax (slot nO), .alu .sub .eax (.reg .ecx), .store (at_ .ebp nO) .eax,
      .mov .eax (slot bO), .alu .add .eax (.reg .ecx), .store (at_ .ebp bO) .eax,
      .mov .eax (.reg .edi), .alu .add .eax (.reg .ecx), .store (at_ .ebp dO) .eax]) s₁
      (Head2 (Ctx := Ctx) (St := St) (W := W) (SP := SP) (K := K) (D := D) (n := n) (b := b) k m₀) := by
  have he := h.env
  have he₁ : Env Ctx St W SP s₁ := he.keep (hs₁.other _ (by decide) (by decide))
    (hs₁.other _ (by decide) (by decide)) (hs₁.other _ (by decide) (by decide)) hs₁.rd hs₁.wr (by rw [hs₁.mem])
  have hd : slotv s₁.mem W dO = D := by rw [hs₁.mem]; exact h.dO
  have hn : slotv s₁.mem W nO = BitVec.ofNat 32 n := by rw [hs₁.mem]; exact h.nO
  have hb : slotv s₁.mem W bO = BitVec.ofNat 32 b := by rw [hs₁.mem]; exact h.bO
  have hc := hs₁.ecx
  have esub : BitVec.ofNat 32 n - BitVec.ofNat 32 k = BitVec.ofNat 32 (n - k) := ofNat_sub32 hk h.nlt
  refine WP.of_runBlock ⟨_, by xrun [he₁.ebp, he₁.esi, L.aW, he₁.wIn, he₁.wIn', hd, hn, hb, hc], ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact he₁.keep (by regs []) (by regs []) (by regs []) rfl rfl (by mems [])
  · regs [hd]
  · regs [he₁.esi, add_ofNat_assoc32]
  · regs [hc]
  · mems [slotv_eq, hd, hc]
  · mems [slotv_eq, hn, hc, esub]
  · mems [slotv_eq, hb, hc, ofNat_add_ofNat32]
  · simp only [mem_setMem, gpr_setMem, mem_setReg, mem_arithFlags, ← hs₁.mem, ← hm]
    exact pslot_write (pslot_write (pslot_write (Frame.refl _ _) (by decide) (by decide) _) (by decide)
      (by decide) _) (by decide) (by decide) _
  · exact h.data.of_eq (by mems [hs₁.rd]) (by mems [hs₁.wr])


omit L in
theorem DataOk.take {St W SP : BitVec 32} {K : Nat} {s : State} {D : BitVec 32} {n k : Nat}
    (h : DataOk St W SP K s D n) (hk : k ≤ n) : DataOk St W SP K s D k where
  rd := fun a m ⟨r, hr, hc⟩ => by
    simp only [List.mem_singleton] at hr; subst hr
    exact h.rd a m ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc ⊢; omega⟩
  fit := by have := h.fit; omega
  st := h.st.sub_left (Region.sub_prefix hk)
  w := h.w.sub_left (Region.sub_prefix hk)
  stk := h.stk.sub_right (Region.sub_prefix hk)

/-- The copy into the buffer. -/
theorem head3_ok (hyo : yo = 0 ∨ yo = 16) (k : Nat) (hk : k ≤ n) (hk1 : 1 ≤ k) (hbk : b + k ≤ 16) (m₀ : Mem) {s : State}
    (h : Head2 (Ctx := Ctx) (St := St) (W := W) (SP := SP) (K := K) (D := D) (n := n) (b := b) k m₀ s) :
    WP isa copyLoop s (Head3 (Ctx := Ctx) (St := St) (W := W) (SP := SP) (K := K) (yo := yo) (D := D)
      (n := n) (b := b) k m₀) := by
  have he := h.env
  have eS := L.aS (o := 32 + b) (by omega)
  have dk := h.data.take hk
  have lp : LoopPre s D (St + BitVec.ofNat 32 (32 + b)) k := by
    refine ⟨h.edi, h.edx, h.ecx, hk1, by have := h.data.fit; have := D.isLt; omega, dk.fit, ?_, dk.rd, ?_, ?_⟩
    · rw [L.nS (by omega)]; have := L.fs; omega
    · rw [eS]; exact he.stC (by omega)
    · rw [eS]; exact dk.st.sub_right (Lay.stSub (by omega))
  refine WP.mono (copyLoop_ok s lp) fun s' c => ?_
  have cm := c.mem
  rw [eS] at cm
  have hlen := length_bytesAt s.mem (w64 D) k
  have fw : Frame [⟨w64 St + BitVec.ofNat 64 (32 + b), k⟩] s.mem s'.mem := by
    rw [cm]; exact writeBytes_frame' _ hlen
  have pw : ∀ o, 272 ≤ o → o + 4 ≤ 284 →
      ∀ r ∈ [(⟨w64 St + BitVec.ofNat 64 (32 + b), k⟩ : Region)], (⟨w64 W + BitVec.ofNat 64 o, 4⟩ : Region).Disjoint r :=
    fun o h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (L.st_w (by omega) (.inr ⟨by omega, by omega⟩)).symm
  have keepS : ∀ {o}, 272 ≤ o → o + 4 ≤ 284 → slotv s'.mem W o = slotv s.mem W o :=
    fun h₁ h₂ => slot_frame fw (pw _ h₁ h₂)
  -- The data and the buffer before the copy are as in `m₀`.
  have dpart : ∀ r ∈ [pslotR W], (⟨w64 D, k⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact dk.w.sub_right (Lay.wSub (by decide))
  have bpart : ∀ r ∈ [pslotR W], (⟨w64 St + BitVec.ofNat 64 32, b⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact L.st_w (by omega) (.inr ⟨by decide, by decide⟩)
  have eD : bytesAt s.mem (w64 D) k = bytesAt m₀ (w64 D) k := bytesAt_frame h.fr dpart (by omega)
  have eB : bytesAt s.mem (w64 St + BitVec.ofNat 64 32) b = bytesAt m₀ (w64 St + BitVec.ofNat 64 32) b :=
    bytesAt_frame h.fr bpart (by omega)
  refine ⟨env_absFrame L hyo he (buf_absFrame fw hbk) (c.other _ (by decide) (by decide) (by decide) (by decide))
    (c.other _ (by decide) (by decide) (by decide) (by decide)) (c.other _ (by decide) (by decide) (by decide)
    (by decide)) c.rd c.wr, by rw [keepS (by decide) (by decide)]; exact h.dO,
    by rw [keepS (by decide) (by decide)]; exact h.nO, by rw [keepS (by decide) (by decide)]; exact h.bO,
    h.data.of_eq c.rd c.wr, ?_, ?_, ?_⟩
  · rw [cm, show w64 St + BitVec.ofNat 64 (32 + b) = w64 St + BitVec.ofNat 64 32 + BitVec.ofNat 64 b from
      (add_ofNat_assoc _ _ _).symm]
    have := bytesAt_writeBytes s.mem (w64 St + BitVec.ofNat 64 32) b (bytesAt s.mem (w64 D) k) (by rw [hlen]; omega)
    rw [hlen] at this
    rw [this, eB, eD]
  · exact (pslot_absFrame h.fr).trans (buf_absFrame fw hbk)
  · exact (h.fr.mono (by simp)).trans (fw.mono (by simp))


omit L in
theorem Head3.keep {k : Nat} {m₀ : Mem} {s s' : State}
    (h : Head3 (Ctx := Ctx) (St := St) (W := W) (SP := SP) (K := K) (yo := yo) (D := D) (n := n) (b := b) k m₀ s)
    (hbp : s'.gpr .ebp = s.gpr .ebp) (hsi : s'.gpr .esi = s.gpr .esi) (hsp : s'.gpr .esp = s.gpr .esp)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    Head3 (Ctx := Ctx) (St := St) (W := W) (SP := SP) (K := K) (yo := yo) (D := D) (n := n) (b := b) k m₀ s' :=
  ⟨h.env.keep hbp hsi hsp hrd hwr (by rw [hm]), by rw [hm]; exact h.dO, by rw [hm]; exact h.nO,
    by rw [hm]; exact h.bO, h.data.of_eq hrd hwr, by rw [hm]; exact h.buf, by rw [hm]; exact h.fr,
    by rw [hm]; exact h.fbuf⟩

theorem head4_ok {k : Nat} (hk : b + k < 2 ^ 32) {m₀ : Mem} {s : State}
    (h : Head3 (Ctx := Ctx) (St := St) (W := W) (SP := SP) (K := K) (yo := yo) (D := D) (n := n) (b := b) k m₀ s) :
    WP isa (.block [.mov .eax (slot bO), .alu .cmp .eax (imm 16)]) s fun s' =>
      Head3 (Ctx := Ctx) (St := St) (W := W) (SP := SP) (K := K) (yo := yo) (D := D) (n := n) (b := b) k m₀ s' ∧
      s'.zf = some (decide (b + k = 16)) := by
  have he := h.env
  have hb := h.bO
  refine WP.of_runBlock ⟨_, by xrun [he.ebp, L.aW, he.wIn', hb], ?_, ?_⟩
  · exact h.keep (by regs []) (by regs []) (by regs []) (by mems []) (by mems []) (by mems [])
  · mems []
    rw [sub_beq32 hk (by decide)]

/-- The buffer at `St + 32`, as a block `ghash1` absorbs. -/
theorem buf_gh (hyo : yo = 0 ∨ yo = 16) {s : State} (he : Env Ctx St W SP s) :
    Env Ctx St W SP s ∧ s.gpr .esi + BitVec.ofNat 32 32 = St + BitVec.ofNat 32 32 ∧
      (St + BitVec.ofNat 32 32).toNat + 16 ≤ 2 ^ 32 ∧ Covers [⟨w64 (St + BitVec.ofNat 32 32), 16⟩] (s.rd ++ s.wr) ∧
      (⟨w64 St + BitVec.ofNat 64 yo, 16⟩ : Region).Disjoint ⟨w64 (St + BitVec.ofNat 32 32), 16⟩ ∧
      (⟨w64 (St + BitVec.ofNat 32 32), 16⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 512, 256⟩ ∧
      (below SP K).Disjoint ⟨w64 (St + BitVec.ofNat 32 32), 16⟩ := by
  rw [L.aS (by decide)]
  refine ⟨he, by rw [he.esi], by rw [L.nS (by decide)]; have := L.fs; omega, covers_left (he.stC (by decide)),
    Lay.st_st (.inl (by omega)) (by omega) (by decide), L.st_w (by decide) (.inr ⟨by decide, by decide⟩),
    L.stk_st (by decide)⟩

/-- The pieces' slots are apart from what `ghash1` writes. -/
theorem pslot_gh (hyo : yo = 0 ∨ yo = 16) {o : Nat} (h₁ : 96 ≤ o) (h₂ : o + 4 ≤ 512) :
    ∀ r ∈ [(⟨w64 St + BitVec.ofNat 64 yo, 16⟩ : Region), ⟨w64 W + BitVec.ofNat 64 512, 256⟩, below SP K],
      (⟨w64 W + BitVec.ofNat 64 o, 4⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (L.st_w (by omega) (.inr ⟨h₁, by omega⟩)).symm
  · exact Lay.w_w (.inl (by omega)) (by omega) (by decide)
  · exact (L.stk_w (by omega)).symm

theorem head_pc (hyo : yo = 0 ∨ yo = 16) (hn0 : n ≠ 0) (hb0 : b ≠ 0) (hb16 : b < 16) (hnlt : n < 2 ^ 32) :
    Pc (fun (m₀ : Mem) s => AbsIn Ctx St W SP K D n b s ∧ s.mem = m₀) (absorbHead yo)
      (AbsMid Ctx St W SP K yo D n b · (min (16 - b) n)) := by
  generalize hk : min (16 - b) n = k
  have hkn : k ≤ n := by omega
  have hk1 : 1 ≤ k := by omega
  have hbk : b + k ≤ 16 := by omega
  refine Pc.seq (Q := fun m₀ s₁ => ∃ s, (AbsIn Ctx St W SP K D n b s ∧ s.mem = m₀) ∧ MinOut k s s₁)
    (hk ▸ Pc.of (I := AbsIn Ctx St W SP K D n b) (R := MinOut (min (16 - b) n))
      (fun s h => minLen_ok L h.env h.nO h.bO (by omega) h.nlt)
      (minLen_ct fun s h => ⟨h.env.ebp, Ctx, St, SP, K, L, h.env, h.nO, h.bO, by omega, h.nlt⟩)
      _ fun _ _ h => h.1) ?_
  refine Pc.seq (Q := Head2 (Ctx := Ctx) (St := St) (W := W) (SP := SP) (K := K) (D := D) (n := n) (b := b) k)
    (Pc.taint [.ebp, .esi] (fun m₀ s₁ ⟨s, ⟨h, hm⟩, hs₁⟩ => head2_ok L k hkn m₀ h hm hs₁)
      (fun _ _ s₁ s₂ ⟨t₁, ⟨h₁, _⟩, g₁⟩ ⟨t₂, ⟨h₂, _⟩, g₂⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [g₁.other _ (by decide) (by decide), g₂.other _ (by decide) (by decide), h₁.env.ebp, h₂.env.ebp]
        · rw [g₁.other _ (by decide) (by decide), g₂.other _ (by decide) (by decide), h₁.env.esi, h₂.env.esi])
      (by taint_decide)) ?_
  refine Pc.seq (Q := Head3 (Ctx := Ctx) (St := St) (W := W) (SP := SP) (K := K) (yo := yo) (D := D) (n := n)
      (b := b) k)
    (Pc.taint [.edi, .edx, .ecx] (fun m₀ s h => head3_ok L hyo k hkn hk1 hbk m₀ h)
      (fun _ _ s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [h₁.edi, h₂.edi]
        · rw [h₁.edx, h₂.edx]
        · rw [h₁.ecx, h₂.ecx])
      (by taint_decide)) ?_
  refine Pc.seq (Q := fun m₀ s => Head3 (Ctx := Ctx) (St := St) (W := W) (SP := SP) (K := K) (yo := yo) (D := D)
      (n := n) (b := b) k m₀ s ∧ s.zf = some (decide (b + k = 16)))
    (Pc.taint [.ebp] (fun m₀ s h => head4_ok L (by omega) h)
      (fun _ _ s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h₁.env.ebp, h₂.env.ebp])
      (by taint_decide)) ?_
  refine Pc.ite (decide (b + k = 16)) (fun _ _ h => h.2) (fun ht => ?_) (fun hf => ?_)
  · have h16 : b + k = 16 := by simpa using ht
    refine Pc.mono (Pc.of (I := Env Ctx St W SP) (fun s he => ghash1_ok L hyo he .esi 32 (.inl rfl)
        (buf_gh L hyo he).2.1 (buf_gh L hyo he).2.2.1 (buf_gh L hyo he).2.2.2.1 (buf_gh L hyo he).2.2.2.2.1
        (buf_gh L hyo he).2.2.2.2.2.1 (buf_gh L hyo he).2.2.2.2.2.2)
      (ghash1_ct L hyo .esi 32 (.inl ⟨rfl, rfl⟩) fun s he => buf_gh L hyo he) _ fun _ _ h => h.1.env)
      (fun _ _ h => h) fun m₀ s₅ ⟨s₄, ⟨h, _⟩, g⟩ => ?_
    have eB := L.aS (o := 32) (by decide)
    have go := g.out
    have gf := g.frame
    rw [eB] at go
    have hY : blockAt s₄.mem (w64 St + BitVec.ofNat 64 yo) = blockAt m₀ (w64 St + BitVec.ofNat 64 yo) :=
      blockAt_frame h.fbuf fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact L.st_w (by omega) (.inr ⟨by decide, by decide⟩)
        · exact Lay.st_st (.inl (by omega)) (by omega) (by omega)
    have hH : Hk s₄.mem Ctx = Hk m₀ Ctx := hk_frame L hyo h.fr
    refine ⟨g.env, hkn, hnlt, ?_, ?_, h.data.of_eq g.rd g.wr, ?_, .inr (by omega), h.fr.trans (gh_absFrame gf)⟩
    · rw [slotv_eq, slot_frame gf (pslot_gh L hyo (by decide) (by decide))]; exact h.dO
    · rw [slotv_eq, slot_frame gf (pslot_gh L hyo (by decide) (by decide))]; exact h.nO
    · intro x hx ha
      refine Proof.Gcm.absorb_complete ha (by rw [length_bytesAt]; omega)
        (B := bytesAt s₄.mem (w64 St + BitVec.ofNat 64 32) 16) ?_ ?_
      · rw [← h16, h.buf, ← hx, ha.2]
      · rw [go, hY, show blockAt s₄.mem (w64 Ctx + BitVec.ofNat 64 240) = Hk m₀ Ctx from hH]; rfl
  · have h16 : ¬ b + k = 16 := by simpa using hf
    have hkn' : k = n := by omega
    subst hkn'
    refine Pc.mono Pc.nil (fun _ _ h => h) fun m₀ s ⟨h, _⟩ => ?_
    refine ⟨h.env, Nat.le_refl _, hnlt, h.dO, h.nO, h.data, fun x hx ha => ?_, .inl (by omega), h.fr⟩
    refine Proof.Gcm.absorb_fill ha (by rw [length_bytesAt]; omega) ?_ (by rw [length_bytesAt, hx]; exact h.buf)
    exact blockAt_frame h.fbuf fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact L.st_w (by omega) (.inr ⟨by decide, by decide⟩)
      · exact Lay.st_st (.inl (by omega)) (by omega) (by omega)

/-! ## Whole blocks -/

/-- After `splitWhole`, `nb` whole blocks from byte `j`. -/
structure Whole1 (j nb : Nat) (m₀ : Mem) (s : State) : Prop where
  env : Env Ctx St W SP s
  ebx : s.gpr .ebx = D + BitVec.ofNat 32 j
  edi : s.gpr .edi = BitVec.ofNat 32 nb
  zf : s.zf = some (decide (nb = 0))
  dO : slotv s.mem W dO = D + BitVec.ofNat 32 (j + 16 * nb)
  nO : slotv s.mem W nO = BitVec.ofNat 32 ((n - j) % 16)
  data : DataOk St W SP K s D n
  abs : ∀ x : List Byte, x.length % 16 = b →
    Absorbed m₀ (w64 St + BitVec.ofNat 64 yo) (w64 St + BitVec.ofNat 64 32) (Hk m₀ Ctx) x →
    Absorbed s.mem (w64 St + BitVec.ofNat 64 yo) (w64 St + BitVec.ofNat 64 32) (Hk m₀ Ctx) (x ++ bytesAt m₀ (w64 D) j)
  whole : n - j = 0 ∨ (b + j) % 16 = 0
  frame : Frame (absFrame St W SP K yo) m₀ s.mem

omit L in
/-- `Absorbed` outside a frame of the slots. -/
theorem absorbed_pslot {m m' : Mem} {H : Block} {x : List Byte} (hf : Frame [pslotR W] m m')
    (h : Absorbed m (w64 St + BitVec.ofNat 64 yo) (w64 St + BitVec.ofNat 64 32) H x) (L : Lay Ctx St W SP K)
    (hyo : yo = 0 ∨ yo = 16) :
    Absorbed m' (w64 St + BitVec.ofNat 64 yo) (w64 St + BitVec.ofNat 64 32) H x := by
  refine h.congr (blockAt_frame hf fun r hr => ?_) (bytesAt_frame hf (fun r hr => ?_) (by omega))
  · simp only [List.mem_singleton] at hr; subst hr
    exact (L.st_w (by omega) (.inr ⟨by decide, by decide⟩))
  · simp only [List.mem_singleton] at hr; subst hr
    exact (L.st_w (by have := Nat.mod_lt x.length (show 16 > 0 by decide); omega)
      (.inr ⟨by decide, by decide⟩))

theorem whole1_ok (hyo : yo = 0 ∨ yo = 16) {j : Nat} {m₀ : Mem} {s : State}
    (h : AbsMid Ctx St W SP K yo D n b m₀ j s) :
    WP isa (.block splitWhole) s (Whole1 (Ctx := Ctx) (St := St) (W := W) (SP := SP) (K := K) (yo := yo) (D := D)
      (n := n) (b := b) j ((n - j) / 16) m₀) := by
  have he := h.env
  obtain ⟨s₁, run, bx, di, zf, g, m, rd, wr⟩ := splitWhole_ok L he h.dO h.nO (r := n - j) (by have := h.nlt; omega)
  refine WP.of_runBlock ⟨s₁, run, ?_⟩
  have fr : Frame [pslotR W] s.mem s₁.mem := by
    rw [m]; exact pslot_write (pslot_write (Frame.refl _ _) (by decide) (by decide) _) (by decide) (by decide) _
  refine ⟨env_absFrame L hyo he (pslot_absFrame fr) (g _ (by decide) (by decide) (by decide) (by decide))
      (g _ (by decide) (by decide) (by decide) (by decide)) (g _ (by decide) (by decide) (by decide) (by decide)) rd wr,
    bx, di, zf, ?_, ?_, h.data.of_eq rd wr, fun x hx ha => absorbed_pslot fr (h.abs x hx ha) L hyo, h.whole,
    h.frame.trans (pslot_absFrame fr)⟩
  · rw [slotv_eq, m]; mems [add_ofNat_assoc32]
  · rw [slotv_eq, m]; mems []

theorem ghArgs_ok' (hyo : yo = 0 ∨ yo = 16) {j nb : Nat} (hnb : nb ≠ 0) (hj : j + 16 * nb ≤ n) {m₀ : Mem} {s : State}
    (h : Whole1 (Ctx := Ctx) (St := St) (W := W) (SP := SP) (K := K) (yo := yo) (D := D) (n := n) (b := b) j nb m₀ s) :
    WP isa (.block (ghArgs yo)) s fun s' => GhReady Ctx St W SP K yo (D + BitVec.ofNat 32 j) nb s' ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have he := h.env
  obtain ⟨s', run, ax, dx, bp, g, m, rd, wr⟩ := ghArgs_ok L (yo := yo) he
  refine WP.of_runBlock ⟨s', run, ?_, m, rd, wr⟩
  have hjn : j < n := by omega
  have eP := h.data.ptr hjn
  obtain ⟨dr, dst, dw, dk⟩ := h.data.part (j := j) (k := 16 * nb) hj
  refine ⟨ax, dx, by rw [g _ (by decide) (by decide) (by decide), h.ebx], by rw [g _ (by decide) (by decide) (by decide),
    h.edi], bp, by rw [g _ (by decide) (by decide) (by decide), he.esi], by rw [g _ (by decide) (by decide) (by decide),
    he.esp], by rw [rd, wr]; exact he.ctxR, by rw [wr]; exact he.stW, by rw [wr]; exact he.wW, by rw [m]; exact he.ctx,
    by rw [h.data.ptrN hjn]; have := h.data.fit; omega, by rw [rd, wr, eP]; exact dr,
    by rw [eP]; exact (dst.sub_right (Lay.stSub (by omega))).symm, by rw [eP]; exact dw.sub_right (Lay.wSub (by decide)),
    by rw [eP]; exact dk⟩

theorem ghArgs_pc (hyo : yo = 0 ∨ yo = 16) {j nb : Nat} (hnb : nb ≠ 0) (hj : j + 16 * nb ≤ n) :
    Pc (Whole1 (Ctx := Ctx) (St := St) (W := W) (SP := SP) (K := K) (yo := yo) (D := D) (n := n) (b := b) j nb)
      (.block (ghArgs yo)) (fun m₀ s => ∃ s₁, Whole1 (Ctx := Ctx) (St := St) (W := W) (SP := SP) (K := K) (yo := yo)
        (D := D) (n := n) (b := b) j nb m₀ s₁ ∧ GhReady Ctx St W SP K yo (D + BitVec.ofNat 32 j) nb s ∧
        s.mem = s₁.mem ∧ s.rd = s₁.rd ∧ s.wr = s₁.wr) := by
  have hw : ∀ (m₀ : Mem) s, Whole1 (Ctx := Ctx) (St := St) (W := W) (SP := SP) (K := K) (yo := yo) (D := D) (n := n)
      (b := b) j nb m₀ s → WP isa (.block (ghArgs yo)) s (fun s' => ∃ s₁, Whole1 (Ctx := Ctx) (St := St) (W := W)
        (SP := SP) (K := K) (yo := yo) (D := D) (n := n) (b := b) j nb m₀ s₁ ∧
        GhReady Ctx St W SP K yo (D + BitVec.ofNat 32 j) nb s' ∧ s'.mem = s₁.mem ∧ s'.rd = s₁.rd ∧ s'.wr = s₁.wr) :=
    fun m₀ s h => WP.mono (ghArgs_ok' L hyo hnb hj h) fun s' ⟨g, m, rd, wr⟩ => ⟨s, h, g, m, rd, wr⟩
  have hr : ∀ (a b' : Mem) s₁ s₂, Whole1 (Ctx := Ctx) (St := St) (W := W) (SP := SP) (K := K) (yo := yo) (D := D)
      (n := n) (b := b) j nb a s₁ → Whole1 (Ctx := Ctx) (St := St) (W := W) (SP := SP) (K := K) (yo := yo) (D := D)
      (n := n) (b := b) j nb b' s₂ → ∀ r ∈ [Reg.ebp, .esi], s₁.gpr r = s₂.gpr r := fun _ _ s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.env.ebp, h₂.env.ebp]
    · rw [h₁.env.esi, h₂.env.esi]
  rcases hyo with rfl | rfl
  · exact Pc.taint [.ebp, .esi] hw hr (by taint_decide)
  · exact Pc.taint [.ebp, .esi] hw hr (by taint_decide)

theorem whole_pc (hyo : yo = 0 ∨ yo = 16) {j : Nat} (hj : j ≤ n) (hnlt : n < 2 ^ 32) :
    Pc (AbsMid Ctx St W SP K yo D n b · j) (absorbWhole yo)
      (AbsMid Ctx St W SP K yo D n b · (j + 16 * ((n - j) / 16))) := by
  generalize hnb : (n - j) / 16 = nb
  have h16 : 16 * nb ≤ n - j := by omega
  refine Pc.seq (Q := Whole1 (Ctx := Ctx) (St := St) (W := W) (SP := SP) (K := K) (yo := yo) (D := D) (n := n)
      (b := b) j nb)
    (hnb ▸ Pc.taint [.ebp] (fun m₀ s h => whole1_ok L hyo h)
      (fun _ _ s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h₁.env.ebp, h₂.env.ebp]) (by taint_decide)) ?_
  refine Pc.ite (decide (nb = 0)) (fun _ _ h => h.zf) (fun ht => ?_) (fun hf => ?_)
  · have h0 : nb = 0 := by simpa using ht
    subst h0
    refine Pc.mono Pc.nil (fun _ _ h => h) fun m₀ s h => ?_
    refine ⟨h.env, by omega, hnlt, by rw [h.dO], by rw [h.nO]; congr 1; omega, h.data, h.abs, h.whole,
      h.frame⟩
  · have h0 : nb ≠ 0 := by simpa using hf
    have hjn : j + 16 * nb ≤ n := by omega
    refine Pc.seq (ghArgs_pc L hyo h0 hjn) ?_
    refine Pc.mono (Pc.of (I := GhReady Ctx St W SP K yo (D + BitVec.ofNat 32 j) nb) (fun _ h => ghW_ok L hyo h) (ghW_ct L hyo) _
      fun _ _ ⟨_, _, g, _⟩ => g) (fun _ _ h => h) fun m₀ s₃ ⟨s₂, ⟨s₁, h₁, g₂, m₂, rd₂, wr₂⟩, g₃⟩ => ?_
    have eP := h₁.data.ptr (j := j) (by omega)
    have go := g₃.out
    have gf := g₃.frame
    rw [eP, m₂] at go
    rw [m₂] at gf
    have hH : blockAt s₁.mem (w64 Ctx + BitVec.ofNat 64 240) = Hk m₀ Ctx := hk_frame L hyo h₁.frame
    have hD : bytesAt s₁.mem (w64 D + BitVec.ofNat 64 j) (16 * nb) = bytesAt m₀ (w64 D + BitVec.ofNat 64 j) (16 * nb) :=
      bytesAt_part (bytesAt_frame h₁.frame (data_absFrame hyo h₁.data) (by have := h₁.data.fit; omega)) hjn
    refine ⟨g₃.env, hjn, hnlt, ?_, ?_, h₁.data.of_eq (g₃.rd.trans rd₂) (g₃.wr.trans wr₂), fun x hx ha => ?_,
      .inr ?_, h₁.frame.trans (gh_absFrame gf)⟩
    · rw [slotv_eq, slot_frame g₃.frame (pslot_gh L hyo (by decide) (by decide)), m₂]; exact h₁.dO
    · rw [slotv_eq, slot_frame g₃.frame (pslot_gh L hyo (by decide) (by decide)), m₂]
      have := h₁.nO; rw [slotv_eq] at this; rw [this]; congr 1; omega
    · have hw : (b + j) % 16 = 0 := h₁.whole.resolve_left (by omega)
      have ex : x ++ bytesAt m₀ (w64 D) (j + 16 * nb) =
          (x ++ bytesAt m₀ (w64 D) j) ++ bytesAt m₀ (w64 D + BitVec.ofNat 64 j) (16 * nb) := by
        rw [bytesAt_add, List.append_assoc]
      rw [ex]
      refine Proof.Gcm.absorb_whole (h₁.abs x hx ha) (by rw [List.length_append, length_bytesAt]; omega)
        (by rw [length_bytesAt]; omega) ?_
      rw [go, hH, Proof.Gcm.blocksAt_eq, hD]
    · have hw : (b + j) % 16 = 0 := h₁.whole.resolve_left (by omega)
      omega


/-! ## The tail, and the whole of `absorb` -/

omit L in
theorem AbsMid.keep {j : Nat} {m₀ : Mem} {s s' : State} (h : AbsMid Ctx St W SP K yo D n b m₀ j s)
    (hbp : s'.gpr .ebp = s.gpr .ebp) (hsi : s'.gpr .esi = s.gpr .esi) (hsp : s'.gpr .esp = s.gpr .esp)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : AbsMid Ctx St W SP K yo D n b m₀ j s' :=
  ⟨h.env.keep hbp hsi hsp hrd hwr (by rw [hm]), h.le, h.nlt, by rw [hm]; exact h.dO, by rw [hm]; exact h.nO,
    h.data.of_eq hrd hwr, by rw [hm]; exact h.abs, h.whole, by rw [hm]; exact h.frame⟩

theorem tail_pc (hyo : yo = 0 ∨ yo = 16) {j : Nat} (hj : j ≤ n) (hr : n - j < 16) :
    Pc (AbsMid Ctx St W SP K yo D n b · j) absorbTail (AbsOut Ctx St W SP K yo D n b ·) := by
  refine Pc.seq (Q := fun m₀ s => AbsMid Ctx St W SP K yo D n b m₀ j s ∧ s.zf = some (decide (n - j = 0)) ∧
      s.gpr .ecx = BitVec.ofNat 32 (n - j))
    (Pc.taint [.ebp] (fun m₀ s h => WP.mono (test_ok L h.env .ecx nO (by decide) h.nO (by have := h.nlt; omega))
        fun s' ⟨zf, cx, g, m, rd, wr⟩ => ⟨h.keep (g _ (by decide)) (g _ (by decide)) (g _ (by decide)) m rd wr, zf, cx⟩)
      (fun _ _ s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h₁.env.ebp, h₂.env.ebp]) (by taint_decide)) ?_
  refine Pc.ite (decide (n - j = 0)) (fun _ _ h => h.2.1) (fun ht => ?_) (fun hf => ?_)
  · have h0 : j = n := by simp at ht; omega
    subst h0
    exact Pc.mono Pc.nil (fun _ _ h => h) fun _ _ h => ⟨h.1.env, h.1.abs, h.1.frame⟩
  · have h0 : n - j ≠ 0 := by simpa using hf
    refine Pc.seq (Q := fun m₀ s => AbsMid Ctx St W SP K yo D n b m₀ j s ∧ s.gpr .edi = D + BitVec.ofNat 32 j ∧
        s.gpr .edx = St + BitVec.ofNat 32 32 ∧ s.gpr .ecx = BitVec.ofNat 32 (n - j))
      (Pc.taint [.ebp, .esi] (fun m₀ s ⟨h, _, cx⟩ => ?_)
        (fun _ _ s₁ s₂ h₁ h₂ r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · rw [h₁.1.env.ebp, h₂.1.env.ebp]
          · rw [h₁.1.env.esi, h₂.1.env.esi]) (by taint_decide)) ?_
    · have he := h.env
      have hd := h.dO
      refine WP.of_runBlock ⟨_, by xrun [he.ebp, he.esi, L.aW, he.wIn', hd], ?_, ?_, ?_, ?_⟩
      · exact h.keep (by regs []) (by regs []) (by regs []) (by mems []) (by mems []) (by mems [])
      · regs []
      · regs [he.esi]
      · regs [cx]
    refine Pc.taint [.edi, .edx, .ecx] (fun m₀ s ⟨h, di, dx, cx⟩ => ?_)
      (fun _ _ s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [h₁.2.1, h₂.2.1]
        · rw [h₁.2.2.1, h₂.2.2.1]
        · rw [h₁.2.2.2, h₂.2.2.2]) (by taint_decide)
    have he := h.env
    have hjn : j < n := by omega
    have eP := h.data.ptr hjn
    have eB := L.aS (o := 32) (by decide)
    obtain ⟨dr, dst, dw, dk⟩ := h.data.part (j := j) (k := n - j) (by omega)
    have lp : LoopPre s (D + BitVec.ofNat 32 j) (St + BitVec.ofNat 32 32) (n - j) := by
      refine ⟨di, dx, cx, by omega, by have := h.nlt; omega, by rw [h.data.ptrN hjn]; have := h.data.fit; omega,
        by rw [L.nS (by decide)]; have := L.fs; omega, by rw [eP]; exact dr, by rw [eB]; exact he.stC (by omega),
        by rw [eP, eB]; exact dst.sub_right (Lay.stSub (by omega))⟩
    refine WP.mono (copyLoop_ok s lp) fun s' c => ?_
    have cm := c.mem
    rw [eP, eB] at cm
    have hlen := length_bytesAt s.mem (w64 D + BitVec.ofNat 64 j) (n - j)
    have fw : Frame [⟨w64 St + BitVec.ofNat 64 32, n - j⟩] s.mem s'.mem := by
      rw [cm]; exact writeBytes_frame' _ hlen
    have fw' : Frame (absFrame St W SP K yo) s.mem s'.mem := buf_absFrame (o := 0) (by simpa using fw) (by omega)
    refine ⟨env_absFrame L hyo he fw' (c.other _ (by decide) (by decide) (by decide) (by decide))
      (c.other _ (by decide) (by decide) (by decide) (by decide)) (c.other _ (by decide) (by decide) (by decide)
      (by decide)) c.rd c.wr, fun x hx ha => ?_, h.frame.trans fw'⟩
    have ex : x ++ bytesAt m₀ (w64 D) n = (x ++ bytesAt m₀ (w64 D) j) ++ bytesAt m₀ (w64 D + BitVec.ofNat 64 j) (n - j) := by
      rw [List.append_assoc, ← bytesAt_add, Nat.add_sub_cancel' hj]
    have ed : bytesAt s.mem (w64 D + BitVec.ofNat 64 j) (n - j) = bytesAt m₀ (w64 D + BitVec.ofNat 64 j) (n - j) :=
      bytesAt_part (bytesAt_frame h.frame (data_absFrame hyo h.data) (by have := h.data.fit; omega)) (by omega)
    rw [ex, ← ed]
    have hw : (b + j) % 16 = 0 := h.whole.resolve_left h0
    refine Proof.Gcm.absorb_tail (h.abs x hx ha) (by rw [List.length_append, length_bytesAt]; omega)
      (by rw [hlen]; omega) ?_ ?_
    · exact blockAt_frame fw fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Lay.st_st (.inl (by omega)) (by omega) (by omega)
    · have := bytesAt_writeBytes_self s.mem (w64 St + BitVec.ofNat 64 32)
        (bytesAt s.mem (w64 D + BitVec.ofNat 64 j) (n - j)) (by rw [hlen]; omega)
      rw [hlen] at this
      rw [cm, hlen]; exact this

theorem absorb_pc (hyo : yo = 0 ∨ yo = 16) (hb16 : b < 16) (hnlt : n < 2 ^ 32) :
    Pc (fun (m₀ : Mem) s => AbsIn Ctx St W SP K D n b s ∧ s.mem = m₀) (absorb yo)
      (AbsOut Ctx St W SP K yo D n b ·) := by
  refine Pc.seq (Q := fun m₀ s => (AbsIn Ctx St W SP K D n b s ∧ s.mem = m₀) ∧ s.zf = some (decide (n = 0)))
    (Pc.taint [.ebp] (fun m₀ s ⟨h, hm⟩ => WP.mono (test_ok L h.env .eax nO (by decide) h.nO hnlt)
        fun s' ⟨zf, _, g, m, rd, wr⟩ => ⟨⟨⟨h.env.keep (g _ (by decide)) (g _ (by decide)) (g _ (by decide)) rd wr
          (by rw [m]), by rw [m]; exact h.dO, by rw [m]; exact h.nO, by rw [m]; exact h.bO, h.b16, h.nlt,
          h.data.of_eq rd wr⟩, by rw [m, hm]⟩, zf⟩)
      (fun _ _ s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.env.ebp, h₂.1.env.ebp]) (by taint_decide)) ?_
  refine Pc.ite (decide (n = 0)) (fun _ _ h => h.2) (fun ht => ?_) (fun hf => ?_)
  · have h0 : n = 0 := by simpa using ht
    subst h0
    refine Pc.mono Pc.nil (fun _ _ h => h) fun m₀ s ⟨⟨h, hm⟩, _⟩ => ⟨h.env, fun x _ ha => ?_, by rw [hm]; exact Frame.refl _ _⟩
    rw [hm]; simpa [bytesAt] using ha
  have hn0 : n ≠ 0 := by simpa using hf
  refine Pc.seq (Q := fun m₀ s => (AbsIn Ctx St W SP K D n b s ∧ s.mem = m₀) ∧ s.zf = some (decide (b = 0)))
    (Pc.taint [.ebp] (fun m₀ s ⟨⟨h, hm⟩, _⟩ => WP.mono (test_ok L h.env .eax bO (by decide) h.bO (by omega))
        fun s' ⟨zf, _, g, m, rd, wr⟩ => ⟨⟨⟨h.env.keep (g _ (by decide)) (g _ (by decide)) (g _ (by decide)) rd wr
          (by rw [m]), by rw [m]; exact h.dO, by rw [m]; exact h.nO, by rw [m]; exact h.bO, h.b16, h.nlt,
          h.data.of_eq rd wr⟩, by rw [m, hm]⟩, zf⟩)
      (fun _ _ s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.1.env.ebp, h₂.1.1.env.ebp]) (by taint_decide)) ?_
  generalize hj₀ : (if b = 0 then 0 else min (16 - b) n) = j₀
  have hj₀n : j₀ ≤ n := by rw [← hj₀]; split <;> omega
  refine Pc.seq (Q := (AbsMid Ctx St W SP K yo D n b · j₀)) ?_
    (Pc.seq (whole_pc L (D := D) (b := b) hyo hj₀n hnlt) (tail_pc L (D := D) (b := b) hyo (by omega) (by omega)))
  refine Pc.ite (decide (b = 0)) (fun _ _ h => h.2) (fun ht => ?_) (fun hf => ?_)
  · have h0 : b = 0 := by simpa using ht
    simp only [h0, ↓reduceIte] at hj₀
    subst hj₀
    refine Pc.mono Pc.nil (fun _ _ h => h) fun m₀ s ⟨⟨h, hm⟩, _⟩ => ⟨h.env, Nat.zero_le _, hnlt, by rw [h.dO]; exact (BitVec.add_zero D).symm,
      by rw [h.nO, Nat.sub_zero], h.data, fun x _ ha => ?_, .inr (by omega), by rw [hm]; exact Frame.refl _ _⟩
    rw [hm]; simpa [bytesAt] using ha
  · have h0 : b ≠ 0 := by simpa using hf
    simp only [h0, ↓reduceIte] at hj₀
    subst hj₀
    exact Pc.mono (head_pc L hyo hn0 h0 hb16 hnlt) (fun _ _ h => h.1) fun _ _ h => h

end

end VG.Proof.AesGcm.X86
