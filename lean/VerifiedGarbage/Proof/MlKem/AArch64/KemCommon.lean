import VerifiedGarbage.Proof.MlKem.AArch64.KeyGen
import VerifiedGarbage.Impl.MlKem.AArch64.Kem

/-!
# ML-KEM-768 on AArch64: what the proofs of `encaps` and `decaps` share

Untrusted: everything here is checked by Lean. A function's buffers
(`Layout`): its `nb` pointer arguments (`kA`), the first `nrd` read and the
others written, and the four it keeps in `x25`–`x28` (`slot`, with
`scratch` in `x28`). What holds from the prologue to the epilogue (`KB`):
the pointers, our caller's registers saved in `scratch`, the other
callee-saved registers, and the buffers the function only reads. Then the
region facts the calls need, reduced to arithmetic on offsets, and the
prologue and epilogue.
-/

namespace VG.Proof.MlKem.AArch64.Kem

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt stateAt Repr)

/-- A function's buffers: `nb` pointer arguments of lengths `len`, the
first `nrd` read and the others written; argument `slot k` is kept in
`slotReg k` (`scratch` is `slot 3`). -/
structure Layout where
  nb : Nat
  nrd : Nat
  len : Nat → Nat
  slot : Nat → Nat

/-- `scratch`. -/
abbrev Layout.sc (L : Layout) : Nat := L.slot 3

/-- Argument `b`. -/
def kA (s₀ : State) (b : Nat) : Addr := s₀.gpr (argReg b)

/-- The arguments' regions `⟨A b, len b⟩` (for `b < nb`) are disjoint if one
of them is written (`nrd ≤ b`), at most 32 KiB, and apart from the 16 bytes
below `sp`. -/
structure KArgs (A : Nat → Addr) (ln : Nat → Nat) (nb nrd : Nat) (sp : Addr) : Prop where
  disj : ∀ b < nb, ∀ c < nb, b ≠ c → nrd ≤ b ∨ nrd ≤ c → Region.Disjoint ⟨A b, ln b⟩ ⟨A c, ln c⟩
  len : ∀ b < nb, ln b ≤ 32768
  stk : ∀ b < nb, Region.Disjoint ⟨sp - 16, 16⟩ ⟨A b, ln b⟩

theorem KArgs.rdisj {A : Nat → Addr} {ln : Nat → Nat} {nb nrd : Nat} {sp : Addr} (h : KArgs A ln nb nrd sp)
    {b₁ o₁ l₁ b₂ o₂ l₂ : Nat} (hb₁ : b₁ < nb) (hb₂ : b₂ < nb) (f₁ : o₁ + l₁ ≤ ln b₁)
    (f₂ : o₂ + l₂ ≤ ln b₂) (hw : b₁ = b₂ ∨ nrd ≤ b₁ ∨ nrd ≤ b₂) (hs : b₁ ≠ b₂ ∨ o₁ + l₁ ≤ o₂ ∨ o₂ + l₂ ≤ o₁) :
    (R A b₁ o₁ l₁).Disjoint (R A b₂ o₂ l₂) := by
  by_cases hb : b₁ = b₂
  · subst hb
    have hl := h.len b₁ hb₁
    have hs' : o₁ + l₁ ≤ o₂ ∨ o₂ + l₂ ≤ o₁ := hs.resolve_left (fun h => h rfl)
    intro x h₁ h₂
    simp only [Region.Contains] at h₁ h₂
    exact sep_off (A b₁) hs' (by omega) (by omega) x (Nat.lt_of_succ_le h₁) (Nat.lt_of_succ_le h₂)
  · exact ((h.disj b₁ hb₁ b₂ hb₂ hb (hw.resolve_left hb)).sub_left (R.sub f₁)).sub_right (R.sub f₂)

theorem KArgs.stkR {A : Nat → Addr} {ln : Nat → Nat} {nb nrd : Nat} {sp : Addr} (h : KArgs A ln nb nrd sp)
    {b o l : Nat} (hb : b < nb) (f : o + l ≤ ln b) : Region.Disjoint ⟨sp - 16, 16⟩ (R A b o l) :=
  (h.stk b hb).sub_right (R.sub f)

structure Pre (L : Layout) (s₀ : State) : Prop where
  rd : s₀.rd = (List.range L.nrd).map fun b => ⟨kA s₀ b, L.len b⟩
  wr : s₀.wr = (List.range' L.nrd (L.nb - L.nrd)).map fun b => ⟨kA s₀ b, L.len b⟩
  args : KArgs (kA s₀) L.len L.nb L.nrd s₀.sp
  sp16 : 16 ≤ s₀.sp.toNat
  slots : ∀ k < 4, L.slot k < L.nb
  scw : L.nrd ≤ L.sc
  scl : L.len L.sc = 32768

/-- Our caller's `x24`–`x28` and `x30`, saved in `scratch`. -/
def Saved (L : Layout) (s₀ : State) (m : Mem) : Prop :=
  ∀ k < 6, m.readW (kA s₀ L.sc + BitVec.ofNat 64 (SV + 8 * k)) 64 = s₀.gpr (kemOwn.getD k .x0)

/-- From the prologue on. -/
structure KB (L : Layout) (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  ptr : ∀ k < 4, s.gpr (slotReg k) = kA s₀ (L.slot k)
  cs : ∀ r ∈ preserved, r ∉ kemOwn → s.gpr r = s₀.gpr r
  sv : Saved L s₀ s.mem
  ro : ∀ b < L.nrd, bytesAt s.mem (kA s₀ b) (L.len b) = bytesAt s₀.mem (kA s₀ b) (L.len b)
  lens : ∀ b < L.nb, L.len b ≤ 32768
  nrd : ∀ {b}, b < L.nrd → b < L.nb

variable {L : Layout}

theorem KB.x28 {s₀ s : State} (h : KB L s₀ s) : s.gpr .x28 = kA s₀ L.sc := h.ptr 3 (by decide)
theorem KB.x25 {s₀ s : State} (h : KB L s₀ s) : s.gpr .x25 = kA s₀ (L.slot 0) := h.ptr 0 (by decide)
theorem KB.x26 {s₀ s : State} (h : KB L s₀ s) : s.gpr .x26 = kA s₀ (L.slot 1) := h.ptr 1 (by decide)
theorem KB.x27 {s₀ s : State} (h : KB L s₀ s) : s.gpr .x27 = kA s₀ (L.slot 2) := h.ptr 2 (by decide)

theorem slotReg_mem : ∀ k < 4, slotReg k ∈ [Reg.x25, .x26, .x27, .x28] := by decide

theorem slot_pres {k : Nat} (hk : k < 4) : slotReg k ∈ preserved ∧ slotReg k ≠ .x30 := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;> decide

/-- The saved registers are bytes `[SV, SV + 48)` of `scratch`. -/
abbrev svR (L : Layout) (s₀ : State) : Region := R (kA s₀) L.sc SV 48

theorem Saved.frame {s₀ : State} {m m' : Mem} (h : Saved L s₀ m) {rs : List Region} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (svR L s₀).Disjoint r) : Saved L s₀ m' := fun k hk => by
  rw [← h k hk]
  refine hf.readW (r := svR L s₀) ?_ hd (by decide)
  rw [show kA s₀ L.sc + BitVec.ofNat 64 (SV + 8 * k) = kA s₀ L.sc + BitVec.ofNat 64 SV + BitVec.ofNat 64 (8 * k)
    by rw [ptr_add]]
  exact contains_off (by omega) (by decide)

/-- A region apart from the saved registers and from the buffers the function only reads. -/
abbrev Safe (L : Layout) (s₀ : State) (r : Region) : Prop :=
  (svR L s₀).Disjoint r ∧ ∀ b < L.nrd, Region.Disjoint ⟨kA s₀ b, L.len b⟩ r

theorem pres_kept : ∀ r ∈ preserved, r ∉ kemOwn → r ∉ [Reg.x25, .x26, .x27, .x28] := by decide

/-- The callee-saved registers but `x24` and `x30`. -/
abbrev keptK : List Reg := [.x19, .x20, .x21, .x22, .x23, .x25, .x26, .x27, .x28]

theorem pres_keptK : ∀ r ∈ preserved, r ∉ kemOwn → r ∈ keptK := by decide

theorem slot_keptK : ∀ k < 4, slotReg k ∈ keptK := by decide

/-- Memory changes only in safe regions, and no register the function keeps. -/
theorem KB.frame {s₀ s s' : State} (h : KB L s₀ s) {rs : List Region} {regs : List Reg}
    (hk : Keep regs s s') (hf : Frame rs s.mem s'.mem) (hr : ∀ r ∈ keptK, r ∉ regs)
    (hd : ∀ r ∈ rs, Safe L s₀ r) : KB L s₀ s' :=
  ⟨by rw [hk.rd, h.rd], by rw [hk.wr, h.wr], by rw [hk.sp, h.sp],
    fun k hk' => by rw [hk.get _ (hr _ (slot_keptK k hk')), h.ptr k hk'],
    fun r hp ho => by rw [hk.get r (hr r (pres_keptK r hp ho)), h.cs r hp ho],
    h.sv.frame hf fun r hr => (hd r hr).1,
    fun b hb => by
      rw [bytesAt_frame hf (fun r hr => (hd r hr).2 b hb) (by have := h.lens b (h.nrd hb); omega), h.ro b hb],
    h.lens, h.nrd⟩

theorem KB.block {s₀ s s' : State} (h : KB L s₀ s) {regs : List Reg} (hk : Keep regs s s')
    (hm : s'.mem = s.mem) (hr : ∀ r ∈ keptK, r ∉ regs) : KB L s₀ s' :=
  h.frame (rs := []) hk (by rw [hm]; exact Frame.refl _ _) hr (fun _ h => by cases h)

/-- A call, which changes only memory in safe regions and registers that are
not callee-saved. -/
theorem KB.call {s₀ s s' : State} (h : KB L s₀ s) {rs : List Region} (hk : Kept rs s s')
    (hd : ∀ r ∈ rs, Safe L s₀ r) : KB L s₀ s' :=
  ⟨by rw [hk.rd, h.rd], by rw [hk.wr, h.wr], by rw [hk.sp, h.sp],
    fun k hk' => by rw [hk.cs _ (slot_pres hk').1 (slot_pres hk').2, h.ptr k hk'],
    fun r hp ho => by rw [hk.cs r hp (fun e => ho (by rw [e]; decide)), h.cs r hp ho],
    h.sv.frame hk.frame fun r hr => (hd r hr).1,
    fun b hb => by
      rw [bytesAt_frame hk.frame (fun r hr => (hd r hr).2 b hb) (by have := h.lens b (h.nrd hb); omega),
        h.ro b hb],
    h.lens, h.nrd⟩

/-! ## Regions -/

theorem Pre.lt {s₀ : State} (hp : Pre L s₀) {k : Nat} (hk : k < 4) : L.slot k < L.nb := hp.slots k hk

theorem Pre.scb {s₀ : State} (hp : Pre L s₀) : L.sc < L.nb := hp.slots 3 (by decide)

/-- A written buffer is safe, if apart from the saved registers. -/
theorem safe_R {s₀ : State} (hp : Pre L s₀) {b o l : Nat} (hb : L.nrd ≤ b ∧ b < L.nb) (f : o + l ≤ L.len b)
    (hs : b ≠ L.sc ∨ SV + 48 ≤ o ∨ o + l ≤ SV) : Safe L s₀ (R (kA s₀) b o l) :=
  ⟨hp.args.rdisj hp.scb hb.2 (by rw [hp.scl]; decide) f (.inr (.inl hp.scw)) (by
      rcases hs with hs | hs
      · exact .inl (Ne.symm hs)
      · exact .inr (by omega)),
    fun c hc => (hp.args.disj c (by omega) b hb.2 (by omega) (.inr hb.1)).sub_right (R.sub f)⟩

theorem below_R {s₀ : State} (hp : Pre L s₀) {b o l : Nat} (hb : b < L.nb) (f : o + l ≤ L.len b) :
    (R (kA s₀) b o l).Disjoint (below s₀.sp 16) := by
  rw [below16]; exact (hp.args.stkR hb f).symm

theorem safe_below {s₀ : State} (hp : Pre L s₀) : Safe L s₀ (below s₀.sp 16) :=
  ⟨below_R hp hp.scb (by rw [hp.scl]; decide), fun c hc => by
    rw [below16]; exact (hp.args.stk c (by have := hp.scw; have := hp.scb; omega)).symm⟩

/-- A buffer of `scratch` below the saved registers is safe. -/
theorem safe_scr {s₀ : State} (hp : Pre L s₀) {o l : Nat} (h : o + l ≤ SV) : Safe L s₀ (R (kA s₀) L.sc o l) :=
  safe_R hp ⟨hp.scw, hp.scb⟩ (by rw [hp.scl]; simp only [SV] at h; omega) (.inr (.inr h))

theorem stk_R {s₀ s : State} (hp : Pre L s₀) (h : KB L s₀ s) {b o l : Nat} (hb : b < L.nb)
    (f : o + l ≤ L.len b) : (stk s).Disjoint (R (kA s₀) b o l) := by
  rw [stk_sp h.sp]; exact hp.args.stkR hb f

/-- Regions a callee may write. -/
theorem cov_w {s₀ s : State} (hp : Pre L s₀) (h : KB L s₀ s) {b o l : Nat} (hb : L.nrd ≤ b ∧ b < L.nb)
    (f : o + l ≤ L.len b) : Covers [R (kA s₀) b o l] s.wr := by
  rw [h.wr, hp.wr]
  exact R.cov (List.mem_map.mpr ⟨b, List.mem_range'_1.mpr ⟨hb.1, by omega⟩, rfl⟩) f

/-- Regions a callee may read. -/
theorem cov_r {s₀ s : State} (hp : Pre L s₀) (h : KB L s₀ s) {b o l : Nat} (hb : b < L.nb)
    (f : o + l ≤ L.len b) : Covers [R (kA s₀) b o l] (s.rd ++ s.wr) := by
  rw [h.rd, h.wr, hp.rd, hp.wr]
  by_cases hr : b < L.nrd
  · exact R.cov (List.mem_append_left _ (List.mem_map.mpr ⟨b, List.mem_range.mpr hr, rfl⟩)) f
  · exact R.cov (List.mem_append_right _
      (List.mem_map.mpr ⟨b, List.mem_range'_1.mpr ⟨by omega, by omega⟩, rfl⟩)) f

/-- Scratch buffers. -/
theorem cov_s {s₀ s : State} (hp : Pre L s₀) (h : KB L s₀ s) {o l : Nat} (f : o + l ≤ 32768) :
    Covers [R (kA s₀) L.sc o l] s.wr :=
  cov_w hp h ⟨hp.scw, hp.scb⟩ (by rw [hp.scl]; exact f)

theorem cov_sr {s₀ s : State} (hp : Pre L s₀) (h : KB L s₀ s) {o l : Nat} (f : o + l ≤ 32768) :
    Covers [R (kA s₀) L.sc o l] (s.rd ++ s.wr) :=
  cov_r hp h hp.scb (by rw [hp.scl]; exact f)

/-- Two buffers of `scratch`. -/
theorem sdisj {s₀ : State} (hp : Pre L s₀) {o₁ l₁ o₂ l₂ : Nat} (f₁ : o₁ + l₁ ≤ 32768) (f₂ : o₂ + l₂ ≤ 32768)
    (h : o₁ + l₁ ≤ o₂ ∨ o₂ + l₂ ≤ o₁) : (R (kA s₀) L.sc o₁ l₁).Disjoint (R (kA s₀) L.sc o₂ l₂) :=
  hp.args.rdisj hp.scb hp.scb (by rw [hp.scl]; exact f₁) (by rw [hp.scl]; exact f₂) (.inl rfl) (.inr h)

theorem hsetup {s₀ s : State} (hp : Pre L s₀) (h : KB L s₀ s) {rate : Nat} (hr : rate ∈ Spec.Sha3.rates) :
    HSetup .x28 ST WK rate s := by
  have e : ∀ o l, (⟨s.gpr .x28 + BitVec.ofNat 64 o, l⟩ : Region) = R (kA s₀) L.sc o l := fun o l => by
    rw [h.x28]
  refine ⟨by decide, by decide, by decide, hr, ?_, by rw [h.sp]; exact hp.sp16, ?_, ?_, ?_⟩
  · rw [e, e]; exact sdisj hp (by decide) (by decide) (by decide)
  · rw [e]; exact stk_R hp h hp.scb (by rw [hp.scl]; decide)
  · rw [e]; exact stk_R hp h hp.scb (by rw [hp.scl]; decide)
  · rw [e, e]; exact covers_cons (cov_s hp h (by decide)) (cov_s hp h (by decide))

/-- A piece at bytes `[o, o + l)` of the buffer in `slotReg k`, apart from the
Keccak state and working space. -/
theorem pieceOk {s₀ s : State} (hp : Pre L s₀) (h : KB L s₀ s) {w : Bool} {k o l : Nat} (hk : k < 4)
    (f : o + l ≤ L.len (L.slot k)) (hs : L.slot k ≠ L.sc ∨ 840 ≤ o) (hl : l < 65536)
    (hw : w = true → L.nrd ≤ L.slot k) : PieceOk .x28 ST WK s w ⟨slotReg k, o, l⟩ := by
  have hb := hp.lt hk
  have eb : preg s ⟨slotReg k, o, l⟩ = R (kA s₀) (L.slot k) o l := by simp only [preg, h.ptr k hk]
  have e : ∀ o l, (⟨s.gpr .x28 + BitVec.ofNat 64 o, l⟩ : Region) = R (kA s₀) L.sc o l := fun o l => by
    rw [h.x28]
  have ho : o < 65536 := by have := hp.args.len _ hb; omega
  have fs : ∀ {o l : Nat}, o + l ≤ 840 → o + l ≤ L.len L.sc := fun h => by rw [hp.scl]; omega
  refine ⟨slot_pres hk, ho, hl, ?_, ?_, ?_, ?_⟩
  · rw [eb, VG.Proof.MlKem.AArch64.STr, e]
    exact hp.args.rdisj hb hp.scb f (fs (by decide)) (.inr (.inr hp.scw)) (by
      rcases hs with hs | hs
      · exact .inl hs
      · exact .inr (.inr (by simp only [KEM.ST]; omega)))
  · rw [eb, VG.Proof.MlKem.AArch64.WKr, e]
    exact hp.args.rdisj hb hp.scb f (fs (by decide)) (.inr (.inr hp.scw)) (by
      rcases hs with hs | hs
      · exact .inl hs
      · exact .inr (.inr (by simp only [KEM.WK]; omega)))
  · rw [eb]; exact stk_R hp h hb f
  · rw [eb]
    cases w
    · exact cov_r hp h hb f
    · exact cov_w hp h ⟨hw rfl, hb⟩ f

/-- An output of a hash: bytes `[o, o + l)` of a written buffer, apart from
the saved registers. -/
def OutOk (L : Layout) (p : Piece) : Prop :=
  ∃ k o l, p = ⟨slotReg k, o, l⟩ ∧ k < 4 ∧ L.nrd ≤ L.slot k ∧ o + l ≤ L.len (L.slot k) ∧
    (L.slot k ≠ L.sc ∨ SV + 48 ≤ o ∨ o + l ≤ SV)

/-- A hash keeps what holds throughout. -/
theorem KB.hash {s₀ s s' : State} (hp : Pre L s₀) (h : KB L s₀ s) {outs : List Piece}
    (hk : Kept (STr .x28 ST s :: WKr .x28 WK s :: below s.sp 16 :: outs.map (preg s)) s s')
    (ho : ∀ p ∈ outs, OutOk L p) : KB L s₀ s' := by
  refine h.call hk fun r hr => ?_
  have e : ∀ o l, (⟨s.gpr .x28 + BitVec.ofNat 64 o, l⟩ : Region) = R (kA s₀) L.sc o l := fun o l => by
    rw [h.x28]
  rcases List.mem_cons.mp hr with rfl | hr
  · rw [VG.Proof.MlKem.AArch64.STr, e]; exact safe_scr hp (by decide)
  rcases List.mem_cons.mp hr with rfl | hr
  · rw [VG.Proof.MlKem.AArch64.WKr, e]; exact safe_scr hp (by decide)
  rcases List.mem_cons.mp hr with rfl | hr
  · rw [h.sp]; exact safe_below hp
  obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hr
  obtain ⟨k, o, l, rfl, hk, hw, f, hs⟩ := ho p hp'
  simp only [preg, h.ptr k hk]
  exact safe_R hp ⟨hw, hp.lt hk⟩ f hs

/-! ## The prologue and the epilogue -/

theorem argReg_not (b : Nat) : argReg b ≠ .x24 ∧ argReg b ≠ .x25 ∧ argReg b ≠ .x26 ∧ argReg b ≠ .x27 ∧
    argReg b ≠ .x28 := by
  unfold argReg
  rcases b with _ | _ | _ | _ | _ | b <;> simp

theorem cov_w₀ {s₀ : State} (hp : Pre L s₀) {b o l : Nat} (hb : L.nrd ≤ b ∧ b < L.nb)
    (f : o + l ≤ L.len b) : Covers [R (kA s₀) b o l] s₀.wr := by
  rw [hp.wr]
  exact R.cov (List.mem_map.mpr ⟨b, List.mem_range'_1.mpr ⟨hb.1, by omega⟩, rfl⟩) f

/-- What the prologue leaves. -/
structure AfterPro (L : Layout) (s₀ s : State) : Prop where
  kb : KB L s₀ s
  x24 : s.gpr .x24 = 1
  keep : Keep [.x25, .x26, .x27, .x28, .x24] s₀ s
  mem : s.mem = s₀.mem ∨ Frame [svR L s₀] s₀.mem s.mem

theorem pres_pro : ∀ r ∈ preserved, r ∉ kemOwn → r ∉ [Reg.x25, .x26, .x27, .x28, .x24] := by decide

theorem prologue_ok {s₀ : State} (hp : Pre L s₀) :
    WP isa (.block (kemPrologue L.sc [L.slot 0, L.slot 1, L.slot 2, L.slot 3])) s₀ (AfterPro L s₀) := by
  rw [kemPrologue, List.append_assoc, WP.block_append_iff]
  have hin : ∀ k < kemOwn.length, InRegions s₀.wr (kA s₀ L.sc + BitVec.ofNat 64 (SV + 8 * k)) 8 :=
    fun k hk => in_R (cov_w₀ hp ⟨hp.scw, hp.scb⟩ (o := SV) (l := 48) (by rw [hp.scl]; decide)) (k := 8 * k)
      (n := 8) (by simp only [kemOwn, List.length_cons, List.length_nil] at hk; omega) (by decide)
  refine WP.mono (KeyGen.saves_ok (kA s₀ L.sc) (argReg L.sc) SV kemOwn (by decide) (by decide) 6 (by decide) rfl hin)
    fun s₁ ⟨g₁, r₁, w₁, p₁, z₁, f₁⟩ => ?_
  rw [show List.range 4 = [0, 1, 2, 3] from rfl]
  simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.getD_cons_zero,
    List.getD_cons_succ]
  refine wp_mov fun s₂ h₂ e₂ => wp_mov fun s₃ h₃ e₃ => wp_mov fun s₄ h₄ e₄ => wp_mov fun s₅ h₅ e₅ =>
    wp_movz fun s₆ h₆ e₆ => wp_nil ?_
  have o₆ : Only [.x25, .x26, .x27, .x28, .x24] s₁ s₆ := ((((h₂.trans h₃).trans h₄).trans h₅).trans h₆).mono
  have k₆ : Keep [.x25, .x26, .x27, .x28, .x24] s₀ s₆ :=
    ⟨fun r hr => by rw [o₆.get r hr, g₁], by rw [o₆.rd, r₁], by rw [o₆.wr, w₁], by rw [o₆.sp, p₁]⟩
  have a : ∀ (b : Nat) {w w' : State} {r : Reg}, Only [r] w w' → r ∈ [Reg.x24, .x25, .x26, .x27, .x28] →
      w'.gpr (argReg b) = w.gpr (argReg b) := fun b _ _ r h hr => h.get _ fun h' => by
    have e := List.mem_singleton.mp h'
    have := argReg_not b
    rcases mem5 hr with rfl | rfl | rfl | rfl | rfl
    exacts [this.1 e, this.2.1 e, this.2.2.1 e, this.2.2.2.1 e, this.2.2.2.2 e]
  have v₁ : ∀ b, s₁.gpr (argReg b) = kA s₀ b := fun b => by rw [g₁]; rfl
  refine ⟨⟨k₆.rd, k₆.wr, k₆.sp, fun k hk => ?_, fun r hr ho => k₆.get r (pres_pro r hr ho), fun k hk => ?_,
    fun b hb => ?_, hp.args.len, fun hb => by have := hp.scw; have := hp.scb; omega⟩, by rw [e₆]; rfl, k₆,
    .inr (by rw [o₆.mem]; exact f₁)⟩
  · rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
    · rw [h₆.get (slotReg 0) (by decide), h₅.get (slotReg 0) (by decide), h₄.get (slotReg 0) (by decide),
        h₃.get (slotReg 0) (by decide), e₂, v₁]
    · rw [h₆.get (slotReg 1) (by decide), h₅.get (slotReg 1) (by decide), h₄.get (slotReg 1) (by decide),
        e₃, a _ h₂ (by decide), v₁]
    · rw [h₆.get (slotReg 2) (by decide), h₅.get (slotReg 2) (by decide), e₄, a _ h₃ (by decide),
        a _ h₂ (by decide), v₁]
    · rw [h₆.get (slotReg 3) (by decide), e₅, a _ h₄ (by decide), a _ h₃ (by decide), a _ h₂ (by decide), v₁]
  · rw [o₆.mem]; exact z₁ k hk
  · rw [o₆.mem]
    exact bytesAt_frame f₁ (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact (hp.args.disj b (by have := hp.scw; have := hp.scb; omega) L.sc hp.scb
        (by have := hp.scw; omega) (.inr hp.scw)).sub_right (R.sub (by rw [hp.scl]; decide))) (by
          have := hp.args.len b (by have := hp.scw; have := hp.scb; omega); omega)

/-- Our caller's registers back, and the result. -/
theorem epilogue_ok {s₀ : State} (hp : Pre L s₀) {u : State} (hk : KB L s₀ u) :
    WP isa (.block kemEpilogue) u fun u' =>
      abiPreserved s₀ u' ∧ u'.gpr .x0 = u.gpr .x24 ∧ u'.mem = u.mem := by
  have cv := cov_sr hp hk (o := SV) (l := 48) (by decide)
  have ld : ∀ k < 6, ∀ {w : State}, w.rd = u.rd ∧ w.wr = u.wr ∧ w.mem = u.mem ∧ w.gpr .x28 = kA s₀ L.sc →
      w.gpr .x28 + BitVec.ofNat 64 (SV + 8 * k) = kA s₀ L.sc + BitVec.ofNat 64 (SV + 8 * k) ∧
      InRegions (w.rd ++ w.wr) (kA s₀ L.sc + BitVec.ofNat 64 (SV + 8 * k)) 8 ∧
      w.mem.readW (kA s₀ L.sc + BitVec.ofNat 64 (SV + 8 * k)) 64 = s₀.gpr (kemOwn.getD k .x0) :=
    fun k hk' {w} ⟨hr, hw, hm, h28⟩ =>
      ⟨by rw [h28], by rw [hr, hw]; exact in_R cv (by omega) (by decide), by rw [hm]; exact hk.sv k hk'⟩
  have st : ∀ {w w' : State} {r : Reg}, Only [r] w w' → r ≠ .x28 →
      w.rd = u.rd ∧ w.wr = u.wr ∧ w.mem = u.mem ∧ w.gpr .x28 = kA s₀ L.sc →
      w'.rd = u.rd ∧ w'.wr = u.wr ∧ w'.mem = u.mem ∧ w'.gpr .x28 = kA s₀ L.sc :=
    fun h hr ⟨a, b, c, d⟩ => ⟨by rw [h.rd, a], by rw [h.wr, b], by rw [h.mem, c],
      by rw [h.get .x28 (by simpa using Ne.symm hr), d]⟩
  rw [kemEpilogue, show List.range 6 = [0, 1, 2, 3, 4, 5] from rfl]
  simp only [List.map_cons, List.map_nil]
  refine wp_mov fun s₁ h₁ e₁ => ?_
  have g₁ := st h₁ (by decide) ⟨rfl, rfl, rfl, hk.x28⟩
  have l₁ := ld 0 (by decide) g₁
  refine wp_ldrx (a := kA s₀ L.sc + BitVec.ofNat 64 (SV + 8 * 0)) (by decide) l₁.1 l₁.2.1 fun s₂ h₂ e₂ => ?_
  have g₂ := st h₂ (by decide) g₁
  have l₂ := ld 1 (by decide) g₂
  refine wp_ldrx (a := kA s₀ L.sc + BitVec.ofNat 64 (SV + 8 * 1)) (by decide) l₂.1 l₂.2.1 fun s₃ h₃ e₃ => ?_
  have g₃ := st h₃ (by decide) g₂
  have l₃ := ld 2 (by decide) g₃
  refine wp_ldrx (a := kA s₀ L.sc + BitVec.ofNat 64 (SV + 8 * 2)) (by decide) l₃.1 l₃.2.1 fun s₄ h₄ e₄ => ?_
  have g₄ := st h₄ (by decide) g₃
  have l₄ := ld 3 (by decide) g₄
  refine wp_ldrx (a := kA s₀ L.sc + BitVec.ofNat 64 (SV + 8 * 3)) (by decide) l₄.1 l₄.2.1 fun s₅ h₅ e₅ => ?_
  have g₅ := st h₅ (by decide) g₄
  have l₅ := ld 4 (by decide) g₅
  refine wp_ldrx (a := kA s₀ L.sc + BitVec.ofNat 64 (SV + 8 * 4)) (by decide) l₅.1 l₅.2.1 fun s₆ h₆ e₆ => ?_
  have g₆ := st h₆ (by decide) g₅
  have l₆ := ld 5 (by decide) g₆
  refine wp_ldrx (a := kA s₀ L.sc + BitVec.ofNat 64 (SV + 8 * 5)) (by decide) l₆.1 l₆.2.1 fun s₇ h₇ e₇ =>
    wp_nil ?_
  have o₇ : Only [.x0, .x24, .x30, .x25, .x26, .x27, .x28] u s₇ :=
    ((((((h₁.trans h₂).trans h₃).trans h₄).trans h₅).trans h₆).trans h₇).mono
  refine ⟨⟨fun r hr => ?_, by rw [o₇.sp, hk.sp]⟩, ?_, o₇.mem⟩
  · by_cases ho : r ∈ kemOwn
    · rcases mem6 ho with rfl | rfl | rfl | rfl | rfl | rfl
      · rw [h₇.get .x24 (by decide), h₆.get .x24 (by decide), h₅.get .x24 (by decide),
          h₄.get .x24 (by decide), h₃.get .x24 (by decide)]
        exact e₂.trans l₁.2.2
      · rw [h₇.get .x30 (by decide), h₆.get .x30 (by decide), h₅.get .x30 (by decide),
          h₄.get .x30 (by decide)]
        exact e₃.trans l₂.2.2
      · rw [h₇.get .x25 (by decide), h₆.get .x25 (by decide), h₅.get .x25 (by decide)]
        exact e₄.trans l₃.2.2
      · rw [h₇.get .x26 (by decide), h₆.get .x26 (by decide)]
        exact e₅.trans l₄.2.2
      · rw [h₇.get .x27 (by decide)]
        exact e₆.trans l₅.2.2
      · exact e₇.trans l₆.2.2
    · rw [o₇.get r (by revert r; decide), hk.cs r hr ho]
  · rw [h₇.get .x0 (by decide), h₆.get .x0 (by decide), h₅.get .x0 (by decide), h₄.get .x0 (by decide),
      h₃.get .x0 (by decide), h₂.get .x0 (by decide), e₁]

end VG.Proof.MlKem.AArch64.Kem
