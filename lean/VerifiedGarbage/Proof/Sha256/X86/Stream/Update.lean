import VerifiedGarbage.Proof.Sha256.X86.Stream.Common
import VerifiedGarbage.Proof.Sha256.X86.Contract
import Mathlib.Tactic.Tauto

/-!
# Streaming SHA-256 on x86 (32-bit): `update`

Untrusted: everything here is checked by Lean. The same structure as the
x86-64 proof (`VG.Proof.Sha256.X86_64.Stream.Update`), with `state` in `ebx`,
`data` in `ebp`, the bytes left in `esi`, the buffered bytes in `edi`, and
`state` and `scratch` also in the argument words at `[esp + 4]` and
`[esp + 16]`, which the inlined compression function reads.
-/

namespace VG.Proof.Sha256.X86.Stream.Update

open VG VG.X86 VG.Impl.Sha256.X86.Stream
open VG.Impl.Sha256.X86 (at_)
open VG.Proof.Sha256.X86 (contains_offset)
open VG.Proof.Sha256.X86.Stream
open VG.Proof.Sha256.Stream
open VG.Spec.Sha256 (HashValue stateAt blockAt compress parseBlock bytesAt)
open VG.Proof.Sha256 (countX86)

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev esp₀ : BitVec 32 := s₀.gpr .esp
abbrev st : BitVec 32 := arg s₀ 0
abbrev cnt : Nat := (countX86 s₀).toNat
abbrev dp : BitVec 32 := arg s₀ 3
abbrev len : Nat := (arg s₀ 4).toNat
abbrev scr : BitVec 32 := arg s₀ 5
abbrev stA : Addr := (st s₀).setWidth 64
abbrev dA : Addr := (dp s₀).setWidth 64
abbrev scA : Addr := (scr s₀).setWidth 64
abbrev stR : Region := ⟨stA s₀, 96⟩
abbrev dR : Region := ⟨dA s₀, len s₀⟩
abbrev scR : Region := ⟨scA s₀, 160⟩
abbrev argR : Region := ⟨addr (esp₀ s₀) 4, 24⟩
abbrev retR : Region := ⟨(esp₀ s₀).setWidth 64, 4⟩
/-- The data. -/
abbrev D : List Byte := bytesAt s₀.mem (dA s₀) (len s₀)

/-- The messages the initial state represents. -/
def R₀ (m : List Byte) : Prop :=
  Spec.Sha256.Repr s₀.mem (stA s₀) m ∧ countX86 s₀ = BitVec.ofNat 64 m.length

/-- Our caller's registers are saved in the scratch space. -/
def Saved (m : Mem) : Prop := ∀ p ∈ saved, m.readW (addr (scr s₀) p.2) 32 = s₀.gpr p.1

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [dR s₀]
  wr : s₀.wr = [stR s₀, scR s₀, argR s₀]
  st_scr : (stR s₀).Disjoint (scR s₀)
  a_st : (argR s₀).Disjoint (stR s₀)
  a_scr : (argR s₀).Disjoint (scR s₀)
  d_st : (dR s₀).Disjoint (stR s₀)
  d_scr : (dR s₀).Disjoint (scR s₀)
  d_a : (dR s₀).Disjoint (argR s₀)
  ret_st : (retR s₀).Disjoint (stR s₀)
  ret_scr : (retR s₀).Disjoint (scR s₀)
  st_fit : (st s₀).toNat + 96 ≤ 2 ^ 32
  d_fit : (dp s₀).toNat + len s₀ ≤ 2 ^ 32
  scr_fit : (scr s₀).toNat + 160 ≤ 2 ^ 32
  sp_fit : (esp₀ s₀).toNat + 28 ≤ 2 ^ 32

theorem pre_of {s₀ : State} (h : Proof.Sha256.updateX86.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩

theorem cnt_mod (s₀ : State) : cnt s₀ % 64 = (arg s₀ 1).toNat % 64 := by
  simp only [cnt, countX86]
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt (arg s₀ 1).isLt, Nat.shiftLeft_eq]
  omega

theorem R₀.length {s₀ : State} {m : List Byte} (h : R₀ s₀ m) : cnt s₀ % 64 = m.length % 64 := by
  rw [cnt, h.2, BitVec.toNat_ofNat]
  omega

theorem len_lt (s₀ : State) : len s₀ < 2 ^ 32 := (arg s₀ 4).isLt

theorem D_length (s₀ : State) : (D s₀).length = len s₀ := by simp [bytesAt]

/-- The return address is below the arguments. -/
theorem ret_a {s₀ : State} (hp : Pre s₀) : (retR s₀).Disjoint (argR s₀) := by
  have := hp.sp_fit
  intro a h₁ h₂
  simp only [Region.Contains] at h₁ h₂
  rw [addr_eq (by omega)] at h₂
  generalize (esp₀ s₀).setWidth 64 = b at *
  bv_omega

namespace Pre
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem st_addr {d : Nat} (hd : d < 96) : addr (st s₀) d = stA s₀ + BitVec.ofNat 64 d :=
  addr_eq (by have := hp.st_fit; omega)

theorem scr_in {d : Nat} (hd : d + 4 ≤ 160) : (scR s₀).Contains (addr (scr s₀) d) 4 :=
  contains_addr hd (by omega) hp.scr_fit

theorem arg_in {d : Nat} (hd₁ : 4 ≤ d) (hd : d + 4 ≤ 28) : (argR s₀).Contains (addr (esp₀ s₀) d) 4 := by
  have := hp.sp_fit
  simp only [Region.Contains]
  rw [addr_eq (by omega), addr_eq (by omega),
    show (esp₀ s₀).setWidth 64 + BitVec.ofNat 64 d - ((esp₀ s₀).setWidth 64 + BitVec.ofNat 64 4) =
      BitVec.ofNat 64 (d - 4) by
      rw [show d = (d - 4) + 4 by omega, BitVec.ofNat_add]; bv_omega,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

/-- A word of the scratch space, as a region. -/
theorem scr_sub {d : Nat} (hd : d + 4 ≤ 160) : Region.Sub ⟨addr (scr s₀) d, 4⟩ (scR s₀) := by
  rw [addr_eq (by have := hp.scr_fit; omega)]
  exact sub_offset hd (by omega)

/-- An argument word, as a region. -/
theorem arg_sub {d : Nat} (hd₁ : 4 ≤ d) (hd : d + 4 ≤ 28) : Region.Sub ⟨addr (esp₀ s₀) d, 4⟩ (argR s₀) := by
  have := hp.sp_fit
  intro a ha
  simp only [Region.Contains] at ha ⊢
  rw [addr_eq (by omega)] at ha
  rw [addr_eq (by omega)]
  generalize (esp₀ s₀).setWidth 64 = b at *
  bv_omega

end Pre

/-! ## Invariants -/

/-- What holds throughout, after consuming `c` bytes of data. -/
structure Common (s₀ : State) (c : Nat) (s : State) : Prop where
  c_le : c ≤ len s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  ebx : s.gpr .ebx = st s₀
  esp : s.gpr .esp = esp₀ s₀
  ebp : s.gpr .ebp = dp s₀ + BitVec.ofNat 32 c
  esi : s.gpr .esi = BitVec.ofNat 32 (len s₀ - c)
  a4 : s.mem.readW (addr (esp₀ s₀) 4) 32 = st s₀
  a16 : s.mem.readW (addr (esp₀ s₀) 16) 32 = scr s₀
  frame : Frame [stR s₀, scR s₀, argR s₀] s₀.mem s.mem
  saved : Saved s₀ s.mem

/-- The loop invariant: the state represents the message followed by the
first `c` bytes of data. -/
structure Inv (s₀ : State) (c : Nat) (s : State) : Prop extends Common s₀ c s where
  edi : s.gpr .edi = BitVec.ofNat 32 ((cnt s₀ + c) % 64)
  repr : ∀ m, R₀ s₀ m → Spec.Sha256.Repr s.mem (stA s₀) (m ++ (D s₀).take c)

/-- A whole block is ready at `eax`, and compressing it absorbs the first `c`
bytes of data. -/
structure Pending (s₀ : State) (c : Nat) (s : State) : Prop extends Common s₀ c s where
  edi : s.gpr .edi = 0
  ecx : s.gpr .ecx = 1
  edx : s.gpr .edx = scr s₀
  mod : (cnt s₀ + c) % 64 = 0
  src : s.gpr .eax = st s₀ + BitVec.ofNat 32 32 ∨
    ∃ c₀, s.gpr .eax = dp s₀ + BitVec.ofNat 32 c₀ ∧ c₀ + 64 ≤ len s₀
  repr : ∀ m, R₀ s₀ m → ∀ mem', stateAt mem' (stA s₀) =
      compress (stateAt s.mem (stA s₀)) (blockAt s.mem ((s.gpr .eax).setWidth 64)) →
    Spec.Sha256.Repr mem' (stA s₀) (m ++ (D s₀).take c)

/-- All the data is absorbed, and nothing is pending. -/
def Done (s₀ : State) (s : State) : Prop := Inv s₀ (len s₀) s ∧ s.gpr .ecx = 0 ∧ s.gpr .edx = scr s₀

theorem Common.of_gpr {s₀ : State} {c : Nat} {s s' : State} (h : Common s₀ c s)
    (hg : ∀ r ∈ [Reg.ebx, .esp, .ebp, .esi], s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Common s₀ c s' where
  c_le := h.c_le
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  ebx := by rw [hg _ (by simp)]; exact h.ebx
  esp := by rw [hg _ (by simp)]; exact h.esp
  ebp := by rw [hg _ (by simp)]; exact h.ebp
  esi := by rw [hg _ (by simp)]; exact h.esi
  a4 := by rw [hm]; exact h.a4
  a16 := by rw [hm]; exact h.a16
  frame := by rw [hm]; exact h.frame
  saved := by rw [hm]; exact h.saved

theorem Inv.of_gpr {s₀ : State} {c : Nat} {s s' : State} (h : Inv s₀ c s)
    (hg : ∀ r ∈ [Reg.ebx, .esp, .ebp, .esi, .edi], s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Inv s₀ c s' :=
  { h.toCommon.of_gpr (fun r hr => hg r (by simp at hr ⊢; tauto)) hm hrd hwr with
    edi := by rw [hg _ (by simp)]; exact h.edi
    repr := by rw [hm]; exact h.repr }

/-! ## Prologue and epilogue -/

/-- The memory after saving our caller's registers. -/
def saveMem (s₀ : State) : Mem :=
  (((s₀.mem.writeW (addr (scr s₀) 112) (s₀.gpr .ebx)).writeW (addr (scr s₀) 116) (s₀.gpr .esi)).writeW
    (addr (scr s₀) 120) (s₀.gpr .edi)).writeW (addr (scr s₀) 124) (s₀.gpr .ebp)

/-- And after rewriting the argument words. -/
def proMem (s₀ : State) : Mem :=
  ((saveMem s₀).writeW (addr (esp₀ s₀) 4) (st s₀)).writeW (addr (esp₀ s₀) 16) (scr s₀)

theorem saveMem_frame {s₀ : State} (hp : Pre s₀) : Frame [scR s₀] s₀.mem (saveMem s₀) := by
  have c : ∀ d, d + 4 ≤ 160 → (scR s₀).Contains (addr (scr s₀) d) (32 / 8) := fun d hd => hp.scr_in hd
  simp only [saveMem]
  exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 112 (by omega))).writeW
    (List.mem_singleton_self _) _ (c 116 (by omega))).writeW (List.mem_singleton_self _) _
    (c 120 (by omega))).writeW (List.mem_singleton_self _) _ (c 124 (by omega))

theorem proMem_frame' {s₀ : State} (hp : Pre s₀) : Frame [scR s₀, argR s₀] s₀.mem (proMem s₀) := by
  simp only [proMem]
  exact (((saveMem_frame hp).mono (by simp)).writeW (by simp) _ (hp.arg_in (d := 4) (by omega) (by omega))).writeW
    (by simp) _ (hp.arg_in (d := 16) (by omega) (by omega))

theorem proMem_frame {s₀ : State} (hp : Pre s₀) : Frame [stR s₀, scR s₀, argR s₀] s₀.mem (proMem s₀) :=
  (proMem_frame' hp).mono (by simp)

theorem saveMem_saved {s₀ : State} (hp : Pre s₀) : Saved s₀ (saveMem s₀) := by
  have hs := hp.scr_fit
  have w : ∀ (m : Mem) (v : BitVec 32) (d e : Nat), d + 4 ≤ 160 → e + 4 ≤ 160 → d + 4 ≤ e ∨ e + 4 ≤ d →
      (m.writeW (addr (scr s₀) e) v).readW (addr (scr s₀) d) 32 = m.readW (addr (scr s₀) d) 32 :=
    fun m v d e h₁ h₂ h => readW_writeW_addr m v (by omega) (by omega) h
  intro p hp'
  simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp'
  rcases hp' with rfl | rfl | rfl | rfl <;> simp only [saveMem]
  · rw [w _ _ 112 124 (by omega) (by omega) (by omega), w _ _ 112 120 (by omega) (by omega) (by omega),
      w _ _ 112 116 (by omega) (by omega) (by omega), Mem.readW_writeW_self32]
  · rw [w _ _ 116 124 (by omega) (by omega) (by omega), w _ _ 116 120 (by omega) (by omega) (by omega),
      Mem.readW_writeW_self32]
  · rw [w _ _ 120 124 (by omega) (by omega) (by omega), Mem.readW_writeW_self32]
  · rw [Mem.readW_writeW_self32]

theorem proMem_saved {s₀ : State} (hp : Pre s₀) : Saved s₀ (proMem s₀) := by
  have sep : ∀ d e, 112 ≤ d → d + 4 ≤ 128 → 4 ≤ e → e + 4 ≤ 28 →
      Mem.Sep (addr (scr s₀) d) 4 (addr (esp₀ s₀) e) 4 := by
    intro d e h₁ h₂ h₃ h₄ x hx hy
    exact hp.a_scr x (hp.arg_sub h₃ h₄ x (by simp only [Region.Contains]; omega))
      (hp.scr_sub (d := d) (by omega) x (by simp only [Region.Contains]; omega))
  intro p hp'
  have hd : 112 ≤ p.2 ∧ p.2 + 4 ≤ 128 := by
    simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl | rfl | rfl <;> simp
  simp only [proMem]
  rw [Mem.readW_writeW_sep (sep p.2 16 hd.1 hd.2 (by omega) (by omega)) (by decide),
    Mem.readW_writeW_sep (sep p.2 4 hd.1 hd.2 (by omega) (by omega)) (by decide)]
  exact saveMem_saved hp p hp'

theorem proMem_a4 {s₀ : State} (hp : Pre s₀) : (proMem s₀).readW (addr (esp₀ s₀) 4) 32 = st s₀ := by
  have := hp.sp_fit
  simp only [proMem]
  rw [readW_writeW_addr _ _ (by omega) (by omega) (by omega), Mem.readW_writeW_self32]

theorem proMem_a16 {s₀ : State} : (proMem s₀).readW (addr (esp₀ s₀) 16) 32 = scr s₀ := by
  simp only [proMem]; rw [Mem.readW_writeW_self32]

theorem prologue_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block ([.mov .eax (.mem (at_ .esp 24))] ++ save .eax ++
      [.mov .ebx (.mem (at_ .esp 4)), .mov .ebp (.mem (at_ .esp 16)), .mov .esi (.mem (at_ .esp 20)),
       .mov .edi (.mem (at_ .esp 8)), .alu .and .edi (.imm 63),
       .store (at_ .esp 4) .ebx, .store (at_ .esp 16) .eax])) s₀ (Inv s₀ 0) := by
  have hsp := hp.sp_fit
  have rin : ∀ d, 4 ≤ d → d + 4 ≤ 28 → InRegions (s₀.rd ++ s₀.wr) (addr (esp₀ s₀) d) 4 :=
    fun d h₁ h₂ => ⟨argR s₀, by simp [hp.wr], hp.arg_in h₁ h₂⟩
  have win : ∀ d, 4 ≤ d → d + 4 ≤ 28 → InRegions s₀.wr (addr (esp₀ s₀) d) 4 :=
    fun d h₁ h₂ => ⟨argR s₀, by simp [hp.wr], hp.arg_in h₁ h₂⟩
  have sin : ∀ d, d + 4 ≤ 160 → InRegions s₀.wr (addr (scr s₀) d) 4 :=
    fun d hd => ⟨scR s₀, by simp [hp.wr], hp.scr_in hd⟩
  -- The saves only touch the scratch space, so the arguments stay readable.
  have sepA : ∀ d e, 112 ≤ d → d + 4 ≤ 128 → 4 ≤ e → e + 4 ≤ 28 →
      Mem.Sep (addr (esp₀ s₀) e) 4 (addr (scr s₀) d) 4 := by
    intro d e h₁ h₂ h₃ h₄ x hx hy
    exact hp.a_scr x (hp.arg_sub h₃ h₄ x (by simp only [Region.Contains]; omega))
      (hp.scr_sub (d := d) (by omega) x (by simp only [Region.Contains]; omega))
  have argSave : ∀ e, 4 ≤ e → e + 4 ≤ 28 →
      (saveMem s₀).readW (addr (esp₀ s₀) e) 32 = s₀.mem.readW (addr (esp₀ s₀) e) 32 := by
    intro e h₁ h₂
    simp only [saveMem]
    rw [Mem.readW_writeW_sep (sepA 124 e (by omega) (by omega) h₁ h₂) (by decide),
      Mem.readW_writeW_sep (sepA 120 e (by omega) (by omega) h₁ h₂) (by decide),
      Mem.readW_writeW_sep (sepA 116 e (by omega) (by omega) h₁ h₂) (by decide),
      Mem.readW_writeW_sep (sepA 112 e (by omega) (by omega) h₁ h₂) (by decide)]
  simp only [List.cons_append, save, saved, List.map_cons, List.map_nil,
    List.nil_append]
  refine wp_movm (a := addr (esp₀ s₀) 24) (ea_at _ _ _) (rin 24 (by omega) (by omega)) fun s₁ u₁ => ?_
  have e₁ : s₁.gpr .eax = scr s₀ := u₁.gpr
  refine wp_store (a := addr (scr s₀) 112) (by rw [ea_at, e₁]) (by rw [u₁.wr]; exact sin 112 (by omega))
    fun s₂ u₂ => ?_
  refine wp_store (a := addr (scr s₀) 116) (by rw [ea_at, u₂.gpr, e₁]) (by rw [u₂.wr, u₁.wr]; exact sin 116 (by omega))
    fun s₃ u₃ => ?_
  refine wp_store (a := addr (scr s₀) 120) (by rw [ea_at, u₃.gpr, u₂.gpr, e₁])
    (by rw [u₃.wr, u₂.wr, u₁.wr]; exact sin 120 (by omega)) fun s₄ u₄ => ?_
  refine wp_store (a := addr (scr s₀) 124) (by rw [ea_at, u₄.gpr, u₃.gpr, u₂.gpr, e₁])
    (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact sin 124 (by omega)) fun s₅ u₅ => ?_
  have g₅ : s₅.gpr = s₁.gpr := by rw [u₅.gpr, u₄.gpr, u₃.gpr, u₂.gpr]
  have m₅ : s₅.mem = saveMem s₀ := by
    rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₄.gpr, u₃.gpr, u₂.gpr, u₁.mem,
      u₁.other .ebx (by decide), u₁.other .esi (by decide), u₁.other .edi (by decide), u₁.other .ebp (by decide)]
    rfl
  have rd₅ : s₅.rd = s₀.rd := by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have wr₅ : s₅.wr = s₀.wr := by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  have sp₅ : s₅.gpr .esp = esp₀ s₀ := by rw [g₅, u₁.other _ (by decide)]
  have rd' : ∀ d, 4 ≤ d → d + 4 ≤ 28 → InRegions (s₅.rd ++ s₅.wr) (addr (esp₀ s₀) d) 4 :=
    fun d h₁ h₂ => by rw [rd₅, wr₅]; exact rin d h₁ h₂
  refine wp_movm (a := addr (esp₀ s₀) 4) (by rw [ea_at, sp₅]) (rd' 4 (by omega) (by omega)) fun s₆ u₆ => ?_
  refine wp_movm (a := addr (esp₀ s₀) 16) (by rw [ea_at, u₆.other _ (by decide), sp₅])
    (by rw [u₆.rd, u₆.wr]; exact rd' 16 (by omega) (by omega)) fun s₇ u₇ => ?_
  refine wp_movm (a := addr (esp₀ s₀) 20) (by rw [ea_at, u₇.other _ (by decide), u₆.other _ (by decide), sp₅])
    (by rw [u₇.rd, u₇.wr, u₆.rd, u₆.wr]; exact rd' 20 (by omega) (by omega)) fun s₈ u₈ => ?_
  refine wp_movm (a := addr (esp₀ s₀) 8)
    (by rw [ea_at, u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), sp₅])
    (by rw [u₈.rd, u₈.wr, u₇.rd, u₇.wr, u₆.rd, u₆.wr]; exact rd' 8 (by omega) (by omega)) fun s₉ u₉ => ?_
  refine wp_andi fun s₁₀ u₁₀ => ?_
  have g : ∀ r, r ≠ .edi → r ≠ .esi → r ≠ .ebp → r ≠ .ebx → s₁₀.gpr r = s₅.gpr r := fun r h1 h2 h3 h4 => by
    rw [u₁₀.other r h1, u₉.other r h1, u₈.other r h2, u₇.other r h3, u₆.other r h4]
  have m₁₀ : s₁₀.mem = saveMem s₀ := by rw [u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, m₅]
  have sp₁₀ : s₁₀.gpr .esp = esp₀ s₀ := by rw [g _ (by decide) (by decide) (by decide) (by decide), sp₅]
  have ld : ∀ e, 4 ≤ e → e + 4 ≤ 28 → s₅.mem.readW (addr (esp₀ s₀) e) 32 = s₀.mem.readW (addr (esp₀ s₀) e) 32 :=
    fun e h₁ h₂ => by rw [m₅]; exact argSave e h₁ h₂
  have ebx₁₀ : s₁₀.gpr .ebx = st s₀ := by
    rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr,
      ld 4 (by omega) (by omega)]; rfl
  have ebp₁₀ : s₁₀.gpr .ebp = dp s₀ := by
    rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, u₆.mem,
      ld 16 (by omega) (by omega)]; rfl
  have esi₁₀ : s₁₀.gpr .esi = arg s₀ 4 := by
    rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.gpr, u₇.mem, u₆.mem, ld 20 (by omega) (by omega)]; rfl
  have edi₁₀ : s₁₀.gpr .edi = BitVec.ofNat 32 (cnt s₀ % 64) := by
    rw [u₁₀.gpr, u₉.gpr, u₈.mem, u₇.mem, u₆.mem, ld 8 (by omega) (by omega), and63, cnt_mod]; rfl
  have eax₁₀ : s₁₀.gpr .eax = scr s₀ := by
    rw [g _ (by decide) (by decide) (by decide) (by decide), g₅, e₁]
  have rd₁₀ : s₁₀.rd = s₀.rd := by rw [u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, rd₅]
  have wr₁₀ : s₁₀.wr = s₀.wr := by rw [u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, wr₅]
  refine wp_store (a := addr (esp₀ s₀) 4) (by rw [ea_at, sp₁₀]) (by rw [wr₁₀]; exact win 4 (by omega) (by omega))
    fun s₁₁ u₁₁ => ?_
  refine wp_store (a := addr (esp₀ s₀) 16) (by rw [ea_at, u₁₁.gpr, sp₁₀])
    (by rw [u₁₁.wr, wr₁₀]; exact win 16 (by omega) (by omega)) fun s₁₂ u₁₂ => WP.block_nil ?_
  have g₁₂ : s₁₂.gpr = s₁₀.gpr := by rw [u₁₂.gpr, u₁₁.gpr]
  have m₁₂ : s₁₂.mem = proMem s₀ := by
    rw [u₁₂.mem, u₁₁.gpr, u₁₁.mem, eax₁₀, ebx₁₀, m₁₀]; rfl
  refine ⟨⟨Nat.zero_le _, by rw [u₁₂.rd, u₁₁.rd, rd₁₀], by rw [u₁₂.wr, u₁₁.wr, wr₁₀],
    by rw [g₁₂, ebx₁₀], by rw [g₁₂, sp₁₀], by rw [g₁₂, ebp₁₀]; simp, ?_, by rw [m₁₂]; exact proMem_a4 hp,
    by rw [m₁₂]; exact proMem_a16, by rw [m₁₂]; exact proMem_frame hp, by rw [m₁₂]; exact proMem_saved hp⟩,
    by rw [g₁₂, edi₁₀, Nat.add_zero], fun m hm => ?_⟩
  · rw [g₁₂, esi₁₀, Nat.sub_zero, len, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [List.take_zero, List.append_nil, m₁₂]
    have hd : ∀ r ∈ [scR s₀, argR s₀], (stR s₀).Disjoint r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [hp.st_scr, hp.a_st.symm]
    exact repr_congr (fun i hi => frame_bytes (proMem_frame' hp) (R := stR s₀) hd (by simp) hi) hm.1

theorem epilogue_ok {s₀ : State} (hp : Pre s₀) {s : State} (hI : Inv s₀ (len s₀) s) :
    WP isa (.block (.mov .eax (.mem (at_ .esp 16)) :: restore .eax)) s fun s' =>
      abiPreserved s₀ s' ∧ Proof.Sha256.updateX86.post s₀ s' := by
  have rin : ∀ d, d + 4 ≤ 160 → InRegions (s.rd ++ s.wr) (addr (scr s₀) d) 4 :=
    fun d hd => ⟨scR s₀, by simp [hI.rd, hI.wr, hp.wr], hp.scr_in hd⟩
  have ain : InRegions (s.rd ++ s.wr) (addr (esp₀ s₀) 16) 4 :=
    ⟨argR s₀, by simp [hI.rd, hI.wr, hp.wr], hp.arg_in (by omega) (by omega)⟩
  simp only [restore, saved, List.map_cons, List.map_nil]
  refine wp_movm (a := addr (esp₀ s₀) 16) (by rw [ea_at, hI.esp]) ain fun s₁ u₁ => ?_
  have e₁ : s₁.gpr .eax = scr s₀ := by rw [u₁.gpr, hI.a16]
  refine wp_movm (a := addr (scr s₀) 112) (by rw [ea_at, e₁]) (by rw [u₁.rd, u₁.wr]; exact rin 112 (by omega))
    fun s₂ u₂ => ?_
  refine wp_movm (a := addr (scr s₀) 116) (by rw [ea_at, u₂.other _ (by decide), e₁])
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact rin 116 (by omega)) fun s₃ u₃ => ?_
  refine wp_movm (a := addr (scr s₀) 120) (by rw [ea_at, u₃.other _ (by decide), u₂.other _ (by decide), e₁])
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact rin 120 (by omega)) fun s₄ u₄ => ?_
  refine wp_movm (a := addr (scr s₀) 124)
    (by rw [ea_at, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), e₁])
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact rin 124 (by omega))
    fun s₅ u₅ => WP.block_nil ?_
  have hm₅ : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  refine ⟨⟨fun r hr => ?_, ?_⟩, fun m hm hc => ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.mem]
      exact hI.saved (.ebx, 112) (by simp [saved])
    · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.mem, u₁.mem]
      exact hI.saved (.esi, 116) (by simp [saved])
    · rw [u₅.other _ (by decide), u₄.gpr, u₃.mem, u₂.mem, u₁.mem]
      exact hI.saved (.edi, 120) (by simp [saved])
    · rw [u₅.gpr, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
      exact hI.saved (.ebp, 124) (by simp [saved])
    · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
        u₁.other _ (by decide), hI.esp]
  · rw [hm₅]
    refine hI.frame.readW (r := retR s₀) (Region.contains_self _ _) ?_ (by decide)
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [hp.ret_st, hp.ret_scr, ret_a hp]
  · have := hI.repr m ⟨hm, hc⟩
    rw [List.take_of_length_le (by rw [D_length])] at this
    show Spec.Sha256.Repr s₅.mem (stA s₀) (m ++ D s₀)
    rw [hm₅]; exact this

/-! ## Consuming data -/

theorem D_getD (s₀ : State) {i : Nat} (hi : i < len s₀) :
    (D s₀).getD i 0 = s₀.mem (dA s₀ + BitVec.ofNat 64 i) := by
  simp [bytesAt, List.getD_eq_getElem?_getD, hi]

/-- The data is unchanged. -/
theorem Common.data {s₀ : State} (hp : Pre s₀) {c : Nat} {s : State} (h : Common s₀ c s) {i : Nat}
    (hi : i < len s₀) : s.mem (dA s₀ + BitVec.ofNat 64 i) = (D s₀).getD i 0 := by
  rw [D_getD s₀ hi]
  refine frame_bytes h.frame (R := dR s₀) ?_ (by simp only; have := len_lt s₀; omega) hi
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  exacts [hp.d_st, hp.d_scr, hp.d_a]

theorem length_mid (s₀ : State) {m : List Byte} (hm : R₀ s₀ m) {c : Nat} (hc : c ≤ len s₀) :
    (m ++ (D s₀).take c).length % 64 = (cnt s₀ + c) % 64 := by
  have := hm.length
  simp only [List.length_append, List.length_take, D_length, Nat.min_eq_left hc]
  omega

theorem take_add_data (s₀ : State) (c t : Nat) (m : List Byte) :
    m ++ (D s₀).take c ++ ((D s₀).drop c).take t = m ++ (D s₀).take (c + t) := by
  rw [List.take_add, List.append_assoc]

theorem ofNat_add_add (x : BitVec 32) (a b : Nat) :
    x + BitVec.ofNat 32 a + BitVec.ofNat 32 b = x + BitVec.ofNat 32 (a + b) := by
  rw [BitVec.ofNat_add, BitVec.add_assoc]

theorem lit32 (n : Nat) : (OfNat.ofNat n : BitVec 32) = BitVec.ofNat 32 n := rfl

/-- A whole block straight from the data. -/
theorem direct_ok {s₀ : State} (hp : Pre s₀) {c : Nat} {s : State} (hI : Inv s₀ c s)
    (hr : (cnt s₀ + c) % 64 = 0) (hl : 64 ≤ len s₀ - c) :
    WP isa (.block direct) s (Pending s₀ (c + 64)) := by
  have hd := hp.d_fit; have hlen := len_lt s₀; have hc := hI.c_le
  unfold direct
  refine wp_movm (a := addr (esp₀ s₀) 16) (by rw [ea_at, hI.esp])
    ⟨argR s₀, by simp [hI.rd, hI.wr, hp.wr], hp.arg_in (by omega) (by omega)⟩ fun s₁ u₁ => ?_
  refine wp_mov fun s₂ u₂ => wp_addi fun s₃ u₃ => wp_subi fun s₄ u₄ _ => wp_movi fun s₅ u₅ => WP.block_nil ?_
  have g : ∀ r, r ≠ .ecx → r ≠ .esi → r ≠ .ebp → r ≠ .eax → r ≠ .edx → s₅.gpr r = s.gpr r :=
    fun r h1 h2 h3 h4 h5 => by rw [u₅.other r h1, u₄.other r h2, u₃.other r h3, u₂.other r h4, u₁.other r h5]
  have hm : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have heax : s₅.gpr .eax = dp s₀ + BitVec.ofNat 32 c := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr,
      u₁.other _ (by decide), hI.ebp]
  refine ⟨⟨by omega, by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, hI.rd], by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, hI.wr],
      by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), hI.ebx],
      by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), hI.esp], ?_, ?_,
      by rw [hm]; exact hI.a4, by rw [hm]; exact hI.a16, by rw [hm]; exact hI.frame, by rw [hm]; exact hI.saved⟩,
    by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), hI.edi, hr]; rfl,
    by rw [u₅.gpr], by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.gpr, hI.a16],
    by omega, .inr ⟨c, heax, by omega⟩, fun m hm₀ mem' hs => ?_⟩
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide),
      hI.ebp, lit32, ofNat_add_add]
  · rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide),
      hI.esi, lit32, sub_ofNat hl, Nat.sub_sub]
  · have hmod := length_mid s₀ hm₀ (c := c) (by omega)
    rw [← take_add_data]
    refine repr_append_block (hI.repr m hm₀)
      (by rw [hmod, hr, List.length_take, List.length_drop, D_length]; omega) ?_
    rw [hs, hm, heax, show (dp s₀ + BitVec.ofNat 32 c).setWidth 64 = addr (dp s₀) c from rfl,
      addr_eq (by omega)]
    refine congrArg (compress _) ?_
    rw [show (m ++ List.take c (D s₀)).drop (64 * ((m ++ List.take c (D s₀)).length / 64)) = [] by
      rw [List.drop_eq_nil_iff]; omega, List.nil_append]
    apply parseBlock_congr
    intro k hk
    rw [show dA s₀ + BitVec.ofNat 64 c + BitVec.ofNat 64 k = dA s₀ + BitVec.ofNat 64 (c + k) by
      simp only [BitVec.ofNat_add]; rw [BitVec.add_assoc], hI.data hp (by omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_drop, hk]

/-! ## Compressing -/

/-- Memory with `state` and `scratch` written back to their argument words. -/
def putArgs (s₀ : State) (m : Mem) : Mem :=
  (m.writeW (addr (esp₀ s₀) 4) (st s₀)).writeW (addr (esp₀ s₀) 16) (scr s₀)

theorem putArgs_frame {s₀ : State} (hp : Pre s₀) (m : Mem) : Frame [argR s₀] m (putArgs s₀ m) :=
  ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (hp.arg_in (d := 4) (by omega) (by omega))).writeW
    (List.mem_singleton_self _) _ (hp.arg_in (d := 16) (by omega) (by omega))

/-- Bytes of a region disjoint from the arguments are unchanged. -/
theorem putArgs_bytes {s₀ : State} (hp : Pre s₀) (m : Mem) {R : Region} (hR : R.Disjoint (argR s₀))
    (hl : R.len ≤ 2 ^ 64) {i : Nat} (hi : i < R.len) :
    putArgs s₀ m (R.base + BitVec.ofNat 64 i) = m (R.base + BitVec.ofNat 64 i) :=
  frame_bytes (putArgs_frame hp m) (by simpa using hR) hl hi

theorem Common.putArgs {s₀ : State} (hp : Pre s₀) {c : Nat} {s s' : State} (h : Common s₀ c s)
    (hg : s'.gpr = s.gpr) (hm : s'.mem = Update.putArgs s₀ s.mem) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : Common s₀ c s' where
  c_le := h.c_le
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  ebx := by rw [hg]; exact h.ebx
  esp := by rw [hg]; exact h.esp
  ebp := by rw [hg]; exact h.ebp
  esi := by rw [hg]; exact h.esi
  a4 := by
    have := hp.sp_fit
    rw [hm, Update.putArgs, readW_writeW_addr _ _ (by omega) (by omega) (by omega), Mem.readW_writeW_self32]
  a16 := by rw [hm, Update.putArgs, Mem.readW_writeW_self32]
  frame := by rw [hm]; exact h.frame.trans ((putArgs_frame hp _).mono (by simp))
  saved p hp' := by
    have hd : 112 ≤ p.2 ∧ p.2 + 4 ≤ 128 := by
      simp only [VG.Impl.Sha256.X86.Stream.saved, List.mem_cons, List.not_mem_nil, or_false] at hp'
      rcases hp' with rfl | rfl | rfl | rfl <;> simp
    rw [hm, (putArgs_frame hp _).readW (r := ⟨addr (scr s₀) p.2, 4⟩) (Region.contains_self _ _)
      (by simpa using hp.a_scr.symm.sub_left (hp.scr_sub (by omega))) (by decide)]
    exact h.saved p hp'

theorem stateAt_putArgs {s₀ : State} (hp : Pre s₀) (m : Mem) :
    stateAt (putArgs s₀ m) (stA s₀) = stateAt m (stA s₀) :=
  stateAt_congr fun i hi => putArgs_bytes hp m (R := stR s₀) hp.a_st.symm (by simp) (by simp only; omega)

theorem repr_putArgs {s₀ : State} (hp : Pre s₀) (m : Mem) {l : List Byte}
    (h : Spec.Sha256.Repr m (stA s₀) l) : Spec.Sha256.Repr (putArgs s₀ m) (stA s₀) l :=
  repr_congr (fun i hi => putArgs_bytes hp m (R := stR s₀) hp.a_st.symm (by simp) hi) h

theorem Inv.putArgs {s₀ : State} (hp : Pre s₀) {c : Nat} {s s' : State} (h : Inv s₀ c s)
    (hg : s'.gpr = s.gpr) (hm : s'.mem = Update.putArgs s₀ s.mem) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : Inv s₀ c s' :=
  { h.toCommon.putArgs hp hg hm hrd hwr with
    edi := by rw [hg]; exact h.edi
    repr := fun m hm₀ => by rw [hm]; exact repr_putArgs hp _ (h.repr m hm₀) }

/-- The block to compress. -/
theorem Pending.blk {s₀ : State} (hp : Pre s₀) {c : Nat} {s : State} (h : Pending s₀ c s) :
    (s.gpr .eax).toNat + 64 ≤ 2 ^ 32 ∧
      ((s.gpr .eax).setWidth 64 = stA s₀ + BitVec.ofNat 64 32 ∨
        ∃ c₀, (s.gpr .eax).setWidth 64 = dA s₀ + BitVec.ofNat 64 c₀ ∧ c₀ + 64 ≤ len s₀) := by
  have hst := hp.st_fit; have hd := hp.d_fit
  rcases h.src with h' | ⟨c₀, h', hc₀⟩
  · refine ⟨by rw [h', BitVec.toNat_add, toNat_ofNat_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega,
      .inl ?_⟩
    rw [h']; exact addr_eq (by omega)
  · refine ⟨by rw [h', BitVec.toNat_add, toNat_ofNat_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega,
      .inr ⟨c₀, ?_, hc₀⟩⟩
    rw [h']; exact addr_eq (by omega)

/-- The block lies in the state or in the data. -/
theorem Pending.blk_sub {s₀ : State} (hp : Pre s₀) {c : Nat} {s : State} (h : Pending s₀ c s) :
    Region.Sub ⟨(s.gpr .eax).setWidth 64, 64⟩ (stR s₀) ∨ Region.Sub ⟨(s.gpr .eax).setWidth 64, 64⟩ (dR s₀) := by
  rcases (h.blk hp).2 with he | ⟨c₀, he, hc₀⟩
  · exact .inl (by rw [he]; exact sub_offset (by omega) (by omega))
  · exact .inr (by rw [he]; exact sub_offset hc₀ (by have := len_lt s₀; omega))

theorem Pending.putArgs {s₀ : State} (hp : Pre s₀) {c : Nat} {s s' : State} (h : Pending s₀ c s)
    (hg : s'.gpr = s.gpr) (hm : s'.mem = Update.putArgs s₀ s.mem) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : Pending s₀ c s' :=
  { h.toCommon.putArgs hp hg hm hrd hwr with
    edi := by rw [hg]; exact h.edi
    ecx := by rw [hg]; exact h.ecx
    edx := by rw [hg]; exact h.edx
    mod := h.mod
    src := by rw [hg]; exact h.src
    repr := fun m hm₀ mem' hs => by
      refine h.repr m hm₀ mem' ?_
      rw [hs, hm, hg, stateAt_putArgs hp]
      refine congrArg (compress _) ?_
      simp only [blockAt]
      apply parseBlock_congr
      intro k hk
      rcases h.blk_sub hp with hsub | hsub
      · exact putArgs_bytes hp _ (R := ⟨(s.gpr .eax).setWidth 64, 64⟩) (hp.a_st.symm.sub_left hsub) (by simp) hk
      · exact putArgs_bytes hp _ (R := ⟨(s.gpr .eax).setWidth 64, 64⟩) (hp.d_a.sub_left hsub) (by simp) hk }

theorem Pending.compress_ok {s₀ : State} (hp : Pre s₀) {c : Nat} {s : State} (h : Pending s₀ c s) :
    WP isa compressAt s (Inv s₀ c) := by
  have hst := hp.st_fit; have hsc := hp.scr_fit; have hsp := hp.sp_fit
  obtain ⟨hbf, hb⟩ := h.blk hp
  have hbs := h.blk_sub hp
  have e32 : Region.Sub ⟨stA s₀, 32⟩ (stR s₀) := Region.sub_prefix (by omega)
  have e112 : Region.Sub ⟨scA s₀, 112⟩ (scR s₀) := Region.sub_prefix (by omega)
  have e16 : Region.Sub ⟨addr (esp₀ s₀) 4, 16⟩ (argR s₀) := Region.sub_prefix (by omega)
  have eret : (s.gpr .esp) = esp₀ s₀ := h.esp
  refine compressAt_ok (st := st s₀) (scr := scr s₀) (blk := s.gpr .eax) (by rw [eret]; exact h.a4)
    (by rw [eret]; exact h.a16) rfl (by rw [eret]; omega) (by omega) hbf (by omega)
    ((hp.st_scr.sub_left e32).sub_right e112) ?_ ?_ (by rw [eret]; exact (hp.a_st.sub_left e16).sub_right e32)
    (by rw [eret]; exact (hp.a_scr.sub_left e16).sub_right e112)
    (by rw [eret]; exact hp.ret_st.sub_right e32) (by rw [eret]; exact hp.ret_scr.sub_right e112) ?_ ?_ ?_ ?_
  · rcases hb with he | ⟨c₀, he, hc₀⟩
    · rw [he]; intro a h₁ h₂; simp only [Region.Contains] at h₁ h₂; bv_omega
    · exact (hp.d_st.sub_left (by rw [he]; exact sub_offset hc₀ (by have := len_lt s₀; omega))).sub_right e32
  · rcases hbs with hsub | hsub
    · exact (hp.st_scr.sub_left hsub).sub_right e112
    · exact (hp.d_scr.sub_left hsub).sub_right e112
  · rw [eret]
    rcases hbs with hsub | hsub
    · exact (hp.a_st.symm.sub_left hsub).sub_right e16
    · exact (hp.d_a.sub_left hsub).sub_right e16
  · rw [h.rd, h.wr, hp.rd, hp.wr, eret]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rcases hb with he | ⟨c₀, he, hc₀⟩
      · exact ⟨stR s₀, by simp, 32, he, by simp⟩
      · exact ⟨dR s₀, by simp, c₀, he, hc₀⟩
    · exact ⟨argR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨stR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨scR s₀, by simp, 0, by simp, by simp⟩
  · rw [h.wr, hp.wr, eret]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨stR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨scR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨argR s₀, by simp, 0, by simp, by simp⟩
  · intro s' hrd hwr hcs hf ha4 ha16 hstate
    have cs : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r := hcs
    rw [eret] at hf ha4 ha16
    refine ⟨⟨h.c_le, hrd.trans h.rd, hwr.trans h.wr, by rw [cs _ (by decide)]; exact h.ebx,
      by rw [cs _ (by decide)]; exact h.esp, by rw [cs _ (by decide)]; exact h.ebp,
      by rw [cs _ (by decide)]; exact h.esi, ha4, ha16, h.frame.trans (hf.sub ?_), fun p hp' => ?_⟩,
      by rw [cs _ (by decide), h.edi, h.mod]; rfl, fun m hm => h.repr m hm _ hstate⟩
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨stR s₀, by simp, e32⟩
      · exact ⟨scR s₀, by simp, e112⟩
      · exact ⟨argR s₀, by simp, e16⟩
    · have hd : 112 ≤ p.2 ∧ p.2 + 4 ≤ 128 := by
        simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp'
        rcases hp' with rfl | rfl | rfl | rfl <;> simp
      rw [hf.readW (r := ⟨addr (scr s₀) p.2, 4⟩) (Region.contains_self _ _) ?_ (by decide)]
      · exact h.saved p hp'
      · intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact (hp.st_scr.symm.sub_left (hp.scr_sub (by omega))).sub_right e32
        · intro a h₁ h₂
          simp only [Region.Contains] at h₁ h₂
          rw [addr_eq (by omega)] at h₁
          generalize scA s₀ = b at *
          bv_omega
        · exact (hp.a_scr.symm.sub_left (hp.scr_sub (by omega))).sub_right e16

theorem Pending.congr {s₀ : State} {c : Nat} {s s' : State} (h : Pending s₀ c s) (hg : s'.gpr = s.gpr)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Pending s₀ c s' :=
  { h.toCommon.of_gpr (fun r _ => by rw [hg]) hm hrd hwr with
    edi := by rw [hg]; exact h.edi
    ecx := by rw [hg]; exact h.ecx
    edx := by rw [hg]; exact h.edx
    mod := h.mod
    src := by rw [hg]; exact h.src
    repr := by rw [hm, hg]; exact h.repr }

/-- The loop's postcondition for one iteration from `c` bytes. -/
def Step (s₀ : State) (c : Nat) (s : State) : Prop :=
  (eval .ne s = some false ∧ Inv s₀ (len s₀) s) ∨ (eval .ne s = some true ∧ ∃ c', c < c' ∧ Inv s₀ c' s)

/-- Write `state` and `scratch` back to their argument words. -/
theorem stores_ok {s₀ : State} (hp : Pre s₀) {c : Nat} {s : State} (hC : Common s₀ c s)
    (hedx : s.gpr .edx = scr s₀) {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', s'.gpr = s.gpr → s'.mem = putArgs s₀ s.mem → s'.rd = s.rd → s'.wr = s.wr →
      WP isa (.block rest) s' Q) :
    WP isa (.block (.store (at_ .esp 4) .ebx :: .store (at_ .esp 16) .edx :: rest)) s Q := by
  have win : ∀ d, 4 ≤ d → d + 4 ≤ 28 → InRegions s.wr (addr (esp₀ s₀) d) 4 :=
    fun d h₁ h₂ => ⟨argR s₀, by simp [hC.wr, hp.wr], hp.arg_in h₁ h₂⟩
  refine wp_store (a := addr (esp₀ s₀) 4) (by rw [ea_at, hC.esp]) (win 4 (by omega) (by omega)) fun s₁ u₁ => ?_
  refine wp_store (a := addr (esp₀ s₀) 16) (by rw [ea_at, u₁.gpr, hC.esp])
    (by rw [u₁.wr]; exact win 16 (by omega) (by omega)) fun s₂ u₂ => ?_
  exact k s₂ (by rw [u₂.gpr, u₁.gpr]) (by rw [u₂.mem, u₁.gpr, u₁.mem, hC.ebx, hedx]; rfl)
    (by rw [u₂.rd, u₁.rd]) (by rw [u₂.wr, u₁.wr])

/-- The second half of the loop body: write the arguments back, compress if a
block is ready, and loop back if so. -/
theorem tail_ok {s₀ : State} (hp : Pre s₀) {c : Nat} {s : State}
    (h : (∃ c', c < c' ∧ Pending s₀ c' s) ∨ Done s₀ s) :
    WP isa (.seq (.block [.store (at_ .esp 4) .ebx, .store (at_ .esp 16) .edx, .alu .test .ecx (.reg .ecx)])
      (.ite .ne (.seq compressAt (.block [.mov .ecx (.imm 1), .alu .test .ecx (.reg .ecx)])) (.block [])))
      s (Step s₀ c) := by
  rcases h with ⟨c', hc, hP⟩ | ⟨hI, hecx, hedx⟩
  · refine WP.seq (stores_ok hp hP.toCommon hP.edx fun s₁ g₁ m₁ rd₁ wr₁ =>
      wp_test fun s₂ f₂ z₂ => WP.block_nil ?_)
    have hP₂ : Pending s₀ c' s₂ := (hP.putArgs hp g₁ m₁ rd₁ wr₁).congr f₂.gpr f₂.mem f₂.rd f₂.wr
    have hz : s₂.zf = some false := by rw [z₂, g₁, hP.ecx]; rfl
    refine WP.ite true (by show s₂.zf.map (!·) = _; rw [hz]; rfl) (fun _ => ?_) (fun h => by cases h)
    refine WP.seq (WP.mono (hP₂.compress_ok hp) fun s₃ hI₃ => ?_)
    refine wp_movi fun s₄ u₄ => wp_test fun s₅ f₅ z₅ => WP.block_nil ?_
    have hz₅ : s₅.zf = some false := by rw [z₅, u₄.gpr]; rfl
    refine .inr ⟨by rw [eval_ne, hz₅]; rfl, c', hc, hI₃.of_gpr (fun r hr => ?_) (by rw [f₅.mem, u₄.mem])
      (by rw [f₅.rd, u₄.rd]) (by rw [f₅.wr, u₄.wr])⟩
    rw [f₅.gpr, u₄.other r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)]
  · refine WP.seq (stores_ok hp hI.toCommon hedx fun s₁ g₁ m₁ rd₁ wr₁ =>
      wp_test fun s₂ f₂ z₂ => WP.block_nil ?_)
    have hz : s₂.zf = some true := by rw [z₂, g₁, hecx]; rfl
    refine WP.ite false (by show s₂.zf.map (!·) = _; rw [hz]; rfl) (fun h => by cases h) (fun _ => WP.block_nil ?_)
    refine .inl ⟨by rw [eval_ne, hz]; rfl, ?_⟩
    exact ((hI.putArgs hp g₁ m₁ rd₁ wr₁).of_gpr (fun r _ => by rw [f₂.gpr]) f₂.mem f₂.rd f₂.wr)

/-! ## Buffering data -/

section
variable (s₀ : State) (c : Nat)
/-- Bytes in the buffer before this iteration. -/
abbrev rr : Nat := (cnt s₀ + c) % 64
/-- Bytes copied into the buffer in this iteration. -/
abbrev tt : Nat := min (64 - rr s₀ c) (len s₀ - c)
/-- Where they go. -/
abbrev q : Addr := stA s₀ + BitVec.ofNat 64 (32 + rr s₀ c)
/-- The data copied. -/
abbrev xs : List Byte := ((D s₀).drop c).take (tt s₀ c)
end

theorem rr_lt (s₀ : State) (c : Nat) : rr s₀ c < 64 := Nat.mod_lt _ (by omega)
theorem rr_eq (s₀ : State) (c : Nat) : rr s₀ c = (cnt s₀ + c) % 64 := rfl
theorem tt_eq (s₀ : State) (c : Nat) : tt s₀ c = min (64 - rr s₀ c) (len s₀ - c) := rfl
theorem tt_le (s₀ : State) (c : Nat) : tt s₀ c ≤ len s₀ - c := Nat.min_le_right _ _
theorem tt_le' (s₀ : State) (c : Nat) : tt s₀ c ≤ 64 - rr s₀ c := Nat.min_le_left _ _

theorem xs_length (s₀ : State) (c : Nat) : (xs s₀ c).length = tt s₀ c := by
  have := tt_le s₀ c
  simp only [xs, List.length_take, List.length_drop, D_length]; omega

/-- The state while copying: `j` bytes copied, into memory `mI` otherwise unchanged. -/
structure Copy (s₀ : State) (c : Nat) (mI : Mem) (j : Nat) (s : State) : Prop where
  j_le : j ≤ tt s₀ c
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  ebx : s.gpr .ebx = st s₀
  esp : s.gpr .esp = esp₀ s₀
  edx : s.gpr .edx = scr s₀
  ebp : s.gpr .ebp = dp s₀ + BitVec.ofNat 32 (c + j)
  esi : s.gpr .esi = BitVec.ofNat 32 (len s₀ - c - tt s₀ c)
  edi : s.gpr .edi = st s₀ + BitVec.ofNat 32 (rr s₀ c + j)
  eax : s.gpr .eax = BitVec.ofNat 32 (tt s₀ c - j)
  mem : s.mem = writeBytes mI (q s₀ c) ((xs s₀ c).take j)

theorem write_frame (s₀ : State) (c : Nat) (mI : Mem) (j : Nat) (hj : j ≤ tt s₀ c) :
    Frame [stR s₀] mI (writeBytes mI (q s₀ c) ((xs s₀ c).take j)) := by
  have := tt_le' s₀ c; have := rr_lt s₀ c
  refine writeBytes_frame _ _ _ ?_
  simp only [q]
  exact contains_offset (by simp only [List.length_take]; omega) (by omega)

theorem copy_step {s₀ : State} (hp : Pre s₀) {c : Nat} {sI : State} (hI : Inv s₀ c sI) {j : Nat}
    (hj : j < tt s₀ c) {s : State} (h : Copy s₀ c sI.mem j s) :
    WP isa (.block [.movzx8 .ecx (at_ .ebp 0), .store8 (at_ .edi 32) .cl,
      .alu .add .ebp (.imm 1), .alu .add .edi (.imm 1), .alu .sub .eax (.imm 1)]) s fun s' =>
      Copy s₀ c sI.mem (j + 1) s' ∧ s'.zf = some (decide (tt s₀ c - (j + 1) = 0)) := by
  have hlen := len_lt s₀; have hd := hp.d_fit; have hst := hp.st_fit
  have hc := hI.c_le
  have hr := rr_lt s₀ c
  have ht := tt_le s₀ c; have ht' := tt_le' s₀ c
  -- The byte read.
  have ea₁ : s.ea (at_ .ebp 0) = dA s₀ + BitVec.ofNat 64 (c + j) := by
    rw [ea_at, h.ebp, addr_add_ofNat (by omega), Nat.add_zero]
  have hin : InRegions (s.rd ++ s.wr) (dA s₀ + BitVec.ofNat 64 (c + j)) 1 :=
    ⟨dR s₀, by simp [h.rd, hp.rd], contains_offset (by omega) (by omega)⟩
  have hbyte : s.mem (dA s₀ + BitVec.ofNat 64 (c + j)) = (D s₀).getD (c + j) 0 := by
    rw [h.mem, ← hI.data hp (by omega)]
    exact frame_bytes (write_frame s₀ c sI.mem j h.j_le) (R := dR s₀) (by simpa using hp.d_st)
      (by show len s₀ ≤ 2 ^ 64; omega) (by show c + j < len s₀; omega)
  -- The byte written.
  have ea₂ : ∀ t : State, t.gpr .edi = st s₀ + BitVec.ofNat 32 (rr s₀ c + j) →
      t.ea (at_ .edi 32) = q s₀ c + BitVec.ofNat 64 j := by
    intro t ht
    rw [ea_at, ht, addr_add_ofNat (by omega), q, BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2; omega
  have hout : InRegions s.wr (q s₀ c + BitVec.ofNat 64 j) 1 :=
    ⟨stR s₀, by simp [h.wr, hp.wr], by
      simp only [q]; rw [BitVec.add_assoc, ← BitVec.ofNat_add]; exact contains_offset (by omega) (by omega)⟩
  have hxs := xs_length s₀ c
  refine wp_movzx8 (d := .ecx) ea₁ hin fun s₁ u₁ => ?_
  refine wp_store8 (r := .cl) (a := q s₀ c + BitVec.ofNat 64 j)
    (ea₂ s₁ (by rw [u₁.other _ (by decide), h.edi])) (by rw [u₁.wr]; exact hout) fun s₂ u₂ => ?_
  refine wp_addi fun s₃ u₃ => wp_addi fun s₄ u₄ => wp_subi fun s₅ u₅ hz₅ => WP.block_nil ?_
  have g : ∀ r, r ≠ .eax → r ≠ .edi → r ≠ .ebp → r ≠ .ecx → s₅.gpr r = s.gpr r := fun r h1 h2 h3 h4 => by
    rw [u₅.other r h1, u₄.other r h2, u₃.other r h3, u₂.gpr, u₁.other r h4]
  have hrax : s₅.gpr .eax = BitVec.ofNat 32 (tt s₀ c - (j + 1)) := by
    rw [u₅.gpr, u₄.other .eax (by decide), u₃.other .eax (by decide), u₂.gpr, u₁.other .eax (by decide), h.eax,
      ofNat_pred (by omega), Nat.sub_sub]
  refine ⟨⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hrax, ?_⟩, ?_⟩
  · rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd]
  · rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr]
  · rw [g .ebx (by decide) (by decide) (by decide) (by decide), h.ebx]
  · rw [g .esp (by decide) (by decide) (by decide) (by decide), h.esp]
  · rw [g .edx (by decide) (by decide) (by decide) (by decide), h.edx]
  · rw [u₅.other .ebp (by decide), u₄.other .ebp (by decide), u₃.gpr, u₂.gpr, u₁.other .ebp (by decide), h.ebp,
      lit32, ofNat_add_add, Nat.add_assoc]
  · rw [g .esi (by decide) (by decide) (by decide) (by decide), h.esi]
  · rw [u₅.other .edi (by decide), u₄.gpr, u₃.other .edi (by decide), u₂.gpr, u₁.other .edi (by decide), h.edi,
      lit32, ofNat_add_add, Nat.add_assoc]
  · have hj' : j < (xs s₀ c).length := by omega
    have hv : BitVec.setWidth 8 (s₁.gpr Reg8.cl.reg) = (D s₀).getD (c + j) 0 := by
      rw [show Reg8.cl.reg = Reg.ecx from rfl, u₁.gpr, BitVec.setWidth_setWidth_of_le _ (by omega),
        BitVec.setWidth_eq, hbyte]
    rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem, hv, h.mem, List.take_add_one,
      List.getElem?_eq_getElem hj', Option.toList_some,
      writeBytes_snoc _ _ _ _ (by simp only [List.length_take]; omega)]
    have hl : (List.take j (xs s₀ c)).length = j := by rw [List.length_take, Nat.min_eq_left hj'.le]
    rw [hl]
    congr 1
    simp only [xs, List.getElem_take, List.getElem_drop, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (show c + j < (D s₀).length by rw [D_length]; omega), Option.getD_some]
  · rw [hz₅, u₄.other .eax (by decide), u₃.other .eax (by decide), u₂.gpr, u₁.other .eax (by decide), h.eax,
      ofNat_pred (by omega), ofNat_beq_zero (by omega), show tt s₀ c - j - 1 = tt s₀ c - (j + 1) by omega]

theorem copy_loop_ok {s₀ : State} (hp : Pre s₀) {c : Nat} {sI : State} (hI : Inv s₀ c sI) {s : State}
    (h : Copy s₀ c sI.mem 0 s) (ht : 0 < tt s₀ c) :
    WP isa (.loop (.block [.movzx8 .ecx (at_ .ebp 0), .store8 (at_ .edi 32) .cl,
      .alu .add .ebp (.imm 1), .alu .add .edi (.imm 1), .alu .sub .eax (.imm 1)]) .ne) s
      (Copy s₀ c sI.mem (tt s₀ c)) := by
  refine WP.loop (M := isa) (fun n s => ∃ j, n = tt s₀ c - j ∧ j < tt s₀ c ∧ Copy s₀ c sI.mem j s)
    ?_ (tt s₀ c) s ⟨0, rfl, ht, h⟩
  rintro n s ⟨j, rfl, hj, hc⟩
  refine WP.mono (copy_step hp hI hj hc) fun s' ⟨hc', hz⟩ => ?_
  by_cases hl : tt s₀ c - (j + 1) = 0
  · refine .inl ⟨by show s'.zf.map (!·) = _; rw [hz]; simp [hl], ?_⟩
    rwa [show j + 1 = tt s₀ c by omega] at hc'
  · exact .inr ⟨by show s'.zf.map (!·) = _; rw [hz]; simp [hl], _, by omega, j + 1, rfl, by omega, hc'⟩

/-- The memory after copying `tt` bytes. -/
theorem copied_facts {s₀ : State} (hp : Pre s₀) {c : Nat} {sI : State} (hI : Inv s₀ c sI) :
    let mem := writeBytes sI.mem (q s₀ c) (xs s₀ c)
    Frame [stR s₀, scR s₀, argR s₀] s₀.mem mem ∧ Saved s₀ mem ∧
      mem.readW (addr (esp₀ s₀) 4) 32 = st s₀ ∧ mem.readW (addr (esp₀ s₀) 16) 32 = scr s₀ ∧
      stateAt mem (stA s₀) = stateAt sI.mem (stA s₀) ∧
      bytesAt mem (stA s₀ + 32) (rr s₀ c + tt s₀ c) = bytesAt sI.mem (stA s₀ + 32) (rr s₀ c) ++ xs s₀ c := by
  intro mem
  have hr := rr_lt s₀ c; have ht' := tt_le' s₀ c
  have hxs := xs_length s₀ c
  have hf : Frame [stR s₀] sI.mem mem := by
    have := write_frame s₀ c sI.mem (tt s₀ c) (Nat.le_refl _)
    rwa [List.take_of_length_le (by omega)] at this
  have word : ∀ (R : Region), R.Disjoint (stR s₀) → R.Contains R.base 4 →
      mem.readW R.base 32 = sI.mem.readW R.base 32 := fun R hR hc =>
    hf.readW hc (by simpa using hR) (by decide)
  refine ⟨hI.frame.trans (hf.mono (by simp)), fun p hp' => ?_, ?_, ?_, ?_, ?_⟩
  · have hd : 112 ≤ p.2 ∧ p.2 + 4 ≤ 128 := by
      simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp'
      rcases hp' with rfl | rfl | rfl | rfl <;> simp
    rw [word ⟨addr (scr s₀) p.2, 4⟩ (hp.st_scr.symm.sub_left (hp.scr_sub (by omega))) (Region.contains_self _ _)]
    exact hI.saved p hp'
  · rw [word ⟨addr (esp₀ s₀) 4, 4⟩ (hp.a_st.sub_left (hp.arg_sub (by omega) (by omega))) (Region.contains_self _ _)]
    exact hI.a4
  · rw [word ⟨addr (esp₀ s₀) 16, 4⟩ (hp.a_st.sub_left (hp.arg_sub (by omega) (by omega)))
      (Region.contains_self _ _)]
    exact hI.a16
  · apply stateAt_congr
    intro i hi
    exact writeBytes_before _ _ _ (by omega) (by omega)
  · show bytesAt (writeBytes sI.mem (q s₀ c) (xs s₀ c)) (stA s₀ + 32) (rr s₀ c + tt s₀ c) = _
    rw [← hxs, show q s₀ c = stA s₀ + 32 + BitVec.ofNat 64 (rr s₀ c) by
      simp only [q, BitVec.ofNat_add]; rw [BitVec.add_assoc]; rfl]
    exact bytesAt_writeBytes _ _ _ _ (by omega)

/-- The state after copying, whatever `edi`, `eax` and `ecx` hold. -/
structure Copied (s₀ : State) (c : Nat) (mI : Mem) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  ebx : s.gpr .ebx = st s₀
  esp : s.gpr .esp = esp₀ s₀
  edx : s.gpr .edx = scr s₀
  ebp : s.gpr .ebp = dp s₀ + BitVec.ofNat 32 (c + tt s₀ c)
  esi : s.gpr .esi = BitVec.ofNat 32 (len s₀ - c - tt s₀ c)
  mem : s.mem = writeBytes mI (q s₀ c) (xs s₀ c)

theorem Copy.copied {s₀ : State} {c : Nat} {mI : Mem} {s : State} (h : Copy s₀ c mI (tt s₀ c) s) :
    Copied s₀ c mI s :=
  ⟨h.rd, h.wr, h.ebx, h.esp, h.edx, h.ebp, h.esi,
    by rw [h.mem, List.take_of_length_le (by rw [xs_length])]⟩

theorem Copied.of_gpr {s₀ : State} {c : Nat} {mI : Mem} {s s' : State} (h : Copied s₀ c mI s)
    (hg : ∀ r ∈ [Reg.ebx, .esp, .edx, .ebp, .esi], s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Copied s₀ c mI s' :=
  ⟨hrd.trans h.rd, hwr.trans h.wr, by rw [hg _ (by simp)]; exact h.ebx, by rw [hg _ (by simp)]; exact h.esp,
    by rw [hg _ (by simp)]; exact h.edx, by rw [hg _ (by simp)]; exact h.ebp,
    by rw [hg _ (by simp)]; exact h.esi, hm.trans h.mem⟩

/-- A full buffer: compress it. -/
theorem fill_pending {s₀ : State} (hp : Pre s₀) {c : Nat} {sI : State} (hI : Inv s₀ c sI) {s : State}
    (h : Copied s₀ c sI.mem s) (hfull : rr s₀ c + tt s₀ c = 64) :
    WP isa (.block [.mov .eax (.reg .ebx), .alu .add .eax (.imm 32), .mov .edi (.imm 0), .mov .ecx (.imm 1)])
      s (Pending s₀ (c + tt s₀ c)) := by
  have hr := rr_lt s₀ c; have ht := tt_le s₀ c; have ht' := tt_le' s₀ c; have hrr := rr_eq s₀ c
  have hxs := xs_length s₀ c
  have hc := hI.c_le
  obtain ⟨hfr, hsv, ha4, ha16, hst, hby⟩ := copied_facts hp hI
  refine wp_mov fun s₁ u₁ => wp_addi fun s₂ u₂ => wp_movi fun s₃ u₃ => wp_movi fun s₄ u₄ => WP.block_nil ?_
  have g : ∀ r, r ≠ .eax → r ≠ .edi → r ≠ .ecx → s₄.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [u₄.other r h3, u₃.other r h2, u₂.other r h1, u₁.other r h1]
  have m₄ : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have heax : s₄.gpr .eax = st s₀ + BitVec.ofNat 32 32 := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.gpr, h.ebx]; rfl
  refine ⟨⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, by rw [m₄, h.mem]; exact ha4, by rw [m₄, h.mem]; exact ha16,
      by rw [m₄, h.mem]; exact hfr, by rw [m₄, h.mem]; exact hsv⟩,
    by rw [u₄.other _ (by decide), u₃.gpr], by rw [u₄.gpr],
    by rw [g _ (by decide) (by decide) (by decide), h.edx], by omega, .inl heax, ?_⟩
  · rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd]
  · rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr]
  · rw [g .ebx (by decide) (by decide) (by decide), h.ebx]
  · rw [g .esp (by decide) (by decide) (by decide), h.esp]
  · rw [g .ebp (by decide) (by decide) (by decide), h.ebp]
  · rw [g .esi (by decide) (by decide) (by decide), h.esi, Nat.sub_sub]
  · intro m hm mem' hs
    rw [← take_add_data]
    have hmod := length_mid s₀ hm hc
    refine repr_append_block (hI.repr m hm) (by rw [hmod, hxs]; exact hfull) ?_
    rw [hs, m₄, h.mem, hst, heax, show (st s₀ + BitVec.ofNat 32 32).setWidth 64 = addr (st s₀) 32 from rfl,
      addr_eq (by have := hp.st_fit; omega)]
    refine congrArg (compress _) ?_
    apply parseBlock_congr
    intro k hk
    have hb := (hI.repr m hm).2
    rw [hmod] at hb
    rw [hb, show rr s₀ c + tt s₀ c = 64 from hfull] at hby
    rw [show stA s₀ + BitVec.ofNat 64 32 = stA s₀ + 32 from rfl]
    exact bytesAt_getD hby hk

/-- All the data fits in the buffer. -/
theorem fill_done {s₀ : State} (hp : Pre s₀) {c : Nat} {sI : State} (hI : Inv s₀ c sI) {s : State}
    (h : Copied s₀ c sI.mem s) (hedi : s.gpr .edi = BitVec.ofNat 32 (rr s₀ c + tt s₀ c))
    (hecx : s.gpr .ecx = 0) (hnf : rr s₀ c + tt s₀ c ≠ 64) : Done s₀ s := by
  have hr := rr_lt s₀ c; have ht := tt_le s₀ c; have ht' := tt_le' s₀ c
  have hrr := rr_eq s₀ c; have htt := tt_eq s₀ c
  have hxs := xs_length s₀ c
  have hc := hI.c_le
  have htl : tt s₀ c = len s₀ - c := by omega
  obtain ⟨hfr, hsv, ha4, ha16, hst, hby⟩ := copied_facts hp hI
  refine ⟨⟨⟨(Nat.le_refl _), h.rd, h.wr, h.ebx, h.esp, ?_, ?_, by rw [h.mem]; exact ha4, by rw [h.mem]; exact ha16,
    by rw [h.mem]; exact hfr, by rw [h.mem]; exact hsv⟩, ?_, fun m hm => ?_⟩, hecx, h.edx⟩
  · rw [h.ebp]; congr 2; omega
  · rw [h.esi]; congr 1; omega
  · rw [hedi]; congr 1; omega
  · have hmod := length_mid s₀ hm hc
    rw [show len s₀ = c + tt s₀ c by omega, ← take_add_data]
    refine repr_append_buf (hI.repr m hm) (by rw [hmod, hxs]; omega) (by rw [h.mem, hst]) ?_
    rw [hmod, hxs, h.mem, hby]
    have hb := (hI.repr m hm).2
    rw [hmod] at hb
    rw [hb]

theorem fill_ok {s₀ : State} (hp : Pre s₀) {c : Nat} {s : State} (hI : Inv s₀ c s) :
    WP isa fill s fun s' => (∃ c', c < c' ∧ Pending s₀ c' s') ∨ Done s₀ s' := by
  have hr := rr_lt s₀ c; have ht := tt_le s₀ c; have ht' := tt_le' s₀ c
  have hrr := rr_eq s₀ c; have htt := tt_eq s₀ c
  have hc := hI.c_le; have hlen := len_lt s₀
  unfold fill
  -- `edx := scratch; eax := 64 - edi; cmp esi, eax`
  refine WP.seq (wp_movm (a := addr (esp₀ s₀) 16) (by rw [ea_at, hI.esp])
    ⟨argR s₀, by simp [hI.rd, hI.wr, hp.wr], hp.arg_in (by omega) (by omega)⟩ fun s₁ u₁ =>
    wp_movi fun s₂ u₂ => wp_sub fun s₃ u₃ _ => wp_cmp fun s₄ f₄ cf₄ _ => WP.block_nil ?_)
  have e₄ : ∀ r, r ≠ .eax → r ≠ .edx → s₄.gpr r = s.gpr r := fun r h h' => by
    rw [f₄.gpr, u₃.other r h, u₂.other r h, u₁.other r h']
  have hm₄ : s₄.mem = s.mem := by rw [f₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have hrd₄ : s₄.rd = s.rd := by rw [f₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have hwr₄ : s₄.wr = s.wr := by rw [f₄.wr, u₃.wr, u₂.wr, u₁.wr]
  have hedx₄ : s₄.gpr .edx = scr s₀ := by
    rw [f₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hI.a16]
  have heax₃ : s₃.gpr .eax = BitVec.ofNat 32 (64 - rr s₀ c) := by
    rw [u₃.gpr, u₂.gpr, u₂.other _ (by decide), u₁.other _ (by decide), hI.edi, ← rr_eq, lit32,
      sub_ofNat (a := 64) (b := rr s₀ c) (by omega)]
  have hcf : s₄.cf = some (decide (len s₀ - c < 64 - rr s₀ c)) := by
    rw [cf₄, heax₃, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hI.esi,
      toNat_ofNat_lt (by omega), toNat_ofNat_lt (by omega)]
  -- `eax := min(eax, esi)`
  refine WP.seq (WP.mono (Q := fun (s₅ : State) => s₅.gpr .eax = BitVec.ofNat 32 (tt s₀ c) ∧
    (∀ r, r ≠ .eax → s₅.gpr r = s₄.gpr r) ∧ s₅.mem = s₄.mem ∧ s₅.rd = s₄.rd ∧ s₅.wr = s₄.wr) ?_
    fun s₅ ⟨heax₅, g₅, m₅, rd₅, wr₅⟩ => ?_)
  · refine WP.ite (decide (len s₀ - c < 64 - rr s₀ c)) (by show s₄.cf = _; rw [hcf]) (fun hb => ?_) (fun hb => ?_)
    · refine wp_mov fun s₅ u₅ => WP.block_nil ⟨?_, u₅.other, u₅.mem, u₅.rd, u₅.wr⟩
      rw [u₅.gpr, e₄ _ (by decide) (by decide), hI.esi]; congr 1; simp at hb; omega
    · refine WP.block_nil ⟨?_, fun _ _ => rfl, rfl, rfl, rfl⟩
      rw [f₄.gpr, heax₃]; congr 1; simp at hb; omega
  -- `esi -= eax; edi += ebx; test eax, eax`
  refine WP.seq (wp_sub fun s₆ u₆ _ => wp_add fun s₇ u₇ => wp_test fun s₈ f₈ z₈ => WP.block_nil ?_)
  have g₈ : ∀ r, r ≠ .esi → r ≠ .edi → r ≠ .eax → r ≠ .edx → s₈.gpr r = s.gpr r := fun r h1 h2 h3 h4 => by
    rw [f₈.gpr, u₇.other r h2, u₆.other r h1, g₅ r h3, e₄ r h3 h4]
  have hm₈ : s₈.mem = s.mem := by rw [f₈.mem, u₇.mem, u₆.mem, m₅, hm₄]
  have hC₀ : Copy s₀ c s.mem 0 s₈ := by
    refine ⟨Nat.zero_le _, by rw [f₈.rd, u₇.rd, u₆.rd, rd₅, hrd₄, hI.rd], by rw [f₈.wr, u₇.wr, u₆.wr, wr₅, hwr₄, hI.wr],
      by rw [g₈ _ (by decide) (by decide) (by decide) (by decide), hI.ebx],
      by rw [g₈ _ (by decide) (by decide) (by decide) (by decide), hI.esp],
      by rw [f₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), g₅ _ (by decide), hedx₄],
      by rw [g₈ _ (by decide) (by decide) (by decide) (by decide), hI.ebp, Nat.add_zero], ?_, ?_, ?_,
      by rw [hm₈, List.take_zero, writeBytes_nil]⟩
    · rw [f₈.gpr, u₇.other _ (by decide), u₆.gpr, g₅ _ (by decide), e₄ _ (by decide) (by decide), hI.esi,
        heax₅, sub_ofNat (by omega)]
    · rw [f₈.gpr, u₇.gpr, u₆.other _ (by decide), g₅ _ (by decide), e₄ _ (by decide) (by decide), hI.edi,
        u₆.other _ (by decide), g₅ _ (by decide), e₄ _ (by decide) (by decide), hI.ebx, BitVec.add_comm,
        ← rr_eq, Nat.add_zero]
    · rw [f₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), heax₅, Nat.sub_zero]
  have hz₈ : s₈.zf = some (decide (tt s₀ c = 0)) := by
    rw [z₈, u₇.other _ (by decide), u₆.other _ (by decide), heax₅, BitVec.and_self, ofNat_beq_zero (by omega)]
  -- Copy the bytes.
  refine WP.seq (WP.mono (Q := Copy s₀ c s.mem (tt s₀ c)) ?_ fun s₉ hC => ?_)
  · refine WP.ite (decide (tt s₀ c = 0)) (by show s₈.zf = _; rw [hz₈]) (fun hb => ?_) (fun hb => ?_)
    · simp only [decide_eq_true_eq] at hb
      exact WP.block_nil (hb ▸ hC₀)
    · simp only [decide_eq_false_iff_not] at hb
      exact copy_loop_ok hp hI hC₀ (by omega)
  -- Is the buffer full?
  refine WP.seq (wp_sub fun s₁₀ u₁₀ _ => wp_movi fun s₁₁ u₁₁ => wp_cmpi fun s₁₂ f₁₂ _ z₁₂ => WP.block_nil ?_)
  have hC₁₂ : Copied s₀ c s.mem s₁₂ :=
    hC.copied.of_gpr (fun r hr => by
      rw [f₁₂.gpr, u₁₁.other r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide),
        u₁₀.other r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)])
      (by rw [f₁₂.mem, u₁₁.mem, u₁₀.mem]) (by rw [f₁₂.rd, u₁₁.rd, u₁₀.rd]) (by rw [f₁₂.wr, u₁₁.wr, u₁₀.wr])
  have hedi₁₂ : s₁₂.gpr .edi = BitVec.ofNat 32 (rr s₀ c + tt s₀ c) := by
    rw [f₁₂.gpr, u₁₁.other _ (by decide), u₁₀.gpr, hC.edi, hC.ebx, BitVec.add_comm, BitVec.add_sub_cancel]
  have hz₁₂ : s₁₂.zf = some (decide (rr s₀ c + tt s₀ c = 64)) := by
    rw [z₁₂, ← f₁₂.gpr, hedi₁₂, lit32, sub_beq (a := rr s₀ c + tt s₀ c) (b := 64) (by omega) (by omega)]
  have hecx : s₁₂.gpr .ecx = 0 := by rw [f₁₂.gpr, u₁₁.gpr]
  refine WP.ite (decide (rr s₀ c + tt s₀ c = 64)) (by show s₁₂.zf = _; rw [hz₁₂]) (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    exact WP.mono (fill_pending hp hI hC₁₂ hb) fun s' h => .inl ⟨c + tt s₀ c, by omega, h⟩
  · simp only [decide_eq_false_iff_not] at hb
    exact WP.block_nil (.inr (fill_done hp hI hC₁₂ hedi₁₂ hecx hb))

theorem body_ok {s₀ : State} (hp : Pre s₀) {c : Nat} {s : State} (hI : Inv s₀ c s) :
    WP isa updateBody s (Step s₀ c) := by
  have hlen := len_lt s₀; have hc := hI.c_le; have hr := rr_lt s₀ c
  unfold updateBody
  refine WP.seq (wp_test fun s₁ f₁ z₁ => WP.block_nil ?_)
  have hI₁ := hI.of_gpr (fun r _ => by rw [f₁.gpr]) f₁.mem f₁.rd f₁.wr
  refine WP.seq (WP.mono (Q := fun s' => (∃ c', c < c' ∧ Pending s₀ c' s') ∨ Done s₀ s') ?_
    fun s' h => tail_ok hp h)
  refine WP.ite (decide (rr s₀ c = 0))
    (by show s₁.zf = _; rw [z₁, hI.edi, BitVec.and_self, ofNat_beq_zero (by omega)])
    (fun hb => ?_) (fun _ => fill_ok hp hI₁)
  simp only [decide_eq_true_eq] at hb
  refine WP.seq (wp_cmpi fun s₂ f₂ cf₂ _ => WP.block_nil ?_)
  have hI₂ := hI₁.of_gpr (fun r _ => by rw [f₂.gpr]) f₂.mem f₂.rd f₂.wr
  have hcf : s₂.cf = some (decide (len s₀ - c < 64)) := by
    rw [cf₂, hI₁.esi, toNat_ofNat_lt (by omega)]; rfl
  refine WP.ite (!decide (len s₀ - c < 64)) (by show s₂.cf.map (!·) = _; rw [hcf]; rfl)
    (fun hb' => ?_) (fun _ => fill_ok hp hI₂)
  simp only [Bool.not_eq_true', decide_eq_false_iff_not, not_lt] at hb'
  exact WP.mono (direct_ok hp hI₂ hb hb') fun s' h => .inl ⟨c + 64, by omega, h⟩

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa update s₀ fun s' => abiPreserved s₀ s' ∧ Proof.Sha256.updateX86.post s₀ s' := by
  unfold update
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ hI => ?_)
  refine WP.seq (WP.mono (Q := Inv s₀ (len s₀)) ?_ fun s₂ hI₂ => epilogue_ok hp hI₂)
  refine WP.loop (M := isa) (fun n s => ∃ c, n = len s₀ - c ∧ Inv s₀ c s) ?_ (len s₀) s₁ ⟨0, rfl, hI⟩
  rintro n s ⟨c, rfl, hI⟩
  refine WP.mono (body_ok hp hI) fun s' h => ?_
  rcases h with ⟨he, hI'⟩ | ⟨he, c', hc, hI'⟩
  · exact .inl ⟨he, hI'⟩
  · exact .inr ⟨he, len s₀ - c', by have := hI'.c_le; omega, c', rfl, hI'⟩

/-! ## Constant time -/

/-- The initial taint: `esp + 4` is the base of the (public) arguments, whose
words at offsets 0 and 20 are the base addresses of `state` and `scratch`. -/
def τ₀ : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [96, 160, 24], bases := [(.esp, 2, 4)],
    slots := [(2, 0, 24)], wbases := [(2, 0, 0), (2, 20, 1)] }

theorem argWord_eq {s : State} (hsp : (s.gpr .esp).toNat + 28 ≤ 2 ^ 32) {k : Nat} (hk : k < 24) :
    addr (s.gpr .esp) 4 + BitVec.ofNat 64 k = argAddr s (k / 4) + BitVec.ofNat 64 (k % 4) := by
  simp only [argAddr]
  rw [show (s.gpr .esp + BitVec.ofNat 32 (4 + 4 * (k / 4))).setWidth 64 = addr (s.gpr .esp) (4 + 4 * (k / 4))
    from rfl, addr_eq (by omega), addr_eq (by omega), BitVec.add_assoc, BitVec.add_assoc,
    ← BitVec.ofNat_add, ← BitVec.ofNat_add]
  congr 2; omega

theorem wf₀ {s : State} (hp : Pre s) : VG.X86.Taint.Wf τ₀ s := by
  have hst := hp.st_fit; have hsc := hp.scr_fit; have hs := hp.sp_fit
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun _ => ⟨by simp [hp.wr, τ₀], ?_, ?_⟩, ?_, ?_, fun h => absurd h (Nat.lt_irrefl 0),
    fun _ h => (List.not_mem_nil h).elim⟩
  · simp only [hp.wr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, List.Pairwise.nil, and_true]
    exact ⟨⟨hp.st_scr, hp.a_st.symm⟩, hp.a_scr.symm, fun _ h => h.elim⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · simp only [addr_toNat]; omega
    · simp only [addr_toNat]; omega
    · simp only; rw [addr_eq (by omega), BitVec.toNat_add, addr_toNat, BitVec.toNat_ofNat]; omega
  · intro p hp'
    simp only [τ₀, List.mem_singleton] at hp'
    subst hp'
    simp [VG.X86.Taint.region, hp.wr]
  · intro p hp'
    simp only [τ₀, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl
    · refine ⟨by decide, ?_⟩
      simp only [VG.X86.Taint.byteAddr, VG.X86.Taint.region, hp.wr]
      show addr (s.mem.readW (addr (esp₀ s) 4 + BitVec.ofNat 64 0) 32) 0 = stA s
      simp [addr, st, arg, argAddr]
    · refine ⟨by decide, ?_⟩
      simp only [VG.X86.Taint.byteAddr, VG.X86.Taint.region, hp.wr]
      show addr (s.mem.readW (addr (esp₀ s) 4 + BitVec.ofNat 64 20) 32) 0 = scA s
      rw [argWord_eq hs (k := 20) (by omega)]
      simp [addr, scr, arg]

theorem agree₀ {s₁ s₂ : State} (h₁ : Proof.Sha256.updateX86.pre s₁) (h₂ : Proof.Sha256.updateX86.pre s₂)
    (hpub : Proof.Sha256.updateX86.pub s₁ s₂) : VG.X86.Taint.Agree τ₀ s₁ s₂ := by
  obtain ⟨hesp, ha⟩ := hpub
  have hp₁ := pre_of h₁; have hp₂ := pre_of h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, wf₀ hp₁, wf₀ hp₂, ?_, ?_,
    fun h => absurd h (Nat.lt_irrefl 0), fun _ _ h => absurd h (Nat.not_lt_zero _)⟩
  · simp only [τ₀, RegSet.mem_ofList, List.mem_singleton] at hr
    subst hr; exact hesp
  · rw [hp₁.wr, hp₂.wr]
    simp only [stR, scR, argR, stA, scA, st, scr, esp₀, ha 0 (by omega), ha 5 (by omega), hesp]
  · intro sl hsl
    simp only [τ₀, List.mem_singleton] at hsl
    subst hsl; decide
  · intro sl hsl k _ hk
    simp only [τ₀, List.mem_singleton] at hsl
    subst hsl
    simp only [Nat.zero_add] at hk
    simp only [VG.X86.Taint.byteAddr, VG.X86.Taint.region, hp₁.wr, hp₂.wr]
    show s₁.mem (addr (esp₀ s₁) 4 + BitVec.ofNat 64 k) = s₂.mem (addr (esp₀ s₂) 4 + BitVec.ofNat 64 k)
    rw [argWord_eq hp₁.sp_fit hk, argWord_eq hp₂.sp_fit hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega))]
    exact congrArg _ (ha _ (by omega))

/-- Memory holding the arguments `0x1000, 0, 0, 0x2000, 0, 0x3000` at `0x4004`. -/
def satMem : Mem := fun a =>
  if a = 0x4005 then 0x10 else if a = 0x4011 then 0x20 else if a = 0x4019 then 0x30 else 0

/-- A state satisfying the precondition (with no data). -/
def sat : State where
  gpr r := match r with
    | .esp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMem
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, 96⟩, ⟨0x3000, 160⟩, ⟨0x4004, 24⟩]

theorem sat_pre : Proof.Sha256.updateX86.pre sat := by
  have a0 : arg sat 0 = 0x1000 := by decide
  have a3 : arg sat 3 = 0x2000 := by decide
  have a4 : arg sat 4 = 0 := by decide
  have a5 : arg sat 5 = 0x3000 := by decide
  have e : argAddr sat 0 = 0x4004 := by decide
  simp only [Proof.Sha256.updateX86, a0, a3, a4, a5, e]
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by decide, by decide, by decide, by decide⟩ <;>
  · intro a h₁ h₂
    simp only [Region.Contains, sat] at h₁ h₂
    bv_omega

theorem update_verified : Verified X86.target update Proof.Sha256.updateX86 := by
  refine ⟨fun s hs => ?_, ?_, ⟨sat, sat_pre⟩⟩
  · obtain ⟨t, s', he, h⟩ := correct (pre_of hs)
    exact ⟨t, s', he, h⟩
  · exact VG.Taint.constantTime (A := taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁ h₂ hp) (by taint_decide)

end VG.Proof.Sha256.X86.Stream.Update
