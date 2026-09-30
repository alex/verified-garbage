import VerifiedGarbage.Proof.MdStream.X86.Common
import Mathlib.Tactic.Tauto
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Streaming Merkle–Damgård hash functions on x86 (32-bit): `update`

Untrusted: everything here is checked by Lean. The correctness of `update`,
for any hash function (`Md`) and any correct compression function
(`CalleeOk`), with `state` in `ebx`, `data` in `ebp`, the bytes left in
`esi`, the buffered bytes in `edi`, and `scratch` read from its argument word
(`[esp + 24]`, never written) for each call of the compression function
(`compressAt_ok`), which uses the 20 bytes below `esp`; and, from the taint
analysis of each hash function's code (which looks into the compression
function), that it is constant time.
-/

namespace VG.Proof.MdStream.X86.Update

open VG VG.X86 VG.Impl.MdStream.X86
open VG.Spec.Sha256 (bytesAt)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil writeBytes_snoc writeBytes_before bytesAt_writeBytes
  writeBytes_frame)

/-! ## The precondition -/

section
variable (P : Params) (S : Nat) (s₀ : State)

abbrev esp₀ : BitVec 32 := s₀.gpr .esp
abbrev st : BitVec 32 := arg s₀ 0
abbrev cnt : Nat := (count s₀).toNat
abbrev dp : BitVec 32 := arg s₀ 3
abbrev len : Nat := (arg s₀ 4).toNat
abbrev scr : BitVec 32 := arg s₀ 5
abbrev stA : Addr := (st s₀).setWidth 64
abbrev dA : Addr := (dp s₀).setWidth 64
abbrev scA : Addr := (scr s₀).setWidth 64
abbrev stR : Region := ⟨stA s₀, P.N + 64⟩
abbrev dR : Region := ⟨dA s₀, len s₀⟩
abbrev scR : Region := ⟨scA s₀, S⟩
abbrev argR : Region := ⟨argAddr s₀ 0, 24⟩
abbrev retR : Region := ⟨(esp₀ s₀).setWidth 64, 4⟩
abbrev stkR : Region := below (esp₀ s₀) 20
/-- The buffer. -/
abbrev buf : Addr := stA s₀ + BitVec.ofNat 64 P.N
/-- The data. -/
abbrev D : List Byte := bytesAt s₀.mem (dA s₀) (len s₀)

/-- Our caller's registers are saved in the scratch space. -/
def Saved (m : Mem) : Prop := ∀ p ∈ saved P, m.readW (addr (scr s₀) p.2) 32 = s₀.gpr p.1

end

/-- The messages the initial state represents, from `iv`. -/
def R₀ {P : Params} (H : Md 64 P.N 8) (s₀ : State) (iv : H.HV) (m : List Byte) : Prop :=
  H.Repr iv s₀.mem (stA s₀) m ∧ count s₀ = BitVec.ofNat 64 m.length

structure Pre (P : Params) (S : Nat) (s₀ : State) : Prop where
  rd : s₀.rd = [dR s₀, argR s₀]
  wr : s₀.wr = [stR P s₀, scR S s₀]
  st_scr : (stR P s₀).Disjoint (scR S s₀)
  d_st : (dR s₀).Disjoint (stR P s₀)
  d_scr : (dR s₀).Disjoint (scR S s₀)
  a_st : (argR s₀).Disjoint (stR P s₀)
  a_scr : (argR s₀).Disjoint (scR S s₀)
  ret_st : (retR s₀).Disjoint (stR P s₀)
  ret_scr : (retR s₀).Disjoint (scR S s₀)
  stk_st : (stkR s₀).Disjoint (stR P s₀)
  stk_scr : (stkR s₀).Disjoint (scR S s₀)
  stk_d : (stkR s₀).Disjoint (dR s₀)
  st_fit : (st s₀).toNat + (P.N + 64) ≤ 2 ^ 32
  d_fit : (dp s₀).toNat + len s₀ ≤ 2 ^ 32
  scr_fit : (scr s₀).toNat + S ≤ 2 ^ 32
  sp_lo : 20 ≤ (esp₀ s₀).toNat
  sp_fit : (esp₀ s₀).toNat + 28 ≤ 2 ^ 32

section
variable {P : Params} {S : Nat} {H : Md 64 P.N 8}

theorem pre_of {s₀ : State} (h : (updK H S).pre s₀) : Pre P S s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := h
  have e := stk_eq h16
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, by show (below _ _).Disjoint _; rw [e]; exact h10,
    by show (below _ _).Disjoint _; rw [e]; exact h11, by show (below _ _).Disjoint _; rw [e]; exact h12,
    h13, h14, h15, h16, h17⟩

theorem cnt_mod (s₀ : State) : cnt s₀ % 64 = (arg s₀ 1).toNat % 64 := by
  simp only [cnt, count]
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt (arg s₀ 1).isLt, Nat.shiftLeft_eq]
  omega

theorem R₀.length {s₀ : State} {iv : H.HV} {m : List Byte} (h : R₀ H s₀ iv m) : cnt s₀ % 64 = m.length % 64 := by
  rw [cnt, h.2, BitVec.toNat_ofNat]
  omega

theorem len_lt (s₀ : State) : len s₀ < 2 ^ 32 := (arg s₀ 4).isLt

theorem D_length (s₀ : State) : (D s₀).length = len s₀ := by simp [bytesAt]

namespace Pre
variable {s₀ : State} (hp : Pre P S s₀)
include hp

theorem scr_in {d : Nat} (hd : d + 4 ≤ S) : (scR S s₀).Contains (addr (scr s₀) d) 4 :=
  contains_addr hd (by omega) hp.scr_fit

theorem arg_in {d : Nat} (hd₁ : 4 ≤ d) (hd : d + 4 ≤ 28) : (argR s₀).Contains (addr (esp₀ s₀) d) 4 := by
  have := hp.sp_fit
  show (⟨addr (esp₀ s₀) 4, 24⟩ : Region).Contains _ _
  rw [addr_eq (by omega), addr_eq (by omega)]
  exact Offset.contains _ hd₁ (by omega) (by omega)

/-- A word of the scratch space, as a region. -/
theorem scr_sub {d : Nat} (hd : d + 4 ≤ S) : Region.Sub ⟨addr (scr s₀) d, 4⟩ (scR S s₀) := by
  rw [addr_eq (by have := hp.scr_fit; omega)]
  exact sub_offset hd (by have := hp.scr_fit; omega)

/-- An argument word, as a region. -/
theorem arg_sub {d : Nat} (hd₁ : 4 ≤ d) (hd : d + 4 ≤ 28) : Region.Sub ⟨addr (esp₀ s₀) d, 4⟩ (argR s₀) := by
  have := hp.sp_fit
  show Region.Sub _ ⟨addr (esp₀ s₀) 4, 24⟩
  rw [addr_eq (by omega), addr_eq (by omega)]
  exact Offset.sub _ hd₁ (by omega)

theorem a_stk : (argR s₀).Disjoint (stkR s₀) := by
  have := hp.sp_fit; have := hp.sp_lo
  show Region.Disjoint ⟨addr (esp₀ s₀) 4, 24⟩ ⟨(esp₀ s₀ - BitVec.ofNat 32 20).setWidth 64, 20⟩
  rw [addr_eq (by omega), Taint.sub_setWidth (by omega)]
  exact Offset.disjoint_below _ (by omega)

theorem ret_stk : (retR s₀).Disjoint (stkR s₀) := by
  have := hp.sp_fit; have := hp.sp_lo
  show Region.Disjoint ⟨(esp₀ s₀).setWidth 64, 4⟩ ⟨(esp₀ s₀ - BitVec.ofNat 32 20).setWidth 64, 20⟩
  rw [Taint.sub_setWidth (by omega)]
  exact Offset.base_disjoint_below _ (by omega)

end Pre

end

/-! ## Invariants -/

/-- What holds throughout, after consuming `c` bytes of data. -/
structure Common (P : Params) (S : Nat) (s₀ : State) (c : Nat) (s : State) : Prop where
  c_le : c ≤ len s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  ebx : s.gpr .ebx = st s₀
  esp : s.gpr .esp = esp₀ s₀
  ebp : s.gpr .ebp = dp s₀ + BitVec.ofNat 32 c
  esi : s.gpr .esi = BitVec.ofNat 32 (len s₀ - c)
  frame : Frame [stR P s₀, scR S s₀, stkR s₀] s₀.mem s.mem
  saved : Saved P s₀ s.mem

/-- The loop invariant: the state represents the message followed by the
first `c` bytes of data. -/
structure Inv {P : Params} (S : Nat) (H : Md 64 P.N 8) (s₀ : State) (c : Nat) (s : State) : Prop
    extends Common P S s₀ c s where
  edi : s.gpr .edi = BitVec.ofNat 32 ((cnt s₀ + c) % 64)
  repr : ∀ iv m, R₀ H s₀ iv m → H.Repr iv s.mem (stA s₀) (m ++ (D s₀).take c)

/-- `k ≥ 1` whole blocks are ready at `eax` (the buffer, or the data), and
compressing them absorbs the first `c` bytes of data. -/
structure Pending {P : Params} (S : Nat) (H : Md 64 P.N 8) (s₀ : State) (c k : Nat) (s : State) : Prop
    extends Common P S s₀ c s where
  edi : s.gpr .edi = 0
  ecx : s.gpr .ecx = BitVec.ofNat 32 k
  k_pos : 0 < k
  mod : (cnt s₀ + c) % 64 = 0
  src : (s.gpr .eax = st s₀ + BitVec.ofNat 32 P.N ∧ k = 1) ∨
    ∃ c₀, s.gpr .eax = dp s₀ + BitVec.ofNat 32 c₀ ∧ c₀ + 64 * k ≤ len s₀
  repr : ∀ iv m, R₀ H s₀ iv m → ∀ mem', H.stateAt mem' (stA s₀) =
      H.compressBlocks (H.stateAt s.mem (stA s₀)) s.mem ((s.gpr .eax).setWidth 64) k →
    H.Repr iv mem' (stA s₀) (m ++ (D s₀).take c)

/-- All the data is absorbed, and nothing is pending. -/
def Done {P : Params} (S : Nat) (H : Md 64 P.N 8) (s₀ : State) (s : State) : Prop :=
  Inv S H s₀ (len s₀) s ∧ s.gpr .ecx = 0

section
variable {P : Params} {S : Nat} {H : Md 64 P.N 8}

theorem Common.of_gpr {s₀ : State} {c : Nat} {s s' : State} (h : Common P S s₀ c s)
    (hg : ∀ r ∈ [Reg.ebx, .esp, .ebp, .esi], s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Common P S s₀ c s' where
  c_le := h.c_le
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  ebx := by rw [hg _ (by simp)]; exact h.ebx
  esp := by rw [hg _ (by simp)]; exact h.esp
  ebp := by rw [hg _ (by simp)]; exact h.ebp
  esi := by rw [hg _ (by simp)]; exact h.esi
  frame := by rw [hm]; exact h.frame
  saved := by rw [hm]; exact h.saved

theorem Inv.of_gpr {s₀ : State} {c : Nat} {s s' : State} (h : Inv S H s₀ c s)
    (hg : ∀ r ∈ [Reg.ebx, .esp, .ebp, .esi, .edi], s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Inv S H s₀ c s' :=
  { h.toCommon.of_gpr (fun r hr => hg r (by simp at hr ⊢; tauto)) hm hrd hwr with
    edi := by rw [hg _ (by simp)]; exact h.edi
    repr := by rw [hm]; exact h.repr }

/-- The argument words are never written. -/
theorem Common.arg {s₀ : State} (hp : Pre P S s₀) {c : Nat} {s : State} (h : Common P S s₀ c s) {d : Nat}
    (h₁ : 4 ≤ d) (h₂ : d + 4 ≤ 28) :
    s.mem.readW (addr (esp₀ s₀) d) 32 = s₀.mem.readW (addr (esp₀ s₀) d) 32 := by
  refine h.frame.readW (r := ⟨addr (esp₀ s₀) d, 4⟩) (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.a_st.sub_left (hp.arg_sub h₁ h₂)
  · exact hp.a_scr.sub_left (hp.arg_sub h₁ h₂)
  · exact hp.a_stk.sub_left (hp.arg_sub h₁ h₂)

/-! ## Prologue and epilogue -/

/-- The memory after saving our caller's registers. -/
def saveMem (P : Params) (s₀ : State) : Mem :=
  (((s₀.mem.writeW (addr (scr s₀) P.so) (s₀.gpr .ebx)).writeW (addr (scr s₀) (P.so + 4)) (s₀.gpr .esi)).writeW
    (addr (scr s₀) (P.so + 8)) (s₀.gpr .edi)).writeW (addr (scr s₀) (P.so + 12)) (s₀.gpr .ebp)

theorem saveMem_frame (hd : Dims P S) {s₀ : State} (hp : Pre P S s₀) : Frame [scR S s₀] s₀.mem (saveMem P s₀) := by
  have := hd.so
  have c : ∀ d, d + 4 ≤ S → (scR S s₀).Contains (addr (scr s₀) d) (32 / 8) := fun d hd => hp.scr_in hd
  simp only [saveMem]
  exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c P.so (by omega))).writeW
    (List.mem_singleton_self _) _ (c (P.so + 4) (by omega))).writeW (List.mem_singleton_self _) _
    (c (P.so + 8) (by omega))).writeW (List.mem_singleton_self _) _ (c (P.so + 12) (by omega))

theorem saveMem_saved (hd : Dims P S) {s₀ : State} (hp : Pre P S s₀) : Saved P s₀ (saveMem P s₀) := by
  have hs := hp.scr_fit; have := hd.so
  have w : ∀ (m : Mem) (v : BitVec 32) (d e : Nat), d + 4 ≤ S → e + 4 ≤ S → d + 4 ≤ e ∨ e + 4 ≤ d →
      (m.writeW (addr (scr s₀) e) v).readW (addr (scr s₀) d) 32 = m.readW (addr (scr s₀) d) 32 :=
    fun m v d e h₁ h₂ h => readW_writeW_addr m v (by omega) (by omega) h
  intro p hp'
  simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp'
  rcases hp' with rfl | rfl | rfl | rfl <;> simp only [saveMem]
  · rw [w _ _ P.so (P.so + 12) (by omega) (by omega) (by omega),
      w _ _ P.so (P.so + 8) (by omega) (by omega) (by omega),
      w _ _ P.so (P.so + 4) (by omega) (by omega) (by omega), Mem.readW_writeW_self32]
  · rw [w _ _ (P.so + 4) (P.so + 12) (by omega) (by omega) (by omega),
      w _ _ (P.so + 4) (P.so + 8) (by omega) (by omega) (by omega), Mem.readW_writeW_self32]
  · rw [w _ _ (P.so + 8) (P.so + 12) (by omega) (by omega) (by omega), Mem.readW_writeW_self32]
  · rw [Mem.readW_writeW_self32]

theorem prologue_ok (hd : Dims P S) {s₀ : State} (hp : Pre P S s₀) :
    WP isa (.block (([.mov .eax (.mem (at_ .esp 24))] : List Instr) ++ save P .eax ++
      ([.mov .ebx (.mem (at_ .esp 4)), .mov .ebp (.mem (at_ .esp 16)), .mov .esi (.mem (at_ .esp 20)),
       .mov .edi (.mem (at_ .esp 8)), .alu .and .edi (.imm 63)] : List Instr))) s₀ (Inv S H s₀ 0) := by
  have := hd.so; have := hd.N
  have rin : ∀ d, 4 ≤ d → d + 4 ≤ 28 → InRegions (s₀.rd ++ s₀.wr) (addr (esp₀ s₀) d) 4 :=
    fun d h₁ h₂ => ⟨argR s₀, by simp [hp.rd], hp.arg_in h₁ h₂⟩
  have sin : ∀ d, d + 4 ≤ S → InRegions s₀.wr (addr (scr s₀) d) 4 :=
    fun d hd => ⟨scR S s₀, by simp [hp.wr], hp.scr_in hd⟩
  -- The saves only touch the scratch space, so the arguments stay readable.
  have sepA : ∀ d e, P.so ≤ d → d + 4 ≤ P.so + 16 → 4 ≤ e → e + 4 ≤ 28 →
      Mem.Sep (addr (esp₀ s₀) e) 4 (addr (scr s₀) d) 4 := by
    intro d e h₁ h₂ h₃ h₄ x hx hy
    exact hp.a_scr x (hp.arg_sub h₃ h₄ x (by simp only [Region.Contains]; omega))
      (hp.scr_sub (d := d) (by omega) x (by simp only [Region.Contains]; omega))
  have argSave : ∀ e, 4 ≤ e → e + 4 ≤ 28 →
      (saveMem P s₀).readW (addr (esp₀ s₀) e) 32 = s₀.mem.readW (addr (esp₀ s₀) e) 32 := by
    intro e h₁ h₂
    simp only [saveMem]
    rw [Mem.readW_writeW_sep (sepA (P.so + 12) e (by omega) (by omega) h₁ h₂) (by decide),
      Mem.readW_writeW_sep (sepA (P.so + 8) e (by omega) (by omega) h₁ h₂) (by decide),
      Mem.readW_writeW_sep (sepA (P.so + 4) e (by omega) (by omega) h₁ h₂) (by decide),
      Mem.readW_writeW_sep (sepA P.so e (by omega) (by omega) h₁ h₂) (by decide)]
  simp only [List.cons_append, save_eq, List.nil_append]
  refine wp_movm (a := addr (esp₀ s₀) 24) (ea_at _ _ _) (rin 24 (by omega) (by omega)) fun s₁ u₁ => ?_
  have e₁ : s₁.gpr .eax = scr s₀ := u₁.gpr
  refine wp_store (a := addr (scr s₀) P.so) (by rw [ea_at, e₁]) (by rw [u₁.wr]; exact sin P.so (by omega))
    fun s₂ u₂ => ?_
  refine wp_store (a := addr (scr s₀) (P.so + 4)) (by rw [ea_at, u₂.gpr, e₁])
    (by rw [u₂.wr, u₁.wr]; exact sin (P.so + 4) (by omega)) fun s₃ u₃ => ?_
  refine wp_store (a := addr (scr s₀) (P.so + 8)) (by rw [ea_at, u₃.gpr, u₂.gpr, e₁])
    (by rw [u₃.wr, u₂.wr, u₁.wr]; exact sin (P.so + 8) (by omega)) fun s₄ u₄ => ?_
  refine wp_store (a := addr (scr s₀) (P.so + 12)) (by rw [ea_at, u₄.gpr, u₃.gpr, u₂.gpr, e₁])
    (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact sin (P.so + 12) (by omega)) fun s₅ u₅ => ?_
  have g₅ : s₅.gpr = s₁.gpr := by rw [u₅.gpr, u₄.gpr, u₃.gpr, u₂.gpr]
  have m₅ : s₅.mem = saveMem P s₀ := by
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
  refine wp_andi fun s₁₀ u₁₀ => WP.block_nil ?_
  have g : ∀ r, r ≠ .edi → r ≠ .esi → r ≠ .ebp → r ≠ .ebx → s₁₀.gpr r = s₅.gpr r := fun r h1 h2 h3 h4 => by
    rw [u₁₀.other r h1, u₉.other r h1, u₈.other r h2, u₇.other r h3, u₆.other r h4]
  have m₁₀ : s₁₀.mem = saveMem P s₀ := by rw [u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, m₅]
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
  have rd₁₀ : s₁₀.rd = s₀.rd := by rw [u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, rd₅]
  have wr₁₀ : s₁₀.wr = s₀.wr := by rw [u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, wr₅]
  refine ⟨⟨Nat.zero_le _, rd₁₀, wr₁₀, ebx₁₀, sp₁₀, by rw [ebp₁₀]; simp, ?_,
    by rw [m₁₀]; exact (saveMem_frame hd hp).mono (by simp), by rw [m₁₀]; exact saveMem_saved hd hp⟩,
    by rw [edi₁₀, Nat.add_zero], fun iv m hm => ?_⟩
  · rw [esi₁₀, Nat.sub_zero, len, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [List.take_zero, List.append_nil, m₁₀]
    exact H.repr_congr (by omega) (fun i hi => frame_bytes (saveMem_frame hd hp) (R := stR P s₀)
      (by simpa using hp.st_scr) (by simp; omega) hi) hm.1

theorem epilogue_ok (hd : Dims P S) {s₀ : State} (hp : Pre P S s₀) {s : State} (hI : Inv S H s₀ (len s₀) s) :
    WP isa (.block (.mov .eax (.mem (at_ .esp 24)) :: restore P .eax)) s fun s' =>
      abiPreserved s₀ s' ∧ (updK H S).post s₀ s' := by
  have := hd.so
  have rin : ∀ d, d + 4 ≤ S → InRegions (s.rd ++ s.wr) (addr (scr s₀) d) 4 :=
    fun d hd => ⟨scR S s₀, by simp [hI.rd, hI.wr, hp.wr], hp.scr_in hd⟩
  have ain : InRegions (s.rd ++ s.wr) (addr (esp₀ s₀) 24) 4 :=
    ⟨argR s₀, by simp [hI.rd, hp.rd], hp.arg_in (by omega) (by omega)⟩
  rw [restore_eq]
  refine wp_movm (a := addr (esp₀ s₀) 24) (by rw [ea_at, hI.esp]) ain fun s₁ u₁ => ?_
  have e₁ : s₁.gpr .eax = scr s₀ := by rw [u₁.gpr, hI.arg hp (by omega) (by omega)]; rfl
  refine wp_movm (a := addr (scr s₀) P.so) (by rw [ea_at, e₁]) (by rw [u₁.rd, u₁.wr]; exact rin P.so (by omega))
    fun s₂ u₂ => ?_
  refine wp_movm (a := addr (scr s₀) (P.so + 4)) (by rw [ea_at, u₂.other _ (by decide), e₁])
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact rin (P.so + 4) (by omega)) fun s₃ u₃ => ?_
  refine wp_movm (a := addr (scr s₀) (P.so + 8)) (by rw [ea_at, u₃.other _ (by decide), u₂.other _ (by decide), e₁])
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact rin (P.so + 8) (by omega)) fun s₄ u₄ => ?_
  refine wp_movm (a := addr (scr s₀) (P.so + 12))
    (by rw [ea_at, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), e₁])
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact rin (P.so + 12) (by omega))
    fun s₅ u₅ => WP.block_nil ?_
  have hm₅ : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  refine ⟨⟨fun r hr => ?_, ?_⟩, fun iv m hm hc => ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.mem]
      exact hI.saved (.ebx, P.so) (by simp [saved])
    · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.mem, u₁.mem]
      exact hI.saved (.esi, P.so + 4) (by simp [saved])
    · rw [u₅.other _ (by decide), u₄.gpr, u₃.mem, u₂.mem, u₁.mem]
      exact hI.saved (.edi, P.so + 8) (by simp [saved])
    · rw [u₅.gpr, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
      exact hI.saved (.ebp, P.so + 12) (by simp [saved])
    · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
        u₁.other _ (by decide), hI.esp]
  · rw [hm₅]
    refine hI.frame.readW (r := retR s₀) (Region.contains_self _ _) ?_ (by decide)
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [hp.ret_st, hp.ret_scr, hp.ret_stk]
  · have := hI.repr iv m ⟨hm, hc⟩
    rw [List.take_of_length_le (by rw [D_length])] at this
    show H.Repr iv s₅.mem (stA s₀) (m ++ D s₀)
    rw [hm₅]; exact this

/-! ## Consuming data -/

theorem D_getD (s₀ : State) {i : Nat} (hi : i < len s₀) :
    (D s₀).getD i 0 = s₀.mem (dA s₀ + BitVec.ofNat 64 i) := by
  simp [bytesAt, List.getD_eq_getElem?_getD, hi]

/-- The data is unchanged. -/
theorem Common.data {s₀ : State} (hp : Pre P S s₀) {c : Nat} {s : State} (h : Common P S s₀ c s) {i : Nat}
    (hi : i < len s₀) : s.mem (dA s₀ + BitVec.ofNat 64 i) = (D s₀).getD i 0 := by
  rw [D_getD s₀ hi]
  exact frame_bytes h.frame (R := dR s₀) (by simpa using ⟨hp.d_st, hp.d_scr, hp.stk_d.symm⟩)
    (by simp only; have := len_lt s₀; omega) hi

theorem length_mid (s₀ : State) {iv : H.HV} {m : List Byte} (hm : R₀ H s₀ iv m) {c : Nat} (hc : c ≤ len s₀) :
    (m ++ (D s₀).take c).length % 64 = (cnt s₀ + c) % 64 := by
  have := hm.length
  simp only [List.length_append, List.length_take, D_length, Nat.min_eq_left hc]
  omega

theorem take_add_data (s₀ : State) (c t : Nat) (m : List Byte) :
    m ++ (D s₀).take c ++ ((D s₀).drop c).take t = m ++ (D s₀).take (c + t) := by
  rw [List.take_add, List.append_assoc]

theorem ofNat_shr6 {a : Nat} (h : a < 2 ^ 32) : BitVec.ofNat 32 a >>> 6 = BitVec.ofNat 32 (a / 64) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega)]

/-- Every whole block left, straight from the data. -/
theorem direct_ok {s₀ : State} (hp : Pre P S s₀) {c : Nat} {s : State} (hI : Inv S H s₀ c s)
    (hr : (cnt s₀ + c) % 64 = 0) (hl : 64 ≤ len s₀ - c) :
    WP isa (.block direct) s (Pending S H s₀ (c + 64 * ((len s₀ - c) / 64)) ((len s₀ - c) / 64)) := by
  have hd := hp.d_fit; have hc := hI.c_le; have hlen := len_lt s₀
  generalize hq : (len s₀ - c) / 64 = q
  have hq1 : 1 ≤ q := by omega
  have hq2 : (len s₀ - c) - (len s₀ - c) % 64 = 64 * q := by omega
  unfold direct
  refine wp_mov fun s₁ u₁ => wp_mov fun s₂ u₂ => wp_andi fun s₃ u₃ => wp_mov fun s₄ u₄ =>
    wp_sub fun s₅ u₅ _ => wp_add fun s₆ u₆ => wp_mov fun s₇ u₇ => wp_mov fun s₈ u₈ =>
    wp_shr (by decide) fun s₉ u₉ => WP.block_nil ?_
  have g : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .ebp → r ≠ .esi → s₉.gpr r = s.gpr r :=
    fun r h1 h2 h3 h4 h5 => by
      rw [u₉.other r h2, u₈.other r h2, u₇.other r h5, u₆.other r h4, u₅.other r h3, u₄.other r h3,
        u₃.other r h2, u₂.other r h2, u₁.other r h1]
  have hm : s₉.mem = s.mem := by
    rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have heax : s₉.gpr .eax = dp s₀ + BitVec.ofNat 32 c := by
    rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr,
      hI.ebp]
  have h3 : s₃.gpr .ecx = BitVec.ofNat 32 ((len s₀ - c) % 64) := by
    rw [u₃.gpr, u₂.gpr, u₁.other _ (by decide), hI.esi, and63, toNat_ofNat_lt (by omega)]
  have h5 : s₅.gpr .edx = BitVec.ofNat 32 (64 * q) := by
    rw [u₅.gpr, u₄.gpr, u₄.other _ (by decide), h3, u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), hI.esi, sub_ofNat (by omega), hq2]
  have h6 : s₆.gpr .edx = BitVec.ofNat 32 (64 * q) := by rw [u₆.other _ (by decide), h5]
  refine ⟨⟨by omega, ?_, ?_,
      by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), hI.ebx],
      by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), hI.esp], ?_, ?_,
      by rw [hm]; exact hI.frame, by rw [hm]; exact hI.saved⟩,
    by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), hI.edi, hr]; rfl,
    ?_, hq1, by omega, .inr ⟨c, heax, by omega⟩, fun iv m hm₀ mem' hs => ?_⟩
  · rw [u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, hI.rd]
  · rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, hI.wr]
  · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, h5,
      u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), hI.ebp, ofNat_add_add]
  · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide),
      u₅.other _ (by decide), u₄.other _ (by decide), h3]
    congr 1; omega
  · rw [u₉.gpr, u₈.gpr, u₇.other _ (by decide), h6, ofNat_shr6 (by omega)]
    congr 1; omega
  · have hmod := length_mid s₀ hm₀ (c := c) (by omega)
    rw [← take_add_data]
    refine H.repr_append_blocks (n := q) (by omega) (hI.repr iv m hm₀) (by rw [hmod, hr])
      (by rw [List.length_take, List.length_drop, D_length]; omega) ?_
    rw [hs, hm, heax, show (dp s₀ + BitVec.ofNat 32 c).setWidth 64 = addr (dp s₀) c from rfl,
      addr_eq (by omega)]
    apply H.compressBlocks_eq
    intro j hj
    rw [show dA s₀ + BitVec.ofNat 64 c + BitVec.ofNat 64 j = dA s₀ + BitVec.ofNat 64 (c + j) by
      simp only [BitVec.ofNat_add]; rw [BitVec.add_assoc], hI.data hp (by omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_drop, hj]

/-! ## Compressing -/

theorem Pending.k_lt {s₀ : State} {c k : Nat} {s : State} (h : Pending S H s₀ c k s) : k < 2 ^ 32 := by
  have := len_lt s₀
  rcases h.src with ⟨_, rfl⟩ | ⟨c₀, _, hc₀⟩ <;> omega

/-- The blocks to compress. -/
theorem Pending.blk {s₀ : State} (hp : Pre P S s₀) {c k : Nat} {s : State} (h : Pending S H s₀ c k s) :
    (s.gpr .eax).toNat + 64 * k ≤ 2 ^ 32 ∧
      (((s.gpr .eax).setWidth 64 = stA s₀ + BitVec.ofNat 64 P.N ∧ k = 1) ∨
        ∃ c₀, (s.gpr .eax).setWidth 64 = dA s₀ + BitVec.ofNat 64 c₀ ∧ c₀ + 64 * k ≤ len s₀) := by
  have hst := hp.st_fit; have hd := hp.d_fit; have := h.k_pos
  rcases h.src with ⟨h', rfl⟩ | ⟨c₀, h', hc₀⟩
  · refine ⟨by rw [h', BitVec.toNat_add, toNat_ofNat_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega,
      .inl ⟨?_, rfl⟩⟩
    rw [h']; exact addr_eq (by omega)
  · refine ⟨by rw [h', BitVec.toNat_add, toNat_ofNat_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega,
      .inr ⟨c₀, ?_, hc₀⟩⟩
    rw [h']; exact addr_eq (by omega)

/-- The blocks lie in the state or in the data. -/
theorem Pending.blk_sub {s₀ : State} (hp : Pre P S s₀) {c k : Nat} {s : State} (h : Pending S H s₀ c k s) :
    Region.Sub ⟨(s.gpr .eax).setWidth 64, 64 * k⟩ (stR P s₀) ∨
      Region.Sub ⟨(s.gpr .eax).setWidth 64, 64 * k⟩ (dR s₀) := by
  rcases (h.blk hp).2 with ⟨he, rfl⟩ | ⟨c₀, he, hc₀⟩
  · exact .inl (by rw [he]; exact sub_offset (by omega) (by have := hp.st_fit; omega))
  · exact .inr (by rw [he]; exact sub_offset hc₀ (by have := len_lt s₀; omega))

/-- The call of the compression function, once `edx` holds `scratch`. -/
theorem Pending.compress_ok (hd : Dims P S) {name : String} {code : Prog isa} (hf : CalleeOk H code)
    {s₀ : State} (hp : Pre P S s₀) {c k : Nat} {s s₁ : State} (h : Pending S H s₀ c k s)
    (u : Upd s s₁ .edx (scr s₀)) : WP isa (compressN name code .ebx .edx) s₁ (Inv S H s₀ c) := by
  have hst := hp.st_fit; have hsc := hp.scr_fit; have := hd.so; have := hd.N
  obtain ⟨hbf, hb⟩ := h.blk hp
  have hbs := h.blk_sub hp
  have eN : Region.Sub ⟨stA s₀, P.N⟩ (stR P s₀) := Region.sub_prefix (by omega)
  have eso : Region.Sub ⟨scA s₀, P.so⟩ (scR S s₀) := Region.sub_prefix (by omega)
  have hk : (s₁.gpr .ecx).toNat = k := by rw [u.other _ (by decide), h.ecx, toNat_ofNat_lt h.k_lt]
  unfold compressN compressWith
  refine WP.seq (WP.block_nil ?_)
  refine compressFrame_ok hf (st := st s₀) (scr := scr s₀) (blk := s.gpr .eax) (E := esp₀ s₀)
    (by decide) (by decide) (by rw [u.other _ (by decide), h.esp])
    (by rw [u.other _ (by decide), h.ebx]) u.gpr (u.other _ (by decide)) hk hp.sp_lo (by omega) hbf (by omega)
    ((hp.st_scr.sub_left eN).sub_right eso) ?_ ?_ (hp.stk_st.sub_right eN) (hp.stk_scr.sub_right eso)
    ?_ ?_ ?_ ?_
  · rcases hb with ⟨he, rfl⟩ | ⟨c₀, he, hc₀⟩
    · rw [he]; exact Offset.disjoint_base _ (Nat.le_refl _) (by omega)
    · exact (hp.d_st.sub_left (by rw [he]; exact sub_offset hc₀ (by have := len_lt s₀; omega))).sub_right eN
  · rcases hbs with hsub | hsub
    · exact (hp.st_scr.sub_left hsub).sub_right eso
    · exact (hp.d_scr.sub_left hsub).sub_right eso
  · rcases hbs with hsub | hsub
    · exact hp.stk_st.sub_right hsub
    · exact hp.stk_d.sub_right hsub
  · rw [u.rd, u.wr, h.rd, h.wr, hp.rd, hp.wr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    rcases hb with ⟨he, rfl⟩ | ⟨c₀, he, hc₀⟩
    · exact ⟨stR P s₀, by simp, P.N, he, by simp⟩
    · exact ⟨dR s₀, by simp, c₀, he, hc₀⟩
  · rw [u.wr, h.wr, hp.wr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨stR P s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨scR S s₀, by simp, 0, by simp, by simp; omega⟩
  · intro s' hrd hwr hcs hf hstate
    have cs : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r := fun r hr => by
      rw [hcs r hr, u.other r (by simp [calleeSaved] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)]
    rw [u.mem] at hf hstate
    refine ⟨⟨h.c_le, by rw [hrd, u.rd, h.rd], by rw [hwr, u.wr, h.wr], by rw [cs _ (by decide)]; exact h.ebx,
      by rw [cs _ (by decide)]; exact h.esp, by rw [cs _ (by decide)]; exact h.ebp,
      by rw [cs _ (by decide)]; exact h.esi, h.frame.trans (hf.sub ?_), fun p hp' => ?_⟩,
      by rw [cs _ (by decide), h.edi, h.mod]; rfl, fun iv m hm => h.repr iv m hm _ hstate⟩
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨stR P s₀, by simp, eN⟩
      · exact ⟨scR S s₀, by simp, eso⟩
      · exact ⟨stkR s₀, by simp, fun _ h => h⟩
    · have hd' := saved_offset hp'
      rw [hf.readW (r := ⟨addr (scr s₀) p.2, 4⟩) (Region.contains_self _ _) ?_ (by decide)]
      · exact h.saved p hp'
      · intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact (hp.st_scr.symm.sub_left (hp.scr_sub (by omega))).sub_right eN
        · rw [addr_eq (by omega)]; exact Offset.disjoint_base _ (by omega) (by omega)
        · exact hp.stk_scr.symm.sub_left (hp.scr_sub (by omega))

theorem Pending.congr {s₀ : State} {c k : Nat} {s s' : State} (h : Pending S H s₀ c k s) (hg : s'.gpr = s.gpr)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Pending S H s₀ c k s' :=
  { h.toCommon.of_gpr (fun r _ => by rw [hg]) hm hrd hwr with
    edi := by rw [hg]; exact h.edi
    ecx := by rw [hg]; exact h.ecx
    k_pos := h.k_pos
    mod := h.mod
    src := by rw [hg]; exact h.src
    repr := by rw [hm, hg]; exact h.repr }

end

/-- The loop's postcondition for one iteration from `c` bytes. -/
def Step {P : Params} (S : Nat) (H : Md 64 P.N 8) (s₀ : State) (c : Nat) (s : State) : Prop :=
  (eval .ne s = some false ∧ Inv S H s₀ (len s₀) s) ∨ (eval .ne s = some true ∧ ∃ c', c < c' ∧ Inv S H s₀ c' s)

section
variable {P : Params} {S : Nat} {H : Md 64 P.N 8}

/-- The second half of the loop body: compress if a block is ready, and loop
back if so. -/
theorem tail_ok (hd : Dims P S) {name : String} {code : Prog isa} (hf : CalleeOk H code) {s₀ : State}
    (hp : Pre P S s₀) {c : Nat} {s : State}
    (h : (∃ c' k, c < c' ∧ Pending S H s₀ c' k s) ∨ Done S H s₀ s) :
    WP isa (.seq (.block [.alu .test .ecx (.reg .ecx)])
      (.ite .ne (.seq (.block [.mov .edx (.mem (at_ .esp 24))])
          (.seq (compressN name code .ebx .edx) (.block [.mov .ecx (.imm 1), .alu .test .ecx (.reg .ecx)])))
        (.block []))) s (Step S H s₀ c) := by
  rcases h with ⟨c', k, hc, hP⟩ | ⟨hI, hecx⟩
  · refine WP.seq (wp_test fun s₂ f₂ z₂ => WP.block_nil ?_)
    have hP₂ : Pending S H s₀ c' k s₂ := hP.congr f₂.gpr f₂.mem f₂.rd f₂.wr
    have hz : s₂.zf = some false := by
      rw [z₂, hP.ecx, BitVec.and_self, ofNat_beq_zero hP.k_lt, decide_eq_false (Nat.pos_iff_ne_zero.mp hP.k_pos)]
    refine WP.ite true (by show s₂.zf.map (!·) = _; rw [hz]; rfl) (fun _ => ?_) (fun h => by cases h)
    refine WP.seq (wp_movm (a := addr (esp₀ s₀) 24) (by rw [ea_at, hP₂.esp])
      ⟨argR s₀, by simp [hP₂.rd, hp.rd], hp.arg_in (by omega) (by omega)⟩ fun s₃ u₃ => WP.block_nil ?_)
    have u₃' : Upd s₂ s₃ .edx (scr s₀) :=
      ⟨by rw [u₃.gpr, hP₂.toCommon.arg hp (by omega) (by omega)]; rfl, u₃.other, u₃.mem, u₃.rd, u₃.wr⟩
    refine WP.seq (WP.mono (hP₂.compress_ok hd hf hp u₃') fun s₄ hI₄ => ?_)
    refine wp_movi fun s₅ u₅ => wp_test fun s₆ f₆ z₆ => WP.block_nil ?_
    have hz₆ : s₆.zf = some false := by rw [z₆, u₅.gpr]; rfl
    refine .inr ⟨by rw [eval_ne, hz₆]; rfl, c', hc, hI₄.of_gpr (fun r hr => ?_) (by rw [f₆.mem, u₅.mem])
      (by rw [f₆.rd, u₅.rd]) (by rw [f₆.wr, u₅.wr])⟩
    rw [f₆.gpr, u₅.other r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)]
  · refine WP.seq (wp_test fun s₂ f₂ z₂ => WP.block_nil ?_)
    have hz : s₂.zf = some true := by rw [z₂, hecx]; rfl
    refine WP.ite false (by show s₂.zf.map (!·) = _; rw [hz]; rfl) (fun h => by cases h) (fun _ => WP.block_nil ?_)
    exact .inl ⟨by rw [eval_ne, hz]; rfl, hI.of_gpr (fun r _ => by rw [f₂.gpr]) f₂.mem f₂.rd f₂.wr⟩

end

/-! ## Buffering data -/

section
variable (P : Params) (s₀ : State) (c : Nat)
/-- Bytes in the buffer before this iteration. -/
abbrev rr : Nat := (cnt s₀ + c) % 64
/-- Bytes copied into the buffer in this iteration. -/
abbrev tt : Nat := min (64 - rr s₀ c) (len s₀ - c)
/-- Where they go. -/
abbrev q : Addr := stA s₀ + BitVec.ofNat 64 (P.N + rr s₀ c)
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
structure Copy (P : Params) (s₀ : State) (c : Nat) (mI : Mem) (j : Nat) (s : State) : Prop where
  j_le : j ≤ tt s₀ c
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  ebx : s.gpr .ebx = st s₀
  esp : s.gpr .esp = esp₀ s₀
  ebp : s.gpr .ebp = dp s₀ + BitVec.ofNat 32 (c + j)
  esi : s.gpr .esi = BitVec.ofNat 32 (len s₀ - c - tt s₀ c)
  edi : s.gpr .edi = st s₀ + BitVec.ofNat 32 (rr s₀ c + j)
  eax : s.gpr .eax = BitVec.ofNat 32 (tt s₀ c - j)
  mem : s.mem = writeBytes mI (q P s₀ c) ((xs s₀ c).take j)

section
variable {P : Params} {S : Nat} {H : Md 64 P.N 8}

theorem write_frame (hd : Dims P S) {s₀ : State} (hp : Pre P S s₀) (c : Nat) (mI : Mem) (j : Nat)
    (hj : j ≤ tt s₀ c) : Frame [stR P s₀] mI (writeBytes mI (q P s₀ c) ((xs s₀ c).take j)) := by
  have := tt_le' s₀ c; have := rr_lt s₀ c; have := hp.st_fit; have := hd.N
  refine writeBytes_frame _ _ _ ?_
  simp only [q]
  exact contains_offset (by simp only [List.length_take]; omega) (by omega)

theorem copy_step (hd : Dims P S) {s₀ : State} (hp : Pre P S s₀) {c : Nat} {sI : State} (hI : Inv S H s₀ c sI)
    {j : Nat} (hj : j < tt s₀ c) {s : State} (h : Copy P s₀ c sI.mem j s) :
    WP isa (.block [.movzx8 .ecx (at_ .ebp 0), .store8 (at_ .edi P.N) .cl,
      .alu .add .ebp (.imm 1), .alu .add .edi (.imm 1), .alu .sub .eax (.imm 1)]) s fun s' =>
      Copy P s₀ c sI.mem (j + 1) s' ∧ s'.zf = some (decide (tt s₀ c - (j + 1) = 0)) := by
  have hdf := hp.d_fit; have hst := hp.st_fit; have := hd.N
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
    exact frame_bytes (write_frame hd hp c sI.mem j h.j_le) (R := dR s₀) (by simpa using hp.d_st)
      (by show len s₀ ≤ 2 ^ 64; omega) (by show c + j < len s₀; omega)
  -- The byte written.
  have ea₂ : ∀ t : State, t.gpr .edi = st s₀ + BitVec.ofNat 32 (rr s₀ c + j) →
      t.ea (at_ .edi P.N) = q P s₀ c + BitVec.ofNat 64 j := by
    intro t ht
    rw [ea_at, ht, addr_add_ofNat (by omega), q, BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2; omega
  have hout : InRegions s.wr (q P s₀ c + BitVec.ofNat 64 j) 1 :=
    ⟨stR P s₀, by simp [h.wr, hp.wr], by
      simp only [q]; rw [BitVec.add_assoc, ← BitVec.ofNat_add]; exact contains_offset (by omega) (by omega)⟩
  have hxs := xs_length s₀ c
  refine wp_movzx8 (d := .ecx) ea₁ hin fun s₁ u₁ => ?_
  refine wp_store8 (r := .cl) (a := q P s₀ c + BitVec.ofNat 64 j)
    (ea₂ s₁ (by rw [u₁.other _ (by decide), h.edi])) (by rw [u₁.wr]; exact hout) fun s₂ u₂ => ?_
  refine wp_addi fun s₃ u₃ => wp_addi fun s₄ u₄ => wp_subi fun s₅ u₅ hz₅ => WP.block_nil ?_
  have g : ∀ r, r ≠ .eax → r ≠ .edi → r ≠ .ebp → r ≠ .ecx → s₅.gpr r = s.gpr r := fun r h1 h2 h3 h4 => by
    rw [u₅.other r h1, u₄.other r h2, u₃.other r h3, u₂.gpr, u₁.other r h4]
  have hrax : s₅.gpr .eax = BitVec.ofNat 32 (tt s₀ c - (j + 1)) := by
    rw [u₅.gpr, u₄.other .eax (by decide), u₃.other .eax (by decide), u₂.gpr, u₁.other .eax (by decide), h.eax,
      ofNat_pred (by omega), Nat.sub_sub]
  refine ⟨⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hrax, ?_⟩, ?_⟩
  · rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd]
  · rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr]
  · rw [g .ebx (by decide) (by decide) (by decide) (by decide), h.ebx]
  · rw [g .esp (by decide) (by decide) (by decide) (by decide), h.esp]
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
    have hl : (List.take j (xs s₀ c)).length = j := by rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj')]
    rw [hl]
    congr 1
    simp only [xs, List.getElem_take, List.getElem_drop, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (show c + j < (D s₀).length by rw [D_length]; omega), Option.getD_some]
  · rw [hz₅, u₄.other .eax (by decide), u₃.other .eax (by decide), u₂.gpr, u₁.other .eax (by decide), h.eax,
      ofNat_pred (by omega), ofNat_beq_zero (by omega), show tt s₀ c - j - 1 = tt s₀ c - (j + 1) by omega]

theorem copy_loop_ok (hd : Dims P S) {s₀ : State} (hp : Pre P S s₀) {c : Nat} {sI : State} (hI : Inv S H s₀ c sI)
    {s : State} (h : Copy P s₀ c sI.mem 0 s) (ht : 0 < tt s₀ c) :
    WP isa (.loop (.block [.movzx8 .ecx (at_ .ebp 0), .store8 (at_ .edi P.N) .cl,
      .alu .add .ebp (.imm 1), .alu .add .edi (.imm 1), .alu .sub .eax (.imm 1)]) .ne) s
      (Copy P s₀ c sI.mem (tt s₀ c)) := by
  refine WP.loop (M := isa) (fun n s => ∃ j, n = tt s₀ c - j ∧ j < tt s₀ c ∧ Copy P s₀ c sI.mem j s)
    ?_ (tt s₀ c) s ⟨0, rfl, ht, h⟩
  rintro n s ⟨j, rfl, hj, hc⟩
  refine WP.mono (copy_step hd hp hI hj hc) fun s' ⟨hc', hz⟩ => ?_
  by_cases hl : tt s₀ c - (j + 1) = 0
  · refine .inl ⟨by show s'.zf.map (!·) = _; rw [hz]; simp [hl], ?_⟩
    rwa [show j + 1 = tt s₀ c by omega] at hc'
  · exact .inr ⟨by show s'.zf.map (!·) = _; rw [hz]; simp [hl], _, by omega, j + 1, rfl, by omega, hc'⟩

/-- The memory after copying `tt` bytes. -/
theorem copied_facts (hd : Dims P S) {s₀ : State} (hp : Pre P S s₀) {c : Nat} {sI : State} (hI : Inv S H s₀ c sI) :
    let mem := writeBytes sI.mem (q P s₀ c) (xs s₀ c)
    Frame [stR P s₀, scR S s₀, stkR s₀] s₀.mem mem ∧ Saved P s₀ mem ∧
      H.stateAt mem (stA s₀) = H.stateAt sI.mem (stA s₀) ∧
      bytesAt mem (buf P s₀) (rr s₀ c + tt s₀ c) = bytesAt sI.mem (buf P s₀) (rr s₀ c) ++ xs s₀ c := by
  intro mem
  have hr := rr_lt s₀ c; have ht' := tt_le' s₀ c; have := hd.N; have := hd.so; have := hd.S
  have hxs := xs_length s₀ c
  have hf : Frame [stR P s₀] sI.mem mem := by
    have := write_frame hd hp c sI.mem (tt s₀ c) (Nat.le_refl _)
    rwa [List.take_of_length_le (by omega)] at this
  have word : ∀ (R : Region), R.Disjoint (stR P s₀) → R.Contains R.base 4 →
      mem.readW R.base 32 = sI.mem.readW R.base 32 := fun R hR hc =>
    hf.readW hc (by simpa using hR) (by decide)
  refine ⟨hI.frame.trans (hf.mono (by simp)), fun p hp' => ?_, ?_, ?_⟩
  · have hd' := saved_offset hp'
    rw [word ⟨addr (scr s₀) p.2, 4⟩ (hp.st_scr.symm.sub_left (hp.scr_sub (by omega))) (Region.contains_self _ _)]
    exact hI.saved p hp'
  · apply H.stateAt_congr
    intro i hi
    exact writeBytes_before _ _ _ (by omega) (by omega)
  · show bytesAt (writeBytes sI.mem (q P s₀ c) (xs s₀ c)) (buf P s₀) (rr s₀ c + tt s₀ c) = _
    rw [← hxs, show q P s₀ c = buf P s₀ + BitVec.ofNat 64 (rr s₀ c) by
      simp only [q, buf]; rw [add_ofNat]]
    exact bytesAt_writeBytes _ _ _ _ (by omega)

/-- The state after copying, whatever `edi`, `eax` and `ecx` hold. -/
structure Copied (P : Params) (s₀ : State) (c : Nat) (mI : Mem) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  ebx : s.gpr .ebx = st s₀
  esp : s.gpr .esp = esp₀ s₀
  ebp : s.gpr .ebp = dp s₀ + BitVec.ofNat 32 (c + tt s₀ c)
  esi : s.gpr .esi = BitVec.ofNat 32 (len s₀ - c - tt s₀ c)
  mem : s.mem = writeBytes mI (q P s₀ c) (xs s₀ c)

theorem Copy.copied {s₀ : State} {c : Nat} {mI : Mem} {s : State} (h : Copy P s₀ c mI (tt s₀ c) s) :
    Copied P s₀ c mI s :=
  ⟨h.rd, h.wr, h.ebx, h.esp, h.ebp, h.esi,
    by rw [h.mem, List.take_of_length_le (by rw [xs_length])]⟩

theorem Copied.of_gpr {s₀ : State} {c : Nat} {mI : Mem} {s s' : State} (h : Copied P s₀ c mI s)
    (hg : ∀ r ∈ [Reg.ebx, .esp, .ebp, .esi], s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Copied P s₀ c mI s' :=
  ⟨hrd.trans h.rd, hwr.trans h.wr, by rw [hg _ (by simp)]; exact h.ebx, by rw [hg _ (by simp)]; exact h.esp,
    by rw [hg _ (by simp)]; exact h.ebp,
    by rw [hg _ (by simp)]; exact h.esi, hm.trans h.mem⟩

/-- A full buffer: compress it. -/
theorem fill_pending (hd : Dims P S) {s₀ : State} (hp : Pre P S s₀) {c : Nat} {sI : State} (hI : Inv S H s₀ c sI)
    {s : State} (h : Copied P s₀ c sI.mem s) (hfull : rr s₀ c + tt s₀ c = 64) :
    WP isa (.block [.mov .eax (.reg .ebx), .alu .add .eax (.imm (BitVec.ofNat 32 P.N)), .mov .edi (.imm 0),
      .mov .ecx (.imm 1)]) s (Pending S H s₀ (c + tt s₀ c) 1) := by
  have ht := tt_le s₀ c; have hrr := rr_eq s₀ c
  have hxs := xs_length s₀ c
  have hc := hI.c_le; have := hd.N
  obtain ⟨hfr, hsv, hst, hby⟩ := copied_facts hd hp hI
  refine wp_mov fun s₁ u₁ => wp_addi fun s₂ u₂ => wp_movi fun s₃ u₃ => wp_movi fun s₄ u₄ => WP.block_nil ?_
  have g : ∀ r, r ≠ .eax → r ≠ .edi → r ≠ .ecx → s₄.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [u₄.other r h3, u₃.other r h2, u₂.other r h1, u₁.other r h1]
  have m₄ : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have heax : s₄.gpr .eax = st s₀ + BitVec.ofNat 32 P.N := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.gpr, h.ebx]
  refine ⟨⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, by rw [m₄, h.mem]; exact hfr, by rw [m₄, h.mem]; exact hsv⟩,
    by rw [u₄.other _ (by decide), u₃.gpr], by rw [u₄.gpr]; rfl, Nat.one_pos, by omega, .inl ⟨heax, rfl⟩, ?_⟩
  · rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd]
  · rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr]
  · rw [g .ebx (by decide) (by decide) (by decide), h.ebx]
  · rw [g .esp (by decide) (by decide) (by decide), h.esp]
  · rw [g .ebp (by decide) (by decide) (by decide), h.ebp]
  · rw [g .esi (by decide) (by decide) (by decide), h.esi, Nat.sub_sub]
  · intro iv m hm mem' hs
    rw [Md.compressBlocks_one] at hs
    rw [← take_add_data]
    have hmod := length_mid s₀ hm hc
    refine H.repr_append_block (by omega) (hI.repr iv m hm) (by rw [hmod, hxs]; exact hfull) ?_
    rw [hs, m₄, h.mem, hst, heax, show (st s₀ + BitVec.ofNat 32 P.N).setWidth 64 = addr (st s₀) P.N from rfl,
      addr_eq (by have := hp.st_fit; omega)]
    refine congrArg (H.compress _) ?_
    apply H.parse_congr
    intro k hk
    have hb := (hI.repr iv m hm).2
    rw [hmod] at hb
    rw [hb, show rr s₀ c + tt s₀ c = 64 from hfull] at hby
    exact bytesAt_getD hby hk

/-- All the data fits in the buffer. -/
theorem fill_done (hd : Dims P S) {s₀ : State} (hp : Pre P S s₀) {c : Nat} {sI : State} (hI : Inv S H s₀ c sI)
    {s : State} (h : Copied P s₀ c sI.mem s) (hedi : s.gpr .edi = BitVec.ofNat 32 (rr s₀ c + tt s₀ c))
    (hecx : s.gpr .ecx = 0) (hnf : rr s₀ c + tt s₀ c ≠ 64) : Done S H s₀ s := by
  have hr := rr_lt s₀ c; have ht' := tt_le' s₀ c
  have hrr := rr_eq s₀ c; have htt := tt_eq s₀ c
  have hxs := xs_length s₀ c
  have hc := hI.c_le
  have htl : tt s₀ c = len s₀ - c := by omega
  obtain ⟨hfr, hsv, hst, hby⟩ := copied_facts hd hp hI
  refine ⟨⟨⟨(Nat.le_refl _), h.rd, h.wr, h.ebx, h.esp, ?_, ?_, by rw [h.mem]; exact hfr,
    by rw [h.mem]; exact hsv⟩, ?_, fun iv m hm => ?_⟩, hecx⟩
  · rw [h.ebp]; congr 2; omega_using [htl, hc]
  · rw [h.esi]; congr 1; omega_using [htl]
  · rw [hedi]; congr 1; omega_using [htl, hc, hrr, hr, ht', hnf]
  · have hmod := length_mid s₀ hm hc
    rw [show len s₀ = c + tt s₀ c by omega_using [htl, hc], ← take_add_data]
    refine H.repr_append_buf (hI.repr iv m hm) (by rw [hmod, hxs]; omega) (by rw [h.mem, hst]) ?_
    rw [hmod, hxs, h.mem, hby]
    have hb := (hI.repr iv m hm).2
    rw [hmod] at hb
    rw [hb]

theorem fill_ok (hd : Dims P S) {s₀ : State} (hp : Pre P S s₀) {c : Nat} {s : State} (hI : Inv S H s₀ c s) :
    WP isa (fill P) s fun s' => (∃ c' k, c < c' ∧ Pending S H s₀ c' k s') ∨ Done S H s₀ s' := by
  have hr := rr_lt s₀ c; have ht' := tt_le' s₀ c
  have htt := tt_eq s₀ c
  have hlen := len_lt s₀
  unfold fill
  -- `eax := 64 - edi; cmp esi, eax`
  refine WP.seq (wp_movi fun s₂ u₂ => wp_sub fun s₃ u₃ _ => wp_cmp fun s₄ f₄ cf₄ _ => WP.block_nil ?_)
  have e₄ : ∀ r, r ≠ .eax → s₄.gpr r = s.gpr r := fun r h => by
    rw [f₄.gpr, u₃.other r h, u₂.other r h]
  have hm₄ : s₄.mem = s.mem := by rw [f₄.mem, u₃.mem, u₂.mem]
  have hrd₄ : s₄.rd = s.rd := by rw [f₄.rd, u₃.rd, u₂.rd]
  have hwr₄ : s₄.wr = s.wr := by rw [f₄.wr, u₃.wr, u₂.wr]
  have heax₃ : s₃.gpr .eax = BitVec.ofNat 32 (64 - rr s₀ c) := by
    rw [u₃.gpr, u₂.gpr, u₂.other _ (by decide), hI.edi, ← rr_eq, lit32,
      sub_ofNat (a := 64) (b := rr s₀ c) (by omega)]
  have hcf : s₄.cf = some (decide (len s₀ - c < 64 - rr s₀ c)) := by
    rw [cf₄, heax₃, u₃.other _ (by decide), u₂.other _ (by decide), hI.esi,
      toNat_ofNat_lt (by omega), toNat_ofNat_lt (by omega)]
  -- `eax := min(eax, esi)`
  refine WP.seq (WP.mono (Q := fun (s₅ : State) => s₅.gpr .eax = BitVec.ofNat 32 (tt s₀ c) ∧
    (∀ r, r ≠ .eax → s₅.gpr r = s₄.gpr r) ∧ s₅.mem = s₄.mem ∧ s₅.rd = s₄.rd ∧ s₅.wr = s₄.wr) ?_
    fun s₅ ⟨heax₅, g₅, m₅, rd₅, wr₅⟩ => ?_)
  · refine WP.ite (decide (len s₀ - c < 64 - rr s₀ c)) (by show s₄.cf = _; rw [hcf]) (fun hb => ?_) (fun hb => ?_)
    · refine wp_mov fun s₅ u₅ => WP.block_nil ⟨?_, u₅.other, u₅.mem, u₅.rd, u₅.wr⟩
      rw [u₅.gpr, e₄ _ (by decide), hI.esi]; congr 1; simp at hb; omega
    · refine WP.block_nil ⟨?_, fun _ _ => rfl, rfl, rfl, rfl⟩
      rw [f₄.gpr, heax₃]; congr 1; simp at hb; omega
  -- `esi -= eax; edi += ebx; test eax, eax`
  refine WP.seq (wp_sub fun s₆ u₆ _ => wp_add fun s₇ u₇ => wp_test fun s₈ f₈ z₈ => WP.block_nil ?_)
  have g₈ : ∀ r, r ≠ .esi → r ≠ .edi → r ≠ .eax → s₈.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [f₈.gpr, u₇.other r h2, u₆.other r h1, g₅ r h3, e₄ r h3]
  have hm₈ : s₈.mem = s.mem := by rw [f₈.mem, u₇.mem, u₆.mem, m₅, hm₄]
  have hC₀ : Copy P s₀ c s.mem 0 s₈ := by
    refine ⟨Nat.zero_le _, by rw [f₈.rd, u₇.rd, u₆.rd, rd₅, hrd₄, hI.rd], by rw [f₈.wr, u₇.wr, u₆.wr, wr₅, hwr₄, hI.wr],
      by rw [g₈ _ (by decide) (by decide) (by decide), hI.ebx],
      by rw [g₈ _ (by decide) (by decide) (by decide), hI.esp],
      by rw [g₈ _ (by decide) (by decide) (by decide), hI.ebp, Nat.add_zero], ?_, ?_, ?_,
      by rw [hm₈, List.take_zero, writeBytes_nil]⟩
    · rw [f₈.gpr, u₇.other _ (by decide), u₆.gpr, g₅ _ (by decide), e₄ _ (by decide), hI.esi,
        heax₅, sub_ofNat (by omega)]
    · rw [f₈.gpr, u₇.gpr, u₆.other _ (by decide), g₅ _ (by decide), e₄ _ (by decide), hI.edi,
        u₆.other _ (by decide), g₅ _ (by decide), e₄ _ (by decide), hI.ebx, BitVec.add_comm,
        ← rr_eq, Nat.add_zero]
    · rw [f₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), heax₅, Nat.sub_zero]
  have hz₈ : s₈.zf = some (decide (tt s₀ c = 0)) := by
    rw [z₈, u₇.other _ (by decide), u₆.other _ (by decide), heax₅, BitVec.and_self, ofNat_beq_zero (by omega)]
  -- Copy the bytes.
  refine WP.seq (WP.mono (Q := Copy P s₀ c s.mem (tt s₀ c)) ?_ fun s₉ hC => ?_)
  · refine WP.ite (decide (tt s₀ c = 0)) (by show s₈.zf = _; rw [hz₈]) (fun hb => ?_) (fun hb => ?_)
    · simp only [decide_eq_true_eq] at hb
      exact WP.block_nil (hb ▸ hC₀)
    · simp only [decide_eq_false_iff_not] at hb
      exact copy_loop_ok hd hp hI hC₀ (by omega)
  -- Is the buffer full?
  refine WP.seq (wp_sub fun s₁₀ u₁₀ _ => wp_movi fun s₁₁ u₁₁ => wp_cmpi fun s₁₂ f₁₂ _ z₁₂ => WP.block_nil ?_)
  have hC₁₂ : Copied P s₀ c s.mem s₁₂ :=
    hC.copied.of_gpr (fun r hr => by
      rw [f₁₂.gpr, u₁₁.other r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide),
        u₁₀.other r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide)])
      (by rw [f₁₂.mem, u₁₁.mem, u₁₀.mem]) (by rw [f₁₂.rd, u₁₁.rd, u₁₀.rd]) (by rw [f₁₂.wr, u₁₁.wr, u₁₀.wr])
  have hedi₁₂ : s₁₂.gpr .edi = BitVec.ofNat 32 (rr s₀ c + tt s₀ c) := by
    rw [f₁₂.gpr, u₁₁.other _ (by decide), u₁₀.gpr, hC.edi, hC.ebx, BitVec.add_comm, BitVec.add_sub_cancel]
  have hz₁₂ : s₁₂.zf = some (decide (rr s₀ c + tt s₀ c = 64)) := by
    rw [z₁₂, ← f₁₂.gpr, hedi₁₂, lit32, sub_beq (a := rr s₀ c + tt s₀ c) (b := 64) (by omega) (by omega)]
  have hecx : s₁₂.gpr .ecx = 0 := by rw [f₁₂.gpr, u₁₁.gpr]
  refine WP.ite (decide (rr s₀ c + tt s₀ c = 64)) (by show s₁₂.zf = _; rw [hz₁₂]) (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    exact WP.mono (fill_pending hd hp hI hC₁₂ hb) fun s' h => .inl ⟨c + tt s₀ c, 1, by omega, h⟩
  · simp only [decide_eq_false_iff_not] at hb
    exact WP.block_nil (.inr (fill_done hd hp hI hC₁₂ hedi₁₂ hecx hb))

theorem body_ok (hd : Dims P S) {name : String} {code : Prog isa} (hf : CalleeOk H code) {s₀ : State}
    (hp : Pre P S s₀) {c : Nat} {s : State} (hI : Inv S H s₀ c s) :
    WP isa (updateBody P name code) s (Step S H s₀ c) := by
  have hlen := len_lt s₀; have hr := rr_lt s₀ c
  unfold updateBody
  refine WP.seq (wp_test fun s₁ f₁ z₁ => WP.block_nil ?_)
  have hI₁ := hI.of_gpr (fun r _ => by rw [f₁.gpr]) f₁.mem f₁.rd f₁.wr
  refine WP.seq (WP.mono (Q := fun s' => (∃ c' k, c < c' ∧ Pending S H s₀ c' k s') ∨ Done S H s₀ s') ?_
    fun s' h => tail_ok hd hf hp h)
  refine WP.ite (decide (rr s₀ c = 0))
    (by show s₁.zf = _; rw [z₁, hI.edi, BitVec.and_self, ofNat_beq_zero (by omega)])
    (fun hb => ?_) (fun _ => fill_ok hd hp hI₁)
  simp only [decide_eq_true_eq] at hb
  refine WP.seq (wp_cmpi fun s₂ f₂ cf₂ _ => WP.block_nil ?_)
  have hI₂ := hI₁.of_gpr (fun r _ => by rw [f₂.gpr]) f₂.mem f₂.rd f₂.wr
  have hcf : s₂.cf = some (decide (len s₀ - c < 64)) := by
    rw [cf₂, hI₁.esi, toNat_ofNat_lt (by omega)]; rfl
  refine WP.ite (!decide (len s₀ - c < 64)) (by show s₂.cf.map (!·) = _; rw [hcf]; rfl)
    (fun hb' => ?_) (fun _ => fill_ok hd hp hI₂)
  simp only [Bool.not_eq_true', decide_eq_false_iff_not, Nat.not_lt] at hb'
  exact WP.mono (direct_ok hp hI₂ hb hb') fun s' h => .inl ⟨_, _, by omega, h⟩

theorem correct (hd : Dims P S) {name : String} {code : Prog isa} (hf : CalleeOk H code) {s₀ : State}
    (hp : Pre P S s₀) :
    WP isa (update P name code) s₀ fun s' => abiPreserved s₀ s' ∧ (updK H S).post s₀ s' := by
  unfold update
  refine WP.seq (WP.mono (prologue_ok (H := H) hd hp) fun s₁ hI => ?_)
  refine WP.seq (WP.mono (Q := Inv S H s₀ (len s₀)) ?_ fun s₂ hI₂ => epilogue_ok hd hp hI₂)
  refine WP.loop (M := isa) (fun n s => ∃ c, n = len s₀ - c ∧ Inv S H s₀ c s) ?_ (len s₀) s₁ ⟨0, rfl, hI⟩
  rintro n s ⟨c, rfl, hI⟩
  refine WP.mono (body_ok hd hf hp hI) fun s' h => ?_
  rcases h with ⟨he, hI'⟩ | ⟨he, c', hc, hI'⟩
  · exact .inl ⟨he, hI'⟩
  · exact .inr ⟨he, len s₀ - c', by have := hI'.c_le; omega, c', rfl, hI'⟩

end

/-! ## Constant time -/

theorem argWord_eq {s : State} {n : Nat} (hsp : (s.gpr .esp).toNat + 4 + n ≤ 2 ^ 32) {k : Nat} (hk : k < n) :
    addr (s.gpr .esp) 4 + BitVec.ofNat 64 k = argAddr s (k / 4) + BitVec.ofNat 64 (k % 4) := by
  simp only [argAddr]
  rw [show (s.gpr .esp + BitVec.ofNat 32 (4 + 4 * (k / 4))).setWidth 64 = addr (s.gpr .esp) (4 + 4 * (k / 4))
    from rfl, addr_eq (by omega), addr_eq (by omega), BitVec.add_assoc, BitVec.add_assoc,
    ← BitVec.ofNat_add, ← BitVec.ofNat_add]
  congr 2; omega

/-- The initial taint: the stack arguments are public, the words holding
`state` and `scratch` are the base addresses of the writable regions, and the
20 bytes below `esp` are outside them. -/
def τ₀ (P : Params) (S : Nat) : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [P.N + 64, S], argLen := 28,
    argBases := [(4, 0), (24, 1)], room := 20 }

section
variable {P : Params} {S : Nat} {H : Md 64 P.N 8}

theorem wf₀ (hd : Dims P S) {s : State} (h : (updK H S).pre s) : VG.X86.Taint.Wf (τ₀ P S) s := by
  have hp := pre_of h
  have hst := hp.st_fit; have hsc := hp.scr_fit; have hs := hp.sp_fit
  have hlo := hp.sp_lo; have := hd.N
  obtain ⟨-, -, -, -, -, -, -, -, -, k1, k2, -⟩ := h
  refine VG.X86.Taint.Wf.entryRoom rfl ⟨fun _ => ⟨by simp [hp.wr, τ₀], ?_, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨hs, ?_⟩, ?_⟩ fun _ => ⟨hlo, ?_⟩
  · simp only [hp.wr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
      List.Pairwise.nil, and_true]
    exact ⟨hp.st_scr, fun _ h => h.elim⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [BitVec.toNat_setWidth] <;> omega
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 24) (by omega) hp.ret_st hp.a_st
    · exact VG.X86.Taint.frame_disjoint (n := 24) (by omega) hp.ret_scr hp.a_scr
  · intro p hp'
    simp only [τ₀, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl <;> refine ⟨by simp [τ₀], ?_⟩ <;>
      simp [VG.X86.Taint.region, hp.wr, addr, arg, argAddr]
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    exacts [k1, k2]

theorem agree₀ (hd : Dims P S) {s₁ s₂ : State} (h₁ : (updK H S).pre s₁) (h₂ : (updK H S).pre s₂)
    (hpub : (updK H S).pub s₁ s₂) : VG.X86.Taint.Agree (τ₀ P S) s₁ s₂ := by
  obtain ⟨hesp, ha⟩ := hpub
  have hp₁ := pre_of h₁; have hp₂ := pre_of h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, wf₀ hd h₁, wf₀ hd h₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => hesp,
    fun k h4 hk => ?_⟩
  · simp only [τ₀, RegSet.mem_ofList, List.mem_singleton] at hr
    subst hr; exact hesp
  · rw [hp₁.wr, hp₂.wr]
    simp only [stR, scR, stA, scA, st, scr, ha 0 (by omega), ha 5 (by omega)]
  · simp only [τ₀] at hk
    rw [show VG.X86.Taint.depth (τ₀ P S).stk = 0 from rfl, Nat.zero_add]
    have f₁ : (s₁.gpr .esp).toNat + 28 ≤ 2 ^ 32 := hp₁.sp_fit
    have f₂ : (s₂.gpr .esp).toNat + 28 ≤ 2 ^ 32 := hp₂.sp_fit
    rw [VG.X86.Taint.argByte_eq f₁ h4 hk, VG.X86.Taint.argByte_eq f₂ h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega))]
    exact congrArg _ (ha _ (by omega))

end

/-- Memory holding the arguments `0x1000, 0, 0, 0x2000, 0, 0x3000` at `0x5004`. -/
def satMem : Mem := fun a =>
  if a = 0x5005 then 0x10 else if a = 0x5011 then 0x20 else if a = 0x5019 then 0x30 else 0

/-- The registers and memory of a state satisfying the precondition (with no data). -/
def sat₀ : State where
  gpr r := match r with
    | .esp => 0x5000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMem
  rd := []
  wr := []

/-- A state satisfying the precondition (with no data). -/
def sat (P : Params) (S : Nat) : State :=
  { sat₀ with rd := [⟨0x2000, 0⟩, ⟨0x5004, 24⟩], wr := [⟨0x1000, P.N + 64⟩, ⟨0x3000, S⟩] }

section
variable {P : Params} {S : Nat} {H : Md 64 P.N 8}

theorem sat_pre (hd : Dims P S) : (updK H S).pre (sat P S) := by
  have := hd.N; have := hd.S
  have a0 : arg (sat P S) 0 = 0x1000 := show arg sat₀ 0 = _ by decide
  have a3 : arg (sat P S) 3 = 0x2000 := show arg sat₀ 3 = _ by decide
  have a4 : arg (sat P S) 4 = 0 := show arg sat₀ 4 = _ by decide
  have a5 : arg (sat P S) 5 = 0x3000 := show arg sat₀ 5 = _ by decide
  have e : argAddr (sat P S) 0 = 0x5004 := show argAddr sat₀ 0 = _ by decide
  have hsp : (sat P S).gpr .esp = 0x5000 := rfl
  simp only [updK, a0, a3, a4, a5, e, hsp]
  have hs : ((0x5000 : BitVec 32).setWidth 64 - 20 : Addr) = 0x4FEC := by decide
  simp only [hs]
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by simp; omega, by decide, by simp; omega,
    by decide, by decide⟩ <;>
  · first
    | exact Offset.disjoint_of_le (by simp only [BitVec.toNat_setWidth, BitVec.reduceToNat]; omega)
        (by simp only [BitVec.toNat_setWidth, BitVec.reduceToNat]; omega)
    | exact (Offset.disjoint_of_le (by simp only [BitVec.toNat_setWidth, BitVec.reduceToNat]; omega)
        (by simp only [BitVec.toNat_setWidth, BitVec.reduceToNat]; omega)).symm

/-- `update` is verified, given that it is constant time (by the taint analysis of each hash
function's code, from `τ₀` and `agree₀`). -/
theorem verified (hd : Dims P S) {name : String} {code : Prog isa} (hf : CalleeOk H code)
    (hct : ConstantTime isa (updK H S).pre (updK H S).pub (update P name code)) :
    Verified X86.target (update P name code) (updK H S) := by
  refine ⟨fun s hs => ?_, hct, ⟨sat P S, sat_pre hd⟩⟩
  obtain ⟨t, s', he, h⟩ := correct hd hf (pre_of hs)
  exact ⟨t, s', he, h⟩

end

end VG.Proof.MdStream.X86.Update

/-!
# Streaming Merkle–Damgård hash functions on x86 (32-bit): `finalize`

Untrusted: everything here is checked by Lean. The correctness of
`finalize`, for any hash function (`Md`) whose code stores the length field
and writes the digest as `Shape` says, and any correct compression function
(`CalleeOk`), with `state` in `ebx`, `scratch` in `ebp`, the buffered bytes in
`edi`, whether the block being padded is not the last in `esi`, and `count`
and `out` in `scratch[so+16..so+28)`. Each compression calls the
compression function (`compressAt_ok`), which uses the 20 bytes below
`esp`. Constant time follows from the taint analysis of each hash function's
code (which looks into the compression function).
-/

namespace VG.Proof.MdStream.X86.Finalize

open VG VG.X86 VG.Impl.MdStream.X86
open VG.Spec.Sha256 (bytesAt)
open VG.Proof.MdStream.X86.Update (argWord_eq)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil writeBytes_snoc writeBytes_before bytesAt_writeBytes
  writeBytes_frame bytesAt_congr)

/-! ## The precondition -/

section
variable (P : Params) (S : Nat) (s₀ : State)

abbrev esp₀ : BitVec 32 := s₀.gpr .esp
abbrev st : BitVec 32 := arg s₀ 0
abbrev cnt : Nat := (count s₀).toNat
abbrev out : BitVec 32 := arg s₀ 3
abbrev scr : BitVec 32 := arg s₀ 4
abbrev stA : Addr := (st s₀).setWidth 64
abbrev outA : Addr := (out s₀).setWidth 64
abbrev scA : Addr := (scr s₀).setWidth 64
abbrev stR : Region := ⟨stA s₀, P.N + 64⟩
abbrev outR : Region := ⟨outA s₀, P.N⟩
abbrev scR : Region := ⟨scA s₀, S⟩
abbrev argR : Region := ⟨addr (esp₀ s₀) 4, 20⟩
abbrev retR : Region := ⟨(esp₀ s₀).setWidth 64, 4⟩
abbrev stkR : Region := below (esp₀ s₀) 20
/-- The buffer. -/
abbrev buf : Addr := stA s₀ + BitVec.ofNat 64 P.N

/-- Our caller's registers are saved in the scratch space. -/
def Saved (m : Mem) : Prop := ∀ p ∈ saved P, m.readW (addr (scr s₀) p.2) 32 = s₀.gpr p.1

end

section
variable {P : Params} (H : Md 64 P.N 8) (s₀ : State)

/-- The messages the initial state represents, from `iv`. -/
def R₀ (iv : H.HV) (m : List Byte) : Prop :=
  H.Repr iv s₀.mem (stA s₀) m ∧ count s₀ = BitVec.ofNat 64 m.length

/-- The final hash value, if `n` bytes are buffered in a block that is not the last. -/
def Fin1 (mem : Mem) (n : Nat) (m : List Byte) : H.HV :=
  H.compress (H.compress (H.stateAt mem (stA s₀))
    (H.parse fun t => (bytesAt mem (buf P s₀) n ++ List.replicate (64 - n) 0).getD t 0))
    (H.parse fun t => (List.replicate (64 - 8) 0 ++ H.lenBytes m.length).getD t 0)

/-- The final hash value, if `n` bytes are buffered in the last block. -/
def Fin0 (mem : Mem) (n : Nat) (m : List Byte) : H.HV :=
  H.compress (H.stateAt mem (stA s₀))
    (H.parse fun t => (bytesAt mem (buf P s₀) n ++ List.replicate (64 - 8 - n) 0 ++
      H.lenBytes m.length).getD t 0)

end

structure Pre (P : Params) (S : Nat) (s₀ : State) : Prop where
  rd : s₀.rd = []
  wr : s₀.wr = [stR P s₀, outR P s₀, scR S s₀, argR s₀]
  st_out : (stR P s₀).Disjoint (outR P s₀)
  st_scr : (stR P s₀).Disjoint (scR S s₀)
  out_scr : (outR P s₀).Disjoint (scR S s₀)
  a_st : (argR s₀).Disjoint (stR P s₀)
  a_out : (argR s₀).Disjoint (outR P s₀)
  a_scr : (argR s₀).Disjoint (scR S s₀)
  ret_st : (retR s₀).Disjoint (stR P s₀)
  ret_out : (retR s₀).Disjoint (outR P s₀)
  ret_scr : (retR s₀).Disjoint (scR S s₀)
  stk_st : (stkR s₀).Disjoint (stR P s₀)
  stk_out : (stkR s₀).Disjoint (outR P s₀)
  stk_scr : (stkR s₀).Disjoint (scR S s₀)
  st_fit : (st s₀).toNat + (P.N + 64) ≤ 2 ^ 32
  out_fit : (out s₀).toNat + P.N ≤ 2 ^ 32
  scr_fit : (scr s₀).toNat + S ≤ 2 ^ 32
  sp_lo : 20 ≤ (esp₀ s₀).toNat
  sp_fit : (esp₀ s₀).toNat + 24 ≤ 2 ^ 32

section
variable {P : Params} {S : Nat} {H : Md 64 P.N 8}

theorem pre_of {s₀ : State} (h : (finK H S).pre s₀) : Pre P S s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19⟩ := h
  have e := stk_eq h18
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, by show (below _ _).Disjoint _; rw [e]; exact h12,
    by show (below _ _).Disjoint _; rw [e]; exact h13, by show (below _ _).Disjoint _; rw [e]; exact h14,
    h15, h16, h17, h18, h19⟩

theorem cnt_mod (s₀ : State) : cnt s₀ % 64 = (arg s₀ 1).toNat % 64 := by
  simp only [cnt, count]
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt (arg s₀ 1).isLt, Nat.shiftLeft_eq]
  omega

theorem R₀.length {s₀ : State} {iv : H.HV} {m : List Byte} (h : R₀ H s₀ iv m) : cnt s₀ % 64 = m.length % 64 := by
  rw [cnt, h.2, BitVec.toNat_ofNat]
  omega

namespace Pre
variable {s₀ : State} (hp : Pre P S s₀)
include hp

theorem scr_in {d : Nat} (hd : d + 4 ≤ S) : (scR S s₀).Contains (addr (scr s₀) d) 4 :=
  contains_addr hd (by omega) hp.scr_fit

theorem scr_sub {d : Nat} (hd : d + 4 ≤ S) : Region.Sub ⟨addr (scr s₀) d, 4⟩ (scR S s₀) := by
  rw [addr_eq (by have := hp.scr_fit; omega)]
  exact sub_offset hd (by have := hp.scr_fit; omega)

theorem arg_in {d : Nat} (hd₁ : 4 ≤ d) (hd : d + 4 ≤ 24) : (argR s₀).Contains (addr (esp₀ s₀) d) 4 := by
  have := hp.sp_fit
  show (⟨addr (esp₀ s₀) 4, 20⟩ : Region).Contains _ _
  rw [addr_eq (by omega), addr_eq (by omega)]
  exact Offset.contains _ hd₁ (by omega) (by omega)

theorem arg_sub {d : Nat} (hd₁ : 4 ≤ d) (hd : d + 4 ≤ 24) : Region.Sub ⟨addr (esp₀ s₀) d, 4⟩ (argR s₀) := by
  have := hp.sp_fit
  show Region.Sub _ ⟨addr (esp₀ s₀) 4, 20⟩
  rw [addr_eq (by omega), addr_eq (by omega)]
  exact Offset.sub _ hd₁ (by omega)

/-- The return address is below the arguments. -/
theorem ret_a : (retR s₀).Disjoint (argR s₀) := by
  have := hp.sp_fit
  show Region.Disjoint ⟨(esp₀ s₀).setWidth 64, 4⟩ ⟨addr (esp₀ s₀) 4, 20⟩
  rw [addr_eq (by omega)]
  exact Offset.base_disjoint _ (Nat.le_refl _) (by omega)

theorem ret_stk : (retR s₀).Disjoint (stkR s₀) := by
  have := hp.sp_fit; have := hp.sp_lo
  show Region.Disjoint ⟨(esp₀ s₀).setWidth 64, 4⟩ ⟨(esp₀ s₀ - BitVec.ofNat 32 20).setWidth 64, 20⟩
  rw [Taint.sub_setWidth (by omega)]
  exact Offset.base_disjoint_below _ (by omega)

end Pre

end

/-! ## Invariants -/

structure Common (P : Params) (S : Nat) (s₀ : State) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  ebx : s.gpr .ebx = st s₀
  ebp : s.gpr .ebp = scr s₀
  esp : s.gpr .esp = esp₀ s₀
  frame : Frame [stR P s₀, scR S s₀, argR s₀, stkR s₀] s₀.mem s.mem
  saved : Saved P s₀ s.mem
  lo : s.mem.readW (addr (scr s₀) (P.so + 16)) 32 = arg s₀ 1
  hi : s.mem.readW (addr (scr s₀) (P.so + 20)) 32 = arg s₀ 2
  outp : s.mem.readW (addr (scr s₀) (P.so + 24)) 32 = out s₀

/-- The loop invariant: `k = 1` while the block being padded is not the last
one, with `n` bytes of it buffered. -/
structure LInv {P : Params} (S : Nat) (H : Md 64 P.N 8) (s₀ : State) (k n : Nat) (s : State) : Prop
    extends Common P S s₀ s where
  k_le : k ≤ 1
  n_le : n ≤ 56 + 8 * k
  edi : s.gpr .edi = BitVec.ofNat 32 n
  esi : s.gpr .esi = BitVec.ofNat 32 k
  hash : ∀ iv m, R₀ H s₀ iv m → H.lenOk m.length → H.hash iv m =
    H.digest (if k = 1 then Fin1 H s₀ s.mem n m else Fin0 H s₀ s.mem n m)

/-- All blocks are compressed. -/
def Done {P : Params} (S : Nat) (H : Md 64 P.N 8) (s₀ : State) (s : State) : Prop :=
  Common P S s₀ s ∧ ∀ iv m, R₀ H s₀ iv m → H.lenOk m.length → H.hash iv m = H.digest (H.stateAt s.mem (stA s₀))

section
variable {P : Params} {S : Nat} {H : Md 64 P.N 8}

theorem Common.of_gpr {s₀ : State} {s s' : State} (h : Common P S s₀ s)
    (hg : ∀ r ∈ [Reg.ebx, .ebp, .esp], s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Common P S s₀ s' where
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  ebx := by rw [hg _ (by simp)]; exact h.ebx
  ebp := by rw [hg _ (by simp)]; exact h.ebp
  esp := by rw [hg _ (by simp)]; exact h.esp
  frame := by rw [hm]; exact h.frame
  saved := by rw [hm]; exact h.saved
  lo := by rw [hm]; exact h.lo
  hi := by rw [hm]; exact h.hi
  outp := by rw [hm]; exact h.outp

/-- A write within `stR` or the arguments keeps what `Common` says about memory. -/
theorem Common.frame_keep (hd : Dims P S) {s₀ : State} (hp : Pre P S s₀) {s : State} (h : Common P S s₀ s)
    {m : Mem} (hf : Frame [stR P s₀, argR s₀] s.mem m) :
    Frame [stR P s₀, scR S s₀, argR s₀, stkR s₀] s₀.mem m ∧ Saved P s₀ m ∧
      m.readW (addr (scr s₀) (P.so + 16)) 32 = arg s₀ 1 ∧ m.readW (addr (scr s₀) (P.so + 20)) 32 = arg s₀ 2 ∧
      m.readW (addr (scr s₀) (P.so + 24)) 32 = out s₀ := by
  have := hd.so
  have word : ∀ d, d + 4 ≤ S → m.readW (addr (scr s₀) d) 32 = s.mem.readW (addr (scr s₀) d) 32 := by
    intro d h₂
    refine hf.readW (r := ⟨addr (scr s₀) d, 4⟩) (Region.contains_self _ _) ?_ (by decide)
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.st_scr.symm.sub_left (hp.scr_sub h₂)
    · exact hp.a_scr.symm.sub_left (hp.scr_sub h₂)
  refine ⟨h.frame.trans (hf.mono (by simp)), fun p hp' => ?_, by rw [word _ (by omega)]; exact h.lo,
    by rw [word _ (by omega)]; exact h.hi, by rw [word _ (by omega)]; exact h.outp⟩
  have hd' := saved_offset hp'
  rw [word p.2 (by omega)]
  exact h.saved p hp'

theorem buf_add (s₀ : State) (n : Nat) : buf P s₀ + BitVec.ofNat 64 n = stA s₀ + BitVec.ofNat 64 (P.N + n) :=
  add_ofNat _ _ _

/-- Writing buffer bytes `[n, n + |xs|)`. -/
theorem buf_frame (hd : Dims P S) {s₀ : State} (m : Mem) {n : Nat} {xs : List Byte} (hn : n + xs.length ≤ 64) :
    Frame [stR P s₀] m (writeBytes m (buf P s₀ + BitVec.ofNat 64 n) xs) := by
  have := hd.N
  refine writeBytes_frame _ _ _ ?_
  rw [buf_add]
  exact contains_offset (by omega) (by omega)

/-! ## Zeroing the buffer -/

/-- Zeroing buffer bytes `[n, lim)` from state `sI`: `j` of them done. -/
structure Zero (P : Params) (s₀ : State) (sI : State) (n lim j : Nat) (s : State) : Prop where
  j_le : j ≤ lim - n
  keep : ∀ r ∈ [Reg.ebx, .ebp, .esp, .esi, .ecx], s.gpr r = sI.gpr r
  rd : s.rd = sI.rd
  wr : s.wr = sI.wr
  edi : s.gpr .edi = BitVec.ofNat 32 (n + j)
  eax : s.gpr .eax = BitVec.ofNat 32 (lim - n - j)
  mem : s.mem = writeBytes sI.mem (buf P s₀ + BitVec.ofNat 64 n) (List.replicate j 0)

theorem zero_step (hd : Dims P S) {s₀ : State} (hp : Pre P S s₀) {sI : State} (hC : Common P S s₀ sI)
    (hecx : sI.gpr .ecx = 0) {n lim j : Nat} (hlim : lim ≤ 64) (hj : j < lim - n) {s : State}
    (h : Zero P s₀ sI n lim j s) :
    WP isa (.block [.mov .edx (.reg .ebx), .alu .add .edx (.reg .edi), .store8 (at_ .edx P.N) .cl,
      .alu .add .edi (.imm 1), .alu .sub .eax (.imm 1)]) s fun s' =>
      Zero P s₀ sI n lim (j + 1) s' ∧ s'.zf = some (decide (lim - n - (j + 1) = 0)) := by
  have hst := hp.st_fit; have := hd.N
  have hebx : s.gpr .ebx = st s₀ := by rw [h.keep _ (by simp), hC.ebx]
  have ha : buf P s₀ + BitVec.ofNat 64 n + BitVec.ofNat 64 j = stA s₀ + BitVec.ofNat 64 (P.N + n + j) := by
    simp only [buf, BitVec.ofNat_add]; ac_rfl
  have hout : InRegions s.wr (buf P s₀ + BitVec.ofNat 64 n + BitVec.ofNat 64 j) 1 := by
    refine ⟨stR P s₀, by simp [h.wr, hC.wr, hp.wr], ?_⟩
    rw [ha]
    exact contains_offset (by omega) (by omega)
  refine wp_mov fun s₁ u₁ => wp_add fun s₂ u₂ => ?_
  refine wp_store8 (r := .cl) (a := buf P s₀ + BitVec.ofNat 64 n + BitVec.ofNat 64 j) ?_
    (by rw [u₂.wr, u₁.wr]; exact hout) fun s₃ u₃ => ?_
  · rw [ea_at, u₂.gpr, u₁.gpr, u₁.other _ (by decide), hebx, h.edi, ha,
      addr_add_ofNat (by omega)]
    congr 2; omega
  refine wp_addi fun s₄ u₄ => wp_subi fun s₅ u₅ hz₅ => WP.block_nil ⟨⟨by omega, fun r hr => ?_,
    by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd], by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr], ?_, ?_, ?_⟩, ?_⟩
  · have : r ≠ .eax ∧ r ≠ .edi ∧ r ≠ .edx := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
    rw [u₅.other r this.1, u₄.other r this.2.1, u₃.gpr, u₂.other r this.2.2, u₁.other r this.2.2, h.keep r hr]
  · rw [u₅.other _ (by decide), u₄.gpr, u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h.edi,
      ← ofNat_succ, Nat.add_assoc]
  · rw [u₅.gpr, u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h.eax,
      ofNat_pred (by omega), Nat.sub_sub]
  · rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem, show Reg8.cl.reg = Reg.ecx from rfl, u₂.other _ (by decide),
      u₁.other _ (by decide), h.keep _ (by simp), hecx, h.mem, List.replicate_succ',
      writeBytes_snoc _ _ _ _ (by simp only [List.length_replicate]; omega), List.length_replicate]
    rfl
  · rw [hz₅, u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h.eax,
      ofNat_pred (by omega), ofNat_beq_zero (by omega), Nat.sub_sub, Nat.sub_sub]

theorem zero_ok (hd : Dims P S) {s₀ : State} (hp : Pre P S s₀) {sI : State} (hC : Common P S s₀ sI)
    (hecx : sI.gpr .ecx = 0) {n lim : Nat} (hlim : lim ≤ 64) (hn : n ≤ lim) {s : State}
    (h : Zero P s₀ sI n lim 0 s) (hz : s.zf = some (decide (lim - n = 0))) :
    WP isa (.ite .e (.block []) (.loop (.block [.mov .edx (.reg .ebx), .alu .add .edx (.reg .edi),
      .store8 (at_ .edx P.N) .cl, .alu .add .edi (.imm 1), .alu .sub .eax (.imm 1)]) .ne)) s
      (Zero P s₀ sI n lim (lim - n)) := by
  refine WP.ite (decide (lim - n = 0)) hz (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    exact WP.block_nil (hb ▸ h)
  · simp only [decide_eq_false_iff_not] at hb
    refine WP.loop (M := isa) (fun k s => ∃ j, k = lim - n - j ∧ j < lim - n ∧ Zero P s₀ sI n lim j s)
      ?_ (lim - n) s ⟨0, rfl, by omega, h⟩
    rintro k s ⟨j, rfl, hj, hZ⟩
    refine WP.mono (zero_step hd hp hC hecx hlim hj hZ) fun s' ⟨hZ', hz'⟩ => ?_
    by_cases hl : lim - n - (j + 1) = 0
    · refine .inl ⟨by show s'.zf.map (!·) = _; rw [hz']; simp [hl], ?_⟩
      rwa [show j + 1 = lim - n by omega] at hZ'
    · exact .inr ⟨by show s'.zf.map (!·) = _; rw [hz']; simp [hl], _, by omega, j + 1, rfl, by omega, hZ'⟩

/-! ## One block -/

/-- The compression of the buffer. -/
theorem compress_buf (hd : Dims P S) {name : String} {code : Prog isa} (hf : CalleeOk H code) {s₀ : State}
    (hp : Pre P S s₀) {s : State} (hC : Common P S s₀ s)
    (heax : s.gpr .eax = st s₀ + BitVec.ofNat 32 P.N) {Q : State → Prop}
    (hQ : ∀ s', Common P S s₀ s' → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      H.stateAt s'.mem (stA s₀) = H.compress (H.stateAt s.mem (stA s₀)) (H.blockAt s.mem (buf P s₀)) → Q s') :
    WP isa (compressAt name code .ebx .ebp) s Q := by
  have hst := hp.st_fit; have hsc := hp.scr_fit; have := hd.N; have := hd.so
  have eN : Region.Sub ⟨stA s₀, P.N⟩ (stR P s₀) := Region.sub_prefix (by omega)
  have eso : Region.Sub ⟨scA s₀, P.so⟩ (scR S s₀) := Region.sub_prefix (by omega)
  have hb : (st s₀ + BitVec.ofNat 32 P.N).setWidth 64 = stA s₀ + BitVec.ofNat 64 P.N := addr_eq (by omega)
  have eb : Region.Sub ⟨(st s₀ + BitVec.ofNat 32 P.N).setWidth 64, 64⟩ (stR P s₀) := by
    rw [hb]; exact sub_offset (by omega) (by omega)
  refine compressAt_ok hf (st := st s₀) (scr := scr s₀) (blk := st s₀ + BitVec.ofNat 32 P.N) (E := esp₀ s₀)
    (by decide) (by decide) (by decide) (by decide) hC.esp hC.ebx hC.ebp heax hp.sp_lo (by omega)
    (by rw [BitVec.toNat_add, toNat_ofNat_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega) (by omega)
    ((hp.st_scr.sub_left eN).sub_right eso) ?_ ((hp.st_scr.sub_left eb).sub_right eso)
    (hp.stk_st.sub_right eN) (hp.stk_scr.sub_right eso) (hp.stk_st.sub_right eb) ?_ ?_ ?_
  · rw [hb]; exact Offset.disjoint_base _ (Nat.le_refl _) (by omega)
  · rw [hC.rd, hC.wr, hp.rd, hp.wr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact ⟨stR P s₀, by simp, P.N, hb, by simp⟩
  · rw [hC.wr, hp.wr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨stR P s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨scR S s₀, by simp, 0, by simp, by simp; omega⟩
  · intro s' hrd hwr hcs hf hstate
    have cs : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r := hcs
    have word : ∀ d, P.so ≤ d → d + 4 ≤ S →
        s'.mem.readW (addr (scr s₀) d) 32 = s.mem.readW (addr (scr s₀) d) 32 := by
      intro d h₁ h₂
      refine hf.readW (r := ⟨addr (scr s₀) d, 4⟩) (Region.contains_self _ _) ?_ (by decide)
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (hp.st_scr.symm.sub_left (hp.scr_sub h₂)).sub_right eN
      · rw [addr_eq (by omega)]; exact Offset.disjoint_base _ (by omega) (by omega)
      · exact hp.stk_scr.symm.sub_left (hp.scr_sub h₂)
    refine hQ s' ⟨hrd.trans hC.rd, hwr.trans hC.wr, by rw [cs _ (by decide)]; exact hC.ebx,
      by rw [cs _ (by decide)]; exact hC.ebp, by rw [cs _ (by decide)]; exact hC.esp,
      hC.frame.trans (hf.sub ?_), fun p hp' => ?_, by rw [word _ (by omega) (by omega)]; exact hC.lo,
      by rw [word _ (by omega) (by omega)]; exact hC.hi, by rw [word _ (by omega) (by omega)]; exact hC.outp⟩
      hcs (by rw [hstate, hb])
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨stR P s₀, by simp, eN⟩
      · exact ⟨scR S s₀, by simp, eso⟩
      · exact ⟨stkR s₀, by simp, fun _ h => h⟩
    · have hd' := saved_offset hp'
      rw [word p.2 hd'.1 (by omega)]
      exact hC.saved p hp'

/-- Point `eax` at the buffer. -/
theorem args_ok {s₀ : State} {s : State} (hC : Common P S s₀ s) :
    WP isa (.block [.mov .eax (.reg .ebx), .alu .add .eax (.imm (BitVec.ofNat 32 P.N))]) s fun s' =>
      Common P S s₀ s' ∧ (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧ s'.gpr .eax = st s₀ + BitVec.ofNat 32 P.N ∧
        s'.mem = s.mem := by
  refine wp_mov fun s₁ u₁ => wp_addi fun s₂ u₂ => WP.block_nil ?_
  have g₂ : ∀ r, r ≠ .eax → s₂.gpr r = s.gpr r := fun r h => by rw [u₂.other r h, u₁.other r h]
  have hm : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
  refine ⟨hC.of_gpr (fun r hr => g₂ r (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)) hm
    (by rw [u₂.rd, u₁.rd]) (by rw [u₂.wr, u₁.wr]), g₂, by rw [u₂.gpr, u₁.gpr, hC.ebx], hm⟩

end

/-- The loop's postcondition for one iteration. -/
def Step {P : Params} (S : Nat) (H : Md 64 P.N 8) (s₀ : State) (k : Nat) (s : State) : Prop :=
  (eval .e s = some false ∧ Done S H s₀ s) ∨ (eval .e s = some true ∧ k = 1 ∧ LInv S H s₀ 0 0 s)

theorem regs3 {r : Reg} (hr : r ∈ [Reg.ebx, .ebp, .esp]) : r ≠ .eax ∧ r ≠ .ecx ∧ r ≠ .edx ∧ r ≠ .edi ∧ r ≠ .esi := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> decide

section
variable {P : Params} {S : Nat} {H : Md 64 P.N 8}

theorem body_ok (hd : Dims P S) (hs : Shape H) {name : String} {code : Prog isa} (hf : CalleeOk H code)
    {s₀ : State} (hp : Pre P S s₀) {k n : Nat} {s : State} (h : LInv S H s₀ k n s) :
    WP isa (finalizeBody P name code) s (Step S H s₀ k) := by
  have hk := h.k_le; have hn := h.n_le; have hst := hp.st_fit; have := hd.N; have := hd.so; have := hd.S
  have hC := h.toCommon
  unfold finalizeBody
  -- `eax := 64` or `56`: the end of the zeros.
  refine WP.seq (wp_movi fun s₁ u₁ => wp_test fun s₂ f₂ z₂ => WP.block_nil ?_)
  have hz₂ : s₂.zf = some (decide (k = 0)) := by
    rw [z₂, u₁.other _ (by decide), h.esi, BitVec.and_self, ofNat_beq_zero (by omega)]
  refine WP.seq (WP.mono (Q := fun (s₃ : State) => s₃.gpr .eax = BitVec.ofNat 32 (56 + 8 * k) ∧
      (∀ r, r ≠ .eax → s₃.gpr r = s.gpr r) ∧ s₃.mem = s.mem ∧ s₃.rd = s.rd ∧ s₃.wr = s.wr) ?_
    fun s₃ ⟨heax₃, g₃, m₃, rd₃, wr₃⟩ => ?_)
  · refine WP.ite (decide (k = 0)) (by show s₂.zf = _; rw [hz₂]) (fun hb => ?_) (fun hb => ?_)
    · simp only [decide_eq_true_eq] at hb; subst hb
      refine wp_movi fun s₃ u₃ => WP.block_nil ⟨by rw [u₃.gpr]; rfl, fun r hr => ?_, ?_, ?_, ?_⟩
      · rw [u₃.other r hr, f₂.gpr, u₁.other r hr]
      · rw [u₃.mem, f₂.mem, u₁.mem]
      · rw [u₃.rd, f₂.rd, u₁.rd]
      · rw [u₃.wr, f₂.wr, u₁.wr]
    · simp only [decide_eq_false_iff_not] at hb
      refine WP.block_nil ⟨by rw [f₂.gpr, u₁.gpr, show k = 1 by omega]; rfl, fun r hr => ?_, ?_, ?_, ?_⟩
      · rw [f₂.gpr, u₁.other r hr]
      · rw [f₂.mem, u₁.mem]
      · rw [f₂.rd, u₁.rd]
      · rw [f₂.wr, u₁.wr]
  -- `ecx := 0; eax -= edi`: zero the rest of the buffer, up to `lim`.
  have hC₃ : Common P S s₀ s₃ := hC.of_gpr (fun r hr => g₃ r (regs3 hr).1) m₃ rd₃ wr₃
  refine WP.seq (wp_movi fun s₄ u₄ => wp_sub fun s₅ u₅ z₅ => WP.block_nil ?_)
  have hC₄ : Common P S s₀ s₄ := hC₃.of_gpr (fun r hr => u₄.other r (regs3 hr).2.1) u₄.mem u₄.rd u₄.wr
  have hecx₄ : s₄.gpr .ecx = 0 := u₄.gpr
  have hedi₄ : s₄.gpr .edi = BitVec.ofNat 32 n := by rw [u₄.other _ (by decide), g₃ _ (by decide), h.edi]
  have heax₅ : s₅.gpr .eax = BitVec.ofNat 32 (56 + 8 * k - n) := by
    rw [u₅.gpr, u₄.other _ (by decide), heax₃, hedi₄, sub_ofNat (a := 56 + 8 * k) (b := n) (by omega)]
  have hZ : Zero P s₀ s₄ n (56 + 8 * k) 0 s₅ := by
    refine ⟨Nat.zero_le _, fun r hr => u₅.other r ?_, u₅.rd, u₅.wr,
      by rw [u₅.other _ (by decide), hedi₄, Nat.add_zero], by rw [heax₅, Nat.sub_zero],
      by rw [u₅.mem, List.replicate_zero, writeBytes_nil]⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
  have hz₅ : s₅.zf = some (decide (56 + 8 * k - n = 0)) := by
    rw [z₅, ← u₅.gpr, heax₅, ofNat_beq_zero (by omega)]
  refine WP.seq (WP.mono (zero_ok hd hp hC₄ hecx₄ (by omega) hn hZ hz₅) fun s₆ hZ₆ => ?_)
  have hm₄ : s₄.mem = s.mem := by rw [u₄.mem, m₃]
  have hf₆ : Frame [stR P s₀] s₄.mem s₆.mem := by
    rw [hZ₆.mem]; exact buf_frame hd _ (by simp only [List.length_replicate]; omega)
  obtain ⟨hfr₆, hsv₆, hlo₆, hhi₆, hout₆⟩ := hC₄.frame_keep hd hp (hf₆.mono (by simp))
  have hC₆ : Common P S s₀ s₆ := ⟨hZ₆.rd.trans hC₄.rd, hZ₆.wr.trans hC₄.wr, by rw [hZ₆.keep _ (by simp), hC₄.ebx],
    by rw [hZ₆.keep _ (by simp), hC₄.ebp], by rw [hZ₆.keep _ (by simp), hC₄.esp], hfr₆, hsv₆, hlo₆, hhi₆, hout₆⟩
  have hst₆ : H.stateAt s₆.mem (stA s₀) = H.stateAt s.mem (stA s₀) := by
    rw [hZ₆.mem, hm₄]
    apply H.stateAt_congr
    intro i hi
    rw [buf_add]
    exact writeBytes_before _ _ _ (by omega) (by simp only [List.length_replicate]; omega)
  have hby₆ : bytesAt s₆.mem (buf P s₀) (56 + 8 * k) =
      bytesAt s.mem (buf P s₀) n ++ List.replicate (56 + 8 * k - n) 0 := by
    rw [hZ₆.mem, hm₄, ← bytesAt_writeBytes _ _ _ _ (by simp only [List.length_replicate]; omega)]
    congr 1; simp only [List.length_replicate]; omega
  have hesi₆ : s₆.gpr .esi = BitVec.ofNat 32 k := by
    rw [hZ₆.keep _ (by simp), u₄.other _ (by decide), g₃ _ (by decide), h.esi]
  -- In the last block, the length field.
  refine WP.seq (wp_test fun s₇ f₇ z₇ => WP.block_nil ?_)
  have hC₇ : Common P S s₀ s₇ := hC₆.of_gpr (fun r _ => by rw [f₇.gpr]) f₇.mem f₇.rd f₇.wr
  have hz₇ : s₇.zf = some (decide (k = 0)) := by
    rw [z₇, hesi₆, BitVec.and_self, ofNat_beq_zero (by omega)]
  have hesi₇ : s₇.gpr .esi = BitVec.ofNat 32 k := by rw [f₇.gpr, hesi₆]
  refine WP.seq (WP.mono (Q := fun (s₈ : State) => Common P S s₀ s₈ ∧ s₈.gpr .esi = BitVec.ofNat 32 k ∧
      H.stateAt s₈.mem (stA s₀) = H.stateAt s.mem (stA s₀) ∧
      ∀ iv m, R₀ H s₀ iv m → H.lenOk m.length → bytesAt s₈.mem (buf P s₀) 64 = bytesAt s.mem (buf P s₀) n ++
        (if k = 1 then List.replicate (64 - n) 0 else List.replicate (56 - n) 0 ++ H.lenBytes m.length)) ?_
    fun s₈ ⟨hC₈, hesi₈, hst₈, hby₈⟩ => ?_)
  · refine WP.ite (decide (k = 0)) (by show s₇.zf = _; rw [hz₇]) (fun hb => ?_) (fun hb => ?_)
    · simp only [decide_eq_true_eq] at hb; subst hb
      have hsc₇ : ∀ d, d + 4 ≤ S → InRegions (s₇.rd ++ s₇.wr) (addr (s₇.gpr .ebp) d) 4 :=
        fun d hd => ⟨scR S s₀, by simp [hC₇.rd, hC₇.wr, hp.wr], by rw [hC₇.ebp]; exact hp.scr_in hd⟩
      have hso₇ : ∀ d, d + 4 ≤ P.N + 64 → InRegions s₇.wr (addr (s₇.gpr .ebx) d) 4 :=
        fun d hd => ⟨stR P s₀, by simp [hC₇.wr, hp.wr], by rw [hC₇.ebx]; exact contains_addr hd (by omega) hst⟩
      refine WP.mono (hs.len s₇ (by rw [hC₇.ebx]; exact hst) (hsc₇ _ (by omega)) (hsc₇ _ (by omega))
        (hso₇ _ (by omega)) (hso₇ _ (by omega))) fun s₈ ⟨g₈, rd₈, wr₈, m₈⟩ => ?_
      rw [hC₇.ebx, hC₇.ebp, hC₇.lo, hC₇.hi, show P.N + 56 = P.N + (64 - 8) by omega, ← buf_add] at m₈
      have hlen := H.lenOf_length (arg s₀ 2 ++ arg s₀ 1)
      have hfL : Frame [stR P s₀] s₇.mem s₈.mem := by
        rw [m₈]; exact buf_frame hd _ (by omega)
      obtain ⟨hfr, hsv, hlo, hhi, hout⟩ := hC₇.frame_keep hd hp (hfL.mono (by simp))
      refine ⟨⟨rd₈.trans hC₇.rd, wr₈.trans hC₇.wr, by rw [g₈ _ (by decide) (by decide) (by decide), hC₇.ebx],
        by rw [g₈ _ (by decide) (by decide) (by decide), hC₇.ebp],
        by rw [g₈ _ (by decide) (by decide) (by decide), hC₇.esp], hfr, hsv, hlo, hhi, hout⟩,
        by rw [g₈ _ (by decide) (by decide) (by decide), hesi₇], ?_, fun iv m hm hok => ?_⟩
      · rw [m₈, ← hst₆, ← f₇.mem]
        apply H.stateAt_congr
        intro i hi
        rw [buf_add]
        exact writeBytes_before _ _ _ (by omega) (by omega)
      · simp only [show ¬ ((0 : Nat) = 1) by decide, ite_false]
        rw [show arg s₀ 2 ++ arg s₀ 1 = count s₀ from rfl, hm.2, H.lenOf_eq _ hok] at m₈
        have e := bytesAt_writeBytes s₇.mem (buf P s₀) (64 - 8) (H.lenBytes m.length)
          (by rw [H.lenBytes_length]; omega)
        rw [H.lenBytes_length] at e
        rw [m₈, e, f₇.mem, hby₆, List.append_assoc]
    · simp only [decide_eq_false_iff_not] at hb
      have hk1 : k = 1 := by omega
      subst hk1
      refine WP.block_nil ⟨hC₇, hesi₇, by rw [f₇.mem, hst₆], fun iv m _ _ => ?_⟩
      rw [f₇.mem, hby₆]; simp
  -- Compress the block.
  refine WP.seq (WP.mono (args_ok hC₈) fun s₉ ⟨hC₉, g₉, heax₉, hm₉⟩ => ?_)
  refine WP.seq (compress_buf hd hf hp hC₉ heax₉ fun s₁₀ hC₁₀ cs₁₀ hst₁₀ => ?_)
  have hesi₁₀ : s₁₀.gpr .esi = BitVec.ofNat 32 k := by
    rw [cs₁₀ _ (by decide), g₉ _ (by decide), hesi₈]
  have hblk : ∀ iv m, R₀ H s₀ iv m → H.lenOk m.length → H.blockAt s₉.mem (buf P s₀) = H.parse fun t =>
      (bytesAt s.mem (buf P s₀) n ++
        (if k = 1 then List.replicate (64 - n) 0 else List.replicate (56 - n) 0 ++ H.lenBytes m.length)).getD t 0 := by
    intro iv m hm hok
    apply H.parse_congr
    intro t ht
    rw [hm₉]
    exact bytesAt_getD (hby₈ iv m hm hok) ht
  -- Next block, if any.
  refine wp_movi fun s₁₁ u₁₁ => wp_subi fun s₁₂ u₁₂ z₁₂ => WP.block_nil ?_
  have hC₁₂ : Common P S s₀ s₁₂ := hC₁₀.of_gpr (fun r hr => by
      rw [u₁₂.other r (regs3 hr).2.2.2.2, u₁₁.other r (regs3 hr).2.2.2.1]) (by rw [u₁₂.mem, u₁₁.mem])
    (by rw [u₁₂.rd, u₁₁.rd]) (by rw [u₁₂.wr, u₁₁.wr])
  have hz : s₁₂.zf = some (decide (k = 1)) := by
    rw [z₁₂, u₁₁.other _ (by decide), hesi₁₀, lit32 1, sub_beq (a := k) (b := 1) (by omega) (by omega)]
  have hst : ∀ iv m, R₀ H s₀ iv m → H.lenOk m.length →
      H.stateAt s₁₂.mem (stA s₀) = H.compress (H.stateAt s.mem (stA s₀)) (H.parse fun t =>
        (bytesAt s.mem (buf P s₀) n ++
          (if k = 1 then List.replicate (64 - n) 0 else List.replicate (56 - n) 0 ++ H.lenBytes m.length)).getD t 0) := by
    intro iv m hm hok
    rw [u₁₂.mem, u₁₁.mem, hst₁₀, hm₉, hst₈, ← hblk iv m hm hok, hm₉]
  by_cases hk1 : k = 1
  · subst hk1
    refine .inr ⟨by show s₁₂.zf = _; rw [hz]; rfl, rfl, ⟨hC₁₂, by omega, by omega, ?_, ?_, fun iv m hm hok => ?_⟩⟩
    · rw [u₁₂.other _ (by decide), u₁₁.gpr]; rfl
    · rw [u₁₂.gpr, u₁₁.other _ (by decide), hesi₁₀]; rfl
    · rw [h.hash iv m hm hok]
      simp only [ite_true, show ¬ (0 = 1) by decide, ite_false, Fin1, Fin0, hst iv m hm hok]
      simp [bytesAt]
  · have hk0 : k = 0 := by omega
    subst hk0
    refine .inl ⟨by show s₁₂.zf = _; rw [hz]; rfl, hC₁₂, fun iv m hm hok => ?_⟩
    rw [h.hash iv m hm hok, hst iv m hm hok]
    simp only [show ¬ (0 = 1) by decide, ite_false, Fin0, List.append_assoc]

/-! ## Prologue -/

/-- The memory after saving our caller's registers and copying `count` and `out` to scratch. -/
def proMem (P : Params) (s₀ : State) : Mem :=
  ((((((s₀.mem.writeW (addr (scr s₀) P.so) (s₀.gpr .ebx)).writeW (addr (scr s₀) (P.so + 4))
    (s₀.gpr .esi)).writeW (addr (scr s₀) (P.so + 8)) (s₀.gpr .edi)).writeW (addr (scr s₀) (P.so + 12))
    (s₀.gpr .ebp)).writeW (addr (scr s₀) (P.so + 16)) (arg s₀ 1)).writeW (addr (scr s₀) (P.so + 20))
    (arg s₀ 2)).writeW (addr (scr s₀) (P.so + 24)) (out s₀)

theorem proMem_frame (hd : Dims P S) {s₀ : State} (hp : Pre P S s₀) : Frame [scR S s₀] s₀.mem (proMem P s₀) := by
  have := hd.so
  have c : ∀ d, d + 4 ≤ S → (scR S s₀).Contains (addr (scr s₀) d) (32 / 8) := fun d hd => hp.scr_in hd
  simp only [proMem]
  exact (((((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c P.so (by omega))).writeW
    (List.mem_singleton_self _) _ (c (P.so + 4) (by omega))).writeW (List.mem_singleton_self _) _
    (c (P.so + 8) (by omega))).writeW (List.mem_singleton_self _) _ (c (P.so + 12) (by omega))).writeW
    (List.mem_singleton_self _) _ (c (P.so + 16) (by omega))).writeW (List.mem_singleton_self _) _
    (c (P.so + 20) (by omega))).writeW (List.mem_singleton_self _) _ (c (P.so + 24) (by omega))

theorem proMem_words (hd : Dims P S) {s₀ : State} (hp : Pre P S s₀) :
    Saved P s₀ (proMem P s₀) ∧ (proMem P s₀).readW (addr (scr s₀) (P.so + 16)) 32 = arg s₀ 1 ∧
      (proMem P s₀).readW (addr (scr s₀) (P.so + 20)) 32 = arg s₀ 2 ∧
      (proMem P s₀).readW (addr (scr s₀) (P.so + 24)) 32 = out s₀ := by
  have hs := hp.scr_fit; have := hd.so
  have w : ∀ (m : Mem) (v : BitVec 32) (d e : Nat), d + 4 ≤ S → e + 4 ≤ S → d + 4 ≤ e ∨ e + 4 ≤ d →
      (m.writeW (addr (scr s₀) e) v).readW (addr (scr s₀) d) 32 = m.readW (addr (scr s₀) d) 32 :=
    fun m v d e h₁ h₂ h => readW_writeW_addr m v (by omega) (by omega) h
  refine ⟨fun p hp' => ?_, ?_, ?_, ?_⟩
  · simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl | rfl | rfl <;> simp only [proMem] <;>
      rw [w _ _ _ (P.so + 24) (by omega) (by omega) (by omega), w _ _ _ (P.so + 20) (by omega) (by omega) (by omega),
        w _ _ _ (P.so + 16) (by omega) (by omega) (by omega)]
    · rw [w _ _ P.so (P.so + 12) (by omega) (by omega) (by omega),
        w _ _ P.so (P.so + 8) (by omega) (by omega) (by omega),
        w _ _ P.so (P.so + 4) (by omega) (by omega) (by omega), Mem.readW_writeW_self32]
    · rw [w _ _ (P.so + 4) (P.so + 12) (by omega) (by omega) (by omega),
        w _ _ (P.so + 4) (P.so + 8) (by omega) (by omega) (by omega), Mem.readW_writeW_self32]
    · rw [w _ _ (P.so + 8) (P.so + 12) (by omega) (by omega) (by omega), Mem.readW_writeW_self32]
    · rw [Mem.readW_writeW_self32]
  · simp only [proMem]
    rw [w _ _ (P.so + 16) (P.so + 24) (by omega) (by omega) (by omega),
      w _ _ (P.so + 16) (P.so + 20) (by omega) (by omega) (by omega), Mem.readW_writeW_self32]
  · simp only [proMem]
    rw [w _ _ (P.so + 20) (P.so + 24) (by omega) (by omega) (by omega), Mem.readW_writeW_self32]
  · simp only [proMem]; rw [Mem.readW_writeW_self32]

/-- The arguments, in memory that differs only in the scratch space. -/
theorem arg_read {s₀ : State} (hp : Pre P S s₀) {m : Mem} (hf : Frame [scR S s₀] s₀.mem m) {e : Nat}
    (h₁ : 4 ≤ e) (h₂ : e + 4 ≤ 24) : m.readW (addr (esp₀ s₀) e) 32 = s₀.mem.readW (addr (esp₀ s₀) e) 32 :=
  hf.readW (Region.contains_self _ _) (by simpa using hp.a_scr.sub_left (hp.arg_sub h₁ h₂)) (by decide)

theorem prologue_ok (hd : Dims P S) {s₀ : State} (hp : Pre P S s₀) :
    WP isa (.seq (.block (([.mov .eax (.mem (at_ .esp 20))] : List Instr) ++ save P .eax ++
      ([.mov .ebp (.reg .eax), .mov .ebx (.mem (at_ .esp 4)),
       .mov .ecx (.mem (at_ .esp 8)), .store (at_ .ebp (P.so + 16)) .ecx,
       .mov .ecx (.mem (at_ .esp 12)), .store (at_ .ebp (P.so + 20)) .ecx,
       .mov .ecx (.mem (at_ .esp 16)), .store (at_ .ebp (P.so + 24)) .ecx,
       .mov .edi (.mem (at_ .esp 8)), .alu .and .edi (.imm 63),
       .mov .edx (.reg .ebx), .alu .add .edx (.reg .edi), .mov .ecx (.imm 0x80),
       .store8 (at_ .edx P.N) .cl, .alu .add .edi (.imm 1),
       .mov .esi (.imm 0), .alu .cmp .edi (.imm 57)] : List Instr)))
      (.ite .ae (.block [.mov .esi (.imm 1)]) (.block []))) s₀
      fun s => ∃ k, LInv S H s₀ k (cnt s₀ % 64 + 1) s := by
  have hst := hp.st_fit; have := hd.so; have := hd.N
  have hr : cnt s₀ % 64 < 64 := Nat.mod_lt _ (by omega)
  have ain : ∀ e, 4 ≤ e → e + 4 ≤ 24 → ∀ t : State, t.rd = s₀.rd → t.wr = s₀.wr →
      InRegions (t.rd ++ t.wr) (addr (esp₀ s₀) e) 4 :=
    fun e h₁ h₂ t hrd hwr => ⟨argR s₀, by simp [hrd, hwr, hp.wr], hp.arg_in h₁ h₂⟩
  have sout : ∀ d, d + 4 ≤ S → ∀ t : State, t.wr = s₀.wr → InRegions t.wr (addr (scr s₀) d) 4 :=
    fun d hd t hwr => ⟨scR S s₀, by simp [hwr, hp.wr], hp.scr_in hd⟩
  have fw : ∀ {m : Mem}, Frame [scR S s₀] s₀.mem m → ∀ d, d + 4 ≤ S → ∀ v : BitVec 32,
      Frame [scR S s₀] s₀.mem (m.writeW (addr (scr s₀) d) v) :=
    fun hf d hd v => hf.writeW (List.mem_singleton_self _) _ (hp.scr_in hd)
  simp only [List.cons_append, save_eq, List.nil_append]
  refine WP.seq ?_
  refine wp_movm (a := addr (esp₀ s₀) 20) (ea_at _ _ _) (ain 20 (by omega) (by omega) s₀ rfl rfl) fun s₁ u₁ => ?_
  have e₁ : s₁.gpr .eax = scr s₀ := u₁.gpr
  refine wp_store (a := addr (scr s₀) P.so) (by rw [ea_at, e₁]) (sout P.so (by omega) _ u₁.wr) fun s₂ u₂ => ?_
  refine wp_store (a := addr (scr s₀) (P.so + 4)) (by rw [ea_at, u₂.gpr, e₁])
    (sout (P.so + 4) (by omega) _ (by rw [u₂.wr, u₁.wr])) fun s₃ u₃ => ?_
  refine wp_store (a := addr (scr s₀) (P.so + 8)) (by rw [ea_at, u₃.gpr, u₂.gpr, e₁])
    (sout (P.so + 8) (by omega) _ (by rw [u₃.wr, u₂.wr, u₁.wr])) fun s₄ u₄ => ?_
  refine wp_store (a := addr (scr s₀) (P.so + 12)) (by rw [ea_at, u₄.gpr, u₃.gpr, u₂.gpr, e₁])
    (sout (P.so + 12) (by omega) _ (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr])) fun s₅ u₅ => ?_
  have g₅ : s₅.gpr = s₁.gpr := by rw [u₅.gpr, u₄.gpr, u₃.gpr, u₂.gpr]
  have rd₅ : s₅.rd = s₀.rd := by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have wr₅ : s₅.wr = s₀.wr := by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  have sp₅ : s₅.gpr .esp = esp₀ s₀ := by rw [g₅, u₁.other _ (by decide)]
  have m₅ : s₅.mem = (((s₀.mem.writeW (addr (scr s₀) P.so) (s₀.gpr .ebx)).writeW (addr (scr s₀) (P.so + 4))
      (s₀.gpr .esi)).writeW (addr (scr s₀) (P.so + 8)) (s₀.gpr .edi)).writeW (addr (scr s₀) (P.so + 12))
      (s₀.gpr .ebp) := by
    rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₄.gpr, u₃.gpr, u₂.gpr, u₁.mem, u₁.other .ebx (by decide),
      u₁.other .esi (by decide), u₁.other .edi (by decide), u₁.other .ebp (by decide)]
  have f₅ : Frame [scR S s₀] s₀.mem s₅.mem := by
    rw [m₅]; exact fw (fw (fw (fw (Frame.refl _ _) P.so (by omega) _) (P.so + 4) (by omega) _) (P.so + 8)
      (by omega) _) (P.so + 12) (by omega) _
  refine wp_mov fun s₆ u₆ => wp_movm (a := addr (esp₀ s₀) 4) (by rw [ea_at, u₆.other _ (by decide), sp₅])
    (ain 4 (by omega) (by omega) s₆ (by rw [u₆.rd, rd₅]) (by rw [u₆.wr, wr₅])) fun s₇ u₇ => ?_
  have ebp₇ : s₇.gpr .ebp = scr s₀ := by rw [u₇.other _ (by decide), u₆.gpr, g₅, e₁]
  have sp₇ : s₇.gpr .esp = esp₀ s₀ := by rw [u₇.other _ (by decide), u₆.other _ (by decide), sp₅]
  have ebx₇ : s₇.gpr .ebx = st s₀ := by
    rw [u₇.gpr, u₆.mem, arg_read hp f₅ (by omega) (by omega)]; rfl
  have rd₇ : s₇.rd = s₀.rd := by rw [u₇.rd, u₆.rd, rd₅]
  have wr₇ : s₇.wr = s₀.wr := by rw [u₇.wr, u₆.wr, wr₅]
  have m₇ : s₇.mem = s₅.mem := by rw [u₇.mem, u₆.mem]
  -- `count` and `out` into scratch.
  refine wp_movm (a := addr (esp₀ s₀) 8) (by rw [ea_at, sp₇]) (ain 8 (by omega) (by omega) s₇ rd₇ wr₇)
    fun s₈ u₈ => ?_
  refine wp_store (a := addr (scr s₀) (P.so + 16)) (by rw [ea_at, u₈.other _ (by decide), ebp₇])
    (sout (P.so + 16) (by omega) _ (by rw [u₈.wr, wr₇])) fun s₉ u₉ => ?_
  have v₉ : s₉.mem = s₅.mem.writeW (addr (scr s₀) (P.so + 16)) (arg s₀ 1) := by
    rw [u₉.mem, u₈.gpr, u₈.mem, m₇, arg_read hp f₅ (by omega) (by omega)]; rfl
  have f₉ : Frame [scR S s₀] s₀.mem s₉.mem := by rw [v₉]; exact fw f₅ (P.so + 16) (by omega) _
  refine wp_movm (a := addr (esp₀ s₀) 12) (by rw [ea_at, u₉.gpr, u₈.other _ (by decide), sp₇])
    (ain 12 (by omega) (by omega) _ (by rw [u₉.rd, u₈.rd, rd₇]) (by rw [u₉.wr, u₈.wr, wr₇])) fun s₁₀ u₁₀ => ?_
  refine wp_store (a := addr (scr s₀) (P.so + 20)) (by rw [ea_at, u₁₀.other _ (by decide), u₉.gpr,
    u₈.other _ (by decide), ebp₇]) (sout (P.so + 20) (by omega) _ (by rw [u₁₀.wr, u₉.wr, u₈.wr, wr₇]))
    fun s₁₁ u₁₁ => ?_
  have v₁₁ : s₁₁.mem = s₉.mem.writeW (addr (scr s₀) (P.so + 20)) (arg s₀ 2) := by
    rw [u₁₁.mem, u₁₀.gpr, u₁₀.mem, arg_read hp f₉ (by omega) (by omega)]; rfl
  have f₁₁ : Frame [scR S s₀] s₀.mem s₁₁.mem := by rw [v₁₁]; exact fw f₉ (P.so + 20) (by omega) _
  have g₁₁ : ∀ r, r ≠ .ecx → s₁₁.gpr r = s₇.gpr r := fun r h => by
    rw [u₁₁.gpr, u₁₀.other r h, u₉.gpr, u₈.other r h]
  refine wp_movm (a := addr (esp₀ s₀) 16) (by rw [ea_at, g₁₁ _ (by decide), sp₇])
    (ain 16 (by omega) (by omega) _ (by rw [u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, rd₇])
      (by rw [u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, wr₇])) fun s₁₂ u₁₂ => ?_
  refine wp_store (a := addr (scr s₀) (P.so + 24)) (by rw [ea_at, u₁₂.other _ (by decide), g₁₁ _ (by decide),
    ebp₇]) (sout (P.so + 24) (by omega) _ (by rw [u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, wr₇])) fun s₁₃ u₁₃ => ?_
  have m₁₃ : s₁₃.mem = proMem P s₀ := by
    rw [u₁₃.mem, u₁₂.gpr, u₁₂.mem, arg_read hp f₁₁ (by omega) (by omega), v₁₁, v₉, m₅]; rfl
  have g₁₃ : ∀ r, r ≠ .ecx → s₁₃.gpr r = s₇.gpr r := fun r h => by rw [u₁₃.gpr, u₁₂.other r h, g₁₁ r h]
  have rd₁₃ : s₁₃.rd = s₀.rd := by rw [u₁₃.rd, u₁₂.rd, u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, rd₇]
  have wr₁₃ : s₁₃.wr = s₀.wr := by rw [u₁₃.wr, u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, wr₇]
  -- The `0x80` byte.
  refine wp_movm (a := addr (esp₀ s₀) 8) (by rw [ea_at, g₁₃ _ (by decide), sp₇])
    (ain 8 (by omega) (by omega) _ rd₁₃ wr₁₃) fun s₁₄ u₁₄ => wp_andi fun s₁₅ u₁₅ => ?_
  have edi₁₅ : s₁₅.gpr .edi = BitVec.ofNat 32 (cnt s₀ % 64) := by
    rw [u₁₅.gpr, u₁₄.gpr, m₁₃, arg_read hp (proMem_frame hd hp) (by omega) (by omega), and63, cnt_mod]
    rfl
  refine wp_mov fun s₁₆ u₁₆ => wp_add fun s₁₇ u₁₇ => wp_movi fun s₁₈ u₁₈ => ?_
  have edx₁₈ : s₁₈.gpr .edx = st s₀ + BitVec.ofNat 32 (cnt s₀ % 64) := by
    rw [u₁₈.other _ (by decide), u₁₇.gpr, u₁₆.gpr, u₁₆.other _ (by decide), edi₁₅, u₁₅.other _ (by decide),
      u₁₄.other _ (by decide), g₁₃ _ (by decide), ebx₇]
  have hq : addr (s₁₈.gpr .edx) P.N = buf P s₀ + BitVec.ofNat 64 (cnt s₀ % 64) := by
    rw [edx₁₈, addr_add_ofNat (by omega), buf_add, Nat.add_comm]
  have hout : InRegions s₁₈.wr (buf P s₀ + BitVec.ofNat 64 (cnt s₀ % 64)) 1 :=
    ⟨stR P s₀, by simp [u₁₈.wr, u₁₇.wr, u₁₆.wr, u₁₅.wr, u₁₄.wr, wr₁₃, hp.wr], by
      rw [buf_add]; exact contains_offset (by omega) (by omega)⟩
  refine wp_store8 (r := .cl) (a := buf P s₀ + BitVec.ofNat 64 (cnt s₀ % 64)) (by rw [ea_at, hq]) hout
    fun s₁₉ u₁₉ => wp_addi fun s₂₀ u₂₀ => wp_movi fun s₂₁ u₂₁ => wp_cmpi fun s₂₂ f₂₂ cf₂₂ _ => WP.block_nil ?_
  have hm₁₉ : s₁₉.mem = writeBytes (proMem P s₀) (buf P s₀ + BitVec.ofNat 64 (cnt s₀ % 64)) [0x80] := by
    rw [u₁₉.mem, show Reg8.cl.reg = Reg.ecx from rfl, u₁₈.gpr, u₁₈.mem, u₁₇.mem, u₁₆.mem, u₁₅.mem, u₁₄.mem, m₁₃,
      ← List.nil_append [(0x80 : Byte)], writeBytes_snoc _ _ _ _ (by simp), writeBytes_nil]
    simp
  have hm₂₂ : s₂₂.mem = s₁₉.mem := by rw [f₂₂.mem, u₂₁.mem, u₂₀.mem]
  have hfb : Frame [stR P s₀] (proMem P s₀) s₁₉.mem := by rw [hm₁₉]; exact buf_frame hd _ (by simp; omega)
  have keep : ∀ r, r ≠ .ecx → r ≠ .edi → r ≠ .edx → r ≠ .esi → s₂₂.gpr r = s₇.gpr r := fun r h1 h2 h3 h4 => by
    rw [f₂₂.gpr, u₂₁.other r h4, u₂₀.other r h2, u₁₉.gpr, u₁₈.other r h1, u₁₇.other r h3, u₁₆.other r h3,
      u₁₅.other r h2, u₁₄.other r h2, g₁₃ r h1]
  obtain ⟨hsv, hlo, hhi, hou⟩ := proMem_words hd hp
  have word : ∀ d, d + 4 ≤ S → s₂₂.mem.readW (addr (scr s₀) d) 32 = (proMem P s₀).readW (addr (scr s₀) d) 32 :=
    fun d hd => by
      rw [hm₂₂]
      exact hfb.readW (Region.contains_self _ _) (by simpa using hp.st_scr.symm.sub_left (hp.scr_sub hd))
        (by decide)
  have hC : Common P S s₀ s₂₂ :=
    ⟨by rw [f₂₂.rd, u₂₁.rd, u₂₀.rd, u₁₉.rd, u₁₈.rd, u₁₇.rd, u₁₆.rd, u₁₅.rd, u₁₄.rd, rd₁₃],
      by rw [f₂₂.wr, u₂₁.wr, u₂₀.wr, u₁₉.wr, u₁₈.wr, u₁₇.wr, u₁₆.wr, u₁₅.wr, u₁₄.wr, wr₁₃],
      by rw [keep _ (by decide) (by decide) (by decide) (by decide), ebx₇],
      by rw [keep _ (by decide) (by decide) (by decide) (by decide), ebp₇],
      by rw [keep _ (by decide) (by decide) (by decide) (by decide), sp₇],
      by rw [hm₂₂]; exact ((proMem_frame hd hp).mono (by simp)).trans (hfb.mono (by simp)),
      fun p hp' => by
        have hd' := saved_offset hp'
        rw [word _ (by omega)]; exact hsv p hp',
      by rw [word _ (by omega)]; exact hlo, by rw [word _ (by omega)]; exact hhi,
      by rw [word _ (by omega)]; exact hou⟩
  have edi₂₂ : s₂₂.gpr .edi = BitVec.ofNat 32 (cnt s₀ % 64 + 1) := by
    rw [f₂₂.gpr, u₂₁.other _ (by decide), u₂₀.gpr, u₁₉.gpr, u₁₈.other _ (by decide), u₁₇.other _ (by decide),
      u₁₆.other _ (by decide), edi₁₅, ofNat_succ]
  have hcf : s₂₂.cf = some (decide (cnt s₀ % 64 + 1 < 57)) := by
    rw [cf₂₂, ← f₂₂.gpr, edi₂₂, toNat_ofNat_lt (by omega)]; rfl
  -- The facts about the buffer.
  have hst' : H.stateAt s₂₂.mem (stA s₀) = H.stateAt s₀.mem (stA s₀) := by
    apply H.stateAt_congr
    intro i hi
    rw [hm₂₂, hm₁₉, buf_add, writeBytes_before _ _ _ (by omega) (by simp; omega)]
    exact frame_bytes (proMem_frame hd hp) (R := stR P s₀) (by simpa using hp.st_scr) (by simp; omega)
      (by show i < P.N + 64; omega)
  have hbytes : ∀ iv m, R₀ H s₀ iv m →
      bytesAt s₂₂.mem (buf P s₀) (cnt s₀ % 64 + 1) = MdStream.Md.rest 64 m ++ [0x80] := by
    intro iv m hm
    have e := bytesAt_writeBytes (proMem P s₀) (buf P s₀) (cnt s₀ % 64) [0x80] (by simp; omega)
    simp only [List.length_singleton] at e
    rw [hm₂₂, hm₁₉, e]
    refine congrArg (· ++ [0x80]) ?_
    rw [hm.length]
    refine (bytesAt_congr ?_).trans hm.1.2
    intro i hi
    rw [buf_add]
    exact frame_bytes (proMem_frame hd hp) (R := stR P s₀) (by simpa using hp.st_scr) (by simp; omega)
      (by show P.N + i < P.N + 64; have := hm.length; omega)
  have hesi : s₂₂.gpr .esi = 0 := by rw [f₂₂.gpr, u₂₁.gpr]
  refine WP.ite (!decide (cnt s₀ % 64 + 1 < 57)) (by show s₂₂.cf.map (!·) = _; rw [hcf]; rfl)
    (fun hb => ?_) (fun hb => ?_)
  · simp only [Bool.not_eq_true', decide_eq_false_iff_not, Nat.not_lt] at hb
    refine wp_movi fun s₂₃ u₂₃ => WP.block_nil ⟨1, hC.of_gpr (fun r hr => u₂₃.other r (regs3 hr).2.2.2.2)
      u₂₃.mem u₂₃.rd u₂₃.wr, (Nat.le_refl _), by omega, by rw [u₂₃.other _ (by decide), edi₂₂], by rw [u₂₃.gpr]; rfl,
      fun iv m hm _ => ?_⟩
    simp only [↓reduceIte]
    rw [H.hash_two (by omega) (by omega) (by rw [← hm.length]; omega), Fin1, u₂₃.mem, hbytes iv m hm, hst',
      hm.1.1, ← hm.length, show 64 - (cnt s₀ % 64 + 1) = 64 - 1 - cnt s₀ % 64 by omega]
  · simp only [Bool.not_eq_false', decide_eq_true_eq] at hb
    refine WP.block_nil ⟨0, hC, by omega, by omega, edi₂₂, by rw [hesi]; rfl, fun iv m hm _ => ?_⟩
    simp only [show ((0 : Nat) = 1) = False by decide, ite_false]
    rw [H.hash_one (by omega) (by rw [← hm.length]; omega), Fin0, hbytes iv m hm, hst', hm.1.1,
      ← hm.length, show 64 - 8 - (cnt s₀ % 64 + 1) = 64 - 8 - 1 - cnt s₀ % 64 by omega]

/-! ## Output and epilogue -/

theorem finalize_eq {name : String} {code : Prog isa} : finalize P name code =
    .seq (.block (([.mov .eax (.mem (at_ .esp 20))] : List Instr) ++ save P .eax ++
      ([.mov .ebp (.reg .eax), .mov .ebx (.mem (at_ .esp 4)),
       .mov .ecx (.mem (at_ .esp 8)), .store (at_ .ebp (P.so + 16)) .ecx,
       .mov .ecx (.mem (at_ .esp 12)), .store (at_ .ebp (P.so + 20)) .ecx,
       .mov .ecx (.mem (at_ .esp 16)), .store (at_ .ebp (P.so + 24)) .ecx,
       .mov .edi (.mem (at_ .esp 8)), .alu .and .edi (.imm 63),
       .mov .edx (.reg .ebx), .alu .add .edx (.reg .edi), .mov .ecx (.imm 0x80),
       .store8 (at_ .edx P.N) .cl, .alu .add .edi (.imm 1),
       .mov .esi (.imm 0), .alu .cmp .edi (.imm 57)] : List Instr)))
    (.seq (.ite .ae (.block [.mov .esi (.imm 1)]) (.block []))
    (.seq (.loop (finalizeBody P name code) .e)
      (.block (.mov .eax (.mem (at_ .ebp (P.so + 24))) :: (P.out ++ restore P .ebp))))) := rfl

theorem epilogue_ok (hd : Dims P S) {s₀ : State} (hp : Pre P S s₀) {sD : State} (hD : Done S H s₀ sD) {s : State}
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hkeep : ∀ r ∈ [Reg.ebx, .ebp, .esp], s.gpr r = sD.gpr r)
    (hm : s.mem = writeBytes sD.mem (outA s₀) (H.digest (H.stateAt sD.mem (stA s₀)))) :
    WP isa (.block (restore P .ebp)) s fun s' => abiPreserved s₀ s' ∧ (finK H S).post s₀ s' := by
  have hC := hD.1
  have := hd.N; have := hd.so
  have hdl := H.digest_length (H.stateAt sD.mem (stA s₀))
  have hfo : Frame [outR P s₀] sD.mem (writeBytes sD.mem (outA s₀) (H.digest (H.stateAt sD.mem (stA s₀)))) :=
    writeBytes_frame _ _ _ (by
      rw [show outA s₀ = outA s₀ + BitVec.ofNat 64 0 by simp]
      exact contains_offset (by omega) (by omega))
  have hebp : s.gpr .ebp = scr s₀ := by rw [hkeep _ (by simp), hC.ebp]
  have rin : ∀ d, d + 4 ≤ S → InRegions (s.rd ++ s.wr) (addr (scr s₀) d) 4 :=
    fun d hd => ⟨scR S s₀, by simp [hrd, hwr, hp.wr], hp.scr_in hd⟩
  have sv : ∀ p ∈ saved P, s.mem.readW (addr (scr s₀) p.2) 32 = s₀.gpr p.1 := by
    intro p hp'
    have hd' := saved_offset hp'
    rw [hm, hfo.readW (r := ⟨addr (scr s₀) p.2, 4⟩) (Region.contains_self _ _)
      (by simpa using hp.out_scr.symm.sub_left (hp.scr_sub (by omega))) (by decide)]
    exact hC.saved p hp'
  rw [restore_eq]
  refine wp_movm (a := addr (scr s₀) P.so) (by rw [ea_at, hebp]) (rin P.so (by omega)) fun s₁ u₁ => ?_
  refine wp_movm (a := addr (scr s₀) (P.so + 4)) (by rw [ea_at, u₁.other _ (by decide), hebp])
    (by rw [u₁.rd, u₁.wr]; exact rin (P.so + 4) (by omega)) fun s₂ u₂ => ?_
  refine wp_movm (a := addr (scr s₀) (P.so + 8)) (by rw [ea_at, u₂.other _ (by decide), u₁.other _ (by decide), hebp])
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact rin (P.so + 8) (by omega)) fun s₃ u₃ => ?_
  refine wp_movm (a := addr (scr s₀) (P.so + 12))
    (by rw [ea_at, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hebp])
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact rin (P.so + 12) (by omega)) fun s₄ u₄ => WP.block_nil ?_
  have hm₄ : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  refine ⟨⟨fun r hr => ?_, ?_⟩, fun iv m hm' hok hc => ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
      exact sv (.ebx, P.so) (by simp [saved])
    · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.mem]
      exact sv (.esi, P.so + 4) (by simp [saved])
    · rw [u₄.other _ (by decide), u₃.gpr, u₂.mem, u₁.mem]
      exact sv (.edi, P.so + 8) (by simp [saved])
    · rw [u₄.gpr, u₃.mem, u₂.mem, u₁.mem]
      exact sv (.ebp, P.so + 12) (by simp [saved])
    · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide),
        hkeep _ (by simp), hC.esp]
  · rw [hm₄, hm, hfo.readW (r := retR s₀) (Region.contains_self _ _) (by simpa using hp.ret_out) (by decide)]
    refine hC.frame.readW (r := retR s₀) (Region.contains_self _ _) ?_ (by decide)
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    exacts [hp.ret_st, hp.ret_scr, hp.ret_a, hp.ret_stk]
  · have e := bytesAt_writeBytes sD.mem (outA s₀) 0 (H.digest (H.stateAt sD.mem (stA s₀))) (by omega)
    rw [hdl, show outA s₀ + BitVec.ofNat 64 0 = outA s₀ by simp, Nat.zero_add,
      show bytesAt sD.mem (outA s₀) 0 = [] from rfl, List.nil_append] at e
    show bytesAt s₄.mem (outA s₀) P.N = _
    rw [hm₄, hm, e, hD.2 iv m ⟨hm', hc⟩ hok]

theorem correct (hd : Dims P S) (hs : Shape H) {name : String} {code : Prog isa} (hf : CalleeOk H code)
    {s₀ : State} (hp : Pre P S s₀) :
    WP isa (finalize P name code) s₀ fun s' => abiPreserved s₀ s' ∧ (finK H S).post s₀ s' := by
  have := hd.N; have hst := hp.st_fit; have ho := hp.out_fit
  rw [finalize_eq, ← seq_assoc]
  refine WP.seq (WP.mono (prologue_ok (H := H) hd hp) fun s₁ ⟨k, hL⟩ => ?_)
  refine WP.seq (WP.mono (Q := Done S H s₀) ?_ fun sD hD => ?_)
  · refine WP.loop (M := isa) (fun i s => ∃ n, LInv S H s₀ i n s) ?_ k s₁ ⟨_, hL⟩
    rintro i s ⟨n, hL⟩
    refine WP.mono (body_ok hd hs hf hp hL) fun s' h => ?_
    rcases h with ⟨he, hD⟩ | ⟨he, rfl, hL'⟩
    · exact .inl ⟨he, hD⟩
    · exact .inr ⟨he, 0, by omega, 0, hL'⟩
  · have hC := hD.1
    refine wp_movm (a := addr (scr s₀) (P.so + 24)) (by rw [ea_at, hC.ebp])
      ⟨scR S s₀, by simp [hC.rd, hC.wr, hp.wr], hp.scr_in (by have := hd.so; omega)⟩ fun s₁ u₁ => ?_
    have heax : s₁.gpr .eax = out s₀ := by rw [u₁.gpr, hC.outp]
    have hebx : s₁.gpr .ebx = st s₀ := by rw [u₁.other _ (by decide), hC.ebx]
    rw [WP.block_append_iff]
    refine WP.mono (hs.out s₁ (by rw [hebx]; omega) (by rw [heax]; exact ho) ?_ ?_ ?_) fun s ⟨g, rd, wr, m⟩ =>
      epilogue_ok hd hp hD (by rw [rd, u₁.rd, hC.rd]) (by rw [wr, u₁.wr, hC.wr])
        (fun r hr => by rw [g r (regs3 hr).2.1, u₁.other r (regs3 hr).1]) (by rw [m, heax, hebx, u₁.mem])
    · refine ⟨stR P s₀, by simp [u₁.rd, u₁.wr, hC.rd, hC.wr, hp.wr, hp.rd], ?_⟩
      rw [hebx]; simpa using contains_offset (base := stA s₀) (off := 0) (n := P.N) (len := P.N + 64)
        (by omega) (by omega)
    · refine ⟨outR P s₀, by simp [u₁.wr, hC.wr, hp.wr], ?_⟩
      rw [heax]; simpa using contains_offset (base := outA s₀) (off := 0) (n := P.N) (len := P.N)
        (by omega) (by omega)
    · rw [hebx, heax]
      exact hp.st_out.sub_left (Region.sub_prefix (by omega))

end

/-! ## Constant time -/

/-- The initial taint: `esp + 4` is the base of the (public) arguments, whose
words at offsets 0, 12 and 16 are the base addresses of `state`, `out` and
`scratch`, and the 20 bytes below `esp` are outside the writable regions. -/
def τ₀ (P : Params) (S : Nat) : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [P.N + 64, P.N, S, 20], bases := [(.esp, 3, 4)],
    slots := [(3, 0, 20)], wbases := [(3, 0, 0), (3, 12, 1), (3, 16, 2)], room := 20 }

section
variable {P : Params} {S : Nat} {H : Md 64 P.N 8}

theorem wf₀ (hd : Dims P S) {s : State} (h : (finK H S).pre s) : VG.X86.Taint.Wf (τ₀ P S) s := by
  have hp := pre_of h
  have hst := hp.st_fit; have ho := hp.out_fit; have hsc := hp.scr_fit; have hs := hp.sp_fit
  have hlo := hp.sp_lo; have := hd.N
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, k1, k2, k3, -⟩ := h
  refine VG.X86.Taint.Wf.entryRoom rfl ⟨fun _ => ⟨by simp [hp.wr, τ₀], ?_, ?_⟩, ?_, ?_,
    fun h => absurd h (Nat.lt_irrefl 0), fun _ h => (List.not_mem_nil h).elim⟩ fun _ => ⟨hlo, ?_⟩
  · simp only [hp.wr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, List.Pairwise.nil, and_true]
    exact ⟨⟨hp.st_out, hp.st_scr, hp.a_st.symm⟩, ⟨hp.out_scr, hp.a_out.symm⟩, hp.a_scr.symm, fun _ h => h.elim⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · simp only [addr_toNat]; omega
    · simp only [addr_toNat]; omega
    · simp only [addr_toNat]; omega
    · simp only; rw [addr_eq (by omega), BitVec.toNat_add, addr_toNat, BitVec.toNat_ofNat]; omega
  · intro p hp'
    simp only [τ₀, List.mem_singleton] at hp'
    subst hp'
    simp [VG.X86.Taint.region, hp.wr]
  · intro p hp'
    simp only [τ₀, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl | rfl
    · refine ⟨by simp [τ₀], ?_⟩
      simp only [VG.X86.Taint.byteAddr, VG.X86.Taint.region, hp.wr]
      show addr (s.mem.readW (addr (esp₀ s) 4 + BitVec.ofNat 64 0) 32) 0 = stA s
      simp [addr, st, arg, argAddr]
    · refine ⟨by simp [τ₀], ?_⟩
      simp only [VG.X86.Taint.byteAddr, VG.X86.Taint.region, hp.wr]
      show addr (s.mem.readW (addr (esp₀ s) 4 + BitVec.ofNat 64 12) 32) 0 = outA s
      rw [argWord_eq (n := 20) (by omega) (k := 12) (by omega)]
      simp [addr, out, arg]
    · refine ⟨by simp [τ₀], ?_⟩
      simp only [VG.X86.Taint.byteAddr, VG.X86.Taint.region, hp.wr]
      show addr (s.mem.readW (addr (esp₀ s) 4 + BitVec.ofNat 64 16) 32) 0 = scA s
      rw [argWord_eq (n := 20) (by omega) (k := 16) (by omega)]
      simp [addr, scr, arg]
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact k1
    · exact k2
    · exact k3
    · intro a h₁ h₂
      simp only [Region.Contains, τ₀] at h₁ h₂
      rw [addr_eq (by omega)] at h₂
      have hE : ((esp₀ s).setWidth 64).toNat = (esp₀ s).toNat := addr_toNat _
      generalize (esp₀ s).setWidth 64 = b at *
      bv_omega

theorem agree₀ (hd : Dims P S) {s₁ s₂ : State} (h₁ : (finK H S).pre s₁) (h₂ : (finK H S).pre s₂)
    (hpub : (finK H S).pub s₁ s₂) : VG.X86.Taint.Agree (τ₀ P S) s₁ s₂ := by
  obtain ⟨hesp, ha⟩ := hpub
  have hp₁ := pre_of h₁; have hp₂ := pre_of h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, wf₀ hd h₁, wf₀ hd h₂, ?_, ?_,
    fun h => absurd h (Nat.lt_irrefl 0), fun _ _ h => absurd h (Nat.not_lt_zero _)⟩
  · simp only [τ₀, RegSet.mem_ofList, List.mem_singleton] at hr
    subst hr; exact hesp
  · rw [hp₁.wr, hp₂.wr]
    simp only [stR, outR, scR, argR, stA, outA, scA, st, out, scr, esp₀, ha 0 (by omega), ha 3 (by omega),
      ha 4 (by omega), hesp]
  · intro sl hsl
    simp only [τ₀, List.mem_singleton] at hsl
    subst hsl; simp [τ₀]
  · intro sl hsl k _ hk
    simp only [τ₀, List.mem_singleton] at hsl
    subst hsl
    simp only [Nat.zero_add] at hk
    simp only [VG.X86.Taint.byteAddr, VG.X86.Taint.region, hp₁.wr, hp₂.wr]
    show s₁.mem (addr (esp₀ s₁) 4 + BitVec.ofNat 64 k) = s₂.mem (addr (esp₀ s₂) 4 + BitVec.ofNat 64 k)
    rw [argWord_eq (n := 20) (by have := hp₁.sp_fit; omega) hk, argWord_eq (n := 20) (by have := hp₂.sp_fit; omega) hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega))]
    exact congrArg _ (ha _ (by omega))

end

/-- Memory holding the arguments `0x1000, 0, 0, 0x2000, 0x3000` at `0x5004`. -/
def satMem : Mem := fun a =>
  if a = 0x5005 then 0x10 else if a = 0x5011 then 0x20 else if a = 0x5015 then 0x30 else 0

/-- The registers and memory of a state satisfying the precondition. -/
def sat₀ : State where
  gpr r := match r with
    | .esp => 0x5000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMem
  rd := []
  wr := []

/-- A state satisfying the precondition. -/
def sat (P : Params) (S : Nat) : State :=
  { sat₀ with wr := [⟨0x1000, P.N + 64⟩, ⟨0x2000, P.N⟩, ⟨0x3000, S⟩, ⟨0x5004, 20⟩] }

section
variable {P : Params} {S : Nat} {H : Md 64 P.N 8}

theorem sat_pre (hd : Dims P S) : (finK H S).pre (sat P S) := by
  have := hd.N; have := hd.S
  have a0 : arg (sat P S) 0 = 0x1000 := show arg sat₀ 0 = _ by decide
  have a3 : arg (sat P S) 3 = 0x2000 := show arg sat₀ 3 = _ by decide
  have a4 : arg (sat P S) 4 = 0x3000 := show arg sat₀ 4 = _ by decide
  have e : argAddr (sat P S) 0 = 0x5004 := show argAddr sat₀ 0 = _ by decide
  have hsp : (sat P S).gpr .esp = 0x5000 := rfl
  simp only [finK, a0, a3, a4, e, hsp]
  have hs : ((0x5000 : BitVec 32).setWidth 64 - 20 : Addr) = 0x4FEC := by decide
  simp only [hs]
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by simp; omega, by simp; omega,
    by simp; omega, by decide, by decide⟩ <;>
  · first
    | exact Offset.disjoint_of_le (by simp only [BitVec.toNat_setWidth, BitVec.reduceToNat]; omega)
        (by simp only [BitVec.toNat_setWidth, BitVec.reduceToNat]; omega)
    | exact (Offset.disjoint_of_le (by simp only [BitVec.toNat_setWidth, BitVec.reduceToNat]; omega)
        (by simp only [BitVec.toNat_setWidth, BitVec.reduceToNat]; omega)).symm

/-- `finalize` is verified, given that it is constant time (by the taint analysis of each hash
function's code, from `τ₀` and `agree₀`). -/
theorem verified (hd : Dims P S) (hs : Shape H) {name : String} {code : Prog isa} (hf : CalleeOk H code)
    (hct : ConstantTime isa (finK H S).pre (finK H S).pub (finalize P name code)) :
    Verified X86.target (finalize P name code) (finK H S) := by
  refine ⟨fun s hs' => ?_, hct, ⟨sat P S, sat_pre hd⟩⟩
  obtain ⟨t, s', he, h⟩ := correct hd hs hf (pre_of hs')
  exact ⟨t, s', he, h⟩

end

end VG.Proof.MdStream.X86.Finalize
