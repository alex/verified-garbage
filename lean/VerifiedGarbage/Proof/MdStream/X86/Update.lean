import VerifiedGarbage.Proof.MdStream.X86.Common
import Mathlib.Tactic.Tauto

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
  simp only [Region.Contains, argAddr]
  rw [show (esp₀ s₀ + BitVec.ofNat 32 (4 + 4 * 0)).setWidth 64 = addr (esp₀ s₀) 4 from rfl,
    addr_eq (by omega), addr_eq (by omega),
    show (esp₀ s₀).setWidth 64 + BitVec.ofNat 64 d - ((esp₀ s₀).setWidth 64 + BitVec.ofNat 64 4) =
      BitVec.ofNat 64 (d - 4) by
      rw [show d = (d - 4) + 4 by omega, BitVec.ofNat_add]; bv_omega,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

/-- A word of the scratch space, as a region. -/
theorem scr_sub {d : Nat} (hd : d + 4 ≤ S) : Region.Sub ⟨addr (scr s₀) d, 4⟩ (scR S s₀) := by
  rw [addr_eq (by have := hp.scr_fit; omega)]
  exact sub_offset hd (by have := hp.scr_fit; omega)

/-- An argument word, as a region. -/
theorem arg_sub {d : Nat} (hd₁ : 4 ≤ d) (hd : d + 4 ≤ 28) : Region.Sub ⟨addr (esp₀ s₀) d, 4⟩ (argR s₀) := by
  have := hp.sp_fit
  intro a ha
  simp only [Region.Contains, argAddr] at ha ⊢
  rw [addr_eq (by omega)] at ha
  rw [show (esp₀ s₀ + BitVec.ofNat 32 (4 + 4 * 0)).setWidth 64 = addr (esp₀ s₀) 4 from rfl, addr_eq (by omega)]
  generalize (esp₀ s₀).setWidth 64 = b at *
  bv_omega

theorem a_stk : (argR s₀).Disjoint (stkR s₀) := by
  have := hp.sp_fit; have := hp.sp_lo
  intro a h₁ h₂
  simp only [Region.Contains, argAddr] at h₁ h₂
  rw [show (esp₀ s₀ + BitVec.ofNat 32 (4 + 4 * 0)).setWidth 64 = addr (esp₀ s₀) 4 from rfl,
    addr_eq (by omega)] at h₁
  rw [Taint.sub_setWidth (by omega)] at h₂
  have hE : ((esp₀ s₀).setWidth 64).toNat = (esp₀ s₀).toNat := addr_toNat _
  generalize (esp₀ s₀).setWidth 64 = b at *
  bv_omega

theorem ret_stk : (retR s₀).Disjoint (stkR s₀) := by
  have := hp.sp_fit; have := hp.sp_lo
  intro a h₁ h₂
  simp only [Region.Contains] at h₁ h₂
  rw [Taint.sub_setWidth (by omega)] at h₂
  have hE : ((esp₀ s₀).setWidth 64).toNat = (esp₀ s₀).toNat := addr_toNat _
  generalize (esp₀ s₀).setWidth 64 = b at *
  bv_omega

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

/-- A whole block is ready at `eax`, and compressing it absorbs the first `c`
bytes of data. -/
structure Pending {P : Params} (S : Nat) (H : Md 64 P.N 8) (s₀ : State) (c : Nat) (s : State) : Prop
    extends Common P S s₀ c s where
  edi : s.gpr .edi = 0
  ecx : s.gpr .ecx = 1
  mod : (cnt s₀ + c) % 64 = 0
  src : s.gpr .eax = st s₀ + BitVec.ofNat 32 P.N ∨
    ∃ c₀, s.gpr .eax = dp s₀ + BitVec.ofNat 32 c₀ ∧ c₀ + 64 ≤ len s₀
  repr : ∀ iv m, R₀ H s₀ iv m → ∀ mem', H.stateAt mem' (stA s₀) =
      H.compress (H.stateAt s.mem (stA s₀)) (H.blockAt s.mem ((s.gpr .eax).setWidth 64)) →
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
  have hsp := hp.sp_fit; have := hd.so; have := hd.N
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

/-- A whole block straight from the data. -/
theorem direct_ok {s₀ : State} (hp : Pre P S s₀) {c : Nat} {s : State} (hI : Inv S H s₀ c s)
    (hr : (cnt s₀ + c) % 64 = 0) (hl : 64 ≤ len s₀ - c) :
    WP isa (.block direct) s (Pending S H s₀ (c + 64)) := by
  have hd := hp.d_fit; have hlen := len_lt s₀; have hc := hI.c_le
  unfold direct
  refine wp_mov fun s₂ u₂ => wp_addi fun s₃ u₃ => wp_subi fun s₄ u₄ _ => wp_movi fun s₅ u₅ => WP.block_nil ?_
  have g : ∀ r, r ≠ .ecx → r ≠ .esi → r ≠ .ebp → r ≠ .eax → s₅.gpr r = s.gpr r :=
    fun r h1 h2 h3 h4 => by rw [u₅.other r h1, u₄.other r h2, u₃.other r h3, u₂.other r h4]
  have hm : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem]
  have heax : s₅.gpr .eax = dp s₀ + BitVec.ofNat 32 c := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, hI.ebp]
  refine ⟨⟨by omega, by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, hI.rd], by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, hI.wr],
      by rw [g _ (by decide) (by decide) (by decide) (by decide), hI.ebx],
      by rw [g _ (by decide) (by decide) (by decide) (by decide), hI.esp], ?_, ?_,
      by rw [hm]; exact hI.frame, by rw [hm]; exact hI.saved⟩,
    by rw [g _ (by decide) (by decide) (by decide) (by decide), hI.edi, hr]; rfl,
    by rw [u₅.gpr], by omega, .inr ⟨c, heax, by omega⟩, fun iv m hm₀ mem' hs => ?_⟩
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), hI.ebp, lit32,
      ofNat_add_add]
  · rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), hI.esi, lit32,
      sub_ofNat hl, Nat.sub_sub]
  · have hmod := length_mid s₀ hm₀ (c := c) (by omega)
    rw [← take_add_data]
    refine H.repr_append_block (by omega) (hI.repr iv m hm₀)
      (by rw [hmod, hr, List.length_take, List.length_drop, D_length]; omega) ?_
    rw [hs, hm, heax, show (dp s₀ + BitVec.ofNat 32 c).setWidth 64 = addr (dp s₀) c from rfl,
      addr_eq (by omega)]
    refine congrArg (H.compress _) ?_
    rw [show (m ++ List.take c (D s₀)).drop (64 * ((m ++ List.take c (D s₀)).length / 64)) = [] by
      rw [List.drop_eq_nil_iff]; omega, List.nil_append]
    apply H.parse_congr
    intro k hk
    rw [show dA s₀ + BitVec.ofNat 64 c + BitVec.ofNat 64 k = dA s₀ + BitVec.ofNat 64 (c + k) by
      simp only [BitVec.ofNat_add]; rw [BitVec.add_assoc], hI.data hp (by omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_drop, hk]

/-! ## Compressing -/

/-- The block to compress. -/
theorem Pending.blk {s₀ : State} (hp : Pre P S s₀) {c : Nat} {s : State} (h : Pending S H s₀ c s) :
    (s.gpr .eax).toNat + 64 ≤ 2 ^ 32 ∧
      ((s.gpr .eax).setWidth 64 = stA s₀ + BitVec.ofNat 64 P.N ∨
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
theorem Pending.blk_sub {s₀ : State} (hp : Pre P S s₀) {c : Nat} {s : State} (h : Pending S H s₀ c s) :
    Region.Sub ⟨(s.gpr .eax).setWidth 64, 64⟩ (stR P s₀) ∨ Region.Sub ⟨(s.gpr .eax).setWidth 64, 64⟩ (dR s₀) := by
  rcases (h.blk hp).2 with he | ⟨c₀, he, hc₀⟩
  · exact .inl (by rw [he]; exact sub_offset (by omega) (by have := hp.st_fit; omega))
  · exact .inr (by rw [he]; exact sub_offset hc₀ (by have := len_lt s₀; omega))

/-- The call of the compression function, once `edx` holds `scratch`. -/
theorem Pending.compress_ok (hd : Dims P S) {name : String} {code : Prog isa} (hf : CalleeOk H code)
    {s₀ : State} (hp : Pre P S s₀) {c : Nat} {s s₁ : State} (h : Pending S H s₀ c s)
    (u : Upd s s₁ .edx (scr s₀)) : WP isa (compressAt name code .ebx .edx) s₁ (Inv S H s₀ c) := by
  have hst := hp.st_fit; have hsc := hp.scr_fit; have hsp := hp.sp_fit; have := hd.so; have := hd.N
  obtain ⟨hbf, hb⟩ := h.blk hp
  have hbs := h.blk_sub hp
  have eN : Region.Sub ⟨stA s₀, P.N⟩ (stR P s₀) := Region.sub_prefix (by omega)
  have eso : Region.Sub ⟨scA s₀, P.so⟩ (scR S s₀) := Region.sub_prefix (by omega)
  refine compressAt_ok hf (st := st s₀) (scr := scr s₀) (blk := s.gpr .eax) (E := esp₀ s₀)
    (by decide) (by decide) (by decide) (by decide) (by rw [u.other _ (by decide), h.esp])
    (by rw [u.other _ (by decide), h.ebx]) u.gpr (u.other _ (by decide)) hp.sp_lo (by omega) hbf (by omega)
    ((hp.st_scr.sub_left eN).sub_right eso) ?_ ?_ (hp.stk_st.sub_right eN) (hp.stk_scr.sub_right eso)
    ?_ ?_ ?_ ?_
  · rcases hb with he | ⟨c₀, he, hc₀⟩
    · rw [he]; intro a h₁ h₂; simp only [Region.Contains] at h₁ h₂; bv_omega
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
    rcases hb with he | ⟨c₀, he, hc₀⟩
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
        · intro a h₁ h₂
          simp only [Region.Contains] at h₁ h₂
          rw [addr_eq (by omega)] at h₁
          generalize scA s₀ = b at *
          bv_omega
        · exact hp.stk_scr.symm.sub_left (hp.scr_sub (by omega))

theorem Pending.congr {s₀ : State} {c : Nat} {s s' : State} (h : Pending S H s₀ c s) (hg : s'.gpr = s.gpr)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Pending S H s₀ c s' :=
  { h.toCommon.of_gpr (fun r _ => by rw [hg]) hm hrd hwr with
    edi := by rw [hg]; exact h.edi
    ecx := by rw [hg]; exact h.ecx
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
    (h : (∃ c', c < c' ∧ Pending S H s₀ c' s) ∨ Done S H s₀ s) :
    WP isa (.seq (.block [.alu .test .ecx (.reg .ecx)])
      (.ite .ne (.seq (.block [.mov .edx (.mem (at_ .esp 24))])
          (.seq (compressAt name code .ebx .edx) (.block [.mov .ecx (.imm 1), .alu .test .ecx (.reg .ecx)])))
        (.block []))) s (Step S H s₀ c) := by
  rcases h with ⟨c', hc, hP⟩ | ⟨hI, hecx⟩
  · refine WP.seq (wp_test fun s₂ f₂ z₂ => WP.block_nil ?_)
    have hP₂ : Pending S H s₀ c' s₂ := hP.congr f₂.gpr f₂.mem f₂.rd f₂.wr
    have hz : s₂.zf = some false := by rw [z₂, hP.ecx]; rfl
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
  have hlen := len_lt s₀; have hdf := hp.d_fit; have hst := hp.st_fit; have := hd.N
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
      .mov .ecx (.imm 1)]) s (Pending S H s₀ (c + tt s₀ c)) := by
  have hr := rr_lt s₀ c; have ht := tt_le s₀ c; have ht' := tt_le' s₀ c; have hrr := rr_eq s₀ c
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
    by rw [u₄.other _ (by decide), u₃.gpr], by rw [u₄.gpr], by omega, .inl heax, ?_⟩
  · rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd]
  · rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr]
  · rw [g .ebx (by decide) (by decide) (by decide), h.ebx]
  · rw [g .esp (by decide) (by decide) (by decide), h.esp]
  · rw [g .ebp (by decide) (by decide) (by decide), h.ebp]
  · rw [g .esi (by decide) (by decide) (by decide), h.esi, Nat.sub_sub]
  · intro iv m hm mem' hs
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
  have hr := rr_lt s₀ c; have ht := tt_le s₀ c; have ht' := tt_le' s₀ c
  have hrr := rr_eq s₀ c; have htt := tt_eq s₀ c
  have hxs := xs_length s₀ c
  have hc := hI.c_le
  have htl : tt s₀ c = len s₀ - c := by omega
  obtain ⟨hfr, hsv, hst, hby⟩ := copied_facts hd hp hI
  refine ⟨⟨⟨(Nat.le_refl _), h.rd, h.wr, h.ebx, h.esp, ?_, ?_, by rw [h.mem]; exact hfr,
    by rw [h.mem]; exact hsv⟩, ?_, fun iv m hm => ?_⟩, hecx⟩
  · rw [h.ebp]; congr 2; omega
  · rw [h.esi]; congr 1; omega
  · rw [hedi]; congr 1; omega
  · have hmod := length_mid s₀ hm hc
    rw [show len s₀ = c + tt s₀ c by omega, ← take_add_data]
    refine H.repr_append_buf (hI.repr iv m hm) (by rw [hmod, hxs]; omega) (by rw [h.mem, hst]) ?_
    rw [hmod, hxs, h.mem, hby]
    have hb := (hI.repr iv m hm).2
    rw [hmod] at hb
    rw [hb]

theorem fill_ok (hd : Dims P S) {s₀ : State} (hp : Pre P S s₀) {c : Nat} {s : State} (hI : Inv S H s₀ c s) :
    WP isa (fill P) s fun s' => (∃ c', c < c' ∧ Pending S H s₀ c' s') ∨ Done S H s₀ s' := by
  have hr := rr_lt s₀ c; have ht := tt_le s₀ c; have ht' := tt_le' s₀ c
  have hrr := rr_eq s₀ c; have htt := tt_eq s₀ c
  have hc := hI.c_le; have hlen := len_lt s₀
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
    exact WP.mono (fill_pending hd hp hI hC₁₂ hb) fun s' h => .inl ⟨c + tt s₀ c, by omega, h⟩
  · simp only [decide_eq_false_iff_not] at hb
    exact WP.block_nil (.inr (fill_done hd hp hI hC₁₂ hedi₁₂ hecx hb))

theorem body_ok (hd : Dims P S) {name : String} {code : Prog isa} (hf : CalleeOk H code) {s₀ : State}
    (hp : Pre P S s₀) {c : Nat} {s : State} (hI : Inv S H s₀ c s) :
    WP isa (updateBody P name code) s (Step S H s₀ c) := by
  have hlen := len_lt s₀; have hc := hI.c_le; have hr := rr_lt s₀ c
  unfold updateBody
  refine WP.seq (wp_test fun s₁ f₁ z₁ => WP.block_nil ?_)
  have hI₁ := hI.of_gpr (fun r _ => by rw [f₁.gpr]) f₁.mem f₁.rd f₁.wr
  refine WP.seq (WP.mono (Q := fun s' => (∃ c', c < c' ∧ Pending S H s₀ c' s') ∨ Done S H s₀ s') ?_
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
  exact WP.mono (direct_ok hp hI₂ hb hb') fun s' h => .inl ⟨c + 64, by omega, h⟩

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
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by simp; omega, by decide, by simp; omega,
    by decide, by decide⟩ <;>
  · intro a h₁ h₂
    simp only [Region.Contains] at h₁ h₂
    bv_omega

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
