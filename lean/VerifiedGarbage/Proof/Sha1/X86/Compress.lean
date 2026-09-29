import VerifiedGarbage.Proof.Sha1.X86.Rounds
import VerifiedGarbage.Proof.Sha1.X86.Contract

/-!
# SHA-1 compression function on x86 (32-bit): the whole function

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.Sha1.X86

open VG VG.X86 VG.Impl.Sha1.X86
open VG.Spec.Sha1 (HashValue Word Block W stateAt blockAt compressBlocks compress parseBlock)

theorem ea_at (s : State) (b : Reg) (d : Nat) : s.ea (at_ b d) = addr (s.gpr b) d := rfl

theorem contains_offset {base : Addr} {len off n : Nat} (h : off + n ≤ len) (ho : off < 2 ^ 64) :
    (⟨base, len⟩ : Region).Contains (base + BitVec.ofNat 64 off) n := by
  simp only [Region.Contains]
  rw [show base + BitVec.ofNat 64 off - base = BitVec.ofNat 64 off by bv_omega, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt ho]
  exact h

theorem contains_sub {base : Addr} {len off n : Nat} (h : off + n ≤ len) (ho : off < 2 ^ 64)
    {a : Addr} (ha : a = base + BitVec.ofNat 64 off) : (⟨base, len⟩ : Region).Contains a n := by
  subst ha; exact contains_offset h ho

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev esp₀ : BitVec 32 := s₀.gpr .esp
abbrev st : BitVec 32 := arg s₀ 0
abbrev bp : BitVec 32 := arg s₀ 1
abbrev nb : Nat := (arg s₀ 2).toNat
abbrev scr : BitVec 32 := arg s₀ 3
abbrev stR : Region := ⟨(st s₀).setWidth 64, 20⟩
abbrev blR : Region := ⟨(bp s₀).setWidth 64, 64 * nb s₀⟩
abbrev scrR : Region := ⟨(scr s₀).setWidth 64, 112⟩
abbrev argR : Region := ⟨argAddr s₀ 0, 16⟩
abbrev retR : Region := ⟨(esp₀ s₀).setWidth 64, 4⟩
abbrev H₀ : HashValue := stateAt s₀.mem ((st s₀).setWidth 64)

/-- Block `i`, and where it starts. -/
abbrev blkAddr (i : Nat) : BitVec 32 := bp s₀ + BitVec.ofNat 32 (64 * i)
abbrev blk (i : Nat) : Block := blockAt s₀.mem ((bp s₀).setWidth 64 + BitVec.ofNat 64 (64 * i))

/-- The address of word `k` of the hash value. -/
abbrev stAddr (k : Nat) : Addr := addr (st s₀) (4 * k)

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [blR s₀, argR s₀]
  wr : s₀.wr = [stR s₀, scrR s₀]
  st_scr : (stR s₀).Disjoint (scrR s₀)
  blk_st : (blR s₀).Disjoint (stR s₀)
  blk_scr : (blR s₀).Disjoint (scrR s₀)
  arg_st : (argR s₀).Disjoint (stR s₀)
  arg_scr : (argR s₀).Disjoint (scrR s₀)
  ret_st : (retR s₀).Disjoint (stR s₀)
  ret_scr : (retR s₀).Disjoint (scrR s₀)
  st_fits : (st s₀).toNat + 20 ≤ 2 ^ 32
  blk_fits : (bp s₀).toNat + 64 * nb s₀ ≤ 2 ^ 32
  scr_fits : (scr s₀).toNat + 112 ≤ 2 ^ 32
  esp_fits : (esp₀ s₀).toNat + 20 ≤ 2 ^ 32

theorem pre_of (s₀ : State) (h : Proof.Sha1.compressX86.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩

namespace Pre
variable {s₀ : State} (h : Pre s₀)
include h

theorem stAddr_eq {k : Nat} (hk : k < 5) :
    stAddr s₀ k = (st s₀).setWidth 64 + BitVec.ofNat 64 (4 * k) :=
  addr_eq (by have := h.st_fits; omega)

theorem argAddr_eq {d : Nat} (hd : d < 20) :
    addr (esp₀ s₀) d = (esp₀ s₀).setWidth 64 + BitVec.ofNat 64 d :=
  addr_eq (by have := h.esp_fits; omega)

theorem blkAddr_eq {i t : Nat} (hi : i < nb s₀) (ht : t < 16) :
    addr (blkAddr s₀ i) (4 * t) =
      (bp s₀).setWidth 64 + BitVec.ofNat 64 (64 * i) + BitVec.ofNat 64 (4 * t) := by
  have := h.blk_fits
  rw [addr_eq (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := (bp s₀).isLt; omega)]
  have e : (blkAddr s₀ i).setWidth 64 = (bp s₀).setWidth 64 + BitVec.ofNat 64 (64 * i) := by
    have := addr_eq (x := bp s₀) (k := 64 * i) (by omega)
    simpa only [addr] using this
  rw [e]

theorem scr_eq {d : Nat} (hd : d < 112) :
    addr (scr s₀) d = (scr s₀).setWidth 64 + BitVec.ofNat 64 d :=
  addr_eq (by have := h.scr_fits; omega)

theorem in_scr {d : Nat} (hd : d + 4 ≤ 112) : InRegions (s₀.rd ++ s₀.wr) (addr (scr s₀) d) 4 :=
  ⟨scrR s₀, by simp [h.wr], contains_sub hd (by omega) (h.scr_eq (by omega))⟩

theorem out_scr {d : Nat} (hd : d + 4 ≤ 112) : InRegions s₀.wr (addr (scr s₀) d) 4 :=
  ⟨scrR s₀, by simp [h.wr], contains_sub hd (by omega) (h.scr_eq (by omega))⟩

theorem arg_contains {d : Nat} (hd : 4 ≤ d) (hd' : d + 4 ≤ 20) :
    (argR s₀).Contains (addr (esp₀ s₀) d) 4 := by
  simp only [Region.Contains, argAddr]
  rw [show (esp₀ s₀ + BitVec.ofNat 32 (4 + 4 * 0)).setWidth 64 = addr (esp₀ s₀) 4 from rfl,
    h.argAddr_eq (by omega), h.argAddr_eq (by omega)]
  have := h.esp_fits
  generalize (esp₀ s₀).setWidth 64 = a
  rw [show a + BitVec.ofNat 64 d - (a + BitVec.ofNat 64 4) = BitVec.ofNat 64 (d - 4) by bv_omega,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

theorem in_arg {d : Nat} (hd : 4 ≤ d) (hd' : d + 4 ≤ 20) :
    InRegions (s₀.rd ++ s₀.wr) (addr (esp₀ s₀) d) 4 :=
  ⟨argR s₀, by simp [h.rd], h.arg_contains hd hd'⟩

/-- An argument slot is inside the argument region. -/
theorem arg_sub {i : Nat} (hi : i < 4) : Region.Sub ⟨argAddr s₀ i, 4⟩ (argR s₀) := by
  intro a ha
  simp only [Region.Contains, argAddr] at ha ⊢
  rw [show (esp₀ s₀ + BitVec.ofNat 32 (4 + 4 * 0)).setWidth 64 = addr (esp₀ s₀) 4 from rfl,
    h.argAddr_eq (by omega)]
  rw [show (s₀.gpr .esp + BitVec.ofNat 32 (4 + 4 * i)).setWidth 64 = addr (esp₀ s₀) (4 + 4 * i)
    from rfl, h.argAddr_eq (by omega)] at ha
  generalize (esp₀ s₀).setWidth 64 = b at *
  bv_omega

/-- The arguments are unchanged while only the state and the scratch buffer are written. -/
theorem arg_frame {m : Mem} (hf : Frame [stR s₀, scrR s₀] s₀.mem m) {i : Nat} (hi : i < 4) :
    m.readW (addr (esp₀ s₀) (4 + 4 * i)) 32 = arg s₀ i := by
  refine (hf.readW (r := ⟨argAddr s₀ i, 4⟩) (Region.contains_self _ _) ?_ (by decide))
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨h.arg_st.sub_left (h.arg_sub hi), h.arg_scr.sub_left (h.arg_sub hi)⟩

theorem blk_contains {i t : Nat} (hi : i < nb s₀) (ht : t < 16) :
    (blR s₀).Contains (addr (blkAddr s₀ i) (4 * t)) 4 := by
  have := h.blk_fits
  rw [h.blkAddr_eq hi ht, show (bp s₀).setWidth 64 + BitVec.ofNat 64 (64 * i) + BitVec.ofNat 64 (4 * t) =
    (bp s₀).setWidth 64 + BitVec.ofNat 64 (64 * i + 4 * t) by bv_omega]
  exact contains_offset (by omega) (by omega)

theorem in_blk {i t : Nat} (hi : i < nb s₀) (ht : t < 16) :
    InRegions (s₀.rd ++ s₀.wr) (addr (blkAddr s₀ i) (4 * t)) 4 :=
  ⟨blR s₀, by simp [h.rd], h.blk_contains hi ht⟩

end Pre

theorem st_sep {s₀ : State} (hp : Pre s₀) {d e : Nat} (hd : d + 4 ≤ 20) (he : e + 4 ≤ 20)
    (hde : d + 4 ≤ e ∨ e + 4 ≤ d) : Mem.Sep (addr (st s₀) d) 4 (addr (st s₀) e) 4 := by
  intro x hx hy
  rw [addr_eq (by have := hp.st_fits; omega)] at hx hy
  generalize (st s₀).setWidth 64 = a at *
  bv_omega

/-- Reading the hash value at offset `d` after writing it at offset `e`. -/
theorem readW_writeW_st {s₀ : State} (hp : Pre s₀) (m : Mem) (v : Word) {d e : Nat}
    (hd : d + 4 ≤ 20) (he : e + 4 ≤ 20) (hde : d + 4 ≤ e ∨ e + 4 ≤ d) :
    (m.writeW (addr (st s₀) e) v).readW (addr (st s₀) d) 32 = m.readW (addr (st s₀) d) 32 :=
  Mem.readW_writeW_sep (st_sep hp hd he hde) (by decide)

theorem st_eq {s₀ : State} (hp : Pre s₀) {d : Nat} (hd : d < 20) :
    addr (st s₀) d = (st s₀).setWidth 64 + BitVec.ofNat 64 d :=
  addr_eq (by have := hp.st_fits; omega)

theorem in_st {s₀ : State} (hp : Pre s₀) {d : Nat} (hd : d + 4 ≤ 20) :
    InRegions (s₀.rd ++ s₀.wr) (addr (st s₀) d) 4 :=
  ⟨stR s₀, by simp [hp.wr], contains_sub hd (by omega) (st_eq hp (by omega))⟩

theorem out_st {s₀ : State} (hp : Pre s₀) {d : Nat} (hd : d + 4 ≤ 20) :
    InRegions s₀.wr (addr (st s₀) d) 4 :=
  ⟨stR s₀, by simp [hp.wr], contains_sub hd (by omega) (st_eq hp (by omega))⟩

theorem stateAt_eq {m : Mem} {s₀ : State} (hp : Pre s₀) {v : HashValue}
    (h : ∀ k : Nat, (hk : k < 5) → m.readW (stAddr s₀ k) 32 = v[k]) :
    stateAt m ((st s₀).setWidth 64) = v := by
  apply Vector.ext
  intro k hk
  simp only [stateAt, Vector.getElem_ofFn]
  rw [← hp.stAddr_eq hk]; exact h k hk

theorem stateAt_get {s₀ : State} (hp : Pre s₀) (m : Mem) {k : Nat} (hk : k < 5) :
    (stateAt m ((st s₀).setWidth 64))[k] = m.readW (stAddr s₀ k) 32 := by
  simp only [stateAt, Vector.getElem_ofFn, hp.stAddr_eq hk]

theorem scr_sep {s₀ : State} (hp : Pre s₀) {d e : Nat} (hd : d + 4 ≤ 112) (he : e + 4 ≤ 112)
    (hde : d + 4 ≤ e ∨ e + 4 ≤ d) : Mem.Sep (addr (scr s₀) e) 4 (addr (scr s₀) d) 4 := by
  intro x hx hy
  rw [hp.scr_eq (by omega)] at hx hy
  generalize (scr s₀).setWidth 64 = a at *
  bv_omega

/-- Reading `[scr + e]` after writing `[scr + d]`. -/
theorem readW_writeW_scr {s₀ : State} (hp : Pre s₀) (m : Mem) (x : Word)
    {d e : Nat} (hd : d + 4 ≤ 112) (he : e + 4 ≤ 112) (hde : d + 4 ≤ e ∨ e + 4 ≤ d) :
    (m.writeW (addr (scr s₀) d) x).readW (addr (scr s₀) e) 32 = m.readW (addr (scr s₀) e) 32 :=
  Mem.readW_writeW_sep (scr_sep hp hd he hde) (by decide)

theorem st_scr_sep {s₀ : State} (hp : Pre s₀) {e d : Nat} (he : e + 4 ≤ 20) (hd : d + 4 ≤ 112) :
    Mem.Sep (addr (st s₀) e) 4 (addr (scr s₀) d) 4 :=
  hp.st_scr.sep (contains_sub he (by omega) (st_eq hp (by omega)))
    (contains_sub hd (by omega) (hp.scr_eq (by omega)))

/-- Reading the hash value after writing the scratch buffer. -/
theorem readW_writeW_scr_st {s₀ : State} (hp : Pre s₀) (m : Mem) (v : Word) {e d : Nat}
    (he : e + 4 ≤ 20) (hd : d + 4 ≤ 112) :
    (m.writeW (addr (scr s₀) d) v).readW (addr (st s₀) e) 32 = m.readW (addr (st s₀) e) 32 :=
  Mem.readW_writeW_sep (st_scr_sep hp he hd) (by decide)

/-- Reading the scratch buffer after writing the hash value. -/
theorem readW_writeW_st_scr {s₀ : State} (hp : Pre s₀) (m : Mem) (v : Word) {e d : Nat}
    (he : e + 4 ≤ 20) (hd : d + 4 ≤ 112) :
    (m.writeW (addr (st s₀) e) v).readW (addr (scr s₀) d) 32 = m.readW (addr (scr s₀) d) 32 :=
  Mem.readW_writeW_sep (fun x h₁ h₂ => st_scr_sep hp he hd x h₂ h₁) (by decide)

/-! ## The loop invariant -/

/-- The callee-saved registers are saved in the scratch buffer. -/
def Saved (s₀ : State) (m : Mem) : Prop :=
  m.readW (addr (scr s₀) 64) 32 = s₀.gpr .ebx ∧ m.readW (addr (scr s₀) 68) 32 = s₀.gpr .esi ∧
  m.readW (addr (scr s₀) 72) 32 = s₀.gpr .edi ∧ m.readW (addr (scr s₀) 76) 32 = s₀.gpr .ebp

/-- What holds between blocks, after `i` of them. -/
structure Common (s₀ : State) (i : Nat) (s : State) : Prop where
  ebp : s.gpr .ebp = scr s₀
  esp : s.gpr .esp = esp₀ s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [stR s₀, scrR s₀] s₀.mem s.mem
  state : stateAt s.mem ((st s₀).setWidth 64) =
    compressBlocks (H₀ s₀) s₀.mem ((bp s₀).setWidth 64) i
  saved : Saved s₀ s.mem

/-- The loop invariant, at the start of block `i`: the block pointer and the
count of blocks left are in the scratch buffer. -/
structure LInv (s₀ : State) (i : Nat) (s : State) : Prop extends Common s₀ i s where
  bpw : s.mem.readW (addr (scr s₀) bpOff) 32 = blkAddr s₀ i
  nw : s.mem.readW (addr (scr s₀) nOff) 32 = BitVec.ofNat 32 (nb s₀ - i)

/-! ## One block -/

theorem load_eq : load = [.mov .edi (.mem ⟨.esp, 4⟩), .mov .eax (.mem ⟨.edi, 0⟩),
    .mov .ebx (.mem ⟨.edi, 4⟩), .mov .ecx (.mem ⟨.edi, 8⟩), .mov .edx (.mem ⟨.edi, 12⟩),
    .mov .esi (.mem ⟨.edi, 16⟩)] := by
  decide

theorem update_eq : update = [.mov .edi (.mem ⟨.esp, 4⟩),
    .alu .add .eax (.mem ⟨.edi, 0⟩), .alu .add .ebx (.mem ⟨.edi, 4⟩),
    .alu .add .ecx (.mem ⟨.edi, 8⟩), .alu .add .edx (.mem ⟨.edi, 12⟩), .alu .add .esi (.mem ⟨.edi, 16⟩),
    .store ⟨.edi, 0⟩ .eax, .store ⟨.edi, 4⟩ .ebx, .store ⟨.edi, 8⟩ .ecx, .store ⟨.edi, 12⟩ .edx,
    .store ⟨.edi, 16⟩ .esi] := by
  decide

theorem advance_eq : advance = [.mov .eax (.mem ⟨.ebp, 80⟩), .alu .add .eax (.imm 64),
    .store ⟨.ebp, 80⟩ .eax, .mov .eax (.mem ⟨.ebp, 84⟩), .alu .sub .eax (.imm 1),
    .store ⟨.ebp, 84⟩ .eax] := rfl

theorem vars0 (s : State) (v : HashValue) : Vars 0 s v ↔
    s.gpr .eax = v[0] ∧ s.gpr .ebx = v[1] ∧ s.gpr .ecx = v[2] ∧ s.gpr .edx = v[3] ∧
    s.gpr .esi = v[4] := Iff.rfl

set_option simprocs false in
theorem load_ok {s₀ : State} (hp : Pre s₀) {s : State} (hesp : s.gpr .esp = esp₀ s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (harg : s.mem.readW (addr (esp₀ s₀) 4) 32 = st s₀) :
    WP isa (.block load) s fun s₁ =>
      Vars 0 s₁ (stateAt s.mem ((st s₀).setWidth 64)) ∧ (∀ r ∈ pubRegs, s₁.gpr r = s.gpr r) ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr ∧ s₁.mem = s.mem := by
  have ia : InRegions (s.rd ++ s.wr) (addr (esp₀ s₀) 4) 4 := by
    rw [hrd, hwr]; exact hp.in_arg (by omega) (by omega)
  have hin : ∀ d, d + 4 ≤ 20 → InRegions (s.rd ++ s.wr) (addr (st s₀) d) 4 := by
    rw [hrd, hwr]; exact fun d hd => in_st hp hd
  have h0 := hin 0 (by decide); have h1 := hin 4 (by decide); have h2 := hin 8 (by decide)
  have h3 := hin 12 (by decide); have h4 := hin 16 (by decide)
  apply WP.of_runBlock
  rw [load_eq]
  simp (config := {decide := true}) only [vars0, runBlock_cons, runStep_some,
    runBlock_nil, exec, readSrc, isa, ea_mk,
    State.load32, State.setReg, hesp, ia, harg, h0, h1, h2, h3, h4, ite_true, ite_false,
    Option.map_some, Option.some.injEq, exists_eq_left']
  simp only [stateAt_get hp _ (show 0 < 5 by decide), stateAt_get hp _ (show 1 < 5 by decide),
    stateAt_get hp _ (show 2 < 5 by decide), stateAt_get hp _ (show 3 < 5 by decide),
    stateAt_get hp _ (show 4 < 5 by decide), stAddr]
  simp (config := {decide := true}) [pubRegs]

/-- Five words written in order to the hash value. -/
def writeState (s₀ : State) (m : Mem) (v : HashValue) : Mem :=
  let a := addr (st s₀)
  (((((m.writeW (a 0) v[0]).writeW (a 4) v[1]).writeW (a 8) v[2]).writeW (a 12) v[3]).writeW (a 16) v[4])

set_option simprocs false in
theorem stateAt_writeState {s₀ : State} (hp : Pre s₀) (m : Mem) (v : HashValue) :
    stateAt (writeState s₀ m v) ((st s₀).setWidth 64) = v := by
  apply stateAt_eq hp
  intro k hk
  simp only [writeState, stAddr]
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4) with h | h | h | h | h <;> subst h <;>
  simp (config := {decide := true}) (disch := decide) only [Mem.readW_writeW_self32, readW_writeW_st hp]

theorem frame_writeState {s₀ : State} (hp : Pre s₀) {m m' : Mem} (h : Frame [stR s₀] m m')
    (v : HashValue) : Frame [stR s₀] m (writeState s₀ m' v) := by
  have c : ∀ d, d + 4 ≤ 20 → (stR s₀).Contains (addr (st s₀) d) (32 / 8) :=
    fun d hd => contains_sub hd (by omega) (st_eq hp (by omega))
  simp only [writeState]
  refine ((((h.writeW ?_ _ (c 0 ?_)).writeW ?_ _ (c 4 ?_)).writeW ?_ _ (c 8 ?_)).writeW ?_ _ (c 12 ?_)).writeW
    ?_ _ (c 16 ?_) <;>
  simp

set_option simprocs false in
theorem update_ok {s₀ : State} (hp : Pre s₀) {s : State} (V H : HashValue) (hv : Vars 0 s V)
    (hesp : s.gpr .esp = esp₀ s₀) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (harg : s.mem.readW (addr (esp₀ s₀) 4) 32 = st s₀)
    (hH : ∀ k : Nat, (hk : k < 5) → s.mem.readW (stAddr s₀ k) 32 = H[k]) :
    WP isa (.block update) s fun s' =>
      s'.mem = writeState s₀ s.mem (Vector.zipWith (· + ·) V H) ∧
      (∀ r ∈ pubRegs, s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have ia : InRegions (s.rd ++ s.wr) (addr (esp₀ s₀) 4) 4 := by
    rw [hrd, hwr]; exact hp.in_arg (by omega) (by omega)
  have hin : ∀ d, d + 4 ≤ 20 → InRegions (s.rd ++ s.wr) (addr (st s₀) d) 4 := by
    rw [hrd, hwr]; exact fun d hd => in_st hp hd
  have hout : ∀ d, d + 4 ≤ 20 → InRegions s.wr (addr (st s₀) d) 4 := by
    rw [hwr]; exact fun d hd => out_st hp hd
  have i0 := hin 0 (by decide); have i1 := hin 4 (by decide); have i2 := hin 8 (by decide)
  have i3 := hin 12 (by decide); have i4 := hin 16 (by decide)
  have o0 := hout 0 (by decide); have o1 := hout 4 (by decide); have o2 := hout 8 (by decide)
  have o3 := hout 12 (by decide); have o4 := hout 16 (by decide)
  have m0 : s.mem.readW (addr (st s₀) 0) 32 = H[0] := hH 0 (by decide)
  have m1 : s.mem.readW (addr (st s₀) 4) 32 = H[1] := hH 1 (by decide)
  have m2 : s.mem.readW (addr (st s₀) 8) 32 = H[2] := hH 2 (by decide)
  have m3 : s.mem.readW (addr (st s₀) 12) 32 = H[3] := hH 3 (by decide)
  have m4 : s.mem.readW (addr (st s₀) 16) 32 = H[4] := hH 4 (by decide)
  rw [vars0] at hv
  obtain ⟨v0, v1, v2, v3, v4⟩ := hv
  apply WP.of_runBlock
  rw [update_eq]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some,
    runBlock_nil, exec, execAlu, readSrc,
    isa, ea_mk, State.load32, State.store32, State.setReg, arithFlags,
    State.setFlags, hesp, ia, harg, i0, i1, i2, i3, i4, o0, o1, o2, o3, o4,
    m0, m1, m2, m3, m4, v0, v1, v2, v3, v4, ite_true, ite_false,
    Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨by simp only [writeState, Vector.getElem_zipWith], ?_⟩
  simp (config := {decide := true}) [pubRegs]

set_option simprocs false in
theorem advance_ok {s₀ : State} (hp : Pre s₀) {s : State} (hebp : s.gpr .ebp = scr s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block advance) s fun s' =>
      s'.mem = (s.mem.writeW (addr (scr s₀) bpOff) (s.mem.readW (addr (scr s₀) bpOff) 32 + 64)).writeW
        (addr (scr s₀) nOff) (s.mem.readW (addr (scr s₀) nOff) 32 - 1) ∧
      s'.zf = some (s.mem.readW (addr (scr s₀) nOff) 32 - 1 == 0) ∧
      (∀ r ∈ pubRegs, s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have i80 : InRegions (s.rd ++ s.wr) (addr (scr s₀) 80) 4 := by
    rw [hrd, hwr]; exact hp.in_scr (by omega)
  have i84 : InRegions (s.rd ++ s.wr) (addr (scr s₀) 84) 4 := by
    rw [hrd, hwr]; exact hp.in_scr (by omega)
  have o80 : InRegions s.wr (addr (scr s₀) 80) 4 := by rw [hwr]; exact hp.out_scr (by omega)
  have o84 : InRegions s.wr (addr (scr s₀) 84) 4 := by rw [hwr]; exact hp.out_scr (by omega)
  have hsep := readW_writeW_scr hp s.mem (s.mem.readW (addr (scr s₀) 80) 32 + 64) (d := 80) (e := 84)
    (by omega) (by omega) (by omega)
  simp only [bpOff, nOff]
  apply WP.of_runBlock
  rw [advance_eq]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some,
    runBlock_nil, exec, execAlu, readSrc,
    isa, ea_mk, State.load32, State.store32, State.setReg, arithFlags,
    State.setFlags, hebp, i80, i84, o80, o84, hsep, ite_true, ite_false,
    Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left']
  simp (config := {decide := true}) [pubRegs]

theorem compressBlocks_succ (H : HashValue) (m : Mem) (p : Addr) (i : Nat) :
    compressBlocks H m p (i + 1) =
      compress (compressBlocks H m p i) (blockAt m (p + BitVec.ofNat 64 (64 * i))) := by
  simp [compressBlocks, List.range_succ, List.foldl_append]

theorem blk_word {s₀ : State} (hp : Pre s₀) {i t : Nat} (hi : i < nb s₀) (ht : t < 16) :
    bswap (s₀.mem.readW (addr (blkAddr s₀ i) (4 * t)) 32) = W (blk s₀ i) t := by
  rw [hp.blkAddr_eq hi ht, W_lt _ ht, bswap_readW]
  simp only [blk, blockAt, parseBlock]
  generalize (bp s₀).setWidth 64 + BitVec.ofNat 64 (64 * i) = a
  rw [show a + BitVec.ofNat 64 (4 * t) + 1 = a + BitVec.ofNat 64 (4 * t + 1) by bv_omega,
    show a + BitVec.ofNat 64 (4 * t + 1) + 1 = a + BitVec.ofNat 64 (4 * t + 2) by bv_omega,
    show a + BitVec.ofNat 64 (4 * t + 2) + 1 = a + BitVec.ofNat 64 (4 * t + 3) by bv_omega]

theorem harg_of {s₀ : State} (hp : Pre s₀) {m : Mem} (hf : Frame [stR s₀, scrR s₀] s₀.mem m) :
    m.readW (addr (esp₀ s₀) 4) 32 = st s₀ :=
  hp.arg_frame hf (i := 0) (by decide)

theorem win_sub (p : BitVec 32) : Region.Sub (winRegion p) ⟨p.setWidth 64, 112⟩ :=
  Region.sub_prefix (by omega)

/-- A word of the scratch buffer from offset 64 on is outside the window. -/
theorem win_word {s₀ : State} (hp : Pre s₀) {m m' : Mem} (hf : Frame [winRegion (scr s₀)] m m') {d : Nat}
    (hd : 64 ≤ d) (hd' : d + 4 ≤ 112) : m'.readW (addr (scr s₀) d) 32 = m.readW (addr (scr s₀) d) 32 := by
  refine hf.readW (Region.contains_self _ _) ?_ (by decide)
  simp only [List.mem_singleton, forall_eq]
  intro a h₁ h₂
  simp only [Region.Contains] at h₁ h₂
  rw [hp.scr_eq (by omega)] at h₁
  generalize (scr s₀).setWidth 64 = b at *
  bv_omega

/-- A word of the scratch buffer is unchanged by writes to the hash value. -/
theorem st_word {s₀ : State} (hp : Pre s₀) {m m' : Mem} (hf : Frame [stR s₀] m m') {d : Nat}
    (hd' : d + 4 ≤ 112) : m'.readW (addr (scr s₀) d) 32 = m.readW (addr (scr s₀) d) 32 := by
  refine hf.readW (Region.contains_self _ _) ?_ (by decide)
  simp only [List.mem_singleton, forall_eq]
  refine Region.Disjoint.sub_left hp.st_scr.symm fun a ha => ?_
  simp only [Region.Contains] at ha ⊢
  rw [hp.scr_eq (by omega)] at ha
  generalize (scr s₀).setWidth 64 = b at *
  bv_omega

theorem body_ok {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < nb s₀) {s : State}
    (hL : LInv s₀ i s) :
    WP isa body s fun s' =>
      (eval .ne s' = some false ∧ Common s₀ (nb s₀) s') ∨
      (eval .ne s' = some true ∧ i + 1 < nb s₀ ∧ LInv s₀ (i + 1) s') := by
  have hfits := hp.scr_fits
  refine WP.seq (WP.mono (load_ok hp hL.esp hL.rd hL.wr (harg_of hp hL.frame))
    fun s₁ ⟨hv₁, hpub₁, hrd₁, hwr₁, hm₁⟩ => ?_)
  have hwin : ∀ r' ∈ [winRegion (scr s₀)], (blR s₀).Disjoint r' := by
    simpa using Region.Disjoint.sub_right hp.blk_scr (win_sub _)
  have hblk : ∀ m, Frame [winRegion (scr s₀)] s₁.mem m → ∀ t : Nat, t < 16 →
      bswap (m.readW (addr (blkAddr s₀ i) (4 * t)) 32) = W (blk s₀ i) t := by
    intro m hm t ht
    rw [hm.readW (hp.blk_contains hi ht) hwin (by decide), hm₁,
      hL.frame.readW (hp.blk_contains hi ht) (by simpa using ⟨hp.blk_st, hp.blk_scr⟩) (by decide)]
    exact blk_word hp hi ht
  have hebp₁ : s₁.gpr .ebp = scr s₀ := (hpub₁ .ebp (by decide)).trans hL.ebp
  refine WP.seq (WP.mono (rounds_ok _ (blk s₀ i) (blkAddr s₀ i) (scr s₀) s₁ (by omega) hebp₁
    (by rw [hrd₁, hwr₁, hL.rd, hL.wr]; exact hp.in_scr (by simp [bpOff]))
    (fun m hm => by rw [win_word hp hm (by simp [bpOff]) (by simp [bpOff]), hm₁]; exact hL.bpw)
    (fun j => by rw [hrd₁, hwr₁, hL.rd, hL.wr]; exact hp.in_scr (by omega))
    (fun j => by rw [hwr₁, hL.wr]; exact hp.out_scr (by omega))
    (fun t ht => by rw [hrd₁, hwr₁, hL.rd, hL.wr]; exact hp.in_blk hi ht) hblk hv₁ 80 (Nat.le_refl _))
    fun s₂ hR => ?_)
  have hst : ∀ r' ∈ [winRegion (scr s₀)], (stR s₀).Disjoint r' := by
    simpa using Region.Disjoint.sub_right hp.st_scr (win_sub _)
  have pub₂ : ∀ r ∈ pubRegs, s₂.gpr r = s.gpr r := fun r hr => by
    rw [hR.pub r hr, hpub₁ r hr]
  have hf₂ : Frame [winRegion (scr s₀)] s.mem s₂.mem := by rw [← hm₁]; exact hR.frame
  have hframe₂ : Frame [stR s₀, scrR s₀] s₀.mem s₂.mem :=
    hL.frame.trans (hf₂.sub fun r hr => ⟨scrR s₀, by simp, by simp at hr; subst hr; exact win_sub _⟩)
  rw [WP.block_append_iff]
  refine WP.mono (update_ok hp _ (stateAt s.mem ((st s₀).setWidth 64)) hR.vars
    (by rw [pub₂ .esp (by decide), hL.esp]) (by rw [hR.rd, hrd₁, hL.rd]) (by rw [hR.wr, hwr₁, hL.wr])
    (harg_of hp hframe₂) fun k hk => ?_) fun s₃ ⟨hm₃, hpub₃, hrd₃, hwr₃⟩ => ?_
  · rw [hf₂.readW (contains_sub (by omega) (by omega) (hp.stAddr_eq hk)) hst (by decide),
      stateAt_get hp _ hk]
  have hebp₃ : s₃.gpr .ebp = scr s₀ := by rw [hpub₃ _ (by decide), pub₂ _ (by decide), hL.ebp]
  refine WP.mono (advance_ok hp hebp₃ (by rw [hrd₃, hR.rd, hrd₁, hL.rd]) (by rw [hwr₃, hR.wr, hwr₁, hL.wr]))
    fun s₄ ⟨hm₄, hz₄, hpub₄, hrd₄, hwr₄⟩ => ?_
  have hfs : Frame [stR s₀] s₂.mem s₃.mem := by rw [hm₃]; exact frame_writeState hp (Frame.refl _ _) _
  have r80 : s₃.mem.readW (addr (scr s₀) bpOff) 32 = blkAddr s₀ i := by
    rw [st_word hp hfs (by simp [bpOff]), win_word hp hf₂ (by simp [bpOff]) (by simp [bpOff])]; exact hL.bpw
  have r84 : s₃.mem.readW (addr (scr s₀) nOff) 32 = BitVec.ofNat 32 (nb s₀ - i) := by
    rw [st_word hp hfs (by simp [nOff]), win_word hp hf₂ (by simp [nOff]) (by simp [nOff])]; exact hL.nw
  rw [r80, r84] at hm₄; rw [r84] at hz₄
  have hnb : nb s₀ < 2 ^ 32 := (arg s₀ 2).isLt
  have hn : BitVec.ofNat 32 (nb s₀ - i) - 1 = BitVec.ofNat 32 (nb s₀ - (i + 1)) := by bv_omega
  rw [hn] at hm₄ hz₄
  have hfa : Frame [scrR s₀] s₃.mem s₄.mem := by
    rw [hm₄]; simp only [bpOff, nOff]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (contains_sub (off := 80) (by omega) (by omega) (hp.scr_eq (by omega)))).writeW
      (List.mem_singleton_self _) _ (contains_sub (off := 84) (by omega) (by omega) (hp.scr_eq (by omega)))
  have hframe : Frame [stR s₀, scrR s₀] s₀.mem s₄.mem := by
    refine hframe₂.trans ((hfs.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩).trans
      (hfa.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩))
  have hsv : ∀ d, 64 ≤ d → d + 4 ≤ 80 → s₄.mem.readW (addr (scr s₀) d) 32 = s.mem.readW (addr (scr s₀) d) 32 := by
    intro d h₁ h₂
    rw [hm₄, readW_writeW_scr hp _ _ (by simp [nOff]) (by omega) (by simp [nOff]; omega),
      readW_writeW_scr hp _ _ (by simp [bpOff]) (by omega) (by simp [bpOff]; omega),
      st_word hp hfs (by omega), win_word hp hf₂ h₁ (by omega)]
  have hstate : stateAt s₄.mem ((st s₀).setWidth 64) =
      compressBlocks (H₀ s₀) s₀.mem ((bp s₀).setWidth 64) (i + 1) := by
    have e : stateAt s₄.mem ((st s₀).setWidth 64) = stateAt s₃.mem ((st s₀).setWidth 64) := by
      apply stateAt_eq hp
      intro k hk
      rw [hm₄, readW_writeW_scr_st hp _ _ (by omega) (by simp [nOff]),
        readW_writeW_scr_st hp _ _ (by omega) (by simp [bpOff]), stateAt_get hp _ hk]
    rw [e, hm₃, stateAt_writeState hp, compressBlocks_succ, ← hL.state]
    rfl
  have hcommon : ∀ j, j = i + 1 → Common s₀ j s₄ := by
    rintro j rfl
    obtain ⟨g0, g1, g2, g3⟩ := hL.saved
    refine ⟨by rw [hpub₄ _ (by decide), hebp₃], by rw [hpub₄ _ (by decide), hpub₃ _ (by decide),
      pub₂ _ (by decide), hL.esp], by rw [hrd₄, hrd₃, hR.rd, hrd₁, hL.rd],
      by rw [hwr₄, hwr₃, hR.wr, hwr₁, hL.wr], hframe, hstate, ?_⟩
    exact ⟨(hsv 64 (by omega) (by omega)).trans g0, (hsv 68 (by omega) (by omega)).trans g1,
      (hsv 72 (by omega) (by omega)).trans g2, (hsv 76 (by omega) (by omega)).trans g3⟩
  have hev : eval .ne s₄ = some (!(BitVec.ofNat 32 (nb s₀ - (i + 1)) == 0)) := by
    simp only [eval, hz₄, Option.map_some]
  by_cases hlast : i + 1 = nb s₀
  · left
    refine ⟨by rw [hev, hlast]; simp, hlast ▸ hcommon _ rfl⟩
  · right
    have hne : nb s₀ - (i + 1) ≠ 0 := by omega
    have h0 : BitVec.ofNat 32 (nb s₀ - (i + 1)) ≠ 0 := by
      intro h
      have h' := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h'
      exact hne h'
    refine ⟨by rw [hev]; simpa using h0, by omega, { hcommon _ rfl with bpw := ?_, nw := ?_ }⟩
    · rw [hm₄, readW_writeW_scr hp _ _ (by simp [nOff]) (by simp [bpOff]) (by simp [bpOff, nOff]),
        Mem.readW_writeW_self32]
      simp only [blkAddr]
      bv_omega
    · rw [hm₄, Mem.readW_writeW_self32]

/-! ## Prologue and epilogue -/

theorem prologue_eq : prologue = [.mov .eax (.mem ⟨.esp, 16⟩), .store ⟨.eax, 64⟩ .ebx,
    .store ⟨.eax, 68⟩ .esi, .store ⟨.eax, 72⟩ .edi, .store ⟨.eax, 76⟩ .ebp,
    .mov .ebp (.reg .eax), .mov .ecx (.mem ⟨.esp, 8⟩), .store ⟨.ebp, 80⟩ .ecx,
    .mov .ecx (.mem ⟨.esp, 12⟩), .store ⟨.ebp, 84⟩ .ecx, .alu .test .ecx (.reg .ecx)] := rfl

theorem epilogue_eq : epilogue = [.mov .ebx (.mem ⟨.ebp, 64⟩), .mov .esi (.mem ⟨.ebp, 68⟩),
    .mov .edi (.mem ⟨.ebp, 72⟩), .mov .ebp (.mem ⟨.ebp, 76⟩)] := rfl

/-- Reading an argument after writing the scratch buffer. -/
theorem readW_writeW_scr_arg {s₀ : State} (hp : Pre s₀) (m : Mem) (v : Word) {d e : Nat}
    (hd : d + 4 ≤ 112) (he : 4 ≤ e) (he' : e + 4 ≤ 20) :
    (m.writeW (addr (scr s₀) d) v).readW (addr (esp₀ s₀) e) 32 = m.readW (addr (esp₀ s₀) e) 32 :=
  Mem.readW_writeW_sep (hp.arg_scr.sep (hp.arg_contains he he')
    (contains_sub hd (by omega) (hp.scr_eq (by omega)))) (by decide)

/-- The memory after the prologue. -/
def saveMem (s₀ : State) : Mem :=
  (((((s₀.mem.writeW (addr (scr s₀) 64) (s₀.gpr .ebx)).writeW (addr (scr s₀) 68) (s₀.gpr .esi)).writeW
    (addr (scr s₀) 72) (s₀.gpr .edi)).writeW (addr (scr s₀) 76) (s₀.gpr .ebp)).writeW
    (addr (scr s₀) 80) (bp s₀)).writeW (addr (scr s₀) 84) (arg s₀ 2)

theorem save_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block prologue) s₀ fun s₁ =>
      s₁.gpr .ebp = scr s₀ ∧ s₁.gpr .esp = esp₀ s₀ ∧ s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr ∧
      s₁.mem = saveMem s₀ ∧ s₁.zf = some (arg s₀ 2 &&& arg s₀ 2 == 0) := by
  have hsa := readW_writeW_scr_arg hp
  have i8 := hp.in_arg (d := 8) (by omega) (by omega)
  have i12 := hp.in_arg (d := 12) (by omega) (by omega)
  have i16 := hp.in_arg (d := 16) (by omega) (by omega)
  have a8 : s₀.mem.readW (addr (esp₀ s₀) 8) 32 = bp s₀ := rfl
  have a12 : s₀.mem.readW (addr (esp₀ s₀) 12) 32 = arg s₀ 2 := rfl
  have a16 : s₀.mem.readW (addr (esp₀ s₀) 16) 32 = scr s₀ := rfl
  have hout := fun d (hd : d + 4 ≤ 112) => hp.out_scr hd
  apply WP.of_runBlock
  rw [prologue_eq]
  simp (config := {decide := true}) (disch := decide) only [runBlock_cons,
    runBlock_nil, runStep_some, exec, execAlu, readSrc, ea_mk, State.setReg, arithFlags,
    State.setFlags, State.load32, State.store32, i8, i12, i16, a8, a12, a16, hout, hsa, ite_true,
    ite_false, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> trivial

theorem saveMem_saved {s₀ : State} (hp : Pre s₀) : Saved s₀ (saveMem s₀) := by
  have hrw := readW_writeW_scr hp
  simp only [Saved, saveMem]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  simp (config := {decide := true}) (disch := decide) only [Mem.readW_writeW_self32, hrw]

theorem saveMem_frame {s₀ : State} (hp : Pre s₀) : Frame [scrR s₀] s₀.mem (saveMem s₀) := by
  have c : ∀ d : Nat, d + 4 ≤ 112 → (scrR s₀).Contains (addr (scr s₀) d) (32 / 8) :=
    fun d hd => contains_sub hd (by omega) (hp.scr_eq (by omega))
  simp only [saveMem]
  have m := List.mem_singleton_self (scrR s₀)
  exact ((((((Frame.refl _ _).writeW m _ (c 64 (by omega))).writeW m _ (c 68 (by omega))).writeW
    m _ (c 72 (by omega))).writeW m _ (c 76 (by omega))).writeW m _ (c 80 (by omega))).writeW m _
    (c 84 (by omega))

theorem linv_zero {s₀ : State} (hp : Pre s₀) {s₁ : State} (hebp : s₁.gpr .ebp = scr s₀)
    (hesp : s₁.gpr .esp = esp₀ s₀) (hrd : s₁.rd = s₀.rd) (hwr : s₁.wr = s₀.wr)
    (hm : s₁.mem = saveMem s₀) : LInv s₀ 0 s₁ := by
  have hrw := readW_writeW_scr hp
  refine ⟨⟨hebp, hesp, hrd, hwr, ?_, ?_, by rw [hm]; exact saveMem_saved hp⟩, ?_, ?_⟩
  · rw [hm]; exact (saveMem_frame hp).sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩
  · rw [hm]
    apply stateAt_eq hp
    intro k hk
    rw [(saveMem_frame hp).readW (contains_sub (len := 20) (off := 4 * k) (by omega) (by omega)
      (hp.stAddr_eq hk))
      (by simpa using hp.st_scr) (by decide), ← stateAt_get hp _ hk]
    rfl
  · rw [hm]; simp only [saveMem, bpOff]
    simp (config := {decide := true}) (disch := decide) only [Mem.readW_writeW_self32, hrw]
    simp [blkAddr]
  · rw [hm]; simp only [saveMem, nOff]
    simp (config := {decide := true}) (disch := decide) only [Mem.readW_writeW_self32]
    simp [nb]

theorem restore_ok {s₀ : State} (hp : Pre s₀) {s : State} (hc : Common s₀ (nb s₀) s) :
    WP isa (.block epilogue) s fun s' =>
      (∀ r ∈ calleeSaved, s'.gpr r = s₀.gpr r) ∧ s'.mem = s.mem := by
  have hin : ∀ d, d + 4 ≤ 112 → InRegions (s.rd ++ s.wr) (addr (scr s₀) d) 4 := by
    rw [hc.rd, hc.wr]; exact fun d hd => hp.in_scr hd
  obtain ⟨g0, g1, g2, g3⟩ := hc.saved
  have hebp := hc.ebp
  have hesp := hc.esp
  apply WP.of_runBlock
  rw [epilogue_eq]
  simp (config := {decide := true}) (disch := decide) only [runBlock_cons,
    runBlock_nil, runStep_some, exec, readSrc, ea_mk, State.setReg, State.load32, hebp, hin,
    g0, g1, g2, g3, ite_true, ite_false, Option.map_some, Option.some.injEq,
    exists_eq_left']
  refine ⟨fun r hr => ?_, trivial⟩
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp (config := {decide := true}) [hesp]

/-! ## The whole function -/

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa compress s₀ fun s' => abiPreserved s₀ s' ∧ Proof.Sha1.compressX86.post s₀ s' := by
  refine WP.seq (WP.mono (save_ok hp) fun s₁ ⟨hebp, hesp, hrd, hwr, hm, hz⟩ => ?_)
  refine WP.seq (WP.mono (Q := Common s₀ (nb s₀)) ?_ fun s₂ hc =>
    WP.mono (restore_ok hp hc) fun s' ⟨hr, hm'⟩ => ⟨⟨hr, ?_⟩, ?_⟩)
  rotate_left
  · rw [hm']
    refine hc.frame.readW (Region.contains_self _ _) ?_ (by decide)
    simpa using ⟨hp.ret_st, hp.ret_scr⟩
  · show stateAt s'.mem _ = _
    rw [hm']; exact hc.state
  have hL₀ := linv_zero hp hebp hesp hrd hwr hm
  refine WP.ite (arg s₀ 2 &&& arg s₀ 2 == 0) (by simp [eval, hz]) (fun h => ?_) (fun h => ?_)
  · have h0 : nb s₀ = 0 := by simp only [BitVec.and_self, beq_iff_eq] at h; simp [nb, h]
    exact WP.block_nil (M := isa) (h0 ▸ hL₀.toCommon)
  · have hpos : 0 < nb s₀ := by
      simp only [BitVec.and_self, beq_eq_false_iff_ne, ne_eq] at h
      exact Nat.pos_of_ne_zero fun h' => h (BitVec.eq_of_toNat_eq (by simpa using h'))
    let Inv : Nat → State → Prop := fun m s => ∃ i, m = nb s₀ - i ∧ i < nb s₀ ∧ LInv s₀ i s
    have hstep : ∀ m s, Inv m s → WP isa body s (fun s' =>
        (eval .ne s' = some false ∧ Common s₀ (nb s₀) s') ∨
        (eval .ne s' = some true ∧ ∃ m' < m, Inv m' s')) := by
      rintro m s ⟨i, rfl, hi, hL⟩
      refine WP.mono (body_ok hp hi hL) fun s' h => ?_
      rcases h with ⟨he, hc⟩ | ⟨he, hi', hL'⟩
      · exact .inl ⟨he, hc⟩
      · exact .inr ⟨he, nb s₀ - (i + 1), by omega, i + 1, rfl, hi', hL'⟩
    exact WP.loop (M := isa) Inv hstep (nb s₀) s₁ ⟨0, rfl, hpos, hL₀⟩

/-- Memory holding the arguments `0x1000, 0x2000, 0, 0x3000` at `0x4004`. -/
def satMem : Mem := fun a =>
  if a = 0x4005 then 0x10 else if a = 0x4009 then 0x20 else if a = 0x4011 then 0x30 else 0

/-- A state satisfying the precondition (with no blocks). -/
def satState : State where
  gpr r := match r with
    | .esp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMem
  rd := [⟨0x2000, 0⟩, ⟨0x4004, 16⟩]
  wr := [⟨0x1000, 20⟩, ⟨0x3000, 112⟩]

theorem sat_pre : Proof.Sha1.compressX86.pre satState := by
  have a0 : arg satState 0 = 0x1000 := by decide
  have a1 : arg satState 1 = 0x2000 := by decide
  have a2 : arg satState 2 = 0 := by decide
  have a3 : arg satState 3 = 0x3000 := by decide
  have e : argAddr satState 0 = 0x4004 := by decide
  simp only [Proof.Sha1.compressX86, a0, a1, a2, a3, e]
  refine ⟨by decide, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by decide, by decide, by decide, by decide⟩ <;>
  · intro a h₁ h₂
    simp only [Region.Contains, satState] at h₁ h₂
    bv_omega

/-- The taint analysis starts with the stack arguments public, and the words
holding `state` and `scratch` known to be the base addresses of the writable
regions. -/
def τ₀ : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [20, 112], argLen := 20, argBases := [(4, 0), (16, 1)] }

theorem wf₀ {s : State} (hp : Pre s) : VG.X86.Taint.Wf τ₀ s := by
  have hst := hp.st_fits; have hsc := hp.scr_fits; have hs := hp.esp_fits
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun _ => ⟨by simp [hp.wr, τ₀], by simpa [hp.wr] using hp.st_scr, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨hs, ?_⟩, ?_⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [BitVec.toNat_setWidth] <;> omega
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by omega) hp.ret_st hp.arg_st
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by omega) hp.ret_scr hp.arg_scr
  · intro p hp'
    simp only [τ₀, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl <;> refine ⟨by decide, ?_⟩ <;>
      simp [VG.X86.Taint.region, hp.wr, addr, arg, argAddr]

theorem agree₀ {s₁ s₂ : State} (h₁ : Proof.Sha1.compressX86.pre s₁)
    (h₂ : Proof.Sha1.compressX86.pre s₂) (hpub : Proof.Sha1.compressX86.pub s₁ s₂) :
    VG.X86.Taint.Agree τ₀ s₁ s₂ := by
  obtain ⟨hesp, a0, a1, a2, a3⟩ := hpub
  have hp₁ := pre_of _ h₁; have hp₂ := pre_of _ h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, wf₀ hp₁, wf₀ hp₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => hesp,
    fun k h4 hk => ?_⟩
  · simp only [τ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact hesp
  · rw [hp₁.wr, hp₂.wr]; simp only [stR, scrR, st, scr, a0, a3]
  · simp only [τ₀] at hk
    rw [show VG.X86.Taint.depth τ₀.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq hp₁.esp_fits h4 hk, VG.X86.Taint.argByte_eq hp₂.esp_fits h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega))]
    have : (k - 4) / 4 = 0 ∨ (k - 4) / 4 = 1 ∨ (k - 4) / 4 = 2 ∨ (k - 4) / 4 = 3 := by omega
    rcases this with h | h | h | h <;> rw [h]
    · exact congrArg _ a0
    · exact congrArg _ a1
    · exact congrArg _ a2
    · exact congrArg _ a3

theorem compress_verified :
    Verified X86.target Impl.Sha1.X86.compress Proof.Sha1.compressX86 :=
  ⟨fun s hs => correct (pre_of s hs),
    VG.Taint.constantTime (A := taint) τ₀ (fun _ _ h₁ h₂ hpub => agree₀ h₁ h₂ hpub) (by taint_decide),
    ⟨satState, sat_pre⟩⟩

end VG.Proof.Sha1.X86
