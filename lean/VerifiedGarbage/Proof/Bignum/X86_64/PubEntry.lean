import VerifiedGarbage.Proof.Bignum.X86_64.PubFail

/-!
# `vg_rsa_public` on x86-64: the entry

`entry` saves the callee-saved registers and the arguments in the header of
the working space, and leaves its base in `rdi` (`entry_ok`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.MlKem.X86_64

/-- Slot `i` of the header at `r11`. -/
def hdr11 (i : Nat) : MemOp := { base := .r11, disp := 8 * (i : Int) }

theorem entry_eq : entry = ([.mov .r11 (.mem { base := .rsp, disp := 24 }),
    .store (hdr11 0) .rbx, .store (hdr11 1) .rbp, .store (hdr11 2) .r12, .store (hdr11 3) .r13,
    .store (hdr11 4) .r14, .store (hdr11 5) .r15,
    .store (hdr11 sOut) .rdi, .store (hdr11 sN) .rdx, .store (hdr11 sK) .rcx, .store (hdr11 sE) .r8,
    .store (hdr11 sElen) .r9] : List Instr) ++ [.mov .rax (.mem { base := .rsp, disp := 8 }), .store (hdr11 sIn) .rax,
    .mov .rdi (.reg .r11)] := rfl

/-- A word of the header past a store to another slot. -/
theorem word_skip {m : Mem} {B : Addr} {i j : Nat} {v x : BitVec 64} (h : word m B (8 * j) = x)
    (hij : i ≠ j) (hi : i < 32) (hj : j < 32) : word (m.writeW (off B (8 * i)) v) B (8 * j) = x :=
  (hdrStore_hdr m B v hi hj hij).trans h

theorem Outside.store_hdr {B : Addr} {n : Nat} {m m' : Mem} (h : Outside B 0 n m m') {i : Nat}
    (hi : 8 * i + 8 ≤ n) (hn : n ≤ 2 ^ 64) (v : BitVec 64) : Outside B 0 n m (m'.writeW (off B (8 * i)) v) :=
  fun x hx => (writeW_outside m' B v (by omega) x (by omega)).trans (h x hx)

/-- The header after `entry`'s stores. -/
def entryMem (m : Mem) (B : Addr) (v0 v1 v2 v3 v4 v5 vo vn vk ve vl : BitVec 64) : Mem :=
  ((((((((((m.writeW (off B (8 * 0)) v0).writeW (off B (8 * 1)) v1).writeW (off B (8 * 2)) v2).writeW
    (off B (8 * 3)) v3).writeW (off B (8 * 4)) v4).writeW (off B (8 * 5)) v5).writeW (off B (8 * sOut)) vo).writeW
    (off B (8 * sN)) vn).writeW (off B (8 * sK)) vk).writeW (off B (8 * sE)) ve).writeW (off B (8 * sElen)) vl

theorem entryMem_facts (m : Mem) (B : Addr) (v0 v1 v2 v3 v4 v5 vo vn vk ve vl : BitVec 64) :
    let m' := entryMem m B v0 v1 v2 v3 v4 v5 vo vn vk ve vl
    word m' B (8 * 0) = v0 ∧ word m' B (8 * 1) = v1 ∧ word m' B (8 * 2) = v2 ∧ word m' B (8 * 3) = v3 ∧
    word m' B (8 * 4) = v4 ∧ word m' B (8 * 5) = v5 ∧ word m' B (8 * sOut) = vo ∧ word m' B (8 * sN) = vn ∧
    word m' B (8 * sK) = vk ∧ word m' B (8 * sE) = ve ∧ word m' B (8 * sElen) = vl ∧
    Outside B 0 (8 * 22) m m' := by
  intro m'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> unfold m' entryMem
  all_goals first
    | (repeat (first | refine word_skip ?_ (by decide) (by decide) (by decide) |
        exact word_writeW_self _ _ _ _)); done
    | (repeat (first | exact Outside.refl _ _ _ _ | refine Outside.store_hdr ?_ (by decide) (by decide) _))

/-- `entry`: the header, from the arguments, and the working space's base
(the third stack argument) in `rdi`. -/
theorem entry_ok {s : State} {B : Addr} (hB : stackArg s 2 = B)
    (hw : ∀ i < 22, InRegions s.wr (off B (8 * i)) 8)
    (ha0 : InRegions (s.rd ++ s.wr) (stackArgAddr s 0) 8) (ha2 : InRegions (s.rd ++ s.wr) (stackArgAddr s 2) 8)
    (hsep : ∀ m', Outside B 0 (8 * 22) s.mem m' → m'.readW (stackArgAddr s 0) 64 = stackArg s 0) :
    WP isa (.block entry) s fun t => t.gpr .rdi = B ∧
      word t.mem B (8 * 0) = s.gpr .rbx ∧ word t.mem B (8 * 1) = s.gpr .rbp ∧
      word t.mem B (8 * 2) = s.gpr .r12 ∧ word t.mem B (8 * 3) = s.gpr .r13 ∧
      word t.mem B (8 * 4) = s.gpr .r14 ∧ word t.mem B (8 * 5) = s.gpr .r15 ∧
      word t.mem B (8 * sOut) = s.gpr .rdi ∧ word t.mem B (8 * sN) = s.gpr .rdx ∧
      word t.mem B (8 * sK) = s.gpr .rcx ∧ word t.mem B (8 * sE) = s.gpr .r8 ∧
      word t.mem B (8 * sElen) = s.gpr .r9 ∧ word t.mem B (8 * sIn) = stackArg s 0 ∧
      Outside B 0 (8 * 22) s.mem t.mem ∧ Keep [.r11, .rax, .rdi] s t := by
  have e0 : s.gpr .rsp + BitVec.ofInt 64 8 = stackArgAddr s 0 := rfl
  have e2 : s.gpr .rsp + BitVec.ofInt 64 24 = stackArgAddr s 2 := rfl
  have hB' : s.mem.readW (stackArgAddr s 2) 64 = B := hB
  have hA0 : s.mem.readW (stackArgAddr s 0) 64 = stackArg s 0 := rfl
  rw [entry_eq, WP.block_append_iff]
  refine WP.mono (WP.keep [.r11] (Q := fun t => t.gpr .r11 = B ∧
      word t.mem B (8 * 0) = s.gpr .rbx ∧ word t.mem B (8 * 1) = s.gpr .rbp ∧
      word t.mem B (8 * 2) = s.gpr .r12 ∧ word t.mem B (8 * 3) = s.gpr .r13 ∧
      word t.mem B (8 * 4) = s.gpr .r14 ∧ word t.mem B (8 * 5) = s.gpr .r15 ∧
      word t.mem B (8 * sOut) = s.gpr .rdi ∧ word t.mem B (8 * sN) = s.gpr .rdx ∧
      word t.mem B (8 * sK) = s.gpr .rcx ∧ word t.mem B (8 * sE) = s.gpr .r8 ∧
      word t.mem B (8 * sElen) = s.gpr .r9 ∧ Outside B 0 (8 * 22) s.mem t.mem) ?_ rfl)
    fun t₁ ⟨⟨h11, h0, h1, h2, h3, h4, h5, hO, hN, hK, hE, hL, ho₁⟩, k₁⟩ => ?_
  · xrun [State.ea, hdr11, e2, ha2, hB', hdrOff, hw 0 (by decide), hw 1 (by decide),
      hw 2 (by decide), hw 3 (by decide), hw 4 (by decide), hw 5 (by decide), hw sOut (by decide),
      hw sN (by decide), hw sK (by decide), hw sE (by decide), hw sElen (by decide)]
    exact entryMem_facts _ _ _ _ _ _ _ _ _ _ _ _ _
  have hr₁ : t₁.mem.readW (stackArgAddr s 0) 64 = stackArg s 0 := hsep _ ho₁
  have ha0₁ : InRegions (t₁.rd ++ t₁.wr) (stackArgAddr s 0) 8 := by rw [k₁.2.1, k₁.2.2]; exact ha0
  have hw₁ : InRegions t₁.wr (off B (8 * sIn)) 8 := by rw [k₁.2.2]; exact hw sIn (by decide)
  have e0₁ : t₁.gpr .rsp + BitVec.ofInt 64 8 = stackArgAddr s 0 := by rw [k₁.gpr (by decide)]; exact e0
  refine WP.mono (WP.keep [.rax, .rdi] (Q := fun t => t.gpr .rdi = B ∧
      t.mem = t₁.mem.writeW (off B (8 * sIn)) (stackArg s 0)) (by
    xrun [State.ea, hdr11, e0₁, ha0₁, hr₁, h11, hdrOff, hw₁]) rfl) fun t ⟨⟨hdi, hm⟩, k₂⟩ => ?_
  refine ⟨hdi, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try rw [hm]
  · exact word_skip h0 (by decide) (by decide) (by decide)
  · exact word_skip h1 (by decide) (by decide) (by decide)
  · exact word_skip h2 (by decide) (by decide) (by decide)
  · exact word_skip h3 (by decide) (by decide) (by decide)
  · exact word_skip h4 (by decide) (by decide) (by decide)
  · exact word_skip h5 (by decide) (by decide) (by decide)
  · exact word_skip hO (by decide) (by decide) (by decide)
  · exact word_skip hN (by decide) (by decide) (by decide)
  · exact word_skip hK (by decide) (by decide) (by decide)
  · exact word_skip hE (by decide) (by decide) (by decide)
  · exact word_skip hL (by decide) (by decide) (by decide)
  · exact word_writeW_self _ _ _ _
  · exact Outside.store_hdr ho₁ (by decide) (by decide) _
  · exact (k₁.trans k₂).mono (by decide)

end VG.Proof.Bignum.X86_64
