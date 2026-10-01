import VerifiedGarbage.Proof.Blake2.X86.CompressS.Pre
import VerifiedGarbage.Proof.Blake2.X86.Stream.Common

/-!
# BLAKE2s on x86 (32-bit): one block

Untrusted: everything here is checked by Lean. `body_ok`: the loop body
compresses block `i` into the state and advances to the next block, from the
loop invariant `LInv`.
-/

namespace VG.Proof.Blake2.X86.CompressS

open VG VG.X86 VG.X86.Wp
open VG.Spec.Blake2 (Work Block HashValue blockBytes stateAt blockAt compressBlocks)
open VG.Impl.Blake2.X86 (at_)
open VG.Impl.Blake2.X86.CompressS
open VG.Proof.MdStream.X86 (contains_addr readW_writeW_addr)

/-! ## The loop invariant -/

/-- What holds between blocks, after `i` of them. -/
structure Common (s₀ : State) (i : Nat) (s : State) : Prop where
  esi : s.gpr .esi = scr s₀
  esp : s.gpr .esp = esp₀ s₀
  ebp : s.gpr .ebp = s₀.gpr .ebp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [stR s₀, scrR s₀] s₀.mem s.mem
  state : stateAt 32 s.mem ((st s₀).setWidth 64) =
    compressBlocks Spec.Blake2.s (H₀ s₀) s₀.mem ((bp s₀).setWidth 64) i (t₀ s₀) (fl s₀)
  saved : Saved s₀ s.mem

/-- The loop invariant, at the start of block `i`. -/
structure LInv (s₀ : State) (i : Nat) (s : State) : Prop extends Common s₀ i s where
  edi : s.gpr .edi = blkAddr s₀ i
  tlo : s.mem.readW (addr (scr s₀) tloOff) 32 = BitVec.ofNat 32 (t₀ s₀ + i * 64)
  thi : s.mem.readW (addr (scr s₀) thiOff) 32 = BitVec.ofNat 32 ((t₀ s₀ + i * 64) / 2 ^ 32)
  flag : s.mem.readW (addr (scr s₀) fOff) 32 = flagW (fl s₀)
  cnt : s.mem.readW (addr (scr s₀) nOff) 32 = BitVec.ofNat 32 (nb s₀ - i)

/-! ## Words of `scratch` and of the state -/

section
variable {B : BitVec 32} (hfit : B.toNat + 512 ≤ 2 ^ 32)
include hfit

theorem rw_scr (m : Mem) (v : BitVec 32) {d e : Nat} (hd : d + 4 ≤ 512) (he : e + 4 ≤ 512)
    (h : d + 4 ≤ e ∨ e + 4 ≤ d) :
    (m.writeW (addr B e) v).readW (addr B d) 32 = m.readW (addr B d) 32 :=
  readW_writeW_addr m v (by omega) (by omega) h

theorem rw_hi (m : Mem) (v : BitVec 32) {k d : Nat} (hk : k < 16) (hd : 64 ≤ d) (hd' : d + 4 ≤ 512) :
    (m.writeW (addr B (vOff k)) v).readW (addr B d) 32 = m.readW (addr B d) 32 :=
  readW_writeW_addr m v (by omega) (by simp only [vOff]; omega) (by simp only [vOff]; omega)

end

theorem rw_word {B : BitVec 32} (hfit : B.toNat + 32 ≤ 2 ^ 32) (m : Mem) (x : BitVec 32) {i k : Nat}
    (hi : i < 8) (hk : k < 8) :
    (m.writeW (addr B (4 * i)) x).readW (addr B (4 * k)) 32 =
      if i = k then x else m.readW (addr B (4 * k)) 32 := by
  by_cases h : i = k
  · subst h; simp only [Mem.readW_writeW_self32, ite_true]
  · simp only [h, ite_false]
    exact readW_writeW_addr m x (by omega) (by omega) (by omega)

section
variable {s₀ : State} (hp : Pre s₀)
include hp

/-! ## Loading the work vector -/

/-- Copying word `k` of the state to the work vector. -/
def cp (k : Nat) : List Instr := [.mov .ecx (.mem (at_ .eax (4 * k))), .store (at_ .esi (vOff k)) .ecx]

/-- The IV part of the work vector, with the counter and the flag. -/
def ivs : List Instr :=
  [.mov .ecx (.imm Spec.Blake2.s.IV[0]), .store (at_ .esi (vOff 8)) .ecx,
   .mov .ecx (.imm Spec.Blake2.s.IV[1]), .store (at_ .esi (vOff 9)) .ecx,
   .mov .ecx (.imm Spec.Blake2.s.IV[2]), .store (at_ .esi (vOff 10)) .ecx,
   .mov .ecx (.imm Spec.Blake2.s.IV[3]), .store (at_ .esi (vOff 11)) .ecx,
   .mov .ecx (.imm Spec.Blake2.s.IV[4]), .alu .xor .ecx (.mem (at_ .esi tloOff)),
   .store (at_ .esi (vOff 12)) .ecx,
   .mov .ecx (.imm Spec.Blake2.s.IV[5]), .alu .xor .ecx (.mem (at_ .esi thiOff)),
   .store (at_ .esi (vOff 13)) .ecx,
   .mov .ecx (.imm Spec.Blake2.s.IV[6]), .alu .xor .ecx (.mem (at_ .esi fOff)),
   .store (at_ .esi (vOff 14)) .ecx,
   .mov .ecx (.imm Spec.Blake2.s.IV[7]), .store (at_ .esi (vOff 15)) .ecx]

omit hp in
theorem load_eq : load = (.mov .eax (.mem (at_ .esp 4)) :: (List.range 8).flatMap cp) ++ ivs := rfl

theorem cp_ok (k : Nat) (hk : k < 8) {s : State} (heax : s.gpr .eax = st s₀)
    (hesi : s.gpr .esi = scr s₀) (hwr : s.wr = s₀.wr) :
    WP isa (.block (cp k)) s fun s' =>
      (∀ r, r ≠ .ecx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.mem = s.mem.writeW (addr (scr s₀) (vOff k)) (s.mem.readW (addr (st s₀) (4 * k)) 32) := by
  refine wp_ldm heax (mem_rd (hp.in_st hwr (by omega))) fun s₁ u₁ => ?_
  refine wp_stm (by rw [u₁.other _ (by decide), hesi])
    (by rw [u₁.wr]; exact hp.in_scr hwr (by simp only [vOff]; omega)) fun s₂ u₂ => WP.block_nil ?_
  refine ⟨fun r hr => by rw [u₂.gpr, u₁.other r hr], by rw [u₂.rd, u₁.rd], by rw [u₂.wr, u₁.wr], ?_⟩
  rw [u₂.mem, u₁.gpr, u₁.mem]

/-- After copying words `0 … n-1` of the state. -/
structure CpInv (s₀ s : State) (n : Nat) (s' : State) : Prop where
  gpr : ∀ r, r ≠ .ecx → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  done : ∀ k < n, s'.mem.readW (addr (scr s₀) (vOff k)) 32 = s.mem.readW (addr (st s₀) (4 * k)) 32
  frame : Frame [workR (scr s₀)] s.mem s'.mem

theorem cps_ok {s : State} (heax : s.gpr .eax = st s₀) (hesi : s.gpr .esi = scr s₀)
    (hwr : s.wr = s₀.wr) : ∀ n ≤ 8, WP isa (.block ((List.range n).flatMap cp)) s (CpInv s₀ s n) := by
  intro n hn
  have fV : (scr s₀).toNat + 64 ≤ 2 ^ 32 := by have := hp.scr_fits; omega
  induction n with
  | zero => exact WP.block_nil ⟨fun _ _ => rfl, rfl, rfl, fun _ h => absurd h (by omega), Frame.refl _ _⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun s₁ h₁ => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    refine WP.mono (cp_ok hp n (by omega) (by rw [h₁.gpr _ (by decide), heax])
      (by rw [h₁.gpr _ (by decide), hesi]) (by rw [h₁.wr, hwr])) fun s₂ ⟨g₂, r₂, w₂, m₂⟩ =>
      ⟨fun r hr => by rw [g₂ r hr, h₁.gpr r hr], by rw [r₂, h₁.rd], by rw [w₂, h₁.wr],
        fun k hk => ?_, ?_⟩
    · rw [m₂, rw_slot fV _ _ (by omega) (by omega)]
      by_cases hkn : n = k
      · subst hkn; simp only [ite_true]; rw [hp.st_frame h₁.frame (by omega)]
      · simp only [hkn, ite_false]; exact h₁.done k (by omega)
    · rw [m₂]
      exact h₁.frame.writeW (List.mem_singleton_self _) _
        (contains_addr (by simp only [vOff]; omega) (by decide) fV)

/-- The memory after `ivs`. -/
def ivMem (m : Mem) (B : BitVec 32) : Mem :=
  (((((((m.writeW (addr B (vOff 8)) Spec.Blake2.s.IV[0]).writeW (addr B (vOff 9)) Spec.Blake2.s.IV[1]).writeW
    (addr B (vOff 10)) Spec.Blake2.s.IV[2]).writeW (addr B (vOff 11)) Spec.Blake2.s.IV[3]).writeW
    (addr B (vOff 12)) (Spec.Blake2.s.IV[4] ^^^ m.readW (addr B tloOff) 32)).writeW
    (addr B (vOff 13)) (Spec.Blake2.s.IV[5] ^^^ m.readW (addr B thiOff) 32)).writeW
    (addr B (vOff 14)) (Spec.Blake2.s.IV[6] ^^^ m.readW (addr B fOff) 32)).writeW
    (addr B (vOff 15)) Spec.Blake2.s.IV[7]

theorem ivs_ok {s : State} (hesi : s.gpr .esi = scr s₀) (hwr : s.wr = s₀.wr) :
    WP isa (.block ivs) s fun s' =>
      s'.gpr .esi = s.gpr .esi ∧ s'.gpr .edi = s.gpr .edi ∧ s'.gpr .esp = s.gpr .esp ∧
      s'.gpr .ebp = s.gpr .ebp ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = ivMem s.mem (scr s₀) := by
  have fV := hp.scr_fits
  have hw : ∀ k, 8 ≤ k → k < 16 → InRegions s.wr (addr (scr s₀) (vOff k)) 4 := fun k _ hk =>
    hp.in_scr hwr (by simp only [vOff]; omega)
  have w8 := hw 8 (by omega) (by omega)
  have w9 := hw 9 (by omega) (by omega)
  have w10 := hw 10 (by omega) (by omega)
  have w11 := hw 11 (by omega) (by omega)
  have w12 := hw 12 (by omega) (by omega)
  have w13 := hw 13 (by omega) (by omega)
  have w14 := hw 14 (by omega) (by omega)
  have w15 := hw 15 (by omega) (by omega)
  have r64 := mem_rd (rd := s.rd) (hp.in_scr (d := tloOff) hwr (by decide))
  have r68 := mem_rd (rd := s.rd) (hp.in_scr (d := thiOff) hwr (by decide))
  have r72 := mem_rd (rd := s.rd) (hp.in_scr (d := fOff) hwr (by decide))
  have hh : ∀ (m : Mem) (v : BitVec 32) (k d : Nat), k < 16 → 64 ≤ d → d + 4 ≤ 512 →
      (m.writeW (addr (scr s₀) (vOff k)) v).readW (addr (scr s₀) d) 32 = m.readW (addr (scr s₀) d) 32 :=
    fun m v k d h1 h2 h3 => rw_hi fV m v h1 h2 h3
  apply WP.of_runBlock
  simp (config := {decide := true}) only [ivs, at_, runBlock_cons, runStep_some,
    runBlock_nil, exec, execAlu, readSrc, ea_mk, State.load32, State.store32, RegUpd.gpr_setReg,
    RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.gpr_arithFlags,
    RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, hesi, w8, w9, w10, w11, w12,
    w13, w14, w15, r64, r68, r72, ite_true, ite_false, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, trivial, trivial, trivial, trivial, ?_⟩
  simp (disch := decide) only [hh]
  rfl

/-! ## The output -/

/-- `h[i] := v[i] ^ v[i + 8] ^ h[i]`. -/
def fn (i : Nat) : List Instr :=
  [.mov .ecx (.mem (at_ .esi (vOff i))), .alu .xor .ecx (.mem (at_ .esi (vOff (i + 8)))),
   .alu .xor .ecx (.mem (at_ .eax (4 * i))), .store (at_ .eax (4 * i)) .ecx]

omit hp in
theorem finish_eq : finish = .mov .eax (.mem (at_ .esp 4)) :: (List.range 8).flatMap fn := rfl

theorem fn_ok (i : Nat) (hi : i < 8) {s : State} (heax : s.gpr .eax = st s₀)
    (hesi : s.gpr .esi = scr s₀) (hwr : s.wr = s₀.wr) :
    WP isa (.block (fn i)) s fun s' =>
      (∀ r, r ≠ .ecx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.mem = s.mem.writeW (addr (st s₀) (4 * i)) (s.mem.readW (addr (scr s₀) (vOff i)) 32 ^^^
        s.mem.readW (addr (scr s₀) (vOff (i + 8))) 32 ^^^ s.mem.readW (addr (st s₀) (4 * i)) 32) := by
  refine wp_ldm hesi (mem_rd (hp.in_scr hwr (by simp only [vOff]; omega))) fun s₁ u₁ => ?_
  refine wp_xorm (by rw [u₁.other _ (by decide), hesi])
    (by rw [u₁.rd, u₁.wr]; exact mem_rd (hp.in_scr hwr (by simp only [vOff]; omega))) fun s₂ u₂ => ?_
  refine wp_xorm (by rw [u₂.other _ (by decide), u₁.other _ (by decide), heax])
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact mem_rd (hp.in_st hwr (by omega))) fun s₃ u₃ => ?_
  refine wp_stm (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), heax])
    (by rw [u₃.wr, u₂.wr, u₁.wr]; exact hp.in_st hwr (by omega)) fun s₄ u₄ => WP.block_nil ?_
  refine ⟨fun r hr => by rw [u₄.gpr, u₃.other r hr, u₂.other r hr, u₁.other r hr],
    by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd], by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr], ?_⟩
  rw [u₄.mem, u₃.gpr, u₃.mem, u₂.gpr, u₂.mem, u₁.gpr, u₁.mem]

/-- After words `0 … n-1` of the output. -/
structure FnInv (s₀ s : State) (n : Nat) (s' : State) : Prop where
  gpr : ∀ r, r ≠ .ecx → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  done : ∀ k < n, s'.mem.readW (addr (st s₀) (4 * k)) 32 = s.mem.readW (addr (scr s₀) (vOff k)) 32 ^^^
    s.mem.readW (addr (scr s₀) (vOff (k + 8))) 32 ^^^ s.mem.readW (addr (st s₀) (4 * k)) 32
  todo : ∀ k, n ≤ k → k < 8 → s'.mem.readW (addr (st s₀) (4 * k)) 32 = s.mem.readW (addr (st s₀) (4 * k)) 32
  frame : Frame [stR s₀] s.mem s'.mem

theorem fns_ok {s : State} (heax : s.gpr .eax = st s₀) (hesi : s.gpr .esi = scr s₀)
    (hwr : s.wr = s₀.wr) : ∀ n ≤ 8, WP isa (.block ((List.range n).flatMap fn)) s (FnInv s₀ s n) := by
  intro n hn
  have fS := hp.st_fits
  induction n with
  | zero => exact WP.block_nil ⟨fun _ _ => rfl, rfl, rfl, fun _ h => absurd h (by omega),
      fun _ _ _ => rfl, Frame.refl _ _⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun s₁ h₁ => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    refine WP.mono (fn_ok hp n (by omega) (by rw [h₁.gpr _ (by decide), heax])
      (by rw [h₁.gpr _ (by decide), hesi]) (by rw [h₁.wr, hwr])) fun s₂ ⟨g₂, r₂, w₂, m₂⟩ =>
      ⟨fun r hr => by rw [g₂ r hr, h₁.gpr r hr], by rw [r₂, h₁.rd], by rw [w₂, h₁.wr],
        fun k hk => ?_, fun k hk hk' => ?_, ?_⟩
    · rw [m₂, rw_word fS _ _ (by omega) (by omega)]
      by_cases hkn : n = k
      · subst hkn
        simp only [ite_true]
        rw [hp.work_frame h₁.frame (by simp only [vOff]; omega),
          hp.work_frame h₁.frame (by simp only [vOff]; omega), h₁.todo n (by omega) (by omega)]
      · simp only [hkn, ite_false]; exact h₁.done k (by omega)
    · rw [m₂, rw_word fS _ _ (by omega) (by omega)]
      simp only [show ¬ n = k by omega, ite_false]
      exact h₁.todo k (by omega) hk'
    · rw [m₂]
      exact h₁.frame.writeW (List.mem_singleton_self _) _ (hp.st_contains (by omega))

/-! ## Advancing -/

/-- The memory after `advance`. -/
def advMem (m : Mem) (B : BitVec 32) : Mem :=
  ((m.writeW (addr B tloOff) (m.readW (addr B tloOff) 32 + 64)).writeW (addr B thiOff)
    (m.readW (addr B thiOff) 32 + 0 + (BitVec.ofBool
      (decide (2 ^ 32 ≤ (m.readW (addr B tloOff) 32).toNat + (64 : BitVec 32).toNat))).setWidth 32)).writeW
    (addr B nOff) (m.readW (addr B nOff) 32 - 1)

theorem advance_ok {s : State} (hesi : s.gpr .esi = scr s₀) (hwr : s.wr = s₀.wr) :
    WP isa (.block advance) s fun s' =>
      s'.gpr .edi = s.gpr .edi + 64 ∧ s'.gpr .esi = s.gpr .esi ∧ s'.gpr .esp = s.gpr .esp ∧
      s'.gpr .ebp = s.gpr .ebp ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.zf = some (s.mem.readW (addr (scr s₀) nOff) 32 - 1 == 0) ∧
      s'.mem = advMem s.mem (scr s₀) := by
  have fV := hp.scr_fits
  have hr : ∀ d, d + 4 ≤ 512 → InRegions (s.rd ++ s.wr) (addr (scr s₀) d) 4 := fun d hd =>
    mem_rd (hp.in_scr hwr hd)
  have hw : ∀ d, d + 4 ≤ 512 → InRegions s.wr (addr (scr s₀) d) 4 := fun d hd => hp.in_scr hwr hd
  have r64 := hr tloOff (by decide)
  have r68 := hr thiOff (by decide)
  have r76 := hr nOff (by decide)
  have w64 := hw tloOff (by decide)
  have w68 := hw thiOff (by decide)
  have w76 := hw nOff (by decide)
  apply WP.of_runBlock
  simp (config := {decide := true}) only [advance, at_, runBlock_cons, runStep_some,
    runBlock_nil, exec, execAlu, readSrc, ea_mk, State.load32, State.store32, RegUpd.gpr_setReg,
    RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.gpr_arithFlags,
    RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, RegUpd.cf_setReg,
    RegUpd.cf_arithFlags, RegUpd.zf_setReg, RegUpd.zf_arithFlags, hesi, r64, r68, r76, w64, w68, w76,
    ite_true, ite_false, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, trivial, trivial, trivial, trivial, ?_, ?_⟩
  · simp (disch := decide) only [rw_scr fV]
  · simp (disch := decide) only [rw_scr fV]
    rfl

end

theorem holds_v0 {B : BitVec 32} (hfit : B.toNat + 512 ≤ 2 ^ 32) {m : Mem} {H : HashValue 32} {T : Nat}
    {f : Bool} (hH : ∀ k (hk : k < 8), m.readW (addr B (vOff k)) 32 = H[k])
    (hlo : m.readW (addr B tloOff) 32 = BitVec.ofNat 32 T)
    (hhi : m.readW (addr B thiOff) 32 = BitVec.ofNat 32 (T / 2 ^ 32))
    (hf : m.readW (addr B fOff) 32 = flagW f) : Holds B (V0 H T f) (ivMem m B) := by
  have fV : B.toNat + 64 ≤ 2 ^ 32 := by omega
  intro k hk
  rw [V0_get _ _ _ k hk]
  simp (disch := omega) only [ivMem, rw_slot fV]
  rw [hlo, hhi, hf]
  have : k < 8 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 := by omega
  rcases this with h8 | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [show ¬ 15 = k by omega, show ¬ 14 = k by omega, show ¬ 13 = k by omega,
      show ¬ 12 = k by omega, show ¬ 11 = k by omega, show ¬ 10 = k by omega, show ¬ 9 = k by omega,
      show ¬ 8 = k by omega, ite_false, h8, dite_true, hH k h8]
  all_goals simp (config := {decide := true}) only [ite_true, ite_false, dite_false]
  all_goals rfl

theorem frame_ivMem {B : BitVec 32} (hfit : B.toNat + 64 ≤ 2 ^ 32) (m : Mem) :
    Frame [workR B] m (ivMem m B) := by
  have ct : ∀ i < 16, (workR B).Contains (addr B (vOff i)) (32 / 8) := fun i hi =>
    contains_addr (by simp only [vOff]; omega) (by decide) hfit
  have hm := List.mem_singleton_self (workR B)
  simp only [ivMem]
  exact (((((((((Frame.refl _ _).writeW hm _ (ct 8 (by omega))).writeW hm _ (ct 9 (by omega))).writeW hm _
    (ct 10 (by omega))).writeW hm _ (ct 11 (by omega))).writeW hm _ (ct 12 (by omega))).writeW hm _
    (ct 13 (by omega))).writeW hm _ (ct 14 (by omega))).writeW hm _ (ct 15 (by omega)))

theorem xor_order (h a b : BitVec 32) : a ^^^ b ^^^ h = h ^^^ a ^^^ b := by
  rw [BitVec.xor_comm _ h, BitVec.xor_assoc]

/-! ## One block -/

theorem body_ok {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < nb s₀) {s : State} (hL : LInv s₀ i s) :
    WP isa body s fun s' =>
      (eval .ne s' = some false ∧ Common s₀ (nb s₀) s') ∨
      (eval .ne s' = some true ∧ i + 1 < nb s₀ ∧ LInv s₀ (i + 1) s') := by
  have fS := hp.st_fits
  have fV := hp.scr_fits
  have fV64 : (scr s₀).toNat + 64 ≤ 2 ^ 32 := by omega
  set H := stateAt 32 s.mem ((st s₀).setWidth 64) with hH
  set T := t₀ s₀ + i * 64 with hT
  have a0 : s.mem.readW (addr (esp₀ s₀) 4) 32 = st s₀ := hp.arg_frame hL.frame (i := 0) (by decide)
  -- Load the work vector.
  refine WP.seq ?_
  rw [load_eq, WP.block_append_iff]
  refine wp_ldm hL.esp (hp.in_arg hL.rd (by omega) (by omega)) fun s₁ u₁ => ?_
  rw [a0] at u₁
  refine WP.mono (cps_ok hp u₁.gpr (by rw [u₁.other _ (by decide), hL.esi]) (by rw [u₁.wr, hL.wr]) 8
    (Nat.le_refl _)) fun s₂ h₂ => ?_
  refine WP.mono (ivs_ok hp (by rw [h₂.gpr _ (by decide), u₁.other _ (by decide), hL.esi])
    (by rw [h₂.wr, u₁.wr, hL.wr])) fun s₃ ⟨e₁, e₂, e₃, e₄, e₅, e₆, e₇⟩ => ?_
  have g₃ : ∀ r, r ≠ .eax → r ≠ .ecx → s₂.gpr r = s.gpr r := fun r h1 h2 => by
    rw [h₂.gpr r h2, u₁.other r h1]
  have f₂ : Frame [workR (scr s₀)] s.mem s₂.mem := by rw [← u₁.mem]; exact h₂.frame
  have f₃ : Frame [workR (scr s₀)] s.mem s₃.mem := by rw [e₇]; exact f₂.trans (frame_ivMem fV64 _)
  have sw : ∀ r ∈ [workR (scr s₀)], ∃ r' ∈ [stR s₀, scrR s₀], Region.Sub r r' :=
    fun r hr => ⟨scrR s₀, by simp, by simp at hr; subst hr; exact Region.sub_prefix (by omega)⟩
  have hR : RS (scr s₀) (blkAddr s₀ i) (blk s₀ i) s (V0 H T (fl s₀)) s₃ := by
    refine ⟨by rw [e₁, g₃ _ (by decide) (by decide), hL.esi], by rw [e₂, g₃ _ (by decide) (by decide), hL.edi],
      by rw [e₃, g₃ _ (by decide) (by decide)], by rw [e₄, g₃ _ (by decide) (by decide)],
      by rw [e₅, h₂.rd, u₁.rd], by rw [e₆, h₂.wr, u₁.wr], ?_, ?_, f₃⟩
    · rw [e₇]
      refine holds_v0 fV (fun k hk => ?_) ?_ ?_ ?_
      · rw [h₂.done k hk, u₁.mem, hH, hp.stateAt_get _ hk]
      · rw [hp.high_frame (.inl f₂) (by decide) (by decide), hL.tlo]
      · rw [hp.high_frame (.inl f₂) (by decide) (by decide), hL.thi]
      · rw [hp.high_frame (.inl f₂) (by decide) (by decide), hL.flag]
    · exact hp.msg hi (hL.frame.trans (f₃.sub sw))
  have hc : Ctx (scr s₀) (blkAddr s₀ i) s.rd s.wr := by rw [hL.rd, hL.wr]; exact hp.ctx hi
  -- The rounds.
  refine WP.seq (WP.mono (rounds_ok hc hR 10) fun s₄ h₄ => ?_)
  set vR := (List.range 10).foldl (Spec.Blake2.round Spec.Blake2.s (blk s₀ i)) (V0 H T (fl s₀)) with hvR
  have f₄ : Frame [stR s₀, scrR s₀] s₀.mem s₄.mem := hL.frame.trans (h₄.frame.sub sw)
  -- The output, and advance.
  rw [finish_eq, List.cons_append]
  refine wp_ldm (by rw [h₄.esp, hL.esp]) (hp.in_arg (by rw [h₄.rd, hL.rd]) (by omega) (by omega))
    fun s₅ u₅ => ?_
  rw [WP.block_append_iff]
  rw [hp.arg_frame f₄ (i := 0) (by decide)] at u₅
  refine WP.mono (fns_ok hp u₅.gpr (by rw [u₅.other _ (by decide), h₄.esi])
    (by rw [u₅.wr, h₄.wr, hL.wr]) 8 (Nat.le_refl _)) fun s₆ h₆ => ?_
  have hesi₆ : s₆.gpr .esi = scr s₀ := by rw [h₆.gpr _ (by decide), u₅.other _ (by decide), h₄.esi]
  have hwr₆ : s₆.wr = s₀.wr := by rw [h₆.wr, u₅.wr, h₄.wr, hL.wr]
  refine advance_ok hp hesi₆ hwr₆ |>.mono fun s₇ ⟨d₁, d₂, d₃, d₄, d₅, d₆, d₇, d₈⟩ => ?_
  -- Registers
  have g₆ : ∀ r, r ≠ .eax → r ≠ .ecx → s₆.gpr r = s₄.gpr r := fun r h1 h2 => by
    rw [h₆.gpr r h2, u₅.other r h1]
  have hrd : s₇.rd = s₀.rd := by rw [d₅, h₆.rd, u₅.rd, h₄.rd, hL.rd]
  have hwr : s₇.wr = s₀.wr := by rw [d₆, hwr₆]
  -- Memory
  have hm₅ : s₅.mem = s₄.mem := u₅.mem
  have f₆ : Frame [stR s₀] s₄.mem s₆.mem := by rw [← hm₅]; exact h₆.frame
  have rA : ∀ d, d + 4 ≤ 512 → d ≠ tloOff → d ≠ thiOff → d ≠ nOff → (d % 4 = 0) →
      s₇.mem.readW (addr (scr s₀) d) 32 = s₆.mem.readW (addr (scr s₀) d) 32 := fun d hd h1 h2 h3 h4 => by
    rw [d₈]; simp only [advMem]
    rw [rw_scr fV _ _ hd (by decide) (by simp only [nOff] at h3 ⊢; omega),
      rw_scr fV _ _ hd (by decide) (by simp only [thiOff] at h2 ⊢; omega),
      rw_scr fV _ _ hd (by decide) (by simp only [tloOff] at h1 ⊢; omega)]
  have f₇ : Frame [stR s₀, scrR s₀] s₀.mem s₇.mem := by
    rw [d₈]; simp only [advMem]
    have hm : scrR s₀ ∈ [stR s₀, scrR s₀] := by simp
    exact (((f₄.trans (f₆.mono (by simp))).writeW hm _ (hp.scr_contains (by decide))).writeW hm _
      (hp.scr_contains (by decide))).writeW hm _ (hp.scr_contains (by decide))
  have hstate : stateAt 32 s₇.mem ((st s₀).setWidth 64) =
      Spec.Blake2.F Spec.Blake2.s H (blk s₀ i) T (fl s₀) := by
    refine hp.stateAt_ext fun k hk => ?_
    have e7 : s₇.mem.readW (addr (st s₀) (4 * k)) 32 = s₆.mem.readW (addr (st s₀) (4 * k)) 32 := by
      rw [d₈]; simp only [advMem]
      have sep : ∀ d, d + 4 ≤ 512 → Mem.Sep (addr (st s₀) (4 * k)) (32 / 8) (addr (scr s₀) d) (32 / 8) :=
        fun d hd => hp.st_scr.sep (hp.st_contains (by omega)) (hp.scr_contains hd)
      rw [Mem.readW_writeW_sep (sep _ (by decide)) (by decide),
        Mem.readW_writeW_sep (sep _ (by decide)) (by decide),
        Mem.readW_writeW_sep (sep _ (by decide)) (by decide)]
    rw [e7, h₆.done k hk, hm₅, h₄.holds k (by omega), h₄.holds (k + 8) (by omega),
      hp.st_frame h₄.frame (by omega), ← hp.stateAt_get _ hk, F_eq]
    simp only [Vector.getElem_ofFn]
    exact xor_order _ _ _
  have hsaved : Saved s₀ s₇.mem := by
    have s₆' : Saved s₀ s₆.mem :=
      hp.saved_frame (hp.saved_frame hL.saved (.inl h₄.frame)) (.inr f₆)
    obtain ⟨a1, a2, a3⟩ := s₆'
    exact ⟨(rA 80 (by omega) (by decide) (by decide) (by decide) rfl).trans a1,
      (rA 84 (by omega) (by decide) (by decide) (by decide) rfl).trans a2,
      (rA 88 (by omega) (by decide) (by decide) (by decide) rfl).trans a3⟩
  have k₆ : ∀ d, 64 ≤ d → d + 4 ≤ 512 → s₆.mem.readW (addr (scr s₀) d) 32 = s.mem.readW (addr (scr s₀) d) 32 :=
    fun d h1 h2 => by
      rw [hp.high_frame (.inr f₆) h1 h2, hp.high_frame (.inl h₄.frame) h1 h2]
  have hcommon : Common s₀ (i + 1) s₇ := by
    refine ⟨by rw [d₂, hesi₆], by rw [d₃, g₆ _ (by decide) (by decide), h₄.esp, hL.esp],
      by rw [d₄, g₆ _ (by decide) (by decide), h₄.ebp, hL.ebp], hrd, hwr, f₇, ?_, hsaved⟩
    rw [hstate, Proof.Blake2.compressBlocks_succ, ← hL.state]
    rfl
  have hnb : nb s₀ < 2 ^ 32 := (arg s₀ 2).isLt
  have hc1 : s₆.mem.readW (addr (scr s₀) nOff) 32 - 1 = BitVec.ofNat 32 (nb s₀ - (i + 1)) := by
    rw [k₆ _ (by decide) (by decide), hL.cnt, ofNat_pred (by omega), Nat.sub_sub]
  have hev : eval .ne s₇ = some (!(BitVec.ofNat 32 (nb s₀ - (i + 1)) == 0)) := by
    rw [Proof.MdStream.X86.eval_ne, d₇, hc1]; rfl
  by_cases hlast : i + 1 = nb s₀
  · left
    refine ⟨by rw [hev, hlast]; simp, hlast ▸ hcommon⟩
  · right
    have hne : nb s₀ - (i + 1) ≠ 0 := by omega
    have h0 : BitVec.ofNat 32 (nb s₀ - (i + 1)) ≠ 0 := by
      intro h
      have h' := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h'
      exact hne h'
    refine ⟨by rw [hev]; simpa using h0, by omega, ⟨hcommon, ?_, ?_, ?_, ?_, ?_⟩⟩
    · rw [d₁, g₆ _ (by decide) (by decide), h₄.edi]
      simp only [blkAddr]
      rw [BitVec.add_assoc, show (64 : BitVec 32) = BitVec.ofNat 32 64 from rfl, BitVec.ofNat_add_ofNat]
      rfl
    · rw [d₈]; simp only [advMem]
      rw [rw_scr fV _ _ (by decide) (by decide) (by decide), rw_scr fV _ _ (by decide) (by decide) (by decide),
        Mem.readW_writeW_self32, k₆ _ (by decide) (by decide), hL.tlo,
        show (64 : BitVec 32) = BitVec.ofNat 32 64 from rfl, ← BitVec.ofNat_add]
      congr 1; omega
    · rw [d₈]; simp only [advMem]
      rw [rw_scr fV _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32,
        k₆ _ (by decide) (by decide), k₆ _ (by decide) (by decide), hL.tlo, hL.thi,
        show ∀ x : BitVec 32, x + 0 = x from fun x => BitVec.add_zero x,
        show (64 : BitVec 32) = BitVec.ofNat 32 64 from rfl,
        Proof.Blake2.X86.Stream.carry_ofNat _ _ (by decide)]
      congr 2; omega
    · rw [rA _ (by decide) (by decide) (by decide) (by decide) rfl, k₆ _ (by decide) (by decide), hL.flag]
    · rw [d₈]; simp only [advMem]
      rw [Mem.readW_writeW_self32, hc1]

end VG.Proof.Blake2.X86.CompressS
