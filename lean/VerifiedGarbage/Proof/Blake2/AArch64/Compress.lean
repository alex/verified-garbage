import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Blake2.Spec
import VerifiedGarbage.Impl.Blake2.AArch64
import VerifiedGarbage.Spec.Blake2.Contract
import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Blake2.AArch64.Contract
import VerifiedGarbage.Proof.Blake2.AArch64.Lit

/-!
# BLAKE2 compression function on AArch64

Untrusted: everything here is checked by Lean. The proof is written once for
both word sizes, over the operand size `z` (`.x` for BLAKE2b, `.w` for
BLAKE2s, words of `z.bits` bits): each code shape is symbolically executed
once, for any registers and offsets (`g_ok` for every `G`, `ld_ok`, `iv_ok`,
`fin_ok` for every word), and only the load of the high word of the counter
(`hiW_ok`) is executed once per word size.

The loop is proven against `Proof.Blake2.compressAArch64` (`compress_correct`,
for any `P` whose rotations fit the word), which the streaming functions use
for their calls; `compressB_verified` and `compressS_verified` move it to the
shared contracts of `Spec/Blake2/Contract.lean`. Constant time is the taint
analysis on the literal code (`Lit.lean`).
-/

namespace VG.Proof.Blake2.AArch64

open VG VG.AArch64
open VG.Impl.Blake2.AArch64 (sz ws lbb wreg T loOff hiOff fOff saved movImm64)
open VG.Spec.Blake2 (Params Work Block HashValue)

/-! ## Words of `z.bits` bits -/

theorem sz_bits (z : Size) : sz z.bits = z := by cases z <;> rfl

theorem ws_bits (z : Size) : ws z.bits = z.bytes := by cases z <;> rfl

theorem bits_div (z : Size) : z.bits / 8 = z.bytes := by cases z <;> rfl

theorem bits_le (z : Size) : z.bits ≤ 64 := by cases z <;> decide

theorem bytes_le (z : Size) : z.bytes ≤ 8 := by cases z <;> decide

theorem ext_trunc (z : Size) (v : BitVec z.bits) : (v.setWidth 64).setWidth z.bits = v := by
  cases z
  · rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]
  · simp only [Size.bits, BitVec.setWidth_eq]

theorem trunc_ofNat (z : Size) (n : Nat) : (BitVec.ofNat 64 n).setWidth z.bits = BitVec.ofNat z.bits n := by
  cases z
  · simp only [Size.bits]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [Nat.mod_mod_of_dvd _ (by decide)]
  · exact BitVec.setWidth_eq _

theorem off_ok (z : Size) {j : Nat} (hj : j < 4096) :
    z.bytes * j % z.bytes = 0 ∧ z.bytes * j < 4096 * z.bytes :=
  ⟨Nat.mul_mod_right _ _, by cases z <;> simp only [Size.bytes] <;> omega⟩

theorem ext64 (v : BitVec Size.x.bits) : v.setWidth 64 = v := BitVec.setWidth_eq v

theorem exec_ldr {z : Size} {s : State} {t n : Reg} {off : Nat}
    (ho : off % z.bytes = 0 ∧ off < 4096 * z.bytes)
    (h : InRegions (s.rd ++ s.wr) (s.gpr n + BitVec.ofNat 64 off) z.bytes) :
    exec (.ldr z t n off) s = some (s.write z t (s.mem.readW (s.gpr n + BitVec.ofNat 64 off) z.bits)) := by
  cases z
  · exact exec_ldr_w ho h
  · exact exec_ldr_x ho h

theorem exec_str {z : Size} {s : State} {t n : Reg} {off : Nat}
    (ho : off % z.bytes = 0 ∧ off < 4096 * z.bytes)
    (h : InRegions s.wr (s.gpr n + BitVec.ofNat 64 off) z.bytes) :
    exec (.str z t n off) s =
      some { s with mem := s.mem.writeW (s.gpr n + BitVec.ofNat 64 off) ((s.gpr t).setWidth z.bits) } := by
  cases z
  · exact exec_str_w ho h
  · rw [exec_str_x ho h]; simp

theorem exec_ror {z : Size} {s : State} {d n : Reg} {sh : Nat} (h : sh < z.bits) :
    exec (.ror z d n sh) s = some (s.write z d ((s.read z n).rotateRight sh)) := by
  simp [exec, h]

theorem readW_writeW_self (z : Size) (m : Mem) (a : Addr) (v : BitVec z.bits) :
    (m.writeW a v).readW a z.bits = v := by
  cases z
  · exact Mem.readW_writeW_self32 m a v
  · exact Mem.readW_writeW_self64 m a v

/-! ## One `G` -/

section G
variable {z : Size} (P : Params z.bits)

/-- The rotations of `P` are encodable at the word size. -/
def ROk : Prop := P.R1 < z.bits ∧ P.R2 < z.bits ∧ P.R3 < z.bits ∧ P.R4 < z.bits

/-- `G` on the registers `a, b, c, d`, symbolically executed once for all of
them (all different, and different from `T` and `x1`). -/
theorem g_ok (hR : ROk P) {a b c d : Reg}
    (hs : [a, b, c, d, T, .x1].Nodup) {j k : Nat} (hj : j < 16) (hk : k < 16)
    (s : State) (va vb vc vd x y : BitVec z.bits) (p : Addr)
    (ha : s.gpr a = va.setWidth 64) (hb : s.gpr b = vb.setWidth 64)
    (hc : s.gpr c = vc.setWidth 64) (hd : s.gpr d = vd.setWidth 64) (hx1 : s.gpr .x1 = p)
    (hij : InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 (z.bytes * j)) z.bytes)
    (hik : InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 (z.bytes * k)) z.bytes)
    (hx : s.mem.readW (p + BitVec.ofNat 64 (z.bytes * j)) z.bits = x)
    (hy : s.mem.readW (p + BitVec.ofNat 64 (z.bytes * k)) z.bits = y) :
    WP isa (.block (Impl.Blake2.AArch64.g P a b c d j k)) s fun s' =>
      s'.gpr a = (mix P va vb vc vd x y).1.setWidth 64 ∧
      s'.gpr b = (mix P va vb vc vd x y).2.1.setWidth 64 ∧
      s'.gpr c = (mix P va vb vc vd x y).2.2.1.setWidth 64 ∧
      s'.gpr d = (mix P va vb vc vd x y).2.2.2.setWidth 64 ∧
      (∀ r, r ≠ a → r ≠ b → r ≠ c → r ≠ d → r ≠ T → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨h1, h2, h3, h4⟩ := hR
  have hs' := VG.nodup_reverse hs
  have oj := off_ok z (j := j) (by omega)
  have ok := off_ok z (j := k) (by omega)
  simp only [T, List.nodup_cons, List.mem_cons, List.not_mem_nil, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.cons_append, or_false, not_or,
    List.nodup_nil, and_true] at hs hs'
  apply WP.of_runBlock
  simp only [Impl.Blake2.AArch64.g, sz_bits, ws_bits, T]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil,
    exec_add, exec_logic, exec_ror h1, exec_ror h2, exec_ror h3, exec_ror h4, exec_ldr oj,
    exec_ldr ok, isa, State.read, RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write,
    RegUpd.wr_write, ite_true, ite_false, hs, hs', ha, hb, hc, hd, hx1, hij, hik, hx, hy,
    ext_trunc, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  and_intros
  · intro r ra rb rc rd rt
    simp only [ra, rb, rc, rd, rt, ite_false]
  · trivial

end G

/-! ## The work vector in registers -/

/-- The registers of the work vector. -/
def wregs : List Reg :=
  [.x3, .x4, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17, .x25, .x26]

theorem wreg_mem' : ∀ k < 16, wreg k ∈ wregs := by decide

theorem wreg_mem {k : Nat} (hk : k < 16) : wreg k ∈ wregs := wreg_mem' k hk

theorem wreg_inj' : ∀ i < 16, ∀ j < 16, wreg i = wreg j → i = j := by decide

theorem wreg_ne {i j : Nat} (hi : i < 16) (hj : j < 16) (h : i ≠ j) : wreg i ≠ wreg j :=
  fun e => h (wreg_inj' i hi j hj e)

theorem ne_wreg {q : Reg} (hq : q ∉ wregs) {k : Nat} (hk : k < 16) : q ≠ wreg k :=
  fun e => hq (by rw [e]; exact wreg_mem hk)

theorem T_not_mem : T ∉ wregs := by decide

theorem wreg_ne_T {k : Nat} (hk : k < 16) : wreg k ≠ T :=
  fun e => T_not_mem (e ▸ wreg_mem hk)

theorem wreg_ne_x1 {k : Nat} (hk : k < 16) : wreg k ≠ .x1 :=
  fun e => (by decide : Reg.x1 ∉ wregs) (e ▸ wreg_mem hk)

section Rounds
variable {z : Size} (P : Params z.bits)

/-- The work vector `v` is in its registers. -/
def Vars (s : State) (v : Work z.bits) : Prop :=
  ∀ k (hk : k < 16), s.gpr (wreg k) = v[k].setWidth 64

/-- The rounds invariant, relative to the state `sB` at their start: the work
vector `v` is in its registers, and nothing else has changed but `T`. -/
structure RI (sB : State) (v : Work z.bits) (s : State) : Prop where
  vars : Vars s v
  other : ∀ q, q ∉ wregs → q ≠ T → s.gpr q = sB.gpr q
  mem : s.mem = sB.mem
  rd : s.rd = sB.rd
  wr : s.wr = sB.wr

/-- The message block `M` is at `p`, in the permitted regions. -/
structure Msg (M : Block z.bits) (p : Addr) (s : State) : Prop where
  x1 : s.gpr .x1 = p
  inr : ∀ j < 16, InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 (z.bytes * j)) z.bytes
  word : ∀ j (hj : j < 16), s.mem.readW (p + BitVec.ofNat 64 (z.bytes * j)) z.bits = M ⟨j, hj⟩

theorem Msg.of_RI {M : Block z.bits} {p : Addr} {sB s : State} {v : Work z.bits} (h : Msg M p sB)
    (hr : RI sB v s) : Msg M p s :=
  ⟨(hr.other _ (by decide) (by decide)).trans h.x1, by rw [hr.rd, hr.wr]; exact h.inr,
    by rw [hr.mem]; exact h.word⟩

theorem gAt_ok (hR : ROk P) {x y c d : Nat} (hx : x < 16) (hy : y < 16) (hc : c < 16) (hd : d < 16)
    (hq : [x, y, c, d].Nodup) (r i : Nat) {M : Block z.bits} {p : Addr} {sB s : State}
    {v : Work z.bits} (hM : Msg M p sB) (h : RI sB v s) :
    WP isa (Impl.Blake2.AArch64.gAt P r i x y c d) s (RI sB (Spec.Blake2.G P v ⟨x, hx⟩ ⟨y, hy⟩
      ⟨c, hc⟩ ⟨d, hd⟩ (M (Spec.Blake2.sigmaAt r (2 * i))) (M (Spec.Blake2.sigmaAt r (2 * i + 1))))) := by
  have hm := hM.of_RI h
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hq
  obtain ⟨⟨nxy, nxc, nxd⟩, ⟨nyc, nyd⟩, ncd, -⟩ := hq
  have hs : [wreg x, wreg y, wreg c, wreg d, T, .x1].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true]
    exact ⟨⟨wreg_ne hx hy nxy, wreg_ne hx hc nxc, wreg_ne hx hd nxd, wreg_ne_T hx, wreg_ne_x1 hx⟩,
      ⟨wreg_ne hy hc nyc, wreg_ne hy hd nyd, wreg_ne_T hy, wreg_ne_x1 hy⟩,
      ⟨wreg_ne hc hd ncd, wreg_ne_T hc, wreg_ne_x1 hc⟩, ⟨wreg_ne_T hd, wreg_ne_x1 hd⟩, by decide⟩
  have sj := (Spec.Blake2.sigmaAt r (2 * i)).isLt
  have sk := (Spec.Blake2.sigmaAt r (2 * i + 1)).isLt
  refine WP.mono (g_ok P hR hs sj sk s v[x] v[y] v[c] v[d] _ _ p (h.vars x hx) (h.vars y hy)
    (h.vars c hc) (h.vars d hd) hm.x1 (hm.inr _ sj) (hm.inr _ sk) (hm.word _ sj) (hm.word _ sk))
    fun s' ⟨ha, hb, hc', hd', ho, hmem, hrd, hwr⟩ => ⟨fun k hk => ?_, fun q hq hT => ?_,
      hmem.trans h.mem, hrd.trans h.rd, hwr.trans h.wr⟩
  · rw [G_get P v (a := ⟨x, hx⟩) (b := ⟨y, hy⟩) (c := ⟨c, hc⟩) (d := ⟨d, hd⟩) nxy nxc nxd nyc nyd
      ncd _ _ k hk]
    simp only
    by_cases ey : y = k
    · subst ey; simp only [ite_true]; exact hb
    by_cases ec : c = k
    · subst ec; simp only [ey, ite_true, ite_false]; exact hc'
    by_cases ed : d = k
    · subst ed; simp only [ey, ec, ite_true, ite_false]; exact hd'
    by_cases ex : x = k
    · subst ex; simp only [ey, ec, ed, ite_true, ite_false]; exact ha
    simp only [ey, ec, ed, ex, ite_false]
    rw [ho _ (wreg_ne hk hx (Ne.symm ex)) (wreg_ne hk hy (Ne.symm ey)) (wreg_ne hk hc (Ne.symm ec))
      (wreg_ne hk hd (Ne.symm ed)) (wreg_ne_T hk)]
    exact h.vars k hk
  · have ne : ∀ {k}, k < 16 → q ≠ wreg k := fun hk e => hq (e ▸ wreg_mem hk)
    rw [ho q (ne hx) (ne hy) (ne hc) (ne hd) hT]; exact h.other q hq hT

theorem round_ok (hR : ROk P) (r : Nat) {M : Block z.bits} {p : Addr} {sB s : State}
    {v : Work z.bits} (hM : Msg M p sB) (h : RI sB v s) :
    WP isa (Impl.Blake2.AArch64.round P r) s (RI sB (Spec.Blake2.round P M v r)) := by
  unfold Impl.Blake2.AArch64.round
  refine WP.seq (WP.mono (gAt_ok P hR (x := 0) (y := 4) (c := 8) (d := 12) (by decide) (by decide)
    (by decide) (by decide) (by decide) r 0 hM h) fun s h => ?_)
  refine WP.seq (WP.mono (gAt_ok P hR (x := 1) (y := 5) (c := 9) (d := 13) (by decide) (by decide)
    (by decide) (by decide) (by decide) r 1 hM h) fun s h => ?_)
  refine WP.seq (WP.mono (gAt_ok P hR (x := 2) (y := 6) (c := 10) (d := 14) (by decide) (by decide)
    (by decide) (by decide) (by decide) r 2 hM h) fun s h => ?_)
  refine WP.seq (WP.mono (gAt_ok P hR (x := 3) (y := 7) (c := 11) (d := 15) (by decide) (by decide)
    (by decide) (by decide) (by decide) r 3 hM h) fun s h => ?_)
  refine WP.seq (WP.mono (gAt_ok P hR (x := 0) (y := 5) (c := 10) (d := 15) (by decide) (by decide)
    (by decide) (by decide) (by decide) r 4 hM h) fun s h => ?_)
  refine WP.seq (WP.mono (gAt_ok P hR (x := 1) (y := 6) (c := 11) (d := 12) (by decide) (by decide)
    (by decide) (by decide) (by decide) r 5 hM h) fun s h => ?_)
  refine WP.seq (WP.mono (gAt_ok P hR (x := 2) (y := 7) (c := 8) (d := 13) (by decide) (by decide)
    (by decide) (by decide) (by decide) r 6 hM h) fun s h => ?_)
  refine WP.mono (gAt_ok P hR (x := 3) (y := 4) (c := 9) (d := 14) (by decide) (by decide)
    (by decide) (by decide) (by decide) r 7 hM h) fun s h => ?_
  exact h

theorem rounds_ok (hR : ROk P) {M : Block z.bits} {p : Addr} {sB : State} {v : Work z.bits}
    (hM : Msg M p sB) (h : RI sB v sB) (n : Nat) :
    WP isa (Impl.Blake2.AArch64.rounds P n) sB
      (RI sB ((List.range n).foldl (Spec.Blake2.round P M) v)) := by
  induction n with
  | zero => exact WP.block_nil (M := isa) h
  | succ n ih =>
    refine WP.seq (WP.mono ih fun s hs => ?_)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact round_ok P hR n hM hs

end Rounds

/-! ## Initializing the work vector -/

section Init
variable {z : Size} (P : Params z.bits)

/-- Words `0 … n-1` of the work vector `v` are in their registers. -/
def PVars (s : State) (v : Work z.bits) (n : Nat) : Prop :=
  ∀ k (hk : k < 16), k < n → s.gpr (wreg k) = v[k].setWidth 64

theorem PVars.step {s s' : State} {v : Work z.bits} {n : Nat} (hn : n < 16) (h : PVars s v n)
    (hw : s'.gpr (wreg n) = v[n].setWidth 64) (ho : ∀ q, q ≠ wreg n → s'.gpr q = s.gpr q) :
    PVars s' v (n + 1) := by
  intro k hk hkn
  by_cases e : k = n
  · subst e; exact hw
  · rw [ho _ (wreg_ne hk hn e)]; exact h k hk (by omega)

/-- What a block that writes one register leaves: the rest of the registers,
the memory and the regions. -/
def Only (d : Reg) (s s' : State) : Prop :=
  (∀ q, q ≠ d → s'.gpr q = s.gpr q) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr

theorem Only.gpr {d : Reg} {s s' : State} (h : Only d s s') {q : Reg} (hq : q ≠ d) :
    s'.gpr q = s.gpr q := h.1 q hq

theorem ld_ok (n : Nat) (hn : n < 8) (s : State) (st : Addr) (hx0 : s.gpr .x0 = st)
    (hin : InRegions (s.rd ++ s.wr) (st + BitVec.ofNat 64 (z.bytes * n)) z.bytes) :
    WP isa (.block [.ldr (sz z.bits) (wreg n) .x0 (ws z.bits * n)]) s fun s' =>
      s'.gpr (wreg n) = (s.mem.readW (st + BitVec.ofNat 64 (z.bytes * n)) z.bits).setWidth 64 ∧
      Only (wreg n) s s' := by
  have o := off_ok z (j := n) (by omega)
  apply WP.of_runBlock
  simp only [sz_bits, ws_bits, runBlock_cons, runStep_some, runBlock_nil, exec_ldr o, isa, hx0, hin,
    Option.some.injEq, exists_eq_left', RegUpd.gpr_write_self]
  exact ⟨trivial, fun q hq => RegUpd.gpr_write_of_ne _ _ _ hq, rfl, rfl, rfl⟩

theorem lds_ok (s : State) (st : Addr) (hx0 : s.gpr .x0 = st)
    (hin : ∀ k < 8, InRegions (s.rd ++ s.wr) (st + BitVec.ofNat 64 (z.bytes * k)) z.bytes)
    (v : Work z.bits)
    (hv : ∀ k (hk : k < 8), s.mem.readW (st + BitVec.ofNat 64 (z.bytes * k)) z.bits = v[k]) :
    ∀ n ≤ 8, WP isa (Impl.Blake2.AArch64.lds (w := z.bits) n) s fun s' =>
      PVars s' v n ∧ (∀ q, q ∉ wregs → s'.gpr q = s.gpr q) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  intro n hn
  induction n with
  | zero => exact WP.block_nil (M := isa) ⟨fun _ _ h => absurd h (by omega), fun _ _ => rfl, rfl, rfl, rfl⟩
  | succ n ih =>
    refine WP.seq (WP.mono (ih (by omega)) fun s₁ ⟨hp, ho, hm, hrd, hwr⟩ => ?_)
    refine WP.mono (ld_ok n (by omega) s₁ st (by rw [ho _ (by decide), hx0])
      (by rw [hrd, hwr]; exact hin n (by omega))) fun s₂ ⟨hw, h₂⟩ => ?_
    refine ⟨hp.step (by omega) (by rw [hw, hm, hv n (by omega)]) h₂.1,
      fun q hq => ?_, h₂.2.1.trans hm, h₂.2.2.1.trans hrd, h₂.2.2.2.trans hwr⟩
    rw [h₂.gpr (ne_wreg hq (by omega)), ho q hq]

theorem iv_ok (d : Reg) (x : BitVec 64) (s : State) :
    WP isa (.block (movImm64 d x)) s fun s' => s'.gpr d = x ∧ Only d s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [movImm64, runBlock_cons, runStep_some, runBlock_nil, exec,
    isa, State.read, RegUpd.gpr_write_self, Size.bits, ite_true, BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
  refine ⟨movz_movk64' x, fun q hq => ?_, rfl, rfl, rfl⟩
  simp only [RegUpd.gpr_write_of_ne _ _ _ hq]

theorem iv_getD {n : Nat} (hn : n < 8) : (P.IV.toList.getD n 0).setWidth 64 = P.IV[n].setWidth 64 := by
  simp [List.getD_eq_getElem?_getD, hn]

theorem ivs_ok (s : State) (v : Work z.bits) (hv : ∀ k (hk : k < 8), v[k + 8] = P.IV[k]) (hp : PVars s v 8) :
    ∀ n ≤ 8, WP isa (Impl.Blake2.AArch64.ivs P n) s fun s' =>
      PVars s' v (n + 8) ∧ (∀ q, q ∉ wregs → s'.gpr q = s.gpr q) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  intro n hn
  induction n with
  | zero => exact WP.block_nil (M := isa) ⟨hp, fun _ _ => rfl, rfl, rfl, rfl⟩
  | succ n ih =>
    refine WP.seq (WP.mono (ih (by omega)) fun s₁ ⟨hp, ho, hm, hrd, hwr⟩ => ?_)
    refine WP.mono (iv_ok _ _ s₁) fun s₂ ⟨hw, h₂⟩ => ?_
    refine ⟨?_, fun q hq => ?_, h₂.2.1.trans hm, h₂.2.2.1.trans hrd, h₂.2.2.2.trans hwr⟩
    · rw [show n + 1 + 8 = n + 8 + 1 by omega]
      exact hp.step (by omega) (by rw [hw, iv_getD P (by omega), hv n (by omega)]) h₂.1
    · rw [h₂.gpr (ne_wreg hq (by omega)), ho q hq]

/-- The scratch words the body reads: the counter `N` (its low 64 bits, and
the bits above) and the flag word `fl`. -/
structure Scr (scr : Addr) (N : Nat) (fl : BitVec 64) (s : State) : Prop where
  x5 : s.gpr .x5 = scr
  inLo : InRegions (s.rd ++ s.wr) (scr + BitVec.ofNat 64 loOff) 8
  inHi : InRegions (s.rd ++ s.wr) (scr + BitVec.ofNat 64 hiOff) 8
  inF : InRegions (s.rd ++ s.wr) (scr + BitVec.ofNat 64 fOff) 8
  lo : s.mem.readW (scr + BitVec.ofNat 64 loOff) 64 = BitVec.ofNat 64 N
  hi : s.mem.readW (scr + BitVec.ofNat 64 hiOff) 64 = BitVec.ofNat 64 (N / 2 ^ 64)
  f : s.mem.readW (scr + BitVec.ofNat 64 fOff) 64 = fl

theorem wreg12 : wreg 12 = .x16 := rfl
theorem wreg13 : wreg 13 = .x17 := rfl
theorem wreg14 : wreg 14 = .x25 := rfl

theorem ctrLo_ok {scr : Addr} {N : Nat} {fl : BitVec 64} (s : State) (hs : Scr scr N fl s)
    (a : BitVec z.bits) (ha : s.gpr (wreg 12) = a.setWidth 64) :
    WP isa (.block (Impl.Blake2.AArch64.ctrLo (w := z.bits))) s fun s' =>
      s'.gpr (wreg 12) = (a ^^^ BitVec.ofNat z.bits N).setWidth 64 ∧
      (∀ q, q ≠ wreg 12 → q ≠ T → s'.gpr q = s.gpr q) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  simp only [wreg12] at ha ⊢
  apply WP.of_runBlock
  simp (config := {decide := true}) only [Impl.Blake2.AArch64.ctrLo, sz_bits, wreg12, T,
    runBlock_cons, runStep_some, runBlock_nil, exec_ldr_x (show loOff % 8 = 0 ∧ loOff < 32768 by decide),
    exec_logic, isa, State.read, RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    ext64, ite_true, ite_false, hs.x5, hs.inLo, hs.lo, ha, ext_trunc, trunc_ofNat,
    Option.some.injEq, exists_eq_left']
  and_intros
  all_goals first | trivial | (intro q h1 h2; simp only [h1, h2, ite_false])

theorem hiW_ok {scr : Addr} {N : Nat} {fl : BitVec 64} (s : State) (hs : Scr scr N fl s) :
    WP isa (.block (Impl.Blake2.AArch64.hiW (w := z.bits))) s fun s' =>
      (s'.gpr T).setWidth z.bits = BitVec.ofNat z.bits (N / 2 ^ z.bits) ∧
      (∀ q, q ≠ T → s'.gpr q = s.gpr q) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  cases z
  · simp (config := {decide := true}) only [Impl.Blake2.AArch64.hiW, T, Size.bits,
      runBlock_cons, runStep_some, runBlock_nil, exec_ldr_x (show loOff % 8 = 0 ∧ loOff < 32768 by decide),
      exec_lsr_x (show 32 < 64 by decide), isa, State.read, RegUpd.gpr_write, RegUpd.mem_write,
      RegUpd.rd_write, RegUpd.wr_write, ite_true, ite_false, hs.x5, hs.inLo, hs.lo,
      BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
    refine ⟨?_, fun q h1 => ?_, trivial⟩
    · apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
        Nat.shiftRight_eq_div_pow]
      rw [show 2 ^ 64 = 2 ^ 32 * 2 ^ 32 by decide, Nat.mod_mul_right_div_self, Nat.mod_mod]
    · simp only [h1, ite_false]
  · simp (config := {decide := true}) only [Impl.Blake2.AArch64.hiW, T, Size.bits,
      runBlock_cons, runStep_some, runBlock_nil, exec_ldr_x (show hiOff % 8 = 0 ∧ hiOff < 32768 by decide),
      isa, RegUpd.gpr_write, RegUpd.mem_write,
      RegUpd.rd_write, RegUpd.wr_write, ite_true, hs.x5, hs.inHi, hs.hi,
      BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
    refine ⟨trivial, fun q h1 => ?_, trivial⟩
    simp only [h1, ite_false]

theorem ctrHi_ok {scr : Addr} {N : Nat} {fl : BitVec 64} (s : State) (hs : Scr scr N fl s)
    (a b c : BitVec z.bits) (ha : s.gpr (wreg 13) = a.setWidth 64) (hc : s.gpr (wreg 14) = c.setWidth 64)
    (hb : (s.gpr T).setWidth z.bits = b) :
    WP isa (.block (Impl.Blake2.AArch64.ctrHi (w := z.bits))) s fun s' =>
      s'.gpr (wreg 13) = (a ^^^ b).setWidth 64 ∧ s'.gpr (wreg 14) = (c ^^^ fl.setWidth z.bits).setWidth 64 ∧
      (∀ q, q ≠ wreg 13 → q ≠ wreg 14 → q ≠ T → s'.gpr q = s.gpr q) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  simp only [wreg13, wreg14] at ha hc ⊢
  apply WP.of_runBlock
  simp (config := {decide := true}) only [Impl.Blake2.AArch64.ctrHi, sz_bits, wreg13, wreg14, T,
    runBlock_cons, runStep_some, runBlock_nil, exec_ldr_x (show fOff % 8 = 0 ∧ fOff < 32768 by decide),
    exec_logic, isa, State.read, RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    ext64, ite_true, ite_false, hs.x5, hs.inF, hs.f, ha, hc, ext_trunc,
    Option.some.injEq, exists_eq_left']
  simp only [T] at hb
  and_intros
  all_goals first | trivial | (intro q h1 h2 h3; simp only [h1, h2, h3, ite_false]) | rw [hb]

end Init

/-! ## The work vector of `F` -/

section InitV
variable {w : Nat} (P : Params w)

/-- The work vector at the start of the rounds of `F` (RFC 7693 §3.2). -/
def initV (h : HashValue w) (t : Nat) (f : Bool) : Work w :=
  let v : Work w := h ++ P.IV
  let v := v.set 12 (v[12] ^^^ BitVec.ofNat w t)
  let v := v.set 13 (v[13] ^^^ BitVec.ofNat w (t / 2 ^ w))
  if f then v.set 14 (v[14] ^^^ BitVec.allOnes w) else v

theorem F_eq (h : HashValue w) (m : Block w) (t : Nat) (f : Bool) :
    Spec.Blake2.F P h m t f =
      Vector.ofFn fun i => h[i] ^^^ ((List.range P.r).foldl (Spec.Blake2.round P m) (initV P h t f))[i] ^^^
        ((List.range P.r).foldl (Spec.Blake2.round P m) (initV P h t f))[i.val + 8] := rfl

/-- The flag word. -/
def flagW (w : Nat) (f : Bool) : BitVec w := if f then BitVec.allOnes w else 0

theorem initV_get (h : HashValue w) (t : Nat) (f : Bool) (k : Nat) (hk : k < 16) :
    (initV P h t f)[k] =
      if k = 12 then (h ++ P.IV)[12] ^^^ BitVec.ofNat w t
      else if k = 13 then (h ++ P.IV)[13] ^^^ BitVec.ofNat w (t / 2 ^ w)
      else if k = 14 then (h ++ P.IV)[14] ^^^ flagW w f
      else (h ++ P.IV)[k] := by
  unfold initV flagW
  by_cases e12 : k = 12
  · subst e12; cases f <;> simp
  by_cases e13 : k = 13
  · subst e13; cases f <;> simp
  by_cases e14 : k = 14
  · subst e14; cases f <;> simp
  cases f <;> simp [e12, e13, e14, Ne.symm e12, Ne.symm e13, Ne.symm e14]

end InitV

theorem flagW_trunc (z : Size) (f : Bool) : (flagW 64 f).setWidth z.bits = flagW z.bits f := by
  cases f <;> cases z <;> simp [flagW] <;> rfl

section Init2
variable {z : Size} (P : Params z.bits)

theorem init_ok {scr st : Addr} {N : Nat} {f : Bool} (s : State) (hs : Scr scr N (flagW 64 f) s)
    (hx0 : s.gpr .x0 = st)
    (hin : ∀ k < 8, InRegions (s.rd ++ s.wr) (st + BitVec.ofNat 64 (z.bytes * k)) z.bytes)
    (h : HashValue z.bits)
    (hh : ∀ k (hk : k < 8), s.mem.readW (st + BitVec.ofNat 64 (z.bytes * k)) z.bits = h[k]) :
    WP isa (Impl.Blake2.AArch64.init P) s fun s' =>
      Vars s' (initV P h N f) ∧ (∀ q, q ∉ wregs → q ≠ T → s'.gpr q = s.gpr q) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hv : ∀ k (hk : k < 8), s.mem.readW (st + BitVec.ofNat 64 (z.bytes * k)) z.bits = (h ++ P.IV)[k] :=
    fun k hk => by rw [hh k hk, Vector.getElem_append_left hk]
  refine WP.seq (WP.mono (lds_ok s st hx0 hin _ hv 8 (Nat.le_refl _)) fun s₁ ⟨hp₁, ho₁, hm₁, hrd₁, hwr₁⟩ => ?_)
  refine WP.seq (WP.mono (ivs_ok P s₁ (h ++ P.IV) (fun k hk => by
      rw [Vector.getElem_append_right (by omega) (by omega)]; simp) hp₁ 8 (Nat.le_refl _))
    fun s₂ ⟨hp₂, ho₂, hm₂, hrd₂, hwr₂⟩ => ?_)
  have o₂ : ∀ q, q ∉ wregs → s₂.gpr q = s.gpr q := fun q hq => (ho₂ q hq).trans (ho₁ q hq)
  have hs₂ : Scr scr N (flagW 64 f) s₂ :=
    ⟨(o₂ _ (by decide)).trans hs.x5, by rw [hrd₂, hwr₂, hrd₁, hwr₁]; exact hs.inLo,
      by rw [hrd₂, hwr₂, hrd₁, hwr₁]; exact hs.inHi, by rw [hrd₂, hwr₂, hrd₁, hwr₁]; exact hs.inF,
      by rw [hm₂, hm₁]; exact hs.lo, by rw [hm₂, hm₁]; exact hs.hi, by rw [hm₂, hm₁]; exact hs.f⟩
  refine WP.seq (WP.mono (ctrLo_ok s₂ hs₂ _ (hp₂ 12 (by decide) (by decide)))
    fun s₃ ⟨h12, ho₃, hm₃, hrd₃, hwr₃⟩ => ?_)
  have hs₃ : Scr scr N (flagW 64 f) s₃ :=
    ⟨(ho₃ _ (by decide) (by decide)).trans hs₂.x5, by rw [hrd₃, hwr₃]; exact hs₂.inLo,
      by rw [hrd₃, hwr₃]; exact hs₂.inHi, by rw [hrd₃, hwr₃]; exact hs₂.inF,
      by rw [hm₃]; exact hs₂.lo, by rw [hm₃]; exact hs₂.hi, by rw [hm₃]; exact hs₂.f⟩
  refine WP.seq (WP.mono (hiW_ok s₃ hs₃) fun s₄ ⟨hT, ho₄, hm₄, hrd₄, hwr₄⟩ => ?_)
  have hs₄ : Scr scr N (flagW 64 f) s₄ :=
    ⟨(ho₄ _ (by decide)).trans hs₃.x5, by rw [hrd₄, hwr₄]; exact hs₃.inLo,
      by rw [hrd₄, hwr₄]; exact hs₃.inHi, by rw [hrd₄, hwr₄]; exact hs₃.inF,
      by rw [hm₄]; exact hs₃.lo, by rw [hm₄]; exact hs₃.hi, by rw [hm₄]; exact hs₃.f⟩
  refine WP.mono (ctrHi_ok s₄ hs₄ (h ++ P.IV)[13] _ (h ++ P.IV)[14]
    (by rw [ho₄ _ (by decide), ho₃ _ (by decide) (by decide)]; exact hp₂ 13 (by decide) (by decide))
    (by rw [ho₄ _ (by decide), ho₃ _ (by decide) (by decide)]; exact hp₂ 14 (by decide) (by decide)) hT)
    fun s₅ ⟨h13, h14, ho₅, hm₅, hrd₅, hwr₅⟩ => ?_
  refine ⟨fun k hk => ?_, fun q hq hT => ?_, by rw [hm₅, hm₄, hm₃, hm₂, hm₁],
    by rw [hrd₅, hrd₄, hrd₃, hrd₂, hrd₁], by rw [hwr₅, hwr₄, hwr₃, hwr₂, hwr₁]⟩
  · rw [initV_get P h N f k hk]
    by_cases e12 : k = 12
    · subst e12; simp only [↓reduceIte]
      rw [ho₅ _ (by decide) (by decide) (by decide), ho₄ _ (by decide)]; exact h12
    by_cases e13 : k = 13
    · subst e13; simp only [↓reduceIte]; exact h13
    by_cases e14 : k = 14
    · subst e14; simp only [↓reduceIte]; rw [← flagW_trunc]; exact h14
    simp only [e12, e13, e14, ite_false]
    rw [ho₅ _ (wreg_ne hk (by decide) e13) (wreg_ne hk (by decide) e14)
      (wreg_ne_T hk), ho₄ _ (wreg_ne_T hk), ho₃ _ (wreg_ne hk (by decide) e12) (wreg_ne_T hk)]
    exact hp₂ k hk (by omega)
  · rw [ho₅ _ (ne_wreg hq (by decide)) (ne_wreg hq (by decide)) hT, ho₄ _ hT,
      ho₃ _ (ne_wreg hq (by decide)) hT, o₂ q hq]

/-! ## Adding the work vector into the state -/

theorem word_sep (z : Size) (p : Addr) {j k : Nat} (hj : j < 8) (hk : k < 8) (h : j ≠ k) :
    Mem.Sep (p + BitVec.ofNat 64 (z.bytes * j)) (z.bits / 8) (p + BitVec.ofNat 64 (z.bytes * k))
      (z.bits / 8) := by
  rw [bits_div]
  have := Nat.mul_le_mul (bytes_le z) (show j ≤ 7 by omega)
  have := Nat.mul_le_mul (bytes_le z) (show k ≤ 7 by omega)
  have := bytes_le z
  refine Offset.sep p ?_ (by omega) (by omega)
  rcases Nat.lt_or_gt_of_ne h with h | h
  · exact .inl (by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ h)
  · exact .inr (by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ h)

theorem fin_step (n : Nat) (hn : n < 8) (s : State) (st : Addr) (hx0 : s.gpr .x0 = st)
    (hin : InRegions (s.rd ++ s.wr) (st + BitVec.ofNat 64 (z.bytes * n)) z.bytes)
    (hout : InRegions s.wr (st + BitVec.ofNat 64 (z.bytes * n)) z.bytes)
    (a b : BitVec z.bits) (ha : s.gpr (wreg n) = a.setWidth 64) (hb : s.gpr (wreg (n + 8)) = b.setWidth 64) :
    WP isa (.block [.ldr (sz z.bits) T .x0 (ws z.bits * n),
      .logic .eor (sz z.bits) T T (wreg n), .logic .eor (sz z.bits) T T (wreg (n + 8)),
      .str (sz z.bits) T .x0 (ws z.bits * n)]) s fun s' =>
      s'.mem = s.mem.writeW (st + BitVec.ofNat 64 (z.bytes * n))
        (s.mem.readW (st + BitVec.ofNat 64 (z.bytes * n)) z.bits ^^^ a ^^^ b) ∧
      (∀ q, q ≠ T → s'.gpr q = s.gpr q) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have o := off_ok z (j := n) (by omega)
  have n1 : wreg n ≠ T := wreg_ne_T (by omega)
  have n2 : wreg (n + 8) ≠ T := wreg_ne_T (by omega)
  simp only [T] at n1 n2
  apply WP.of_runBlock
  simp (config := {decide := true}) only [sz_bits, ws_bits, T, runBlock_cons, runStep_some,
    exec_ldr o, exec_logic, isa, State.read, RegUpd.gpr_write, ite_true, ite_false, hx0, hin, n1, n2,
    ha, hb, ext_trunc]
  rw [exec_str o (by simp only [RegUpd.wr_write, RegUpd.gpr_write, ite_false,
    show Reg.x0 ≠ Reg.x27 by decide, hx0]; exact hout)]
  simp only [runStep_some, runBlock_nil, Option.some.injEq, exists_eq_left', RegUpd.gpr_write,
    ite_true, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write, hx0, ext_trunc,
    show Reg.x0 ≠ Reg.x27 by decide, ite_false]
  refine ⟨trivial, fun q hq => ?_, trivial, trivial⟩
  simp only [hq, ite_false]

theorem word_contains (z : Size) (p : Addr) {k : Nat} (hk : k < 8) :
    (⟨p, 8 * z.bytes⟩ : Region).Contains (p + BitVec.ofNat 64 (z.bytes * k)) (z.bits / 8) := by
  rw [bits_div]
  have := Nat.mul_le_mul (bytes_le z) (show k ≤ 7 by omega)
  have := bytes_le z
  refine Offset.contains_base p ?_ (by omega)
  rw [← Nat.mul_succ, Nat.mul_comm 8]; exact Nat.mul_le_mul_left _ hk

theorem fin_ok (s : State) (st : Addr) (hx0 : s.gpr .x0 = st)
    (hin : ∀ k < 8, InRegions (s.rd ++ s.wr) (st + BitVec.ofNat 64 (z.bytes * k)) z.bytes)
    (hout : ∀ k < 8, InRegions s.wr (st + BitVec.ofNat 64 (z.bytes * k)) z.bytes)
    (v : Work z.bits) (hv : Vars s v) (h : HashValue z.bits)
    (hh : ∀ k (hk : k < 8), s.mem.readW (st + BitVec.ofNat 64 (z.bytes * k)) z.bits = h[k]) :
    ∀ n ≤ 8, WP isa (Impl.Blake2.AArch64.fin (w := z.bits) n) s fun s' =>
      (∀ k (hk : k < 8), s'.mem.readW (st + BitVec.ofNat 64 (z.bytes * k)) z.bits =
        if k < n then h[k] ^^^ v[k] ^^^ v[k + 8] else h[k]) ∧
      Frame [⟨st, 8 * z.bytes⟩] s.mem s'.mem ∧ (∀ q, q ≠ T → s'.gpr q = s.gpr q) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  intro n hn
  induction n with
  | zero =>
    exact WP.block_nil (M := isa) ⟨fun k hk => by simpa using hh k hk, Frame.refl _ _,
      fun _ _ => rfl, rfl, rfl⟩
  | succ n ih =>
    refine WP.seq (WP.mono (ih (by omega)) fun s₁ ⟨hm₁, hf₁, ho₁, hrd₁, hwr₁⟩ => ?_)
    refine WP.mono (fin_step n (by omega) s₁ st (by rw [ho₁ _ (by decide), hx0])
      (by rw [hrd₁, hwr₁]; exact hin n (by omega)) (by rw [hwr₁]; exact hout n (by omega)) v[n] v[n + 8]
      (by rw [ho₁ _ (wreg_ne_T (by omega))]; exact hv n (by omega))
      (by rw [ho₁ _ (wreg_ne_T (by omega))]; exact hv (n + 8) (by omega)))
      fun s₂ ⟨hm₂, ho₂, hrd₂, hwr₂⟩ => ?_
    have e : s₁.mem.readW (st + BitVec.ofNat 64 (z.bytes * n)) z.bits = h[n] := by
      rw [hm₁ n (by omega)]; simp
    refine ⟨fun k hk => ?_, ?_, fun q hq => (ho₂ q hq).trans (ho₁ q hq), hrd₂.trans hrd₁,
      hwr₂.trans hwr₁⟩
    · rw [hm₂, e]
      by_cases hkn : k = n
      · subst hkn; rw [readW_writeW_self]; simp
      · rw [Mem.readW_writeW_sep (word_sep z st hk (by omega) hkn) (by rw [bits_div]; have := bytes_le z; omega),
          hm₁ k hk]
        by_cases hlt : k < n
        · simp [hlt, show k < n + 1 by omega]
        · simp [hlt, show ¬k < n + 1 by omega]
    · rw [hm₂]; exact hf₁.writeW (List.mem_singleton_self _) _ (word_contains z st (by omega))

end Init2

/-! ## Advancing to the next block -/

/-- The carry out of the low word when the counter `N` advances by `2 ^ k`: the new low
word is below `2 ^ k` exactly when the addition wrapped. -/
theorem carry (N k : Nat) (hk : k = 6 ∨ k = 7) :
    BitVec.ofNat 64 (N / 2 ^ 64) + (((BitVec.ofNat 64 N + BitVec.ofNat 64 (2 ^ k)) >>> k - BitVec.ofNat 64 1) >>> 63) =
      BitVec.ofNat 64 ((N + 2 ^ k) / 2 ^ 64) := by
  have hN := Nat.div_add_mod N (2 ^ 64)
  have hL := Nat.mod_lt N (show 2 ^ 64 > 0 by decide)
  have hb : 2 ≤ 2 ^ k ∧ 2 ^ k ≤ 128 := by rcases hk with rfl | rfl <;> decide
  rw [BitVec.ofNat_add_ofNat]
  generalize N / 2 ^ 64 = A at hN ⊢
  generalize N % 2 ^ 64 = L at hN hL ⊢
  subst hN
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow, show (BitVec.ofNat 64 1).toNat = 1 from rfl]
  have e1 : (2 ^ 64 * A + L + 2 ^ k) % 2 ^ 64 = (L + 2 ^ k) % 2 ^ 64 := by
    rw [Nat.add_assoc, Nat.mul_add_mod]
  have e2 : (2 ^ 64 * A + L + 2 ^ k) / 2 ^ 64 = A + (L + 2 ^ k) / 2 ^ 64 := by
    rw [Nat.add_assoc, Nat.mul_add_div (by decide)]
  rw [e1, e2]
  generalize 2 ^ k = B at *
  by_cases hc : L + B < 2 ^ 64
  · rw [Nat.mod_eq_of_lt hc, Nat.div_eq_of_lt hc]
    have h1 : 1 ≤ (L + B) / B := by
      rw [Nat.le_div_iff_mul_le (by omega)]; omega
    have h2 : (L + B) / B ≤ (L + B) / 2 := Nat.div_le_div_left hb.1 (by decide)
    have : (2 ^ 64 - 1 + (L + B) / B) % 2 ^ 64 / 2 ^ 63 = 0 := by omega
    rw [this]; omega
  · have q1 : (L + B) / 2 ^ 64 = 1 := by omega
    have q2 : (L + B) % 2 ^ 64 = L + B - 2 ^ 64 := by omega
    rw [q2, q1, Nat.div_eq_of_lt (show L + B - 2 ^ 64 < B by omega)]
    omega

theorem bb_eq (z : Size) : 16 * ws z.bits = 2 ^ lbb z.bits := by cases z <;> rfl

theorem lbb_cases (z : Size) : lbb z.bits = 6 ∨ lbb z.bits = 7 := by cases z <;> decide

theorem lo_hi_sep (scr : Addr) :
    Mem.Sep (scr + BitVec.ofNat 64 hiOff) (64 / 8) (scr + BitVec.ofNat 64 loOff) (64 / 8) :=
  Offset.sep scr (by decide) (by decide) (by decide)

theorem advance_ok {z : Size} {scr : Addr} {N : Nat} {fl : BitVec 64} (s : State)
    (hs : Scr scr N fl s) (hoLo : InRegions s.wr (scr + BitVec.ofNat 64 loOff) 8)
    (hoHi : InRegions s.wr (scr + BitVec.ofNat 64 hiOff) 8) :
    WP isa (.block (Impl.Blake2.AArch64.advance (w := z.bits))) s fun s' =>
      s'.gpr .x1 = s.gpr .x1 + BitVec.ofNat 64 (2 ^ lbb z.bits) ∧ s'.gpr .x2 = s.gpr .x2 - 1 ∧
      s'.mem = (s.mem.writeW (scr + BitVec.ofNat 64 loOff) (BitVec.ofNat 64 (N + 2 ^ lbb z.bits))).writeW
        (scr + BitVec.ofNat 64 hiOff) (BitVec.ofNat 64 ((N + 2 ^ lbb z.bits) / 2 ^ 64)) ∧
      (∀ q, q ≠ .x1 → q ≠ .x2 → q ≠ .x3 → q ≠ .x4 → q ≠ .x6 → s'.gpr q = s.gpr q) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hk := lbb_cases z
  have hb : 2 ^ lbb z.bits < 4096 := by rcases hk with h | h <;> rw [h] <;> decide
  have hk' : lbb z.bits < 64 := by omega
  have hsep : ∀ X : BitVec 64, (s.mem.writeW (scr + BitVec.ofNat 64 loOff) X).readW
      (scr + BitVec.ofNat 64 hiOff) 64 = BitVec.ofNat 64 (N / 2 ^ 64) := fun X => by
    rw [Mem.readW_writeW_sep (lo_hi_sep scr) (by decide)]; exact hs.hi
  have ol : loOff % 8 = 0 ∧ loOff < 32768 := by decide
  have oh : hiOff % 8 = 0 ∧ hiOff < 32768 := by decide
  apply WP.of_runBlock
  simp (config := {decide := true}) only [Impl.Blake2.AArch64.advance, bb_eq, runBlock_cons,
    runStep_some, exec_addImm_x hb, exec_ldr_x ol, isa, State.read, RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    ite_true, ite_false, ext64, hs.x5, hs.inLo, hs.lo]
  rw [exec_str_x ol]
  · simp (config := {decide := true}) only [runStep_some, runBlock_cons, exec_lsr_x hk',
      exec_lsr_x (show 63 < 64 by decide), exec_subImm_x (show 1 < 4096 by decide), exec_add,
      exec_ldr_x oh, isa, State.read, RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write,
      RegUpd.wr_write, ite_true, ite_false, ext64, hs.x5, hs.inHi, hsep]
    rw [exec_str_x oh]
    · simp (config := {decide := true}) only [runStep_some, runBlock_cons, runBlock_nil,
        exec_subImm_x (show 1 < 4096 by decide), isa, State.read, RegUpd.gpr_write, RegUpd.mem_write,
        RegUpd.rd_write, RegUpd.wr_write, ite_true, ite_false, ext64, hs.x5,
        Option.some.injEq, exists_eq_left']
      refine ⟨trivial, rfl, ?_, fun q h1 h2 h3 h4 h6 => ?_, trivial⟩
      · rw [← carry N _ hk, ← BitVec.ofNat_add_ofNat]
      · simp only [h1, h2, h3, h4, h6, ite_false]
    · simp (config := {decide := true}) only [RegUpd.wr_write, RegUpd.gpr_write, ite_false, hs.x5]
      exact hoHi
  · simp (config := {decide := true}) only [RegUpd.wr_write, RegUpd.gpr_write, ite_false, hs.x5]
    exact hoLo

/-! ## Saving registers, the counter and the flag word -/

/-- The flag word, computed without a branch from `last`. -/
theorem flag_eq (l : BitVec 32) :
    (0 : BitVec 64) - (((l ||| l).setWidth 64 ||| ((0 : BitVec 64) - (l ||| l).setWidth 64)) >>> 63) =
      flagW 64 (l != 0) := by
  rw [BitVec.or_self, BitVec.ushiftRight_or_distrib]
  have hl := l.isLt
  by_cases h : l = 0
  · subst h; decide
  · have h0 : l.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq (by simpa using e))
    have e1 : l.setWidth 64 >>> 63 = 0 := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ushiftRight, BitVec.toNat_setWidth, Nat.shiftRight_eq_div_pow,
        show (0 : BitVec 64).toNat = 0 from rfl]
      omega
    have e2 : ((0 : BitVec 64) - l.setWidth 64) >>> 63 = 1 := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_setWidth,
        Nat.shiftRight_eq_div_pow, show (0 : BitVec 64).toNat = 0 from rfl,
        show (1 : BitVec 64).toNat = 1 from rfl]
      omega
    rw [e1, e2, show ((0 : BitVec 64) ||| 1) = 1 from rfl]
    have ht : (l != 0) = true := by simpa using h
    simp only [flagW, ht, ite_true]
    decide

theorem movz0 : ((0 : BitVec 16).setWidth Size.x.bits <<< (16 * 0) : BitVec 64) = 0 := by decide

/-- The scratch after `save ++ setup`. -/
def setupMem (m : Mem) (scr : Addr) (r25 r26 r27 t : BitVec 64) (f : Bool) : Mem :=
  (((((m.writeW (scr + BitVec.ofNat 64 0) r25).writeW (scr + BitVec.ofNat 64 8) r26).writeW
    (scr + BitVec.ofNat 64 16) r27).writeW (scr + BitVec.ofNat 64 loOff) t).writeW
    (scr + BitVec.ofNat 64 hiOff) (0 : BitVec 64)).writeW (scr + BitVec.ofNat 64 fOff) (flagW 64 f)

theorem exec_movz_x0 {s : State} {d : Reg} : exec (.movz .x d 0 0) s = some (s.write .x d 0) := by
  simp only [exec, show 16 * 0 < Size.x.bits from by decide, ite_true]
  rw [movz0]

theorem exec_sub {sz : Size} {s : State} {d n m : Reg} :
    exec (.sub sz d n m) s = some (s.write sz d (s.read sz n - s.read sz m)) := rfl

theorem setup_ok (s : State) (scr : Addr) (hx5 : s.gpr .x5 = scr)
    (ho : ∀ d, d + 8 ≤ 512 → InRegions s.wr (scr + BitVec.ofNat 64 d) 8) :
    WP isa (.block (Impl.Blake2.AArch64.save ++ Impl.Blake2.AArch64.setup)) s fun s' =>
      s'.mem = setupMem s.mem scr (s.gpr .x25) (s.gpr .x26) (s.gpr .x27) (s.gpr .x3)
        ((s.gpr .x4).setWidth 32 != 0) ∧
      (∀ q, q ≠ .x3 → q ≠ .x4 → q ≠ T → s'.gpr q = s.gpr q) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have o0 := ho 0 (by decide); have o8 := ho 8 (by decide); have o16 := ho 16 (by decide)
  have o32 := ho loOff (by decide); have o40 := ho hiOff (by decide); have o48 := ho fOff (by decide)
  apply WP.of_runBlock
  simp (config := {decide := true}) only [Impl.Blake2.AArch64.save, Impl.Blake2.AArch64.setup,
    saved, List.map_cons, List.map_nil, List.cons_append, List.nil_append, T, runBlock_cons,
    runStep_some, runBlock_nil, exec_str_x, exec_movz_x0, exec_logic, exec_sub,
    exec_lsr_x (show 63 < 64 by decide), isa, State.read,
    RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write, ite_true, ite_false,
    hx5, eq_self, o0, o8, o16, o32, o40, o48, ext64, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun q h3 h4 h27 => ?_, trivial⟩
  · rw [show Size.w.bits = 32 from rfl, flag_eq]; rfl
  · simp only [h3, h4, h27, ite_false]

theorem restore_ok (s : State) (scr : Addr) (hx5 : s.gpr .x5 = scr)
    (hi : ∀ d, d + 8 ≤ 512 → InRegions (s.rd ++ s.wr) (scr + BitVec.ofNat 64 d) 8) :
    WP isa (.block Impl.Blake2.AArch64.restore) s fun s' =>
      s'.gpr .x25 = s.mem.readW (scr + BitVec.ofNat 64 0) 64 ∧
      s'.gpr .x26 = s.mem.readW (scr + BitVec.ofNat 64 8) 64 ∧
      s'.gpr .x27 = s.mem.readW (scr + BitVec.ofNat 64 16) 64 ∧
      (∀ q, q ≠ .x25 → q ≠ .x26 → q ≠ .x27 → s'.gpr q = s.gpr q) ∧ s'.mem = s.mem := by
  have o0 := hi 0 (by decide); have o8 := hi 8 (by decide); have o16 := hi 16 (by decide)
  apply WP.of_runBlock
  simp (config := {decide := true}) only [Impl.Blake2.AArch64.restore, saved, List.map_cons,
    List.map_nil, runBlock_cons, runStep_some, runBlock_nil, exec_ldr_x, isa, RegUpd.gpr_write,
    RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write, ite_true, ite_false, hx5, eq_self, o0, o8,
    o16, ext64, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, trivial, fun q h1 h2 h3 => ?_, trivial⟩
  simp only [h1, h2, h3, ite_false]

/-! ## The whole function -/

section Regions
variable (z : Size) (s₀ : State)

abbrev st : Addr := s₀.gpr .x0
abbrev bp : Addr := s₀.gpr .x1
abbrev nb : Nat := (s₀.gpr .x2).toNat
abbrev scr : Addr := s₀.gpr .x5
abbrev t₀ : Nat := (s₀.gpr .x3).toNat
abbrev fl : Bool := (s₀.gpr .x4).setWidth 32 != 0
abbrev stR : Region := ⟨st s₀, 8 * z.bytes⟩
abbrev blR : Region := ⟨bp s₀, Spec.Blake2.blockBytes z.bits * nb s₀⟩
abbrev scrR : Region := ⟨scr s₀, 512⟩
abbrev H₀ : HashValue z.bits := Spec.Blake2.stateAt z.bits s₀.mem (st s₀)
/-- Where block `i` starts. -/
abbrev blkAddr (i : Nat) : Addr := bp s₀ + BitVec.ofNat 64 (Spec.Blake2.blockBytes z.bits * i)

end Regions

theorem bbz (z : Size) : Spec.Blake2.blockBytes z.bits = 16 * z.bytes := by cases z <;> rfl

theorem bb_pow (z : Size) : Spec.Blake2.blockBytes z.bits = 2 ^ lbb z.bits := by cases z <;> rfl

theorem stateAt_get' (z : Size) (m : Mem) (p : Addr) {k : Nat} (hk : k < 8) :
    (Spec.Blake2.stateAt z.bits m p)[k] = m.readW (p + BitVec.ofNat 64 (z.bytes * k)) z.bits := by
  simp only [Spec.Blake2.stateAt, Vector.getElem_ofFn, bits_div]

theorem stateAt_eq' {z : Size} {m : Mem} {p : Addr} {v : HashValue z.bits}
    (h : ∀ k (hk : k < 8), m.readW (p + BitVec.ofNat 64 (z.bytes * k)) z.bits = v[k]) :
    Spec.Blake2.stateAt z.bits m p = v := by
  apply Vector.ext
  intro k hk
  rw [stateAt_get' z m p hk]
  exact h k hk

theorem bytes_pos (z : Size) : 0 < z.bytes := by cases z <;> decide

theorem word_contains' (z : Size) (p : Addr) {k : Nat} (hk : k < 8) :
    (⟨p, 8 * z.bytes⟩ : Region).Contains (p + BitVec.ofNat 64 (z.bytes * k)) z.bytes := by
  have := word_contains z p hk
  rwa [bits_div] at this

theorem blk_bound (z : Size) {i j n : Nat} (hi : i < n) (hj : j < 16)
    (hn : Spec.Blake2.blockBytes z.bits * n < 2 ^ 64) :
    Spec.Blake2.blockBytes z.bits * i + z.bytes * j + z.bytes ≤ Spec.Blake2.blockBytes z.bits * n ∧
      Spec.Blake2.blockBytes z.bits * i + z.bytes * j < 2 ^ 64 := by
  rw [bbz] at *
  cases z <;> simp only [Size.bytes] at * <;> omega

structure Pre (z : Size) (s₀ : State) : Prop where
  rd : s₀.rd = [blR z s₀]
  wr : s₀.wr = [stR z s₀, scrR s₀]
  st_scr : (stR z s₀).Disjoint (scrR s₀)
  blk_st : (blR z s₀).Disjoint (stR z s₀)
  blk_scr : (blR z s₀).Disjoint (scrR s₀)

theorem pre_of {z : Size} (P : Params z.bits) (s₀ : State) (h : (compressAArch64 P).pre s₀) :
    Pre z s₀ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  simp only [bits_div] at h1 h2 h3 h4 h5
  exact ⟨h1, h2, h3, h4, h5⟩

namespace Pre
variable {z : Size} {s₀ : State} (h : Pre z s₀)
include h

theorem nb_lt : Spec.Blake2.blockBytes z.bits * nb s₀ < 2 ^ 64 := by
  by_contra hn
  have hb := bytes_pos z
  refine h.blk_st (st s₀) ?_ (Offset.contains_base (st s₀) (d := 0) (n := 1) (k := 8 * z.bytes) (by omega) (by decide) |>
    fun c => by simpa using c)
  simp only [Region.Contains]
  have := (st s₀ - bp s₀).isLt
  omega

theorem in_state {k : Nat} (hk : k < 8) :
    InRegions (s₀.rd ++ s₀.wr) (st s₀ + BitVec.ofNat 64 (z.bytes * k)) z.bytes :=
  ⟨stR z s₀, by simp [h.wr], word_contains' z _ hk⟩

theorem out_state {k : Nat} (hk : k < 8) :
    InRegions s₀.wr (st s₀ + BitVec.ofNat 64 (z.bytes * k)) z.bytes :=
  ⟨stR z s₀, by simp [h.wr], word_contains' z _ hk⟩

theorem in_scr (d : Nat) (hd : d + 8 ≤ 512) :
    InRegions (s₀.rd ++ s₀.wr) (scr s₀ + BitVec.ofNat 64 d) 8 :=
  ⟨scrR s₀, by simp [h.wr], Offset.contains_base _ hd (by omega)⟩

theorem out_scr (d : Nat) (hd : d + 8 ≤ 512) : InRegions s₀.wr (scr s₀ + BitVec.ofNat 64 d) 8 :=
  ⟨scrR s₀, by simp [h.wr], Offset.contains_base _ hd (by omega)⟩

theorem blk_contains' {i j : Nat} (hi : i < nb s₀) (hj : j < 16) :
    (blR z s₀).Contains (blkAddr z s₀ i + BitVec.ofNat 64 (z.bytes * j)) z.bytes := by
  have hb := blk_bound z hi hj h.nb_lt
  rw [Offset.add_ofNat_add_ofNat]
  exact Offset.contains_base _ hb.1 hb.2

theorem blk_contains {i j : Nat} (hi : i < nb s₀) (hj : j < 16) :
    (blR z s₀).Contains (blkAddr z s₀ i + BitVec.ofNat 64 (z.bytes * j)) (z.bits / 8) := by
  rw [bits_div]; exact h.blk_contains' hi hj

theorem in_blk {i j : Nat} (hi : i < nb s₀) (hj : j < 16) :
    InRegions (s₀.rd ++ s₀.wr) (blkAddr z s₀ i + BitVec.ofNat 64 (z.bytes * j)) z.bytes :=
  ⟨blR z s₀, by simp [h.rd], h.blk_contains' hi hj⟩

/-- A scratch word is unchanged by writes to the state. -/
theorem cell_frame {m m' : Mem} (hf : Frame [stR z s₀] m m') {d : Nat} (hd : d + 8 ≤ 512) :
    m'.readW (scr s₀ + BitVec.ofNat 64 d) 64 = m.readW (scr s₀ + BitVec.ofNat 64 d) 64 :=
  hf.readW (r := scrR s₀) (Offset.contains_base _ hd (by omega)) (by simpa using h.st_scr.symm)
    (by decide)

/-- A word of the state is unchanged by writes to the scratch. -/
theorem state_frame {m m' : Mem} (hf : Frame [scrR s₀] m m') {k : Nat} (hk : k < 8) :
    m'.readW (st s₀ + BitVec.ofNat 64 (z.bytes * k)) z.bits =
      m.readW (st s₀ + BitVec.ofNat 64 (z.bytes * k)) z.bits :=
  hf.readW (r := stR z s₀) (word_contains z _ hk) (by simpa using h.st_scr)
    (by have := bits_le z; omega)

/-- A word of the state is unchanged by a write to a scratch word. -/
theorem state_sep (m : Mem) (v : BitVec 64) {k e : Nat} (hk : k < 8) (he : e + 8 ≤ 512) :
    (m.writeW (scr s₀ + BitVec.ofNat 64 e) v).readW (st s₀ + BitVec.ofNat 64 (z.bytes * k)) z.bits =
      m.readW (st s₀ + BitVec.ofNat 64 (z.bytes * k)) z.bits :=
  Mem.readW_writeW_sep (h.st_scr.sep (word_contains z _ hk)
    (Offset.contains_base _ (show e + 64 / 8 ≤ 512 from he) (by omega)))
    (by have := bits_le z; omega)

/-- A block word is where it was at the start, when only the state and the scratch changed. -/
theorem blk_frame {m : Mem} (hf : Frame [stR z s₀, scrR s₀] s₀.mem m) {i j : Nat} (hi : i < nb s₀)
    (hj : j < 16) :
    m.readW (blkAddr z s₀ i + BitVec.ofNat 64 (z.bytes * j)) z.bits =
      Spec.Blake2.blockAt z.bits s₀.mem (blkAddr z s₀ i) ⟨j, hj⟩ := by
  rw [hf.readW (h.blk_contains hi hj) (by simpa using ⟨h.blk_st, h.blk_scr⟩)
    (by have := bits_le z; omega), blockAt_word, bits_div]

end Pre

/-- A scratch word is unchanged by a write to another. -/
theorem cell_sep (p : Addr) (m : Mem) (v : BitVec 64) {d e : Nat}
    (h : (d + 8 ≤ e ∨ e + 8 ≤ d) ∧ d + 8 ≤ 512 ∧ e + 8 ≤ 512) :
    (m.writeW (p + BitVec.ofNat 64 e) v).readW (p + BitVec.ofNat 64 d) 64 =
      m.readW (p + BitVec.ofNat 64 d) 64 :=
  Mem.readW_writeW_sep (Offset.sep p (n := 64 / 8) (k := 64 / 8) h.1 (by omega) (by omega))
    (by decide)

/-- The registers the code never writes (and `x0`, `x5`). -/
def keptRegs : List Reg := [.x0, .x5, .x19, .x20, .x21, .x22, .x23, .x24, .x28, .x30]

theorem kept_ok : ∀ r ∈ keptRegs, r ∉ wregs ∧ r ≠ T ∧ r ≠ .x1 ∧ r ≠ .x2 ∧ r ≠ .x3 ∧ r ≠ .x4 ∧
    r ≠ .x6 ∧ r ≠ .x25 ∧ r ≠ .x26 ∧ r ≠ .x27 := by decide

section Loop
variable {z : Size} (P : Params z.bits)

/-- What holds between blocks, after `i` of them. -/
structure Common (s₀ : State) (i : Nat) (s : State) : Prop where
  kept : ∀ r ∈ keptRegs, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [stR z s₀, scrR s₀] s₀.mem s.mem
  state : Spec.Blake2.stateAt z.bits s.mem (st s₀) =
    Spec.Blake2.compressBlocks P (H₀ z s₀) s₀.mem (bp s₀) i (t₀ s₀) (fl s₀)
  sv0 : s.mem.readW (scr s₀ + BitVec.ofNat 64 0) 64 = s₀.gpr .x25
  sv8 : s.mem.readW (scr s₀ + BitVec.ofNat 64 8) 64 = s₀.gpr .x26
  sv16 : s.mem.readW (scr s₀ + BitVec.ofNat 64 16) 64 = s₀.gpr .x27
  lo : s.mem.readW (scr s₀ + BitVec.ofNat 64 loOff) 64 =
    BitVec.ofNat 64 (t₀ s₀ + i * Spec.Blake2.blockBytes z.bits)
  hi : s.mem.readW (scr s₀ + BitVec.ofNat 64 hiOff) 64 =
    BitVec.ofNat 64 ((t₀ s₀ + i * Spec.Blake2.blockBytes z.bits) / 2 ^ 64)
  f : s.mem.readW (scr s₀ + BitVec.ofNat 64 fOff) 64 = flagW 64 (fl s₀)

/-- The loop invariant, at the start of block `i`. -/
structure LInv (s₀ : State) (i : Nat) (s : State) : Prop extends Common P s₀ i s where
  x1 : s.gpr .x1 = blkAddr z s₀ i
  x2 : s.gpr .x2 = BitVec.ofNat 64 (nb s₀ - i)

theorem Common.x0 {s₀ : State} {i : Nat} {s : State} (h : Common P s₀ i s) : s.gpr .x0 = st s₀ :=
  h.kept _ (by decide)

theorem Common.x5 {s₀ : State} {i : Nat} {s : State} (h : Common P s₀ i s) : s.gpr .x5 = scr s₀ :=
  h.kept _ (by decide)

theorem Common.scr {s₀ : State} (hp : Pre z s₀) {i : Nat} {s : State} (h : Common P s₀ i s) :
    Scr (scr s₀) (t₀ s₀ + i * Spec.Blake2.blockBytes z.bits) (flagW 64 (fl s₀)) s :=
  ⟨h.x5 P, by rw [h.rd, h.wr]; exact hp.in_scr _ (by decide),
    by rw [h.rd, h.wr]; exact hp.in_scr _ (by decide), by rw [h.rd, h.wr]; exact hp.in_scr _ (by decide),
    h.lo, h.hi, h.f⟩

/-! ## One block -/

theorem body_ok (hR : ROk P) {s₀ : State} (hp : Pre z s₀) {i : Nat} (hi : i < nb s₀) {s : State}
    (hL : LInv P s₀ i s) :
    WP isa (Impl.Blake2.AArch64.body P) s fun s' =>
      (eval (.nonzero .x .x2) s' = some false ∧ Common P s₀ (nb s₀) s') ∨
      (eval (.nonzero .x .x2) s' = some true ∧ i + 1 < nb s₀ ∧ LInv P s₀ (i + 1) s') := by
  have hC := hL.toCommon
  have hin : ∀ k < 8, InRegions (s.rd ++ s.wr) (st s₀ + BitVec.ofNat 64 (z.bytes * k)) z.bytes := by
    rw [hC.rd, hC.wr]; exact fun k hk => hp.in_state hk
  have hout : ∀ k < 8, InRegions s.wr (st s₀ + BitVec.ofNat 64 (z.bytes * k)) z.bytes := by
    rw [hC.wr]; exact fun k hk => hp.out_state hk
  have hh : ∀ k (hk : k < 8), s.mem.readW (st s₀ + BitVec.ofNat 64 (z.bytes * k)) z.bits =
      (Spec.Blake2.compressBlocks P (H₀ z s₀) s₀.mem (bp s₀) i (t₀ s₀) (fl s₀))[k] := fun k hk => by
    rw [← stateAt_get' z _ _ hk, hC.state]
  refine WP.seq (WP.mono (init_ok P s (hC.scr P hp) (hC.x0 P) hin _ hh)
    fun s₁ ⟨hv₁, ho₁, hm₁, hrd₁, hwr₁⟩ => ?_)
  have hM : Msg (Spec.Blake2.blockAt z.bits s₀.mem (blkAddr z s₀ i)) (blkAddr z s₀ i) s₁ :=
    ⟨(ho₁ _ (by decide) (by decide)).trans hL.x1,
      by rw [hrd₁, hwr₁, hC.rd, hC.wr]; exact fun j hj => hp.in_blk hi hj,
      fun j hj => by rw [hm₁]; exact hp.blk_frame hC.frame hi hj⟩
  refine WP.seq (WP.mono (rounds_ok P hR hM ⟨hv₁, fun _ _ _ => rfl, rfl, rfl, rfl⟩ P.r)
    fun s₂ hR₂ => ?_)
  have o₂ : ∀ q, q ∉ wregs → q ≠ T → s₂.gpr q = s.gpr q := fun q h1 h2 =>
    (hR₂.other q h1 h2).trans (ho₁ q h1 h2)
  have hm₂ : s₂.mem = s.mem := hR₂.mem.trans hm₁
  refine WP.seq (WP.mono (fin_ok s₂ (st s₀) ((o₂ _ (by decide) (by decide)).trans (hC.x0 P))
    (by rw [hR₂.rd, hR₂.wr, hrd₁, hwr₁]; exact hin) (by rw [hR₂.wr, hwr₁]; exact hout) _ hR₂.vars
    (Spec.Blake2.compressBlocks P (H₀ z s₀) s₀.mem (bp s₀) i (t₀ s₀) (fl s₀))
    (by rw [hm₂]; exact hh) 8 (Nat.le_refl _)) fun s₃ ⟨hf₃, hF₃, ho₃, hrd₃, hwr₃⟩ => ?_)
  have hF₃' : Frame [stR z s₀] s.mem s₃.mem := hm₂ ▸ hF₃
  have hrw₃ : s₃.rd = s₀.rd ∧ s₃.wr = s₀.wr :=
    ⟨by rw [hrd₃, hR₂.rd, hrd₁, hC.rd], by rw [hwr₃, hR₂.wr, hwr₁, hC.wr]⟩
  have o₃ : ∀ q, q ∉ wregs → q ≠ T → s₃.gpr q = s.gpr q := fun q h1 h2 =>
    (ho₃ q h2).trans (o₂ q h1 h2)
  have hS₃ : Scr (scr s₀) (t₀ s₀ + i * Spec.Blake2.blockBytes z.bits) (flagW 64 (fl s₀)) s₃ :=
    ⟨(o₃ _ (by decide) (by decide)).trans (hC.x5 P),
      by rw [hrw₃.1, hrw₃.2]; exact hp.in_scr _ (by decide),
      by rw [hrw₃.1, hrw₃.2]; exact hp.in_scr _ (by decide),
      by rw [hrw₃.1, hrw₃.2]; exact hp.in_scr _ (by decide),
      by rw [hp.cell_frame hF₃' (by decide)]; exact hC.lo,
      by rw [hp.cell_frame hF₃' (by decide)]; exact hC.hi,
      by rw [hp.cell_frame hF₃' (by decide)]; exact hC.f⟩
  refine WP.mono (advance_ok s₃ hS₃ (by rw [hrw₃.2]; exact hp.out_scr _ (by decide))
    (by rw [hrw₃.2]; exact hp.out_scr _ (by decide)))
    fun s₄ ⟨hx1₄, hx2₄, hm₄, ho₄, hrd₄, hwr₄⟩ => ?_
  have o₄ : ∀ q, q ∉ wregs → q ≠ T → q ≠ .x1 → q ≠ .x2 → s₄.gpr q = s.gpr q := fun q h1 h2 h3 h4 =>
    (ho₄ q h3 h4 (ne_wreg h1 (k := 0) (by decide)) (ne_wreg h1 (k := 1) (by decide))
      (ne_wreg h1 (k := 2) (by decide))).trans (o₃ q h1 h2)
  have hx1₃ : s₃.gpr .x1 = blkAddr z s₀ i := (o₃ _ (by decide) (by decide)).trans hL.x1
  have hx2₃ : s₃.gpr .x2 = BitVec.ofNat 64 (nb s₀ - i) := (o₃ _ (by decide) (by decide)).trans hL.x2
  have hx2 : s₄.gpr .x2 = BitVec.ofNat 64 (nb s₀ - (i + 1)) := by
    rw [hx2₄, hx2₃, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl,
      Offset.ofNat_sub_ofNat (by omega), Nat.sub_sub]
  have hbb : t₀ s₀ + i * Spec.Blake2.blockBytes z.bits + 2 ^ lbb z.bits =
      t₀ s₀ + (i + 1) * Spec.Blake2.blockBytes z.bits := by
    rw [← bb_pow, Nat.succ_mul, Nat.add_assoc]
  have hframe : Frame [stR z s₀, scrR s₀] s₀.mem s₄.mem := by
    refine hC.frame.trans ?_
    rw [hm₄]
    exact ((hF₃'.mono fun r hr => by simp only [List.mem_singleton] at hr; simp [hr]).writeW
      (r := scrR s₀) (by simp) _ (Offset.contains_base _ (by decide) (by decide))).writeW
      (r := scrR s₀) (by simp) _ (Offset.contains_base _ (by decide) (by decide))
  have hcell : ∀ d, (d = 0 ∨ d = 8 ∨ d = 16 ∨ d = fOff) →
      s₄.mem.readW (scr s₀ + BitVec.ofNat 64 d) 64 = s.mem.readW (scr s₀ + BitVec.ofNat 64 d) 64 := by
    intro d hd
    have h1 : (d + 8 ≤ hiOff ∨ hiOff + 8 ≤ d) ∧ d + 8 ≤ 512 ∧ hiOff + 8 ≤ 512 := by
      simp only [hiOff, fOff] at hd ⊢; omega
    have h2 : (d + 8 ≤ loOff ∨ loOff + 8 ≤ d) ∧ d + 8 ≤ 512 ∧ loOff + 8 ≤ 512 := by
      simp only [loOff, fOff] at hd ⊢; omega
    rw [hm₄, cell_sep _ _ _ h1, cell_sep _ _ _ h2, hp.cell_frame hF₃' h1.2.1]
  have hcommon : Common P s₀ (i + 1) s₄ := by
    refine ⟨fun r hr => ?_, by rw [hrd₄, hrw₃.1], by rw [hwr₄, hrw₃.2], hframe, ?_,
      by rw [hcell 0 (by decide)]; exact hC.sv0, by rw [hcell 8 (by decide)]; exact hC.sv8,
      by rw [hcell 16 (by decide)]; exact hC.sv16, ?_, ?_,
      by rw [hcell fOff (by decide)]; exact hC.f⟩
    · obtain ⟨a, b, c, d, -⟩ := kept_ok r hr
      rw [o₄ r a b c d]; exact hC.kept r hr
    · refine stateAt_eq' fun k hk => ?_
      rw [hm₄, hp.state_sep _ _ hk (by decide), hp.state_sep _ _ hk (by decide), hf₃ k hk,
        compressBlocks_succ, F_eq, Vector.getElem_ofFn]
      simp only [hk, ite_true, Fin.getElem_fin]
    · rw [hm₄, cell_sep _ _ _ (d := loOff) (e := hiOff) (by decide), Mem.readW_writeW_self64, hbb]
    · rw [hm₄, Mem.readW_writeW_self64, hbb]
  have hev : eval (.nonzero .x .x2) s₄ = some (BitVec.ofNat 64 (nb s₀ - (i + 1)) != 0) := by
    simp only [eval, State.read, ext64, hx2]
  have := hp.nb_lt
  have hbpos : 0 < Spec.Blake2.blockBytes z.bits := by rw [bbz]; have := bytes_pos z; omega
  have hnb : nb s₀ < 2 ^ 64 := (s₀.gpr .x2).isLt
  by_cases hlast : i + 1 = nb s₀
  · left
    refine ⟨by rw [hev, hlast]; simp, hlast ▸ hcommon⟩
  · right
    have hne : nb s₀ - (i + 1) ≠ 0 := by omega
    have h0 : BitVec.ofNat 64 (nb s₀ - (i + 1)) ≠ 0 := by
      intro h
      have h' := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h'
      exact hne h'
    refine ⟨by rw [hev]; simpa using h0, by omega, { hcommon with x1 := ?_, x2 := hx2 }⟩
    rw [hx1₄, hx1₃, Offset.add_ofNat_add_ofNat, ← bb_pow, ← Nat.mul_succ]

/-! ## The whole function -/

theorem setup_frame (s₀ : State) (r25 r26 r27 t : BitVec 64) (f : Bool) :
    Frame [scrR s₀] s₀.mem (setupMem s₀.mem (scr s₀) r25 r26 r27 t f) := by
  have c : ∀ d, d + 8 ≤ 512 → (scrR s₀).Contains (scr s₀ + BitVec.ofNat 64 d) (64 / 8) :=
    fun d hd => Offset.contains_base _ hd (by omega)
  have m : scrR s₀ ∈ [scrR s₀] := List.mem_singleton_self _
  exact ((((((Frame.refl _ _).writeW m _ (c 0 (by decide))).writeW m _ (c 8 (by decide))).writeW m _
    (c 16 (by decide))).writeW m _ (c loOff (by decide))).writeW m _ (c hiOff (by decide))).writeW m _
    (c fOff (by decide))

theorem common_zero {s₀ : State} (hp : Pre z s₀) {s₁ : State}
    (hm : s₁.mem = setupMem s₀.mem (scr s₀) (s₀.gpr .x25) (s₀.gpr .x26) (s₀.gpr .x27) (s₀.gpr .x3)
      (fl s₀))
    (ho : ∀ q, q ≠ .x3 → q ≠ .x4 → q ≠ T → s₁.gpr q = s₀.gpr q) (hrd : s₁.rd = s₀.rd)
    (hwr : s₁.wr = s₀.wr) : Common P s₀ 0 s₁ := by
  have hf := setup_frame s₀ (s₀.gpr .x25) (s₀.gpr .x26) (s₀.gpr .x27) (s₀.gpr .x3) (fl s₀)
  refine ⟨fun r hr => ?_, hrd, hwr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨-, b, -, -, c, d, -⟩ := kept_ok r hr
    exact ho r c d b
  · rw [hm]; exact hf.mono fun r hr => by simp only [List.mem_singleton] at hr; simp [hr]
  · refine stateAt_eq' fun k hk => ?_
    rw [hm, hp.state_frame hf hk, ← stateAt_get' z _ _ hk]
    rfl
  all_goals simp (config := {decide := true}) only [hm, setupMem, cell_sep, Mem.readW_writeW_self64]
  · simp
  · rw [Nat.zero_mul, Nat.add_zero, Nat.div_eq_of_lt (s₀.gpr .x3).isLt]; rfl

theorem correct (hR : ROk P) {s₀ : State} (hp : Pre z s₀) :
    WP isa (Impl.Blake2.AArch64.compress P) s₀ fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ (compressAArch64 P).post s₀ s' := by
  refine WP.seq (WP.mono (setup_ok s₀ (scr s₀) rfl hp.out_scr) fun s₁ ⟨hm₁, ho₁, hrd₁, hwr₁⟩ => ?_)
  have hc₁ : Common P s₀ 0 s₁ := common_zero P hp hm₁ ho₁ hrd₁ hwr₁
  refine WP.seq (WP.mono (Q := Common P s₀ (nb s₀)) ?_ fun s₂ hc => ?_)
  · have hx2 : s₁.gpr .x2 = s₀.gpr .x2 := ho₁ _ (by decide) (by decide) (by decide)
    refine WP.ite (s₁.gpr .x2 == 0) (by simp only [eval, State.read, ext64]) (fun h => ?_)
      (fun h => ?_)
    · have h0 : nb s₀ = 0 := by rw [hx2] at h; simp at h; simp [nb, h]
      exact WP.block_nil (M := isa) (h0 ▸ hc₁)
    · have hpos : 0 < nb s₀ := by
        rw [hx2] at h
        simp only [beq_eq_false_iff_ne, ne_eq] at h
        exact Nat.pos_of_ne_zero fun h' => h (BitVec.eq_of_toNat_eq (by simpa using h'))
      let Inv : Nat → State → Prop := fun m s => ∃ i, m = nb s₀ - i ∧ i < nb s₀ ∧ LInv P s₀ i s
      have hstep : ∀ m s, Inv m s → WP isa (Impl.Blake2.AArch64.body P) s (fun s' =>
          (eval (.nonzero .x .x2) s' = some false ∧ Common P s₀ (nb s₀) s') ∨
          (eval (.nonzero .x .x2) s' = some true ∧ ∃ m' < m, Inv m' s')) := by
        rintro m s ⟨i, rfl, hi, hL⟩
        refine WP.mono (body_ok P hR hp hi hL) fun s' h => ?_
        rcases h with ⟨he, hc⟩ | ⟨he, hi', hL'⟩
        · exact .inl ⟨he, hc⟩
        · exact .inr ⟨he, nb s₀ - (i + 1), by omega, i + 1, rfl, hi', hL'⟩
      have hL₀ : LInv P s₀ 0 s₁ :=
        { hc₁ with
          x1 := by rw [ho₁ _ (by decide) (by decide) (by decide)]; simp [blkAddr]
          x2 := by rw [hx2]; simp [nb] }
      exact WP.loop (M := isa) Inv hstep (nb s₀) s₁ ⟨0, rfl, hpos, hL₀⟩
  · refine WP.mono (restore_ok s₂ (scr s₀) (hc.x5 P) (by rw [hc.rd, hc.wr]; exact hp.in_scr))
      fun s' ⟨h25, h26, h27, ho, hm⟩ => ⟨fun r hr => ?_, ?_⟩
    · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first
        | (rw [h25]; exact hc.sv0) | (rw [h26]; exact hc.sv8) | (rw [h27]; exact hc.sv16)
        | (rw [ho _ (by decide) (by decide) (by decide)]; exact hc.kept _ (by decide))
    · show Spec.Blake2.stateAt z.bits s'.mem (st s₀) = _
      rw [hm, hc.state]

/-- The generic proof, for either word size. -/
theorem compress_correct (hR : ROk P) :
    ∀ s, (compressAArch64 P).pre s → ∃ t s', Exec isa (Impl.Blake2.AArch64.compress P) s t s' ∧
      AArch64.abiPreserved s s' ∧ (compressAArch64 P).post s s' := fun s hs => by
  obtain ⟨t, s', he, h₁, h₂⟩ := correct P hR (pre_of P s hs)
  exact ⟨t, s', he, ⟨h₁, Exec.sp he⟩, h₂⟩

end Loop

/-! ## BLAKE2b and BLAKE2s -/

theorem rok_b : ROk (z := .x) Spec.Blake2.b := by unfold ROk; decide
theorem rok_s : ROk (z := .w) Spec.Blake2.s := by unfold ROk; decide

theorem compressB_correct : ∀ s, (compressAArch64 Spec.Blake2.b).pre s → ∃ t s',
    Exec isa (Impl.Blake2.AArch64.compress Spec.Blake2.b) s t s' ∧ AArch64.abiPreserved s s' ∧
      (compressAArch64 Spec.Blake2.b).post s s' :=
  compress_correct (z := .x) _ rok_b

theorem compressS_correct : ∀ s, (compressAArch64 Spec.Blake2.s).pre s → ∃ t s',
    Exec isa (Impl.Blake2.AArch64.compress Spec.Blake2.s) s t s' ∧ AArch64.abiPreserved s s' ∧
      (compressAArch64 Spec.Blake2.s).post s s' :=
  compress_correct (z := .w) _ rok_s

theorem compressB_noFrames : (Impl.Blake2.AArch64.compress Spec.Blake2.b).noFrames = true := by
  lit_decide

theorem compressS_noFrames : (Impl.Blake2.AArch64.compress Spec.Blake2.s).noFrames = true := by
  lit_decide

theorem agree_pub {w : Nat} (P : Params w) :
    ∀ s₁ s₂, (compressAArch64 P).pre s₁ → (compressAArch64 P).pre s₂ →
      (compressAArch64 P).pub s₁ s₂ → taint.Agree (Taint.ofRegs [.x0, .x1, .x2, .x5]) s₁ s₂ := by
  rintro s₁ s₂ - - ⟨h0, h1, h2, -, -, h5, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> assumption

theorem compressB_ct : ConstantTime isa (compressAArch64 Spec.Blake2.b).pre
    (compressAArch64 Spec.Blake2.b).pub (Impl.Blake2.AArch64.compress Spec.Blake2.b) :=
  VG.Taint.constantTime (A := taint) _ (agree_pub _) (by taint_decide)

theorem compressS_ct : ConstantTime isa (compressAArch64 Spec.Blake2.s).pre
    (compressAArch64 Spec.Blake2.s).pub (Impl.Blake2.AArch64.compress Spec.Blake2.s) :=
  VG.Taint.constantTime (A := taint) _ (agree_pub _) (by taint_decide)

/-- A state satisfying the precondition (with no blocks). -/
def satState (n : Nat) : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x5 => 0x3000 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, n⟩, ⟨0x3000, 512⟩]

theorem compressB_verified' :
    Verified AArch64.target (Impl.Blake2.AArch64.compress Spec.Blake2.b) (compressAArch64 Spec.Blake2.b) :=
  ⟨compressB_correct, compressB_ct, satState 64, rfl, rfl, Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide)⟩

theorem compressS_verified' :
    Verified AArch64.target (Impl.Blake2.AArch64.compress Spec.Blake2.s) (compressAArch64 Spec.Blake2.s) :=
  ⟨compressS_correct, compressS_ct, satState 32, rfl, rfl, Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide)⟩

theorem compressB_verified :
    Verified AArch64.target (Impl.Blake2.AArch64.compress Spec.Blake2.b)
      (Spec.Blake2.compressBContract AArch64.abi) :=
  compressB_verified'.of_implies (by
    sig_implies [Spec.Blake2.compressBContract, Spec.Blake2.compressBSig, compressAArch64,
      AArch64.abi, AArch64.argRegs, Spec.Blake2.blockBytes] [satState] using satState 64)

theorem compressS_verified :
    Verified AArch64.target (Impl.Blake2.AArch64.compress Spec.Blake2.s)
      (Spec.Blake2.compressSContract AArch64.abi) :=
  compressS_verified'.of_implies (by
    sig_implies [Spec.Blake2.compressSContract, Spec.Blake2.compressSSig, compressAArch64,
      AArch64.abi, AArch64.argRegs, Spec.Blake2.blockBytes] [satState] using satState 32)

end VG.Proof.Blake2.AArch64
