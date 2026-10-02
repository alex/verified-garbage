import VerifiedGarbage.Proof.MlDsa.Arm.KeyGen.Site
import VerifiedGarbage.Spec.MlDsa.Contract
import VerifiedGarbage.Proof.Framework.Sig

/-!
# ML-DSA on 32-bit ARM: the contracts of the primitives, evaluated

For each primitive the top-level functions call, its contract's precondition
(`ntt_pre`, …), from plain facts about the state `x` the callee starts from:
the arguments in their registers (and the fifth in the stack slot, `stackArg x
0`), the regions it is given, their disjointness and the stack below `x.sp`;
what its postcondition says (`…_post`); and its public data, from the
equalities of two such states (`…_pub`). Each is proven once, by evaluating
the contract (`sig_pre`, `sig_post`, `sig_pub`) on a state that is a variable.
-/

namespace VG.Proof.MlDsa.Arm.KeyGen

open VG VG.Arm VG.Proof.MlKem.Arm
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- Closes the evaluated precondition of a contract from the hypotheses. -/
macro "cpre" : tactic => `(tactic| (
  and_intros <;> first
    | assumption
    | (have := State.sp _ |>.isLt; omega)
    | omega))

/-! ## `vg_mldsa_ntt`, `vg_mldsa_inv_ntt` -/

section
variable {stk : Nat} {x y : State}

theorem ip_pre {t : Poly → Poly} {f w : BitVec 32} (g0 : x.gpr .r0 = f) (g1 : x.gpr .r1 = w)
    (hrd : x.rd = []) (hwr : x.wr = [regA f 1024, regA w 1024]) (hsp : stk ≤ x.sp.toNat)
    (hd : (regA f 1024).Disjoint (regA w 1024)) (kf : (below x stk).Disjoint (regA f 1024))
    (kw : (below x stk).Disjoint (regA w 1024)) (ff : f.toNat + 1024 ≤ 2 ^ 32) (fw : w.toNat + 1024 ≤ 2 ^ 32)
    (hr : Reduced x.mem (State.addr f)) : (inPlaceContract Arm.abi t stk).pre x := by
  rcases stk with _ | n <;>
  · sig_pre [inPlaceContract, inPlaceSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    simp only [g0, g1]
    cpre

theorem ip_post {t : Poly → Poly} (h : (inPlaceContract Arm.abi t stk).post x y) :
    PolyIs y.mem (State.addr (x.gpr .r0)) (t (polyAt x.mem (State.addr (x.gpr .r0)))) := by
  sig_post [inPlaceContract, inPlaceSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
  exact h

theorem ip_pub {t : Poly → Poly} (hsp : x.sp = y.sp) (h0 : x.gpr .r0 = y.gpr .r0) (h1 : x.gpr .r1 = y.gpr .r1) :
    (inPlaceContract Arm.abi t stk).pub x y := by
  sig_pub [inPlaceContract, inPlaceSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  exact ⟨hsp, h0, h1⟩

end

/-! ## `vg_mldsa_multiply_ntt`, `vg_mldsa_multiply_add_ntt` -/

section
variable {stk : Nat} {x y : State} {h f g : BitVec 32}

theorem mul_pre (g0 : x.gpr .r0 = h) (g1 : x.gpr .r1 = f) (g2 : x.gpr .r2 = g)
    (hrd : x.rd = [regA f 1024, regA g 1024]) (hwr : x.wr = [regA h 1024]) (hsp : stk ≤ x.sp.toNat)
    (d1 : (regA h 1024).Disjoint (regA f 1024)) (d2 : (regA h 1024).Disjoint (regA g 1024))
    (kh : (below x stk).Disjoint (regA h 1024)) (kf : (below x stk).Disjoint (regA f 1024))
    (kg : (below x stk).Disjoint (regA g 1024)) (fh : h.toNat + 1024 ≤ 2 ^ 32) (ff : f.toNat + 1024 ≤ 2 ^ 32)
    (fg : g.toNat + 1024 ≤ 2 ^ 32) (rf : Reduced x.mem (State.addr f)) (rg : Reduced x.mem (State.addr g)) :
    (mulContract Arm.abi stk).pre x := by
  rcases stk with _ | n <;>
  · sig_pre [mulContract, mulSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    simp only [g0, g1, g2]
    cpre

theorem mul_post (hp : (mulContract Arm.abi stk).post x y) :
    PolyIs y.mem (State.addr (x.gpr .r0))
      (multiplyNTT (polyAt x.mem (State.addr (x.gpr .r1))) (polyAt x.mem (State.addr (x.gpr .r2)))) := by
  sig_post [mulContract, mulSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hp
  exact hp

theorem mulAdd_pre (g0 : x.gpr .r0 = h) (g1 : x.gpr .r1 = f) (g2 : x.gpr .r2 = g)
    (hrd : x.rd = [regA f 1024, regA g 1024]) (hwr : x.wr = [regA h 1024]) (hsp : stk ≤ x.sp.toNat)
    (d1 : (regA h 1024).Disjoint (regA f 1024)) (d2 : (regA h 1024).Disjoint (regA g 1024))
    (kh : (below x stk).Disjoint (regA h 1024)) (kf : (below x stk).Disjoint (regA f 1024))
    (kg : (below x stk).Disjoint (regA g 1024)) (fh : h.toNat + 1024 ≤ 2 ^ 32) (ff : f.toNat + 1024 ≤ 2 ^ 32)
    (fg : g.toNat + 1024 ≤ 2 ^ 32) (rh : Reduced x.mem (State.addr h)) (rf : Reduced x.mem (State.addr f))
    (rg : Reduced x.mem (State.addr g)) : (mulAddContract Arm.abi stk).pre x := by
  rcases stk with _ | n <;>
  · sig_pre [mulAddContract, mulSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    simp only [g0, g1, g2]
    cpre

theorem mulAdd_post (hp : (mulAddContract Arm.abi stk).post x y) :
    PolyIs y.mem (State.addr (x.gpr .r0)) (add (polyAt x.mem (State.addr (x.gpr .r0)))
      (multiplyNTT (polyAt x.mem (State.addr (x.gpr .r1))) (polyAt x.mem (State.addr (x.gpr .r2))))) := by
  sig_post [mulAddContract, mulSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hp
  exact hp

theorem mul_pub (hsp : x.sp = y.sp) (h0 : x.gpr .r0 = y.gpr .r0) (h1 : x.gpr .r1 = y.gpr .r1)
    (h2 : x.gpr .r2 = y.gpr .r2) : (mulContract Arm.abi stk).pub x y := by
  sig_pub [mulContract, mulSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  exact ⟨hsp, h0, h1, h2⟩

theorem mulAdd_pub (hsp : x.sp = y.sp) (h0 : x.gpr .r0 = y.gpr .r0) (h1 : x.gpr .r1 = y.gpr .r1)
    (h2 : x.gpr .r2 = y.gpr .r2) : (mulAddContract Arm.abi stk).pub x y := by
  sig_pub [mulAddContract, mulSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  exact ⟨hsp, h0, h1, h2⟩

end

/-! ## `vg_mldsa_add`, `vg_mldsa_sub` -/

section
variable {stk : Nat} {x y : State} {f g : BitVec 32}

theorem add_pre (g0 : x.gpr .r0 = f) (g1 : x.gpr .r1 = g) (hrd : x.rd = [regA g 1024])
    (hwr : x.wr = [regA f 1024]) (hsp : stk ≤ x.sp.toNat) (d1 : (regA f 1024).Disjoint (regA g 1024))
    (kf : (below x stk).Disjoint (regA f 1024)) (kg : (below x stk).Disjoint (regA g 1024))
    (ff : f.toNat + 1024 ≤ 2 ^ 32) (fg : g.toNat + 1024 ≤ 2 ^ 32) (rf : Reduced x.mem (State.addr f))
    (rg : Reduced x.mem (State.addr g)) : (addContract Arm.abi stk).pre x := by
  rcases stk with _ | n <;>
  · sig_pre [addContract, accSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    simp only [g0, g1]
    cpre

theorem add_post (hp : (addContract Arm.abi stk).post x y) :
    PolyIs y.mem (State.addr (x.gpr .r0))
      (add (polyAt x.mem (State.addr (x.gpr .r0))) (polyAt x.mem (State.addr (x.gpr .r1)))) := by
  sig_post [addContract, accSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hp
  exact hp

theorem add_pub (hsp : x.sp = y.sp) (h0 : x.gpr .r0 = y.gpr .r0) (h1 : x.gpr .r1 = y.gpr .r1) :
    (addContract Arm.abi stk).pub x y := by
  sig_pub [addContract, accSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  exact ⟨hsp, h0, h1⟩

theorem sub_pre (g0 : x.gpr .r0 = f) (g1 : x.gpr .r1 = g) (hrd : x.rd = [regA g 1024])
    (hwr : x.wr = [regA f 1024]) (hsp : stk ≤ x.sp.toNat) (d1 : (regA f 1024).Disjoint (regA g 1024))
    (kf : (below x stk).Disjoint (regA f 1024)) (kg : (below x stk).Disjoint (regA g 1024))
    (ff : f.toNat + 1024 ≤ 2 ^ 32) (fg : g.toNat + 1024 ≤ 2 ^ 32) (rf : Reduced x.mem (State.addr f))
    (rg : Reduced x.mem (State.addr g)) : (subContract Arm.abi stk).pre x := by
  rcases stk with _ | n <;>
  · sig_pre [subContract, accSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    simp only [g0, g1]
    cpre

theorem sub_post (hp : (subContract Arm.abi stk).post x y) :
    PolyIs y.mem (State.addr (x.gpr .r0))
      (sub (polyAt x.mem (State.addr (x.gpr .r0))) (polyAt x.mem (State.addr (x.gpr .r1)))) := by
  sig_post [subContract, accSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hp
  exact hp

theorem sub_pub (hsp : x.sp = y.sp) (h0 : x.gpr .r0 = y.gpr .r0) (h1 : x.gpr .r1 = y.gpr .r1) :
    (subContract Arm.abi stk).pub x y := by
  sig_pub [subContract, accSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  exact ⟨hsp, h0, h1⟩

end

/-! ## `vg_mldsa_rej_ntt_poly`, `vg_mldsa_rej_bounded_poly` -/

section
variable {stk : Nat} {x y : State} {sd a w e : BitVec 32}

theorem rejNtt_pre (g0 : x.gpr .r0 = sd) (g1 : x.gpr .r1 = a) (g2 : x.gpr .r2 = w)
    (hrd : x.rd = [regA sd 34]) (hwr : x.wr = [regA a 1024, regA w 2048]) (hsp : stk ≤ x.sp.toNat)
    (d1 : (regA sd 34).Disjoint (regA a 1024)) (d2 : (regA sd 34).Disjoint (regA w 2048))
    (d3 : (regA a 1024).Disjoint (regA w 2048))
    (k1 : (below x stk).Disjoint (regA sd 34)) (k2 : (below x stk).Disjoint (regA a 1024))
    (k3 : (below x stk).Disjoint (regA w 2048)) (f1 : sd.toNat + 34 ≤ 2 ^ 32) (f2 : a.toNat + 1024 ≤ 2 ^ 32)
    (f3 : w.toNat + 2048 ≤ 2 ^ 32) : (rejNTTContract Arm.abi stk).pre x := by
  rcases stk with _ | n <;>
  · sig_pre [rejNTTContract, rejNTTSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    simp only [g0, g1, g2]
    cpre

theorem rejNtt_post (hp : (rejNTTContract Arm.abi stk).post x y) :
    ((y.gpr .r0 = 1 → Reduced y.mem (State.addr (x.gpr .r1))) ∧
      Outcome (fun b => rejNTTPoly b.rejNTT (bytesAt x.mem (State.addr (x.gpr .r0)) 34)) (y.gpr .r0)
        (polyAt y.mem (State.addr (x.gpr .r1)))) := by
  sig_post [rejNTTContract, rejNTTSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hp
  rwa [setWidth_append32] at hp

theorem rejNtt_pub (hsp : x.sp = y.sp) (h0 : x.gpr .r0 = y.gpr .r0) (h1 : x.gpr .r1 = y.gpr .r1)
    (h2 : x.gpr .r2 = y.gpr .r2)
    (hl : bytesAt x.mem (State.addr (x.gpr .r0)) 34 = bytesAt y.mem (State.addr (y.gpr .r0)) 34) :
    (rejNTTContract Arm.abi stk).pub x y := by
  sig_pub [rejNTTContract, rejNTTSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  exact ⟨hsp, congrArg leakBytes hl, h0, h1, h2⟩

theorem rejBounded_pre (g0 : x.gpr .r0 = sd) (g1 : x.gpr .r1 = e) (g2 : x.gpr .r2 = a) (g3 : x.gpr .r3 = w)
    (hrd : x.rd = [regA sd 66]) (hwr : x.wr = [regA a 1024, regA w 2048]) (hsp : stk ≤ x.sp.toNat)
    (d1 : (regA sd 66).Disjoint (regA a 1024)) (d2 : (regA sd 66).Disjoint (regA w 2048))
    (d3 : (regA a 1024).Disjoint (regA w 2048))
    (k1 : (below x stk).Disjoint (regA sd 66)) (k2 : (below x stk).Disjoint (regA a 1024))
    (k3 : (below x stk).Disjoint (regA w 2048)) (f1 : sd.toNat + 66 ≤ 2 ^ 32) (f2 : a.toNat + 1024 ≤ 2 ^ 32)
    (f3 : w.toNat + 2048 ≤ 2 ^ 32) (he : e.toNat = 2 ∨ e.toNat = 4) : (rejBoundedContract Arm.abi stk).pre x := by
  rcases stk with _ | n <;>
  · sig_pre [rejBoundedContract, rejBoundedSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    simp only [g0, g1, g2, g3]
    cpre

theorem rejBounded_post (hp : (rejBoundedContract Arm.abi stk).post x y) :
    ((y.gpr .r0 = 1 → Reduced y.mem (State.addr (x.gpr .r2))) ∧
      Outcome (fun b => (rejBoundedPoly (x.gpr .r1).toNat b.rejBounded (bytesAt x.mem (State.addr (x.gpr .r0)) 66)).map
        toRq) (y.gpr .r0) (polyAt y.mem (State.addr (x.gpr .r2)))) := by
  sig_post [rejBoundedContract, rejBoundedSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hp
  rwa [setWidth_append32] at hp

theorem rejBounded_pub (hsp : x.sp = y.sp) (h0 : x.gpr .r0 = y.gpr .r0) (h1 : x.gpr .r1 = y.gpr .r1)
    (h2 : x.gpr .r2 = y.gpr .r2) (h3 : x.gpr .r3 = y.gpr .r3)
    (hl : rejBoundedLeak (x.gpr .r1).toNat (bytesAt x.mem (State.addr (x.gpr .r0)) 66) =
      rejBoundedLeak (y.gpr .r1).toNat (bytesAt y.mem (State.addr (y.gpr .r0)) 66)) :
    (rejBoundedContract Arm.abi stk).pub x y := by
  sig_pub [rejBoundedContract, rejBoundedSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  exact ⟨hsp, hl, h0, h1, h2, h3⟩

end

/-! ## `vg_mldsa_power2round` -/

section
variable {stk : Nat} {x y : State} {t t1 t0 : BitVec 32}

theorem p2r_pre (g0 : x.gpr .r0 = t) (g1 : x.gpr .r1 = t1) (g2 : x.gpr .r2 = t0)
    (hrd : x.rd = [regA t 1024]) (hwr : x.wr = [regA t1 1024, regA t0 1024]) (hsp : stk ≤ x.sp.toNat)
    (d1 : (regA t 1024).Disjoint (regA t1 1024)) (d2 : (regA t 1024).Disjoint (regA t0 1024))
    (d3 : (regA t1 1024).Disjoint (regA t0 1024))
    (k1 : (below x stk).Disjoint (regA t 1024)) (k2 : (below x stk).Disjoint (regA t1 1024))
    (k3 : (below x stk).Disjoint (regA t0 1024)) (f1 : t.toNat + 1024 ≤ 2 ^ 32) (f2 : t1.toNat + 1024 ≤ 2 ^ 32)
    (f3 : t0.toNat + 1024 ≤ 2 ^ 32) (hr : Reduced x.mem (State.addr t)) : (power2RoundContract Arm.abi stk).pre x := by
  rcases stk with _ | n <;>
  · sig_pre [power2RoundContract, power2RoundSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    simp only [g0, g1, g2]
    cpre

theorem p2r_post (hp : (power2RoundContract Arm.abi stk).post x y) :
    NatPolyIs y.mem (State.addr (x.gpr .r1))
        ((polyAt x.mem (State.addr (x.gpr .r0))).map fun c => (power2Round c).1.toNat) ∧
      PolyIs y.mem (State.addr (x.gpr .r2)) ((polyAt x.mem (State.addr (x.gpr .r0))).map fun c => ofInt (power2Round c).2) := by
  sig_post [power2RoundContract, power2RoundSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hp
  exact hp

theorem p2r_pub (hsp : x.sp = y.sp) (h0 : x.gpr .r0 = y.gpr .r0) (h1 : x.gpr .r1 = y.gpr .r1)
    (h2 : x.gpr .r2 = y.gpr .r2) : (power2RoundContract Arm.abi stk).pub x y := by
  sig_pub [power2RoundContract, power2RoundSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  exact ⟨hsp, h0, h1, h2⟩

end

/-! ## `vg_mldsa_simple_bit_pack`, `vg_mldsa_bit_pack` -/

section
variable {stk : Nat} {x y : State} {f a b o l : BitVec 32}

theorem sbp_pre (g0 : x.gpr .r0 = f) (g1 : x.gpr .r1 = b) (g2 : x.gpr .r2 = o) (g3 : x.gpr .r3 = l)
    (hrd : x.rd = [regA f 1024]) (hwr : x.wr = [regA o l.toNat]) (hsp : stk ≤ x.sp.toNat)
    (d1 : (regA f 1024).Disjoint (regA o l.toNat))
    (k1 : (below x stk).Disjoint (regA f 1024)) (k2 : (below x stk).Disjoint (regA o l.toNat))
    (f1 : f.toNat + 1024 ≤ 2 ^ 32) (f2 : o.toNat + l.toNat ≤ 2 ^ 32) (hb : b.toNat ∈ simpleBitPackBounds)
    (hl : l.toNat = 32 * bitlen b.toNat) (hc : ∀ i < n, (coeffAt x.mem (State.addr f) i).toNat ≤ b.toNat) :
    (simpleBitPackContract Arm.abi stk).pre x := by
  rcases stk with _ | n <;>
  · sig_pre [simpleBitPackContract, simpleBitPackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    simp only [g0, g1, g2, g3]
    cpre

theorem sbp_post (hp : (simpleBitPackContract Arm.abi stk).post x y) :
    bytesAt y.mem (State.addr (x.gpr .r2)) (x.gpr .r3).toNat =
      simpleBitPack (natPolyAt x.mem (State.addr (x.gpr .r0))) (x.gpr .r1).toNat := by
  sig_post [simpleBitPackContract, simpleBitPackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hp
  exact hp

theorem sbp_pub (hsp : x.sp = y.sp) (h0 : x.gpr .r0 = y.gpr .r0) (h1 : x.gpr .r1 = y.gpr .r1)
    (h2 : x.gpr .r2 = y.gpr .r2) (h3 : x.gpr .r3 = y.gpr .r3) : (simpleBitPackContract Arm.abi stk).pub x y := by
  sig_pub [simpleBitPackContract, simpleBitPackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  exact ⟨hsp, h0, h1, h2, h3⟩

theorem bp_pre (g0 : x.gpr .r0 = f) (g1 : x.gpr .r1 = a) (g2 : x.gpr .r2 = b) (g3 : x.gpr .r3 = o)
    (ga : stackArg x 0 = l)
    (hrd : x.rd = [regA f 1024, ⟨stackArgAddr x 0, 4⟩]) (hwr : x.wr = [regA o l.toNat]) (hsp : stk ≤ x.sp.toNat)
    (hs4 : x.sp.toNat + 4 ≤ 2 ^ 32)
    (d1 : (regA f 1024).Disjoint (regA o l.toNat)) (d2 : (regA o l.toNat).Disjoint ⟨stackArgAddr x 0, 4⟩)
    (k1 : (below x stk).Disjoint (regA f 1024)) (k2 : (below x stk).Disjoint (regA o l.toNat))
    (k3 : (below x stk).Disjoint ⟨stackArgAddr x 0, 4⟩)
    (f1 : f.toNat + 1024 ≤ 2 ^ 32) (f2 : o.toNat + l.toNat ≤ 2 ^ 32) (hab : (a.toNat, b.toNat) ∈ bitPackParams)
    (hl : l.toNat = 32 * bitlen (a.toNat + b.toNat)) (hr : Reduced x.mem (State.addr f))
    (hc : ∀ i < n, -(a.toNat : Int) ≤ modPm (coeffAt x.mem (State.addr f) i).toNat q ∧
      modPm (coeffAt x.mem (State.addr f) i).toNat q ≤ b.toNat) :
    (bitPackContract Arm.abi stk).pre x := by
  rcases stk with _ | n <;>
  · sig_pre [bitPackContract, bitPackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    simp only [g0, g1, g2, g3, ga]
    cpre

theorem bp_post (hp : (bitPackContract Arm.abi stk).post x y) :
    bytesAt y.mem (State.addr (x.gpr .r3)) (stackArg x 0).toNat =
      bitPack ((polyAt x.mem (State.addr (x.gpr .r0))).map fun c => modPm c.val q) (x.gpr .r1).toNat
        (x.gpr .r2).toNat := by
  sig_post [bitPackContract, bitPackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hp
  exact hp

theorem bp_pub (hsp : x.sp = y.sp) (h0 : x.gpr .r0 = y.gpr .r0) (h1 : x.gpr .r1 = y.gpr .r1)
    (h2 : x.gpr .r2 = y.gpr .r2) (h3 : x.gpr .r3 = y.gpr .r3) (ha : stackArg x 0 = stackArg y 0) :
    (bitPackContract Arm.abi stk).pub x y := by
  sig_pub [bitPackContract, bitPackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  exact ⟨hsp, h0, h1, h2, h3, ha⟩

end

/-! ## `vg_mldsa_sample_in_ball` -/

section
variable {stk : Nat} {x y : State} {ct len tau c w : BitVec 32}

theorem ball_pre (g0 : x.gpr .r0 = ct) (g1 : x.gpr .r1 = len) (g2 : x.gpr .r2 = tau) (g3 : x.gpr .r3 = c)
    (ga : stackArg x 0 = w)
    (hrd : x.rd = [regA ct len.toNat, ⟨stackArgAddr x 0, 4⟩]) (hwr : x.wr = [regA c 1024, regA w 2048])
    (hsp : stk ≤ x.sp.toNat) (hs4 : x.sp.toNat + 4 ≤ 2 ^ 32)
    (d1 : (regA ct len.toNat).Disjoint (regA c 1024)) (d2 : (regA ct len.toNat).Disjoint (regA w 2048))
    (d3 : (regA c 1024).Disjoint (regA w 2048)) (d4 : (regA c 1024).Disjoint ⟨stackArgAddr x 0, 4⟩)
    (d5 : (regA w 2048).Disjoint ⟨stackArgAddr x 0, 4⟩)
    (k1 : (below x stk).Disjoint (regA ct len.toNat)) (k2 : (below x stk).Disjoint (regA c 1024))
    (k3 : (below x stk).Disjoint (regA w 2048)) (k4 : (below x stk).Disjoint ⟨stackArgAddr x 0, 4⟩)
    (f1 : ct.toNat + len.toNat ≤ 2 ^ 32) (f2 : c.toNat + 1024 ≤ 2 ^ 32) (f3 : w.toNat + 2048 ≤ 2 ^ 32)
    (hp : (len.toNat, tau.toNat) ∈ ballParams) : (sampleInBallContract Arm.abi stk).pre x := by
  rcases stk with _ | n <;>
  · sig_pre [sampleInBallContract, sampleInBallSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    simp only [g0, g1, g2, g3, ga]
    cpre

theorem ball_post (hp : (sampleInBallContract Arm.abi stk).post x y) :
    ((y.gpr .r0 = 1 → Reduced y.mem (State.addr (x.gpr .r3))) ∧
      Outcome (fun b => (sampleInBall (x.gpr .r2).toNat b.ball
        (bytesAt x.mem (State.addr (x.gpr .r0)) (x.gpr .r1).toNat)).map toRq) (y.gpr .r0)
        (polyAt y.mem (State.addr (x.gpr .r3)))) := by
  sig_post [sampleInBallContract, sampleInBallSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hp
  rwa [setWidth_append32] at hp

theorem ball_pub (hsp : x.sp = y.sp) (h0 : x.gpr .r0 = y.gpr .r0) (h1 : x.gpr .r1 = y.gpr .r1)
    (h2 : x.gpr .r2 = y.gpr .r2) (h3 : x.gpr .r3 = y.gpr .r3) (ha : stackArg x 0 = stackArg y 0)
    (hl : bytesAt x.mem (State.addr (x.gpr .r0)) (x.gpr .r1).toNat =
      bytesAt y.mem (State.addr (y.gpr .r0)) (y.gpr .r1).toNat) :
    (sampleInBallContract Arm.abi stk).pub x y := by
  sig_pub [sampleInBallContract, sampleInBallSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  exact ⟨hsp, congrArg leakBytes hl, h0, h1, h2, h3, ha⟩

end

/-! ## `vg_mldsa_use_hint` -/

section
variable {stk : Nat} {x y : State} {h r g2 o : BitVec 32}

theorem useHint_pre (g0 : x.gpr .r0 = h) (g1 : x.gpr .r1 = r) (gg : x.gpr .r2 = g2) (g3 : x.gpr .r3 = o)
    (hrd : x.rd = [regA h 1024, regA r 1024]) (hwr : x.wr = [regA o 1024]) (hsp : stk ≤ x.sp.toNat)
    (d1 : (regA h 1024).Disjoint (regA o 1024)) (d2 : (regA r 1024).Disjoint (regA o 1024))
    (k1 : (below x stk).Disjoint (regA h 1024)) (k2 : (below x stk).Disjoint (regA r 1024))
    (k3 : (below x stk).Disjoint (regA o 1024)) (f1 : h.toNat + 1024 ≤ 2 ^ 32) (f2 : r.toNat + 1024 ≤ 2 ^ 32)
    (f3 : o.toNat + 1024 ≤ 2 ^ 32) (hg : g2.toNat ∈ gamma2s) (hr : Reduced x.mem (State.addr r)) :
    (useHintContract Arm.abi stk).pre x := by
  rcases stk with _ | n <;>
  · sig_pre [useHintContract, useHintSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    simp only [g0, g1, gg, g3]
    cpre

theorem useHint_post (hp : (useHintContract Arm.abi stk).post x y) :
    NatPolyIs y.mem (State.addr (x.gpr .r3)) (Vector.zipWith (fun hj rj => (useHint (x.gpr .r2).toNat hj rj).toNat)
      ((hintAt x.mem (State.addr (x.gpr .r0)) 1).headD (Vector.replicate n false))
      (polyAt x.mem (State.addr (x.gpr .r1)))) := by
  sig_post [useHintContract, useHintSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hp
  exact hp

theorem useHint_pub (hsp : x.sp = y.sp) (h0 : x.gpr .r0 = y.gpr .r0) (h1 : x.gpr .r1 = y.gpr .r1)
    (h2 : x.gpr .r2 = y.gpr .r2) (h3 : x.gpr .r3 = y.gpr .r3) : (useHintContract Arm.abi stk).pub x y := by
  sig_pub [useHintContract, useHintSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  exact ⟨hsp, h0, h1, h2, h3⟩

end

/-! ## `vg_mldsa_bit_unpack`, `vg_mldsa_unpack_t1` -/

section
variable {stk : Nat} {x y : State} {v len a b f : BitVec 32}

theorem bu_pre (g0 : x.gpr .r0 = v) (g1 : x.gpr .r1 = len) (g2 : x.gpr .r2 = a) (g3 : x.gpr .r3 = b)
    (ga : stackArg x 0 = f)
    (hrd : x.rd = [regA v len.toNat, ⟨stackArgAddr x 0, 4⟩]) (hwr : x.wr = [regA f 1024])
    (hsp : stk ≤ x.sp.toNat) (hs4 : x.sp.toNat + 4 ≤ 2 ^ 32)
    (d1 : (regA v len.toNat).Disjoint (regA f 1024)) (d2 : (regA f 1024).Disjoint ⟨stackArgAddr x 0, 4⟩)
    (k1 : (below x stk).Disjoint (regA v len.toNat)) (k2 : (below x stk).Disjoint (regA f 1024))
    (k3 : (below x stk).Disjoint ⟨stackArgAddr x 0, 4⟩)
    (f1 : v.toNat + len.toNat ≤ 2 ^ 32) (f2 : f.toNat + 1024 ≤ 2 ^ 32)
    (hab : (a.toNat, b.toNat) ∈ bitPackParams) (hl : len.toNat = 32 * bitlen (a.toNat + b.toNat)) :
    (bitUnpackContract Arm.abi stk).pre x := by
  rcases stk with _ | n <;>
  · sig_pre [bitUnpackContract, bitUnpackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    simp only [g0, g1, g2, g3, ga]
    cpre

theorem bu_post (hp : (bitUnpackContract Arm.abi stk).post x y) :
    PolyIs y.mem (State.addr (stackArg x 0))
      (toRq (bitUnpack (bytesAt x.mem (State.addr (x.gpr .r0)) (x.gpr .r1).toNat) (x.gpr .r2).toNat
        (x.gpr .r3).toNat)) := by
  sig_post [bitUnpackContract, bitUnpackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hp
  exact hp

theorem bu_pub (hsp : x.sp = y.sp) (h0 : x.gpr .r0 = y.gpr .r0) (h1 : x.gpr .r1 = y.gpr .r1)
    (h2 : x.gpr .r2 = y.gpr .r2) (h3 : x.gpr .r3 = y.gpr .r3) (ha : stackArg x 0 = stackArg y 0) :
    (bitUnpackContract Arm.abi stk).pub x y := by
  sig_pub [bitUnpackContract, bitUnpackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  exact ⟨hsp, h0, h1, h2, h3, ha⟩

theorem t1_pre (g0 : x.gpr .r0 = v) (g1 : x.gpr .r1 = f)
    (hrd : x.rd = [regA v 320]) (hwr : x.wr = [regA f 1024]) (hsp : stk ≤ x.sp.toNat)
    (d1 : (regA v 320).Disjoint (regA f 1024))
    (k1 : (below x stk).Disjoint (regA v 320)) (k2 : (below x stk).Disjoint (regA f 1024))
    (f1 : v.toNat + 320 ≤ 2 ^ 32) (f2 : f.toNat + 1024 ≤ 2 ^ 32) :
    (unpackT1Contract Arm.abi stk).pre x := by
  rcases stk with _ | n <;>
  · sig_pre [unpackT1Contract, unpackT1Sig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    simp only [g0, g1]
    cpre

theorem t1_post (hp : (unpackT1Contract Arm.abi stk).post x y) :
    PolyIs y.mem (State.addr (x.gpr .r1))
      ((simpleBitUnpack (bytesAt x.mem (State.addr (x.gpr .r0)) 320) t1Max).map fun c => ofInt (c * 2 ^ d : Nat)) := by
  sig_post [unpackT1Contract, unpackT1Sig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hp
  exact hp

theorem t1_pub (hsp : x.sp = y.sp) (h0 : x.gpr .r0 = y.gpr .r0) (h1 : x.gpr .r1 = y.gpr .r1) :
    (unpackT1Contract Arm.abi stk).pub x y := by
  sig_pub [unpackT1Contract, unpackT1Sig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  exact ⟨hsp, h0, h1⟩

end

/-! ## `vg_mldsa_hint_bit_unpack` -/

section
variable {stk : Nat} {x y : State} {yy len om h hl : BitVec 32}

theorem hbu_pre (g0 : x.gpr .r0 = yy) (g1 : x.gpr .r1 = len) (g2 : x.gpr .r2 = om) (g3 : x.gpr .r3 = h)
    (ga : stackArg x 0 = hl)
    (hrd : x.rd = [regA yy len.toNat, ⟨stackArgAddr x 0, 4⟩]) (hwr : x.wr = [regA h (hl.toNat * 4)])
    (hsp : stk ≤ x.sp.toNat) (hs4 : x.sp.toNat + 4 ≤ 2 ^ 32)
    (d1 : (regA yy len.toNat).Disjoint (regA h (hl.toNat * 4)))
    (d2 : (regA h (hl.toNat * 4)).Disjoint ⟨stackArgAddr x 0, 4⟩)
    (k1 : (below x stk).Disjoint (regA yy len.toNat)) (k2 : (below x stk).Disjoint (regA h (hl.toNat * 4)))
    (k3 : (below x stk).Disjoint ⟨stackArgAddr x 0, 4⟩)
    (f1 : yy.toNat + len.toNat ≤ 2 ^ 32) (f2 : h.toNat + hl.toNat * 4 ≤ 2 ^ 32)
    (hp : (om.toNat, len.toNat - om.toNat) ∈ hintParams) (ho : om.toNat ≤ len.toNat)
    (hh : hl.toNat = 256 * (len.toNat - om.toNat)) :
    (hintBitUnpackContract Arm.abi stk).pre x := by
  rcases stk with _ | n <;>
  · sig_pre [hintBitUnpackContract, hintBitUnpackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    simp only [g0, g1, g2, g3, ga]
    cpre

theorem hbu_post (hp : (hintBitUnpackContract Arm.abi stk).post x y) :
    match hintBitUnpack (x.gpr .r2).toNat ((x.gpr .r1).toNat - (x.gpr .r2).toNat)
      (bytesAt x.mem (State.addr (x.gpr .r0)) (x.gpr .r1).toNat) with
    | some hint => y.gpr .r0 = 1 ∧ HintIs y.mem (State.addr (x.gpr .r3)) ((x.gpr .r1).toNat - (x.gpr .r2).toNat) hint
    | none => y.gpr .r0 = 0 := by
  sig_post [hintBitUnpackContract, hintBitUnpackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hp
  rwa [setWidth_append32] at hp

theorem hbu_pub (hsp : x.sp = y.sp) (h0 : x.gpr .r0 = y.gpr .r0) (h1 : x.gpr .r1 = y.gpr .r1)
    (h2 : x.gpr .r2 = y.gpr .r2) (h3 : x.gpr .r3 = y.gpr .r3) (ha : stackArg x 0 = stackArg y 0)
    (hl : bytesAt x.mem (State.addr (x.gpr .r0)) (x.gpr .r1).toNat =
      bytesAt y.mem (State.addr (y.gpr .r0)) (y.gpr .r1).toNat) :
    (hintBitUnpackContract Arm.abi stk).pub x y := by
  sig_pub [hintBitUnpackContract, hintBitUnpackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  exact ⟨hsp, congrArg leakBytes hl, h0, h1, h2, h3, ha⟩

end

/-! ## `vg_mldsa_norm_lt` -/

section
variable {stk : Nat} {x y : State} {f : BitVec 32}

theorem normLt_pre (g0 : x.gpr .r0 = f) (hrd : x.rd = [regA f 1024]) (hwr : x.wr = [])
    (hsp : stk ≤ x.sp.toNat) (k1 : (below x stk).Disjoint (regA f 1024)) (f1 : f.toNat + 1024 ≤ 2 ^ 32)
    (hr : Reduced x.mem (State.addr f)) : (normLtContract Arm.abi stk).pre x := by
  rcases stk with _ | n <;>
  · sig_pre [normLtContract, normLtSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    simp only [g0]
    cpre

theorem normLt_post (hp : (normLtContract Arm.abi stk).post x y) :
    y.gpr .r0 = if normRq [polyAt x.mem (State.addr (x.gpr .r0))] < (x.gpr .r1).toNat then 1 else 0 := by
  sig_post [normLtContract, normLtSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hp
  rwa [setWidth_append32] at hp

theorem normLt_pub (hsp : x.sp = y.sp) (h0 : x.gpr .r0 = y.gpr .r0) (h1 : x.gpr .r1 = y.gpr .r1) :
    (normLtContract Arm.abi stk).pub x y := by
  sig_pub [normLtContract, normLtSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  exact ⟨hsp, h0, h1⟩

end

end VG.Proof.MlDsa.Arm.KeyGen
