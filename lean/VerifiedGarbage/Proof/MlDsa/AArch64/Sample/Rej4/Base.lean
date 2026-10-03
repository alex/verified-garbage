import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Absorb
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Zero
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.RejNttLoop
import VerifiedGarbage.Proof.MlDsa.Sample.Hash

namespace VG.Proof.MlDsa.AArch64.Sample.Rej4
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Impl.MlDsa.AArch64.Sample.Rej4 (oBuf oSave saved)
open VG.Proof.Sha3 (iterF)

def seedP (s : State) : Addr := s.gpr .x0
def aP (s : State) : Addr := s.gpr .x1
def scr (s : State) : Addr := s.gpr .x2
def at' (s : State) (o : Nat) : Addr := scr s + BitVec.ofNat 64 o

def seedsR (s : State) : Region := ⟨seedP s,136⟩
def aR (s : State) : Region := ⟨aP s,4096⟩
def scrR (s : State) : Region := ⟨scr s,8192⟩
def lowR (s : State) : Region := ⟨scr s,oSave⟩
def saveR (s : State) : Region := ⟨at' s oSave,144⟩

structure Pre (s : State) : Prop where
  rd : s.rd = [seedsR s]
  wr : s.wr = [aR s,scrR s]
  seed_a : (seedsR s).Disjoint (aR s)
  seed_scr : (seedsR s).Disjoint (scrR s)
  a_scr : (aR s).Disjoint (scrR s)

abbrev B (s : State) (k : Nat) : List Byte := Spec.MlDsa.seed4 s.mem (seedP s) k
abbrev A0 (s : State) (k : Nat) : Spec.Sha3.State := Proof.Sha3.Seed34.A0 (B s k)
def stateP (s : State) (pair : Nat) : Addr := at' s (400*pair)
def bufP (s : State) (k : Nat) : Addr := at' s (oBuf+1008*k)
def bufAt (s : State) (k n : Nat) : Addr := at' s (oBuf+1008*k+168*n)

structure Env (σ s : State) : Prop where
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  sp : s.sp = σ.sp
  x19 : s.gpr .x19 = scr σ
  x20 : s.gpr .x20 = seedP σ
  x21 : s.gpr .x21 = aP σ
  x30 : s.gpr .x30 = σ.gpr .x30
  savedG : ∀ i < 10, s.mem.readW (at' σ (oSave+8*i)) 64 = σ.gpr (saved[i]!)
  savedV : ∀ i < 8, s.mem.readW (at' σ (oSave+80+8*i)) 64 = vdword (σ.v (Impl.Sha3.AArch64.Sha3.Vector.vreg (8+i))) 0
  frame : Frame [aR σ,scrR σ] σ.mem s.mem

theorem in_scr {σ s : State} (hp : Pre σ) (hw : s.wr = σ.wr) {d n : Nat} (hd : d+n ≤ 8192) :
    InRegions s.wr (at' σ d) n := by
  rw [hw,hp.wr]
  exact ⟨scrR σ,by simp,Offset.contains_base (scr σ) hd (by omega)⟩

theorem in_scr_rd {σ s : State} (hp : Pre σ) (_hr : s.rd = σ.rd) (hw : s.wr = σ.wr)
    {d n : Nat} (hd : d+n ≤ 8192) : InRegions (s.rd++s.wr) (at' σ d) n := by
  obtain ⟨r,hm,hc⟩ := in_scr hp hw hd
  exact ⟨r,List.mem_append.mpr (.inr hm),hc⟩

theorem in_seed {σ s : State} (hp : Pre σ) (hr : s.rd = σ.rd)
    {d n : Nat} (hd : d+n ≤ 136) : InRegions (s.rd++s.wr) (seedP σ+BitVec.ofNat 64 d) n := by
  rw [hr,hp.rd]
  exact ⟨seedsR σ,by simp,Offset.contains_base (seedP σ) hd (by omega)⟩

theorem low_save (σ : State) : (saveR σ).Disjoint (lowR σ) :=
  Offset.disjoint_base (scr σ) (d := oSave) (n := 144) (k := oSave) (by decide) (by decide)

theorem B_length (σ : State) (k : Nat) : (B σ k).length = 34 := Proof.Sha3.bytesAt_length _ _ _
end VG.Proof.MlDsa.AArch64.Sample.Rej4
