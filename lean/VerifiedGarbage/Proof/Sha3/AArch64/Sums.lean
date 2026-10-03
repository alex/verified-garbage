import VerifiedGarbage.Proof.Framework.AArch64.TaintMono
import VerifiedGarbage.Impl.MlKem1024.AArch64.Encaps
import VerifiedGarbage.Impl.MlKem1024.AArch64.Decaps
import VerifiedGarbage.Impl.MlKem.AArch64.Encaps
import VerifiedGarbage.Impl.MlKem.AArch64.Decaps
import VerifiedGarbage.Impl.MlKem.AArch64.KeyGen

/-!
# Summaries for the constant-time checks of the sponge's callers

The constant-time check of each caller of the sponge (ML-KEM, ML-DSA) with
each Keccak backend (`Permutation`) analyses, at every call, the permutation
and the sponge's functions, and the ML-KEM functions it calls. Here those
calls are summarized once (`taint_summary`), and the checks use the summaries
(`taint_decide_sum`).

Each summary applies to a call from its arguments public, and keeps public
the callee-saved registers the function does not write (`keeping`).
-/

namespace VG.Proof.Sha3.AArch64.MlKemSums

open VG VG.AArch64

/-- The callee-saved registers. -/
def callee : List Reg := [.x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28]

/-! ## ML-KEM's functions -/

taint_summary ntt : VectorTaint.taint (VectorTaint.ofRegs [.x0, .x1])
  (.call "vg_mlkem_ntt" Impl.MlKem.AArch64.ntt)
  keeping (VectorTaint.ofRegs callee)

taint_summary nttInv : VectorTaint.taint (VectorTaint.ofRegs [.x0, .x1])
  (.call "vg_mlkem_inv_ntt" Impl.MlKem.AArch64.nttInv)
  keeping (VectorTaint.ofRegs callee)

taint_summary mul : VectorTaint.taint (VectorTaint.ofRegs [.x0, .x1, .x2, .x3])
  (.call "vg_mlkem_multiply_ntts" Impl.MlKem.AArch64.multiplyNTTs)
  keeping (VectorTaint.ofRegs callee)

taint_summary add : VectorTaint.taint (VectorTaint.ofRegs [.x0, .x1])
  (.call "vg_mlkem_add" Impl.MlKem.AArch64.add)
  keeping (VectorTaint.ofRegs callee)

taint_summary sub : VectorTaint.taint (VectorTaint.ofRegs [.x0, .x1])
  (.call "vg_mlkem_sub" Impl.MlKem.AArch64.sub)
  keeping (VectorTaint.ofRegs callee)

taint_summary cbd2 : VectorTaint.taint (VectorTaint.ofRegs [.x0, .x1])
  (.call "vg_mlkem_cbd2" Impl.MlKem.AArch64.cbd2)
  keeping (VectorTaint.ofRegs callee)

taint_summary encode12 : VectorTaint.taint (VectorTaint.ofRegs [.x0, .x1])
  (.call "vg_mlkem_encode12" Impl.MlKem.AArch64.encode12)
  keeping (VectorTaint.ofRegs callee)

taint_summary decode12 : VectorTaint.taint (VectorTaint.ofRegs [.x0, .x1])
  (.call "vg_mlkem_decode12" Impl.MlKem.AArch64.decode12)
  keeping (VectorTaint.ofRegs callee)

taint_summary ce : VectorTaint.taint (VectorTaint.ofRegs [.x0, .x2, .x3])
  (.call "vg_mlkem_compress_encode" Impl.MlKem.AArch64.compressEncode)
  keeping (VectorTaint.ofRegs callee)

taint_summary dd : VectorTaint.taint (VectorTaint.ofRegs [.x0, .x1, .x3])
  (.call "vg_mlkem_decode_decompress" Impl.MlKem.AArch64.decodeDecompress)
  keeping (VectorTaint.ofRegs callee)

taint_summary ce1024 : VectorTaint.taint (VectorTaint.ofRegs [.x0, .x2, .x3])
  (.call "vg_mlkem1024_compress_encode" Impl.MlKem1024.AArch64.compressEncode)
  keeping (VectorTaint.ofRegs callee)

taint_summary dd1024 : VectorTaint.taint (VectorTaint.ofRegs [.x0, .x1, .x3])
  (.call "vg_mlkem1024_decode_decompress" Impl.MlKem1024.AArch64.decodeDecompress)
  keeping (VectorTaint.ofRegs callee)

end VG.Proof.Sha3.AArch64.MlKemSums

namespace VG.Proof.Sha3.AArch64

open Lean Elab Command

/-- The sets of callee-saved registers, besides `x19`–`x24` (which the
sponge's functions use), public at the calls of the sponge's functions. -/
private def spongeSaved : List (String × String) :=
  [("28", ".x25, .x26, .x27, .x28"), ("27", ".x25, .x26, .x27"), ("26", ".x25, .x26")]

/-- The summaries `sponge_taint_summaries` may define in `ns`, in the order
`taint_decide_sum` tries them. -/
def spongeSumNames : List String :=
  ["absorb23", "absorb24", "absorb28", "absorb27", "absorb24_26"] ++
  (spongeSaved.map fun (n, _) => s!"pad{n}") ++ (spongeSaved.map fun (n, _) => s!"squeeze{n}") ++
  (spongeSaved.map fun (n, _) => s!"perm{n}s") ++ ["permS"] ++
  (spongeSaved.map fun (n, _) => s!"perm{n}") ++ ["absorb", "pad", "squeeze", "perm"]

/-- The ML-KEM functions' summaries (`MlKemSums`). -/
def mlkemSumNames : List String :=
  ["ntt", "nttInv", "mul", "add", "sub", "cbd2", "encode12", "decode12", "ce", "dd", "ce1024",
    "dd1024"].map ("VG.Proof.Sha3.AArch64.MlKemSums." ++ ·)

/-- The commands of `sponge_taint_summaries ns callee`, with the summaries of
the permutation and of `pad` and `squeeze` those of `base`, if given (for a
callee that differs only in its absorb). The permutation and `pad` keep the
callee-saved registers; `absorb` and `squeeze` restore `x19`–`x24` from
memory, and keep `x25`–`x28`. -/
def spongeSumCmds (ns c : String) (base : Option String) :
    List String × List (String × String) := Id.run do
  let fn (f n : String) :=
    s!"(.call (\"vg_keccak_{f}\" ++ {c}.suffix) (Impl.Sha3.AArch64.Stream.{n}With {c}))"
  let ofRegs (rs : String) := s!"(VectorTaint.ofRegs [{rs}])"
  let all := "(VectorTaint.ofRegs VG.Proof.Sha3.AArch64.MlKemSums.callee)"
  let high := ofRegs ".x25, .x26, .x27, .x28"
  let pns := base.getD ns
  let args := ".x0, .x1, .x2, .x3, .x4, .x5"
  let absorb := s!"taint_summary {ns}.absorb : VectorTaint.taint {ofRegs args} " ++
    s!"{fn "absorb" "absorb"} keeping {high} using {pns}.perm"
  if let some b := base then
    return ([absorb], ["pad", "squeeze", "perm"].map fun n => (s!"{ns}.{n}", s!"{b}.{n}"))
  return ([s!"taint_summary {ns}.perm : VectorTaint.taint {ofRegs ".x0, .x1"} " ++
      s!"(.call {c}.name {c}.code) keeping {all}", absorb,
    s!"taint_summary {ns}.pad : VectorTaint.taint {ofRegs ".x0, .x1, .x2, .x4"} " ++
      s!"{fn "pad" "pad"} keeping {all} using {ns}.perm",
    s!"taint_summary {ns}.squeeze : VectorTaint.taint {ofRegs args} " ++
      s!"{fn "squeeze" "squeeze"} keeping {high} using {ns}.perm"], [])

/-- The commands of `sponge_taint_summaries ns callee saving`, for a
permutation that writes the callee-saved registers (restoring them): no
summary keeps anything, so each function has a summary for each set of
callee-saved registers public at some call (the larger first). -/
def spongeSumSavingCmds (ns c : String) : List String := Id.run do
  let perm := s!"(.call {c}.name {c}.code)"
  let fn (f n : String) :=
    s!"(.call (\"vg_keccak_{f}\" ++ {c}.suffix) (Impl.Sha3.AArch64.Stream.{n}With {c}))"
  let ofRegs (rs : String) := s!"(VectorTaint.ofRegs [{rs}])"
  let s := ".x19, .x20, .x21, .x22, .x23, .x24"
  let perms := (spongeSaved.map fun (n, rs) => (s!"perm{n}s", s!".x0, .x1, {s}, {rs}")) ++
    [("permS", s!".x0, .x1, {s}")] ++
    (spongeSaved.map fun (n, rs) => (s!"perm{n}", s!".x0, .x1, {rs}")) ++ [("perm", ".x0, .x1")]
  let usingS := " ".intercalate (perms.map fun (n, _) => s!"{ns}.{n}")
  let args := ".x0, .x1, .x2, .x3, .x4, .x5"
  let absorbs := [("absorb23", ".x23, .x25, .x26, .x27, .x28"),
    ("absorb24", ".x24, .x25, .x26, .x27, .x28"), ("absorb28", ".x25, .x26, .x27, .x28"),
    ("absorb27", ".x25, .x26, .x27"), ("absorb24_26", ".x24, .x25, .x26")]
  return (perms.map fun (n, rs) =>
      s!"taint_summary {ns}.{n} : VectorTaint.taint {ofRegs rs} {perm}") ++
    (absorbs.map fun (n, rs) =>
      s!"taint_summary {ns}.{n} : VectorTaint.taint {ofRegs (args ++ ", " ++ rs)} " ++
        s!"{fn "absorb" "absorb"} using {usingS}") ++
    (spongeSaved.map fun (n, rs) =>
      s!"taint_summary {ns}.pad{n} : VectorTaint.taint {ofRegs (".x0, .x1, .x2, .x4, " ++ rs)} " ++
        s!"{fn "pad" "pad"} using {usingS}") ++
    (spongeSaved.map fun (n, rs) =>
      s!"taint_summary {ns}.squeeze{n} : VectorTaint.taint {ofRegs (args ++ ", " ++ rs)} " ++
        s!"{fn "squeeze" "squeeze"} using {usingS}")

/-- `sponge_taint_summaries ns callee` defines, in the namespace `ns`, the
summaries of the permutation `callee` and of the sponge's functions over it
(the absorb, pad and squeeze calls of `Impl.Sha3.AArch64.Stream`), for
`sponge_taint_decide ns`; `sponge_taint_summaries ns callee from base` only
that of absorb, and takes the others from `base` (for a callee that differs
from `base`'s only in its absorb); `sponge_taint_summaries ns callee saving`
those of a permutation that writes (and restores) the callee-saved
registers (`spongeSumSavingCmds`). -/
syntax "sponge_taint_summaries " ident ident (" from " ident)? (&" saving")? : command

elab_rules : command
  | `(sponge_taint_summaries $ns $callee $[from $base]? $[saving%$sv]?) => do
    let (cmds, aliases) := if sv.isSome then
        (spongeSumSavingCmds ns.getId.toString callee.getId.toString, [])
      else spongeSumCmds ns.getId.toString callee.getId.toString (base.map (·.getId.toString))
    for cmd in cmds do
      match Parser.runParserCategory (← getEnv) `command cmd with
      | .ok stx => elabCommand stx
      | .error e => throwError "sponge_taint_summaries: {e}"
    -- The summaries of `base`, under the names of `ns`.
    liftTermElabM do
      for (a, b) in aliases do
        let b ← realizeGlobalConstNoOverload (mkIdent b.toName)
        let name := (← getCurrNamespace) ++ a.toName
        let type := (← getConstInfo b).type
        addDecl <| .thmDecl { name, levelParams := [], type, value := mkConst b }

/-- `taint_decide_sum` with the summaries of `sponge_taint_summaries ns` and
of ML-KEM's functions. -/
elab "sponge_taint_decide " ns:ident : tactic => do
  let ns := ns.getId.toString
  let mut names := #[]
  for n in (spongeSumNames.map fun n => s!"{ns}.{n}") ++ mlkemSumNames do
    if !(← resolveGlobalName n.toName).isEmpty then names := names.push n
  let tac := s!"taint_decide_sum [{", ".intercalate names.toList}]"
  match Parser.runParserCategory (← getEnv) `tactic tac with
  | .ok stx => Tactic.evalTactic stx
  | .error e => throwError "sponge_taint_decide: {e}"

end VG.Proof.Sha3.AArch64
